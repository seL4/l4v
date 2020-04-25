/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * Running 64-bit Isabelle is a dangerous task. In particular, it is liable to
 * suck up all your RAM and send your system into swap-death on quite a regular
 * basis.
 *
 * This Linux utility will regularly scan the system for signs of swap-death
 * (i.e., low memory and high pagefault rate and high load average) and send
 * SIGSTOP to processes suspected of being the cause.
 *
 * When it triggers, it will write to syslog stating the process stopped.
 *
 * 2012 David Greenaway
 */

#define _GNU_SOURCE /* for asprintf */
#include <stdio.h>
#include <stdlib.h>

#include <sys/types.h>
#include <sys/sysinfo.h>
#include <sys/time.h>
#include <sys/resource.h>

#include <dirent.h>
#include <unistd.h>
#include <signal.h>
#include <syslog.h>
#include <string.h>

/* A system load-average considered "dangerous". */
#define DANGEROUS_LOAD 3.0

/* A system load-average considered "very dangerous". */
#define VERY_DANGEROUS_LOAD 10.0

/* A percentage of RAM considered to be "dangerously low". */
#define DANGEROUS_FREE_RAM 0.02

/* A number of page-faults per second considered to be heavy swapping. */
#define DANGEROUS_FAULTS_PER_SECOND 100

/* A minimum Linux OOM score for a process to be considered for stopping. */
#define MIN_OOM_SCORE 3

/* Number of seconds we sleep between each system probe. */
#define SLEEP_TIME 5

/* Number of seconds we sleep for after stopping a process before considereing
 * stopping another. */
#define SLEEP_AFTER_STOP_SECONDS 15

/* Scheduling priority we should run at. */
#define SCHED_PRIO (-10)

/* Misc OS constants. */
#define MAX_PATH_SIZE 1024
#define MAX_LINE_SIZE 1024
#define LINUX_SYSINFO_LOADS_SCALE 65536

void fatal(const char *str)
{
    printf("%s\n", str);
    exit(1);
}

/* Get the name of a process from its PID. */
int name_of(int pid, char *output, size_t len)
{
    char *path;
    if (asprintf(&path, "/proc/%d/cmdline", pid) == -1) {
        return -1;
    }

    /* Open the process's command line details from /proc. */
    FILE *f = fopen(path, "r");
    free(path);
    if (f == NULL) {
        return -1;
    }

    /* Here we potentially read too much, but cmdline entries are NUL delimited
     * so the resulting data is a valid C string of just the first argument as
     * desired.
     */
    int r = fread(output, len, 1, f);
    (void)r;
    fclose(f);

    return 0;
}

/* Iterate through processes in the system. */
void iterate_processes(char **limit, void (*proc_fn)(int, void *), void *data)
{
    /* Open /proc */
    DIR *proc_dir = opendir("/proc");
    if (proc_dir == NULL) {
        fprintf(stderr, "Could not open /proc.");
        exit(1);
    }

    /* Read through processes. */
    while (1) {
        /* Read directory. */
        struct dirent *e = readdir(proc_dir);
        if (e == NULL) {
            break;
        }

        /* Skip non-directories. */
        if ((e->d_type & DT_DIR) == 0) {
            continue;
        }

        /* Process? */
        int p = atoi(e->d_name);
        if (p == 0) {
            continue;
        }

        if (limit != NULL) {
            int skip = 1;

            /* Find the name of the process we're looking at. */
            char name[PATH_MAX];
            if (name_of(p, name, PATH_MAX) != 0)
                /* This process doesn't have a name. Poor thing. */
            {
                continue;
            }

            /* Determine if this process matches any of the processes we should
             * be considering.
             */
            char **l;
            for (l = limit; *l != NULL; l++) {
                if (!strcmp(name, *l)) {
                    skip = 0;
                    break;
                }
                char *last_slash = strrchr(name, '/');
                if (last_slash != NULL && !strcmp(last_slash + 1, *l)) {
                    skip = 0;
                    break;
                }
            }

            if (skip == 1)
                /* No match. */
            {
                continue;
            }

#if DEBUG
            printf("Considering %s...\n", name);
#endif
        }

        proc_fn(p, data);
    }

    /* Cleanup. */
    closedir(proc_dir);
}

struct test_data {
    int worst_pid;
    unsigned long worst_oom_score;
    long long total_faults;
};

void test_process(int p, void *d)
{
    struct test_data *data = d;
    char buf[MAX_PATH_SIZE];
    unsigned long oom_score = 0;
    unsigned long vmem_usage = 0;
    unsigned long rmem_usage = 0;
    unsigned long pagefaults = 0;
    char state;
    FILE *f;
    int n;

    /* Read OOM score of process. */
    sprintf(buf, "/proc/%d/oom_score", p);
    f = fopen(buf, "r");
    if (f == NULL) {
        return;
    }
    n = fscanf(f, "%lu", &oom_score);
    if (n != 1) {
        fatal("Could not read process oom_score.");
    }
    fclose(f);

    /* Read memory usage of process. */
    sprintf(buf, "/proc/%d/statm", p);
    f = fopen(buf, "r");
    if (f == NULL) {
        return;
    }
    n = fscanf(f, "%lu %lu", &vmem_usage, &rmem_usage);
    if (n != 2) {
        fatal("Could not read process memory usage.");
    }
    fclose(f);

    /* Read pagefault information about the process. */
    sprintf(buf, "/proc/%d/stat", p);
    f = fopen(buf, "r");
    if (f == NULL) {
        return;
    }
    n = fscanf(f, "%*d %*s %c %*d %*d %*d %*d %*d %*u %*u %*u %lu", &state, &pagefaults);
    if (n != 2) {
        fatal("Could not read process stat info.");
    }
    fclose(f);

    /* Are we in an active_state? */
    int process_active = (state != 'T' && state != 'Z');

    /* Collate data. */
    data->total_faults += pagefaults;
    if (oom_score > data->worst_oom_score && process_active) {
        data->worst_oom_score = oom_score;
        data->worst_pid = p;
    }
}

static long int parse_meminfo_int(char *buf)
{
    while (*buf == ' ') {
        buf++;
    }
    return strtol(buf, NULL, 10);
}

static void get_free_memory(unsigned long *total, unsigned long *free)
{
    char buf[MAX_LINE_SIZE];
    unsigned long memtotal = 0;
    unsigned long memfree = 0;
    unsigned long memcached = 0;

    /* Read meminfo file. */
    FILE *f = fopen("/proc/meminfo", "r");
    if (f == NULL) {
        fprintf(stderr, "Could not open /proc/meminfo.");
        exit(1);
    }

    while (1) {
        char *r = fgets(buf, MAX_LINE_SIZE, f);
        if (r == NULL) {
            break;
        }
        if (strncmp("MemTotal: ", buf, 10) == 0) {
            memtotal = parse_meminfo_int(buf + 10);
        } else if (strncmp("MemFree:  ", buf, 10) == 0) {
            memfree = parse_meminfo_int(buf + 10);
        } else if (strncmp("Cached:   ", buf, 10) == 0) {
            memcached = parse_meminfo_int(buf + 10);
        }
    }

    fclose(f);
    *total = memtotal;
    *free = memfree + memcached;
}

int is_system_unstable(
    long long last_fault_count,
    long long this_fault_count)
{
    struct sysinfo info;
    int error = sysinfo(&info);
    if (error) {
        return 0;
    }

    /* Get free RAM. */
    unsigned long memtotal, memfree;
    get_free_memory(&memtotal, &memfree);
    double free_ram = (memfree / (double)memtotal);

    /* Get number of faults. */
    long long faults = 0;
    if (last_fault_count > 0) {
        faults = (this_fault_count - last_fault_count);
    }

    /* Get system load. */
    double system_load = info.loads[0] / (double)LINUX_SYSINFO_LOADS_SCALE;

#if DEBUG
    /* Print information. */
    printf("[RAM: %5.1lf] [LOAD: %5.1lf] [FAULTS: %5lld]\n",
           free_ram * 100.0, system_load, faults);
#endif

    /* Determine if the system is unstable. */
    if (free_ram > DANGEROUS_FREE_RAM) {
        return 0;
    }
    if (system_load < DANGEROUS_LOAD) {
        return 0;
    }
    if (faults < DANGEROUS_FAULTS_PER_SECOND * SLEEP_TIME && system_load < VERY_DANGEROUS_LOAD) {
        return 0;
    }
    return 1;
}

/* Determine what signal the given string parses to. */
int parse_signal(const char *input, int *signal, const char **signame)
{
    if (!strcmp(input, "SIGABRT") || !strcmp(input, "6")) {
        *signal = SIGABRT;
        *signame = "SIGABRT";
        return 0;
    }

    if (!strcmp(input, "SIGSTOP") || !strcmp(input, "17")) {
        *signal = SIGSTOP;
        *signame = "SIGSTOP";
        return 0;
    }

    if (!strcmp(input, "SIGTERM") || !strcmp(input, "15")) {
        *signal = SIGTERM;
        *signame = "SIGTERM";
        return 0;
    }

    if (!strcmp(input, "SIGKILL") || !strcmp(input, "9")) {
        *signal = SIGKILL;
        *signame = "SIGKILL";
        return 0;
    }

    return 1;
}

void usage(int argc, char **argv)
{
    printf("\n"
           "usage: %s [<SIGNAL>] [<processes>]\n\n"
           "Monitors the system for high load and sends a signal to (hopefully)\n"
           "the culprit process.\n\n"
           "<SIGNAL> must be either SIGKILL or SIGSTOP.\n"
           "If you don't pass a list of candidate processes, all are considered.\n\n",
           argc > 0 ? argv[0] : "autostop");
}

int main(int argc, char **argv)
{
    int skip_count = 0;
    long long last_fault_count = 0;
    int signal;
    const char *signame;
    char **suspects;

    /* Determine which signal to send. */
    if (argc < 2) {
        signal = SIGSTOP;
        signame = "SIGSTOP";
    } else {
        int error = parse_signal(argv[1], &signal, &signame);
        if (error) {
            usage(argc, argv);
            return 1;
        }
    }

    /* Determine the list of candidate processes. */
    suspects = argc > 2 ? &argv[2] : NULL;

    /* Set our scheduling priority higher. */
    (void)setpriority(PRIO_PROCESS, 0, SCHED_PRIO);

    while (1) {
        /* Collect data. */
        struct test_data d = {
            .worst_pid = -1,
            .worst_oom_score = MIN_OOM_SCORE,
            .total_faults = 0,
        };
        iterate_processes(suspects, test_process, &d);

        /* Determine if things are looking bad and we haven't recently stoped something. */
        if (is_system_unstable(last_fault_count, d.total_faults)) {
            if (d.worst_pid != -1 && skip_count == 0) {
#if DEBUG
                printf("Sending %s to pid %d.\n", signame, d.worst_pid);
#endif
                int error = kill(d.worst_pid, signal);
                if (!error) {
                    syslog(LOG_ALERT,
                           "auto-stop: Sending %s to pid %d to prevent system melt-down.\n", signame, d.worst_pid);
                    skip_count = SLEEP_AFTER_STOP_SECONDS / SLEEP_TIME;
                }
            }
        }
        if (skip_count > 0) {
            skip_count--;
        }

        last_fault_count = d.total_faults;
        sleep(SLEEP_TIME);
    }

    return 0;
}
