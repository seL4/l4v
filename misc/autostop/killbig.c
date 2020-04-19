/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/*
 * KILL processes that consume more than X bytes of RAM.
 *
 * When it triggers, it will write to syslog stating the process stopped.
 *
 * 2012 David Greenaway
 */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

#include <sys/types.h>
#include <sys/sysinfo.h>
#include <sys/time.h>
#include <sys/resource.h>

#include <dirent.h>
#include <unistd.h>
#include <signal.h>
#include <syslog.h>
#include <string.h>

#define MAX_PATH_SIZE 1024

/* Scheduling priority we should run at. */
#define SCHED_PRIO (-10)

void fatal(const char *str)
{
    printf("%s\n", str);
    exit(1);
}

/* Iterate through processes in the system. */
void iterate_processes(void (*proc_fn)(int, void *), void *data)
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
        if (p != 0) {
            proc_fn(p, data);
        }
    }

    /* Cleanup. */
    closedir(proc_dir);
}

void test_process(int p, void *data)
{
    /*
     * Test process with pid 'p'.
     *
     * We must be aware that the process might have died between the time
     * we found out about it and the time we test it; we deal with such
     * race conditions by skipping over the process.
     */

    uint64_t max_usage_mb = *(uint64_t *)data;
    char buf[MAX_PATH_SIZE];
    unsigned long vmem_usage = 0;
    unsigned long rmem_usage = 0;
    FILE *f;
    int n;

    /* Read memory usage of process. */
    sprintf(buf, "/proc/%d/statm", p);
    f = fopen(buf, "r");
    if (f == NULL) {
        return;
    }
    n = fscanf(f, "%lu %lu", &vmem_usage, &rmem_usage);
    if (n != 2) {
        /* This may still not return anything if the process dies between us
         * opening the file and performing this read. */
        fclose(f);
        return;
    }
    fclose(f);

    /* Convert from pages to megabytes. */
    rmem_usage = rmem_usage * (4096 / 1024) / 1024;

    /* Kill the proces if it is too big. */
    if (rmem_usage >= max_usage_mb) {
        (void)kill(p, SIGKILL);
        syslog(LOG_ALERT,
               "killbig: Sending SIGKILL to pid %d (process size of %lu MB exceeds %lu MB).\n",
               p, rmem_usage, max_usage_mb);
    }
}

void usage(int argc, char **argv)
{
    printf("\n"
           "usage: %s <max mem usage in MB>\n\n",
           argc > 0 ? argv[0] : "killbig");
}

int main(int argc, char **argv)
{
    uint64_t max_mem_usage;

    /* Determine which signal to send. */
    if (argc < 2) {
        usage(argc, argv);
        return 1;
    }
    max_mem_usage = (uint64_t)atoll(argv[1]);
    if (max_mem_usage <= 16) {
        usage(argc, argv);
        return 1;
    }

    /* Set our scheduling priority higher. */
    (void)setpriority(PRIO_PROCESS, 0, SCHED_PRIO);

    /* Monitor. */
    while (1) {
        iterate_processes(test_process, &max_mem_usage);
        sleep(5);
    }
}
