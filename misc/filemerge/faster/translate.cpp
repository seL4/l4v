/*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */

/* This program was written by a recovering C programmer. It likely has many
 * things that will make C++ programmers cringe. FFTF.
 */

#include <cassert>
#include <cwchar>
#include <error.h>
#include <errno.h>
#include <fstream>
#include <getopt.h>
#include <iostream>
#include <locale>
#include <map>

using namespace std;

#define die(args...) error(-1, errno, args)

#include "tables.hpp" /* generated */

static int to_ascii(wifstream &in, wofstream &out) {
    assert(in.is_open());
    assert(out.is_open());

    wchar_t c;
    while (in.get(c)) {

        const auto t = unicode_to_ascii.find(c);
        if (t == unicode_to_ascii.end())
            out << c;
        else
            out << t->second;

    }

    return 0;
}

static int to_unicode(wifstream &in, wofstream &out) {
    assert(in.is_open());
    assert(out.is_open());

    wchar_t buffer[ASCII_SEQ_MAX + 1];
    unsigned int index = 0;

    wchar_t c;
    while (in.get(c)) {

        buffer[index++] = c;

        if ((index == 1 && buffer[0] != '\\') ||
            (index == 2 && buffer[1] != '<') ||
            (index == 3 && buffer[2] == '^')) {
            /* Dump the buffer. */
            buffer[index] = '\0';
            out << buffer;
            index = 0;
        } else if (buffer[index - 1] == '>') {
            buffer[index] = '\0';
            const auto t = ascii_to_unicode.find(buffer);
            if (t == ascii_to_unicode.end())
                die("unrecognised ASCII sequence \"%.*ls\"", (int)index,
                    buffer);
            else
                out << t->second;
            index = 0;
        } else if (index == sizeof(buffer) - 1) {
            die("too large ASCII sequence \"%.*ls...\" in source", (int)index,
                buffer);
        }
    }

    if (index > 0) {
        /* There is some pending text in the buffer. */
        buffer[index] = '\0';
        out << buffer;
    }

    return 0;
}

class Options {
    public:
        wifstream input;
        wofstream output;
        enum {
            TO_UNICODE = 0,
            TO_ASCII,
        } mode;

        Options() : mode(TO_UNICODE) {}

        ~Options() {
            input.close();
            output.close();
        }
};

static int parse_args(int argc, char **argv, Options &options) {
    while (true) {
        static struct option opts[] = {
            {"input", required_argument, 0, 'i'},
            {"output", required_argument, 0, 'o'},
            {"to-ascii", no_argument, 0, 'a'},
            {"to-unicode", no_argument, 0, 'u'},
            {0, 0, 0, 0},
        };
        int index = 0;

        int c = getopt_long(argc, argv, "ai:o:u", opts, &index);

        if (c == -1)
            break;

        switch (c) {
            case 'a':
                options.mode = Options::TO_ASCII;
                break;

            case 'i':
                if (options.input.is_open())
                    options.input.close();
                options.input.open(optarg);
                if (!options.input.is_open())
                    die("failed to open %s", optarg);
                break;

            case 'o':
                if (options.output.is_open())
                    options.output.close();
                options.output.open(optarg);
                if (!options.output.is_open())
                    die("failed to open %s", optarg);
                break;

            case 'u':
                options.mode = Options::TO_UNICODE;
                break;

            default:
                return -1;
        }
    }

    if (!options.input.is_open())
        options.input.open("/dev/stdin");
    if (!options.output.is_open())
        options.output.open("/dev/stdout");

    return 0;
}

int main(int argc, char **argv) {

    /* Switch to the user's native locale, which hopefully supports UTF-8. */
    locale::global(locale(""));

    Options options;

    if (parse_args(argc, argv, options) != 0)
        return -1;

    switch (options.mode) {

        case Options::TO_ASCII:
            return to_ascii(options.input, options.output);

        case Options::TO_UNICODE:
            return to_unicode(options.input, options.output);

        default:
            assert(!"invalid mode?");
    }

    return 0;
}
