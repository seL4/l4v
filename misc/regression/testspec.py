#!/usr/bin/env python3
#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

import os
import heapq
import argparse
import sys

from lxml import etree

REGRESSION_DIR = os.path.dirname(os.path.realpath(__file__))
REGRESSION_DTD = os.path.join(REGRESSION_DIR, "regression.dtd")


class TestSpecParseException(Exception):
    pass


class TestEnv(object):

    def __init__(self, base_dir):
        self.base_dir = os.path.normpath(base_dir)
        self.cwd = self.base_dir
        self.timeout = 0
        self.cpu_timeout = 0
        self.depends = frozenset()

    _update = {
        'cwd': lambda self, cwd: os.path.normpath(os.path.join(self.base_dir, cwd)),
        'timeout': lambda self, timeout: timeout,
        'cpu_timeout': lambda self, cpu_timeout: cpu_timeout,
        'depends': lambda self, depends: self.depends | frozenset(depends)
    }

    __slots__ = 'base_dir', 'cwd', 'timeout', 'cpu_timeout', 'depends'

    def update(self, updates):
        new_env = TestEnv.__new__(TestEnv)
        new_env.base_dir = self.base_dir
        for name, upd in TestEnv._update.items():
            new = upd(self, updates[name]) if name in updates else getattr(self, name)
            setattr(new_env, name, new)
        return new_env


def parse_attributes(tag, env):
    """Parse attributes such as "timeout" in the given XML tag,
    returning an updated env to reflect them."""

    updates = {}

    def parse_attr(name, xml_name, cast):
        value = tag.get(xml_name)
        if value is not None:
            updates[name] = cast(value)

    parse_attr("cwd", "cwd", str)
    parse_attr("timeout", "timeout", int)
    parse_attr("cpu_timeout", "cpu-timeout", float)
    parse_attr("depends", "depends", lambda s: s.split())

    return env.update(updates) if updates else env


class Test(object):

    __slots__ = (
        'name', 'command', 'cwd', 'timeout', 'cpu_timeout',
        'depends', 'depends_trans', 'depends_rtrans',
        'reverse', 'reverse_trans', 'reverse_rtrans'
    )

    def __init__(self, name, command, env):
        self.name = name
        self.command = command
        self.cwd = env.cwd
        self.timeout = env.timeout
        self.cpu_timeout = env.cpu_timeout
        self.depends = env.depends


def parse_test(doc, env):
    test = Test(doc.get("name"), doc.text.strip(), env)
    return [test]


def tests_names(tests):
    return [t.name for t in tests]


def parse_sequence(doc, env):
    tests = []

    for child in doc:
        new_tests = parse_tag(child, env)
        tests += new_tests
        env = env.update({"depends": tests_names(new_tests)})

    return tests


def parse_set(doc, env):
    tests = []

    for child in doc:
        tests += parse_tag(child, env)

    return tests


parsers = {
    'testsuite': parse_set,
    'set': parse_set,
    'sequence': parse_sequence,
    'test': parse_test
}


def parse_tag(doc, env):
    try:
        parser = parsers[doc.tag]
    except KeyError:
        raise TestSpecParseException("Unknown tag '%s'" % doc.tag)
    return parser(doc, parse_attributes(doc, env))


def validate_xml(doc, filename):
    """Ensure the XML matches the regression DTD."""

    # Read in the DTD
    with open(REGRESSION_DTD) as dtd_file:
        dtd = etree.DTD(dtd_file)

    # Parse the file, and validate against the DTD.
    if not dtd.validate(doc):
        raise Exception(
            "%s does not validate against DTD:\n\n" % filename
            + str(dtd.error_log))


def parse_testsuite_xml(filename):
    # Parse the file.
    parser = etree.XMLParser(remove_comments=True, recover=False)
    doc = etree.parse(filename, parser=parser)

    # Validate the XML.
    validate_xml(doc, filename)

    # Setup an empty environment
    env = TestEnv(os.path.dirname(filename))

    # Parse this tag as a set of tests.
    # Returns a list of all tests found in this file.
    return parse_tag(doc.getroot(), env)


def parse_test_files(xml_files):
    tests = []
    for x in xml_files:
        try:
            tests += parse_testsuite_xml(x)
        except:
            sys.stderr.write("Exception while parsing file: %s.\n" % x)
            raise
    return tests


def show_names(names):
    return ' '.join(sorted(names))


def check_tests(tests):
    # Check that test names are unique.
    names, dups = set(), set()
    for n in tests_names(tests):
        if n in names:
            dups.add(n)
        else:
            names.add(n)
    if dups:
        raise TestSpecParseException(
            "Duplicate test names: %s" % show_names(dups))

    # Check that dependencies exist.
    bad_depends = {dep for t in tests for dep in t.depends} - names
    if bad_depends:
        raise TestSpecParseException(
            "Invalid dependencies: %s" % show_names(bad_depends))


def step_rel(rel):
    # From a one-step relation represented as a dictionary,
    # generate the corresponding one-or-two-step relation.
    return dict((s, rel[s].union(*(rel[t] for t in rel[s]))) for s in rel)


def trans_depends(rel):
    # Repeatedly add dependencies of dependencies until convergence.
    rel_t = step_rel(rel)
    while rel_t != rel:
        rel, rel_t = rel_t, step_rel(rel_t)
    return rel_t


def refl_depends(rel):
    rel_r = {}
    for t in rel:
        rel_r[t] = rel[t] | {t}
    return rel_r


class Depends(object):
    __slots__ = 'step', 'trans', 'rtrans'

    def __init__(self, step):
        trans = trans_depends(step)
        rtrans = refl_depends(trans)

        # Provide access to dictionary contents,
        # without exposing dictionaries to mutation.
        def lookup(rel):
            # Allow the user to customise handling of missing keys,
            # but by default, raise the appropriate KeyError.
            def result(x, fail=lambda x: rel[x]):
                if x in rel:
                    return rel[x]
                else:
                    return fail(x)
            return result

        self.step = lookup(step)
        self.trans = lookup(trans)
        self.rtrans = lookup(rtrans)


def collect_dependencies(tests):
    forward, reverse = {}, {}
    for t in tests:
        forward[t.name] = frozenset(t.depends)
        reverse[t.name] = frozenset(r.name for r in tests if t.name in r.depends)
    return Depends(forward), Depends(reverse)


def toposort(keys, forward_depends, reverse_depends):
    """Topological sort.

    Perform a toposort of keys, retaining the existing ordering as closely
    as possible, without breaking dependencies.
    """

    # Count number of forward dependencies.
    fwd_deps = dict((k, len(forward_depends(k))) for k in keys)

    # Enumerate keys so we can retain ordering as much as possible.
    enum_of_key = dict((k, i) for (i, k) in enumerate(keys))

    if len(enum_of_key) != len(keys):
        raise Exception("toposort: non-unique keys")

    #
    # Generate heap of tests without a parent, and keep popping off
    # the heap and processing the tests.
    #
    result = []
    candidates = [(p, k) for (p, k) in enumerate(keys) if fwd_deps[k] == 0]

    while len(candidates) > 0:
        (p, k) = heapq.heappop(candidates)
        result.append(k)
        for j in reverse_depends(k):
            fwd_deps[j] -= 1
            if fwd_deps[j] == 0:
                heapq.heappush(candidates, (enum_of_key[j], j))

    if len(result) != len(keys) or set(result) != set(keys):
        raise Exception("toposort: panic")

    return result


class TestInfo(object):
    __slots__ = 'tests', 'tests_by_name', 'forward_deps', 'reverse_deps'

    def __init__(self, tests, tests_by_name, forward_deps, reverse_deps):
        self.tests = tests
        self.tests_by_name = tests_by_name
        self.forward_deps = forward_deps
        self.reverse_deps = reverse_deps


def process_tests(tests):
    """Given a list of tests (possibly from multiple XML file), check for
    errors and return a list of tests in dependency-satisfying order."""

    # Check test names are unique and dependencies exist.
    check_tests(tests)

    # Collect dependencies.
    forward_deps, reverse_deps = collect_dependencies(tests)

    # Annotate tests with richer dependencies.
    for t in tests:
        t.reverse = reverse_deps.step(t.name)
        t.depends_trans = forward_deps.trans(t.name)
        t.reverse_trans = reverse_deps.trans(t.name)
        t.depends_rtrans = forward_deps.rtrans(t.name)
        t.reverse_rtrans = reverse_deps.rtrans(t.name)

    tests_by_name = dict((t.name, t) for t in tests)

    # Check for cyclic dependencies.
    cyclic = [t.name for t in tests if t.name in t.depends_trans]
    if cyclic:
        raise TestSpecParseException("Tests with cyclic dependencies: %s" % show_names(cyclic))

    # Sort tests in dependency order.
    ordered_names = toposort(tests_names(tests), forward_deps.step, reverse_deps.step)
    tests = [tests_by_name[t] for t in ordered_names]

    return TestInfo(tests, tests_by_name, forward_deps, reverse_deps)


def process_test_files(xml_files):
    return process_tests(parse_test_files(xml_files))


def main():
    # Parse arguments
    parser = argparse.ArgumentParser(description="Regression Framework Testspec Parser")
    parser.add_argument("file", metavar="FILE", type=str, nargs="*",
                        help="a regression XML file to parse")
    args = parser.parse_args()

    # Ensure we have at least one file.
    if len(args.file) == 0:
        parser.error("Please provide at least one XML file.")

    # Fetch XML tests.
    test_info = process_test_files(args.file)

    # Print results
    for test in test_info.tests:
        print("\"%s\" [timeout=%d, cpu-timeout=%g, parents=%s, cwd=%s]" % (
            test.command, test.timeout, test.cpu_timeout, ",".join(test.depends), test.cwd))


if __name__ == "__main__":
    main()
