#!/usr/bin/env python
#
# Copyright 2014, NICTA
#
# This software may be distributed and modified according to the terms of
# the BSD 2-Clause license. Note that NO WARRANTY is provided.
# See "LICENSE_BSD2.txt" for details.
#
# @TAG(NICTA_BSD)
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

class Test(object):

    __slots__ = ('name', 'command', 'cwd', 'timeout', 'cpu_timeout', 'depends')

    def __init__(self, name, command, env):
        self.name = name
        self.command = command
        self.cwd = env.cwd
        self.timeout = env.timeout
        self.cpu_timeout = env.cpu_timeout
        self.depends = set(env.depends)

class TestEnv(object):

    def __init__(self, base_dir):
        self.base_dir = os.path.normpath(base_dir)
        self.cwd = self.base_dir
        self.timeout = 0
        self.cpu_timeout = 0
        self.depends = set()

    _update = {
        'cwd': lambda self, cwd: os.path.normpath(os.path.join(self.base_dir, cwd)),
        'timeout': lambda self, timeout: timeout,
        'cpu_timeout': lambda self, cpu_timeout: cpu_timeout,
        'depends': lambda self, depends: self.depends | set(depends)
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
        if value is not None: updates[name] = cast(value)

    parse_attr("cwd", "cwd", str)
    parse_attr("timeout", "timeout", int)
    parse_attr("cpu_timeout", "cpu-timeout", float)
    parse_attr("depends", "depends", lambda s: s.split())

    return env.update(updates) if updates else env

def parse_test(doc, env):
    test = Test(doc.get("name"), doc.text.strip(), env)
    return [test]

def parse_sequence(doc, env):
    tests = []

    for child in doc:
        new_tests = parse_tag(child, env)
        tests += new_tests
        env = env.update({"depends": map(lambda t: t.name, new_tests)})

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
    try: parser = parsers[doc.tag]
    except KeyError: raise TestSpecParseException("Unknown tag '%s'" % doc.tag)
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

def find_cycle(keys, depends_on):
    """Find the shortest cycle in the input graph. Unnecessarily O(n**2)."""
    def dfs(n):
        safe = set()
        active = set()
        def do_dfs(n):
            if n in safe:
                return None
            if n in active:
                return [n]
            active.add(n)
            for c in depends_on(n):
                x = do_dfs(c)
                if x is not None:
                    return [n] + x
            active.discard(n)
            safe.add(n)
        return do_dfs(n)
    shortest_cycle = None
    for i in keys:
        x = dfs(i)
        if x is not None and (shortest_cycle is None or len(x) < len(shortest_cycle)):
            shortest_cycle = x
    return shortest_cycle

def toposort(keys, prio, depends_on):
    """topological sort of keys.

    Perform a toposort for keys, trying to order elements by the priority
    returned by function "prio" as closely as possible without breaking
    dependencies.
    """
    #
    # We start by creating a dictionary of which tests are dependent on others,
    # and then how many outstanding dependencies each test has.
    #
    # Instead of using "dependents" and "dependencies", we use "parents" and
    # "children". A parent must be processed before its child.
    #
    keys = sorted(keys, key=prio)
    children = {}
    num_parents = {}
    for key in keys:
        num_parents[key] = len(depends_on(key))
        for parent in depends_on(key):
            children.setdefault(parent, set()).add(key)

    #
    # Generate heap of tests without a parent, and keep popping off
    # the heap and processing the tests.
    #
    final_order = []
    parentless = sorted([(prio(k), k) for k in keys if num_parents[k] == 0])
    while len(parentless) > 0:
        (p, k) = heapq.heappop(parentless)
        final_order.append(k)
        for s in children.get(k, []):
            num_parents[s] -= 1
            if num_parents[s] == 0:
                heapq.heappush(parentless, (prio(s), s))

    # Ensure we saw everybody. If we didn't, there is a cycle.
    if len(keys) != len(final_order):
        shortest_cycle = find_cycle(keys, depends_on)
        raise ValueError("Circular dependency involving: %s" %
                (" -> ".join(shortest_cycle)))

    return final_order

def process_tests(tests):
    """Given a list of tests (possibly from multiple XML file), check for
    errors and return a list of tests in dependency-satisfying order."""

    # Check for duplicate names.
    seen_names = set()
    for t in tests:
        if t.name in seen_names:
            raise TestSpecParseException("Duplicate test name detected: %s" % t.name)
        seen_names.add(t.name)

    # Check dependencies.
    valid_names = set()
    for test in tests:
        valid_names.add(test.name)
    for test in tests:
        test_depends = sorted(test.depends)
        for dependency_name in test_depends:
            if dependency_name not in valid_names:
                raise TestSpecParseException("Dependency '%s' invalid." % dependency_name)

    # Toposort.
    test_ordering = {}
    for (n, t) in enumerate(tests):
        test_ordering[t.name] = n
    test_depends = {}
    for t in tests:
        test_depends[t.name] = t.depends
    try:
        ordering = toposort([t.name for t in tests],
                lambda x: test_ordering[x],
                lambda x: test_depends[x])
    except ValueError as e:
        raise TestSpecParseException("Cycle in dependencies: %s" % e.message)

    ordering = dict((t, n) for (n, t) in enumerate(ordering))
    tests = sorted(tests, key=lambda k: ordering[k.name])

    return tests

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
    tests = process_test_files(args.file)

    # Print results
    for test in tests:
        print("\"%s\" [timeout=%d, cpu-timeout=%g, parents=%s, cwd=%s]" % (
            test.command, test.timeout, test.cpu_timeout, ",".join(test.depends), test.cwd))


if __name__ == "__main__":
    main()
