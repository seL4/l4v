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
import copy
import heapq
import glob
import subprocess
import itertools
import argparse
import sys

from lxml import etree

REGRESSION_DIR = os.path.dirname(os.path.realpath(__file__))
REGRESSION_DTD = os.path.join(REGRESSION_DIR, "regression.dtd")

class TestSpecParseException(Exception):
    pass

class TestEnv():
    def __init__(self, pwd):
        self.pwd = pwd
        self.cwd = "."
        self.timeout = 0
        self.cpu_timeout = 0
        self.depends = set()

class Test():
    def __init__(self, name, command, timeout=0, cpu_timeout=0, cwd="", depends=None):
        self.name = name
        self.command = command
        self.timeout = timeout
        self.cpu_timeout = cpu_timeout
        self.cwd = cwd

        if depends == None:
            depends = set([])
        self.depends = depends

def parse_attributes(tag, env, strict=True):
    """Parse attributes such as "timeout" in the given XML tag,
    updating the given "env" to reflect them."""
    if tag.get("timeout"):
        try:
            env.timeout = int(tag.get("timeout"))
        except:
            if strict:
                raise
    if tag.get("cpu-timeout"):
        try:
            env.cpu_timeout = float(tag.get("cpu-timeout"))
        except:
            if strict:
                raise
    if tag.get("cwd"):
        env.cwd = tag.get("cwd")
    if tag.get("depends"):
        env.depends |= set(tag.get("depends").split())

def parse_test(doc, env, strict=True):
    """Parse a <test> tag."""
    env = copy.deepcopy(env)
    parse_attributes(doc, env, strict=strict)
    return Test(doc.get("name"), doc.text.strip(),
            timeout=env.timeout,
            cpu_timeout=env.cpu_timeout,
            cwd=os.path.normpath(os.path.join(env.pwd, env.cwd)),
            depends=env.depends)

def parse_sequence(doc, env, strict=True):
    # Create a copy of env so that the scope is restored.
    env = copy.deepcopy(env)

    # Parse attributes.
    parse_attributes(doc, env)

    # Parse children.
    tests = []
    for child in doc:
        if child.tag == "set":
            # Parse set, recording dependencies of the tests inside the set.
            new_tests = parse_set(child, env, strict=strict)
            for x in new_tests:
                env.depends.add(x.name)
            tests += new_tests
        elif child.tag == "sequence":
            # Parse sequence, recording dependencies of the tests inside the set.
            new_tests = parse_sequence(child, env, strict=strict)
            for x in new_tests:
                env.depends.add(x.name)
            tests += new_tests
        elif child.tag == "test":
            tests.append(parse_test(child, env, strict=strict))
            env.depends.add(tests[-1].name)
        elif strict:
            raise TestSpecParseException("Unknown tag '%s'" % child.tag)

    return tests

def parse_set(doc, env, strict=True):
    # Create a copy of env so that the scope is restored.
    env = copy.deepcopy(env)

    # Parse attributes.
    parse_attributes(doc, env, strict=strict)

    # Parse children.
    tests = []
    for child in doc:
        if child.tag == "set":
            tests += parse_set(child, env, strict=strict)
        elif child.tag == "sequence":
            tests += parse_sequence(child, env, strict=strict)
        elif child.tag == "test":
            tests.append(parse_test(child, env, strict=strict))
        elif strict:
            raise TestSpecParseException("Unknown tag '%s'" % child.tag)

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
                if x != None:
                    return [n] + x
            active.discard(n)
            safe.add(n)
        return do_dfs(n)
    shortest_cycle = None
    for i in keys:
        x = dfs(i)
        if x != None and (shortest_cycle == None
                or len(x) < len(shortest_cycle)):
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

def validate_xml(filename):
    """Ensure the XML matches the regression DTD."""

    # Read in the DTD
    with open(REGRESSION_DTD) as dtd_file:
        dtd = etree.DTD(dtd_file)

    # Parse the file, and validate against the DTD.
    parser = etree.XMLParser(remove_comments=True)
    doc = etree.parse(filename, parser=parser)
    if not dtd.validate(doc):
        raise Exception(
                "%s does not validate against DTD:\n\n" % filename
                + str(dtd.error_log))

def parse_testsuite_xml(filename, strict=True):

    # Validate the XML if requested.
    if strict:
        validate_xml(filename)

    # Parse the file. We try to keep reading broken XML. If "strict" is false,
    # keep trying to parse over broken XML.
    parser = etree.XMLParser(remove_comments=True, recover=(not strict))
    doc = etree.parse(filename, parser=parser).getroot()

    # Setup an empty environment
    env = TestEnv(os.path.dirname(filename))

    # Parse this tag as a set of tests.
    return parse_set(doc, env, strict=strict)

def process_tests(tests, strict=False):
    """Given a list of tests (possibly from multiple XML file), check for
    errors and return a list of tests in dependency-satisfying order."""

    # Check for duplicate names.
    seen_names = set()
    for t in tests:
        if t.name in seen_names:
            if strict:
                raise TestSpecParseException("Duplicate test name detected: %s" % t.name)
            for x in itertools.count(2):
                proposed_name = "%s_%d" % (t.name, x)
                if not proposed_name in seen_names:
                    t.name = proposed_name
                    break
        seen_names.add(t.name)

    # Check dependencies.
    valid_names = set()
    for test in tests:
        valid_names.add(test.name)
    for test in tests:
        test_depends = sorted(test.depends)
        for dependency_name in test_depends:
            if not dependency_name in valid_names:
                if strict:
                    raise TestSpecParseException(
                            "Dependency '%s' invalid." % dependency_name)
                test.depends.remove(dependency_name)

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
        if strict:
            raise TestSpecParseException(
                    "Cycle in dependencies: %s" % e.message)
        else:
            # There is a cycle, but we want to continue anyway.
            # Just ignore all deps and hope for the best.
            ordering = dict((t, n) for (n, t)
                    in enumerate(sorted([t.name for t in tests])))
    ordering = dict((t, n) for (n, t) in enumerate(ordering))
    tests = sorted(tests, key=lambda k: ordering[k.name])

    return tests

def legacy_testspec(root):
    """Find tests inside makefiles."""

    # Find candidate "IsaMakefile"s
    candidates = sorted(
        glob.glob(os.path.join(root, "*", "IsaMakefile"))
        + glob.glob(os.path.join(root, "*", "*", "IsaMakefile")))

    # Get isabelle binary.
    isabelle_bin = os.path.abspath(os.path.join(root, "isabelle", "bin", "isabelle"))

    # Run "isabelle make report-regression" on each.
    def report_regression(filename):
        filename = os.path.abspath(filename)
        base_name = os.path.split(os.path.dirname(filename))[1]
        try:
            with open(os.devnull, "w") as devnull:
                results = subprocess.check_output(
                    [isabelle_bin, "make", "-f", filename, "report-regression"],
                    cwd=os.path.dirname(filename),
                    stderr=devnull)
            return [(base_name + "/" + x, x) for x in results.strip().split()]
        except subprocess.CalledProcessError:
            return []

    # Search for tests.
    tests = []
    for candidate in candidates:
        targets = report_regression(os.path.abspath(candidate))
        for (name, target) in targets:
            new_test = Test(name, "isabelle make " + target, timeout=4*3600,
                        cwd=os.path.dirname(os.path.abspath(candidate)))
            tests.append(new_test)
    return tests

def parse_test_files(xml_files, strict=False):
    tests = []
    for x in xml_files:
        try:
            tests += parse_testsuite_xml(x)
        except:
            sys.stderr.write("Exception while parsing file: %s.\n" % x)
            if strict:
                raise
    return process_tests(tests, strict=strict)

def main():
    # Parse arguments
    parser = argparse.ArgumentParser(description="Regression Framework Testspec Parser")
    parser.add_argument("file", metavar="FILE", type=str, nargs="*",
            help="a regression XML file to parse")
    parser.add_argument("-r", "--relax", action="store_false", dest="strict",
            help="be less strict when parsing XML files")
    parser.add_argument("-l", "--legacy", action="store_true",
            help="use legacy 'IsaMakefile' specs")
    args = parser.parse_args()

    # Ensure we are either in legacy more or we have at least one file.
    if not args.legacy and len(args.file) == 0:
        parser.error("Please provide at least one XML file.")
    if args.legacy and len(args.file) > 0:
        parser.error("Can not use both legacy mode and XML files.")

    if args.legacy:
        # Fetch legacy tests.
        tests = legacy_testspec(os.getcwd())
    else:
        # Fetch XML tests.
        tests = parse_test_files(args.file, strict=args.strict)

    # Print results
    for test in tests:
        print("\"%s\" [timeout=%d, cpu-timeout=%g, parents=%s, cwd=%s]" % (
            test.command, test.timeout, test.cpu_timeout, ",".join(test.depends), test.cwd))


if __name__ == "__main__":
    main()

