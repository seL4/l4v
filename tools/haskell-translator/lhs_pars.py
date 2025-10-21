#
# Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
#
# SPDX-License-Identifier: BSD-2-Clause
#

from __future__ import print_function
from __future__ import absolute_import
import re
import sys
import os
import six
from six.moves import map
from six.moves import range
from six.moves import zip
from functools import reduce

import braces
from msgs import error, warning


class Call(object):

    def __init__(self):
        self.restr = None
        self.decls_only = False
        self.instanceproofs = False
        self.bodies_only = False
        self.bad_type_assignment = False
        self.body = False
        self.current_context = []


class Def(object):

    def __init__(self):
        self.type = None
        self.defined = None
        self.body = None
        self.line = None
        self.sig = None
        self.instance_proofs = []
        self.instance_extras = []
        self.comments = []
        self.primrec = None
        self.deriving = []
        self.instance_defs = {}


def parse(call):
    """Parses a file."""
    set_global(call)

    defs = get_defs(call.filename)

    lines = get_lines(defs, call)

    lines = perform_module_redirects(lines, call)

    return ['%s\n' % line for line in lines]


def settings_line(l):
    """Adjusts some global settings."""
    bits = l.split(',')
    for bit in bits:
        bit = bit.strip()
        (kind, setting) = bit.split('=')
        kind = kind.strip()
        if kind == 'keep_constructor':
            [cons] = setting.split()
            keep_conss[cons] = 1
        else:
            assert not "setting kind understood", bit


def set_global(_call):
    global call
    call = _call
    global filename
    filename = _call.filename


file_defs = {}


def splitList(list, pred):
    """Splits a list according to pred."""
    result = []
    el = []
    for l in list:
        if pred(l):
            if el != []:
                result.append(el)
                el = []
        else:
            el.append(l)
    if el != []:
        result.append(el)
    return result


def takeWhile(list, pred):
    """Returns the initial portion of the list where each
element matches pred"""
    limit = 0

    for l in list:
        if pred(l):
            limit = limit + 1
        else:
            break
    return list[0:limit]


def get_defs(filename):
    # if filename in file_defs:
    #    return file_defs[filename]

    cmdline = os.environ['L4CPP']
    f = os.popen('cpp -Wno-invalid-pp-token -traditional-cpp %s %s' %
                 (cmdline, filename))
    input = [line.rstrip() for line in f]
    f.close()
    defs = top_transform(input, filename.endswith(".lhs"))

    file_defs[filename] = defs
    return defs


def top_transform(input, isLhs):
    """Top level transform, deals with lhs artefacts, divides
        the code up into a series of seperate definitions, and
        passes these definitions through the definition transforms."""
    to_process = []
    comments = []
    for n, line in enumerate(input):
        if '\t' in line:
            warning('tab in line %d, %s.\n' % (n, filename))
        if isLhs:
            if line.startswith('> '):
                if '--' in line:
                    line = line.split('--')[0].strip()

                if line[2:].strip() == '':
                    comments.append((n, 'C', ''))
                elif line.startswith('> {-#'):
                    comments.append((n, 'C', '(*' + line + '*)'))
                else:
                    to_process.append((line[2:], n))
            else:
                if line.strip():
                    comments.append((n, 'C', '(*' + line + '*)'))
                else:
                    comments.append((n, 'C', ''))
        else:
            if '--' in line:
                line = line.split('--')[0].rstrip()

            if line.strip() == '':
                comments.append((n, 'C', ''))
            elif line.strip().startswith('{-'):
                # single-line {- -} comments only
                comments.append((n, 'C', '(*' + line + '*)'))
            elif line.startswith('#'):
                # preprocessor directives
                comments.append((n, 'C', '(*' + line + '*)'))
            else:
                to_process.append((line, n))

    def_tree = offside_tree(to_process)
    defs = create_defs(def_tree)
    defs = group_defs(defs)

    #   Forget about the comments for now

    # defs_plus_comments = [d.line, d) for d in defs] + comments
    # defs_plus_comments.sort()
    # defs = []
    # prev_comments = []
    # for term in defs_plus_comments:
    #     if term[1] == 'C':
    #         prev_comments.append(term[2])
    #     else:
    #         d = term[1]
    #         d.comments = prev_comments
    #         defs.append(d)
    #         prev_comments = []

    # apply def_transform and cut out any None return values
    defs = [defs_transform(d) for d in defs]
    defs = [d for d in defs if d is not None]

    defs = ensure_type_ordering(defs)

    return defs


def get_lines(defs, call):
    """Gets the output lines needed for this call from
        all the potential output generated at parse time."""

    if call.restr:
        defs = [d for d in defs if d.type == 'comments'
                or call.restr(d)]

    output = []
    for d in defs:
        lines = def_lines(d, call)
        if lines:
            output.extend(lines)
            output.append('')

    return output


def offside_tree(input):
    """Breaks lines up into a tree based on the offside rule.
        Each line gets as children the lines following it up until
        the next line whose indent is less or equal."""
    if input == []:
        return []
    head, head_n = input[0]
    head_indent = len(head) - len(head.lstrip())
    children = []
    result = []
    for line, n in input[1:]:
        indent = len(line) - len(line.lstrip())
        if indent <= head_indent:
            result.append((head, head_n, offside_tree(children)))
            head, head_n, head_indent = (line, n, indent)
            children = []
        else:
            children.append((line, n))
    result.append((head, head_n, offside_tree(children)))

    return result


def discard_line_numbers(tree):
    """Takes a tree containing tuples (line, n, children) and
        discards the n terms, returning a tree with tuples
        (line, children)"""
    result = []
    for (line, _, children) in tree:
        result.append((line, discard_line_numbers(children)))
    return result


def flatten_tree(tree):
    """Returns a tree to the set of numbered lines it was
        drawn from."""
    result = []
    for (line, children) in tree:
        result.append(line)
        result.extend(flatten_tree(children))

    return result


def create_defs(tree):
    defs = [create_def(elt) for elt in tree]
    defs = [d for d in defs if d is not None]

    return defs


def group_defs(defs):
    """Takes a file broken into a series of definitions, and locates
        multiple definitions of constants, caused by type signatures or
        pattern matching, and accumulates to a single object per genuine
        definition"""
    defgroups = []
    defined = ''
    for d in defs:
        this_defines = d.defined
        if d.type != 'definitions':
            this_defines = ''
        if this_defines == defined and this_defines:
            defgroups[-1].body.extend(d.body)
        else:
            defgroups.append(d)
            defined = this_defines

    return defgroups


def create_def(elt):
    """Takes an element of an offside tree and creates
        a definition object."""
    (line, n, children) = elt
    children = discard_line_numbers(children)
    return create_def_2(line, children, n)


def create_def_2(line, children, n):
    d = Def()
    d.body = [(line, children)]
    d.line = n
    lead = line.split(None, 3)
    if lead[0] in ['import', 'module', 'class']:
        return
    elif lead[0] == 'instance':
        type = 'instance'
        defined = lead[2]
    elif lead[0] in ['type', 'newtype', 'data']:
        type = 'newtype'
        defined = lead[1]
    else:
        type = 'definitions'
        defined = lead[0]

    d.type = type
    d.defined = defined
    return d


def get_primrecs():
    f = open('primrecs')
    keys = [line.strip() for line in f]
    return set(key for key in keys if key != '')


primrecs = get_primrecs()


def defs_transform(d):
    """Transforms the set of definitions for a function. This
        may include its type signature, and may include the special
        case of multiple definitions."""
    # the first tokens of the first line in the first definition
    if d.type == 'newtype':
        return newtype_transform(d)
    elif d.type == 'instance':
        return instance_transform(d)

    lead = d.body[0][0].split(None, 2)
    if lead[1] == '::':
        d.sig = type_sig_transform(d.body[0])
        d.body.pop(0)

    if d.defined in primrecs:
        return primrec_transform(d)

    if len(d.body) > 1:
        d.body = pattern_match_transform(d.body)

    if len(d.body) == 0:
        print()
        print(d)
        assert 0

    d.body = body_transform(d.body, d.defined, d.sig)
    return d


def wrap_qualify(lines, deep=True):
    if len(lines) == 0:
        return lines

    """Close and then re-open a locale so instantiations can go through"""
    if deep:
        asdfextra = ""
    else:
        asdfextra = ""

    if call.current_context:
        lines.insert(0, 'end\nqualify {} (in Arch) {}'.format(call.current_context[-1],
                                                              asdfextra))
        lines.append('end_qualify\ncontext Arch begin global_naming %s' % call.current_context[-1])
    return lines


def def_lines(d, call):
    """Produces the set of lines associated with a definition."""
    if call.all_bits:
        L = []
        if d.comments:
            L.extend(flatten_tree(d.comments))
            L.append('')
        if d.type == 'definitions':
            L.append('definition')
            if d.sig:
                L.extend(flatten_tree([d.sig]))
                L.append('where')
                L.extend(flatten_tree(d.body))
        elif d.type == 'newtype':
            L.extend(flatten_tree(d.body))
        if d.instance_proofs:
            L.extend(wrap_qualify(flatten_tree(d.instance_proofs)))
            L.append('')
        if d.instance_extras:
            L.extend(flatten_tree(d.instance_extras))
            L.append('')
        return L

    if call.instanceproofs:
        if not call.bodies_only:
            instance_proofs = wrap_qualify(flatten_tree(d.instance_proofs))
        else:
            instance_proofs = []

        if not call.decls_only:
            instance_extras = flatten_tree(d.instance_extras)
        else:
            instance_extras = []

        newline_needed = len(instance_proofs) > 0 and len(instance_extras) > 0
        return instance_proofs + (['']
                                  if newline_needed else []) + instance_extras

    if call.body:
        return get_lambda_body_lines(d)

    comments = d.comments
    try:
        typesig = flatten_tree([d.sig])
    except:
        typesig = []
    body = flatten_tree(d.body)
    type = d.type

    if type == 'definitions':
        if call.decls_only:
            if typesig:
                return comments + ["consts'"] + typesig
            else:
                return []
        elif call.bodies_only:
            if d.sig:
                defname = '%s_def' % d.defined
                if d.primrec:
                    warning('body-only primrec:\n' + body[0], call.filename)
                    return comments + ['primrec'] + body
                return comments + ['defs %s:' % defname] + body
            else:
                return comments + ['definition'] + body
        else:
            if d.primrec:
                return comments + ['primrec'] + typesig \
                    + ['where'] + body
            if typesig:
                return comments + ['definition'] + typesig + ['where'] + body
            else:
                return comments + ['definition'] + body
    elif type == 'comments':
        return comments
    elif type == 'newtype':
        if not call.bodies_only:
            return body


def type_sig_transform(tree_element):
    """Performs transformations on a type signature line
        preceding a function declaration or some such."""

    line = reduce_to_single_line(tree_element)
    (pre, post) = line.split('::')
    result = type_transform(post)
    if '[pp' in result:
        print(line)
        print(pre)
        print(post)
        print(result)
        assert 0
    line = pre + ':: "' + result + '"'

    return (line, [])


ignore_classes = {'Error': 1}
hand_classes = {'Bits': ['HS_bit'],
                'Num': ['minus', 'one', 'zero', 'plus', 'numeral'],
                'FiniteBits': ['finiteBit']}


def type_transform(string):
    """Performs transformations on a type signature, whether
        part of a type signature line or occuring in a function."""

    # deal with type classes by recursion
    bits = string.split('=>', 1)
    if len(bits) == 2:
        lhs = bits[0].strip()
        if lhs.startswith('(') and lhs.endswith(')'):
            instances = lhs[1:-1].split(',')
            string = ' => '.join(instances + [bits[1]])
        else:
            instances = [lhs]
        var_annotes = {}
        for instance in instances:
            (name, var) = instance.split()
            if name in ignore_classes:
                continue
            if name in hand_classes:
                names = hand_classes[name]
            else:
                names = [type_conv(name)]
            var = "'" + var
            var_annotes.setdefault(var, [])
            var_annotes[var].extend(names)
        transformed = type_transform(bits[1])
        for (var, insts) in six.iteritems(var_annotes):
            if len(insts) == 1:
                newvar = '(%s :: %s)' % (var, insts[0])
            else:
                newvar = '(%s :: {%s})' % (var, ', '.join(insts))
            transformed = newvar.join(transformed.split(var, 1))
        return transformed

    # get rid of (), insert Unit, which converts to unit
    string = 'Unit'.join(string.split('()'))

    # divide up by -> or by , then divide on space.
    # apply everything locally then work back up
    bstring = braces.str(string, '(', ')')
    bits = bstring.split('->')
    r = r' \<Rightarrow> '
    if len(bits) == 1:
        bits = bstring.split(',')
        r = ' * '
    result = [type_bit_transform(bit) for bit in bits]
    return r.join(result)


def type_bit_transform(bit):
    s = str(bit).strip()
    if s.startswith('['):
        # handling this properly is hard.
        assert s.endswith(']')
        bit2 = braces.str(s[1:-1], '(', ')')
        return '%s list' % type_bit_transform(bit2)
    bits = bit.split(None, braces=True)
    if str(bits[0]) == 'PPtr':
        assert len(bits) == 2
        return 'machine_word'
    if len(bits) > 1 and bits[1].startswith('['):
        assert bits[-1].endswith(']')
        arg = ' '.join([str(bit) for bit in bits[1:]])[1:-1]
        arg = type_transform(arg)
        return ' '.join([arg, 'list', str(type_conv(bits[0]))])
    bits = [type_conv(bit) for bit in bits]
    bits = constructor_reversing(bits)
    bits = [bit.map(type_transform) for bit in bits]
    strs = [str(bit) for bit in bits]
    return ' '.join(strs)


def reduce_to_single_line(tree_element):
    def inner(tree_element, acc):
        (line, children) = tree_element
        acc.append(line)
        for child in children:
            inner(child, acc)
        return acc
    return ' '.join(inner(tree_element, []))


type_conv_table = {
    'Maybe': 'option',
    'Bool': 'bool',
    'Word': 'machine_word',
    'Int': 'nat',
    'String': 'unit list'}


def type_conv(string):
    """Converts a type used in Haskell to our equivalent"""
    if string.startswith('('):
        # ignore compound types, type_transform will descend into em
        result = string
    elif '.' in string:
        # qualified references
        bits = string.split('.')
        typename = bits[-1]
        module = reduce(lambda x, y: x + '.' + y, bits[:-1])
        typename = type_conv(typename)
        result = module + '.' + typename
    elif string[0].islower():
        # type variable
        result = "'%s" % string
    elif string[0] == '[' and string[-1] == ']':
        # list
        inner = type_conv(string[1:-1])
        result = '%s list' % inner
    elif str(string) in type_conv_table:
        result = type_conv_table[str(string)]
    else:
        # convert StudlyCaps to lower_with_underscores
        was_lower = False
        s = ''
        for c in string:
            if c.isupper() and was_lower:
                s = s + '_' + c.lower()
            else:
                s = s + c.lower()
            was_lower = c.islower()
        result = s
        type_conv_table[str(string)] = result

    return braces.clone(result, string)


def constructor_reversing(tokens):
    if len(tokens) < 2:
        return tokens
    elif len(tokens) == 2:
        return [tokens[1], tokens[0]]
    elif tokens[0] == '[' and tokens[2] == ']':
        return [tokens[1], braces.str('list', '(', ')')]
    elif len(tokens) == 4 and tokens[1] == '[' and tokens[3] == ']':
        listToken = braces.str('(List %s)' % tokens[2], '(', ')')
        return [listToken, tokens[0]]
    elif tokens[0] == 'array':
        arrow_token = braces.str(r'\<Rightarrow>', '(', ')')
        return [tokens[1], arrow_token, tokens[2]]
    elif tokens[0] == 'either':
        plus_token = braces.str('+', '(', ')')
        return [tokens[1], plus_token, tokens[2]]
    elif len(tokens) == 5 and tokens[2] == '[' and tokens[4] == ']':
        listToken = braces.str('(List %s)' % tokens[3], '(', ')')
        lbrack = braces.str('(', '+', '+')
        rbrack = braces.str(')', '+', '+')
        comma = braces.str(',', '+', '+')
        return [lbrack, tokens[1], comma, listToken, rbrack, tokens[0]]
    elif len(tokens) == 3:
        # here comes a fudge
        lbrack = braces.str('(', '+', '+')
        rbrack = braces.str(')', '+', '+')
        comma = braces.str(',', '+', '+')
        return [lbrack, tokens[1], comma, tokens[2], rbrack, tokens[0]]
    else:
        error(f"error parsing {filename}\n"
              f"Can't deal with {tokens}")
        sys.exit(1)


def newtype_transform(d):
    """Takes a Haskell style newtype/data type declaration, whose
        options are divided with | and each of whose options has named
        elements, and forms a datatype statement and definitions for
        the named extractors and their update functions."""
    if len(d.body) != 1:
        print('--- newtype long body ---')
        print(d)
    [(line, children)] = d.body

    if children and children[-1][0].lstrip().startswith('deriving'):
        l = reduce_to_single_line(children[-1])
        children = children[:-1]
        r = re.compile(r"[,\s\(\)]+")
        bits = r.split(l)
        bits = [bit for bit in bits if bit and bit != 'deriving']
        d.deriving = bits

    line = reduce_to_single_line((line, children))

    bits = line.split(None, 1)
    op = bits[0]
    line = bits[1]
    bits = line.split('=', 1)
    header = type_conv(bits[0].strip())
    d.typename = header
    d.typedeps = set()
    if len(bits) == 1:
        # line of form 'data Blah' introduces unknown type?
        d.body = [('typedecl %s' % header, [])]
        all_type_arities[header] = []  # HACK
        return d
    line = bits[1]

    if op == 'type':
        # type synonym
        return typename_transform(line, header, d)
    elif line.find('{') == -1:
        # not a record
        return simple_newtype_transform(line, header, d)
    else:
        return named_newtype_transform(line, header, d)


# parameterised types of which we know that they are already defined in Isabelle
known_type_assignments = [
    'domain_schedule',
    'kernel',
    'kernel_f',
    'kernel_f f',  # there is a KernelF instance that gets transformed into this
    'kernel_init',
    'kernel_init_state',
    'machine_data',
    'machine_monad',
    'ready_queue',
    'user_monad',
    'fpustate',
    'eight_tuple a'
]


def typename_transform(line, header, d):
    try:
        [oldtype] = line.split()
    except:
        if header not in known_type_assignments:
            warning('Type assignment with parameters not supported %s\n  Translated string was "%s"'
                    % (d.body, header), filename)
            call.bad_type_assignment = True
        return
    if oldtype.startswith('Data.Word.Word'):
        # take off the prefix, leave Word32 or Word64 etc
        oldtype = oldtype[10:]
    oldtype = type_conv(oldtype)
    # get rid of (), insert unit
    oldtype = 'unit'.join(oldtype.split('()'))
    bits = oldtype.split()
    for bit in bits:
        d.typedeps.add(bit)
    lines = [
        'type_synonym %s = "%s"' % (header, oldtype),
        # translations (* TYPE 1 *)',
        # "%s" <=(type) "%s"' % (oldtype, header)
    ]
    d.body = [(line, []) for line in lines]
    return d


keep_conss = {}


def simple_newtype_transform(line, header, d):
    lines = []
    arities = []
    for i, bit in enumerate(line.split('|')):
        braced = braces.str(bit, '(', ')')
        bits = braced.split()
        if len(bits) == 2:
            last_lhs = bits[0]

        if i == 0:
            l = '    %s' % bits[0]
        else:
            l = '  | %s' % bits[0]
        for bit in bits[1:]:
            if bit.startswith('('):
                bit = bit[1:-1]
            typename = type_transform(str(bit))
            if len(bits) == 2:
                last_rhs = typename
            if ' ' in typename:
                typename = '"%s"' % typename
            l = l + ' ' + typename
            d.typedeps.add(typename)
        lines.append(l)

        arities.append((str(bits[0]), len(bits[1:])))

    if list((dict(arities)).values()) == [1] and header not in keep_conss:
        return type_wrapper_type(header, last_lhs, last_rhs, d)

    d.body = [('datatype %s =' % header, [(line, []) for line in lines])]

    set_instance_proofs(header, arities, d)

    return d


all_constructor_args = {}


def named_newtype_transform(line, header, d):
    bits = line.split('|')

    constructors = [get_type_map(bit) for bit in bits]
    all_constructor_args.update(dict(constructors))

    lines = []
    for i, (name, map) in enumerate(constructors):
        if i == 0:
            l = '    %s' % name
        else:
            l = '  | %s' % name
        oname = name
        for name, type in map:
            if type is None:
                print("ERR: None snuck into constructor list for %s" % name)
                print(line, header, oname)
                assert False

            if name is None:
                opt_name = ""
                opt_close = ""
            else:
                opt_name = " (" + name + " :"
                opt_close = ")"

            if len(type.split()) == 1 and '(' not in type:
                the_type = type
            else:
                the_type = '"' + type + '"'

            l = l + opt_name + ' ' + the_type + opt_close

            for bit in type.split():
                d.typedeps.add(bit)
        lines.append(l)

    names = {}
    types = {}
    for cons, map in constructors:
        for i, (name, type) in enumerate(map):
            names.setdefault(name, {})
            names[name][cons] = i
            types[name] = type

    for name, map in six.iteritems(names):
        lines.append('')
        lines.extend(named_update_definitions(name, map, types[name], header,
                                              dict(constructors)))

    for name, map in constructors:
        if map == []:
            continue
        lines.append('')
        lines.extend(named_constructor_translation(name, map, header))

    if len(constructors) > 1:
        for name, map in constructors:
            lines.append('')
            check = named_constructor_check(name, map, header)
            lines.extend(check)

    if len(constructors) == 1:
        for ex_name, _ in six.iteritems(names):
            for up_name, _ in six.iteritems(names):
                lines.append('')
                lines.extend(named_extractor_update_lemma(ex_name, up_name))

    arities = [(name, len(map)) for (name, map) in constructors]

    if list((dict(arities)).values()) == [1] and header not in keep_conss:
        [(cons, map)] = constructors
        [(name, type)] = map
        return type_wrapper_type(header, cons, type, d, decons=(name, type))

    set_instance_proofs(header, arities, d)

    d.body = [('datatype %s =' % header, [(line, []) for line in lines])]
    return d


def named_extractor_update_lemma(ex_name, up_name):
    lines = []
    lines.append('lemma %s_%s_update [simp]:' % (ex_name, up_name))

    if up_name == ex_name:
        lines.append('  "%s (%s_update f v) = f (%s v)"' %
                     (ex_name, up_name, ex_name))
    else:
        lines.append('  "%s (%s_update f v) = %s v"' %
                     (ex_name, up_name, ex_name))

    lines.append('  by (cases v) simp')

    return lines


def named_extractor_definitions(name, map, type, header, constructors):
    lines = []
    lines.append('primrec')
    lines.append('  %s :: "%s \\<Rightarrow> %s"'
                 % (name, header, type))
    lines.append('where')
    is_first = True
    for cons, i in six.iteritems(map):
        if is_first:
            l = '  "%s (%s' % (name, cons)
            is_first = False
        else:
            l = '| "%s (%s' % (name, cons)
        num = len(constructors[cons])
        for k in range(num):
            l = l + ' v%d' % k
        l = l + ') = v%d"' % i
        lines.append(l)

    return lines


def named_update_definitions(name, map, type, header, constructors):
    lines = []
    lines.append('primrec')
    ra = r'\<Rightarrow>'
    if len(type.split()) > 1:
        type = '(%s)' % type
    lines.append('  %s_update :: "(%s %s %s) %s %s %s %s"'
                 % (name, type, ra, type, ra, header, ra, header))
    lines.append('where')
    is_first = True
    for cons, i in six.iteritems(map):
        if is_first:
            l = '  "%s_update f (%s' % (name, cons)
            is_first = False
        else:
            l = '| "%s_update f (%s' % (name, cons)
        num = len(constructors[cons])
        for k in range(num):
            l = l + ' v%d' % k
        l = l + ') = %s' % cons
        for k in range(num):
            if k == i:
                l = l + ' (f v%d)' % k
            else:
                l = l + ' v%d' % k
        l = l + '"'
        lines.append(l)

    return lines


def named_constructor_translation(name, map, header):
    lines = []
    lines.append('abbreviation (input)')
    l = '  %s_trans :: "' % name
    for n, type in map:
        l = l + '(' + type + r') \<Rightarrow> '
    l = l + '%s" ("%s\'_ \\<lparr> %s= _' % (header, name, map[0][0])
    for n, type in map[1:]:
        l = l + ', %s= _' % n.replace("_", "'_")
    l = l + r' \<rparr>")'
    lines.append(l)
    lines.append('where')
    l = '  "%s_ \\<lparr> %s= v0' % (name, map[0][0])
    for i, (n, type) in enumerate(map[1:]):
        l = l + ', %s= v%d' % (n, i + 1)
    l = l + ' \\<rparr> == %s' % name
    for i in range(len(map)):
        l = l + ' v%d' % i
    l = l + '"'
    lines.append(l)

    return lines


def named_constructor_check(name, map, header):
    lines = []
    lines.append('definition')
    lines.append('  is%s :: "%s \\<Rightarrow> bool"' % (name, header))
    lines.append('where')
    lines.append(' "is%s v \\<equiv> case v of' % name)
    l = '    %s ' % name
    for i, _ in enumerate(map):
        l = l + 'v%d ' % i
    l = l + r'\<Rightarrow> True'
    lines.append(l)
    lines.append(r'  | _ \<Rightarrow> False"')

    return lines


def type_wrapper_type(header, cons, rhs, d, decons=None):
    if '\\<Rightarrow>' in d.typedeps:
        d.body = [('(* type declaration of %s omitted *)' % header, [])]
        return d
    lines = [
        'type_synonym %s = "%s"' % (header, rhs),
        # translations (* TYPE 2 *)',
        # "%s" <=(type) "%s"' % (header, rhs),
        '',
        'definition',
        '  %s :: "%s \\<Rightarrow> %s"' % (cons, header, header),
        'where %s_def[simp]:' % cons,
        ' "%s \\<equiv> id"' % cons,
    ]
    if decons:
        (decons, decons_type) = decons
        lines.extend([
            '',
            'definition',
            '  %s :: "%s \\<Rightarrow> %s"' % (decons, header, header),
            'where',
            '  %s_def[simp]:' % decons,
            ' "%s \\<equiv> id"' % decons,
            '',
            'definition'
            '  %s_update :: "(%s \\<Rightarrow> %s) \\<Rightarrow> %s \\<Rightarrow> %s"'
            % (decons, header, header, header, header),
            'where',
            '  %s_update_def[simp]:' % decons,
            ' "%s_update f y \\<equiv> f y"' % decons,
            ''
        ])
        lines.extend(named_constructor_translation(cons, [(decons, decons_type)
                                                          ], header))

    d.body = [(line, []) for line in lines]
    return d


def instance_transform(d):
    [(line, children)] = d.body
    bits = line.split(None, 3)
    assert bits[0] == 'instance'
    classname = bits[1]
    typename = type_conv(bits[2])
    if classname == 'Show':
        warning("discarding class instance '%s :: Show'" % typename, filename)
        return None
    if typename == '()':
        warning("discarding class instance 'unit :: %s'" % classname, filename)
        return None
    if len(bits) == 3:
        if children == []:
            defs = []
        else:
            [(l, c)] = children
            assert l.strip() == 'where'
            defs = c
    else:
        assert bits[3:] == ['where']
        defs = children
    defs = [create_def_2(l, c, 0) for (l, c) in defs]
    defs = [d2 for d2 in defs if d2 is not None]
    defs = group_defs(defs)
    defs = [defs_transform(d2) for d2 in defs]
    defs_dict = {}
    for d2 in defs:
        if d2 is not None:
            defs_dict[d2.defined] = d2
    d.instance_defs = defs_dict
    d.deriving = [classname]
    if typename not in all_type_arities:
        error(f'attempting {d.defined}\n'
              f'(typename {repr(typename)})\n'
              f'when reading {filename}\n'
              f'but class not defined yet\n'
              f'perhaps parse in different order?\n'
              f'hint: #INCLUDE_HASKELL_PREPARSE\n')
        sys.exit(1)
    arities = all_type_arities[typename]
    set_instance_proofs(typename, arities, d)

    return d


all_type_arities = {}


def set_instance_proofs(header, constructor_arities, d):
    all_type_arities[header] = constructor_arities
    pfs = []
    exs = []
    canonical = list(enumerate(constructor_arities))

    classes = d.deriving
    instance_proof_fns = set(
        sorted((instance_proof_table[classname] for classname in classes),
               key=lambda x: x.order))
    for f in instance_proof_fns:
        (npfs, nexs) = f(header, canonical, d)
        pfs.extend(npfs)
        exs.extend(nexs)

    if d.type == 'newtype' and len(canonical) == 1 and False:
        [(cons, n)] = constructor_arities
        if n == 1:
            pfs.extend(finite_instance_proofs(header, cons))

    if pfs:
        lead = '(* %s instance proofs *)' % header
        d.instance_proofs = [(lead, [(line, []) for line in pfs])]
    if exs:
        lead = '(* %s extra instance defs *)' % header
        d.instance_extras = [(lead, [(line, []) for line in exs])]


def finite_instance_proofs(header, cons):
    lines = []
    lines.append('')
    lines.append('instance %s :: finite' % header)
    if call.current_context:
        lines.append('interpretation Arch .')
    lines.append('  apply (intro_classes)')
    lines.append('  apply (rule_tac f="%s" in finite_surj_type)'
                 % cons)
    lines.append('  apply (safe, case_tac x, simp_all)')
    lines.append('  done')

    return (lines, [])

# wondering where the serialisable proofs went? see
# commit 21361f073bbafcfc985934e563868116810d9fa2 for last known occurence.


# leave type tags 0..11 for explicit use outside of this script
next_type_tag = 12


def storable_instance_proofs(header, canonical, d):
    proofs = []
    extradefs = []

    global next_type_tag
    next_type_tag = next_type_tag + 1
    proofs.extend([
        '', 'defs (overloaded)', '  typetag_%s[simp]:' % header,
        ' "typetag (x :: %s) \\<equiv> %d"' % (header, next_type_tag), ''
        'instance %s :: dynamic' % header, '  by (intro_classes, simp)'
    ])

    proofs.append('')
    proofs.append('instance %s :: storable ..' % header)

    defs = d.instance_defs
    extradefs.append('')
    if 'objBits' in defs:
        extradefs.append('definition')
        body = flatten_tree(defs['objBits'].body)
        bits = body[0].split('objBits')
        assert bits[0].strip() == '"'
        if bits[1].strip().startswith('_'):
            bits[1] = 'x ' + bits[1].strip()[1:]
        bits = bits[1].split(None, 1)
        body[0] = '  objBits_%s: "objBits (%s :: %s) %s' \
            % (header, bits[0], header, bits[1])
        extradefs.extend(body)

    extradefs.append('')
    if 'makeObject' in defs:
        extradefs.append('definition')
        body = flatten_tree(defs['makeObject'].body)
        bits = body[0].split('makeObject')
        assert bits[0].strip() == '"'
        body[0] = '  makeObject_%s: "(makeObject :: %s) %s' \
            % (header, header, bits[1])
        extradefs.extend(body)

    extradefs.extend(['', 'definition', ])
    if 'loadObject' in defs:
        extradefs.append('  loadObject_%s:' % header)
        extradefs.extend(flatten_tree(defs['loadObject'].body))
    else:
        extradefs.extend([
            '  loadObject_%s[simp]:' % header,
            ' "(loadObject p q n obj) :: %s \\<equiv>' % header,
            '    loadObject_default p q n obj"',
        ])

    extradefs.extend(['', 'definition', ])
    if 'updateObject' in defs:
        extradefs.append('  updateObject_%s:' % header)
        body = flatten_tree(defs['updateObject'].body)
        bits = body[0].split('updateObject')
        assert bits[0].strip() == '"'
        bits = bits[1].split(None, 1)
        body[0] = ' "updateObject (%s :: %s) %s' \
            % (bits[0], header, bits[1])
        extradefs.extend(body)
    else:
        extradefs.extend([
            '  updateObject_%s[simp]:' % header,
            ' "updateObject (val :: %s) \\<equiv>' % header,
            '    updateObject_default val"',
        ])

    return (proofs, extradefs)


storable_instance_proofs.order = 1


def pspace_storable_instance_proofs(header, canonical, d):
    proofs = []
    extradefs = []

    proofs.append('')
    proofs.append('instance %s :: pre_storable' % header)
    proofs.append('  by (intro_classes,')
    proofs.append(
        '      auto simp: projectKO_opts_defs split: kernel_object.splits arch_kernel_object.splits)')

    defs = d.instance_defs
    extradefs.append('')
    if 'objBits' in defs:
        extradefs.append('definition')
        body = flatten_tree(defs['objBits'].body)
        bits = body[0].split('objBits')
        assert bits[0].strip() == '"'
        if bits[1].strip().startswith('_'):
            bits[1] = 'x ' + bits[1].strip()[1:]
        bits = bits[1].split(None, 1)
        body[0] = '  objBits_%s: "objBits (%s :: %s) %s' \
            % (header, bits[0], header, bits[1])
        extradefs.extend(body)

    extradefs.append('')
    if 'makeObject' in defs:
        extradefs.append('definition')
        body = flatten_tree(defs['makeObject'].body)
        bits = body[0].split('makeObject')
        assert bits[0].strip() == '"'
        body[0] = '  makeObject_%s: "(makeObject :: %s) %s' \
            % (header, header, bits[1])
        extradefs.extend(body)

    extradefs.extend(['', 'definition', ])
    if 'loadObject' in defs:
        extradefs.append('  loadObject_%s:' % header)
        extradefs.extend(flatten_tree(defs['loadObject'].body))
    else:
        extradefs.extend([
            '  loadObject_%s[simp]:' % header,
            ' "(loadObject p q n obj) :: %s kernel \\<equiv>' % header,
            '    loadObject_default p q n obj"',
        ])

    extradefs.extend(['', 'definition', ])
    if 'updateObject' in defs:
        extradefs.append('  updateObject_%s:' % header)
        body = flatten_tree(defs['updateObject'].body)
        bits = body[0].split('updateObject')
        assert bits[0].strip() == '"'
        bits = bits[1].split(None, 1)
        body[0] = ' "updateObject (%s :: %s) %s' \
            % (bits[0], header, bits[1])
        extradefs.extend(body)
    else:
        extradefs.extend([
            '  updateObject_%s[simp]:' % header,
            ' "updateObject (val :: %s) \\<equiv>' % header,
            '    updateObject_default val"',
        ])

    return (proofs, extradefs)


pspace_storable_instance_proofs.order = 1


def num_instance_proofs(header, canonical, d):
    assert len(canonical) == 1
    [(_, (cons, n))] = canonical
    assert n == 1
    lines = []

    def add_bij_instance(classname, fns):
        ins = bij_instance(classname, header, cons, fns)
        lines.extend(ins)

    add_bij_instance('plus', [('plus', '%s + %s', True)])
    add_bij_instance('minus', [('minus', '%s - %s', True)])
    add_bij_instance('zero', [('zero', '0', True)])
    add_bij_instance('one', [('one', '1', True)])
    add_bij_instance('times', [('times', '%s * %s', True)])

    return (lines, [])


num_instance_proofs.order = 2


def enum_instance_proofs(header, canonical, d):
    def singular_canonical():
        if len(canonical) == 1:
            [(_, (_, n))] = canonical
            return n == 1
        else:
            return False

    lines = ['(*<*)']
    if singular_canonical():
        [(_, (cons, n))] = canonical
        # special case for datatypes with single constructor with one argument
        lines.append('instantiation %s :: enum begin' % header)
        if call.current_context:
            lines.append('interpretation Arch .')
        lines.append('definition')
        lines.append('  enum_%s: "enum_class.enum \\<equiv> map %s enum"'
                     % (header, cons))

    else:
        cons_no_args = [cons for i, (cons, n) in canonical if n == 0]
        cons_one_arg = [cons for i, (cons, n) in canonical if n == 1]
        cons_two_args = [cons for i, (cons, n) in canonical if n > 1]
        assert cons_two_args == []
        lines.append('instantiation %s :: enum begin' % header)
        if call.current_context:
            lines.append('interpretation Arch .')
        lines.append('definition')
        lines.append('  enum_%s: "enum_class.enum \\<equiv> ' % header)
        if len(cons_no_args) == 0:
            lines.append('    []')
        else:
            lines.append('    [ ')
            for cons in cons_no_args[:-1]:
                lines.append('      %s,' % cons)
            for cons in cons_no_args[-1:]:
                lines.append('      %s' % cons)
            lines.append('    ]')
        for cons in cons_one_arg:
            lines.append('    @ (map %s enum)' % cons)
        lines[-1] = lines[-1] + '"'
    lines.append('')
    for cons in cons_one_arg:
        lines.append('lemma %s_map_distinct[simp]: "distinct (map %s enum)"' % (cons, cons))
        lines.append('  apply (simp add: distinct_map)')
        lines.append('  by (meson injI %s.inject)' % header)
    lines.append('')
    lines.append('definition')
    lines.append('  "enum_class.enum_all (P :: %s \\<Rightarrow> bool) \\<longleftrightarrow> Ball UNIV P"'
                 % header)
    lines.append('')
    lines.append('definition')
    lines.append('  "enum_class.enum_ex (P :: %s \\<Rightarrow> bool) \\<longleftrightarrow> Bex UNIV P"'
                 % header)
    lines.append('')
    lines.append('  instance')
    lines.append('  apply intro_classes')
    lines.append('   apply (safe, simp)')
    lines.append('   apply (case_tac x)')
    if len(canonical) == 1:
        lines.append('  apply (auto simp: enum_%s enum_all_%s_def enum_ex_%s_def'
                     % (header, header, header))
        lines.append('    distinct_map_enum)')
        lines.append('  done')
    else:
        lines.append('  apply (simp_all add: enum_%s enum_all_%s_def enum_ex_%s_def)'
                     % (header, header, header))
        lines.append('  by fast+')
    lines.append('end')
    lines.append('')
    lines.append('instantiation %s :: enum_alt' % header)
    lines.append('begin')
    if call.current_context:
        lines.append('interpretation Arch .')
    lines.append('definition')
    lines.append('  enum_alt_%s: "enum_alt \\<equiv> ' % header)
    lines.append('    alt_from_ord (enum :: %s list)"' % header)
    lines.append('instance ..')
    lines.append('end')
    lines.append('')
    lines.append('instantiation %s :: enumeration_both' % header)
    lines.append('begin')
    if call.current_context:
        lines.append('interpretation Arch .')
    lines.append('instance by (intro_classes, simp add: enum_alt_%s)'
                 % header)
    lines.append('end')
    lines.append('')
    lines.append('(*>*)')

    return (lines, [])


enum_instance_proofs.order = 3


def bits_instance_proofs(header, canonical, d):
    assert len(canonical) == 1
    [(_, (cons, n))] = canonical
    assert n == 1

    return (bij_instance('bit', header, cons,
                         [('shiftL', 'shiftL %s n', True),
                          ('shiftR', 'shiftR %s n', True),
                          ('bitSize', 'bitSize %s', False)]), [])


bits_instance_proofs.order = 5


def no_proofs(header, canonical, d):
    return ([], [])


no_proofs.order = 6

# FIXME "Bounded" emits enum proofs even if something already has enum proofs
# generated due to "Enum"

instance_proof_table = {
    'Eq': no_proofs,
    'Bounded': no_proofs,  # enum_instance_proofs,
    'Enum': enum_instance_proofs,
    'Ix': no_proofs,
    'Ord': no_proofs,
    'Show': no_proofs,
    'Bits': bits_instance_proofs,
    'Real': no_proofs,
    'Num': num_instance_proofs,
    'Integral': no_proofs,
    'Storable': storable_instance_proofs,
    'PSpaceStorable': pspace_storable_instance_proofs,
    'Typeable': no_proofs,
    'Error': no_proofs,
}


def bij_instance(classname, typename, constructor, fns):
    L = [
        '',
        'instance %s :: %s ..' % (typename, classname),
        'defs (overloaded)'
    ]
    for (fname, fstr, cast_return) in fns:
        n = len(fstr.split('%s')) - 1
        names = ('x', 'y', 'z', 'w')[:n]
        names2 = tuple([name + "'" for name in names])
        fstr1 = fstr % names
        fstr2 = fstr % names2
        L.append('  %s_%s: "%s \\<equiv>' % (fname, typename, fstr1))
        for name in names:
            L.append("    case %s of %s %s' \\<Rightarrow>"
                     % (name, constructor, name))
        if cast_return:
            L.append('      %s (%s)"' % (constructor, fstr2))
        else:
            L.append('      %s"' % fstr2)

    return L


def get_type_map(string):
    """Takes Haskell named record syntax and produces
        a map (in the form of a list of tuples) defining
        the converted types of the names."""
    bits = string.split(None, 1)
    header = bits[0].strip()
    if len(bits) == 1:
        return (header, [])
    actual_map = bits[1].strip()
    if not (actual_map.startswith('{') and actual_map.endswith('}')):
        error(f'in {filename}\n'
              'Expected "A { blah :: blah etc }"\n'
              'However { and } not found correctly\n'
              f'When parsing {string}')
        sys.exit(1)
    actual_map = actual_map[1:-1]

    bits = braces.str(actual_map, '(', ')').split(',')
    bits.reverse()
    type = None
    map = []
    for bit in bits:
        bits = bit.split('::')
        if len(bits) == 2:
            type = type_transform(str(bits[1]).strip())
            name = str(bits[0]).strip()
        else:
            name = str(bit).strip()
        map.append((name, type))
    map.reverse()
    return (header, map)


numLiftIO = [0]


def body_transform(body, defined, sig, nopattern=False):
    # assume single object
    [(line, children)] = body

    if '(' in line.split('=')[0] and not nopattern:
        [(line, children)] = \
            pattern_match_transform([(line, children)])

    if 'liftIO' in reduce_to_single_line((line, children)):
        # liftIO is the translation boundary for current
        # SEL4, below which we get into details of interaction
        # with the foreign function interface - axiomatise
        assert '=' in line
        line = line.split('=')[0]
        bits = line.split()
        numLiftIO[0] = numLiftIO[0] + 1
        rhs = '(%d :: Int) %s' % (numLiftIO[0], ' '.join(bits[1:]))
        line = '%s\\<equiv> underlying_arch_op %s' % (line, rhs)
        children = []
    elif '=' in line:
        line = '\\<equiv>'.join(line.split('=', 1))
    elif leading_bar.match(children[0][0]):
        pass
    elif '=' in children[0][0]:
        (nextline, c2) = children[0]
        children[0] = ('\\<equiv>'.join(nextline.split('=', 1)), c2)
    else:
        warning('def of %s missing =\n' % defined, filename)

    if children and (children[-1][0].endswith('where') or
                     children[-1][0].lstrip().startswith('where')):
        bits = line.split(r'\<equiv>')
        where_clause = where_clause_transform(children[-1])
        children = children[:-1]
        if len(bits) == 2 and bits[1].strip():
            line = bits[0] + r'\<equiv>'
            new_line = ' ' * len(line) + bits[1]
            children = [(new_line, children)]
    else:
        where_clause = []

    (line, children) = zipWith_transforms(line, children)

    (line, children) = supplied_transforms(line, children)

    (line, children) = case_clauses_transform((line, children))

    (line, children) = do_clauses_transform((line, children), sig)

    if children and leading_bar.match(children[0][0]):
        line = line + r' \<equiv>'
        children = guarded_body_transform(children, ' = ')

    children = where_clause + children

    if not nopattern:
        line = lhs_transform(line)
    line = lhs_de_underscore(line)

    (line, children) = type_assertion_transform(line, children)

    (line, children) = run_regexes((line, children))
    (line, children) = run_ext_regexes((line, children))

    (line, children) = bracket_dollar_lambdas((line, children))

    line = '"' + line
    (line, children) = add_trailing_string('"', (line, children))
    return [(line, children)]


dollar_lambda_regex = re.compile(r"\$\s*\\<lambda>")


def bracket_dollar_lambdas(xxx_todo_changeme):
    (line, children) = xxx_todo_changeme
    if dollar_lambda_regex.search(line):
        [left, right] = dollar_lambda_regex.split(line)
        line = '%s(\\<lambda>%s' % (left, right)
        both = (line, children)
        if has_trailing_string(';', both):
            both = remove_trailing_string(';', both)
            (line, children) = add_trailing_string(');', both)
        else:
            (line, children) = add_trailing_string(')', both)
    children = [bracket_dollar_lambdas(elt) for elt in children]
    return (line, children)


def zipWith_transforms(line, children):
    if 'zipWithM_' not in line:
        children = [zipWith_transforms(l, c) for (l, c) in children]
        return (line, children)

    if children == []:
        return (line, [])

    if len(children) == 2:
        [(l, c), (l2, c2)] = children
        if c == [] and c2 == [] and '..]' in l + l2:
            children = [(l + ' ' + l2.strip(), [])]

    (l, c) = children[-1]
    if c != [] or '..]' not in l:
        return (line, children)

    bits = line.split('zipWithM_', 1)
    line = bits[0] + 'mapM_'
    ws = lead_ws(l)
    line2 = ws + '(split ' + bits[1]

    bits = braces.str(l, '[', ']').split(None, braces=True)

    line3 = ws + ' '.join(bits[:-2]) + ')'
    used_children = children[:-1] + [(line3, [])]

    sndlast = bits[-2]
    last = bits[-1]
    if last.endswith('..]'):
        internal = last[1:-3].strip()
        if ',' in internal:
            bits = internal.split(',')
            l = '%s(zipE4 (%s) (%s) (%s))' \
                % (ws, sndlast, bits[0], bits[-1])
        else:
            l = '%s(zipE3 (%s) (%s))' % (ws, sndlast, internal)
    else:
        internal = sndlast[1:-3].strip()
        if ',' in internal:
            bits = internal.split(',')
            l = '%s(zipE2 (%s) (%s) (%s))' \
                % (ws, bits[0], bits[1], last)
        else:
            l = '%s(zipE1 (%s) (%s))' % (ws, internal, last)

    return (line, [(line2, used_children), (l, [])])


def supplied_transforms(line, children):
    t = convert_to_stripped_tuple(line, children)

    if t in supplied_transform_table:
        ws1 = lead_ws(line)
        result = supplied_transform_table[t]
        ws2 = lead_ws(result[0])
        result = adjust_ws(result, len(ws1) - len(ws2))
        supplied_transforms_usage[t] = 1
        return result

    children = [supplied_transforms(l, c) for (l, c) in children]

    return (line, children)


def convert_to_stripped_tuple(line, children):
    children = [convert_to_stripped_tuple(l, c) for (l, c) in children]

    return (line.strip(), tuple(children))


def type_assertion_transform_inner(line):
    m = type_assertion.search(line)
    if not m:
        return line
    var = m.expand('\\1')
    type = m.expand('\\2').strip()
    type = type_transform(type)
    return line[:m.start()] + '(%s::%s)' % (var, type) \
        + type_assertion_transform_inner(line[m.end():])


def type_assertion_transform(line, children):
    children = [type_assertion_transform(l, c) for (l, c) in children]

    return (type_assertion_transform_inner(line), children)


def where_clause_guarded_body(xxx_todo_changeme1):
    (line, children) = xxx_todo_changeme1
    if children and leading_bar.match(children[0][0]):
        return (line + ' =', guarded_body_transform(children, ' = '))
    else:
        return (line, children)


def where_clause_transform(xxx_todo_changeme2):
    (line, children) = xxx_todo_changeme2
    ws = line.split('where', 1)[0]
    if line.strip() != 'where':
        assert line.strip().startswith('where')
        children = [(''.join(line.split('where', 1)), [])] + children
    pre = ws + 'let'
    post = ws + 'in'

    children = [(l, c) for (l, c) in children if l.split()[1] != '::']
    children = [case_clauses_transform((l, c)) for (l, c) in children]
    children = [do_clauses_transform(
        (l, c),
        None,
        type=0) for (l, c) in children]
    children = list(map(where_clause_guarded_body, children))
    for i, (l, c) in enumerate(children):
        l2 = braces.str(l, '(', ')')
        if len(l2.split('=')[0].split()) > 1:
            # turn f a = b into f = (\a -> b)
            l = '->'.join(l.split('=', 1))
            l = lead_ws(l) + ' = (\\ '.join(l.split(None, 1))
            (l, c) = add_trailing_string(')', (l, c))
            children[i] = (l, c)
    children = order_let_children(children)
    for i, child in enumerate(children[:-1]):
        children[i] = add_trailing_string(';', child)
    return [(pre, [])] + children + [(post, [])]


varname_re = re.compile(r"\w+")


def order_let_children(L):
    single_lines = [reduce_to_single_line(elt) for elt in L]
    keys = [str(braces.str(line, '(', ')').split('=')[0]).split()[0]
            for line in single_lines]
    keys = dict((key, n) for (n, key) in enumerate(keys))
    bits = [varname_re.findall(line) for line in single_lines]
    deps = {}
    for i, bs in enumerate(bits):
        for bit in bs:
            if bit in keys:
                j = keys[bit]
                if j != i:
                    deps.setdefault(i, {})[j] = 1
    done = {}
    L2 = []
    todo = dict(enumerate(L))
    n = len(todo)
    while n:
        todo_keys = list(todo.keys())
        for key in todo_keys:
            depstodo = [dep
                        for dep in list(deps.get(key, {}).keys()) if dep not in done]
            if depstodo == []:
                L2.append(todo.pop(key))
                done[key] = 1
        if len(todo) == n:
            print("No progress resolving let deps")
            print()
            print(list(todo.values()))
            print()
            print("Dependencies:")
            print(deps)
            assert 0
        n = len(todo)
    return L2


def do_clauses_transform(xxx_todo_changeme3, rawsig, type=None):
    (line, children) = xxx_todo_changeme3
    if children and children[-1][0].lstrip().startswith('where'):
        where_clause = where_clause_transform(children[-1])
        where_clause = [do_clauses_transform(
            (l, c), rawsig, 0) for (l, c) in where_clause]
        others = (line, children[:-1])
        others = do_clauses_transform(others, rawsig, type)
        (line, children) = where_clause[0]
        return (line, children + where_clause[1:] + [others])

    if children:
        (l, c) = children[0]
        if c == [] and l.endswith('do'):
            line = line + ' ' + l.strip()
            children = children[1:]

    if type is None:
        if not rawsig:
            type = 0
            sig = None
        else:
            sig = ' '.join(flatten_tree([rawsig]))
            type = monad_type_acquire(sig)
    (line, type) = monad_type_transform((line, type))
    if children == []:
        return (line, [])

    rhs = line.split('<-', 1)[-1]
    if rhs.strip() == 'syscall' or rhs.strip() == 'atomicSyscall':
        assert len(children) == 5
        children = [do_clauses_transform(elt,
                                         rawsig,
                                         type=subtype)
                    for elt, subtype in zip(children, [1, 0, 1, 0, type])]
    elif line.strip().endswith('catchFailure'):
        assert len(children) == 2
        children = [do_clauses_transform(elt,
                                         rawsig,
                                         type=subtype)
                    for elt, subtype in zip(children, [1, 0])]
    else:
        children = [do_clauses_transform(elt,
                                         rawsig,
                                         type=type) for elt in children]

    if not line.endswith('do'):
        return (line, children)

    children, other_children = split_on_unmatched_bracket(children)

    # single statement do clause won't parse in Isabelle
    if len(children) == 1:
        ws = lead_ws(line)
        return (line[:-2] + '(', children + [(ws + ')', [])])

    line = line[:-2] + '(do' + 'E' * type

    children = [(l, c) for (l, c) in children if l.strip() or c]

    children2 = []
    for (l, c) in children:
        if l.lstrip().startswith('let '):
            if '=' not in l:
                extra = reduce_to_single_line(c[0])
                assert '=' in extra
                l = l + ' ' + extra
                c = c[1:]
            l = ''.join(l.split('let ', 1))
            letsubs = '<- return' + 'Ok' * type + ' ('
            l = letsubs.join(l.split('=', 1))
            (l, c) = add_trailing_string(')', (l, c))
            children2.extend(do_clause_pattern(l, c, type))
        else:
            children2.extend(do_clause_pattern(l, c, type))

    children = [add_trailing_string(';', child)
                for child in children2[:-1]] + [children2[-1]]

    ws = lead_ws(line)
    children.append((ws + 'od' + 'E' * type + ')', []))

    return (line, children + other_children)


left_start_table = {
    'ASIDPool': '(inv ASIDPool)',
    'HardwareASID': 'id',
    'ArchObjectCap': 'capCap',
    'Just': 'the'
}


def do_clause_pattern(line, children, type, n=0):
    bits = line.split('<-')
    default = [('\\<leftarrow>'.join(bits), children)]
    if len(bits) == 1:
        return default
    (left, right) = line.split('<-', 1)
    if ':' not in left and '[' not in left \
            and len(left.split()) == 1:
        return default
    left = left.strip()

    v = 'v%d' % get_next_unique_id()

    ass = 'assert' + ('E' * type)
    ws = lead_ws(line)

    if left.startswith('('):
        assert left.endswith(')')
        if (',' in left):
            return default
        else:
            left = left[1:-1]
    bs = braces.str(left, '[', ']')
    if len(bs.split(':')) > 1:
        bits = [str(bit).strip() for bit in bs.split(':', 1)]
        lines = [('%s%s <- %s' % (ws, v, right), children),
                 ('%s%s <- headM %s' % (ws, bits[0], v), []),
                 ('%s%s <- tailM %s' % (ws, bits[1], v), [])]
        result = []
        for (l, c) in lines:
            result.extend(do_clause_pattern(l, c, type, n + 1))
        return result
    if left == '[]':
        return [('%s%s <- %s' % (ws, v, right), children),
                ('%s%s (%s = []) []' % (ws, ass, v), [])]
    if left.startswith('['):
        assert left.endswith(']')
        bs = braces.str(left[1:-1], '[', ']')
        bits = bs.split(',', 1)
        if len(bits) == 1:
            new_left = '%s:%s' % (bits[0], v)
            new_line = '%s%s <- %s' % (ws, new_left, right)
            extra = [('%s%s (%s = []) []' % (ws, ass, v), [])]
        else:
            new_left = '%s:[%s]' % (bits[0], bits[1])
            new_line = lead_ws(line) + new_left + ' <- ' + right
            extra = []
        return do_clause_pattern(new_line, children, type, n + 1) \
            + extra
    for lhs in left_start_table:
        if left.startswith(lhs):
            left = left[len(lhs):]
            tab = left_start_table[lhs]
            lM = 'liftM' + 'E' * type
            nl = ('%s <- %s %s $ %s' % (left, lM, tab, right))
            return do_clause_pattern(nl, children, type, n + 1)

    print(line)
    print(left)
    assert 0


def split_on_unmatched_bracket(elts, n=None):
    if n is None:
        elts, other_elts, n = split_on_unmatched_bracket(elts, 0)
        return (elts, other_elts)

    for (i, (line, children)) in enumerate(elts):
        for (j, c) in enumerate(line):
            if c == '(':
                n = n + 1
            if c == ')':
                n = n - 1
                if n < 0:
                    frag1 = line[:j]
                    frag2 = ' ' * len(frag1) + line[j:]
                    new_elts = elts[:i] + [(frag1, [])]
                    oth_elts = [(frag2, children)] \
                        + elts[i + 1:]
                    return (new_elts, oth_elts, n)
        c, other_c, n = split_on_unmatched_bracket(children, n)
        if other_c:
            new_elts = elts[:i] + [(line, c)]
            other_elts = other_c + elts[i + 1:]
            return (new_elts, other_elts, n)

    return (elts, [], n)


def monad_type_acquire(sig, type=0):
    # note kernel appears after kernel_f/kernel_monad
    for (key, n) in [('kernel_f', 1), ('fault_monad', 1), ('syscall_monad', 2),
                     ('kernel_monad', 0), ('kernel_init', 1), ('kernel_p', 1),
                     ('kernel', 0)]:
        if key in sig:
            sigend = sig.split(key)[-1]
            return monad_type_acquire(sigend, n)

    return type


def monad_type_transform(xxx_todo_changeme4):
    (line, type) = xxx_todo_changeme4
    split = None
    if 'withoutError' in line:
        split = 'withoutError'
        newtype = 1
    elif 'doKernelOp' in line:
        split = 'doKernelOp'
        newtype = 0
    elif 'runInit' in line:
        split = 'runInit'
        newtype = 1
    elif 'withoutFailure' in line:
        split = 'withoutFailure'
        newtype = 0
    elif 'withoutFault' in line:
        split = 'withoutFault'
        newtype = 0
    elif 'withoutPreemption' in line:
        split = 'withoutPreemption'
        newtype = 0
    elif 'allowingFaults' in line:
        split = 'allowingFaults'
        newtype = 1
    elif 'allowingErrors' in line:
        split = 'allowingErrors'
        newtype = 2
    elif '`catchFailure`' in line:
        [left, right] = line.split('`catchFailure`', 1)
        left, _ = monad_type_transform((left, 1))
        right, type = monad_type_transform((right, 0))
        return (left + '`catchFailure`' + right, type)
    elif 'catchingFailure' in line:
        split = 'catchingFailure'
        newtype = 1
    elif 'catchF' in line:
        split = 'catchF'
        newtype = 1
    elif 'emptyOnFailure' in line:
        split = 'emptyOnFailure'
        newtype = 1
    elif 'constOnFailure' in line:
        split = 'constOnFailure'
        newtype = 1
    elif 'nothingOnFailure' in line:
        split = 'nothingOnFailure'
        newtype = 1
    elif 'nullCapOnFailure' in line:
        split = 'nullCapOnFailure'
        newtype = 1
    elif '`catchFault`' in line:
        split = '`catchFault`'
        newtype = 1
    elif 'capFaultOnFailure' in line:
        split = 'capFaultOnFailure'
        newtype = 1
    elif 'ignoreFailure' in line:
        split = 'ignoreFailure'
        newtype = 1
    elif 'handleInvocation False' in line:  # THIS IS A HACK
        split = 'handleInvocation False'
        newtype = 0
    if split:
        [left, right] = line.split(split, 1)
        left, _ = monad_type_transform((left, type))
        right, newnewtype = monad_type_transform((right, newtype))
        return (left + split + right, newnewtype)

    if type:
        line = ('return' + 'Ok' * type).join(line.split('return'))
        line = ('when' + 'E' * type).join(line.split('when'))
        line = ('unless' + 'E' * type).join(line.split('unless'))
        line = ('mapM' + 'E' * type).join(line.split('mapM'))
        line = ('forM' + 'E' * type).join(line.split('forM'))
        line = ('liftM' + 'E' * type).join(line.split('liftM'))
        line = ('assert' + 'E' * type).join(line.split('assert'))
        line = ('stateAssert' + 'E' * type).join(line.split('stateAssert'))

    return (line, type)


def case_clauses_transform(xxx_todo_changeme5):
    (line, children) = xxx_todo_changeme5
    children = [case_clauses_transform(child) for child in children]

    if not line.endswith(' of'):
        return (line, children)

    bits = line.split('case ', 1)
    beforecase = bits[0]
    x = bits[1][:-3]

    if '::' in x:
        x2 = braces.str(x, '(', ')')
        bits = x2.split('::', 1)
        if len(bits) == 2:
            x = str(bits[0]) + ':: ' + type_transform(str(bits[1]))

    if children and children[-1][0].strip().startswith('where'):
        warning('where clause in case: %r, removing case.' % line, filename)
        return (beforecase + r'\<comment> \<open>case removed\<close> undefined', [])
        # where_clause = where_clause_transform(children[-1])
        # children = children[:-1]
        # (in_stmt, l) = where_clause[-1]
        # l.append(case_clauses_transform((line, children)))
        # return where_clause

    cases = []
    bodies = []
    for (l, c) in children:
        bits = l.split('->', 1)
        while len(bits) == 1:
            if c == []:
                error('wtf %r\n' % l, filename)
                sys.exit(1)
            if c[0][0].strip().startswith('|'):
                bits = [bits[0], '']
                c = guarded_body_transform(c, '->')
            elif c[0][1] == []:
                l = l + ' ' + c.pop(0)[0].strip()
                bits = l.split('->', 1)
            else:
                [(moreline, c)] = c
                l = l + ' ' + moreline.strip()
                bits = l.split('->', 1)
        case = bits[0].strip()
        tail = bits[1]
        if c and c[-1][0].lstrip().startswith('where'):
            where_clause = where_clause_transform(c[-1])
            ws = lead_ws(where_clause[0][0])
            c = where_clause + [(ws + tail.strip(), [])] + c[:-1]
            tail = ''
        cases.append(case)
        bodies.append((tail, c))

    cases = tuple(cases)  # used as key of a dict later, needs to be hashable
    # (since lists are mutable, they aren't)
    if not cases:
        print(line)
    conv = get_case_conv(cases)
    if conv == '<X>':
        warning('blanked case in caseconvs', filename)
        return (beforecase + r'\<comment> \<open>case removed\<close> undefined', [])
    if not conv:
        warning('no caseconv for %r\n' % (cases, ), filename)
        if cases not in cases_added:
            casestr = 'case \\x of ' + ' -> '.join(cases) + ' -> '

            f = open('caseconvs', 'a')
            f.write('%s ---X>\n\n' % casestr)
            f.close()
            cases_added[cases] = 1
        return (beforecase + r'\<comment> \<open>case removed\<close> undefined', [])
    conv = subs_nums_and_x(conv, x)

    new_line = beforecase + '(' + conv[0][0]
    assert conv[0][1] is None

    ws = lead_ws(children[0][0])
    new_children = []
    for (header, endnum) in conv[1:]:
        if endnum is None:
            new_children.append((ws + header, []))
        else:
            if (len(bodies) <= endnum):
                error('index %d out of bounds in case %r\n' % (endnum, cases), filename)
                sys.exit(1)

            (body, c) = bodies[endnum]
            new_children.append((ws + header + ' ' + body, c))

    if has_trailing_string(',', new_children[-1]):
        new_children[-1] = \
            remove_trailing_string(',', new_children[-1])
        new_children.append((ws + '),', []))
    else:
        new_children.append((ws + ')', []))

    return (new_line, new_children)


def guarded_body_transform(body, div):
    new_body = []
    if body[-1][0].strip().startswith('where'):
        new_body.extend(where_clause_transform(body[-1]))
        body = body[:-1]
    for i, (line, children) in enumerate(body):
        try:
            while div not in line:
                (l, c) = children[0]
                children = c + children[1:]
                line = line + ' ' + l.strip()
        except:
            error('missing %r in %r\nhandling %r' % (div, line, body), filename)
            sys.exit(1)
        try:
            [ws, guts] = line.split('| ', 1)
        except:
            error('missing "|" in %r\nhandling %r' % (line, body), filename)
            sys.exit(1)
        if i == 0:
            new_body.append((ws + 'if', []))
        else:
            new_body.append((ws + 'else if', []))
        guts = ' then '.join(guts.split(div, 1))
        new_body.append((ws + guts, children))
    new_body.append((ws + 'else undefined', []))

    return new_body


def lhs_transform(line):
    if '(' not in line:
        return line

    [left, right] = line.split(r'\<equiv>')

    ws = left[:len(left) - len(left.lstrip())]

    left = left.lstrip()

    bits = braces.str(left, '(', ')').split(braces=True)

    for (i, bit) in enumerate(bits):
        if bit.startswith('('):
            bits[i] = 'arg%d' % i
            case = 'case arg%d of %s \\<Rightarrow> ' % (i, bit)
            right = case + right

    return ws + ' '.join([str(bit) for bit in bits]) + r'\<equiv>' + right


def lhs_de_underscore(line):
    if '_' not in line:
        return line

    [left, right] = line.split(r'\<equiv>')

    ws = left[:len(left) - len(left.lstrip())]

    left = left.lstrip()
    bits = left.split()

    for (i, bit) in enumerate(bits):
        if bit == '_':
            bits[i] = 'arg%d' % i

    return ws + ' '.join([str(bit) for bit in bits]) + r' \<equiv>' + right


regexes = [
    (re.compile(r" \. "), r" \<circ> "),
    (re.compile('-1'), '- 1'),
    (re.compile('-2'), '- 2'),
    (re.compile(r"\(![ ]*(\w+)\)"), r"(flip id \1)"),
    (re.compile(r"\(\+(\w+)\)"), r"(\<lambda> x. x + \1)"),
    (re.compile(r"\\([^<].*?)\s*->"), r"\<lambda> \1."),
    (re.compile('}'), r"\<rparr>"),
    (re.compile(r"(\s)!!(\s)"), r"\1LIST_INDEX\2"),
    (re.compile(r"(\w)!"), r"\1 "),
    (re.compile(r"\s?!"), ''),
    (re.compile(r"LIST_INDEX"), r"!"),
    (re.compile('`testBit`'), '!!'),
    (re.compile(r"//"), ' aLU '),
    (re.compile('otherwise'), 'True     '),
    (re.compile(r"(^|\W)fail "), r"\1haskell_fail "),
    (re.compile('assert '), 'haskell_assert '),
    (re.compile('assertE '), 'haskell_assertE '),
    (re.compile('=='), '='),
    (re.compile(r"\(/="), r'(\<lambda>x. x \<noteq>'),
    (re.compile('/='), r'\<noteq>'),
    (re.compile('"([^"])*"'), '[]'),
    (re.compile('&&'), r'\<and>'),
    (re.compile(r'\|\|'), r'\<or>'),
    (re.compile(r"(\W)not(\s)"), r"\1Not\2"),
    (re.compile(r"(\W)and(\s)"), r"\1andList\2"),
    (re.compile(r"(\W)or(\s)"), r"\1orList\2"),
    # regex ordering important here
    (re.compile(r"\.&\."), '&&'),
    (re.compile(r"\(\.\|\.\)"), r"bitOR"),
    (re.compile(r"\(\+\)"), r"op +"),
    (re.compile(r"\.\|\."), '||'),
    (re.compile(r"Data\.Word\.Word"), r"word"),
    (re.compile(r"Data\.Map\."), r"data_map_"),
    (re.compile(r"Data\.Set\."), r"data_set_"),
    (re.compile(r"BinaryTree\."), 'bt_'),
    (re.compile("mapM_"), "mapM_x"),
    (re.compile("forM_"), "forM_x"),
    (re.compile("forME_"), "forME_x"),
    (re.compile("mapME_"), "mapME_x"),
    (re.compile("zipWithM_"), "zipWithM_x"),
    (re.compile(r"bit\s+([0-9]+)(\s)"), r"(1 << \1)\2"),
    (re.compile('`mod`'), 'mod'),
    (re.compile('`div`'), 'div'),
    (re.compile(r"`((\w|\.)*)`"), r"`~\1~`"),
    (re.compile('size'), 'magnitude'),
    (re.compile('foldr'), 'foldR'),
    (re.compile(r"\+\+"), '@'),
    (re.compile(r"(\s|\)|\w|\]):(\s|\(|\w|$|\[)"), r"\1#\2"),
    (re.compile(r"\[([^]]*)\.\.([^]]*)\]"), r"[\1 .e. \2]"),
    (re.compile(r"\[([^]]*)\.\.\s*$"), r"[\1 .e."),
    (re.compile(' Right'), ' Inr'),
    (re.compile(' Left'), ' Inl'),
    (re.compile('\\(Left'), '(Inl'),
    (re.compile('\\(Right'), '(Inr'),
    (re.compile(r"\$!"), r"$"),
    (re.compile('([^>])>='), r'\1\<ge>'),
    (re.compile('>>([^=])'), r'>>_\1'),
    (re.compile('<='), r'\<le>'),
    (re.compile(r" \\\\ "), " `~listSubtract~` "),
    (re.compile(r"(\s\w+)\s*@\s*\w+\s*{\s*}\s*\<leftarrow>"),
     r"\1 \<leftarrow>"),
]

ext_regexes = [
    (re.compile(r"(\s[A-Z]\w*)\s*{"), r"\1_ \<lparr>", re.compile(r"(\w)\s*="),
     r"\1="),
    (re.compile(r"(\([A-Z]\w*)\s*{"), r"\1_ \<lparr>", re.compile(r"(\w)\s*="),
     r"\1="),
    (re.compile(r"{([^={<]*[^={<:])=([^={<]*)\\<rparr>"),
     r"\<lparr>\1:=\2\<rparr>",
     re.compile(r"THIS SHOULD NOT APPEAR IN THE SOURCE"), ""),
    (re.compile(r"{"), r"\<lparr>", re.compile(r"([^=:])=(\s|$|\w)"),
     r"\1:=\2"),
]

leading_bar = re.compile(r"\s*\|")

type_assertion = re.compile(r"\(([^(]*)::([^)]*)\)")


def run_regexes(xxx_todo_changeme6, _regexes=regexes):
    (line, children) = xxx_todo_changeme6
    for re, s in _regexes:
        line = re.sub(s, line)
    children = [run_regexes(elt, _regexes=_regexes) for elt in children]
    return ((line, children))


def run_ext_regexes(xxx_todo_changeme7):
    (line, children) = xxx_todo_changeme7
    for re, s, add_re, add_s in ext_regexes:
        m = re.search(line)
        if m is None:
            continue
        before = line[:m.start()]
        substituted = m.expand(s)
        after = line[m.end():]
        add = [(add_re, add_s)]
        (after, children) = run_regexes((after, children), _regexes=add)
        line = before + substituted + after
    children = [run_ext_regexes(elt) for elt in children]
    return (line, children)


def get_case_lhs(lhs):
    assert lhs.startswith('case \\x of ')
    lhs = lhs.split('case \\x of ', 1)[1]
    cases = lhs.split('->')
    cases = [case.strip() for case in cases]
    cases = [case for case in cases if case != '']
    cases = tuple(cases)

    return cases


def get_case_rhs(rhs):
    tuples = []
    while '->' in rhs:
        bits = rhs.split('->', 1)
        s = bits[0]
        bits = bits[1].split(None, 1)
        n = int(takeWhile(bits[0], lambda x: x.isdigit())) - 1
        if len(bits) > 1:
            rhs = bits[1]
        else:
            rhs = ''
        tuples.append((s, n))
    if rhs != '':
        tuples.append((rhs, None))

    conv = []
    for (string, num) in tuples:
        bits = string.split('\\n')
        bits = [bit.strip() for bit in bits]
        conv.extend([(bit, None) for bit in bits[:-1]])
        conv.append((bits[-1], num))

    conv = [(s, n) for (s, n) in conv if s != '' or n is not None]

    if conv[0][1] is not None:
        error(f'{repr(conv[0][1])}\n'
              f'For technical reasons the first line of this case conversion must be split with \\n:\n'
              f'  {repr(rhs)}\n'
              f'(further notes: the rhs of each caseconv must have multiple lines\n'
              f'and the first cannot contain any ->1, ->2 etc.)\n', filename)
        sys.exit(1)

    # this is a tad dodgy, but means that case_clauses_transform
    # can be safely run twice on the same input
    if conv[0][0].endswith('of'):
        conv[0] = (conv[0][0] + ' ', conv[0][1])

    return conv


def render_caseconv(cases, conv, f):
    bits = [bit for bit in conv.split('\\n') if bit != '']
    assert bits
    casestr = 'case \\x of ' + ' -> '.join(cases) + ' -> '
    f.write('%s --->' % casestr)
    for bit in bits:
        f.write(bit)
        f.write('\n')
    f.write('\n')


def get_case_conv_table():
    f = open('caseconvs')
    f2 = open('caseconvs-useful', 'w')
    result = {}
    input = map(str.rstrip, f)
    input = ("\\n".join(lines) for lines in splitList(input, lambda s: s == ''))

    for line in input:
        if line.strip() == '':
            continue
        try:
            if '---X>' in line:
                [from_case, _] = line.split('---X>')
                cases = get_case_lhs(from_case)
                result[cases] = "<X>"
            else:
                [from_case, to_case] = line.split('--->')
                cases = get_case_lhs(from_case)
                conv = get_case_rhs(to_case)
                result[cases] = conv
                if (not all_constructor_patterns(cases) and
                        not is_extended_pattern(cases)):
                    render_caseconv(cases, to_case, f2)
        except Exception as e:
            error(f'error parsing {repr(line)}\n {e}', 'caseconvs')
            sys.exit(1)

    f.close()
    f2.close()

    return result


def all_constructor_patterns(cases):
    if cases[-1].strip() == '_':
        cases = cases[:-1]
    for pat in cases:
        if not is_constructor_pattern(pat):
            return False
    return True


def is_constructor_pattern(pat):
    """A constructor pattern takes the form Cons var1 var2 ...,
        characterised by all alphanumeric names, the constructor starting
        with an uppercase alphabetic char and the vars with lowercase."""
    bits = pat.split()
    for bit in bits:
        if (not bit.isalnum()) and (not bit == '_'):
            return False
    if not bits[0][0].isupper():
        return False
    for bit in bits[1:]:
        if (not bit[0].islower()) and (not bit == '_'):
            return False
    return True


ext_checker = re.compile(r"^(\(|\)|,|{|}|=|[a-zA-Z][0-9']?|\s|_|:|\[|\])*$")


def is_extended_pattern(cases):
    for case in cases:
        if not ext_checker.match(case):
            return False
    return True


case_conv_table = get_case_conv_table()
cases_added = {}


def get_case_conv(cases):
    if all_constructor_patterns(cases):
        return all_constructor_conv(cases)

    if is_extended_pattern(cases):
        return extended_pattern_conv(cases)

    return case_conv_table.get(cases)


constructor_conv_table = {
    'Just': 'Some',
    'Nothing': 'None',
    'Left': 'Inl',
    'Right': 'Inr',
    'PPtr': r'\<comment> \<open>PPtr\<close>',
    'Register': r'\<comment> \<open>Register\<close>',
    'Word': r'\<comment> \<open>Word\<close>',
}

unique_ids_per_file = {}


def get_next_unique_id():
    id = unique_ids_per_file.get(filename, 1)
    unique_ids_per_file[filename] = id + 1
    return id


def all_constructor_conv(cases):
    conv = [('case \\x of', None)]

    for i, pat in enumerate(cases):
        bits = pat.split()
        if bits[0] in constructor_conv_table:
            bits[0] = constructor_conv_table[bits[0]]
        for j, bit in enumerate(bits):
            if j > 0 and bit == '_':
                bits[j] = 'v%d' % get_next_unique_id()
        pat = ' '.join(bits)
        if i == 0:
            conv.append(('  %s \\<Rightarrow> ' % pat, i))
        else:
            conv.append(('| %s \\<Rightarrow> ' % pat, i))
    return conv


word_getter = re.compile(r"([a-zA-Z0-9]+)")

record_getter = re.compile(r"([a-zA-Z0-9]+\s*{[a-zA-Z0-9'\s=\,_\(\):\]\[]*})")


def extended_pattern_conv(cases):
    conv = [('case \\x of', None)]

    for i, pat in enumerate(cases):
        pat = '#'.join(pat.split(':'))
        while record_getter.search(pat):
            [left, record, right] = record_getter.split(pat)
            record = reduce_record_pattern(record)
            pat = left + record + right
        if '{' in pat:
            print(pat)
        assert '{' not in pat
        bits = word_getter.split(pat)
        bits = [constructor_conv_table.get(bit, bit) for bit in bits]
        pat = ''.join(bits)
        if i == 0:
            conv.append(('  %s \\<Rightarrow> ' % pat, i))
        else:
            conv.append(('| %s \\<Rightarrow> ' % pat, i))
    return conv


def reduce_record_pattern(string):
    assert string[-1] == '}'
    string = string[:-1]
    [left, right] = string.split('{')
    cons = left.strip()
    right = braces.str(right, '(', ')')
    eqs = right.split(',')
    uses = {}
    for eq in eqs:
        eq = str(eq).strip()
        if eq:
            [left, right] = eq.split('=')
            (left, right) = (left.strip(), right.strip())
            if len(right.split()) > 1:
                right = '(%s)' % right
            uses[left] = right
    if cons not in all_constructor_args:
        error(f'trying to build case for {cons}\n'
              f'when reading {filename}\n'
              f'but constructor not seen yet\n'
              f'perhaps parse in different order?\n'
              f'hint: #INCLUDE_HASKELL_PREPARSE')
        sys.exit(1)
    args = all_constructor_args[cons]
    args = [uses.get(name, '_') for (name, type) in args]
    return cons + ' ' + ' '.join(args)


def subs_nums_and_x(conv, x):
    ids = []

    result = []
    for (line, num) in conv:
        line = x.join(line.split('\\x'))
        bits = line.split('\\v')
        line = bits[0]
        for bit in bits[1:]:
            bits = bit.split('\\', 1)
            n = int(bits[0])
            while n >= len(ids):
                ids.append(get_next_unique_id())
            line = line + 'v%d' % (ids[n])
            if len(bits) > 1:
                line = line + bits[1]
        result.append((line, num))

    return result


def get_supplied_transform_table():
    f = open('supplied')

    lines = [line.rstrip() for line in f]
    f.close()

    lines = [(line, n + 1) for (n, line) in enumerate(lines)]
    lines = [(line, n) for (line, n) in lines if line != '']

    for line in lines:
        if '\t' in line:
            warning('tab character in supplied')

    tree = offside_tree(lines)

    result = {}

    for line, n, children in tree:
        if ('conv:' not in line) or len(children) != 2:
            warning(f'supplied line {n} dropped')
            if 'conv:' not in line:
                warning('\t\t(token "conv:" missing)')
            if len(children) != 2:
                warning(f'\t\t({len(children)} children != 2)')
            continue

        children = discard_line_numbers(children)

        before, after = children

        before = convert_to_stripped_tuple(before[0], before[1])

        result[before] = after

    return result


def print_tree(tree, indent=0):
    for line, children in tree:
        print('\t' * indent) + line.strip()
        print_tree(children, indent + 1)


supplied_transform_table = get_supplied_transform_table()
supplied_transforms_usage = dict((
    key, 0) for key in six.iterkeys(supplied_transform_table))


def warn_supplied_usage():
    for (key, usage) in six.iteritems(supplied_transforms_usage):
        if not usage:
            warning(f'supplied conv unused: {key[0]}')


quotes_getter = re.compile('"[^"]+"')


def detect_recursion(body):
    """Detects whether any of the bodies of the definitions of this
        function recursively refer to it."""
    single_lines = [reduce_to_single_line(elt) for elt in body]
    single_lines = [''.join(quotes_getter.split(l)) for l in single_lines]
    bits = [line.split(None, 1) for line in single_lines]
    name = bits[0][0]
    assert [n for (n, _) in bits if n != name] == []
    return [body for (n, body) in bits if name in body] != []


def primrec_transform(d):
    sig = d.sig
    defn = d.defined
    body = []
    is_not_first = False
    for (l, c) in d.body:
        [(l, c)] = body_transform([(l, c)], defn, sig, nopattern=True)
        if is_not_first:
            l = "| " + l
        else:
            l = "  " + l
            is_not_first = True
        l = l.split(r'\<equiv>')
        assert len(l) == 2
        l = '= ('.join(l)
        (l, c) = remove_trailing_string('"', (l, c))
        (l, c) = add_trailing_string(')"', (l, c))
        body.append((l, c))
    d.primrec = True
    d.body = body
    return d


variable_name_regex = re.compile(r"^[a-z]\w*$")


def is_variable_name(string):
    return variable_name_regex.match(string)


def pattern_match_transform(body):
    """Converts a body containing possibly multiple definitions
        and containing pattern matches into a normal Isabelle definition
        followed by a big Haskell case expression which is resolved
        elsewhere."""
    splits = []
    for (line, children) in body:
        string = braces.str(line, '(', ')')
        while len(string.split('=')) == 1:
            if len(children) == 1:
                [(moreline, children)] = children
                string = string + ' ' + moreline.strip()
            elif children and leading_bar.match(children[0][0]):
                string = string + ' ='
                children = \
                    guarded_body_transform(children, ' = ')
            elif children and children[0][1] == []:
                (moreline, _) = children.pop(0)
                string = string + ' ' + moreline.strip()
            else:
                print()
                print(line)
                print()
                for child in children:
                    print(child)
                assert 0

        [lead, tail] = string.split('=', 1)
        bits = lead.split()
        unbraced = bits
        function = str(bits[0])
        splits.append((bits[1:], unbraced[1:], tail, children))

    common = splits[0][0][:]
    for i, term in enumerate(common):
        if term.startswith('('):
            common[i] = None
        if '@' in term:
            common[i] = None
        if term[0].isupper():
            common[i] = None

    for (bits, _, _, _) in splits[1:]:
        for i, term in enumerate(bits):
            if i >= len(common):
                print_tree(body)
            if term != common[i]:
                is_var = is_variable_name(str(term))
                if common[i] == '_' and is_var:
                    common[i] = term
                elif term != '_':
                    common[i] = None

    for i, term in enumerate(common):
        if term == '_':
            common[i] = 'x%d' % i

    blanks = [i for (i, n) in enumerate(common) if n is None]

    line = '%s ' % function
    for i, name in enumerate(common):
        if name is None:
            line = line + 'x%d ' % i
        else:
            line = line + '%s ' % name
    if blanks == []:
        print(splits)
        print(common)
    if len(blanks) == 1:
        line = line + '= case x%d of' % blanks[0]
    else:
        line = line + '= case (x%d' % blanks[0]
        for i in blanks[1:]:
            line = line + ', x%d' % i
        line = line + ') of'

    children = []
    for (bits, unbraced, tail, c) in splits:
        if len(blanks) == 1:
            l = '  %s' % unbraced[blanks[0]]
        else:
            l = '  (%s' % unbraced[blanks[0]]
            for i in blanks[1:]:
                l = l + ', %s' % unbraced[i]
            l = l + ')'
        l = l + ' -> %s' % tail
        children.append((l, c))

    return [(line, children)]


def get_lambda_body_lines(d):
    """Returns lines equivalent to the body of the function as
        a lambda expression."""
    fn = d.defined

    [(line, children)] = d.body

    line = line[1:]
    # find \<equiv> in first or 2nd line
    if r'\<equiv>' not in line and r'\<equiv>' in children[0][0]:
        (l, c) = children[0]
        children = c + children[1:]
        line = line + l
    [lhs, rhs] = line.split(r'\<equiv>', 1)
    bits = lhs.split()
    args = bits[1:]
    assert fn in bits[0]

    line = r'(\<lambda>' + ' '.join(args) + '. ' + rhs
    # lines = ['(* body of %s *)' % fn, line] + flatten_tree (children)
    lines = [line] + flatten_tree(children)
    assert (lines[-1].endswith('"'))
    lines[-1] = lines[-1][:-1] + ')'

    return lines


def add_trailing_string(s, xxx_todo_changeme8):
    (line, children) = xxx_todo_changeme8
    if children == []:
        return (line + s, children)
    else:
        modified = add_trailing_string(s, children[-1])
        return (line, children[0:-1] + [modified])


def remove_trailing_string(s, xxx_todo_changeme9, _handled=False):
    (line, children) = xxx_todo_changeme9
    if not _handled:
        try:
            return remove_trailing_string(s, (line, children), _handled=True)
        except:
            error('handling %s\n' % ((line, children), ), filename)
            raise
    if children == []:
        if not line.endswith(s):
            error('expected %r\n to end with %r' % (line, s), filename)
            assert line.endswith(s)
        n = len(s)
        return (line[:-n], [])
    else:
        modified = remove_trailing_string(s, children[-1], _handled=True)
        return (line, children[0:-1] + [modified])


def get_trailing_string(n, xxx_todo_changeme10):
    (line, children) = xxx_todo_changeme10
    if children == []:
        return line[-n:]
    else:
        return get_trailing_string(n, children[-1])


def has_trailing_string(s, xxx_todo_changeme11):
    (line, children) = xxx_todo_changeme11
    if children == []:
        return line.endswith(s)
    else:
        return has_trailing_string(s, children[-1])


def ensure_type_ordering(defs):
    typedefs = [d for d in defs if d.type == 'newtype']
    other = [d for d in defs if d.type != 'newtype']

    final_typedefs = []
    while typedefs:
        try:
            i = 0
            deps = typedefs[i].typedeps
            while 1:
                for j, term in enumerate(typedefs):
                    if term.typename in deps:
                        break
                else:
                    break
                i = j
                deps = typedefs[i].typedeps
            final_typedefs.append(typedefs.pop(i))
        except Exception as e:
            print('Exception hit ordering types:')
            for td in typedefs:
                print('  - %s' % td.typename)
            raise e

    return final_typedefs + other


def lead_ws(string):
    amount = len(string) - len(string.lstrip())
    return string[:amount]


def adjust_ws(xxx_todo_changeme12, n):
    (line, children) = xxx_todo_changeme12
    if n > 0:
        line = ' ' * n + line
    else:
        x = -n
        line = line[x:]

    return (line, [adjust_ws(child, n) for child in children])


modulename = re.compile(r"(\w+\.)+")


def perform_module_redirects(lines, call):
    return [subst_module_redirects(line, call) for line in lines]


def subst_module_redirects(line, call):
    m = modulename.search(line)
    if not m:
        return line
    module = line[m.start():m.end() - 1]
    before = line[:m.start()]
    after = line[m.end():]
    after = subst_module_redirects(after, call)
    if module in call.moduletranslations:
        module = call.moduletranslations[module]
    if module:
        return before + module + '.' + after
    else:
        return before + after
