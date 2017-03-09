#!/usr/bin/env python3

# Currently ARM_HYP.lhs files duplicate ARM.lhs functionality, but we are not
# sure how accurately. This script preprocesses ARM_HYP.lhs files for the "ARM"
# target ("arm-kzm") and checks for differences against an ARM.lhs in that
# directory, if one exists.
# XXX: we ignore .hs files since at the time of writing there aren't any
# interesting ones

# This is a temporary hack to aid development of Haskell files that are
# targeted at both ARM and ARM_HYP targets. In future, there should be only ARM
# files.

import os, sys
import os.path
import sh # pip install sh, apt-get install python3-sh, etc.
import tempfile
import re

target = 'ARM'
platform = 'KZM'

arm = 'ARM.lhs'
ahyp = 'ARM_HYP.lhs'

diff = sh.Command('colordiff' if os.access('/usr/bin/colordiff', os.X_OK) else 'diff')

arm_lhs_files = set(s.strip() for s in sh.find('.','-name',arm))
arm_hyp_lhs_files = set(s.strip() for s in sh.find('.','-name',ahyp))

def litfilter(lines):
    for line in lines:
        if line.startswith(b'#'):
            yield line
            continue
        m = re.match(b'^(>\s)', line)
        if not m: continue
        l2 = line.replace(m.group(1), b'', 1)
        yield(l2)

def dump_temp_lines(lines):
    outfile = tempfile.NamedTemporaryFile()
    outfile.writelines(lines)
    outfile.seek(0)
    return outfile

def preprocess(filename):

    with open(filename, 'rb') as f:
        infile = dump_temp_lines(litfilter(f.readlines()))

    outfile = tempfile.NamedTemporaryFile()
    r = sh.cpp('-undef','-Wtraditional',
               '-D__GLASGOW_HASKELL__=708','-x','assembler-with-cpp','-P',
               '-DPLATFORM='+platform, '-DTARGET='+target,
               '-DPLATFORM_'+platform, '-DTARGET_'+target,
               infile.name, o=outfile.name)
    infile.close()
    outfile.seek(0)
    return outfile

def compare_arm_and_hyp(common_path):
    path_arm = os.path.join(common_path, arm)
    path_hyp = os.path.join(common_path, ahyp)
    print('Comparing %s and %s' % (path_arm, path_hyp))

    a = preprocess(path_arm)
    h = preprocess(path_hyp)

    # now change all mentions of ".ARM_HYP" to ".ARM" to compact the diff
    # note: this will not catch an accidental .ARM import in .ARM_HYP, but that
    #       should not compile anyway
    h2 = dump_temp_lines((l.replace(b'.ARM_HYP', b'.ARM') for l in h.readlines()))

    print(diff('-w', a.name, h2.name, _ok_code=[0,1]))

    a.close()
    h.close()

# Files that are in ARM_HYP but not ARM should be ARM_HYP specific
arm_hyp_only = []
for path in sorted(arm_hyp_lhs_files):
    d, f = os.path.split(path)
    if (not os.path.exists(os.path.join(d, arm))):
        arm_hyp_only.append(os.path.join(d, arm))
if arm_hyp_only:
    print('These files appear to be ARM_HYP-specific:')
    print('\n'.join(arm_hyp_only))

print('')

# Files in ARM that are not in ARM_HYP are likely already merged
for path in sorted(arm_lhs_files):
    d, f = os.path.split(path)
    if (not os.path.exists(os.path.join(d, ahyp))):
        print('Missing or merged: %s in %s' % (ahyp, d))
        continue
    # lhs files exist for both platforms, let's compare their preprocessed versions
    compare_arm_and_hyp(d)

