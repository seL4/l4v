#
# Copyright 2014, General Dynamics C4 Systems
#
# This software may be distributed and modified according to the terms of
# the GNU General Public License version 2. Note that NO WARRANTY is provided.
# See "LICENSE_GPLv2.txt" for details.
#
# @TAG(GD_GPL)
#


BOOT_MODULES = Kernel/CSpace Kernel/Thread Kernel/FaultHandler \
    Kernel/VSpace Kernel/Init Model/PSpace Object/TCB Object/CNode \
	Object/ObjectType Object/Endpoint Object/Interrupt \
	Object/IOPort/X64

BOOT_FILES=$(BOOT_MODULES:%=src/SEL4/%.lhs-boot)

GHC=ghc

all: build pdf

build: $(BOOT_FILES)
	cabal sandbox init
	cabal install --dependencies-only -w $(GHC)
	cabal configure --configure-option="arm-kzm" -w $(GHC) 
	cabal build

build-x64: $(BOOT_FILES)
	cabal sandbox init
	cabal install --dependencies-only
	# FIXME: allow some warnings for now
	cabal configure --configure-option="x64-pc99" --flags="-FFI -ArchArm" --ghc-options="-fno-warn-unused-matches -fno-warn-unused-imports"

	cabal build
pdf:
	cd doc && make

%.lhs-boot: %.lhs mkhsboot.pl
	perl mkhsboot.pl -l < $< > $@

clean:
	rm -f $(BOOT_FILES)
	cabal clean

.PHONY: all build pdf clean
