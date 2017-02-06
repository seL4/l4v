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
    Object/ObjectType Object/Endpoint Object/Interrupt

BOOT_FILES=$(BOOT_MODULES:%=src/SEL4/%.lhs-boot)
CUSTOM_BOOT_FILES = src/SEL4/Object/Structures.lhs-boot

# We use the cabal executable that we installed via stack,
# and use the PATH from `stack exec` to find it.
# However, cabal refuses to run when the GHC_PACKAGE_PATH
# variable is set, so we use `stack-path` to clear
# GHC_PACKAGE_PATH first.
CABAL=stack exec -- ./stack-path cabal

# these warnings are useless during large Haskell updates
GHC_DEV_OPTS=--ghc-options="-fno-warn-unused-matches -fno-warn-unused-imports"

all: build-arm-hyp-nosmmu
# original value: build-arm pdf

sandbox: .stack-work
	$(CABAL) sandbox init
	$(CABAL) install --dependencies-only

build-arm: sandbox $(BOOT_FILES)
	$(CABAL) configure --configure-option="arm-kzm" \
	    --flags="ArchArm" \
	    --builddir="dist/arm"
	$(CABAL) build --builddir="dist/arm"

build-arm-hyp: sandbox $(BOOT_FILES) $(CUSTOM_BOOT_FILES)
	$(CABAL) configure --configure-option="arm-tk1" \
	    --flags="ArchArmHyp -FFI" $(GHC_DEV_OPTS) \
	    --builddir="dist/arm-hyp"
	$(CABAL) build --builddir="dist/arm-hyp"

build-arm-hyp-nosmmu: sandbox $(BOOT_FILES) $(CUSTOM_BOOT_FILES)
	$(CABAL) configure --configure-option="arm-tk1-nosmmu" \
	    --flags="ArchArmHyp -FFI" $(GHC_DEV_OPTS) \
	    --builddir="dist/arm-hyp-nosmmu"
	$(CABAL) build --builddir="dist/arm-hyp-nosmmu"

pdf:
	cd doc && make

# We assume that if the .stack-work directory exists,
# we don't need to install ghc, cabal, nor fetch the cabal
# package database.
# We make this assumption to avoid hitting the network on
# every build.
# However, this means that if .stack-work exists, but the
# cabal package database is missing, the build will fail.

.stack-work:
	stack --install-ghc build cabal-install
	$(CABAL) update

$(CUSTOM_BOOT_FILES):
	echo "never run mkhsboot for hand-crafted lhs-boot files"

%.lhs-boot: %.lhs mkhsboot.pl
	perl mkhsboot.pl -l < $< > $@

clean:
	rm -f $(BOOT_FILES)
	$(CABAL) clean

realclean:
	rm -rf $(BOOT_FILES) dist .stack-work .cabal-sandbox cabal.sandbox.config

.PHONY: all build build-arm-hyp pdf clean sandbox realclean
