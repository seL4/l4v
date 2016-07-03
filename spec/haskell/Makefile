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
# FIXME ^ VCPUs go above?

BOOT_FILES=$(BOOT_MODULES:%=src/SEL4/%.lhs-boot)

# We use the cabal executable that we installed via stack,
# and use the PATH from `stack exec` to find it.
# However, cabal refuses to run when the GHC_PACKAGE_PATH
# variable is set, so we use `stack-path` to clear
# GHC_PACKAGE_PATH first.
CABAL=stack exec -- ./stack-path cabal

#all: build pdf FIXME original
all: build-arm-hyp

build: .stack-work $(BOOT_FILES)
	$(CABAL) sandbox init
	$(CABAL) install --dependencies-only
	$(CABAL) configure --configure-option="arm-kzm" \
	    --flags="ArchArm"
	$(CABAL) build

# FIXME XXX these warnings are useless during large Haskell updates
GHC_FIXME_OPTS=--ghc-options="-fno-warn-unused-matches -fno-warn-unused-imports"

build-arm-hyp: .stack_work $(BOOT_FILES)
	$(CABAL) sandbox init
	$(CABAL) install --dependencies-only
	$(CABAL) configure --configure-option="arm-tk1" \
	    --flags="ArchArmHyp -FFI" $(GHC_FIXME_OPTS)
	$(CABAL) build

build-arm-hyp-nosmmu: $(BOOT_FILES)
	cabal sandbox init
	cabal install --dependencies-only -w "$(GHC)"
	cabal configure --configure-option="arm-tk1-nosmmu" -w "$(GHC)" \
	    --flags="ArchArmHyp -FFI" $(GHC_FIXME_OPTS)
	cabal build

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

%.lhs-boot: %.lhs mkhsboot.pl
	perl mkhsboot.pl -l < $< > $@

clean:
	rm -f $(BOOT_FILES)
	$(CABAL) clean

realclean:
	rm -rf $(BOOT_FILES) dist .stack-work .cabal-sandbox cabal.sandbox.config

.PHONY: all build build-arm-hyp pdf clean realclean
