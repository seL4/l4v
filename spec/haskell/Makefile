#
# Copyright 2014, General Dynamics C4 Systems
#
# SPDX-License-Identifier: GPL-2.0-only
#

BOOT_MODULES = Kernel/CSpace Kernel/Thread Kernel/FaultHandler \
    Kernel/VSpace Kernel/Init Model/PSpace Object/TCB Object/CNode \
    Object/ObjectType Object/Endpoint Object/Interrupt \
    Object/Reply Object/Notification Object/IOPort/X64

BOOT_FILES=$(BOOT_MODULES:%=src/SEL4/%.lhs-boot)
CUSTOM_BOOT_FILES = src/SEL4/Object/Structures.lhs-boot

# We use the cabal executable that we installed via stack,
# and use the PATH from `stack exec` to find it.
# However, cabal refuses to run when the GHC_PACKAGE_PATH
# variable is set, so we use `stack-path` to clear
# GHC_PACKAGE_PATH first.
CABAL=stack exec -- ./stack-path cabal

CABAL_CONFIGURE=$(CABAL) v2-configure
CABAL_BUILD=$(CABAL) v2-build
CABAL_UPDATE=$(CABAL) v2-update
CABAL_INSTALL=$(CABAL) v2-install

RM_BACKUP=rm -f cabal.project.local~*

# warnings that are useless during large Haskell updates
GHC_DEV_OPTS=--ghc-options=""

all: build-arm build-riscv

# build targets by L4V_ARCH:
ARM: build-arm
ARM_HYP: build-arm-hyp-nosmmu
X64: build-x64
RISCV64: build-riscv
AARCH64: build-aarch64

sandbox: .stack-work

build-arm: sandbox $(BOOT_FILES)
	$(CABAL_CONFIGURE) --configure-option="arm-kzm" \
	    --flags="ArchArm" \
	    --builddir="dist/arm"
	$(RM_BACKUP)
	$(CABAL_BUILD) --builddir="dist/arm"

build-arm-hyp: sandbox $(BOOT_FILES) $(CUSTOM_BOOT_FILES)
	$(CABAL_CONFIGURE) --configure-option="arm-tk1" \
	    --flags="ArchArmHyp -FFI" \
	    --builddir="dist/arm-hyp"
	$(RM_BACKUP)
	$(CABAL_BUILD) --builddir="dist/arm-hyp"

build-arm-hyp-nosmmu: sandbox $(BOOT_FILES) $(CUSTOM_BOOT_FILES)
	$(CABAL_CONFIGURE) --configure-option="arm-tk1-nosmmu" \
	    --flags="ArchArmHyp -FFI" \
	    --builddir="dist/arm-hyp-nosmmu"
	$(RM_BACKUP)
	$(CABAL_BUILD) --builddir="dist/arm-hyp-nosmmu"

build-x64: sandbox $(BOOT_FILES)
	$(CABAL_CONFIGURE) --configure-option="x64-pc99" \
	    --flags="ArchX64 -FFI" \
	    --builddir="dist/x64"
	$(RM_BACKUP)
	$(CABAL_BUILD) --builddir="dist/x64"

build-riscv: sandbox $(BOOT_FILES)
	$(CABAL_CONFIGURE) --configure-option="riscv-hifive" \
	    --flags="ArchRiscV -FFI" \
	    --builddir="dist/riscv"
	$(RM_BACKUP)
	$(CABAL_BUILD) --builddir="dist/riscv"

build-aarch64: sandbox $(BOOT_FILES)
	$(CABAL_CONFIGURE) --configure-option="aarch64-tx2" \
	    --flags="ArchAArch64 -FFI" \
	    --builddir="dist/aarch64"
	$(RM_BACKUP)
	$(CABAL_BUILD) --builddir="dist/aarch64"

# We assume that if the .stack-work directory exists,
# we don't need to install ghc, cabal, nor fetch the cabal
# package database.
# We make this assumption to avoid hitting the network on
# every build.
# However, this means that if .stack-work exists, but the
# cabal package database is missing, the build will fail.

.stack-work:
	mkdir -p ~/.stack
	stack --install-ghc build cabal-install
	$(CABAL_UPDATE)

$(CUSTOM_BOOT_FILES):
	echo "never run mkhsboot for hand-crafted lhs-boot files"

%.lhs-boot: %.lhs mkhsboot.pl
	perl mkhsboot.pl -l < $< > $@

clean:
	rm -f $(BOOT_FILES)
	$(CABAL) clean

realclean:
	rm -rf $(BOOT_FILES) dist .stack-work .cabal-sandbox cabal.sandbox.config

.PHONY: all build-arm build-arm-hyp build-x64 clean sandbox realclean
