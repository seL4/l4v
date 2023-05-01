<!--
     Copyright 2024, Proofcraft Pty Ltd

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# DTS Overlays

This directory contains device tree overlay files that can be used to override
default platform parameters such as available memory regions.

The default files in the repository are all empty.

To provide an override, place a file `overlay.dts` into the respective
architecture directory, e.g. `ARM/overlay.dts`.

The l4v build system will pick up this overlay file when it generates the
kernel configuration data and preprocessed kernel code. It will rebuild proof
sessions according to their dependencies.

The `X64` build does not support overlays, and therefore does not provide a
default.
