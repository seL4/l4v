<!--
     Copyright 2024, Proofcraft Pty Ltd

     SPDX-License-Identifier: CC-BY-SA-4.0
-->

# DTS Overlays

This directory can be used to supply custom device tree overlay files that
override default platform parameters such as available memory regions.

Without a custom overlay, the seL4 kernel build will use an empty overlay file.

To provide an override, place a file `overlay.dts` into the respective
architecture directory, e.g. `ARM/overlay.dts`.

The l4v build system will pick up this overlay file when it generates the
kernel configuration data and preprocessed kernel code. It will rebuild proof
sessions according to their dependencies.

The `X64` build does not support overlays, so an overlay in an `X64`
subdirectory will be ignored.
