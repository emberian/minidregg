# Application share-issue custody and physical-root source gate

An independent Persvati warm snapshot compiled the 12 modules in the [serial verdict](verdict.log) with Lean 4.30.0. The [source manifest](source-sha256.txt) pins every checked file, including physical read guard `2c447ebb`, share delegation `36e22bc1`, approval-bound issue authoring `31584793`, structured request/plan inspection `4b47dd92`, and Host.Main `c931db5d`. The source receiver and replay dependency suffixes were recompiled after the physical-root changes.

The earlier source-publisher and share-issue images do not contain these repairs. This is a narrow source/OLean check only: no new native Host was linked, and no signed share issue or selected-source publication was accepted. The full executable must be built from a separately frozen, source-matched cut before those receiving fixtures run.
