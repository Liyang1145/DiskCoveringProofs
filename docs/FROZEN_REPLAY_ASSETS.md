<!-- SPDX-License-Identifier: MIT -->
# Frozen replay inputs / 冻结复现输入

The [replay asset release](https://github.com/Liyang1145/DiskCoveringProofs/releases/tag/proof-assets-replay-20261014)
supplements the earlier core/source release. Every available bundle has a
repository-pinned package index. Download availability is recorded in
`PROJECT_STATE.json`; do not treat an index awaiting upload confirmation as a
completed public delivery.

## n11 generator inputs and gate evidence

`assets/replay/n11-supplement/PACKAGES.json` binds three C450 generator inputs,
the captured 680-row driver result and the corresponding original logs and
wrapper receipts: 1,364 files, 636,941,175 raw bytes. Together with the earlier
2,383-file source snapshot, this supports regenerating and inspecting the
already-emitted C450 modules. Historical auxiliary probes are outside this
supplement.

```sh
make restore-n11-supplement
```

The receipts are **source-reported gate outcomes**, not new full-root
acceptance. All 680 wrapper receipts have null per-module source hash fields;
they do not establish a source binding at build time. The source snapshot is
separately pinned. No Lean execution was performed during packaging, and the
last accepted C450/energy/class credits remain unchanged. See the bundle
`PROFILE.json` and rebuild/audit the actual root before upgrading any credit.

## n21 and n22 frozen snapshots

The selected set is the union of the authoritative n21/n22 snapshot `files`
maps, plus those two snapshots themselves: 990,409 files. It preserves the
written proofs, exact inputs and the snapshot-bound historical prerequisites;
it is not claimed to be a mathematically proved minimum input set. A 1 GiB
raw budget is used because one required JSON exceeds 512 MiB. Raising this
packaging budget does not modify the file or any mathematical inequality.

```sh
make restore-replay-n21-n22
```

The exact package index and confirmed availability are installed after the
complete export and release digest checks. Discovery history outside the
snapshots, compiler caches and unrelated workspace contents are not selected.

## n23 through n25 complete migrated frozen union

`assets/replay/n23-n25-full/PACKAGES.json` binds 1,020,085 files,
66,482,183,809 raw bytes in 260 packages, totaling 8,646,763,961 archive bytes.
This reuses 252 original migration ZIPs (898,000 files) and eight supplemental
ZIPs for 121,463 local-copy and 622 metadata files. The entire migrated union
has been preserved rather than guessing that large native runs, catalogues or
archive-only members are disposable caches.

```sh
make restore-replay-n23-n25
```

The original ZIPs have one auxiliary `ASSET-MANIFEST.jsonl` member. The index
explicitly binds its length and SHA256; the restorer checks it, does not extract
it, and still rejects every undeclared member. Asset members remain subject to
the complete frozen file ledger. The original package bytes are unchanged.
`SERVER-PACKAGE-AUDIT.json` records fresh archive/member hashes and raw/decoded
credential-shape scanning; it records no mathematical replay.

Files restore beneath `<destination>/assets/<canonical>`. Original Windows/WSL
references in certificates remain unchanged. Use the explicit roots in
`ORIGINAL-PATH-MAP.json` to develop a relocation wrapper; byte restoration by
itself does not make every old process/PID-based finalizer portable. Mathematical
replay must recompute the bearing conditions, not consume old accepted flags.

The two large order groups contain approximately 73 GB of original file
contents altogether, plus cache and filesystem overhead when downloaded and
restored. Restore the order group needed for the selected task. These are
frozen proof inputs, not the entire historical 100 GB-scale workspace.

## Remaining scope

n26's server was unreachable through the provided connection helper. Its
frozen arithmetic export seed remains published; the complete remote asset set
and any newer progress were not obtained. File distribution never discharges
its remaining mathematical obligations. Archived sources retain their existing
rights and provenance; the new wrapper's MIT grant does not relicense them.
