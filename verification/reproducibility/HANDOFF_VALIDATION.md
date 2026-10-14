<!-- SPDX-License-Identifier: MIT -->
# Agent handoff validation — 2026-10-14

The n23–25 core bundle was freshly exported from all 55 pinned inputs and
restored into a separate directory with a Unicode name. Every file SHA256
and raw length matched: 61,130,881 bytes. No mathematics was replayed here.

The exporter/restorer/inventory suite has 33 controls and passed both normal
Python and `python -O`; one symlink creation control was skipped on the local
Windows host because symlink creation is unavailable. The suite covers
missing inputs, wrong hashes and lengths, path escapes, duplicate/conflicting
entries, changed inputs during export, damaged ZIPs, unbound members,
refusal to overwrite different data and read-only migration inventory use.
Original delivery rejection controls also passed.

The global handoff index matches the declared paths, raw lengths and SHA256
in the delivery manifest. This checks declarations, not every archived byte
or mathematical obligation. GitHub CI performs the complete Git-delivery
byte check separately; external data bundles have their own pinned indexes.

Server notes and the maintained connection helper were found locally.
The configured management relay and configured direct fallback both timed
out during SSH handshake. No server research, service or database was changed.
The remote n26 file state was not verified.
