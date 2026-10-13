"""Finite immutable slab syntax only; never certifies search exhaustion."""
from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import no_duplicate_keys

assert __debug__


def rows(path, B, slab_index):
    previous, count = None, 0
    with path.open(encoding="ascii") as stream:
        header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
        assert header == {"schema": "sorted-outer-collar-slab-v1", "N": 25, "B": B,
                          "index": slab_index, "rows": 100000, "not_a_complete_search": True}
        for index, line in enumerate(stream):
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert set(row) == {"centers", "faces"}
            centers, faces = row["centers"], row["faces"]
            assert type(centers) is int and B <= centers < 25
            assert faces and faces == sorted(set(faces))
            assert all(type(m) is int and 0 < m < 1 << centers and m.bit_count() == 3
                       and m & ((1 << B)-1) for m in faces)
            used = 0
            for mask in faces:
                used |= mask
            assert used == (1 << centers)-1
            code = tuple(faces)
            assert previous is None or previous < code
            previous = code
            count += 1
            yield index, row
    assert count == header["rows"]


def ledger_header(N, B, slab_index):
    assert N == 25 and B in (15, 16, 17)
    return {"schema": "finite-origin-slab-sparse-partition-ledger-v1",
            "N": N, "B": B, "slab_index": slab_index,
            "not_a_complete_competitor_family_or_union": True}
