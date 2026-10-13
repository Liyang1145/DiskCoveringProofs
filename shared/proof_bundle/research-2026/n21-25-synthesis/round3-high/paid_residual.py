"""Distinct bounded-memory residual reader; ordinary full Catalog rejects it."""
from pathlib import Path
import json
from stream_catalog import Catalog, no_duplicate_keys

assert __debug__


class PaidResidualCatalog(Catalog):
    def __init__(self, path):
        self.path = Path(path)
        self.stream = self.path.open(encoding="utf8")
        marker = '"survivors":['
        self.buffer = self.stream.read(1 << 20)
        while marker not in self.buffer:
            more = self.stream.read(1 << 20)
            assert more and len(self.buffer) < 64*(1 << 20), "missing/oversized residual header"
            self.buffer += more
        start = self.buffer.index(marker)
        self.header = json.loads(self.buffer[:start]+'"survivors":[]}',
                                 object_pairs_hook=no_duplicate_keys)
        self.header.pop("survivors")
        assert self.header["schema"] == "paid-peeling-residual-v1"
        assert self.header["complete"] is False and self.header["residual_complete"] is True
        assert type(self.header["orbits"]) is int and self.header["orbits"] >= 0
        assert self.header["root_degree_prune"] is True
        payments = self.header["proof_payments"]
        assert len({row["obstacle"] for row in payments}) == len(payments)
        assert all(type(row["pruned_recursive_states"]) is int and row["pruned_recursive_states"] > 0
                   for row in payments)
        assert sum(row["pruned_recursive_states"] for row in payments) == self.header["proof_prunes"]
        self.position = start+len(marker)
        self.finished = False
