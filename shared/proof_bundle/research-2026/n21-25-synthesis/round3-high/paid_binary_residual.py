"""Independent fixed-record reader and full external-merge equality audit."""
from pathlib import Path
from heapq import heappush, heappop
import json
import struct
from stream_catalog import no_duplicate_keys

assert __debug__


class BinaryRows:
    def __init__(self, path, *, run=False):
        self.path = Path(path)
        assert not str(self.path).endswith(".building")
        self.stream = self.path.open("rb")
        assert self.stream.read(8) == (b"PAIDRUN1" if run else b"PAIDRSV1")
        size = 20 if run else 24
        fixed = self.stream.read(size)
        assert len(fixed) == size
        if run:
            N, B, F, count = struct.unpack("<IIIQ", fixed)
            self.header = {"N": N, "B": B, "orbits": count}
        else:
            N, B, F, length, count = struct.unpack("<IIIIQ", fixed)
            assert 0 < length <= 64*(1 << 20)
            metadata = self.stream.read(length)
            assert len(metadata) == length
            self.header = json.loads(metadata.decode("ascii"), object_pairs_hook=no_duplicate_keys)
            assert (self.header["N"], self.header["B"]) == (N, B)
            assert self.header["schema"] == "paid-peeling-residual-binary-v1"
            assert self.header["complete"] is False and self.header["residual_complete"] is True
            payments = self.header["proof_payments"]
            assert len({row["obstacle"] for row in payments}) == len(payments)
            assert all(type(row["pruned_recursive_states"]) is int and row["pruned_recursive_states"] > 0
                       for row in payments)
            assert sum(row["pruned_recursive_states"] for row in payments) == self.header["proof_prunes"]
            assert "orbits" not in self.header
            self.header["orbits"] = count
        assert 3 <= B <= N <= 25 and F == 2*N-B-2
        self.F = F
        self.finished = False

    def rows(self):
        assert not self.finished
        previous = None
        record = struct.Struct("<"+"I"*(self.F+1))
        for index in range(self.header["orbits"]):
            block = self.stream.read(record.size)
            assert len(block) == record.size, "truncated binary residual"
            stabilizer, *faces = record.unpack(block)
            assert stabilizer > 0 and 2*self.header["B"] % stabilizer == 0
            assert faces == sorted(set(faces))
            assert all(0 < mask < 1 << self.header["N"] and mask.bit_count() == 3 for mask in faces)
            code = tuple(faces)
            assert previous is None or previous < code
            previous = code
            yield index, {"stabilizer": stabilizer, "faces": faces}
        assert not self.stream.read(1), "extra binary residual bytes"
        self.stream.close()
        self.finished = True


def verify_merge(path):
    catalogue = BinaryRows(path)
    runfolder = Path(str(path)+".runs")
    count = catalogue.header["run_count"]
    assert sorted(p.name for p in runfolder.iterdir()) == sorted(f"run-{i}.bin" for i in range(count))
    runs = [BinaryRows(runfolder / f"run-{i}.bin", run=True) for i in range(count)]
    assert all((row.header["N"], row.header["B"]) ==
               (catalogue.header["N"], catalogue.header["B"]) for row in runs)
    assert sum(run.header["orbits"] for run in runs) == catalogue.header["rows_to_runs"]
    iterators = [iter(run.rows()) for run in runs]
    heap = []
    def advance(i):
        item = next(iterators[i], None)
        if item is not None:
            _, row = item
            heappush(heap, (tuple(row["faces"]), i, row["stabilizer"]))
    for i in range(len(runs)):
        advance(i)
    outputs = iter(catalogue.rows())
    previous = None
    previous_stab = None
    seen = unique = 0
    while heap:
        code, i, stabilizer = heappop(heap)
        if code == previous:
            assert stabilizer == previous_stab
        else:
            row = next(outputs, None)
            assert row is not None
            index, actual = row
            assert index == unique and actual == {"stabilizer": stabilizer, "faces": list(code)}
            previous, previous_stab = code, stabilizer
            unique += 1
        seen += 1
        advance(i)
    assert next(outputs, None) is None and catalogue.finished and all(row.finished for row in runs)
    assert seen == catalogue.header["rows_to_runs"] and unique == catalogue.header["orbits"]
    return catalogue.header, runs
