"""Standard-library bounded-memory reader for the frozen C++ catalogue format."""
from pathlib import Path
import hashlib
import json

assert __debug__


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def no_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        assert key not in result
        result[key] = value
    return result


DECODER = json.JSONDecoder(object_pairs_hook=no_duplicate_keys)


class Catalog:
    def __init__(self, path):
        self.path = Path(path)
        self.stream = self.path.open("r", encoding="utf8")
        self.buffer = self.stream.read(1 << 20)
        marker = '"survivors":['
        start = self.buffer.index(marker)
        self.header = json.loads(self.buffer[:start]+'"survivors":[]}', object_pairs_hook=no_duplicate_keys)
        self.header.pop("survivors")
        assert self.header["complete"] and type(self.header["orbits"]) is int
        self.position = start+len(marker)
        self.finished = False

    def fill(self):
        more = self.stream.read(1 << 20)
        assert more, "truncated catalogue"
        self.buffer = self.buffer[self.position:]+more
        self.position = 0

    def token(self):
        while True:
            while self.position < len(self.buffer) and self.buffer[self.position].isspace():
                self.position += 1
            if self.position < len(self.buffer):
                return self.buffer[self.position]
            self.fill()

    def rows(self):
        assert not self.finished
        count = 0
        first = True
        while True:
            char = self.token()
            if not first:
                if char == "]":
                    break
                assert char == ","
                self.position += 1
                char = self.token()
                assert char != "]", "trailing comma"
            elif char == "]":
                break
            assert char == "{"
            while True:
                try:
                    row, end = DECODER.raw_decode(self.buffer, self.position)
                    self.position = end
                    break
                except json.JSONDecodeError:
                    self.fill()
            assert set(row) == {"stabilizer", "faces"}
            assert type(row["stabilizer"]) is int and row["stabilizer"] > 0
            masks = row["faces"]
            assert masks == sorted(set(masks))
            assert len(masks) == 2*self.header["N"]-self.header["B"]-2
            assert all(type(m) is int and 0 < m < (1 << self.header["N"]) and m.bit_count() == 3 for m in masks)
            yield count, row
            count += 1
            first = False
        self.position += 1
        tail = self.buffer[self.position:]+self.stream.read()
        assert tail.strip() == "}"
        assert count == self.header["orbits"], (count, self.header["orbits"])
        self.finished = True
        self.stream.close()

