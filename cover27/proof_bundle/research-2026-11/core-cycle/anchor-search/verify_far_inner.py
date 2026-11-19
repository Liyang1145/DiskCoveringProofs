"""Verify that all thirteen inner disks stay within the fixed core norm cap."""
import argparse
import json
from pathlib import Path

from polar_tables import END, OUTER_CAPS, R, SCALE, radial_roles
from verify_expanded_core_count import LOWER
from weighted_rings import verify_weighted_rings


def verify(source):
    upper = LOWER
    for record in json.loads(source.read_text(encoding="utf-8")):
        lo,hi,count,far = (record[k] for k in ("low","high","count","far"))
        if lo!=upper or not lo<hi<=OUTER_CAPS[14] or count!=10 or far!=1:
            raise ValueError("invalid or disconnected outer-norm interval")
        core = lo-R-1000
        if not 2*R<core<lo-R:
            raise ValueError("the origin disk may meet the core circle")
        if lo-2*R<=core-R:
            raise ValueError("a boundary-adjacent center could miss the lower end of the core shell")
        classes = radial_roles(14,lo,hi,core,count)
        classes.remove((2,0,END,False))
        classes += [(1,core+R,END,False),(1,0,END,False)]
        caps = record["caps"]
        rings = record["rings"]
        if len(caps)!=len(classes) or not rings or any(not 0<s<=SCALE or w<=0 for s,w in rings):
            raise ValueError("invalid weighted radial certificate")
        cases=[(m,a,b,cap,owner) for (m,a,b,owner),cap in zip(classes,caps)]
        boxes = verify_weighted_rings(R,rings,cases)
        upper = hi
        print(f"PASS B=14: on D1 in [{lo},{hi}]/1e9, all inner norms are < {(core+R)}/1e9 ({sum(boxes)} radial boxes).")
    if upper!=OUTER_CAPS[14]:
        raise ValueError("missing top end of the norm range")
    print("PASS B=14: in each certified interval, the ten disks reaching its designated core circle include every inner neighbor of a boundary owner.")


if __name__=="__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source",type=Path)
    verify(parser.parse_args().source)
