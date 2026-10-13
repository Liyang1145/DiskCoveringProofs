"""N23/N24 actual-cover necessity only; not a geometric weak-graph theorem."""
from fractions import Fraction as F
from refine_collar_origin import exposed_mask, radius_gate

assert __debug__


def classify(N, B, faces, radius_upper):
    assert type(N) is int and N in (23, 24)
    assert type(B) is int and 3 <= B <= N
    U = F(radius_upper)
    gap = radius_gate(U)
    assert faces and faces == sorted(set(faces))
    mask = exposed_mask(N, B, faces)
    exposed = mask.bit_count()
    return {
        "N": N, "B": B, "radius_upper": str(U),
        "strict_gap_1_minus_4U": str(gap),
        "exposed_label_mask": mask, "exposed_centers": exposed,
        "actual_cover_obstruction": exposed == N,
        "kind": ("actual-cover-unexposed-origin-obstruction" if exposed == N else "not-paid-by-origin-condition"),
        "not_a_standalone_geometric_weak_graph_exclusion": True,
        "actual_unit_disk_cover_auxiliary_rod_interface_required": True,
    }
