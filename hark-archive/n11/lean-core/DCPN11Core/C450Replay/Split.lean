/- Memory-bounded variant of `cellB` checking for cells with many packets: the expensive
   `validB` part is split over several declarations (one kernel run each). -/
import DCPN11Core.C450Replay.Kernel
namespace DCPN11Core.C450Replay

theorem cellB_intro {s : TenSeg} {c : Cell}
    (h1 : (!c.packets.isEmpty && chainB (31/50) (69/50) c.packets) = true)
    (h2 : c.packets.all (fun p => decide (p.qLo = c.q.lo) && decide (p.qHi = c.q.hi)) = true)
    (h3 : c.packets.all (validB s) = true) : cellB s c = true := by
  unfold cellB
  rw [h1, Bool.true_and, List.all_eq_true]
  intro p hp
  have a := (List.all_eq_true.mp h2) p hp
  have b := (List.all_eq_true.mp h3) p hp
  rw [a, b]
  rfl

end DCPN11Core.C450Replay
