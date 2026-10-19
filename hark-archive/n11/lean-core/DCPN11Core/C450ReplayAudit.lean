/- Axiom audit for the core C450 replay (segments with Lean replay). -/
import DCPN11Core.C450Replay.Seg23.All
import DCPN11Core.C450Replay.Seg24.All
import DCPN11Core.C450Replay.Seg25.All
import DCPN11Core.C450Replay.Seg26.All
import DCPN11Core.C450Replay.Seg27.All
import DCPN11Core.C450Replay.Seg28.All
import DCPN11Core.C450Replay.Seg29.All
import DCPN11Core.C450Replay.Seg30.All
import DCPN11Core.C450Replay.Seg31.All
import DCPN11Core.C450Replay.Seg32.All
import DCPN11Core.C450Replay.Seg33.All
import DCPN11Core.C450Replay.Seg34.All
import DCPN11Core.C450Replay.Seg35.All
import DCPN11Core.C450Replay.Seg36.All
import DCPN11Core.C450Replay.Controls
import DCPN11Core.SwitchArith
#print axioms DCPN11Core.C450Replay.validB_sound
#print axioms DCPN11Core.C450Replay.cellB_packet
#print axioms DCPN11Core.C450Replay.Seg23.all_valid
#print axioms DCPN11Core.C450Replay.Seg23.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg23.listed_ok
#print axioms DCPN11Core.C450Replay.Seg23.head_ok
#print axioms DCPN11Core.C450Replay.Seg24.all_valid
#print axioms DCPN11Core.C450Replay.Seg24.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg24.listed_ok
#print axioms DCPN11Core.C450Replay.Seg24.head_ok
#print axioms DCPN11Core.C450Replay.Seg25.all_valid
#print axioms DCPN11Core.C450Replay.Seg25.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg25.listed_ok
#print axioms DCPN11Core.C450Replay.Seg25.head_ok
#print axioms DCPN11Core.C450Replay.Seg26.all_valid
#print axioms DCPN11Core.C450Replay.Seg26.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg26.listed_ok
#print axioms DCPN11Core.C450Replay.Seg26.head_ok
#print axioms DCPN11Core.C450Replay.Seg27.all_valid
#print axioms DCPN11Core.C450Replay.Seg27.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg27.listed_ok
#print axioms DCPN11Core.C450Replay.Seg27.head_ok
#print axioms DCPN11Core.C450Replay.Seg28.all_valid
#print axioms DCPN11Core.C450Replay.Seg28.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg28.listed_ok
#print axioms DCPN11Core.C450Replay.Seg28.head_ok
#print axioms DCPN11Core.C450Replay.Seg29.all_valid
#print axioms DCPN11Core.C450Replay.Seg29.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg29.listed_ok
#print axioms DCPN11Core.C450Replay.Seg29.head_ok
#print axioms DCPN11Core.C450Replay.Seg30.all_valid
#print axioms DCPN11Core.C450Replay.Seg30.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg30.listed_ok
#print axioms DCPN11Core.C450Replay.Seg30.head_ok
#print axioms DCPN11Core.C450Replay.Seg31.all_valid
#print axioms DCPN11Core.C450Replay.Seg31.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg31.listed_ok
#print axioms DCPN11Core.C450Replay.Seg31.head_ok
#print axioms DCPN11Core.C450Replay.Seg32.all_valid
#print axioms DCPN11Core.C450Replay.Seg32.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg32.listed_ok
#print axioms DCPN11Core.C450Replay.Seg32.head_ok
#print axioms DCPN11Core.C450Replay.Seg33.all_valid
#print axioms DCPN11Core.C450Replay.Seg33.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg33.listed_ok
#print axioms DCPN11Core.C450Replay.Seg33.head_ok
#print axioms DCPN11Core.C450Replay.Seg34.all_valid
#print axioms DCPN11Core.C450Replay.Seg34.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg34.listed_ok
#print axioms DCPN11Core.C450Replay.Seg34.head_ok
#print axioms DCPN11Core.C450Replay.Seg35.all_valid
#print axioms DCPN11Core.C450Replay.Seg35.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg35.listed_ok
#print axioms DCPN11Core.C450Replay.Seg35.head_ok
#print axioms DCPN11Core.C450Replay.Seg36.all_valid
#print axioms DCPN11Core.C450Replay.Seg36.tiling_ok
#print axioms DCPN11Core.C450Replay.Seg36.listed_ok
#print axioms DCPN11Core.C450Replay.Seg36.head_ok
#print axioms DCPN11Core.C450Replay.Controls.badAmp_rejected
#print axioms DCPN11Core.C450Replay.Controls.gapCell_rejected
#print axioms DCPN11Core.SwitchArith.sum_eq_total
