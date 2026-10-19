/- Controls for the C450 core replay: one accepted-format packet passes; two perturbations
   (amplitude bound p0 lowered by 1e-6; radial hi widened by 1/100) are rejected; a cell whose
   packet chain has a gap is rejected. Data: C450Source14GroupedC01.packet0 (WIP snapshot). -/
import DCPN11Core.C450Replay.Seg14.Data
namespace DCPN11Core.C450Replay.Controls
open DCPN11Core.C450Replay
def good : Packet := ⟨((31:Rat)/50),((1011:Rat)/1600),(-1:Rat),((-15:Rat)/16),((6647749589:Rat)/10000000000),((6838750003:Rat)/10000000000),(-1:Rat),((-18279248767:Rat)/20220000000),((9929701407:Rat)/10000000000),(1:Rat),((18538009:Rat)/156250000),((5059718083:Rat)/10000000000),((774353207440902397090472377182741:Rat)/14196125000000000000000000000000000),((6987690287966325757501899:Rat)/14440000000000000000000000)⟩
def badAmp : Packet := ⟨((31:Rat)/50),((1011:Rat)/1600),(-1:Rat),((-15:Rat)/16),((6647749589:Rat)/10000000000),((6838750003:Rat)/10000000000),(-1:Rat),((-18279248767:Rat)/20220000000),((9929701407:Rat)/10000000000),(1:Rat),((18538009:Rat)/156250000),((5059718083:Rat)/10000000000),((774339011315902397090472377182741:Rat)/14196125000000000000000000000000000),((6987690287966325757501899:Rat)/14440000000000000000000000)⟩
def badHi : Packet := ⟨((31:Rat)/50),((1027:Rat)/1600),(-1:Rat),((-15:Rat)/16),((6647749589:Rat)/10000000000),((6838750003:Rat)/10000000000),(-1:Rat),((-18279248767:Rat)/20220000000),((9929701407:Rat)/10000000000),(1:Rat),((18538009:Rat)/156250000),((5059718083:Rat)/10000000000),((774353207440902397090472377182741:Rat)/14196125000000000000000000000000000),((6987690287966325757501899:Rat)/14440000000000000000000000)⟩
theorem good_ok : validB Seg14.seg good = true := by decide +kernel
theorem badAmp_rejected : validB Seg14.seg badAmp = false := by decide +kernel
theorem badHi_rejected : validB Seg14.seg badHi = false := by decide +kernel
def gapCell : Cell := ⟨⟨(-1:Rat),((-15:Rat)/16)⟩,[good]⟩
/-- a single packet [31/50,1011/1600] does not reach 69/50: chain check must fail -/
theorem gapCell_rejected : cellB Seg14.seg gapCell = false := by decide +kernel
theorem tile_gap_rejected : tileB (-1) 1 [⟨-1,0⟩, ⟨1/16,1⟩] = false := by decide +kernel
end DCPN11Core.C450Replay.Controls
