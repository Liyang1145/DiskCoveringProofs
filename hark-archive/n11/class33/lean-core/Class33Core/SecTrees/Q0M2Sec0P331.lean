import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P331
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(9/4 : Rat),(3/4 : Rat),(13/16 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 2 (11/16 : Rat),.S 0 (17/8 : Rat),.L (594395/524288 : Rat) (1407513/1048576 : Rat) (113827/524288 : Rat) (270415/1048576 : Rat),.S 1 (25/32 : Rat),.L (1232393/1048576 : Rat) (1422857/1048576 : Rat) (236145/1048576 : Rat) (34179/131072 : Rat),.L (314967/262144 : Rat) (727365/524288 : Rat) (7547/32768 : Rat) (34963/131072 : Rat),.S 0 (17/8 : Rat),.L (1244917/1048576 : Rat) (182697/131072 : Rat) (238587/1048576 : Rat) (281053/1048576 : Rat),.S 1 (25/32 : Rat),.L (322679/262144 : Rat) (739755/524288 : Rat) (30941/131072 : Rat) (71147/262144 : Rat),.L (1317739/1048576 : Rat) (1511171/1048576 : Rat) (63203/262144 : Rat) (145419/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P331
