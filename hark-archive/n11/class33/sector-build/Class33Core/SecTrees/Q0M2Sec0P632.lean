import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P632
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(3/4 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/16 : Rat) (1010361/1048576 : Rat) (3113/262144 : Rat) (96529/524288 : Rat),.S 0 (3/2 : Rat),.L (405869/524288 : Rat) (708727/524288 : Rat) (154791/1048576 : Rat) (272369/1048576 : Rat),.S 0 (7/4 : Rat),.L (1168629/1048576 : Rat) (1568879/1048576 : Rat) (223733/1048576 : Rat) (18891/65536 : Rat),.S 2 (13/16 : Rat),.L (1314151/1048576 : Rat) (1662715/1048576 : Rat) (126055/524288 : Rat) (160451/524288 : Rat),.L (170321/131072 : Rat) (1715207/1048576 : Rat) (32699/131072 : Rat) (165689/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P632
