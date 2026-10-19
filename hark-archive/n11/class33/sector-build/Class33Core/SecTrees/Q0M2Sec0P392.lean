import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P392
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(15/16 : Rat),(1 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (5/16 : Rat) (977219/1048576 : Rat) (62295/1048576 : Rat) (5833/32768 : Rat),.S 0 (3/2 : Rat),.L (737421/1048576 : Rat) (644383/524288 : Rat) (70265/524288 : Rat) (61787/262144 : Rat),.S 0 (7/4 : Rat),.L (1007459/1048576 : Rat) (1408517/1048576 : Rat) (12031/65536 : Rat) (270613/1048576 : Rat),.S 2 (9/16 : Rat),.L (568879/524288 : Rat) (1463309/1048576 : Rat) (217735/1048576 : Rat) (281395/1048576 : Rat),.L (589435/524288 : Rat) (1511365/1048576 : Rat) (56431/262144 : Rat) (72719/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P392
