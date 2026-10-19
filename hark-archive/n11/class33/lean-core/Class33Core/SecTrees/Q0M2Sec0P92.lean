import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P92
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(0 : Rat),(1/16 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (13/16 : Rat) (1014951/1048576 : Rat) (162523/1048576 : Rat) (193945/1048576 : Rat),.S 1 (29/32 : Rat),.L (13/16 : Rat) (1057937/1048576 : Rat) (162523/1048576 : Rat) (50565/262144 : Rat),.L (27/32 : Rat) (1090889/1048576 : Rat) (42207/262144 : Rat) (208643/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P92
