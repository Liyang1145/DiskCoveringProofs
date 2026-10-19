import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P552
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(13/16 : Rat),(7/8 : Rat),(7/8 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (0 : Rat) (995371/1048576 : Rat) (0 : Rat) (95081/524288 : Rat),.S 0 (3/2 : Rat),.L (406785/524288 : Rat) (1406809/1048576 : Rat) (155143/1048576 : Rat) (270277/1048576 : Rat),.S 0 (7/4 : Rat),.L (586627/524288 : Rat) (389817/262144 : Rat) (28079/131072 : Rat) (4693/16384 : Rat),.S 2 (15/16 : Rat),.L (1314843/1048576 : Rat) (827497/524288 : Rat) (126123/524288 : Rat) (79841/262144 : Rat),.L (170321/131072 : Rat) (1715207/1048576 : Rat) (32699/131072 : Rat) (165689/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P552
