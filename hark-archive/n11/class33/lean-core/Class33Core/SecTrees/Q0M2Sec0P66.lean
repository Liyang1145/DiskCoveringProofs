import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P66
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(3/4 : Rat),(25/32 : Rat),(1/8 : Rat),(3/16 : Rat)⟩
def toks : List Tok := [.S 2 (5/32 : Rat),.S 0 (9/4 : Rat),.L (405851/524288 : Rat) (971569/1048576 : Rat) (4837/32768 : Rat) (92783/524288 : Rat),.L (834315/1048576 : Rat) (999821/1048576 : Rat) (159129/1048576 : Rat) (191021/1048576 : Rat),.S 0 (9/4 : Rat),.L (828819/1048576 : Rat) (124625/131072 : Rat) (158073/1048576 : Rat) (47619/262144 : Rat),.L (856427/1048576 : Rat) (257493/262144 : Rat) (163381/1048576 : Rat) (196849/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P66
