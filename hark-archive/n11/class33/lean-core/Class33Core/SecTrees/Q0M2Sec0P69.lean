import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P69
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(25/32 : Rat),(13/16 : Rat),(1/8 : Rat),(3/16 : Rat)⟩
def toks : List Tok := [.S 2 (5/32 : Rat),.S 0 (9/4 : Rat),.L (843823/1048576 : Rat) (1004457/1048576 : Rat) (160957/1048576 : Rat) (191917/1048576 : Rat),.L (216623/262144 : Rat) (129111/131072 : Rat) (165317/1048576 : Rat) (197413/1048576 : Rat),.S 0 (9/4 : Rat),.L (860695/1048576 : Rat) (257465/262144 : Rat) (82101/524288 : Rat) (49207/262144 : Rat),.L (222101/262144 : Rat) (1063071/1048576 : Rat) (84767/524288 : Rat) (101627/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P69
