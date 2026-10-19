import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P3
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(0 : Rat),(1/2 : Rat),(0 : Rat),(1/2 : Rat)⟩
def toks : List Tok := [.S 1 (1/4 : Rat),.L (0 : Rat) (454047/524288 : Rat) (0 : Rat) (173327/1048576 : Rat),.S 2 (1/4 : Rat),.L (0 : Rat) (454047/524288 : Rat) (0 : Rat) (173327/1048576 : Rat),.S 1 (3/8 : Rat),.L (353449/1048576 : Rat) (472587/524288 : Rat) (67201/1048576 : Rat) (180473/1048576 : Rat),.L (432885/1048576 : Rat) (67553/65536 : Rat) (20583/262144 : Rat) (103349/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P3
