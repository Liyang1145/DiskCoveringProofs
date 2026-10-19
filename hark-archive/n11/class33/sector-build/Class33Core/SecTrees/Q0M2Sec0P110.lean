import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P110
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (5/8 : Rat) (934615/1048576 : Rat) (31203/262144 : Rat) (178437/1048576 : Rat),.S 0 (3/2 : Rat),.L (763047/1048576 : Rat) (266721/262144 : Rat) (36361/262144 : Rat) (203993/1048576 : Rat),.S 1 (29/32 : Rat),.L (852877/1048576 : Rat) (1166963/1048576 : Rat) (81349/524288 : Rat) (111705/524288 : Rat),.L (442171/524288 : Rat) (599925/524288 : Rat) (10547/65536 : Rat) (229807/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P110
