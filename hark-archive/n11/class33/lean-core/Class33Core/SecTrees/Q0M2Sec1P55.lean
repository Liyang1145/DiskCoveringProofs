import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P55
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(1/2 : Rat),(1 : Rat),(3/4 : Rat),(13/16 : Rat),(0 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 2 (1/8 : Rat),.S 1 (25/32 : Rat),.L (5/8 : Rat) (440099/524288 : Rat) (31203/262144 : Rat) (167955/1048576 : Rat),.L (21/32 : Rat) (913047/1048576 : Rat) (131085/1048576 : Rat) (174281/1048576 : Rat),.S 1 (25/32 : Rat),.S 0 (3/4 : Rat),.L (273685/524288 : Rat) (48051/65536 : Rat) (104171/1048576 : Rat) (18319/131072 : Rat),.L (143323/262144 : Rat) (205633/262144 : Rat) (54561/524288 : Rat) (78433/524288 : Rat),.S 0 (3/4 : Rat),.L (579723/1048576 : Rat) (801219/1048576 : Rat) (55175/524288 : Rat) (38193/262144 : Rat),.L (605259/1048576 : Rat) (427449/524288 : Rat) (57615/524288 : Rat) (10193/65536 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P55
