import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P302
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(7/8 : Rat),(1 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 1 (15/16 : Rat),.S 2 (9/16 : Rat),.L (596365/524288 : Rat) (1590515/1048576 : Rat) (57105/262144 : Rat) (153273/524288 : Rat),.L (1244329/1048576 : Rat) (413189/262144 : Rat) (29809/131072 : Rat) (159459/524288 : Rat),.S 2 (9/16 : Rat),.L (625259/524288 : Rat) (1657945/1048576 : Rat) (3745/16384 : Rat) (19997/65536 : Rat),.L (1301037/1048576 : Rat) (860121/524288 : Rat) (249545/1048576 : Rat) (332385/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P302
