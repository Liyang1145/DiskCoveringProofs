import Class33Core.SecTrees.Q0M2Sec2Base
namespace Class33Core.SecTrees.Q0M2Sec2.P113
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec2
def box : Box := ⟨(19/8 : Rat),(5/2 : Rat),(7/8 : Rat),(15/16 : Rat),(7/8 : Rat),(15/16 : Rat)⟩
def toks : List Tok := [.S 0 (39/16 : Rat),.S 1 (29/32 : Rat),.S 2 (29/32 : Rat),.L (105231/65536 : Rat) (1803519/1048576 : Rat) (81271/262144 : Rat) (174541/524288 : Rat),.L (856749/524288 : Rat) (917609/524288 : Rat) (82759/262144 : Rat) (355461/1048576 : Rat),.S 2 (29/32 : Rat),.L (856749/524288 : Rat) (917609/524288 : Rat) (82759/262144 : Rat) (355461/1048576 : Rat),.S 0 (77/32 : Rat),.L (1753285/1048576 : Rat) (1844755/1048576 : Rat) (169499/524288 : Rat) (357383/1048576 : Rat),.L (1763959/1048576 : Rat) (463949/262144 : Rat) (170569/524288 : Rat) (179805/524288 : Rat),.S 1 (29/32 : Rat),.S 2 (29/32 : Rat),.L (1703469/1048576 : Rat) (911997/524288 : Rat) (41129/131072 : Rat) (353201/1048576 : Rat),.L (1733621/1048576 : Rat) (928017/524288 : Rat) (83765/262144 : Rat) (179829/524288 : Rat),.S 2 (29/32 : Rat),.L (1733621/1048576 : Rat) (928017/524288 : Rat) (83765/262144 : Rat) (179829/524288 : Rat),.L (1764307/1048576 : Rat) (1886871/1048576 : Rat) (42651/131072 : Rat) (182943/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec2.P113
