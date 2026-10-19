import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P369
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(7/8 : Rat),(15/16 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (1/4 : Rat) (230221/262144 : Rat) (24913/524288 : Rat) (175791/1048576 : Rat),.S 0 (3/2 : Rat),.L (689957/1048576 : Rat) (614383/524288 : Rat) (131435/1048576 : Rat) (235439/1048576 : Rat),.S 0 (7/4 : Rat),.L (239245/262144 : Rat) (1346359/1048576 : Rat) (182749/1048576 : Rat) (258417/1048576 : Rat),.S 2 (9/16 : Rat),.L (1082247/1048576 : Rat) (1400071/1048576 : Rat) (25871/131072 : Rat) (268953/1048576 : Rat),.L (140623/131072 : Rat) (1448717/1048576 : Rat) (215255/1048576 : Rat) (34815/131072 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P369
