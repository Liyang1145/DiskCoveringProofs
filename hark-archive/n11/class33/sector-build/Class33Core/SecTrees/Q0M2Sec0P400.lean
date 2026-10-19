import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P400
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(9/4 : Rat),(15/16 : Rat),(1 : Rat),(9/16 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 0 (17/8 : Rat),.S 1 (31/32 : Rat),.L (1300929/1048576 : Rat) (1512251/1048576 : Rat) (62381/262144 : Rat) (291051/1048576 : Rat),.L (664793/524288 : Rat) (1543959/1048576 : Rat) (255131/1048576 : Rat) (297321/1048576 : Rat),.S 1 (31/32 : Rat),.S 2 (19/32 : Rat),.L (677077/524288 : Rat) (1523415/1048576 : Rat) (259943/1048576 : Rat) (293257/1048576 : Rat),.L (690261/524288 : Rat) (1551305/1048576 : Rat) (132557/524288 : Rat) (298775/1048576 : Rat),.S 2 (19/32 : Rat),.L (345979/262144 : Rat) (97203/65536 : Rat) (66445/262144 : Rat) (74889/262144 : Rat),.L (1410085/1048576 : Rat) (791523/524288 : Rat) (33865/131072 : Rat) (305065/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P400
