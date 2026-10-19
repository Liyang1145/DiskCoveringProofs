import Class33Core.SecTrees.Q0M2Sec3Base
namespace Class33Core.SecTrees.Q0M2Sec3.P5
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec3
def box : Box := ⟨(0 : Rat),(1 : Rat),(1/4 : Rat),(1/2 : Rat),(1/2 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (1/2 : Rat),.S 2 (3/4 : Rat),.L (0 : Rat) (614565/1048576 : Rat) (0 : Rat) (117011/1048576 : Rat),.S 2 (7/8 : Rat),.L (1/4 : Rat) (741245/1048576 : Rat) (24913/524288 : Rat) (8829/65536 : Rat),.L (3/8 : Rat) (217307/262144 : Rat) (37387/524288 : Rat) (41461/262144 : Rat),.S 2 (3/4 : Rat),.S 0 (3/4 : Rat),.L (90805/524288 : Rat) (707523/1048576 : Rat) (2157/65536 : Rat) (134801/1048576 : Rat),.L (66949/262144 : Rat) (815299/1048576 : Rat) (50901/1048576 : Rat) (38869/262144 : Rat),.S 2 (7/8 : Rat),.S 0 (3/4 : Rat),.L (21487/65536 : Rat) (832361/1048576 : Rat) (32681/524288 : Rat) (158755/1048576 : Rat),.L (209935/524288 : Rat) (470187/524288 : Rat) (19963/262144 : Rat) (44887/262144 : Rat),.S 0 (3/4 : Rat),.L (460801/1048576 : Rat) (958865/1048576 : Rat) (43827/524288 : Rat) (91557/524288 : Rat),.L (529263/1048576 : Rat) (533445/524288 : Rat) (50357/524288 : Rat) (101997/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec3.P5
