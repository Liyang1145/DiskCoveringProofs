import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P4
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(0 : Rat),(1/2 : Rat),(0 : Rat),(1/4 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 1 (1/8 : Rat),.S 2 (9/16 : Rat),.S 1 (1/16 : Rat),.L (7/16 : Rat) (597939/1048576 : Rat) (87263/1048576 : Rat) (14229/131072 : Rat),.L (3/8 : Rat) (542361/1048576 : Rat) (37387/524288 : Rat) (6451/65536 : Rat),.S 1 (1/16 : Rat),.L (1/2 : Rat) (663481/1048576 : Rat) (99765/1048576 : Rat) (3949/32768 : Rat),.L (7/16 : Rat) (303855/524288 : Rat) (87263/1048576 : Rat) (28925/262144 : Rat),.S 2 (9/16 : Rat),.S 1 (3/16 : Rat),.L (5/16 : Rat) (244627/524288 : Rat) (62295/1048576 : Rat) (93081/1048576 : Rat),.L (1/4 : Rat) (439515/1048576 : Rat) (24913/524288 : Rat) (83597/1048576 : Rat),.S 1 (3/16 : Rat),.L (3/8 : Rat) (277041/524288 : Rat) (37387/524288 : Rat) (52727/524288 : Rat),.L (5/16 : Rat) (503281/1048576 : Rat) (62295/1048576 : Rat) (95757/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P4
