import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P53
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(0 : Rat),(1/2 : Rat),(7/8 : Rat),(15/16 : Rat),(1/8 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 0 (1/4 : Rat),.S 1 (29/32 : Rat),.S 2 (3/16 : Rat),.L (11/16 : Rat) (206573/262144 : Rat) (68681/524288 : Rat) (157589/1048576 : Rat),.L (5/8 : Rat) (763917/1048576 : Rat) (31203/262144 : Rat) (36403/262144 : Rat),.S 2 (3/16 : Rat),.L (23/32 : Rat) (53689/65536 : Rat) (143645/1048576 : Rat) (163881/1048576 : Rat),.L (21/32 : Rat) (99575/131072 : Rat) (131085/1048576 : Rat) (151885/1048576 : Rat),.S 2 (3/16 : Rat),.L (725999/1048576 : Rat) (219907/262144 : Rat) (34585/262144 : Rat) (83923/524288 : Rat),.L (663757/1048576 : Rat) (826037/1048576 : Rat) (126419/1048576 : Rat) (39385/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P53
