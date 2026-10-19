import Class33Core.SecTrees.Q0M2Sec6Base
namespace Class33Core.SecTrees.Q0M2Sec6.P67
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec6
def box : Box := ⟨(2 : Rat),(17/8 : Rat),(7/8 : Rat),(15/16 : Rat),(7/8 : Rat),(15/16 : Rat)⟩
def toks : List Tok := [.S 0 (33/16 : Rat),.S 1 (29/32 : Rat),.S 2 (29/32 : Rat),.L (95671/65536 : Rat) (411281/262144 : Rat) (18419/65536 : Rat) (317399/1048576 : Rat),.L (1557831/1048576 : Rat) (1674199/1048576 : Rat) (150033/524288 : Rat) (323191/1048576 : Rat),.S 2 (29/32 : Rat),.L (1557831/1048576 : Rat) (1674199/1048576 : Rat) (150033/524288 : Rat) (323191/1048576 : Rat),.L (1585405/1048576 : Rat) (1701831/1048576 : Rat) (305531/1048576 : Rat) (164353/524288 : Rat),.S 1 (29/32 : Rat),.S 2 (29/32 : Rat),.L (1560195/1048576 : Rat) (837815/524288 : Rat) (150267/524288 : Rat) (323477/1048576 : Rat),.L (1587811/1048576 : Rat) (1705209/1048576 : Rat) (306009/1048576 : Rat) (82345/262144 : Rat),.S 2 (29/32 : Rat),.L (1587811/1048576 : Rat) (1705209/1048576 : Rat) (306009/1048576 : Rat) (82345/262144 : Rat),.S 0 (67/32 : Rat),.L (811643/524288 : Rat) (213787/131072 : Rat) (156527/524288 : Rat) (330397/1048576 : Rat),.L (819071/524288 : Rat) (862831/524288 : Rat) (39501/131072 : Rat) (333469/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec6.P67
