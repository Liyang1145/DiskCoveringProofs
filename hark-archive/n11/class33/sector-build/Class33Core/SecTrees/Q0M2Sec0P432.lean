import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P432
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(9/4 : Rat),(7/8 : Rat),(15/16 : Rat),(11/16 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 0 (17/8 : Rat),.S 1 (29/32 : Rat),.L (1351037/1048576 : Rat) (1554393/1048576 : Rat) (64833/262144 : Rat) (149693/524288 : Rat),.L (689119/524288 : Rat) (198185/131072 : Rat) (132333/524288 : Rat) (305547/1048576 : Rat),.S 1 (29/32 : Rat),.S 2 (23/32 : Rat),.L (1403727/1048576 : Rat) (1573293/1048576 : Rat) (269671/1048576 : Rat) (303131/1048576 : Rat),.L (1431479/1048576 : Rat) (1602069/1048576 : Rat) (137563/524288 : Rat) (38605/131072 : Rat),.S 2 (23/32 : Rat),.L (1432367/1048576 : Rat) (1604649/1048576 : Rat) (275301/1048576 : Rat) (38669/131072 : Rat),.L (91245/65536 : Rat) (816663/524288 : Rat) (140363/524288 : Rat) (315051/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P432
