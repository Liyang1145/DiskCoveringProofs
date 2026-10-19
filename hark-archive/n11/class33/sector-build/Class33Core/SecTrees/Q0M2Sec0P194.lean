import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P194
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(5/2 : Rat),(11/4 : Rat),(7/8 : Rat),(29/32 : Rat),(11/32 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 1 (57/64 : Rat),.S 2 (23/64 : Rat),.S 0 (21/8 : Rat),.L (298893/262144 : Rat) (653347/524288 : Rat) (114487/524288 : Rat) (250653/1048576 : Rat),.L (605987/524288 : Rat) (1317767/1048576 : Rat) (232167/1048576 : Rat) (252819/1048576 : Rat),.S 0 (21/8 : Rat),.L (1209805/1048576 : Rat) (1322447/1048576 : Rat) (3621/16384 : Rat) (126867/524288 : Rat),.L (1226749/1048576 : Rat) (1333863/1048576 : Rat) (235045/1048576 : Rat) (255969/1048576 : Rat),.S 2 (23/64 : Rat),.S 0 (21/8 : Rat),.L (1211479/1048576 : Rat) (661569/524288 : Rat) (116035/524288 : Rat) (126935/524288 : Rat),.L (306989/262144 : Rat) (667133/524288 : Rat) (14705/65536 : Rat) (16003/65536 : Rat),.S 0 (21/8 : Rat),.L (1225685/1048576 : Rat) (669445/524288 : Rat) (117419/524288 : Rat) (128477/524288 : Rat),.L (1242709/1048576 : Rat) (337591/262144 : Rat) (238157/1048576 : Rat) (259201/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P194
