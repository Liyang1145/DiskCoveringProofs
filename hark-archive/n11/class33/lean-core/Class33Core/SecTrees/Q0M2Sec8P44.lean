import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P44
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(1 : Rat),(2 : Rat),(1/2 : Rat),(3/4 : Rat),(0 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 1 (5/8 : Rat),.S 0 (3/2 : Rat),.S 2 (1/8 : Rat),.L (3/8 : Rat) (776371/1048576 : Rat) (37387/524288 : Rat) (74001/524288 : Rat),.L (356241/1048576 : Rat) (394141/524288 : Rat) (16933/262144 : Rat) (9393/65536 : Rat),.L (1/4 : Rat) (988403/1048576 : Rat) (24913/524288 : Rat) (11801/65536 : Rat),.S 2 (1/8 : Rat),.S 0 (3/2 : Rat),.L (1/2 : Rat) (3551/4096 : Rat) (99765/1048576 : Rat) (21689/131072 : Rat),.L (1/2 : Rat) (973109/1048576 : Rat) (99765/1048576 : Rat) (185863/1048576 : Rat),.S 0 (3/2 : Rat),.S 1 (11/16 : Rat),.L (476817/1048576 : Rat) (853847/1048576 : Rat) (22677/262144 : Rat) (81443/524288 : Rat),.L (269473/524288 : Rat) (919407/1048576 : Rat) (102563/1048576 : Rat) (87753/524288 : Rat),.L (544497/1048576 : Rat) (1042319/1048576 : Rat) (103623/1048576 : Rat) (99619/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P44
