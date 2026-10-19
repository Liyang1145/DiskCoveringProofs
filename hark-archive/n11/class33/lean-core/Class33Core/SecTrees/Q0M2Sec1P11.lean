import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P11
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(1 : Rat),(2 : Rat),(1/2 : Rat),(3/4 : Rat),(0 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 1 (5/8 : Rat),.S 2 (1/8 : Rat),.L (3/8 : Rat) (853067/1048576 : Rat) (37387/524288 : Rat) (10171/65536 : Rat),.S 0 (3/2 : Rat),.L (356241/1048576 : Rat) (394141/524288 : Rat) (16933/262144 : Rat) (9393/65536 : Rat),.L (53357/131072 : Rat) (906819/1048576 : Rat) (81183/1048576 : Rat) (173081/1048576 : Rat),.S 2 (1/8 : Rat),.S 1 (11/16 : Rat),.L (1/2 : Rat) (115091/131072 : Rat) (99765/1048576 : Rat) (175761/1048576 : Rat),.L (9/16 : Rat) (988103/1048576 : Rat) (112281/1048576 : Rat) (94379/524288 : Rat),.S 1 (11/16 : Rat),.S 0 (3/2 : Rat),.L (476817/1048576 : Rat) (853847/1048576 : Rat) (22677/262144 : Rat) (81443/524288 : Rat),.L (544497/1048576 : Rat) (974721/1048576 : Rat) (103623/1048576 : Rat) (93087/524288 : Rat),.S 0 (3/2 : Rat),.L (269473/524288 : Rat) (919407/1048576 : Rat) (102563/1048576 : Rat) (87753/524288 : Rat),.L (302695/524288 : Rat) (1042319/1048576 : Rat) (14407/131072 : Rat) (99619/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P11
