import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P460
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(15/16 : Rat),(31/32 : Rat),(21/32 : Rat),(11/16 : Rat)⟩
def toks : List Tok := [.S 1 (61/64 : Rat),.S 2 (43/64 : Rat),.S 1 (121/128 : Rat),.L (804979/524288 : Rat) (53081/32768 : Rat) (310405/1048576 : Rat) (328059/1048576 : Rat),.L (404471/262144 : Rat) (53339/32768 : Rat) (77995/262144 : Rat) (82427/262144 : Rat),.S 1 (121/128 : Rat),.L (812861/524288 : Rat) (214349/131072 : Rat) (156769/524288 : Rat) (331295/1048576 : Rat),.L (816821/524288 : Rat) (1723049/1048576 : Rat) (315113/1048576 : Rat) (166473/524288 : Rat),.S 2 (43/64 : Rat),.S 1 (123/128 : Rat),.L (406453/262144 : Rat) (1715105/1048576 : Rat) (78389/262144 : Rat) (165679/524288 : Rat),.L (102109/65536 : Rat) (1723361/1048576 : Rat) (315133/1048576 : Rat) (333009/1048576 : Rat),.S 1 (123/128 : Rat),.L (1641565/1048576 : Rat) (865653/524288 : Rat) (316689/1048576 : Rat) (167299/524288 : Rat),.L (824745/524288 : Rat) (869781/524288 : Rat) (318267/1048576 : Rat) (336251/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P460
