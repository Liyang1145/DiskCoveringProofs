import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P368
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(27/32 : Rat),(7/8 : Rat),(23/32 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 1 (55/64 : Rat),.S 2 (47/64 : Rat),.S 1 (109/128 : Rat),.L (1578487/1048576 : Rat) (1664267/1048576 : Rat) (304159/1048576 : Rat) (321211/1048576 : Rat),.L (1586353/1048576 : Rat) (1672533/1048576 : Rat) (38215/131072 : Rat) (322859/1048576 : Rat),.S 1 (109/128 : Rat),.L (1557/1024 : Rat) (1680479/1048576 : Rat) (153655/524288 : Rat) (81111/262144 : Rat),.L (400557/262144 : Rat) (1688745/1048576 : Rat) (154435/524288 : Rat) (326093/1048576 : Rat),.S 2 (47/64 : Rat),.S 1 (111/128 : Rat),.L (797111/524288 : Rat) (840399/524288 : Rat) (307281/1048576 : Rat) (324507/1048576 : Rat),.L (1602095/1048576 : Rat) (1689063/1048576 : Rat) (77211/262144 : Rat) (81539/262144 : Rat),.S 1 (111/128 : Rat),.L (402523/262144 : Rat) (848505/524288 : Rat) (9701/32768 : Rat) (327743/1048576 : Rat),.L (808979/524288 : Rat) (1705275/1048576 : Rat) (311995/1048576 : Rat) (329393/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P368
