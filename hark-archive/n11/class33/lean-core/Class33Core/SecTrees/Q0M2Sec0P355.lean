import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P355
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(27/32 : Rat),(7/8 : Rat),(21/32 : Rat),(11/16 : Rat)⟩
def toks : List Tok := [.S 1 (55/64 : Rat),.S 2 (43/64 : Rat),.S 1 (109/128 : Rat),.L (1515067/1048576 : Rat) (49983/32768 : Rat) (145803/524288 : Rat) (308321/1048576 : Rat),.L (761479/524288 : Rat) (1607721/1048576 : Rat) (146583/524288 : Rat) (154981/524288 : Rat),.S 1 (109/128 : Rat),.L (1530905/1048576 : Rat) (1615653/1048576 : Rat) (294737/1048576 : Rat) (155769/524288 : Rat),.L (769395/524288 : Rat) (1623919/1048576 : Rat) (296297/1048576 : Rat) (313181/1048576 : Rat),.S 2 (43/64 : Rat),.S 1 (111/128 : Rat),.L (382713/262144 : Rat) (1615985/1048576 : Rat) (294727/1048576 : Rat) (77901/262144 : Rat),.L (769375/524288 : Rat) (1624249/1048576 : Rat) (296289/1048576 : Rat) (156623/524288 : Rat),.S 1 (111/128 : Rat),.L (773339/524288 : Rat) (1632183/1048576 : Rat) (148929/524288 : Rat) (39353/131072 : Rat),.L (1554569/1048576 : Rat) (1640447/1048576 : Rat) (74855/262144 : Rat) (79117/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P355
