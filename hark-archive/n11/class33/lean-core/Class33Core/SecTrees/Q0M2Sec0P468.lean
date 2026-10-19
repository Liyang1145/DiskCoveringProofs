import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P468
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(9/4 : Rat),(15/16 : Rat),(1 : Rat),(11/16 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 0 (17/8 : Rat),.S 1 (31/32 : Rat),.L (1405677/1048576 : Rat) (202079/131072 : Rat) (135027/524288 : Rat) (77933/262144 : Rat),.L (1433339/1048576 : Rat) (205981/131072 : Rat) (68873/262144 : Rat) (317941/1048576 : Rat),.S 1 (31/32 : Rat),.S 2 (23/32 : Rat),.L (1461181/1048576 : Rat) (1636059/1048576 : Rat) (140487/524288 : Rat) (315595/1048576 : Rat),.L (744269/524288 : Rat) (832321/524288 : Rat) (8949/32768 : Rat) (160643/524288 : Rat),.S 2 (23/32 : Rat),.L (745079/524288 : Rat) (833761/524288 : Rat) (8959/32768 : Rat) (80465/262144 : Rat),.L (1517325/1048576 : Rat) (424003/262144 : Rat) (292053/1048576 : Rat) (327543/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P468
