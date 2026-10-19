import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P488
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(9/4 : Rat),(19/8 : Rat),(3/4 : Rat),(13/16 : Rat),(3/4 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 2 (13/16 : Rat),.S 1 (25/32 : Rat),.S 0 (37/16 : Rat),.L (1404991/1048576 : Rat) (193265/131072 : Rat) (269919/1048576 : Rat) (74437/262144 : Rat),.L (1424787/1048576 : Rat) (1567131/1048576 : Rat) (136905/524288 : Rat) (301909/1048576 : Rat),.S 0 (37/16 : Rat),.L (1433963/1048576 : Rat) (1576685/1048576 : Rat) (275615/1048576 : Rat) (303803/1048576 : Rat),.L (1454167/1048576 : Rat) (1598113/1048576 : Rat) (279593/1048576 : Rat) (154027/524288 : Rat),.S 1 (25/32 : Rat),.S 0 (37/16 : Rat),.L (182841/131072 : Rat) (201049/131072 : Rat) (281279/1048576 : Rat) (310095/1048576 : Rat),.L (1483327/1048576 : Rat) (25471/16384 : Rat) (71335/262144 : Rat) (157209/524288 : Rat),.S 0 (37/16 : Rat),.L (373129/262144 : Rat) (818871/524288 : Rat) (287153/1048576 : Rat) (157965/524288 : Rat),.S 2 (27/32 : Rat),.L (1513545/1048576 : Rat) (1628505/1048576 : Rat) (145653/524288 : Rat) (78523/262144 : Rat),.L (1542725/1048576 : Rat) (829979/524288 : Rat) (74269/262144 : Rat) (320353/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P488
