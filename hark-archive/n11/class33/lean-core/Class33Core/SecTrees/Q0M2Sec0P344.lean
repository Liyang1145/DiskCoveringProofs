import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P344
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(9/4 : Rat),(13/16 : Rat),(7/8 : Rat),(5/8 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 2 (11/16 : Rat),.S 0 (17/8 : Rat),.S 1 (27/32 : Rat),.L (1242383/1048576 : Rat) (719333/524288 : Rat) (238093/1048576 : Rat) (138271/524288 : Rat),.L (39675/32768 : Rat) (734945/524288 : Rat) (60851/262144 : Rat) (70673/262144 : Rat),.S 1 (27/32 : Rat),.L (1287589/1048576 : Rat) (743321/524288 : Rat) (246917/1048576 : Rat) (285995/1048576 : Rat),.L (1315543/1048576 : Rat) (1518591/1048576 : Rat) (126191/524288 : Rat) (18269/65536 : Rat),.S 0 (17/8 : Rat),.S 1 (27/32 : Rat),.L (1297407/1048576 : Rat) (1492437/1048576 : Rat) (62209/262144 : Rat) (287139/1048576 : Rat),.L (165511/131072 : Rat) (761689/524288 : Rat) (254055/1048576 : Rat) (146625/524288 : Rat),.S 1 (27/32 : Rat),.L (672509/524288 : Rat) (771439/524288 : Rat) (258153/1048576 : Rat) (297107/1048576 : Rat),.L (171567/131072 : Rat) (393657/262144 : Rat) (263547/1048576 : Rat) (303395/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P344
