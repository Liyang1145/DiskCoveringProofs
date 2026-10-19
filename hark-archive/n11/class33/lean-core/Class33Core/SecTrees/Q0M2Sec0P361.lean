import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P361
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(13/16 : Rat),(27/32 : Rat),(23/32 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 1 (53/64 : Rat),.S 2 (47/64 : Rat),.S 1 (105/128 : Rat),.L (96691/65536 : Rat) (407799/262144 : Rat) (297933/1048576 : Rat) (78657/262144 : Rat),.L (1554909/1048576 : Rat) (1639465/1048576 : Rat) (299487/1048576 : Rat) (316273/1048576 : Rat),.S 1 (105/128 : Rat),.L (781481/524288 : Rat) (1647407/1048576 : Rat) (150541/524288 : Rat) (317853/1048576 : Rat),.L (196351/131072 : Rat) (413919/262144 : Rat) (302637/1048576 : Rat) (79875/262144 : Rat),.S 2 (47/64 : Rat),.S 1 (107/128 : Rat),.L (390691/262144 : Rat) (1647733/1048576 : Rat) (301043/1048576 : Rat) (158959/524288 : Rat),.L (24541/16384 : Rat) (1656001/1048576 : Rat) (302601/1048576 : Rat) (319565/1048576 : Rat),.S 1 (107/128 : Rat),.L (789329/524288 : Rat) (1663945/1048576 : Rat) (304193/1048576 : Rat) (321147/1048576 : Rat),.L (99157/65536 : Rat) (418053/262144 : Rat) (305751/1048576 : Rat) (322795/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P361
