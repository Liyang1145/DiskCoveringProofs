import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P495
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(25/32 : Rat),(13/16 : Rat),(3/4 : Rat),(13/16 : Rat)⟩
def toks : List Tok := [.S 2 (25/32 : Rat),.S 1 (51/64 : Rat),.S 2 (49/64 : Rat),.L (773777/524288 : Rat) (819405/524288 : Rat) (298031/1048576 : Rat) (158071/524288 : Rat),.L (1563503/1048576 : Rat) (413757/262144 : Rat) (150595/524288 : Rat) (319371/1048576 : Rat),.S 2 (49/64 : Rat),.L (195401/131072 : Rat) (206919/131072 : Rat) (301131/1048576 : Rat) (319435/1048576 : Rat),.L (789573/524288 : Rat) (835785/524288 : Rat) (152145/524288 : Rat) (322667/1048576 : Rat),.S 1 (51/64 : Rat),.S 2 (51/64 : Rat),.L (1579377/1048576 : Rat) (1671249/1048576 : Rat) (19021/65536 : Rat) (322603/1048576 : Rat),.L (398773/262144 : Rat) (1687791/1048576 : Rat) (153727/524288 : Rat) (162951/524288 : Rat),.S 2 (51/64 : Rat),.L (398773/262144 : Rat) (1687791/1048576 : Rat) (153727/524288 : Rat) (162951/524288 : Rat),.L (402741/262144 : Rat) (1704015/1048576 : Rat) (310605/1048576 : Rat) (164571/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P495
