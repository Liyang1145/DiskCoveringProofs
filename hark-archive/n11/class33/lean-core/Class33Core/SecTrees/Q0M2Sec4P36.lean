import Class33Core.SecTrees.Q0M2Sec4Base
namespace Class33Core.SecTrees.Q0M2Sec4.P36
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec4
def box : Box := ⟨(3/2 : Rat),(13/8 : Rat),(7/8 : Rat),(1 : Rat),(7/8 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 1 (15/16 : Rat),.S 2 (15/16 : Rat),.S 0 (25/16 : Rat),.L (621483/524288 : Rat) (697365/524288 : Rat) (238207/1048576 : Rat) (2093/8192 : Rat),.L (40115/32768 : Rat) (719153/524288 : Rat) (246153/1048576 : Rat) (276471/1048576 : Rat),.S 0 (25/16 : Rat),.L (20103/16384 : Rat) (722419/524288 : Rat) (123361/524288 : Rat) (277757/1048576 : Rat),.L (1328735/1048576 : Rat) (1489711/1048576 : Rat) (63741/262144 : Rat) (286601/1048576 : Rat),.S 2 (15/16 : Rat),.S 0 (25/16 : Rat),.L (20103/16384 : Rat) (722419/524288 : Rat) (123361/524288 : Rat) (277757/1048576 : Rat),.L (1328735/1048576 : Rat) (1489711/1048576 : Rat) (63741/262144 : Rat) (286601/1048576 : Rat),.S 0 (25/16 : Rat),.L (1331749/1048576 : Rat) (1487513/1048576 : Rat) (127777/524288 : Rat) (286167/1048576 : Rat),.S 1 (31/32 : Rat),.L (343843/262144 : Rat) (754943/524288 : Rat) (33013/131072 : Rat) (36323/131072 : Rat),.L (699053/524288 : Rat) (1534001/1048576 : Rat) (134283/524288 : Rat) (295351/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec4.P36
