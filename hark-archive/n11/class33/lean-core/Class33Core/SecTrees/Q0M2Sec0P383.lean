import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P383
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(7/8 : Rat),(29/32 : Rat),(9/16 : Rat),(19/32 : Rat)⟩
def toks : List Tok := [.S 1 (57/64 : Rat),.S 2 (37/64 : Rat),.S 1 (113/128 : Rat),.L (726019/524288 : Rat) (1535405/1048576 : Rat) (279173/1048576 : Rat) (73907/262144 : Rat),.L (364995/262144 : Rat) (1543665/1048576 : Rat) (140369/524288 : Rat) (297263/1048576 : Rat),.S 1 (113/128 : Rat),.L (1467773/1048576 : Rat) (1551579/1048576 : Rat) (282273/1048576 : Rat) (298829/1048576 : Rat),.L (368927/262144 : Rat) (48745/32768 : Rat) (141919/524288 : Rat) (300465/1048576 : Rat),.S 2 (37/64 : Rat),.S 1 (115/128 : Rat),.L (1467925/1048576 : Rat) (1551925/1048576 : Rat) (282303/1048576 : Rat) (149449/524288 : Rat),.L (46121/32768 : Rat) (195023/131072 : Rat) (141935/524288 : Rat) (300533/1048576 : Rat),.S 1 (115/128 : Rat),.L (1483647/1048576 : Rat) (392025/262144 : Rat) (285403/1048576 : Rat) (151051/524288 : Rat),.L (1491587/1048576 : Rat) (1576359/1048576 : Rat) (143485/524288 : Rat) (303739/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P383
