import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P359
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(13/16 : Rat),(27/32 : Rat),(11/16 : Rat),(23/32 : Rat)⟩
def toks : List Tok := [.S 1 (53/64 : Rat),.S 2 (45/64 : Rat),.S 1 (105/128 : Rat),.L (757637/524288 : Rat) (24981/16384 : Rat) (291647/1048576 : Rat) (308187/1048576 : Rat),.L (1523139/1048576 : Rat) (1607053/1048576 : Rat) (146601/524288 : Rat) (309829/1048576 : Rat),.S 1 (105/128 : Rat),.L (191395/131072 : Rat) (403747/262144 : Rat) (73697/262144 : Rat) (155703/524288 : Rat),.L (1539019/1048576 : Rat) (1623257/1048576 : Rat) (148171/524288 : Rat) (313049/1048576 : Rat),.S 2 (45/64 : Rat),.S 1 (107/128 : Rat),.L (11961/8192 : Rat) (1615321/1048576 : Rat) (147379/524288 : Rat) (19467/65536 : Rat),.L (24045/16384 : Rat) (405897/262144 : Rat) (296315/1048576 : Rat) (313115/1048576 : Rat),.S 1 (107/128 : Rat),.L (1546881/1048576 : Rat) (1631525/1048576 : Rat) (148949/524288 : Rat) (314693/1048576 : Rat),.L (777373/524288 : Rat) (1639793/1048576 : Rat) (299455/1048576 : Rat) (158169/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P359
