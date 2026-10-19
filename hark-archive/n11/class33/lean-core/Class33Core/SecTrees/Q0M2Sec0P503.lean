import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P503
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(2 : Rat),(13/16 : Rat),(7/8 : Rat),(3/4 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 0 (1 : Rat),.L (0 : Rat) (115263/131072 : Rat) (0 : Rat) (88013/524288 : Rat),.S 0 (3/2 : Rat),.L (188305/262144 : Rat) (654805/524288 : Rat) (143559/1048576 : Rat) (251223/1048576 : Rat),.S 0 (7/4 : Rat),.L (543111/524288 : Rat) (1452845/1048576 : Rat) (103869/524288 : Rat) (279333/1048576 : Rat),.S 2 (13/16 : Rat),.L (304327/262144 : Rat) (1541459/1048576 : Rat) (116603/524288 : Rat) (148413/524288 : Rat),.L (633507/524288 : Rat) (1595201/1048576 : Rat) (242899/1048576 : Rat) (76869/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P503
