import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P121
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(13/16 : Rat),(7/8 : Rat),(1/2 : Rat),(5/8 : Rat)⟩
def toks : List Tok := [.S 2 (9/16 : Rat),.S 1 (27/32 : Rat),.L (141973/131072 : Rat) (1489053/1048576 : Rat) (27169/131072 : Rat) (286471/1048576 : Rat),.L (72759/65536 : Rat) (190365/131072 : Rat) (222861/1048576 : Rat) (293159/1048576 : Rat),.S 1 (27/32 : Rat),.L (1188529/1048576 : Rat) (1551211/1048576 : Rat) (227603/1048576 : Rat) (74689/262144 : Rat),.L (304077/262144 : Rat) (1585105/1048576 : Rat) (233011/1048576 : Rat) (305473/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P121
