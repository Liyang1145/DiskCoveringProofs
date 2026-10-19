import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P451
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(9/4 : Rat),(15/16 : Rat),(1 : Rat),(5/8 : Rat),(11/16 : Rat)⟩
def toks : List Tok := [.S 0 (17/8 : Rat),.S 1 (31/32 : Rat),.L (1352729/1048576 : Rat) (1563939/1048576 : Rat) (16229/65536 : Rat) (301277/1048576 : Rat),.L (690441/524288 : Rat) (1595403/1048576 : Rat) (265185/1048576 : Rat) (76879/262144 : Rat),.S 1 (31/32 : Rat),.S 2 (21/32 : Rat),.L (1407159/1048576 : Rat) (789691/524288 : Rat) (270345/1048576 : Rat) (152169/524288 : Rat),.L (717025/524288 : Rat) (401909/262144 : Rat) (17227/65536 : Rat) (309945/1048576 : Rat),.S 2 (21/32 : Rat),.L (359131/262144 : Rat) (805515/524288 : Rat) (276119/1048576 : Rat) (310619/1048576 : Rat),.L (365805/262144 : Rat) (204899/131072 : Rat) (8793/32768 : Rat) (158109/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P451
