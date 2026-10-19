import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P121
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(15/16 : Rat),(31/32 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 2 (7/32 : Rat),.S 0 (9/4 : Rat),.L (1037585/1048576 : Rat) (1219733/1048576 : Rat) (198321/1048576 : Rat) (233679/1048576 : Rat),.S 0 (19/8 : Rat),.L (1082689/1048576 : Rat) (306811/262144 : Rat) (207053/1048576 : Rat) (235143/1048576 : Rat),.L (548767/524288 : Rat) (622067/524288 : Rat) (209931/1048576 : Rat) (238435/1048576 : Rat),.S 0 (9/4 : Rat),.L (1055001/1048576 : Rat) (1245713/1048576 : Rat) (201691/1048576 : Rat) (238743/1048576 : Rat),.S 0 (19/8 : Rat),.L (1106615/1048576 : Rat) (1254115/1048576 : Rat) (211691/1048576 : Rat) (120191/524288 : Rat),.L (1123547/1048576 : Rat) (1272993/1048576 : Rat) (3359/16384 : Rat) (244067/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P121
