import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P99
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(0 : Rat),(1/2 : Rat),(3/4 : Rat),(7/8 : Rat),(1/2 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 1 (13/16 : Rat),.S 2 (5/8 : Rat),.S 0 (1/4 : Rat),.L (1/8 : Rat) (188579/524288 : Rat) (12453/524288 : Rat) (17929/262144 : Rat),.L (206153/1048576 : Rat) (495721/1048576 : Rat) (19589/524288 : Rat) (94315/1048576 : Rat),.S 0 (1/4 : Rat),.L (0 : Rat) (70933/262144 : Rat) (0 : Rat) (53933/1048576 : Rat),.L (177903/1048576 : Rat) (226215/524288 : Rat) (33807/1048576 : Rat) (86059/1048576 : Rat),.S 2 (5/8 : Rat),.S 0 (1/4 : Rat),.L (3/16 : Rat) (438379/1048576 : Rat) (37363/1048576 : Rat) (20845/262144 : Rat),.S 1 (27/32 : Rat),.L (64267/262144 : Rat) (523077/1048576 : Rat) (12215/262144 : Rat) (99535/1048576 : Rat),.L (35597/131072 : Rat) (34439/65536 : Rat) (54131/1048576 : Rat) (52435/524288 : Rat),.S 0 (1/4 : Rat),.L (1/16 : Rat) (84331/262144 : Rat) (3113/262144 : Rat) (16033/262144 : Rat),.L (98211/524288 : Rat) (497523/1048576 : Rat) (2333/65536 : Rat) (47329/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P99
