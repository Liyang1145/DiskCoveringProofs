import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P184
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(7/8 : Rat),(29/32 : Rat),(1/4 : Rat),(5/16 : Rat)⟩
def toks : List Tok := [.S 0 (9/4 : Rat),.S 2 (9/32 : Rat),.L (252551/262144 : Rat) (1206553/1048576 : Rat) (193027/1048576 : Rat) (28889/131072 : Rat),.L (128689/131072 : Rat) (616621/524288 : Rat) (196759/1048576 : Rat) (29539/131072 : Rat),.S 2 (9/32 : Rat),.S 0 (19/8 : Rat),.L (1067483/1048576 : Rat) (1215679/1048576 : Rat) (51027/262144 : Rat) (232889/1048576 : Rat),.L (543093/524288 : Rat) (309039/262144 : Rat) (207731/1048576 : Rat) (14805/65536 : Rat),.S 0 (19/8 : Rat),.L (546301/524288 : Rat) (155395/131072 : Rat) (104487/524288 : Rat) (238245/1048576 : Rat),.S 1 (57/64 : Rat),.L (556573/524288 : Rat) (1248929/1048576 : Rat) (106479/524288 : Rat) (239371/1048576 : Rat),.L (1128983/1048576 : Rat) (632699/524288 : Rat) (216031/1048576 : Rat) (30323/131072 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P184
