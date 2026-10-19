import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P51
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(1/2 : Rat),(1 : Rat),(3/4 : Rat),(7/8 : Rat),(0 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 2 (1/8 : Rat),.S 1 (13/16 : Rat),.S 2 (1/16 : Rat),.L (11/16 : Rat) (220759/262144 : Rat) (68681/524288 : Rat) (84251/524288 : Rat),.L (166113/262144 : Rat) (852221/1048576 : Rat) (15819/131072 : Rat) (162573/1048576 : Rat),.S 2 (1/16 : Rat),.L (3/4 : Rat) (948611/1048576 : Rat) (37483/262144 : Rat) (11321/65536 : Rat),.L (729857/1048576 : Rat) (917577/1048576 : Rat) (17385/131072 : Rat) (87577/524288 : Rat),.S 1 (13/16 : Rat),.S 0 (3/4 : Rat),.L (273685/524288 : Rat) (801219/1048576 : Rat) (104171/1048576 : Rat) (38193/262144 : Rat),.L (143323/262144 : Rat) (427449/524288 : Rat) (54561/524288 : Rat) (10193/65536 : Rat),.S 0 (3/4 : Rat),.S 2 (3/16 : Rat),.L (84437/131072 : Rat) (846891/1048576 : Rat) (64333/524288 : Rat) (40387/262144 : Rat),.L (77871/131072 : Rat) (403533/524288 : Rat) (14827/131072 : Rat) (153895/1048576 : Rat),.L (637307/1048576 : Rat) (919717/1048576 : Rat) (121359/1048576 : Rat) (87783/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P51
