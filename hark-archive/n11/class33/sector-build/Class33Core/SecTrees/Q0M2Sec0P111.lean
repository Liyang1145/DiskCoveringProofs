import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P111
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(2 : Rat),(5/2 : Rat),(7/8 : Rat),(29/32 : Rat),(3/16 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 2 (7/32 : Rat),.S 0 (9/4 : Rat),.L (486875/524288 : Rat) (1154115/1048576 : Rat) (92993/524288 : Rat) (220913/1048576 : Rat),.S 0 (19/8 : Rat),.L (509275/524288 : Rat) (290385/262144 : Rat) (12165/65536 : Rat) (55589/262144 : Rat),.L (1033273/1048576 : Rat) (1178229/1048576 : Rat) (197487/1048576 : Rat) (3525/16384 : Rat),.S 0 (9/4 : Rat),.L (991603/1048576 : Rat) (1180171/1048576 : Rat) (189433/1048576 : Rat) (112989/524288 : Rat),.S 0 (19/8 : Rat),.L (1042789/1048576 : Rat) (594233/524288 : Rat) (6229/32768 : Rat) (28449/131072 : Rat),.L (1059553/1048576 : Rat) (1207095/1048576 : Rat) (50643/262144 : Rat) (115609/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P111
