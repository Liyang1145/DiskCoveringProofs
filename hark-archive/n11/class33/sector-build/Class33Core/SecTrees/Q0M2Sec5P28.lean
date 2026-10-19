import Class33Core.SecTrees.Q0M2Sec5Base
namespace Class33Core.SecTrees.Q0M2Sec5.P28
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec5
def box : Box := ⟨(7/4 : Rat),(2 : Rat),(5/8 : Rat),(3/4 : Rat),(3/4 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 1 (11/16 : Rat),.S 2 (13/16 : Rat),.S 0 (15/8 : Rat),.L (1087381/1048576 : Rat) (1297807/1048576 : Rat) (207963/1048576 : Rat) (248915/1048576 : Rat),.L (285097/262144 : Rat) (1355131/1048576 : Rat) (109123/524288 : Rat) (32517/131072 : Rat),.S 0 (15/8 : Rat),.L (1137303/1048576 : Rat) (678409/524288 : Rat) (217647/1048576 : Rat) (130233/524288 : Rat),.L (1192219/1048576 : Rat) (707943/524288 : Rat) (228321/1048576 : Rat) (272061/1048576 : Rat),.S 0 (15/8 : Rat),.S 2 (13/16 : Rat),.L (569191/524288 : Rat) (673133/524288 : Rat) (851/4096 : Rat) (129199/524288 : Rat),.L (296669/262144 : Rat) (175535/131072 : Rat) (227243/1048576 : Rat) (67445/262144 : Rat),.S 2 (13/16 : Rat),.L (1194073/1048576 : Rat) (1406533/1048576 : Rat) (114341/524288 : Rat) (270223/1048576 : Rat),.S 0 (31/16 : Rat),.L (627503/524288 : Rat) (1425155/1048576 : Rat) (240555/1048576 : Rat) (68471/262144 : Rat),.L (1282707/1048576 : Rat) (1454939/1048576 : Rat) (245963/1048576 : Rat) (139873/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec5.P28
