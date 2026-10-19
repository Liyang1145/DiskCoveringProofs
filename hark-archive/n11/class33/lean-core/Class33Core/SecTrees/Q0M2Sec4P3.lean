import Class33Core.SecTrees.Q0M2Sec4Base
namespace Class33Core.SecTrees.Q0M2Sec4.P3
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec4
def box : Box := ⟨(1/2 : Rat),(1 : Rat),(0 : Rat),(1/4 : Rat),(3/4 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 2 (7/8 : Rat),.S 1 (1/8 : Rat),.S 2 (13/16 : Rat),.L (5/8 : Rat) (913047/1048576 : Rat) (31203/262144 : Rat) (174281/1048576 : Rat),.L (11/16 : Rat) (489365/524288 : Rat) (68681/524288 : Rat) (46737/262144 : Rat),.S 0 (3/4 : Rat),.L (273685/524288 : Rat) (433053/524288 : Rat) (104171/1048576 : Rat) (41311/262144 : Rat),.L (143323/262144 : Rat) (919717/1048576 : Rat) (54561/524288 : Rat) (87783/524288 : Rat),.S 1 (1/8 : Rat),.S 2 (15/16 : Rat),.L (3/4 : Rat) (522197/524288 : Rat) (37483/262144 : Rat) (199639/1048576 : Rat),.L (13/16 : Rat) (1110043/1048576 : Rat) (162523/1048576 : Rat) (212357/1048576 : Rat),.S 0 (3/4 : Rat),.L (169255/262144 : Rat) (124517/131072 : Rat) (64479/524288 : Rat) (190309/1048576 : Rat),.L (701603/1048576 : Rat) (1049621/1048576 : Rat) (66833/524288 : Rat) (200651/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec4.P3
