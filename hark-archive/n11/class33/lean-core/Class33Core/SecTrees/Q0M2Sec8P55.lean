import Class33Core.SecTrees.Q0M2Sec8Base
namespace Class33Core.SecTrees.Q0M2Sec8.P55
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec8
def box : Box := ⟨(1/2 : Rat),(1 : Rat),(7/8 : Rat),(1 : Rat),(0 : Rat),(1/4 : Rat)⟩
def toks : List Tok := [.S 2 (1/8 : Rat),.S 1 (15/16 : Rat),.S 2 (1/16 : Rat),.L (13/16 : Rat) (1014181/1048576 : Rat) (162523/1048576 : Rat) (48449/262144 : Rat),.L (795283/1048576 : Rat) (982957/1048576 : Rat) (151631/1048576 : Rat) (46941/262144 : Rat),.S 2 (1/16 : Rat),.L (7/8 : Rat) (1079747/1048576 : Rat) (87569/524288 : Rat) (51621/262144 : Rat),.L (430363/524288 : Rat) (1048357/1048576 : Rat) (10263/65536 : Rat) (100203/524288 : Rat),.S 1 (15/16 : Rat),.S 0 (3/4 : Rat),.S 2 (3/16 : Rat),.L (370321/524288 : Rat) (911949/1048576 : Rat) (141147/1048576 : Rat) (174069/1048576 : Rat),.L (343797/524288 : Rat) (871519/1048576 : Rat) (130983/1048576 : Rat) (166285/1048576 : Rat),.L (701603/1048576 : Rat) (492315/524288 : Rat) (66833/524288 : Rat) (188087/1048576 : Rat),.S 0 (3/4 : Rat),.L (46377/65536 : Rat) (124517/131072 : Rat) (70707/524288 : Rat) (190309/1048576 : Rat),.L (766109/1048576 : Rat) (1049621/1048576 : Rat) (9127/65536 : Rat) (200651/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec8.P55
