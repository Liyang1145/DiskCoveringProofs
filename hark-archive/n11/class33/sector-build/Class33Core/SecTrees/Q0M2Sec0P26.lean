import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P26
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(0 : Rat),(314159265358979323847/100000000000000000000 : Rat),(1/2 : Rat),(9/16 : Rat),(1/4 : Rat),(3/8 : Rat)⟩
def toks : List Tok := [.S 0 (2 : Rat),.L (1/8 : Rat) (249663/262144 : Rat) (12453/524288 : Rat) (190795/1048576 : Rat),.S 2 (5/16 : Rat),.S 0 (5/2 : Rat),.L (304461/524288 : Rat) (938333/1048576 : Rat) (115931/1048576 : Rat) (89577/524288 : Rat),.S 1 (17/32 : Rat),.L (321883/524288 : Rat) (451973/524288 : Rat) (61297/524288 : Rat) (10783/65536 : Rat),.S 2 (9/32 : Rat),.L (684095/1048576 : Rat) (14003/16384 : Rat) (130313/1048576 : Rat) (85517/524288 : Rat),.L (354185/524288 : Rat) (927399/1048576 : Rat) (67481/524288 : Rat) (88523/524288 : Rat),.S 0 (5/2 : Rat),.L (657529/1048576 : Rat) (998215/1048576 : Rat) (125227/1048576 : Rat) (190711/1048576 : Rat),.S 1 (17/32 : Rat),.L (348893/524288 : Rat) (120467/131072 : Rat) (132935/1048576 : Rat) (92027/524288 : Rat),.S 2 (11/32 : Rat),.L (366653/524288 : Rat) (479355/524288 : Rat) (139741/1048576 : Rat) (45771/262144 : Rat),.L (379419/524288 : Rat) (990115/1048576 : Rat) (144637/1048576 : Rat) (94573/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P26
