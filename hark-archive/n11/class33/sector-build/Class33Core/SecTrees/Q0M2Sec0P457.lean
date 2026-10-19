import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P457
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(15/16 : Rat),(31/32 : Rat),(5/8 : Rat),(21/32 : Rat)⟩
def toks : List Tok := [.S 1 (61/64 : Rat),.S 2 (41/64 : Rat),.S 1 (121/128 : Rat),.L (1578467/1048576 : Rat) (833101/524288 : Rat) (76039/262144 : Rat) (321597/1048576 : Rat),.L (1586405/1048576 : Rat) (837229/524288 : Rat) (152865/524288 : Rat) (323243/1048576 : Rat),.S 1 (121/128 : Rat),.L (797103/524288 : Rat) (1682395/1048576 : Rat) (153639/524288 : Rat) (162413/524288 : Rat),.L (801069/524288 : Rat) (1690651/1048576 : Rat) (77213/262144 : Rat) (326473/1048576 : Rat),.S 2 (41/64 : Rat),.S 1 (123/128 : Rat),.L (797173/524288 : Rat) (841357/524288 : Rat) (307305/1048576 : Rat) (324889/1048576 : Rat),.L (1602289/1048576 : Rat) (1690969/1048576 : Rat) (154441/524288 : Rat) (326537/1048576 : Rat),.S 1 (123/128 : Rat),.L (1610073/1048576 : Rat) (424727/262144 : Rat) (77607/262144 : Rat) (164061/524288 : Rat),.L (809005/524288 : Rat) (1707163/1048576 : Rat) (312005/1048576 : Rat) (329771/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P457
