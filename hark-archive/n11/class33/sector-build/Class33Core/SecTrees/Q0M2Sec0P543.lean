import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P543
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(25/32 : Rat),(13/16 : Rat),(7/8 : Rat),(15/16 : Rat)⟩
def toks : List Tok := [.S 2 (29/32 : Rat),.S 1 (51/64 : Rat),.S 2 (57/64 : Rat),.L (836731/524288 : Rat) (885229/524288 : Rat) (323043/1048576 : Rat) (171221/524288 : Rat),.L (211147/131072 : Rat) (1786983/1048576 : Rat) (163089/524288 : Rat) (345759/1048576 : Rat),.S 2 (57/64 : Rat),.L (1689359/1048576 : Rat) (1786683/1048576 : Rat) (163107/524288 : Rat) (345699/1048576 : Rat),.L (852531/524288 : Rat) (225401/131072 : Rat) (164675/524288 : Rat) (349019/1048576 : Rat),.S 1 (51/64 : Rat),.S 2 (59/64 : Rat),.L (1704903/1048576 : Rat) (901753/524288 : Rat) (164659/524288 : Rat) (349079/1048576 : Rat),.L (860321/524288 : Rat) (910013/524288 : Rat) (20779/65536 : Rat) (176201/524288 : Rat),.S 2 (59/64 : Rat),.L (1720777/1048576 : Rat) (1819731/1048576 : Rat) (332491/1048576 : Rat) (176171/524288 : Rat),.L (1736505/1048576 : Rat) (459063/262144 : Rat) (167819/524288 : Rat) (355669/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P543
