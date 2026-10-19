import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P464
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(31/32 : Rat),(1 : Rat),(5/8 : Rat),(21/32 : Rat)⟩
def toks : List Tok := [.S 1 (63/64 : Rat),.S 2 (41/64 : Rat),.S 1 (125/128 : Rat),.L (1610235/1048576 : Rat) (212403/131072 : Rat) (77615/262144 : Rat) (328185/1048576 : Rat),.L (1618183/1048576 : Rat) (1707477/1048576 : Rat) (312039/1048576 : Rat) (329833/1048576 : Rat),.S 1 (125/128 : Rat),.L (1625949/1048576 : Rat) (857709/524288 : Rat) (313583/1048576 : Rat) (82855/262144 : Rat),.L (408473/262144 : Rat) (215459/131072 : Rat) (315163/1048576 : Rat) (333071/1048576 : Rat),.S 2 (41/64 : Rat),.S 1 (127/128 : Rat),.L (1626133/1048576 : Rat) (1715731/1048576 : Rat) (78405/262144 : Rat) (331483/1048576 : Rat),.L (817043/524288 : Rat) (1723983/1048576 : Rat) (315201/1048576 : Rat) (333133/1048576 : Rat),.S 1 (127/128 : Rat),.L (410459/262144 : Rat) (865963/524288 : Rat) (316743/1048576 : Rat) (167361/524288 : Rat),.L (1649783/1048576 : Rat) (1740179/1048576 : Rat) (318325/1048576 : Rat) (168187/524288 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P464
