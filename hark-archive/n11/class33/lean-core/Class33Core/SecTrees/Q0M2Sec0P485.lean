import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P485
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(31/32 : Rat),(1 : Rat),(23/32 : Rat),(3/4 : Rat)⟩
def toks : List Tok := [.S 1 (63/64 : Rat),.S 2 (47/64 : Rat),.S 1 (125/128 : Rat),.L (1704713/1048576 : Rat) (1796441/1048576 : Rat) (5145/16384 : Rat) (347659/1048576 : Rat),.L (856313/524288 : Rat) (225587/131072 : Rat) (330861/1048576 : Rat) (174659/524288 : Rat),.S 1 (125/128 : Rat),.L (1720501/1048576 : Rat) (1812655/1048576 : Rat) (83109/262144 : Rat) (350919/1048576 : Rat),.L (216051/131072 : Rat) (1820911/1048576 : Rat) (334017/1048576 : Rat) (88145/262144 : Rat),.S 2 (47/64 : Rat),.S 1 (127/128 : Rat),.L (860271/524288 : Rat) (1812951/1048576 : Rat) (83111/262144 : Rat) (175489/524288 : Rat),.L (432115/262144 : Rat) (910603/524288 : Rat) (83507/262144 : Rat) (352639/1048576 : Rat),.S 1 (127/128 : Rat),.L (1736319/1048576 : Rat) (914583/524288 : Rat) (20975/65536 : Rat) (177121/524288 : Rat),.L (1744231/1048576 : Rat) (1837421/1048576 : Rat) (10537/32768 : Rat) (355905/1048576 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P485
