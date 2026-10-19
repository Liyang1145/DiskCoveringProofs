import Class33Core.SecTrees.Q0M2Sec0Base
namespace Class33Core.SecTrees.Q0M2Sec0.P353
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec0
def box : Box := ⟨(3 : Rat),(314159265358979323847/100000000000000000000 : Rat),(27/32 : Rat),(7/8 : Rat),(5/8 : Rat),(21/32 : Rat)⟩
def toks : List Tok := [.S 1 (55/64 : Rat),.S 2 (41/64 : Rat),.S 1 (109/128 : Rat),.L (741713/524288 : Rat) (1567073/1048576 : Rat) (17835/65536 : Rat) (150949/524288 : Rat),.L (745665/524288 : Rat) (1575337/1048576 : Rat) (286919/1048576 : Rat) (18971/65536 : Rat),.S 1 (109/128 : Rat),.L (1499241/1048576 : Rat) (791631/524288 : Rat) (288481/1048576 : Rat) (305107/1048576 : Rat),.L (753569/524288 : Rat) (1591527/1048576 : Rat) (36255/131072 : Rat) (306747/1048576 : Rat),.S 2 (41/64 : Rat),.S 1 (111/128 : Rat),.L (1499237/1048576 : Rat) (1583601/1048576 : Rat) (9015/32768 : Rat) (305175/1048576 : Rat),.L (1507147/1048576 : Rat) (198983/131072 : Rat) (145021/524288 : Rat) (153407/524288 : Rat),.S 1 (111/128 : Rat),.L (1515039/1048576 : Rat) (1599791/1048576 : Rat) (291601/1048576 : Rat) (308387/1048576 : Rat),.L (761471/524288 : Rat) (1608055/1048576 : Rat) (293163/1048576 : Rat) (77507/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec0.P353
