import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P48
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(5/2 : Rat),(314159265358979323847/100000000000000000000 : Rat),(11/16 : Rat),(3/4 : Rat),(3/4 : Rat),(7/8 : Rat)⟩
def toks : List Tok := [.S 2 (13/16 : Rat),.S 1 (23/32 : Rat),.L (1245459/1048576 : Rat) (1607971/1048576 : Rat) (238693/1048576 : Rat) (77503/262144 : Rat),.L (636505/524288 : Rat) (820019/524288 : Rat) (244069/1048576 : Rat) (316387/1048576 : Rat),.S 1 (23/32 : Rat),.L (649795/524288 : Rat) (1674699/1048576 : Rat) (249263/1048576 : Rat) (323291/1048576 : Rat),.S 0 (11/4 : Rat),.S 2 (27/32 : Rat),.L (362693/262144 : Rat) (209177/131072 : Rat) (69731/262144 : Rat) (323035/1048576 : Rat),.L (1480167/1048576 : Rat) (853385/524288 : Rat) (284717/1048576 : Rat) (82423/262144 : Rat),.L (1439545/1048576 : Rat) (853385/524288 : Rat) (138357/524288 : Rat) (82423/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P48
