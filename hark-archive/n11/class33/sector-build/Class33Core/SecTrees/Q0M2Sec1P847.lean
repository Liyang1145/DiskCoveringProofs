import Class33Core.SecTrees.Q0M2Sec1Base
namespace Class33Core.SecTrees.Q0M2Sec1.P847
open Class33Core.SectorKernel Class33Core.SecTrees.Q0M2Sec1
def box : Box := ⟨(11/4 : Rat),(314159265358979323847/100000000000000000000 : Rat),(31/32 : Rat),(1 : Rat),(15/16 : Rat),(1 : Rat)⟩
def toks : List Tok := [.S 0 (3 : Rat),.S 2 (31/32 : Rat),.S 1 (63/64 : Rat),.L (1855939/1048576 : Rat) (2048525/1048576 : Rat) (359637/1048576 : Rat) (199381/524288 : Rat),.L (935459/524288 : Rat) (2065165/1048576 : Rat) (362661/1048576 : Rat) (201085/524288 : Rat),.S 1 (63/64 : Rat),.L (1886617/1048576 : Rat) (1040481/524288 : Rat) (365833/1048576 : Rat) (12669/32768 : Rat),.L (1901771/1048576 : Rat) (2 : Rat) (368899/1048576 : Rat) (102183/262144 : Rat),.L (1926581/1048576 : Rat) (2 : Rat) (373925/1048576 : Rat) (102183/262144 : Rat)]
theorem ok : chkAll co M box toks [] = true := by decide +kernel
end Class33Core.SecTrees.Q0M2Sec1.P847
