import N11Formalization.FmAssembly
import N11Formalization.BoxRstar

namespace N11Formalization

-- 桥探针：两份盒心表（我的 `cCert`/`cCertR` 与 box-rstar 的 `certC`/`certCR`）是否逐位相同？
example : cCertR = certCR := by
  funext i
  fin_cases i <;> norm_num [cCertR, certCR, cCert, certC]

-- 判别力对照：把下标挪一格就会不同（证明上面的逐位核对不是恒真）
example : cCertR ≠ (fun i : Fin 12 => cCertR (i + 1)) := by
  intro h
  have h0 := congrFun h 0
  norm_num [cCertR, cCert] at h0

end N11Formalization
