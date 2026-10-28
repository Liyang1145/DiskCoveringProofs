import Mathlib

/-!
# 可核验的十六进制浮点字面量解码（GUIDE §3「dyadic 解码」义务）

外部证书（JSON）里的坐标与半径以 C99 十六进制浮点字面量给出，例如
`0x1.12e0be826d695p-30`。数值语义必须由**证明助理侧**确定，不能把宿主语言的浮点结果
当实数公理导入。

本文件提供：
* `hexFloat.parse`：可计算的解码器 →（符号, 整数部分数字表, 小数部分数字表, 二进制指数）；
* `hexFloat.toQ`：语义，即精确**有理数**（二进有理）；
* `hexNatVal_lt_pow`：数字表合法性引理（每个数字 `< 16` ⇒ 值 `< 16^长度`）。

可信链：源字面量 --parse--> 数字表 --toQ--> 精确有理数。
`parse` 的**具体**输出在内核里由 `decide` 核查（见 `Certificates/RootBox.lean`），
故「源字面量 ↦ 精确有理数」这一步不依赖任何宿主浮点。
-/

namespace N11Formalization

/-- 单个十六进制数字字符 → 数值（非法字符为 `none`）。 -/
def hexDigitVal (c : Char) : Option ℕ :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then some (c.toNat - 55)
  else none

theorem hexDigitVal_lt {c : Char} {n : ℕ} (h : hexDigitVal c = some n) : n < 16 := by
  unfold hexDigitVal at h
  split_ifs at h with h1 h2 h3
  · simp only [Option.some.injEq] at h; omega
  · simp only [Option.some.injEq] at h; omega
  · simp only [Option.some.injEq] at h; omega

/-- 单个**十进制**数字字符 → 数值（指数部分用）。 -/
def decDigitVal (c : Char) : Option ℕ :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48) else none

/-- 在字符表中**首次**出现 `t` 处切分（`t` 本身丢弃）。 -/
def splitFirst (t : Char) : List Char → List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if c == t then ([], cs)
      else
        let r := splitFirst t cs
        (c :: r.1, r.2)

/-- 全部字符必须是十六进制数字，输出数字表。 -/
def allHexDigits : List Char → Option (List ℕ)
  | [] => some []
  | c :: cs =>
      hexDigitVal c >>= fun d => allHexDigits cs >>= fun ds => some (d :: ds)

/-- 全部字符必须是十进制数字，输出数字表（指数部分）。 -/
def allDecDigits : List Char → Option (List ℕ)
  | [] => some []
  | c :: cs =>
      decDigitVal c >>= fun d => allDecDigits cs >>= fun ds => some (d :: ds)

/-- 数字表 → ℕ（高位在前）。 -/
def hexNatVal : List ℕ → ℕ
  | [] => 0
  | d :: ds => d * 16 ^ ds.length + hexNatVal ds

/-- 十进制数字表 → ℕ。 -/
def decNatVal : List ℕ → ℕ
  | [] => 0
  | d :: ds => d * 10 ^ ds.length + decNatVal ds

/-- 合法性引理：每个数字均 `< 16` ⇒ 值 `< 16 ^ 长度`（无溢出/无编码别名）。 -/
theorem hexNatVal_lt_pow {l : List ℕ} (h : ∀ d ∈ l, d < 16) :
    hexNatVal l < 16 ^ l.length := by
  induction l with
  | nil => simp [hexNatVal]
  | cons d ds ih =>
      have hd : d < 16 := h d (List.mem_cons_self ..)
      have hds : ∀ e ∈ ds, e < 16 := fun e he => h e (List.mem_cons_of_mem _ he)
      have h2 : hexNatVal ds < 16 ^ ds.length := ih hds
      have h1 : d ≤ 15 := by omega
      calc hexNatVal (d :: ds)
          = d * 16 ^ ds.length + hexNatVal ds := rfl
        _ < d * 16 ^ ds.length + 16 ^ ds.length := Nat.add_lt_add_left h2 _
        _ = (d + 1) * 16 ^ ds.length := by ring
        _ ≤ 16 * 16 ^ ds.length := Nat.mul_le_mul_right _ (by omega)
        _ = 16 ^ (d :: ds).length := by
              rw [List.length_cons, Nat.pow_succ]; ring

/-- 解码后的十六进制浮点：`(-1)^neg · (ip.fp)_16 · 2^exp`。 -/
structure HexFloat where
  neg : Bool
  ip : List ℕ
  fp : List ℕ
  exp : ℤ
  deriving DecidableEq, Repr

namespace HexFloat

/-- **语义**：精确有理数（二进有理），不使用任何宿主浮点。 -/
def toQ (h : HexFloat) : ℚ :=
  (if h.neg then -1 else 1) *
    (((hexNatVal h.ip * 16 ^ h.fp.length + hexNatVal h.fp : ℕ) : ℚ) /
      ((16 ^ h.fp.length : ℕ) : ℚ)) *
    (2 : ℚ) ^ h.exp

/-- 解码器：`[+-]?0x<hex>.<hex>p[+-]<dec>`（小数部分与 `p` 指数可缺省）。 -/
def parse (s : String) : Option HexFloat :=
  let (neg, l) :=
    match s.toList with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | l => (false, l)
  match l with
  | '0' :: x :: rest =>
      if x == 'x' || x == 'X' then
        let sp := splitFirst 'p' rest
        let sd := splitFirst '.' sp.1
        let (es, ed) :=
          match sp.2 with
          | '-' :: r => (true, r)
          | '+' :: r => (false, r)
          | r => (false, r)
        match allHexDigits sd.1, allHexDigits sd.2, allDecDigits ed with
        | some a, some b, some c =>
            let e : ℤ := (decNatVal c : ℤ)
            some ⟨neg, a, b, if es then -e else e⟩
        | _, _, _ => none
      else none
  | _ => none

end HexFloat

end N11Formalization
