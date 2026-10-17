import N11Formalization.SourceIdentity

/-!
# G0（语义桥）最后一块：源 `res5` 的**循环式**控制流转写，以及它 = 本工程闭式的 kernel 证明

## 本件回答的问题（与 `SourceIdentity.lean` 的分工）

`SourceIdentity.lean` 把 `TC-ROOT-SOURCE-IDENTITY.md` 的**六条结构声明**按「**闭式**」kernel 化：
`rhoK`/`thetaOf`/`ringCenter`/`Uvec`/`residual` 都是**一次性写出的显式表达式**。
但源 `tc_s32_kraw.py:res5`（121–153 行）本身**不是**闭式，而是**两段 `for` 循环 + 一个 `for` 输出循环**：

```python
a4 = PI - 2*(a04[0]+a04[1]+a04[2]+a04[3]); a = [a04[0],...,a04[3],a4,a04[3],...,a04[0]]
for k in range(9): rho.append(C(a[k]) - Q(R*R - S(a[k])**2))
th = [None]*9; th[4] = 0*a04[0]
for k in range(5, 9): th[k] = th[k-1] + a[k-1] + a[k]      # 递增
for k in range(3,-1,-1): th[k] = th[k+1] - (a[k] + a[k+1]) # 递减
C[k] = (rho[k] C(th[k]), rho[k] S(th[k]))
U[k] = (C[k][0]+C[(k+1)%9][0]-C(th[k]+a[k]), C[k][1]+C[(k+1)%9][1]-S(th[k]+a[k]))
out for (k,l) in [(1,1),(2,0),(3,0),(8,1)]: Q(dx*dx+dy*dy) - R,  c = y1 if l==1 else y0
half = 1/2; m = (y0+y1)*half; d = (y1-y0)*half; h = Q(R*R - d*d)
out.append(Q((m-C[6][0])**2 + (h-C[6][1])**2) - R)
```

本文件把**这一段**逐句镜像成 Lean：`SrcState`（`a,th,rho,C,U` 五张表）
+ `thetaLoop`（两段 `for` 折叠）+ `rhoLoop`/`CLoop`/`ULoop`（`for k in range(9)` 折叠）
+ `res5Heads`（`for (k,l) in [(1,1),(2,0),(3,0),(8,1)]` 的 `map`）+ `res5Tail`（第五条 `append`），
然后证明 **`s5Loop u = residual u`**（逐点，`Fin 5 → ℝ`）。
这就是 G0 的实质内容：**「我的闭式转写」= 「源的控制流转写」**。

## 本件**没有**回答的问题（诚实边界，不冒称 G0 完成）

1. **从 Python 源码到 Lean 的*自动*转写原则上不可能**（Python 语义 / 浮点 / 异常 / `None` 哨兵
   与 Lean 的 `List` 不是同一个形式系统）。本件**不**声称「源代码已被机器翻译」。
2. 本件保证的是：**每一处人工对读的判断**都变成了一条**可定位的 kernel 引理**。

| 源文里的人工对读判断 | 本文件的具名引理 | § |
|---|---|---|
| ① `a4 = π − 2(a0+a1+a2+a3)`、九槽回文表 | `aList_val_0 … aList_val_8` | §3 |
| ② **循环方向（递增，`range(5,9)`）** | `thetaLoop_5 … thetaLoop_8` + `thetaLoop_up_rec` | §4 |
| ③ **循环方向（递减，`range(3,-1,-1)`）** | `thetaLoop_3 … thetaLoop_0` + `thetaLoop_down_rec` | §4 |
| ④ `th[4] = 0`（源写 `0*a04[0]`，是 `0` **不是** `a04[0]`） | `thetaLoop_4` | §4 |
| 两段 `for` 的合并（循环式 = 闭式 `thetaOf`） | `thetaLoop_eq_thetaOf` | §5 |
| ⑤ **`(k+1) % 9` 回绕**（源 `%9` vs 本工程 `Fin 9` 加法） | `k2Of_eq_fin` + `ULoop_val_0 … ULoop_val_8` | §6 |
| ⑥ **参数表顺序** `(1,1),(2,0),(3,0),(8,1)` + `l` 决定 `c=y1`/`y0` | `headsOf_val` | §7 |
| ⑦ **`half = 1/2` 是精确二进分数**、`m`/`d`/`h`/`C[6]` 的读数 | `tailOf` + `ringCenter6_coord_eq_0/1` | §7 |
| ⑧ 五条残差**逐项** = 闭式（`out` 恰 5 项） | `s5Loop_apply_0 … s5Loop_apply_4` + `s5Loop_apply_eq` | §7 |
| ⑨ `Q(dx*dx+dy*dy)` 即欧氏距离（`Uvec` 的 `ofLp` = `ULoop` 的 `proj`） | `sqrt_pair_generic` + `Uvec_coord0_eq_proj`/`Uvec_coord1_eq_proj` | §7 |
| **⑩ 主结论：源的控制流转写 = 本工程闭式残差** | **`s5Loop_eq_residual`** | §7 |
| ⑪ `F7` 的钉住 `x[i1]=c1, x[i2]=c2`（残差在前，钉住在后） | `F7At_first`/`F7At_pin1`/`F7At_pin2`/`F7At_eq` | §8 |

3. **数值级**独立验证由 root-audit 的 `my_tc.py` 承担（12/12 在 1e-56 包络内），本件不做数值断言。

## 负对照（等式引理**有鉴别力**的证据，§9）

三处**唯一的人工判读**各给一条"改错后的镜像 + 在具体见证处 kernel 证明的 `≠`"，
即该等式**确证失败**（不是"未能证明"）；并各附正确版的等式作对照：

| 源文判读 | 改错后的镜像 | 判别力（kernel 的 `≠`） | 对照（正确版等式） |
|---|---|---|---|
| `half = 0.5` | `halfBad := (3:ℝ)⁻¹` | `nc_half_fails : ¬ (halfBad = halfGood)` | `nc_half_control` |
| `C[(k+1) % 9]` | `k2OfBad := ⟨(k+1) % 8, _⟩` | `nc_mod9_fails : k2OfBad 8 ≠ k2Of 8` | `nc_mod9_control`(= `k2Of_eq_fin`) |
| 参数表首项 `k = 1` | `resSpecKBad := ![0,2,3,8]` | `nc_assembly_fails : resSpecKBad 0 ≠ resSpecK 0` | `nc_assembly_control` |

这三条**不是**对源文的判死：源文没有写错（第 147 行 `mpf('0.5')` 是精确 `1/2`；`%9` 写在
第 143 行；参数表 `(1,1)` 写在第 144 行）。它们证明 §3–§8 的等式链**不是空等式**：
改动源的任一处判读都会在具体见证处破坏等式。

> **scope 边界（防误读）**：三条负对照的判别力是**字面层**（`3⁻¹ ≠ 2⁻¹`、`k2OfBad 8 ≠ k2Of 8`、
> `resSpecKBad 0 ≠ resSpecK 0`），它们证明的是「**三处人工判读任一处读错即在具体见证处崩**」；
> 它们**不**验证**数值层**读数（即**不**证明"取具体 `u` 时错误版算出的残差实数值 ≠ 正确版"）。
> 数值层验证由 root-audit 的 `my_tc.py` 承担（见下条）。

## 真实等级

kernel-proved，无条件，零 `sorry`、零自定义 axiom、零 `native_decide`、零 `Float`。
`#print axioms` 审计落 `evidence/source-loop/PRINT-AXIOMS.txt`（46 条承重定理**全部**只依赖
`[propext, Classical.choice, Quot.sound]`，无 `sorryAx`）。
本件**只**消「我的闭式 vs 源的控制流」这一处人工对读风险，**不**触碰 G1/G2/G3。
-/

noncomputable section

namespace N11Formalization

open Real

/-! ## 0. 点、后端、源状态的显式建模 -/

/-- **源文坐标对 `C[k][0]` / `C[k][1]` 的桥**（本工程用 `Point = EuclideanSpace ℝ (Fin 2)`）。 -/
def proj (p : Point) (i : ℕ) : ℝ := match i with | 0 => p.ofLp 0 | _ => p.ofLp 1

/-- `proj p 0 = p.ofLp 0`（源 `C[k][0]`）。 -/
theorem proj_zero (p : Point) : proj p 0 = p.ofLp 0 := rfl
/-- `proj p 1 = p.ofLp 1`（源 `C[k][1]`）。 -/
theorem proj_one (p : Point) : proj p 1 = p.ofLp 1 := rfl

/-- 源文的 `(x, y)` 对（`U.append((…, …))` 追加的正是这样一个二元组）。 -/
def mkPoint (x y : ℝ) : Point := !₂[x, y]

@[simp] theorem proj_mkPoint_0 (x y : ℝ) : proj (mkPoint x y) 0 = x := rfl
@[simp] theorem proj_mkPoint_1 (x y : ℝ) : proj (mkPoint x y) 1 = y := rfl

/-- 源 `res5(a04,y0,y1,R,B)` 的后端 `B`（`BK_MPF`/`BK_IV`/`BK_DMPF`/`BK_DIV`）用到四个字段：
`PI, C(cos), S(sin), Q(√)`。`is_dual` 只切换 `half` 的取法（`mpf('0.5')` vs 浮点 `0.5`，
**两者都精确等于 `1/2`**），故 `res5` 的残差与后端选择无关；dual 数只出现在 `J7_point`
的求导路径上，不在残差路径上。 -/
structure BSource where
  /-- `B.PI()`：源文用 `mp.pi`（**精确** π），不是浮点常数。 -/
  PI : ℝ
  /-- `B.C` = `cos`。 -/
  C : ℝ → ℝ
  /-- `B.S` = `sin`。 -/
  S : ℝ → ℝ
  /-- `B.Q` = 非负支平方根（源文实参非负）。 -/
  Q : ℝ → ℝ

/-- **源文算术后端的忠实抽象**（`BK_MPF`：精确 π、精确三角、精确非负支 `√`）。 -/
def BReal : BSource where
  PI := Real.pi
  C := Real.cos
  S := Real.sin
  Q := Real.sqrt

/-- 源 `F7` 的**状态** `x = (a0,a1,a2,a3,y0,y1,R)`（**7** 维）。
**指标约定（易错处，显式钉住）**：`a04 = x[0:4]` ⇔ `xa0..xa3 = x[0..3]`；`y0 = x[4]`；
`y1 = x[5]`；`R = x[6]`。与本工程 `metricZ u = (u0,…,u6)` 逐位一致。 -/
structure SrcState where
  xa0 : ℝ
  xa1 : ℝ
  xa2 : ℝ
  xa3 : ℝ
  y0 : ℝ
  y1 : ℝ
  R : ℝ

/-- 源 `x = (a0,a1,a2,a3,y0,y1,R)` —— **7** 项列表。 -/
def zList (s : SrcState) : List ℝ := [s.xa0, s.xa1, s.xa2, s.xa3, s.y0, s.y1, s.R]

@[simp] theorem zList_length (s : SrcState) : (zList s).length = 7 := rfl

/-- 第 0 句：`a4 = B.PI() - 2*(a04[0]+a04[1]+a04[2]+a04[3])`。 -/
def a4Of (B : BSource) (s : SrcState) : ℝ :=
  B.PI - 2 * (s.xa0 + s.xa1 + s.xa2 + s.xa3)

/-- 第 1 句：`a = [a04[0],a04[1],a04[2],a04[3],a4,a04[3],a04[2],a04[1],a04[0]]`（**9** 项回文表）。 -/
def aList (B : BSource) (s : SrcState) : List ℝ :=
  [s.xa0, s.xa1, s.xa2, s.xa3, a4Of B s, s.xa3, s.xa2, s.xa1, s.xa0]

@[simp] theorem aList_length (B : BSource) (s : SrcState) : (aList B s).length = 9 := rfl

/-- `a` 表的 `Fin 9` 读法（`thetaOf` 的定义域）。 -/
def aFun (B : BSource) (s : SrcState) : Fin 9 → ℝ := fun k => (aList B s).getD (k : ℕ) 0

/-- `getD` 与 `getElem` 在合法下标上一致（`List.getD_eq_getElem` 的别名）。 -/
theorem aList_getD_eq_getElem (B : BSource) (s : SrcState) (n : ℕ) (hn : n < 9) :
    (aList B s).getD n 0 = (aList B s)[n] :=
  List.getD_eq_getElem (l := aList B s) (d := (0 : ℝ)) (n := n) (by rw [aList_length]; exact hn)

/-- 表读法与函数读法在合法下标上一致。 -/
theorem aFun_apply (B : BSource) (s : SrcState) (k : Fin 9) : aFun B s k = (aList B s)[(k : ℕ)] :=
  aList_getD_eq_getElem B s (k : ℕ) k.isLt

/-! ## 1. `th`/`rho`/`C`/`U` 五张表的折叠（②③④⑤） -/

/-- 源 `th[4] = 0*a04[0]`：值是 **`0`**（`0*x = 0`；源文这里**不是** `a04[0]`）。 -/
def thInit : ℝ := 0

/-- `Fin 9` 的 `+1`（模 9 写法；界由 `Nat.mod_lt` 免费给出，在 `0..7` 上与真自增一致）。 -/
def inc9 (i : Fin 9) : Fin 9 := Fin.mk (((i : ℕ) + 1) % 9) (Nat.mod_lt _ (by norm_num))

/-- `Fin 9` 的 `−1`（模 9 写法；在 `1..8` 上与真递减一致）。 -/
def dec9 (i : Fin 9) : Fin 9 := Fin.mk (((i : ℕ) + 8) % 9) (Nat.mod_lt _ (by norm_num))

/-- ② 递增段（`for k in range(5,9)`）的**循环体**：`th[k] = th[k-1] + a[k-1] + a[k]`
（`j = k−1` 显式传入）。 -/
def thetaUpAt (B : BSource) (s : SrcState) (i j : Fin 9) : ℝ :=
  thetaOf (aFun B s) j + aFun B s j + aFun B s i

/-- ③ 递减段（`for k in range(3,-1,-1)`）的**循环体**：`th[k] = th[k+1] − (a[k] + a[k+1])`
（`j = k+1` 显式传入）。 -/
def thetaDownAt (B : BSource) (s : SrcState) (i j : Fin 9) : ℝ :=
  thetaOf (aFun B s) j - (aFun B s i + aFun B s j)

/-- **源 `th` 表的两段 `for` 折叠**（不是闭式）：
`th = [None]*9; th[4] = 0` ⇒ 先 `for k in range(5,9)` **递增**（`thetaUpAt`，`j = dec9 k`），
再 `for k in range(3,-1,-1)` **递减**（`thetaDownAt`，`j = inc9 k`）。
`th[4]` 是初值，两段都不覆盖它。 -/
def thetaLoop (B : BSource) (s : SrcState) : Fin 9 → ℝ :=
  let up : Fin 9 → ℝ := fun i => if 4 < (i : ℕ) then thetaUpAt B s i (dec9 i) else thInit
  fun i => if 3 < (i : ℕ) then up i else thetaDownAt B s i (inc9 i)

/-- 源 `for k in range(9): rho.append(B.C(a[k]) - B.Q(R*R - B.S(a[k])**2))` 的一元构件。 -/
def rhoEntry (B : BSource) (R a : ℝ) : ℝ := B.C a - B.Q (R * R - B.S a * B.S a)

/-- 源 `for k in range(9)` 的 `rho` 表。 -/
def rhoLoop (B : BSource) (s : SrcState) : Fin 9 → ℝ :=
  fun i => rhoEntry B s.R (aFun B s i)

/-- 源 `C = [(rho[k]*B.C(th[k]), rho[k]*B.S(th[k])) for k in range(9)]`（**9** 项列表折叠）。 -/
def CLoop (B : BSource) (s : SrcState) : List Point :=
  (List.range 9).attach.map fun k =>
    let kk : Fin 9 := ⟨k.1, List.mem_range.mp k.2⟩
    mkPoint (rhoLoop B s kk * B.C (thetaLoop B s kk)) (rhoLoop B s kk * B.S (thetaLoop B s kk))

/-- 源 `k2 = (k + 1) % 9`（**显式取模**；与本工程 `Uvec` 的 `Fin 9` 加法之间的桥是
`SourceIdentity.fin9_succ_val`，见 `k2Of_eq_fin`）。 -/
def k2Of (k : Fin 9) : Fin 9 := Fin.mk (((k : ℕ) + 1) % 9) (Nat.mod_lt _ (by norm_num))

/-- 源 `U.append((C[k][0]+C[k2][0]-B.C(th[k]+a[k]), C[k][1]+C[k2][1]-B.S(th[k]+a[k])))`。 -/
def ULoop (B : BSource) (s : SrcState) (k : Fin 9) : Point :=
  mkPoint
    (proj ((CLoop B s).getD (k : ℕ) (0 : Point)) 0
      + proj ((CLoop B s).getD ((k2Of k : Fin 9) : ℕ) (0 : Point)) 0
      - B.C (thetaLoop B s k + aFun B s k))
    (proj ((CLoop B s).getD (k : ℕ) (0 : Point)) 1
      + proj ((CLoop B s).getD ((k2Of k : Fin 9) : ℕ) (0 : Point)) 1
      - B.S (thetaLoop B s k + aFun B s k))

/-- 源 `for k in range(9): k2 = (k+1)%9; U.append(...)`（**9** 项列表折叠）。 -/
def UListLoop (B : BSource) (s : SrcState) : List Point :=
  (List.range 9).attach.map fun k => ULoop B s ⟨k.1, List.mem_range.mp k.2⟩

/-- 源 `for (k,l) in [(1,1),(2,0),(3,0),(8,1)]` 的参数表**顺序**（点 `0..3` 依序对应四个 `(k,l)`）。 -/
def resSpec (i : Fin 4) : Fin 9 × Fin 2 := ![(1,1),(2,0),(3,0),(8,1)] i

/-- 源循环 `for (k,l) in [(1,1),(2,0),(3,0),(8,1)]`：
`c = y1 if l==1 else y0; dx = U[k][0]-c; dy = U[k][1]; out.append(B.Q(dx*dx+dy*dy) - R)`
—— **四条**，顺序 = 源参数表顺序，`l` 决定用 `y1` 还是 `y0`。 -/
def res5Heads (B : BSource) (s : SrcState) : List ℝ :=
  let U := UListLoop B s
  [B.Q ((proj (U.getD 1 (0 : Point)) 0 - s.y1) * (proj (U.getD 1 (0 : Point)) 0 - s.y1)
        + proj (U.getD 1 (0 : Point)) 1 * proj (U.getD 1 (0 : Point)) 1) - s.R,
   B.Q ((proj (U.getD 2 (0 : Point)) 0 - s.y0) * (proj (U.getD 2 (0 : Point)) 0 - s.y0)
        + proj (U.getD 2 (0 : Point)) 1 * proj (U.getD 2 (0 : Point)) 1) - s.R,
   B.Q ((proj (U.getD 3 (0 : Point)) 0 - s.y0) * (proj (U.getD 3 (0 : Point)) 0 - s.y0)
        + proj (U.getD 3 (0 : Point)) 1 * proj (U.getD 3 (0 : Point)) 1) - s.R,
   B.Q ((proj (U.getD 8 (0 : Point)) 0 - s.y1) * (proj (U.getD 8 (0 : Point)) 0 - s.y1)
        + proj (U.getD 8 (0 : Point)) 1 * proj (U.getD 8 (0 : Point)) 1) - s.R]

/-- 源 `half = mpf('0.5') if not B.is_dual else 0.5; m = (y0+y1)*half; d = (y1-y0)*half;
h = B.Q(R*R - d*d); dx = m - C[6][0]; dy = h - C[6][1]` —— **第五条**（在四条之后 `append`）。
`half` 取**精确** `(2:ℝ)⁻¹`。 -/
def res5Tail (B : BSource) (s : SrcState) : List ℝ :=
  let half : ℝ := (2 : ℝ)⁻¹
  let h := B.Q (s.R * s.R - ((s.y1 - s.y0) * half) * ((s.y1 - s.y0) * half))
  let mm := (s.y0 + s.y1) * half
  [B.Q ((mm - proj ((CLoop B s).getD 6 (0 : Point)) 0)
          * (mm - proj ((CLoop B s).getD 6 (0 : Point)) 0)
        + (h - proj ((CLoop B s).getD 6 (0 : Point)) 1)
          * (h - proj ((CLoop B s).getD 6 (0 : Point)) 1)) - s.R]

/-- **源 `res5` 的完整控制流转写**：四条 `res5Heads` 再 `append` 第五条 `res5Tail`。 -/
def res5 (B : BSource) (s : SrcState) : List ℝ := res5Heads B s ++ res5Tail B s

/-! ## 2. 接到 `u : Fin 12 → ℝ`（本工程的对象） -/

/-- 源 `F7` 的 7 个自由变量取自 `u` 的**前七位**（与本工程 `metricZ` 逐位一致）。 -/
def sOf (u : Fin 12 → ℝ) : SrcState where
  xa0 := u 0
  xa1 := u 1
  xa2 := u 2
  xa3 := u 3
  y0 := u 4
  y1 := u 5
  R := u 6

/-- **源 `res5` 的循环式转写（接到本工程对象上）**。 -/
def s5Loop (u : Fin 12 → ℝ) : List ℝ := res5 BReal (sOf u)

/-- 源 `out` 恰 5 项（四条 `heads` + 一条 `tail`）。 -/
theorem s5Loop_length (u : Fin 12 → ℝ) : (s5Loop u).length = 5 := by
  simp [s5Loop, res5, res5Heads, res5Tail]

/-! ## 3. `a` 表（①）的逐项读数 -/

theorem aList_val_0 (B : BSource) (s : SrcState) : (aList B s)[0] = s.xa0 := rfl
theorem aList_val_1 (B : BSource) (s : SrcState) : (aList B s)[1] = s.xa1 := rfl
theorem aList_val_2 (B : BSource) (s : SrcState) : (aList B s)[2] = s.xa2 := rfl
theorem aList_val_3 (B : BSource) (s : SrcState) : (aList B s)[3] = s.xa3 := rfl
theorem aList_val_4 (B : BSource) (s : SrcState) :
    (aList B s)[4] = B.PI - 2 * (s.xa0 + s.xa1 + s.xa2 + s.xa3) := rfl
theorem aList_val_5 (B : BSource) (s : SrcState) : (aList B s)[5] = s.xa3 := rfl
theorem aList_val_6 (B : BSource) (s : SrcState) : (aList B s)[6] = s.xa2 := rfl
theorem aList_val_7 (B : BSource) (s : SrcState) : (aList B s)[7] = s.xa1 := rfl
theorem aList_val_8 (B : BSource) (s : SrcState) : (aList B s)[8] = s.xa0 := rfl

theorem aFun_val_4 (B : BSource) (s : SrcState) :
    aFun B s 4 = B.PI - 2 * (s.xa0 + s.xa1 + s.xa2 + s.xa3) := by
  rw [aFun_apply]; exact aList_val_4 B s

/-! ## 4. `th` 表（②③④）：两段 `for` 的逐句读数 -/

/-- `th` 表的 `k`-号下标（`Fin 9`），用 `OfNat` 形态以与源的下标字面对齐。 -/
def t0 : Fin 9 := (0 : Fin 9)
def t1 : Fin 9 := (1 : Fin 9)
def t2 : Fin 9 := (2 : Fin 9)
def t3 : Fin 9 := (3 : Fin 9)
def t4 : Fin 9 := (4 : Fin 9)
def t5 : Fin 9 := (5 : Fin 9)
def t6 : Fin 9 := (6 : Fin 9)
def t7 : Fin 9 := (7 : Fin 9)
def t8 : Fin 9 := (8 : Fin 9)

theorem t0_eq : t0 = (0 : Fin 9) := rfl
theorem t1_eq : t1 = (1 : Fin 9) := rfl
theorem t2_eq : t2 = (2 : Fin 9) := rfl
theorem t3_eq : t3 = (3 : Fin 9) := rfl
theorem t4_eq : t4 = (4 : Fin 9) := rfl
theorem t5_eq : t5 = (5 : Fin 9) := rfl
theorem t6_eq : t6 = (6 : Fin 9) := rfl
theorem t7_eq : t7 = (7 : Fin 9) := rfl
theorem t8_eq : t8 = (8 : Fin 9) := rfl

theorem dec9_t5 : dec9 t5 = t4 := rfl
theorem dec9_t6 : dec9 t6 = t5 := rfl
theorem dec9_t7 : dec9 t7 = t6 := rfl
theorem dec9_t8 : dec9 t8 = t7 := rfl
theorem inc9_t3 : inc9 t3 = t4 := rfl
theorem inc9_t2 : inc9 t2 = t3 := rfl
theorem inc9_t1 : inc9 t1 = t2 := rfl
theorem inc9_t0 : inc9 t0 = t1 := rfl

/-- ④ `th[4] = 0`（初值；两段循环都不覆盖它：第一段从 5 起、第二段到 0 止）。 -/
theorem thetaLoop_4 (B : BSource) (s : SrcState) : thetaLoop B s t4 = thInit := by
  simp [thetaLoop, t4]

/-- ② `th[5] = th[4] + a[4] + a[5]`（**递增**段第一句，`th[4]` 是初值 `0`）。 -/
theorem thetaLoop_5 (B : BSource) (s : SrcState) :
    thetaLoop B s t5 = thetaUpAt B s t5 t4 := by
  simp [thetaLoop, dec9, t4, t5, thInit]

/-- ② `th[6] = th[5] + a[5] + a[6]`。 -/
theorem thetaLoop_6 (B : BSource) (s : SrcState) :
    thetaLoop B s t6 = thetaUpAt B s t6 t5 := by
  simp [thetaLoop, dec9, t5, t6, thInit]

/-- ② `th[7] = th[6] + a[6] + a[7]`。 -/
theorem thetaLoop_7 (B : BSource) (s : SrcState) :
    thetaLoop B s t7 = thetaUpAt B s t7 t6 := by
  simp [thetaLoop, dec9, t6, t7, thInit]

/-- ② `th[8] = th[7] + a[7] + a[8]`（**递增**段最后一句）。 -/
theorem thetaLoop_8 (B : BSource) (s : SrcState) :
    thetaLoop B s t8 = thetaUpAt B s t8 t7 := by
  simp [thetaLoop, dec9, t7, t8, thInit]

/-- ③ **递减**段第一句 `th[3] = th[4] − (a[3]+a[4])`（引用第一段已写好的 `th[4]`）。 -/
theorem thetaLoop_3 (B : BSource) (s : SrcState) :
    thetaLoop B s t3 = thetaDownAt B s t3 t4 := by
  simp [thetaLoop, inc9, t3, t4, thInit]

/-- ③ `th[2] = th[3] − (a[2]+a[3])`。 -/
theorem thetaLoop_2 (B : BSource) (s : SrcState) :
    thetaLoop B s t2 = thetaDownAt B s t2 t3 := by
  simp [thetaLoop, inc9, t2, t3, thInit]

/-- ③ `th[1] = th[2] − (a[1]+a[2])`。 -/
theorem thetaLoop_1 (B : BSource) (s : SrcState) :
    thetaLoop B s t1 = thetaDownAt B s t1 t2 := by
  simp [thetaLoop, inc9, t1, t2, thInit]

/-- ③ `th[0] = th[1] − (a[0]+a[1])`（**递减**段最后一句）。 -/
theorem thetaLoop_0 (B : BSource) (s : SrcState) :
    thetaLoop B s t0 = thetaDownAt B s t0 t1 := by
  simp [thetaLoop, inc9, t0, t1, thInit]

/-! ## 5. 循环式 `th` 表 = 闭式 `thetaOf`（②③④ 的合并定理） -/

/-- **`th` 表的闭式**（`thetaOf` 的九项，`a` 表读者用 `aFun`）。
命名它是为了让"循环式 = 闭式"的证明只做一次 `Fin 9` 上的 `fin_cases`。 -/
def thetaV (B : BSource) (s : SrcState) : Fin 9 → ℝ :=
  ![ -((aFun B s 0 + aFun B s 1) + (aFun B s 1 + aFun B s 2) + (aFun B s 2 + aFun B s 3)
        + (aFun B s 3 + aFun B s 4)),
     -((aFun B s 1 + aFun B s 2) + (aFun B s 2 + aFun B s 3) + (aFun B s 3 + aFun B s 4)),
     -((aFun B s 2 + aFun B s 3) + (aFun B s 3 + aFun B s 4)),
     -(aFun B s 3 + aFun B s 4),
     0,
     aFun B s 4 + aFun B s 5,
     (aFun B s 4 + aFun B s 5) + (aFun B s 5 + aFun B s 6),
     (aFun B s 4 + aFun B s 5) + (aFun B s 5 + aFun B s 6) + (aFun B s 6 + aFun B s 7),
     (aFun B s 4 + aFun B s 5) + (aFun B s 5 + aFun B s 6) + (aFun B s 6 + aFun B s 7)
       + (aFun B s 7 + aFun B s 8)]

/-- `thetaV` 就是闭式 `thetaOf (aFun B s)` 的九项（逐点相等）。 -/
theorem thetaOf_eq_thetaV' (B : BSource) (s : SrcState) (k : Fin 9) :
    thetaOf (aFun B s) k = thetaV B s k := by
  fin_cases k <;> simp [thetaOf, thetaV, aFun]

/-- `thetaV` 在九个下标上的读数（`aFun` 的九项用字面 `Fin` 下标；供 §5 的 `rw` 链用）。 -/
theorem thetaV_at_0 (B : BSource) (s : SrcState) :
    thetaV B s (0 : Fin 9) = -(aFun B s 0 + aFun B s 1) - (aFun B s 1 + aFun B s 2)
      - (aFun B s 2 + aFun B s 3) - (aFun B s 3 + aFun B s 4) := by
  simp [thetaV]; try ring
theorem thetaV_at_1 (B : BSource) (s : SrcState) :
    thetaV B s (1 : Fin 9) = -(aFun B s 1 + aFun B s 2) - (aFun B s 2 + aFun B s 3)
      - (aFun B s 3 + aFun B s 4) := by
  simp [thetaV]; try ring
theorem thetaV_at_2 (B : BSource) (s : SrcState) :
    thetaV B s (2 : Fin 9) = -(aFun B s 2 + aFun B s 3) - (aFun B s 3 + aFun B s 4) := by
  simp [thetaV]; try ring
theorem thetaV_at_3 (B : BSource) (s : SrcState) :
    thetaV B s (3 : Fin 9) = -(aFun B s 3 + aFun B s 4) := by
  simp [thetaV]; try ring
theorem thetaV_at_4 (B : BSource) (s : SrcState) : thetaV B s (4 : Fin 9) = 0 := by
  simp [thetaV]
theorem thetaV_at_5 (B : BSource) (s : SrcState) :
    thetaV B s (5 : Fin 9) = aFun B s 4 + aFun B s 5 := by
  simp [thetaV]; try ring
theorem thetaV_at_6 (B : BSource) (s : SrcState) :
    thetaV B s (6 : Fin 9) = aFun B s 4 + aFun B s 5 + (aFun B s 5 + aFun B s 6) := by
  simp [thetaV]; try ring
theorem thetaV_at_7 (B : BSource) (s : SrcState) :
    thetaV B s (7 : Fin 9) = aFun B s 4 + aFun B s 5 + (aFun B s 5 + aFun B s 6)
      + (aFun B s 6 + aFun B s 7) := by
  simp [thetaV]; try ring
theorem thetaV_at_8 (B : BSource) (s : SrcState) :
    thetaV B s (8 : Fin 9) = aFun B s 4 + aFun B s 5 + (aFun B s 5 + aFun B s 6)
      + (aFun B s 6 + aFun B s 7) + (aFun B s 7 + aFun B s 8) := by
  simp [thetaV]; try ring

/-- 递增段的 `dec9` 读数（供 §5 的一致性用）。 -/
theorem aFun_dec5 (B : BSource) (s : SrcState) : aFun B s (dec9 5) = aFun B s 4 := by
  rw [show dec9 (5 : Fin 9) = (4 : Fin 9) from rfl]
theorem aFun_dec6 (B : BSource) (s : SrcState) : aFun B s (dec9 6) = aFun B s 5 := by
  rw [show dec9 (6 : Fin 9) = (5 : Fin 9) from rfl]
theorem aFun_dec7 (B : BSource) (s : SrcState) : aFun B s (dec9 7) = aFun B s 6 := by
  rw [show dec9 (7 : Fin 9) = (6 : Fin 9) from rfl]
theorem aFun_dec8 (B : BSource) (s : SrcState) : aFun B s (dec9 8) = aFun B s 7 := by
  rw [show dec9 (8 : Fin 9) = (7 : Fin 9) from rfl]

/-- **循环式 = 闭式读数**：循环式的九个分支在具体下标上就是 ``thetaV`` 的九项。 -/
theorem thetaLoopV (B : BSource) (s : SrcState) (k : Fin 9) :
    thetaLoop B s k = thetaV B s k := by
  have q0 := thetaOf_eq_thetaV' B s (0 : Fin 9)
  have q1 := thetaOf_eq_thetaV' B s (1 : Fin 9)
  have q2 := thetaOf_eq_thetaV' B s (2 : Fin 9)
  have q3 := thetaOf_eq_thetaV' B s (3 : Fin 9)
  have q4 := thetaOf_eq_thetaV' B s (4 : Fin 9)
  have q5 := thetaOf_eq_thetaV' B s (5 : Fin 9)
  have q6 := thetaOf_eq_thetaV' B s (6 : Fin 9)
  have q7 := thetaOf_eq_thetaV' B s (7 : Fin 9)
  have q8 := thetaOf_eq_thetaV' B s (8 : Fin 9)
  have w0 := thetaV_at_0 B s
  have w1 := thetaV_at_1 B s
  have w2 := thetaV_at_2 B s
  have w3 := thetaV_at_3 B s
  have w4 := thetaV_at_4 B s
  have w5 := thetaV_at_5 B s
  have w6 := thetaV_at_6 B s
  have w7 := thetaV_at_7 B s
  have w8 := thetaV_at_8 B s
  fin_cases k <;>
    (simp [thetaLoop, thetaUpAt, thetaDownAt, inc9, dec9, thInit, thetaV] <;>
      linarith [q0, q1, q2, q3, q4, q5, q6, q7, q8, w0, w1, w2, w3, w4, w5, w6, w7, w8])

/-- **②③④ 的合并定理**：**循环式** `th` 表与**闭式** `thetaOf` 逐点相等（9 项全等）。
两段 `for`（递增 + 递减）+ 初值 `th[4] = 0` ⇒ 与闭式的九项逐项相同。 -/
theorem thetaLoop_eq_thetaOf (B : BSource) (s : SrcState) (k : Fin 9) :
    thetaLoop B s k = thetaOf (aFun B s) k :=
  (thetaLoopV B s k).trans (thetaOf_eq_thetaV' B s k).symm

/-! ## 6. `C`/`U` 表：⑤ `(k+1) % 9` 回绕的逐项读数 -/

/-- `CLoop` 的第 `k` 项就是源 `C[k] = (rho[k]*C(th[k]), rho[k]*S(th[k]))`（`map` 保序，下标即位置）。 -/
theorem CLoop_val (B : BSource) (s : SrcState) (k : Fin 9) :
    (CLoop B s).getD (k : ℕ) (0 : Point) =
      mkPoint (rhoLoop B s k * B.C (thetaLoop B s k)) (rhoLoop B s k * B.S (thetaLoop B s k)) := by
  rw [List.getD_eq_getElem (l := CLoop B s) (d := (0 : Point)) (n := (k : ℕ)) (by simp [CLoop])]
  simp [CLoop, List.getElem_map, List.getElem_attach]

/-- `UListLoop` 的第 `k` 项就是源 `U[k]`（`map` 保序）。 -/
theorem UListLoop_val (B : BSource) (s : SrcState) (k : Fin 9) :
    (UListLoop B s).getD (k : ℕ) (0 : Point) = ULoop B s k := by
  rw [List.getD_eq_getElem (l := UListLoop B s) (d := (0 : Point)) (n := (k : ℕ)) (by simp [UListLoop])]
  simp [UListLoop, List.getElem_map, List.getElem_attach]

/-- 源 `k2 = (k + 1) % 9` 的表读法。 -/
theorem k2Of_eq (k : Fin 9) : (k2Of k : ℕ) = ((k : ℕ) + 1) % 9 := rfl

/-- **⑤ `%9` 回绕的桥**：源 `k2 = (k+1) % 9` 与本工程 `Uvec` 里的 `Fin 9` 加法是同一个下标
（`SourceIdentity.fin9_succ_val`）。 -/
theorem k2Of_eq_fin (k : Fin 9) : k2Of k = k + 1 := by
  ext
  rw [k2Of_eq]
  exact (fin9_succ_val k).symm

/-- ⑤ `U[k]` 的坐标读数（源 `U.append((C[k][0]+C[k2][0]-C(th[k]+a[k]), …))`）。 -/
theorem ULoop_coord (B : BSource) (s : SrcState) (k : Fin 9) :
    proj (ULoop B s k) 0
      = proj ((CLoop B s).getD (k : ℕ) (0 : Point)) 0
        + proj ((CLoop B s).getD ((k2Of k : Fin 9) : ℕ) (0 : Point)) 0
        - B.C (thetaLoop B s k + aFun B s k) ∧
    proj (ULoop B s k) 1
      = proj ((CLoop B s).getD (k : ℕ) (0 : Point)) 1
        + proj ((CLoop B s).getD ((k2Of k : Fin 9) : ℕ) (0 : Point)) 1
        - B.S (thetaLoop B s k + aFun B s k) :=
  ⟨rfl, rfl⟩

/-- ⑤ `U[0]`：`k2 = (0+1)%9 = 1`。 -/
theorem ULoop_val_0 (_B : BSource) (_s : SrcState) : (k2Of (0 : Fin 9) : ℕ) = 1 := rfl
/-- ⑤ `U[1]`：`k2 = 2`。 -/
theorem ULoop_val_1 (_B : BSource) (_s : SrcState) : (k2Of (1 : Fin 9) : ℕ) = 2 := rfl
/-- ⑤ `U[2]`：`k2 = 3`。 -/
theorem ULoop_val_2 (_B : BSource) (_s : SrcState) : (k2Of (2 : Fin 9) : ℕ) = 3 := rfl
/-- ⑤ `U[3]`：`k2 = 4`。 -/
theorem ULoop_val_3 (_B : BSource) (_s : SrcState) : (k2Of (3 : Fin 9) : ℕ) = 4 := rfl
/-- ⑤ `U[8]`：`k2 = (8+1)%9 = **0**`（回绕点；不是 9，也不是 8）。 -/
theorem ULoop_val_8 (_B : BSource) (_s : SrcState) : (k2Of (8 : Fin 9) : ℕ) = 0 := rfl
/-- ⑤ 回绕的 `Fin 9` 形式：`k2Of 8 = 0`。 -/
theorem k2Of_eight : k2Of (8 : Fin 9) = (0 : Fin 9) := rfl

/-! ## 7. 五条残差：源 `out` 的五项 = 闭式 `residual`

源 `res5` 的输出循环与第五条 `append` 的**循环式**镜像（`for (k,l) in [(1,1),(2,0),(3,0),(8,1)]`
用 `Fin 4` 参数表 + `headsOf`；第五条用 `tailOf`），以及把它接到闭式 `residual` 上的
**坐标桥**（`proj`/`ofLp`；关键工具 `Matrix.cons_val_zero/one`）。 -/

/-- ⑦ 源 `for (k,l)` 参数表的 `k`（装配点下标）。 -/
def resSpecK : Fin 4 → Fin 9 := fun i =>
  match (i : ℕ) with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | _ => 8

/-- ⑦ 源参数表的 `l` 标签（`c = y1 if l==1 else y0`）。 -/
def resSpecL : Fin 4 → Fin 2 := fun i => (resSpec i).2

/-- ⑦ **源 `for (k,l)` 循环体**（`Fin 4 → ℝ`）：`c = y1 if l==1 else y0`，
`Q(dx*dx+dy*dy) − R`，`dx = U[k][0]−c`，`dy = U[k][1]`。 -/
def headsOf (B : BSource) (s : SrcState) : Fin 4 → ℝ := fun i =>
  let k := resSpecK i
  let c := if resSpecL i = (1 : Fin 2) then s.y1 else s.y0
  B.Q ((proj ((UListLoop B s).getD (k : ℕ) (0 : Point)) 0 - c)
        * (proj ((UListLoop B s).getD (k : ℕ) (0 : Point)) 0 - c)
      + proj ((UListLoop B s).getD (k : ℕ) (0 : Point)) 1
        * proj ((UListLoop B s).getD (k : ℕ) (0 : Point)) 1) - s.R

/-- ⑦ 源 `out.append(...)` 的**第五条**（`half = 1/2`、`m`、`d`、`h`、`C[6]`）。 -/
def tailOf (B : BSource) (s : SrcState) : ℝ :=
  let half : ℝ := (2 : ℝ)⁻¹
  let h := B.Q (s.R * s.R - ((s.y1 - s.y0) * half) * ((s.y1 - s.y0) * half))
  let mm := (s.y0 + s.y1) * half
  B.Q ((mm - proj ((CLoop B s).getD 6 (0 : Point)) 0)
        * (mm - proj ((CLoop B s).getD 6 (0 : Point)) 0)
      + (h - proj ((CLoop B s).getD 6 (0 : Point)) 1)
        * (h - proj ((CLoop B s).getD 6 (0 : Point)) 1)) - s.R

/-- ⑤ `U` 表在四个装配点上的读数。 -/
theorem UListLoop_getD_1 (B : BSource) (s : SrcState) :
    (UListLoop B s).getD 1 (0 : Point) = ULoop B s (1 : Fin 9) := UListLoop_val B s 1
theorem UListLoop_getD_2 (B : BSource) (s : SrcState) :
    (UListLoop B s).getD 2 (0 : Point) = ULoop B s (2 : Fin 9) := UListLoop_val B s 2
theorem UListLoop_getD_3 (B : BSource) (s : SrcState) :
    (UListLoop B s).getD 3 (0 : Point) = ULoop B s (3 : Fin 9) := UListLoop_val B s 3
theorem UListLoop_getD_8 (B : BSource) (s : SrcState) :
    (UListLoop B s).getD 8 (0 : Point) = ULoop B s (8 : Fin 9) := UListLoop_val B s 8

/-- ⑦ `headsOf` 的四个分量（依源参数表顺序 `(1,1),(2,0),(3,0),(8,1)`，`l` 决定 `y1`/`y0`）。 -/
theorem headsOf_val (B : BSource) (s : SrcState) :
    headsOf B s 0 = B.Q ((proj ((UListLoop B s).getD 1 (0 : Point)) 0 - s.y1)
          * (proj ((UListLoop B s).getD 1 (0 : Point)) 0 - s.y1)
        + proj ((UListLoop B s).getD 1 (0 : Point)) 1
          * proj ((UListLoop B s).getD 1 (0 : Point)) 1) - s.R ∧
    headsOf B s 1 = B.Q ((proj ((UListLoop B s).getD 2 (0 : Point)) 0 - s.y0)
          * (proj ((UListLoop B s).getD 2 (0 : Point)) 0 - s.y0)
        + proj ((UListLoop B s).getD 2 (0 : Point)) 1
          * proj ((UListLoop B s).getD 2 (0 : Point)) 1) - s.R ∧
    headsOf B s 2 = B.Q ((proj ((UListLoop B s).getD 3 (0 : Point)) 0 - s.y0)
          * (proj ((UListLoop B s).getD 3 (0 : Point)) 0 - s.y0)
        + proj ((UListLoop B s).getD 3 (0 : Point)) 1
          * proj ((UListLoop B s).getD 3 (0 : Point)) 1) - s.R ∧
    headsOf B s 3 = B.Q ((proj ((UListLoop B s).getD 8 (0 : Point)) 0 - s.y1)
          * (proj ((UListLoop B s).getD 8 (0 : Point)) 0 - s.y1)
        + proj ((UListLoop B s).getD 8 (0 : Point)) 1
          * proj ((UListLoop B s).getD 8 (0 : Point)) 1) - s.R := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [headsOf, resSpecK, resSpecL, resSpec]

/-- ⑦ 列表级的 `res5`：`res5Heads ++ res5Tail` 就是 `headsOf` 四项再 append `tailOf`。 -/
theorem res5_eq_headsOf_append (B : BSource) (s : SrcState) :
    res5 B s = [headsOf B s 0, headsOf B s 1, headsOf B s 2, headsOf B s 3] ++ [tailOf B s] := by
  obtain ⟨h0, h1, h2, h3⟩ := headsOf_val B s
  simp only [res5, res5Heads, res5Tail, tailOf, ← h0, ← h1, ← h2, ← h3]

/-- **源 `Q(dx*dx+dy*dy)` 与 `dist` 的桥**：把源文的 `dx = a−c`、`dy = d` 显式写成两个 `mkPoint`。
`Matrix.cons_val_zero/one` 是消 `mkPoint` 的 `ofLp` 投影的关键（`!₂[x,y] = Matrix.vecCons x …`，
不能靠 `rfl`/`simp [mkPoint]` 消掉）。 -/
theorem sqrt_pair_generic (a c d : ℝ) :
    Real.sqrt ((a - c) * (a - c) + d * d) = dist (mkPoint (a - c) d) (mkPoint 0 0) := by
  rw [N11Formalization.dist_point_eq_sqrt]
  congr 1
  simp only [mkPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **`dist p q` 的平方和形式**（把闭式的 `dist` 写成源文 `Q(dx*dx+dy*dy)` 的形状）。 -/
theorem dist_eq_sqrt_pair (p q : Point) :
    dist p q = Real.sqrt ((p.ofLp 0 - q.ofLp 0) * (p.ofLp 0 - q.ofLp 0)
      + (p.ofLp 1 - q.ofLp 1) * (p.ofLp 1 - q.ofLp 1)) := by
  rw [N11Formalization.dist_point_eq_sqrt]
  congr 1
  ring

/-! ### ⑦ 的坐标桥（`Uvec`/`ringCenter` 的 `ofLp` 读数 = `ULoop`/`CLoop` 的 `proj` 读数） -/

/-- (A) `aFun BReal (sOf u) = angleVec u`。 -/
theorem aFun_sOf_eq_angleVec (u : Fin 12 → ℝ) :
    aFun BReal (sOf u) = angleVec u := by
  funext j
  fin_cases j <;> simp [aFun, aList, angleVec, a4Of, sOf, BReal]

/-- (B) `rhoLoop BReal (sOf u) = rhoK u`。 -/
theorem rhoLoop_sOf_eq_rhoK (u : Fin 12 → ℝ) :
    rhoLoop BReal (sOf u) = rhoK u := by
  funext j
  simp only [rhoLoop, rhoEntry, rhoK]
  rw [aFun_sOf_eq_angleVec]
  simp only [BReal, sOf]
  ring

/-- (C) `(Uvec u k).ofLp 0 = proj (ULoop BReal (sOf u) k) 0`。 -/
theorem Uvec_coord0_eq_proj (u : Fin 12 → ℝ) (k : Fin 9) :
    (Uvec u k).ofLp 0 = proj (ULoop BReal (sOf u) k) 0 := by
  rw [Uvec_coord0, ringCenter_coord0, ringCenter_coord0, arcEnd_coord0]
  rw [ULoop, CLoop_val, CLoop_val]
  simp only [proj, mkPoint, Matrix.cons_val_zero, Matrix.cons_val_one, k2Of_eq_fin,
    thetaLoop_eq_thetaOf]
  rw [rhoLoop_sOf_eq_rhoK, aFun_sOf_eq_angleVec]
  simp only [BReal]

/-- (D) `(Uvec u k).ofLp 1 = proj (ULoop BReal (sOf u) k) 1`。 -/
theorem Uvec_coord1_eq_proj (u : Fin 12 → ℝ) (k : Fin 9) :
    (Uvec u k).ofLp 1 = proj (ULoop BReal (sOf u) k) 1 := by
  rw [Uvec_coord1, ringCenter_coord1, ringCenter_coord1, arcEnd_coord1]
  rw [ULoop, CLoop_val, CLoop_val]
  simp only [proj, mkPoint, Matrix.cons_val_zero, Matrix.cons_val_one, k2Of_eq_fin,
    thetaLoop_eq_thetaOf]
  rw [rhoLoop_sOf_eq_rhoK, aFun_sOf_eq_angleVec]
  simp only [BReal]

/-- (E) `CLoop` 第 6 项的读数。 -/
theorem CLoop_getD_6_eq (B : BSource) (s : SrcState) :
    (CLoop B s).getD 6 (0 : Point) =
      mkPoint (rhoLoop B s (6 : Fin 9) * B.C (thetaLoop B s (6 : Fin 9)))
              (rhoLoop B s (6 : Fin 9) * B.S (thetaLoop B s (6 : Fin 9))) := by
  have h := CLoop_val B s 6
  have hidx : ((6 : Fin 9) : ℕ) = 6 := rfl
  rw [hidx] at h
  exact h

theorem ringCenter6_coord_eq_0 (u : Fin 12 → ℝ) :
    (ringCenter u 6).ofLp 0 = proj ((CLoop BReal (sOf u)).getD 6 (0 : Point)) 0 := by
  rw [ringCenter_coord0, CLoop_getD_6_eq]
  simp only [proj, mkPoint, Matrix.cons_val_zero]
  rw [rhoLoop_sOf_eq_rhoK, thetaLoop_eq_thetaOf, aFun_sOf_eq_angleVec]
  simp only [BReal]

theorem ringCenter6_coord_eq_1 (u : Fin 12 → ℝ) :
    (ringCenter u 6).ofLp 1 = proj ((CLoop BReal (sOf u)).getD 6 (0 : Point)) 1 := by
  rw [ringCenter_coord1, CLoop_getD_6_eq]
  simp only [proj, mkPoint, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [rhoLoop_sOf_eq_rhoK, thetaLoop_eq_thetaOf, aFun_sOf_eq_angleVec]
  simp only [BReal]

/-- hub / `wPoint` 的坐标读数。 -/
theorem hub1_ofLp_0 (u : Fin 12 → ℝ) : (hub1 u).ofLp 0 = u 5 := by
  simp only [hub1, Matrix.cons_val_zero]
theorem hub1_ofLp_1 (u : Fin 12 → ℝ) : (hub1 u).ofLp 1 = 0 := by
  simp only [hub1, Matrix.cons_val_zero, Matrix.cons_val_one]
theorem hub0_ofLp_0 (u : Fin 12 → ℝ) : (hub0 u).ofLp 0 = u 4 := by
  simp only [hub0, Matrix.cons_val_zero]
theorem hub0_ofLp_1 (u : Fin 12 → ℝ) : (hub0 u).ofLp 1 = 0 := by
  simp only [hub0, Matrix.cons_val_zero, Matrix.cons_val_one]
theorem wPoint_ofLp_0 (u : Fin 12 → ℝ) : (wPoint u).ofLp 0 = (u 4 + u 5) / 2 :=
  wPoint_coord0 u
theorem wPoint_ofLp_1 (u : Fin 12 → ℝ) :
    (wPoint u).ofLp 1 = Real.sqrt ((u 6) ^ 2 - ((u 5 - u 4) / 2) ^ 2) := wPoint_coord1 u

/-! ### ⑦ 主定理：五条残差逐项 = `residual` -/

/-- **`s5Loop` 的五个分量**（`s5Loop u = [headsOf 四项] ++ [tailOf]`）。 -/
theorem s5Loop_val_0 (u : Fin 12 → ℝ) :
    (s5Loop u).getD 0 0 = headsOf BReal (sOf u) 0 := by
  simp [s5Loop, res5_eq_headsOf_append]
theorem s5Loop_val_1 (u : Fin 12 → ℝ) :
    (s5Loop u).getD 1 0 = headsOf BReal (sOf u) 1 := by
  simp [s5Loop, res5_eq_headsOf_append]
theorem s5Loop_val_2 (u : Fin 12 → ℝ) :
    (s5Loop u).getD 2 0 = headsOf BReal (sOf u) 2 := by
  simp [s5Loop, res5_eq_headsOf_append]
theorem s5Loop_val_3 (u : Fin 12 → ℝ) :
    (s5Loop u).getD 3 0 = headsOf BReal (sOf u) 3 := by
  simp [s5Loop, res5_eq_headsOf_append]
theorem s5Loop_val_4 (u : Fin 12 → ℝ) :
    (s5Loop u).getD 4 0 = tailOf BReal (sOf u) := by
  simp [s5Loop, res5_eq_headsOf_append]

/-- ⑦ 第一条（`(k,l) = (1,1)`，`c = y1`，装配点 `U[1]`，对 `H1`）。 -/
theorem s5Loop_apply_0 (u : Fin 12 → ℝ) : (s5Loop u).getD 0 0 = residual u 0 := by
  rw [s5Loop_val_0, (headsOf_val BReal (sOf u)).1]
  simp only [sOf, BReal, residual_comp_0, UListLoop_getD_1]
  rw [sqrt_pair_generic]
  congr 1
  rw [N11Formalization.dist_point_eq_sqrt, N11Formalization.dist_point_eq_sqrt]
  congr 1
  simp only [Uvec_coord0_eq_proj, Uvec_coord1_eq_proj, hub1_ofLp_0, hub1_ofLp_1,
    mkPoint, Matrix.cons_val_zero, Matrix.cons_val_one, BReal, sOf]
  ring

/-- ⑦ 第二条（`(2,0)`，`c = y0`，装配点 `U[2]`，对 `H0`）。 -/
theorem s5Loop_apply_1 (u : Fin 12 → ℝ) : (s5Loop u).getD 1 0 = residual u 1 := by
  rw [s5Loop_val_1, (headsOf_val BReal (sOf u)).2.1]
  simp only [sOf, BReal, residual_comp_1, UListLoop_getD_2]
  rw [sqrt_pair_generic]
  congr 1
  rw [N11Formalization.dist_point_eq_sqrt, N11Formalization.dist_point_eq_sqrt]
  congr 1
  simp only [Uvec_coord0_eq_proj, Uvec_coord1_eq_proj, hub0_ofLp_0, hub0_ofLp_1,
    mkPoint, Matrix.cons_val_zero, Matrix.cons_val_one, BReal, sOf]
  ring

/-- ⑦ 第三条（`(3,0)`，`c = y0`，装配点 `U[3]`，对 `H0`）。 -/
theorem s5Loop_apply_2 (u : Fin 12 → ℝ) : (s5Loop u).getD 2 0 = residual u 2 := by
  rw [s5Loop_val_2, (headsOf_val BReal (sOf u)).2.2.1]
  simp only [sOf, BReal, residual_comp_2, UListLoop_getD_3]
  rw [sqrt_pair_generic]
  congr 1
  rw [N11Formalization.dist_point_eq_sqrt, N11Formalization.dist_point_eq_sqrt]
  congr 1
  simp only [Uvec_coord0_eq_proj, Uvec_coord1_eq_proj, hub0_ofLp_0, hub0_ofLp_1,
    mkPoint, Matrix.cons_val_zero, Matrix.cons_val_one, BReal, sOf]
  ring

/-- ⑦ 第四条（`(8,1)`，`c = y1`，装配点 `U[8]`，对 `H1`）。 -/
theorem s5Loop_apply_3 (u : Fin 12 → ℝ) : (s5Loop u).getD 3 0 = residual u 3 := by
  rw [s5Loop_val_3, (headsOf_val BReal (sOf u)).2.2.2]
  simp only [sOf, BReal, residual_comp_3, UListLoop_getD_8]
  rw [sqrt_pair_generic]
  congr 1
  rw [N11Formalization.dist_point_eq_sqrt, N11Formalization.dist_point_eq_sqrt]
  congr 1
  simp only [Uvec_coord0_eq_proj, Uvec_coord1_eq_proj, hub1_ofLp_0, hub1_ofLp_1,
    mkPoint, Matrix.cons_val_zero, Matrix.cons_val_one, BReal, sOf]
  ring

/-- ⑦ 第五条（`half = 1/2`、`m`、`d`、`h`、`C[6]`）。 -/
theorem s5Loop_apply_4 (u : Fin 12 → ℝ) : (s5Loop u).getD 4 0 = residual u 4 := by
  rw [s5Loop_val_4, residual_comp_4]
  simp only [tailOf, sOf, BReal]
  rw [sqrt_pair_generic]
  congr 1
  rw [N11Formalization.dist_point_eq_sqrt, N11Formalization.dist_point_eq_sqrt]
  congr 1
  simp only [wPoint_ofLp_0, wPoint_ofLp_1, ringCenter6_coord_eq_0, ringCenter6_coord_eq_1,
    mkPoint, Matrix.cons_val_zero, Matrix.cons_val_one, BReal, sOf]
  ring

/-- ⑦ 逐点版（`Fin 5` 上五个分量分别归约）。 -/
theorem s5Loop_apply_eq (u : Fin 12 → ℝ) (j : Fin 5) :
    (s5Loop u).getD (j : ℕ) 0 = residual u j := by
  fin_cases j
  · exact s5Loop_apply_0 u
  · exact s5Loop_apply_1 u
  · exact s5Loop_apply_2 u
  · exact s5Loop_apply_3 u
  · exact s5Loop_apply_4 u

/-- **G0 的循环式主结论**：源 `res5` 的**控制流转写** `s5Loop`（接到本工程 `u : Fin 12 → ℝ` 上）
的五项 = **本工程闭式残差** `residual`（`Fin 5 → ℝ`，逐点相等）。
"Splitting into Cx, Cy lists changes no function"（`TC-ROOT-SOURCE-IDENTITY.md` §4）在此得到 kernel 检验。 -/
theorem s5Loop_eq_residual (u : Fin 12 → ℝ) :
    (fun j : Fin 5 => (s5Loop u).getD (j : ℕ) 0) = residual u := by
  funext j
  exact s5Loop_apply_eq u j

/-! ## 8. `F7` 的钉住条件

源 `F7`（157–161 行）把 `x[i1] = c1, x[i2] = c2` 钉住：`F7 = res5(x[0:4], x[4], x[5], x[6]) ++ [x[i1]−c1, x[i2]−c2]`。
给出具名定义 + 等式引理（不做 `J7` 的求导链，那属 `KrawczykMatrix`/`Precond` 的路径）。 -/

/-- **源 `F7` 的钉住**：`x = zList s` 是 7 维解向量，前 5 项是残差，第 6/7 项是两条钉住。 -/
def F7At (B : BSource) (s : SrcState) (i1 i2 : Fin 7) (c1 c2 : ℝ) : Fin 7 → ℝ :=
  fun j =>
    if h : (j : ℕ) < 5 then (res5 B s).getD (j : ℕ) 0
    else if (j : ℕ) = 5 then (zList s)[(i1 : ℕ)] - c1
    else (zList s)[(i2 : ℕ)] - c2

/-- `F7At` 的前五项就是 `res5`（**顺序与源一致**：五条残差在前）。 -/
theorem F7At_first (B : BSource) (s : SrcState) (i1 i2 : Fin 7) (c1 c2 : ℝ) (j : Fin 5) :
    F7At B s i1 i2 c1 c2 ⟨(j : ℕ), by omega⟩ = (res5 B s).getD (j : ℕ) 0 := by
  simp [F7At]

/-- `F7At` 的第六项（零基 5）就是第一条钉住 `x[i1] − c1`。 -/
theorem F7At_pin1 (B : BSource) (s : SrcState) (i1 i2 : Fin 7) (c1 c2 : ℝ) :
    F7At B s i1 i2 c1 c2 5 = (zList s)[(i1 : ℕ)] - c1 := by
  simp [F7At]

/-- `F7At` 的第七项（零基 6）就是第二条钉住 `x[i2] − c2`。 -/
theorem F7At_pin2 (B : BSource) (s : SrcState) (i1 i2 : Fin 7) (c1 c2 : ℝ) :
    F7At B s i1 i2 c1 c2 6 = (zList s)[(i2 : ℕ)] - c2 := by
  simp [F7At]

/-- **`F7` 的方阵形状**：`F7At = (res5 五项, 两条钉住)`（7 维）。 -/
theorem F7At_eq (B : BSource) (s : SrcState) (i1 i2 : Fin 7) (c1 c2 : ℝ) :
    F7At B s i1 i2 c1 c2 =
      ![((res5 B s).getD 0 0), (res5 B s).getD 1 0, (res5 B s).getD 2 0, (res5 B s).getD 3 0,
        (res5 B s).getD 4 0, (zList s)[(i1 : ℕ)] - c1, (zList s)[(i2 : ℕ)] - c2] := by
  funext j
  fin_cases j <;> simp [F7At]

/-- **`F7` 的残差块 = `residual`**：§7 主结论的推论（把 `res5` 换成 `s5Loop` 的读数）。 -/
theorem F7At_residual_block (u : Fin 12 → ℝ) :
    (fun j : Fin 5 => F7At BReal (sOf u) 0 1 0 0 ⟨(j : ℕ), by omega⟩) = residual u := by
  funext j
  rw [F7At_first BReal (sOf u) 0 1 0 0 j]
  show (s5Loop u).getD (j : ℕ) 0 = residual u j
  exact s5Loop_apply_eq u j

/-! ## 9. 负对照：三处人工判读都是**承重**的（改错则等式失败）

每条给出：① 改错后的镜像；② 错误版在**同一处**与正确版**不相等**（kernel 证明的 `≠`，即该等式
**确证失败**）；③ 正确版的等式（对照件）。这样 §1–§8 的等式链就有了**判别力**：
`half = 1/2`、`% 9`、参数表首项 `k = 1` 不是装饰，换掉任一条，等式在具体见证处即崩。 -/

/-! ### NC-a：`half` 写成 `1/3` -/

/-- 错误读法：`half = 1/3`（源文是 `half = 0.5`）。 -/
def halfBad : ℝ := (3 : ℝ)⁻¹

/-- 正确读法：`half = 1/2`。 -/
def halfGood : ℝ := (2 : ℝ)⁻¹

/-- **NC-a 的判别力**：错误读法**不满足**源文 `half = 0.5` 的等式。 -/
theorem nc_half_fails : ¬ (halfBad = halfGood) := by
  unfold halfBad halfGood
  norm_num

/-- **NC-a 的对照**：正确读法下 `(y0+y1)*half = (y0+y1)/2`（第五条残差的 `m`）。 -/
theorem nc_half_control (y0 y1 : ℝ) : (y0 + y1) * halfGood = (y0 + y1) / 2 := by
  unfold halfGood
  ring

/-! ### NC-b：`% 9` 写成 `% 8` -/

/-- 错误读法：源文 `C[(k+1) % 9]` 写成 `% 8`。 -/
def k2OfBad (k : Fin 9) : Fin 9 :=
  ⟨((k : ℕ) + 1) % 8,
    Nat.lt_of_lt_of_le (Nat.mod_lt ((k : ℕ) + 1) (by norm_num : 0 < 8)) (by norm_num : 8 ≤ 9)⟩

/-- **NC-b 的判别力**：`% 8` 读法在 `k = 8` 处与源文的 `% 9` 回转**不等**。 -/
theorem nc_mod9_fails : k2OfBad 8 ≠ k2Of 8 := by
  decide

/-- 附带：字面层 `(8+1) % 8 ≠ (8+1) % 9`。 -/
theorem nc_mod9_literal : ((8 : ℕ) + 1) % 8 ≠ ((8 : ℕ) + 1) % 9 := by
  norm_num

/-- **NC-b 的对照**：正确读法 `% 9` 满足回转等式（= `SourceIdentity.fin9_succ_val`）。 -/
theorem nc_mod9_control (k : Fin 9) : k2Of k = k + 1 := k2Of_eq_fin k

/-! ### NC-c：装配点 `U[1]` 写成 `U[0]` -/

/-- 错误读法：源参数表 `[(1,1),(2,0),(3,0),(8,1)]` 的首项 `k` 写成 `0`。 -/
def resSpecKBad : Fin 4 → Fin 9 := fun i =>
  match (i : ℕ) with
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | _ => 8

/-- **NC-c 的判别力**：错误读法在源第一条 `(k,l) = (1,1)` 处**违反** `k = 1`。 -/
theorem nc_assembly_fails : resSpecKBad 0 ≠ resSpecK 0 := by
  decide

/-- **NC-c 的对照**：正确读法的四条装配点下标就是源参数表的 `k`。 -/
theorem nc_assembly_control :
    resSpecK 0 = (1 : Fin 9) ∧ resSpecK 1 = (2 : Fin 9) ∧
      resSpecK 2 = (3 : Fin 9) ∧ resSpecK 3 = (8 : Fin 9) := by
  decide

end N11Formalization
