# Q0-KERNEL-FINAL-AUDIT —— q0 closure 完整证书的 interval `atan2` / ring mean-value 核源审

**范围**：只审 `lead/certify_q0_closure.py` 与其解析说明 `lead/CLOSURE-KERNEL-ANALYTIC-AUDIT.md` 的**核**（interval `atan2`、ring mean-value、`q ≥ qmin` 筛选、矩形跨 `qmin` 时的中心/延拓、三角退化、`discarded_upper` 覆盖）。
**不做**：不复述 radius transfer；不重跑长计算；不改 lead 文件；无 claim。

## §1 因子与确切域（源内逐条核对）

| 项 | 源中内容 | 审计 |
|---|---|---|
| `q` | `q = (u−v)² + 4uv sin²(a/2)`；在**genuine 域**上恒正，在**放宽盒域** `a∈[0,π], u,v∈[0,1]` 上取 `[0,4]` | ✓ 一致；注意放宽域含 `q = 0`（如 `u = v, a = 0`）⇒ 筛选/延拓必须处理 |
| `w` | `w = 2asin(R√q/2)`，`F = R²uv sin(a)/2 + (w − sin w)/2 + Cw − μ…`；`C ≥ 0`（line 9）⇒ `h(w) = (C+1/2)w − sin w/2` **递增** | ✓ 递增性用于把 `w` 的端点包络做成安全方向；`q = 0 ⇒ w = 0` 连续可延拓 |
| `√q` | `√q = |u − v e^{ia}|`，对 `u,v` 的绝对偏导 ≤ 1 | ✓ mean-value/Lipschitz 界合法（ring 的 mean-value 核） |
| `β` | `β = atan2(v sin a, u − v cos a)`，对 `q>0, 0<a<π` 落在 `[0,π]`；偏导 `(uv cos a − v²)/q, −v sin a/q, u sin a/q` | ✓ **全角域 `[0,π]`**（不是半平面）；导数公式只在 `q>0` 有效 |
| 角包络 | 源明文："direct angle enclosure uses nonnegative y and general x"，即直接**值域**包络 | ✓ 关键：角包络不依赖 `q>0` 的导数公式 ⇒ 在 `q→0` 仍安全 |
| 二次支持 | `Q(A,B) = max_{0≤y≤1}(Ay²+By)` 对系数单调；`scalar_quad` 取两端点 + 可能的凹顶点 | ✓ 与"非负 y / 系数单调"一致 |

## §2 `q ≥ qmin` 筛选与矩形跨边界

* `qmin(r) = 4sin²(π − 8asin r)/r²`（源另一处给出），配"九边界弧各 ≤ `2asin r` ⇒ `r ≥ sin(π/9)`"的域嵌套论证 ✓。
* **跨 `qmin` 边界的矩形**：
  (a) 源的因子在 `q` 上是**连续**的（`w`、`uv sin a`、`(w−sin w)/2`、`Cw` 都在 `q = 0` 有有限极限 ✓）；
  (b) `β` 在 `q = 0` **无定义**（`atan2(0,0)`），但**有界**（值域 ⊆ `[0,π]`）且源用"值域包络"而非导数 ⇒ **可延拓且包络安全** ✓；
  ⇒ **"矩形跨 `qmin` 时用中心是否合法"不成立为必要**：正确的做法是**整个矩形（含边界）**用**连续延拓**的因子包络，而不是取中心点 ✓；源实现的"direct angle enclosure + 非负 y/系数单调"正符合此要求 ✓（就核而言，无需以中心合法性为前提）。
* **筛选合法性**：`q ≥ qmin` 的剪枝只能用于**已被域嵌套论证排除**的区域（`r < sin(π/9)` 或弧长不允许）；对合法域内的盒，剪枝必须由**上界**判据承担（见 §3）✓。

## §3 `discarded_upper` 覆盖与 split 记账

* 源明文：**"All boxes initially cover the entire relaxed factor domain, outer float endpoints outward. Each split covers the parent including the shared boundary."** ⇒ 盒树的分裂是**覆盖式**的（子盒并集 ⊇ 父盒，含共享边界）✓；
* `lower` 只影响**终止/剪枝**（termination/pruning），`discarded_upper` 记的是按**上界**排除的盒；因分裂覆盖性成立，**所有被丢弃区域都落在被记录的 `discarded_upper` 盒的并集内** ✓；
* **审计保留**：① 剪枝（`lower`）与丢弃（`upper`）必须分开记账，不能用剪枝掩盖未证明区域；② 退化盒（`q = 0` 角点、`a ∈ {0,π}`、`u = 0` 或 `v = 0`）必须靠 §1 的连续延拓包络处理，否则丢弃记账会漏掉测度零但非空的边界面 ✓。

## §4 三角退化清单（源内覆盖情况）

| 退化 | 源的处理 | 结论 |
|---|---|---|
| `a = 0` 或 `a = π` | `uv sin a = 0`、`w = 2asin(R√q/2)` 有限；角包络为值域 | ✓ 连续，无缺口 |
| `u = 0` 或 `v = 0` | `q = u² + v² ∓ 2uv cos a` 退化为单点距离；`F` 首项为 0 | ✓ 连续 |
| `q = 0`（`u = v, a = 0`） | `w = 0`；`β` 无定义但值域包络 | ✓ 可延拓（`β` 用范围，不用导数） |
| 三角退化（三点共线/重合） | 不在本核内（属 face 侧几何）；本核只依赖 `q, a, u, v` | ✓ 本核不引入额外假设 |

## §5 结论（可承重 / 不可承重）

* **可承重（源内自洽）**：① ring mean-value 核（`√q = |u − ve^{ia}|`、绝对偏导 ≤ 1）与 `w` 的递增性（`C ≥ 0`）成立；② interval `atan2` 覆盖**全角域 `[0,π]`**，且**角包络用值域而非 `q>0` 导数** ⇒ `q = 0` 边界安全；③ 盒树分裂为覆盖式、`lower` 与 `upper` 记账可分离 ⇒ `discarded_upper` 的并集覆盖被丢区域；④ 退化清单（`a` 端点、`u`/`v` 为 0、`q = 0`）在连续延拓下无缺口。
* **不可承重**：本件**未**重跑证书、**未**独立验证 `C ≥ 0` 的 line-9 断言与 `qmin` 域嵌套（属其它件）；不含 radius transfer；不含 `q0(6,7)` 在 `r ∈ (3/8, 19/50]` 的排除。无 claim、无 lead 文件改动。

## §6 CORRECTION（撤回 §1 β 行与 §2 的"连续延拓"说法；改为逐行 guard 审计）

**撤回**：我曾写"`β` 在 `q = 0` 连续可延拓"——**错** ✗。`atan2(v sin a, u − v cos a)` 在 `u = v, a → 0` 时**沿不同路径极限不同**（无连续延拓）。同时也纠正：源 L100 之后**确有 `β` 的 mean-value 处理**（不只 direct 角包络）。连续延拓**不是**本核的立足点；**guard 才是**。

**逐行读 `certify_q0_closure.py` L80–108（源审计义务）**
| 行 | 内容 | 审计 |
|---|---|---|
| L82 | `q=(u−v)²+4uv sin²(a/2)`，结果**clamp 到 [0,4]**；`qmin=4sin²(π−8asin R)/R²` | ✓ 与 `q ≤ 4` 一致（后续 `den` 需要） |
| L83 | `if q.b < qmin.a: return None` | ✓ 只在**严格低于 qmin 下端点**时筛掉 ⇒ 保守 |
| L84–86 | `w=2asin(R√q/2)`；`h` 由**递增**函数（`C≥0`）作用于 `w` 的**外端** | ✓ 方向安全 |
| L87 | `direct` = 朴素区间包络 | ✓ 与 L97/L99/L107 的相交仅在两者**都是有效包络**时成立 |
| **L89–92（关键 guard）** | `if q.a>0:` 用导数式 `wa,wu,wv`（并 clip 到 `±L`）；`else:` 三个全取 `±L` | ✓ **回退是 Lipschitz 界，不是连续值前提**：`√q=|u−v e^{ia}|` 对 `(a,u,v)` 的偏导绝对值 ≤ 1（`uv sin a/√q ≤ 1` 亦然），再乘 `R/√(1−R²q/4) ≤ L=R/√(1−R²)` ⇒ `±L` 在 `q→0` 仍**成立** |
| **L98（β guard）** | `bet = [0,π] if q.a≤0 else atan2(...)` | ✓ `q.a≤0` 时用**值域**界（不依赖任何极限）；`q.a>0` 时 `atan2` 才有定义 |
| L99 | `old = direct ∩ mean`（取 max 下端/min 上端） | ✓ 二者均为有效包络时相交合法；此处 `mean` 尚不含 β 项 |
| **L100（关键 guard）** | `if q.a≤0 or a.a<0 or a.b≥pi.a: return direct2` | ✓ **β 的 mean-value 精化只在 `q.a>0` 且 `0≤a<π` 时启用** ⇒ 恰在 β 可微、导数式有效的域内；退化情形**提前返回**，不引入可微性假设 |
| L101–106 | `ba,bu,bv=∂β/∂(a,u,v)`，`betm` 取盒中点，`mean2 = center2 + Σ gg·(box−mid)` | ✓ 中点 `q>0` 有定义；`gg` 含 closure 项 `(hl−hr)db + (hl+hr)dw/2 − (hr if a-slot)` ✓ |
| L107 | 返回 `direct2 ∩ mean2` | ✓ 同样只在两者都有效时（L100 保证）成立 |

**结论**：核的正确性依赖 **两处 guard**（L89–92 的 `q.a>0`/L98 的 β 值域回退，以及 L100 的提前返回），**不依赖** `q=0` 处的任何连续延拓；`discarded_upper`/剪枝记账的口径同 §3（分裂覆盖式 + `lower` 仅影响终止）；本行审计不含重跑、不改 lead 文件。
