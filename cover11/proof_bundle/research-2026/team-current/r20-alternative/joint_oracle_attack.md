# joint_oracle_attack — 有界联合非凸攻击 min_P V>=R* 是否可信

**范围**：`joint_oracle_attack.py` / `.json` / 本 md（r20-alternative；不修改 v2；未 claim；无子 agent；纯 numeric）。

## 设定（canonical deficit simplex）
`widths = L − D·y`、`y ≥ 0`、`Σy = 1`、`D = 9L − 2π`、`L = 2·arcsin(0.38)`；`U` = widths 前角和角上的单位向量（θ₀=0）。
变量 = `y₁..y₈` + 44 free primal coords（11 sites + 11 aux）+ `r` = **53**；
约束 = 18 endpoints + 33 face cones（**与 fixed_oracle_v2 同一 SOC/长度单位 `r − |edge| ≥ 0`**，已审 r² vs r 单位）+ `y_i ≥ 0`(8) + `1 − Σy ≥ 0`。
目标 min r；starts ≤12：candidate、uniform、9 个 simple 顶点、1 asymmetric mix；每 run ≤400 iter；总 6.1 s < 30 s。

## 结果（`best r = 0.37998385311983746`，`n_below_R* = 0`）
| start | r | r − R* | success | min51 | Σy |
|---|---|---|---|---|---|
| **candidate（control）** | 0.379983853 | **−1.28e−15** | True | −2.1e−15 | 1.000000 |
| uniform | 0.393659620 | +1.368e−02 | True | −6.7e−16 | 1.000000 |
| vertex0/1/2 | 0.412808886 | +3.283e−02 | True | ~1e−14 | 1.000000 |
| vertex3 / vertex8 | 0.406901455 | +2.692e−02 | True | −1.0e−14 | 1.000000 |
| vertex4 | 0.406813259 | +2.683e−02 | **False**（min51 −4.1e−09）| | 1.000000 |
| vertex5 | 0.407576156 | +2.759e−02 | True | −3.2e−15 | 1.000000 |
| vertex6 | 0.407575938 | +2.759e−02 | True | +3.3e−16 | 1.000000 |
| vertex7 | 0.405939175 | +2.596e−02 | **False**（min51 −1.4e−05）| | 1.000000 |
| asymmetric_mix | 0.395338508 | +1.535e−02 | True | −4.5e−14 | 1.000000 |

## 判定（口径）
- **candidate control 恢复 `R*`（差 −1.3e−15）⇒ 单位与 canonical index 审校通过**；
- **0/12 starts 给出 `V < R* − 1e−7`**（且 51 边 residual、`Σy = 1`、domain 达标）⇒
  **`min_P V ≥ R*` 在本有界攻击下**未被证伪**（可信但非证明）**；
- 若曾命中 `V < R*`：只说明 **fixed-oracle 全球路线不成立**，**不是**实际 cover 反例；此类数值发现须保留待 **exact rational interior certificate**（本轮未触发）；
- vertex4 / vertex7 两次 `success=False`（min51 −4.1e−09 / −1.4e−05）⇒ 其 r 读数**不干净**，不作证据，也不构成下界；
- 全 numeric；无全局证明；v2 未改；sites/aux/widths 已逐 run 存入 `.json`。
