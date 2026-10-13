# DIRECT-PATCH-REPLAY — 独立直接 containment 核（120 局部叶，只读）

> 义务（lead 2026-09-26）：`replay_closed_dbm.py` 经 `known_patch(db)` 认证的最后 120 个局部叶，
> 可能隐性依赖历史分支（C913 / C914-corner / C916 / C915 / C918 / reflected）。要求写一个**只读、独立、
> 直接**的 containment 核：仅读 `cosine_dbm_local920.json` + C891 exact dyadic rootbox，逐叶验证
> raw8 直接 `q² ≤ C919²` 或 `C920²`；**不调用 known_patch、不信保存 patch 名字**；并核对半径
> `C919 = 191/25000`、`C920 = 729/50000` 与 `growth = 1/100000` 证书。
> 本目录只写 `direct_patch_replay.json` + 脚本；未改 lead；未重审 C891 root contraction；无子代理。

## 输入（sha256 已钉在输出 JSON 内）

| 文件 | sha256（前 32） | 角色 |
|---|---|---|
| `lead/cosine_dbm_local920.json` | `6706b42690a1d99d8f49523ff0d7d82f` | 全域树 5011 节点；120 个 patch 叶的精确 DBM 胞 |
| `lead/repaired_tc_krawczyk.json` | `0154400192cf677e22d8f06b14dda67a` | C891 exact dyadic root box（center_hex/radius_hex） |
| `lead/anisotropic_stress_ball_certificate.json` | `76b7f600b65cd7a3e99a35e12106814f` | C919 常数（rho=764/100000, growth=1/100000） |
| `lead/relative_stress_ball_certificate.json` | `beb2fd4f0ac504c5dc86fa62b08800b6` | C920 常数（rho=1458/100000, growth=1/100000） |

`cosine_dbm_local920.json` 的 sha256 **与 lead 自己 replay 记录一致**
（`lead/closed_dbm_replay.json` 的 `source_sha256 = 6706b426…aef987`）⇒ 读的是同一版本。

## 方法（独立性）

1. **不 import 任何 lead 模块**；chart 从定义重推：`θ_i = i·L − D·t_i`，`L = 2·asin(19/50)`，
   `D = 9L − 2π`；raw8 坐标 k（k=0..7）为角差 `θ_i − θ_6`（`i = (k−2) mod 9`）相对 C891 根的偏离
   ```
   h_k = (i−6)·L − D·(t_i − t_6) − (θ*_i − θ*_6)
   ```
   胞信息只用 `db[i][6] ≤ t_6 − t_i`、`db[6][i] ≥ t_i − t_6` 的 DBM 凸包（8 个坐标**独立**取凸包 ⇒ q² 只被**高估**，判 PASS 是保守的）。
2. **全精确有理算术（Fraction）**，不用 mpmath。仅两个超越输入以有理区间外包：
   - π：Machin `16·atan(1/5) − 4·atan(1/239)`，交错级数余项 ≤ 首个未取项（区间宽 7.0e-86）；
   - `asin(19/50)`：正项二项级数 + 比值界 `c_{k+1}/c_k ≤ x²`（区间宽 4.2e-139）。
   ⇒ L、D 的区间宽 ≤ 1.5e-85；根角区间半宽 ≤ 2.8e-08 rad（来自 C891 box 的 1e-9 半径，未重审）。
3. 判定：`hi(q²) ≤ 半径²` 才 PASS；`lo(q²) > 半径²` 才 FAIL；跨越则 UNDETERMINED。

## 结果（120/120 直接通过，无隐性旧分支依赖）

```
direct verdicts: PASS_C919 = 12 , PASS_C920 = 108 , FAIL_both = 0 , UNDETERMINED = 0
saved-label 交叉表（label 只用于对照，不参与计算）:
   C919-direct-DBM   n= 12   -> 全部判 C919
   C920-direct-DBM   n=108   -> 全部判 C920
```

- **没有任何叶**只满足 C913/C914/C916/C915/C918 或 reflected 分支而不满足直接 C919/C920
  ⇒ 这 120 个叶对历史 patch 分支**无隐性依赖**（这正是本轮要排除的）。
- 最紧的边距（`thr − hi(q²)`，精确有理）：
  - C919 组：id 4856 边距 2.605e-06（占阈值 95.54%）、id 4778 2.732e-06、id 4853 6.038e-06；最宽 2.531e-05。
  - C920 组：**id 4996 边距 6.529e-07（占阈值 99.69%）**、id 4958 2.755e-06、id 4823/4824 3.659e-06；最宽 1.537e-04。
  - 全部边距 > 0（精确有理比较），故即使最紧的 id 4996 也是**严格** PASS；且因 q² 走的是**放宽**凸包，
    该叶真实 max q² 只会更小 ⇒ 保守 PASS，无风险。
  - 另：这 120 个叶的**保存标签本身**也只有 `C919-direct-DBM`(12) 与 `C920-direct-DBM`(108) 两类，
    没有叶带 C913/C914/C916/C915/C918/reflected 旧名 ⇒ 旧分支既不在标签层、也不在直接 containment 层被需要。

## 半径与 growth 证书核对（精确有理）

| 项 | 核验 |
|---|---|
| `C919 = 191/25000` | `191/25000 = 764/100000` ✓ 与 `anisotropic_stress_ball_certificate.json` 的 `rho` 完全相同；`C919² = 36481/625000000` |
| `C920 = 729/50000` | `729/50000 = 1458/100000` ✓ 与 `relative_stress_ball_certificate.json` 的 `rho` 完全相同；`C920² = 531441/2500000000` |
| `growth = 1/100000` | 两证书 `growth` 字段均精确等于 `1/100000` ✓ |
| C919 正性 | `τ·B·G·q = 1/10·182·1892/1000·191/25000 = 8221213/31250000 = 0.2631 < 1` ✓（余量 0.7369） |
| C919 系数 | `μ/2 − C·q − quartic·q² = 108664567373/9375000000000000 = 1.1590887e-05 > 1/100000` ✓（余量 1.59e-06；quartic = 183716467/15000000 = 12.24776 与证书 12.24776446… 一致） |
| C920 正性 | `1468·495/1000·15363/1000000·729/50000 = 406916047791/2500000000000 = 0.16277 < 1` ✓ |
| C920 系数 | `μ/2 − C·q − quartic·q² = 31782564942993/3125000000000000000 = 1.0170421e-05 > 1/100000` ✓（余量 1.70e-07；quartic = 6489412381/3750000000 = 1.73050997 与证书 1.730509968… 一致） |
| 证书记录值 vs 精确值 | 两证书的 `coefficient_lower` 均 ≤ 本次精确值 ✓（记录值是区间下界，方向正确） |

## 对照（kernel 非空洞）

`direct_patch_replay_control.json`：同一代码路径，对叶 id 4436（判 C919）做扰动：
- 凸包放宽 `db[6][i] += 1/100` ⇒ `q² = [2.668e-04, 6.499e-04]` ⇒ **FAIL**（两侧都越界）✓
- 凸包按 1% 收窄 ⇒ `q² = [2.703e-08, 4.662e-05]` ⇒ 仍 **C919** ✓
- 保存标签从不进入计算（只 `db` 行参与），标签仅用于交叉表 ✓

## 作用域与缺口（勿越读）

1. 本核只验证**包含**：每个叶的 raw8 胞凸包落在 C919 或 C920 球内。**没有**重证 C919/C920 的
   finite-remainder/解析引理本身（那是在册 proved-interval claims）；本核只**精确复核**了这两条用到的
   半径常数与 growth 不等式。
2. C891 root contraction **未重审**（按要求）；根角区间的不确定度 2.8e-08 rad 直接进入 q² 区间。
3. q² 用 8 个坐标的独立凸包（放宽）⇒ PASS 保守；本轮无 UNDETERMINED，故每个叶都是严格 PASS。
4. reflected 分支本轮**不需要**（直接分支已全覆盖）；若后续有叶只满足 reflected，需单独核。
5. 本件不涉及"任意覆盖类穷尽"，也不改任何全局下界口径。

## 复现

```
py -3 -X utf8 r20_direct_patch_replay.py            # -> direct_patch_replay.json（1.0 s）
py -3 -X utf8 r20_direct_patch_replay_control.py    # -> direct_patch_replay_control.json
```
