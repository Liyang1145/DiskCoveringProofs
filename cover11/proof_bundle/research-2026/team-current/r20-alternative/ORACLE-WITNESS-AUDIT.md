# ORACLE-WITNESS-AUDIT —— cover → 51-edge oracle 的**必要 witness 接口**审核

**范围（lead 指定）**：只审"真 cover ⇒ 51 边 oracle 的必要 witness 接口"。**给定**：canonical 9-ring + 2-hub q0**(6,7)** reduction（hub 的 q0 度 = 6、7 ✓）、嵌入的 refined nearest-site dual disk、`r ≤ 19/50`。
**不作假设**：**不**假设 `V`（oracle 最小 `t`）等于 cover 半径；**不**重审优化器。
源：`lead/FIXED-SWITCH-SOC-REDUCTION.md` §1–§4、`lead/DUAL-DISK-INTERFACE-AUDIT.md`（C801）。

## §1 oracle 结构（只取必要方向）

`V(U) = min t` s.t. `|c_i − U_{i−1}| ≤ t`、`|c_i − U_i| ≤ t`（18）+ `|c_s − z_f| ≤ t`（11 faces × 3 = 33），`z_f` **自由**（非外心定义），凸、无需 acute。
**关键点**：这些约束对真 cover 是**必要**的（下界方向）；⟹ 若在 8 维开关域上 `V ≥ R_upper`，则 `r_11 ≥ R_upper` ✓；**反向不成立**——`V ≤ r_true`，等号需要额外的物理/KTT lifting（本件不碰）。

## §2 18 条 endpoint 的必要 witness

真 cover + 该 canonical reduction：边界开关 `U_i` ∈ ∂D 被覆盖，且（给定）由**相邻**两环的 r-盘覆盖 ⟹ `|c_i − U_i| ≤ r`、`|c_{i+1} − U_i| ≤ r` ✓。
**退化重叠处理**：若 `U_i` 同时落入非相邻环盘（overlap），**必要方向不受影响**——相邻对的距离条件仍成立（witness 由 canonical 标注给出，不依赖唯一性）；⛔ 反向（"只有相邻两环覆盖它"）是**额外**假设，本件不使用（与 C894 撤回方向一致）。

## §3 33 条 face cone 的必要 witness（11 faces，含 boundary/artificial）

C801 提供构造：**每个 clipped cell 取内点**（hub 的 cell 可取 site 本身），**每条正长共享 Voronoi 边取内点**；每个内点 primal 顶点至少入射 3 个 cell（凸 cell 只有一个局部角扇）。
⇒ 对每个 face `f = {s1,s2,s3}`，存在公共 witness 点 `z_f* ∈ D`，使 `|c_{s} − z_f*| ≤ r` 对三个 site 同时成立（顶点情形由"covering assumption ⇒ 每个入射 site 距离 ≤ r"给出）✓
⇒ oracle 取 `z_f = z_f*`、`t = r` 可行 ⟹ 33 条**必要** ✓。
**伪/边界面（两个 hub faces `{9,10,0}`、`{9,10,4}`，以及含边界弧的面）**：witness 取 hub site 或该 clipped cell 内点（C801 明文允许 "for hubs it may be the site"）⟹ 条件仍为必要 ✓；此时 `z_f` 可与某 site **重合**（`z_f` 自由，允许退化）✓。
**退化情形**：零长 Voronoi 边/退化顶点（三点共线或重合）由 C801 的"仅取正长边内点"处理；若某 face 的 cell 退化为点/线段，witness 退化为该点，`|c_s − z_f| ≤ r` 仍由覆盖假设给出 ⟹ 必要方向保持 ✓。若 face 的 site triplet 退化（面积 0），oracle 的 3 条 cone 仍可为真（`z_f` 取该退化点），**不**产生虚假必要条件 ✓。

## §4 结论（本件可承重的）

1. **接口成立（必要方向）**：在给定的 q0(6,7) canonical reduction 与嵌入 dual disk 下，真 cover 的 9 开关 + 11 faces 给出 18 + 33 = **51 条必要条件**，witness 显式（端点 = 相邻环盘；face = clipped cell 内点/hub site），**含边界与两个 hub/artificial faces**；退化 overlap 与零长边**不破坏必要性**（仅使 witness 不唯一）。
2. **不可承重**：`V` 与 cover 半径的关系只有 `V ≤ r_true`；**不能**由 `V` 的数值直接读 cover 半径，也不能把 oracle 的可行性当作 cover 的充分条件（`z_f` 自由 ⇒ 解不必可嵌入、不需 inward rings、甚至不必覆盖 D，见 §1 源文明示）。
3. **未做**：不重审任何优化器；不涉及角度域/8 角全局义务（源 §4 的条件另行处理）；无 claim；不改 lead 文件。
