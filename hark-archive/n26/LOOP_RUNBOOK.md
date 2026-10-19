# n26 loop runbook
每轮：读 LOOP_STATE.md / STATUS.md / 本文件；看 /workspace/work/dcp-n11-lean/LOOP_STATE.md、free -g、ps（同时只一个重进程）。
标记格式「看护轮 RUNNING @<line> <时间 CST>」写在 LOOP_STATE.md 的 RUNNING 行；>4h 无进程即清。
环境：pip install --user -q python-flint mpmath numpy scipy cvxpy（容器重建后需重装）。每条命令 ≤110s，脚本须可续跑并原子写盘（tmp+os.replace）。
## 局部切片森林方法（local/，用于含/贴近候选 θ* 的盒）
- hp.py：arb 320 位 Schur 能量（零权杆与孤立自由点删除）；kkt2_122.json 提供 θ*、λ0。
- homog2.py：浮点 G、D（正乘子杆），prop.py → prop.json（u0、τ0=D⁺Gu0、v=Nu0、a、μ=11/200）。
- geom.py：区域与壳片；run_forest.py <秒>：certA 逐片逐段证书写 local/leaves/m*_s*.json，可续跑。
- certB.py <秒>：独立复核，状态 local/verB.json，可续跑；两者都过才算闭合。
- 新区域：改 geom.py 的区域定义/RHO0（certB.region_R 与 shells 需同步独立改）。
## 纪律
浮点只提议；闭合需 A+B；只算算术层；不推送、不开 issue/PR/评论。只有闭合/新复核证书/重要反例或阻塞才汇报。
