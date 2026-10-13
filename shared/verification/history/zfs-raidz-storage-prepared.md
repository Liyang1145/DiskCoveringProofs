# ZFS 阵列磁盘格式化记录

本次根据用户“格式化 ZFS 阵列的盘，那个没用”的明确指示执行。系统会话日期为 2026-10-06；执行主机的本地时钟当时显示 2026-10-07 08:12 +08:00，二者存在约一天的时钟差异，因此此处不把主机时间当作准确当前日期。

## 目标和结果

只处理原 `HDD_PULL` 六盘 RAIDZ 数据组：Windows 磁盘 4–9。写入前逐盘核对了硬盘序列号、约 1 TB 容量、非系统盘状态和单个 ZFS GPT 分区。已清除 ZFS 分区结构、重新初始化 GPT，并在每盘上建立一个独立 NTFS 卷：

| 磁盘 | 序列号 | 新盘符 | 卷标 | 可用空间 |
|---:|---|:---:|---|---:|
| 4 | ZFL7LHAV | F: | DATA-ZFL7LHAV | 约 931.37 GiB |
| 5 | ZFL7JJX5 | G: | DATA-ZFL7JJX5 | 约 931.37 GiB |
| 6 | ZFL7JMYM | H: | DATA-ZFL7JMYM | 约 931.37 GiB |
| 7 | ZFL7M9J2 | I: | DATA-ZFL7M9J2 | 约 931.37 GiB |
| 8 | ZFL7M3L2 | J: | DATA-ZFL7M3L2 | 约 931.37 GiB |
| 9 | ZFL7KNWV | K: | DATA-ZFL7KNWV | 约 931.37 GiB |

独立复核确认盘符和序列号匹配、NTFS 健康、磁盘在线且非只读。这六盘现在是六个独立卷，没有 RAIDZ 冗余；约 5.46 TiB 的总可用空间不能视作一个有冗余的阵列。

格式化前已存在的 D:、E: 两个 Kingston SSD NTFS 卷未由本次操作改动。C: 和 EFI 系统盘也未改动。格式化后 C: 仍约有 4.36 GiB 可用空间，故新增空间是 F:–K: 独立数据卷，不是扩展 C:。

## 数据恢复边界

六盘原 ZFS 分区/池元数据已移除，原 `HDD_PULL` RAIDZ 不能按原样挂载。操作使用快速格式化，并未逐扇区覆写，不能称作安全擦除；部分旧数据仍可能留在介质扇区上。

## 证明工作关系

没有移动活动证明输入或输出，也没有停止/重启 n=25 原进程。其 B17 scheduler `SUMMARY.json` 已生成，处理了 66,857 个必要父：worker 阶段暂列 66,631 个严格完整、226 个待付；该 summary 明确声明它不是 fresh full-parent payment merge。

原完整父图审计 PID 12552 仍在真实运行；本次有界句柄等待未观察到终止，未取得退出码。其日志从 41,750 增至 42,000 个“whole conditional filling trees freshly accepted”；这只是进行中的重放进度，不是最终父图付款接受。`COMPLETE-PAYMENT-AUDIT/VERIFIED.json`、n=25 最终父接受和全局接受件尚未出现。

n=23、24 的正式接受件、终验流水线哈希及最终独立审计 exit 0 互相吻合；结论范围是计算机辅助 source proof，不是 Lean/Coq 形式化或第三方审查。
