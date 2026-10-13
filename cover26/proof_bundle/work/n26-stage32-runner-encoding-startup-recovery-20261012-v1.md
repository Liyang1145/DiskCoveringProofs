# Stage32 prepared runner startup encoding recovery

Observed 2026-10-12 03:11:56 Asia/Shanghai.

Original stage32 discovery session5075 completed terminal0 with all4800
events. Actual proposal SHA256
`1251706ca5a589645fb5770abf2f33c09915a5e4cf80c4cea1827ccda76cef24`.
The first invocation of the newly prepared PowerShell runner failed before
executing Python: Windows PowerShell interpreted its BOM-less UTF8 Chinese
runtime directory literal using the system codepage, producing a different
path and a CommandNotFoundException.

Read-only checks showed no stage32 bundle, catalogue or publication target,
and no stage32 Python/WSL worker. No native event, build, acceptance or
publication ran in this failed startup. The completed discovery is preserved
and must not be repeated.

Fix only the newly prepared, not frozen/bound runners: construct the same
actual existing runtime directory from explicit character codepoints in
ASCII source. Apply the same fix to the not-yet-executed v9 runner. This
changes no verifier, mathematical predicate, model, acceptance or old report.
Retry the stage32 full chain after confirming the target still absent.
No WSL/service/process restart or runtime installation is involved.
