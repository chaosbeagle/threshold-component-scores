# Build and audit

## Requirements

- Git and [elan](https://github.com/leanprover/elan), with its `lean` and `lake` commands on PATH.
- Bash for the supplied shell scripts (Linux, macOS, or Git Bash on Windows); alternatively use PowerShell below.
- Network access for the pinned toolchain, dependency sources, and official Mathlib cache on the first build.

The repository contains source files only. Dependency revisions are fixed in `lean/lake-manifest.json`, and the compiler is fixed in `lean/lean-toolchain`. Keep these files unchanged; do not run `lake update` when reproducing this version.

## Bash

From the repository root:

```bash
cd lean
bash build.sh
```

This downloads the official cache for the imported Mathlib modules, builds the local library from source, prints the types and axiom dependencies of every explicitly named theorem, and checks every imported constant in the project namespace. The dependency cache defaults to `lean/.cache/mathlib`; an existing `MATHLIB_CACHE_DIR` is respected.

To rerun only the audits after a successful build:

```bash
bash audit.sh
```

To run each step separately after dependency caches are available:

```bash
lake build
lake env lean AxiomAudit.lean
lake env lean KernelAudit.lean
```

## Windows PowerShell

From the repository root:

```powershell
Set-Location lean
if (-not $env:MATHLIB_CACHE_DIR) {
    $env:MATHLIB_CACHE_DIR = Join-Path $PWD '.cache/mathlib'
}
$mathlibModules = Get-ChildItem ThresholdComponentScores/*.lean |
    Select-String '^import Mathlib' |
    ForEach-Object { ($_.Line -split '\s+')[1] } |
    Sort-Object -Unique
lake exe cache get $mathlibModules
if ($LASTEXITCODE -ne 0) { throw 'Dependency cache download failed' }
lake build
if ($LASTEXITCODE -ne 0) { throw 'Lean build failed' }
lake env lean AxiomAudit.lean
if ($LASTEXITCODE -ne 0) { throw 'Theorem audit failed' }
lake env lean KernelAudit.lean
if ($LASTEXITCODE -ne 0) { throw 'Kernel audit failed' }
```

## Expected checks

- `lake build` exits successfully and compiles 17 proof modules plus the root library.
- `AxiomAudit.lean` checks all 181 explicitly named theorems.
- `KernelAudit.lean` checks all 485 imported project constants. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted; any other axiom makes the audit fail.

Build success checks the formal declarations. Their correspondence to the article is documented in [formal coverage](docs/formal-coverage.md). Complexity and clinical-validity claims are outside the Lean verification scope.

## 繁體中文

先安裝 Git 與 elan，從專案根目錄進入 `lean`，再執行 `bash build.sh`；Windows 也可使用上方的 PowerShell 指令。第一次執行需要下載固定版本的編譯器、依賴原始碼與官方 Mathlib 快取。請保留 `lean-toolchain` 與 `lake-manifest.json`，不要執行 `lake update` 變更依賴。

建置流程會編譯證明、列出 181 個具名定理的型別與公理依賴，並檢查 485 個專案常數。通過編譯表示對應的 Lean 宣告通過檢查；完整論文的計算複雜度分類與臨床效能不在此形式驗證範圍內。
