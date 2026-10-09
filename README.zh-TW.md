[English](README.md) | **繁體中文**

# 閾值式連通元件評分的精確穩健性與計算複雜度

本專案研究圖模型中閾值式連通元件評分的精確穩健性保證與計算限制，並以 Lean 形式化驗證其語意核心。

模型受冠狀動脈鈣化評分啟發，結合閾值啟動、連通元件、最小元件大小，以及由最大強度決定的權重。研究結論適用於所定義的數學模型，不構成臨床效能驗證。

## 閱讀與重現

1. **論文：**[閱讀 PDF](paper/threshold-component-scores.pdf)。
2. **Lean 專案：**[瀏覽原始碼](lean/)與[形式驗證範圍](docs/formal-coverage.md)。
3. **固定依賴版本：**[Lean、Mathlib 與全部間接依賴版本](DEPENDENCIES.md)。
4. **編譯說明：**[編譯與稽核 Lean 專案](BUILD.md)。
5. **專案背景：**[緣起與研究目的](docs/project.zh-TW.md)。

## 研究結果與形式驗證範圍

論文探討有限狀態表示與原始評分像集的等價性、可達極值、無損的穩定連通元件摘要、帶有獨立邊界檢驗的分類不變半徑、單調性，以及計算複雜度。

Lean 原始碼涵蓋精確的有理數圖模型及其語意結果，包括有限狀態化、分數極值、摘要建構與有理數見證提升、分類不變半徑與邊界條件，以及非負且非遞減權重下的角點語意。

複雜度分類、困難性歸約、二進位編碼、位元長度與執行時間界限，以及共同偏移的等價性，仍屬於論文中的數學證明。具型別的角點程序是非可計算的數學規格。本專案並未宣稱整篇論文皆經 Lean 驗證；詳細對應請見[逐項形式驗證範圍](docs/formal-coverage.md)。

## 快速開始

安裝 [elan](https://github.com/leanprover/elan)、Git 與 Bash 後，執行：

```bash
git clone https://github.com/chaosbeagle/threshold-component-scores.git
cd threshold-component-scores/lean
bash build.sh
```

建置使用 Lean **4.32.0** 與儲存庫中的依賴鎖定檔，會編譯證明模組，並檢查定理型別及傳遞的核心公理依賴。Windows 指令與獨立稽核步驟請見 [BUILD.md](BUILD.md)。
