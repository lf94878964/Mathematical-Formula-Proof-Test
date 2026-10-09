# 經典數學定理的 Lean 4 證明

> 這是作者無聊時隨手做的測試。
> 所有檔案已通過 Lean 編譯器驗證。

## 內容

| 檔案 | 主題 |
| --- | --- |
| `algebra.lean` | 完全平方、平方差、AM-GM、柯西-施瓦茲不等式、拉格朗日恆等式、三角不等式 |
| `induction.lean` | 高斯求和、奇數和、平方和、等比級數、伯努利不等式 |
| `classic.lean` | 康托爾定理、歐幾里得質數無窮、√2 無理性 |

## 環境

- Lean 4（透過 [elan](https://github.com/leanprover/elan) 安裝）
- [Mathlib](https://github.com/leanprover-community/mathlib4)

## 使用方式

```bash
lake new MyMath math
cd MyMath
lake exe cache get
```

把 `.lean` 檔案放進專案資料夾後，用 VS Code 開啟整個專案資料夾，或在命令列驗證：

```bash
lake env lean Algebra.lean
lake env lean Induction.lean
lake env lean Classic.lean
```

沒有輸出代表編譯通過。

## 備註

- 純屬娛樂與練習，沒有嚴肅的學術目的。
- 引理名稱與策略行為可能隨 Mathlib 版本變動。