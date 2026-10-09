import Mathlib

/-! # 數學歸納法：經典求和公式 -/

/-- 自訂遞迴定義：1 + 2 + ... + n -/
def sumTo : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumTo n + (n + 1)

/-- 高斯求和公式：2 · (1 + ... + n) = n(n+1) -/
theorem gauss_sum (n : ℕ) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [sumTo, mul_add, ih]
    ring

/-- 同一個公式，使用 Mathlib 的 Finset 寫法 -/
theorem gauss_finset (n : ℕ) :
    2 * ∑ i ∈ Finset.range (n + 1), i = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- 前 n 個奇數之和等於 n² -/
theorem sum_odd (n : ℕ) :
    ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- 前 n 個平方數之和：6 · Σ i² = n(n+1)(2n+1) -/
theorem sum_squares (n : ℕ) :
    6 * ∑ i ∈ Finset.range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- 等比級數：(x - 1) · (1 + x + ... + x^(n-1)) = x^n - 1 -/
theorem geom_sum' (x : ℤ) (n : ℕ) :
    (x - 1) * ∑ i ∈ Finset.range n, x ^ i = x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

/-- 伯努利不等式：(1 + x)^n ≥ 1 + n x，x ≥ -1 -/
theorem bernoulli (x : ℝ) (hx : -1 ≤ x) (n : ℕ) :
    1 + n * x ≤ (1 + x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ 1 + x := by linarith
    have h2 : 0 ≤ (k : ℝ) * x ^ 2 := by positivity
    calc 1 + ((k + 1 : ℕ) : ℝ) * x
        ≤ (1 + k * x) * (1 + x) := by push_cast; nlinarith [h2]
      _ ≤ (1 + x) ^ k * (1 + x) := by exact mul_le_mul_of_nonneg_right ih h1
      _ = (1 + x) ^ (k + 1) := by ring
