import Mathlib

/-! # 經典代數公式與不等式 -/

/-- 完全平方公式 -/
theorem add_sq' (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

/-- 平方差公式 -/
theorem sq_diff (a b : ℝ) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by
  ring

/-- 二元算術-幾何平均不等式（AM-GM）的平方形式 -/
theorem two_mul_le_add_sq' (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- AM-GM：√(ab) ≤ (a+b)/2 的無根號版本：4ab ≤ (a+b)^2 -/
theorem four_mul_le_sq_add (a b : ℝ) : 4 * a * b ≤ (a + b) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- 二維柯西-施瓦茲不等式 -/
theorem cauchy_schwarz_two (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a * d - b * c)]

/-- 拉格朗日恆等式（二維） -/
theorem lagrange_identity (a b c d : ℝ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 := by
  ring

/-- 三角不等式（實數絕對值） -/
theorem triangle_ineq (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  exact abs_add x y