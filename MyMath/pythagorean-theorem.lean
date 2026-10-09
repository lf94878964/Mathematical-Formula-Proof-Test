import Mathlib

open RealInnerProductSpace

/-! ## 一、面積與相似三角形類 -/

/-- 1. 歐幾里得《原本》I.47：以剪切保面積，
    兩條直角邊上的正方形各等於斜邊正方形被高分出的一個矩形 -/
theorem m01_euclid (a b c p q : ℝ)
    (h₁ : a^2 = c * p) (h₂ : b^2 = c * q) (h₃ : p + q = c) :
    a^2 + b^2 = c^2 := by
  calc a^2 + b^2 = c * p + c * q := by rw [h₁, h₂]
    _ = c * (p + q) := by ring
    _ = c^2 := by rw [h₃]; ring

/-- 2. 相似三角形：斜邊上的高把大三角形分成兩個與它相似的三角形 -/
theorem m02_similar (a b c p q : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h₁ : a / c = p / a) (h₂ : b / c = q / b) (h₃ : p + q = c) :
    a^2 + b^2 = c^2 := by
  have e₁ : a^2 = c * p := by
    field_simp at h₁
    nlinarith [h₁]
  have e₂ : b^2 = c * q := by
    field_simp at h₂
    nlinarith [h₂]
  calc a^2 + b^2 = c * p + c * q := by rw [e₁, e₂]
    _ = c * (p + q) := by ring
    _ = c^2 := by rw [h₃]; ring

/-- 3. 周髀算經（弦圖）：大正方形 (a+b)² = 小正方形 c² + 四個直角三角形 -/
theorem m03_zhoubi (a b c : ℝ)
    (h : (a + b)^2 = c^2 + 4 * (a * b / 2)) : a^2 + b^2 = c^2 := by
  nlinarith [h]

/-- 4. 婆什迦羅（Bhaskara）：c² = 四個三角形 + 邊長 (b−a) 的小正方形 -/
theorem m04_bhaskara (a b c : ℝ)
    (h : c^2 = 4 * (a * b / 2) + (b - a)^2) : a^2 + b^2 = c^2 := by
  nlinarith [h]

/-- 5. 加菲爾德（Garfield）總統的梯形：梯形面積兩種算法 -/
theorem m05_garfield (a b c : ℝ)
    (h : (a + b) / 2 * (a + b) = 2 * (a * b / 2) + c^2 / 2) :
    a^2 + b^2 = c^2 := by
  nlinarith [h]

/-- 6. 達文西：六邊形被對稱軸分成全等兩半，兩種切法面積相等 -/
theorem m06_davinci (a b c : ℝ)
    (h : a^2 + b^2 + 2 * (a * b / 2) = c^2 + 2 * (a * b / 2)) :
    a^2 + b^2 = c^2 := by
  linarith [h]

/-- 7. 愛因斯坦：相似圖形的面積與斜邊平方成正比，
    且大三角形面積 = 兩個小三角形面積之和 -/
theorem m07_einstein (a b c k S S₁ S₂ : ℝ) (hk : k ≠ 0)
    (hS : S = k * c^2) (h₁ : S₁ = k * a^2) (h₂ : S₂ = k * b^2)
    (hsum : S = S₁ + S₂) : a^2 + b^2 = c^2 := by
  have h : k * (a^2 + b^2) = k * c^2 := by nlinarith [hS, h₁, h₂, hsum]
  exact mul_left_cancel₀ hk h

/-! ## 二、圓與幾何定理類 -/

/-- 8. 圓冪定理：以 B 為圓心、b 為半徑作圓，AC 為切線，
    割線 AB 過圓心，故 a² = (c−b)(c+b) -/
theorem m08_power_of_point (a b c : ℝ)
    (h : a^2 = (c - b) * (c + b)) : a^2 + b^2 = c^2 := by
  nlinarith [h]

/-- 9. 阿波羅尼奧斯中線定理：斜邊中線 m = c/2（泰勒斯定理） -/
theorem m09_apollonius (a b c m : ℝ)
    (hap : a^2 + b^2 = 2 * (m^2 + (c / 2)^2)) (hm : m = c / 2) :
    a^2 + b^2 = c^2 := by
  subst hm
  nlinarith [hap]

/-- 10. 托勒密定理：圓內接矩形，兩對角線乘積 = 兩組對邊乘積之和 -/
theorem m10_ptolemy (AC BD AB CD BC AD : ℝ)
    (hptol : AC * BD = AB * CD + BC * AD)
    (h₁ : AC = BD) (h₂ : AB = CD) (h₃ : BC = AD) :
    AC^2 = AB^2 + BC^2 := by
  subst h₁ h₂ h₃
  nlinarith [hptol]

/-- 11. 海倫公式：面積 ab/2 代入海倫公式，得 (a²+b²−c²)² = 0 -/
theorem m11_heron (a b c s : ℝ) (hs : s = (a + b + c) / 2)
    (hheron : (a * b / 2)^2 = s * (s - a) * (s - b) * (s - c)) :
    a^2 + b^2 = c^2 := by
  subst hs
  have h : (a^2 + b^2 - c^2)^2 = 0 := by nlinarith [hheron]
  have h' : a^2 + b^2 - c^2 = 0 := (pow_eq_zero_iff (two_ne_zero)).mp h
  linarith

/-- 12. 內切圓：面積 = r·s，其中 r = (a+b−c)/2 為直角三角形內切圓半徑 -/
theorem m12_incircle (a b c r s : ℝ) (hr : r = (a + b - c) / 2)
    (hs : s = (a + b + c) / 2) (harea : a * b / 2 = r * s) :
    a^2 + b^2 = c^2 := by
  subst hr hs
  nlinarith [harea]

/-! ## 三、三角函數類 -/

/-- 13. 餘弦定理，取 γ = π/2 -/
theorem m13_law_of_cosines (a b c γ : ℝ)
    (hlaw : c^2 = a^2 + b^2 - 2 * a * b * Real.cos γ)
    (hγ : γ = Real.pi / 2) : a^2 + b^2 = c^2 := by
  subst hγ
  rw [hlaw, Real.cos_pi_div_two]
  ring

/-- 14. 三角恆等式 sin²θ + cos²θ = 1，其中 a = c·sinθ，b = c·cosθ -/
theorem m14_trig (a b c θ : ℝ) (ha : a = c * Real.sin θ) (hb : b = c * Real.cos θ) :
    a^2 + b^2 = c^2 := by
  calc a^2 + b^2 = c^2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by
        rw [ha, hb]; ring
    _ = c^2 := by rw [Real.sin_sq_add_cos_sq, mul_one]

/-- 15. 三角：由餘弦差角公式 cos(θ−θ) = cos θ cos θ + sin θ sin θ = 1 推出 -/
theorem m15_cos_sub (a b c θ : ℝ) (ha : a = c * Real.sin θ) (hb : b = c * Real.cos θ) :
    a^2 + b^2 = c^2 := by
  have h := Real.cos_sub θ θ
  rw [sub_self, Real.cos_zero] at h
  calc a^2 + b^2 = c^2 * (Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ) := by
        rw [ha, hb]; ring
    _ = c^2 := by rw [← h, mul_one]

/-! ## 四、解析幾何與代數結構類 -/

/-- 16. 解析幾何（內積）：C 處的向量內積為 0（直角），
    則 |AB|² = |AC|² + |BC|² -/
theorem m16_dot_product (x₁ y₁ x₂ y₂ x₃ y₃ : ℝ)
    (h : (x₁ - x₃) * (x₂ - x₃) + (y₁ - y₃) * (y₂ - y₃) = 0) :
    (x₁ - x₂)^2 + (y₁ - y₂)^2 =
      ((x₁ - x₃)^2 + (y₁ - y₃)^2) + ((x₂ - x₃)^2 + (y₂ - y₃)^2) := by
  nlinarith [h]

/-- 17. 泰勒斯圓：A=(−r,0)，B=(r,0)，C=(x,y) 在圓 x²+y²=r² 上，
    則 |AC|² + |BC|² = |AB|² -/
theorem m17_thales (r x y : ℝ) (h : x^2 + y^2 = r^2) :
    ((x + r)^2 + y^2) + ((x - r)^2 + y^2) = (2 * r)^2 := by
  nlinarith [h]

/-- 18. 複數：|z|² = (實部)² + (虛部)² -/
theorem m18_complex (z : ℂ) :
    Complex.normSq z = z.re^2 + z.im^2 := by
  rw [Complex.normSq_apply]
  ring

/-- 19. 一般實內積空間：x ⊥ y ⇒ ‖x+y‖² = ‖x‖² + ‖y‖² -/
theorem m19_inner_product {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (h : ⟪x, y⟫_ℝ = 0) :
    ‖x + y‖^2 = ‖x‖^2 + ‖y‖^2 := by
  rw [norm_add_sq_real, h]
  ring

/-- 20. 微積分：固定一條直角邊 b = c(0)，讓另一直角邊 x 變動，
    斜邊 c(x) 滿足 c'(x) = x / c(x)，則 c² − x² 為常數 -/
theorem m20_calculus (c : ℝ → ℝ) (hc : ∀ x, 0 < c x)
    (hd : ∀ x, HasDerivAt c (x / c x) x) (x : ℝ) :
    c x ^ 2 - x ^ 2 = c 0 ^ 2 := by
  have key : ∀ t, HasDerivAt (fun t => c t * c t - t * t) 0 t := by
    intro t
    have h := ((hd t).mul (hd t)).sub ((hasDerivAt_id' t).mul (hasDerivAt_id' t))
    have hne : c t ≠ 0 := (hc t).ne'
    have e  : t / c t * c t = t := by field_simp
    have e' : c t * (t / c t) = t := by field_simp
    exact h.congr_deriv (by linarith)
  have hdiff : Differentiable ℝ (fun t => c t * c t - t * t) :=
    fun t => (key t).differentiableAt
  have hder : ∀ t, deriv (fun t => c t * c t - t * t) t = 0 :=
    fun t => (key t).deriv
  have h0 : c x * c x - x * x = c 0 * c 0 - 0 * 0 :=
    is_const_of_deriv_eq_zero hdiff hder x 0
  nlinarith [h0]
