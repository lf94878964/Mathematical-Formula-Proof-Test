import Mathlib

/-! # 經典定理：康托爾、歐幾里得、√2 無理性 -/

/-- 康托爾定理：不存在 α 到 α 的冪集的滿射 -/
theorem cantor' (α : Type) (f : α → Set α) : ¬ Function.Surjective f := by
  intro h
  obtain ⟨a, ha⟩ := h {x | x ∉ f x}
  have h1 : a ∈ f a ↔ a ∈ {x | x ∉ f x} := by rw [ha]
  have h2 : a ∈ f a ↔ a ∉ f a := h1
  rcases em (a ∈ f a) with h3 | h3
  · exact h2.mp h3 h3
  · exact h3 (h2.mpr h3)

/-- 歐幾里得：質數有無窮多個（對任意 n，存在 ≥ n 的質數） -/
theorem infinite_primes' (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime := by
  have h1 : Nat.factorial n + 1 ≠ 1 := by
    have := Nat.factorial_pos n
    omega
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd h1
  refine ⟨p, ?_, hp⟩
  by_contra hlt
  push_neg at hlt
  have hdvd : p ∣ Nat.factorial n := Nat.dvd_factorial hp.pos hlt.le
  have h2 : p ∣ 1 := (Nat.dvd_add_right hdvd).mp hpd
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

/-- √2 無理性的核心：p² = 2q² 在正整數中無解（無窮遞降） -/
theorem no_sqrt_two : ∀ q p : ℕ, q ≠ 0 → p ^ 2 ≠ 2 * q ^ 2 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro p hq h
    have hp : 2 ∣ p :=
      Nat.Prime.dvd_of_dvd_pow Nat.prime_two (n := 2) ⟨q ^ 2, h⟩
    obtain ⟨k, rfl⟩ := hp
    have h2 : q ^ 2 = 2 * k ^ 2 := by nlinarith [h]
    have hq2 : 2 ∣ q :=
      Nat.Prime.dvd_of_dvd_pow Nat.prime_two (n := 2) ⟨k ^ 2, h2⟩
    obtain ⟨m, rfl⟩ := hq2
    have h3 : k ^ 2 = 2 * m ^ 2 := by nlinarith [h2]
    have hm : m ≠ 0 := by
      rintro rfl
      simp at hq
    exact ih m (by omega) k hm h3

/-- 直接引用 Mathlib：√2 是無理數 -/
example : Irrational (Real.sqrt 2) := irrational_sqrt_two
