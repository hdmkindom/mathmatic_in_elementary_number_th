import MathmaticInElementaryNumberTh.Basic

-- 禁用未使用变量警告
-- set_option linter.unusedVariables false

open Nat

open Finset

-- # Chapter 1 Greatest Common Divisor

-- ## 1.1 Exact Division

namespace Excat_Division

-- ### Definition 1.1 (Exact Division)

-- def m|n
def e_dvd (m n : ℤ) (h : m ≠ 0) : Prop := ∃ q : ℤ, n = q * m

-- ### Proposition 1.1 (Mutual Divisibility Implies Equality)

-- If m |n and n |m, then m = ±n.
theorem e_dvd_iff_eq (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    e_dvd m n hm ∧ e_dvd n m hn ↔ m = n ∨ m = -n := by
  constructor
  · rintro ⟨⟨q1, h1⟩, ⟨q2, h2⟩⟩
    have hq : q1 * q2 = 1 := by
      rw [h2] at h1
      rw [← mul_assoc] at h1 -- 去括号
      have h_1 : (1 - q1 * q2) * n = 0 := by
        linarith
      have h_2 : (1 - q1 * q2) = 0 ∨ n = 0 := by
        apply Int.mul_eq_zero.mp
        exact h_1
      have h_3 : n = 0 ∨ (1 - q1 * q2) = 0 := by
        apply Or.comm.mp
        exact h_2
      cases h_3
      · contradiction
      · linarith -- 直接用linarith就能解决,第一个分支矛盾,第二个分支直接linarith

    have hq1 : q1 = 1 ∨ q1 = -1 := by
      exact Int.eq_one_or_neg_one_of_mul_eq_one hq
    cases hq1 with -- 析取处理
    | inl hq1' => left; rw [h1, hq1']; ring
    | inr hq1' => right; rw [h1, hq1']; ring

  · rintro (h1 | h2)
    constructor
    · use 1
      rw [h1]
      ring
    · use 1
      rw [h1]
      ring
    constructor
    · use -1
      rw [h2]
      ring
    · use -1
      rw [h2]
      ring

-- ### Proposition 1.2 (Transitivity of Divisibility)

-- If d|m and m|n, then d|n.
theorem e_dvd_trans (d m n : ℤ) (hd : d ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) :
    e_dvd d m hd → e_dvd m n hm → e_dvd d n hd := by
  intro h_dvd_dm h_dvd_mn
  rcases h_dvd_dm with ⟨m', h1⟩ -- 展开 e_dvd 定义
  rcases h_dvd_mn with ⟨n', h2⟩
  use n' * m'
  rw [h2, h1]
  ring

-- ### Proposition 1.3 (Divisibility of Linear Combination)

-- If d|m and d|n, then d|am + bn for any a, b ∈Z.
theorem e_dvd_add_mul (d m n a b : ℤ) (hd : d ≠ 0) (hm : m ≠ 0) (hn : n ≠ 0) :
    e_dvd d m hd → e_dvd d n hd → e_dvd d (a * m + b * n) hd := by
  intro h_dvd_dm h_dvd_dn
  rcases h_dvd_dm with ⟨m', h1⟩
  rcases h_dvd_dn with ⟨n', h2⟩
  use a * m' + b * n'
  rw [h1, h2]
  ring

-- ### Proposition 1.4 (Bound of Divisors)

-- If m|n and n ≠ 0, then |m|≤|n|
theorem e_dvd_le (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    e_dvd m n hm → |m| ≤ |n| := by
  intro h_dvd_mn
  rcases h_dvd_mn with ⟨q, h1⟩

  have h_abs : |n| = |q| * |m| := by
    rw [h1, abs_mul]

  have hq : |q| ≥ 1 := by
    by_contra hq1 -- 反证法
    push_neg at hq1 -- 去否定
    have hq0 : |q| = 0 := by
      linarith [abs_nonneg q]
    have q0 : q = 0 := by
      exact abs_eq_zero.mp hq0
    rw [q0] at h1
    have h0 : n = 0 := by
      rw [h1, zero_mul] -- 出矛盾
    contradiction

  have h_abs' : |n| = |m| * |q| := by
    rw [h1, abs_mul]
    linarith

  have h_le : |m| * 1 ≤ |n| := by -- 中间步处理
    exact (mul_le_mul_of_nonneg_left hq (abs_nonneg m)).trans_eq h_abs'.symm
  linarith

-- ### Corollary 1.1 (Divisibility with Restriction Forces Zero)

-- If m|n and |n| < |m|, then n = 0
theorem e_dvd_abs_lt_zero (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    e_dvd m n hm → |n| < |m| → n = 0 := by
  intro h_dvd_mn h_lt
  have h_le : |m| ≤ |n| := by
    exact e_dvd_le m n hm hn h_dvd_mn
  linarith

end Excat_Division
