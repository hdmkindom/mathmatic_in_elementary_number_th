import MathmaticInElementaryNumberTh.Ch1_Greatest_Common_Divisor.Ch1_2_Division_with_remainder

-- 禁用未使用变量警告
-- set_option linter.unusedVariables false

open Nat

open Finset

-- # Chapter 1 Greatest Common Divisor

-- ## 1.3 Greatest Common Divisor

namespace Greatest_Common_Divisor

variable (n : ℕ)

-- ### Definition 1.2 (Divisor)

-- If d|n, then d is called a divisor of n.
def divisors : Finset ℕ := {d ∈ Ico 1 (n + 1) | d ∣ n} -- from mathlib

-- ### Definition 1.3 (Common Divisor)

-- For m, n ∈Z, if an integer d satisfies d |m and d |n,
-- then d is called a common divisor of m and n
def common_divisors (m n : ℕ) : Finset ℕ :=
  {d ∈ Ico 1 (min m n + 1) | d ∣ m ∧ d ∣ n}

-- ### Definition 1.4 (Greatest Common Divisor)

--For m, n ∈ Z, not both zero, the greatest common divisor of m and n,
-- denoted by gcd(m, n), is the largest positive common divisor of m and n.
def gcd (m n : ℕ) : ℕ := Nat.gcd m n -- from mathlib

-- ### Proposition 1.5.1 (The greatest common divisor is commutative)

-- gcd(m, n) = gcd(n, m)
theorem gcd_comm (m n : ℕ) : gcd m n = gcd n m := by
  exact Nat.gcd_comm m n -- from mathlib

-- ### Proposition 1.5.2 (The greatest common divisor divides both numbers)

-- If m|n, then gcd(m, n) = m
theorem gcd_eq_left (m n : ℕ) (hmn : m ∣ n) : gcd m n = m := by
  exact Nat.gcd_eq_left hmn -- from mathlib
-- If m|n, then gcd(m, n) = n
-- theorem gcd_eq_right (m n : ℕ) (hmn : m ∣ n) : gcd m n = n := by
--   rw [gcd_comm]
--   exact Nat.gcd_eq_right hmn -- from mathlib


-- ### Proposition 1.5.3 (The greatest common divisor divides both numbers)
-- In particular, gcd(m, 0) = m for any m ∈ Z with m ≠ 0

end Greatest_Common_Divisor
