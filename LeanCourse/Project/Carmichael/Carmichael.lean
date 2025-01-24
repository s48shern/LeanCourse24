import LeanCourse.Project.Carmichael.Lemmata
import Mathlib

open Real Function Nat BigOperators Set Finset Algebra Int
open Classical
--open Nat.Squarefree

def isCarmichael (n : ℕ) := ¬ Nat.Prime n ∧ (∀ (a : ℤ), Int.gcd a n = 1 → (n:ℤ) ∣ a^(n-1)-1) ∧ n>1
lemma carmichael_not_prime {n:ℕ} (h: isCarmichael n) : ¬ Nat.Prime n := by exact h.1
lemma carmichael_def_property {n: ℕ} (h: isCarmichael n): (∀ (a : ℤ), Int.gcd a n = 1 → (n:ℤ) ∣ a^(n-1)-1) := h.2.1
lemma carmichael_ge_4 {n:ℕ} (h: isCarmichael n) : n ≥ 4 := by {
  have h':= h.2.2
  have h'': n ≠ 2 := by {
    by_contra hnot
    rw [hnot] at h
    exact h.1 Nat.prime_two
  }
  have h': n > 2 := Nat.lt_of_le_of_ne h' (_root_.id (Ne.symm h''))
  have h'': n ≠ 3 := by {
    by_contra hnot
    rw [hnot] at h
    exact h.1 Nat.prime_three
  }
  exact Nat.lt_of_le_of_ne h' (_root_.id (Ne.symm h''))
}
