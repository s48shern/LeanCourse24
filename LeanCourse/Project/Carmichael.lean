import Mathlib

open Real Function Nat BigOperators Set Finset Algebra Int
open Classical
--open Nat.Squarefree

--We can take a in ℕ for the condition fermat as n is always odd
lemma carmichael_prop_is_odd (n : ℕ): n > 2 ∧ (∀ (a : ℤ), (Int.gcd a n = 1 → (n:ℤ) ∣ a ^ (n - 1) - 1 )) → ¬ 2 ∣ n := by {
  intro h2
  obtain ⟨h2, ha⟩:= h2
  specialize ha (n-1)
  have h: (n-1: ℤ).gcd (n) = 1 := by {
    have hh: (n-1:ℤ) = (n-1:ℕ) := by{
      refine Eq.symm (Int.natCast_pred_of_pos ?_)
      exact zero_lt_of_lt h2
    }
    --have hh: (m:ℕ)=m := by exact rfl
    rw[hh]
    norm_cast
    refine (coprime_self_sub_left ?h).mpr ?_
    exact one_le_of_lt h2
    exact Nat.gcd_one_left n
  }
  have ha:= ha h
  by_contra hnot
  rw [← Int.modEq_zero_iff_dvd] at ha
  have ha: (n - 1) ^ (n - 1) ≡ 1 [ZMOD n] := by exact Int.ModEq.add_right_cancel' (-1) ha
  have ha2: (-1)^(n-1) ≡ 1 [ZMOD n] := by
    calc (-1)^(n-1) ≡ (n - 1) ^ (n - 1) [ZMOD n] := by{
      refine Int.ModEq.pow (n - 1) ?_
      ring_nf
      exact Int.ModEq.symm Int.add_modEq_right
    }
    _ ≡ 1 [ZMOD n] := by exact ha
  have hend: (-1) ^ (n - 1) = -1 := by{
    refine Odd.neg_one_pow ?intro.h
    refine Nat.Even.sub_odd ?intro.h.h ?intro.h.hm ?intro.h.hn
    exact one_le_of_lt h2
    exact (even_iff_exists_two_nsmul n).mpr hnot
    trivial
  }
  have hend: (-1)^(n-1) ≡ -1 [ZMOD n] := by exact congrFun (congrArg HMod.hMod hend) (n:ℤ)
  have hend: -1 ≡ 1 [ZMOD n] := by exact Int.ModEq.trans (_root_.id (Int.ModEq.symm hend)) ha2
  have hend: 2 ≡ 0 [ZMOD n] := by exact Int.ModEq.symm (Int.ModEq.add_left_cancel (_root_.id (Int.ModEq.symm hend)) rfl)
  rw [Int.modEq_zero_iff_dvd] at hend
  norm_cast at hend
  have hend: n=2 := by exact Eq.symm (Nat.dvd_antisymm hnot hend)
  have hend: ¬ n>2 := by exact Eq.not_gt hend
  exact hend h2
}


structure Carmichael where
  n: ℕ
  notPrime : ¬ Nat.Prime n
  g1: n>1
  fermat: ∀ (a : ℤ), Int.gcd a n = 1 → (n:ℤ) ∣ a^(n-1)-1

def isCarmichael (n : ℕ):= ¬ Nat.Prime n ∧ (∀ (a : ℤ), Int.gcd a n = 1 → (n:ℤ) ∣ a^(n-1)-1) ∧ n>1
def squarefree (n : ℕ) := ∀ (x : ℕ), Nat.Prime x → ¬x * x ∣ n

theorem Korselt (n : ℕ) (hp: ¬ Nat.Prime n ∧ n > 1) : isCarmichael n ↔ (squarefree n ∧ (∀ p, Nat.Prime p → p ∣ n → (p-1) ∣ (n-1))) :=
  by {
    constructor
    . intro h
      rw [isCarmichael] at h
      have h:= h.2.1
      have hsq: squarefree n := by{
        rw [squarefree]
        by_contra hnot
        simp at hnot
        obtain ⟨p, hp, hd⟩:=hnot
        have hd: ∃ k,∃ n', k≥ 2 ∧ p^k*n'=n ∧ xgcd p n' = 1 := by {
          sorry
        }
        obtain ⟨k, n', hk, hpk, hpn⟩:=hd
        --have hcong: ∃ a, a ≅ 1+p (mod p^k)
        sorry
      }
      constructor
      . exact hsq
      . intro p hpp hpn
        sorry
    . intro h
      rw [isCarmichael]
      constructor
      . exact hp.1
      . constructor
        . intro a
          sorry
        . exact hp.2
  }

lemma Korselts_criterion' (k: ℕ) : k>0 ∧ Nat.Prime (6*k + 1) ∧ Nat.Prime (12*k+1) ∧  Nat.Prime (18*k+1) →
  ∀ (a : ℕ), xgcd a ((6*k + 1)*(12*k+1)*(18*k+1)) = 1 → ((6*k + 1)*(12*k+1)*(18*k+1)) ∣ a^(((6*k + 1)*(12*k+1)*(18*k+1))-1)-1 := by sorry

@[simp] lemma isCarmichael' (n: ℕ): isCarmichael (n : ℕ) ↔ ¬ Nat.Prime n ∧ ∀ (a : ℕ), n ∣ a^(n-1)-1 := by sorry

theorem carmichael_properties (k: ℕ) : isCarmichael k → ¬ 2 ∣ k ∧
  (∃ p1, ∃ p2, ∃ p3, Nat.Prime p1 ∧ p1 ∣ k ∧ Nat.Prime p2 ∧ p2 ∣ k ∧ Nat.Prime p3 ∧ p3 ∣ k ∧ ¬ p1=p2 ∧ ¬ p1=p3 ∧ ¬ p2=p3) ∧
  ∀ p, Nat.Prime p ∧ p ∣ k → p < Nat.sqrt k := by {
    intro h
    constructor
    . apply carmichael_prop_is_odd
      . by_cases h': k=2
        . absurd h.1
          rw [h']
          trivial
        . have h:=h.2.2
          exact Nat.lt_of_le_of_ne h fun a ↦ h' (_root_.id (Eq.symm a))
      . exact h.2.1
    . constructor
      . sorry
      . intro p hp
        sorry
  }
