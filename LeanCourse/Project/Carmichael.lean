import Mathlib

open Real Function Nat BigOperators Set Finset Algebra Int
open Classical
--open Nat.Squarefree

--We can take a in ℕ for the condition fermat as n is always odd
lemma weak_carmichael_is_odd (n : ℕ): n > 2 ∧ (∀ (a : ℤ), (Int.gcd a n = 1 → (n:ℤ) ∣ a ^ (n - 1) - 1 )) → ¬ 2 ∣ n := by {
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
#leansearch "prime maximum power divisor."
theorem Korselt (n : ℕ) (hp: ¬ Nat.Prime n ∧ n > 1) : isCarmichael n ↔ (Squarefree n ∧ (∀ p, Nat.Prime p → p ∣ n → (p-1:ℤ) ∣ (n-1:ℤ))) :=
  by {
    constructor
    . intro h
      rw [isCarmichael] at h
      have h:= h.2.1
      have hsq: Squarefree n := by{
        rw [@squarefree_iff_prime_squarefree]
        by_contra hnot
        simp at hnot
        obtain ⟨p, hp, hd⟩:=hnot
        have hd: ∃ k,∃ n', k≥ 2 ∧ p^k*n'=n ∧ Nat.gcd p n' = 1 := by {
          rename_i h_1
          simp_all only [not_false_eq_true, gt_iff_lt, and_self, implies_true, true_and, ge_iff_le, exists_and_left]
          obtain ⟨left, right⟩ := h_1
          obtain ⟨m, hn⟩ := hd
          use p.maxPowDiv m + 2
          constructor
          · linarith
          · use m /  (p ^ (p.maxPowDiv m))
            constructor
            · calc p ^ (p.maxPowDiv m + 2) * (m /  (p ^ (p.maxPowDiv m))) = (p ^ (p.maxPowDiv m) * p ^ 2) * (m /  (p ^ (p.maxPowDiv m))) := by ring_nf
              _ = p ^ 2 * p ^ p.maxPowDiv m * m /  (p ^ (p.maxPowDiv m)):= by {
                rw [@npow_mul_comm]
                refine Eq.symm (Nat.mul_div_assoc (p ^ 2 * p ^ p.maxPowDiv m) ?H)
                exact maxPowDiv.pow_dvd p m
              }
              _ = p ^ 2 * m * p ^ p.maxPowDiv m  /  (p ^ (p.maxPowDiv m))  := by rw [Nat.mul_right_comm]
              _ = p^2 *m* 1 := by {
                simp_all only [Nat.cast_mul, mul_one, _root_.mul_eq_mul_right_iff]
                have h : m ≠ 0 := by {
                  simp_all only [ne_eq]
                  intro a
                  subst a
                  simp_all only [CharP.cast_eq_zero, mul_zero, Int.gcd_zero_right, _root_.zero_le, tsub_eq_zero_of_le,
                    pow_zero, sub_self, dvd_refl, implies_true, not_lt_zero']
                }
                simp_all only [ne_eq, or_false]
                ring_nf
                have h: p > 0 := by {simp_all only [gt_iff_lt]; exact Nat.Prime.pos hp}
                refine Nat.div_eq_of_eq_mul_left ?H1 ?H2
                exact Nat.pos_pow_of_pos (p.maxPowDiv m) h
                exact Nat.mul_right_comm (p ^ 2) (p ^ p.maxPowDiv m) m
                }
              _ = n := by{
              subst hn
              simp_all only [Nat.cast_mul, mul_one, _root_.mul_eq_mul_right_iff]
              have h: p ^2 = p*p := by ring_nf
              simp_all only [true_or]
              }
            · refine Eq.symm (Nat.gcd_greatest ?h.right.hda ?h.right.hdb ?h.right.hd)
              · exact Nat.one_dvd p
              · exact Nat.one_dvd (m / p ^ p.maxPowDiv m)
              · intro x ha1 ha2
                rw [@dvd_one]
                rw [propext (dvd_prime hp)] at ha1
                by_contra h
                have h : x = p := by simp_all only [false_or, Nat.cast_mul]
                rw [h] at ha2
                obtain ⟨k, hn⟩ := ha2




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

lemma Korselts_criterion' (p0 p1 p2: ℕ) : Nat.Prime p0 ∧ Nat.Prime p1 ∧ Nat.Prime p2 ∧ (∃(k :ℕ), k>0 ∧ p0 = 6 * k + 1 ∧ p1 = 12 * k + 1 ∧ p2 = 18 * k + 1) → isCarmichael (p0 * p1 * p2) := by {
  rintro ⟨hp0, hp1, hp2, k, hk, hkp0, hkp1, hkp2⟩
  have hp0g: p0>1 := by exact Prime.one_lt hp0
  have hp1g: p1>1 := by exact Prime.one_lt hp1
  have hp2g: p2>1 := by exact Prime.one_lt hp2
  have hp01g: p0*p1 > 1:= by exact Right.one_lt_mul' hp0g hp1g
  rw [Korselt]
  constructor
  . refine Nat.squarefree_mul_iff.mpr ?intro.intro.intro.intro.intro.intro.intro.left.a
    constructor
    refine coprime_mul_iff_left.mpr ?intro.intro.intro.intro.intro.intro.intro.left.a.left.a
    constructor
    have hint: ¬ p0 ∣ p2 := by {
      rw [@prime_def_lt'] at hp2
      have hint: p0 < p2 := by linarith
      exact hp2.2 p0 hp0g hint
    }
    exact (Nat.Prime.coprime_iff_not_dvd hp0).mpr hint
    have hint: ¬ p1 ∣ p2 := by {
      rw [@prime_def_lt'] at hp2
      have hint: p1 < p2 := by linarith
      exact hp2.2 p1 hp1g hint
    }
    exact (Nat.Prime.coprime_iff_not_dvd hp1).mpr hint
    constructor
    refine Nat.squarefree_mul_iff.mpr ?intro.intro.intro.intro.intro.intro.intro.left.a.right.left.a
    constructor
    have hint: ¬ p0 ∣ p1 := by {
      rw [@prime_def_lt'] at hp1
      have hint: p0 < p1 := by linarith
      exact hp1.2 p0 hp0g hint
    }
    exact (Nat.Prime.coprime_iff_not_dvd hp0).mpr hint
    constructor
    exact Irreducible.squarefree hp0
    exact Irreducible.squarefree hp1
    exact Irreducible.squarefree hp2
  intro p hp hpp
  have hp2: p=p0 ∨ p=p1 ∨ p=p2:= by{
    by_contra hcont
    simp at hcont
    rw [propext (Prime.dvd_iff_not_coprime hp)] at hpp
    rw [@coprime_mul_iff_right] at hpp
    rw [@coprime_mul_iff_right] at hpp
    simp at hpp
    have hpp0: p.Coprime p0:= by {
      have hint: ¬ p ∣ p0 := by {
        rw [@prime_def_lt'] at hp0
        by_cases hc: p < p0
        exact hp0.2 p (Prime.two_le hp) hc
        simp at hc
        exact not_dvd_of_pos_of_lt (zero_lt_of_lt hp0g) (Nat.lt_of_le_of_ne hc (Ne.symm hcont.1))
      }
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hint
    }
    have hpp1: p.Coprime p1:= by {
      have hint: ¬ p ∣ p1 := by {
        rw [@prime_def_lt'] at hp1
        by_cases hc: p < p1
        exact hp1.2 p (Prime.two_le hp) hc
        simp at hc
        exact not_dvd_of_pos_of_lt (zero_lt_of_lt hp1g) (Nat.lt_of_le_of_ne hc (Ne.symm hcont.2.1))
      }
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hint
    }
    have hpp2: p.Coprime p2:= by {
      have hint: ¬ p ∣ p2 := by {
        rw [@prime_def_lt'] at hp2
        by_cases hc: p < p2
        exact hp2.2 p (Prime.two_le hp) hc
        simp at hc
        exact not_dvd_of_pos_of_lt (zero_lt_of_lt hp2g) (Nat.lt_of_le_of_ne hc (Ne.symm hcont.2.2))
      }
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hint
    }
    exact ((hpp hpp0 hpp1) hpp2)
  }
  obtain hp|hp|hp:= hp2
  . rw [hp]
    rw [← Int.modEq_zero_iff_dvd]
    calc p0 * p1 * p2 - 1 ≡ 1 * p1 * p2 - 1 [ZMOD p0 - 1] := by {
      refine Int.ModEq.sub ?h₁ rfl
      refine Int.ModEq.mul ?_ rfl
      exact Int.ModEq.mul_right p1 (Int.modEq_sub p0 1)
    }
    _ ≡ k * 30 + k ^ 2 * 216 [ZMOD p0 - 1] := by rw [hkp1, hkp2]; push_cast; ring_nf; trivial
    _ ≡ 0 + 0 [ZMOD p0 - 1] := by {
      rw [hkp0]
      have hi: 6 * k ≡ 0 [ZMOD 6 * k] := by{
        refine Dvd.dvd.modEq_zero_int ?_
        trivial
      }
      refine Int.ModEq.add ?_ ?_
      . simp
        calc k * 30 ≡ 6*k*5 [ZMOD 6*k] := by ring_nf; trivial
        _ ≡ 0*5 [ZMOD 6*k] := Int.ModEq.mul_right 5 hi
        _ ≡ 0 [ZMOD 6*k] := by rfl
      . simp
        calc k^2 * 216 ≡ 6*k*(36*k) [ZMOD 6*k] := by ring_nf; trivial
        _ ≡ 0*(36*k) [ZMOD 6*k] := Int.ModEq.mul_right (36*k) hi
        _ ≡ 0 [ZMOD 6*k] := by ring_nf; trivial
    }
  . rw [hp]
    rw [← Int.modEq_zero_iff_dvd]
    calc p0 * p1 * p2 - 1 ≡ p0 * 1 * p2 - 1 [ZMOD p1 - 1] := by {
      refine Int.ModEq.sub_right 1 ?_
      refine Int.ModEq.mul_right p2 ?_
      exact Int.ModEq.mul_left p0 (Int.modEq_sub p1 1)
    }
    _ ≡ k * 24 + k ^ 2 * 108 [ZMOD p1 - 1] := by rw [hkp0, hkp2]; push_cast; ring_nf; trivial
    _ ≡ 0 + 0 [ZMOD p1 - 1] := by {
      rw [hkp1]
      have hi: 12 * k ≡ 0 [ZMOD 12 * k] := by{
        refine Dvd.dvd.modEq_zero_int ?_
        trivial
      }
      refine Int.ModEq.add ?_ ?_
      . simp
        calc k * 24 ≡ 12*k*2 [ZMOD 12*k] := by ring_nf; trivial
        _ ≡ 0*2 [ZMOD 12*k] := Int.ModEq.mul_right 2 hi
        _ ≡ 0 [ZMOD 12*k] := by rfl
      . simp
        calc k^2 * 108 ≡ 12*k*(9*k) [ZMOD 12*k] := by ring_nf; trivial
        _ ≡ 0*(9*k) [ZMOD 12*k] := Int.ModEq.mul_right (9*k) hi
        _ ≡ 0 [ZMOD 12*k] := by ring_nf; trivial
    }
  . rw [hp]
    rw [← Int.modEq_zero_iff_dvd]
    calc p0 * p1 * p2 - 1 ≡ p0 * p1 * 1 - 1 [ZMOD p2 - 1] := by {
      refine Int.ModEq.sub_right 1 ?_
      refine Int.ModEq.mul_left (p0*p1) (Int.modEq_sub p2 1)
    }
    _ ≡ k * 18 + k ^ 2 * 72 [ZMOD p2 - 1] := by rw [hkp0, hkp1]; push_cast; ring_nf; trivial
    _ ≡ 0 + 0 [ZMOD p2 - 1] := by {
      rw [hkp2]
      have hi: k*18 ≡ 0 [ZMOD k*18] := by{
        refine Dvd.dvd.modEq_zero_int ?_
        trivial
      }
      refine Int.ModEq.add ?_ ?_
      . simp
        ring_nf; exact hi
      . ring_nf
        simp
        calc k^2 * 72 ≡ k*18*(4*k) [ZMOD k*18] := by ring_nf; trivial
        _ ≡ 0*(4*k) [ZMOD k*18] := Int.ModEq.mul_right (4*k) hi
        _ ≡ 0 [ZMOD k*18] := by ring_nf; trivial
    }
  constructor
  refine not_prime_mul ?intro.intro.intro.intro.intro.intro.intro.hp.left.a1 ?intro.intro.intro.intro.intro.intro.intro.hp.left.b1
  exact Ne.symm (Nat.ne_of_lt hp01g)
  exact Ne.symm (Nat.ne_of_lt hp2g)
  exact Right.one_lt_mul' hp01g hp2g
}

@[simp] lemma isCarmichael' (n: ℕ): isCarmichael n ↔ ¬ Nat.Prime n ∧ ∀ (a : ℕ), n ∣ a^(n-1)-1 := by sorry

theorem carmichael_properties (k: ℕ) : isCarmichael k → ¬ 2 ∣ k ∧
  (∃ p1, ∃ p2, ∃ p3, Nat.Prime p1 ∧ p1 ∣ k ∧ Nat.Prime p2 ∧ p2 ∣ k ∧ Nat.Prime p3 ∧ p3 ∣ k ∧ ¬ p1=p2 ∧ ¬ p1=p3 ∧ ¬ p2=p3) ∧
  ∀ p, Nat.Prime p ∧ p ∣ k → p < Nat.sqrt k := by {
    intro h
    constructor
    . apply weak_carmichael_is_odd
      . by_cases h': k=2
        . absurd h.1
          rw [h']
          trivial
        . have h'':=h.2.2
          constructor
          . exact Nat.lt_of_le_of_ne h'' fun a ↦ h' (_root_.id (Eq.symm a))
          . exact h.2.1
    . constructor
      . sorry
      . intro p hp
        sorry
  }
