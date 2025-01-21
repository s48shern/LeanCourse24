import LeanCourse.Project.Korselt
import Mathlib

open Real Function Nat BigOperators Set Finset Algebra Int
open Classical

lemma Chernick_construction {p0 p1 p2: ℕ} : Nat.Prime p0 ∧ Nat.Prime p1 ∧ Nat.Prime p2 ∧
  (∃(k :ℕ), k>0 ∧ p0 = 6 * k + 1 ∧ p1 = 12 * k + 1 ∧ p2 = 18 * k + 1)
  → isCarmichael (p0 * p1 * p2) := by {
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
  constructor
  intro p hp
  have hpp := hp.2
  have hp := hp.1
  have hp2: p=p0 ∨ p=p1 ∨ p=p2:= by{
    by_contra hcont
    simp only [not_or] at hcont
    rw [propext (Prime.dvd_iff_not_coprime hp)] at hpp
    rw [@coprime_mul_iff_right] at hpp
    rw [@coprime_mul_iff_right] at hpp
    simp only [not_and, ne_eq, and_imp] at hpp
    have hpp0: p.Coprime p0:= by {
      have hint: ¬ p ∣ p0 := by {
        rw [@prime_def_lt'] at hp0
        by_cases hc: p < p0
        exact hp0.2 p (Prime.two_le hp) hc
        simp only [not_lt] at hc
        exact not_dvd_of_pos_of_lt (zero_lt_of_lt hp0g) (Nat.lt_of_le_of_ne hc (Ne.symm hcont.1))
      }
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hint
    }
    have hpp1: p.Coprime p1:= by {
      have hint: ¬ p ∣ p1 := by {
        rw [@prime_def_lt'] at hp1
        by_cases hc: p < p1
        exact hp1.2 p (Prime.two_le hp) hc
        simp? at hc
        exact not_dvd_of_pos_of_lt (zero_lt_of_lt hp1g) (Nat.lt_of_le_of_ne hc (Ne.symm hcont.2.1))
      }
      exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hint
    }
    have hpp2: p.Coprime p2:= by {
      have hint: ¬ p ∣ p2 := by {
        rw [@prime_def_lt'] at hp2
        by_cases hc: p < p2
        exact hp2.2 p (Prime.two_le hp) hc
        simp only [not_lt] at hc
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
      apply Int.ModEq.mul_right p1 (Int.modEq_sub p0 1)
    }
    _ ≡ k * 30 + k ^ 2 * 216 [ZMOD p0 - 1] := by rw [hkp1, hkp2]; push_cast; ring_nf; trivial
    _ ≡ 0 + 0 [ZMOD p0 - 1] := by {
      rw [hkp0]
      have hi: 6 * k ≡ 0 [ZMOD 6 * k] := by{
        refine Dvd.dvd.modEq_zero_int ?_
        trivial
      }
      refine Int.ModEq.add ?_ ?_
      . simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_sub_cancel_right]
        calc k * 30 ≡ 6*k*5 [ZMOD 6*k] := by ring_nf; trivial
        _ ≡ 0*5 [ZMOD 6*k] := Int.ModEq.mul_right 5 hi
        _ ≡ 0 [ZMOD 6*k] := by rfl
      . simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_sub_cancel_right]
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
      . simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_sub_cancel_right]
        calc k * 24 ≡ 12*k*2 [ZMOD 12*k] := by ring_nf; trivial
        _ ≡ 0*2 [ZMOD 12*k] := Int.ModEq.mul_right 2 hi
        _ ≡ 0 [ZMOD 12*k] := by rfl
      . simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_sub_cancel_right]
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
      . simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, add_sub_cancel_right]
        ring_nf; exact hi
      . ring_nf
        simp only [reduceNeg, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat,
          neg_add_cancel_left]
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

lemma carmichael_def_property' {n: ℕ} (h: isCarmichael n): ∀ (a : ℤ), (n:ℤ) ∣ a^n-a := by {
  have h':= (Korselt).1 h
  have h': Squarefree n ∧ (∀ (p : ℕ), Nat.Prime p ∧ p ∣ n → (p:ℤ) - 1 ∣ (n:ℤ) - 1) := by{
    constructor
    exact h'.1
    exact h'.2.1
  }
  intro a
  obtain ⟨ setP, hsetP, hprime⟩ := exists_prime_decomposition (zero_lt_of_lt h.2.2)
  refine Int.modEq_iff_dvd.mp ?mp.right.right.intro.intro.a
  refine Int.ModEq.symm ?_
  refine (congruence_by_prime_decomposition (zero_lt_of_lt h.2.2) h'.1 hsetP).1 ?_
  intro p hsetp
  by_cases hcase: (a.gcd p = 1)
  obtain ⟨hsetp1,hsetp2⟩:= (hsetP p).1 hsetp
  have hsetP:= h'.2 p ((hsetP p).1 hsetp)
  have hp: Nat.Prime p ∧ p ∣ n := by{
    constructor
    exact hsetp1
    exact hsetp2
  }
  have hend:=n_pow_card_sub_one_eq_one hsetp1 hsetp2 (h'.2 p hp) h.2.2 (isCoprime_iff_gcd_eq_one.mpr hcase)
  calc a ^ n ≡ a*a^(n-1) [ZMOD ↑p] := by{
    rw [← Int.pow_succ']
    have h': n - 1 + 1 = n:= by{
      refine Nat.sub_add_cancel ?h
      exact one_le_of_lt h.2.2
    }
    rw [h']
  }
    _ ≡ a*1 [ZMOD ↑p] := by {
      exact Int.ModEq.mul_left a hend
    }
  ring_nf
  trivial
  have h2: (p:ℤ) ∣ a := by {
    rw [@eq_one_iff_not_exists_prime_dvd] at hcase
    simp only [not_forall, Classical.not_imp, Decidable.not_not] at hcase
    obtain ⟨p', hpp', hp'⟩:= hcase
    have hp' : (p':ℤ) ∣ (a.gcd ↑p:ℤ ) := by norm_cast
    have hp'p: (p':ℤ) ∣ (p:ℤ) := by {
      have haux: (a.gcd ↑p:ℤ) ∣ (p:ℤ) := by exact Int.gcd_dvd_right
      exact Int.dvd_trans hp' haux
    }
    have hp'p: (p':ℤ)=(p:ℤ) := by{
      norm_cast at hp'p
      norm_cast
      have hp:= ((hsetP p).1 hsetp).1
      exact (Nat.prime_dvd_prime_iff_eq hpp' hp).mp hp'p
    }
    rw [← hp'p]
    have haux: (a.gcd ↑p:ℤ) ∣ a := by exact Int.gcd_dvd_left
    exact Int.dvd_trans hp' haux
  }
  refine Int.ModEq.symm ((fun {n a b} ↦ Int.modEq_iff_dvd.mpr) ?_)
  refine Int.dvd_sub ?_ h2
  exact (Dvd.dvd.pow h2 (not_eq_zero_of_lt h.2.2))
}

lemma isCarmichael' {n: ℕ}: isCarmichael n ↔ (n > 1 ∧ ¬ Nat.Prime n ∧ ∀ (a : ℤ), (n:ℤ) ∣ a^n-a) := by{
  constructor
  . intro h
    have h':= (Korselt).1 h
    have h': Squarefree n ∧ (∀ (p : ℕ), Nat.Prime p ∧ p ∣ n → (p:ℤ) - 1 ∣ (n:ℤ) - 1) := by{
      constructor
      exact h'.1
      exact h'.2.1
    }
    unfold isCarmichael at h
    constructor
    . exact h.2.2
    constructor
    . exact h.1
    exact carmichael_def_property' h
  . intro hpn
    have han:=hpn.2.2
    have h1n:=hpn.1
    have hpn:=hpn.2.1
    unfold isCarmichael
    constructor
    exact hpn
    constructor
    . intro a ha
      refine Int.ModEq.dvd ?mpr.right.left.a
      have han:= han a
      have han: (n:ℤ) ∣ a* (a ^ (n-1) - 1):= by {
        have haux: a* (a ^ (n-1) - 1) = a ^ n - a := by {
          ring_nf
          rw [← Int.pow_succ']
          have h: n-1+1=n := by {
            refine Nat.sub_add_cancel (one_le_of_lt h1n)
          }
          rw [h]
        }
        rw [haux]
        exact han
      }
      have han: (n:ℤ) ∣ (a ^ (n-1) - 1) := by {
        refine dvd_of_dvd_mul_right_of_gcd_one han ?hab
        rw [← ha]
        exact Int.gcd_comm (↑n) a
      }
      exact Int.modEq_iff_dvd.mpr han
    exact h1n
}

theorem carmichael_primes_lt_sqrt {k: ℕ} (hintro: isCarmichael k) : ∀ p, Nat.Prime p ∧ p ∣ k → p < Real.sqrt k := by {
  intro p hp
  obtain ⟨hsqr, hm1, hpk, hnk⟩:= (Korselt.1 hintro)
  have hea:= (isCarmichael'.1 hintro).2.2
  have hnum: ((p:ℤ)-1)*((k:ℤ)/(p:ℤ))+((k:ℤ)/(p:ℤ)-1)=(k:ℤ)-1 := by {
    ring_nf
    simp only [reduceNeg, add_right_inj]
    refine Int.mul_ediv_cancel' ?H
    norm_cast
    exact hp.2
  }
  have hnum: (p:ℤ)-1 ∣ (k:ℤ)/(p:ℤ)-1 := by {
    have h:=hm1 p hp
    rw [← hnum] at h
    refine (Int.dvd_iff_dvd_of_dvd_add h).mp ?_
    exact Int.dvd_mul_right (↑p - 1) (↑k / ↑p)
  }
  have hnum: (p:ℤ)-1 ≤ (k:ℤ)/(p:ℤ)-1:= by{
    refine Int.le_of_dvd ?h ?_
    refine Int.sub_pos_of_lt ?h.h
    norm_cast
    refine (Nat.lt_div_iff_mul_lt ?h.h.hdn 1).mpr ?h.h.a
    exact hp.2
    simp only [mul_one]
    have hp2:=hp.2
    have hp:=hp.1
    refine Nat.lt_of_le_of_ne ?h.h.a.h₁ ?h.h.a.h₂
    refine Nat.le_of_dvd (zero_lt_of_lt hnk) hp2
    by_contra hnot
    rw [hnot] at hp
    exact hpk hp
    exact hnum
  }
  simp only [tsub_le_iff_right, sub_add_cancel] at hnum
  by_contra hnot
  simp only [gt_iff_lt, not_lt] at hnot
  norm_cast at hnum
  have hnum: p ≤ Real.sqrt k := by {
    calc (p:ℝ) ≤ ↑k/↑p := by {
      refine (le_div_iff₀' ?hc).mpr ?_
      have hp:=hp.1
      norm_cast;exact Prime.pos hp
      norm_cast;exact Nat.mul_le_of_le_div p p k hnum
    }
    _ ≤ k/Real.sqrt k := by {
      refine div_le_div_of_nonneg_left ?_ ?_ hnot
      norm_cast;exact Nat.zero_le k
      refine sqrt_pos_of_pos ?refine_2.a
      norm_cast;exact zero_lt_of_lt hnk
    }
    _ = Real.sqrt k := div_sqrt
  }
  have hnum: p*p=k:= by{
    rw [@Nat.le_antisymm_iff]
    constructor
    have haux: (p:ℝ)*(p:ℝ)≤ k := by{
      calc p*p≤ √↑k*√↑k := by {
        refine _root_.mul_self_le_mul_self ?ha hnum
        norm_cast
        exact Nat.zero_le p
      }
      _ = (√↑k)^2 := by exact Eq.symm (pow_two √↑k)
      _ = k := by {
        refine sq_sqrt ?_
        norm_cast;exact Nat.zero_le k
      }
    }
    norm_cast at haux
    have haux: (p:ℝ)*(p:ℝ)≥ k := by{
      calc p*p≥ √↑k*√↑k := by {
        refine _root_.mul_self_le_mul_self ?_ hnot
        exact Real.sqrt_nonneg ↑k
      }
      _ = (√↑k)^2 := by exact Eq.symm (pow_two √↑k)
      _ = k := by {
        refine sq_sqrt ?_
        norm_cast;exact Nat.zero_le k
      }
    }
    norm_cast at haux
  }
  have hnum: p*p ∣ k := by exact dvd_of_eq hnum
  have hnum := hsqr p hnum
  have hnum' : ¬ (IsUnit p) := by {
    have hp:=hp.1
    refine Prime.not_unit ?_
    exact prime_iff.mp hp
  }
  exact hnum' hnum
}

theorem carmichael_has_3_factors {k: ℕ} {s: Finset ℕ} (hs: ∀p, p ∈ s ↔ Nat.Prime p ∧ p ∣ k) (h: isCarmichael k) : s.card > 2 := by {
  have h':= carmichael_primes_lt_sqrt h
  obtain ⟨hsqrf, hm1, hpk, hk1⟩ := Korselt.1 h
  by_contra hnot
  simp only [gt_iff_lt, not_lt] at hnot
  have hep: ∃ p, Nat.Prime p ∧ p ∣ k := by {
    refine Nat.exists_prime_and_dvd ?hn
    have h:=h.2.2
    exact Ne.symm (Nat.ne_of_lt h)
  }
  have hnot: s.card=1 ∨ s.card=2 := by{
    refine le_and_le_add_one_iff.mp ?_
    constructor
    simp only [one_le_card]
    obtain ⟨ p, hp⟩:= hep
    have hep:= (hs p).2 hp
    rw [@Finset.nonempty_iff_ne_empty]
    exact ne_empty_of_mem hep
    simp only [Nat.reduceAdd]
    exact hnot
  }
  have pdes:= forall_prime_descomposition_squarefree (zero_lt_of_lt hk1) hsqrf hs
  obtain hnot|hnot:=hnot
  . obtain ⟨ p, hnot⟩ := card_eq_one.mp hnot
    have hp: p ∈ s:= by {
      refine Finset.singleton_subset_iff.mp ?_
      exact Finset.subset_of_eq (_root_.id (Eq.symm hnot))
    }
    rw[hnot] at pdes
    simp only [Finset.prod_singleton] at pdes
    obtain ⟨hp1, hp2⟩:= (hs p).1 hp
    have hnot: p<k:= by {
      refine Nat.lt_of_le_of_ne ?h₁ ?h₂
      exact Nat.le_of_eq pdes
      by_contra hnot'
      rw [hnot'] at hp1
      exact hpk hp1
    }
    have hnot: ¬ p=k:= by exact Nat.ne_of_lt hnot
    exact hnot pdes
  . obtain ⟨ p , q, hpq, hnot⟩ := card_eq_two.mp hnot
    have hp: p ∈ s:= by {
      rw [hnot]
      exact mem_insert_self p {q}
    }
    have hq: q ∈ s:= by {
      rw [hnot]
      refine Finset.mem_insert.mpr ?_
      right
      exact Finset.mem_singleton.mpr rfl
    }
    rw[hnot] at pdes
    rw [prod_pair hpq] at pdes
    have hq1:= ((hs q).1 hq).1
    have hp1:= ((hs p).1 hp).1
    have hq:= h' q ((hs q).1 hq)
    have hp:= h' p ((hs p).1 hp)
    have hnot: (p:ℝ) * (q:ℝ) < (k:ℝ) := by {
      calc (p:ℝ) * (q:ℝ) < √↑k * (q:ℝ) := by {
        refine mul_lt_mul_of_pos_right hp ?a0
        norm_cast
        exact Prime.pos hq1
      }
      _ < √↑k * √↑k := by {
        refine mul_lt_mul_of_pos_left hq ?_
        refine sqrt_pos_of_pos ?_
        norm_cast
        exact zero_lt_of_lt hk1
      }
      _ = k := by simp only [Nat.cast_nonneg, mul_self_sqrt]
    }
    norm_cast at hnot
    have hnot: ¬ p * q = k := by exact Nat.ne_of_lt hnot
    exact hnot pdes
}
