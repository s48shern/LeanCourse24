import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.MaxPowDiv
import Mathlib.Data.Nat.Squarefree
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

open Real Function Nat BigOperators Set Finset Algebra Int
open Classical

lemma weak_carmichael_is_odd {n : ℕ}: n > 2 ∧ (∀ (a : ℤ), (Int.gcd a n = 1 → (n:ℤ) ∣ a ^ (n - 1) - 1 )) → ¬ 2 ∣ n := by {
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

lemma prime_dvd_def {n m p : ℕ} (hd : p^m ∣ n) (hp: Nat.Prime p) (hn: n>0) : ∃ k,∃ c, k≥ m ∧ p^k*c=n ∧ Nat.gcd p c = 1 := by{
  simp_all only [not_false_eq_true, gt_iff_lt, and_self, implies_true, true_and, ge_iff_le, exists_and_left]
  obtain ⟨c, hn⟩ := hd
  use p.maxPowDiv c + m
  constructor
  · linarith
  · use c /  (p ^ (p.maxPowDiv c))
    constructor
    · calc p ^ (p.maxPowDiv c + m) * (c /  (p ^ (p.maxPowDiv c))) = (p ^ (p.maxPowDiv c) * p ^ m) * (c /  (p ^ (p.maxPowDiv c))) := by ring_nf
      _ = p ^  m * p ^ p.maxPowDiv c * c /  (p ^ (p.maxPowDiv c)):= by {
        rw [@npow_mul_comm]
        refine Eq.symm (Nat.mul_div_assoc (p ^  m * p ^ p.maxPowDiv c) ?H)
        exact maxPowDiv.pow_dvd p c
      }
      _ = p ^  m * c * p ^ p.maxPowDiv c  /  (p ^ (p.maxPowDiv c))  := by rw [Nat.mul_right_comm]
      _ = p^ m * c* 1 := by {
        simp_all only [Nat.cast_mul, mul_one, _root_.mul_eq_mul_right_iff]
        have h : c ≠ 0 := by {
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
        exact Nat.pos_pow_of_pos (p.maxPowDiv c) h
        exact Nat.mul_right_comm (p ^  m) (p ^ p.maxPowDiv c) c
        }
      _ = n := by{
      subst hn
      simp_all only [Nat.cast_mul, mul_one, _root_.mul_eq_mul_right_iff]
      }
    · refine Eq.symm (Nat.gcd_greatest ?h.right.hda ?h.right.hdb ?h.right.hd)
      · exact Nat.one_dvd p
      · exact Nat.one_dvd (c / p ^ p.maxPowDiv c)
      · intro x ha1 ha2
        rw [@dvd_one]
        rw [propext (dvd_prime hp)] at ha1
        by_contra h
        have h : x = p := by simp_all only [false_or, Nat.cast_mul]
        rw [h] at ha2
        norm_num
        have hdiv : p ^ (p.maxPowDiv c+1) ∣ c := by {
          obtain ⟨n, hn ⟩ := ha2
          have hdiv : c = p^(p.maxPowDiv c+1)*n := by {
            calc c = p^(p.maxPowDiv c)* p*n := by {
              rw [Nat.div_eq_iff_eq_mul_left] at hn
              · ring_nf;
                linarith
              · refine Nat.pow_pos ?H.h
                exact Prime.pos hp
              · exact maxPowDiv.pow_dvd p c
            }
            _ = p^(p.maxPowDiv c+1) *n := by {
            simp_all only [or_true, Nat.cast_mul, _root_.mul_eq_mul_right_iff]
            apply Or.inl
            rfl}
          }
          exact Dvd.intro n (_root_.id (Eq.symm hdiv))
        }
        have hcontra : p.maxPowDiv c+1 ≤ p.maxPowDiv c := by {
          apply Nat.maxPowDiv.le_of_dvd
          · exact Prime.one_lt hp
          · by_contra hc
            push_neg at hc
            have hc : c = 0 := by exact eq_zero_of_le_zero hc
            rw [hc] at hn
            linarith
          · exact hdiv
        }
        linarith
}

lemma forall_prime_decomposition {n: ℕ} {s: Finset ℕ} (hn0: n>0): (∀ p, p∈ s ↔ Nat.Prime p ∧ p ∣ n) →  ∏ p ∈ s, (p ^ p.maxPowDiv n:ℤ) = n := by {
  have hind: ∀s: Finset ℕ, ∀n>0, (∀ p, p∈ s ↔ Nat.Prime p ∧ p ∣ n) → ∏ p ∈ s, (p ^ p.maxPowDiv n:ℤ) = n := by {
    intro s
    induction s using Finset.induction with
    | empty => {
      intro n hn0 hintro
      simp
      norm_cast
      by_contra hcont
      have h'': ∃ p, Nat.Prime p ∧ p ∣ n := by exact Nat.exists_prime_and_dvd fun a ↦ hcont (_root_.id (Eq.symm a))
      obtain ⟨p, hp⟩:=h''
      exact (List.mem_nil_iff p).mp ((hintro p).2 hp)
    }
    | @insert x s hxs ih => {
      intro n hn0 hintro
      rw [Finset.prod_insert hxs]
      specialize ih (n/x^(x.maxPowDiv n))
      have hx:= (hintro x).1 (mem_insert_self x s)
      have hend: (∀ (p : ℕ), p ∈ s ↔ Nat.Prime p ∧ p ∣ n / x^(x.maxPowDiv n)) := by{
        intro p
        constructor
        . intro hintro2
          have hp:= (hintro p).1 (Finset.mem_insert_of_mem hintro2)
          constructor
          . exact hp.1
          . refine (Nat.dvd_div_iff_mul_dvd ?mp.right.hbc).mpr ?mp.right.a
            exact maxPowDiv.pow_dvd x n
            refine Coprime.mul_dvd_of_dvd_of_dvd ?mp.right.a.hmn ?mp.right.a.hm ?mp.right.a.hn
            . have hx:=hx.1
              have hp:=hp.1
              have haux: x.Coprime p:= by{
                refine (coprime_primes hx hp).mpr ?mp.right.a.hmn.a
                by_contra hnot
                rw [hnot] at hxs
                exact hxs hintro2
              }
              exact Coprime.pow_left (x.maxPowDiv n) haux
            . exact maxPowDiv.pow_dvd x n
            exact hp.2
        . intro hintro2
          have hintro:= (hintro p).2
          have hcond: Nat.Prime p ∧ p ∣ n := by{
            constructor
            exact hintro2.1
            have h':= hintro2.2
            have h'2: n / x ^ x.maxPowDiv n ∣ n := by {
              have h'x:= hx.1
              have haux:  0<x ^ x.maxPowDiv n := by refine Nat.pow_pos ?h; exact Prime.pos h'x
              refine Nat.dvd_of_mul_dvd_mul_right haux ?_
              have h''x: x ^ x.maxPowDiv n ∣ n := by exact maxPowDiv.pow_dvd x n
              rw [Nat.div_mul_cancel h''x]
              exact Nat.dvd_mul_right n (x ^ x.maxPowDiv n)
            }
            exact Nat.dvd_trans h' h'2
          }
          have hintro:= hintro hcond
          rw [@Finset.mem_insert] at hintro
          obtain hintro|hintro:=hintro
          . by_contra
            have hintro2:= hintro2.2
            have hpx: x ^ x.maxPowDiv n * p ∣ n := by refine (Nat.dvd_div_iff_mul_dvd ?hbc).mp ?_;exact maxPowDiv.pow_dvd x n; exact hintro2
            rw [hintro] at hpx
            have hpx: x ^ (x.maxPowDiv n + 1) ∣ n := by exact hpx
            have hx:=hx.1
            have hx1: x>1 := by exact Prime.one_lt hx
            have hpx: x.maxPowDiv n + 1 ≤ x.maxPowDiv n := Nat.maxPowDiv.le_of_dvd hx1 hn0 hpx
            have hlast: x.maxPowDiv n + 1 > x.maxPowDiv n := Nat.lt_add_right 1 hpx
            have hlast: ¬ x.maxPowDiv n + 1 ≤ x.maxPowDiv n := not_succ_le_self (x.maxPowDiv n)
            exact hlast hpx
          . exact hintro
      }
      have hcond1: n / x ^ x.maxPowDiv n > 0 := by {
        refine (Nat.lt_div_iff_mul_lt ?hdn 0).mpr hn0
        exact maxPowDiv.pow_dvd x n
      }
      have ih := ih hcond1 hend
      have hfinal: ∀ (x p:ℕ),  (x ∣ n ∧ p ∣ n ∧ p.Prime ∧ x.Prime ∧ p ≠ x) → p.maxPowDiv (n / x ^ x.maxPowDiv n) = p.maxPowDiv n := by {
        intro x p hp
        obtain ⟨hnx, hnp, hpp, hpx, hnpx⟩:= hp
        have hcpx: p.Coprime x := (coprime_primes hpp hpx).mpr hnpx
        refine Eq.symm (Nat.le_antisymm ?intro.intro.h₁ ?intro.intro.h₂)
        . refine maxPowDiv.le_of_dvd ?intro.intro.h₁.hp ?intro.intro.h₁.hn ?intro.intro.h₁.h
          exact Prime.one_lt hpp
          refine (Nat.div_pos_iff ?intro.intro.h₁.hn.hb).mpr ?intro.intro.h₁.hn.a
          exact pow_ne_zero (x.maxPowDiv n) (Nat.Prime.ne_zero hpx)
          exact Nat.le_of_dvd hn0 (Nat.maxPowDiv.pow_dvd x n)
          refine (Nat.dvd_div_iff_mul_dvd ?intro.intro.h₁.h.hbc).mpr ?intro.intro.h₁.h.a
          exact maxPowDiv.pow_dvd x n
          refine Coprime.mul_dvd_of_dvd_of_dvd ?intro.intro.h₁.h.a.hmn (maxPowDiv.pow_dvd x n) (maxPowDiv.pow_dvd p n)
          exact coprime_pow_primes (x.maxPowDiv n) (p.maxPowDiv n) hpx hpp (_root_.id (Ne.symm hnpx))
        . refine maxPowDiv.le_of_dvd ?intro.intro.h₂.hp hn0 ?intro.intro.h₂.h
          exact Prime.one_lt hpp
          refine Nat.dvd_trans (maxPowDiv.pow_dvd p (n / x ^ x.maxPowDiv n)) ?intro.intro.h₂.h.h₂
          refine div_dvd_of_dvd (maxPowDiv.pow_dvd x n)
      }
      have hfinal: ∀(x: ℕ), ∀(s: Finset ℕ), ((x ∣ n ∧ x.Prime ∧ x ∉ s ∧ (∀ p, p ∈ s → (Nat.Prime p ∧ p ∣ n))) → ∏ p ∈ s, (p:ℤ) ^ p.maxPowDiv (n / x ^ x.maxPowDiv n) = ∏ p ∈ s, (p:ℤ) ^ p.maxPowDiv n):= by {
        intro x s h
        obtain ⟨hxn, hxp, hs⟩:=h
        induction s using Finset.induction with
        | empty => rfl
        | @insert x2 s2 hxs ih => {
          rw [Finset.prod_insert hxs]
          rw [ih]
          rw [hfinal x x2]
          exact Eq.symm (Finset.prod_insert hxs)
          constructor
          . exact hxn
          constructor
          . exact (hs.2 x2 (Finset.mem_insert_self x2 s2)).2
          constructor
          . exact (hs.2 x2 (Finset.mem_insert_self x2 s2)).1
          constructor
          . exact hxp
          . rw [← @forall_mem_not_eq] at hs
            have hs:= (hs.1 x2 (Finset.mem_insert_self x2 s2))
            exact fun a ↦ hs (_root_.id (Eq.symm a))
          constructor
          . have hs:=hs.1
            rw [@Finset.mem_insert] at hs
            simp at hs
            exact hs.2
          . intro p hsp
            exact hs.2 p (Finset.mem_insert_of_mem hsp)
        }
      }
      rw [hfinal] at ih
      rw [ih]
      norm_cast
      have h''x: x ^ x.maxPowDiv n ∣ n := by exact maxPowDiv.pow_dvd x n
      exact Nat.mul_div_cancel_left' h''x
      constructor
      exact hx.2
      constructor
      exact hx.1
      constructor
      exact hxs
      intro p hsp
      exact (hintro p).1 (Finset.mem_insert_of_mem hsp)
    }
  }
  exact hind s n hn0
}

lemma exists_prime_decomposition {n: ℕ} (hn0: n>0): ∃s : Finset ℕ, (∀ p, p∈ s ↔ Nat.Prime p ∧ p ∣ n) ∧ ∏ p ∈ s, (p ^ p.maxPowDiv n:ℤ) = n := by {
  let setP1 := {p : ℕ | Nat.Prime p ∧ p ∣ n}
  have hsetp : setP1.Finite := by {
    have hsetsp: {x: ℕ | x≤ n}.Finite := finite_le_nat n
    refine Finite.subset hsetsp ?ht
    intro p hp
    unfold setP1 at hp
    have hp:= hp.2
    exact Nat.le_of_dvd hn0 hp
  }
  let setP:= Set.Finite.toFinset hsetp
  use setP
  have h: (∀ (p : ℕ), p ∈ setP ↔ Nat.Prime p ∧ p ∣ n) := by {
    unfold setP
    simp
    intro p
    constructor
    . exact fun a ↦ a
    . exact fun a ↦ a
  }
  constructor
  exact h
  exact forall_prime_decomposition hn0 h
}

lemma forall_prime_descomposition_squarefree {n : ℕ} {s: Finset ℕ} (hn0: n > 0) (hsqn: Squarefree n): (∀ p, p∈ s ↔ Nat.Prime p ∧ p ∣ n) → (∏ p ∈ s, p = n) := by {
  have hind: ∀ s, ∀ n, (Squarefree n ∧ (∀ (p : ℕ), p ∈ s ↔ Nat.Prime p ∧ p ∣ n)) → ∏ p ∈ s, ↑p = ↑n:= by {
    intro s
    induction s using Finset.induction with
    | empty => {
      intro n hn
      have hsqn:= hn.1
      have hn:=hn.2
      simp
      by_contra hcont
      have h'': ∃ p, Nat.Prime p ∧ p ∣ n := by exact Nat.exists_prime_and_dvd fun a ↦ hcont (_root_.id (Eq.symm a))
      obtain ⟨p, hp⟩:=h''
      exact (List.mem_nil_iff p).mp ((hn p).2 hp)
    }
    | @insert x s hxs ih => {
      intro n hn
      have hsqn := hn.1
      have hn := hn.2
      specialize ih (n/x)
      rw [Finset.prod_insert hxs]
      rw [ih]
      exact Nat.mul_div_cancel_left' ((hn x).1 (Finset.mem_insert_self x s)).2
      constructor
      . rw [@squarefree_iff_prime_squarefree]
        intro p hp
        by_contra hnot
        have hcond: n/x ∣ n := by {
          refine div_dvd_of_dvd ?h
          exact ((hn x).1 (Finset.mem_insert_self x s)).2
        }
        have hcond: p*p ∣ n := Nat.dvd_trans hnot hcond
        unfold Squarefree at hsqn
        have hcond2: ¬ IsUnit p := by exact hp.not_unit
        exact hcond2 (hsqn p hcond)
      intro p
      constructor
      . intro hp
        have hn1:= (hn p).1 (Finset.mem_insert_of_mem hp)
        have hn2:= (hn x).1 (Finset.mem_insert_self x s)
        constructor
        exact hn1.1
        refine Nat.dvd_div_of_mul_dvd ?insert.mp.right.h
        refine Coprime.mul_dvd_of_dvd_of_dvd ?insert.mp.right.h.hmn ?insert.mp.right.h.hm ?insert.mp.right.h.hn
        have hp2:= hn1.1
        have hx:= hn2.1
        refine (coprime_primes hx hp2).mpr ?insert.mp.right.h.hmn.a
        by_contra hnot
        rw [hnot] at hxs
        exact hxs hp
        exact hn2.2
        exact hn1.2
      . intro hintro
        have hintro': Nat.Prime p ∧ p ∣ n := by{
          constructor
          exact hintro.1
          refine Nat.dvd_trans hintro.2 ?right.h₂
          refine div_dvd_of_dvd ?right.h₂.h
          exact ((hn x).1 (Finset.mem_insert_self x s)).2
        }
        have hintro':= (hn p).2 hintro'
        rw [@Finset.mem_insert] at hintro'
        obtain hintro'|hintro':=hintro'
        . rw [hintro'] at hintro
          have hx1:= hintro.1
          have hx2:= hintro.2
          have hx2: x*x ∣ n := by{
            refine Nat.mul_dvd_of_dvd_div ?hcb hx2
            exact ((hn x).1 (Finset.mem_insert_self x s)).2
          }
          have hx2:=hsqn x hx2
          by_contra
          exact (hx1.not_unit) hx2
        . exact hintro'
    }
  }
  intro hintro
  have hcond: (Squarefree n ∧ ∀ (p : ℕ), p ∈ s ↔ Nat.Prime p ∧ p ∣ n) := by{
    constructor
    exact hsqn
    exact fun p ↦ hintro p
  }
  exact hind s n hcond
}

lemma exists_prime_descomposition_squarefree {n : ℕ} (hn0: n > 0) (hsqn: Squarefree n): ∃(s: Finset ℕ), (∀ p, p∈ s ↔ Nat.Prime p ∧ p ∣ n) ∧ (∏ p ∈ s, p = n) := by {
  have h:= exists_prime_decomposition hn0
  obtain ⟨s, h⟩:= h
  use s
  constructor
  exact h.1
  exact forall_prime_descomposition_squarefree hn0 hsqn h.1
}

lemma congruence_by_prime_decomposition {n: ℕ} {a c: ℤ} {s: Finset ℕ} (hn0: n > 0) (hsqn: Squarefree n) (hsp: ∀ p, p∈ s ↔ Nat.Prime p ∧ p ∣ n): (∀p ∈ s, a ≡ c [ZMOD (p:ℤ)]) ↔ (a ≡ c [ZMOD (n:ℤ)]) := by {
  have hprime:= forall_prime_descomposition_squarefree hn0 hsqn hsp
  constructor
  intro hp
  have h': ∀s: Finset ℕ, (∀ p: ℕ, p ∈ s → (Nat.Prime p ∧ p ∣ n)) → a ≡ c [ZMOD (∏ p in s, p)] := by{
    intro s2
    induction s2 using Finset.induction with
    | empty => {
      intro hintro
      simp
      exact Int.modEq_one
    }
    | @insert x s2 hxs ih => {
      intro hintro
      rw [Finset.prod_insert hxs]
      rw [← Int.modEq_and_modEq_iff_modEq_mul]
      constructor
      . exact hp x ((hsp x).2 (hintro x (mem_insert_self x s2)))
      apply ih ?_
      intro p hp
      exact hintro p (mem_insert_of_mem hp)
      simp
      have haux: ∀s: Finset ℕ, (∏ x ∈ s, (x:ℤ)).natAbs = (∏ x ∈ s, x) := by {
        intro s
        induction s using Finset.induction with
        | empty => rfl
        | @insert x2 s2 hxs2 ih2 => {
          rw [Finset.prod_insert hxs2]
          rw [Finset.prod_insert hxs2]
          rw [Int.natAbs_mul]
          rw [ih2]
          simp
        }
      }
      rw [haux s2]
      refine coprime_prod_right_iff.mpr ?insert.a
      intro i hi
      have hiprime:=(hintro i (Finset.mem_insert_of_mem hi)).1
      have hxprime:=(hintro x (Finset.mem_insert_self x s2)).1
      refine (coprime_primes hxprime hiprime).mpr ?insert.a.a
      by_contra hnot
      rw [hnot] at hxs
      exact hxs hi
    }
  }
  have hcond: (∀ p ∈ s, Nat.Prime p ∧ p ∣ n) := by {
    intro p a_1
    subst hprime
    simp_all only [and_imp, gt_iff_lt, CanonicallyOrderedCommSemiring.prod_pos, and_self]
  }
  have h':= h' s hcond
  have hprime: ∏ p ∈ s, (p:ℤ) = (n:ℤ) := by {
    rw [← hprime]
    simp
  }
  rw [hprime] at h'
  exact h'
  intro hintro
  intro p hp
  have hp:=(hsp p).1 hp
  obtain ⟨hp1, hp2⟩:= hp
  rw[Int.modEq_iff_dvd] at hintro
  rw[Int.modEq_iff_dvd]
  have hp2: (p:ℤ) ∣ (n:ℤ) := by {
    norm_cast
  }
  exact Int.dvd_trans hp2 hintro
}

lemma coprime_if_dvd_coprime {a:ℤ} {n p:ℕ} (hpp3: IsCoprime a n) (hpp2: p ∣ n): IsCoprime a p := by {
  rw [@dvd_def] at hpp2
  obtain ⟨c, hc⟩:= hpp2
  rw[hc] at hpp3
  rw [@isCoprime_iff_gcd_eq_one] at hpp3
  push_cast at hpp3
  rw [@isCoprime_iff_gcd_eq_one]
  exact gcd_eq_one_of_gcd_mul_right_eq_one_left hpp3
}

lemma n_pow_card_sub_one_eq_one {a: ℤ} {n p: ℕ} (hpp1: Nat.Prime p) (hpp2: p ∣ n) (h: (p:ℤ)-1 ∣ (n:ℤ)-1) (hp2: n>1) (hpp3: IsCoprime a p): a ^ (n - 1) ≡ 1 [ZMOD (p:ℤ)] := by{
  have hpa:=hpp3
  have hpa: a ^ (p - 1) ≡ 1 [ZMOD (p:ℤ)] := by{
    specialize hpa
    exact Int.ModEq.pow_card_sub_one_eq_one hpp1 hpa
  }
  have hf: (p-1:ℤ) = (p-1:ℕ) := by {
    exact Eq.symm (Int.natCast_pred_of_pos (Prime.pos hpp1))
  }
  rw [hf] at h
  have hf: (n-1:ℤ) = (n-1:ℕ) := by {
    exact Eq.symm (Int.natCast_pred_of_pos (zero_lt_of_lt hp2))
  }
  rw [hf] at h
  norm_cast at h
  rw [@dvd_def] at h
  have h2: ∀ c, a ^ ((p - 1)*c) ≡ 1 [ZMOD (p:ℤ)]:= by{
    intro c
    calc a ^ ((p - 1)*c) ≡ (a ^ (p - 1))^c [ZMOD (p:ℤ)] := by ring_nf; trivial
    _ ≡ 1^c [ZMOD (p:ℤ)] := Int.ModEq.pow c hpa
    _ ≡ 1 [ZMOD (p:ℤ)] := by ring_nf; trivial
  }
  obtain ⟨c, hc⟩:= h
  specialize h2 c
  ring_nf at h2
  rw [← hc] at h2
  exact h2
}

lemma powerPrimePositive {p k : ℕ} (hk : k ≥ 1) (hp: Nat.Prime p) : 0 < p^k := by {
  refine (pow_pos_iff ?H.hn).mpr ?H.a
  · exact not_eq_zero_of_lt hk
  · exact Prime.pos hp
}

lemma Unit_divides {p: ℕ} {b : ZMod p} (hu: IsUnit b) (hp: Nat.Prime p)  :¬ p ∣ b.val:= by{
  have hp2 : NeZero p := by rw [@neZero_iff]; exact Nat.Prime.ne_zero hp
  have hgroup : MonoidWithZero (ZMod p):= by exact CommMonoidWithZero.toMonoidWithZero
  have hgroup2 : Nontrivial (ZMod p):= by refine ZMod.nontrivial_iff.mpr ?_;exact Nat.Prime.ne_one hp
  have h_range : b.val < p := by exact ZMod.val_lt b
  intro hc
  have h_zero : b.val = 0 := by exact eq_zero_of_dvd_of_lt hc h_range

  rw [@ZMod.val_eq_zero] at h_zero
  have h_nzero : (b : ZMod p) ≠ 0:= by {
    intro h_zero
    have hnot: ¬ (@IsUnit (ZMod p) (@MonoidWithZero.toMonoid (ZMod p) Semiring.toMonoidWithZero) b) := by {
      rw [h_zero]
      rw [@isUnit_iff_exists]
      simp
    }
    exact hnot hu
  }
  exact h_nzero h_zero
}

lemma ModtoZmod (n a b: ℕ) : ( a ≡ b [MOD n]) ↔((a : ℤ) ≡ (b : ℤ) [ZMOD (n: ℤ )]) := by {
  exact Iff.symm natCast_modEq_iff
}

lemma ZmodtoMod (n a b: ℕ) : ((a : ℤ) ≡ (b : ℤ)  [ZMOD (n: ℤ )]) ↔( a ≡ b [MOD n]) := by {
  exact natCast_modEq_iff
}

#check Nat.chineseRemainder
#check ZMod.chineseRemainder
#check ZMod.eq_iff_modEq_nat
#check isCyclic_iff_exists_ofOrder_eq_natCard
