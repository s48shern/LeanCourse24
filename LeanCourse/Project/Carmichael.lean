import Mathlib

open Real Function Nat BigOperators Set Finset Algebra Int
open Classical
--open Nat.Squarefree

--We can take a in ℕ for the condition fermat as n is always odd
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

structure Carmichael where
  n: ℕ
  notPrime : ¬ Nat.Prime n
  g1: n>1
  fermat: ∀ (a : ℤ), Int.gcd a n = 1 → (n:ℤ) ∣ a^(n-1)-1

def isCarmichael (n : ℕ) := ¬ Nat.Prime n ∧ (∀ (a : ℤ), Int.gcd a n = 1 → (n:ℤ) ∣ a^(n-1)-1) ∧ n>1

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


lemma ModtoZmod (n a b: ℕ) : ( a ≡ b [MOD n]) ↔((a : ℤ) ≡ (b : ℤ) [ZMOD (n: ℤ )]) := by {
  exact Iff.symm natCast_modEq_iff
}

lemma ZmodtoMod (n a b: ℕ) : ((a : ℤ) ≡ (b : ℤ)  [ZMOD (n: ℤ )]) ↔( a ≡ b [MOD n]) := by {
  exact natCast_modEq_iff
}

lemma briefsimp (p m2 : ℕ) : p * (m2 + 1) + 1 ≡ 1 + (m2 + 1) * p [MOD p ^ 2] := by {
  have hzed :  p * (m2 + 1) + 1 ≡ 1 + (m2 + 1) * p [ZMOD p ^ 2] := by {
    calc
      p * (m2 + 1) + 1
          ≡ (m2 + 1) * p + 1 [ZMOD p ^ 2] := by{
            ring_nf; rfl}
      _ ≡ 1 + (m2 + 1) * p [ZMOD p ^ 2] := by{
            ring_nf; rfl
      }
  }
  exact (ModtoZmod (p ^ 2) (p * (m2 + 1) + 1) (1 + (m2 + 1) * p)).mpr hzed
}
lemma quicklemma (p n: ℕ ) (hn: n ≥2): 1 + ↑p + ↑p * ↑(n-2) ≡ 1 + ↑p * subNatNat (2 + (n-2)) 1 [ZMOD ↑p ^ 2] := by{

    norm_cast
    calc 1 + p + p * ↑(n-2) ≡ 1 + p * (n-1)[ZMOD ↑p ^ 2] := by {
      apply modEq_iff_add_fac.mpr
      use 0
      ring_nf
      simp_all only [ge_iff_le, Nat.cast_sub, Nat.cast_ofNat]
      linarith
    }
    _≡ 1 + ↑p * subNatNat (n) 1 [ZMOD ↑p ^ 2] := by norm_cast
    _≡ 1 + ↑p * subNatNat (2 + (n - 2)) 1 [ZMOD ↑p ^ 2] := by {
      have h: (2 + (n-2))=n := by apply add_sub_of_le; exact hn
      simp_rw[h]; rfl
    }
  }

lemma endingLemma (a b c p :ℤ ) (h1 : a ≡ b [ZMOD p^2]) (h2:  c ≡ 0 [ZMOD p^2]) : a + c ≡ b [ZMOD p^2]:= by {
  calc  a + c≡ a + 0 [ZMOD p^2] := by exact Int.ModEq.add rfl h2
  _ ≡ a [ZMOD p^2] := by norm_num
  _ ≡ b [ZMOD p^2] := by exact h1
}
--zify
--Fin_cases and discard nontrivial
--interval_cases n <;> try decide
lemma calcs (m2 i : ℕ) (h:m2-i ≥ 1): 1+ m2 -i ≥ 1 +1:= by {
  calc 1+ m2 -i = 1 + (m2-i):= by {
    refine AddLECancellable.add_tsub_assoc_of_le ?hc ?h 1
    exact Contravariant.AddLECancellable
    have h1_ : m2 -i ≥ 0 := by exact Nat.zero_le (m2 - i);
    omega
    }
  _ ≥ 1+1 := by exact Nat.add_le_add_left h 1
}
lemma BinomialCongruence (n p n' k : ℕ) (hpk : p ^ k * n' = n) (hn : n ≥ 2) (hred :(1+ p)^(n-1) ≡ 1 [ZMOD p^2] ): (1+ p)^(n-1) ≡ 1 + (n-1)*p [ZMOD p^2] := by {
  have hobvious : (n - 1 + 1) = n := by ring_nf; apply add_sub_of_le; linarith
  have haux :  (1+ p)^(n-1) = ∑ m ∈ Finset.range (n), 1 ^ m * p ^ (n -1 - m) * (n - 1).choose m := by {
      rw [add_pow];
      simp [hobvious]
    }
  norm_cast
  simp_rw [haux]
  push_cast
  let m1 := n-1
  have hprob: n = m1+1 := by linarith
  rw [hprob]
  rw [Finset.sum_range_succ]
  simp

  let m2:= m1-1
  have hprob2: m1= m2+1 := by {
    refine Eq.symm (Nat.sub_add_cancel ?h);
    linarith
  }
  rw [hprob2]
  rw [Finset.sum_range_succ]
  simp
  have haux : p * (m2 + 1) + 1 ≡ 1 + (m2 + 1) * p [ZMOD p ^ 2] := by {
    calc
      p * (m2 + 1) + 1
          ≡ (m2 + 1) * p + 1 [ZMOD p ^ 2] := by{
            ring_nf; rfl}
      _ ≡ 1 + (m2 + 1) * p [ZMOD p ^ 2] := by{
            ring_nf; rfl
      }
  }

  rw[hprob2] at hprob;
  have hprob : m2 = n-2 := by{exact rfl}
  have hsum : ∑ x ∈ Finset.range m2, p ^ (m2 + 1 - x) * (1+m2).choose x ≡ 0 [ZMOD p^2] := by{
    apply Dvd.dvd.modEq_zero_int
    apply Finset.dvd_sum
    intro i hi
    have h : ↑p^2 ∣ ↑p ^ (m2 + 1 - i):= by {
      have hcalc: m2 + 1 - i ≥ 2:= by {
        apply Nat.add_one_le_iff.mpr
        ring_nf;
        have h:  m2 -i≥ 1:= by apply zero_lt_sub_of_lt; exact List.mem_range.mp hi
        refine gt_iff_lt.mp ?_
        calc 1+ m2 -i ≥1+1 := by exact calcs m2 i h
        _ > 1 := by exact one_lt_succ_succ 0
      }
      exact Nat.pow_dvd_pow p hcalc
    }
    refine dvd_iff_exists_eq_mul_left.mpr ?h.h.advd_iff_exists_eq_mul_left
    obtain ⟨c, hc⟩ :=h
    use (1+m2).choose i*c
    norm_cast
    simp_rw[hc]
    linarith
  }

  ring_nf at hsum; ring_nf
  have final :  1 + ↑p + ↑p * ↑m2 ≡ 1 + ↑p * subNatNat (2 + m2) 1 [ZMOD ↑p ^ 2] := by{
    norm_cast
    simp_rw[hprob]
    exact quicklemma p n hn
  }
  apply endingLemma (1 + ↑p + ↑p * ↑m2) (1 + ↑p * subNatNat (2 + m2) 1) (∑ x ∈ Finset.range m2, ↑p ^ (1 + m2 - x) * ↑((1 + m2).choose x)) (↑p) final hsum
}
lemma powerPrimePositive (p k : ℕ) (hk : k ≥ 1) (hp: Nat.Prime p) : 0 < p^k := by {
  refine (pow_pos_iff ?H.hn).mpr ?H.a
  · exact not_eq_zero_of_lt hk
  · exact Prime.pos hp
}
lemma SquareFreePart2  {n p n' k : ℕ} (hp: Nat.Prime p) (hd : p * p ∣ n) (hpk : p ^ k * n' = n) (hn : n >1) (hred : (1+ p)^(n-1) ≡ 1 [MOD p^2]) (hk: k ≥ 2): False := by{
  have hred:(1+ p)^(n-1) ≡ 1 [ZMOD p^2] := by norm_cast; exact (ZmodtoMod (p ^ 2) ((1+ p)^(n-1)) (1)).mpr hred
  have hobvious : (n - 1 + 1) = n := by ring_nf; apply add_sub_of_le; linarith
  have hbin : (1+ p)^(n-1) ≡ 1 + (n-1)*p [ZMOD p^2] := by {
   exact BinomialCongruence n p n' k hpk hn hred
  }
  have hdiv : 1 + (n-1)*p +p≡ 1 [ZMOD p^2] := by{
    calc 1 + (n-1)*p +p≡ 1 + n * p  - p + p [ZMOD p^2] := by {
      ring_nf; rfl
    }
    _ ≡ 1 + 0 * p - p + p [ZMOD p^2] :=
      by {
        rw [← Nat.pow_two] at hd; simp; refine Int.ModEq.symm ((fun {a b n} ↦ modEq_iff_add_fac.mpr) ?_)
        use n'*p^(k-1)
        simp
        norm_cast
        rw [← hpk]
        ring_nf
        refine (Nat.mul_right_cancel_iff ?h.p).mpr ?h.b
        · by_contra hc
          push_neg at hc
          have hn : n' = 0 := by exact eq_zero_of_le_zero hc
          rw[hn] at hpk
          linarith
        · calc p* p^k = p ^(k+1) := by exact Eq.symm Nat.pow_succ'
          _ = p^2 * p^(k-1) := by {
            let k1 := k-1
            have hk2: k = k1 +1 := by refine Nat.eq_add_of_sub_eq ?hle rfl; exact one_le_of_lt hk
            have hk3: k -1 ≥ 1 := by exact Nat.le_sub_one_of_lt hk
            refine (Nat.div_eq_iff_eq_mul_left ?H ?H').mp ?_
            · exact powerPrimePositive p (k - 1) hk3 hp
            · refine (Nat.dvd_prime_pow hp).mpr ?H'.a
              use k-1
              constructor
              · linarith
              · rfl
            · refine Nat.div_eq_of_eq_mul_right ?H1 ?H2
              · exact powerPrimePositive p (k - 1) hk3 hp
              · have hpk :  p ^ (k - 1) * p ^ 2 = p ^(k -1 +2) := by exact Eq.symm (Nat.pow_add p (k - 1) 2)
                rw[hpk]
                exact Mathlib.Tactic.Ring.pow_congr rfl (congrFun (congrArg HAdd.hAdd hk2) 1) rfl
          }
      }
    _ ≡ 1 - p + p [ZMOD p^2] := by {
      have h0 : 0* p = 0 := by exact Nat.zero_mul p
      simp [h0]
    }
    _ ≡ 1 [ZMOD p^2] := by {
      have h0 : -p + p ≡ 0 [ZMOD p^2]:= by apply Dvd.dvd.modEq_zero_int; norm_num
      simp [h0]
    }
  }

  have hcontra : 1 +p≡ 1 [ZMOD p^2 ]:= by {
    calc  1+p ≡ (1 + p) ^ (n - 1)+p [ZMOD p^2]:= by exact Int.ModEq.add (_root_.id (Int.ModEq.symm hred)) rfl
    _ ≡ 1 + (↑n - 1) * ↑p + p [ZMOD p^2]:= by exact Int.ModEq.add hbin rfl
    _≡ 1 [ZMOD p^2] := by exact hdiv
  }
  have hdiv : p ≡ 0 [ZMOD p^2 ]:=by {
    exact Int.ModEq.add_left_cancel' 1 hcontra
  }
  rw [Int.modEq_zero_iff_dvd] at hdiv
  have h1 : 1 < p := by exact Prime.one_lt hp
  have h2 : 1 < 2 := by linarith
  apply Nat.not_pos_pow_dvd h1 h2
  exact ofNat_dvd.mp hdiv

}


lemma carmichael_is_squarefree  {n : ℕ} (h: isCarmichael n) : Squarefree n := by{
  rw [isCarmichael] at h
  have hp: ¬ Nat.Prime n ∧ n > 1 := by constructor;exact h.1;exact h.2.2
  have hn : n >1 := hp.2
  have h:= h.2.1
  rename_i h_1
  rw [@squarefree_iff_prime_squarefree]
  by_contra hnot
  simp at hnot
  obtain ⟨p, hp, hd⟩:=hnot
  have hd: ∃ k,∃ n', k≥ 2 ∧ p^k*n'=n ∧ Nat.gcd p n' = 1 := by {
    rw [← Nat.pow_two] at hd
    exact prime_dvd_def hd hp (zero_lt_of_lt hn)
  }
  have hobvious : (n - 1 + 1) = n := by ring_nf; apply add_sub_of_le; linarith
  obtain ⟨k, n', hk, hpk, hpn⟩:=hd
  have hcong: ∃ (a : ℕ), a ≡ 1 + p [MOD p^k] ∧  a ≡ 1 [MOD n']:= by{
    have hcop: (p^k).Coprime n' := by exact Coprime.pow_left k hpn
    obtain ⟨a, ha⟩ := Nat.chineseRemainder hcop (1 + p) 1
    use a
  }
  obtain ⟨a, ha⟩ := hcong
  have hgcd : a.gcd ↑n = 1 := by {
    obtain ⟨left, right⟩ := ha
    have h1: a.gcd n' = 1 := by {
      calc a.gcd n' = (1).gcd n' := by exact ModEq.gcd_eq right
      _ = 1 := by exact Nat.gcd_one_left n'
    }
    have h2: a.gcd (p^k) = 1 := by {
      have haux: a.gcd (p^k) = (1+p).gcd (p^k) := by exact ModEq.gcd_eq left
      have haux2: (1+p).gcd (p) = 1 := by simp
      rw[haux]
      exact Coprime.pow_right k haux2
    }
    have hfin : a.gcd n ∣  1 := by {
      rw [←hpk]
      calc a.gcd ((p^k) * n' )∣ a.gcd (p^k) * a.gcd (n') := by exact Nat.gcd_mul_dvd_mul_gcd a (p ^ k) n'
      _ =  a.gcd (p^k) * 1 := by rw [h1]
      _ = 1 := by rw[h2];
    }
    exact Nat.eq_one_of_dvd_one hfin
  }
  specialize h a
  have h := h hgcd

  have hcarm : a ^ (n-1) ≡ 1 [MOD n] := by {
    refine Nat.ModEq.symm (Nat.modEq_of_dvd ?_)
    subst hpk
    simp_all only [ge_iff_le, not_false_eq_true, gt_iff_lt, and_self, Nat.cast_mul, Nat.cast_pow, implies_true,
      Nat.cast_one]
  }
  have hred : (1+ p)^(n-1) ≡ 1 [MOD p^2] := by {
    have ha := ha.1
    have hb :  a ≡ 1 + p [MOD p ^ 2] := by {
      apply Nat.modEq_of_dvd
      rw [Nat.modEq_iff_dvd] at ha
      norm_cast at *
      calc ↑(p^2) ∣ ↑(p^k) := by refine ofNat_dvd.mpr ?_; exact Nat.pow_dvd_pow p hk
      _ ∣ subNatNat (1 + p) a:= by exact ha
    }
    have hc : a ^ (n - 1) ≡ 1 [MOD p^2] := by {
      apply Nat.modEq_of_dvd
      rw [Nat.modEq_iff_dvd] at hcarm
      norm_cast at *
      calc  ↑(p^2) ∣ ↑(n) := by  refine ofNat_dvd.mpr ?_ ; rw [← Nat.pow_two] at hd; exact hd
      _ ∣ subNatNat 1 (a ^ (n - 1)) := by exact hcarm
    }
    calc (1+ p)^(n-1) ≡ a ^ (n - 1) [MOD p^2] := by exact Nat.ModEq.pow (n - 1) (_root_.id (Nat.ModEq.symm hb))
    _ ≡ 1 [MOD p^2] := by exact hc
  }
  exact SquareFreePart2 hp hd hpk hn hred hk
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


theorem Korselt {n : ℕ} (hp1: ¬ Nat.Prime n) (hp2: n > 1) : isCarmichael n ↔ (Squarefree n ∧ (∀ p, Nat.Prime p ∧ p ∣ n → (p-1:ℤ) ∣ (n-1:ℤ))) :=
  by {
    constructor
    . intro h
      rw [isCarmichael] at h
      have hsq: Squarefree n := by{
        exact carmichael_is_squarefree h
      }
      have h:= h.2.1
      constructor
      . exact hsq
      . intro p hpp
        have hpn:=hpp.1.2
        have hdiv:= hpp.2
        have hpp:= hpp.1

        have h2 : Nat.gcd p n = p := by apply Nat.gcd_eq_left ; exact hdiv

        have h3 : ¬p ^ 2 ∣ n := by{
          intro hcontra
          rw [@squarefree_iff_prime_squarefree] at hsq
          specialize hsq p
          have hsq := hsq hpp
          ring_nf at hsq
          contradiction
        }
        have h4: p.Coprime (n/p):= by{
          refine coprime_iff_gcd_eq_one.mpr ?_
          sorry
        }
        have h5: ∃b, b^(p-1)≡ 1 [ZMOD p] := by sorry
        obtain ⟨ b, hb ⟩ := h5
        have h6:∃a, a ≡ b [ZMOD p] ∧ a ≡ 1[ZMOD (n/p)]:= by sorry
        obtain ⟨ a, ha ⟩ := h6
        have h7 : a.gcd (n/p) =1:= by {
          sorry

        }
        sorry
    . intro h
      rw [isCarmichael]
      constructor
      . exact hp1
      . constructor
        . intro a han
          have hpa: ∀p, Nat.Prime p ∧ p∣n → IsCoprime a p:= by{
            intro p hpp
            rw [@dvd_def] at hpp
            have hpp:=hpp.2
            obtain ⟨c, hc⟩:= hpp
            rw[hc] at han
            rw [@isCoprime_iff_gcd_eq_one]
            exact gcd_eq_one_of_gcd_mul_right_eq_one_left han
          }
          have hpa: ∀p, Nat.Prime p ∧ p∣n → a ^ (p - 1) ≡ 1 [ZMOD (p:ℤ)] := by{
            intro p hp1
            specialize hpa p hp1
            exact Int.ModEq.pow_card_sub_one_eq_one hp1.1 hpa
          }
          have hpa: ∀p, Nat.Prime p ∧ p∣n → a ^ (n - 1) ≡ 1 [ZMOD (p:ℤ)] := by{
            intro p hp1
            specialize hpa p hp1
            have h:= h.2 p hp1
            have hf: (p-1:ℤ) = (p-1:ℕ) := by {
              exact Eq.symm (Int.natCast_pred_of_pos (Prime.pos hp1.1))
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
            rw [← hc] at h2
            exact h2
          }
          have hsetP:=exists_prime_descomposition_squarefree (zero_lt_of_lt hp2) h.1
          obtain ⟨setP, hsetP⟩:=hsetP
          have h': ∀s: Finset ℕ, (∀ p: ℕ, p ∈ s → (Nat.Prime p ∧ p ∣ n)) → a^(n-1) ≡ 1 [ZMOD (∏ p in s, p)] := by{
            intro s
            induction s using Finset.induction with
            | empty => {
              intro hintro
              simp
              exact Int.modEq_one
            }
            | @insert x s hxs ih => {
              intro hintro
              rw [Finset.prod_insert hxs]
              rw [← Int.modEq_and_modEq_iff_modEq_mul]
              constructor
              . exact (hpa x (hintro x (mem_insert_self x s)))--exact ((hintro.2.2.2 x) (mem_insert_self x s))
              apply ih ?_
              intro p hp
              exact hintro p (mem_insert_of_mem hp)
              simp
              have haux: (∀ p ∈ insert x s, Nat.Prime p ∧ p ∣ n) → (x:ℤ).natAbs.Coprime (∏ x ∈ s, (x:ℤ)).natAbs := by{
                induction s using Finset.induction with
                  | empty => intro h2; exact coprime_of_dvd' fun k a a a ↦ a
                  | @insert x2 s2 hxs2 ih2 => {
                    intro hintro2
                    rw [Finset.prod_insert hxs2]
                    have hintro1: ¬ x∈ s2 := by {
                      by_contra hnot
                      exact hxs (Finset.mem_insert_of_mem hnot)
                    }
                    have hintro2: ((∀ p ∈ s2, Nat.Prime p ∧ p ∣ n) → a ^ (n - 1) ≡ 1 [ZMOD ∏ p ∈ s2, ↑p]) := sorry
                    have hintro3: (∀ p ∈ insert x s2, Nat.Prime p ∧ p ∣ n) := by {
                      intro p hp
                      rw [@Finset.mem_insert] at hp
                      obtain hp|hp:=hp
                      . rw [hp]
                        have hend: x∈ insert x (insert x2 s2) := by exact mem_insert_self x (insert x2 s2)
                        exact hintro x hend
                      . have hend: p ∈ insert x (insert x2 s2) := Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp)
                        exact hintro p hend
                    }
                    specialize ih2 hintro1 hintro2 hintro3
                    rw [Int.natAbs_mul]
                    refine Coprime.mul_right ?insert.insert.H1 (ih2 hintro3)
                    have hx:= (hintro x (mem_insert_self x (insert x2 s2))).1
                    have hx2:= (hintro x2 (Finset.mem_insert_of_mem (mem_insert_self x2 s2) )).1
                    simp
                    refine (coprime_primes hx hx2).mpr ?insert.insert.H1.a
                    by_contra hnot
                    have hlast: x ∈ insert x2 s2 := by {
                      rw [hnot]
                      exact mem_insert_self x2 s2
                    }
                    exact hxs hlast
                  }
              }
              exact haux hintro
            }
          }
          have hcond: ∀ p ∈ setP, Nat.Prime p ∧ p ∣ n := by {
            intro p hp
            apply (hsetP.1 p).1 hp
          }
          have h':=h' setP hcond
          have hcond: ∏ p ∈ setP, (p:ℤ)=(n:ℤ):= by {
            have hsetP:=hsetP.2
            rw [Mathlib.Tactic.Zify.natCast_eq] at hsetP
            rw [@Nat.cast_prod] at hsetP
            exact hsetP
          }
          rw [hcond] at h'
          exact Int.ModEq.dvd (_root_.id (Int.ModEq.symm h'))
        . exact hp2
  }

lemma Korselts_criterion' {p0 p1 p2: ℕ} : Nat.Prime p0 ∧ Nat.Prime p1 ∧ Nat.Prime p2 ∧
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
  intro p hp
  have hpp := hp.2
  have hp := hp.1
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
  refine not_prime_mul ?intro.intro.intro.intro.intro.intro.intro.hp.left.a1 ?intro.intro.intro.intro.intro.intro.intro.hp.left.b1
  exact Ne.symm (Nat.ne_of_lt hp01g)
  exact Ne.symm (Nat.ne_of_lt hp2g)
  exact Right.one_lt_mul' hp01g hp2g
}

@[simp] lemma isCarmichael' (n: ℕ): isCarmichael n ↔ (n > 1 ∧ ¬ Nat.Prime n ∧ ∀ (a : ℤ), (n:ℤ) ∣ a^(n-1)-1) := by{
  constructor
  . intro h
    unfold isCarmichael at h
    constructor
    . exact h.2.2
    constructor
    . exact h.1
    sorry
  . intro hpn
    have han:=hpn.2.2
    have h1n:=hpn.1
    have hpn:=hpn.2.1
    unfold isCarmichael
    constructor
    exact hpn
    constructor
    . intro a ha
      exact han a
    exact h1n
}

theorem carmichael_properties {k: ℕ} : isCarmichael k → ¬ 2 ∣ k ∧
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
#eval Squarefree 561
lemma NotCarmichaelPrime(p :ℕ ) (hp :Nat.Prime p) : ¬ isCarmichael p := by{
  rw[isCarmichael];
  push_neg;
  intro _ __1
  simp_all only
  }

lemma listPrime561 : Nat.primeFactorsList 561 = [3, 11, 17] := by {
    have h1 : 561 = 3 * 11 * 17 := by norm_num
    have p3 : Nat.Prime 3 := by exact Nat.prime_three
    have p11 : Nat.Prime 11 := by exact properDivisors_eq_singleton_one_iff_prime.mp rfl
    have p17 : Nat.Prime 17 := by exact properDivisors_eq_singleton_one_iff_prime.mp rfl
    simp_rw[h1];
    have h2:Nat.primeFactorsList 3 = [3] := by exact primeFactorsList_prime p3
    have h3:Nat.primeFactorsList 11= [11] := by exact primeFactorsList_prime p11
    have h4:Nat.primeFactorsList 17= [17] := by exact primeFactorsList_prime p17
    have h2:Nat.primeFactorsList (3*11) = [3,11] := by  {
      simp [Nat.primeFactorsList, Nat.factorization];
      constructor
      · norm_num
      · norm_num; exact h3
    }
    have h2:Nat.primeFactorsList (187) = [11,17] := by  {
      simp [Nat.primeFactorsList, Nat.factorization];
      constructor
      · norm_num
      · norm_num; exact h4
    }
    simp [Nat.primeFactorsList, Nat.factorization];
    constructor
    · norm_num
    · norm_num; exact h2


}
lemma LowestCarmichael : isCarmichael 561 ∧ ∀ (i :ℕ ), i < 561 → ¬ isCarmichael i:= by {
  constructor
  ·
    have h1 : 561 = 3 * 11 * 17 := by norm_num
    -- Step 2: Verify primes
    have p3 : Nat.Prime 3 := by exact Nat.prime_three
    have p11 : Nat.Prime 11 := by exact properDivisors_eq_singleton_one_iff_prime.mp rfl
    have p17 : Nat.Prime 17 := by exact properDivisors_eq_singleton_one_iff_prime.mp rfl
    have sq3 : Squarefree 3 := by exact Irreducible.squarefree p3
    have sq11 : Squarefree 11 := by exact Irreducible.squarefree p11
    have sq17 : Squarefree 17 := by exact Irreducible.squarefree p17
    -- Step 3: Check divisors
    rw [h1]
    rw [Korselt]
    constructor
    · by_contra hc
      rw [@Nat.squarefree_mul_iff] at hc
      rw [@coprime_mul_iff_left] at hc
      have hd : (Coprime 3 17 ∧ Coprime 11 17) ∧ Squarefree (3 * 11) ∧ Squarefree 17 := by {
        constructor
        · constructor
          · norm_num
          · norm_num
        · constructor
          · refine _root_.squarefree_mul_iff.mpr ?right.left.a
            constructor
            · exact coprime_iff_isRelPrime.mp rfl
            · exact ⟨sq3, sq11⟩
          · exact sq17

      }
      contradiction
    · intro p hp
      norm_num
      simp_all only [Nat.reduceMul]
      obtain ⟨left, right⟩ := hp
      have h1 : 561 = 3 * 11 * 17 := by norm_num
      have h2 : Nat.primeFactorsList 561 = [3, 11, 17] := by simp_rw[h1]; exact listPrime561
      have hlist : p ∈ [3, 11, 17] := by{
        rw[←h2]
        refine (mem_primeFactorsList ?hn).mpr ?_
        exact Ne.symm (zero_ne_add_one 560)
        exact And.symm ⟨right, left⟩
      }
      fin_cases hlist
      · norm_num
      · norm_num
      · norm_num
    · norm_num
    · norm_num
  · intro i hi
    have h_2: Nat.Prime i → ¬ isCarmichael i := by sorry
    have h_2_1 : Nat.Prime (i/3) ∧ ¬((i/3)-1) ∣ (i-1) → ¬ isCarmichael i := by sorry
    have h_2_2 : Nat.Prime (i/5) ∧ ¬((i/5)-1) ∣ (i-1) → ¬ isCarmichael i := by sorry
    have h_3 : 2 ∣ i → ¬ isCarmichael i := by sorry
    have h_4 : 3∣ i ∧ ¬ 2 ∣ (i-1) →¬ isCarmichael i := by sorry
    have h_5 : 5∣ i ∧ ¬ 4 ∣ (i-1) →¬ isCarmichael i := by sorry
    have h_6 : 7∣ i ∧ ¬ 6 ∣ (i-1) →¬ isCarmichael i := by sorry
    have h_7 : 11∣ i ∧ ¬ 10∣ (i-1) →¬ isCarmichael i := by sorry
    have h_8 : 13∣ i ∧ ¬ 12∣ (i-1) →¬ isCarmichael i := by sorry
    have h_9: 17∣ i ∧ ¬ 16∣ (i-1) →¬ isCarmichael i := by sorry
    have h_10: 19∣  i ∧ ¬ 18∣ (i-1) →¬ isCarmichael i := by sorry
    have h_11: 23∣ i ∧ ¬ 22∣ (i-1) →¬ isCarmichael i := by sorry
    have h_12: 29∣ i ∧ ¬ 28∣ (i-1) →¬ isCarmichael i := by sorry
    have h_13: 31∣ i ∧ ¬ 30∣ (i-1) →¬ isCarmichael i := by sorry
    have h_14: 37∣ i ∧ ¬ 36∣ (i-1) →¬ isCarmichael i := by sorry
    have h_15: 41∣ i ∧ ¬ 40∣ (i-1) →¬ isCarmichael i := by sorry
    have h_16: 47∣ i ∧ ¬ 46∣ (i-1) →¬ isCarmichael i := by sorry
    have h_17: 53∣ i ∧ ¬ 52∣ (i-1) →¬ isCarmichael i := by sorry
    have h_18: 59∣ i ∧ ¬ 58∣ (i-1) →¬ isCarmichael i := by sorry
    have h_19: 61∣ i ∧ ¬ 60∣ (i-1) →¬ isCarmichael i := by sorry
    have h_20: 67∣ i ∧ ¬ 66∣ (i-1) →¬ isCarmichael i := by sorry
    have h_22: 73∣ i ∧ ¬ 72∣ (i-1) →¬ isCarmichael i := by sorry
    have h_23: 89∣ i ∧ ¬ 88∣ (i-1) →¬ isCarmichael i := by sorry
    have h_24: 79∣ i ∧ ¬ 78∣ (i-1) →¬ isCarmichael i := by sorry
    have h_sq : (Nat.sqrt i) * (Nat.sqrt i) = i → ¬ isCarmichael i := by sorry
    have h_s9: 9 ∣ i →  ¬ isCarmichael i := by sorry
    have h_s25 : 25 ∣ i →  ¬ isCarmichael i := by sorry
    have h_sq_3 : (Nat.sqrt (i/3)) * (Nat.sqrt (i/3)) = (i/3)→ ¬ isCarmichael i := by sorry
    have h_sq_5: (Nat.sqrt (i/5)) * (Nat.sqrt (i/5)) = (i/5)→ ¬ isCarmichael i := by sorry
    have h_sq_7: (Nat.sqrt (i/7)) * (Nat.sqrt (i/7)) = (i/7)→ ¬ isCarmichael i := by sorry
    interval_cases i

    all_goals try {apply h_4; norm_num; done}
    all_goals try {apply h_2; norm_num; done}
    all_goals try {apply h_3; norm_num; done}
    all_goals try {apply h_5; norm_num; done}
    all_goals try {apply h_6; norm_num; done}
    all_goals try {apply h_7; norm_num; done}
    all_goals try {apply h_8; norm_num; done}
    all_goals try {apply h_9; norm_num; done}
    all_goals try {apply h_2_1; norm_num; done}
    all_goals try {apply h_2_2; norm_num; done}
    all_goals try {apply h_10; norm_num; done}
    all_goals try {apply h_13; norm_num; done}
    all_goals try {apply h_14; norm_num; done}
    all_goals try {apply h_15; norm_num; done}
    all_goals try {apply h_16; norm_num; done}
    all_goals try {apply h_17; norm_num; done}
    all_goals try {apply h_18; norm_num; done}
    all_goals try {apply h_19; norm_num; done}
    all_goals try {apply h_20; norm_num; done}
    all_goals try {apply h_22; norm_num; done}
    all_goals try {apply h_sq; norm_num; done}
    all_goals try {apply h_sq_3; norm_num; done}
    all_goals try {apply h_sq_5; norm_num; done}
    all_goals try {apply h_sq_7; norm_num; done}
    all_goals try {apply h_24; norm_num; done}


}

