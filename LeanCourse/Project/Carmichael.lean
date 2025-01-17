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

#check ZMod.isUnit_iff_coprime

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
lemma existenceCyclic (p a: ℕ) (hp: Nat.Prime p): ∃ (b: ℕ ), IsUnit ↑b := by{
  apply?

}
lemma korselt_prime_division {n : ℕ} (h: isCarmichael n) ( hsq: Squarefree n ):(∀ p, Nat.Prime p ∧ p ∣ n → (p-1:ℤ) ∣ (n-1:ℤ)) ∧ ¬ Nat.Prime n ∧ n > 1 := by{
  have hp1:= h.1
  have hp2:= h.2.2
  rw [isCarmichael] at h
  have h:= h.2.1;
  constructor
  · intro p hpp
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
      refine (Nat.Prime.coprime_iff_not_dvd hpp).mpr ?_
      by_contra hnot
      rw [propext (Nat.dvd_div_iff_mul_dvd hdiv)] at hnot
      rw [← Nat.pow_two] at hnot
      exact h3 hnot
    }

    have h5: ∀b, b≡0 [ZMOD p] ∨ b^(p-1)≡ 1 [ZMOD p] := by {
      intro b
      by_cases hcase: b ≡ 0 [ZMOD ↑p]
      left;exact hcase
      right
      refine ModEq.pow_card_sub_one_eq_one hpp ?_
      rw [@Int.modEq_zero_iff_dvd] at hcase
      rw[isCoprime_comm, Prime.coprime_iff_not_dvd]
      exact hcase
      exact prime_iff_prime_int.mp hpp
    }
    have h5_1 : ∃ (b : (ZMod p)), IsUnit b :=by {
      by_cases hp: p >2
      · use 2
        have hcop: Nat.Coprime 2 p:= by {
          refine coprime_two_left.mpr ?_
          have hp2: p ≠ 2 := by linarith
          exact Prime.odd_of_ne_two hpp hp2
        }
        rw [←ZMod.isUnit_iff_coprime 2 p] at hcop
        have haux : 2 = ↑2 := by norm_num
        norm_num at hcop
        exact hcop

      · have hp2: p =2 := by {
          have hp2 : p ≤ 2:= by exact Nat.le_of_not_lt hp
          refine Eq.symm (Nat.le_antisymm ?h₁ hp2)
          exact Prime.two_le hpp
        }
        use 1
        exact isUnit_one
    }
    obtain ⟨b, hb'⟩ := h5_1
    specialize h5 (b).val

    have hb : ¬ (b).val ≡ 0 [ZMOD ↑p]:= by{
      by_contra hc
      rw [← ZMod.intCast_eq_intCast_iff] at hc
      norm_cast at hc
      rw? at hc

    }
    simp [hb] at h5
    have h6:∃a, a ≡ b.val [ZMOD p] ∧ a ≡ 1[ZMOD (n/p)]:= by {
      obtain ⟨a, ha⟩ := Nat.chineseRemainder h4 (b).val 1
      obtain ⟨l, r⟩:=ha
      use a
      constructor
      · exact (ZmodtoMod (p) (a) (b).val).mpr l
      · exact (ZmodtoMod (n/p) (a) (1)).mpr r
    }
    obtain ⟨ a, ha ⟩ := h6
    have h7 : a.gcd (n/p) =1:= by {
      have ha:= ha.2
      have ha: (n/p:ℤ) ∣ a - 1 := Int.ModEq.dvd (_root_.id (Int.ModEq.symm ha))
      rw [Int.dvd_def] at ha
      obtain ⟨c, hc⟩:=ha
      apply Tactic.NormNum.int_gcd_helper' 1 (-c)
      . simp
      . simp
      ring_nf
      rw [← hc]
      ring_nf
    }
    have h8 : a^(n-1) ≡ 1 [ZMOD n] := by{
      obtain ⟨l, r⟩:=ha
      sorry
    }
    have h9 : a^(n-1) ≡ 1 [ZMOD p] := by{
      refine Int.ModEq.symm ((fun {n a b} ↦ Int.modEq_iff_dvd.mpr) ?_)
      calc (p:ℤ) ∣ n := by norm_cast;
      _ ∣ a ^ (n - 1) - 1 := by exact Int.ModEq.dvd (_root_.id (Int.ModEq.symm h8))
    }
    have h10 : (↑(b2))^(n-1) ≡ 1 [ZMOD p]:= by {
      calc (↑(b2))^(n-1) ≡ (a)^(n-1) [ZMOD p] := by refine Int.ModEq.symm (Int.ModEq.pow (n - 1) ?h1); exact ha.1
      _ ≡ 1 [ZMOD p] := by exact h9
    }


    sorry
  · constructor
    · exact hp1
    · exact hp2
}
theorem Korselt {n : ℕ} : isCarmichael n ↔ (Squarefree n ∧ (∀ p, Nat.Prime p ∧ p ∣ n → (p-1:ℤ) ∣ (n-1:ℤ)) ∧ ¬ Nat.Prime n ∧ n > 1) :=
  by {
    constructor
    . intro h
      have hp1:= h.1
      have hp2:= h.2.2
      rw [isCarmichael] at h
      have hsq: Squarefree n := by{
        exact carmichael_is_squarefree h
      }
      constructor
      . have h:= h.2.1; exact hsq
      . rw [← isCarmichael] at h; exact korselt_prime_division h hsq
    . intro h
      have hp1:= h.2.2.1
      have hp2:= h.2.2.2
      have h: Squarefree n ∧ (∀ (p : ℕ), Nat.Prime p ∧ p ∣ n → (p:ℤ) - 1 ∣ (n:ℤ) - 1) := by{
        constructor
        exact h.1
        exact h.2.1
      }
      rw [isCarmichael]
      constructor
      . exact hp1
      . constructor
        . intro a han
          have han: ∀p, Nat.Prime p ∧ p∣ n → a ^ (n - 1) ≡ 1 [ZMOD (p:ℤ)] := by {
            intro p hp
            refine n_pow_card_sub_one_eq_one hp.1 hp.2 (h.2 p hp) hp2 ?_
            refine coprime_if_dvd_coprime ?_ hp.2
            exact isCoprime_iff_gcd_eq_one.mpr han
          }
          have hsetP:=exists_prime_descomposition_squarefree (zero_lt_of_lt hp2) h.1
          obtain ⟨setP, hsetP⟩:=hsetP
          have hcond: (∀ p ∈ setP, a ^ (n - 1) ≡ 1 [ZMOD ↑p]) := by {
            intro p a_1
            simp_all only [gt_iff_lt, and_imp]
          }
          refine Int.ModEq.dvd ?mpr.right.left.intro.a
          refine Int.ModEq.symm ?mpr.right.left.intro.a.a
          exact (congruence_by_prime_decomposition (zero_lt_of_lt hp2) h.1 hsetP.1).1 hcond
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
  constructor
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
  constructor
  refine not_prime_mul ?intro.intro.intro.intro.intro.intro.intro.hp.left.a1 ?intro.intro.intro.intro.intro.intro.intro.hp.left.b1
  exact Ne.symm (Nat.ne_of_lt hp01g)
  exact Ne.symm (Nat.ne_of_lt hp2g)
  exact Right.one_lt_mul' hp01g hp2g
}

@[simp] lemma isCarmichael' {n: ℕ}: isCarmichael n ↔ (n > 1 ∧ ¬ Nat.Prime n ∧ ∀ (a : ℤ), (n:ℤ) ∣ a^n-a) := by{
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
      simp at hcase
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
    simp
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
    simp
    have hp2:=hp.2
    have hp:=hp.1
    refine Nat.lt_of_le_of_ne ?h.h.a.h₁ ?h.h.a.h₂
    refine Nat.le_of_dvd (zero_lt_of_lt hnk) hp2
    by_contra hnot
    rw [hnot] at hp
    exact hpk hp
    exact hnum
  }
  simp at hnum
  by_contra hnot
  simp at hnot
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
  simp at hnot
  have hep: ∃ p, Nat.Prime p ∧ p ∣ k := by {
    refine Nat.exists_prime_and_dvd ?hn
    have h:=h.2.2
    exact Ne.symm (Nat.ne_of_lt h)
  }
  have hnot: s.card=1 ∨ s.card=2 := by{
    refine le_and_le_add_one_iff.mp ?_
    constructor
    simp
    obtain ⟨ p, hp⟩:= hep
    have hep:= (hs p).2 hp
    rw [@Finset.nonempty_iff_ne_empty]
    exact ne_empty_of_mem hep
    simp
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
    simp at pdes
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
      _ = k := by simp
    }
    norm_cast at hnot
    have hnot: ¬ p * q = k := by exact Nat.ne_of_lt hnot
    exact hnot pdes
}
