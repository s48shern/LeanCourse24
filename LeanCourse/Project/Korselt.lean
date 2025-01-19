import LeanCourse.Project.Carmichael
import Mathlib
import Mathlib.GroupTheory.OrderOfElement

open Real Function Nat BigOperators Set Finset Algebra Int
open Classical

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

lemma group_unit {M₀ : Type} [MonoidWithZero M₀] [Nontrivial M₀] (b : M₀) (hu: IsUnit b) :b ≠ 0 := by {
  exact IsUnit.ne_zero hu
}

lemma Unit_divides(p a: ℕ) (b : ZMod p) (hu: IsUnit b)(hp: Nat.Prime p)  :¬ p ∣ b.val:= by{
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
lemma equality_greater_1 (n:ℕ) (h: n ≥ 1):(Nat.cast (n-1):ℤ) = subNatNat n 1:= by {
  exact Eq.symm (subNatNat_of_le h)
}
lemma Product_cast {p a: ℕ} (b: (ZMod p)ˣ) (hp: Nat.Prime p) (hb :(b: ZMod p)^(a)=(b: ZMod p)^(orderOf b) ): b^(a)=b^(orderOf b) := by {
  ext : 1
  simp_all only [Units.val_pow_eq_pow_val]
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
    have h5_1 : ∃ (b : (ZMod p)ˣ), IsUnit (b: ZMod p) ∧ orderOf b  = p - 1 :=by {
      by_cases hp: p >2
      · have hCyclic : IsAddCyclic ((ZMod p)):= by exact ZMod.instIsAddCyclic p
        have hCyclic2 : IsCyclic ((ZMod p)ˣ):= by {
          haveI : Fact (Nat.Prime p) := ⟨hpp⟩
          exact instIsCyclicUnitsOfFinite
        }
        rw [@isCyclic_iff_exists_ofOrder_eq_natCard] at hCyclic2
        have hcard: Nat.card (ZMod p)ˣ = p-1 := by {
          haveI : Fact (Nat.Prime p) := ⟨hpp⟩
          simp [ZMod.card_units_eq_totient p]
          exact totient_prime hpp
        }
        rw [hcard] at hCyclic2
        obtain ⟨b, hb⟩ := hCyclic2
        use b
        constructor
        · exact Units.isUnit b
        · haveI : NeZero p := ⟨Nat.Prime.ne_zero hpp⟩
          exact hb
      · have hp2: p =2 := by {
          have hp2 : p ≤ 2:= by exact Nat.le_of_not_lt hp
          refine Eq.symm (Nat.le_antisymm ?h₁ hp2)
          exact Prime.two_le hpp
        }
        use 1
        constructor
        exact isUnit_one
        rw [hp2]
        simp
    }
    obtain ⟨b, hb', hb''⟩ := h5_1
    specialize h5 ((b: ZMod p)).val

    have hb : ¬ ((b: ZMod p)).val ≡ 0 [ZMOD ↑p]:= by{
      by_contra hc
      rw [← ZMod.intCast_eq_intCast_iff] at hc
      norm_cast at hc
      rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at hc
      have hndiv : ¬ p ∣ (b: ZMod p).val := by exact Unit_divides p n b hb' hpp
      contradiction
    }
    simp [hb] at h5
    have h6:∃a, a ≡ (b: ZMod p).val [ZMOD p] ∧ a ≡ 1[ZMOD (n/p)] ∧ a ≥ 0:= by {
      obtain ⟨a, ha⟩ := Nat.chineseRemainder h4 ((b: ZMod p)).val 1
      obtain ⟨l, r⟩:=ha
      use a
      constructor
      · exact (ZmodtoMod (p) (a) ((b: ZMod p)).val).mpr l
      · constructor
        · exact (ZmodtoMod (n/p) (a) (1)).mpr r
        · exact ofNat_zero_le a

    }
    obtain ⟨ a, ha ⟩ := h6
    have hg0 := ha.2.2
    have ha: a ≡ ↑(b: ZMod p).val [ZMOD ↑p] ∧ a ≡ 1 [ZMOD ↑n / ↑p] := by {
      constructor
      · exact ha.1
      · exact ha.2.1
    }
    have h7 : a.gcd (n/p) =1:= by {
      have ha:= ha.2
      have ha: (n/p:ℤ) ∣ a - 1 := by exact Int.ModEq.dvd (_root_.id (Int.ModEq.symm ha))
      rw [Int.dvd_def] at ha
      obtain ⟨c, hc⟩:=ha
      apply Tactic.NormNum.int_gcd_helper' 1 (-c)
      . simp
      . simp
      ring_nf
      rw [← hc]
      ring_nf
    }

    have h7_1 : a.gcd n =1:= by {
      have ha' : a = a.toNat := by exact Eq.symm (toNat_of_nonneg hg0)
      have ha:= ha.1
      have ha: ↑p ∣  (b: ZMod p).val -a :=by exact Int.ModEq.dvd ha
      have ha: ¬ ↑p ∣ a := by {
        by_contra hnot
        have hb2:(p:ℤ) ∣ ((b: ZMod p).val:ℤ) := by exact (Int.dvd_iff_dvd_of_dvd_sub ha).mpr hnot
        rw [@Int.modEq_zero_iff_dvd] at hb
        contradiction
      }
      rw[ha'] at ha
      norm_cast at ha;
      have hgcd: a.toNat.gcd p = 1 := by {
        have hcop :Coprime p a.toNat:= by exact (Nat.Prime.coprime_iff_not_dvd hpp).mpr ha
        exact coprime_comm.mp hcop
      }
      rw[ha']
      norm_cast
      have hfin: a.toNat.gcd n ∣1 := by {
        calc a.toNat.gcd n =  a.toNat.gcd (n/p * p) := by {
          have hdiv: n = n/p * p := by exact Eq.symm (Nat.div_mul_cancel hdiv)
          rw[←hdiv]
        }
        _ ∣  a.toNat.gcd (n/p) *a.toNat.gcd p := by exact Nat.gcd_mul_dvd_mul_gcd a.toNat (n / p) p
        _ = 1 * 1 := by rw[hgcd]; rw[ha'] at h7; norm_cast at h7; rw[h7]
      }

      exact Nat.eq_one_of_dvd_one hfin
    }

    have h8 : a^(n-1) ≡ 1 [ZMOD n] := Int.ModEq.symm ((fun {n a b} ↦ Int.modEq_iff_dvd.mpr) (h a h7_1))
    have h9 : a^(n-1) ≡ 1 [ZMOD p] := by{
      refine Int.ModEq.symm ((fun {n a b} ↦ Int.modEq_iff_dvd.mpr) ?_)
      calc (p:ℤ) ∣ n := by norm_cast;
      _ ∣ a ^ (n - 1) - 1 := by exact Int.ModEq.dvd (_root_.id (Int.ModEq.symm h8))
    }
    have h10 : ((b: ZMod p)).val^(n-1) ≡ 1 [ZMOD p]:= by {
      calc ((b: ZMod p).val)^(n-1) ≡ (a)^(n-1) [ZMOD p] := by refine Int.ModEq.symm (Int.ModEq.pow (n - 1) ?h1); exact ha.1
      _ ≡ 1 [ZMOD p] := by exact h9
    }
    have hend: p - 1 ∣ n - 1 := by {
      haveI : NeZero p := ⟨Nat.Prime.ne_zero hpp⟩

      have hend': orderOf b ∣ n-1 := by {
        have haux: ↑(b: ZMod p).val ^ (n - 1) ≡ ↑(b: ZMod p).val ^ (p- 1) [ZMOD ↑p] := by exact  Int.ModEq.trans h10 (_root_.id (Int.ModEq.symm h5))
        rw[← hb''] at haux
        norm_cast at haux
        have haux' : (b: ZMod p)^(n-1)=(b: ZMod p)^(orderOf b) := by {
          have haux' :(b: ZMod p).val ^ (n - 1) ≡ (b: ZMod p).val ^ (orderOf b) [MOD p] := by exact (ModtoZmod (p) ((b: ZMod p).val ^ (n - 1)) ((b: ZMod p).val ^ (orderOf b))).mpr haux
          rw [← ZMod.eq_iff_modEq_nat] at haux'
          simp at haux'
          exact haux'
        }
        have haux' : b^(n-1)=b^(orderOf b) := by {
              exact Product_cast b hpp haux'
        }
        apply orderOf_dvd_of_pow_eq_one
        have hb : b^orderOf b = 1 := by exact pow_orderOf_eq_one b
        rw [← hb]
        exact haux'


      }

      simp_rw[hb''] at hend'
      exact hend'
    }
    zify at hend
    norm_cast
    have hn : (Nat.cast (p-1):ℤ) = subNatNat p 1 := by apply equality_greater_1 p; exact Prime.one_le hpp
    have hn2 : (Nat.cast (n-1):ℤ) = subNatNat n 1 := by apply equality_greater_1 n; exact one_le_of_lt hp2
    rw [← hn]
    rw[← hn2]
    exact hend

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
