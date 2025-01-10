import LeanCourse.Project.Carmichael

open Real Function Nat BigOperators Set Finset Algebra Int
open Classical

#eval Squarefree 561
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
lemma Carmichael561: isCarmichael 561 := by {
  have h1 : 561 = 3 * 11 * 17 := by norm_num
  have p3 : Nat.Prime 3 := by exact Nat.prime_three
  have p11 : Nat.Prime 11 := by exact properDivisors_eq_singleton_one_iff_prime.mp rfl
  have p17 : Nat.Prime 17 := by exact properDivisors_eq_singleton_one_iff_prime.mp rfl
  have sq3 : Squarefree 3 := by exact Irreducible.squarefree p3
  have sq11 : Squarefree 11 := by exact Irreducible.squarefree p11
  have sq17 : Squarefree 17 := by exact Irreducible.squarefree p17
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
}
lemma NotCarmichaelPrime(p :ℕ ) (hp :Nat.Prime p) : ¬ isCarmichael p := by{
  rw[isCarmichael];
  push_neg;
  intro _ __1
  simp_all only
  }
lemma NotCarmichaelPrimeDiv(p i:ℕ ): i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime p ∧  p ∣ i ∧ ¬ (p-1:ℤ) ∣ (i-1:ℤ)→ ¬ isCarmichael i := by{
  intro hi
  obtain ⟨hi, hnp, hp, hdiv⟩ := hi
  rw[Korselt];
  push_neg;
  intro h
  use p
  simp_all only [and_self, true_and]
  obtain ⟨left, right⟩ := hdiv
  · exact fun a ↦ a
  · exact hnp
  · exact hi
  }


lemma sqdiv2 (i j:ℕ ): j > 0∧ j ∣ i ∧ ¬ Nat.Prime i ∧  i/j >1∧(Nat.sqrt (i/j)) * (Nat.sqrt (i/j))= (i/j)→¬ isCarmichael i := by {
  intro hi
  obtain ⟨hj, hj2, h1, h2,h⟩ := hi
  rw[Korselt]
  rw [← Nat.exists_mul_self] at h
  obtain ⟨ n, hn⟩ := h
  rw [not_and_or]
  have h:¬ Squarefree i := by{
      ring_nf at hn
      have hdiv :(n^2 ∣ i) := by {
        calc n^2  ∣ i /j := by apply dvd_of_eq hn
        _  ∣ i := by {
          exact div_dvd_of_dvd hj2
        }
      }
      have hdist:(n≠1) := by{
        rw[← hn] at h2
        by_contra hc
        rw[hc] at h2
        contradiction
      }
      rw [Nat.squarefree_iff_prime_squarefree]
      push_neg
      have hp : ∃ p, Nat.Prime p ∧ p ∣ n := by exact Nat.exists_prime_and_dvd hdist
      obtain ⟨p, hp⟩ := hp
      obtain ⟨hp1, hp2⟩ := hp
      use p
      constructor
      · exact hp1
      · ring_nf
        calc p^2 ∣ n^2 := by exact pow_dvd_pow_of_dvd hp2 2
        _ ∣ i := by exact hdiv
  }
  exact Decidable.not_or_of_imp fun a a_1 ↦ h a
  exact h1
  calc i ≥ i/j := by exact Nat.div_le_self i j
  _ > 1 := by exact h2

}
 lemma divsmall (i j:ℕ):Nat.Prime j∧ ¬ Nat.Prime i∧ i >1∧ j^2 ∣ i →  ¬ isCarmichael i := by {
  intro hi
  obtain ⟨h, h2, h3, hi⟩ := hi
  rw[Korselt]
  rw [not_and_or]
  have h: ¬ Squarefree i := by {
     rw [Nat.squarefree_iff_prime_squarefree]
     push_neg
     use j
     constructor
     · exact h
     · ring_nf;exact hi
  }
  exact Decidable.not_or_of_imp fun a a_1 ↦ h a
  exact h2
  exact h3
 }

lemma ncarm0and1 (i :ℕ ) (h: i < 2): ¬ isCarmichael i := by{
  rw[isCarmichael]
  push_neg
  intro hi hj
  exact le_of_lt_succ h
}

lemma LowestCarmichael :∀ (i :ℕ ), i < 100→ ¬ isCarmichael i:= by {
  intro i hi
  have h_0: i < 2 → ¬ isCarmichael i := by intro haux; exact ncarm0and1 i haux
  have h_1: Nat.Prime i → ¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrime i a
  have h_3 : i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 3 ∧ 3∣ i ∧ ¬ (3-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 3 i a
  have h_5: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 5 ∧ 5∣ i ∧ ¬ (5-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 5 i a
  have h_7: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 7 ∧ 7∣ i ∧ ¬ (7-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 7 i a
  have h_11: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 11 ∧ 11∣ i ∧ ¬ (11-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 11 i a
  have h_13: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 13 ∧ 13∣ i ∧ ¬ (13-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 13 i a
  have h_17: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 17 ∧ 17∣ i ∧ ¬ (17-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 17 i a
  have h_19: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 19 ∧ 19∣ i ∧ ¬ (19-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 19 i a
  have h_23: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 23 ∧ 23∣ i ∧ ¬ (23-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 23 i a
  have h_29: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 29 ∧ 29∣ i ∧ ¬ (29-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 29 i a
  have h_31: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 31 ∧ 31∣ i ∧ ¬ (31-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 31 i a
  have h_37: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 37 ∧ 37∣ i ∧ ¬ (37-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 37 i a
  have h_41: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 41 ∧ 41∣ i ∧ ¬ (41-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 41 i a
  have h_43: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 43 ∧ 43∣ i ∧ ¬ (43-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 43 i a
  have h_47: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 47 ∧ 47∣ i ∧ ¬ (47-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 47 i a

  have h_sq :1>0 ∧ 1∣i ∧ ¬Nat.Prime i ∧ i/1>1 ∧  (Nat.sqrt (i/1)) * (Nat.sqrt (i/1)) = i/1→ ¬ isCarmichael i := by exact fun a ↦ sqdiv2 i 1 a
  have h_s4: Nat.Prime 2∧ ¬ Nat.Prime i∧ i >1∧ 2^2 ∣ i →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 2 a
  have h_s9: Nat.Prime 3∧ ¬ Nat.Prime i∧ i >1∧ 3^2 ∣ i →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 3 a
  have h_s25 : Nat.Prime 5∧ ¬ Nat.Prime i∧ i >1∧ 5^2 ∣ i  →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 5 a
  have h_sq_3 : 3>0 ∧ 3∣i ∧ ¬Nat.Prime i ∧ i/3>1 ∧ (Nat.sqrt (i/3)) * (Nat.sqrt (i/3)) = (i/3)→ ¬ isCarmichael i := by  exact fun a ↦ sqdiv2 i 3 a
  have h_sq_5: 5>0 ∧ 5∣i ∧ ¬Nat.Prime i ∧ i/5>1∧ (Nat.sqrt (i/5)) * (Nat.sqrt (i/5)) = (i/5)→ ¬ isCarmichael i := by  exact fun a ↦ sqdiv2 i 5 a
  have h_sq_7: 7>0 ∧ 7∣i ∧ ¬Nat.Prime i ∧ i/7>1 ∧ (Nat.sqrt (i/7)) * (Nat.sqrt (i/7)) = (i/7)→ ¬ isCarmichael i := by exact fun a ↦ sqdiv2 i 7 a
  interval_cases i

  all_goals try {apply h_0; norm_num; done}
  all_goals try {apply h_sq; norm_num; done}
  all_goals try {apply h_sq_3; norm_num; done}
  all_goals try {apply h_sq_5; norm_num; done}
  all_goals try {apply h_sq_7; norm_num; done}
  all_goals try {apply h_s4; norm_num; done}
  all_goals try {apply h_s9; norm_num; done}
  all_goals try {apply h_s25; norm_num; done}
  all_goals try {apply h_1; norm_num; done}

  all_goals try {apply h_3; norm_num; done}
  all_goals try {apply h_5; norm_num; done}
  all_goals try {apply h_7; norm_num; done}
  all_goals try {apply h_11; norm_num; done}
  all_goals try {apply h_13; norm_num; done}
  all_goals try {apply h_17; norm_num; done}
  all_goals try {apply h_19; norm_num; done}
  all_goals try {apply h_23; norm_num; done}
  all_goals try {apply h_29; norm_num; done}
  all_goals try {apply h_31; norm_num; done}
  all_goals try {apply h_37; norm_num; done}
  all_goals try {apply h_41; norm_num; done}
  all_goals try {apply h_43; norm_num; done}
  all_goals try {apply h_47; norm_num; }

}


lemma LowestCarmichael2 :∀ (i :ℕ ), i ≥ 100 ∧ i<200 →¬ isCarmichael i:= by {
  intro i hi
  have h_0: i < 2 → ¬ isCarmichael i := by intro haux; exact ncarm0and1 i haux
  have h_1: Nat.Prime i → ¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrime i a
  have h_3 : i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 3 ∧ 3∣ i ∧ ¬ (3-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 3 i a
  have h_5: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 5 ∧ 5∣ i ∧ ¬ (5-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 5 i a
  have h_7: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 7 ∧ 7∣ i ∧ ¬ (7-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 7 i a
  have h_11: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 11 ∧ 11∣ i ∧ ¬ (11-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 11 i a
  have h_13: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 13 ∧ 13∣ i ∧ ¬ (13-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 13 i a
  have h_17: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 17 ∧ 17∣ i ∧ ¬ (17-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 17 i a
  have h_19: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 19 ∧ 19∣ i ∧ ¬ (19-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 19 i a
  have h_23: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 23 ∧ 23∣ i ∧ ¬ (23-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 23 i a
  have h_29: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 29 ∧ 29∣ i ∧ ¬ (29-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 29 i a
  have h_31: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 31 ∧ 31∣ i ∧ ¬ (31-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 31 i a
  have h_37: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 37 ∧ 37∣ i ∧ ¬ (37-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 37 i a
  have h_41: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 41 ∧ 41∣ i ∧ ¬ (41-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 41 i a
  have h_43: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 43 ∧ 43∣ i ∧ ¬ (43-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 43 i a
  have h_47: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 47 ∧ 47∣ i ∧ ¬ (47-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 47 i a
  have h_53: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 53 ∧ 53∣ i ∧ ¬ (53-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 53 i a
  have h_59: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 59 ∧ 59∣ i ∧ ¬ (59-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 59 i a
  have h_61: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 61 ∧ 61∣ i ∧ ¬ (61-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 61 i a
  have h_67: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 67 ∧ 67∣ i ∧ ¬ (67-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 67 i a
  have h_71: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 71 ∧ 71∣ i ∧ ¬ (71-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 71 i a
  have h_73: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 73 ∧ 73∣ i ∧ ¬ (73-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 73 i a
  have h_79: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 79 ∧ 79∣ i ∧ ¬ (79-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 79 i a
  have h_83: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 83 ∧ 83∣ i ∧ ¬ (83-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 83 i a
  have h_89: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 89 ∧ 89∣ i ∧ ¬ (89-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 89 i a
  have h_97: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 97 ∧ 97∣ i ∧ ¬ (97-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 97 i a
  have h_sq :1>0 ∧ 1∣i ∧ ¬Nat.Prime i ∧ i/1>1 ∧  (Nat.sqrt (i/1)) * (Nat.sqrt (i/1)) = i/1→ ¬ isCarmichael i := by exact fun a ↦ sqdiv2 i 1 a
  have h_s4: Nat.Prime 2∧ ¬ Nat.Prime i∧ i >1∧ 2^2 ∣ i →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 2 a
  have h_s9: Nat.Prime 3∧ ¬ Nat.Prime i∧ i >1∧ 3^2 ∣ i →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 3 a
  have h_s25 : Nat.Prime 5∧ ¬ Nat.Prime i∧ i >1∧ 5^2 ∣ i  →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 5 a
  have h_sq_3 : 3>0 ∧ 3∣i ∧ ¬Nat.Prime i ∧ i/3>1 ∧ (Nat.sqrt (i/3)) * (Nat.sqrt (i/3)) = (i/3)→ ¬ isCarmichael i := by  exact fun a ↦ sqdiv2 i 3 a
  have h_sq_5: 5>0 ∧ 5∣i ∧ ¬Nat.Prime i ∧ i/5>1∧ (Nat.sqrt (i/5)) * (Nat.sqrt (i/5)) = (i/5)→ ¬ isCarmichael i := by  exact fun a ↦ sqdiv2 i 5 a
  have h_sq_7: 7>0 ∧ 7∣i ∧ ¬Nat.Prime i ∧ i/7>1 ∧ (Nat.sqrt (i/7)) * (Nat.sqrt (i/7)) = (i/7)→ ¬ isCarmichael i := by exact fun a ↦ sqdiv2 i 7 a
  obtain ⟨left, right⟩ := hi
  interval_cases i
  all_goals try {apply h_sq; norm_num; done}
  all_goals try {apply h_sq_3; norm_num; done}
  all_goals try {apply h_sq_5; norm_num; done}
  all_goals try {apply h_sq_7; norm_num; done}
  all_goals try {apply h_s4; norm_num; done}
  all_goals try {apply h_s9; norm_num; done}
  all_goals try {apply h_s25; norm_num; done}
  all_goals try {apply h_1; norm_num; done}
  all_goals try {apply h_3; norm_num; done}
  all_goals try {apply h_5; norm_num; done}
  all_goals try {apply h_7; norm_num; done}
  all_goals try {apply h_11; norm_num; done}
  all_goals try {apply h_19; norm_num; done}
  all_goals try {apply h_29; norm_num; done}
  all_goals try {apply h_37; norm_num; done}
  all_goals try {apply h_41; norm_num; done}
  all_goals try {apply h_43; norm_num; done}
  all_goals try {apply h_47; norm_num; done}
  all_goals try {apply h_53; norm_num; done}
  all_goals try {apply h_59; norm_num; done}
  all_goals try {apply h_61; norm_num; done}
  all_goals try {apply h_67; norm_num; done}
  all_goals try {apply h_71; norm_num; done}
  all_goals try {apply h_73; norm_num; done}
  all_goals try {apply h_79; norm_num; done}
  all_goals try {apply h_83; norm_num; done}
  all_goals try {apply h_89; norm_num; done}
  all_goals try {apply h_97; norm_num; }
}
lemma LowestCarmichael3 :∀ (i :ℕ ), i ≥ 200∧  i < 300→ ¬ isCarmichael i:= by {
  intro i hi
  have h_0: i < 2 → ¬ isCarmichael i := by intro haux; exact ncarm0and1 i haux
  have h_1: Nat.Prime i → ¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrime i a
  have h_3 : i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 3 ∧ 3∣ i ∧ ¬ (3-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 3 i a
  have h_5: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 5 ∧ 5∣ i ∧ ¬ (5-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 5 i a
  have h_7: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 7 ∧ 7∣ i ∧ ¬ (7-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 7 i a
  have h_11: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 11 ∧ 11∣ i ∧ ¬ (11-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 11 i a
  have h_13: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 13 ∧ 13∣ i ∧ ¬ (13-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 13 i a
  have h_17: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 17 ∧ 17∣ i ∧ ¬ (17-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 17 i a
  have h_19: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 19 ∧ 19∣ i ∧ ¬ (19-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 19 i a
  have h_23: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 23 ∧ 23∣ i ∧ ¬ (23-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 23 i a
  have h_29: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 29 ∧ 29∣ i ∧ ¬ (29-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 29 i a
  have h_31: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 31 ∧ 31∣ i ∧ ¬ (31-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 31 i a
  have h_37: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 37 ∧ 37∣ i ∧ ¬ (37-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 37 i a
  have h_41: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 41 ∧ 41∣ i ∧ ¬ (41-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 41 i a
  have h_43: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 43 ∧ 43∣ i ∧ ¬ (43-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 43 i a
  have h_47: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 47 ∧ 47∣ i ∧ ¬ (47-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 47 i a
  have h_53: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 53 ∧ 53∣ i ∧ ¬ (53-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 53 i a
  have h_59: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 59 ∧ 59∣ i ∧ ¬ (59-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 59 i a
  have h_61: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 61 ∧ 61∣ i ∧ ¬ (61-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 61 i a
  have h_67: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 67 ∧ 67∣ i ∧ ¬ (67-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 67 i a
  have h_71: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 71 ∧ 71∣ i ∧ ¬ (71-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 71 i a
  have h_73: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 73 ∧ 73∣ i ∧ ¬ (73-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 73 i a
  have h_79: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 79 ∧ 79∣ i ∧ ¬ (79-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 79 i a
  have h_83: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 83 ∧ 83∣ i ∧ ¬ (83-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 83 i a
  have h_89: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 89 ∧ 89∣ i ∧ ¬ (89-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 89 i a
  have h_97: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 97 ∧ 97∣ i ∧ ¬ (97-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 97 i a
  have h_101: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 101 ∧ 101∣ i ∧ ¬ (101-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 101 i a
  have h_103: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 103 ∧ 103∣ i ∧ ¬ (103-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 103 i a
  have h_107: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 107 ∧ 107∣ i ∧ ¬ (107-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 107 i a
  have h_109: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 109 ∧ 109∣ i ∧ ¬ (109-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 109 i a
  have h_113: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 113 ∧ 113∣ i ∧ ¬ (113-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 113 i a
  have h_127: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 127 ∧ 127∣ i ∧ ¬ (127-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 127 i a
  have h_131: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 131 ∧ 131∣ i ∧ ¬ (131-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 131 i a
  have h_137: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 137 ∧ 137∣ i ∧ ¬ (137-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 137 i a
  have h_139: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 139 ∧ 139∣ i ∧ ¬ (139-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 139 i a
  have h_149: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 149 ∧ 149∣ i ∧ ¬ (149-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 149 i a


  have h_sq :1>0 ∧ 1∣i ∧ ¬Nat.Prime i ∧ i/1>1 ∧  (Nat.sqrt (i/1)) * (Nat.sqrt (i/1)) = i/1→ ¬ isCarmichael i := by exact fun a ↦ sqdiv2 i 1 a
  have h_s4: Nat.Prime 2∧ ¬ Nat.Prime i∧ i >1∧ 2^2 ∣ i →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 2 a
  have h_s9: Nat.Prime 3∧ ¬ Nat.Prime i∧ i >1∧ 3^2 ∣ i →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 3 a
  have h_s25 : Nat.Prime 5∧ ¬ Nat.Prime i∧ i >1∧ 5^2 ∣ i  →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 5 a
  have h_sq_3 : 3>0 ∧ 3∣i ∧ ¬Nat.Prime i ∧ i/3>1 ∧ (Nat.sqrt (i/3)) * (Nat.sqrt (i/3)) = (i/3)→ ¬ isCarmichael i := by  exact fun a ↦ sqdiv2 i 3 a
  have h_sq_5: 5>0 ∧ 5∣i ∧ ¬Nat.Prime i ∧ i/5>1∧ (Nat.sqrt (i/5)) * (Nat.sqrt (i/5)) = (i/5)→ ¬ isCarmichael i := by  exact fun a ↦ sqdiv2 i 5 a
  have h_sq_7: 7>0 ∧ 7∣i ∧ ¬Nat.Prime i ∧ i/7>1 ∧ (Nat.sqrt (i/7)) * (Nat.sqrt (i/7)) = (i/7)→ ¬ isCarmichael i := by exact fun a ↦ sqdiv2 i 7 a
  obtain ⟨left, right⟩ := hi
  interval_cases i
  all_goals try {apply h_sq; norm_num; done}
  all_goals try {apply h_sq_3; norm_num; done}
  all_goals try {apply h_sq_5; norm_num; done}
  all_goals try {apply h_sq_7; norm_num; done}
  all_goals try {apply h_s4; norm_num; done}
  all_goals try {apply h_s9; norm_num; done}
  all_goals try {apply h_s25; norm_num; done}
  all_goals try {apply h_1; norm_num; done}
  all_goals try {apply h_3; norm_num; done}
  all_goals try {apply h_5; norm_num; done}
  all_goals try {apply h_7; norm_num; done}
  all_goals try {apply h_11; norm_num; done}
  all_goals try {apply h_13; norm_num; done}
  all_goals try {apply h_19; norm_num; done}
  all_goals try {apply h_31; norm_num; done}
  all_goals try {apply h_37; norm_num; done}
  all_goals try {apply h_41; norm_num; done}
  all_goals try {apply h_53; norm_num; done}
  all_goals try {apply h_67; norm_num; done}
  all_goals try {apply h_71; norm_num; done}
  all_goals try {apply h_73; norm_num; done}
  all_goals try {apply h_79; norm_num; done}
  all_goals try {apply h_83; norm_num; done}
  all_goals try {apply h_89; norm_num; done}
  all_goals try {apply h_97; norm_num; done}
  all_goals try {apply h_101; norm_num; done}
  all_goals try {apply h_103; norm_num; done}
  all_goals try {apply h_107; norm_num; done}
  all_goals try {apply h_109; norm_num; done}
  all_goals try {apply h_113; norm_num; done}
  all_goals try {apply h_127; norm_num; done}
  all_goals try {apply h_131; norm_num; done}
  all_goals try {apply h_137; norm_num; done}
  all_goals try {apply h_139; norm_num; done}
  all_goals try {apply h_149; norm_num}
}


lemma LowestCarmichael4 :∀ (i :ℕ ), i ≥ 400∧  i < 500→ ¬ isCarmichael i:= by {
  intro i hi
  have h_0: i < 2 → ¬ isCarmichael i := by intro haux; exact ncarm0and1 i haux
  have h_1: Nat.Prime i → ¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrime i a
  have h_3 : i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 3 ∧ 3∣ i ∧ ¬ (3-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 3 i a
  have h_5: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 5 ∧ 5∣ i ∧ ¬ (5-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 5 i a
  have h_7: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 7 ∧ 7∣ i ∧ ¬ (7-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 7 i a
  have h_11: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 11 ∧ 11∣ i ∧ ¬ (11-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 11 i a
  have h_13: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 13 ∧ 13∣ i ∧ ¬ (13-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 13 i a
  have h_17: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 17 ∧ 17∣ i ∧ ¬ (17-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 17 i a
  have h_19: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 19 ∧ 19∣ i ∧ ¬ (19-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 19 i a
  have h_23: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 23 ∧ 23∣ i ∧ ¬ (23-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 23 i a
  have h_29: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 29 ∧ 29∣ i ∧ ¬ (29-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 29 i a
  have h_31: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 31 ∧ 31∣ i ∧ ¬ (31-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 31 i a
  have h_37: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 37 ∧ 37∣ i ∧ ¬ (37-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 37 i a
  have h_41: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 41 ∧ 41∣ i ∧ ¬ (41-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 41 i a
  have h_43: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 43 ∧ 43∣ i ∧ ¬ (43-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 43 i a
  have h_47: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 47 ∧ 47∣ i ∧ ¬ (47-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 47 i a
  have h_53: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 53 ∧ 53∣ i ∧ ¬ (53-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 53 i a
  have h_59: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 59 ∧ 59∣ i ∧ ¬ (59-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 59 i a
  have h_61: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 61 ∧ 61∣ i ∧ ¬ (61-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 61 i a
  have h_67: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 67 ∧ 67∣ i ∧ ¬ (67-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 67 i a
  have h_71: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 71 ∧ 71∣ i ∧ ¬ (71-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 71 i a
  have h_73: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 73 ∧ 73∣ i ∧ ¬ (73-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 73 i a
  have h_79: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 79 ∧ 79∣ i ∧ ¬ (79-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 79 i a
  have h_83: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 83 ∧ 83∣ i ∧ ¬ (83-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 83 i a
  have h_89: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 89 ∧ 89∣ i ∧ ¬ (89-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 89 i a
  have h_97: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 97 ∧ 97∣ i ∧ ¬ (97-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 97 i a
  have h_101: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 101 ∧ 101∣ i ∧ ¬ (101-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 101 i a
  have h_103: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 103 ∧ 103∣ i ∧ ¬ (103-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 103 i a
  have h_107: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 107 ∧ 107∣ i ∧ ¬ (107-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 107 i a
  have h_109: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 109 ∧ 109∣ i ∧ ¬ (109-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 109 i a
  have h_113: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 113 ∧ 113∣ i ∧ ¬ (113-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 113 i a
  have h_127: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 127 ∧ 127∣ i ∧ ¬ (127-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 127 i a
  have h_131: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 131 ∧ 131∣ i ∧ ¬ (131-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 131 i a
  have h_137: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 137 ∧ 137∣ i ∧ ¬ (137-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 137 i a
  have h_139: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 139 ∧ 139∣ i ∧ ¬ (139-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 139 i a
  have h_149: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 149 ∧ 149∣ i ∧ ¬ (149-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 149 i a
  have h_151: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 151 ∧ 151∣ i ∧ ¬ (151-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 151 i a
  have h_157: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 157 ∧ 157∣ i ∧ ¬ (157-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 157 i a
  have h_163: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 163 ∧ 162∣ i ∧ ¬ (163-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 163 i a
  have h_167: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 167 ∧ 167∣ i ∧ ¬ (167-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 167 i a
  have h_173: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 173 ∧ 173∣ i ∧ ¬ (173-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 173 i a
  have h_179: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 179 ∧ 179∣ i ∧ ¬ (179-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 179 i a
  have h_181: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 181 ∧ 181∣ i ∧ ¬ (181-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 181 i a
  have h_191: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 191 ∧ 191∣ i ∧ ¬ (191-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 191 i a
  have h_193: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 193 ∧ 193∣ i ∧ ¬ (193-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 193 i a
  have h_197: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 197 ∧ 197∣ i ∧ ¬ (197-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 197 i a
  have h_199: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 199 ∧ 199 ∣ i ∧ ¬ (199 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
  by exact fun a ↦ NotCarmichaelPrimeDiv 199 i a
  have h_211: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 211 ∧ 211 ∣ i ∧ ¬ (211 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 211 i a

  have h_223: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 223 ∧ 223 ∣ i ∧ ¬ (223 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 223 i a

  have h_227: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 227 ∧ 227 ∣ i ∧ ¬ (227 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 227 i a

  have h_229: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 229 ∧ 229 ∣ i ∧ ¬ (229 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 229 i a

  have h_233: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 233 ∧ 233 ∣ i ∧ ¬ (233 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 233 i a

  have h_239: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 239 ∧ 239 ∣ i ∧ ¬ (239 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 239 i a

  have h_241: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 241 ∧ 241 ∣ i ∧ ¬ (241 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 241 i a

  have h_251: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 251 ∧ 251 ∣ i ∧ ¬ (251 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 251 i a

  have h_257: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 257 ∧ 257 ∣ i ∧ ¬ (257 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 257 i a

  have h_263: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 263 ∧ 263 ∣ i ∧ ¬ (263 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 263 i a

  have h_269: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 269 ∧ 269 ∣ i ∧ ¬ (269 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 269 i a

  have h_271: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 271 ∧ 271 ∣ i ∧ ¬ (271 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 271 i a

  have h_277: i > 1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 277 ∧ 277 ∣ i ∧ ¬ (277 - 1) ∣ (i - 1:ℤ) → ¬ isCarmichael i :=
    by exact fun a ↦ NotCarmichaelPrimeDiv 277 i a




  have h_sq :1>0 ∧ 1∣i ∧ ¬Nat.Prime i ∧ i/1>1 ∧  (Nat.sqrt (i/1)) * (Nat.sqrt (i/1)) = i/1→ ¬ isCarmichael i := by exact fun a ↦ sqdiv2 i 1 a
  have h_s4: Nat.Prime 2∧ ¬ Nat.Prime i∧ i >1∧ 2^2 ∣ i →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 2 a
  have h_s9: Nat.Prime 3∧ ¬ Nat.Prime i∧ i >1∧ 3^2 ∣ i →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 3 a
  have h_s25 : Nat.Prime 5∧ ¬ Nat.Prime i∧ i >1∧ 5^2 ∣ i  →  ¬ isCarmichael i := by exact fun a ↦ divsmall i 5 a
  have h_sq_3 : 3>0 ∧ 3∣i ∧ ¬Nat.Prime i ∧ i/3>1 ∧ (Nat.sqrt (i/3)) * (Nat.sqrt (i/3)) = (i/3)→ ¬ isCarmichael i := by  exact fun a ↦ sqdiv2 i 3 a
  have h_sq_5: 5>0 ∧ 5∣i ∧ ¬Nat.Prime i ∧ i/5>1∧ (Nat.sqrt (i/5)) * (Nat.sqrt (i/5)) = (i/5)→ ¬ isCarmichael i := by  exact fun a ↦ sqdiv2 i 5 a
  have h_sq_7: 7>0 ∧ 7∣i ∧ ¬Nat.Prime i ∧ i/7>1 ∧ (Nat.sqrt (i/7)) * (Nat.sqrt (i/7)) = (i/7)→ ¬ isCarmichael i := by exact fun a ↦ sqdiv2 i 7 a
  obtain ⟨left, right⟩ := hi
  interval_cases i
  all_goals try {apply h_sq; norm_num; done}
  all_goals try {apply h_sq_3; norm_num; done}
  all_goals try {apply h_sq_5; norm_num; done}
  all_goals try {apply h_sq_7; norm_num; done}
  all_goals try {apply h_s4; norm_num; done}
  all_goals try {apply h_s9; norm_num; done}
  all_goals try {apply h_s25; norm_num; done}
  all_goals try {apply h_1; norm_num; done}
  all_goals try {apply h_3; norm_num; done}
  all_goals try {apply h_5; norm_num; done}
  all_goals try {apply h_7; norm_num; done}
  all_goals try {apply h_11; norm_num; done}
  all_goals try {apply h_13; norm_num; done}
  all_goals try {apply h_17; norm_num; done}
  all_goals try {apply h_19; norm_num; done}
  all_goals try {apply h_23; norm_num; done}
  all_goals try {apply h_29; norm_num; done}
  all_goals try {apply h_31; norm_num; done}
  all_goals try {apply h_37; norm_num; done}
  all_goals try {apply h_41; norm_num; done}
  all_goals try {apply h_43; norm_num; done}
  all_goals try {apply h_47; norm_num; done}
  all_goals try {apply h_53; norm_num; done}
  all_goals try {apply h_59; norm_num; done}
  all_goals try {apply h_61; norm_num; done}
  all_goals try {apply h_67; norm_num; done}
  all_goals try {apply h_71; norm_num; done}
  all_goals try {apply h_73; norm_num; done}
  all_goals try {apply h_79; norm_num; done}
  all_goals try {apply h_83; norm_num; done}
  all_goals try {apply h_89; norm_num; done}
  all_goals try {apply h_97; norm_num; done}
  all_goals try {apply h_101; norm_num; done}
  all_goals try {apply h_103; norm_num; done}
  all_goals try {apply h_107; norm_num; done}
  all_goals try {apply h_109; norm_num; done}
  all_goals try {apply h_113; norm_num; done}
  all_goals try {apply h_127; norm_num; done}
  all_goals try {apply h_131; norm_num; done}
  all_goals try {apply h_137; norm_num; done}
  all_goals try {apply h_139; norm_num; done}
  all_goals try {apply h_149; norm_num; done}
  all_goals try {apply h_151; norm_num; done}
  all_goals try {apply h_157; norm_num; done}
  all_goals try {apply h_163; norm_num; done}
  all_goals try {apply h_167; norm_num; done}
  all_goals try {apply h_173; norm_num; done}
  all_goals try {apply h_179; norm_num; done}
  all_goals try {apply h_181; norm_num; done}
  all_goals try {apply h_191; norm_num; done}
  all_goals try {apply h_193; norm_num; done}
  all_goals try {apply h_197; norm_num; done}
  all_goals try {apply h_199; norm_num; done}
  all_goals try {apply h_199; norm_num; done}
  all_goals try {apply h_211; norm_num; done}
  all_goals try {apply h_223; norm_num; done}
  all_goals try {apply h_227; norm_num; done}
  all_goals try {apply h_229; norm_num; done}
  all_goals try {apply h_233; norm_num; done}
  all_goals try {apply h_239; norm_num; done}
  all_goals try {apply h_241; norm_num; done}
  all_goals try {apply h_251; norm_num; done}
  all_goals try {apply h_257; norm_num; done}
  all_goals try {apply h_263; norm_num; done}
  all_goals try {apply h_269; norm_num; done}
  all_goals try {apply h_271; norm_num; done}
  all_goals try {apply h_277; norm_num; done}
}
