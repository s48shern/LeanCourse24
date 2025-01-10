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

lemma LowestCarmichael :∀ (i :ℕ ), i < 561 → ¬ isCarmichael i:= by {
  intro i hi
  have h_2: Nat.Prime i → ¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrime i a
  have h_3 : i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 2∧ 2∣ i ∧ ¬ (2-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 2 i a
  have h_4 : i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 3 ∧ 3∣ i ∧ ¬ (3-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 3 i a
  have h_5: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 5 ∧ 5∣ i ∧ ¬ (5-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 5 i a
  have h_7: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 7 ∧ 7∣ i ∧ ¬ (7-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 7 i a
  have h_11: i >1 ∧ ¬ Nat.Prime i ∧ Nat.Prime 11 ∧ 11∣ i ∧ ¬ (11-1) ∣ (i-1:ℤ)→¬ isCarmichael i := by exact fun a ↦ NotCarmichaelPrimeDiv 11 i a

  have h_sq : (Nat.sqrt i) * (Nat.sqrt i) = i → ¬ isCarmichael i := by sorry
  have h_s9: 9 ∣ i →  ¬ isCarmichael i := by sorry
  have h_s25 : 25 ∣ i →  ¬ isCarmichael i := by sorry
  have h_sq_3 : (Nat.sqrt (i/3)) * (Nat.sqrt (i/3)) = (i/3)→ ¬ isCarmichael i := by sorry
  have h_sq_5: (Nat.sqrt (i/5)) * (Nat.sqrt (i/5)) = (i/5)→ ¬ isCarmichael i := by sorry
  have h_sq_7: (Nat.sqrt (i/7)) * (Nat.sqrt (i/7)) = (i/7)→ ¬ isCarmichael i := by sorry
  interval_cases i
  all_goals try {apply h_sq; norm_num; done}
  all_goals try {apply h_4; norm_num; done}
  all_goals sorry

}
