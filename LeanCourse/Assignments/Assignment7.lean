import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Nat.Choose.Dvd
noncomputable section
open Function Ideal Polynomial Classical
open scoped Matrix
-- This is removed intentionally and should not be used manually in the exercises
attribute [-ext] LinearMap.prod_ext
-- Pablo cageao and Sergio Hernando

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 8.2 and 9.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 26.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice.
Feel free to skip these exercises-/

example (n m : ℤ) : span {n} ⊔ span {m} = span {gcd n m} := by {
  rw [@span_gcd]
  exact Eq.symm (span_insert n {m})
  }

example (n m : ℤ) : span {n} ⊓ span {m} = span {lcm n m} := by {
  ext x
  constructor
  · intro h
    have h1 := h.1
    have h3 : n ∣ x := by exact mem_span_singleton.mp h1
    have h1 := h.2
    have h2 : m ∣ x := by exact mem_span_singleton.mp h1
    have h1 : (lcm n m) ∣ x := by exact lcm_dvd h3 h2
    rw [@mem_span_singleton]
    exact h1
  · intro h
    constructor
    all_goals rw [@SetLike.mem_coe]
    all_goals rw [@mem_span_singleton]
    all_goals have h1 : lcm n m ∣ x := by exact mem_span_singleton.mp h
    have h: n ∣ x := by{
      calc n ∣ lcm n m := by exact dvd_lcm_left n m
    _ ∣ x := by exact h1
    }
    exact h
    calc m ∣ lcm n m := by exact dvd_lcm_right n m
    _ ∣ x := by exact h1
  }
#leansearch "span gcd."
/- Show that transposing a matrix gives rise to a linear equivalence. -/
example {R M m n : Type*} [Ring R] [AddCommGroup M] [Module R M] :
  Matrix m n M ≃ₗ[R] Matrix n m M where
    toFun := fun M ↦ Mᵀ
    map_add' := by {
      simp
    }
    map_smul' := by {
      simp
    }
    invFun := by {
      exact fun a a_1 a_2 ↦ a a_2 a_1
    }
    left_inv := by {
      exact congrFun rfl
    }
    right_inv := by {
      exact congrFun rfl
    }

/- A ring has characteristic `p` if `1 + ⋯ + 1 = 0`, where we add `1` `p` times to itself.
This is written `CharP` in Lean.
In a module over a ring with characteristic 2, for every element `m` we have `m + m = 0`. -/
example {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [h :CharP R 2] (m : M) :
    m + m = 0 := by {
      sorry
  }

section Frobenius
variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p]
/- Let's define the Frobenius morphism `x ↦ x ^ p`.
You can use lemmas from the library.
We state that `p` is prime using `Fact p.Prime`.
This allows type-class inference to see that this is true.
You can access the fact that `p` is prime using `hp.out`. -/

def frobeniusMorphism (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [CharP R p] :
  R →+* R :=  RingHom.id R


@[simp] lemma frobeniusMorphism_def (x : R) : frobeniusMorphism p R x = x ^ p := by {
  unfold frobeniusMorphism
  sorry
}

/- Prove the following equality for iterating the frobenius morphism. -/
lemma iterate_frobeniusMorphism (n : ℕ) (x : R) : (frobeniusMorphism p R)^[n] x = x ^ p ^ n := by {
  sorry
  }

/- Show that the Frobenius morphism is injective on a domain. -/
lemma frobeniusMorphism_injective [IsDomain R] :
    Function.Injective (frobeniusMorphism p R) := by {
  sorry
  }

/- Show that the Frobenius morphism is bijective on a finite domain. -/
lemma frobeniusMorphism_bijective [IsDomain R] [Finite R] :
    Function.Bijective (frobeniusMorphism p R) := by {
  sorry
  }

example [IsDomain R] [Finite R] (k : ℕ) (x : R) : x ^ p ^ k = 1 ↔ x = 1 := by {
  sorry
  }

example {R : Type*} [CommRing R] [IsDomain R] [Finite R] [CharP R 2] (x : R) : IsSquare x := by {
  sorry
  }

end Frobenius


section Ring
variable {R : Type*} [CommRing R]


/- Let's define ourselves what it means to be a unit in a ring and then
prove that the units of a ring form a group.
Hint: I recommend that you first prove that the product of two units is again a unit,
and that you define the inverse of a unit separately using `Exists.choose`.
Hint 2: to prove associativity, use something like `intros; ext; apply mul_assoc`
(`rw` doesn't work well because of the casts) -/

#check Exists.choose
#check Exists.choose_spec
def IsAUnit (x : R) : Prop := ∃ y, y * x = 1

def IsAUnit.mul {x y : R} (hx : IsAUnit x) (hy : IsAUnit y) : IsAUnit (x * y) := by {
  sorry
  }

instance groupUnits : Group {x : R // IsAUnit x} := sorry

-- you have the correct group structure if this is true by `rfl`
example (x y : {x : R // IsAUnit x}) : (↑(x * y) : R) = ↑x * ↑y := by sorry

end Ring

/- Let's prove that if `M →ₗ[R] M` forms a module over `R`, then `R` must be a commutative ring.
To prove this we have to additionally assume that `M` contains at least two elements, and
`smul_eq_zero : r • x = 0 ↔ r = 0 ∨ x = 0` (this is given by the `NoZeroSMulDivisors` class).-/
#check exists_ne
lemma commutative_of_module {R M M' : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M]
    [NoZeroSMulDivisors R M] [Module R (M →ₗ[R] M)]
    (h : ∀ (r : R) (f : M →ₗ[R] M) (x : M), (r • f) x = r • f x)
    (r s : R) : r * s = s * r := by {
  sorry
  }


/-! # Exercises to hand-in. -/

/- The Frobenius morphism in a domain of characteristic `p` is the map `x ↦ x ^ p`.
Let's prove that the Frobenius morphism is additive, without using that
fact from the library. A proof sketch is given, and the following results will be useful. -/

#check add_pow
#check CharP.cast_eq_zero_iff

variable (p : ℕ) [hp : Fact p.Prime] (R : Type*) [CommRing R] [hchar :CharP R p] in
open Nat Finset in
lemma add_pow_eq_pow_add_pow (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by {
  have hp' : p.Prime := hp.out
  have range_eq_insert_Ioo : range p = insert 0 (Ioo 0 p)
  · rw [@insert_eq]
    ext k
    have hk1 : p > 0 := by exact pos_of_neZero p
    constructor
    · intro hk
      simp at *
      have hk1 : p > 0 := by exact pos_of_neZero p
      rw [@or_and_left]
      constructor
      · exact Nat.eq_zero_or_pos k
      · exact Or.symm (Or.intro_left (k = 0) hk)
    · intro hk
      simp at *
      cases' hk with hp hq
      · linarith
      · exact hq.2
  have dvd_choose : ∀ i ∈ Ioo 0 p, p ∣ Nat.choose p i := by {
    simp at *
    intro i hi hp
    refine Prime.dvd_choose hp' hp ?hab ?h
    simp
    constructor
    · linarith
    · exact hi
    exact Nat.le_refl p
  }

  have h6 : ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i = 0 :=
  calc
    _ =  ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * 0 := by {
      have hzero : ∀i ∈ Ioo 0 p, (p.choose i : R)= 0:= by  {
        intro j hj
        specialize dvd_choose j hj
        simp_all only [mem_Ioo]
        rw [charP_iff] at hchar
        specialize hchar (p.choose j)
        rw [@Iff.comm] at hchar
        simp_all only [iff_true]
      }
      exact sum_congr rfl fun x_1 a ↦ congrArg (HMul.hMul (x ^ x_1 * y ^ (p - x_1))) (hzero x_1 a)
    }
    _ = 0 := by {
      simp
    }

  have hfin : (x + y) ^ p = x ^ p + y ^ p  + ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i := by {
    calc (x + y) ^ p = ∑ i in range (p + 1), x ^ i * y ^ (p - i) * ↑(Nat.choose p i) := by exact add_pow x y p
    _ = ∑ i in range (p), x ^ i * y ^ (p - i) * ↑(Nat.choose p i) + x^p:= by rw [Finset.sum_range_succ];simp
    _= x^p + ∑ i in range (p), x ^ i * y ^ (p - i) * ↑(Nat.choose p i) := by exact Eq.symm (AddCommMagma.add_comm (x ^ p) (∑ m ∈ range p, x ^ m * y ^ (p - m) * ↑(p.choose m)))
    _= x^p + ∑ i in range (p), x ^ i * y ^ (p - i) * (Nat.choose p i) := by norm_cast
    _= x^p + y^p + ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * (Nat.choose p i) := by {
      simp_all only [mem_Ioo, and_imp, lt_self_iff_false, false_and, not_false_eq_true, sum_insert, pow_zero, tsub_zero,
        one_mul, choose_zero_right, cast_one, mul_one, add_zero]
    }
  }
  calc (x + y) ^ p = x ^ p + y ^ p  + ∑ i in Ioo 0 p, x ^ i * y ^ (p - i) * Nat.choose p i := by exact hfin
  _ = x ^ p + y ^ p + 0 := by norm_cast; rw[h6]
  _ = x ^ p + y ^ p := by ring

}

section LinearMap

variable {R M₁ M₂ N M' : Type*} [CommRing R]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N] [AddCommGroup M']
  [Module R M₁] [Module R M₂] [Module R N] [Module R M']

/- Define the coproduct of two linear maps, and prove the characterization below.
Note that this proof works exactly the same for vector spaces over a field as it works
for modules over a ring, so feel free to think of `M₁`, `M₂`, `N` and `M'` as vector spaces.
You might recognize this as the characterization of a *coproduct* in category theory. -/

def coproduct (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) : M₁ × M₂ →ₗ[R] N where
  toFun x := f x.1 + g x.2
  map_add' x y := by{
    simp only [Prod.fst_add, map_add, Prod.snd_add]
    exact add_add_add_comm (f x.1) (f y.1) (g x.2) (g y.2)
    }
  map_smul' r x := by{
    simp only [Prod.smul_fst, map_smul, Prod.smul_snd, RingHom.id_apply, smul_add]
  }

-- this can be useful to have as a simp-lemma, and should be proven by `rfl`
@[simp] lemma coproduct_def (f : M₁ →ₗ[R] N) (g : M₂ →ₗ[R] N) (x : M₁) (y : M₂) :
  coproduct f g (x, y) = f x + g y  := rfl

lemma coproduct_unique {f : M₁ →ₗ[R] N} {g : M₂ →ₗ[R] N} {l : M₁ × M₂ →ₗ[R] N} :
    l = coproduct f g ↔
    l.comp (LinearMap.inl R M₁ M₂) = f ∧
    l.comp (LinearMap.inr R M₁ M₂) = g := by {
  constructor
  · intro h
    rw [h]
    constructor
    · ext x
      simp only [LinearMap.coe_comp, LinearMap.coe_inl, comp_apply, coproduct_def, map_zero,
        add_zero]
    · ext x
      simp only [LinearMap.coe_comp, LinearMap.coe_inr, comp_apply, coproduct_def, map_zero,
        zero_add]
  · intro h
    ext ⟨x, y⟩
    obtain ⟨h₁, h₂⟩ := h
    have : l (x, y) = l (x, 0) + l (0, y) := by
      rw [←l.map_add]
      simp
    rw[this]
    subst h₁ h₂
    simp_all only [coproduct_def, LinearMap.coe_comp, LinearMap.coe_inl, comp_apply, LinearMap.coe_inr]
  }


end LinearMap
