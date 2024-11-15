import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8.1.
  Chapter 7 explains some of the design decisions for classes in Mathlib.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 19.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


/- Prove the following exercises about functions where the domain/codomain are
subtypes. -/

abbrev PosReal : Type := {x : ℝ // x > 0}
variable (a : Real) (p : Real → PosReal) (s : {a : Real // a > 0 })
/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by {
    intro x y hx
    simp
    have h2: ↑(f x) ≤ ↑(f y) := by exact hf hx
  }

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : range f ⊆ {x | x > 0}) (h2f : Monotone f) :
  Monotone (log ∘ f) := by {
  intro x y hx
  simp only [comp_apply]
  have h2: f x ≤ f y := by exact h2f hx

  }

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by {
    intro x y hx
    simp
    apply hf
    simp_all only [Subtype.mk_le_mk, exp_le_exp]
    }

/- Only specify that a function is well-behaved on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by {
    intro x y hx
    simp
    apply hf
    all_goals simp
    exact exp_pos x
    exact exp_pos y
    exact hx
    }



variable {G H K : Type*} [Group G] [Group H] [Group K]
open Subgroup


/- State and prove that the preimage of `U` under the composition of `φ` and `ψ` is a preimage
of a preimage of `U`. This should be an equality of subgroups! -/
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) : sorry := sorry

/- State and prove that the image of `S` under the composition of `φ` and `ψ`
is a image of an image of `S`. -/
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) : sorry := sorry



/- Define the conjugate of a subgroup, as the elements of the form `xhx⁻¹` for `h ∈ H`. -/
def conjugate (x : G) (H : Subgroup G) : Subgroup G := sorry


/- Now let's prove that a group acts on its own subgroups by conjugation. -/

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by {
  sorry
  }

lemma conjugate_mul (x y : G) (H : Subgroup G) :
    conjugate (x * y) H = conjugate x (conjugate y H) := by {
  sorry
  }


/- Saying that a group `G` acts on a set `X` can be done with `MulAction`.
The two examples below show the two properties that a group action must satisfy. -/
#print MulAction

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
example (g g' : G) (x : X) : (g * g') • x = g • (g' • x) := by exact?
example (x : X) : (1 : G) • x = x := by exact?

/- Now show that `conjugate` specifies a group action from `G` onto its subgroups. -/
instance : MulAction G (Subgroup G) := sorry



/-! # Exercises to hand-in. -/


/- A `Setoid` is the name for an equivalence relation in Lean.
Let's define the smallest equivalence relation on a type `X`. -/
def myEquivalenceRelation (X : Type*) : Setoid X where
  r x y := x = y
  iseqv := {
    refl := by{
      exact fun x ↦ rfl
    }
    symm := by{
      exact fun {x y} a ↦ id (Eq.symm a)
    }
    trans := by{
      simp
    }
  } -- Here you have to show that this is an equivalence.
                 -- If you click on the `sorry`, a lightbulb will appear to give the fields

/- This simp-lemma will simplify `x ≈ y` to `x = y` in the lemma below. -/
@[simp] lemma equiv_iff_eq (X : Type*) (x y : X) :
  letI := myEquivalenceRelation X; x ≈ y ↔ x = y := by rfl

/-
Now let's prove that taking the quotient w.r.t. this equivalence relation is
equivalent to the original type.

Use `Quotient.mk` to define a map into a quotient (or its notation `⟦_⟧`)
Use `Quotient.lift` to define a map out of a quotient.
Use `Quotient.sound` to prove that two elements of the quotient are equal.
Use `Quotient.ind` to prove something for all elements of a quotient.
You can use this using the induction tactic: `induction x using Quotient.ind; rename_i x`.
-/
def quotient_equiv_subtype (X : Type*) :
    Quotient (myEquivalenceRelation X) ≃ X where
      toFun := Quotient.lift id (by
        intro a b hab
        exact hab
      )
      invFun := by{
        let f (k : X ) : (Quotient (myEquivalenceRelation X)) := ⟦k⟧
        use f
      }
      left_inv := by{
        apply Quotient.ind
        intro x
        rfl
      }
      right_inv := by {
        rintro x
        rfl
      }




section GroupActions

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/- Below is the orbit of an element `x ∈ X` w.r.t. a group action by `G`.
Prove that the orbits of two elements are equal
precisely when one element is in the orbit of the other. -/
def orbitOf (x : X) : Set X := range (fun g : G ↦ g • x)
#check MulAction.mem_orbit_iff

lemma orbitOf_eq_iff (x y : X) : orbitOf G x = orbitOf G y ↔ y ∈ orbitOf G x := by {
  constructor
  · intro hx
    rw[hx]
    unfold orbitOf
    rw [@Set.mem_range]
    use 1
    simp
  · intro hx
    unfold orbitOf at hx
    rw [@Set.mem_range] at hx
    obtain ⟨z, hz⟩ := hx
    have h1 : orbitOf G (z • x) = orbitOf G x := by{
      refine Eq.symm (Set.ext ?_)
      intro x_1
      constructor
      · intro h1
        obtain ⟨z1, hz1⟩ := h1
        simp at hz1
        use z1 • (z⁻¹)
        simp only [smul_eq_mul]
        calc (z1 * z⁻¹) • z • x = z1 • z⁻¹ • z • x := MulAction.mul_smul z1 (z⁻¹) (z • x)
        _ = z1 • x := by simp
        _ = x_1 := by rw [← hz1]
      · intro h
        obtain ⟨z1, hz1⟩ := h
        simp at hz1
        use (z1 • z)
        subst hz1 hz
        simp_all only [smul_eq_mul]
        exact mul_smul z1 z x
    }
    ext k
    constructor
    · intro horb
      rw[← hz]
      rw[h1]
      exact horb
    · intro horb
      rw[←hz] at horb
      rw[← h1]
      exact horb
  }

/- Define the stabilizer of an element `x` as the subgroup of elements
`g ∈ G` that satisfy `g • x = x`. -/
def stabilizerOf (x : X) : Subgroup G := sorry

-- This is a lemma that allows `simp` to simplify `x ≈ y` in the proof below.
@[simp] theorem leftRel_iff {x y : G} {s : Subgroup G} :
    letI := QuotientGroup.leftRel s; x ≈ y ↔ x⁻¹ * y ∈ s :=
  QuotientGroup.leftRel_apply

/- Let's probe the orbit-stabilizer theorem.

Hint: Only define the forward map (as a separate definition),
and use `Equiv.ofBijective` to get an equivalence.
(Note that we are coercing `orbitOf G x` to a (sub)type in the right-hand side) -/
def orbit_stabilizer_theorem (x : X) : G ⧸ stabilizerOf G x ≃ orbitOf G x := by {
  sorry
  }


end GroupActions
