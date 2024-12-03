import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace
-- Pablo Cageao and Sergio Hernando

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 10.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 3.12.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- You can use `filter_upwards` to conveniently conclude `Eventually` statements from `Eventually`
in one or more hypotheses using the same filter. -/
example {ι : Type*} {L : Filter ι} {f g : ι → ℝ} (h1 : ∀ᶠ i in L, f i ≤ g i)
    (h2 : ∀ᶠ i in L, g i ≤ f i) : ∀ᶠ i in L, f i = g i := by
  filter_upwards [h1, h2] with i h1 h2
  exact le_antisymm h1 h2

example {ι : Type*} {L : Filter ι} {a b : ι → ℤ} (h1 : ∀ᶠ i in L, a i ≤ b i + 1)
    (h2 : ∀ᶠ i in L, b i ≤ a i + 1) (h3 : ∀ᶠ i in L, b i ≠ a i) : ∀ᶠ i in L, |a i - b i| = 1 := by {
    filter_upwards [h1, h2, h3] with i h1 h2 h3
    have h2 : b i - a i ≤ 1 := by linarith
    have h1 : a i - b i ≤ 1 := by linarith
    have h1 : |a i - b i| ≤ 1 := by {
      refine abs_sub_le_iff.mpr ?_
      constructor
      · exact h1
      · exact h2
    }
    rw [@Int.abs_le_one_iff] at h1
    simp_all only [ne_eq, tsub_le_iff_right, Int.reduceNeg]
    cases h1 with
    | inl h =>
      simp_all only [abs_zero, zero_ne_one]
      push_neg at h3
      have h : b i = a i := by linarith
      exact h3 h
    | inr h_1 =>
      cases h_1 with
      | inl h => simp_all only [abs_one]
      | inr h_2 => simp_all only [Int.reduceNeg, abs_neg, abs_one]

  }

/- The goal of the following exercise is to prove that
the regular open sets in a topological space form a complete boolean algebra.
`U ⊔ V` is given by `interior (closure (U ∪ V))`.
`U ⊓ V` is given by `U ∩ V`. -/


variable {X : Type*} [TopologicalSpace X]

variable (X) in
structure RegularOpens where
  carrier : Set X
  isOpen : IsOpen carrier
  regular' : interior (closure carrier) = carrier

namespace RegularOpens

/- We write some lemmas so that we can easily reason about regular open sets. -/
variable {U V : RegularOpens X}

instance : SetLike (RegularOpens X) X where
  coe := RegularOpens.carrier
  coe_injective' := fun ⟨_, _, _⟩ ⟨_, _, _⟩ _ => by congr

theorem le_def {U V : RegularOpens X} : U ≤ V ↔ (U : Set X) ⊆ (V : Set X) := by simp
@[simp] theorem regular {U : RegularOpens X} : interior (closure (U : Set X)) = U := U.regular'

@[simp] theorem carrier_eq_coe (U : RegularOpens X) : U.1 = ↑U := rfl

@[ext] theorem ext (h : (U : Set X) = V) : U = V :=
  SetLike.coe_injective h


/- First we want a complete lattice structure on the regular open sets.
We can obtain this from a so-called `GaloisCoinsertion` with the closed sets.
This is a pair of maps
* `l : RegularOpens X → Closeds X`
* `r : Closeds X → RegularOpens X`
with the properties that
* for any `U : RegularOpens X` and `C : Closeds X` we have `l U ≤ C ↔ U ≤ r U`
* `r ∘ l = id`
If you know category theory, this is an *adjunction* between orders
(or more precisely, a coreflection).
-/

/- The closure of a regular open set. Of course mathlib knows that the closure of a set is closed.
(the `simps` attribute will automatically generate the simp-lemma for you that
`(U.cl : Set X) = closure (U : Set X)`
-/
@[simps]
def cl (U : RegularOpens X) : Closeds X :=
  ⟨closure U, sorry⟩

/- The interior of a closed set. You will have to prove yourself that it is regular open. -/
@[simps]
def _root_.TopologicalSpace.Closeds.int (C : Closeds X) : RegularOpens X :=
  ⟨interior C, sorry, sorry⟩

/- Now let's show the relation between these two operations. -/
lemma cl_le_iff {U : RegularOpens X} {C : Closeds X} :
    U.cl ≤ C ↔ U ≤ C.int := by sorry

@[simp] lemma cl_int : U.cl.int = U := by sorry

/- This gives us a GaloisCoinsertion. -/

def gi : GaloisCoinsertion cl (fun C : Closeds X ↦ C.int) where
  gc U C := cl_le_iff
  u_l_le U := by simp
  choice C hC := C.int
  choice_eq C hC := rfl

/- It is now a general theorem that we can lift the complete lattice structure from `Closeds X`
to `RegularOpens X`. The lemmas below give the definitions of the lattice operations. -/

instance completeLattice : CompleteLattice (RegularOpens X) :=
  GaloisCoinsertion.liftCompleteLattice gi

@[simp] lemma coe_inf {U V : RegularOpens X} : ↑(U ⊓ V) = (U : Set X) ∩ V := by
  have : U ⊓ V = (U.cl ⊓ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_sup {U V : RegularOpens X} : ↑(U ⊔ V) = interior (closure ((U : Set X) ∪ V)) := by
  have : U ⊔ V = (U.cl ⊔ V.cl).int := rfl
  simp [this]

@[simp] lemma coe_top : ((⊤ : RegularOpens X) : Set X) = univ := by
  have : (⊤ : RegularOpens X) = (⊤ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_bot : ((⊥ : RegularOpens X) : Set X) = ∅ := by
  have : (⊥ : RegularOpens X) = (⊥ : Closeds X).int := rfl
  simp [this]

@[simp] lemma coe_sInf {U : Set (RegularOpens X)} :
    ((sInf U : RegularOpens X) : Set X) =
    interior (⋂₀ ((fun u : RegularOpens X ↦ closure u) '' U)) := by
  have : sInf U = (sInf (cl '' U)).int := rfl
  simp [this]

@[simp] lemma Closeds.coe_sSup {C : Set (Closeds X)} : ((sSup C : Closeds X) : Set X) =
    closure (⋃₀ ((↑) '' C)) := by
  have : sSup C = Closeds.closure (sSup ((↑) '' C)) := rfl
  simp [this]

@[simp] lemma coe_sSup {U : Set (RegularOpens X)} :
    ((sSup U : RegularOpens X) : Set X) =
    interior (closure (⋃₀ ((fun u : RegularOpens X ↦ closure u) '' U))) := by
  have : sSup U = (sSup (cl '' U)).int := rfl
  simp [this]

/- We still have to prove that this gives a distributive lattice.
Warning: these are hard. -/
instance completeDistribLattice : CompleteDistribLattice (RegularOpens X) :=
  CompleteDistribLattice.ofMinimalAxioms
  { completeLattice with
    inf_sSup_le_iSup_inf := by sorry
    iInf_sup_le_sup_sInf := by sorry
    }


instance : HasCompl (RegularOpens X) := sorry


@[simp]
lemma coe_compl (U : RegularOpens X) : ↑Uᶜ = interior (U : Set X)ᶜ := by sorry


instance : CompleteBooleanAlgebra (RegularOpens X) :=
  { inferInstanceAs (CompleteDistribLattice (RegularOpens X)) with
    inf_compl_le_bot := by sorry
    top_le_sup_compl := by sorry
    le_sup_inf := by sorry
    sdiff_eq := by sorry
    himp_eq := by sorry }




/-! # Exercises to hand-in. -/

/- Here is a technical property using filters, characterizing when a 2-valued function converges to
a filter of the form `if q then F else G`. The next exercise is a more concrete application.
Useful lemmas here are
-/
#check Filter.Eventually.filter_mono
#check Filter.Eventually.mono
#check pure
lemma technical_filter_exercise {ι α : Type*} {p : ι → Prop} {q : Prop} {a b : α}
    {L : Filter ι} {F G : Filter α}
    (hbF : ∀ᶠ x in F, x ≠ b) (haG : ∀ᶠ x in G, x ≠ a) (haF : pure a ≤ F) (hbG : pure b ≤ G) :
    (∀ᶠ i in L, p i ↔ q) ↔
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) := by {
  have hab : a ≠ b := by{
    exact haF hbF
  }
  rw [tendsto_iff_eventually]
  constructor
  · intro h
    intro p1 hp
    filter_upwards [h] with i h
    simp at *
    replace h : p i = q := propext h
    subst h
    split
    next h =>
      simp_all only [iff_true, ↓reduceIte]
      apply haF
      exact hp
    next h =>
      simp_all only [iff_false, ↓reduceIte]
      apply hbG
      exact hp
  · intro h
    simp_all only [ne_eq]
    split at h
    next h =>
      simp_all only [iff_true]
      apply Filter.Eventually.mono
      apply h
      exact hbF
      intro x a_1
      simp_all only [ite_eq_right_iff, imp_false, Decidable.not_not]
    next h =>
      simp_all only [iff_false]
      apply Filter.Eventually.mono
      apply h
      exact haG
      intro x a_1
      simp_all only [ite_eq_left_iff, Classical.not_imp, not_false_eq_true]
  }

/- To be more concrete, we can use the previous lemma to prove the following.
if we denote the characteristic function of `A` by `1_A`, and `f : ℝ → ℝ` is a function,
then  `f * 1_{s i}` tends to `f * 1_t` iff `x ∈ s i` is eventually equivalent to
`x ∈ t` for all `x`. (note that this does *not* necessarily mean that `s i = t` eventually).
`f * 1_t` is written `indicator t f` in Lean.
Useful lemmas for this exercise are `indicator_apply`, `apply_ite` and `tendsto_pi_nhds`. -/
#check indicator_apply
#check apply_ite
#check tendsto_pi_nhds
lemma tendsto_indicator_iff {ι : Type*} {L : Filter ι} {s : ι → Set ℝ} {t : Set ℝ} {f : ℝ → ℝ}
    (ha : ∀ x, f x ≠ 0) :
    (∀ x, ∀ᶠ i in L, x ∈ s i ↔ x ∈ t) ↔
    Tendsto (fun i ↦ indicator (s i) f) L (𝓝 (indicator t f)) := by {
    let f':=(fun i x1 ↦ if x1 ∈ s i then f x1 else 0)
    let g':=(fun x1 ↦ if x1 ∈ t then f x1 else 0)
    have h: Tendsto f' L (𝓝 g') ↔ ∀ (x), Tendsto (fun i ↦ f' i x) L (𝓝 (g' x)) := by {
      exact tendsto_pi_nhds
    }
    have h': (∀ (x), 𝓝 (g' x) = if x ∈ t then 𝓝 (f x) else 𝓝 0) := by {
      unfold g'
      exact fun x ↦ apply_ite 𝓝 (x ∈ t) (f x) 0
    }
    unfold indicator
    constructor
    . intro hx
      rw [h]
      intro x
      specialize h' x
      rw [h']
      rw [← technical_filter_exercise]
      . exact hx x
      . exact ContinuousAt.eventually_ne (fun ⦃U⦄ a ↦ a) (ha x)
      . exact ContinuousAt.eventually_ne (fun ⦃U⦄ a ↦ a) fun a ↦ ha x (id (Eq.symm a))
      . exact intervalIntegral.FTCFilter.pure_le
      . exact intervalIntegral.FTCFilter.pure_le
    . intro hx x
      rw [h] at hx
      specialize hx x
      rw [h'] at hx
      rw [← technical_filter_exercise] at hx
      . exact hx
      . exact ContinuousAt.eventually_ne (fun ⦃U⦄ a ↦ a) (ha x)
      . exact ContinuousAt.eventually_ne (fun ⦃U⦄ a ↦ a) fun a ↦ ha x (id (Eq.symm a))
      . exact intervalIntegral.FTCFilter.pure_le
      . exact intervalIntegral.FTCFilter.pure_le
  }
