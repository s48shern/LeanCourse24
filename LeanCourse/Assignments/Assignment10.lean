import LeanCourse.Common
import LeanCourse.DiffGeom

open Set ENat Manifold Metric Module Bundle Function
noncomputable section


/-
* There are no exercises in Mathematics in Lean about differential geometry

* You do not need to hand-in any exercises.

* You can solve the exercises below to practice with manifolds in Lean.
  Or work on your project instead.
-/

/-! # Exercises to practice. -/



/-
Partial homeomorphisms are globally defined maps with a globally defined "inverse", but the only
relevant set is the *source*, which should be mapped homeomorphically to the *target*.

Define a partial homeomorphism from `ℝ` to `ℝ` which is just `x ↦ -x`, but on `(-1, 1)`. In
Lean, the interval `(-1, 1)` is denoted by `Ioo (-1 : ℝ) 1` (where `o` stands for _open_). -/

def myFirstLocalHomeo : PartialHomeomorph ℝ ℝ where
  toFun := fun x ↦ -x
  invFun := fun x ↦ -x
  source := Ioo (-1) 1
  target := Ioo (-1) 1
  map_source' := by{
    intro x a
    simp_all only [mem_Ioo, neg_lt_neg_iff, true_and]
    obtain ⟨left, right⟩ := a
    rw [@neg_lt] at left
    exact left}
  map_target' := by
    {
      intro x a
      simp_all only [mem_Ioo, neg_lt_neg_iff, true_and]
      obtain ⟨left, right⟩ := a
      rw [@neg_lt] at left
      exact left
    }
  left_inv' := by
    {
      intro x a
      simp_all only [mem_Ioo, neg_neg]
    }
  right_inv' := by
    {
      intro x a
      simp_all only [mem_Ioo, neg_neg]}
  open_source :=by {
  simp_all only
  exact isOpen_Ioo
  }
  open_target := by {
  simp_all only
  exact isOpen_Ioo
  }
  continuousOn_toFun := by{
    simp_all only
    exact continuousOn_neg
  }
  continuousOn_invFun := by simp_all only; exact continuousOn_neg

/-!
### Smooth functions on `[0, 1]`

We will prove two simple lemmas about smooth maps on `[0, 1]`.
These lemmas are easy, but are still quite some work in Lean,
because Mathlib is missing many lemmas about manifolds.
In particular, don't expect any lemma that is about closed submanifolds.
-/

open unitInterval

def g : I → ℝ := Subtype.val

/- Smoothness results for `EuclideanSpace` are expressed for general `L^p` spaces
(as `EuclideanSpace` has the `L^2` norm), in: -/
#check PiLp.contDiff_coord
#check PiLp.contDiffOn_iff_coord

-- this is the charted space structure on `I`
#check IccManifold
#check contMDiff_iff

/- You might want to use `contMDiff_iff` and unfold the definition of
`modelWithCornersEuclideanHalfSpace` (and some other functions) in the proof. -/

example : ContMDiff (𝓡∂ 1) 𝓘(ℝ) ∞ g := by {
    refine contMDiff_iff.mpr ?_
    simp_all
    apply And.intro
    · exact continuous_iff_le_induced.mpr fun U a ↦ a
    · intro a b
      obtain ⟨left, right⟩ := b
      split
      next h => sorry
      next h =>
        simp_all only [not_lt]
        sorry

  }

lemma msmooth_of_smooth {f : ℝ → I} {s : Set ℝ} (h : ContDiffOn ℝ ∞ (fun x ↦ (f x : ℝ)) s) :
  ContMDiffOn 𝓘(ℝ) (𝓡∂ 1) ∞ f s := by {
  refine contMDiffOn_iff_target.mpr ?_
  constructor
  · refine ContinuousAt.continuousOn ?left.hcont
    intro x a
    refine Continuous.continuousAt ?left.hcont.h
    unfold ContDiffOn at h
    have h := h x a
    unfold ContDiffWithinAt at h
    sorry

  · intro y
    simp_all only [extChartAt, PartialHomeomorph.extend, chartAt_unitInterval, coe_lt_one, PartialEquiv.coe_trans,
    ModelWithCorners.toPartialEquiv_coe, PartialHomeomorph.toFun_eq_coe, PartialEquiv.trans_source,
    ModelWithCorners.source_eq, preimage_univ, inter_univ]
    obtain ⟨val, property⟩ := y
    split
    next h_1 =>
      rw [@contMDiffOn_iff_contDiffOn]
      sorry
    next h_1 =>
      simp_all only [not_lt]
      sorry
  }

/-! # No exercises to hand-in. -/
