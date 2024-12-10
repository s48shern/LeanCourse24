import LeanCourse.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution
import Mathlib.Data.Real.Irrational
import Mathlib.MeasureTheory.Function.Jacobian
open BigOperators Function Set Real Topology Filter
open MeasureTheory Interval Convolution ENNReal
noncomputable section

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace

--Pablo Cageao & Sergio Javier Hernando

/-
* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 11 & 12.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 10.12.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example (x : ℝ) :
    deriv (fun x ↦ Real.exp (x ^ 2)) x = 2 * x * Real.exp (x ^ 2) := by {
  simp_all
  linarith
  }

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {n : ℕ∞} in
/- In this exercise you should combine the right lemmas from the library,
in particular `IsBoundedBilinearMap.contDiff`. -/
--#check IsBoundedBilinearMap.contDiff
example (L : E →L[𝕜] E →L[𝕜] E) (f g : E → E) (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun z : E × E ↦ L (f z.1) (g z.2)) := by {
  apply IsBoundedBilinearMap.contDiff
  refine
    { add_left := ?hb.add_left, smul_left := ?hb.smul_left, add_right := ?hb.add_right,
      smul_right := ?hb.smul_right, bound := ?hb.bound }
  simp
  intro x y c
  sorry
  sorry
  sorry
  sorry
  sorry
  }


section

variable (α : Type*)
 [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-
In the next three exercises we will show that every continuous injective function `ℝ → ℝ` is
either strictly monotone or strictly antitone.

We start by proving a slightly harder version of the exercise in class.
We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
Useful lemmas: `uIcc_of_le` and `mem_uIcc`. -/
#check uIcc_of_le
#check mem_uIcc
#check intermediate_value_uIcc
lemma mono_exercise_part1 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  unfold Injective at *
  by_contra h
  simp at h
  have hfIxa: [[f x, f a]] ⊆ f '' [[x, a]] := by{
    have hf': ContinuousOn f [[x, a]] := by exact Continuous.continuousOn hf
    exact intermediate_value_uIcc hf'
  }
  have hfIab: [[f a, f b]] ⊆ f '' [[a, b]] := by{
    have hf': ContinuousOn f [[a, b]] := by exact Continuous.continuousOn hf
    exact intermediate_value_uIcc hf'
  }
  have hfIxb: [[f x, f b]] ⊆ f '' [[x, b]] := by{
    have hf': ContinuousOn f [[x, b]] := by exact Continuous.continuousOn hf
    exact intermediate_value_uIcc hf'
  }
  by_cases h': x≥b
  . have hc: ∃c, f a < c ∧ c < f b := by exact exists_between h2ab
    obtain ⟨c, hca, hcb⟩ := hc
    have hcab: c ∈ [[f a, f b]] := by{
      rw [mem_uIcc]
      left
      exact ⟨le_of_lt hca, le_of_lt hcb⟩
    }
    specialize hfIab hcab
    have hcxb: c ∈ [[f x, f b]] := by{
      rw [mem_uIcc]
      left
      exact ⟨le_of_lt (gt_trans hca h), le_of_lt hcb⟩
    }
    specialize hfIxb hcxb
    have hint: (f '' [[a, b]]) ∩ (f '' [[x, b]]) = {f b} := by{
      rw [Eq.symm (image_inter h2f)]
      have heq: [[a, b]] ∩ [[x, b]] = {b}:= by{
        ext y
        constructor
        . intro hy
          obtain ⟨hab, hxb⟩:=hy
          rw [mem_uIcc] at hab hxb
          have h': y=b := by sorry
          exact h2f (h2f (congrArg f (congrArg f h')))
        . intro hy
          have hy:= h2f (h2f (congrArg f (congrArg f hy)))
          rw [hy]
          constructor
          . rw [mem_uIcc]
            left
            constructor
            . exact hab
            . exact Preorder.le_refl b
          . rw [mem_uIcc]
            right
            constructor
            . exact Preorder.le_refl b
            . exact h'
      }
      rw [congrArg (image f) heq]
      exact image_singleton
    }
    have hc: c ∈ f '' [[a, b]] ∩ f '' [[x, b]] := by exact mem_inter hfIab hfIxb
    rw [hint] at hc
    have hc:= h2f (h2f (congrArg f (congrArg f hc)))
    have hc: ¬ c < f b := by exact not_lt.mpr (le_of_eq (h2f (h2f (congrArg f (congrArg f (id (Eq.symm hc)))))))
    exact hc hcb
  . simp at h'
    have hc: ∃c, f x < c ∧ c < f a := by exact exists_between h
    obtain ⟨c, hcx, hca⟩ := hc
    have hcax: c ∈ [[f x, f a]] := by{
      rw [mem_uIcc]
      left
      exact ⟨le_of_lt hcx, le_of_lt hca⟩
    }
    specialize hfIxa hcax
    have hcxb: c ∈ [[f x, f b]] := by{
      rw [mem_uIcc]
      left
      exact ⟨le_of_lt hcx, le_of_lt (gt_trans h2ab hca)⟩
    }
    specialize hfIxb hcxb
    have hint: (f '' [[a, x]]) ∩ (f '' [[x, b]]) = {f b} := by{
      sorry
    }
    have hc: c ∈ f '' [[a, x]] ∩ f '' [[x, b]] := by {
      rw [uIcc_comm a x]
      exact mem_inter hfIxa hfIxb
    }
    rw [hint] at hc
    have hc:= h2f (h2f (congrArg f (congrArg f hc)))
    have hc: ¬ c < f b := by exact not_lt.mpr (le_of_eq (h2f (h2f (congrArg f (congrArg f (id (Eq.symm hc)))))))
    have hc': c < f b:= by exact gt_trans h2ab hca
    exact hc hc'
}

/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma mono_exercise_part2 {f : α → α} (hf : Continuous f) (h2f : Injective f)
    {a b : α} (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by {
  sorry
  }

/-
Now we can finish just by using the previous exercise multiple times.
In this proof we take advantage that we did the previous exercise for an arbitrary order,
because that allows us to apply it to `ℝ` with the reversed order `≥`.
This is called `OrderDual ℝ`. This allows us to get that `f` is also strictly monotone on
`(-∞, b]`.
Now finish the proof yourself.
You do not need to apply the intermediate value theorem in this exercise.
-/
lemma mono_exercise_part3 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) :
    StrictMono f ∨ StrictAnti f := by {
  have : ∀ {a b : ℝ} (hab : a ≤ b) (h2ab : f a < f b), StrictMonoOn f (Iic b)
  · intro a b hab h2ab
    have := mono_exercise_part2 (OrderDual ℝ) hf h2f hab h2ab
    rw [strictMonoOn_dual_iff.symm] at this
    exact this
  sorry
  }

end

/-
Let's prove that the absolute value function is not differentiable at 0.
You can do this by showing that the left derivative and the right derivative do exist,
but are not equal. We can state this with `HasDerivWithinAt`
To make the proof go through, we need to show that the intervals have unique derivatives.
An example of a set that doesn't have unique derivatives is the set `ℝ × {0}`
as a subset of `ℝ × ℝ`, since that set doesn't contains only points in the `x`-axis,
so within that set there is no way to know what the derivative of a function should be
in the direction of the `y`-axis.

The following lemmas will be useful
* `HasDerivWithinAt.congr`
* `uniqueDiffWithinAt_convex`
* `HasDerivWithinAt.derivWithin`
* `DifferentiableAt.derivWithin`.
-/

example : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := by {
  intro h
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0 := by {
    sorry
    }
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0 := by {
    sorry
    }
  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by {
  sorry
  }
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by {
  sorry
  }
  -- sorry
  sorry
  }



/- There are special cases of the change of variables theorems for affine transformations
(but you can also use the change of variable theorem from the lecture) -/
example (a b : ℝ) :
    ∫ x in a..b, sin (x / 2 + 3) =
    2 * cos (a / 2 + 3) - 2 * cos (b / 2  + 3) := by {
  sorry
  }

/- Use the change of variables theorem for this exercise. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, exp x * f (exp x) = ∫ y in exp '' s, f y := by {
  sorry
  }

example (x : ℝ) : ∫ t in (0)..x, t * exp t = (x - 1) * exp x + 1 := by {
  sorry
  }

example (a b : ℝ) : ∫ x in a..b, 2 * x * exp (x ^ 2) =
    exp (b ^ 2) - exp (a ^ 2) := by {
  sorry
  }


/-! # Exercises to hand-in. -/

/- This is a copy of `mono_exercise_part1` above. See the comments there for more info. -/
variable (α : Type*) [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] in
lemma mono_exercise_part1_copy {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by {
  unfold Injective at *
  by_contra h
  simp at h
  have hfIxa: [[f x, f a]] ⊆ f '' [[x, a]] := by{
    have hf': ContinuousOn f [[x, a]] := by exact Continuous.continuousOn hf
    exact intermediate_value_uIcc hf'
  }
  have hfIab: [[f a, f b]] ⊆ f '' [[a, b]] := by{
    have hf': ContinuousOn f [[a, b]] := by exact Continuous.continuousOn hf
    exact intermediate_value_uIcc hf'
  }
  have hfIxb: [[f x, f b]] ⊆ f '' [[x, b]] := by{
    have hf': ContinuousOn f [[x, b]] := by exact Continuous.continuousOn hf
    exact intermediate_value_uIcc hf'
  }
  by_cases h': x≥b
  . have hc: ∃c, f a < c ∧ c < f b := by exact exists_between h2ab
    obtain ⟨c, hca, hcb⟩ := hc
    have hcab: c ∈ [[f a, f b]] := by{
      rw [mem_uIcc]
      left
      exact ⟨le_of_lt hca, le_of_lt hcb⟩
    }
    specialize hfIab hcab
    have hcxb: c ∈ [[f x, f b]] := by{
      rw [mem_uIcc]
      left
      exact ⟨le_of_lt (gt_trans hca h), le_of_lt hcb⟩
    }
    specialize hfIxb hcxb
    have hint: (f '' [[a, b]]) ∩ (f '' [[x, b]]) = {f b} := by{
      rw [Eq.symm (image_inter h2f)]
      have heq: [[a, b]] ∩ [[x, b]] = {b}:= by{
        rw [uIcc_of_le]
        rw [uIcc_of_ge]
        rw [Set.Icc_inter_Icc_eq_singleton]
        . exact hab
        . exact h'
        . exact h'
        . exact hab
      }
      rw [congrArg (image f) heq]
      exact image_singleton
    }
    have hc: c ∈ f '' [[a, b]] ∩ f '' [[x, b]] := by exact mem_inter hfIab hfIxb
    rw [hint] at hc
    have hc:= h2f (h2f (congrArg f (congrArg f hc)))
    have hc: ¬ c < f b := by exact Eq.not_lt hc
    exact hc hcb
  . simp at h'
    have hc: ∃c, f x < c ∧ c < f a := by exact exists_between h
    obtain ⟨c, hcx, hca⟩ := hc
    have hcax: c ∈ [[f x, f a]] := by{
      rw [mem_uIcc]
      left
      exact ⟨le_of_lt hcx, le_of_lt hca⟩
    }
    specialize hfIxa hcax
    have hcxb: c ∈ [[f x, f b]] := by{
      rw [mem_uIcc]
      left
      exact ⟨le_of_lt hcx, le_of_lt (gt_trans h2ab hca)⟩
    }
    specialize hfIxb hcxb
    have hint: (f '' [[a, x]]) ∩ (f '' [[x, b]]) = {f x} := by{
      rw [Eq.symm (image_inter h2f)]
      have heq: [[a, x]] ∩ [[x, b]] = {x} := by {
        rw [uIcc_of_le]
        rw [uIcc_of_le]
        rw [Set.Icc_inter_Icc_eq_singleton]
        . exact hx
        . exact le_of_lt h'
        . exact le_of_lt h'
        . exact hx
      }
      rw [congrArg (image f) heq]
      exact image_singleton
    }
    have hc: c ∈ f '' [[a, x]] ∩ f '' [[x, b]] := by {
      rw [uIcc_comm a x]
      exact mem_inter hfIxa hfIxb
    }
    rw [hint] at hc
    have hc:= h2f (h2f (congrArg f (congrArg f hc)))
    have hc': ¬ f x < c := by exact Eq.not_gt hc
    exact hc' hcx
  }

/- Prove the following using the change of variables theorem. -/
lemma change_of_variables_exercise (f : ℝ → ℝ) :
    ∫ x in (0)..π, sin x * f (cos x) = ∫ y in (-1)..1, f y := by {
    let g : ℝ → ℝ := cos
    let f1 : ℝ → ℝ := -sin
    have g_deriv : ∀ x ∈ Icc 0 π, HasDerivAt g (-sin x) x := by{
      intros x hx
      exact (hasDerivAt_cos x)
    }
    have g_deriv': ∀ x ∈ [[0,π]], HasDerivWithinAt g (-sin x) [[0,π]] x := by {
      intro x hx
      refine HasDerivAt.hasDerivWithinAt (hasDerivAt_cos x)
    }
    have s_measurable: MeasurableSet [[0,π]] := by exact measurableSet_uIcc
    have g_inj : InjOn g (Icc 0 π) := by exact injOn_cos
    have g_cont : ContinuousOn g (Icc 0 π) := continuousOn_cos
    have g_deriv_cont : ContinuousOn f1 (Icc 0 π) := by {
      simp_all only [mem_Icc, and_imp, continuousOn_neg_iff, g, f1]
      exact continuousOn_sin
    }
    simp_all only [mem_Icc, and_imp, continuousOn_neg_iff, g, f1]
    calc ∫ x in (0)..π, sin x * f (cos x) = ∫ x in [[0, π]], sin x * f (cos x) := by {
      rw [intervalIntegral.integral_of_le]
      have hint: [[0, π]] = Icc 0 π := by {
        refine uIcc_of_le ?h
        exact pi_nonneg
      }
      simp_all only [mem_Icc, and_imp, measurableSet_Icc]
      exact Eq.symm integral_Icc_eq_integral_Ioc
      exact pi_nonneg
    }
    _= ∫ x in [[0, π]], (abs (sin x)) * f (cos x) := by{
      have hpos :  ∀ x : ℝ,  (x ∈ [[0, π]]) → sin x ≥ 0 := by{
        intro x hx
        rw [@mem_uIcc] at hx
        have hx : ( 0 ≤ x ∧ x ≤ π ) := by{ cases hx with
        | inl h => simp_all only [and_self]
        | inr h_1 =>{
          obtain ⟨left, right⟩ := h_1
          apply And.intro
          · calc 0 ≤ π := by exact pi_nonneg
            _ ≤ x := by exact left
          · calc x ≤ 0 := by exact right
            _ ≤ π := by exact pi_nonneg}
        }
        apply sin_nonneg_of_nonneg_of_le_pi
        exact hx.1
        exact hx.2
      }
      have habs : ∀ x : ℝ, (x ∈ [[0, π]]) → sin x = abs (sin x)  := by{
        exact fun x a ↦ Eq.symm (abs_of_nonneg (hpos x a))
      }
      apply setIntegral_congr measurableSet_Icc
      intros x hx
      rw [@mul_eq_mul_right_iff]
      exact mul_eq_mul_left_iff.mp (congrArg (HMul.hMul (f (cos x))) (habs x hx))
    }
    _ = ∫ y in (cos '' [[0,π]]), f y := by {
        rw [← uIcc_of_le] at g_inj
        rw [integral_image_eq_integral_abs_deriv_smul s_measurable g_deriv' g_inj]
        . simp
        . exact pi_nonneg
      }
    _ = ∫ y in [[-1,1]], f y := by {
      have hint : (cos '' [[0,π]]) = [[-1,1]] := by{
        ext x
        constructor
        · intro h
          rw [@mem_image] at h
          obtain ⟨y, hy⟩ := h
          simp_all only [neg_le_self_iff, zero_le_one, uIcc_of_le, mem_Icc]
          obtain ⟨left, right⟩ := hy
          subst right
          apply And.intro
          · exact neg_one_le_cos y
          · exact cos_le_one y
        · intro h
          simp_all only [neg_le_self_iff, zero_le_one, uIcc_of_le, mem_Icc, mem_image]
          obtain ⟨left, right⟩ := h
          use (arccos x)
          apply And.intro
          · rw [@mem_uIcc]
            have h1 : 0 ≤ arccos x := by exact arccos_nonneg x
            have h2 : arccos x ≤ π := by exact arccos_le_pi x
            simp_all only [and_self, true_or]
          · exact cos_arccos left right
      }
      simp_all only [neg_le_self_iff, zero_le_one, uIcc_of_le]
    }
    _ = ∫ y in (-1)..1, f y := by {
      rw [intervalIntegral.integral_of_le]
      have hint: [[-1, 1]] = Icc (-1) 1 := by {
        simp_all only [Int.reduceNeg, neg_le_self_iff, zero_le_one, uIcc_of_le]
      }
      simp_all
      exact integral_Icc_eq_integral_Ioc
      linarith
    }
  }
