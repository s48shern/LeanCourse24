import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Set Nat
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 4, sections 2, 3.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 5.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- Do the exercises about sets from last exercise set, if you haven't done them because
we didn't cover the material in class yet. -/


variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by {
  constructor
  · intro hx
    subst s
    intro x
    trivial
  · intro hx
    unfold univ
    apply Subset.antisymm
    exact fun ⦃a⦄ a ↦ trivial
    exact fun ⦃a⦄ a_1 ↦ hx a
  }


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  by_contra hq
  push_neg at hq
  have hp := hq.left
  have hnp := hq.right
  contradiction
  }

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (123 + 32 * 3, (x + y) ^ 2) = (219, x ^ 2 + 2 * x * y + y ^ 2) := by {
  norm_num
  linarith
  }

/- `A ≃ B` means that there is a bijection from `A` to `B`.
So in this exercise you are asked to prove that there is a bijective correspondence between
  functions from `ℤ × ℕ` to `ℤ × ℤ`
and
  functions from `ℕ` to `ℕ`
This is an exercise about finding lemmas from the library.
Your proof is supposed to only combine results from the library,
you are not supposed to define the bijection yourself.
If you want, you can use `calc` blocks with `≃`. -/
example : (ℤ × ℕ → ℤ × ℤ) ≃ (ℕ → ℕ) := by {
  have ha: (ℤ × ℕ ≃ ℤ ) := by{
    exact (Denumerable.equiv₂ ℤ (ℤ × ℕ)).symm
  }
  have hb: (ℤ × ℤ ≃ ℤ ) := by{
    exact Denumerable.pair
  }
  have hc: (ℤ ≃ ℕ ) := by{
    exact Equiv.intEquivNat
  }
  calc (ℤ × ℕ → ℤ × ℤ) ≃ (ℤ → ℤ × ℤ) := by exact Equiv.piCongrLeft' (fun a ↦ ℤ × ℤ) ha
  _ ≃ (ℕ → ℤ × ℤ) :=  by exact Equiv.piCongrLeft' (fun a ↦ ℤ × ℤ) hc
  _ ≃ (ℕ → ℤ) := by exact Equiv.piCongrRight fun a ↦ hb
  _ ≃ (ℕ → ℕ) := by exact Equiv.piCongrRight fun a ↦ hc
  }
open Classical
/- Prove a version of the axiom of choice Lean's `Classical.choose`. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by {
  exact skolem.mp hC
  }


/-! # Exercises to hand-in. -/


/- ## Converging sequences

Prove two more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma sequentialLimit_reindex {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
  unfold SequentialLimit at *
  simp at *
  intro ε hε
  specialize hs ε
  have hs:= hs hε
  obtain ⟨N0, hs⟩:= hs
  specialize hr N0
  obtain ⟨N1, hr⟩:= hr
  let N:= max N0 N1
  have hN1: N≥ N1 := by exact Nat.le_max_right N0 N1
  have hN0: N≥ N0 := by exact Nat.le_max_left N0 N1
  use N
  intro n hn
  specialize hr n
  have hN1: n≥ N1 := by exact Nat.le_trans hN1 hn
  have hN0: n≥ N0 := by exact Nat.le_trans hN0 hn
  have hr:= hr hN1
  specialize hs (r n)
  have hs:= hs hr
  exact hs
  }



/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma sequentialLimit_squeeze {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
  unfold SequentialLimit at *
  simp at *
  intro ε hε
  specialize hs₁ ε
  specialize hs₃ ε
  have hs1 := hs₁ hε
  have hs3 := hs₃ hε
  obtain ⟨N1, hs1⟩:= hs1
  obtain ⟨N3, hs3⟩:= hs3
  let N:= max N1 N3
  have hN1: N≥ N1 := by exact Nat.le_max_left N1 N3
  have hN3: N≥ N3 := by exact Nat.le_max_right N1 N3
  use N
  intro n hn
  specialize hs1 n
  specialize hs3 n
  specialize hs₁s₂ n
  specialize hs₂s₃ n
  have hN1: n ≥  N1 := by exact Nat.le_trans hN1 hn
  have hN3: n ≥ N3 := by exact Nat.le_trans hN3 hn
  have hs1:= hs1 hN1
  have hs3:= hs3 hN3
  unfold abs at *
  have h1l : s₁ n  > a - ε := by exact sub_lt_of_abs_sub_lt_left (hs1)
  have h3r : s₃ n  < a + ε := by {
    have hp:  s₃ n - a < ε := by exact lt_of_abs_lt (hs3)
    linarith
  }
  have h2l :s₂ n  > a - ε := by {
    calc a - ε < s₁ n := by exact h1l
    _ ≤  s₂ n := by exact hs₁s₂
  }
  have h2r :s₂ n  < a + ε := by {
    calc a + ε > s₃ n := by exact h3r
    _ ≥  s₂ n := by exact hs₂s₃
  }
  simp
  constructor
  · exact sub_left_lt_of_lt_add h2r
  · exact sub_lt_comm.mp h2l
  }

/- ## Sets -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
  ext x
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := hx.1
    have h3: a ∈ f ⁻¹' t := by {
    simp[ha]
    apply hx.2
    }
    have ha2: a ∈ s ∩ f ⁻¹' t:= by{
      simp
      constructor
      · apply ha.1
      · apply h3
    }
    have hf : f (a) ∈ f '' (s ∩ f ⁻¹' t) := by use a
    rw[←ha.2]
    apply hf
  · intro hx
    constructor
    · have h1: f '' (s ∩ f ⁻¹' t) ⊆ f '' s :=  by{
        rintro y ⟨a, ha, rfl⟩
        have ha:= ha.1
        use a
      }
      exact h1 hx
    · have h1: f '' (s ∩ f ⁻¹' t) ⊆ f '' (f ⁻¹' t) :=  by{
        rintro y ⟨a, ha, rfl⟩
        have ha:= ha.2
        use a
      }
      have h2 : x ∈ f '' (f ⁻¹' t) :=by exact h1 hx
      rcases h2 with ⟨y, hy, rfl⟩
      exact hy
  }

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {
  ext y
  constructor
  · intro hy
    refine (mem_union y {x | x ≤ -4} {x | x ≥ 4}).mpr ?h.mp.a
    simp [hy]
    have h_sq : y^2 ≥ 16 := hy
    have h_abs : |y| ≥ 4 := by {
    have h_def : |y| = √ (y^2):= by exact Eq.symm (sqrt_sq_eq_abs y)
    rw[h_def]
    refine (Real.le_sqrt' ?hx).mpr ?_
    linarith
    norm_num
    exact h_sq
    }
    exact le_abs'.mp h_abs

  · intro hy
    refine mem_preimage.mpr ?h.mpr.a
    refine mem_setOf.mpr ?h.mpr.a.a
    have h_neg : y ≤ -4 ∨ y ≥ 4 := by exact hy
    cases h_neg
    · calc y^2 = (-y)^2 := by exact Eq.symm (neg_pow_two y)
      _ ≥ 4^2 := by {
        have hcalc: 4 ≤ -y := by linarith
        refine sq_le_sq.mpr ?_
        refine abs_le_abs hcalc ?h₁
        gcongr
        linarith
      }
      _ = 16 := by linarith
    · have hcalc : y ≥ 4 := by linarith
      calc y^2 ≥ 4^2 := by {
      refine pow_le_pow_left ?ha hcalc 2
      linarith
      }
      _ = 16 := by linarith
  }


/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
def conditionalInverse_restr (y : β)
  (h: ∃ x ∈ s, f x = y) : α :=
  Classical.choose h

lemma invFun_spec_restr (y : β) (h : ∃ x, x ∈ s ∧ f x = y) :
    (conditionalInverse_restr f s y h) ∈ s ∧ f (conditionalInverse_restr f s y h) = y := Classical.choose_spec h

def inverse_restr [Inhabited α] (f : α → β) (y : β) : α :=
  if h : ∃ x ∈ s, f x = y then
    conditionalInverse_restr f s y h else default

lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {
  unfold InjOn at *
  unfold LeftInvOn
  let g: β → α := inverse_restr s f
  --fun y ↦ if h: ∃ x ∈ s, f x = y then Classical.choose h else (default)
  use g
  intro x hx
  unfold g
  have h': ∃ x_1 ∈ s, f x_1 = f x := by {use x}
  simp [inverse_restr]
  simp [h']
  apply hf
  . exact (invFun_spec_restr f s (f x) h').1
  . exact hx
  . exact (invFun_spec_restr f s (f x) h').2
  }


/- Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

To help you along the way, some potentially useful ways to reformulate the hypothesis are given. -/

-- This lemma might be useful.

#check Injective.eq_iff

lemma set_bijection_of_partition {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by {
  -- h1' and h1'' might be useful later as arguments of `simp` to simplify your goal.
  --unfold Injective at *
  unfold univ at *
  --unfold range at *
  have hf: ∀a b, f a = f b ↔ a = b := by exact fun a b ↦ Injective.eq_iff hf
  have hg: ∀a b, g a = g b ↔ a = b := by exact fun a b ↦ Injective.eq_iff hg
  have h1' : ∀ x y, f x ≠ g y := by {
    intro x y
    by_contra hnot
    have hnotF: f x ∈ {x | ∃ y, f y = x} := by simp
    have hnotG: f x ∈ {x | ∃ y, g y = x} := by {
      rw [hnot]
      simp
    }
    have hnotFG: f x ∈ {x | ∃ y, f y = x} ∩ {x | ∃ y, g y = x} := by{
      exact mem_inter hnotF hnotG
    }
    have hnotf: f x ∈ (∅ : Set γ) := by {
      rw [← h1]
      exact hnotFG
    }
    trivial
  }
  have h1'' : ∀ y x, g y ≠ f x := by exact fun y x a ↦ h1' x y (id (Eq.symm a))
  have h2' : ∀ x, x ∈ range f ∪ range g := by {
    intro x
    unfold range
    unfold range at h2
    rw [h2]
    trivial
  }
  let L : Set α × Set β → Set γ := fun (y, z) ↦ ((f '' y) ∪ (g '' z))
  let R : Set γ → Set α × Set β := fun x ↦ (f⁻¹' x, g⁻¹' x)
  use L
  use R
  constructor
  . ext x y
    unfold R
    unfold L
    simp
    constructor
    . intro h
      obtain h|h:=h
      . obtain ⟨x1,hfx1, hyx1⟩:=h
        exact mem_of_eq_of_mem (id (Eq.symm hyx1)) hfx1
      . obtain ⟨x1,hfx1, hyx1⟩:=h
        exact mem_of_eq_of_mem (id (Eq.symm hyx1)) hfx1
    . intro hy
      have hxy: (∃xy, f xy = y) ∨ (∃xy, g xy = y) := by exact h2' y
      obtain ⟨xy, hxy⟩|⟨xy, hxy⟩:=hxy
      . left
        use xy
        constructor
        . rw [← hxy] at hy
          exact hy
        . exact hxy
      . right
        use xy
        constructor
        . rw [← hxy] at hy
          exact hy
        . exact hxy
  . unfold R
    unfold L
    ext x y
    . simp
      constructor
      intro h
      obtain ⟨x1, h⟩|⟨x1, h⟩:=h
      . have h': x1 = y := by exact (hf x1 y).1 h.2
        rw [h'] at h
        exact h.1
      . by_contra
        have h': f y ∈ range f ∩ range g := by{
          have h'g: f y ∈ range f:= by exact mem_range_self y
          have h'f: f y ∈ range g:= by {
            rw [← h.2]
            exact mem_range_self x1
          }
          exact mem_inter h'g h'f
        }
        simp_all only [setOf_true, ne_eq, mem_univ, implies_true, and_false, L, R]
      . intro h
        left
        use y
    . simp
      constructor
      intro h
      obtain ⟨x1, h⟩|⟨x1, h⟩:=h
      . by_contra
        have h': g y ∈ range f ∩ range g := by{
          have h'g: g y ∈ range g:= by exact mem_range_self y
          have h'f: g y ∈ range f:= by {
            rw [← h.2]
            exact mem_range_self x1
          }
          exact mem_inter h'f h'g
        }
        simp_all only [setOf_true, ne_eq, mem_univ, implies_true, and_false, L, R]
      . have h': x1 = y := by exact (hg x1 y).1 h.2
        rw [h'] at h
        exact h.1
      . intro h
        right
        use y
  }
