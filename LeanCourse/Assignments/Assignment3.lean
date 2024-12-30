import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real Function Set Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 2, 3, 5, 6.
  Read chapter 4, section 1.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 29.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example {p : ℝ → Prop} (h : ∀ x, p x) : ∃ x, p x := by {
  use 1
  specialize h 1
  exact h
  }


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by {
  intro hx
  obtain ⟨x₀, hx₀⟩ := hx
  use x₀
  specialize h x₀
  exact h hx₀
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by {
  constructor
  . intro hx x px
    have epx : (∃x, p x) := by exact Exists.intro x px
    exact hx epx
  . intro hx ex
    obtain ⟨x, hhx⟩ := ex
    specialize hx x
    exact hx hhx
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by {
      constructor
      . intro hx
        obtain ⟨x, hpx, hr⟩ := hx
        constructor
        . use x
        . exact hr
      . intro h
        obtain ⟨hpx, hr⟩ := h
        obtain ⟨x, hpx⟩ := hpx
        use x
  }

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
  constructor
  . intro hpx
    by_contra h
    obtain ⟨x, hpx⟩ := hpx
    specialize h x
    exact h hpx
  . intro hf
    by_contra he
    sorry
  }

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by {
  unfold SequentialLimit
  intro ε hε
  use 0
  intro n hn
  simp
  exact hε
  }

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m k : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by {
  calc (n)! ∣ (m)! := by exact factorial_dvd_factorial h
  _ ∣ (m+1)! := by exact Dvd.intro_left m.succ rfl
  }

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by {
  sorry
  }

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by {
  sorry
  }

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
  sorry
  }

example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by {
  sorry
  }

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by {
  sorry
  }

end Set

/-! # Exercises to hand-in. -/


/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
  constructor
  . intro h
    obtain ⟨x, hpx|hqx⟩ := h
    . left
      use x
    . right
      use x
  . intro h
    obtain hpx|hqx := h
    . obtain ⟨x, h⟩ := hpx
      use x
      left
      exact h
    . obtain ⟨x, h⟩ := hqx
      use x
      right
      exact h
  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by {
  unfold SurjectiveFunction
  unfold SurjectiveFunction at hf
  constructor
  . intro h y
    simp at h
    specialize h y
    obtain ⟨x, hx⟩ := h
    use (f x)
  . intro h y
    simp
    specialize h y
    obtain ⟨x, hx⟩:=h
    specialize hf x
    obtain ⟨x', hx'⟩:=hf
    use x'
    rw [hx']
    exact hx
  }

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {
  unfold SurjectiveFunction
  unfold SurjectiveFunction at hf
  ring
  intro y
  specialize hf ((y-1)/2)
  obtain ⟨x, hx⟩:= hf
  use (x-12)/3
  ring
  rw [hx]
  ring
  }

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  unfold Surjective
  by_contra h
  let R := {x | x ∉ f x}
  specialize h R
  obtain ⟨a, fa⟩:=h
  by_cases ha : a∈ R
  . have nha : a ∉ (f a) := by exact ha
    rw [← fa] at ha
    exact nha ha
  . rw [← fa] at ha
    have nha : a ∈ R := by exact ha
    rw [fa] at ha
    exact ha nha
  }

end Surjectivity

/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {
  unfold SequentialLimit at hs ht
  unfold SequentialLimit
  intro ε hε
  simp
  specialize hs (ε/2)
  specialize ht (ε/2)
  have ε2 : ε / 2 > 0 := by exact half_pos hε
  have hs := hs ε2
  have ht := ht ε2
  obtain ⟨ns, hs⟩:= hs
  obtain ⟨nt, ht⟩:= ht
  let N := max ns nt
  have h1 : N≥ ns := by exact Nat.le_max_left ns nt
  have h2 : N≥ nt := by exact Nat.le_max_right ns nt
  use N
  intro n hn
  specialize ht n
  specialize hs n
  have hNt: n ≥ nt := by exact Nat.le_trans h2 hn
  have hNs: n ≥ ns := by exact Nat.le_trans h1 hn
  have ht := ht hNt
  have hs := hs hNs
  calc |s n + t n - (a + b)| = |(t n - b) + (s n - a)| := by ring
  _ ≤ |t n - b| + |s n - a| := by exact abs_add_le (t n - b) (s n - a)
  _ < (ε / 2) + (ε / 2) := by gcongr
  _ = ε := by ring
  }

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by {
  unfold SequentialLimit at *
  intro ε hε
  by_cases hc: c=0
  . use 0
    intro n hn
    rw [hc]
    simp
    exact hε
  . specialize hs (ε/|c|)
    have hε2 : (ε/|c|)>0 := by{
      refine div_pos hε ?hb
      simp
      exact hc
    }
    have hs:= hs hε2
    obtain ⟨N, hs⟩ := hs
    use N
    intro n hn
    specialize hs n
    have hs:= hs hn
    simp
    calc |c * s n-c*a|=|c*(s n-a)| := by ring
    _ = |c| * (|s n-a|):= by exact abs_mul c (s n - a)
    _ < |c| * (ε / |c|) := by gcongr
    _ = |c| * (1/|c|) * ε:= by ring
    _= ε := by field_simp
  }





section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by {
  unfold EventuallyGrowsFaster
  intro k
  use k
  intro n hn
  simp
  gcongr
  }

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by {
  unfold EventuallyGrowsFaster
  unfold EventuallyGrowsFaster at h₂ h₁
  intro k
  specialize h₁ k
  specialize h₂ k
  obtain ⟨N1, hn1⟩ := h₁
  obtain ⟨N2, hn2⟩ := h₂
  let N := max N1 N2
  have h1 : N≥ N1 := by exact Nat.le_max_left N1 N2
  have h2 : N≥ N2 := by exact Nat.le_max_right N1 N2
  use N
  intro n hn
  specialize hn1 n
  specialize hn2 n
  have h1 : n ≥ N1:= by linarith
  have h2 : n ≥ N2:= by linarith
  simp
  have hn1 := hn1 h1
  have hn2 := hn2 h2
  calc k * (t₁ n + t₂ n) = k*t₁ n + k* t₂ n:= by ring
  _ ≤ s₁ n + k* t₂ n := by gcongr
  _ ≤ s₁ n + s₂ n := by gcongr
  }

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  unfold EventuallyGrowsFaster
  simp
  use (fun n ↦ (n)!)
  constructor
  · intro k
    use k
    intro n hn
    ring
    calc k * n ! ≤ n*n ! := by gcongr
    _ ≤ (n)* ((n)!) + n !:= by linarith
    _ = (n+1)*(n !) := by linarith
    _ = (n + 1)! := by exact rfl
    _ = (1 +n)! := by ring
  · intro n
    exact factorial_ne_zero n



  }

end Growth
