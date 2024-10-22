import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 2, sections 2, 3, 4 and 5
  Read chapter 3, sections 1, 4.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 22.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

example {a b : ℝ} (h1 : a + 2 * b = 4) (h2 : a - b = 1) : a = 2 := by {
  have ha: b = a-1:=
   calc b = b + 0 :=  by ring
   _ = b + a - a:= by ring
   _ = -(a - b) + a := by ring
   _= -(1) + a := by rw[h2]
   _= -1 + a := by ring
   _= a -1 := by ring
  rw [ha] at h1
  ring at h1
  linarith -- I know I could've done it before but I wanted to try using have
  }

example {u v : ℝ} (h1 : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by {
  rw[←h1]
  linarith
  }

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by {

    refine add_le_add ?h₁ ?h₂
    linarith
    have ha : x ≤ y+2 := by linarith
    exact exp_le_exp.mpr ha
  }

/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by {
  constructor
  · exact fun a_1 ↦ le_tsub_of_add_le_right a_1
  . exact fun a_1 ↦  le_sub_iff_add_le.mp a_1
  }

/- Note: for purely numerical problems, you can use `norm_num`
(although `ring` or `linarith` also work in some cases). -/
example : 2 + 3 * 4 + 5 ^ 6 ≤ 7 ^ 8 := by norm_num
example (x : ℝ) : (1 + 1) * x + (7 ^ 2 - 35 + 1) = 2 * x + 15 := by norm_num

/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example (x : ℝ) (hx : x = 3) : x ^ 2 + 3 * x - 5 = 13 := by
  rw [hx]
  norm_num

example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by {
  calc n - m^2  ≤  n - 0 := by{
    gcongr
    exact sq_nonneg m
  }
  _ ≤ n+3 := by linarith
  }

example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by {
  specialize h 2
  ring at h
  gcongr
  }

example {a₁ a₂ a₃ b₁ b₂ b₃ : ℝ} (h₁₂ : a₁ + a₂ + 1 ≤ b₁ + b₂) (h₃ : a₃ + 2 ≤ b₃) :
  exp (a₁ + a₂) + a₃ + 1 ≤ exp (b₁ + b₂) + b₃ + 1 := by {
  have ha : a₃< b₃:= by {linarith }
  have hb : a₁ + a₂ < b₁ + b₂:= by {linarith }
  gcongr
  }

/- Divisibility also gives an order. Warning: divisibility uses a unicode character,
which can be written using `\|`. -/

/-- Prove this using calc. -/
lemma exercise_division (n m k l : ℕ) (h₁ : n ∣ m) (h₂ : m = k) (h₃ : k ∣ l) : n ∣ l := by {
  calc n ∣ m := by exact h₁
  _ = k := by rw[h₂]
  _ ∣  l := by  exact h₃
  }


/- We can also work with abstract partial orders. -/

section PartialOrder

variable {X : Type*} [PartialOrder X]
variable (x y z : X)

/- A partial order is defined to be an order relation `≤` with the following axioms -/
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

/- every preorder comes automatically with an associated strict order -/
example : x < y ↔ x ≤ y ∧ x ≠ y := lt_iff_le_and_ne

/- the reverse order `≥`/`>` is defined from `≤`/`<`.
In Mathlib we usually state lemmas using `≤`/`<` instead of `≥`/`>`. -/
example : x ≥ y ↔ y ≤ x := by rfl
example : x > y ↔ y < x := by rfl


example (hxy : x ≤ y) (hyz : y ≤ z) (hzx : z ≤ x) : x = y ∧ y = z ∧ x = z := by {
  have h2 : x = y := by rw[le_antisymm hxy (le_trans hyz hzx)]
  have h1 : x = z := by rw[le_antisymm hzx (le_trans hxy hyz)]
  have h3 : y = z := by rw[le_antisymm hyz (le_trans hzx hxy)]
  constructor
  · exact h2
  constructor
  · exact h3
  · exact h1
  }


end PartialOrder


/-! # Exercises to hand-in. -/

/- Prove this using a calculation. -/
lemma exercise_calc_real {t : ℝ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 := by {
  calc t^2 - 3 * t - 17 ≥ 10^2 - 3 * 10 - 17 := by {
    apply add_le_add
    nlinarith [ht]
    linarith }
  _ = 53 := by norm_num
  _  ≥ 5 := by norm_num
  }

/- Prove this using a calculation.
The arguments `{R : Type*} [CommRing R] {t : R}` mean
"let `t` be an element of an arbitrary commutative ring `R`." -/
lemma exercise_calc_ring {R : Type*} [CommRing R] {t : R} (ht : t ^ 2 - 4 = 0) :
    t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = 10 * t + 2 := by {
    have ha : t^2 = 4 := by apply eq_of_sub_eq_zero ht
    calc t ^ 4 + 3 * t ^ 3 - 3 * t ^ 2 - 2 * t - 2 = t^2* t^2 +  3* t * t^2 - 3 * t ^ 2 - 2 * t - 2 := by ring
    _ = (4)* (4) +  3* t * (4) - 3 * (4) - 2 * t - 2 := by rw[ha]
    _ = 16 + 12*t-12 -2*t -2 := by ring
    _ = 10* t + 2 := by ring
  }

/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by {
  have ha : n ≤ 2 := by linarith [sq_nonneg m, h]

  calc n+1 ≤ 2+1 := by exact (Int.add_le_add_iff_right 1).mpr ha
  _ = 3 := by ring
  _ ≤ 3 + k ^ 2 := by linarith [sq_nonneg k]

  }



section Min
variable (a b c : ℝ)

/- The following theorems characterize `min`.
Let's this characterization it to prove that `min` is commutative and associative.
Don't use other lemmas about `min` from Mathlib! -/
#check (min : ℝ → ℝ → ℝ)
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

lemma exercise_min_comm : min a b = min b a := by {
  have h₁ : min a b ≤ min b a := le_min (min_le_right a b) (min_le_left a b)
  have h₂ : min b a ≤ min a b := le_min (min_le_right b a) (min_le_left b a)
  rw[le_antisymm h₁ h₂]
  }

lemma exercise_min_assoc : min a (min b c) = min (min a b) c := by {

  have h₁ : min a (min b c) ≤ min (min a b) c:= by{
    apply le_min
    apply le_min
    apply min_le_left
    have hb : min a (min b c )≤ b := by{
      calc  min a (min b c ) ≤ min b c := by apply min_le_right
      _ ≤ b := by apply min_le_left
    }
    apply hb
    calc  min a (min b c ) ≤ min b c := by apply min_le_right
      _ ≤ c := by apply min_le_right
  }
  have h₂ :  min (min a b) c ≤ min a (min b c):= by{
    apply le_min
    have ha : min (min a b) c ≤ a := by{
      calc  min (min a b) c≤ (min a b) := by apply min_le_left
      _ ≤ a := by apply min_le_left
    }
    apply ha
    have hc : min (min a b) c ≤ c := by apply min_le_right
    have hb : min (min a b) c ≤ b := by{
      calc  min (min a b) c≤ (min a b) := by apply min_le_left
      _ ≤ b := by apply min_le_right
    }
    apply le_min
    apply hb
    apply hc
  }
  rw[le_antisymm h₁ h₂]
  }-- I'm sure there is an easier way, but I'm still not very familiar with lean syntax

end Min

/- Prove that the following function is continuous.
You can use `Continuous.div` as the first step,
and use the search techniques to find other relevant lemmas.
`ne_of_lt`/`ne_of_gt` will be useful to prove the inequality. -/
lemma exercise_continuity : Continuous (fun x ↦ (sin (x ^ 5) * cos x) / (x ^ 2 + 1)) := by {
  apply Continuous.div
  {
    apply Continuous.mul
    {
      refine Continuous.comp' ?hf.hf.hg ?hf.hf.hf
      · apply continuous_sin
      · apply continuous_pow 5
    }
    · apply continuous_cos
  }
  {
    exact Continuous.add (continuous_pow 2) continuous_const
  }
  {
    intro x
    have : x^2 + 1 = 0 → x^2 = -1:= by{
      intro h
      linarith -- This will simplify to show contradiction
    }
    have : x^2 ≥ 0 := pow_two_nonneg x
    linarith
  }

  }

/- Prove this only using `intro`/`constructor`/`obtain`/`exact` -/
lemma exercise_and_comm : ∀ (p q : Prop), p ∧ q ↔ q ∧ p := by {
  intro hp hq
  constructor
  · exact fun a ↦ id (And.symm a)
  · exact fun a ↦ id (And.symm a)
  }


/-- Prove the following properties of nondecreasing functions. -/
def Nondecreasing (f : ℝ → ℝ) : Prop := ∀ x₁ x₂ : ℝ, x₁ ≤ x₂ → f x₁ ≤ f x₂

lemma exercise_nondecreasing_comp (f g : ℝ → ℝ) (hg : Nondecreasing g) (hf : Nondecreasing f) :
    Nondecreasing (g ∘ f) := by {
  unfold Nondecreasing
  simp
  unfold Nondecreasing at hf hg
  intro x y h
  specialize hg (f x) (f y)
  specialize hf x y
  specialize hf h
  specialize hg hf
  exact hg
  }


/-- Note: `f + g` is the function defined by `(f + g)(x) := f(x) + g(x)`.
  `simp` can simplify `(f + g) x` to `f x + g x`. -/
lemma exercise_nondecreasing_add (f g : ℝ → ℝ) (hf : Nondecreasing f) (hg : Nondecreasing g) :
    Nondecreasing (f + g) := by {
  unfold Nondecreasing
  simp
  unfold Nondecreasing at hf hg
  intro x y h
  specialize hg x y
  specialize hf x y
  specialize hg h
  specialize hf h
  linarith
  }



/-- Prove the following property of even. -/
def EvenFunction (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

lemma exercise_even_iff (f g : ℝ → ℝ) (hf : EvenFunction f) :
    EvenFunction (f + g) ↔ EvenFunction g := by {
  constructor
  . intro (hfg: EvenFunction (f+g))
    unfold EvenFunction
    unfold EvenFunction at hf
    unfold EvenFunction at hfg
    intro x
    simp at hfg
    specialize hf x
    specialize hfg x
    linarith
  . intro (hg: EvenFunction g)
    unfold EvenFunction
    unfold EvenFunction at hg hf
    intro x
    simp
    specialize hg x
    specialize hf x
    linarith
  }
