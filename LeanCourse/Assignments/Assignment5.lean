import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Nat BigOperators Set Finset
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 5 (mostly section 2) and 6 (mostly sections 1 and 2).

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises under "Exercises to hand-in". Deadline: 12.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- A note on definitions -/

lemma my_lemma : 3 + 1 = 4 := rfl
def myThree : ℕ := 3

/-
Tactics like `simp` and `rw` will not unfold definitions unless instructed to.
Tactics like `exact` and `apply` will unfold definitions if needed.
Uncomment the following lines one-by-one to see the difference. -/

example : myThree + 1 = 4 := by simp [myThree]
  -- rw [my_lemma] -- fails
  -- simp [my_lemma] -- fails to use `my_lemma`
  -- exact my_lemma -- works
  -- apply my_lemma -- works
  -- rw [myThree, my_lemma] -- works after instructing `rw` to unfold the definition
    -- works after instructing `simp` to unfold the definition
                    -- (it doesn't need `my_lemma` to then prove the goal)



/- The following exercises are to practice with casts. -/
example (n : ℤ) (h : (n : ℚ) = 3) : 3 = n := by {
  norm_cast at h
  exact (Eq.symm h)
  }

example (n m : ℕ) (h : (n : ℚ) + 3 ≤ 2 * m) : (n : ℝ) + 1 < 2 * m := by {
  norm_cast at *
  exact lt_of_succ_lt h
  }

example (n m : ℕ) (h : (n : ℚ) = m ^ 2 - 2 * m) : (n : ℝ) + 1 = (m - 1) ^ 2 := by {
  sorry
  }

example (n m : ℕ) : (n : ℝ) < (m : ℝ) ↔ n < m := by {
  norm_cast
  }

example (n m : ℕ) (hn : 2 ∣ n) (h : n / 2 = m) : (n : ℚ) / 2 = m := by {
  norm_cast
  }

example (q q' : ℚ) (h : q ≤ q') : exp q ≤ exp q' := by {
  rw [exp_le_exp]
  norm_cast
  }

example (n : ℤ) (h : 0 < n) : 0 < Real.sqrt n := by {
  refine sqrt_pos_of_pos ?_
  norm_cast
  }

/- Working with `Finset` is very similar to working with `Set`.
However, some notation, such as `f '' s` or `𝒫 s` doesn't exist for `Finset`. -/
example (s t : Finset ℕ) : (s ∪ t) ∩ t = (s ∩ t) ∪ t := by {
  ext x
  simp
  }

example {α β : Type*} (f : α → β) (s : Finset α) (y : β) : y ∈ s.image f ↔ ∃ x ∈ s, f x = y := by {
  simp
  }

/- `Disjoint` can be used to state that two (fin)sets are disjoint.
Use `Finset.disjoint_left` (or `Set.disjoint_left`) to unfold its definition.
If you have `x ∈ t \ s` apply `simp` first to get a conjunction of two conditions.
-/
example {α : Type*} (s t : Finset α) : Disjoint s (t \ s) := by {
  unfold Disjoint
  intro x hs ht
  simp at *
  calc x ⊆ s ∩ (t \ s):= by exact Finset.subset_inter hs ht
    _ = ∅ := by exact inter_sdiff_self s t
  }


/- Let's define the Fibonacci sequence -/
def fibonacci : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => fibonacci (n + 1) + fibonacci n

/- Prove the following exercises by induction. -/

example (n : ℕ) : ∑ i in range n, fibonacci (2 * i + 1) = fibonacci (2 * n) := by {
  induction n with
  | zero => rfl
  | succ n hi =>
    simp [fibonacci]
    rw [sum_range_succ, hi]
    ring
  }

example (n : ℕ) : ∑ i in range n, (fibonacci i : ℤ) = fibonacci (n + 1) - 1 := by {
  induction n with
  | zero => rfl
  | succ n hi =>
    simp [fibonacci]
    rw [sum_range_succ, hi]
    ring
  }

example (n : ℕ) : 6 * ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) := by {
  induction n with
  | zero => rfl
  | succ n hi =>
    rw [sum_range_succ]
    let z:=∑ x ∈ Finset.range (n + 1), x ^ 2
    calc 6*(z+(n + 1) ^ 2)=6 * z + 6 * (n + 1) ^ 2 := by exact Nat.mul_add 6 z ((n + 1) ^ 2)
    _ = n * (n + 1) * (2 * n + 1) + 6 * (n + 1) ^ 2 := by rw [hi]
    _ = (n + 1) * (n + 1 + 1) * (2 * (n + 1) + 1) := by ring
  }

def fac : ℕ → ℕ
  | 0       => 1
  | (n + 1) => (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2 ^ n ≤ fac (n + 1) := by {
  induction n with
  | zero => rw [fac]; rw[fac]; simp
  | succ n hi =>
    rw [fac]
    have h': 2≤ n+1+1 := by exact Nat.le_add_left 2 n
    calc 2^(n+1)=2*2^(n) := by ring
    _ ≤ (n+1+1)*2^n := by refine Nat.mul_le_mul_right (2 ^ n) h'
    _ ≤ (n + 1 + 1) * fac (n + 1) := by exact Nat.mul_le_mul_left (n + 1 + 1) hi
  }

example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by {
  induction n with
  | zero => rw[fac]; rfl
  | succ n hi =>
    rw [fac]
    rw [prod_range_succ]
    rw [hi]
    ring
  }

example (n : ℕ) : fac (2 * n) = fac n * 2 ^ n * ∏ i in range n, (2 * i + 1) := by {
  induction n with
  | zero => rw[fac]; rfl
  | succ n hi =>
    ring
    have h': fac (2 + n * 2) = fac (2*n+1+1):= by ring
    have h'': Finset.range (1 + n) = Finset.range (n + 1) := by{
      have h'1: 1+n=n+1 := by ring
      rw [h'1]
    }
    have h'': ∏ x ∈ Finset.range (1 + n), (2 * x + 1) = ∏ x ∈ Finset.range (n + 1), (2 * x + 1) := by rw[h'']
    rw [h'', prod_range_succ]
    calc fac (2 + n * 2) = (2*n+2)*fac (2 * n +1):= by rw [h'];rw [fac]
    _ = (2*n+2)*(2*n+1)*fac (2 * n) := by rw [fac];ring
    _ = (2*n+2)*(2*n+1)*fac n * 2 ^ n * ∏ i ∈ Finset.range n, (2 * i + 1):= by rw [hi];ring
    _ = ((n+1)*fac n) * (2 ^ n*2) * ((∏ i ∈ Finset.range n, (2 * i + 1))*(2*n+1)) := by ring
    _ = fac (n+1) * (2 ^ n*2) * ((∏ i ∈ Finset.range n, (2 * i + 1))*(2*n+1)) := by rw [fac];
    _ = fac (1 + n) * 2 ^ n * 2 * ((∏ x ∈ Finset.range n, (2 * x + 1)) * (2 * n + 1)) := by ring
  }





/- **Exercise**.
Define scalar multiplication of a real number and a `Point`. -/

@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

-- give definition here

def Point.mul (a b: Point) : ℝ := a.x*b.x+a.y*b.y+a.z*b.z

/- **Exercise**.Define Pythagorean triples, i.e. triples `a b c : ℕ` with `a^2 + b^2 = c^2`.
Give an example of a Pythagorean triple, and show that multiplying a Pythagorean triple by a
constant gives another Pythagorean triple. -/

-- give definition here

structure PythagoreanTriple extends Point where
  h_pyt : x*x + y*y = z*z

def miTriple : PythagoreanTriple where
  x:=3
  y:=4
  z:=5
  h_pyt:= by ring

def PythagoreanTriple.mul (n: ℝ) (a: PythagoreanTriple) : PythagoreanTriple where
  x:=n*a.x
  y:=n*a.y
  z:=n*a.z
  h_pyt:=by{
    ring
    calc n ^ 2 * a.x ^ 2 + n ^ 2 * a.y ^ 2 = n ^ 2 * (a.x*a.x + a.y*a.y) := by refine Mathlib.Tactic.Ring.add_overlap_pf n 2 ?pq_pf; ring
    _ = n ^ 2 * a.z ^ 2 := by rw [a.h_pyt]; ring
  }

/- Prove that triples of equivalent types are equivalent. -/

@[ext] structure Triple (α : Type*) where
  x : α
  y : α
  z : α

example (α β : Type*) (e : α ≃ β) : Triple α ≃ Triple β := sorry



/- 5. Show that if `G` is an abelian group then triples from elements of `G` is an abelian group. -/

class AbelianGroup' (G : Type*) where
  add (x : G) (y : G) : G
  comm (x y : G) : add x y = add y x
  assoc (x y z : G) : add (add x y) z = add x (add y z)
  zero : G
  add_zero : ∀ x : G, add x zero = x
  neg : G → G
  add_neg : ∀ x : G, add x (neg x) = zero

example (G : Type*) [AbelianGroup' G] : AbelianGroup' (Triple G) where
  add (a : Triple G) (b : Triple G) := {x := AbelianGroup'.add a.x b.x, y := AbelianGroup'.add a.y b.y, z := AbelianGroup'.add a.z b.z: Triple G}
  comm (a b: Triple G) := by simp_rw [AbelianGroup'.comm]
  assoc (a b c: Triple G) := by simp_rw [AbelianGroup'.assoc]
  zero := ⟨AbelianGroup'.zero, AbelianGroup'.zero, AbelianGroup'.zero⟩
  add_zero := by {
    intro x
    simp_rw [AbelianGroup'.add_zero]
  }
  neg  (a: Triple G) := ⟨AbelianGroup'.neg a.x, AbelianGroup'.neg a.y, AbelianGroup'.neg a.z⟩
  add_neg := by intro x;simp_rw [AbelianGroup'.add_neg]


/-! # Exercises to hand-in. -/

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

-- give the definition here
structure StrictBipointedType where
  type: Type
  x₀: type
  x₁: type
  h_strict: x₀ ≠ x₁

-- state and prove the lemma here

lemma strictBipointed (a: StrictBipointedType): ∀ z: a.type, z ≠ a.x₀ ∨ z ≠ a.x₁ := by{
  intro z
  by_contra h
  simp at h
  have h':= h.2
  rw [h.1] at h'
  exact a.h_strict h'
}

/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i in range (n + 1), (i : ℚ) ^ 3) = (∑ i in range (n + 1), (i : ℚ)) ^ 2 := by {
  induction n with
  | zero => simp
  | succ n hi =>
    sorry
  }

/-
Suppose `(A i)_i` is a sequence of sets indexed by a well-ordered type
(this is an order where every nonempty set has a minimum element).
We now define a new sequence by `C n = A n \ (⋃ i < n, A i)`.
In this exercise, we show that the new sequence is pairwise disjoint but has the same union as the
original sequence.
-/
lemma disjoint_unions {ι α : Type*} [LinearOrder ι] [wf : WellFoundedLT ι] (A C : ι → Set α)
  (hC : ∀ i, C i = A i \ ⋃ j < i, A j) : Pairwise (Disjoint on C) ∧ ⋃ i, C i = ⋃ i, A i := by {
  have h := wf.wf.has_min -- this hypothesis allows you to use well-orderedness
  unfold Pairwise
  unfold Disjoint
  simp
  have h'': ∀ i, A i \ ⋃ j_1, ⋃ (_ : j_1 < i), A j_1 ⊆ A i := by {
    intro i
    exact diff_subset
  }
  constructor
  . intro i j hij
    intro x hxi hxj
    have hij: j<i ∨ i<j := by exact lt_or_gt_of_ne fun a ↦ hij (id (Eq.symm a))
    obtain hij|hij:= hij
    . have hCi:= hC i
      have hCj:= hC j
      rw [hCi] at hxi
      rw [hCj] at hxj
      have h': A i \ ⋃ j, ⋃ (_ : j < i), A j ⊆ A i \ A j := by{
        apply diff_subset_diff_right ?h
        exact Set.subset_biUnion_of_mem hij
      }
      have hx: x ⊆ A j ∩ (A i \ A j) := by{
        apply Set.subset_inter (fun ⦃a⦄ a_1 ↦ h'' j (hxj a_1)) fun ⦃a⦄ a_1 ↦ h' (hxi a_1)
      }
      have h': A j ∩ (A i \ A j) = ∅ := by exact inter_diff_self (A j) (A i)
      rw [h'] at hx
      exact subset_eq_empty hx rfl
    . have hCi:= hC i
      have hCj:= hC j
      rw [hCi] at hxi
      rw [hCj] at hxj
      have h': A j \ ⋃ i, ⋃ (_ : i < j), A i ⊆ A j \ A i := by{
         refine diff_subset_diff_right ?h'
         exact Set.subset_biUnion_of_mem hij
      }
      have hx: x ⊆ A i ∩ (A j \ A i) := by{
        apply Set.subset_inter (fun ⦃a⦄ a_1 ↦ h'' i (hxi a_1)) fun ⦃a⦄ a_1 ↦ h' (hxj a_1)
      }
      have h': A i ∩ (A j \ A i) = ∅ := by exact inter_diff_self (A i) (A j)
      rw [h'] at hx
      exact subset_eq_empty hx rfl
  . ext x
    simp
    constructor
    . intro hc
      obtain ⟨i, hi⟩ := hc
      use i
      rw [hC i] at hi
      exact h'' i hi
    . intro hc
      obtain ⟨i, hi⟩ := hc
      let I:= {i | x∈ A i}
      have hI: I.Nonempty := by exact nonempty_of_mem hi
      have hI:= h I hI
      obtain ⟨i, hii⟩:= hI
      use i
      rw [hC i]
      apply (mem_diff x).mpr
      constructor
      . exact hii.1
      . by_contra h_contra
        simp at h_contra
        obtain ⟨j, hj1, hj2⟩:=h_contra
        exact hii.2 j hj2 hj1
  }



/- Next, we'll prove that if `2 ^ n - 1` is prime, then `n` is prime.
The first exercise is a preparation, and I've given you a skeleton of the proof for the
second exercise. Note how we do some computations in the integers, since the subtraction on `ℕ`
is less well-behaved.
(The converse is not true, because `89 ∣ 2 ^ 11 - 1`) -/

lemma not_prime_iff (n : ℕ) :
    ¬ Nat.Prime n ↔ n = 0 ∨ n = 1 ∨ ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ n = a * b := by {
  sorry
  }

lemma prime_of_prime_two_pow_sub_one (n : ℕ) (hn : Nat.Prime (2 ^ n - 1)) : Nat.Prime n := by {
  by_contra h2n
  rw [not_prime_iff] at h2n
  obtain rfl|rfl|⟨a, b, ha, hb, rfl⟩ := h2n
  · sorry
  · sorry
  have h : (2 : ℤ) ^ a - 1 ∣ (2 : ℤ) ^ (a * b) - 1
  · rw [← Int.modEq_zero_iff_dvd]
    calc (2 : ℤ) ^ (a * b) - 1
        ≡ ((2 : ℤ) ^ a) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
      _ ≡ (1 : ℤ) ^ b - 1 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
      _ ≡ 0 [ZMOD (2 : ℤ) ^ a - 1] := by sorry
  have h2 : 2 ^ 2 ≤ 2 ^ a := by sorry
  have h3 : 1 ≤ 2 ^ a := by sorry
  have h4 : 2 ^ a - 1 ≠ 1 := by zify; simp [h3]; linarith
  have h5 : 2 ^ a - 1 < 2 ^ (a * b) - 1 := by
    apply tsub_lt_tsub_right_of_le h3
    sorry
  have h6' : 2 ^ 0 ≤ 2 ^ (a * b) := by sorry
  have h6 : 1 ≤ 2 ^ (a * b) := h6'
  have h' : 2 ^ a - 1 ∣ 2 ^ (a * b) - 1 := by norm_cast at h
  rw [Nat.prime_def_lt] at hn
  sorry
  }

#eval (a ^ 2 + b)*(b ^ 2 + a)

/- Prove that for positive `a` and `b`, `a^2 + b` and `b^2 + a` cannot both be squares.
Prove it on paper first! -/
lemma not_isSquare_sq_add_or (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬ IsSquare (a ^ 2 + b) ∨ ¬ IsSquare (b ^ 2 + a) := by {
  unfold IsSquare
  by_contra hc
  simp at hc
  obtain ⟨xa, ha⟩:= hc.1
  obtain ⟨xb, hb⟩:= hc.2
  sorry
  }


/-- Let's prove that the positive reals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosReal : Type := {x : ℝ // 0 < x}

def groupPosReal : Group PosReal where
inv (x: PosReal):= sorry --((1:PosReal)/x: PosReal)
inv_mul_cancel:=sorry



/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] card_powerset
#check Finset.induction

lemma fintype_card_powerset (α : Type*) (s : Finset α) :
    Finset.card (powerset s) = 2 ^ Finset.card s := by {
  induction s using Finset.induction with
  | empty => simp
  | @insert x s hxs ih =>
    rw [card_insert_of_not_mem hxs]
    sorry
  }
