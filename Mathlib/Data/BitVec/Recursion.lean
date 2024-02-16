import Mathlib.Data.BitVec.Defs
import Mathlib.Data.BitVec.Lemmas
import Mathlib.Data.Vector

/-!
  A `Bitvec n` is morally a sequence of `n` bits.
  This file establishes a way to shift to this perspective by proving the equivalence between
  `Bitvec n` and `Vector bool n`.
  Furthermore, we show how various (arithmetic) operations on bitvectors relate to a naive
  bit-by-bit implementation of those operations using the vector perspective.
-/

namespace Std.BitVec

variable {n : Nat}
universe u

/-
  ## Pseudo constructors
-/

/-- There is only one `empty` bitvector, namely, `nil` -/
theorem zero_length_eq_nil :
    ∀ (xs : BitVec 0), xs = nil := by
  intro xs
  have : xs.toNat < 2 ^ 0 := xs.toFin.prop
  simp only [Nat.pow_zero, Nat.lt_one_iff] at this
  have : xs.toNat = nil.toNat := this
  simp only [nil, toNat_inj] at this
  simp only [this]

/-- Two bitvectors are equal iff all their "bits" are two by two equal -/
theorem bit_to_bit_eq {xs ys : BitVec n} :
    xs = ys ↔ ∀ i : Nat, xs.getLsb i = ys.getLsb i := by
  apply Iff.intro <;> intro h
  case mp =>
    simp only [h, implies_true]
  case mpr =>
    have : xs.toNat = ys.toNat := Nat.eq_of_testBit_eq h
    simp only [<-toNat_inj, this]

/-- Get the `head` and `tail` of a bitvector (head being the least significant bit) -/
def head (xs : BitVec (n + 1)) : Bool :=
  getLsb xs n

def tail (xs : BitVec (n + 1)) : BitVec n :=
  extractLsb' 0 n xs

/-- A bitvector is the `cons` of its `head` and its `tail` --/
theorem cons_head_tail_eq {n : Nat} (x : BitVec (n + 1)) :
    x = cons (head x) (tail x) := by
  rw [bit_to_bit_eq]
  intro i
  rw [getLsb_cons]
  if h : i = n then
    simp only [h, head, if_true]
  else
    simp only [h, tail, extractLsb', if_false, Nat.shiftRight_zero, ofNat_toNat, getLsb_truncate]
    if h' : i < n then
      simp only [h', decide_True, Bool.true_and]
    else
      simp only [h', decide_False, Bool.false_and]
      have : i >= n + 1 := by
        have : n <= i := by simp only [Nat.ge_of_not_lt h']
        have hrefl : ¬n = i := by
          intro hr'
          apply h
          exact Eq.symm hr'
        exact Nat.succ_le_of_lt (Nat.lt_of_le_of_ne this hrefl)
      rw [getLsb_ge x i (this)]

theorem head_cons (x : Bool) (xs : BitVec n) :
    head (cons x xs) = x := by
  simp only [head, getLsb_cons, if_true]

theorem tail_cons {x : Bool} {xs : BitVec n} :
    tail (cons x xs) = xs := by
  simp only [tail, extractLsb', bit_to_bit_eq]
  intro i
  if h : i >= n then
    simp only [toNat_cons, Nat.shiftRight_zero, ge_iff_le, h, getLsb_ge]
  else
    simp only [getLsb, toNat_cons, Nat.shiftRight_zero, toNat_ofNat, Nat.testBit_mod_two_pow,
      Nat.lt_of_not_ge h, decide_True, Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le, h,
      decide_False, Bool.false_and, Bool.false_or, Bool.true_and]

/-!
  ## Induction principles
-/

/-- A custom recursion principle for bitvectors in terms of `nil` and `cons` -/
@[elab_as_elim]
def consRecursion {motive : {n : Nat} → BitVec n → Sort u}
    (nil : motive nil)
    (ind : {n : Nat} → (x : Bool) → (xs : BitVec n) → motive xs → motive (cons x xs))
    {n : Nat} : ∀ xs : BitVec n, motive xs :=
  fun xs => by
    match n with
    | 0 =>
      have : xs = .nil := by
        simp only [zero_length_eq_nil]
      rw [this]
      exact nil
    | Nat.succ n =>
      rw [cons_head_tail_eq xs]
      exact ind (head xs) (tail xs) (consRecursion nil ind (tail xs))

@[simp]
theorem consRecursion_nil {motive nil ind} :
    consRecursion (motive:=motive) nil ind .nil = nil := by
  rfl

@[simp]
theorem consRecursion_cons {motive nil ind} {x : Bool} {xs : BitVec n} :
    consRecursion (motive:=motive) nil ind (cons x xs)
    = ind x xs (consRecursion nil ind xs) := by
  apply eq_of_heq
  simp only [consRecursion, Eq.mpr]
  apply HEq.trans (eqRec_heq' _ _)
  rw [head_cons, tail_cons]

/-
  `consRecursion` is a so-called custom recursion principle, which allows us to pretend that
  `BitVec` is almost an inductive type, with `nil` and `cons` as its constructors.

  For example, in proofs (using tactic mode) about some `xs : BitVec n`, we can write
  ```lean
  induction xs using consRecursion
  ```
  And the goal would be split in two cases, one for `nil` and one for `cons`, with an induction
  hypothesis for the second goal.

  This is why recursion principles are also sometimes called induction principles.
  However, they are also useful beyond proofs. A recursion principle can be used to define a
  structurally recursive function on bitvectors.
  That is, in `let f := consRecursion h_nil h_cons`, the `h_nil` argument gives the return value of
  `f nil`, while `h_cons` is a function that maps `x`, `xs` and `f xs` to the return value of
  `f (cons x xs)`
-/

/-- Two bitvectors are equal if their heads and tails are equal --/
theorem head_tail_eq {xs ys : BitVec (n + 1)} :
    xs = ys <-> head xs = head ys ∧ tail xs = tail ys := by
  apply Iff.intro <;> intro h
  case mp =>
    simp only [h, and_self]
  case mpr =>
    have : xs = cons (head ys) (tail ys) := by
      rw [<-h.left, <-h.right]
      exact cons_head_tail_eq xs
    rw [this, <-cons_head_tail_eq]

end BitVec
