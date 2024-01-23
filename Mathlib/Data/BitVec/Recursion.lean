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
universe u v

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
  simp only [nil, BitVec.zero, toNat_inj] at this
  simp only [this]

/-- Two bitvectors are equal iff all their bits are two by two equal -/
theorem bit_to_bit_eq {xs ys : BitVec n} :
    xs = ys ↔ ∀ i : Nat, xs.getLsb i = ys.getLsb i := by
  apply Iff.intro
  case mp =>
    intro h
    simp [h]
  case mpr =>
    intro h
    simp [getLsb_eq_testBit] at h
    have : xs.toNat = ys.toNat := Nat.eq_of_testBit_eq h
    rw [toNat_inj] at this
    exact this

/-- Get the head and tail of a BitVec (head being the least significant bit) -/
def head (xs : BitVec (n + 1)) : Bool :=
  getLsb xs n

def tail (xs : BitVec (n + 1)) : BitVec n :=
  extractLsb' 0 n xs

theorem cons_head_tail_eq {n : Nat} (x : BitVec (n + 1)) :
    x = cons (head x) (tail x) := by
  rw [bit_to_bit_eq]
  intro i
  have : getLsb (cons (head x) (tail x)) i =
    if i = n then head x else getLsb (tail x) i := by
    simp [getLsb_cons]
  rw [this]
  if h : i = n then
    rw [h]
    simp [head]
  else
    rw [if_neg h]
    simp [tail, extractLsb', getLsb_eq_testBit, Nat.testBit_mod_two_pow]
    have prop : x.toNat < 2 ^ (n + 1) := x.toFin.prop
    if h' : i > n then
      have h_lt : 2 ^ (n + 1) ≤ 2 ^ i := by
        have : n + 1 ≤ i := by
          rw [Nat.succ_le_iff]
          exact h'
        exact Nat.pow_le_pow_of_le_right (Nat.zero_lt_succ _) this
      have : x.toNat.testBit i = false := by
        simp only [Nat.testBit_lt_two, Nat.lt_of_lt_of_le (prop) h_lt]
      simp [this]
    else
      have : i < n := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h') h
      simp [this]

theorem head_cons (x : Bool) (xs : BitVec n) :
    head (cons x xs) = x := by
  simp [head, getLsb_cons]

theorem tail_cons {x : Bool} {xs : BitVec n} :
    tail (cons x xs) = xs := by
  simp [tail, extractLsb', bit_to_bit_eq]
  intro i
  simp [getLsb_eq_testBit, Nat.testBit_mod_two_pow]
  have prop : xs.toNat < 2 ^ n := xs.toFin.prop
  if h : i ≥ n then
    simp [Nat.not_lt_of_ge h]
    have h_lt : 2 ^ n ≤ 2 ^ i := by
      exact Nat.pow_le_pow_of_le_right (Nat.zero_lt_succ _) h
    simp only [Nat.testBit_lt_two, Nat.lt_of_lt_of_le (prop) h_lt]
  else
    have h' : i < n := Nat.lt_of_not_ge h
    simp [Nat.testBit_lt_two, h']
    rw [<-getLsb_eq_testBit, <-getLsb_eq_testBit, getLsb_cons]
    have : ¬i = n := by simp [Nat.ne_of_lt h']
    simp [this]

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
  simp only [consRecursion]
  simp only [Eq.mpr]
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

/-!
  ## Properties over `cons`
-/

variable {m : Nat}

theorem head_tail_eq {xs ys : BitVec (n + 1)} :
    xs = ys ↔ head xs = head ys ∧ tail xs = tail ys := by
  apply Iff.intro
  case mp =>
    intro h
    simp [h]
  case mpr =>
    intro h
    have H : head xs = head ys := h.left
    have T : tail xs = tail ys := h.right
    have : xs = cons (head ys) (tail ys) := by
      rw [←T, ←H]
      exact cons_head_tail_eq xs
    rw [this, ←cons_head_tail_eq]

end BitVec
