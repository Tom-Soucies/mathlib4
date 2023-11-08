import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Vector

#check Vector.mapAccumr

#align_import data.Bitvec.core from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"
/-!
  A `Bitvec n` is morally a sequence of `n` bits.
  This file establishes a way to shift to this perspective by proving the equivalence between
  `Bitvec n` and `Vector bool n`.
  Furthermore, we show how various (arithmetic) operations on Bitvectors relate to a naive
  bit-by-bit implementation of those operations using the vector perspective.
-/

namespace Bitvec

variable {n : Nat}
universe u v

/-
  ## Pseudo constructors
-/

/-- The empty Bitvector -/
def nil : Bitvec 0 :=
  Bitvec.zero 0

/-- Prepend a single bit to the front of a Bitvector. The new bit is the most significant bit -/
def cons (x : Bool) (xs : Bitvec n) : Bitvec (n+1) :=
  Vector.cons x xs

-- /-- Append a single bit to the end of a Bitvector. The new bit is the least significant bit -/
-- def concat (xs : Bitvec n) (x : Bool) : Bitvec (n+1) :=
--   xs.append (Bitvec.fill 1 x)

/-- There is only one `empty` Bitvector, namely, `nil` -/
theorem zero_length_eq_nil :
    ∀ (xs : Bitvec 0), xs = nil := by simp

/-!
  ## Induction principles
-/

/-- A custom recursion principle for Bitvectors in terms of `nil` and `cons` -/
@[elab_as_elim]
def consRecursion {motive : {n : Nat} → Bitvec n → Sort u}
    (nil : motive nil)
    (cons : {n : Nat} → (x : Bool) → (xs : Bitvec n) → motive xs → motive (cons x xs))
    {n : Nat} (xs : Bitvec n) : motive xs :=
  /-
    This one might be a bit hard to prove.
    For now, the `consRecursion_nil` and `consRecursion_cons` theorems fully specify how
    `consRecursion` should behave, and it is enough to use those in proofs about definitions using
    `consRecursion`
  -/
  sorry

@[simp]
theorem consRecursion_nil {motive nil cons} :
    consRecursion (motive:=motive) nil cons .nil = nil := by
  sorry

@[simp]
theorem consRecursion_cons {motive nil cons} {x : Bool} {xs : Bitvec n} :
    consRecursion (motive:=motive) nil cons (Bitvec.cons x xs)
    = cons x xs (consRecursion nil cons xs) := by
  sorry

/-
  `consRecursion` is a so-called custom recursion principle, which allows us to pretend that
  `Bitvec` is almost an inductive type, with `nil` and `cons` as its constructors.

  For example, in proofs (using tactic mode) about some `xs : Bitvec n`, we can write
  ```lean
  induction xs using consRecursion
  ```
  And the goal would be split in two cases, one for `nil` and one for `cons`, with an induction
  hypothesis for the second goal.

  This is why recursion principles are also sometimes called induction principles.
  However, they are also useful beyond proofs. A recursion principle can be used to define a
  structurally recursive function on Bitvectors.
  That is, in `let f := consRecursion h_nil h_cons`, the `h_nil` argument gives the return value of
  `f Bitvec.nil`, while `h_cons` is a function that maps `x`, `xs` and `f xs` to the return value of
  `f (Bitvec.cons x xs)`
-/


/-!
  ## Equivalence
-/

/-- Turn a Bitvector into a vector of bools of the same length -/
def asVector {n : Nat} : Bitvec n → Vector Bool n :=
  fun xs =>
    consRecursion
      (Vector.nil)
      (fun x _ xs => Vector.cons x xs)
      xs

/-- Turn a vector of bools into a Bitvector of the same length -/
def ofVector {n : Nat} : Vector Bool n → Bitvec n :=
  fun x =>
    match n with
    | 0 => nil
    | Nat.succ _ => cons (Vector.head x) (ofVector <| Vector.tail x)

/-- Distribution of vectorEquiv over cons -/
theorem asVector_cons {x : Bool} {xs : Bitvec n} :
    asVector (cons x xs) = Vector.cons x (asVector xs) := by
  simp only [asVector, ofVector, consRecursion_cons]

theorem ofVector_cons {x : Bool} {xs : Vector Bool n} :
    ofVector (Vector.cons x xs) = cons x (ofVector xs) := by
  simp only [ofVector, asVector, consRecursion_cons]
  have H0 : Vector.head (Vector.cons x xs) = x := rfl
  have H1 : Vector.tail (Vector.cons x xs) = xs := rfl
  rw [H0, H1]

def vectorEquiv {n : Nat} : Bitvec n ≃ Vector Bool n where
  toFun := asVector
  invFun := ofVector
  left_inv := fun xs => by
    induction xs using consRecursion
    case nil => rfl
    case _ _ _ ih =>
      simp only [asVector] at ih
      simp only [asVector, consRecursion_cons, ofVector_cons, ih]
  right_inv := fun x => by
    induction n
    case zero => simp only [ofVector, asVector, Vector.eq_nil]
    case _ _ ih =>
      simp [ofVector, asVector_cons, ofVector_cons, ih]

variable {m : Nat}

/-- Get the head and tail of a Bitvec (head being the least significant bit) -/
def head : Bitvec (n+1) → Bool :=
  fun xs => Vector.head xs.asVector

def tail : Bitvec (n + 1) → Bitvec n :=
  fun xs => Vector.tail xs.asVector

/-!
  ## Constants
-/

theorem zero_asVector :
    (Bitvec.zero m).asVector = Vector.replicate m false := by
  induction m
  case zero =>
    apply vectorEquiv.symm.injective
    simp
  case succ m ih =>
    have : asVector (Bitvec.zero (Nat.succ m)) = Vector.cons false (asVector (Bitvec.zero m)) := by
      have : Bitvec.zero (Nat.succ m) = cons false (Bitvec.zero m) := by rfl
      rw [this]
      simp only [asVector_cons]
    rw [this]
    have : Vector.replicate (Nat.succ m) false = Vector.cons false (Vector.replicate m false) := by
      simp only [Vector.replicate, Vector.cons, List.replicate]
    rw [this]
    simp only [ih]

/-!
  ## Bitwise
-/

theorem complement_asVector {x : Bitvec n} :
    (~~~x) = (ofVector <| Vector.map not x.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [ofVector, asVector, Vector.eq_nil]
  case cons b x ih =>
    simp only [ofVector_cons, asVector_cons, Vector.map_cons]
    have : ~~~cons b x = cons (!b) (~~~x) := by
      simp only [Complement.complement]
      simp only [Bitvec.cons]
      rfl
    rw [this, ih]

variable {x y : Bitvec n}

theorem and_asVector :
    (x &&& y) = (ofVector <| Vector.map₂ and x.asVector y.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [ofVector, asVector, Vector.eq_nil]
  case cons b x ih =>
    simp only [asVector_cons]
    have : y = Bitvec.cons (head y) (tail y) := by
      sorry
    rw [this]
    simp only [asVector_cons, Vector.map₂_cons]
    have : cons b x &&& cons (head y) (tail y) = cons (b && head y) (x &&& tail y) := by
      sorry
    rw [this]
    have : cons (b && head y) (x &&& tail y) = cons (b && head y) (ofVector <| Vector.map₂ and x.asVector y.asVector) := by
      rw [ih]
    sorry

theorem or_asVector :
    (x ||| y) = (ofVector <| Vector.map₂ or x.asVector y.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [ofVector, asVector, Vector.eq_nil]
  case cons b x ih =>
    simp only [consRecursion_cons, asVector_cons]
    sorry

theorem xor_asVector :
    (x ^^^ y) = (ofVector <| Vector.map₂ xor x.asVector y.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [ofVector, asVector, Vector.eq_nil]
  case cons b x ih =>
    simp only [consRecursion_cons, asVector_cons]
    sorry

/-
  TODO: `shiftLeft`, `shiftRight`, `rotateLeft`, `rotateRight`
-/

/-!
  ## Comparisons
-/

/-
  TODO: `lt`, `le`, `slt`, `sle`, `sgt`, `sge`
-/

/-!
  ## Arithmetic
-/

theorem add_asVector :
    x + y = (ofVector <| Prod.snd <|
      Vector.mapAccumr₂ (fun x y c => (_, _)) x.asVector y.asVector false
    ) := by
  induction x using consRecursion
  case nil =>
    simp only [ofVector, asVector, Vector.eq_nil]
    have : y = nil := by simp only [zero_length_eq_nil]
    rw [this]
    rfl
  case cons b x ih =>
    simp only [consRecursion_cons, asVector_cons]
    sorry

theorem sub_asVector :
    x - y = (ofVector <| Prod.snd <|
      Vector.mapAccumr₂ (fun x y c => (_, _)) x.asVector y.asVector false
    ) := by
  induction x using consRecursion
  case nil =>
    simp only [ofVector, asVector, Vector.eq_nil]
    have : y = nil := by simp only [zero_length_eq_nil]
    rw [this]
    rfl
  case cons b x ih =>
    simp only [consRecursion_cons, asVector_cons]
    sorry

/-
  TODO: `mul`, `div`, `mod`
  These operations cannot (easily) be defined in terms of `mapAccumr`.
  We could still formulate bitwise implementatoins, but the question is whether this is even useful
-/

end Bitvec
