import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
import Mathlib.Data.Vector

#check Vector.mapAccumr

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

/-- The empty bitvector -/
def nil : BitVec 0 :=
  BitVec.zero 0

/-- There is only one `empty` bitvector, namely, `nil` -/
theorem zero_length_eq_nil :
    ∀ (xs : BitVec 0), xs = nil := by
  intro xs
  have : xs.toNat < 2 ^ 0 := xs.toFin.prop
  simp only [Nat.pow_zero, Nat.lt_one_iff] at this
  have : xs.toNat = nil.toNat := this
  simp only [nil, BitVec.zero, toNat_inj] at this
  simp only [this]

/-- Prepend a single bit to the front of a bitvector. The new bit is the least significant bit -/
def cons (x : Bool) (xs : BitVec n) : BitVec (n+1) :=
  BitVec.ofNat (n + 1) (2 * BitVec.toNat xs + cond x 1 0)

/-- Get the head and tail of a BitVec (head being the least significant bit) -/
def head (xs : BitVec (n + 1)) : Bool :=
  Bool.ofNat (BitVec.toNat xs % 2)

def tail (xs : BitVec (n + 1)) : BitVec n :=
  BitVec.ofNat n (Nat.div2 (BitVec.toNat xs))

/- Todo : prove equivalence between this and getlsb (same thing for extractlsb) -/
theorem head_as_getlsb {n : Nat} (xs : BitVec (n + 1)) :
    head xs = BitVec.getLsb xs 0 := by
  sorry

theorem tail_as_extractlsb {n : Nat} (xs : BitVec (n + 1)) :
    tail xs = BitVec.extractLsb' 1 n xs := by
  sorry

theorem cons_as_append {x : Bool} {xs : BitVec n} :
    cons x xs = xs.append (BitVec.ofNat 1 (cond x 1 0)) := by
  sorry


/-!
  ## Induction principles
-/

/-- A custom recursion principle for bitvectors in terms of `nil` and `cons` -/
@[elab_as_elim]
def consRecursion {motive : {n : Nat} → BitVec n → Sort u}
    (nil : motive nil)
    (cons : {n : Nat} → (x : Bool) → (xs : BitVec n) → motive xs → motive (cons x xs))
    {n : Nat} (xs : BitVec n) : motive xs :=
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
theorem consRecursion_cons {motive nil cons} {x : Bool} {xs : BitVec n} :
    consRecursion (motive:=motive) nil cons (.cons x xs)
    = cons x xs (consRecursion nil cons xs) := by
  sorry

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
  `f BitVec.nil`, while `h_cons` is a function that maps `x`, `xs` and `f xs` to the return value of
  `f (BitVec.cons x xs)`
-/

lemma neq_succ {n p : Nat} (h : n < 2 ^ p) :
    2 * n + 1 < 2 ^ (p + 1) := by
  have : 2 * (n + 1) <= 2 * 2 ^ p := Nat.mul_le_mul_left 2 (Nat.succ_le_of_lt h)
  have : 2 * n + 2 <= 2 * 2 ^ p := Nat.mul_succ 2 n ▸ this
  have : Nat.succ (2 * n + 1) <= 2 * 2 ^ p := by
    simp [Nat.succ_eq_add_one, Nat.add_assoc]
    exact this
  have : 2 * n + 1 < 2 * 2 ^ p := Nat.lt_of_succ_le this
  simp only [Nat.pow_succ, Nat.mul_comm (2 ^ p)]
  exact this

theorem head_cons {x : Bool} {xs : BitVec n} :
    head (cons x xs) = x := by
  simp only [cons, head]
  induction x
  case true =>
    simp only [cond]
    rw [BitVec.toNat_ofNat]
    . simp [Nat.add_comm]
    . have : 2 * BitVec.toNat xs + 1 < 2 ^ (n + 1) := neq_succ xs.toFin.prop
      exact this
  case false =>
    simp only [cond]
    rw [BitVec.toNat_ofNat]
    simp
    rw [Nat.add_zero]
    have : 2 * BitVec.toNat xs < 2 * 2 ^ n := Nat.mul_lt_mul' (Nat.le_refl 2) xs.toFin.prop (Nat.zero_lt_succ 1)
    simp only [Nat.pow_succ, Nat.mul_comm (2 ^ n)]
    exact this

theorem tail_cons {x : Bool} {xs : BitVec n} :
    tail (cons x xs) = xs := by
  simp only [cons, tail]
  induction x
  case true =>
    simp only [cond]
    rw [BitVec.toNat_ofNat]
    . simp [Nat.div2_val, Nat.mul_comm]
    . have : 2 * BitVec.toNat xs + 1 < 2 ^ (n + 1) := neq_succ xs.toFin.prop
      exact this
  case false =>
    simp only [cond]
    rw [BitVec.toNat_ofNat]
    simp
    . simp [Nat.div2_val, Nat.mul_comm]
    . have : 2 * BitVec.toNat xs < 2 * 2 ^ n := Nat.mul_lt_mul' (Nat.le_refl 2) xs.toFin.prop (Nat.zero_lt_succ 1)
      simp only [Nat.pow_succ, Nat.mul_comm (2 ^ n), Nat.add_zero]
      exact this

theorem cons_head_tail_eq (x : BitVec (n + 1)) :
    x = cons (head x) (tail x) := by
  simp only [cons, tail, Nat.div2_val]
  have : (BitVec.toNat x) / 2 < 2 ^ n := by
    have : BitVec.toNat x < 2 ^ (n + 1) := x.toFin.prop
    have : BitVec.toNat x / 2 < 2 ^ (n + 1) / 2 := by

      sorry
    have H0 : 2 ^ (n + 1) / 2 = 2 ^ n := by
      rw [Nat.pow_succ]
      simp
    rw [H0] at this
    exact this
  rw [BitVec.toNat_ofNat this]
  -- have : 2 * (BitVec.toNat x / 2) = cons false x
  induction head x
  case false =>
    simp only [cond, Nat.add_zero]
    sorry
  case true =>
    simp [cond]
    sorry

theorem head_tail_eq {xs ys : BitVec (n + 1)} :
    xs = ys ↔ head xs = head ys ∧ tail xs = tail ys := by
  apply Iff.intro
  case mp =>
    intro h
    simp only [h]
  case mpr =>
    intro h
    have H : head xs = head ys := h.left
    have T : tail xs = tail ys := h.right
    have : xs = cons (head ys) (tail ys) := by
      rw [←T, ←H]
      exact cons_head_tail_eq xs
    rw [this, ←cons_head_tail_eq]

/-!
  ## Equivalence
-/

/-- Turn a bitvector into a vector of bools of the same length -/
def asVector {n : Nat} : BitVec n → Vector Bool n :=
  fun xs =>
    consRecursion
      (Vector.nil)
      (fun x _ xs => Vector.cons x xs)
      xs

/-- Turn a vector of bools into a bitvector of the same length -/
def ofVector {n : Nat} : Vector Bool n → BitVec n :=
  fun x =>
    match n with
    | 0 => nil
    | Nat.succ _ => cons (Vector.head x) (ofVector <| Vector.tail x)

/-- Distribution of vectorEquiv over cons -/
theorem asVector_cons {x : Bool} {xs : BitVec n} :
    asVector (cons x xs) = Vector.cons x (asVector xs) := by
  simp only [asVector, ofVector, consRecursion_cons]

theorem ofVector_cons {x : Bool} {xs : Vector Bool n} :
    ofVector (Vector.cons x xs) = cons x (ofVector xs) := by
  simp only [ofVector, asVector, consRecursion_cons]
  have H0 : Vector.head (Vector.cons x xs) = x := rfl
  have H1 : Vector.tail (Vector.cons x xs) = xs := rfl
  rw [H0, H1]

def vectorEquiv {n : Nat} : BitVec n ≃ Vector Bool n where
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

/-!
  ## Constants
-/

theorem zero_asVector :
    (BitVec.zero m).asVector = Vector.replicate m false := by
  induction m
  case zero =>
    apply vectorEquiv.symm.injective
    simp
  case succ m ih =>
    have : asVector (BitVec.zero (Nat.succ m)) = Vector.cons false (asVector (BitVec.zero m)) := by
      have : BitVec.zero (Nat.succ m) = cons false (BitVec.zero m) := by
        simp [BitVec.cons, BitVec.zero, BitVec.append]
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

theorem head_complement {x : BitVec (n + 1)} :
    head (~~~x) = !head x := by
  sorry

theorem tail_complement {x : BitVec (n + 1)} :
    tail (~~~x) = ~~~(tail x) := by
  sorry

theorem complement_cons {x : Bool} {xs : BitVec n} :
    ~~~cons x xs = cons (!x) (~~~xs) := by
  rw [head_tail_eq]
  apply And.intro
  case left =>
    simp only [head_cons, head_complement]
  case right =>
    simp only [tail_cons, tail_complement]

theorem complement_asVector {x : BitVec n} :
    (~~~x) = (ofVector <| Vector.map not x.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [ofVector, asVector, Vector.eq_nil]
  case cons b x ih =>
    simp only [ofVector_cons, asVector_cons, Vector.map_cons, complement_cons]
    rw [ih]

variable {x y : BitVec n}

/- And_AsVector theorem -/
theorem head_and {x y : BitVec (n + 1)} :
    head (x &&& y) = (head x && head y) := by
  sorry

theorem tail_and {x y : BitVec (n + 1)} :
    tail (x &&& y) = tail x &&& tail y := by
  sorry

theorem and_cons {x y : Bool} {xs ys : BitVec n} :
    (cons x xs) &&& (cons y ys) = cons (x && y) (xs &&& ys) := by
  rw [head_tail_eq]
  apply And.intro
  case left =>
    simp only [head_cons, head_and]
  case right =>
    simp only [tail_cons, tail_and]

theorem and_asVector :
    (x &&& y) = (ofVector <| Vector.map₂ and x.asVector y.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [zero_length_eq_nil]
  case cons b x ih =>
    simp only [asVector_cons]
    rw [cons_head_tail_eq y]
    simp only [and_cons, head_cons]
    simp only [asVector_cons]
    have : Vector.map₂ and (Vector.cons b (asVector x)) (Vector.cons (head y) (asVector (tail y))) =
      Vector.cons (b && head y) (Vector.map₂ and (asVector x) (asVector (tail y))) := by
      rfl
    rw [this]
    simp only [ofVector_cons, head_cons]
    rw [head_tail_eq, ih]
    simp

/- Or_AsVector theorem -/
theorem head_or {x y : BitVec (n + 1)} :
    head (x ||| y) = (head x || head y) := by
  sorry

theorem tail_or {x y : BitVec (n + 1)} :
    tail (x ||| y) = tail x ||| tail y := by
  sorry

theorem or_cons {x y : Bool} {xs ys : BitVec n} :
    (cons x xs) ||| (cons y ys) = cons (x || y) (xs ||| ys) := by
  rw [head_tail_eq]
  apply And.intro
  case left =>
    simp only [head_cons, head_or]
  case right =>
    simp only [tail_cons, tail_or]

theorem or_asVector :
    (x ||| y) = (ofVector <| Vector.map₂ or x.asVector y.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [zero_length_eq_nil]
  case cons b x ih =>
    simp only [asVector_cons]
    rw [cons_head_tail_eq y]
    simp only [or_cons, head_cons]
    simp only [asVector_cons]
    have : Vector.map₂ or (Vector.cons b (asVector x)) (Vector.cons (head y) (asVector (tail y))) =
      Vector.cons (b || head y) (Vector.map₂ or (asVector x) (asVector (tail y))) := by
      rfl
    rw [this]
    simp only [ofVector_cons, head_cons]
    rw [head_tail_eq, ih]
    simp

/- Xor_AsVector theorem -/
theorem head_xor {x y : BitVec (n + 1)} :
    head (x ^^^ y) = (xor (head x) (head y)) := by
  sorry

theorem tail_xor {x y : BitVec (n + 1)} :
    tail (x ^^^ y) = tail x ^^^ tail y := by
  sorry

theorem xor_cons {x y : Bool} {xs ys : BitVec n} :
    (cons x xs) ^^^ (cons y ys) = cons (xor x y) (xs ^^^ ys) := by
  rw [head_tail_eq]
  apply And.intro
  case left =>
    simp only [head_cons, head_xor]
  case right =>
    simp only [tail_cons, tail_xor]

theorem xor_asVector :
    (x ^^^ y) = (ofVector <| Vector.map₂ xor x.asVector y.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [zero_length_eq_nil]
  case cons b x ih =>
    simp only [asVector_cons]
    rw [cons_head_tail_eq y]
    simp only [xor_cons, head_cons]
    simp only [asVector_cons]
    have : Vector.map₂ xor (Vector.cons b (asVector x)) (Vector.cons (head y) (asVector (tail y))) =
      Vector.cons (xor b (head y)) (Vector.map₂ xor (asVector x) (asVector (tail y))) := by
      rfl
    rw [this]
    simp only [ofVector_cons, head_cons]
    rw [head_tail_eq, ih]
    simp

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

end BitVec
