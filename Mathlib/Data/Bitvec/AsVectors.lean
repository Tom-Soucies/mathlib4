import Mathlib.Data.Bitvec.Defs
import Mathlib.Data.Bitvec.Lemmas
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

/-- Get the head and tail of a BitVec (head being the least significant bit) -/
def head (xs : BitVec (n + 1)) : Bool :=
  BitVec.getLsb xs 0

def tail (xs : BitVec (n + 1)) : BitVec n :=
  BitVec.extractLsb' 1 n xs

/-!
  ## Induction principles
-/

/-- A custom recursion principle for bitvectors in terms of `nil` and `cons` -/
@[elab_as_elim]
def consRecursion {motive : {n : Nat} → BitVec n → Sort u}
    (nil : motive nil)
    (ind : {n : Nat} → (x : Bool) → (xs : BitVec n) → motive xs → motive (cons x xs))
    {n : Nat} (xs : BitVec n) : motive xs :=
  /-
    This one might be a bit hard to prove.
    For now, the `consRecursion_nil` and `consRecursion_cons` theorems fully specify how
    `consRecursion` should behave, and it is enough to use those in proofs about definitions using
    `consRecursion`
  -/
  sorry

@[simp]
theorem consRecursion_nil {motive nil ind} :
    consRecursion (motive:=motive) nil ind .nil = nil := by
  sorry

@[simp]
theorem consRecursion_cons {motive nil ind} {x : Bool} {xs : BitVec n} :
    consRecursion (motive:=motive) nil ind (.cons x xs)
    = ind x xs (consRecursion nil ind xs) := by
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

theorem asVector_eq {xs ys : BitVec n} :
    asVector xs = asVector ys ↔ xs = ys := by
  apply Iff.intro (fun h => vectorEquiv.injective h) (congr_arg asVector)

/-!
  ## Properties over `cons`
-/

variable {m : Nat}

/-- Prepend a single bit to the front of a bitvector. The new bit is the least significant bit -/
theorem cons_as_math (x : Bool) (xs : BitVec n) :
    cons x xs = BitVec.ofNat (n+1) (2 * BitVec.toNat xs + cond x 1 0) := by
  simp only [cons]
  sorry

/- Todo : prove equivalence between this and getlsb (same thing for extractlsb) -/
theorem head_as_math {n : Nat} (xs : BitVec (n + 1)) :
    head xs = Bool.ofNat (BitVec.toNat xs % 2) := by
  simp only [head]
  sorry

theorem tail_as_math {n : Nat} (xs : BitVec (n + 1)) :
    tail xs = BitVec.ofNat n (Nat.div2 (BitVec.toNat xs)) := by
  simp only [tail]
  sorry

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
  rw [cons_as_math, head_as_math]
  induction x
  case true =>
    simp only [cond]
    rw [BitVec.toNat_ofNat]
    . simp [Nat.add_comm, Bool.ofNat]
    . have : 2 * BitVec.toNat xs + 1 < 2 ^ (n + 1) := neq_succ xs.toFin.prop
      exact this
  case false =>
    simp only [cond]
    rw [BitVec.toNat_ofNat]
    simp
    rw [Bool.ofNat]
    simp
    have : 2 * BitVec.toNat xs < 2 * 2 ^ n := Nat.mul_lt_mul' (Nat.le_refl 2) xs.toFin.prop (Nat.zero_lt_succ 1)
    simp only [Nat.pow_succ, Nat.mul_comm (2 ^ n)]
    exact this

theorem tail_cons {x : Bool} {xs : BitVec n} :
    tail (cons x xs) = xs := by
  rw [cons_as_math, tail_as_math]
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
  rw [<-asVector_eq]
  apply vectorEquiv.right_inv

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

/-!
  ## Constants
-/

theorem zero_asVector :
    (BitVec.zero m).asVector = Vector.replicate m false := by
  induction m
  case zero =>
    apply vectorEquiv.right_inv
  case succ m ih =>
    have : asVector (BitVec.zero (Nat.succ m)) = Vector.cons false (asVector (BitVec.zero m)) := by
      have : BitVec.zero (Nat.succ m) = cons false (BitVec.zero m) := by
        simp [cons_as_math]
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

/- Complement_AsVector theorem -/
theorem complement_cons {x : Bool} {xs : BitVec n} :
    ~~~cons x xs = cons (!x) (~~~xs) := by
  rw [<-asVector_eq]
  apply vectorEquiv.right_inv

theorem complement_asVector {x : BitVec n} :
    (~~~x) = (ofVector <| Vector.map not x.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [ofVector, asVector, Vector.eq_nil]
    rfl
  case ind b x ih =>
    simp only [ofVector_cons, asVector_cons, Vector.map_cons, complement_cons]
    rw [ih]

/-
  TODO: `shiftLeft`, `shiftRight`, `rotateLeft`, `rotateRight`
-/

/- ShiftLeft_AsVector theorem (one iteration) -/
theorem shiftLeft_cons {x : Bool} {xs : BitVec n} :
    (cons x xs) <<< 1 = cons false (xs <<< 1) := by
  rw [<-asVector_eq]
  apply vectorEquiv.right_inv

theorem shiftLeft_asVector {x : BitVec n} :
    (x <<< 1) = (ofVector <| Vector.map (fun _ => false) x.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [zero_length_eq_nil]
  case ind b x ih =>
    simp only [ofVector_cons, asVector_cons, Vector.map_cons, shiftLeft_cons]
    rw [ih]

variable {x y : BitVec n}

/- And_AsVector theorem -/
theorem and_cons {x y : Bool} {xs ys : BitVec n} :
    (cons x xs) &&& (cons y ys) = cons (x && y) (xs &&& ys) := by
  rw [<-asVector_eq]
  simp only [asVector_cons]
  apply vectorEquiv.right_inv

theorem and_asVector :
    (x &&& y) = (ofVector <| Vector.map₂ and x.asVector y.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [zero_length_eq_nil]
  case ind b x ih =>
    simp only [asVector_cons]
    rw [cons_head_tail_eq y]
    simp only [and_cons, asVector_cons]
    have : Vector.map₂ and (Vector.cons b (asVector x)) (Vector.cons (head y) (asVector (tail y))) =
      Vector.cons (b && head y) (Vector.map₂ and (asVector x) (asVector (tail y))) := by
      rfl
    rw [this]
    simp only [ofVector_cons]
    rw [head_tail_eq, ih]
    simp

/- Or_AsVector theorem -/
theorem or_cons {x y : Bool} {xs ys : BitVec n} :
    (cons x xs) ||| (cons y ys) = cons (x || y) (xs ||| ys) := by
  rw [<-asVector_eq]
  simp only [asVector_cons]
  apply vectorEquiv.right_inv

theorem or_asVector :
    (x ||| y) = (ofVector <| Vector.map₂ or x.asVector y.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [zero_length_eq_nil]
  case ind b x ih =>
    simp only [asVector_cons]
    rw [cons_head_tail_eq y]
    simp only [or_cons, asVector_cons]
    have : Vector.map₂ or (Vector.cons b (asVector x)) (Vector.cons (head y) (asVector (tail y))) =
      Vector.cons (b || head y) (Vector.map₂ or (asVector x) (asVector (tail y))) := by
      rfl
    rw [this]
    simp only [ofVector_cons]
    rw [head_tail_eq, ih]
    simp

/- Xor_AsVector theorem -/
theorem xor_cons {x y : Bool} {xs ys : BitVec n} :
    (cons x xs) ^^^ (cons y ys) = cons (xor x y) (xs ^^^ ys) := by
  rw [<-asVector_eq]
  simp only [asVector_cons]
  apply vectorEquiv.right_inv

theorem xor_asVector :
    (x ^^^ y) = (ofVector <| Vector.map₂ xor x.asVector y.asVector) := by
  induction x using consRecursion
  case nil =>
    simp only [zero_length_eq_nil]
  case ind b x ih =>
    simp only [asVector_cons]
    rw [cons_head_tail_eq y]
    simp only [xor_cons, asVector_cons]
    have : Vector.map₂ xor (Vector.cons b (asVector x)) (Vector.cons (head y) (asVector (tail y))) =
      Vector.cons (xor b (head y)) (Vector.map₂ xor (asVector x) (asVector (tail y))) := by
      rfl
    rw [this]
    simp only [ofVector_cons]
    rw [head_tail_eq, ih]
    simp

/-!
  ## Comparisons
-/

/-
  TODO: `lt`, `le`, `slt`, `sle`, `sgt`, `sge`
-/

/- Lt_AsVector theorem -/
def lt_bool (x y c : Bool) : Bool × Bool :=
  ((!x && y) || (x == y && c), false)

theorem lt_asVector :
    BitVec.ult x y = (Prod.fst <|
      Vector.mapAccumr₂ lt_bool (asVector x) (asVector y) false
    ) := by
  induction x using consRecursion
  case nil =>
    simp only [zero_length_eq_nil]
    sorry
  case ind b x ih =>
    simp only [asVector_cons]
    rw [cons_head_tail_eq y]
    simp only [asVector_cons]
    sorry

/-!
  ## Arithmetic
-/

/- Add_AsVector theorem -/
def sum_bool (x y c : Bool) : Bool × Bool :=
  (or (and x y) (or (and x c) (and c y)), xor (xor x y) c)

theorem add_cons {x y : Bool} {xs ys : BitVec n} :
    (cons x xs) + (cons y ys) = cons (Prod.snd (sum_bool x y false)) (adc xs ys (Prod.fst (sum_bool x y false))) := by
  rw [<-asVector_eq]
  simp only [asVector_cons]
  apply vectorEquiv.right_inv

theorem add_asVector :
    x + y = (ofVector <| Prod.snd <|
      Vector.mapAccumr₂ sum_bool (asVector x) (asVector y) false
    ) := by
  induction x using consRecursion
  case nil =>
    simp only [ofVector, asVector, Vector.eq_nil]
    have : y = nil := by simp only [zero_length_eq_nil]
    rw [this]
    rfl
  case ind b x ih =>
    simp only [asVector_cons]
    rw [cons_head_tail_eq y]
    simp only [add_cons, asVector_cons]
    have : (Vector.mapAccumr₂ sum_bool (Vector.cons b (asVector x)) (Vector.cons (head y) (asVector (tail y))) false).2 =
      Vector.cons (sum_bool b (head y) false).2 (Vector.mapAccumr₂ sum_bool (asVector x) (asVector (tail y)) (Prod.fst <| sum_bool b (head y) false)).2 := by
      match b, (head y) with
      | true, true =>
        rw [sum_bool]
        simp
        sorry
      | false, true =>
        rw [sum_bool]
        simp
        sorry
      | true, false =>
        rw [sum_bool]
        simp
        sorry
      | false, false =>
        rw [sum_bool]
        simp
        sorry
    rw [this]
    simp only [ofVector_cons]
    rw [head_tail_eq]
    apply And.intro
    case left =>
      rw [head_cons, head_cons]
    case right =>
      rw [tail_cons, tail_cons]
      match b, (head y) with
      | true, true =>
        simp [sum_bool]
        have : adc x (tail y) true = x + (tail y) + 1 := by
          simp [adc]
          rw [<-BitVec.add_eq]
          simp [BitVec.add]
          sorry
        rw [this, ih]
        sorry
      | false, _ | _, false =>
        simp [sum_bool]
        have : adc x (tail y) false = x + (tail y) := by
          simp [adc]
          rw [<-BitVec.add_eq]
          simp [BitVec.add]
          sorry
        rw [this]
        rw [ih]

/- Sub_Asvector theorem-/
def sub_bool (x y c : Bool) : Bool × Bool :=
  (or (and (not x) y) (and (not x) c), xor (xor (not x) y) c)

theorem sub_cons {x y : Bool} {xs ys : BitVec n} :
    (cons x xs) - (cons y ys) = cons (Prod.snd (sub_bool x y false)) (Prod.snd (sbb xs ys (Prod.fst (sub_bool x y false)))) := by
  rw [<-asVector_eq]
  simp only [asVector_cons]
  apply vectorEquiv.right_inv

theorem sub_asVector :
    x - y = (ofVector <| Prod.snd <|
      Vector.mapAccumr₂ sub_bool x.asVector y.asVector false
    ) := by
  induction x using consRecursion
  case nil =>
    simp only [ofVector, asVector, Vector.eq_nil]
    have : y = nil := by simp only [zero_length_eq_nil]
    rw [this]
    rfl
  case ind b x ih =>
    simp only [asVector_cons]
    rw [cons_head_tail_eq y]
    simp only [sub_cons, asVector_cons]
    have : (Vector.mapAccumr₂ sub_bool (Vector.cons b (asVector x)) (Vector.cons (head y) (asVector (tail y))) false).2 =
      Vector.cons (sub_bool b (head y) false).2 (Vector.mapAccumr₂ sub_bool (asVector x) (asVector (tail y)) (Prod.fst <| sub_bool b (head y) false)).2 := by
      sorry
    rw [this]
    simp only [ofVector_cons]
    rw [head_tail_eq]
    apply And.intro
    case left =>
      rw [head_cons, head_cons]
    case right =>
      rw [tail_cons, tail_cons]
      match b, (head y) with
      | false, true =>
        simp [sub_bool]
        have : Prod.snd (sbb x (tail y) true) = x - (tail y) - 1 := by
          simp only [sbb]
          rw [<-BitVec.sub_eq]
          simp [BitVec.sub]
          sorry
        rw [this]
        rw [ih]
        sorry
      | true, _ | _, false =>
        simp [sub_bool]
        have : Prod.snd (sbb x (tail y) false) = x - (tail y) := by
          simp [sbb]
          rw [<-BitVec.sub_eq]
          simp [BitVec.sub]
          sorry
        rw [this]
        rw [ih]

/-
  TODO: `mul`, `div`, `mod`
  These operations cannot (easily) be defined in terms of `mapAccumr`.
  We could still formulate bitwise implementatoins, but the question is whether this is even useful
-/

/-- False theorem but proved -/
theorem falsely {x : BitVec n} :
    x = 0 ∧ x = 1 := by
  rw [<-asVector_eq, <-asVector_eq]
  apply And.intro <;> apply vectorEquiv.right_inv

theorem falsy : False := by
  have : (1 : BitVec (n + 1)) = 0 := falsely.left
  have F : head (1 : BitVec (n + 1)) = head (0 : BitVec (n + 1)) := congr_arg head this
  simp [head, getLsb] at F
  have T : (1 % 2 ^ (n + 1) &&& 1 != 0) = true := by
    have : 1 % 2 ^ (n + 1) = 1 := by
      rw [Nat.mod_eq_of_lt]
      simp [Nat.pow_succ]
      have : 0 < 2 ^ n := by induction n <;> simp
      have : 1 < 2 ^ n * 2 := Nat.mul_lt_mul' (Nat.succ_le_of_lt this) (Nat.le_refl 2) (this)
      exact this
    rw [this]
    rfl
  simp [T] at F

#print falsy

end BitVec
