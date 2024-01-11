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

/-- Two bitvectors are equal iff all their bits are equal 2 to 2 -/
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
    simp [tail, extractLsb', getLsb_eq_testBit]
    rw [Nat.testBit_mod_two_pow]
    have prop : x.toNat < 2 ^ (n + 1) := x.toFin.prop
    if h' : i > n then
      have h_lt : 2 ^ (n + 1) ≤ 2 ^ i := by
        have : n + 1 ≤ i := by
          rw [Nat.succ_le_iff]
          exact h'
        exact Nat.pow_le_pow_of_le_right (Nat.zero_lt_succ _) this
      have : x.toNat.testBit i = false := by
        rw [Nat.testBit_lt_two]
        simp only [Nat.lt_of_lt_of_le (prop) h_lt]
      simp [this]
    else
      have : i < n := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h') h
      simp [this]

theorem head_cons (x : Bool) (xs : BitVec n) :
    head (cons x xs) = x := by
  simp [head, getLsb_cons]

theorem small_getLsb (i : Nat) (x : Bool) (xs : BitVec n) (h : i < n) :
    getLsb (cons x xs) i = getLsb xs i := by
  rw [getLsb_cons]
  have : ¬i = n := by simp [Nat.ne_of_lt h]
  simp [this]

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
    rw [<-getLsb_eq_testBit, <-getLsb_eq_testBit, small_getLsb i x xs h']

/-!
  ## Induction principles
-/

/-- A custom recursion principle for bitvectors in terms of `nil` and `cons` -/
@[elab_as_elim]
def consRecursion {motive : {n : Nat} → BitVec n → Sort u}
    (nil : motive nil)
    (ind : {n : Nat} → (x : Bool) → (xs : BitVec n) → motive xs → motive (cons x xs))
    {n : Nat} : ∀ xs : BitVec n, motive xs :=
  /-
    This one might be a bit hard to prove.
    For now, the `consRecursion_nil` and `consRecursion_cons` theorems fully specify how
    `consRecursion` should behave, and it is enough to use those in proofs about definitions using
    `consRecursion`
  -/
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

/-- Distribution of vectorEquiv over head and tail -/
theorem asVector_head {n : Nat} (xs : BitVec (n + 1)) :
    head xs = Vector.head (asVector xs) := by
  simp only [asVector, consRecursion_cons]
  rfl

theorem asVector_tail {n : Nat} (xs : BitVec (n + 1)) :
    asVector (tail xs) = Vector.tail (asVector xs) := by
  simp only [asVector, consRecursion]
  rfl

/-- Distribution of vectorEquiv over cons -/
theorem asVector_cons {x : Bool} {xs : BitVec n} :
    asVector (cons x xs) = Vector.cons x (asVector xs) := by
  simp only [asVector, consRecursion_cons]

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

theorem asofVector_eq {xs : Vector Bool n} :
    asVector (ofVector xs) = xs := by
  apply vectorEquiv.right_inv

theorem ofasVector_eq {xs : BitVec n} :
    ofVector (asVector xs) = xs := by
  apply vectorEquiv.left_inv

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

/-!
  ## Constants
-/

theorem zero_asVector :
    (BitVec.zero m).asVector = Vector.replicate m false := by
  induction m
  case zero =>
    rfl
  case succ m ih =>
    have : asVector (BitVec.zero (Nat.succ m)) = Vector.cons false (asVector (BitVec.zero m)) := by
      have : BitVec.zero (Nat.succ m) = cons false (BitVec.zero m) := by
        rw [head_tail_eq]
        apply And.intro
        case left =>
          simp [head_cons]
          simp [head, getLsb]
        case right =>
          simp [tail_cons]
          simp [tail, extractLsb']
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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  ((!x && y) || (x == y && c), (x == y && c))

def lt_cons {x y : Bool} {xs ys : BitVec n} :
    BitVec.ult (cons x xs) (cons y ys) = ((!x && y) || (x == y && (BitVec.ult xs ys))) := by
  sorry

theorem lt_asVector :
    BitVec.ult x y = (Prod.fst <|
      Vector.mapAccumr₂ lt_bool (asVector x) (asVector y) false
    ) := by
  induction x using consRecursion
  case nil =>
    simp only [zero_length_eq_nil]
    rfl
  case ind b x ih =>
    simp only [asVector_cons]
    rw [cons_head_tail_eq y]
    simp only [lt_cons, asVector_cons]
    rw [ih]
    have : (Vector.mapAccumr₂ lt_bool (Vector.cons b (asVector x)) (Vector.cons (head y) (asVector (tail y))) false).1 =
      ((!b && head y) || (b == (head y) && (Vector.mapAccumr₂ lt_bool (asVector x) (asVector (tail y)) false).1)) := by
      rfl
    rw [this]

/- Le_AsVector theorem -/
def le_bool (x y c : Bool) : Bool × Bool :=
  ((!x && y) || (x == y && c), x == y && c)

def le_cons {x y : Bool} {xs ys : BitVec n} :
    BitVec.ule (cons x xs) (cons y ys) = ((!x && y) || (x == y && (BitVec.ule xs ys))) := by
  sorry

theorem le_asVector :
    BitVec.ule x y = (Prod.fst <|
      Vector.mapAccumr₂ le_bool (asVector x) (asVector y) true
    ) := by
  induction x using consRecursion
  case nil =>
    simp only [zero_length_eq_nil]
    rfl
  case ind b x ih =>
    simp only [asVector_cons]
    rw [cons_head_tail_eq y]
    simp only [le_cons, asVector_cons]
    rw [ih]
    have : (Vector.mapAccumr₂ le_bool (Vector.cons b (asVector x)) (Vector.cons (head y) (asVector (tail y))) true).1 =
      ((!b && head y) || (b == (head y) && (Vector.mapAccumr₂ le_bool (asVector x) (asVector (tail y)) true).1)) := by
      rfl
    rw [this]

/-!
  ## Arithmetic
-/

/- Add_AsVector theorem -/
def sum_bool (x y c : Bool) : Bool × Bool :=
  (or (and x y) (or (and x c) (and c y)), xor (xor x y) c)

theorem add_cons {x y : Bool} {xs ys : BitVec n} :
    (cons x xs) + (cons y ys) = cons (Prod.snd (sum_bool x y false)) (adc'' xs ys (Prod.fst (sum_bool x y false))) := by
  sorry

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
        have : adc'' x (tail y) true = x + (tail y) + 1 := by
          simp [adc]
          rw [<-add_eq]
          simp [BitVec.add]
          sorry
        rw [this, ih]
        sorry
      | false, _ | _, false =>
        simp [sum_bool]
        have : adc'' x (tail y) false = x + (tail y) := by
          simp [adc'']
          rw [<-add_eq]
          simp [BitVec.add]
          sorry
        rw [this]
        rw [ih]

/- Sub_Asvector theorem-/
def sub_bool (x y c : Bool) : Bool × Bool :=
  (or (and (not x) y) (and (not x) c), xor (xor (not x) y) c)

theorem sub_cons {x y : Bool} {xs ys : BitVec n} :
    (cons x xs) - (cons y ys) = cons (Prod.snd (sub_bool x y false)) (Prod.snd (sbb xs ys (Prod.fst (sub_bool x y false)))) := by
  sorry

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
          rw [<-sub_eq]
          simp [BitVec.sub]
          sorry
        rw [this]
        rw [ih]
        sorry
      | true, _ | _, false =>
        simp [sub_bool]
        have : Prod.snd (sbb x (tail y) false) = x - (tail y) := by
          simp [sbb]
          rw [<-sub_eq]
          simp [BitVec.sub]
          sorry
        rw [this]
        rw [ih]

/-
  TODO: `mul`, `div`, `mod`
  These operations cannot (easily) be defined in terms of `mapAccumr`.
  We could still formulate bitwise implementatoins, but the question is whether this is even useful
-/

end BitVec
