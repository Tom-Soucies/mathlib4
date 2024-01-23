import Mathlib.Data.BitVec.Defs
import Mathlib.Data.BitVec.Lemmas
import Mathlib.Data.BitVec.Recursion
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
