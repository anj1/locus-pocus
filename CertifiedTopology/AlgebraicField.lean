module

public import CertifiedTopology.AlgebraicRoot

@[expose] public section

namespace CertifiedTopology.AlgebraicField

open AlgebraicRoot ExecutableIsolation Polynomial
open DensePolynomial (Coefficients)

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {model : RealModel K}
variable (r : Root model)

noncomputable def evaluate (p : Coefficients K) : ℝ := (realPoly model.hom p).eval r.value

omit [IsStrictOrderedRing K] in
@[simp] theorem evaluate_constant (a : K) : evaluate r [a] = model.hom a := by
  simp [evaluate, realPoly, DensePolynomial.polynomial]

omit [IsStrictOrderedRing K] in
@[simp] theorem evaluate_add (p q : Coefficients K) :
    evaluate r (DensePolynomial.add p q) = evaluate r p + evaluate r q := by
  simp [evaluate, realPoly]

omit [IsStrictOrderedRing K] in
@[simp] theorem evaluate_sub (p q : Coefficients K) :
    evaluate r (DensePolynomial.sub p q) = evaluate r p - evaluate r q := by
  simp [evaluate, realPoly, Polynomial.map_sub]

omit [IsStrictOrderedRing K] in
@[simp] theorem evaluate_mul (p q : Coefficients K) :
    evaluate r (DensePolynomial.mul p q) = evaluate r p * evaluate r q := by
  simp [evaluate, realPoly, Polynomial.map_mul]

omit [IsStrictOrderedRing K] in
@[simp] theorem evaluate_neg (p : Coefficients K) :
    evaluate r (DensePolynomial.neg p) = -evaluate r p := by
  simp [evaluate, realPoly, Polynomial.map_neg]

def reduce (p : Coefficients K) : Coefficients K :=
  if p.length < r.polynomial.length then p else (DensePolynomial.divmod p r.polynomial).2

omit [IsStrictOrderedRing K] in
@[simp] theorem evaluate_reduce (p : Coefficients K) : evaluate r (reduce r p) = evaluate r p := by
  unfold reduce
  split
  · rfl
  have eq := congrArg (fun q : Polynomial K => (q.map model.hom).eval r.value)
    (DensePolynomial.divmod_spec p r.polynomial).1
  have hz : (realPoly model.hom r.polynomial).eval r.value = 0 := r.represents.root
  simpa only [evaluate, realPoly, Polynomial.map_add, Polynomial.map_mul, eval_add,
    eval_mul, hz, mul_zero, zero_add] using eq.symm

/-- A fraction of bounded-degree polynomials evaluated at the selected real
    root. The denominator is certified to be nonzero at that root. -/
structure Fraction (r : Root model) where
  num : Coefficients K
  den : Coefficients K
  den_ne_zero : evaluate r den ≠ 0

namespace Fraction

noncomputable def value (a : Fraction r) : ℝ := evaluate r a.num / evaluate r a.den

def constant (a : K) : Fraction r := ⟨[a], [1], by simp⟩

omit [IsStrictOrderedRing K] in
@[simp] theorem value_constant (a : K) : (constant r a).value = model.hom a := by
  simp [constant, value]

/-- Reduce powers by the root polynomial after arithmetic. -/
def make (p q : Coefficients K) (hq : evaluate r q ≠ 0) : Fraction r :=
  ⟨reduce r p, reduce r q, by simpa using hq⟩

omit [IsStrictOrderedRing K] in
@[simp] theorem value_make (p q : Coefficients K) (hq : evaluate r q ≠ 0) :
    (make r p q hq).value = evaluate r p / evaluate r q := by simp [make, value]

def add (a b : Fraction r) : Fraction r :=
  make r (DensePolynomial.add (DensePolynomial.mul a.num b.den) (DensePolynomial.mul b.num a.den))
    (DensePolynomial.mul a.den b.den) (by simp [a.den_ne_zero, b.den_ne_zero])

omit [IsStrictOrderedRing K] in
@[simp] theorem value_add (a b : Fraction r) : (add r a b).value = a.value + b.value := by
  rw [add, value_make]
  simp only [evaluate_add, evaluate_mul, value]
  field_simp [a.den_ne_zero, b.den_ne_zero]

def mul (a b : Fraction r) : Fraction r :=
  make r (DensePolynomial.mul a.num b.num) (DensePolynomial.mul a.den b.den)
    (by simp [a.den_ne_zero, b.den_ne_zero])

omit [IsStrictOrderedRing K] in
@[simp] theorem value_mul (a b : Fraction r) : (mul r a b).value = a.value * b.value := by
  rw [mul, value_make]
  simp [value, div_mul_div_comm]

def neg (a : Fraction r) : Fraction r := ⟨DensePolynomial.neg a.num, a.den, a.den_ne_zero⟩

omit [IsStrictOrderedRing K] in
@[simp] theorem value_neg (a : Fraction r) : (neg r a).value = -a.value := by simp [neg, value, neg_div]

def inv (a : Fraction r) : Fraction r :=
  if h : zeroAt model r a.num = true then constant r 0
  else ⟨a.den, a.num, mt (zeroAt_correct model r a.num).mpr h⟩

@[simp] theorem value_inv (a : Fraction r) : (inv r a).value = a.value⁻¹ := by
  unfold inv
  split
  · rename_i h
    have e : evaluate r a.num = 0 := (zeroAt_correct model r a.num).mp h
    simp [constant, value, e]
  · simp [value, inv_div]

def sign (a : Fraction r) : Side :=
  AlgebraicRoot.sign model r (reduce r (DensePolynomial.mul a.num a.den))

theorem sign_correct (a : Fraction r) : sign r a = side a.value 0 := by
  rw [sign, AlgebraicRoot.sign_correct]
  change side (evaluate r (reduce r (DensePolynomial.mul a.num a.den))) 0 = _
  rw [evaluate_reduce, evaluate_mul]
  let n := evaluate r a.num
  let d := evaluate r a.den
  change side (n*d) 0 = side (n/d) 0
  have hd : d ≠ 0 := a.den_ne_zero
  have hsq : 0 < d^2 := sq_pos_of_ne_zero hd
  have eq : n*d = (n/d)*d^2 := by field_simp
  rw [eq]
  simp [side, mul_neg_iff, hsq, hsq.not_gt, hd]

end Fraction

def equivalent : Setoid (Fraction r) where
  r a b := a.value = b.value
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The quotient has computable representatives and exact comparison.
    Only its interpretation as a real number uses noncomputable data. -/
abbrev Number := Quotient (equivalent r)

def ofFraction (a : Fraction r) : Number r := Quotient.mk _ a

noncomputable def value : Number r → ℝ :=
  Quotient.lift (Fraction.value r) (fun _ _ eq => eq)

omit [IsStrictOrderedRing K] in
@[simp] theorem value_ofFraction (a : Fraction r) : value r (ofFraction r a) = a.value := rfl

omit [IsStrictOrderedRing K] in
theorem value_injective : Function.Injective (value r) := by
  intro a b
  induction a,b using Quotient.inductionOn₂ with
  | _ a b => intro h; exact Quotient.sound (s := equivalent r) h

def ofBase (a : K) : Number r := ofFraction r (Fraction.constant r a)

omit [IsStrictOrderedRing K] in
@[simp] theorem value_ofBase (a : K) : value r (ofBase r a) = model.hom a := Fraction.value_constant r a

def generator : Number r :=
  ofFraction r ⟨[0,1], [1], by simp⟩

omit [IsStrictOrderedRing K] in
@[simp] theorem value_generator : value r (generator r) = r.value := by
  rw [generator, value_ofFraction]
  simp [Fraction.value, evaluate, realPoly, DensePolynomial.polynomial]

instance : Zero (Number r) := ⟨ofBase r 0⟩
instance : One (Number r) := ⟨ofBase r 1⟩

instance : Add (Number r) :=
  ⟨Quotient.map₂ (Fraction.add r) (fun a b ha c d hb => by
    change (Fraction.add r a c).value = (Fraction.add r b d).value
    simp only [Fraction.value_add, show a.value = b.value from ha, show c.value = d.value from hb])⟩

instance : Mul (Number r) :=
  ⟨Quotient.map₂ (Fraction.mul r) (fun a b ha c d hb => by
    change (Fraction.mul r a c).value = (Fraction.mul r b d).value
    simp only [Fraction.value_mul, show a.value = b.value from ha, show c.value = d.value from hb])⟩

instance : Neg (Number r) :=
  ⟨Quotient.map (Fraction.neg r) (fun a b ha => by
    change (Fraction.neg r a).value = (Fraction.neg r b).value
    simp only [Fraction.value_neg, show a.value = b.value from ha])⟩

instance : Inv (Number r) :=
  ⟨Quotient.map (Fraction.inv r) (fun a b ha => by
    change (Fraction.inv r a).value = (Fraction.inv r b).value
    simp only [Fraction.value_inv, show a.value = b.value from ha])⟩

instance : Sub (Number r) := ⟨fun x y => x + -y⟩
instance : Div (Number r) := ⟨fun x y => x * y⁻¹⟩

@[simp] theorem value_zero : value r 0 = 0 := by change value r (ofBase r 0) = _; simp
@[simp] theorem value_one : value r 1 = 1 := by change value r (ofBase r 1) = _; simp

@[simp] theorem value_add (a b : Number r) :
    value r (a+b) = value r a + value r b := by
  induction a,b using Quotient.inductionOn₂ with
  | _ a b => exact Fraction.value_add r a b

@[simp] theorem value_mul (a b : Number r) :
    value r (a*b) = value r a * value r b := by
  induction a,b using Quotient.inductionOn₂ with
  | _ a b => exact Fraction.value_mul r a b

omit [IsStrictOrderedRing K] in
@[simp] theorem value_neg (a : Number r) :
    value r (-a) = -value r a := by
  induction a using Quotient.inductionOn
  exact Fraction.value_neg r _

@[simp] theorem value_inv (a : Number r) :
    value r a⁻¹ = (value r a)⁻¹ := by
  induction a using Quotient.inductionOn
  exact Fraction.value_inv r _

@[simp] theorem value_sub (a b : Number r) :
    value r (a-b) = value r a - value r b := by
  change value r (a + -b) = _
  simp [sub_eq_add_neg]

@[simp] theorem value_div (a b : Number r) :
    value r (a/b) = value r a / value r b := by
  change value r (a*b⁻¹) = _
  simp [div_eq_mul_inv]

def sign (a : Number r) : Side :=
  Quotient.liftOn a (Fraction.sign r) fun x y h => by
    rw [Fraction.sign_correct, Fraction.sign_correct, show x.value = y.value from h]

theorem sign_correct (a : Number r) : sign r a = side (value r a) 0 := by
  induction a using Quotient.inductionOn
  exact Fraction.sign_correct r _


instance : NatCast (Number r) := ⟨fun n => ofBase r (n : K)⟩
instance : IntCast (Number r) := ⟨fun n => ofBase r (n : K)⟩
instance : NNRatCast (Number r) := ⟨fun q => ofBase r (q : K)⟩
instance : RatCast (Number r) := ⟨fun q => ofBase r (q : K)⟩

instance : SMul ℕ (Number r) := ⟨fun n a => (n : Number r)*a⟩
instance : SMul ℤ (Number r) := ⟨fun n a => (n : Number r)*a⟩
instance : SMul ℚ≥0 (Number r) := ⟨fun q a => (q : Number r)*a⟩
instance : SMul ℚ (Number r) := ⟨fun q a => (q : Number r)*a⟩

instance : Pow (Number r) ℕ := ⟨fun a n => npowRec n a⟩
instance : Pow (Number r) ℤ := ⟨fun a n => zpowRec npowRec n a⟩

@[simp] theorem value_natCast (n : ℕ) : value r (n : Number r) = n := by
  change value r (ofBase r (n : K)) = _; simp

@[simp] theorem value_intCast (n : ℤ) : value r (n : Number r) = n := by
  change value r (ofBase r (n : K)) = _; simp

@[simp] theorem value_nnratCast (q : ℚ≥0) : value r (q : Number r) = q := by
  change value r (ofBase r (q : K)) = _; simp

@[simp] theorem value_ratCast (q : ℚ) : value r (q : Number r) = q := by
  change value r (ofBase r (q : K)) = _; simp

@[simp] theorem value_nsmul (n : ℕ) (a : Number r) : value r (n • a) = (n : ℝ)*value r a := by
  change value r ((n : Number r)*a) = _
  simp

@[simp] theorem value_zsmul (n : ℤ) (a : Number r) : value r (n • a) = (n : ℝ)*value r a := by
  change value r ((n : Number r)*a) = _
  simp

instance : Field (Number r) where
  zero := (0 : Number r)
  one := (1 : Number r)
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  sub := (· - ·)
  inv := (·⁻¹)
  div := (· / ·)
  add_assoc a b c := value_injective r (by simp [add_assoc])
  zero_add a := value_injective r (by simp)
  add_zero a := value_injective r (by simp)
  nsmul n a := (n : Number r)*a
  nsmul_zero a := value_injective r (by simp)
  nsmul_succ n a := value_injective r (by simp [Nat.cast_succ, add_mul])
  add_comm a b := value_injective r (by simp [add_comm])
  mul_assoc a b c := value_injective r (by simp [mul_assoc])
  one_mul a := value_injective r (by simp)
  mul_one a := value_injective r (by simp)
  npow := npowRec
  zero_mul a := value_injective r (by simp)
  mul_zero a := value_injective r (by simp)
  left_distrib a b c := value_injective r (by simp [mul_add])
  right_distrib a b c := value_injective r (by simp [add_mul])
  natCast n := ofBase r (n : K)
  natCast_zero := value_injective r (by simp)
  natCast_succ n := value_injective r (by simp [Nat.cast_succ])
  zsmul n a := (n : Number r)*a
  zsmul_zero' a := value_injective r (by simp)
  zsmul_succ' n a := value_injective r (by simp [Nat.cast_succ, add_mul])
  zsmul_neg' n a := value_injective r (by simp [Int.cast_negSucc]; ring)
  neg_add_cancel a := value_injective r (by simp)
  intCast n := ofBase r (n : K)
  intCast_ofNat n := value_injective r (by simp)
  intCast_negSucc n := value_injective r (by simp [Int.cast_negSucc])
  mul_comm a b := value_injective r (by simp [mul_comm])
  zpow := zpowRec npowRec
  exists_pair_ne := ⟨(0 : Number r), (1 : Number r), fun h =>
    (zero_ne_one : (0 : ℝ) ≠ 1) (by simpa using congrArg (value r) h)⟩
  mul_inv_cancel a ha := value_injective r (by
    have h : value r a ≠ 0 := by
      rw [← value_zero r]
      exact fun e => ha (value_injective r e)
    simp [h])
  inv_zero := value_injective r (by simp)
  nnratCast q := ofBase r (q : K)
  ratCast q := ofBase r (q : K)
  nnratCast_def q := value_injective r (by simp [NNRat.cast_def])
  ratCast_def q := value_injective r (by simp [Rat.cast_def])
  nnqsmul q a := (q : Number r)*a
  qsmul q a := (q : Number r)*a

def compareNumbers (x y : Number r) : Ordering :=
  match sign r (x-y) with
  | .below => .lt
  | .on => .eq
  | .above => .gt

theorem compareNumbers_correct (x y : Number r) :
    compareNumbers r x y = compare (value r x) (value r y) := by
  unfold compareNumbers
  rw [sign_correct, value_sub]
  rcases lt_trichotomy (value r x) (value r y) with h | h | h
  · simp [side, sub_neg.mpr h, compare_lt_iff_lt.mpr h]
  · simp [side, h]
  · have hl : ¬value r x - value r y < 0 := (sub_pos.mpr h).not_gt
    simp [side, hl, (sub_pos.mpr h).ne', compare_gt_iff_gt.mpr h]

instance : LE (Number r) := ⟨fun a b => compareNumbers r a b ≠ .gt⟩
instance : LT (Number r) := ⟨fun a b => compareNumbers r a b = .lt⟩
instance (a b : Number r) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (compareNumbers r a b ≠ .gt))
instance (a b : Number r) : Decidable (a < b) :=
  inferInstanceAs (Decidable (compareNumbers r a b = .lt))

theorem value_le {a b : Number r} : value r a ≤ value r b ↔ a ≤ b := by
  change _ ↔ compareNumbers r a b ≠ .gt
  rw [compareNumbers_correct, ne_eq, compare_gt_iff_gt, not_lt]

theorem value_lt {a b : Number r} : value r a < value r b ↔ a < b := by
  change _ ↔ compareNumbers r a b = .lt
  rw [compareNumbers_correct, compare_lt_iff_lt]

theorem numerator_zero (a : Fraction r) :
    zeroAt model r a.num = true ↔ a.value = 0 := by
  rw [zeroAt_correct, IsRoot.def, Fraction.value, div_eq_zero_iff]
  exact (or_iff_left a.den_ne_zero).symm

def isZero (a : Number r) : Bool :=
  Quotient.liftOn a (fun v => zeroAt model r v.num) (fun x y h => by
    apply Bool.eq_iff_iff.mpr
    rw [numerator_zero, numerator_zero, show x.value = y.value from h])

theorem isZero_correct (a : Number r) : isZero r a = true ↔ value r a = 0 := by
  induction a using Quotient.inductionOn
  exact numerator_zero r _

instance : DecidableEq (Number r) := fun a b =>
  decidable_of_iff (isZero r (a-b) = true) (by
    rw [isZero_correct, value_sub, sub_eq_zero, (value_injective r).eq_iff])

instance : Ord (Number r) := ⟨compareNumbers r⟩
instance : Min (Number r) := ⟨fun a b => if a ≤ b then a else b⟩
instance : Max (Number r) := ⟨fun a b => if a ≤ b then b else a⟩

instance : LinearOrder (Number r) where
  le_refl a := (value_le r).mp le_rfl
  le_trans a b c hab hbc :=
    (value_le r).mp (((value_le r).mpr hab).trans ((value_le r).mpr hbc))
  le_antisymm a b hab hba :=
    value_injective r (le_antisymm ((value_le r).mpr hab) ((value_le r).mpr hba))
  lt_iff_le_not_ge a b := by
    rw [← value_lt r, ← value_le r, ← value_le r, lt_iff_le_not_ge]
  le_total a b := (le_total (value r a) (value r b)).imp (value_le r).mp (value_le r).mp
  toDecidableLE := fun _ _ => inferInstance
  toDecidableLT := fun _ _ => inferInstance
  toDecidableEq := inferInstance
  compare_eq_compareOfLessAndEq a b := by
    change compareNumbers r a b = _
    rw [compareNumbers_correct, LinearOrder.compare_eq_compareOfLessAndEq]
    simp only [compareOfLessAndEq, value_lt r, (value_injective r).eq_iff]

instance : IsStrictOrderedRing (Number r) :=
  Function.Injective.isStrictOrderedRing (value r) (value_zero r) (value_one r)
    (value_add r) (value_mul r) (value_le r) (value_lt r)

noncomputable def embedding : Number r →+* ℝ where
  toFun := value r
  map_zero' := value_zero r
  map_one' := value_one r
  map_mul' := value_mul r
  map_add' := value_add r

theorem embedding_strictMono : StrictMono (embedding r) := fun _ _ h => (value_lt r).mpr h

theorem realModel : RealModel (Number r) := ⟨embedding r, embedding_strictMono r⟩

theorem realModel_hom : (realModel r).hom = embedding r :=
  (realModel r).hom_eq _ (embedding_strictMono r)

def baseMap : K →+* Number r where
  toFun := ofBase r
  map_zero' := rfl
  map_one' := rfl
  map_mul' x y := value_injective r (by simp)
  map_add' x y := value_injective r (by simp)

@[simp] theorem embedding_baseMap (x : K) : embedding r (baseMap r x) = model.hom x :=
  value_ofBase r x

@[simp] theorem embedding_generator : embedding r (generator r) = r.value := value_generator r

end CertifiedTopology.AlgebraicField
