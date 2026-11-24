module

public import CertifiedTopology.DensePolynomial

@[expose] public section

namespace CertifiedTopology

open Polynomial

/-- Canonical ascending coefficient lists. Nested instances represent
    multivariate polynomials in a fixed projection order. -/
structure PolynomialData (K : Type) [Zero K] [DecidableEq K] where
  coefficients : List K
  normalized : DensePolynomial.trim coefficients = coefficients
  deriving Repr

namespace PolynomialData

variable {K : Type} [CommRing K] [DecidableEq K]

theorem trim_idem (p : List K) :
    DensePolynomial.trim (DensePolynomial.trim p) = DensePolynomial.trim p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    cases h : DensePolynomial.trim p with
    | nil =>
      have e : DensePolynomial.trim (a :: p) = (if a = 0 then [] else [a]) := by
        simp only [DensePolynomial.trim, h]
      rw [e]
      by_cases ha : a = 0 <;> simp [DensePolynomial.trim, ha]
    | cons b q =>
      have e : DensePolynomial.trim (a :: p) = a :: b :: q := by
        simp only [DensePolynomial.trim, h]
      rw [h] at ih
      rw [e]
      conv_lhs => rw [DensePolynomial.trim]
      rw [ih]

def ofCoefficients (p : List K) : PolynomialData K :=
  ⟨DensePolynomial.trim p, trim_idem p⟩

noncomputable def polynomial (p : PolynomialData K) : Polynomial K :=
  DensePolynomial.polynomial p.coefficients

@[simp] theorem polynomial_ofCoefficients (p : List K) :
    (ofCoefficients p).polynomial = DensePolynomial.polynomial p :=
  DensePolynomial.polynomial_trim p

theorem polynomial_injective : Function.Injective (polynomial (K := K)) := by
  intro a b eq
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  change DensePolynomial.polynomial a = DensePolynomial.polynomial b at eq
  have an := DensePolynomial.trim_eq_nil a
  have bn := DensePolynomial.trim_eq_nil b
  rw [ha] at an
  rw [hb] at bn
  have lena := DensePolynomial.degree_trim a
  have lenb := DensePolynomial.degree_trim b
  rw [ha, eq] at lena
  rw [hb] at lenb
  have zero : a.length = 0 ↔ b.length = 0 := by simp [an, bn, eq]
  have len : a.length = b.length := by omega
  congr 1
  apply List.ext_getElem len
  intro i hi hj
  have e := congrArg (fun p : Polynomial K => p.coeff i) eq
  simpa only [DensePolynomial.coeff_polynomial, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj, Option.getD_some] using e

instance : DecidableEq (PolynomialData K) := fun a b =>
  decidable_of_iff (a.coefficients = b.coefficients) ⟨fun e => by cases a; cases b; cases e; rfl, congrArg coefficients⟩

def constant (a : K) : PolynomialData K := ofCoefficients [a]

instance : Zero (PolynomialData K) := ⟨constant 0⟩
instance : One (PolynomialData K) := ⟨constant 1⟩
instance : Add (PolynomialData K) := ⟨fun a b => ofCoefficients (DensePolynomial.add a.coefficients b.coefficients)⟩
instance : Mul (PolynomialData K) := ⟨fun a b => ofCoefficients (DensePolynomial.mul a.coefficients b.coefficients)⟩
instance : Neg (PolynomialData K) := ⟨fun a => ofCoefficients (DensePolynomial.neg a.coefficients)⟩
instance : Sub (PolynomialData K) := ⟨fun a b => a + -b⟩
instance : NatCast (PolynomialData K) := ⟨fun n => constant n⟩
instance : IntCast (PolynomialData K) := ⟨fun n => constant n⟩
instance : SMul ℕ (PolynomialData K) := ⟨fun n a => (n : PolynomialData K)*a⟩
instance : SMul ℤ (PolynomialData K) := ⟨fun n a => (n : PolynomialData K)*a⟩

def X : PolynomialData K := ofCoefficients [0,1]

@[simp] theorem polynomial_constant (a : K) : (constant a).polynomial = C a := by
  simp [constant, DensePolynomial.polynomial]

@[simp] theorem polynomial_X : (X : PolynomialData K).polynomial = Polynomial.X := by
  simp [X, DensePolynomial.polynomial]

@[simp] theorem polynomial_zero : (0 : PolynomialData K).polynomial = 0 := by
  change (constant (0 : K)).polynomial = _
  simp

@[simp] theorem polynomial_one : (1 : PolynomialData K).polynomial = 1 := by
  change (constant (1 : K)).polynomial = _
  simp

@[simp] theorem polynomial_plus (a b : PolynomialData K) :
    (a + b).polynomial = a.polynomial + b.polynomial :=
  (polynomial_ofCoefficients _).trans (DensePolynomial.polynomial_add _ _)

@[simp] theorem polynomial_times (a b : PolynomialData K) :
    (a * b).polynomial = a.polynomial * b.polynomial :=
  (polynomial_ofCoefficients _).trans (DensePolynomial.polynomial_mul _ _)

@[simp] theorem polynomial_minus (a : PolynomialData K) :
    (-a).polynomial = -a.polynomial :=
  (polynomial_ofCoefficients _).trans (DensePolynomial.polynomial_neg _)

@[simp] theorem polynomial_subtract (a b : PolynomialData K) :
    (a - b).polynomial = a.polynomial - b.polynomial := by
  change (a + -b).polynomial = _
  simp [sub_eq_add_neg]

@[simp] theorem polynomial_natCast (n : ℕ) :
    (n : PolynomialData K).polynomial = n := by
  change (constant (n : K)).polynomial = _
  simp

@[simp] theorem polynomial_intCast (n : ℤ) :
    (n : PolynomialData K).polynomial = n := by
  change (constant (n : K)).polynomial = _
  simp

@[simp] theorem polynomial_nsmul (n : ℕ) (a : PolynomialData K) :
    (n • a).polynomial = n * a.polynomial := by
  change ((n : PolynomialData K)*a).polynomial = _
  simp

@[simp] theorem polynomial_zsmul (n : ℤ) (a : PolynomialData K) :
    (n • a).polynomial = n * a.polynomial := by
  change ((n : PolynomialData K)*a).polynomial = _
  simp

instance : CommRing (PolynomialData K) where
  zero := (0 : PolynomialData K)
  one := (1 : PolynomialData K)
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  sub := (· - ·)
  add_assoc _ _ _ := polynomial_injective (by simp [add_assoc])
  zero_add _ := polynomial_injective (by simp)
  add_zero _ := polynomial_injective (by simp)
  nsmul n a := (n : PolynomialData K)*a
  nsmul_zero _ := polynomial_injective (by simp)
  nsmul_succ _ _ := polynomial_injective (by simp [Nat.cast_succ, add_mul])
  add_comm _ _ := polynomial_injective (by simp [add_comm])
  mul_assoc _ _ _ := polynomial_injective (by simp [mul_assoc])
  one_mul _ := polynomial_injective (by simp)
  mul_one _ := polynomial_injective (by simp)
  zero_mul _ := polynomial_injective (by simp)
  mul_zero _ := polynomial_injective (by simp)
  left_distrib _ _ _ := polynomial_injective (by simp [mul_add])
  right_distrib _ _ _ := polynomial_injective (by simp [add_mul])
  natCast n := constant n
  natCast_zero := polynomial_injective (by simp)
  natCast_succ _ := polynomial_injective (by simp [Nat.cast_succ])
  zsmul n a := (n : PolynomialData K)*a
  zsmul_zero' _ := polynomial_injective (by simp)
  zsmul_succ' _ _ := polynomial_injective (by simp [Nat.cast_succ, add_mul])
  zsmul_neg' _ _ := polynomial_injective (by simp [Int.cast_negSucc]; ring)
  neg_add_cancel _ := polynomial_injective (by simp)
  intCast n := constant n
  intCast_ofNat _ := polynomial_injective (by simp)
  intCast_negSucc _ := polynomial_injective (by simp [Int.cast_negSucc])
  mul_comm _ _ := polynomial_injective (by simp [mul_comm])

noncomputable def embedding : PolynomialData K →+* Polynomial K where
  toFun := polynomial
  map_zero' := polynomial_zero
  map_one' := polynomial_one
  map_add' := polynomial_plus
  map_mul' := polynomial_times

def coefficient (p : PolynomialData K) (i : ℕ) : K := p.coefficients[i]?.getD 0

def natDegree (p : PolynomialData K) : ℕ := p.coefficients.length - 1

def derivative (p : PolynomialData K) : PolynomialData K :=
  ofCoefficients (DensePolynomial.derivative p.coefficients)

def evaluate (p : PolynomialData K) (x : K) : K := DensePolynomial.eval p.coefficients x

@[simp] theorem coefficient_correct (p : PolynomialData K) (i : ℕ) :
    coefficient p i = p.polynomial.coeff i := (DensePolynomial.coeff_polynomial _ _).symm

@[simp] theorem natDegree_correct (p : PolynomialData K) : p.natDegree = p.polynomial.natDegree := by
  simpa only [natDegree, polynomial, p.normalized] using (DensePolynomial.degree_trim p.coefficients).symm

@[simp] theorem derivative_correct (p : PolynomialData K) :
    p.derivative.polynomial = p.polynomial.derivative := by
  rw [derivative, polynomial_ofCoefficients, DensePolynomial.polynomial_derivative]
  rfl

@[simp] theorem evaluate_correct (p : PolynomialData K) (x : K) :
    p.evaluate x = p.polynomial.eval x := DensePolynomial.eval_correct _ _

end PolynomialData
end CertifiedTopology
