module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Tactic

@[expose] public section

namespace CertifiedTopology.DensePolynomial

open Polynomial

/-- Coefficients in ascending degree order, with missing coefficients equal to zero. -/
abbrev Coefficients (R : Type) := List R

variable {R S : Type}

noncomputable def polynomial [Semiring R] : Coefficients R → Polynomial R
  | [] => 0
  | a :: p => C a + X * polynomial p

@[simp] theorem coeff_polynomial [Semiring R] (p : Coefficients R) (i : ℕ) :
    (polynomial p).coeff i = p[i]?.getD 0 := by
  induction p generalizing i with
  | nil => simp [polynomial]
  | cons a p ih =>
    cases i with
    | zero => simp [polynomial]
    | succ i => simp [polynomial, coeff_X_mul, ih]

theorem natDegree_le [Semiring R] (p : Coefficients R) :
    (polynomial p).natDegree ≤ p.length - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_polynomial, List.getElem?_eq_none (by omega)]
  rfl

def eval₂ [Semiring R] [CommSemiring S] (f : R →+* S) (x : S) : Coefficients R → S
  | [] => 0
  | a :: p => f a + x * eval₂ f x p

@[simp] theorem eval₂_correct [Semiring R] [CommSemiring S] (f : R →+* S) (x : S)
    (p : Coefficients R) : eval₂ f x p = ((polynomial p).map f).eval x := by
  induction p with
  | nil => simp [eval₂, polynomial]
  | cons a p ih => simp [eval₂, polynomial, ih, eval_mul]

def eval [CommSemiring R] (p : Coefficients R) (x : R) : R := eval₂ (RingHom.id R) x p

@[simp] theorem eval_correct [CommSemiring R] (p : Coefficients R) (x : R) :
    eval p x = (polynomial p).eval x := by simp [eval]

def add [Add R] : Coefficients R → Coefficients R → Coefficients R
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

@[simp] theorem polynomial_add [Semiring R] (p q : Coefficients R) :
    polynomial (add p q) = polynomial p + polynomial q := by
  induction p generalizing q with
  | nil => simp [add, polynomial]
  | cons a p ih =>
    cases q with
    | nil => simp [add, polynomial]
    | cons b q => simp [add, polynomial, ih, mul_add, add_add_add_comm]

def neg [Neg R] (p : Coefficients R) : Coefficients R := p.map (- ·)

@[simp] theorem polynomial_neg [Ring R] (p : Coefficients R) :
    polynomial (neg p) = -polynomial p := by
  induction p with
  | nil => simp [neg, polynomial]
  | cons a p ih =>
    change polynomial ((-a) :: neg p) = _
    simp [polynomial, ih, add_comm]

def sub [Add R] [Neg R] (p q : Coefficients R) : Coefficients R := add p (neg q)

@[simp] theorem polynomial_sub [Ring R] (p q : Coefficients R) :
    polynomial (sub p q) = polynomial p - polynomial q := by simp [sub, sub_eq_add_neg]

def scale [Mul R] (a : R) (p : Coefficients R) : Coefficients R := p.map (a * ·)

@[simp] theorem polynomial_scale [CommSemiring R] (a : R) (p : Coefficients R) :
    polynomial (scale a p) = C a * polynomial p := by
  induction p with
  | nil => simp [scale, polynomial]
  | cons c p ih =>
    change polynomial ((a*c) :: scale a p) = _
    simp [polynomial, ih, mul_add, mul_left_comm]

def shift [Zero R] : ℕ → Coefficients R → Coefficients R
  | 0, p => p
  | n+1, p => 0 :: shift n p

@[simp] theorem polynomial_shift [Semiring R] (n : ℕ) (p : Coefficients R) :
    polynomial (shift n p) = X ^ n * polynomial p := by
  induction n with
  | zero => simp [shift]
  | succ n ih => simp [shift, polynomial, ih, pow_succ', mul_assoc]

def mul [Semiring R] : Coefficients R → Coefficients R → Coefficients R
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

@[simp] theorem polynomial_mul [CommSemiring R] (p q : Coefficients R) :
    polynomial (mul p q) = polynomial p * polynomial q := by
  induction p with
  | nil => simp [mul, polynomial]
  | cons a p ih => simp [mul, polynomial, ih, add_mul, mul_assoc]

def derivativeFrom [Semiring R] : ℕ → Coefficients R → Coefficients R
  | _, [] => []
  | n, a :: p => (n : R) * a :: derivativeFrom (n + 1) p

def derivative [Semiring R] (p : Coefficients R) : Coefficients R :=
  derivativeFrom 1 p.tail

private theorem derivativeFrom_coeff [Semiring R] (n : ℕ) (p : Coefficients R) (i : ℕ) :
    (derivativeFrom n p)[i]?.getD 0 = (↑(n+i) : R) * p[i]?.getD 0 := by
  induction p generalizing n i with
  | nil => simp [derivativeFrom]
  | cons a p ih =>
    cases i with
    | zero => simp [derivativeFrom]
    | succ i => simpa [derivativeFrom, Nat.add_right_comm, Nat.add_assoc, Nat.add_comm 1 i]
        using ih (n+1) i

@[simp] theorem polynomial_derivative [CommSemiring R] (p : Coefficients R) :
    polynomial (derivative p) = (polynomial p).derivative := by
  ext i
  simp only [derivative, coeff_polynomial, derivativeFrom_coeff, Polynomial.coeff_derivative]
  rw [mul_comm, Nat.add_comm]
  cases p <;> simp

/-- Remove trailing zeros so that the length records the actual degree. -/
def trim [Zero R] [DecidableEq R] : Coefficients R → Coefficients R
  | [] => []
  | a :: p =>
    match trim p with
    | [] => if a = 0 then [] else [a]
    | b :: q => a :: b :: q

@[simp] theorem polynomial_trim [Semiring R] [DecidableEq R] (p : Coefficients R) :
    polynomial (trim p) = polynomial p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    cases h : trim p with
    | nil =>
      have hp : polynomial p = 0 := ih.symm.trans (congrArg polynomial h)
      simp [trim, h, polynomial, hp]
      split <;> simp_all [polynomial]
    | cons b q =>
      simp only [trim, h, polynomial]
      rw [← ih, h, polynomial]

def lead [Zero R] (p : Coefficients R) : R := p.getLastD 0

theorem lead_trim_ne_zero [Zero R] [DecidableEq R] (p : Coefficients R) (h : trim p ≠ []) :
    lead (trim p) ≠ 0 := by
  induction p with
  | nil => exact (h rfl).elim
  | cons a p ih =>
    cases e : trim p with
    | nil =>
      simp [trim, e] at h ⊢
      split <;> simp_all [lead]
    | cons b q =>
      have hn : trim p ≠ [] := by simp [e]
      simpa [trim, e, lead] using ih hn

private theorem coeff_last [Semiring R] (p : Coefficients R) (h : p ≠ []) :
    (polynomial p).coeff (p.length - 1) = lead p := by
  induction p with
  | nil => exact (h rfl).elim
  | cons a p ih =>
    cases p with
    | nil => simp [polynomial, lead]
    | cons b q =>
      have e : (a :: b :: q).length - 1 = ((b :: q).length - 1) + 1 := by simp
      rw [e, polynomial, coeff_add, coeff_C, ite_eq_right (by omega), zero_add, coeff_X_mul]
      simpa [lead] using ih (by simp)

theorem degree_trim [Semiring R] [DecidableEq R] (p : Coefficients R) :
    (polynomial p).natDegree = (trim p).length - 1 := by
  cases h : trim p with
  | nil => simpa [h, polynomial] using congrArg Polynomial.natDegree (polynomial_trim p).symm
  | cons a q =>
    have hn : trim p ≠ [] := by simp [h]
    rw [← polynomial_trim p]
    have eq := le_antisymm (natDegree_le (trim p)) (le_natDegree_of_ne_zero
      ((coeff_last _ hn).trans_ne (lead_trim_ne_zero p hn)))
    simpa only [h] using eq

theorem leadingCoeff_trim [Semiring R] [DecidableEq R] (p : Coefficients R) :
    (polynomial p).leadingCoeff = lead (trim p) := by
  rw [← coeff_natDegree, degree_trim, ← polynomial_trim p]
  match h : trim p with
  | [] => simp [lead, polynomial]
  | _ :: _ => exact coeff_last _ (by simp)

@[simp] theorem trim_eq_nil [Semiring R] [DecidableEq R] (p : Coefficients R) :
    trim p = [] ↔ polynomial p = 0 := by
  constructor
  · intro h
    rw [← polynomial_trim p, h, polynomial]
  · intro h
    by_contra hn
    exact lead_trim_ne_zero p hn (by rw [← leadingCoeff_trim, h, leadingCoeff_zero])

theorem trim_length_le_iff [Semiring R] [DecidableEq R] (p : Coefficients R) (n : ℕ) :
    (trim p).length ≤ n ↔ ∀ i ≥ n, (polynomial p).coeff i = 0 := by
  constructor
  · intro h i hi
    rw [← polynomial_trim p, coeff_polynomial, List.getElem?_eq_none (h.trans hi)]
    rfl
  · intro h
    by_contra! H
    have hn : trim p ≠ [] := by
      rintro he
      simp [he] at H
    have hz := h ((trim p).length - 1) (by omega)
    rw [← polynomial_trim p, coeff_last _ hn] at hz
    exact lead_trim_ne_zero p hn hz

section Division

variable [Field R] [DecidableEq R]

def cancellationDegree (p q : Coefficients R) : ℕ := (trim p).length - (trim q).length

def cancellationCoefficient (p q : Coefficients R) : R :=
  lead (trim p) / lead (trim q)

def cancel (p q : Coefficients R) : Coefficients R :=
  sub p (shift (cancellationDegree p q) (scale (cancellationCoefficient p q) q))

theorem cancel_shorter (p q : Coefficients R)
    (h : (trim q).length ≤ (trim p).length ∧ trim q ≠ []) :
    (trim (cancel p q)).length < (trim p).length := by
  have hq : 0 < (trim q).length := List.length_pos_iff.mpr h.2
  have hd : cancellationDegree p q ≤ (trim p).length - 1 := by
    unfold cancellationDegree
    omega
  have he : (trim p).length - 1 - cancellationDegree p q = (trim q).length - 1 := by
    unfold cancellationDegree
    omega
  apply Nat.lt_of_le_of_lt ((trim_length_le_iff _ ((trim p).length - 1)).mpr ?_) (by omega)
  intro i hi
  simp only [cancel, polynomial_sub, polynomial_scale, polynomial_shift, coeff_sub]
  conv_lhs => enter [2, 2]; rw [show i = (i - cancellationDegree p q) + cancellationDegree p q by omega]
  rw [coeff_X_pow_mul, coeff_C_mul]
  by_cases eq : i = (trim p).length - 1
  · subst i
    rw [he, ← degree_trim p, ← degree_trim q, coeff_natDegree, coeff_natDegree,
      leadingCoeff_trim, leadingCoeff_trim, cancellationCoefficient, div_mul_cancel₀ _ (lead_trim_ne_zero q h.2),
      sub_self]
  · have hz := (trim_length_le_iff p (trim p).length).mp le_rfl i (by omega)
    have hz' := (trim_length_le_iff q (trim q).length).mp le_rfl (i - cancellationDegree p q) (by omega)
    rw [hz, hz', mul_zero, sub_zero]

/-- Euclidean division with a decreasing normalized dividend. For a zero
    divisor the quotient is zero and the remainder is the dividend. -/
def divmod (p q : Coefficients R) : Coefficients R × Coefficients R :=
  if _h : (trim q).length ≤ (trim p).length ∧ trim q ≠ [] then
    let d := divmod (cancel p q) q
    (add d.1 (shift (cancellationDegree p q) [cancellationCoefficient p q]), d.2)
  else ([], trim p)
termination_by (trim p).length
decreasing_by exact cancel_shorter p q _h

theorem divmod_spec (p q : Coefficients R) :
    polynomial p = polynomial (divmod p q).1 * polynomial q + polynomial (divmod p q).2 ∧
      (trim q = [] ∨ (trim (divmod p q).2).length < (trim q).length) := by
  rw [divmod]
  split
  · rename_i h
    let d := divmod (cancel p q) q
    have ih := divmod_spec (cancel p q) q
    refine ⟨?_, ih.2⟩
    change polynomial p = polynomial
      (add d.1 (shift (cancellationDegree p q) [cancellationCoefficient p q])) * _ + _
    have eq : polynomial (cancel p q) = polynomial d.1 * polynomial q + polynomial d.2 := ih.1
    simp only [cancel, polynomial_sub, polynomial_shift, polynomial_scale] at eq
    simp only [polynomial_add, polynomial_shift, polynomial, mul_zero, add_zero]
    linear_combination eq
  · rename_i h
    refine ⟨by simp [polynomial], ?_⟩
    by_cases hn : trim q = []
    · exact Or.inl hn
    · refine Or.inr ?_
      have len : (trim p).length < (trim q).length := lt_of_not_ge (fun hg => h ⟨hg, hn⟩)
      have eq : (trim (trim p)).length = (trim p).length := by
        have eq := (degree_trim (trim p)).symm.trans ((congrArg Polynomial.natDegree
          (polynomial_trim p)).trans (degree_trim p))
        have he : trim (trim p) = [] ↔ trim p = [] := by rw [trim_eq_nil, polynomial_trim, trim_eq_nil]
        simp only [← List.length_eq_zero_iff] at he
        omega
      simpa only [eq] using len
termination_by (trim p).length
decreasing_by exact cancel_shorter p q (by assumption)

/-- The last nonzero Euclidean remainder. Its unit normalization is irrelevant. -/
def gcd (p q : Coefficients R) : Coefficients R :=
  if _h : trim q = [] then trim p else gcd q (divmod p q).2
termination_by (trim q).length
decreasing_by exact (divmod_spec p q).2.resolve_left _h

theorem gcd_spec [Field S] (f : R →+* S) (p q : Coefficients R) (a : Polynomial S) :
    a ∣ (polynomial (gcd p q)).map f ↔
      a ∣ (polynomial p).map f ∧ a ∣ (polynomial q).map f := by
  rw [gcd]
  split
  · rename_i h
    simp [show polynomial q = 0 from (trim_eq_nil q).mp h]
  · rename_i h
    rw [gcd_spec f q (divmod p q).2 a]
    have eq := congrArg (Polynomial.map f) (divmod_spec p q).1
    simp only [Polynomial.map_add, Polynomial.map_mul] at eq
    constructor
    · rintro ⟨hq, hr⟩
      refine ⟨?_, hq⟩
      rw [eq]
      exact dvd_add (dvd_mul_of_dvd_right hq _) hr
    · rintro ⟨hp, hq⟩
      refine ⟨hq, ?_⟩
      have hr := eq_sub_of_add_eq' eq.symm
      rw [hr]
      exact dvd_sub hp (dvd_mul_of_dvd_right hq _)
termination_by (trim q).length
decreasing_by exact (divmod_spec p q).2.resolve_left (by assumption)

end Division
end CertifiedTopology.DensePolynomial
