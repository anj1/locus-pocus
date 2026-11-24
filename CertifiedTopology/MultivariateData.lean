module

public import CertifiedTopology.PolynomialData
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Algebra.Polynomial

@[expose] public section

namespace CertifiedTopology

namespace PolynomialData

variable {R S : Type} [CommRing R] [DecidableEq R] [CommRing S]

/-- Executable evaluation of the outer variable after mapping coefficients. -/
def evalHom (φ : R →+* S) (x : S) : PolynomialData R →+* S where
  toFun p := DensePolynomial.eval₂ φ x p.coefficients
  map_zero' := by
    rw [DensePolynomial.eval₂_correct]
    change ((0 : PolynomialData R).polynomial.map φ).eval x = 0
    simp
  map_one' := by
    rw [DensePolynomial.eval₂_correct]
    change ((1 : PolynomialData R).polynomial.map φ).eval x = 1
    simp
  map_add' p q := by
    simp only [DensePolynomial.eval₂_correct]
    change ((p+q).polynomial.map φ).eval x = (p.polynomial.map φ).eval x + (q.polynomial.map φ).eval x
    simp
  map_mul' p q := by
    simp only [DensePolynomial.eval₂_correct]
    change ((p*q).polynomial.map φ).eval x = (p.polynomial.map φ).eval x * (q.polynomial.map φ).eval x
    simp [Polynomial.map_mul]

@[simp] theorem evalHom_correct (φ : R →+* S) (x : S) (p : PolynomialData R) :
    evalHom φ x p = (p.polynomial.map φ).eval x := DensePolynomial.eval₂_correct _ _ _

@[simp] theorem evalHom_constant (φ : R →+* S) (x : S) (a : R) :
    evalHom φ x (constant a) = φ a := by simp

@[simp] theorem evalHom_X (φ : R →+* S) (x : S) :
    evalHom φ x X = x := by simp

def mapData [DecidableEq S] (φ : R →+* S) (p : PolynomialData R) : PolynomialData S :=
  ofCoefficients (p.coefficients.map φ)

@[simp] theorem polynomial_mapData [DecidableEq S] (φ : R →+* S) (p : PolynomialData R) :
    (mapData φ p).polynomial = p.polynomial.map φ := by
  change (ofCoefficients _).polynomial = (DensePolynomial.polynomial p.coefficients).map φ
  rw [polynomial_ofCoefficients]
  induction p.coefficients with
  | nil => simp [DensePolynomial.polynomial]
  | cons a p ih =>
    simp only [List.map_cons, DensePolynomial.polynomial, Polynomial.map_add, Polynomial.map_C,
      Polynomial.map_mul, Polynomial.map_X, ih]

def constantHom : R →+* PolynomialData R where
  toFun := constant
  map_zero' := rfl
  map_one' := rfl
  map_add' a b := polynomial_injective (by simp)
  map_mul' a b := polynomial_injective (by simp)

end PolynomialData

/-- The executable coefficient rings, one for each position in the
    cylindrical variable order. -/
structure PolynomialRingData where
  carrier : Type
  [ring : CommRing carrier]
  [eq : DecidableEq carrier]

attribute [instance] PolynomialRingData.ring PolynomialRingData.eq

def nestedPolynomials (K : Type) [CommRing K] [DecidableEq K] : ℕ → PolynomialRingData
  | 0 => ⟨K⟩
  | n+1 => ⟨PolynomialData (nestedPolynomials K n).carrier⟩

abbrev Multi (K : Type) [CommRing K] [DecidableEq K] (n : ℕ) := (nestedPolynomials K n).carrier

namespace Multi

variable {K S : Type} [CommRing K] [DecidableEq K] [CommRing S]

def evalHom (φ : K →+* S) : {n : ℕ} → (Fin n → S) → Multi K n →+* S
  | 0, _ => φ
  | n+1, x => PolynomialData.evalHom (evalHom φ (fun i => x i.castSucc)) (x (Fin.last n))

theorem evalHom_snoc (φ : K →+* S) {n : ℕ} (x : Fin n → S) (y : S) (p : Multi K (n+1)) :
    evalHom φ (Fin.snoc x y) p = PolynomialData.evalHom (evalHom φ x) y p := by
  simp only [evalHom, Fin.snoc_castSucc, Fin.snoc_last]
  rfl

theorem evalHom_comp {T : Type} [CommRing T] (φ : K →+* S) (ψ : S →+* T)
    {n : ℕ} (x : Fin n → S) (p : Multi K n) :
    ψ (evalHom φ x p) = evalHom (ψ.comp φ) (ψ ∘ x) p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change ψ (DensePolynomial.eval₂ (evalHom φ (fun i : Fin n => x i.castSucc)) (x (Fin.last n)) p.coefficients)
      = DensePolynomial.eval₂ (evalHom (ψ.comp φ) (fun i : Fin n => ψ (x i.castSucc)))
        (ψ (x (Fin.last n))) p.coefficients
    induction p.coefficients with
    | nil => simp [DensePolynomial.eval₂]
    | cons a q h =>
      simp only [DensePolynomial.eval₂, map_add, map_mul, h, ih, Function.comp_def]

def constant : {n : ℕ} → K → Multi K n
  | 0, a => a
  | _+1, a => PolynomialData.constant (constant a)

def coordinate : {n : ℕ} → Fin n → Multi K n
  | 0, i => i.elim0
  | _n+1, i => Fin.lastCases PolynomialData.X (fun j => PolynomialData.constant (coordinate j)) i

/-- Recognize a polynomial independent of every coordinate. -/
def constantValue : {n : ℕ} → Multi K n → Option K
  | 0, a => some a
  | _+1, p =>
    match p.coefficients with
    | [] => some 0
    | [a] => constantValue a
    | _ => none

theorem constantValue_correct (φ : K →+* S) {n : ℕ} (x : Fin n → S)
    (p : Multi K n) {a : K} (h : constantValue p = some a) : evalHom φ x p = φ a := by
  induction n with
  | zero => exact congrArg φ (Option.some.inj h)
  | succ n ih =>
    change DensePolynomial.eval₂ (evalHom φ (fun i : Fin n => x i.castSucc)) (x (Fin.last n))
      p.coefficients = φ a
    cases h₁ : p.coefficients with
    | nil =>
      simp only [constantValue, h₁, Option.some.injEq] at h
      simp [DensePolynomial.eval₂, ← h]
    | cons b bs =>
      cases bs with
      | nil =>
        simp only [constantValue, h₁] at h
        simpa [DensePolynomial.eval₂] using ih (fun i => x i.castSucc) b h
      | cons c cs =>
        simp [constantValue, h₁] at h

def leadingScalar : {n : ℕ} → Multi K n → K
  | 0, a => a
  | _+1, p => p.coefficients.getLast?.elim 0 leadingScalar

def totalDegree : {n : ℕ} → Multi K n → ℕ
  | 0, _ => 0
  | _+1, p => (p.coefficients.zipIdx.map (fun (a, i) => totalDegree a + i)).foldl max 0

@[simp] theorem eval_constant (φ : K →+* S) {n : ℕ} (x : Fin n → S) (a : K) :
    evalHom φ x (constant a) = φ a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change PolynomialData.evalHom (evalHom φ (fun i : Fin n => x i.castSucc)) (x (Fin.last n))
      (PolynomialData.constant (constant a)) = _
    exact (PolynomialData.evalHom_constant _ _ _).trans (ih _)

@[simp] theorem eval_coordinate (φ : K →+* S) {n : ℕ} (x : Fin n → S) (i : Fin n) :
    evalHom φ x (coordinate i) = x i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    cases i using Fin.lastCases with
    | last =>
      change PolynomialData.evalHom _ _ (Fin.lastCases PolynomialData.X
        (fun j => PolynomialData.constant (coordinate j)) (Fin.last n)) = _
      rw [Fin.lastCases_last]
      exact PolynomialData.evalHom_X _ _
    | cast j =>
      change PolynomialData.evalHom _ _ (Fin.lastCases PolynomialData.X
        (fun k => PolynomialData.constant (coordinate k)) j.castSucc) = _
      rw [Fin.lastCases_castSucc]
      exact (PolynomialData.evalHom_constant _ _ _).trans (ih _ j)

@[fun_prop] theorem continuous_eval (φ : K →+* ℝ) {n : ℕ} (p : Multi K n) :
    Continuous fun x : Fin n → ℝ => evalHom φ x p := by
  induction n with
  | zero =>
    change Continuous (fun _ : Fin 0 → ℝ => φ p)
    exact continuous_const
  | succ n ih =>
    let base := fun x : Fin (n+1) → ℝ => evalHom φ (fun i : Fin n => x i.castSucc)
    let z := fun x : Fin (n+1) → ℝ => x (Fin.last n)
    change Continuous fun x => DensePolynomial.eval₂ (base x) (z x) p.coefficients
    have cz : Continuous z := continuous_apply _
    induction p.coefficients with
    | nil => exact continuous_const
    | cons a ps hp =>
      have ha : Continuous fun x => base x a :=
        (ih a).comp (continuous_pi fun _ => continuous_apply _)
      exact ha.add (cz.mul hp)

def constantHom : (n : ℕ) → K →+* Multi K n
  | 0 => RingHom.id K
  | n+1 => PolynomialData.constantHom.comp (constantHom n)

@[simp] theorem constantHom_apply (n : ℕ) (a : K) :
    constantHom (K := K) n a = constant a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change PolynomialData.constant (constantHom n a) = PolynomialData.constant (constant a)
    rw [ih]

def substitute {n m : ℕ} (p : Multi K n) (x : Fin n → Multi K m) : Multi K m :=
  evalHom (constantHom m) x p

theorem substitute_correct (φ : K →+* S) {n m : ℕ}
    (p : Multi K n) (x : Fin n → Multi K m) (y : Fin m → S) :
    evalHom φ y (substitute p x) = evalHom φ (fun i => evalHom φ y (x i)) p := by
  rw [substitute, evalHom_comp]
  have h : (evalHom φ y).comp (constantHom m) = φ := by
    ext a
    simp
  rw [h]
  rfl

theorem nontrivial [Nontrivial K] (n : ℕ) : Nontrivial (Multi K n) := by
  refine ⟨0, 1, ?_⟩
  intro e
  have h := congrArg (evalHom (RingHom.id K) (fun _ : Fin n => (0 : K))) e
  simp at h

end Multi
end CertifiedTopology
