module

public import CertifiedTopology.ProjectionData

@[expose] public section

namespace CertifiedTopology.ProjectionData

open Quartic QuarticDecision Polynomial

variable {R : Type} [CommRing R] [DecidableEq R]

/-- The callbacks avoid constructing vacuous branches of the projection program. -/
def guard {A : Type} (knownZero : R → Option Bool) (c : R)
    (z nz : Unit → Decision R A) : Decision R A :=
  match knownZero c with
  | some true => z ()
  | some false => nz ()
  | none => .test c (z ()) (nz ())

def pruneDegree (knownZero : R → Option Bool) :
    ℕ → PolynomialData R → Decision R (Option (PolynomialData R × ℕ))
  | 0, f => guard knownZero (f.coefficient 0) (fun _ => .leaf none)
      (fun _ => .leaf (some (f, 0)))
  | n+1, f => guard knownZero (f.coefficient (n+1))
      (fun _ => pruneDegree knownZero n (dropTerm f (n+1)))
      (fun _ => .leaf (some (f, n+1)))

def pruneGCD (knownZero : R → Option Bool) (f : PolynomialData R) (m : ℕ) :
    ℕ → PolynomialData R → Decision R (PolynomialData R)
  | 0, g => guard knownZero (g.coefficient 0) (fun _ => .leaf f) (fun _ => .leaf 1)
  | n+1, g => guard knownZero (g.coefficient (n+1))
      (fun _ => pruneGCD knownZero f m n (dropTerm g (n+1)))
      (fun _ => pruneGCD knownZero g (n+1) n (pseudoRemainder (n+1) g (m+1-(n+1)) f))
termination_by n _ => n

def pruneSquarefree (knownZero : R → Option Bool) (f : PolynomialData R) (n : ℕ) :
    Decision R (FiberData R) :=
  (pruneDegree knownZero n f).bind fun e =>
    match e with
    | none => .leaf .line
    | some (_, 0) => .leaf .empty
    | some (g, d+1) =>
      (pruneGCD knownZero g (d+1) d g.derivative).bind fun h =>
        (pruneDegree knownZero h.natDegree h).bind (squarefreeLeaf g d)

def pruneFiber (knownZero : R → Option Bool) (f g : PolynomialData R) :
    Decision R (FiberData R) :=
  (pruneGCD knownZero f f.natDegree g.natDegree g).bind fun h => pruneSquarefree knownZero h h.natDegree

/-- Compute just the product on the selected route. -/
def productAt {F : Type} [Field F] [DecidableEq F] (φ : R →+* F) (knownZero : R → Option Bool) :
    List (PolynomialData R) → PolynomialData R
  | [] => 1
  | p :: ps =>
    let rest := productAt φ knownZero ps
    match (pruneDegree knownZero p.natDegree p).run φ with
    | some (q, _+1) => q * rest
    | _ => rest

section Correct

variable {F : Type} [Field F] [DecidableEq F]
variable (φ : R →+* F) (knownZero : R → Option Bool)
variable (sound : ∀ c b, knownZero c = some b → (φ c = 0 ↔ b = true))
include sound

theorem run_guard {A : Type} (c : R) (z nz : Unit → Decision R A) :
    (guard knownZero c z nz).run φ = if φ c = 0 then (z ()).run φ else (nz ()).run φ := by
  unfold guard
  cases h : knownZero c with
  | none => rfl
  | some b =>
    cases b with
    | true => simp [(sound c true h).mpr rfl]
    | false => simp [show φ c ≠ 0 from fun eq => Bool.false_ne_true ((sound c false h).mp eq)]

theorem run_pruneDegree (n : ℕ) (f : PolynomialData R) :
    (pruneDegree knownZero n f).run φ = (degreeDecision n f).run φ := by
  induction n generalizing f with
  | zero => rw [pruneDegree, run_guard φ knownZero sound, degreeDecision, Decision.run] <;> rfl
  | succ n ih =>
    rw [pruneDegree, run_guard φ knownZero sound, degreeDecision, Decision.run, ih] <;> rfl

theorem run_pruneGCD (n m : ℕ) (f g : PolynomialData R) :
    (pruneGCD knownZero f m n g).run φ = (gcdDecision f m n g).run φ := by
  induction n generalizing m f g with
  | zero => rw [pruneGCD, run_guard φ knownZero sound, gcdDecision, Decision.run] <;> rfl
  | succ n ih =>
    rw [pruneGCD, run_guard φ knownZero sound, gcdDecision, Decision.run, ih, ih]

theorem run_pruneSquarefree (n : ℕ) (f : PolynomialData R) :
    (pruneSquarefree knownZero f n).run φ = (squarefreeDecision f n).run φ := by
  simp only [pruneSquarefree, squarefreeDecision, Decision.run_bind, run_pruneDegree φ knownZero sound]
  cases (degreeDecision n f).run φ with
  | none => rfl
  | some a =>
    obtain ⟨g,d⟩ := a
    cases d with
    | zero => rfl
    | succ d =>
      simp [squarefreeFromDegree, squarefreeNonconstant, run_pruneGCD φ knownZero sound,
        run_pruneDegree φ knownZero sound]

theorem run_pruneFiber (f g : PolynomialData R) :
    (pruneFiber knownZero f g).run φ = (fiberDecision f g).run φ := by
  simp [pruneFiber, fiberDecision, run_pruneGCD φ knownZero sound, run_pruneSquarefree φ knownZero sound]

theorem productAt_spec [Nontrivial R] (ps : List (PolynomialData R)) :
    let q := (productAt φ knownZero ps).polynomial.map φ
    q ≠ 0 ∧ ∀ z, q.IsRoot z ↔
      ∃ p ∈ ps, p.polynomial.map φ ≠ 0 ∧ (p.polynomial.map φ).IsRoot z := by
  induction ps with
  | nil => simp [productAt,IsRoot.def]
  | cons p ps ih =>
    have test := Quartic.degreeDecision_spec φ p.polynomial p.natDegree (PolynomialData.natDegree_correct p).ge
    rw [← degreeDecision_polynomial,run_map] at test
    simp only [productAt,run_pruneDegree φ knownZero sound]
    cases e : (degreeDecision p.natDegree p).run φ with
    | none =>
      have hp : p.polynomial.map φ = 0 := by simpa only [e,interpretDegree,Option.map_none] using test
      simpa [hp] using ih
    | some q =>
      obtain ⟨a,d⟩ := q
      simp only [e,interpretDegree,Option.map_some] at test
      obtain ⟨same,_,lead,deg⟩ := test
      have nz : a.polynomial.map φ ≠ 0 := by
        intro h
        exact lead (by simpa [coeff_map] using congrArg (fun f : Polynomial F => f.coeff d) h)
      have np : p.polynomial.map φ ≠ 0 := same ▸ nz
      cases d with
      | zero =>
        have hp : ∀ z, ¬(p.polynomial.map φ).IsRoot z := by
          intro z hz
          rw [← same, eq_C_of_natDegree_eq_zero deg] at hz
          have eq : (a.polynomial.map φ).coeff 0 = 0 := by simpa [IsRoot.def] using hz
          exact lead (by simpa [coeff_map] using eq)
        refine ⟨ih.1,?_⟩
        intro z
        exact (ih.2 z).trans ⟨fun ⟨q,hq,hz⟩ => ⟨q,List.mem_cons_of_mem _ hq,hz⟩,
          fun ⟨q,hq,hz,he⟩ => (List.mem_cons.mp hq).elim (fun eq => (hp z (eq ▸ he)).elim)
            (fun h => ⟨q,h,hz,he⟩)⟩
      | succ d =>
        simp only [PolynomialData.polynomial_times,Polynomial.map_mul]
        refine ⟨mul_ne_zero nz ih.1,?_⟩
        intro z
        have eq (a b : Polynomial F) : (a*b).IsRoot z ↔ a.IsRoot z ∨ b.IsRoot z := by
          simp only [IsRoot.def,eval_mul,mul_eq_zero]
        rw [eq,same,ih.2 z]
        simp [np]

end Correct
end CertifiedTopology.ProjectionData
