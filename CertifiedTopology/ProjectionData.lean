module

public import CertifiedTopology.PolynomialData
public import CertifiedTopology.QuarticProjection

@[expose] public section

namespace CertifiedTopology.ProjectionData

open Quartic Polynomial

namespace QuarticDecision

def mapResult {R A B : Type} (f : A → B) : Decision R A → Decision R B
  | .leaf a => .leaf (f a)
  | .test c z nz => .test c (mapResult f z) (mapResult f nz)

@[simp] theorem map_bind {R A B C : Type} (f : B → C) (d : Decision R A) (g : A → Decision R B) :
    mapResult f (d.bind g) = d.bind (fun a => mapResult f (g a)) := by
  induction d with
  | leaf => rfl
  | test c z nz hz hn => simp [mapResult, Decision.bind, hz, hn]

theorem bind_mapped {R A B C : Type} (d : Decision R A) (f : A → B) (g : B → Decision R C) :
    (mapResult f d).bind g = d.bind (g ∘ f) := by
  induction d with
  | leaf => rfl
  | test c z nz hz hn => simp [mapResult, Decision.bind, hz, hn]

theorem tests_mem_bind {R A B : Type} {d : Decision R A} {f : A → Decision R B}
    {c : R} (h : c ∈ d.tests) : c ∈ (d.bind f).tests := by
  induction d with
  | leaf => simp [Decision.tests] at h
  | test a z nz hz hn =>
    simpa only [Decision.bind, Decision.tests, List.mem_cons, List.mem_append] using
      (show c = a ∨ c ∈ (z.bind f).tests ∨ c ∈ (nz.bind f).tests from
        (by simpa only [Decision.tests, List.mem_cons, List.mem_append] using h :
          c = a ∨ c ∈ z.tests ∨ c ∈ nz.tests).imp_right (Or.imp hz hn))

@[simp] theorem run_map {R A B F : Type} [Zero F] [DecidableEq F]
    (ev : R → F) (f : A → B) (d : Decision R A) :
    (mapResult f d).run ev = f (d.run ev) := by
  induction d with
  | leaf => rfl
  | test c z nz hz hn =>
    simp only [mapResult, Decision.run]
    split <;> simp_all

theorem run_zero_congr {R A F G : Type} [Zero F] [DecidableEq F] [Zero G] [DecidableEq G]
    (ev : R → F) (ew : R → G) (d : Decision R A)
    (h : ∀ c ∈ d.tests, ev c = 0 ↔ ew c = 0) : d.run ev = d.run ew := by
  induction d with
  | leaf => rfl
  | test c z nz hz hn =>
    simp only [Decision.tests, List.mem_cons, List.mem_append] at h
    simp only [Decision.run]
    by_cases hc : ev c = 0
    · rw [ite_eq_left hc, ite_eq_left ((h c (Or.inl rfl)).mp hc)]
      exact hz (fun a ha => h a (Or.inr (Or.inl ha)))
    · rw [ite_eq_right hc, ite_eq_right (mt (h c (Or.inl rfl)).mpr hc)]
      exact hn (fun a ha => h a (Or.inr (Or.inr ha)))

end QuarticDecision

open QuarticDecision

variable {R : Type} [CommRing R] [DecidableEq R]

def term (n : ℕ) (a : R) : PolynomialData R :=
  PolynomialData.ofCoefficients (DensePolynomial.shift n [a])

@[simp] theorem term_polynomial (n : ℕ) (a : R) :
    (term n a).polynomial = C a * X^n := by
  rw [term, PolynomialData.polynomial_ofCoefficients, DensePolynomial.polynomial_shift]
  simp only [DensePolynomial.polynomial, mul_zero, add_zero]
  exact mul_comm _ _

def cancelTerm (m n : ℕ) (f : PolynomialData R) : PolynomialData R :=
  term (m-n) (f.coefficient m)

def cancelLead (m n : ℕ) (f g : PolynomialData R) : PolynomialData R :=
  PolynomialData.constant (g.coefficient n) * f - cancelTerm m n f * g

@[simp] theorem cancelTerm_polynomial (m n : ℕ) (f : PolynomialData R) :
    (cancelTerm m n f).polynomial = Quartic.cancelTerm m n f.polynomial := by
  simp [cancelTerm, Quartic.cancelTerm]

@[simp] theorem cancelLead_polynomial (m n : ℕ) (f g : PolynomialData R) :
    (cancelLead m n f g).polynomial = Quartic.cancelLead m n f.polynomial g.polynomial := by
  simp [cancelLead, Quartic.cancelLead]

def pseudoDiv (n : ℕ) (g : PolynomialData R) :
    ℕ → PolynomialData R → PolynomialData R × PolynomialData R
  | 0, f => (0, f)
  | k + 1, f =>
    let qr := pseudoDiv n g k (cancelLead (n+k) n f g)
    (PolynomialData.constant (g.coefficient n)^k * cancelTerm (n+k) n f + qr.1, qr.2)

def pseudoRemainder (n : ℕ) (g : PolynomialData R) :
    ℕ → PolynomialData R → PolynomialData R
  | 0, f => f
  | k+1, f => pseudoRemainder n g k (cancelLead (n+k) n f g)

private theorem pseudoDiv_polynomial (n k : ℕ) (f g : PolynomialData R) :
    (pseudoDiv n g k f).map PolynomialData.polynomial PolynomialData.polynomial =
      Quartic.pseudoDiv n g.polynomial k f.polynomial := by
  induction k generalizing f with
  | zero => simp [pseudoDiv, Quartic.pseudoDiv]
  | succ k ih =>
    have hh := ih (cancelLead (n+k) n f g)
    rw [cancelLead_polynomial] at hh
    have hm (p : PolynomialData R) : (p^k).polynomial = p.polynomial^k :=
      map_pow PolynomialData.embedding p k
    simp [pseudoDiv, Quartic.pseudoDiv, hm, ← hh]

private theorem pseudoRemainder_polynomial (n k : ℕ) (f g : PolynomialData R) :
    (pseudoRemainder n g k f).polynomial = Quartic.pseudoRemainder n g.polynomial k f.polynomial := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => simp [pseudoRemainder, Quartic.pseudoRemainder, ih]

def dropTerm (f : PolynomialData R) (n : ℕ) : PolynomialData R := f - term n (f.coefficient n)

@[simp] theorem dropTerm_polynomial (f : PolynomialData R) (n : ℕ) :
    (dropTerm f n).polynomial = Quartic.dropTerm f.polynomial n := by
  simp [dropTerm, Quartic.dropTerm, C_mul_X_pow_eq_monomial]

def gcdDecision (f : PolynomialData R) (m : ℕ) :
    ℕ → PolynomialData R → Decision R (PolynomialData R)
  | 0, g => .test (g.coefficient 0) (.leaf f) (.leaf 1)
  | n+1, g => .test (g.coefficient (n+1))
      (gcdDecision f m n (dropTerm g (n+1)))
      (gcdDecision g (n+1) n (pseudoRemainder (n+1) g (m + 1 - (n+1)) f))
termination_by n _ => n

theorem gcdDecision_polynomial (f g : PolynomialData R) (m n : ℕ) :
    mapResult PolynomialData.polynomial (gcdDecision f m n g) =
      Quartic.gcdDecision f.polynomial m n g.polynomial := by
  induction n generalizing f g m with
  | zero => simp [gcdDecision, Quartic.gcdDecision, mapResult]
  | succ n ih =>
    rw [gcdDecision, Quartic.gcdDecision, mapResult, ih, ih]
    simp only [PolynomialData.coefficient_correct, dropTerm_polynomial, pseudoRemainder_polynomial]

def degreeDecision : ℕ → PolynomialData R → Decision R (Option (PolynomialData R × ℕ))
  | 0, f => .test (f.coefficient 0) (.leaf none) (.leaf (some (f, 0)))
  | n+1, f => .test (f.coefficient (n+1)) (degreeDecision n (dropTerm f (n+1)))
      (.leaf (some (f, n+1)))

noncomputable def interpretDegree : Option (PolynomialData R × ℕ) → Option (Polynomial R × ℕ) :=
  Option.map (fun (p,n) => (p.polynomial,n))

theorem degreeDecision_polynomial (f : PolynomialData R) (n : ℕ) :
    mapResult interpretDegree (degreeDecision n f) = Quartic.degreeDecision n f.polynomial := by
  induction n generalizing f with
  | zero => simp [degreeDecision, Quartic.degreeDecision, mapResult, interpretDegree]
  | succ n ih =>
    rw [degreeDecision, Quartic.degreeDecision, mapResult, ih]
    simp [interpretDegree, mapResult]

inductive FiberData (R : Type) [CommRing R] [DecidableEq R]
  | line
  | empty
  | roots (poly : PolynomialData R) (degree : ℕ)

noncomputable def FiberData.interpret : FiberData R → Fiber R
  | .line => .line
  | .empty => .empty
  | .roots p d => .roots p.polynomial d

def squarefreeLeaf (g : PolynomialData R) (d : ℕ) :
    Option (PolynomialData R × ℕ) → Decision R (FiberData R)
  | none => .leaf .empty
  | some (_, 0) => .leaf (.roots g (d+1))
  | some (a, e+1) =>
    .leaf (.roots (pseudoDiv (e+1) a (d+2-(e+1)) g).1 (d+1-(e+1)))

def squarefreeNonconstant (g : PolynomialData R) (d : ℕ) (h : PolynomialData R) :
    Decision R (FiberData R) :=
  (degreeDecision h.natDegree h).bind (squarefreeLeaf g d)

def squarefreeFromDegree : Option (PolynomialData R × ℕ) → Decision R (FiberData R)
  | none => .leaf .line
  | some (_, 0) => .leaf .empty
  | some (g, d+1) =>
    (gcdDecision g (d+1) d g.derivative).bind (squarefreeNonconstant g d)

def squarefreeDecision (f : PolynomialData R) (n : ℕ) : Decision R (FiberData R) :=
  (degreeDecision n f).bind squarefreeFromDegree

set_option maxHeartbeats 500000 in
theorem squarefreeDecision_polynomial (f : PolynomialData R) (n : ℕ) :
    mapResult FiberData.interpret (squarefreeDecision f n) = Quartic.squarefreeDecision f.polynomial n := by
  unfold squarefreeDecision Quartic.squarefreeDecision
  rw [map_bind, ← degreeDecision_polynomial, bind_mapped]
  congr 1
  funext e
  rcases e with _ | ⟨g,d⟩
  · rfl
  cases d with
  | zero => rfl
  | succ d =>
    simp only [squarefreeFromDegree, interpretDegree, Option.map_some, Function.comp_apply]
    rw [map_bind, ← PolynomialData.derivative_correct, ← gcdDecision_polynomial, bind_mapped]
    congr 1
    funext h
    simp only [squarefreeNonconstant, Function.comp_apply, PolynomialData.natDegree_correct]
    rw [map_bind, ← degreeDecision_polynomial, bind_mapped]
    congr 1
    funext j
    rcases j with _ | ⟨a,e⟩
    · rfl
    cases e with
    | zero => rfl
    | succ e =>
      have eq := congrArg Prod.fst (pseudoDiv_polynomial (e+1) (d+2-(e+1)) g a)
      simpa [squarefreeLeaf, interpretDegree, mapResult, FiberData.interpret] using congrArg
        (fun q => (Decision.leaf (Fiber.roots q (d+1-(e+1))) : Decision R (Fiber R))) eq

def fiberDecision (f g : PolynomialData R) : Decision R (FiberData R) :=
  (gcdDecision f f.natDegree g.natDegree g).bind fun h => squarefreeDecision h h.natDegree

theorem fiberDecision_polynomial (f g : PolynomialData R) :
    mapResult FiberData.interpret (fiberDecision f g) = Quartic.fiberDecision f.polynomial g.polynomial := by
  simp only [fiberDecision, Quartic.fiberDecision, map_bind, PolynomialData.natDegree_correct]
  rw [← gcdDecision_polynomial, bind_mapped]
  congr 1
  funext h
  exact squarefreeDecision_polynomial _ _

section Union

variable {F : Type} [Field F] [DecidableEq F] [CharZero F] [Nontrivial R]

theorem squarefree_spec (φ : R →+* F) (p : PolynomialData R) :
    Fiber.Spec φ (p.polynomial.map φ)
      (((squarefreeDecision p p.natDegree).run φ).interpret) := by
  have h := Quartic.squarefreeDecision_spec φ p.polynomial p.natDegree
    (by exact (PolynomialData.natDegree_correct p).ge)
  rw [← squarefreeDecision_polynomial, run_map] at h
  exact h

theorem fiber_spec (φ : R →+* F) (p q : PolynomialData R) (z : F) :
    let ans := (fiberDecision p q).run φ
    match ans with
    | .line => ∀ t, (p.polynomial.map φ).IsRoot t ∧ (q.polynomial.map φ).IsRoot t
    | .empty => ¬((p.polynomial.map φ).IsRoot z ∧ (q.polynomial.map φ).IsRoot z)
    | .roots h n =>
      (h.polynomial.map φ).natDegree = n ∧ (h.polynomial.map φ) ≠ 0 ∧
        ((h.polynomial.map φ).IsRoot z ↔
          (p.polynomial.map φ).IsRoot z ∧ (q.polynomial.map φ).IsRoot z) ∧
        ((h.polynomial.map φ).IsRoot z → ¬(h.polynomial.map φ).derivative.IsRoot z) := by
  obtain ⟨g, hg⟩ := Quartic.fiberDecision_spec φ p.polynomial q.polynomial
  rw [← fiberDecision_polynomial, run_map] at hg
  dsimp only
  cases h : (fiberDecision p q).run φ with
  | line =>
    simp only [h, FiberData.interpret, Fiber.Spec] at hg
    intro t
    exact (g.isRoot t).mp (by simp [hg, IsRoot.def])
  | empty =>
    simp only [h, FiberData.interpret, Fiber.Spec] at hg
    exact mt (g.isRoot z).mpr (hg z)
  | roots a n =>
    simp only [h, FiberData.interpret, Fiber.Spec] at hg
    exact ⟨hg.1, hg.2.1, (hg.2.2.1 z).trans (g.isRoot z), hg.2.2.2 z⟩

end Union
end CertifiedTopology.ProjectionData
