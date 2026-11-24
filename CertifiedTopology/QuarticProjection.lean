module

public import CertifiedTopology.Plane
public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

namespace CertifiedTopology.Quartic

open Polynomial

abbrev TriPoly (K : Type) [Semiring K] := Polynomial (Plane.BiPoly K)

/-- Branches test whether a coefficient polynomial vanishes on the base. -/
inductive Decision (R A : Type) where
  | leaf (result : A)
  | test (coefficient : R) (zero nonzero : Decision R A)

namespace Decision

def run {R A F : Type} [Zero F] [DecidableEq F] (ev : R → F) : Decision R A → A
  | .leaf a => a
  | .test c z nz => if ev c = 0 then z.run ev else nz.run ev

def tests {R A : Type} : Decision R A → List R
  | .leaf _ => []
  | .test c z nz => c :: (z.tests ++ nz.tests)

def bind {R A B : Type} (d : Decision R A) (f : A → Decision R B) : Decision R B :=
  match d with
  | .leaf a => f a
  | .test c z nz => .test c (z.bind f) (nz.bind f)

@[simp] theorem run_bind {R A B F : Type} [Zero F] [DecidableEq F] (ev : R → F)
    (d : Decision R A) (f : A → Decision R B) :
    (d.bind f).run ev = (f (d.run ev)).run ev := by
  induction d with
  | leaf => rfl
  | test c z nz hz hn =>
    simp only [bind, run]
    split <;> simp_all

theorem run_congr {R A F : Type} [Zero F] [DecidableEq F] (d : Decision R A) (ev ew : R → F)
    (h : ∀ c ∈ d.tests, ev c = 0 ↔ ew c = 0) : d.run ev = d.run ew := by
  induction d with
  | leaf => rfl
  | test c z nz hz hn =>
    simp only [tests, List.mem_cons, List.mem_append] at h
    by_cases hc : ev c = 0
    · have hw := (h c (Or.inl rfl)).mp hc
      simpa only [run, ite_eq_left hc, ite_eq_left hw] using hz (fun a ha => h a (Or.inr (Or.inl ha)))
    · have hw := mt (h c (Or.inl rfl)).mpr hc
      simpa only [run, ite_eq_right hc, ite_eq_right hw] using hn (fun a ha => h a (Or.inr (Or.inr ha)))

end Decision

section Algebra

variable {R F : Type} [CommRing R] [Field F]

/-- One fraction-free cancellation step with degree bounds m and n. -/
noncomputable def cancelTerm (m n : ℕ) (f : Polynomial R) : Polynomial R :=
  C (f.coeff m) * X ^ (m - n)

noncomputable def cancelLead (m n : ℕ) (f g : Polynomial R) : Polynomial R :=
  C (g.coeff n) * f - cancelTerm m n f * g

private theorem cancelLead_degree [Nontrivial R] {m n : ℕ} {f g : Polynomial R}
    (hm : 0 < m) (hn : n ≤ m) (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    (cancelLead m n f g).natDegree < m := by
  have hbound : (cancelLead m n f g).natDegree ≤ m := by
    have hleft : (C (g.coeff n) * f).natDegree ≤ m :=
      natDegree_mul_le.trans (by simpa using hf)
    have hright : (cancelTerm m n f * g).natDegree ≤ m := by
      rw [cancelTerm, mul_assoc]
      calc
        _ ≤ (C (f.coeff m)).natDegree + (X ^ (m - n) * g).natDegree := natDegree_mul_le
        _ ≤ m := by
          have h := natDegree_mul_le (p := (X : Polynomial R) ^ (m - n)) (q := g)
          rw [natDegree_C, natDegree_X_pow] at *
          omega
    exact (natDegree_sub_le _ _).trans (max_le hleft hright)
  have hc : (cancelLead m n f g).coeff m = 0 := by
    have he : (X ^ (m - n) * g).coeff m = g.coeff n := by
      conv_lhs => enter [2]; rw [show m = n + (m - n) by omega]
      exact coeff_X_pow_mul g _ _
    simp only [cancelLead, cancelTerm, coeff_sub, mul_assoc, coeff_C_mul, he]
    ring
  by_contra! h
  have he := le_antisymm hbound h
  have hnz : cancelLead m n f g ≠ 0 := by
    intro hz
    rw [hz, natDegree_zero] at he
    omega
  exact (leadingCoeff_ne_zero.mpr hnz) (by rw [← coeff_natDegree, he, hc])

/-- Pseudo-division with a fixed number of cancellations. Specialization
    commutes with every step because it uses only ring operations. -/
noncomputable def pseudoDiv (n : ℕ) (g : Polynomial R) :
    ℕ → Polynomial R → Polynomial R × Polynomial R
  | 0, f => (0, f)
  | k + 1, f =>
    let m := n + k
    let qr := pseudoDiv n g k (cancelLead m n f g)
    (C (g.coeff n)^k * cancelTerm m n f + qr.1, qr.2)

/-- The gcd steps need only the remainder, so they skip quotient arithmetic. -/
noncomputable def pseudoRemainder (n : ℕ) (g : Polynomial R) :
    ℕ → Polynomial R → Polynomial R
  | 0, f => f
  | k + 1, f => pseudoRemainder n g k (cancelLead (n + k) n f g)

private theorem pseudoRemainder_eq (n k : ℕ) (f g : Polynomial R) :
    pseudoRemainder n g k f = (pseudoDiv n g k f).2 := by
  induction k generalizing f with
  | zero => rfl
  | succ k ih => exact ih _

theorem pseudoDiv_spec [Nontrivial R] (n k : ℕ) (f g : Polynomial R)
    (hn : 0 < n) (hf : f.natDegree < n + k) (hg : g.natDegree ≤ n) :
    let qr := pseudoDiv n g k f
    C (g.coeff n)^k * f = qr.1 * g + qr.2 ∧ qr.2.natDegree < n := by
  induction k generalizing f with
  | zero => simpa [pseudoDiv] using hf
  | succ k ih =>
    have hd := cancelLead_degree (f := f) (g := g) (m := n + k) (n := n)
      (by omega) (by omega) (by omega) hg
    obtain ⟨he, hr⟩ := ih _ hd
    simp only [pseudoDiv]
    refine ⟨?_, hr⟩
    simp only [cancelLead] at he ⊢
    rw [pow_succ]
    linear_combination he

private theorem pseudoDiv_map_spec [Nontrivial R] (φ : R →+* F)
    (n k : ℕ) (f g : Polynomial R) (hn : 0 < n)
    (hf : f.natDegree < n + k) (hg : g.natDegree ≤ n) :
    let qr := pseudoDiv n g k f
    C (φ (g.coeff n))^k * f.map φ = qr.1.map φ * g.map φ + qr.2.map φ ∧
      (qr.2.map φ).natDegree < n := by
  obtain ⟨he, hr⟩ := pseudoDiv_spec n k f g hn hf hg
  refine ⟨?_, natDegree_map_le.trans_lt hr⟩
  simpa only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_C]
    using congrArg (Polynomial.map φ) he

noncomputable def dropTerm (f : Polynomial R) (n : ℕ) : Polynomial R :=
  f - monomial n (f.coeff n)

private theorem dropTerm_degree [Nontrivial R] {f : Polynomial R} {n : ℕ}
    (hn : 0 < n) (hf : f.natDegree ≤ n) : (dropTerm f n).natDegree ≤ n - 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  simp only [dropTerm, coeff_sub, coeff_monomial, Finsupp.single_apply]
  by_cases he : n = i
  · subst i
    simp
  · rw [ite_eq_right he, sub_zero, coeff_eq_zero_of_natDegree_lt (by omega)]

private theorem map_dropTerm (φ : R →+* F) (f : Polynomial R) {n : ℕ} (h : φ (f.coeff n) = 0) :
    (dropTerm f n).map φ = f.map φ := by
  simp [dropTerm, Polynomial.map_sub, map_monomial, h]

/-- A generalized gcd specification allows any nonzero scalar multiple. -/
def CommonDivisors (f g d : Polynomial F) : Prop :=
  ∀ a, a ∣ d ↔ a ∣ f ∧ a ∣ g

/-- Test the highest coefficient before deciding whether to discard the term
    or take a pseudo-remainder. -/
noncomputable def gcdDecision (f : Polynomial R) (m : ℕ) :
    ℕ → Polynomial R → Decision R (Polynomial R)
  | 0, g => .test (g.coeff 0) (.leaf f) (.leaf 1)
  | n + 1, g => .test (g.coeff (n + 1))
      (gcdDecision f m n (dropTerm g (n + 1)))
      (gcdDecision g (n + 1) n (pseudoRemainder (n + 1) g (m + 1 - (n + 1)) f))
termination_by n _ => n

theorem gcdDecision_spec [Nontrivial R] [DecidableEq F] (φ : R →+* F) (f g : Polynomial R) (m n : ℕ)
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) :
    CommonDivisors (f.map φ) (g.map φ) (((gcdDecision f m n g).run φ).map φ) := by
  induction n generalizing f g m with
  | zero =>
    have e := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hg)
    rw [gcdDecision, Decision.run]
    by_cases h : φ (g.coeff 0) = 0
    · have hz : g.map φ = 0 := by
        conv_lhs => rw [e]
        simp [h]
      simp [h, hz, CommonDivisors, Decision.run]
    · have hu : IsUnit (g.map φ) := by
        have E : g.map φ = C (φ (g.coeff 0)) :=
          (congrArg (Polynomial.map φ) e).trans (Polynomial.map_C φ)
        exact E.symm ▸ isUnit_C.mpr (isUnit_iff_ne_zero.mpr h)
      simp only [ite_eq_right h, Decision.run, Polynomial.map_one, CommonDivisors]
      intro a
      exact ⟨fun ha => ⟨ha.trans (one_dvd _), ha.trans (one_dvd _)⟩,
        fun ha => ha.2.trans (hu.dvd)⟩
  | succ n ih =>
    rw [gcdDecision, Decision.run]
    by_cases h : φ (g.coeff (n+1)) = 0
    · rw [ite_eq_left h]
      simpa only [map_dropTerm φ g h] using
        ih f (dropTerm g (n+1)) m hf (dropTerm_degree (by omega) hg)
    · rw [ite_eq_right h, pseudoRemainder_eq]
      let k := m + 1 - (n + 1)
      have hb : f.natDegree < n+1+k := by omega
      obtain ⟨_, hr⟩ := pseudoDiv_spec (n+1) k f g (by omega) hb hg
      have H := ih g (pseudoDiv (n+1) g k f).2 (n+1) hg (by omega)
      intro a
      rw [H]
      obtain ⟨he, _⟩ := pseudoDiv_map_spec φ (n+1) k f g (by omega) hb hg
      have hu : IsUnit (C (φ (g.coeff (n+1))) ^ k) :=
        (isUnit_C.mpr (isUnit_iff_ne_zero.mpr h)).pow k
      constructor
      · rintro ⟨ha, hr⟩
        exact ⟨hu.dvd_mul_left.mp (he.symm ▸ dvd_add (dvd_mul_of_dvd_right ha _) hr), ha⟩
      · rintro ⟨ha, hb⟩
        refine ⟨hb, ?_⟩
        have eqr : (pseudoDiv (n+1) g k f).2.map φ =
            C (φ (g.coeff (n+1))) ^ k * f.map φ -
              (pseudoDiv (n+1) g k f).1.map φ * g.map φ := by
          change C (φ (g.coeff (n+1))) ^ k * f.map φ = _ at he
          linear_combination -he
        rw [eqr]
        exact dvd_sub (hu.dvd_mul_left.mpr ha) (dvd_mul_of_dvd_right hb _)


noncomputable def degreeDecision : ℕ → Polynomial R → Decision R (Option (Polynomial R × ℕ))
  | 0, f => .test (f.coeff 0) (.leaf none) (.leaf (some (f, 0)))
  | n + 1, f => .test (f.coeff (n + 1)) (degreeDecision n (dropTerm f (n + 1)))
      (.leaf (some (f, n + 1)))

theorem degreeDecision_spec [Nontrivial R] [DecidableEq F] (φ : R →+* F) (f : Polynomial R)
    (n : ℕ) (hf : f.natDegree ≤ n) :
    match (degreeDecision n f).run φ with
    | none => f.map φ = 0
    | some (g, d) => g.map φ = f.map φ ∧ g.natDegree ≤ d ∧
        φ (g.coeff d) ≠ 0 ∧ (g.map φ).natDegree = d := by
  have degreeOf (g : Polynomial R) (d : ℕ) (hg : g.natDegree ≤ d)
      (h : φ (g.coeff d) ≠ 0) : (g.map φ).natDegree = d :=
    le_antisymm (natDegree_map_le.trans hg)
      (le_natDegree_of_ne_zero (by simpa only [coeff_map] using h))
  induction n generalizing f with
  | zero =>
    rw [degreeDecision, Decision.run]
    by_cases h : φ (f.coeff 0) = 0
    · simp only [ite_eq_left h, Decision.run]
      have e := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hf)
      exact (congrArg (Polynomial.map φ) e).trans (by simp [h])
    · rw [ite_eq_right h]
      exact ⟨rfl, hf, h, degreeOf f 0 hf h⟩
  | succ n ih =>
    rw [degreeDecision, Decision.run]
    by_cases h : φ (f.coeff (n+1)) = 0
    · rw [ite_eq_left h]
      simpa only [map_dropTerm φ f h] using
        ih (dropTerm f (n+1)) (dropTerm_degree (by omega) hf)
    · rw [ite_eq_right h]
      exact ⟨rfl, hf, h, degreeOf f (n+1) hf h⟩

namespace CommonDivisors

theorem left {f g d : Polynomial F} (h : CommonDivisors f g d) : d ∣ f :=
  ((h d).mp dvd_rfl).1

theorem right {f g d : Polynomial F} (h : CommonDivisors f g d) : d ∣ g :=
  ((h d).mp dvd_rfl).2

theorem isRoot {f g d : Polynomial F} (h : CommonDivisors f g d) (t : F) :
    d.IsRoot t ↔ f.IsRoot t ∧ g.IsRoot t := by
  rw [← dvd_iff_isRoot, ← dvd_iff_isRoot, ← dvd_iff_isRoot]
  exact h (X - C t)

theorem eq_zero_iff {f g d : Polynomial F} (h : CommonDivisors f g d) :
    d = 0 ↔ f = 0 ∧ g = 0 := by
  simpa only [zero_dvd_iff] using h 0

end CommonDivisors

/-- A leaf describes either an exceptional full line, an empty fiber, or
    the simple roots of a polynomial of fixed degree. -/
inductive Fiber (R : Type) [Semiring R] where
  | line
  | empty
  | roots (poly : Polynomial R) (degree : ℕ)

def Fiber.Spec (φ : R →+* F) (f : Polynomial F) : Fiber R → Prop
  | .line => f = 0
  | .empty => ∀ t, ¬f.IsRoot t
  | .roots q d => (q.map φ).natDegree = d ∧ (q.map φ) ≠ 0 ∧
      (∀ t, (q.map φ).IsRoot t ↔ f.IsRoot t) ∧
      ∀ t, (q.map φ).IsRoot t → ¬(q.map φ).derivative.IsRoot t

private theorem simple_of_constant_derivativeGCD {f g : Polynomial F}
    (h : CommonDivisors f f.derivative g) (hg : g.natDegree = 0) (hn : g ≠ 0)
    (t : F) (ht : f.IsRoot t) : ¬f.derivative.IsRoot t := by
  intro hd
  have hz := (h.isRoot t).mpr ⟨ht, hd⟩
  have e := eq_C_of_natDegree_eq_zero hg
  have ev : (C (g.coeff 0)).eval t = 0 := (congrArg (eval t) e).symm.trans hz
  rw [eval_C] at ev
  exact hn (e.trans (C_eq_zero.mpr ev))

theorem quotient_roots [CharZero F] {f g q : Polynomial F} {a : F}
    (ha : a ≠ 0) (hf : f ≠ 0) (hd : f.derivative ≠ 0)
    (hg : CommonDivisors f f.derivative g) (he : C a * f = q * g) :
    q ≠ 0 ∧ (∀ t, q.IsRoot t ↔ f.IsRoot t) ∧
      ∀ t, q.IsRoot t → ¬q.derivative.IsRoot t := by
  have hp : q * g ≠ 0 := he ▸ mul_ne_zero (C_ne_zero.mpr ha) hf
  have hq : q ≠ 0 := left_ne_zero_of_mul hp
  have hn : g ≠ 0 := right_ne_zero_of_mul hp
  have forward (t : F) (ht : q.IsRoot t) : f.IsRoot t := by
    have eq := congrArg (eval t) he
    simp only [eval_mul, eval_C, IsRoot.def] at eq ht ⊢
    exact (mul_eq_zero.mp (eq.trans (by simp [ht]))).resolve_left ha
  have hm (t : F) (ht : f.IsRoot t) : q.rootMultiplicity t = 1 := by
    have hfd := derivative_rootMultiplicity_of_root ht
    have hle : g.rootMultiplicity t ≤ f.derivative.rootMultiplicity t :=
      le_rootMultiplicity_iff hd |>.mpr
        ((((le_rootMultiplicity_iff hn).mp le_rfl)).trans hg.right)
    have hge : f.derivative.rootMultiplicity t ≤ g.rootMultiplicity t := by
      apply (le_rootMultiplicity_iff hn).mpr
      apply (hg _).mpr
      exact ⟨(le_rootMultiplicity_iff hf).mp (by omega), (le_rootMultiplicity_iff hd).mp le_rfl⟩
    have eq := congrArg (rootMultiplicity t) he
    rw [rootMultiplicity_C_mul ha, rootMultiplicity_mul hp] at eq
    have hpos := (rootMultiplicity_pos hf).mpr ht
    omega
  refine ⟨hq, fun t => ⟨forward t, fun ht => (rootMultiplicity_pos hq).mp (by rw [hm t ht]; decide)⟩, ?_⟩
  intro t ht hd
  have hgt := (one_lt_rootMultiplicity_iff_isRoot hq).mpr ⟨ht, hd⟩
  rw [hm t (forward t ht)] at hgt
  omega

/-- Remove repeated roots only after computing the common divisor of the
    original equations. This keeps the lifting polynomial small. -/
noncomputable def squarefreeDecision (f : Polynomial R) (n : ℕ) : Decision R (Fiber R) :=
  (degreeDecision n f).bind fun
    | none => .leaf .line
    | some (_, 0) => .leaf .empty
    | some (g, d+1) =>
      (gcdDecision g (d+1) d g.derivative).bind fun h =>
        (degreeDecision h.natDegree h).bind fun
          | none => .leaf .empty
          | some (_, 0) => .leaf (.roots g (d+1))
          | some (a, e+1) =>
            .leaf (.roots (pseudoDiv (e+1) a (d+2-(e+1)) g).1 (d+1-(e+1)))

theorem squarefreeDecision_spec [Nontrivial R] [DecidableEq F] [CharZero F] (φ : R →+* F)
    (f : Polynomial R) (n : ℕ) (hf : f.natDegree ≤ n) :
    Fiber.Spec φ (f.map φ) ((squarefreeDecision f n).run φ) := by
  have h := degreeDecision_spec φ f n hf
  simp only [squarefreeDecision, Decision.run_bind]
  cases he : (degreeDecision n f).run φ with
  | none => simpa only [he, Decision.run, Fiber.Spec] using h
  | some v =>
    obtain ⟨g, d⟩ := v
    simp only [he] at h
    obtain ⟨eq, hg, hlead, hdeg⟩ := h
    have hgn : g.map φ ≠ 0 := by
      intro hz
      exact hlead (by simpa only [coeff_map, hz, coeff_zero] using
        (coeff_map φ d (p := g)).symm)
    cases d with
    | zero =>
      simp only [Decision.run, Fiber.Spec]
      intro t ht
      rw [← eq, eq_C_of_natDegree_eq_zero hdeg, IsRoot.def, eval_C] at ht
      exact hlead (by simpa only [coeff_map] using ht)
    | succ d =>
      simp only [Decision.run_bind]
      let h := (gcdDecision g (d+1) d g.derivative).run φ
      have hh : CommonDivisors (g.map φ) (g.map φ).derivative (h.map φ) := by
        simpa only [h, derivative_map] using gcdDecision_spec φ g g.derivative (d+1) d
          hg ((natDegree_derivative_le g).trans (by omega))
      have hh0 : h.map φ ≠ 0 := fun hz => hgn (hh.eq_zero_iff.mp hz).1
      have hc := degreeDecision_spec φ h h.natDegree le_rfl
      change Fiber.Spec φ (f.map φ)
        ((match (degreeDecision h.natDegree h).run φ with
          | none => Decision.leaf Fiber.empty
          | some (_, 0) => Decision.leaf (Fiber.roots g (d+1))
          | some (a, e+1) =>
            Decision.leaf (Fiber.roots (pseudoDiv (e+1) a (d+2-(e+1)) g).1 (d+1-(e+1)))).run φ)
      rw [← eq]
      cases hd : (degreeDecision h.natDegree h).run φ with
      | none =>
        simp only [hd] at hc
        exact (hh0 hc).elim
      | some v =>
        obtain ⟨a,e⟩ := v
        simp only [hd] at hc
        obtain ⟨ae, ha, hal, had⟩ := hc
        cases e with
        | zero =>
          change Fiber.Spec φ (g.map φ) (Fiber.roots g (d+1))
          exact ⟨hdeg, hgn, fun _ => Iff.rfl,
            simple_of_constant_derivativeGCD hh (ae ▸ had) hh0⟩
        | succ e =>
          simp only [Decision.run, Fiber.Spec]
          let k := d+2-(e+1)
          let qr := pseudoDiv (e+1) a k g
          obtain ⟨hqr, hr⟩ := pseudoDiv_map_spec φ (e+1) k g a (by omega) (by omega) ha
          have hdvd : a.map φ ∣ qr.2.map φ := by
            have hdiv : a.map φ ∣ g.map φ := ae.symm ▸ hh.left
            have eqr : qr.2.map φ = C (φ (a.coeff (e+1)))^k * g.map φ - qr.1.map φ * a.map φ := by
              change C (φ (a.coeff (e+1)))^k * g.map φ = _ at hqr
              linear_combination -hqr
            rw [eqr]
            exact dvd_sub (dvd_mul_of_dvd_right hdiv _) (dvd_mul_left _ _)
          have hzero : qr.2.map φ = 0 := eq_zero_of_dvd_of_natDegree_lt hdvd (had.symm ▸ hr)
          have eqr : C ((φ (a.coeff (e+1)))^k) * g.map φ = qr.1.map φ * h.map φ := by
            rw [Polynomial.C_pow, ← ae, ← add_zero (qr.1.map φ * a.map φ), ← hzero]
            exact hqr
          have hn := pow_ne_zero k hal
          obtain ⟨hq, hroot, hsimple⟩ :=
            quotient_roots hn hgn (derivative_ne_zero.mpr (by omega)) hh eqr
          refine ⟨?_, hq, hroot, hsimple⟩
          have hdegrees := congrArg natDegree eqr
          rw [natDegree_mul (C_ne_zero.mpr hn) hgn, natDegree_C, zero_add,
            natDegree_mul hq hh0, hdeg, ← ae, had] at hdegrees
          change (qr.1.map φ).natDegree = d+1-(e+1)
          omega

/-- All common zeros, including nullified equations, are classified by
    specializing the decisions made over the coefficient ring. -/
noncomputable def fiberDecision (f g : Polynomial R) : Decision R (Fiber R) :=
  (gcdDecision f f.natDegree g.natDegree g).bind fun d => squarefreeDecision d d.natDegree

theorem fiberDecision_spec [Nontrivial R] [DecidableEq F] [CharZero F] (φ : R →+* F)
    (f g : Polynomial R) :
    let d := ((gcdDecision f f.natDegree g.natDegree g).run φ).map φ
    CommonDivisors (f.map φ) (g.map φ) d ∧ Fiber.Spec φ d ((fiberDecision f g).run φ) := by
  refine ⟨gcdDecision_spec φ f g _ _ le_rfl le_rfl, ?_⟩
  simpa only [fiberDecision, Decision.run_bind] using squarefreeDecision_spec φ
    ((gcdDecision f f.natDegree g.natDegree g).run φ) _ le_rfl

end Algebra
end CertifiedTopology.Quartic
