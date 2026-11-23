module

public import CertifiedTopology.Plane
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Radical.Basic

@[expose] public section

namespace CertifiedTopology.Plane

open Polynomial UniqueFactorizationMonoid

/-- Removing repeated factors before projection keeps a single cut for each
    shared section. In particular, copies of the same equation do not make
    the discriminant vanish identically. -/
noncomputable def rootPolynomial {K : Type} [Field K] [DecidableEq K] (ps : List (BiPoly K)) : BiPoly K :=
  radical ((ps.filter (· ≠ 0)).dedup.prod)

private theorem squarefree_fraction {R K : Type} [CommRing R] [IsDomain R]
    [NormalizedGCDMonoid R] [Field K] [Algebra R K] [IsFractionRing R K]
    {f : Polynomial R} (hf : Squarefree f) :
    Squarefree (f.map (algebraMap R K)) := by
  let φ := algebraMap R K
  have hi : Function.Injective φ := IsFractionRing.injective R K
  intro d hd
  have h0 : d ≠ 0 := by
    intro h
    rw [h, zero_mul, zero_dvd_iff] at hd
    exact hf.ne_zero ((map_injective φ hi) (by simpa using hd))
  let n : Polynomial R := IsLocalization.integerNormalization (nonZeroDivisors R) d
  let g := n.primPart
  have hg : g.IsPrimitive := isPrimitive_primPart n
  obtain ⟨c, hc, he⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) d
  change n.map φ = c • d at he
  have hfc : φ c ≠ 0 := fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hc)
    (hi (h.trans (φ.map_zero.symm)))
  have eq : C (φ c) * d = C (φ n.content) * g.map φ := by
    calc
      C (φ c) * d = c • d := by
        rw [C_mul']
        exact algebraMap_smul K c d
      _ = n.map φ := he.symm
      _ = C (φ n.content) * g.map φ := by
        rw [← Polynomial.map_C, ← Polynomial.map_mul, ← n.eq_C_content_mul_primPart]
  have hgd : g.map φ ∣ d := by
    refine ⟨C ((φ c)⁻¹ * φ n.content), ?_⟩
    apply mul_left_cancel₀ (show C (φ c) ≠ 0 by simp [hfc])
    rw [eq, mul_comm (g.map φ), ← mul_assoc, ← C_mul, ← mul_assoc,
      mul_inv_cancel₀ hfc, one_mul]
  have hm : (g*g).map φ ∣ f.map φ := by
    rw [Polynomial.map_mul]
    exact (mul_dvd_mul hgd hgd).trans hd
  have hu := hf g ((hg.mul hg).dvd_of_fraction_map_dvd_fraction_map hm)
  exact isUnit_or_eq_zero_of_isUnit_integerNormalization_primPart h0 hu

noncomputable def critical (q : BiPoly ℝ) : List (Polynomial ℝ) :=
  [q.leadingCoeff, q.resultant q.derivative]

theorem rootPolynomial_ne_zero {K : Type} [Field K] [DecidableEq K] (ps : List (BiPoly K)) : rootPolynomial ps ≠ 0 :=
  radical_ne_zero

private theorem squarefree_resultant {R K : Type} [CommRing R] [IsDomain R]
    [NormalizedGCDMonoid R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    {q : Polynomial R} (hs : Squarefree q) : q.resultant q.derivative ≠ 0 := by
  let φ := algebraMap R K
  have hi : Function.Injective φ := IsFractionRing.injective R K
  have hc : IsCoprime (q.map φ) (q.derivative.map φ) := by
    rw [← derivative_map]
    exact PerfectField.separable_iff_squarefree.mpr (squarefree_fraction hs)
  intro hz
  have hr : (q.map φ).resultant (q.derivative.map φ) = 0 := by
    rw [natDegree_map_eq_of_injective hi q, natDegree_map_eq_of_injective hi q.derivative,
      resultant_map_map, hz, map_zero]
  exact (resultant_eq_zero_iff.mp hr).2 hc

theorem rootPolynomial_resultant_ne_zero {K : Type} [Field K] [DecidableEq K] [CharZero K] (ps : List (BiPoly K)) :
    let q := rootPolynomial ps
    q.resultant q.derivative ≠ 0 :=
  squarefree_resultant (K := FractionRing (Polynomial K)) squarefree_radical

theorem specialize_degree {q : BiPoly ℝ} {x : ℝ} (h : q.leadingCoeff.eval x ≠ 0) :
    (specialize x q).natDegree = q.natDegree := by
  exact natDegree_map_of_leadingCoeff_ne_zero _ h

theorem specialize_simple {q : BiPoly ℝ} {x : ℝ}
    (hl : q.leadingCoeff.eval x ≠ 0) (hr : (q.resultant q.derivative).eval x ≠ 0)
    {y : ℝ} (hy : value q (x,y) = 0) :
    value q.derivative (x,y) ≠ 0 := by
  have hd := specialize_degree hl
  have ed : (specialize x q.derivative) = (specialize x q).derivative := by
    exact (derivative_map _ _).symm
  have hnon : specialize x q ≠ 0 := by
    intro h
    have hz : (specialize x q).leadingCoeff = 0 := by simp [h]
    exact hl ((leadingCoeff_map_of_leadingCoeff_ne_zero (evalRingHom x) hl).symm.trans hz)
  have er : (specialize x q).resultant (specialize x q.derivative) =
      (q.resultant q.derivative).eval x := by
    have hdd : (specialize x q.derivative).natDegree = q.derivative.natDegree := by
      rw [ed, natDegree_derivative, hd, natDegree_derivative]
    change ((q.map (evalRingHom x)).resultant (q.derivative.map (evalRingHom x))) = _
    rw [show (q.map (evalRingHom x)).natDegree = q.natDegree from hd,
      show (q.derivative.map (evalRingHom x)).natDegree = q.derivative.natDegree from hdd,
      resultant_map_map]
    rfl
  have coprime : IsCoprime (specialize x q) (specialize x q.derivative) := by
    by_contra h
    exact hr (er.symm.trans (resultant_eq_zero_iff.mpr ⟨Or.inl hnon,h⟩))
  obtain ⟨a,b,hab⟩ := coprime
  intro h
  have ev := congrArg (Polynomial.eval y) hab
  have hy' : (specialize x q).eval y = 0 := hy
  have h' : (specialize x q.derivative).eval y = 0 := h
  simp [hy', h'] at ev

/-- A divisor with the same radical defines the same zero set after every
    specialization, including when the entire fiber specializes to zero. -/
theorem factor_value_zero {d f : BiPoly ℝ} (hd : d ∣ f) {n : ℕ} (hf : f ∣ d^n)
    (p : ℝ × ℝ) : value d p = 0 ↔ value f p = 0 := by
  let E := (evalRingHom p.2).comp (specialize p.1)
  change E d = 0 ↔ E f = 0
  constructor
  · intro hz
    have h := map_dvd E hd
    rw [hz, zero_dvd_iff] at h
    exact h
  · intro hz
    have h := map_dvd E hf
    rw [hz, map_pow, zero_dvd_iff] at h
    exact not_imp_not.mp (fun h0 => pow_ne_zero n h0) h

theorem radical_dvd_rootPolynomial {K : Type} [Field K] [DecidableEq K] {ps : List (BiPoly K)} {f : BiPoly K}
    (hmem : f ∈ ps) (hf : f ≠ 0) : radical f ∣ rootPolynomial ps := by
  apply radical_dvd_radical
  · exact List.dvd_prod (by simp [hmem, hf])
  · apply List.prod_ne_zero
    simp

/-- Polynomial identities certifying one squarefree root source and a
    finite set of base cuts. The witnesses for each input preserve its zeros
    after specialization, even when some inputs have repeated factors. -/
structure Projection (ps : List (BiPoly ℝ)) where
  root : BiPoly ℝ
  cuts : List (Polynomial ℝ)
  nonzero : ∀ f ∈ cuts, f ≠ 0
  regular : ∀ (x : ℝ), (∀ f ∈ cuts, f.eval x ≠ 0) →
    root.leadingCoeff.eval x ≠ 0 ∧
      ∀ y, value root (x,y) = 0 → value root.derivative (x,y) ≠ 0
  factors : ∀ f ∈ ps, f ≠ 0 → ∃ d, d ∣ root ∧ d ∣ f ∧ ∃ n : ℕ, f ∣ d^n

/-- Use a nonzero derivative resultant as a certificate of regular lifting. -/
noncomputable def Projection.ofResultant (ps : List (BiPoly ℝ)) (q : BiPoly ℝ)
    (hq : q ≠ 0) (hr : q.resultant q.derivative ≠ 0)
    (hfactors : ∀ f ∈ ps, f ≠ 0 → ∃ d, d ∣ q ∧ d ∣ f ∧ ∃ n : ℕ, f ∣ d^n) :
    Projection ps where
  root := q
  cuts := critical q
  nonzero f hf := by
    rcases List.mem_cons.mp hf with h | h
    · subst f
      exact leadingCoeff_ne_zero.mpr hq
    · rw [List.mem_singleton] at h
      exact h ▸ hr
  regular x h := by
    have hl : q.leadingCoeff.eval x ≠ 0 := h _ (by simp [critical])
    have hd : (q.resultant q.derivative).eval x ≠ 0 := h _ (by simp [critical])
    exact ⟨hl,fun _ hy => specialize_simple hl hd hy⟩
  factors := hfactors

/-- The built-in squarefree projection supplies a certificate for every input. -/
noncomputable def Projection.fromInputs (ps : List (BiPoly ℝ)) : Projection ps :=
  Projection.ofResultant ps (rootPolynomial ps) (rootPolynomial_ne_zero ps)
    (rootPolynomial_resultant_ne_zero ps) fun f hf hn =>
      ⟨radical f, radical_dvd_rootPolynomial hf hn, radical_dvd_self, exists_dvd_radical_self_pow hn⟩

/-- Interpret both coefficient layers using the given field embedding. -/
noncomputable def embedCoefficients {K : Type} [Field K] (ι : K →+* ℝ) :
    BiPoly K →+* BiPoly ℝ := mapRingHom (mapRingHom ι)

/-- Factorization and resultant computation can take place entirely in the
    input coefficient field before the result is interpreted over the reals. -/
noncomputable def Projection.fromEmbedded {K : Type} [Field K] [DecidableEq K] [CharZero K]
    (ι : K →+* ℝ) (ps : List (BiPoly K)) : Projection (ps.map (embedCoefficients ι)) := by
  let q := rootPolynomial ps
  let E := embedCoefficients ι
  let φ : Polynomial K →+* Polynomial ℝ := mapRingHom ι
  have iφ : Function.Injective φ := Polynomial.map_injective ι ι.injective
  have iE : Function.Injective E := Polynomial.map_injective φ iφ
  have hQ : E q ≠ 0 := fun h => rootPolynomial_ne_zero ps (iE (h.trans E.map_zero.symm))
  have hR : (E q).resultant (E q).derivative ≠ 0 := by
    have eq : (E q).resultant (E q).derivative = φ (q.resultant q.derivative) := by
      change (q.map φ).resultant (q.map φ).derivative = _
      rw [derivative_map, natDegree_map_eq_of_injective iφ q,
        natDegree_map_eq_of_injective iφ q.derivative, resultant_map_map]
    intro h
    exact rootPolynomial_resultant_ne_zero ps (iφ ((eq.symm.trans h).trans φ.map_zero.symm))
  refine Projection.ofResultant _ (E q) hQ hR ?_
  intro f hf hn
  obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
  have h0 : g ≠ 0 := fun h => hn (h ▸ E.map_zero)
  obtain ⟨n,hn'⟩ := exists_dvd_radical_self_pow h0
  refine ⟨E (radical g), map_dvd E (radical_dvd_rootPolynomial hg h0),
    map_dvd E radical_dvd_self, n, ?_⟩
  rw [← map_pow]
  exact map_dvd E hn'

/-- Check a projection supplied by a polynomial arithmetic engine using a
    Bézout identity. The cleared denominator is a base cut. A supplied
    identity can replace calculation of a Sylvester determinant. -/
noncomputable def Projection.ofBezout (ps : List (BiPoly ℝ)) (q a b : BiPoly ℝ)
    (c : Polynomial ℝ) (hq : q ≠ 0) (hc : c ≠ 0)
    (identity : a*q + b*q.derivative = C c)
    (hfactors : ∀ f ∈ ps, f ≠ 0 → ∃ d, d ∣ q ∧ d ∣ f ∧ ∃ n : ℕ, f ∣ d^n) :
    Projection ps where
  root := q
  cuts := [q.leadingCoeff,c]
  nonzero f hf := by
    rcases List.mem_cons.mp hf with h | h
    · subst f
      exact leadingCoeff_ne_zero.mpr hq
    · rw [List.mem_singleton] at h
      exact h ▸ hc
  regular x h := by
    refine ⟨h _ (by simp),fun y hy hd => ?_⟩
    have he := congrArg (fun f => value f (x,y)) identity
    rw [value_add, value_mul, value_mul, value_x, hy, hd, mul_zero, mul_zero, add_zero] at he
    exact h c (by simp) he.symm
  factors := hfactors

end CertifiedTopology.Plane
