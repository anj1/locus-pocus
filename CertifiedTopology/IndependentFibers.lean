module

public import CertifiedTopology.CADSeparation

@[expose] public section

namespace CertifiedTopology.CADDecision

open Polynomial Set ExecutableIsolation CylindricalData ComputableCAD

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

def fixedCoefficients : List (Multi K n) → Option (List K)
  | [] => some []
  | p :: ps =>
    match Multi.constantValue p, fixedCoefficients ps with
    | some a, some as => some (a :: as)
    | _, _ => none

theorem fixedCoefficients_correct (model : RealModel K) (x : Fin n → ℝ)
    {ps : List (Multi K n)} {qs : List K} (h : fixedCoefficients ps = some qs) :
    (DensePolynomial.polynomial ps).map (Multi.evalHom model.hom x) = realPoly model.hom qs := by
  induction ps generalizing qs with
  | nil =>
    have e : qs = [] := (Option.some.inj h).symm
    simp [e, realPoly, DensePolynomial.polynomial]
  | cons p ps ih =>
    cases hp : Multi.constantValue p with
    | none => simp [fixedCoefficients,hp] at h
    | some a =>
      cases hs : fixedCoefficients ps with
      | none => simp [fixedCoefficients,hp,hs] at h
      | some as =>
        have hq : qs = a :: as := by simpa [fixedCoefficients,hp,hs,eq_comm] using h
        rw [hq]
        simp only [realPoly,DensePolynomial.polynomial,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_X,
          Polynomial.map_C,Multi.constantValue_correct model.hom x p hp]
        exact congrArg (fun q => C (model.hom a) + X*q) (ih hs)

def fixedSource (p : ComputableCAD.Poly K n) : Option (PolynomialData K) :=
  if p.coefficients.length ≤ 1 then some 1
  else if p = ProjectionData.term p.natDegree (p.coefficient p.natDegree) then some PolynomialData.X
  else (fixedCoefficients p.coefficients).map PolynomialData.ofCoefficients

theorem fixedSource_correct (model : RealModel K) (p : ComputableCAD.Poly K n)
    (x : Fin n → ℝ) (hn : specialized model p x ≠ 0) {q : PolynomialData K}
    (h : fixedSource p = some q) :
    realPoly model.hom q.coefficients ≠ 0 ∧
      ∀ z, (realPoly model.hom q.coefficients).IsRoot z ↔ (specialized model p x).IsRoot z := by
  unfold fixedSource at h
  split at h
  · rename_i short
    have e : q = 1 := (Option.some.inj h).symm
    subst q
    change (1 : PolynomialData K).polynomial.map model.hom ≠ 0 ∧
      ∀ z, (((1 : PolynomialData K).polynomial).map model.hom).IsRoot z ↔ (specialized model p x).IsRoot z
    simp only [PolynomialData.polynomial_one,Polynomial.map_one]
    refine ⟨one_ne_zero,?_⟩
    intro z
    cases he : p.coefficients with
    | nil => exact (hn (by simp [specialized,PolynomialData.polynomial,DensePolynomial.polynomial,he])).elim
    | cons a as =>
      cases as with
      | nil =>
        have eq : specialized model p x = C (Multi.evalHom model.hom x a) := by
          simp [specialized,PolynomialData.polynomial,DensePolynomial.polynomial,he]
        have nz : Multi.evalHom model.hom x a ≠ 0 := fun hz => hn (by rw [eq,hz,C_0])
        simp [eq,IsRoot.def,nz]
      | cons b bs => simp [he] at short
  · rename_i long
    split at h
    · rename_i mono
      have e : q = PolynomialData.X := (Option.some.inj h).symm
      subst q
      have hd : p.natDegree ≠ 0 := by unfold PolynomialData.natDegree; omega
      have eq : specialized model p x =
          C (Multi.evalHom model.hom x (p.coefficient p.natDegree)) * X^p.natDegree := by
        conv_lhs => rw [mono]
        simp [specialized]
      have nz : Multi.evalHom model.hom x (p.coefficient p.natDegree) ≠ 0 :=
        fun h => hn (by rw [eq,h,C_0,zero_mul])
      change (PolynomialData.X (K := K)).polynomial.map model.hom ≠ 0 ∧
        ∀ z, ((PolynomialData.X (K := K)).polynomial.map model.hom).IsRoot z ↔ (specialized model p x).IsRoot z
      simp only [PolynomialData.polynomial_X,Polynomial.map_X,eq,IsRoot.def,
        eval_mul,eval_C,eval_pow,eval_X,mul_eq_zero,nz,false_or,pow_eq_zero_iff hd]
      exact ⟨X_ne_zero,fun _ => trivial⟩
    · cases e : fixedCoefficients p.coefficients with
      | none => simp [e] at h
      | some qs =>
        have t : q = PolynomialData.ofCoefficients qs := by
          simpa only [e,Option.map_some,Option.some.injEq,eq_comm] using h
        subst q
        have eq : specialized model p x = (PolynomialData.ofCoefficients qs).polynomial.map model.hom :=
          (fixedCoefficients_correct model x e).trans
            (congrArg (fun f : Polynomial K => f.map model.hom) (PolynomialData.polynomial_ofCoefficients _)).symm
        change (PolynomialData.ofCoefficients qs).polynomial.map model.hom ≠ 0 ∧
          ∀ z, ((PolynomialData.ofCoefficients qs).polynomial.map model.hom).IsRoot z ↔
            (specialized model p x).IsRoot z
        rw [← eq]
        simp [hn]

/-- A stack row can use a fixed one-dimensional slice when its root
    positions are independent of the base point. -/
def fixedRow (model : RealModel K) (q : PolynomialData K) (i : ℕ) : Slice (AlgebraicRoot.Root model) :=
  (CADStacks.slicesOf none (AlgebraicRoot.roots model (isolate model q.coefficients))).getD i (.sector none none)

theorem fixedRow_correct (model : RealModel K) (p : ComputableCAD.Poly K n)
    (x : Fin n → ℝ) (hn : specialized model p x ≠ 0) {q : PolynomialData K}
    (h : fixedSource p = some q) (i : ℕ) :
    CADStacks.mapSlice AlgebraicRoot.Root.value (fixedRow model q i) =
      (realStack (specialized model p x)).getD i (.sector none none) := by
  let r := isolate model q.coefficients
  let rs := AlgebraicRoot.roots model r
  have spec := fixedSource_correct model p x hn h
  have eq : rs.map AlgebraicRoot.Root.value = sortedRoots (specialized model p x) := by
    apply roots_eq_sorted hn (List.pairwise_map.mpr (AlgebraicRoot.roots_ordered model r))
    intro z
    refine Iff.trans ?_ (spec.2 z)
    rw [List.mem_map]
    exact ⟨fun ⟨w,hw,e⟩ => e ▸ AlgebraicRoot.roots_sound model r hw,
      fun hz => AlgebraicRoot.roots_complete model r spec.1 hz⟩
  have e := CADStacks.slicesOf_map (AlgebraicRoot.Root.value (model := model)) none rs
  rw [realStack,← CADStacks.slicesOf_real,← eq]
  change CADStacks.mapSlice AlgebraicRoot.Root.value ((CADStacks.slicesOf none rs).getD i (.sector none none)) =
    (CADStacks.slicesOf ((none : Option (AlgebraicRoot.Root model)).map AlgebraicRoot.Root.value)
      (rs.map AlgebraicRoot.Root.value)).getD i (.sector none none)
  rw [← e]
  let f : Slice (AlgebraicRoot.Root model) → Slice ℝ := CADStacks.mapSlice AlgebraicRoot.Root.value
  exact (List.getD_map (CADStacks.slicesOf none rs) (.sector none none) (n := i) f).symm

end CertifiedTopology.CADDecision
