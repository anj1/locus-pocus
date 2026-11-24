module

public import CertifiedTopology.ComputedTopology

@[expose] public section

namespace CertifiedTopology.ComputedInput

open ExecutableIsolation CylindricalData

/-- Distinct real roots are numbered from the smallest, starting at zero.
    Coefficients of the defining rational polynomial are in ascending order. -/
structure RootSpec where
  coefficients : List ℚ
  index : ℕ

def selectRoot {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (model : RealModel K) (input : RootSpec) : Option (AlgebraicRoot.Root model) :=
  let coefficients := List.map (Rat.cast : ℚ → K) input.coefficients
  (AlgebraicRoot.roots model (isolate model coefficients))[input.index]?

theorem selectRoot_correct {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (model : RealModel K) {input : RootSpec} {r : AlgebraicRoot.Root model}
    (h : selectRoot model input = some r) :
    (realPoly model.hom (List.map (Rat.cast : ℚ → K) input.coefficients)).IsRoot r.value := by
  unfold selectRoot at h
  exact AlgebraicRoot.roots_sound model _ (List.mem_of_getElem? h)

theorem selectRoot_value {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (model : RealModel K) (input : RootSpec) :
    (selectRoot model input).map AlgebraicRoot.Root.value =
      (sortedRoots (realPoly model.hom (List.map (Rat.cast : ℚ → K) input.coefficients)))[input.index]? := by
  let p := List.map (Rat.cast : ℚ → K) input.coefficients
  let res := isolate model p
  let rs := AlgebraicRoot.roots model res
  have sorted : rs.map AlgebraicRoot.Root.value = sortedRoots (realPoly model.hom p) := by
    have spec := res.correct
    cases e : res.roots with
    | all =>
      rw [e] at spec
      have hz : realPoly model.hom p = 0 := spec
      have empty : rs = [] := by
        unfold rs AlgebraicRoot.roots
        split <;> simp_all
      rw [hz, empty, List.map_nil]
      exact (List.eq_nil_iff_length_eq_zero.mpr (by simp [sortedRoots])).symm
    | finite ws =>
      rw [e] at spec
      apply roots_eq_sorted spec.1 (List.pairwise_map.mpr (AlgebraicRoot.roots_ordered model res))
      intro t
      rw [List.mem_map]
      exact ⟨fun ⟨a,ha,e⟩ => e ▸ AlgebraicRoot.roots_sound model res ha,
        fun h => AlgebraicRoot.roots_complete model res spec.1 h⟩
  change rs[input.index]?.map AlgebraicRoot.Root.value = (sortedRoots (realPoly model.hom p))[input.index]?
  rw [← sorted,List.getElem?_map]

theorem selectRoot_index {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (model : RealModel K) {input : RootSpec} {r : AlgebraicRoot.Root model}
    (h : selectRoot model input = some r) :
    (sortedRoots (realPoly model.hom (List.map (Rat.cast : ℚ → K) input.coefficients)))[input.index]? =
      some r.value := by
  simpa only [h, Option.map_some] using (selectRoot_value model input).symm

def coefficients : (specs : List RootSpec) → Option (ExactPoint RealModel.rational specs.length)
  | [] => some (.origin RealModel.rational)
  | s :: ss =>
    match coefficients ss with
    | none => none
    | some p => (selectRoot p.model s).map (fun r => p.extend (AlgebraicRoot.rootSample p.model r).val)

noncomputable def RootSpec.realValue (s : RootSpec) : Option ℝ :=
  (sortedRoots (realPoly (Rat.castHom ℝ) s.coefficients))[s.index]?

theorem selectRoot_realValue {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (model : RealModel K) (s : RootSpec) :
    (selectRoot model s).map AlgebraicRoot.Root.value = s.realValue := by
  have eq (cs : List ℚ) : realPoly model.hom (List.map (Rat.cast : ℚ → K) cs) =
      realPoly (Rat.castHom ℝ) cs := by
    induction cs with
    | nil => simp [realPoly, DensePolynomial.polynomial]
    | cons c cs ih =>
      rw [List.map_cons]
      change Polynomial.map model.hom (Polynomial.C (c : K) +
        Polynomial.X * DensePolynomial.polynomial (List.map (Rat.cast : ℚ → K) cs)) =
        Polynomial.map (Rat.castHom ℝ) (Polynomial.C c + Polynomial.X * DensePolynomial.polynomial cs)
      simp only [Polynomial.map_add, Polynomial.map_C, Polynomial.map_mul, Polynomial.map_X, map_ratCast]
      simp only [realPoly] at ih
      rw [ih]
      rfl
  unfold RootSpec.realValue
  rw [selectRoot_value, eq]

theorem coefficients_exists (specs : List RootSpec) :
    (coefficients specs).isSome = true ↔ ∀ s ∈ specs, s.realValue.isSome = true := by
  induction specs with
  | nil => simp [coefficients]
  | cons s ss ih =>
    simp only [coefficients, List.forall_mem_cons]
    cases h : coefficients ss with
    | none =>
      have hn : ¬ ∀ t ∈ ss, t.realValue.isSome = true := fun ht => by
        simpa [h] using ih.mpr ht
      simp [h, hn]
    | some p =>
      have ht := ih.mp (by simp [h])
      have eq : (selectRoot p.model s).isSome = s.realValue.isSome := by
        simpa using congrArg Option.isSome (selectRoot_realValue p.model s)
      simp only [Option.isSome_map, eq]
      exact (and_iff_left ht).symm

/-- The coefficient tower contains the selected roots in input order, with
    coordinates reversed because it adjoins the tail of the list first. -/
theorem coefficients_correct {specs : List RootSpec} {p : ExactPoint RealModel.rational specs.length}
    (h : coefficients specs = some p) (i : Fin specs.length) :
    (specs.get i).realValue = some (p.value i.rev) := by
  induction specs with
  | nil => exact i.elim0
  | cons s ss ih =>
    simp only [coefficients] at h
    split at h
    · contradiction
    · rename_i q hq
      cases hr : selectRoot q.model s with
      | none => simp [hr] at h
      | some r =>
        rw [hr, Option.map_some, Option.some.injEq] at h
        subst p
        rw [ExactPoint.value_extend]
        cases i using Fin.cases with
        | zero =>
          simpa only [List.get_cons_zero, Fin.rev_zero, Fin.snoc_last, hr, Option.map_some,
            (AlgebraicRoot.rootSample q.model r).property] using (selectRoot_realValue q.model s).symm
        | succ j =>
          rw [Fin.rev_succ, Fin.snoc_castSucc]
          exact ih hq j

structure SparseTerm (m : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  coefficient : Sum ℚ (Fin m)

def SparseTerm.polynomial {m : ℕ} (p : ExactPoint RealModel.rational m) (t : SparseTerm m) :
    Multi p.field 3 :=
  let c := t.coefficient.elim p.coefficients (p.point ∘ Fin.rev)
  Multi.constant c * (Multi.coordinate 0)^t.x * (Multi.coordinate 1)^t.y * (Multi.coordinate 2)^t.z

def sparse {m : ℕ} (p : ExactPoint RealModel.rational m) (terms : List (SparseTerm m)) : Multi p.field 3 :=
  (terms.map (SparseTerm.polynomial p)).sum

noncomputable def SparseTerm.eval {m : ℕ} (p : ExactPoint RealModel.rational m) (t : SparseTerm m)
    (a : Fin 3 → ℝ) : ℝ :=
  t.coefficient.elim Rat.cast (p.value ∘ Fin.rev) * (a 0)^t.x * (a 1)^t.y * (a 2)^t.z

noncomputable def SparseTerm.evalSpec (specs : List RootSpec) (t : SparseTerm specs.length)
    (a : Fin 3 → ℝ) : ℝ :=
  t.coefficient.elim Rat.cast (fun i => (specs.get i).realValue.getD 0) *
    (a 0)^t.x * (a 1)^t.y * (a 2)^t.z

theorem SparseTerm.eval_spec {specs : List RootSpec} {p : ExactPoint RealModel.rational specs.length}
    (h : coefficients specs = some p) (t : SparseTerm specs.length) (a : Fin 3 → ℝ) :
    t.eval p a = t.evalSpec specs a := by
  unfold SparseTerm.eval SparseTerm.evalSpec
  cases e : t.coefficient with
  | inl q => rfl
  | inr i => simp only [Sum.elim_inr, Function.comp_apply, coefficients_correct h i, Option.getD_some]

theorem SparseTerm.eval_correct {m : ℕ} (p : ExactPoint RealModel.rational m) (t : SparseTerm m)
    (a : Fin 3 → ℝ) :
    Multi.evalHom p.model.hom a (t.polynomial p) = t.eval p a := by
  simp only [SparseTerm.polynomial, SparseTerm.eval, map_mul, map_pow, Multi.eval_constant, Multi.eval_coordinate]
  congr 3
  cases t.coefficient with
  | inl q =>
    have eq := RealModel.rational.hom_eq (Rat.castHom ℝ) Rat.cast_strictMono
    exact (DFunLike.congr_fun p.compatible q).trans (DFunLike.congr_fun eq q)
  | inr i => rfl

theorem sparse_correct {m : ℕ} (p : ExactPoint RealModel.rational m)
    (terms : List (SparseTerm m)) (a : Fin 3 → ℝ) :
    Multi.evalHom p.model.hom a (sparse p terms) = (terms.map fun t => t.eval p a).sum := by
  induction terms with
  | nil => simp [sparse]
  | cons t ts ih => simpa [sparse, SparseTerm.eval_correct] using congrArg (t.eval p a + ·) ih

def solve {m : ℕ} (p : ExactPoint RealModel.rational m) (a b : List (SparseTerm m)) :
    ComputedTopology.Intersection p.model (sparse p a) (sparse p b) :=
  ComputedTopology.solve p.model (sparse p a) (sparse p b)

def solveStrata {m : ℕ} (p : ExactPoint RealModel.rational m) (a b : List (SparseTerm m)) :
    CADDecision.Stratification p.model (ComputedTopology.zeroSetFormula (sparse p a) (sparse p b)) [] :=
  ComputedTopology.stratifyIntersection p.model (sparse p a) (sparse p b)

def rationalJson (a b : List (SparseTerm 0)) : Lean.Json :=
  (solve (.origin RealModel.rational) a b).toJson (some fun c => Lean.toJson (toString (show ℚ from c)))

end CertifiedTopology.ComputedInput
