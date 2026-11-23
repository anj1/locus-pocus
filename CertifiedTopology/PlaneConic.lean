module

public import CertifiedTopology.PlaneCharts
public import CertifiedTopology.Trivialization
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

@[expose] public section

namespace CertifiedTopology.Plane

open Polynomial
open Quadratic (Kind Family)

noncomputable def asFamily (f : BiPoly ℝ) : Family := ⟨f.coeff 2, f.coeff 1, f.coeff 0⟩

theorem asFamily_value {f : BiPoly ℝ} (h : f.natDegree ≤ 2) (x y : ℝ) :
    (asFamily f).value x y = value f (x,y) := by
  have eq : f = C (f.coeff 2) * X^2 + C (f.coeff 1) * X + C (f.coeff 0) := by
    apply AddMonoidAlgebra.coeff_injective
    apply DFunLike.ext
    intro i
    simp only [coeff_add, coeff_C_mul_X_pow, coeff_C]
    by_cases hi : i ≤ 2
    · interval_cases i <;> simp
    · obtain ⟨i, rfl⟩ : ∃ j, i = j + 3 := ⟨i-3, by omega⟩
      simp [coeff_eq_zero_of_natDegree_lt (show f.natDegree < i + 3 by omega)]
  change (asFamily f).value x y = ((f.map (evalRingHom x)).eval y)
  conv_rhs => rw [eq]
  simp [asFamily, Family.value, pow_two]

noncomputable def modelPolynomial : Kind → Polynomial ℝ
  | .line => 0
  | .empty => 1
  | .point => X
  | .twoPoints => X^2 - C 1

theorem modelPolynomial_zero (k : Kind) (t : ℝ) :
    (modelPolynomial k).eval t = 0 ↔ k.model t := by
  cases k <;> simp [modelPolynomial, Kind.model, sub_eq_zero]

noncomputable def constModel (x : ℝ) : Polynomial ℝ :=
  if x = 0 then 0 else 1

theorem constModel_zero (x t : ℝ) : (constModel x).eval t = 0 ↔ x = 0 := by
  by_cases hx : x = 0 <;> simp [constModel, hx]

/-- A single active quadratic in the lifting coordinate, with any number of
    constraints in the base coordinate. Degree drops are detected at projection. -/
noncomputable def conicChart (f : BiPoly ℝ) (hf : f.natDegree ≤ 2)
    (xs : List (Polynomial ℝ)) (s : Slice ℝ)
    (hs : s ∈ Univariate.decompose ((asFamily f).projection ++ xs)) :
    Chart (f :: xs.map C) s := by
  let F := asFamily f
  let d := Isolation.fromProjection F.projection xs
  let x₀ := Slice.sample (n := 0) () s
  let row := (s, F.projection.map fun p => side (p.eval x₀) 0)
  have hr : row ∈ d.rows := List.mem_map_of_mem hs
  let h := F.trivialization d hr
  let T : Band s ≃ₜ Band s := h.choose
  have ht := h.choose_spec
  let k := Quadratic.Family.kindOfSigns row.2
  refine ⟨T.symm, ?_, modelPolynomial k :: xs.map (fun g => constModel (g.eval x₀)), ?_⟩
  · intro p
    have eq : (T (T.symm p)).1 = (T.symm p).1 := ht.1 (T.symm p)
    rw [T.apply_symm_apply] at eq
    exact eq.symm
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · refine ⟨modelPolynomial k, by simp, fun p => ?_⟩
      rw [modelPolynomial_zero]
      have he : k.model (T.symm p).2 ↔ F.value (T (T.symm p)).1.val (T (T.symm p)).2 = 0 :=
        ht.2 (T.symm p)
      rw [T.apply_symm_apply] at he
      rw [← asFamily_value hf]
      exact he.symm
    · obtain ⟨g,hgx,rfl⟩ := List.mem_map.mp hg
      refine ⟨constModel (g.eval x₀), List.mem_cons_of_mem _ (List.mem_map_of_mem hgx), fun p => ?_⟩
      rw [constModel_zero, value_x]
      exact (side_congr ((Univariate.decompose_correct (F.projection ++ xs)).2.2 s hs
        p.1.val p.1.property g (List.mem_append_right _ hgx))).2.1

noncomputable def ofConic (f : BiPoly ℝ) (hf : f.natDegree ≤ 2)
    (xs : List (Polynomial ℝ)) : Diagram (f :: xs.map C) :=
  ofCharts ((asFamily f).projection ++ xs) _ (conicChart f hf xs)

/-- Recognize a single nonconstant polynomial in the lifting coordinate,
    allowing duplicates and any number of base-only conditions. -/
noncomputable def solveConic? (ps : List (BiPoly ℝ)) : Option (Diagram ps) := by
  classical
  match ps.find? (fun f => 0 < f.natDegree) with
  | none => exact none
  | some f =>
    by_cases h : f.natDegree ≤ 2 ∧ ∀ g ∈ ps, g = f ∨ g.natDegree = 0
    · let xs := ps.map (fun g => g.coeff 0)
      refine some ((ofConic f h.1 xs).restrict ?_)
      intro g hg
      rcases h.2 g hg with he | hd
      · simp [he]
      · apply List.mem_cons_of_mem
        apply List.mem_map.mpr
        exact ⟨g.coeff 0, List.mem_map_of_mem hg, (const_coeff hd).symm⟩
    · exact none

end CertifiedTopology.Plane
