module

public import CertifiedTopology.Input
public import CertifiedTopology.Univariate

@[expose] public section

namespace CertifiedTopology
open Polynomial

namespace Expr
/-- Interpret the polynomial expression after choosing a univariate parameterization. -/
noncomputable def polynomial {ι} (vars : ι → Polynomial ℝ) : Expr ℝ ι → Polynomial ℝ
  | .const c => C c
  | .var i => vars i
  | .neg f => -(f.polynomial vars)
  | .add f g => f.polynomial vars + g.polynomial vars
  | .mul f g => f.polynomial vars * g.polynomial vars

theorem polynomial_correct {ι} (e : Expr ℝ ι) (vars : ι → Polynomial ℝ) (t : ℝ) :
    (e.polynomial vars).eval t = e.eval (fun i => (vars i).eval t) := by
  induction e <;> simp_all [polynomial,eval]
end Expr

namespace Predicate

noncomputable def polynomials {ι} (vars : ι → Polynomial ℝ) : Predicate ℝ ι → List (Polynomial ℝ)
  | .atom e _ => [e.polynomial vars]
  | .truth _ => []
  | .neg f => f.polynomials vars
  | .conj f g | .disj f g => f.polynomials vars ++ g.polynomials vars

theorem eval_on_path {ι} (f : Predicate ℝ ι) (vars : ι → Polynomial ℝ) {x y : ℝ}
    (h : ∀ p ∈ f.polynomials vars, side (p.eval x) 0 = side (p.eval y) 0) :
    f.eval (fun i => (vars i).eval x) = f.eval (fun i => (vars i).eval y) := by
  induction f with
  | truth => rfl
  | atom e s =>
    have he := h (e.polynomial vars) (by simp [polynomials])
    simp only [Expr.polynomial_correct] at he
    simp [eval,he]
  | neg f ih => simp [eval,ih h]
  | conj f g ih jh | disj f g ih jh =>
    simp only [eval,ih (fun _ hp => h _ (List.mem_append_left _ hp)),
      jh (fun _ hp => h _ (List.mem_append_right _ hp))]

/-- The returned slice describes the final coordinate over the unique zero-dimensional base. -/
def sliceOf : Cell ℝ 1 → Slice ℝ
  | .lift .origin s => s

private theorem contains_slice (c : Cell ℝ 1) (x : ℝ) :
    Univariate.contains (sliceOf c) x ↔ c.Contains ((),x) := by
  cases c with
  | lift b s =>
    cases b
    change _ ↔ True ∧ _
    exact ⟨fun h => ⟨trivial,h⟩, And.right⟩

private theorem slice_injective : Function.Injective sliceOf := by
  rintro ⟨_⟩ ⟨_⟩ h
  rename_i b s c t
  cases b
  cases c
  exact congrArg (Cell.lift .origin) h

/-- Automatic dispatch on one real coordinate. Factored affine inputs use affine CAD;
    other polynomial formulas use the arbitrary-degree root partition. -/
noncomputable def solveLine (f : Predicate ℝ (Fin 1)) : List (Slice ℝ) :=
  match f.solveAffine? with
  | some cs => cs.map sliceOf
  | none =>
    (Univariate.decompose (f.polynomials (fun _ => X))).filter fun s =>
      f.eval (fun _ => Slice.sample (n := 0) () s)

theorem solveLine_correct (f : Predicate ℝ (Fin 1)) (x : ℝ) :
    f.eval (fun _ => x) = true ↔ ∃! s, s ∈ f.solveLine ∧ Univariate.contains s x := by
  cases he : f.solveAffine? with
  | some cs =>
    have hv : Aff.vector (K := ℝ) (n := 1) ((),x) = fun _ => x := by
      funext i
      fin_cases i
      rfl
    rw [← hv,f.solveAffine_correct he]
    simp only [solveLine,he]
    constructor
    · rintro ⟨c,⟨hc,hx⟩,hu⟩
      refine ⟨sliceOf c,⟨List.mem_map_of_mem hc,(contains_slice c x).mpr hx⟩,?_⟩
      rintro s ⟨hs,hy⟩
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hs
      exact congrArg sliceOf (hu d ⟨hd,(contains_slice d x).mp hy⟩)
    · rintro ⟨s,⟨hs,hx⟩,hu⟩
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hs
      refine ⟨c,⟨hc,(contains_slice c x).mp hx⟩,?_⟩
      rintro d ⟨hd,hy⟩
      exact slice_injective (hu _ ⟨List.mem_map_of_mem hd,(contains_slice d x).mpr hy⟩)
  | none =>
    let vars : Fin 1 → Polynomial ℝ := fun _ => X
    obtain ⟨cov,_,inv⟩ := Univariate.decompose_correct (f.polynomials vars)
    have H s (hs : s ∈ Univariate.decompose (f.polynomials vars)) (hx : Univariate.contains s x) :
        f.eval (fun _ => x) = f.eval (fun _ => Slice.sample (n := 0) () s) := by
      simpa [vars] using f.eval_on_path vars (inv s hs x hx)
    simp only [solveLine,he]
    obtain ⟨s,⟨hs,hx⟩,hu⟩ := cov x
    constructor
    · intro ht
      exact ⟨s,⟨List.mem_filter.mpr ⟨hs,(H s hs hx) ▸ ht⟩,hx⟩,
        fun d hd => hu d ⟨(List.mem_filter.mp hd.1).1,hd.2⟩⟩
    · rintro ⟨d,⟨hd,hy⟩,_⟩
      obtain ⟨hd,ht⟩ := List.mem_filter.mp hd
      exact (H d hd hy).trans ht

end Predicate
end CertifiedTopology
