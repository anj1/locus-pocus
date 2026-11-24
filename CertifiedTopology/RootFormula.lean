module

public import CertifiedTopology.FirstOrder
public import CertifiedTopology.CellRank

@[expose] public section

namespace CertifiedTopology.CADDecision

open Polynomial Set ExecutableIsolation CylindricalData AlgebraicRoot CADStacks

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable (model : RealModel K)

theorem side_on {a : ℝ} : side a 0 = .on ↔ a = 0 := by
  rcases lt_trichotomy a 0 with h | rfl | h
  · simp [side, h, h.ne]
  · simp
  · simp [side, h.not_gt, h.ne']

theorem side_below {a : ℝ} : side a 0 = .below ↔ a < 0 := by
  unfold side
  split <;> (try split) <;> simp_all

theorem side_above {a : ℝ} : side a 0 = .above ↔ 0 < a := by
  rcases lt_trichotomy a 0 with h | rfl | h
  · simp [side, h, h.not_gt]
  · simp [side]
  · simp [side, h, h.not_gt, h.ne']

def rationalCut (a : ℚ) (s : Side) : SignFormula K 1 :=
  .atom (Multi.coordinate 0 - Multi.constant (a : K)) s

theorem rationalCut_correct (a : ℚ) (s : Side) (x : Fin 1 → ℝ) :
    (rationalCut (K := K) a s).holds model x ↔ side (x 0 - a) 0 = s := by
  simp [rationalCut, SignFormula.holds]

def rootPolySign (r : Root model) (s : Side) : SignFormula K 1 :=
  .atom (PolynomialData.ofCoefficients r.polynomial) s

theorem rootPolySign_correct (r : Root model) (s : Side) (x : Fin 1 → ℝ) :
    (rootPolySign model r s).holds model x ↔ side ((realPoly model.hom r.polynomial).eval (x 0)) 0 = s := by
  change side (PolynomialData.evalHom model.hom (x 0) (PolynomialData.ofCoefficients r.polynomial)) 0 = s ↔ _
  rw [PolynomialData.evalHom_correct, PolynomialData.polynomial_ofCoefficients]

/-- On a single isolating interval, the squarefree polynomial's endpoint
    signs discriminate the two sides of its unique root. -/
def bracketCut (r : Root model) (s : Side) : SignFormula K 1 :=
  match r.window with
  | .point q => rationalCut q s
  | .interval l u =>
    let afterL := rationalCut l .above
    let beforeU := rationalCut u .below
    let inside := afterL.and beforeU
    match s with
    | .on => inside.and (rootPolySign model r .on)
    | .below => afterL.not.or (inside.and (rootPolySign model r (side (DensePolynomial.eval r.polynomial (l : K)) 0)))
    | .above => beforeU.not.or (inside.and (rootPolySign model r (side (DensePolynomial.eval r.polynomial (u : K)) 0)))

theorem bracketCut_correct (r : Root model) (s : Side) (x : Fin 1 → ℝ) :
    (bracketCut model r s).holds model x ↔ side (x 0-r.value) 0 = s := by
  cases h : r.window with
  | point q =>
    have w := r.represents.inside
    rw [h] at w
    have e : r.value = (q : ℝ) := w
    simpa only [bracketCut,h,e] using rationalCut_correct model q s x
  | interval l u =>
    let p := realPoly model.hom r.polynomial
    have rrep := r.represents
    rw [h] at rrep
    have hr : (l : ℝ) < r.value ∧ r.value < (u : ℝ) := rrep.inside
    have ends : p.eval (l : ℝ) * p.eval (u : ℝ) < 0 := rrep.crosses
    have nzl : p.eval (l : ℝ) ≠ 0 := fun e => by simp [e] at ends
    have nzu : p.eval (u : ℝ) ≠ 0 := fun e => by simp [e] at ends
    have distinct : side (p.eval (l : ℝ)) 0 ≠ side (p.eval (u : ℝ)) 0 := by
      intro he
      rcases mul_neg_iff.mp ends with a | a
      · have eq := (side_congr (K := ℝ) he).1
        exact (not_lt_of_gt a.1) (eq.mpr a.2)
      · exact (not_lt_of_gt a.2) ((side_congr (K := ℝ) he).1.mp a.1)
    have left (t : ℝ) (ht : t ∈ Ico (l : ℝ) r.value) :
        side (p.eval t) 0 = side (p.eval (l : ℝ)) 0 := by
      let A := Ico (l : ℝ) r.value
      letI : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp (convex_Ico _ _).isPreconnected
      refine Plane.same_sign_of_zero (f := fun a : A => p.eval a.val)
        (p.continuous.comp continuous_subtype_val) ⟨t,ht⟩ ⟨_,le_rfl,hr.1⟩ ?_
      intro y
      refine iff_of_false ?_ nzl
      intro hz
      rcases eq_or_lt_of_le y.property.1 with h | hy
      · exact nzl (h.symm ▸ hz)
      · exact y.property.2.ne (rrep.unique y.val ⟨hy,y.property.2.trans hr.2⟩ hz)
    have right (t : ℝ) (ht : t ∈ Ioc r.value (u : ℝ)) :
        side (p.eval t) 0 = side (p.eval (u : ℝ)) 0 := by
      let A := Ioc r.value (u : ℝ)
      letI : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp (convex_Ioc _ _).isPreconnected
      refine Plane.same_sign_of_zero (f := fun a : A => p.eval a.val)
        (p.continuous.comp continuous_subtype_val) ⟨t,ht⟩ ⟨_,hr.2,le_rfl⟩ ?_
      intro y
      refine iff_of_false ?_ nzu
      intro hz
      rcases eq_or_lt_of_le y.property.2 with h | hy
      · exact nzu (h ▸ hz)
      · exact y.property.1.ne' (rrep.unique y.val ⟨hr.1.trans y.property.1,hy⟩ hz)
    have ls : side (DensePolynomial.eval r.polynomial (l : K)) 0 = side (p.eval (l : ℝ)) 0 := by
      rw [map_side model.hom model.strictMono, map_eval model.hom]
    have us : side (DensePolynomial.eval r.polynomial (u : K)) 0 = side (p.eval (u : ℝ)) 0 := by
      rw [map_side model.hom model.strictMono, map_eval model.hom]
    cases s with
    | on =>
      simp only [bracketCut,h,SignFormula.holds.eq_4,rationalCut_correct,rootPolySign_correct,
        side_on,side_above,side_below,sub_pos,sub_neg,sub_eq_zero]
      exact ⟨fun ⟨a,b⟩ => rrep.unique (x 0) a b,fun e => e.symm ▸ ⟨hr,rrep.root⟩⟩
    | below =>
      change (bracketCut model r .below).holds model x ↔ _
      simp only [bracketCut,h,SignFormula.holds.eq_4,SignFormula.holds.eq_5,
        SignFormula.holds.eq_3,rationalCut_correct,rootPolySign_correct,side_above,
        side_below,sub_pos,sub_neg,ls]
      constructor
      · rintro (hl | ⟨⟨hl,hu⟩,hs⟩)
        · exact (le_of_not_gt hl).trans_lt hr.1
        · rcases lt_trichotomy (x 0) r.value with lt | he | gt
          · exact lt
          · exact (nzl (side_on.mp (hs.symm.trans (by rw [he]; exact side_on.mpr rrep.root)))).elim
          · exact (distinct (hs.symm.trans (right _ ⟨gt,hu.le⟩))).elim
      · intro hx
        by_cases hl : (l : ℝ) < x 0
        · exact Or.inr ⟨⟨hl,hx.trans hr.2⟩,left _ ⟨hl.le,hx⟩⟩
        · exact Or.inl hl
    | above =>
      simp only [bracketCut,h,SignFormula.holds.eq_4,SignFormula.holds.eq_5,
        SignFormula.holds.eq_3,rationalCut_correct,rootPolySign_correct,side_above,
        side_below,sub_pos,sub_neg,us]
      constructor
      · rintro (hu | ⟨⟨hl,hu⟩,hs⟩)
        · exact hr.2.trans_le (le_of_not_gt hu)
        · rcases lt_trichotomy (x 0) r.value with lt | he | gt
          · exact (distinct ((left _ ⟨hl.le,lt⟩).symm.trans hs)).elim
          · exact (nzu (side_on.mp (hs.symm.trans (by rw [he]; exact side_on.mpr rrep.root)))).elim
          · exact gt
      · intro hx
        by_cases hu : x 0 < (u : ℝ)
        · exact Or.inr ⟨⟨hr.1.trans hx,hu⟩,right _ ⟨hx,hu.le⟩⟩
        · exact Or.inl hu

/-- A linear defining polynomial supplies the endpoint directly in the
    coefficient field, avoiding cuts at the edges of its isolating window. -/
def isolatedCut (r : Root model) (s : Side) : SignFormula K 1 :=
  match r.polynomial with
  | [b, a] =>
    if a = 0 then bracketCut model r s
    else .atom (Multi.coordinate 0 - Multi.constant (-b / a)) s
  | _ => bracketCut model r s

theorem isolatedCut_correct (r : Root model) (s : Side) (x : Fin 1 → ℝ) :
    (isolatedCut model r s).holds model x ↔ side (x 0-r.value) 0 = s := by
  unfold isolatedCut
  split
  · rename_i b a h
    split
    · exact bracketCut_correct model r s x
    · rename_i ha
      have hr := r.represents.root
      rw [h, Polynomial.IsRoot.def] at hr
      have eq : model.hom b + model.hom a * r.value = 0 := by
        simpa [realPoly, DensePolynomial.polynomial, Polynomial.map_add, Polynomial.map_mul,
          Polynomial.eval_mul] using hr
      have nz : model.hom a ≠ 0 := fun e => ha (model.strictMono.injective (e.trans (map_zero _).symm))
      have er : r.value = -model.hom b / model.hom a := (eq_div_iff nz).mpr (by linarith only [eq])
      simp [SignFormula.holds, er]
  · exact bracketCut_correct model r s x

def isolatedSlice : Slice (Root model) → SignFormula K 1
  | .sectionAt r => isolatedCut model r .on
  | .sector l u =>
    (l.elim (.truth true) (fun r => isolatedCut model r .above)).and
      (u.elim (.truth true) (fun r => isolatedCut model r .below))

theorem isolatedSlice_correct (s : Slice (Root model)) (x : Fin 1 → ℝ) :
    (isolatedSlice model s).holds model x ↔ Univariate.contains (mapSlice Root.value s) (x 0) := by
  cases s with
  | sectionAt r =>
    rw [isolatedSlice,isolatedCut_correct,side_on,sub_eq_zero]
    rfl
  | sector l u =>
    cases l <;> cases u <;> simp [isolatedSlice, SignFormula.holds.eq_4, SignFormula.holds.eq_1,
      isolatedCut_correct,side_above,side_below,sub_pos,sub_neg,mapSlice,Univariate.contains,Slice.Contains,Aff.eval]

def univariateCell (p : ComputableCAD.Poly K 0) (row : ℕ) : SignFormula K 1 :=
  let res := isolate model (p.coefficients : List K)
  isolatedSlice model ((slicesOf none (AlgebraicRoot.roots model res)).getD row (.sector none none))

theorem univariateCell_correct (p : ComputableCAD.Poly K 0) (row : ℕ) (x : Fin 1 → ℝ)
    (hn : ComputableCAD.specialized model p Fin.elim0 ≠ 0) :
    (univariateCell model p row).holds model x ↔ x ∈ (Code.lift .origin p row).carrier model := by
  let res := isolate model (p.coefficients : List K)
  let rs := AlgebraicRoot.roots model res
  have hpoly : realPoly model.hom (p.coefficients : List K) =
      ComputableCAD.specialized model p Fin.elim0 := rfl
  have roots_eq : rs.map Root.value = sortedRoots (ComputableCAD.specialized model p Fin.elim0) := by
    apply roots_eq_sorted hn (List.pairwise_map.mpr (roots_ordered model res))
    intro t
    rw [← hpoly,List.mem_map]
    exact ⟨fun ⟨r,h,he⟩ => he ▸ roots_sound model res h, fun h => roots_complete model res (hpoly ▸ hn) h⟩
  rw [univariateCell,isolatedSlice_correct]
  change Univariate.contains (mapSlice Root.value ((slicesOf none rs).getD row (.sector none none))) (x 0) ↔
    (_ ∧ Univariate.contains
    ((realStack (ComputableCAD.specialized model p (CADStacks.dropLast x))).getD row _) (x 0))
  have e : CADStacks.dropLast x = Fin.elim0 := Subsingleton.elim _ _
  have frames : (slicesOf none rs).map (mapSlice Root.value) = slicesOf none (rs.map Root.value) :=
    slicesOf_map Root.value none rs
  rw [e,realStack,← slicesOf_real,← roots_eq,← frames]
  have get : ((slicesOf none rs).map (mapSlice Root.value)).getD row (.sector none none) =
      mapSlice Root.value ((slicesOf none rs).getD row (.sector none none)) :=
    List.getD_map _ (.sector none none) (mapSlice Root.value)
  rw [get]
  exact (and_iff_right (mem_univ _)).symm

end CertifiedTopology.CADDecision
