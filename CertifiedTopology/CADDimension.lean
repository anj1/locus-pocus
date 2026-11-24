module

public import CertifiedTopology.CADPrefix
public import CertifiedTopology.CADClosure
public import Mathlib.Topology.GDelta.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace CertifiedTopology.CADDecision

open Set Topology ExecutableIsolation ComputableCAD CADStacks CylindricalData

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ}

/-- No coordinate projection to the specified number of coordinates has
    dense image in a nonempty open set. -/
def ThinAt (d : ℕ) (A : Set (Fin n → ℝ)) : Prop :=
  ∀ i : Fin d ↪ Fin n, IsNowhereDense (FreeChart.project i '' A)

namespace ThinAt

theorem mono {d : ℕ} {A B : Set (Fin n → ℝ)} (h : ThinAt d B) (hAB : A ⊆ B) : ThinAt d A :=
  fun i => (h i).mono (image_mono hAB)

theorem empty (n d : ℕ) : ThinAt d (∅ : Set (Fin n → ℝ)) := by
  intro i
  simp [IsNowhereDense]

theorem union {d : ℕ} {A B : Set (Fin n → ℝ)} (hA : ThinAt d A) (hB : ThinAt d B) : ThinAt d (A ∪ B) := by
  intro i
  rw [image_union]
  exact (hA i).union (hB i)

theorem iUnion {ι : Type} [Finite ι] {d : ℕ} {A : ι → Set (Fin n → ℝ)} (h : ∀ i, ThinAt d (A i)) :
    ThinAt d (⋃ i, A i) := by
  intro e
  rw [image_iUnion]
  exact IsNowhereDense.iUnion fun i => h i e

theorem closure {d : ℕ} {A : Set (Fin n → ℝ)} (h : ThinAt d A) : ThinAt d (closure A) :=
  fun i => (h i).closure.mono (image_closure_subset_closure_image (FreeChart.project_continuous i))

theorem aboveAmbient {d : ℕ} (h : n < d) (A : Set (Fin n → ℝ)) : ThinAt d A := by
  intro i
  have hn := Fintype.card_le_of_injective i i.injective
  simp only [Fintype.card_fin] at hn
  omega

theorem zero_iff_empty (A : Set (Fin n → ℝ)) : ThinAt 0 A ↔ A = ∅ := by
  constructor
  · intro h
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    let e : Fin 0 ↪ Fin n := ⟨Fin.elim0,fun x => x.elim0⟩
    have eq : FreeChart.project e '' A = univ :=
      eq_univ_iff_forall.mpr fun y => ⟨x,hx,Subsingleton.elim _ _⟩
    have hn := h e
    rw [eq,IsNowhereDense,closure_univ,interior_univ] at hn
    exact univ_nonempty.ne_empty hn
  · rintro rfl
    exact empty n 0

end ThinAt

noncomputable def extendProjection {d : ℕ} (e : Fin d ↪ Fin n) : Fin (d + (n-d)) ≃ Fin n := by
  classical
  let R := range e
  let a : Fin d ≃ R := Equiv.ofInjective e e.injective
  let b : Fin (n-d) ≃ (Rᶜ : Set (Fin n)) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, Fintype.card_compl_set, Fintype.card_fin,
      ← Fintype.card_congr a, Fintype.card_fin])
  exact finSumFinEquiv.symm.trans ((a.sumCongr b).trans (Equiv.Set.sumCompl R))

theorem extendProjection_prefix {d : ℕ} (e : Fin d ↪ Fin n) (i : Fin d) :
    extendProjection e (Fin.castAdd (n-d) i) = e i := by
  classical
  simp [extendProjection,Equiv.Set.sumCompl,Equiv.sumCompl,Equiv.ofInjective]

noncomputable def coordinateOrder {m : ℕ} (e : Fin m ≃ Fin n) :
    (Fin n → ℝ) ≃ₜ (Fin m → ℝ) where
  toFun x := x ∘ e
  invFun x := x ∘ e.symm
  left_inv x := by ext i; simp
  right_inv x := by ext i; simp
  continuous_toFun := continuous_pi fun i => continuous_apply (e i)
  continuous_invFun := continuous_pi fun i => continuous_apply (e.symm i)

theorem coordinateProjection_open {d : ℕ} (e : Fin d ↪ Fin n) : IsOpenMap (FreeChart.project e) := by
  have eq : FreeChart.project e = prefixPoint d (n-d) ∘ coordinateOrder (extendProjection e) := by
    funext p i
    change p (e i) = p (extendProjection e (Fin.castAdd (n-d) i))
    rw [extendProjection_prefix]
  rw [eq]
  exact (prefixPoint_open d (n-d)).comp (coordinateOrder (extendProjection e)).isOpenMap

theorem cell_dimension_bound {model : RealModel K} {d : ℕ} {A : Set (Fin n → ℝ)}
    (h : ThinAt (d+1) A) (c : ComputableCAD.Cell model n) (sub : c.carrier ⊆ A) :
    c.code.dimension ≤ d := by
  by_contra! big
  let F := c.freeChart.some
  let e : Fin (d+1) ↪ Fin c.code.dimension := Fin.castLEEmb (Nat.succ_le_of_lt big)
  have eq : FreeChart.project (e.trans F.indices) '' c.carrier = FreeChart.project e '' F.domain := by
    rw [← F.image_eq, image_image]
    rfl
  have thin := (h (e.trans F.indices)).mono (image_mono sub)
  rw [eq] at thin
  have op := coordinateProjection_open e _ F.open_domain
  have ne : (FreeChart.project e '' F.domain).Nonempty :=
    ⟨_, mem_image_of_mem _ (F.chart ⟨c.sample.value,c.sample_mem⟩).property⟩
  exact ne.ne_empty (by
    have hh := interior_mono (s := FreeChart.project e '' F.domain)
        (t := closure (FreeChart.project e '' F.domain)) subset_closure
    rwa [op.interior_eq,thin,subset_empty_iff] at hh)

theorem region_cells {model : RealModel K} (f : Prenex K n) {c : ComputableCAD.Cell model n}
    (hc : c ∈ Prenex.regions model f) :
    c ∈ (ComputableCAD.cad model n (Prenex.compile model f).tests).cells := by
  obtain ⟨a,_,h⟩ := List.mem_filterMap.mp hc
  split at h
  · exact (Option.some.inj h) ▸ a.property
  · cases h

theorem prefix_boundary_thin (model : RealModel K) (d k : ℕ) (f : Prenex K (d+k))
    (bound : ThinAt (d+1) {x | f.holds model x}) :
    IsNowhereDense (prefixPoint d k '' (closure {x | f.holds model x} \ {x | f.holds model x})) := by
  classical
  let plan := Prenex.compile model f
  let bd := ComputableCAD.cad model d (projectPrefix d k plan.tests)
  let cs := Prenex.regions model f
  let S := {x | f.holds model x}
  let thinBase := ⋃ i : Fin bd.cells.length,
    if (bd.cells.get i).code.dimension < d then (bd.cells.get i).carrier else ∅
  have thin : IsNowhereDense thinBase := by
    apply IsNowhereDense.iUnion
    intro i
    split
    · rename_i h
      exact (bd.cells.get i).freeChart.some.thin h
    · simp [IsNowhereDense]
  refine thin.mono ?_
  rintro _ ⟨x,⟨hc,hs⟩,rfl⟩
  obtain ⟨b,⟨hb,hx⟩,unique⟩ := bd.partition (prefixPoint d k x)
  by_cases hdim : b.code.dimension < d
  · obtain ⟨i,rfl⟩ := List.get_of_mem hb
    exact mem_iUnion.mpr ⟨i,by simpa only [ite_eq_left hdim] using hx⟩
  have db : b.code.dimension = d := by
    have h := Fintype.card_le_of_injective b.freeChart.some.indices b.freeChart.some.indices.injective
    simp only [Fintype.card_fin] at h
    omega
  have ob : IsOpen b.carrier := by
    have h := b.freeChart
    rw [db] at h
    exact h.some.full_open
  let T := prefixPoint d k ⁻¹' b.carrier
  have oT : IsOpen T := ob.preimage (prefixPoint_continuous _ _)
  let z : T := ⟨x,hx⟩
  let B (c : ComputableCAD.Cell model (d+k)) := prefixCode d k c.code = b.code
  have restrict : (Subtype.val : T → Fin (d+k) → ℝ) ⁻¹' S =
      ⋃ i : Fin cs.length,
        if B (cs.get i) then (Subtype.val : T → Fin (d+k) → ℝ) ⁻¹' (cs.get i).carrier else ∅ := by
    ext y
    rw [mem_iUnion]
    constructor
    · intro hy
      obtain ⟨c,hc,hcy⟩ := (Prenex.regions_correct model f y.val).mp hy
      obtain ⟨b',hb',ep⟩ := cad_prefix_mem model d k plan.tests c (region_cells f hc)
      have hh := prefix_member model d k c.code _ hcy
      rw [ep] at hh
      obtain ⟨_,_,uy⟩ := bd.partition (prefixPoint d k y.val)
      have e := (uy b' ⟨hb',hh⟩).trans (uy b ⟨hb,y.property⟩).symm
      obtain ⟨i,rfl⟩ := List.get_of_mem hc
      have hp : B (cs.get i) := ep.trans (congrArg ComputableCAD.Cell.code e)
      refine ⟨i,?_⟩
      rw [ite_eq_left hp]
      exact hcy
    · rintro ⟨i,hy⟩
      split at hy
      · exact (Prenex.regions_correct model f y.val).mpr ⟨cs.get i,List.get_mem _ _,hy⟩
      · cases hy
  have closed : IsClosed ((Subtype.val : T → Fin (d+k) → ℝ) ⁻¹' S) := by
    rw [restrict]
    apply isClosed_iUnion_of_finite
    intro i
    split
    · rename_i e
      let u := cs.get i
      have sub : u.carrier ⊆ S := fun y hy =>
        (Prenex.regions_correct model f y).mpr ⟨u, List.get_mem _ _,hy⟩
      have du := cell_dimension_bound bound u sub
      have prefix_eq : prefixCode d k u.code = b.code := e
      have lower := prefix_dimension d k u.code
      rw [prefix_eq,db] at lower
      have eq : u.code.dimension = (prefixCode d k u.code).dimension := by
        rw [prefix_eq,db]
        omega
      have hc := relative_closed_tail model d k u.code u.layers eq
      rw [prefix_eq] at hc
      exact hc
    · exact isClosed_empty
  have hz : z ∈ (Subtype.val : T → Fin (d+k) → ℝ) ⁻¹' closure S := hc
  rw [oT.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
    continuous_subtype_val,closed.closure_eq] at hz
  exact (hs hz).elim

theorem boundary_thin (model : RealModel K) (d : ℕ) (f : Prenex K n)
    (bound : ThinAt (d+1) {x | f.holds model x}) :
    ThinAt d (closure {x | f.holds model x} \ {x | f.holds model x}) := by
  intro e
  let k := n-d
  let p := extendProjection e
  let h := coordinateOrder p
  let S := {x | f.holds model x}
  let g := f.rename p.symm
  have eq : {x | g.holds model x} = h '' S := by
    ext x
    rw [mem_ofPred_eq,Prenex.rename_correct,← Homeomorph.preimage_symm]
    rfl
  have same : ThinAt (d+1) {x | g.holds model x} := by
    rw [eq]
    intro i
    rw [image_image]
    exact bound (i.trans p.toEmbedding)
  have thin := prefix_boundary_thin model d k g same
  rw [eq, ← h.image_closure, ← image_sdiff h.injective, image_image] at thin
  have he : prefixPoint d k ∘ h = FreeChart.project e := by
    funext x i
    change x (p (Fin.castAdd k i)) = x (e i)
    rw [extendProjection_prefix]
  change IsNowhereDense ((prefixPoint d k ∘ h) '' (closure S \ S)) at thin
  rwa [he] at thin

end CertifiedTopology.CADDecision
