module

public import CertifiedTopology.CADModels

@[expose] public section

namespace CertifiedTopology.CADStacks

open Set Topology

variable {n m d : ℕ} {A : Set (Fin n → ℝ)}

/-- A cell projects homeomorphically onto an open set of its free coordinates. -/
structure FreeChart (A : Set (Fin n → ℝ)) (d : ℕ) where
  indices : Fin d ↪ Fin n
  domain : Set (Fin d → ℝ)
  open_domain : IsOpen domain
  chart : A ≃ₜ domain
  correct : ∀ a : A, (chart a).val = a.val ∘ indices

namespace FreeChart

noncomputable def origin : FreeChart (univ : Set (Fin 0 → ℝ)) 0 :=
  ⟨Function.Embedding.refl _, univ, isOpen_univ, Homeomorph.refl _, fun _ => rfl⟩

noncomputable def sectionChart (F : FreeChart A d) (c : Fin m → A → ℝ) (j : Fin m)
    (h : Continuous (c j)) : FreeChart (region c (.sectionAt j)) d where
  indices := F.indices.trans ⟨Fin.castSucc,Fin.castSucc_injective _⟩
  domain := F.domain
  open_domain := F.open_domain
  chart := (sectionModel c j h).trans F.chart
  correct x := F.correct (regionBase c (.sectionAt j) x)

def sectorIndex (f : Fin d ↪ Fin n) : Fin (d+1) ↪ Fin (n+1) where
  toFun := Fin.lastCases (Fin.last n) (Fin.castSucc ∘ f)
  inj' := by
    intro i j
    cases i using Fin.lastCases <;> cases j using Fin.lastCases <;>
      simp [Function.comp_def, Fin.castSucc_inj, f.injective.eq_iff]
    intro h
    exact (Fin.castSucc_ne_last _ h.symm).elim

theorem dropLast_snoc (x : Fin n → ℝ) (z : ℝ) : dropLast (Fin.snoc x z) = x := by
  funext i
  exact @Fin.snoc_castSucc n (fun _ => ℝ) z x i

theorem last_snoc (x : Fin n → ℝ) (z : ℝ) : last (Fin.snoc x z) = z :=
  @Fin.snoc_last n (fun _ => ℝ) z x

theorem region_open {c : Fin m → A → ℝ} (hA : IsOpen A) (l u : Option (Fin m))
    (hc : ∀ i, Continuous (c i)) : IsOpen (region c (.sector l u)) := by
  let T := dropLast ⁻¹' A
  have openT : IsOpen T := hA.preimage (continuous_pi fun i => continuous_apply i.castSucc)
  let proj (x : T) : A := ⟨dropLast x.val,x.property⟩
  have cont : Continuous proj := (continuous_pi (fun i =>
    (continuous_apply i.castSucc).comp continuous_subtype_val)).subtype_mk _
  let endpt (i : Fin m) (x : T) := c i (proj x)
  let vert (x : T) := last x.val
  have v : Continuous vert := (continuous_apply _).comp continuous_subtype_val
  have h (i : Fin m) : Continuous (endpt i) := (hc i).comp cont
  let B := {x : T | Univariate.contains (mapSlice (fun i => endpt i x) (.sector l u)) (vert x)}
  have eq : region c (.sector l u) = Subtype.val '' B := by
    ext x
    constructor
    · rintro ⟨hx,hs⟩
      exact ⟨⟨x,hx⟩,hs,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨y.property,hy⟩
  rw [eq]
  apply openT.isOpenEmbedding_subtypeVal.isOpenMap
  cases l with
  | none =>
    cases u with
    | none =>
      have E : B = univ := by ext x; simp [B,mapSlice,Univariate.contains,Slice.Contains]
      rw [E]; exact isOpen_univ
    | some u =>
      have E : B = {x | vert x < endpt u x} := by
        ext x; simp [B,mapSlice,Univariate.contains,Slice.Contains,Aff.eval]
      rw [E]; exact isOpen_lt v (h u)
  | some l =>
    cases u with
    | none =>
      have E : B = {x | endpt l x < vert x} := by
        ext x; simp [B,mapSlice,Univariate.contains,Slice.Contains,Aff.eval]
      rw [E]; exact isOpen_lt (h l) v
    | some u =>
      have E : B = {x | endpt l x < vert x} ∩ {x | vert x < endpt u x} := by
        ext x; simp [B,mapSlice,Univariate.contains,Slice.Contains,Aff.eval]
      rw [E]; exact (isOpen_lt (h l) v).inter (isOpen_lt v (h u))

noncomputable def transferRegion (F : FreeChart A d) (c : Fin m → A → ℝ) (s : Slice (Fin m)) :
    region c s ≃ₜ region (fun i => c i ∘ F.chart.symm) s where
  toFun x :=
    let base := regionBase c s x
    ⟨Fin.snoc (F.chart base).val (last x.val),
      (region_snoc _ _ _ _).mpr ⟨(F.chart base).property, by
        simp only [Function.comp_apply, F.chart.symm_apply_apply]
        exact x.property.choose_spec⟩⟩
  invFun x :=
    let base := regionBase (fun i => c i ∘ F.chart.symm) s x
    ⟨Fin.snoc (F.chart.symm base).val (last x.val),
      (region_snoc _ _ _ _).mpr ⟨(F.chart.symm base).property,x.property.choose_spec⟩⟩
  left_inv x := by
    let a := regionBase c s x
    let b := F.chart a
    have hb : regionBase (fun i => c i ∘ F.chart.symm) s
        ⟨Fin.snoc b.val (last x.val), by exact (region_snoc _ _ _ _).mpr ⟨b.property, by
          change Univariate.contains (mapSlice (fun i => c i (F.chart.symm (F.chart a))) s) (last x.val)
          rw [F.chart.symm_apply_apply]; exact x.property.choose_spec⟩⟩ = b :=
      Subtype.ext (dropLast_snoc _ _)
    apply Subtype.ext
    change Fin.snoc (F.chart.symm _).val _ = x.val
    rw [hb,F.chart.symm_apply_apply,last_snoc]
    exact snoc_dropLast _
  right_inv x := by
    let b := regionBase (fun i => c i ∘ F.chart.symm) s x
    let a := F.chart.symm b
    have ha : regionBase c s ⟨Fin.snoc a.val (last x.val),
        (region_snoc _ _ _ _).mpr ⟨a.property,x.property.choose_spec⟩⟩ = a :=
      Subtype.ext (dropLast_snoc _ _)
    apply Subtype.ext
    change Fin.snoc (F.chart _).val _ = x.val
    rw [ha,F.chart.apply_symm_apply,last_snoc]
    exact snoc_dropLast _
  continuous_toFun :=
    (continuous_snoc ((continuous_subtype_val.comp F.chart.continuous_toFun).comp (regionBase_continuous c s))
      ((continuous_apply _).comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    (continuous_snoc ((continuous_subtype_val.comp F.chart.symm.continuous_toFun).comp
      (regionBase_continuous _ s)) ((continuous_apply _).comp continuous_subtype_val)).subtype_mk _

noncomputable def sector (F : FreeChart A d) (c : Fin m → A → ℝ) (l u : Option (Fin m))
    (hc : ∀ i, Continuous (c i)) : FreeChart (region c (.sector l u)) (d+1) where
  indices := sectorIndex F.indices
  domain := region (fun i => c i ∘ F.chart.symm) (.sector l u)
  open_domain := region_open F.open_domain l u (fun i => (hc i).comp F.chart.symm.continuous_toFun)
  chart := transferRegion F c (.sector l u)
  correct x := by
    funext i
    cases i using Fin.lastCases with
    | last =>
      change @Fin.snoc d (fun _ => ℝ) (F.chart (regionBase c _ x)).val (last x.val) (Fin.last d) =
        x.val (sectorIndex F.indices (Fin.last d))
      simp [sectorIndex,last]
    | cast i =>
      change @Fin.snoc d (fun _ => ℝ) (F.chart (regionBase c _ x)).val (last x.val) i.castSucc =
        x.val (sectorIndex F.indices i.castSucc)
      simp only [Fin.snoc_castSucc,sectorIndex,Function.Embedding.coeFn_mk,Fin.lastCases_castSucc,Function.comp_apply]
      exact congrFun (F.correct _) i

theorem image_eq (F : FreeChart A d) : (fun x : Fin n → ℝ => x ∘ F.indices) '' A = F.domain := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    change x ∘ F.indices ∈ F.domain
    rw [← F.correct ⟨x,hx⟩]
    exact (F.chart ⟨x,hx⟩).property
  · intro hy
    let x := F.chart.symm ⟨y,hy⟩
    exact ⟨x.val,x.property,(F.correct x).symm.trans
      (congrArg Subtype.val (F.chart.apply_symm_apply ⟨y,hy⟩))⟩

def project (e : Fin d ↪ Fin n) (x : Fin n → ℝ) : Fin d → ℝ := x ∘ e

theorem project_continuous (e : Fin d ↪ Fin n) : Continuous (project e) :=
  continuous_pi fun i => continuous_apply (e i)

theorem full_open (F : FreeChart A n) : IsOpen A := by
  have surj := Finite.injective_iff_surjective.mp F.indices.injective
  have inj : Function.Injective (project F.indices) := by
    intro x y e
    funext i
    obtain ⟨j,rfl⟩ := surj i
    exact congrFun e j
  have eq : A = project F.indices ⁻¹' F.domain := by
    ext x
    change x ∈ A ↔ project F.indices x ∈ F.domain
    rw [← F.image_eq]
    exact ⟨fun h => ⟨x,h,rfl⟩,fun ⟨y,hy,e⟩ => inj e ▸ hy⟩
  rw [eq]
  exact F.open_domain.preimage (project_continuous _)

theorem closedOverDomain (F : FreeChart A d) :
    IsClosed ((Subtype.val : (project F.indices ⁻¹' F.domain) → (Fin n → ℝ)) ⁻¹' A) := by
  let T := project F.indices ⁻¹' F.domain
  let down (x : T) : F.domain := ⟨project F.indices x.val,x.property⟩
  have cd : Continuous down :=
    ((project_continuous _).comp (continuous_subtype_val (p := fun x => x ∈ T))).subtype_mk _
  have eq : ((Subtype.val : T → Fin n → ℝ) ⁻¹' A) =
      {x | (F.chart.symm (down x)).val = x.val} := by
    ext x
    change x.val ∈ A ↔ (F.chart.symm (down x)).val = x.val
    constructor
    · intro hx
      have e : down x = F.chart ⟨x.val,hx⟩ := by
        apply Subtype.ext
        exact (F.correct ⟨x.val,hx⟩).symm
      rw [e,F.chart.symm_apply_apply]
    · intro h
      rw [← h]
      exact (F.chart.symm (down x)).property
  rw [eq]
  exact isClosed_eq (continuous_subtype_val.comp (F.chart.symm.continuous_toFun.comp cd))
    continuous_subtype_val

theorem closure_on_domain (F : FreeChart A d) {x : Fin n → ℝ} (hx : x ∈ closure A)
    (hp : project F.indices x ∈ F.domain) : x ∈ A := by
  let T := project F.indices ⁻¹' F.domain
  have hT : IsOpen T := F.open_domain.preimage (project_continuous _)
  let q : T := ⟨x,hp⟩
  have hs : q ∈ (Subtype.val : T → Fin n → ℝ) ⁻¹' closure A := hx
  rw [hT.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
    continuous_subtype_val, F.closedOverDomain.closure_eq] at hs
  exact hs

theorem thin (F : FreeChart A d) (hd : d < n) : interior (closure A) = ∅ := by
  classical
  have out : ∃ j : Fin n, j ∉ range F.indices := by
    by_contra! h
    have surj : Function.Surjective F.indices := fun j => h j
    have e := Fintype.card_congr (Equiv.ofBijective F.indices ⟨F.indices.injective,surj⟩)
    simp only [Fintype.card_fin] at e
    omega
  obtain ⟨j,hj⟩ := out
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  let U := interior (closure A)
  obtain ⟨ε,he,sub⟩ := Metric.isOpen_iff.mp (isOpen_interior : IsOpen U) x hx
  obtain ⟨a,ha,hdist⟩ := Metric.mem_closure_iff.mp (interior_subset hx) ε he
  have au : a ∈ U := sub (Metric.mem_ball.mpr (by rwa [dist_comm]))
  let T := project F.indices ⁻¹' F.domain
  have hT : IsOpen T := F.open_domain.preimage (project_continuous _)
  let line (t : ℝ) := Function.update a j t
  have cline : Continuous line := by
    apply continuous_pi
    intro i
    by_cases e : i = j
    · subst i
      simp only [line,Function.update_self]
      exact continuous_id
    · simpa [line,Function.update_of_ne e] using (continuous_const : Continuous fun _ : ℝ => a i)
  have pv (t : ℝ) : project F.indices (line t) = project F.indices a := by
    funext i
    exact Function.update_of_ne (fun e => hj ⟨i,e⟩) _ _
  have aT : a ∈ T := by
    change a ∘ F.indices ∈ F.domain
    rw [← F.correct ⟨a,ha⟩]
    exact (F.chart ⟨a,ha⟩).property
  have center_mem : a j ∈ line ⁻¹' (U ∩ T) := by
    change line (a j) ∈ U ∩ T
    simpa [line] using (show a ∈ U ∩ T from ⟨au,aT⟩)
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp ((isOpen_interior.inter hT).preimage cline) _ center_mem
  let t := a j + δ/2
  have ht : t ∈ Metric.ball (a j) δ := by
    rw [Metric.mem_ball,Real.dist_eq]
    simpa [t,abs_of_pos (half_pos hδ)] using half_lt_self hδ
  have hline : line t ∈ U ∩ T := hball ht
  have hy : line t ∈ A := F.closure_on_domain (interior_subset hline.1) hline.2
  have e : F.chart ⟨line t,hy⟩ = F.chart ⟨a,ha⟩ := by
    apply Subtype.ext
    rw [F.correct ⟨line t,hy⟩, F.correct ⟨a,ha⟩]
    exact pv t
  have heq := congrArg (fun y : A => y.val j) (F.chart.injective e)
  have eq : t = a j := by simpa [line] using heq
  dsimp [t] at eq
  linarith

end FreeChart

end CertifiedTopology.CADStacks
