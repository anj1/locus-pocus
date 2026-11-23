module

public import CertifiedTopology.Plane

@[expose] public section

namespace CertifiedTopology.Plane

open Set Polynomial

abbrev Band (s : Slice ℝ) := strip s × ℝ

/-- A planar lifting certificate on one horizontal cell. The homeomorphism
    identifies the stack with fixed horizontal levels. For each requested
    polynomial, only its zeros on those model cells need to be certified. -/
structure Chart (ps : List (BiPoly ℝ)) (s : Slice ℝ) where
  normalize : Band s ≃ₜ Band s
  preservesBase : ∀ p, (normalize p).1 = p.1
  model : List (Polynomial ℝ)
  zeroStable : ∀ f ∈ ps, ∃ g ∈ model, ∀ p : Band s,
    value f (p.1.val, p.2) = 0 ↔ g.eval (normalize p).2 = 0

def Band.inPlane {s : Slice ℝ} (p : Band s) : ℝ × ℝ := (p.1.val, p.2)

def Chart.region {ps : List (BiPoly ℝ)} {s : Slice ℝ} (d : Chart ps s)
    (t : Slice ℝ) : Set (ℝ × ℝ) := {p | ∃ hp : p.1 ∈ strip s,
      (d.normalize (⟨p.1,hp⟩, p.2)).2 ∈ strip t}

theorem Chart.region_projection {ps : List (BiPoly ℝ)} {s : Slice ℝ} (d : Chart ps s)
    {t : Slice ℝ} (ht : (strip t).Nonempty) (x : ℝ) :
    (∃ y, (x,y) ∈ d.region t) ↔ x ∈ strip s := by
  constructor
  · rintro ⟨y, hx, _⟩
    exact hx
  · intro hx
    obtain ⟨y, hy⟩ := ht
    let p : Band s := (⟨x,hx⟩,y)
    let z := d.normalize.symm p
    have h : d.normalize z = p := d.normalize.apply_symm_apply p
    have eq : z.1 = p.1 := (d.preservesBase z).symm.trans (congrArg Prod.fst h)
    refine ⟨z.2, hx, ?_⟩
    have ez : (⟨x,hx⟩, z.2) = z := Prod.ext eq.symm rfl
    rw [ez, h]
    exact hy

noncomputable def Chart.regionHomeomorph {ps : List (BiPoly ℝ)} {s : Slice ℝ}
    (d : Chart ps s) (t : Slice ℝ) : d.region t ≃ₜ strip s × strip t where
  toFun := fun ⟨p, hp⟩ =>
    let v := d.normalize (⟨p.1, hp.choose⟩, p.2)
    (v.1, ⟨v.2, hp.choose_spec⟩)
  invFun := fun p =>
    let v := d.normalize.symm (p.1, p.2.val)
    ⟨v.inPlane, v.1.property, by
      change (d.normalize (d.normalize.symm (p.1, p.2.val))).2 ∈ strip t
      rw [d.normalize.apply_symm_apply]
      exact p.2.property⟩
  left_inv := by
    rintro ⟨p, hp⟩
    apply Subtype.ext
    change (d.normalize.symm (d.normalize (⟨p.1,hp.choose⟩,p.2))).inPlane = p
    rw [d.normalize.symm_apply_apply]
    rfl
  right_inv := by
    intro p
    apply Prod.ext
    · change (d.normalize (d.normalize.symm (p.1, p.2.val))).1 = p.1
      rw [d.normalize.apply_symm_apply]
    · apply Subtype.ext
      change (d.normalize (d.normalize.symm (p.1,p.2.val))).2 = p.2.val
      rw [d.normalize.apply_symm_apply]
  continuous_toFun := by
    have h : Continuous fun p : d.region t => d.normalize (⟨p.1.1,p.2.choose⟩,p.1.2) :=
      d.normalize.continuous.comp
        ((continuous_fst.comp continuous_subtype_val).subtype_mk _ |>.prodMk
          (continuous_snd.comp continuous_subtype_val))
    exact h.fst.prodMk (h.snd.subtype_mk _)
  continuous_invFun := by
    have h : Continuous fun p : strip s × strip t =>
        d.normalize.symm (p.1,p.2.val) :=
      d.normalize.symm.continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
    exact ((continuous_subtype_val.comp h.fst).prodMk h.snd).subtype_mk _

noncomputable def Chart.cellWithCuts {ps : List (BiPoly ℝ)} {s : Slice ℝ} (d : Chart ps s)
    (hs : Slice.sample (n := 0) () s ∈ strip s) {t : Slice ℝ}
    {ys : Univariate.CutTable d.model} (ht : t ∈ ys.cells) : Cell :=
  let x : strip s := ⟨_, hs⟩
  let y : strip t := ⟨_, ys.sample_mem ht⟩
  let e := d.regionHomeomorph t
  { carrier := d.region t
    sample := (e.symm (x,y)).val
    sample_mem := (e.symm (x,y)).property
    contractible := by
      let := (convex_strip s).contractibleSpace ⟨x.val, x.property⟩
      let := (convex_strip t).contractibleSpace ⟨y.val, y.property⟩
      exact e.contractibleSpace }

private theorem same_sign_of_zero {α : Type} [TopologicalSpace α] [PreconnectedSpace α]
    {f : α → ℝ} (hc : Continuous f) (p q : α) (hz : ∀ x, f x = 0 ↔ f q = 0) :
    side (f p) 0 = side (f q) 0 := by
  by_cases hq : f q = 0
  · rw [(hz p).2 hq, hq]
  have nozero : (0 : ℝ) ∉ range f := by
    rintro ⟨x, hx⟩
    exact hq ((hz x).1 hx)
  have ord := isPreconnected_iff_ordConnected.mp
    (isPreconnected_range hc : IsPreconnected (range f))
  have interval := ord.out (mem_range_self p) (mem_range_self q)
  have interval' := ord.out (mem_range_self q) (mem_range_self p)
  have hp : f p ≠ 0 := fun h => hq ((hz p).1 h)
  rcases lt_or_gt_of_ne hp with hp' | hp' <;> rcases lt_or_gt_of_ne hq with hq' | hq'
  · simp [side, hp', hq']
  · exact (nozero (interval ⟨hp'.le, hq'.le⟩)).elim
  · exact (nozero (interval' ⟨hq'.le, hp'.le⟩)).elim
  · simp [side, hp'.not_gt, hq'.not_gt, hp, hq]

theorem Chart.cellWithCuts_invariant {ps : List (BiPoly ℝ)} {s : Slice ℝ} (d : Chart ps s)
    (hs : Slice.sample (n := 0) () s ∈ strip s) {t : Slice ℝ}
    {ys : Univariate.CutTable d.model} (ht : t ∈ ys.cells)
    (p : ℝ × ℝ) (hp : p ∈ (d.cellWithCuts hs ht).carrier) {f : BiPoly ℝ} (hf : f ∈ ps) :
    side (value f p) 0 = side (value f (d.cellWithCuts hs ht).sample) 0 := by
  let c := d.cellWithCuts hs ht
  obtain ⟨g, hg, he⟩ := d.zeroStable f hf
  let := c.contractible
  let F : c.carrier → ℝ := fun x => value f x.val
  have hF : Continuous F := (continuous_value f).comp continuous_subtype_val
  change side (F ⟨p,hp⟩) 0 = side (F ⟨c.sample,c.sample_mem⟩) 0
  apply same_sign_of_zero hF
  intro x
  have hz (x : c.carrier) : F x = 0 ↔ g.eval (d.regionHomeomorph t x).2.val = 0 :=
    he (⟨x.val.1,x.property.choose⟩,x.val.2)
  rw [hz, hz]
  exact (side_congr (ys.invariant ht (d.regionHomeomorph t x).2.property
    (d.regionHomeomorph t ⟨c.sample,c.sample_mem⟩).2.property hg)).2.1

noncomputable def Chart.cell {ps : List (BiPoly ℝ)} {s : Slice ℝ} (d : Chart ps s)
    (hs : s.sample (n := 0) () ∈ strip s) {t : Slice ℝ}
    (ht : t ∈ Univariate.decompose d.model) : Cell :=
  d.cellWithCuts hs (ys := Univariate.CutTable.fromPolynomials d.model) ht

theorem Chart.cell_invariant {ps : List (BiPoly ℝ)} {s : Slice ℝ} (d : Chart ps s)
    (hs : s.sample (n := 0) () ∈ strip s) {t : Slice ℝ}
    (ht : t ∈ Univariate.decompose d.model) (p : ℝ × ℝ) (hp : p ∈ (d.cell hs ht).carrier)
    {f : BiPoly ℝ} (hf : f ∈ ps) :
    side (value f p) 0 = side (value f (d.cell hs ht).sample) 0 :=
  d.cellWithCuts_invariant hs (ys := Univariate.CutTable.fromPolynomials d.model) ht p hp hf

/-- The chart and a checked root table for its one-variable model. -/
structure CheckedChart (ps : List (BiPoly ℝ)) (s : Slice ℝ) where
  chart : Chart ps s
  cuts : Univariate.CutTable chart.model

theorem Chart.cell_sample_of_fixed {ps : List (BiPoly ℝ)} {s t : Slice ℝ} (d : Chart ps s)
    (hs : (s.sample (n := 0) ()) ∈ strip s)
    {ys : Univariate.CutTable d.model} (ht : t ∈ ys.cells)
    (hf : ∀ y, d.normalize (⟨s.sample (n := 0) (), hs⟩, y) =
      (⟨s.sample (n := 0) (), hs⟩, y)) :
    (d.cellWithCuts hs ht).sample = (s.sample (n := 0) (), t.sample (n := 0) ()) := by
  let p : Band s := (⟨s.sample (n := 0) (), hs⟩, t.sample (n := 0) ())
  change (d.normalize.symm p).inPlane = p.inPlane
  have he : d.normalize p = p := hf p.2
  conv_lhs => rw [← he, d.normalize.symm_apply_apply]

noncomputable def checkedChartCells {xs : List (Polynomial ℝ)} (base : Univariate.CutTable xs)
    {ps : List (BiPoly ℝ)} (charts : ∀ s ∈ base.cells, CheckedChart ps s) : List Cell :=
  base.cells.attach.flatMap fun s =>
    let d := charts s.val s.property
    d.cuts.cells.attach.map fun t => d.chart.cellWithCuts (base.sample_mem s.property) t.property

theorem mem_checkedChartCells {xs : List (Polynomial ℝ)} (base : Univariate.CutTable xs)
    {ps : List (BiPoly ℝ)} (charts : ∀ s ∈ base.cells, CheckedChart ps s) {c : Cell} :
    c ∈ checkedChartCells base charts ↔
      ∃ (s : Slice ℝ) (hs : s ∈ base.cells)
        (t : Slice ℝ) (ht : t ∈ (charts s hs).cuts.cells),
        c = (charts s hs).chart.cellWithCuts (base.sample_mem hs) ht := by
  simp [checkedChartCells, List.mem_flatMap, eq_comm]

/-- Lift one checked stack on each checked base cell. -/
noncomputable def ofCheckedCharts {xs : List (Polynomial ℝ)} (base : Univariate.CutTable xs)
    {ps : List (BiPoly ℝ)} (charts : ∀ s ∈ base.cells, CheckedChart ps s) : Diagram ps where
  cells := checkedChartCells base charts
  partition := by
    intro p
    obtain ⟨s, ⟨hs, hx⟩, unique⟩ := base.partition p.1
    let d := charts s hs
    let y := (d.chart.normalize (⟨p.1, hx⟩, p.2)).2
    obtain ⟨t, ⟨ht, hy⟩, unique'⟩ := d.cuts.partition y
    refine ⟨d.chart.cellWithCuts (base.sample_mem hs) ht,
      ⟨(mem_checkedChartCells base charts).mpr ⟨s,hs,t,ht,rfl⟩, ⟨hx,hy⟩⟩, ?_⟩
    rintro c ⟨hc, hpc⟩
    obtain ⟨s',hs',t',ht',rfl⟩ := (mem_checkedChartCells base charts).mp hc
    obtain ⟨hx',hy'⟩ := hpc
    have eq := unique s' ⟨hs',hx'⟩
    subst s'
    have eq' := unique' t' ⟨ht', hy'⟩
    subst t'
    rfl
  invariant := by
    intro c hc p hp f hf
    obtain ⟨s,hs,t,ht,rfl⟩ := (mem_checkedChartCells base charts).mp hc
    exact (charts s hs).chart.cellWithCuts_invariant _ ht p hp hf

theorem ofCheckedCharts_cell_model {xs : List (Polynomial ℝ)} {base : Univariate.CutTable xs}
    {ps : List (BiPoly ℝ)} (charts : ∀ s ∈ base.cells, CheckedChart ps s)
    {c : Cell} (hc : c ∈ (ofCheckedCharts base charts).cells) :
    ∃ s ∈ base.cells, ∃ t : Slice ℝ,
      Nonempty (c.carrier ≃ₜ strip s × strip t) ∧ Prod.fst '' c.carrier = strip s := by
  obtain ⟨s,hs,t,ht,rfl⟩ := (mem_checkedChartCells base charts).mp hc
  let d := charts s hs
  have nonempty : (strip t).Nonempty := ⟨_, d.cuts.sample_mem ht⟩
  refine ⟨s,hs,t,⟨d.chart.regionHomeomorph t⟩,?_⟩
  ext x
  change x ∈ Prod.fst '' d.chart.region t ↔ x ∈ strip s
  constructor
  · rintro ⟨⟨_, y⟩, hp, rfl⟩
    exact (d.chart.region_projection nonempty _).1 ⟨y,hp⟩
  · intro hx
    obtain ⟨y,hy⟩ := (d.chart.region_projection nonempty x).2 hx
    exact ⟨(x,y),hy,rfl⟩

theorem ofCheckedCharts_cylindrical {xs : List (Polynomial ℝ)} {base : Univariate.CutTable xs}
    {ps : List (BiPoly ℝ)} (charts : ∀ s ∈ base.cells, CheckedChart ps s)
    {c d : Cell} (hc : c ∈ (ofCheckedCharts base charts).cells)
    (hd : d ∈ (ofCheckedCharts base charts).cells) :
    Prod.fst '' c.carrier = Prod.fst '' d.carrier ∨
      Disjoint (Prod.fst '' c.carrier) (Prod.fst '' d.carrier) := by
  obtain ⟨s,hs,_,_,he⟩ := ofCheckedCharts_cell_model charts hc
  obtain ⟨t,ht,_,_,hf⟩ := ofCheckedCharts_cell_model charts hd
  rw [he,hf]
  by_cases h : s = t
  · exact Or.inl (congrArg strip h)
  · refine Or.inr (Set.disjoint_left.mpr fun x hx hy => ?_)
    obtain ⟨_,_,unique⟩ := base.partition x
    exact h ((unique s ⟨hs,hx⟩).trans (unique t ⟨ht,hy⟩).symm)

/-- Construct a planar CAD using the mathematical univariate root source. -/
noncomputable def ofCharts (xs : List (Polynomial ℝ)) (ps : List (BiPoly ℝ))
    (charts : ∀ s ∈ Univariate.decompose xs, Chart ps s) : Diagram ps :=
  ofCheckedCharts (Univariate.CutTable.fromPolynomials xs) fun s hs =>
    let d := charts s hs
    ⟨d, Univariate.CutTable.fromPolynomials d.model⟩

noncomputable def chartCells (xs : List (Polynomial ℝ)) (ps : List (BiPoly ℝ))
    (charts : ∀ s ∈ Univariate.decompose xs, Chart ps s) : List Cell :=
  (ofCharts xs ps charts).cells

theorem ofCharts_cell_model {xs : List (Polynomial ℝ)} {ps : List (BiPoly ℝ)}
    (charts : ∀ s ∈ Univariate.decompose xs, Chart ps s)
    {c : Cell} (hc : c ∈ (ofCharts xs ps charts).cells) :
    ∃ s ∈ Univariate.decompose xs, ∃ t : Slice ℝ,
      Nonempty (c.carrier ≃ₜ strip s × strip t) ∧ Prod.fst '' c.carrier = strip s :=
  ofCheckedCharts_cell_model _ hc

theorem ofCharts_cylindrical {xs : List (Polynomial ℝ)} {ps : List (BiPoly ℝ)}
    (charts : ∀ s ∈ Univariate.decompose xs, Chart ps s)
    {c d : Cell} (hc : c ∈ (ofCharts xs ps charts).cells)
    (hd : d ∈ (ofCharts xs ps charts).cells) :
    Prod.fst '' c.carrier = Prod.fst '' d.carrier ∨
      Disjoint (Prod.fst '' c.carrier) (Prod.fst '' d.carrier) :=
  ofCheckedCharts_cylindrical _ hc hd

/-- At a critical base coordinate, specialize directly before isolating roots.
    This also handles a polynomial that vanishes on the entire vertical line. -/
noncomputable def pointChart (ps : List (BiPoly ℝ)) (x : ℝ) : Chart ps (.sectionAt x) where
  normalize := Homeomorph.refl _
  preservesBase := fun _ => rfl
  model := ps.map (specialize x)
  zeroStable := by
    intro f hf
    refine ⟨specialize x f, List.mem_map_of_mem hf, ?_⟩
    intro p
    have h : p.1.val = x := p.1.property
    change value f (p.1.val, p.2) = 0 ↔ (specialize x f).eval p.2 = 0
    rw [h]
    rfl

/-- Only the open base intervals require a delineation certificate. Isolated
    critical coordinates are lifted by direct specialization. -/
noncomputable def ofOpenCharts (xs : List (Polynomial ℝ)) (ps : List (BiPoly ℝ))
    (charts : ∀ (l u : Option ℝ), Slice.sector l u ∈ Univariate.decompose xs →
      Chart ps (.sector l u)) : Diagram ps :=
  ofCharts xs ps fun s hs => match s with
    | .sectionAt x => pointChart ps x
    | .sector l u => charts l u hs

end CertifiedTopology.Plane
