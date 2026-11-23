module

public import CertifiedTopology.PlaneProjection
public import CertifiedTopology.PlaneRoots
public import CertifiedTopology.PlaneNormalize

@[expose] public section

namespace CertifiedTopology.Plane

open Polynomial Set Filter
open scoped Topology

private theorem specialize_coeff (q : BiPoly ℝ) (x : ℝ) (i : ℕ) :
    (specialize x q).coeff i = (q.coeff i).eval x := by
  exact coeff_map _ _

theorem specialize_leading {q : BiPoly ℝ} {x : ℝ} (h : q.leadingCoeff.eval x ≠ 0) :
    (specialize x q).leadingCoeff = q.leadingCoeff.eval x :=
  leadingCoeff_map_of_leadingCoeff_ne_zero (evalRingHom x) h

private theorem specialize_derivative (q : BiPoly ℝ) (x : ℝ) :
    (specialize x q).derivative = specialize x q.derivative :=
  derivative_map _ _

theorem locally_bounded_specialize (q : BiPoly ℝ) {A : Set ℝ}
    (hl : ∀ x : A, q.leadingCoeff.eval x.val ≠ 0) (x : A) :
    ∃ M : ℝ, ∀ᶠ u in 𝓝 x, ∀ y, (specialize u.val q).eval y = 0 → y ∈ Icc (-M) M := by
  open scoped NNReal in
    have cb : Continuous (fun x : A => (specialize x.val q).cauchyBound) := by
      have eq : (fun x : A => (specialize x.val q).cauchyBound) =
          fun x => (Finset.range q.natDegree).sup (fun i => ‖(q.coeff i).eval x.val‖₊) /
            ‖q.leadingCoeff.eval x.val‖₊ + 1 := by
        funext x
        simp only [cauchyBound, specialize_degree (hl x), specialize_coeff, specialize_leading (hl x)]
      rw [eq]
      have hn (f : Polynomial ℝ) : Continuous (fun x : A => ‖f.eval x.val‖₊) :=
        (f.continuous.comp continuous_subtype_val).nnNorm
      have hsup : Continuous (fun x : A =>
          (Finset.range q.natDegree).sup (fun i => ‖(q.coeff i).eval x.val‖₊)) :=
        Continuous.finset_sup_apply (fun i _ => hn (q.coeff i))
      exact (hsup.div₀ (hn q.leadingCoeff) (fun x => by simpa using hl x)).add continuous_const
  let M := ((specialize x.val q).cauchyBound : ℝ) + 1
  have hM : ((specialize x.val q).cauchyBound : ℝ) < M := by dsimp [M]; linarith
  have ev : ∀ᶠ u in 𝓝 x, ((specialize u.val q).cauchyBound : ℝ) < M :=
    (isOpen_lt (NNReal.continuous_coe.comp cb) continuous_const).mem_nhds hM
  refine ⟨M,ev.mono fun u hu y hy => ?_⟩
  have nz := leadingCoeff_ne_zero.mp ((specialize_leading (hl u)).trans_ne (hl u))
  have hb := IsRoot.norm_lt_cauchyBound nz (show (specialize u.val q).IsRoot y from hy)
  have hh : |y| < M := by
    have hnorm : ‖y‖ < ((specialize u.val q).cauchyBound : ℝ) := hb
    exact (Real.norm_eq_abs y ▸ hnorm).trans hu
  exact ⟨(abs_lt.mp hh).1.le,(abs_lt.mp hh).2.le⟩

/-- Specialization gives a family of simple roots wherever the leading
    coefficient and the derivative resultant are nonzero. -/
noncomputable def specializedFamily (q : BiPoly ℝ) (A : Set ℝ)
    (hl : ∀ x : A, q.leadingCoeff.eval x.val ≠ 0)
    (hr : ∀ (x : A) y, value q (x.val,y) = 0 → value q.derivative (x.val,y) ≠ 0) :
    RootFamily A where
  poly x := specialize x.val q
  nonzero x := leadingCoeff_ne_zero.mp ((specialize_leading (hl x)).trans_ne (hl x))
  eval_continuous :=
    (continuous_value q).comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  derivative_continuous := by
    simp only [specialize_derivative]
    exact (continuous_value q.derivative).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  simple x y hy := by
    rw [specialize_derivative]
    exact hr x y hy
  locally_bounded := locally_bounded_specialize q hl

/-- A sector avoids the roots of every nonzero projection polynomial. -/
theorem sector_avoids {xs : List (Polynomial ℝ)} {l u : Option ℝ}
    (hs : Slice.sector l u ∈ Univariate.decompose xs) {f : Polynomial ℝ}
    (hf : f ∈ xs) (hn : f ≠ 0) (x : strip (.sector l u)) : f.eval x.val ≠ 0 :=
  (Univariate.CutTable.fromPolynomials xs).sector_avoids hs hf hn x.property

theorem factor_root_status {q d g : BiPoly ℝ} (eq : q = d*g)
    {A : Set ℝ} [PreconnectedSpace A] (r : A → ℝ) (cr : Continuous r)
    (hr : ∀ x, value q (x.val,r x) = 0)
    (hs : ∀ x, value q.derivative (x.val,r x) ≠ 0) (x y : A) :
    value d (x.val,r x) = 0 ↔ value d (y.val,r y) = 0 := by
  let dval (u : A) := value d (u.val,r u)
  let gval (u : A) := value g (u.val,r u)
  have cd : Continuous dval := (continuous_value d).comp (continuous_subtype_val.prodMk cr)
  have cg : Continuous gval := (continuous_value g).comp (continuous_subtype_val.prodMk cr)
  have H (u : A) : dval u = 0 ↔ gval u ≠ 0 := by
    constructor
    · intro hd hg
      apply hs u
      rw [eq, derivative_mul, value_add, value_mul, value_mul]
      change _ * gval u + dval u * _ = 0
      simp [hd,hg]
    · intro hg
      have h := hr u
      rw [eq, value_mul] at h
      exact (mul_eq_zero.mp h).resolve_right hg
  have hc : IsLocallyConstant (fun u => dval u = 0) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro u
    by_cases h : dval u = 0
    · filter_upwards [(isOpen_ne_fun cg continuous_const).mem_nhds ((H u).1 h)] with v hv
      exact propext ⟨fun _ => h, fun _ => (H v).2 hv⟩
    · filter_upwards [(isOpen_ne_fun cd continuous_const).mem_nhds h] with v hv
      exact propext ⟨fun e => (hv e).elim,fun e => (h e).elim⟩
  exact Iff.of_eq (hc.apply_eq_of_preconnectedSpace x y)

/-- Lift a sector by tracking the distinct roots of the squarefree product.
    Each original polynomial owns a fixed subset of those sections. -/
noncomputable def generalChartAtSample {ps : List (BiPoly ℝ)} (p : Projection ps) (s : Slice ℝ)
    (hs : Slice.sample (n := 0) () s ∈ strip s)
    (h : ∀ (x : strip s) f, f ∈ p.cuts → f.eval x.val ≠ 0) :
    {d : Chart ps s // ∀ y, d.normalize (⟨s.sample (n := 0) (), hs⟩, y) =
        (⟨s.sample (n := 0) (), hs⟩, y)} := by
  classical
  let A := strip s
  let x₀ : A := ⟨_, hs⟩
  let : ContractibleSpace A := (convex_strip s).contractibleSpace ⟨x₀.val,x₀.property⟩
  let Q := p.root
  have hl (x : A) := (p.regular x.val (h x)).1
  have hr (x : A) := (p.regular x.val (h x)).2
  let P := specializedFamily Q A hl hr
  let r := P.rootSection x₀
  have c (i) : Continuous (r i) := P.continuous_section x₀ i
  have ord (x : A) : StrictMono fun i => r i x := P.section_order x₀ x
  let E := Vertical.matchSectionsWithFixed r (fun i _ => r i x₀) c (fun _ => continuous_const) ord (fun _ => ord x₀)
  let T := E.val
  have ht : ∀ x i, T.height x (r i x) = r i x₀ := E.property.1
  refine ⟨⟨T.homeo, T.base, ps.map (specialize x₀.val), ?_⟩, ?_⟩
  swap
  · intro y
    exact Prod.ext (T.base (x₀,y)) (E.property.2 x₀ (fun _ => rfl) y)
  intro f hf
  refine ⟨specialize x₀.val f, List.mem_map_of_mem hf, ?_⟩
  rintro ⟨x,y⟩
  change value f (x.val,y) = 0 ↔ value f (x₀.val,T.height x y) = 0
  by_cases h0 : f = 0
  · simp [h0, value_hom]
  obtain ⟨d, hdq, hdf, n, hfd⟩ := p.factors f hf h0
  obtain ⟨g,hg⟩ := hdq
  have crosses (i) : value f (x.val,r i x) = 0 ↔ value f (x₀.val,r i x₀) = 0 := by
    have hh (u : A) : value Q (u.val,r i u) = 0 :=
      (P.mem_roots u _).mp (P.section_mem x₀ u i)
    have simp' (u : A) : value Q.derivative (u.val,r i u) ≠ 0 :=
      hr u _ (hh u)
    rw [← factor_value_zero hdf hfd (x.val,r i x), ← factor_value_zero hdf hfd (x₀.val,r i x₀)]
    exact factor_root_status hg (r i) (c i) hh simp' x x₀
  have root_of_input (u : A) (t : ℝ) (h : value f (u.val,t) = 0) : t ∈ P.roots u := by
    apply (P.mem_roots u t).mpr
    change value p.root (u.val,t) = 0
    rw [hg, value_mul, (factor_value_zero hdf hfd _).2 h, zero_mul]
  constructor
  · intro h
    obtain ⟨i,hi⟩ := P.exists_section x₀ x (root_of_input x y h)
    change r i x = y at hi
    rw [← hi, ht, ← crosses i, hi]
    exact h
  · intro h
    obtain ⟨i,hi⟩ := P.exists_section x₀ x₀ (root_of_input x₀ _ h)
    change r i x₀ = T.height x y at hi
    have eq : y = r i x := (T.height_injective x) (hi.symm.trans (ht x i).symm)
    rwa [eq, crosses i, hi]

noncomputable def generalChart {ps : List (BiPoly ℝ)} (p : Projection ps) (s : Slice ℝ)
    (hs : s.sample (n := 0) () ∈ strip s)
    (h : ∀ (x : strip s) f, f ∈ p.cuts → f.eval x.val ≠ 0) : Chart ps s :=
  (generalChartAtSample p s hs h).val

/-- Base cuts for the projection and vertical cuts for every sampled fiber. -/
structure LiftingData {ps : List (BiPoly ℝ)} (p : Projection ps) where
  base : Univariate.CutTable p.cuts
  fibers : ∀ s ∈ base.cells, Univariate.CutTable (ps.map (specialize (s.sample (n := 0) ())))

namespace LiftingData

variable {ps : List (BiPoly ℝ)} {p : Projection ps}

noncomputable def chart (data : LiftingData p) (s : Slice ℝ) (hs : s ∈ data.base.cells) :
    {d : CheckedChart ps s // (∀ y, d.chart.normalize (⟨_, data.base.sample_mem hs⟩, y) =
      (⟨s.sample (n := 0) (), data.base.sample_mem hs⟩, y)) ∧
      d.cuts.cells = (data.fibers s hs).cells} := by
  cases s with
  | sectionAt x =>
    exact ⟨⟨pointChart ps x, data.fibers _ hs⟩, (fun _ => rfl), rfl⟩
  | sector l u =>
    let d := generalChartAtSample p (.sector l u) (data.base.sample_mem hs) fun x f hf =>
      data.base.sector_avoids hs hf (p.nonzero f hf) x.property
    exact ⟨⟨d.val, data.fibers _ hs⟩, d.property, rfl⟩

/-- Lift directly from the supplied projection and checked root tables. -/
noncomputable def solve (data : LiftingData p) : Diagram ps :=
  ofCheckedCharts data.base fun s hs => (data.chart s hs).val

theorem sample_eq (data : LiftingData p) {c : Cell} (hc : c ∈ data.solve.cells) :
    ∃ (s : Slice ℝ) (hs : s ∈ data.base.cells), ∃ t ∈ (data.fibers s hs).cells,
      c.sample = (s.sample (n := 0) (), t.sample (n := 0) ()) := by
  obtain ⟨s, hs, t, ht, rfl⟩ := (mem_checkedChartCells data.base
    (fun s hs => (data.chart s hs).val)).mp hc
  exact ⟨s, hs, t, (data.chart s hs).property.2 ▸ ht,
    Chart.cell_sample_of_fixed _ _ ht (data.chart s hs).property.1⟩

theorem cell_model (data : LiftingData p) {c : Cell} (hc : c ∈ data.solve.cells) :
    ∃ s ∈ data.base.cells, ∃ t : Slice ℝ,
      Nonempty (c.carrier ≃ₜ strip s × strip t) ∧ Prod.fst '' c.carrier = strip s :=
  ofCheckedCharts_cell_model _ hc

theorem cylindrical (data : LiftingData p) {c d : Cell} (hc : c ∈ data.solve.cells)
    (hd : d ∈ data.solve.cells) :
    Prod.fst '' c.carrier = Prod.fst '' d.carrier ∨
      Disjoint (Prod.fst '' c.carrier) (Prod.fst '' d.carrier) :=
  ofCheckedCharts_cylindrical _ hc hd

/-- Default tables for the total mathematical solver. -/
noncomputable def fromPolynomials (p : Projection ps) : LiftingData p where
  base := Univariate.CutTable.fromPolynomials p.cuts
  fibers s _ := Univariate.CutTable.fromPolynomials (ps.map (specialize (s.sample (n := 0) ())))

end LiftingData

/-- Lift from checked projection data, with no separate topological
    assumptions about the proposed cuts. -/
noncomputable def solveWith {ps : List (BiPoly ℝ)} (p : Projection ps) : Diagram ps :=
  (LiftingData.fromPolynomials p).solve

/-- A total sign-invariant planar CAD over the reals. The generic projection
    uses a squarefree product, its leading coefficient, and its derivative
    resultant. Critical fibers are specialized separately. -/
noncomputable def solve (ps : List (BiPoly ℝ)) : Diagram ps := solveWith (Projection.fromInputs ps)

/-- Use exact coefficients from an embedded field, such as ℚ or the real
    algebraic numbers, for the algebraic projection phase. -/
noncomputable def solveOver {K : Type} [Field K] [DecidableEq K] [CharZero K]
    (ι : K →+* ℝ) (ps : List (BiPoly K)) : Diagram (ps.map (embedCoefficients ι)) :=
  solveWith (Projection.fromEmbedded ι ps)

theorem solveWith_cell_model {ps : List (BiPoly ℝ)} (p : Projection ps) {c : Cell}
    (hc : c ∈ (solveWith p).cells) :
    ∃ s ∈ Univariate.decompose p.cuts, ∃ t : Slice ℝ,
      Nonempty (c.carrier ≃ₜ strip s × strip t) ∧ Prod.fst '' c.carrier = strip s :=
  (LiftingData.fromPolynomials p).cell_model hc

theorem solveWith_cylindrical {ps : List (BiPoly ℝ)} (p : Projection ps) {c d : Cell}
    (hc : c ∈ (solveWith p).cells) (hd : d ∈ (solveWith p).cells) :
    Prod.fst '' c.carrier = Prod.fst '' d.carrier ∨
      Disjoint (Prod.fst '' c.carrier) (Prod.fst '' d.carrier) :=
  (LiftingData.fromPolynomials p).cylindrical hc hd

theorem solve_cell_model {ps : List (BiPoly ℝ)} {c : Cell} (hc : c ∈ (solve ps).cells) :
    ∃ s ∈ Univariate.decompose (critical (rootPolynomial ps)), ∃ t : Slice ℝ,
      Nonempty (c.carrier ≃ₜ strip s × strip t) ∧ Prod.fst '' c.carrier = strip s :=
  solveWith_cell_model _ hc

theorem solve_cylindrical {ps : List (BiPoly ℝ)} {c d : Cell}
    (hc : c ∈ (solve ps).cells) (hd : d ∈ (solve ps).cells) :
    Prod.fst '' c.carrier = Prod.fst '' d.carrier ∨
      Disjoint (Prod.fst '' c.carrier) (Prod.fst '' d.carrier) :=
  solveWith_cylindrical _ hc hd

end CertifiedTopology.Plane
