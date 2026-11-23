module

public import CertifiedTopology.QuadricCAD
public import CertifiedTopology.PlaneConic
public import CertifiedTopology.PlaneAffine
public import CertifiedTopology.PlaneGeneral
public import CertifiedTopology.Extension

@[expose] public section

namespace CertifiedTopology.Quadric

/-- Try the specialized axis-separated, affine, or single-conic projection. -/
noncomputable def solve? (q r : Equation ℝ) : Option (List Cell) :=
  let ps := (program q r).projection
  let diagram := (Plane.solveAxes? ps).orElse fun _ =>
    (Plane.solveAffine? ps).orElse fun _ => Plane.solveConic? ps
  diagram.map (solve q r)

/-- A finite partition of the intersection, with certified samples and cell topology. -/
def IntersectionSpec (q r : Equation ℝ) (cs : List Cell) : Prop :=
  (∀ p : Space, (∃! c, c ∈ cs ∧ p ∈ c.carrier) ↔
    q.eval p.1.1 p.1.2 p.2 = 0 ∧ r.eval p.1.1 p.1.2 p.2 = 0) ∧
  (∀ c ∈ cs, c.sample ∈ c.carrier ∧ ContractibleSpace c.carrier)

theorem solve_spec (q r : Equation ℝ) (d : Plane.Diagram (program q r).projection) :
    IntersectionSpec q r (solve q r d) := by
  constructor
  · intro p
    constructor
    · rintro ⟨c, hc, _⟩
      exact (solve_correct q r d p).mp ⟨c,hc.1,hc.2⟩
    · intro hp
      obtain ⟨c, hc, hpc⟩ := (solve_correct q r d p).mpr hp
      exact ⟨c, ⟨hc,hpc⟩, fun e he => solve_disjoint q r d he.1 hc he.2 hpc⟩
  · exact fun c hc => ⟨c.sample_mem, solve_contractible q r d hc⟩

theorem solve?_correct (q r : Equation ℝ) {cs : List Cell}
    (h : solve? q r = some cs) : IntersectionSpec q r cs := by
  unfold solve? at h
  dsimp only at h
  obtain ⟨d, _, hcs⟩ := Option.map_eq_some_iff.mp h
  subst cs
  exact solve_spec q r d

/-- Use specialized planar projection when possible, and the total squarefree
    planar decomposition for every other pair of quadric equations. -/
noncomputable def decompose (q r : Equation ℝ) : List Cell :=
  match solve? q r with
  | some cs => cs
  | none => solve q r (Plane.solve (program q r).projection)

theorem decompose_correct (q r : Equation ℝ) : IntersectionSpec q r (decompose q r) := by
  unfold decompose
  split
  · exact solve?_correct q r (by assumption)
  · exact solve_spec q r _

theorem decompose_of_diagram (q r : Equation ℝ) :
    ∃ d : Plane.Diagram (program q r).projection, decompose q r = solve q r d := by
  unfold decompose
  split
  · rename_i cells h
    unfold solve? at h
    obtain ⟨d, _, hcs⟩ := Option.map_eq_some_iff.mp h
    exact ⟨d, hcs.symm⟩
  · exact ⟨_, rfl⟩

theorem decompose_cover (q r : Equation ℝ) (p : Space) :
    (∃ c ∈ decompose q r, p ∈ c.carrier) ↔
      q.eval p.1.1 p.1.2 p.2 = 0 ∧ r.eval p.1.1 p.1.2 p.2 = 0 := by
  obtain ⟨d, h⟩ := decompose_of_diagram q r
  rw [h]
  exact solve_correct q r d p

/-- Use checked projection identities and checked root tables at both levels of
    the planar lift. The base and fiber samples come from those tables. -/
noncomputable def decomposeWith (q r : Equation ℝ)
    {p : Plane.Projection (program q r).projection} (data : Plane.LiftingData p) : List Cell :=
  solve q r data.solve

theorem decomposeWith_correct (q r : Equation ℝ)
    {p : Plane.Projection (program q r).projection} (data : Plane.LiftingData p) :
    IntersectionSpec q r (decomposeWith q r data) :=
  solve_spec q r data.solve

theorem decomposeWith_cell_model (q r : Equation ℝ)
    {p : Plane.Projection (program q r).projection} (data : Plane.LiftingData p)
    {c : Cell} (hc : c ∈ decomposeWith q r data) :
    ∃ s ∈ data.base.cells, ∃ t : Slice ℝ,
      match c.height with
      | none => Nonempty (c.carrier ≃ₜ (Plane.strip s × Plane.strip t) × ℝ)
      | some _ => Nonempty (c.carrier ≃ₜ Plane.strip s × Plane.strip t) := by
  obtain ⟨s, hs, t, ⟨e⟩, _⟩ := data.cell_model (solve_base_mem q r data.solve hc)
  refine ⟨s, hs, t, ?_⟩
  have h := solve_cell_model q r data.solve hc
  cases hh : c.height <;> rw [hh] at h
  · exact ⟨h.some.trans (e.prodCongr (Homeomorph.refl ℝ))⟩
  · exact ⟨h.some.trans e⟩

theorem decomposeWith_cylindrical_x (q r : Equation ℝ)
    {p : Plane.Projection (program q r).projection} (data : Plane.LiftingData p)
    {c e : Cell} (hc : c ∈ decomposeWith q r data) (he : e ∈ decomposeWith q r data) :
    (Prod.fst ∘ Prod.fst) '' c.carrier = (Prod.fst ∘ Prod.fst) '' e.carrier ∨
      Disjoint ((Prod.fst ∘ Prod.fst) '' c.carrier) ((Prod.fst ∘ Prod.fst) '' e.carrier) := by
  change (fun x : Space => x.1.1) '' c.carrier = (fun x : Space => x.1.1) '' e.carrier ∨
    Disjoint ((fun x : Space => x.1.1) '' c.carrier) ((fun x : Space => x.1.1) '' e.carrier)
  rw [← Set.image_image Prod.fst Prod.fst c.carrier, ← Set.image_image Prod.fst Prod.fst e.carrier,
    c.image_fst, e.image_fst]
  exact data.cylindrical (solve_base_mem q r data.solve hc) (solve_base_mem q r data.solve he)

/-- Keep the algebraic projection in the input coefficient field. The selected
    cells and their topology are interpreted in real space. -/
noncomputable def diagramOver {K : Type} [Field K] [DecidableEq K] [CharZero K]
    (ι : K →+* ℝ) (q r : Equation K) :
    Plane.Diagram (program (q.map ι) (r.map ι)).projection :=
  (projection_embed ι q r).symm ▸ Plane.solveOver ι (program q r).projection

/-- Try the specialized routes, then use exact coefficient-field projection. -/
noncomputable def decomposeOver {K : Type} [Field K] [DecidableEq K] [CharZero K]
    (ι : K →+* ℝ) (q r : Equation K) : List Cell :=
  match solve? (q.map ι) (r.map ι) with
  | some cs => cs
  | none => solve (q.map ι) (r.map ι) (diagramOver ι q r)

theorem decomposeOver_correct {K : Type} [Field K] [DecidableEq K] [CharZero K]
    (ι : K →+* ℝ) (q r : Equation K) :
    IntersectionSpec (q.map ι) (r.map ι) (decomposeOver ι q r) := by
  unfold decomposeOver
  split
  · exact solve?_correct _ _ (by assumption)
  · exact solve_spec _ _ _

/-- Solve two quadrics whose coefficients are real algebraic numbers. -/
noncomputable def decomposeRealAlg (q r : Equation RealAlg) : List Cell :=
  decomposeOver (algebraicClosure ℚ ℝ).toSubfield.subtype q r

theorem decomposeRealAlg_correct (q r : Equation RealAlg) :
    let ι := (algebraicClosure ℚ ℝ).toSubfield.subtype
    IntersectionSpec (q.map ι) (r.map ι) (decomposeRealAlg q r) :=
  decomposeOver_correct _ q r

end CertifiedTopology.Quadric
