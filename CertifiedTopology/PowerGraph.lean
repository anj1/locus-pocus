module

public import CertifiedTopology.Isolation
public import CertifiedTopology.Plane
public import CertifiedTopology.TopologyArtifact
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace CertifiedTopology.PowerGraph

open Set Polynomial TopologyArtifact

/-- A curve with one coordinate fixed by a polynomial graph, and the other
    by a shifted second or fourth power. -/
structure Equation where
  graph : Plane.BiPoly ℝ
  center : Polynomial ℝ
  radicand : Polynomial ℝ
  fourth : Bool := false

abbrev Space := (ℝ × ℝ) × ℝ

def Equation.power (q : Equation) (v : ℝ) : ℝ :=
  if q.fourth then v^4 else v^2

@[fun_prop] theorem Equation.continuous_power (q : Equation) : Continuous q.power := by
  unfold power
  split <;> fun_prop

def Equation.locus (q : Equation) : Set Space :=
  {p | p.1.2 = Plane.value q.graph (p.1.1, p.2) ∧
    q.power (p.2 - q.center.eval p.1.1) = q.radicand.eval p.1.1}

theorem Equation.closed (q : Equation) : IsClosed q.locus :=
  (isClosed_eq (by fun_prop) ((Plane.continuous_value q.graph).comp (by fun_prop))).inter
    (isClosed_eq (by fun_prop) (q.radicand.continuous.comp (by fun_prop)))

noncomputable def Equation.radius (q : Equation) (d : ℝ) : ℝ :=
  if q.fourth then √(√d) else √d

@[fun_prop] theorem Equation.continuous_radius (q : Equation) : Continuous q.radius := by
  unfold radius
  split <;> fun_prop

theorem Equation.radius_zero (q : Equation) : q.radius 0 = 0 := by
  simp [radius]

theorem Equation.radius_pos (q : Equation) {d : ℝ} (hd : 0 < d) : 0 < q.radius d := by
  unfold radius
  split
  · exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hd)
  · exact Real.sqrt_pos.mpr hd

theorem Equation.power_nonneg (q : Equation) (v : ℝ) : 0 ≤ q.power v := by
  unfold power
  split <;> positivity

theorem Equation.power_eq_iff (q : Equation) (v d : ℝ) (hd : 0 ≤ d) :
    q.power v = d ↔ v = q.radius d ∨ v = -q.radius d := by
  unfold power radius
  split_ifs with h
  · have h₁ := Real.sq_sqrt (Real.sqrt_nonneg d)
    have h₂ := Real.sq_sqrt hd
    have eq : (v^2)^2 = d ↔ v^2 = √d := by
      nth_rw 1 [← h₂]
      rw [sq_eq_sq_iff_eq_or_eq_neg]
      constructor
      · rintro (h | h)
        · exact h
        · linarith [sq_nonneg v, Real.sqrt_nonneg d]
      · exact Or.inl
    rw [show v^4 = (v^2)^2 by ring, eq]
    nth_rw 1 [← h₁]
    exact sq_eq_sq_iff_eq_or_eq_neg
  · nth_rw 1 [← Real.sq_sqrt hd]
    exact sq_eq_sq_iff_eq_or_eq_neg

noncomputable def height (q : Equation) (upper : Bool) (x : ℝ) : ℝ :=
  q.center.eval x + if upper then q.radius (q.radicand.eval x) else -q.radius (q.radicand.eval x)

@[fun_prop] theorem continuous_height (q : Equation) (upper : Bool) : Continuous (height q upper) := by
  cases upper <;> unfold height <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

noncomputable def path (q : Equation) (upper : Bool) (x : ℝ) : Space :=
  ((x, Plane.value q.graph (x, height q upper x)), height q upper x)

@[fun_prop] theorem continuous_path (q : Equation) (upper : Bool) : Continuous (path q upper) := by
  unfold path
  have ch := continuous_height q upper
  exact (continuous_id.prodMk ((Plane.continuous_value q.graph).comp (continuous_id.prodMk ch))).prodMk ch

theorem mem_path_image (q : Equation) (u : Bool) (A : Set ℝ) (p : Space) :
    p ∈ path q u '' A ↔ p.1.1 ∈ A ∧ p.1.2 = Plane.value q.graph (p.1.1, p.2) ∧
      p.2 = height q u p.1.1 := by
  rcases p with ⟨⟨x,y⟩,z⟩
  simp only [path, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨t, ht, ⟨rfl, hy⟩, rfl⟩
    exact ⟨ht, hy.symm, rfl⟩
  · rintro ⟨hx, hy, hz⟩
    exact ⟨x, hx, ⟨rfl, hz ▸ hy.symm⟩, hz.symm⟩

theorem path_isClosedMap (q : Equation) (upper : Bool) : IsClosedMap (path q upper) := by
  intro A hA
  have eq : path q upper '' A = {p : Space | p.1.1 ∈ A} ∩
      ({p | p.1.2 = Plane.value q.graph (p.1.1, p.2)} ∩ {p | p.2 = height q upper p.1.1}) := by
    ext p
    exact mem_path_image q upper A p
  rw [eq]
  exact (hA.preimage (by fun_prop)).inter
    ((isClosed_eq (by fun_prop) ((Plane.continuous_value q.graph).comp (by fun_prop))).inter
      (isClosed_eq (by fun_prop) (by fun_prop)))

theorem strip_section (a : ℝ) : Plane.strip (.sectionAt a) = {a} := rfl

theorem strip_unbounded : Plane.strip (.sector none none) = univ := by
  ext
  simp [Plane.strip, Univariate.contains, Slice.Contains]

theorem strip_lower (a : ℝ) : Plane.strip (.sector (some a) none) = Ioi a := by
  ext
  simp [Plane.strip, Univariate.contains, Slice.Contains, Aff.eval]

theorem strip_upper (a : ℝ) : Plane.strip (.sector none (some a)) = Iio a := by
  ext
  simp [Plane.strip, Univariate.contains, Slice.Contains, Aff.eval]

theorem strip_bounded (a b : ℝ) : Plane.strip (.sector (some a) (some b)) = Ioo a b := by
  ext
  simp [Plane.strip, Univariate.contains, Slice.Contains, Aff.eval]

theorem strip_locallyClosed (s : Slice ℝ) : IsLocallyClosed (Plane.strip s) := by
  cases s with
  | sectionAt x => rw [strip_section]; exact isClosed_singleton.isLocallyClosed
  | sector l u =>
    apply IsOpen.isLocallyClosed
    cases l <;> cases u <;> simp [strip_unbounded, strip_lower, strip_upper, strip_bounded,
      isOpen_Iio, isOpen_Ioi, isOpen_Ioo]

theorem path_locallyClosed (q : Equation) (u : Bool) {A : Set ℝ} (hA : IsLocallyClosed A) :
    IsLocallyClosed (path q u '' A) := by
  have eq : path q u '' A = {p : Space | p.1.1 ∈ A} ∩ (path q u '' univ) := by
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, mem_path_image, mem_univ, true_and]
  rw [eq]
  exact (hA.preimage (by fun_prop)).inter ((path_isClosedMap q u _ isClosed_univ).isLocallyClosed)

/-- The data emitted by a univariate sign-table backend. Only the row signs and
    the position of each row in the closure of another row enter the executable part. -/
structure Base (q : Equation) where
  signs : List Side
  incident : Fin signs.length → Fin signs.length → Bool
  region : Fin signs.length → Set ℝ
  partition : ∀ x, ∃! i, x ∈ region i
  nonempty : ∀ i, (region i).Nonempty
  locallyClosed : ∀ i, IsLocallyClosed (region i)
  contractible : ∀ i, ContractibleSpace (region i)
  sign_correct : ∀ i x, x ∈ region i → side (q.radicand.eval x) 0 = signs.get i
  incident_correct : ∀ i j x, x ∈ region j → (incident i j = true ↔ x ∈ closure (region i))

namespace Base

/-- Interpret a labeled univariate decomposition as a base for lifting.
    The checker ties the finite signs to the diagram and checks each
    proposed closure relation against the exact real intervals. -/
def ofDiagram {q : Equation} (d : Isolation.Diagram [q.radicand]) (signs : List Side)
    (shape : Fin signs.length → Slice ℝ) (injective : Function.Injective shape)
    (layout : d.rows = (List.finRange signs.length).map (fun i => (shape i, [signs.get i])))
    (nonempty : ∀ i, (Plane.strip (shape i)).Nonempty)
    (incident : Fin signs.length → Fin signs.length → Bool)
    (correct : ∀ i j x, x ∈ Plane.strip (shape j) →
      (incident i j = true ↔ x ∈ closure (Plane.strip (shape i)))) : Base q where
  signs := signs
  incident := incident
  region i := Plane.strip (shape i)
  partition x := by
    obtain ⟨row, ⟨hr, hx⟩, hu⟩ := d.partition x
    rw [layout] at hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    refine ⟨i, hx, fun j hj => ?_⟩
    have hm : (shape j, [signs.get j]) ∈ d.rows := by
      rw [layout]
      exact List.mem_map_of_mem (List.mem_finRange j)
    exact injective (congrArg Prod.fst (hu _ ⟨hm,hj⟩))
  nonempty := nonempty
  locallyClosed i := strip_locallyClosed (shape i)
  contractible i := (Plane.convex_strip (shape i)).contractibleSpace (nonempty i)
  sign_correct i x hx := by
    have h := d.valid (shape i, [signs.get i]) (by
      rw [layout]
      exact List.mem_map_of_mem (List.mem_finRange i)) x hx
    simpa using h
  incident_correct := correct

end Base

def branches : Side → List Bool
  | .below => []
  | .on => [false]
  | .above => [false, true]

theorem branches_correct (q : Equation) (x z : ℝ) :
    q.power (z - q.center.eval x) = q.radicand.eval x ↔
      ∃ upper ∈ branches (side (q.radicand.eval x) 0), z = height q upper x := by
  let d := q.radicand.eval x
  let c := q.center.eval x
  change q.power (z-c) = d ↔ ∃ upper ∈ branches (side d 0), z = height q upper x
  rcases lt_trichotomy d 0 with hn | he | hp
  · simp only [side, ite_eq_left hn, branches, List.not_mem_nil, false_and, exists_false, iff_false]
    intro h
    exact hn.not_ge (h ▸ q.power_nonneg (z-c))
  · rw [q.power_eq_iff _ _ he.ge, he]
    simp [side, branches, height, show q.radicand.eval x = 0 from he, q.radius_zero, c, sub_eq_zero]
  · have hs : side d 0 = .above := by simp [side, hp.not_gt, hp.ne']
    rw [hs, q.power_eq_iff _ _ hp.le]
    simp only [branches, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · rintro (h | h)
      · exact ⟨true, Or.inr rfl, by simp [height]; linarith⟩
      · exact ⟨false, Or.inl rfl, by simp [height]; linarith⟩
    · rintro ⟨_, rfl | rfl, h⟩ <;> simp [height] at h <;> (first | left; linarith | right; linarith)

private theorem height_eq (q : Equation) (x : ℝ) (s : Side)
    (hs : side (q.radicand.eval x) 0 = s) (hn : s ≠ .below) (u v : Bool) :
    height q u x = height q v x ↔ u = v ∨ s = .on := by
  cases u <;> cases v <;> simp [height]
  all_goals
    unfold side at hs
    split_ifs at hs with h₁ h₂
    · exact (hn hs.symm).elim
    · simp [h₂, hs.symm, q.radius_zero]
    · have hp : 0 < q.radicand.eval x := lt_of_le_of_ne (le_of_not_gt h₁) (Ne.symm h₂)
      have hp' := q.radius_pos hp
      constructor
      · intro h
        linarith
      · simp [hs.symm]

namespace Base

variable {q : Equation}

abbrev Cell (d : Base q) := Fin d.signs.length × Bool

def compute (signs : List Side) (incident : Fin signs.length → Fin signs.length → Bool) :
    Layout (Fin signs.length × Bool) :=
  Layout.ofCells ((List.finRange signs.length).flatMap fun i => (branches (signs.get i)).map (i, ·))
    fun (i,u) (j,v) => incident i j && (u == v || signs.get j == .on)

def solve (d : Base q) : Layout d.Cell := compute d.signs d.incident

theorem solve_nodup (d : Base q) : d.solve.cells.Nodup := by
  have hn : (List.finRange d.signs.length).Nodup :=
    List.nodup_finRange _
  apply List.nodup_flatMap.mpr
  refine ⟨?_, hn.imp ?_⟩
  · intro i _
    apply List.Nodup.map (fun _ _ h => congrArg Prod.snd h)
    cases d.signs.get i <;> simp [branches]
  · intro i j hij c hi hj
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hi
    obtain ⟨v,_,h⟩ := List.mem_map.mp hj
    exact hij (congrArg Prod.fst h).symm

noncomputable def carrier (d : Base q) (c : d.Cell) : Set Space :=
  path q c.2 '' d.region c.1

private theorem mem_solve (d : Base q) (c : d.Cell) :
    c ∈ d.solve.cells ↔ c.2 ∈ branches (d.signs.get c.1) := by
  rcases c with ⟨i,u⟩
  simp [solve, compute, Layout.ofCells, List.mem_flatMap]

theorem mem_carrier (d : Base q) {p : Space} (c : d.Cell) :
    p ∈ d.carrier c ↔ p.1.1 ∈ d.region c.1 ∧
      p.1.2 = Plane.value q.graph (p.1.1, p.2) ∧ p.2 = height q c.2 p.1.1 :=
  mem_path_image q c.2 _ p

/-- Projection to the free coordinate is a homeomorphism on each lifted branch. -/
noncomputable def cellModel (d : Base q) (c : d.Cell) : d.carrier c ≃ₜ d.region c.1 where
  toFun p := ⟨p.val.1.1, ((mem_carrier d c).mp p.property).1⟩
  invFun t := ⟨path q c.2 t, mem_image_of_mem _ t.property⟩
  left_inv p := by
    obtain ⟨t, ht, eq⟩ := p.property
    apply Subtype.ext
    change path q c.2 p.val.1.1 = p.val
    rw [← eq]
    rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_fst.comp continuous_fst).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_path _ _).comp continuous_subtype_val).subtype_mk _

theorem solve_correct (d : Base q) : Valid d.solve d.carrier q.locus := by
  have baseUnique (x : ℝ) (i j) (hi : x ∈ d.region i) (hj : x ∈ d.region j) : i = j := by
    obtain ⟨_,_,hu⟩ := d.partition x
    exact (hu i hi).trans (hu j hj).symm
  refine ⟨q.closed, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    rw [← List.exists_mem_iff_get (l := d.solve.cells) (p := fun c => p ∈ d.carrier c)]
    constructor
    · intro hp
      obtain ⟨i, hi, _⟩ := d.partition p.1.1
      obtain ⟨u, hu, he⟩ := (branches_correct q _ _).mp hp.2
      rw [d.sign_correct i _ hi] at hu
      exact ⟨(i,u), (mem_solve d _).mpr hu, (mem_carrier d _).mpr ⟨hi,hp.1,he⟩⟩
    · rintro ⟨⟨i,u⟩, hm, hp⟩
      obtain ⟨hi,hy,hz⟩ := (mem_carrier d _).mp hp
      have hb := (mem_solve d _).mp hm
      rw [← d.sign_correct i _ hi] at hb
      exact ⟨hy, (branches_correct q _ _).mpr ⟨u,hb,hz⟩⟩
  · intro p i j hp hp'
    let c := d.solve.cells.get i
    let e := d.solve.cells.get j
    have hc := (mem_solve d c).mp (List.get_mem _ i)
    have he := (mem_solve d e).mp (List.get_mem _ j)
    obtain ⟨hi,_,hz⟩ := (mem_carrier d c).mp hp
    obtain ⟨hj,_,hw⟩ := (mem_carrier d e).mp hp'
    have hb := baseUnique _ _ _ hi hj
    have hn : d.signs.get c.1 ≠ .below := by intro h; rw [h] at hc; cases hc
    have eq := (height_eq q _ _ (d.sign_correct c.1 _ hi) hn c.2 e.2).mp (hz.symm.trans hw)
    apply d.solve_nodup.injective_get
    apply Prod.ext hb
    rcases eq with eq | eq
    · exact eq
    · have heq : d.signs.get e.1 = .on := hb ▸ eq
      rw [eq] at hc
      rw [heq] at he
      exact (show c.2 = false by simpa [branches] using hc).trans
        (show e.2 = false by simpa [branches] using he).symm
  · intro i
    exact (d.nonempty _).image _
  · intro i
    exact path_locallyClosed q _ (d.locallyClosed (d.solve.cells.get i).1)
  · intro i
    let := d.contractible (d.solve.cells.get i).1
    exact (d.cellModel (d.solve.cells.get i)).contractibleSpace
  · intro i j p hp
    let c := d.solve.cells.get i
    let e := d.solve.cells.get j
    obtain ⟨hj,hy,hz⟩ := (mem_carrier d e).mp hp
    have he := (mem_solve d e).mp (List.get_mem _ j)
    have hn : d.signs.get e.1 ≠ .below := by intro h; rw [h] at he; cases he
    change (d.solve.incident i j = true ↔ p ∈ closure (path q c.2 '' d.region c.1))
    rw [(path_isClosedMap q c.2).closure_image_eq_of_continuous (continuous_path _ _) (d.region c.1)]
    have inc : d.solve.incident i j =
        (d.incident c.1 e.1 && (c.2 == e.2 || d.signs.get e.1 == .on)) :=
      Layout.incident_ofCells _ _ i j
    rw [inc]
    change (d.incident c.1 e.1 && (c.2 == e.2 || d.signs.get e.1 == .on)) = true ↔ _
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      d.incident_correct c.1 e.1 p.1.1 hj]
    rw [mem_path_image, ← hy]
    have heq := height_eq q _ _ (d.sign_correct e.1 _ hj) hn c.2 e.2
    constructor
    · rintro ⟨hx,h⟩
      have h₁ := heq.mpr h
      exact ⟨hx, rfl, hz.trans h₁.symm⟩
    · rintro ⟨hx,_,h⟩
      exact ⟨hx, heq.mp (h.symm.trans hz)⟩

end Base
end CertifiedTopology.PowerGraph
