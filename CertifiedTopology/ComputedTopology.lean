module

public import CertifiedTopology.CADStratification
public import Lean.Data.Json

@[expose] public section

namespace CertifiedTopology.ComputedTopology

open Set ExecutableIsolation CylindricalData CADDecision

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
variable {model : RealModel K}

abbrev CADCell (model : RealModel K) (n : ℕ) := ComputableCAD.Cell model n

noncomputable def carrier (cs : List (CADCell model n)) (i : Fin cs.length) : Set (Fin n → ℝ) :=
  (cs.get i).carrier

def overlap (model : RealModel K) (cells : List (CADCell model n)) (i j : Fin cells.length) : Bool :=
  i != j && fastOverlap model (cells.get i).code (cells.get j).code

theorem overlap_symm (model : RealModel K) (cells : List (CADCell model n))
    (i j : Fin cells.length) : overlap model cells i j = overlap model cells j i := by
  apply Bool.eq_iff_iff.mpr
  simp only [overlap,Bool.and_eq_true,bne_iff_ne]
  rw [fastOverlap_correct model _ _ (cells.get i).regular (cells.get j).regular
    ⟨_,(cells.get i).sample_mem⟩ ⟨_,(cells.get j).sample_mem⟩]
  rw [fastOverlap_correct model _ _ (cells.get j).regular (cells.get i).regular
    ⟨_,(cells.get j).sample_mem⟩ ⟨_,(cells.get i).sample_mem⟩]
  rw [ne_comm,inter_comm]

/-- The closure solver runs once per unordered pair. -/
def overlapTable (model : RealModel K) (cells : List (CADCell model n)) :
    Vector (Vector Bool cells.length) cells.length :=
  Vector.ofFn fun i => Vector.ofFn fun j => i < j && overlap model cells i j

def tableEdge {k : ℕ} (t : Vector (Vector Bool k) k) (i j : Fin k) : Bool :=
  if i < j then (t.get i).get j else (t.get j).get i

theorem tableEdge_correct (model : RealModel K) (cells : List (CADCell model n))
    (i j : Fin cells.length) : tableEdge (overlapTable model cells) i j = overlap model cells i j := by
  have get {k : ℕ} {A : Type} (f : Fin k → A) (i : Fin k) : (Vector.ofFn f).get i = f i := by
    simp [Vector.get]
    exact congrArg f (Fin.ext rfl)
  unfold tableEdge overlapTable
  by_cases h : i < j
  · simp [h,get]
  · by_cases h' : j < i
    · simp [h,h',get,overlap_symm model cells j i]
    · obtain rfl := le_antisymm (le_of_not_gt h') (le_of_not_gt h)
      simp [get,overlap]

def closureTable (model : RealModel K) (cells : List (CADCell model n)) :
    ClosureComponents.ClosureIncidence (carrier cells) where
  edge := tableEdge (overlapTable model cells)
  correct i j := by
    rw [tableEdge_correct, overlap, Bool.and_eq_true, bne_iff_ne, fastOverlap_correct model _ _
      (cells.get i).regular (cells.get j).regular
      ⟨_,(cells.get i).sample_mem⟩ ⟨_,(cells.get j).sample_mem⟩]
    rfl

def componentLabels (model : RealModel K) (cells : List (CADCell model n)) :
    Vector (Fin cells.length) cells.length :=
  ClosureComponents.ClosureIncidence.computeLabels (tableEdge (overlapTable model cells))

noncomputable def locus (model : RealModel K) (p q : Multi K n) : Set (Fin n → ℝ) :=
  {x | Multi.evalHom model.hom x p = 0 ∧ Multi.evalHom model.hom x q = 0}

theorem locus_closed (model : RealModel K) (p q : Multi K n) : IsClosed (locus model p q) := by
  exact (isClosed_eq (Multi.continuous_eval model.hom p) continuous_const).inter
    (isClosed_eq (Multi.continuous_eval model.hom q) continuous_const)

def zeroSetFormula (p q : Multi K n) : Prenex K n :=
  .matrix (.and (.atom p .on) (.atom q .on))

theorem zeroSetFormula_correct (model : RealModel K) (p q : Multi K n) :
    (zeroSetFormula p q).carrier model = locus model p q := by
  ext x
  exact and_congr side_on side_on

/-- The solution is derived from the two input polynomials. Cell codes,
    closure predicates and the connected-component algorithm share that data. -/
structure Intersection (model : RealModel K) (p q : Multi K n) where
  cells : List (CADCell model n)
  nodup : cells.Nodup
  partition : ∀ x, x ∈ locus model p q ↔ ∃! c, c ∈ cells ∧ x ∈ c.carrier
  contained : ∀ c ∈ cells, c.carrier ⊆ locus model p q

def solve (model : RealModel K) (p q : Multi K n) : Intersection model p q where
  cells := ComputableCAD.intersection model p q
  nodup := ComputableCAD.intersection_nodup model p q
  partition := ComputableCAD.intersection_correct model p q
  contained c hc x hx := by
    rw [ComputableCAD.intersection_eq] at hc
    obtain ⟨hc, h⟩ := List.mem_filter.mp hc
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
    have inv := (ComputableCAD.cad model n [p,q]).invariant c hc x hx
    exact ⟨side_on.mp ((inv p (by simp)).trans h.1), side_on.mp ((inv q (by simp)).trans h.2)⟩

def Intersection.refine {p q : Multi K n} (a : Intersection model p q) :
    Stratification model (zeroSetFormula p q) [] := by
  refine match h : a.cells with
  | [c] => stratifyCell (zeroSetFormula p q) c ?_
  | _ => ?_
  · rw [zeroSetFormula_correct]
    ext x
    constructor
    · intro hx
      obtain ⟨d,hd,hm⟩ := ((a.partition x).mp hx).exists
      rw [h, List.mem_singleton] at hd
      exact hd ▸ hm
    · exact fun hx => a.contained c (h.symm ▸ List.mem_singleton_self c) hx
  if h : a.cells.all (fun c => c.code.dimension == 0) = true then
    refine stratifyPoints (zeroSetFormula p q) [] a.cells a.nodup ?_ ?_ ?_
    · rw [zeroSetFormula_correct]
      exact a.partition
    · rw [zeroSetFormula_correct]
      exact a.contained
    · intro c hc
      exact beq_iff_eq.mp (List.all_eq_true.mp h c hc)
  else
    exact stratify model (zeroSetFormula p q)

def stratifyIntersection (model : RealModel K) (p q : Multi K n) :
    Stratification model (zeroSetFormula p q) [] := (solve model p q).refine

theorem stratifyIntersection_correct (model : RealModel K) (p q : Multi K n) (x : Fin n → ℝ) :
    x ∈ locus model p q ↔ ∃! s, s ∈ (stratifyIntersection model p q).strata ∧ x ∈ s.carrier := by
  rw [← zeroSetFormula_correct]
  exact (stratifyIntersection model p q).unique x

def strataJson {f : Prenex K n} {constraints : List (Prenex K n)} (s : Stratification model f constraints) :
    Lean.Json :=
  let strata := s.strata
  .arr <| (List.finRange strata.length).toArray.map fun i =>
    let ci := strata.get i
    let row := s.incidenceRow i
    let closureIndices := (List.finRange strata.length).filterMap fun j =>
      if row j then some j.val else none
    Lean.Json.mkObj [
      ("dimension", Lean.toJson ci.dimension),
      ("closure", Lean.toJson closureIndices)]


namespace Intersection

variable {p q : Multi K n} (s : Intersection model p q)

theorem cover (x : Fin n → ℝ) : x ∈ locus model p q ↔ ∃ i, x ∈ carrier s.cells i := by
  constructor
  · intro h
    obtain ⟨c,hc,hx⟩ := ((s.partition x).mp h).exists
    obtain ⟨i,rfl⟩ := List.get_of_mem hc
    exact ⟨i,hx⟩
  · rintro ⟨i,hi⟩
    exact s.contained _ (List.get_mem _ _) hi

def labels : Vector (Fin s.cells.length) s.cells.length := componentLabels model s.cells

def closure (i : Fin s.cells.length) : Prenex K n := closureFormula model (s.cells.get i).code

theorem closure_correct (i : Fin s.cells.length) (x : Fin n → ℝ) :
    (s.closure i).holds model x ↔ x ∈ _root_.closure (carrier s.cells i) :=
  closureFormula_correct model (s.cells.get i).code (s.cells.get i).regular x

theorem component_correct (i : Fin s.cells.length) {x : Fin n → ℝ} (hx : x ∈ carrier s.cells i) :
    connectedComponentIn (locus model p q) x =
      ⋃ j : {j // s.labels.get i = s.labels.get j}, carrier s.cells j.val :=
  (closureTable model s.cells).component_correct (locus_closed model p q) s.cover
    (fun j => (s.cells.get j).connected) i hx

end Intersection

def indices : {n : ℕ} → Code K n → List ℕ
  | 0, .origin => []
  | n+1, .lift b _ row => indices b ++ [row]

def polynomialJson (encode : K → Lean.Json) : (n : ℕ) → Multi K n → Lean.Json
  | 0, a => encode a
  | n+1, p => .arr ((p.coefficients.map (polynomialJson encode n)).toArray)

def codeJson (encode : K → Lean.Json) : {n : ℕ} → Code K n → List Lean.Json
  | 0, .origin => []
  | n+1, .lift b p row => codeJson encode b ++ [
    Lean.Json.mkObj [("row", Lean.toJson row),
      ("ascending_coefficients", .arr ((p.coefficients.map (polynomialJson encode n)).toArray))]]

def Intersection.toJson {p q : Multi K n} (s : Intersection model p q)
    (encode : Option (K → Lean.Json)) : Lean.Json := Id.run do
  let cells := s.cells
  let edges := tableEdge (overlapTable model cells)
  let labels := ClosureComponents.ClosureIncidence.computeLabels edges
  return .arr <| (List.finRange cells.length).toArray.map fun i =>
    let code := (cells.get i).code
    let rows := indices code
    Lean.Json.mkObj ([
      ("rows", Lean.toJson rows),
      ("dimension", Lean.toJson code.dimension),
      ("component", Lean.toJson (labels.get i).val),
      ("closure_overlap", Lean.toJson ((List.finRange cells.length).filterMap fun j =>
        if edges i j then some j.val else none))] ++
      (encode.toList.map fun f => ("cylindrical_description", .arr (codeJson f code).toArray)))

end CertifiedTopology.ComputedTopology
