module

public import CertifiedTopology.QuadricIntersection
public import CertifiedTopology.ClosureComponents

@[expose] public section

namespace CertifiedTopology.Quadric

open Set

def locus (q r : Equation ℝ) : Set Space :=
  {p | q.eval p.1.1 p.1.2 p.2 = 0 ∧ r.eval p.1.1 p.1.2 p.2 = 0}

theorem isClosed_locus (q r : Equation ℝ) : IsClosed (locus q r) := by
  have h (f : Equation ℝ) : Continuous fun p : Space => f.eval p.1.1 p.1.2 p.2 := by
    unfold Equation.eval Equation.linear Equation.offset
    fun_prop
  exact (isClosed_eq (h q) continuous_const).inter (isClosed_eq (h r) continuous_const)

namespace Cell

/-- Edges join cells whose closures meet in real space. -/
def closureGraph (cs : List Cell) : SimpleGraph (Fin cs.length) :=
  ClosureComponents.graph fun i => (cs.get i).carrier

theorem connectedComponentIn_eq_closures {cs : List Cell} {S : Set Space}
    (hclosed : IsClosed S)
    (hcover : ∀ x, x ∈ S ↔ ∃ j : Fin cs.length, x ∈ (cs.get j).carrier)
    (hconn : ∀ j : Fin cs.length, ContractibleSpace (cs.get j).carrier)
    (i : Fin cs.length) :
    connectedComponentIn S (cs.get i).sample =
      ⋃ j : {j // (closureGraph cs).Reachable i j}, closure (cs.get j.val).carrier :=
  ClosureComponents.connectedComponentIn_eq_closures hclosed hcover
    (fun j => by
      let := hconn j
      exact isPreconnected_iff_preconnectedSpace.mpr inferInstance)
    i (cs.get i).sample_mem

end Cell

/-- A checker can supply closure intersections for every pair of output cells. -/
structure ClosureIncidence (cs : List Cell) where
  edge : Fin cs.length → Fin cs.length → Bool
  correct : ∀ i j, edge i j = true ↔ (Cell.closureGraph cs).Adj i j

namespace ClosureIncidence

variable {cs : List Cell}

/-- The total mathematical incidence table. A computational backend can
    instead supply Boolean entries and certify them in `correct`. -/
noncomputable def fromClosures (cs : List Cell) : ClosureIncidence cs := by
  classical
  exact ⟨fun i j => decide ((Cell.closureGraph cs).Adj i j), fun _ _ => by simp⟩

abbrev merge {n : ℕ} := @ClosureComponents.ClosureIncidence.merge n
abbrev edges {n : ℕ} := @ClosureComponents.ClosureIncidence.edges n
abbrev computeLabels {n : ℕ} := @ClosureComponents.ClosureIncidence.computeLabels n

def labels (d : ClosureIncidence cs) : Vector (Fin cs.length) cs.length := computeLabels d.edge

def toClosureIncidence (d : ClosureIncidence cs) :
    ClosureComponents.ClosureIncidence (fun i : Fin cs.length => (cs.get i).carrier) :=
  ⟨d.edge, d.correct⟩

theorem same_label (d : ClosureIncidence cs) (i j : Fin cs.length) :
    d.labels.get i = d.labels.get j ↔ (Cell.closureGraph cs).Reachable i j :=
  d.toClosureIncidence.same_label i j

/-- The cells with the same label partition the connected component of the
    chosen sample. This includes cells at shared limit points. -/
theorem component_correct (q r : Equation ℝ)
    (p : Plane.Diagram (program q r).projection) (d : ClosureIncidence (solve q r p))
    (i : Fin (solve q r p).length) :
    connectedComponentIn (locus q r) ((solve q r p).get i).sample =
      ⋃ j : {j // d.labels.get i = d.labels.get j}, ((solve q r p).get j.val).carrier := by
  have cover (x : Space) : x ∈ locus q r ↔ ∃ j : Fin (solve q r p).length,
      x ∈ ((solve q r p).get j).carrier :=
    (solve_correct q r p x).symm.trans List.exists_mem_iff_get
  exact d.toClosureIncidence.component_correct (isClosed_locus q r) cover
    (fun j => by
      let := solve_contractible q r p (List.get_mem (solve q r p) j)
      exact isPreconnected_iff_preconnectedSpace.mpr inferInstance)
    i ((solve q r p).get i).sample_mem

theorem decompose_component_correct (q r : Equation ℝ) (d : ClosureIncidence (decompose q r))
    (i : Fin (decompose q r).length) :
    connectedComponentIn (locus q r) ((decompose q r).get i).sample =
      ⋃ j : {j // d.labels.get i = d.labels.get j}, ((decompose q r).get j.val).carrier := by
  obtain ⟨p, hp⟩ := decompose_of_diagram q r
  generalize h : decompose q r = cs at d i ⊢
  rw [h] at hp
  clear h
  subst cs
  exact component_correct q r p d i

end ClosureIncidence

/-- Label every cell of the total dispatcher by its connected component. -/
noncomputable def decomposeComponents (q r : Equation ℝ) :
    Vector (Fin (decompose q r).length) (decompose q r).length :=
  (ClosureIncidence.fromClosures (decompose q r)).labels

theorem decomposeComponents_correct (q r : Equation ℝ) (i : Fin (decompose q r).length) :
    connectedComponentIn (locus q r) ((decompose q r).get i).sample =
      ⋃ j : {j // (decomposeComponents q r).get i = (decomposeComponents q r).get j},
        ((decompose q r).get j.val).carrier :=
  ClosureIncidence.decompose_component_correct q r (ClosureIncidence.fromClosures _) i

end CertifiedTopology.Quadric
