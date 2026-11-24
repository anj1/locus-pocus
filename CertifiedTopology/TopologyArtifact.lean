module

public import CertifiedTopology.ClosureComponents
public import Mathlib.Topology.Homotopy.Contractible
public import Mathlib.Topology.LocallyClosed

@[expose] public section

namespace CertifiedTopology.TopologyArtifact

open Set

/-- The executable portion of a finite stratification. Row `i` of `frontier`
    describes the cells contained in the closure of cell `i`, including itself. -/
structure Layout (C : Type) where
  cells : List C
  frontier : Vector (Vector Bool cells.length) cells.length

def Layout.ofCells {C : Type} (cs : List C) (inClosure : C → C → Bool) : Layout C :=
  ⟨cs, Vector.ofFn fun i => Vector.ofFn fun j => inClosure (cs.get i) (cs.get j)⟩

def Layout.incident {C : Type} (a : Layout C) (i j : Fin a.cells.length) : Bool :=
  (a.frontier.get i).get j

def Layout.edge {C : Type} (a : Layout C) (i j : Fin a.cells.length) : Bool :=
  (i != j) && (a.incident i j || a.incident j i)

def Layout.labels {C : Type} (a : Layout C) : Vector (Fin a.cells.length) a.cells.length :=
  ClosureComponents.ClosureIncidence.computeLabels a.edge

theorem Layout.incident_ofCells {C : Type} (cs : List C) (r : C → C → Bool)
    (i j : Fin cs.length) :
    (Layout.ofCells cs r).incident i j = r (cs.get i) (cs.get j) := by
  have get {n : ℕ} {A : Type} (f : Fin n → A) (i : Fin n) :
      (Vector.ofFn f).get i = f i := by
    simp [Vector.get]
    exact congrArg f (Fin.ext rfl)
  simp only [Layout.incident, Layout.ofCells, get]

variable {X C : Type} [TopologicalSpace X]

/-- The specification relates only finite data to subsets of the original
    space. The frontier test must classify the entire target cell. -/
structure Valid (a : Layout C) (carrier : C → Set X) (S : Set X) : Prop where
  closed : IsClosed S
  cover : ∀ x, x ∈ S ↔ ∃ i : Fin a.cells.length, x ∈ carrier (a.cells.get i)
  unique : ∀ x i j, x ∈ carrier (a.cells.get i) → x ∈ carrier (a.cells.get j) → i = j
  nonempty : ∀ i : Fin a.cells.length, (carrier (a.cells.get i)).Nonempty
  locallyClosed : ∀ i : Fin a.cells.length, IsLocallyClosed (carrier (a.cells.get i))
  contractible : ∀ i : Fin a.cells.length, ContractibleSpace (carrier (a.cells.get i))
  frontier_correct : ∀ (i j : Fin a.cells.length) x, x ∈ carrier (a.cells.get j) →
    (a.incident i j = true ↔ x ∈ closure (carrier (a.cells.get i)))

namespace Valid

variable {a : Layout C} {carrier : C → Set X} {S : Set X}

theorem connected (h : Valid a carrier S) (i : Fin a.cells.length) :
    IsPreconnected (carrier (a.cells.get i)) := by
  let := h.contractible i
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance

theorem closure_eq (h : Valid a carrier S) (i : Fin a.cells.length) :
    closure (carrier (a.cells.get i)) =
      ⋃ j : {j // a.incident i j = true}, carrier (a.cells.get j.val) := by
  have incl : closure (carrier (a.cells.get i)) ⊆ S :=
    closure_minimal (fun x hx => (h.cover x).mpr ⟨i, hx⟩) h.closed
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := (h.cover x).mp (incl hx)
    exact mem_iUnion.mpr ⟨⟨j, (h.frontier_correct i j x hj).mpr hx⟩, hj⟩
  · intro hx
    obtain ⟨⟨j, hij⟩, hj⟩ := mem_iUnion.mp hx
    exact (h.frontier_correct i j x hj).mp hij

private def frontierGraph (a : Layout C) : SimpleGraph (Fin a.cells.length) where
  Adj i j := a.edge i j = true
  symm := ⟨fun i j => by simp [Layout.edge, ne_comm, Bool.or_comm]⟩
  loopless := ⟨fun i => by simp [Layout.edge]⟩

private theorem reachable (h : Valid a carrier S) (i j : Fin a.cells.length) :
    (frontierGraph a).Reachable i j ↔
      (ClosureComponents.graph (fun k => carrier (a.cells.get k))).Reachable i j := by
  rw [SimpleGraph.reachable_iff_reflTransGen, SimpleGraph.reachable_iff_reflTransGen]
  constructor <;> intro path
  · induction path with
    | refl => exact .refl
    | @tail k l _ hkl ih =>
      have he : k ≠ l ∧ (a.incident k l = true ∨ a.incident l k = true) := by
        simpa [frontierGraph, Layout.edge] using hkl
      refine ih.tail ⟨he.1, ?_⟩
      rcases he.2 with hk | hl
      · obtain ⟨x, hx⟩ := h.nonempty l
        exact ⟨x, (h.frontier_correct k l x hx).mp hk, subset_closure hx⟩
      · obtain ⟨x, hx⟩ := h.nonempty k
        exact ⟨x, subset_closure hx, (h.frontier_correct l k x hx).mp hl⟩
  · induction path with
    | refl => exact .refl
    | @tail k l _ hkl ih =>
      obtain ⟨x, hx, hx'⟩ := hkl.2
      rw [h.closure_eq k] at hx
      obtain ⟨⟨m, hm⟩, hxm⟩ := mem_iUnion.mp hx
      have hm' := (h.frontier_correct l m x hxm).mpr hx'
      have adj {u v : Fin a.cells.length} (h : u ≠ v)
          (hr : a.incident u v = true ∨ a.incident v u = true) :
          (frontierGraph a).Adj u v := by
        change a.edge u v = true
        simp [Layout.edge, h, hr]
      have hm₁ : Relation.ReflTransGen (frontierGraph a).Adj k m := by
        by_cases he : k = m
        · subst m
          exact .refl
        · exact .single (adj he (Or.inl hm))
      have hm₂ : Relation.ReflTransGen (frontierGraph a).Adj m l := by
        by_cases he : m = l
        · subst m
          exact .refl
        · exact .single (adj he (Or.inr hm'))
      exact (ih.trans hm₁).trans hm₂

theorem component_correct (h : Valid a carrier S) (i : Fin a.cells.length)
    {x : X} (hx : x ∈ carrier (a.cells.get i)) :
    connectedComponentIn S x =
      ⋃ j : {j // a.labels.get i = a.labels.get j}, carrier (a.cells.get j.val) := by
  have eq j : a.labels.get i = a.labels.get j ↔
      (ClosureComponents.graph (fun k => carrier (a.cells.get k))).Reachable i j :=
    (ClosureComponents.ClosureIncidence.computeLabels_correct (frontierGraph a) a.edge
      (fun _ _ => Iff.rfl) i j).trans (h.reachable i j)
  exact ClosureComponents.connectedComponentIn_eq_cells h.closed h.cover h.connected i hx _ eq

end Valid
end CertifiedTopology.TopologyArtifact
