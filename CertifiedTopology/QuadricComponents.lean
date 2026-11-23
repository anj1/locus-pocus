module

public import CertifiedTopology.QuadricIntersection
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

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
def closureGraph (cs : List Cell) : SimpleGraph (Fin cs.length) where
  Adj i j := i ≠ j ∧ (closure (cs.get i).carrier ∩ closure (cs.get j).carrier).Nonempty
  symm := ⟨fun _ _ h => ⟨h.1.symm, inter_comm _ _ ▸ h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The union of the cells in a graph component is the actual connected
    component. The proof uses a finite closed cover by cell closures. -/
theorem connectedComponentIn_eq_closures {cs : List Cell} {S : Set Space}
    (hclosed : IsClosed S)
    (hcover : ∀ x, x ∈ S ↔ ∃ j : Fin cs.length, x ∈ (cs.get j).carrier)
    (hconn : ∀ j : Fin cs.length, ContractibleSpace (cs.get j).carrier)
    (i : Fin cs.length) :
    connectedComponentIn S (cs.get i).sample =
      ⋃ j : {j // (closureGraph cs).Reachable i j}, closure (cs.get j.val).carrier := by
  classical
  let G := closureGraph cs
  let C := fun j : Fin cs.length => closure (cs.get j).carrier
  let x := (cs.get i).sample
  let U := ⋃ j : {j // G.Reachable i j}, C j.val
  let V := ⋃ j : {j // ¬ G.Reachable i j}, C j.val
  change connectedComponentIn S x = U
  have hsub (j : Fin cs.length) : C j ⊆ S :=
    closure_minimal (fun _ hp => (hcover _).mpr ⟨j, hp⟩) hclosed
  have hx : x ∈ C i := subset_closure (cs.get i).sample_mem
  have pc (j : Fin cs.length) : IsPreconnected (C j) := by
    let := hconn j
    exact isPreconnected_iff_preconnectedSpace.mpr inferInstance |>.closure
  have hreach (j : Fin cs.length) (h : G.Reachable i j) :
      C j ⊆ connectedComponentIn S x := by
    rw [SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact (pc i).subset_connectedComponentIn hx (hsub i)
    | @tail a b _ hab ih =>
      obtain ⟨y, hya, hyb⟩ := hab.2
      rw [connectedComponentIn_eq (ih hya)]
      exact (pc b).subset_connectedComponentIn hyb (hsub b)
  apply Subset.antisymm
  · have hU : IsClosed U := isClosed_iUnion_of_finite fun _ => isClosed_closure
    have hV : IsClosed V := isClosed_iUnion_of_finite fun _ => isClosed_closure
    have dj : Disjoint U V := by
      refine disjoint_left.mpr fun y hyu hyv => ?_
      obtain ⟨⟨j, hj⟩, hyj⟩ := mem_iUnion.mp hyu
      obtain ⟨⟨k, hk⟩, hyk⟩ := mem_iUnion.mp hyv
      by_cases eq : j = k
      · exact hk (eq ▸ hj)
      · exact hk (hj.trans (SimpleGraph.Adj.reachable (G := G) ⟨eq, y, hyj, hyk⟩))
    have huv : S ⊆ U ∪ V := by
      intro y hy
      obtain ⟨j, hj⟩ := (hcover y).mp hy
      by_cases e : G.Reachable i j
      · exact Or.inl (mem_iUnion.mpr ⟨⟨j,e⟩, subset_closure hj⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨j,e⟩, subset_closure hj⟩)
    have xu : x ∈ U := mem_iUnion.mpr ⟨⟨i, SimpleGraph.Reachable.refl i⟩, hx⟩
    have xS := hsub i hx
    intro y hy
    by_contra hyu
    have hyV : y ∈ V :=
      (huv (connectedComponentIn_subset S x hy)).resolve_left hyu
    have hn := isPreconnected_closed_iff.mp isPreconnected_connectedComponentIn
      U V hU hV ((connectedComponentIn_subset S x).trans huv)
      ⟨x, mem_connectedComponentIn xS, xu⟩ ⟨y, hy, hyV⟩
    obtain ⟨z, _, hzu, hzv⟩ := hn
    exact disjoint_left.mp dj hzu hzv
  · exact iUnion_subset fun j => hreach j.val j.property

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

def merge {n : ℕ} (labels : Vector (Fin n) n) (e : Fin n × Fin n) :
    Vector (Fin n) n :=
  if labels.get e.1 = labels.get e.2 then labels
  else Vector.ofFn fun k => if labels.get k = labels.get e.2 then labels.get e.1 else labels.get k

private theorem get_ofFn {n : ℕ} {α : Type} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]
  exact congrArg f (Fin.ext rfl)

private theorem merge_old {n : ℕ} (labels : Vector (Fin n) n) (e : Fin n × Fin n)
    {i j : Fin n} (h : labels.get i = labels.get j) :
    (merge labels e).get i = (merge labels e).get j := by
  simp only [merge]
  split <;> simp only [get_ofFn, h]

private theorem merge_edge {n : ℕ} (labels : Vector (Fin n) n) (e : Fin n × Fin n) :
    (merge labels e).get e.1 = (merge labels e).get e.2 := by
  simp only [merge]
  split <;> simp_all [get_ofFn]

private theorem merge_sound {n : ℕ} {G : SimpleGraph (Fin n)} (labels : Vector (Fin n) n)
    (e : Fin n × Fin n) (he : G.Adj e.1 e.2)
    (sound : ∀ i j, labels.get i = labels.get j → G.Reachable i j)
    {i j : Fin n} (h : (merge labels e).get i = (merge labels e).get j) :
    G.Reachable i j := by
  simp only [merge] at h
  split at h
  · exact sound i j h
  · simp only [get_ofFn] at h
    split_ifs at h with hi hj hj
    · exact sound i j (hi.trans hj.symm)
    · exact (sound i e.2 hi).trans (he.reachable.symm.trans (sound e.1 j h))
    · exact (sound i e.1 h).trans (he.reachable.trans (sound e.2 j hj.symm))
    · exact sound i j h

def edges {n : ℕ} (edge : Fin n → Fin n → Bool) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter (edge i)).map (fun j => (i, j))

private theorem mem_edges (d : ClosureIncidence cs) (e : Fin cs.length × Fin cs.length) :
    e ∈ edges d.edge ↔ (Cell.closureGraph cs).Adj e.1 e.2 := by
  rcases e with ⟨i,j⟩
  simp [edges, List.mem_flatMap, d.correct]

/-- Merge labels once per edge. This computes components from the checked
    incidence matrix without enumerating graph walks. -/
def computeLabels {n : ℕ} (edge : Fin n → Fin n → Bool) : Vector (Fin n) n :=
  (edges edge).foldl merge (Vector.ofFn id)

def labels (d : ClosureIncidence cs) : Vector (Fin cs.length) cs.length := computeLabels d.edge

private theorem fold_sound {n : ℕ} {G : SimpleGraph (Fin n)}
    (es : List (Fin n × Fin n)) (valid : ∀ e ∈ es, G.Adj e.1 e.2)
    (initial : Vector (Fin n) n)
    (sound : ∀ i j, initial.get i = initial.get j → G.Reachable i j) :
    ∀ i j, (es.foldl merge initial).get i = (es.foldl merge initial).get j → G.Reachable i j := by
  induction es generalizing initial with
  | nil => exact sound
  | cons e es ih =>
    exact ih (fun e h => valid e (List.mem_cons_of_mem _ h)) _
      (fun i j h => merge_sound initial e (valid e (by simp)) sound h)

private theorem fold_preserves {n : ℕ} (es : List (Fin n × Fin n))
    (initial : Vector (Fin n) n) {i j : Fin n} (h : initial.get i = initial.get j) :
    (es.foldl merge initial).get i = (es.foldl merge initial).get j := by
  induction es generalizing initial with
  | nil => exact h
  | cons e es ih => exact ih _ (merge_old initial e h)

private theorem fold_merges {n : ℕ} (es : List (Fin n × Fin n))
    (initial : Vector (Fin n) n) (e : Fin n × Fin n) (he : e ∈ es) :
    (es.foldl merge initial).get e.1 = (es.foldl merge initial).get e.2 := by
  induction es generalizing initial with
  | nil => simp at he
  | cons f es ih =>
    rcases List.mem_cons.mp he with rfl | h
    · exact fold_preserves es _ (merge_edge initial e)
    · exact ih _ h

theorem same_label (d : ClosureIncidence cs) (i j : Fin cs.length) :
    d.labels.get i = d.labels.get j ↔ (Cell.closureGraph cs).Reachable i j := by
  constructor
  · unfold labels computeLabels
    apply fold_sound (edges d.edge) (fun _ h => (d.mem_edges _).mp h)
      (Vector.ofFn id) _ i j
    intro a b h
    have : a = b := by simpa only [get_ofFn, id_eq] using h
    subst b
    exact SimpleGraph.Reachable.refl a
  · rw [SimpleGraph.reachable_iff_reflTransGen]
    intro h
    induction h with
    | refl => rfl
    | @tail a b _ hab ih =>
      exact ih.trans (fold_merges (edges d.edge) (Vector.ofFn id) (a,b) ((d.mem_edges _).mpr hab))

/-- The cells with the same label partition the connected component of the
    chosen sample. This includes cells at shared limit points. -/
theorem component_correct (q r : Equation ℝ)
    (p : Plane.Diagram (program q r).projection) (d : ClosureIncidence (solve q r p))
    (i : Fin (solve q r p).length) :
    connectedComponentIn (locus q r) ((solve q r p).get i).sample =
      ⋃ j : {j // d.labels.get i = d.labels.get j}, ((solve q r p).get j.val).carrier := by
  let cells := solve q r p
  let G := Cell.closureGraph cells
  have cover (x : Space) : x ∈ locus q r ↔ ∃ j : Fin cells.length, x ∈ (cells.get j).carrier :=
    (solve_correct q r p x).symm.trans List.exists_mem_iff_get
  rw [Cell.connectedComponentIn_eq_closures (isClosed_locus q r)
    cover (fun j => solve_contractible q r p (List.get_mem ..)) i]
  ext x
  simp only [mem_iUnion, Subtype.exists, exists_prop, d.same_label]
  constructor
  · rintro ⟨j, hj, hx⟩
    have sub : closure (cells.get j).carrier ⊆ locus q r :=
      closure_minimal (fun _ h => (cover _).mpr ⟨j, h⟩) (isClosed_locus q r)
    obtain ⟨k, hk⟩ := (cover x).mp (sub hx)
    refine ⟨k, hj.trans ?_, hk⟩
    by_cases eq : j = k
    · subst k
      exact SimpleGraph.Reachable.refl j
    · exact SimpleGraph.Adj.reachable (G := G) ⟨eq, x, hx, subset_closure hk⟩
  · rintro ⟨j, hj, hx⟩
    exact ⟨j, hj, subset_closure hx⟩

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
