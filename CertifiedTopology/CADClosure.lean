module

public import CertifiedTopology.CellFormula
public import CertifiedTopology.ClosureComponents
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

@[expose] public section

namespace CertifiedTopology.CADDecision

open Set ExecutableIsolation CylindricalData

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n m : ℕ}

def existsVector (m : ℕ) : (k : ℕ) → Prenex K (m+k) → Prenex K m
  | 0, f => f
  | k+1, f => existsVector m k (.exists_ f)

theorem existsVector_correct (model : RealModel K) (x : Fin m → ℝ) :
    (k : ℕ) → (f : Prenex K (m+k)) →
    (existsVector m k f).holds model x ↔ ∃ y : Fin k → ℝ, f.holds model (Fin.append x y)
  | 0, f => by
    have e (y : Fin 0 → ℝ) : Fin.append x y = x := by funext i; exact Fin.append_left x y i
    simp only [existsVector, e]
    exact ⟨fun h => ⟨Fin.elim0,h⟩, fun ⟨_,h⟩ => h⟩
  | k+1, f => by
    rw [existsVector, existsVector_correct model x k]
    constructor
    · rintro ⟨y,t,h⟩
      exact ⟨Fin.snoc y t, (Fin.append_snoc x y t).symm ▸ h⟩
    · rintro ⟨y,h⟩
      let a := CADStacks.dropLast y
      let t := CADStacks.last y
      have eta : Fin.snoc (Fin.append x a) t = Fin.append x y :=
        (Fin.append_snoc x a t).symm.trans (congrArg (Fin.append x) (CADStacks.snoc_dropLast y))
      exact ⟨a,t,eta.symm ▸ h⟩

namespace SignFormula

def all : List (SignFormula K n) → SignFormula K n
  | [] => .truth true
  | f :: fs => .and f (all fs)

theorem all_correct (model : RealModel K) (x : Fin n → ℝ) (fs : List (SignFormula K n)) :
    (all fs).holds model x ↔ ∀ f ∈ fs, f.holds model x := by
  induction fs with
  | nil => simp [all, holds]
  | cons f fs ih => simp [all, holds, ih]

end SignFormula

def proximity (n : ℕ) : SignFormula K (n+1+n) :=
  let eps := Multi.coordinate (Fin.castAdd n (Fin.last n))
  .all <| (List.finRange n).map fun i =>
    let a := Multi.coordinate (Fin.castAdd n i.castSucc)
    let b := Multi.coordinate (Fin.natAdd (n+1) i)
    .and (.atom (a - b - eps) .below) (.atom (b - a - eps) .below)

theorem proximity_correct (model : RealModel K) (x y : Fin n → ℝ) {e : ℝ} (he : 0 < e) :
    (proximity (K := K) n).holds model (Fin.append (Fin.snoc x e) y) ↔ dist x y < e := by
  rw [dist_pi_lt_iff he, proximity, SignFormula.all_correct]
  simp only [List.forall_mem_map, List.mem_finRange, true_implies, SignFormula.holds, side_below,
    map_sub, Multi.eval_coordinate, Fin.append_left, Fin.append_right,
    Fin.snoc_castSucc, Fin.snoc_last, Real.dist_eq]
  apply forall_congr'
  intro i
  rw [abs_lt]
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]

def nonpositive (n : ℕ) : SignFormula K (n+1) :=
  .not (.atom (Multi.coordinate (Fin.last n)) .above)

theorem nonpositive_correct (model : RealModel K) (x : Fin n → ℝ) (e : ℝ) :
    (nonpositive (K := K) n).holds model (Fin.snoc x e) ↔ ¬ 0 < e := by
  simp [nonpositive, SignFormula.holds, side_above]

def near (model : RealModel K) (c : Code K n) : Prenex K (n+1) :=
  existsVector (n+1) n (Prenex.matrixAnd (proximity n) ((cellFormula model c).rename (Fin.natAdd (n+1))))

theorem near_correct (model : RealModel K) (c : Code K n)
    (h : ComputableCAD.RegularCode model c) (x : Fin n → ℝ) {e : ℝ} (he : 0 < e) :
    (near model c).holds model (Fin.snoc x e) ↔ ∃ y ∈ c.carrier model, dist x y < e := by
  unfold near
  rw [existsVector_correct]
  apply exists_congr
  intro y
  rw [Prenex.matrixAnd_correct, proximity_correct model x y he, Prenex.rename_correct]
  have eta : Fin.append (Fin.snoc x e) y ∘ Fin.natAdd (n+1) = y := by
    funext i
    exact Fin.append_right (Fin.snoc x e) y i
  rw [eta, cellFormula_correct model c h]
  exact and_comm

/-- An exact first-order description of the ambient closure of a CAD cell. -/
def closureFormula (model : RealModel K) (c : Code K n) : Prenex K n :=
  .forall_ ((Prenex.matrix (nonpositive n)).either (near model c))

theorem closureFormula_correct (model : RealModel K) (c : Code K n)
    (h : ComputableCAD.RegularCode model c) (x : Fin n → ℝ) :
    (closureFormula model c).holds model x ↔ x ∈ closure (c.carrier model) := by
  rw [Metric.mem_closure_iff]
  change (∀ e : ℝ, (Prenex.either (.matrix (nonpositive n)) (near model c)).holds model (Fin.snoc x e)) ↔ _
  apply forall_congr'
  intro e
  rw [Prenex.either_correct, show (Prenex.matrix (nonpositive n) : Prenex K (n+1)).holds model
    (Fin.snoc x e) ↔ ¬ 0 < e from nonpositive_correct model x e]
  by_cases he : 0 < e
  · simpa only [he, not_true_eq_false, false_or, true_implies] using near_correct model c h x he
  · simp [he]

def overlapFormula (model : RealModel K) (a b : Code K n) : Prenex K n :=
  .forall_ ((Prenex.matrix (nonpositive n)).either ((near model a).both (near model b)))

theorem overlapFormula_correct (model : RealModel K) (a b : Code K n)
    (ha : ComputableCAD.RegularCode model a) (hb : ComputableCAD.RegularCode model b)
    (x : Fin n → ℝ) :
    (overlapFormula model a b).holds model x ↔ x ∈ closure (a.carrier model) ∩ closure (b.carrier model) := by
  simp only [mem_inter_iff, Metric.mem_closure_iff]
  change (∀ e : ℝ, (Prenex.either (.matrix (nonpositive n)) ((near model a).both (near model b))).holds
    model (Fin.snoc x e)) ↔ _
  rw [← forall_and]
  apply forall_congr'
  intro e
  rw [Prenex.either_correct, Prenex.both_correct,
    show (Prenex.matrix (nonpositive n) : Prenex K (n+1)).holds model (Fin.snoc x e) ↔ ¬ 0 < e from
      nonpositive_correct model x e, ← forall_and]
  by_cases he : 0 < e
  · simp only [he, not_true_eq_false, false_or, true_implies,
      near_correct model a ha x he, near_correct model b hb x he]
  · simp [he]

def closuresMeet (model : RealModel K) (a b : Code K n) : Bool :=
  Prenex.decideSentence model
    (existsVector 0 n ((overlapFormula model a b).rename (Fin.natAdd 0)))

theorem closuresMeet_correct (model : RealModel K) (a b : Code K n)
    (ha : ComputableCAD.RegularCode model a) (hb : ComputableCAD.RegularCode model b) :
    closuresMeet model a b = true ↔ (closure (a.carrier model) ∩ closure (b.carrier model)).Nonempty := by
  rw [closuresMeet, Prenex.decideSentence_correct, existsVector_correct]
  apply exists_congr
  intro y
  have e : Fin.append Fin.elim0 y ∘ Fin.natAdd 0 = y := by
    funext i
    exact Fin.append_right Fin.elim0 y i
  rw [Prenex.rename_correct, e, overlapFormula_correct model a b ha hb]

end CertifiedTopology.CADDecision
