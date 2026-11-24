module

public import CertifiedTopology.BoxClosures
public import CertifiedTopology.CADSets

@[expose] public section

namespace CertifiedTopology.CADDecision

open Set ExecutableIsolation CylindricalData AlgebraicRoot CADStacks

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ} {model : RealModel K}

def closedSlice (model : RealModel K) : Slice (Root model) → SignFormula K 1
  | .sectionAt r => isolatedCut model r .on
  | .sector l u =>
    (l.elim (.truth true) fun r => (isolatedCut model r .below).not).and
      (u.elim (.truth true) fun r => (isolatedCut model r .above).not)

theorem closedSlice_correct (model : RealModel K) (s : Slice (Root model)) (x : Fin 1 → ℝ) :
    (closedSlice model s).holds model x ↔ x 0 ∈ closedInterval (mapSlice Root.value s) := by
  cases s with
  | sectionAt r =>
    rw [closedSlice,isolatedCut_correct,side_on,sub_eq_zero]
    simp only [mapSlice,closedInterval,mem_ofPred_eq,low,high,Option.mem_some,forall_eq']
    exact ⟨fun h => h ▸ ⟨le_rfl,le_rfl⟩,fun h => le_antisymm h.2 h.1⟩
  | sector l u =>
    cases l <;> cases u <;> simp [closedSlice, SignFormula.holds.eq_4, SignFormula.holds.eq_3,
      SignFormula.holds.eq_1,isolatedCut_correct,side_below,side_above,sub_neg,sub_pos,mapSlice,
      closedInterval,low,high]

namespace Box

def describe (model : RealModel K) (closed : Bool) : {n : ℕ} → Box model n → SignFormula K n
  | 0, .origin => .truth true
  | n+1, .lift b s =>
    let height := if closed then closedSlice model s else isolatedSlice model s
    .and ((describe model closed b).rename Fin.castSucc) (height.rename (fun _ => Fin.last n))

theorem describe_correct (model : RealModel K) :
    {n : ℕ} → (b : Box model n) → (x : Fin n → ℝ) →
    (describe model false b).holds model x ↔ x ∈ carrier model b
  | 0, .origin, _ => by simp [describe,SignFormula.holds,carrier]
  | n+1, .lift b s, x => by
    simp only [describe, Bool.false_eq_true,ite_false,SignFormula.holds.eq_4]
    rw [SignFormula.rename_correct,SignFormula.rename_correct,isolatedSlice_correct,describe_correct model b]
    rfl

theorem describe_closed_correct (model : RealModel K) :
    {n : ℕ} → (b : Box model n) → (h : (carrier model b).Nonempty) → (x : Fin n → ℝ) →
    (describe model true b).holds model x ↔ x ∈ closure (carrier model b)
  | 0, .origin, _, _ => by simp [describe,SignFormula.holds,carrier]
  | n+1, .lift b s, ⟨p,hp⟩, x => by
    simp only [describe,ite_true,SignFormula.holds.eq_4]
    rw [SignFormula.rename_correct,SignFormula.rename_correct,closedSlice_correct,
      describe_closed_correct model b ⟨dropLast p,hp.1⟩,closure_lift,
      closedInterval_eq _ ⟨last p,hp.2⟩]
    rfl

end Box

def describeCell (c : ComputableCAD.Cell model n) : Prenex K n :=
  match Box.fromCode model c.code with
  | none => cellFormula model c.code
  | some b => .matrix (b.describe model false)

theorem describeCell_correct (c : ComputableCAD.Cell model n) :
    (describeCell c).carrier model = c.carrier := by
  unfold describeCell
  split
  · ext x
    exact cellFormula_correct model c.code c.regular x
  · rename_i b h
    ext x
    exact (Box.describe_correct model b x).trans (Iff.of_eq (congrArg (x ∈ ·)
      (Box.fromCode_correct model c.code c.regular b h)))

def describeCellClosure (c : ComputableCAD.Cell model n) : Prenex K n :=
  match Box.fromCode model c.code with
  | none => closureFormula model c.code
  | some b => .matrix (b.describe model true)

theorem describeCellClosure_correct (c : ComputableCAD.Cell model n) :
    (describeCellClosure c).carrier model = closure c.carrier := by
  unfold describeCellClosure
  split
  · ext x
    exact closureFormula_correct model c.code c.regular x
  · rename_i b h
    have e := Box.fromCode_correct model c.code c.regular b h
    have ne : (Box.carrier model b).Nonempty := e.symm ▸ ⟨c.sample.value,c.sample_mem⟩
    ext x
    exact (Box.describe_closed_correct model b ne x).trans (Iff.of_eq (congrArg (x ∈ closure ·) e))

def closureFromCells (model : RealModel K) (f : Prenex K n) : Prenex K n :=
  Prenex.union ((f.regions model).map describeCellClosure)

theorem closureFromCells_correct (model : RealModel K) (f : Prenex K n) :
    (closureFromCells model f).carrier model = closure (f.carrier model) := by
  let cs := f.regions model
  let C := fun i : Fin cs.length => (cs.get i).carrier
  have covered : f.carrier model = ⋃ i, C i := by
    ext x
    rw [mem_iUnion]
    exact (f.regions_correct model x).trans ⟨fun ⟨c,hc,hx⟩ => by
      obtain ⟨i,rfl⟩ := List.get_of_mem hc
      exact ⟨i,hx⟩,fun ⟨i,hi⟩ => ⟨cs.get i,List.get_mem _ _,hi⟩⟩
  have eq : (closureFromCells model f).carrier model = ⋃ i, closure (C i) := by
    ext x
    simp only [closureFromCells,Prenex.carrier_union,mem_iUnion,exists_prop,List.mem_map]
    constructor
    · rintro ⟨_,⟨c,hc,rfl⟩,hx⟩
      obtain ⟨i,rfl⟩ := List.get_of_mem hc
      rw [describeCellClosure_correct] at hx
      exact ⟨i,hx⟩
    · rintro ⟨i,hx⟩
      refine ⟨_,⟨cs.get i,List.get_mem _ _,rfl⟩,?_⟩
      rw [describeCellClosure_correct]
      exact hx
  rw [eq,covered]
  apply Subset.antisymm
  · exact iUnion_subset fun i => closure_mono (subset_iUnion C i)
  · apply closure_minimal
    · exact iUnion_mono fun i => subset_closure
    · exact isClosed_iUnion_of_finite fun i => isClosed_closure

/-- Fixed-coordinate charts let the closure of a quantifier-free set
    reuse exact interval bounds. Other formulas use the metric definition. -/
def describeClosure (model : RealModel K) (f : Prenex K n) : Prenex K n :=
  match f with
  | .matrix _ =>
    let cs := f.regions model
    if cs.all (fun c => (Box.fromCode model c.code).isSome) then
      Prenex.union (cs.map describeCellClosure)
    else f.closure
  | _ => f.closure

theorem describeClosure_correct (model : RealModel K) (f : Prenex K n) :
    (describeClosure model f).carrier model = closure (f.carrier model) := by
  cases f with
  | matrix g =>
    unfold describeClosure
    dsimp only
    split
    · exact closureFromCells_correct model (.matrix g)
    · exact Prenex.carrier_closure model (.matrix g)
  | exists_ g => exact Prenex.carrier_closure model (.exists_ g)
  | forall_ g => exact Prenex.carrier_closure model (.forall_ g)

end CertifiedTopology.CADDecision
