module

public import CertifiedTopology.ComputableCAD

@[expose] public section

namespace CertifiedTopology.CADDecision

open ExecutableIsolation

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
variable {model : RealModel K}

inductive SignFormula (K : Type) [Field K] [LinearOrder K] (n : ℕ)
  | truth (value : Bool)
  | atom (poly : Multi K n) (sign : Side)
  | not (f : SignFormula K n)
  | and (f g : SignFormula K n)
  | or (f g : SignFormula K n)

namespace SignFormula

def inputs : SignFormula K n → List (Multi K n)
  | .truth _ => []
  | .atom p _ => [p]
  | .not f => f.inputs
  | .and f g | .or f g => f.inputs ++ g.inputs

def decision (c : ComputableCAD.Cell model n) : SignFormula K n → Bool
  | .truth b => b
  | .atom p s => c.sign p == s
  | .not f => !(decision c f)
  | .and f g => decision c f && decision c g
  | .or f g => decision c f || decision c g

def holds (model : RealModel K) (x : Fin n → ℝ) : SignFormula K n → Prop
  | .truth b => b = true
  | .atom p s => side (Multi.evalHom model.hom x p) 0 = s
  | .not f => ¬holds model x f
  | .and f g => holds model x f ∧ holds model x g
  | .or f g => holds model x f ∨ holds model x g

theorem decision_correct (f : SignFormula K n) (c : ComputableCAD.Cell model n) {x : Fin n → ℝ}
    (h : c.Invariant f.inputs) (hx : x ∈ c.carrier) :
    f.decision c = true ↔ f.holds model x := by
  induction f with
  | truth b => rfl
  | atom p s =>
    simp only [decision, holds, beq_iff_eq]
    rw [h x hx p (by simp [inputs])]
  | not f ih =>
    cases he : decision c f with
    | true => simp [decision, holds, he, (ih h).mp he]
    | false =>
      have n : ¬f.holds model x := fun hp => Bool.false_ne_true (he.symm.trans ((ih h).mpr hp))
      simp [decision, holds, he, n]
  | and f g ih jh =>
    rw [decision, Bool.and_eq_true, holds]
    exact and_congr (ih (fun y hy p hp => h y hy p (List.mem_append_left _ hp)))
      (jh (fun y hy p hp => h y hy p (List.mem_append_right _ hp)))
  | or f g ih jh =>
    rw [decision, Bool.or_eq_true, holds]
    exact or_congr (ih (fun y hy p hp => h y hy p (List.mem_append_left _ hp)))
      (jh (fun y hy p hp => h y hy p (List.mem_append_right _ hp)))

end SignFormula

/-- Quantified variables are appended in cylindrical order. The matrix is
    a Boolean combination of exact polynomial sign tests. -/
inductive Prenex (K : Type) [Field K] [LinearOrder K] : ℕ → Type
  | matrix {n : ℕ} (f : SignFormula K n) : Prenex K n
  | exists_ {n : ℕ} (f : Prenex K (n+1)) : Prenex K n
  | forall_ {n : ℕ} (f : Prenex K (n+1)) : Prenex K n

namespace Prenex

def projection : {n : ℕ} → Prenex K n → List (Multi K n)
  | _, .matrix f => f.inputs
  | _, .exists_ f | _, .forall_ f => ComputableCAD.project (projection f)

def holds (model : RealModel K) : {n : ℕ} → (Fin n → ℝ) → Prenex K n → Prop
  | _, x, .matrix f => f.holds model x
  | _, x, .exists_ f => ∃ y : ℝ, holds model (Fin.snoc x y) f
  | _, x, .forall_ f => ∀ y : ℝ, holds model (Fin.snoc x y) f

theorem originInvariant (f : Prenex K 0) : (ComputableCAD.origin model).Invariant f.projection := by
  intro x _ p _
  rw [ComputableCAD.Cell.sign_correct]
  have eq : x = (ComputableCAD.origin model).sample.value := by ext i; exact i.elim0
  rw [eq]

/-- Store the projected tests once at each quantifier level. The same
    compiled subtree is applied to every cell in a stack. -/
structure EvaluationPlan (model : RealModel K) (f : Prenex K n) where
  tests : List (Multi K n)
  specification : tests = f.projection
  evaluate (c : ComputableCAD.Cell model n) (h : c.Invariant tests) : Bool
  correct : ∀ c h x, (hx : x ∈ c.carrier) → evaluate c h = true ↔ f.holds model x

def compile (model : RealModel K) : {n : ℕ} → (f : Prenex K n) → EvaluationPlan model f
  | _, .matrix f => ⟨f.inputs, rfl, fun c _ => f.decision c, fun c h x hx => f.decision_correct c (x := x) h hx⟩
  | _, .exists_ f => by
    let plan := compile model f
    let tests := ComputableCAD.project plan.tests
    let go (c : ComputableCAD.Cell model _) (inv : c.Invariant tests) :=
      let rows := ComputableCAD.lift c plan.tests inv
      rows.cells.attach.any fun a => plan.evaluate a.val (rows.invariant _ a.property)
    refine ⟨tests, congrArg ComputableCAD.project plan.specification, go, ?_⟩
    intro c h x hx
    let rows := ComputableCAD.lift c plan.tests h
    change (rows.cells.attach.any _ = true) ↔ ∃ y : ℝ, f.holds model (Fin.snoc x y)
    rw [List.any_eq_true]
    constructor
    · rintro ⟨a,_,ha⟩
      obtain ⟨y,hy⟩ := rows.surjects a.val a.property x hx
      exact ⟨y,(plan.correct a.val (rows.invariant _ a.property) _ hy).mp ha⟩
    · rintro ⟨y,hy⟩
      obtain ⟨a,ha,hc⟩ := (rows.partition x hx y).exists
      exact ⟨⟨a,ha⟩,List.mem_attach _ _,(plan.correct a (rows.invariant _ ha) _ hc).mpr hy⟩
  | _, .forall_ f => by
    let plan := compile model f
    let tests := ComputableCAD.project plan.tests
    let go (c : ComputableCAD.Cell model _) (inv : c.Invariant tests) :=
      let rows := ComputableCAD.lift c plan.tests inv
      rows.cells.attach.all fun a => plan.evaluate a.val (rows.invariant _ a.property)
    refine ⟨tests, congrArg ComputableCAD.project plan.specification, go, ?_⟩
    intro c h x hx
    let rows := ComputableCAD.lift c plan.tests h
    change (rows.cells.attach.all _ = true) ↔ ∀ y : ℝ, f.holds model (Fin.snoc x y)
    rw [List.all_eq_true]
    constructor
    · intro hs y
      obtain ⟨a,ha,hc⟩ := (rows.partition x hx y).exists
      exact (plan.correct a (rows.invariant _ ha) _ hc).mp (hs ⟨a,ha⟩ (List.mem_attach _ _))
    · intro hs a _
      obtain ⟨y,hy⟩ := rows.surjects a.val a.property x hx
      exact (plan.correct a.val (rows.invariant _ a.property) _ hy).mpr (hs y)

def decideSentence (model : RealModel K) (f : Prenex K 0) : Bool :=
  let plan := compile model f
  plan.evaluate (ComputableCAD.origin model) (plan.specification.symm ▸ f.originInvariant)

theorem decideSentence_correct (model : RealModel K) (f : Prenex K 0) :
    decideSentence model f = true ↔ f.holds model Fin.elim0 :=
  (compile model f).correct (ComputableCAD.origin model) _ _ (Set.mem_univ _)

/-- Compute the cells where a formula with free coordinates holds. -/
def regions (model : RealModel K) (f : Prenex K n) : List (ComputableCAD.Cell model n) :=
  let plan := compile model f
  let d := ComputableCAD.cad model n plan.tests
  d.cells.attach.filterMap fun c =>
    if plan.evaluate c.val (d.invariant _ c.property) then some c.val else none

theorem regions_correct (model : RealModel K) (f : Prenex K n) (x : Fin n → ℝ) :
    f.holds model x ↔ ∃ c ∈ regions model f, x ∈ c.carrier := by
  let plan := compile model f
  let d := ComputableCAD.cad model n plan.tests
  constructor
  · intro hx
    obtain ⟨c,⟨hc,hm⟩,_⟩ := d.partition x
    have yes := (plan.correct c (d.invariant _ hc) _ hm).mpr hx
    refine ⟨c,List.mem_filterMap.mpr ⟨⟨c,hc⟩,List.mem_attach _ _,?_⟩,hm⟩
    exact if_pos yes
  · rintro ⟨c,hc,hm⟩
    obtain ⟨a,_,hf⟩ := List.mem_filterMap.mp hc
    change (if plan.evaluate a.val (d.invariant _ a.property) then some a.val else none) = some c at hf
    split at hf
    · rename_i yes
      have eq := Option.some.inj hf
      exact (plan.correct a.val (d.invariant _ a.property) _ (eq.symm ▸ hm)).mp yes
    · contradiction

end Prenex
end CertifiedTopology.CADDecision
