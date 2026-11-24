module

public import CertifiedTopology.CADDimension

@[expose] public section

namespace CertifiedTopology.CADDecision

open Set ExecutableIsolation

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

namespace Prenex

def carrier (model : RealModel K) (f : Prenex K n) : Set (Fin n → ℝ) :=
  {x | f.holds model x}

def empty : Prenex K n := .matrix (.truth false)

@[simp] theorem carrier_empty (model : RealModel K) : (empty : Prenex K n).carrier model = ∅ := by
  ext x
  simp [carrier,empty,holds,SignFormula.holds]

@[simp] theorem carrier_both (model : RealModel K) (a b : Prenex K n) :
    (a.both b).carrier model = a.carrier model ∩ b.carrier model := by
  ext x
  exact both_correct model a b x

@[simp] theorem carrier_neg (model : RealModel K) (a : Prenex K n) :
    a.neg.carrier model = (a.carrier model)ᶜ := by
  ext x
  exact neg_correct model a x

@[simp] theorem carrier_either (model : RealModel K) (a b : Prenex K n) :
    (a.either b).carrier model = a.carrier model ∪ b.carrier model := by
  ext x
  exact either_correct model a b x

def union : List (Prenex K n) → Prenex K n
  | [] => empty
  | f :: fs => f.either (union fs)

theorem carrier_union (model : RealModel K) (fs : List (Prenex K n)) :
    (union fs).carrier model = ⋃ f ∈ fs, f.carrier model := by
  ext x
  simp only [mem_iUnion,exists_prop]
  induction fs with
  | nil => simp [union]
  | cons f fs ih =>
    rw [union,carrier_either,mem_union,ih]
    exact ⟨fun h => h.elim (fun hx => ⟨f,by simp,hx⟩)
      (fun ⟨g,hg,hx⟩ => ⟨g,List.mem_cons_of_mem _ hg,hx⟩),
      fun ⟨g,hg,hx⟩ => (List.mem_cons.mp hg).elim (fun e => Or.inl (e ▸ hx))
        (fun hm => Or.inr ⟨g,hm,hx⟩)⟩

def subtract (a b : Prenex K n) : Prenex K n := a.both b.neg

@[simp] theorem carrier_subtract (model : RealModel K) (a b : Prenex K n) :
    (a.subtract b).carrier model = a.carrier model \ b.carrier model := by
  rw [subtract,carrier_both,carrier_neg]
  rfl

def nearForm (f : Prenex K n) : Prenex K (n+1) :=
  existsVector (n+1) n (matrixAnd (proximity n) (f.rename (Fin.natAdd (n+1))))

theorem nearForm_correct (model : RealModel K) (f : Prenex K n) (x : Fin n → ℝ) {e : ℝ}
    (he : 0 < e) :
    f.nearForm.holds model (Fin.snoc x e) ↔ ∃ y ∈ f.carrier model, dist x y < e := by
  rw [nearForm, existsVector_correct]
  apply exists_congr
  intro y
  rw [matrixAnd_correct, proximity_correct model x y he,rename_correct]
  have eq : Fin.append (Fin.snoc x e) y ∘ Fin.natAdd (n+1) = y := by
    funext i
    exact Fin.append_right (Fin.snoc x e) y i
  rw [eq]
  exact and_comm

def closure (f : Prenex K n) : Prenex K n :=
  .forall_ ((Prenex.matrix (nonpositive n)).either f.nearForm)

@[simp] theorem carrier_closure (model : RealModel K) (f : Prenex K n) :
    f.closure.carrier model = _root_.closure (f.carrier model) := by
  ext x
  rw [Metric.mem_closure_iff]
  change (∀ e : ℝ, (Prenex.either (.matrix (nonpositive n)) f.nearForm).holds model (Fin.snoc x e)) ↔ _
  apply forall_congr'
  intro e
  rw [either_correct, show (Prenex.matrix (nonpositive n) : Prenex K (n+1)).holds model
    (Fin.snoc x e) ↔ ¬ 0 < e from nonpositive_correct model x e]
  by_cases he : 0 < e
  · simpa only [he, not_true_eq_false, false_or, true_implies] using f.nearForm_correct model x he
  · simp [he]

def boundary (f : Prenex K n) : Prenex K n := f.closure.subtract f

@[simp] theorem carrier_boundary (model : RealModel K) (f : Prenex K n) :
    f.boundary.carrier model = _root_.closure (f.carrier model) \ f.carrier model := by
  simp [boundary]

def hasPoint (model : RealModel K) (f : Prenex K n) : Bool :=
  decideSentence model (existsVector 0 n (f.rename (Fin.natAdd 0)))

theorem hasPoint_correct (model : RealModel K) (f : Prenex K n) :
    f.hasPoint model = true ↔ (f.carrier model).Nonempty := by
  rw [hasPoint,decideSentence_correct,existsVector_correct]
  apply exists_congr
  intro x
  have e : Fin.append Fin.elim0 x ∘ Fin.natAdd 0 = x := by
    funext i
    exact Fin.append_right Fin.elim0 x i
  rw [rename_correct,e]
  rfl

def inside (model : RealModel K) (a b : Prenex K n) : Bool :=
  !((a.subtract b).hasPoint model)

theorem inside_correct (model : RealModel K) (a b : Prenex K n) :
    a.inside model b = true ↔ a.carrier model ⊆ b.carrier model := by
  unfold inside
  rw [Bool.not_eq_true', ← Bool.not_eq_true, hasPoint_correct, carrier_subtract, not_nonempty_iff_eq_empty,
    sdiff_eq_empty]

end Prenex

theorem nodup_filterMap {A B : Type*} (xs : List A) (f : A → Option B) (hn : xs.Nodup)
    (inj : ∀ a ∈ xs, ∀ b ∈ xs, ∀ c, f a = some c → f b = some c → a = b) :
    (xs.filterMap f).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have h := ih (List.nodup_cons.mp hn).2 (fun p hp q hq c =>
      inj p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq) c)
    cases e : f a with
    | none => simpa [List.filterMap_cons,e] using h
    | some c =>
      rw [List.filterMap_cons,e,List.nodup_cons]
      refine ⟨?_,h⟩
      intro hx
      obtain ⟨b,hb,hc⟩ := List.mem_filterMap.mp hx
      have eq := inj a (by simp) b (List.mem_cons_of_mem _ hb) c e hc
      exact (List.nodup_cons.mp hn).1 (eq.symm ▸ hb)

structure Classification (model : RealModel K) (f : Prenex K n) (constraints : List (Prenex K n)) where
  cells : List (ComputableCAD.Cell model n)
  nodup : cells.Nodup
  cover : ∀ x, x ∈ f.carrier model ↔ ∃! c, c ∈ cells ∧ x ∈ c.carrier
  contained : ∀ c ∈ cells, c.carrier ⊆ f.carrier model
  compatible : ∀ c ∈ cells, ∀ g ∈ constraints, c.carrier ⊆ g.carrier model ∨ Disjoint c.carrier (g.carrier model)

def classify (model : RealModel K) (f : Prenex K n) (constraints : List (Prenex K n)) :
    Classification model f constraints := by
  let plan := f.compile model
  let d := ComputableCAD.cad model n (plan.tests ++ constraints.flatMap Prenex.projection)
  let inv (c : {c // c ∈ d.cells}) : c.val.Invariant plan.tests :=
    fun x hx p hp => d.invariant _ c.property x hx p (List.mem_append_left _ hp)
  let select := d.cells.attach.filterMap fun c => if plan.evaluate c.val (inv c) then some c.val else none
  have members (c : ComputableCAD.Cell model n) :
      c ∈ select ↔ ∃ p : {c // c ∈ d.cells}, p.val = c ∧ plan.evaluate p.val (inv p) = true := by
    constructor
    · intro h
      obtain ⟨a,_,ha⟩ := List.mem_filterMap.mp h
      change (if plan.evaluate a.val (inv a) then some a.val else none) = some c at ha
      split at ha
      · rename_i yes
        exact ⟨a,Option.some.inj ha,yes⟩
      · cases ha
    · rintro ⟨a,rfl,ha⟩
      exact List.mem_filterMap.mpr ⟨a,List.mem_attach _ _,if_pos ha⟩
  refine ⟨select,?_,?_,?_,?_⟩
  · apply nodup_filterMap _ _ (List.nodup_attach.mpr (ComputableCAD.cad_nodup model n _))
    intro a _ b _ c ha hb
    split at ha <;> split at hb <;> try contradiction
    exact Subtype.ext ((Option.some.inj ha).trans (Option.some.inj hb).symm)
  · intro x
    constructor
    · intro hx
      obtain ⟨c,⟨hm,hc⟩,hu⟩ := d.partition x
      have he := (plan.correct c (inv ⟨c,hm⟩) x hc).mpr hx
      refine ⟨c,⟨(members c).mpr ⟨⟨c,hm⟩,rfl,he⟩,hc⟩,?_⟩
      rintro a ⟨ha,ha'⟩
      obtain ⟨b,rfl,_⟩ := (members a).mp ha
      exact hu _ ⟨b.property,ha'⟩
    · intro h
      obtain ⟨c,hc,hx⟩ := h.exists
      obtain ⟨a,rfl,ha⟩ := (members c).mp hc
      exact (plan.correct a.val (inv a) x hx).mp ha
  · intro c hc x hx
    obtain ⟨a,rfl,ha⟩ := (members c).mp hc
    exact (plan.correct a.val (inv a) x hx).mp ha
  · intro c hc g hg
    obtain ⟨a,rfl,_⟩ := (members c).mp hc
    let q := g.compile model
    have ih : a.val.Invariant q.tests := by
      intro x hx p hp
      rw [q.specification] at hp
      exact d.invariant _ a.property x hx p
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨g,hg,hp⟩))
    cases he : q.evaluate a.val ih with
    | true => exact Or.inl fun x hx => (q.correct a.val ih x hx).mp he
    | false =>
      exact Or.inr (disjoint_left.mpr fun x hx hg =>
        Bool.false_ne_true (he.symm.trans ((q.correct a.val ih x hx).mpr hg)))

end CertifiedTopology.CADDecision
