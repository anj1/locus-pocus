module

public import CertifiedTopology.CADDecision

@[expose] public section

namespace CertifiedTopology.CADDecision

open ExecutableIsolation

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

namespace SignFormula

variable {n m : ℕ}

def rename (i : Fin n → Fin m) : SignFormula K n → SignFormula K m
  | .truth b => .truth b
  | .atom p s => .atom (Multi.substitute p (Multi.coordinate ∘ i)) s
  | .not f => .not (rename i f)
  | .and f g => .and (rename i f) (rename i g)
  | .or f g => .or (rename i f) (rename i g)

theorem rename_correct (model : RealModel K) (i : Fin n → Fin m) (x : Fin m → ℝ) (f : SignFormula K n) :
    (f.rename i).holds model x ↔ f.holds model (x ∘ i) := by
  induction f with
  | truth b => rfl
  | atom p s => simp [rename, holds, Multi.substitute_correct, Function.comp_def]
  | not f ih => exact not_congr ih
  | and f g ih jh => exact and_congr ih jh
  | or f g ih jh => exact or_congr ih jh

end SignFormula

namespace Prenex

def extendIndex {n m : ℕ} (i : Fin n → Fin m) : Fin (n+1) → Fin (m+1) :=
  Fin.lastCases (Fin.last m) (Fin.castSucc ∘ i)

theorem snoc_extendIndex {n m : ℕ} (i : Fin n → Fin m) (x : Fin m → ℝ) (y : ℝ) :
    Fin.snoc x y ∘ extendIndex i = Fin.snoc (x ∘ i) y := by
  funext j
  cases j using Fin.lastCases <;> simp [extendIndex, Function.comp_def]

def rename : {n m : ℕ} → (Fin n → Fin m) → Prenex K n → Prenex K m
  | _, _, i, .matrix f => .matrix (f.rename i)
  | _, _, i, .exists_ f => .exists_ (rename (extendIndex i) f)
  | _, _, i, .forall_ f => .forall_ (rename (extendIndex i) f)

theorem rename_correct (model : RealModel K) :
    ∀ {n m : ℕ} (i : Fin n → Fin m) (x : Fin m → ℝ) (f : Prenex K n),
    (f.rename i).holds model x ↔ f.holds model (x ∘ i)
  | _, _, i, x, .matrix f => f.rename_correct model i x
  | _, _, i, x, .exists_ f => by
    apply exists_congr
    intro y
    exact (rename_correct model (extendIndex i) (Fin.snoc x y) f).trans (by rw [snoc_extendIndex])
  | _, _, i, x, .forall_ f => by
    apply forall_congr'
    intro y
    exact (rename_correct model (extendIndex i) (Fin.snoc x y) f).trans (by rw [snoc_extendIndex])

def weaken {n : ℕ} (f : Prenex K n) : Prenex K (n+1) := f.rename Fin.castSucc

theorem weaken_correct (model : RealModel K) {n : ℕ} (f : Prenex K n)
    (x : Fin n → ℝ) (y : ℝ) :
    f.weaken.holds model (Fin.snoc x y) ↔ f.holds model x := by
  have e : Fin.snoc x y ∘ Fin.castSucc = x := by
    funext i
    exact @Fin.snoc_castSucc n (fun _ => ℝ) y x i
  exact (rename_correct model Fin.castSucc _ f).trans (by rw [e])

def neg : {n : ℕ} → Prenex K n → Prenex K n
  | _, .matrix f => .matrix (.not f)
  | _, .exists_ f => .forall_ (neg f)
  | _, .forall_ f => .exists_ (neg f)

theorem neg_correct (model : RealModel K) :
    ∀ {n : ℕ} (f : Prenex K n) (x : Fin n → ℝ),
      f.neg.holds model x ↔ ¬f.holds model x
  | _, .matrix _, _ => Iff.rfl
  | _, .exists_ f, x => (forall_congr' fun y => neg_correct model f (Fin.snoc x y)).trans not_exists.symm
  | _, .forall_ f, x => (exists_congr fun y => neg_correct model f (Fin.snoc x y)).trans not_forall.symm

def matrixAnd : {n : ℕ} → SignFormula K n → Prenex K n → Prenex K n
  | _, a, .matrix b => .matrix (.and a b)
  | _, a, .exists_ b => .exists_ (matrixAnd (a.rename Fin.castSucc) b)
  | _, a, .forall_ b => .forall_ (matrixAnd (a.rename Fin.castSucc) b)

private theorem and_exists_right {P : Prop} {Q : ℝ → Prop} :
    (∃ y, P ∧ Q y) ↔ P ∧ ∃ y, Q y := by
  constructor
  · rintro ⟨y, h, q⟩
    exact ⟨h,y,q⟩
  · rintro ⟨h,y,q⟩
    exact ⟨y,h,q⟩

private theorem and_forall_right {P : Prop} {Q : ℝ → Prop} :
    (∀ y, P ∧ Q y) ↔ P ∧ ∀ y, Q y := by
  exact ⟨fun h => ⟨(h 0).1,fun y => (h y).2⟩, fun h y => ⟨h.1,h.2 y⟩⟩

theorem matrixAnd_correct (model : RealModel K) :
    ∀ {n : ℕ} (a : SignFormula K n) (b : Prenex K n) (x : Fin n → ℝ),
      (matrixAnd a b).holds model x ↔ a.holds model x ∧ b.holds model x
  | _, a, .matrix b, x => Iff.rfl
  | _, a, .exists_ b, x => by
    change (∃ y : ℝ, (matrixAnd (a.rename Fin.castSucc) b).holds model (Fin.snoc x y)) ↔ _
    refine (exists_congr fun y => (matrixAnd_correct model _ b _).trans ?_).trans and_exists_right
    exact and_congr (weaken_correct model (.matrix a) x y) Iff.rfl
  | _, a, .forall_ b, x => by
    change (∀ y : ℝ, (matrixAnd (a.rename Fin.castSucc) b).holds model (Fin.snoc x y)) ↔ _
    refine (forall_congr' fun y => (matrixAnd_correct model _ b _).trans ?_).trans and_forall_right
    exact and_congr (weaken_correct model (.matrix a) x y) Iff.rfl

def both : {n : ℕ} → Prenex K n → Prenex K n → Prenex K n
  | _, .matrix a, b => matrixAnd a b
  | _, .exists_ a, b => .exists_ (both a b.weaken)
  | _, .forall_ a, b => .forall_ (both a b.weaken)

theorem both_correct (model : RealModel K) :
    ∀ {n : ℕ} (a b : Prenex K n) (x : Fin n → ℝ),
      (both a b).holds model x ↔ a.holds model x ∧ b.holds model x
  | _, .matrix a, b, x => matrixAnd_correct model a b x
  | _, .exists_ a, b, x => by
    change (∃ y : ℝ, (both a b.weaken).holds model (Fin.snoc x y)) ↔ _
    have eq (y : ℝ) : (both a b.weaken).holds model (Fin.snoc x y) ↔
        b.holds model x ∧ a.holds model (Fin.snoc x y) :=
      (both_correct model a _ _).trans
        ((and_congr Iff.rfl (weaken_correct model b x y)).trans and_comm)
    exact (exists_congr eq).trans (and_exists_right.trans and_comm)
  | _, .forall_ a, b, x => by
    change (∀ y : ℝ, (both a b.weaken).holds model (Fin.snoc x y)) ↔ _
    have eq (y : ℝ) : (both a b.weaken).holds model (Fin.snoc x y) ↔
        b.holds model x ∧ a.holds model (Fin.snoc x y) :=
      (both_correct model a _ _).trans
        ((and_congr Iff.rfl (weaken_correct model b x y)).trans and_comm)
    exact (forall_congr' eq).trans (and_forall_right.trans and_comm)

def either {n : ℕ} (a b : Prenex K n) : Prenex K n := (a.neg.both b.neg).neg

theorem either_correct (model : RealModel K) {n : ℕ} (a b : Prenex K n) (x : Fin n → ℝ) :
    (either a b).holds model x ↔ a.holds model x ∨ b.holds model x := by
  rw [either, neg_correct, both_correct, neg_correct, neg_correct]
  tauto

end Prenex
end CertifiedTopology.CADDecision
