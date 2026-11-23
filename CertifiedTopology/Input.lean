module

public import CertifiedTopology.Formula
public import Mathlib.Basic.Complex.Basic

@[expose] public section

namespace CertifiedTopology

/-- Polynomial expressions; a coordinate type may distinguish parameters from fiber variables. -/
inductive Expr (K ι : Type) where
  | const (c : K)
  | var (i : ι)
  | add (f g : Expr K ι)
  | neg (f : Expr K ι)
  | mul (f g : Expr K ι)
  deriving Repr

namespace Expr
variable {K ι : Type}

def eval [Ring K] (p : ι → K) : Expr K ι → K
  | .const c => c
  | .var i => p i
  | .add f g => f.eval p + g.eval p
  | .neg f => -f.eval p
  | .mul f g => f.eval p * g.eval p

/-- Split all complex coefficients and coordinates before making ordered comparisons. -/
def realify : Expr ℂ ι → Expr ℝ (ι ⊕ ι) × Expr ℝ (ι ⊕ ι)
  | .const c => (.const c.re,.const c.im)
  | .var i => (.var (.inl i),.var (.inr i))
  | .add f g =>
    let (a,b) := f.realify
    let (c,d) := g.realify
    (.add a c,.add b d)
  | .neg f =>
    let (a,b) := f.realify
    (.neg a,.neg b)
  | .mul f g =>
    let (a,b) := f.realify
    let (c,d) := g.realify
    (.add (.mul a c) (.neg (.mul b d)), .add (.mul a d) (.mul b c))

theorem realify_correct (f : Expr ℂ ι) (p : ι → ℂ) :
    let xy := Sum.elim (fun i => (p i).re) (fun i => (p i).im)
    f.realify.1.eval xy = (f.eval p).re ∧ f.realify.2.eval xy = (f.eval p).im := by
  induction f <;> simp_all [realify,eval,Complex.mul_re,Complex.mul_im,sub_eq_add_neg]

theorem realify_zero (f : Expr ℂ ι) (p : ι → ℂ) :
    let xy := Sum.elim (fun i => (p i).re) (fun i => (p i).im)
    f.eval p = 0 ↔ f.realify.1.eval xy = 0 ∧ f.realify.2.eval xy = 0 := by
  obtain ⟨hr,hi⟩ := f.realify_correct p
  dsimp only
  rw [hr,hi,Complex.ext_iff]
  rfl

end Expr

namespace Aff
variable {K : Type} [Field K]

def fixed : (n : ℕ) → K → Aff K n
  | 0,c => c
  | n+1,c => (fixed n c,0)

def coordinate : {n : ℕ} → Fin n → Aff K n
  | 0,i => i.elim0
  | n+1,i => Fin.lastCases (fixed n 0,1) (fun j => (coordinate j,0)) i

def vector : {n : ℕ} → Point K n → Fin n → K
  | 0,_ => Fin.elim0
  | _+1,(p,t) => Fin.snoc (vector p) t

@[simp] theorem fixed_eval {n} (c : K) (p : Point K n) : eval (fixed n c) p = c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fixed,eval,ih]

@[simp] theorem coordinate_eval {n} (i : Fin n) (p : Point K n) :
    eval (coordinate i) p = vector p i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih => cases i using Fin.lastCases <;> simp [coordinate,vector,eval,ih]

def offset : {n : ℕ} → Aff K n → K
  | 0,c => c
  | _+1,(b,_) => offset b

theorem eval_eq_offset [DecidableEq K] {n} (f : Aff K n) (h : constant f) (p : Point K n) :
    eval f p = offset f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨b,a⟩ := f
    simp [constant] at h
    simp [offset,eval,h.1,ih b h.2]

end Aff

namespace Expr

variable {K : Type} [Field K] [DecidableEq K] {n : ℕ}

/-- Recognize affine expressions, including multiplication by computed constants. -/
def affine? : Expr K (Fin n) → Option (Aff K n)
  | .const c => some (Aff.fixed n c)
  | .var i => some (Aff.coordinate i)
  | .neg f => (f.affine?).map (Aff.scale (-1))
  | .add f g => do return Aff.sub (← f.affine?) (Aff.scale (-1) (← g.affine?))
  | .mul f g => do
    let a ← f.affine?
    let b ← g.affine?
    if Aff.constant a then return Aff.scale (Aff.offset a) b
    if Aff.constant b then return Aff.scale (Aff.offset b) a
    none

theorem affine_correct (f : Expr K (Fin n)) {a} (h : f.affine? = some a) (p : Point K n) :
    Aff.eval a p = f.eval (Aff.vector p) := by
  induction f generalizing a with
  | const | var => simp only [affine?,Option.some.injEq] at h; subst a; simp [eval]
  | neg f ih =>
    obtain ⟨b,hb,rfl⟩ := Option.map_eq_some_iff.mp h
    simp [eval,ih hb]
  | add f g ih jh =>
    cases hf : affine? f <;> cases hg : affine? g <;> simp [affine?,hf,hg] at h
    subst a
    simp [eval,ih hf,jh hg]
  | mul f g ih jh =>
    cases hf : affine? f <;> cases hg : affine? g <;> simp [affine?,hf,hg] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst a
      rw [Aff.eval_scale,← Aff.eval_eq_offset _ (by assumption) p,ih hf,jh hg,eval]
    split at h
    · simp only [Option.some.injEq] at h
      subst a
      rw [Aff.eval_scale,← Aff.eval_eq_offset _ (by assumption) p,jh hg,ih hf,eval,mul_comm]
    contradiction

/-- Products keep their input factorization; sums go through the affine recognizer. -/
def factors? (f : Expr K (Fin n)) : Option (List (Aff K n)) :=
  match f with
  | .mul g h => do return (← g.factors?) ++ (← h.factors?)
  | _ => f.affine?.map List.singleton

theorem factors_correct (f : Expr K (Fin n)) {fs} (h : f.factors? = some fs) (p : Point K n) :
    productEval fs p = f.eval (Aff.vector p) := by
  induction f generalizing fs with
  | mul f g ih jh =>
    cases hf : f.factors? <;> cases hg : g.factors? <;> simp [factors?,hf,hg] at h
    subst fs
    simpa [productEval,eval] using congrArg₂ (· * ·) (ih hf) (jh hg)
  | const | var | neg | add =>
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp h
    simpa [productEval,List.singleton] using affine_correct _ ha p

end Expr
inductive Predicate (K ι : Type) where
  | atom (e : Expr K ι) (test : Side)
  | truth (b : Bool)
  | neg (f : Predicate K ι)
  | conj (f g : Predicate K ι)
  | disj (f g : Predicate K ι)

namespace Predicate
variable {K ι : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

def eval (p : ι → K) : Predicate K ι → Bool
  | .atom e t => side (e.eval p) 0 == t
  | .truth b => b
  | .neg f => !(f.eval p)
  | .conj f g => f.eval p && g.eval p
  | .disj f g => f.eval p || g.eval p

def compile : Predicate K (Fin n) → Option (Formula (Aff K n))
  | .atom e t => e.factors?.map (.atom · t)
  | .truth b => some (.truth b)
  | .neg f => f.compile.map .neg
  | .conj f g => do return .conj (← f.compile) (← g.compile)
  | .disj f g => do return .disj (← f.compile) (← g.compile)

omit [IsStrictOrderedRing K] in
theorem compile_correct (f : Predicate K (Fin n)) {g} (h : f.compile = some g)
    (p : Point K n) : g.eval p = f.eval (Aff.vector p) := by
  induction f generalizing g with
  | atom e t =>
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp h
    simp [Formula.eval,eval,e.factors_correct ha]
  | truth b => simp [compile] at h; subst g; rfl
  | neg f ih =>
    obtain ⟨a,ha,rfl⟩ := Option.map_eq_some_iff.mp h
    simp [Formula.eval,eval,ih ha]
  | conj f j ih jh | disj f j ih jh =>
    cases hf : f.compile <;> cases hj : j.compile <;> simp [compile,hf,hj] at h
    subst g
    simp [Formula.eval,eval,ih hf,jh hj]

def solveAffine? (f : Predicate K (Fin n)) := f.compile.map solve

theorem solveAffine_correct (f : Predicate K (Fin n)) {cs} (h : f.solveAffine? = some cs)
    (p : Point K n) : f.eval (Aff.vector p) = true ↔ ∃! c, c ∈ cs ∧ c.Contains p := by
  obtain ⟨g,hg,rfl⟩ := Option.map_eq_some_iff.mp h
  rw [← compile_correct f hg]
  exact solve_correct g p

end Predicate
end CertifiedTopology
