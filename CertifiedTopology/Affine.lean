module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic
public import Mathlib.Data.List.Dedup

@[expose] public section

namespace CertifiedTopology

/-- Coordinates are added on the right, in projection order. -/
abbrev Point (K : Type) : ℕ → Type _
  | 0 => Unit
  | n+1 => Point K n × K

/-- A constant, or a lower-dimensional offset and the last coefficient. -/
abbrev Aff (K : Type) : ℕ → Type _
  | 0 => K
  | n+1 => Aff K n × K

namespace Aff

variable {K : Type} [Field K]

instance decEqAff [DecidableEq K] : (m : ℕ) → DecidableEq (Aff K m)
  | 0 => inferInstanceAs (DecidableEq K)
  | m+1 => letI := decEqAff m; inferInstanceAs (DecidableEq (Aff K m × K))

def constant [DecidableEq K] : {m : ℕ} → Aff K m → Bool
  | 0, _ => true
  | _+1, (b,a) => a == 0 && constant b

def eval : {n : ℕ} → Aff K n → Point K n → K
  | 0, c, _ => c
  | _+1, (b,a), (p,t) => eval b p + a*t

theorem eval_constant [DecidableEq K] {m} (f : Aff K m) (h : constant f)
    (p q : Point K m) : eval f p = eval f q := by
  induction m with
  | zero => rfl
  | succ m ih =>
    obtain ⟨b,a⟩ := f
    simp [constant] at h
    simp [eval,h.1,ih b h.2 p.1 q.1]

def scale : {n : ℕ} → K → Aff K n → Aff K n
  | 0, s,c => s*(c : K)
  | _+1, s,(b,a) => (scale s b, s*a)

def sub : {n : ℕ} → Aff K n → Aff K n → Aff K n
  | 0, c,d => (c : K)-(d : K)
  | _+1, (b,a),(d,e) => (sub b d, a-e)

@[simp] theorem eval_scale {n} (s : K) (f : Aff K n) (p : Point K n) :
    eval (scale s f) p = s * eval f p := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [scale,eval,ih]; ring

@[simp] theorem eval_sub {n} (f g : Aff K n) (p : Point K n) :
    eval (sub f g) p = eval f p - eval g p := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sub,eval,ih]; ring

end Aff

inductive Side | below | on | above deriving Repr, DecidableEq

def side {K : Type} [LinearOrder K] (x y : K) : Side :=
  if x < y then .below else if x = y then .on else .above

section Order
variable {K : Type} [LinearOrder K]

@[simp] theorem side_self (x : K) : side x x = .on := by simp [side]
theorem side_congr {x y z w : K} (h : side x y = side z w) :
    (x < y ↔ z < w) ∧ (x = y ↔ z = w) ∧ (y < x ↔ w < z) := by
  unfold side at h
  split_ifs at h <;> simp_all <;> constructor <;> constructor <;> intro <;> order

end Order

section CAD
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

abbrev root (f : Aff K (n+1)) : Aff K n := Aff.scale (-f.2⁻¹) f.1

/-- Vertical polynomials survive projection. All pairs of nonvertical roots are compared. -/
def roots (fs : List (Aff K (n+1))) : List (Aff K n) :=
  ((fs.filter fun f => f.2 != 0).map root).dedup

/-- Compare each unordered pair of root functions once. -/
def differences : List (Aff K n) → List (Aff K n)
  | [] => []
  | r :: rs => rs.map (Aff.sub r) ++ differences rs

def project (fs : List (Aff K (n+1))) : List (Aff K n) :=
  ((fs.filter fun f => f.2 == 0).map Prod.fst) ++
    differences (roots fs)

/-- Optional endpoints denote the two infinite ends. -/
inductive Slice (A : Type) where
  | sectionAt (r : A)
  | sector (lo hi : Option A)
  deriving Repr

namespace Slice

def Contains (p : Point K n) : Slice (Aff K n) → K → Prop
  | .sectionAt r, t => t = Aff.eval r p
  | .sector lo hi, t =>
    (∀ r ∈ lo, Aff.eval r p < t) ∧ (∀ r ∈ hi, t < Aff.eval r p)

def sample (p : Point K n) : Slice (Aff K n) → K
  | .sectionAt r => Aff.eval r p
  | .sector none none => 0
  | .sector (some l) none => Aff.eval l p + 1
  | .sector none (some h) => Aff.eval h p - 1
  | .sector (some l) (some h) => (Aff.eval l p + Aff.eval h p)/2

end Slice

/-- Insert in increasing order, keeping one representative of coincident roots. -/
def insertRoot (p : Point K n) (r : Aff K n) : List (Aff K n) → List (Aff K n)
  | [] => [r]
  | a :: as =>
    if Aff.eval r p < Aff.eval a p then r :: a :: as
    else if Aff.eval r p = Aff.eval a p then a :: as
    else a :: insertRoot p r as

def orderedRoots (p : Point K n) (rs : List (Aff K n)) :=
  rs.foldr (insertRoot p) []

def slices (lo : Option (Aff K n)) : List (Aff K n) → List (Slice (Aff K n))
  | [] => [.sector lo none]
  | a :: as => .sector lo (some a) :: .sectionAt a :: slices (some a) as

def stack (p : Point K n) (rs : List (Aff K n)) := slices none (orderedRoots p rs)

inductive Cell (K : Type) : ℕ → Type _ where
  | origin : Cell K 0
  | lift {n : ℕ} : Cell K n → Slice (Aff K n) → Cell K (n+1)

namespace Cell

def sample : {m : ℕ} → Cell K m → Point K m
  | 0, .origin => ()
  | _+1, .lift b s => let p := sample b; (p, s.sample p)

def Contains : {m : ℕ} → Cell K m → Point K m → Prop
  | 0, .origin, _ => True
  | _+1, .lift b s, (p,t) => Contains b p ∧ s.Contains p t

def dimension : {m : ℕ} → Cell K m → ℕ
  | 0, .origin => 0
  | _+1, .lift b (.sectionAt _) => dimension b
  | _+1, .lift b (.sector _ _) => dimension b + 1

end Cell

def prune (fs : List (Aff K n)) := (fs.filter (fun f => !Aff.constant f)).dedup

def cad : (m : ℕ) → List (Aff K m) → List (Cell K m)
  | 0, _ => [.origin]
  | m+1, fs => (cad m (prune (project fs))).flatMap fun b =>
    (stack b.sample (roots fs)).map (Cell.lift b)

end CAD
end CertifiedTopology
