module

public import CertifiedTopology.Affine
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

namespace CertifiedTopology.Quadratic

/-- Topology of the real zero fiber, with the whole line as a separate case. -/
inductive Kind | empty | point | twoPoints | line deriving DecidableEq, Repr

/-- The classifier uses field operations and comparisons only. -/
def classify {K : Type} [Field K] [LinearOrder K] (a b c : K) : Kind :=
  if a = 0 then
    if b = 0 then (if c = 0 then .line else .empty) else .point
  else if discrim a b c < 0 then .empty
  else if discrim a b c = 0 then .point else .twoPoints

def Realizes (q : ℝ → ℝ) : Kind → Prop
  | .line => ∀ x, q x = 0
  | .empty => ∀ x, q x ≠ 0
  | .point => ∃ r, ∀ x, q x = 0 ↔ x = r
  | .twoPoints => ∃ l h, l < h ∧ ∀ x, q x = 0 ↔ x = l ∨ x = h

theorem classify_correct (a b c : ℝ) :
    Realizes (fun x => a * (x*x) + b*x + c) (classify a b c) := by
  unfold classify
  split_ifs with ha hb hc hd he
  · simp [Realizes, *]
  · simp [Realizes, *]
  · refine ⟨-c/b, fun x => ?_⟩
    simp only [ha,zero_mul,zero_add,eq_div_iff hb]
    constructor <;> intro h <;> linarith
  · intro x hx
    have h := discrim_eq_sq_of_quadratic_eq_zero hx
    nlinarith [sq_nonneg (2*a*x+b)]
  · exact ⟨-b/(2*a), quadratic_eq_zero_iff_of_discrim_eq_zero ha he⟩
  · have hp : 0 < discrim a b c := lt_of_le_of_ne (le_of_not_gt hd) (Ne.symm he)
    let s := Real.sqrt (discrim a b c)
    have hs : discrim a b c = s*s := (Real.mul_self_sqrt hp.le).symm
    have hpos : 0 < s := Real.sqrt_pos.2 hp
    let u := (-b+s)/(2*a)
    let v := (-b-s)/(2*a)
    have huv : u ≠ v := by
      intro e
      have e' := (div_left_inj₀ (mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) ha)).mp e
      linarith
    rcases lt_or_gt_of_ne huv with h | h
    · exact ⟨u,v,h,quadratic_eq_zero_iff ha hs⟩
    · exact ⟨v,u,h,fun x => (quadratic_eq_zero_iff ha hs x).trans or_comm⟩

/-- Over each sign cell in a, the cut in c is a continuous function of a,b.
    The b-axis is needed only on the zero-leading-coefficient branch. -/
inductive CoeffCell where
  | quadratic (leading height : Side)
  | linear (slope : Side)
  | constant (offset : Side)
  deriving DecidableEq, Repr

def locate {K : Type} [Field K] [LinearOrder K] (a b c : K) : CoeffCell :=
  if a = 0 then
    if b = 0 then .constant (side c 0) else .linear (side b 0)
  else .quadratic (side a 0) (side c (b^2/(4*a)))

def CoeffCell.kind : CoeffCell → Kind
  | .constant .on => .line
  | .constant _ => .empty
  | .linear _ => .point
  | .quadratic _ .on => .point
  | .quadratic .below .above | .quadratic .above .below => .twoPoints
  | .quadratic _ _ => .empty

theorem locate_correct {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a b c : K) : (locate a b c).kind = classify a b c := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · subst a b
      rcases lt_trichotomy c 0 with h | h | h <;>
        simp [locate,classify,side,CoeffCell.kind, *,not_lt_of_gt,ne_of_lt,ne_of_gt]
    · simp [locate,classify,ha,hb,CoeffCell.kind]
  · have h₄ : 4*a ≠ 0 := mul_ne_zero (by norm_num) ha
    have ident : discrim a b c = (b^2/(4*a)-c)*(4*a) := by
      rw [sub_mul, div_mul_cancel₀ _ h₄, discrim]; ring
    rcases lt_or_gt_of_ne ha with han | hap
    all_goals rcases lt_trichotomy c (b^2/(4*a)) with h | h | h
    all_goals simp only [locate,classify,ite_eq_right ha,side,ident]
    all_goals split_ifs <;> simp_all [CoeffCell.kind,mul_neg_iff,sub_neg,sub_pos,
      mul_eq_zero,sub_eq_zero] <;> (exfalso; grind)

theorem fiber_on_cell (a b c : ℝ) :
    Realizes (fun x => a*(x*x)+b*x+c) (locate a b c).kind :=
  locate_correct a b c ▸ classify_correct a b c

end CertifiedTopology.Quadratic
