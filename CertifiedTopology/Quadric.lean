module

public import CertifiedTopology.Quadratic
public import CertifiedTopology.Input
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace CertifiedTopology.Quadric

/-- A quadric in cylindrical order, with the coefficients of `z²`, `z`, and `1`
    stored separately. The ten coefficients also represent lower-degree equations. -/
structure Equation (K : Type) where
  zz : K
  xz : K
  yz : K
  z : K
  xx : K
  xy : K
  yy : K
  x : K
  y : K
  constant : K
  deriving DecidableEq, Repr

abbrev Plane := ℝ × ℝ
abbrev Space := Plane × ℝ

namespace Equation

variable {K : Type} [CommRing K]

def linear (q : Equation K) (x y : K) : K := q.xz * x + q.yz * y + q.z

def offset (q : Equation K) (x y : K) : K :=
  q.xx * x^2 + q.xy * x*y + q.yy * y^2 + q.x * x + q.y * y + q.constant

def eval (q : Equation K) (x y z : K) : K :=
  q.zz * (z*z) + q.linear x y * z + q.offset x y

end Equation

/-- A branch specifies the common fiber itself, with two roots always in increasing order. -/
inductive Fiber (K : Type) where
  | empty
  | graph (z : K)
  | pair (lower upper : K)
  | line
  deriving Repr

def Fiber.Contains (t : K) : Fiber K → Prop
  | .empty => False
  | .graph u => t = u
  | .pair u v => t = u ∨ t = v
  | .line => True

/-- The linear and constant remainders after cancelling the second `z²` term. -/
def slope {K : Type} [CommRing K] (q r : Equation K) (x y : K) :=
  q.zz * r.linear x y - r.zz * q.linear x y

def remainder {K : Type} [CommRing K] (q r : Equation K) (x y : K) :=
  q.zz * r.offset x y - r.zz * q.offset x y

/-- The numerator obtained by substituting `z = -c/b` in the first quadric. -/
def numerator {K : Type} [CommRing K] (q : Equation K) (x y b c : K) :=
  q.zz * c^2 - q.linear x y * c * b + q.offset x y * b^2

/-- An exact fiber description over an ordered field. In the two-root case
    the heights are `center ± sqrt(discriminant) / |denominator|`. -/
inductive Roots (K : Type) where
  | empty
  | graph (z : K)
  | pair (center denominator discriminant : K)
  | line
  deriving DecidableEq, Repr

noncomputable def Roots.overReal : Roots ℝ → Fiber ℝ
  | .empty => .empty
  | .graph z => .graph z
  | .pair c a d => .pair (c - Real.sqrt d / |a|) (c + Real.sqrt d / |a|)
  | .line => .line

def quadraticRoots {K : Type} [Field K] [LinearOrder K] (a b c : K) : Roots K :=
  let d := discrim a b c
  if d < 0 then .empty
  else if d = 0 then .graph (-b / (2*a))
  else .pair (-b / (2*a)) (2*a) d

/-- The only nonlinear operation in lifting a quadratic fiber is a square root. -/
noncomputable def quadraticFiber (a b c : ℝ) : Fiber ℝ :=
  (quadraticRoots a b c).overReal

theorem quadraticFiber_correct {a : ℝ} (ha : a ≠ 0) (b c t : ℝ) :
    (quadraticFiber a b c).Contains t ↔ a*(t*t)+b*t+c = 0 := by
  unfold quadraticFiber quadraticRoots
  dsimp only
  split_ifs with hn hz
  · change False ↔ _
    rw [quadratic_eq_zero_iff_discrim_eq_sq ha]
    exact ⟨False.elim, fun h => by rw [h] at hn; exact (sq_nonneg _).not_gt hn⟩
  · exact (quadratic_eq_zero_iff_of_discrim_eq_zero ha hz t).symm
  · have hd : 0 < discrim a b c := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz)
    have hs := Real.mul_self_sqrt hd.le
    have hab : (2*a : ℝ) ≠ 0 := mul_ne_zero two_ne_zero ha
    rw [quadratic_eq_zero_iff ha hs.symm]
    change (_ = _ ∨ _ = _) ↔ (_ = _ ∨ _ = _)
    rcases lt_or_gt_of_ne hab with h | h
    · rw [abs_of_neg h, div_neg, sub_neg_eq_add, ← sub_eq_add_neg,
        ← add_div, ← sub_div]
    · rw [abs_of_pos h, ← sub_div, ← add_div, or_comm]

/-- Pivot on an equation with a nonzero `z²` coefficient. -/
def quadraticPivotRoots {K : Type} [Field K] [LinearOrder K]
    (q r : Equation K) (x y : K) : Roots K :=
  let b := slope q r x y
  let c := remainder q r x y
  if b = 0 then
    if c = 0 then quadraticRoots q.zz (q.linear x y) (q.offset x y) else .empty
  else if numerator q x y b c = 0 then .graph (-c/b) else .empty

/-- Branch for a pair of equations both of degree at most one in `z`. -/
def linearPivotRoots {K : Type} [Field K] [LinearOrder K]
    (q r : Equation K) (x y : K) : Roots K :=
  let b := q.linear x y
  let c := q.offset x y
  let e := r.linear x y
  let f := r.offset x y
  if b = 0 then
    if c = 0 then
      if e = 0 then (if f = 0 then .line else .empty) else .graph (-f/e)
    else .empty
  else if b*f-e*c = 0 then .graph (-c/b) else .empty

/-- This dispatch includes zero equations, degree drops and coincident surface
    components. It uses field operations and comparisons only. -/
def roots {K : Type} [Field K] [LinearOrder K] (q r : Equation K) (x y : K) : Roots K :=
  if q.zz = 0 then
    if r.zz = 0 then linearPivotRoots q r x y else quadraticPivotRoots r q x y
  else quadraticPivotRoots q r x y

noncomputable def quadraticPivot (q r : Equation ℝ) (x y : ℝ) : Fiber ℝ :=
  (quadraticPivotRoots q r x y).overReal

noncomputable def linearPivot (q r : Equation ℝ) (x y : ℝ) : Fiber ℝ :=
  (linearPivotRoots q r x y).overReal

noncomputable def fiber (q r : Equation ℝ) (x y : ℝ) : Fiber ℝ :=
  (roots q r x y).overReal

theorem quadraticPivot_eq (q r : Equation ℝ) (x y : ℝ) :
    quadraticPivot q r x y =
      let b := slope q r x y
      let c := remainder q r x y
      if b = 0 then
        if c = 0 then quadraticFiber q.zz (q.linear x y) (q.offset x y) else .empty
      else if numerator q x y b c = 0 then .graph (-c/b) else .empty := by
  unfold quadraticPivot quadraticPivotRoots
  dsimp only
  split_ifs <;> rfl

theorem linearPivot_eq (q r : Equation ℝ) (x y : ℝ) :
    linearPivot q r x y =
      let b := q.linear x y
      let c := q.offset x y
      let e := r.linear x y
      let f := r.offset x y
      if b = 0 then
        if c = 0 then
          if e = 0 then (if f = 0 then .line else .empty) else .graph (-f/e)
        else .empty
      else if b*f-e*c = 0 then .graph (-c/b) else .empty := by
  unfold linearPivot linearPivotRoots
  dsimp only
  split_ifs <;> rfl

theorem quadraticPivot_correct (q r : Equation ℝ) (ha : q.zz ≠ 0) (x y t : ℝ) :
    (quadraticPivot q r x y).Contains t ↔ q.eval x y t = 0 ∧ r.eval x y t = 0 := by
  let b := slope q r x y
  let c := remainder q r x y
  have eliminate : b*t+c = q.zz * r.eval x y t - r.zz * q.eval x y t := by
    simp only [b,c,slope,remainder,Equation.eval]
    ring
  have equiv : (q.eval x y t = 0 ∧ r.eval x y t = 0) ↔
      (q.eval x y t = 0 ∧ b*t+c = 0) := by
    rw [eliminate]
    constructor
    · rintro ⟨hq,hr⟩; simp [hq,hr]
    · rintro ⟨hq,hr⟩; simpa [hq,ha] using hr
  rw [equiv, quadraticPivot_eq]
  change (if b = 0 then
      (if c = 0 then quadraticFiber q.zz (q.linear x y) (q.offset x y) else Fiber.empty)
      else if numerator q x y b c = 0 then Fiber.graph (-c/b) else Fiber.empty).Contains t ↔ _
  by_cases hb : b = 0
  · simp only [hb, ite_true, zero_mul, zero_add]
    split_ifs with hc
    · simpa only [hc, eq_self_iff_true, and_true, Equation.eval] using
        quadraticFiber_correct ha (q.linear x y) (q.offset x y) t
    · simp [Fiber.Contains,hc]
  · have ht : b*t+c = 0 ↔ t = -c/b := by rw [eq_div_iff hb]; constructor <;> intro h <;> linarith
    have hn : q.eval x y (-c/b) * b^2 = numerator q x y b c := by
      unfold Equation.eval numerator
      field_simp [hb]
      ring
    have hzero : q.eval x y (-c/b) = 0 ↔ numerator q x y b c = 0 := by
      rw [← hn, mul_eq_zero]
      simp [hb]
    rw [ite_eq_right hb, ht, and_comm]
    by_cases hz : numerator q x y b c = 0
    · simp only [hz, ite_true, Fiber.Contains]
      exact ⟨fun e => ⟨e, e.symm ▸ hzero.mpr hz⟩, And.left⟩
    · simpa [hz, Fiber.Contains] using
        (show ¬(t = -c/b ∧ q.eval x y t = 0) by
          rintro ⟨rfl, hs⟩; exact hz (hzero.mp hs))

theorem linearPivot_correct (q r : Equation ℝ) (hq : q.zz = 0) (hr : r.zz = 0)
    (x y t : ℝ) : (linearPivot q r x y).Contains t ↔
      q.eval x y t = 0 ∧ r.eval x y t = 0 := by
  let b := q.linear x y
  let c := q.offset x y
  let e := r.linear x y
  let f := r.offset x y
  have root {u v : ℝ} (hu : u ≠ 0) : u*t+v = 0 ↔ t = -v/u := by
    rw [eq_div_iff hu]; constructor <;> intro h <;> linarith
  rw [linearPivot_eq]
  simp only [Equation.eval,hq,hr,zero_mul,zero_add]
  change (if b = 0 then
    (if c = 0 then (if e = 0 then (if f = 0 then Fiber.line else Fiber.empty) else Fiber.graph (-f/e))
    else Fiber.empty) else if b*f-e*c = 0 then Fiber.graph (-c/b) else Fiber.empty).Contains t ↔
    b*t+c = 0 ∧ e*t+f = 0
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · by_cases he : e = 0
      · by_cases hf : f = 0 <;> simp [hb,hc,he,hf,Fiber.Contains]
      · simp [hb,hc,he,root he,Fiber.Contains]
    · simp [hb,hc,Fiber.Contains]
  · have evalRoot : (e*(-c/b)+f)*b = b*f-e*c := by field_simp [hb]; ring
    rw [ite_eq_right hb, root hb]
    by_cases h : b*f-e*c = 0
    · simp only [h, ite_true, Fiber.Contains]
      exact ⟨fun ht => ⟨ht, by rw [ht]; exact (mul_eq_zero.mp
        (evalRoot.trans h)).resolve_right hb⟩, And.left⟩
    · simp only [h, ite_false, Fiber.Contains, false_iff]
      rintro ⟨rfl, he⟩
      apply h
      rw [← evalRoot, he, zero_mul]

/-- The decision tree solves the simultaneous equations pointwise over every base point. -/
theorem fiber_correct (q r : Equation ℝ) (x y t : ℝ) :
    (fiber q r x y).Contains t ↔ q.eval x y t = 0 ∧ r.eval x y t = 0 := by
  unfold fiber roots
  split_ifs with hq hr
  · exact linearPivot_correct q r hq hr x y t
  · exact (quadraticPivot_correct r q hr x y t).trans and_comm
  · exact quadraticPivot_correct q r hq x y t

section Map

variable {K L : Type} [Field K] [Field L]
variable (φ : K →+* L)

def Equation.map (q : Equation K) : Equation L :=
  ⟨φ q.zz, φ q.xz, φ q.yz, φ q.z, φ q.xx, φ q.xy, φ q.yy, φ q.x, φ q.y, φ q.constant⟩

def Roots.map : Roots K → Roots L
  | .empty => .empty
  | .graph z => .graph (φ z)
  | .pair c a d => .pair (φ c) (φ a) (φ d)
  | .line => .line

@[simp] theorem Equation.zz_map (q : Equation K) : (q.map φ).zz = φ q.zz := rfl

@[simp] theorem Equation.linear_map (q : Equation K) (x y : K) :
    (q.map φ).linear (φ x) (φ y) = φ (q.linear x y) := by simp [Equation.map, Equation.linear]

@[simp] theorem Equation.offset_map (q : Equation K) (x y : K) :
    (q.map φ).offset (φ x) (φ y) = φ (q.offset x y) := by simp [Equation.map, Equation.offset]

@[simp] theorem Equation.eval_map (q : Equation K) (x y z : K) :
    (q.map φ).eval (φ x) (φ y) (φ z) = φ (q.eval x y z) := by
  simp [Equation.eval]

variable [LinearOrder K] [LinearOrder L]

private theorem quadraticRoots_map (mono : StrictMono φ) (a b c : K) :
    quadraticRoots (φ a) (φ b) (φ c) = (quadraticRoots a b c).map φ := by
  have hn (u : K) : φ u < 0 ↔ u < 0 := by simpa using mono.lt_iff_lt (a := u) (b := 0)
  have e : discrim (φ a) (φ b) (φ c) = φ (discrim a b c) := by simp [discrim, map_ofNat]
  simp only [quadraticRoots, e, hn, map_eq_zero]
  split_ifs <;> simp [Roots.map, map_ofNat]

private theorem quadraticPivotRoots_map (mono : StrictMono φ) (q r : Equation K) (x y : K) :
    quadraticPivotRoots (q.map φ) (r.map φ) (φ x) (φ y) =
      (quadraticPivotRoots q r x y).map φ := by
  have e (b c : K) : numerator (q.map φ) (φ x) (φ y) (φ b) (φ c) =
      φ (numerator q x y b c) := by simp [numerator]
  have eb : slope (q.map φ) (r.map φ) (φ x) (φ y) = φ (slope q r x y) := by
    simp [slope]
  have ec : remainder (q.map φ) (r.map φ) (φ x) (φ y) = φ (remainder q r x y) := by
    simp [remainder]
  simp only [quadraticPivotRoots, eb, ec, e, map_eq_zero]
  split_ifs <;> simp [Roots.map, quadraticRoots_map φ mono]

private theorem linearPivotRoots_map (q r : Equation K) (x y : K) :
    linearPivotRoots (q.map φ) (r.map φ) (φ x) (φ y) =
      (linearPivotRoots q r x y).map φ := by
  simp only [linearPivotRoots, Equation.linear_map, Equation.offset_map, ← map_mul, ← map_sub,
    map_eq_zero]
  split_ifs <;> simp [Roots.map]

/-- The exact decision tree commutes with ordered field embeddings. It may run
    on rational coordinates and then be interpreted in the reals. -/
theorem roots_map (mono : StrictMono φ) (q r : Equation K) (x y : K) :
    roots (q.map φ) (r.map φ) (φ x) (φ y) = (roots q r x y).map φ := by
  unfold roots
  have h (f : Equation K) : (f.map φ).zz = 0 ↔ f.zz = 0 := by simp [Equation.map]
  simp only [h]
  split_ifs
  · exact linearPivotRoots_map φ q r x y
  · exact quadraticPivotRoots_map φ mono r q x y
  · exact quadraticPivotRoots_map φ mono q r x y

theorem roots_correct (ι : K →+* ℝ) (mono : StrictMono ι) (q r : Equation K) (x y : K) (z : ℝ) :
    ((roots q r x y).map ι).overReal.Contains z ↔
      (q.map ι).eval (ι x) (ι y) z = 0 ∧ (r.map ι).eval (ι x) (ι y) z = 0 := by
  rw [← roots_map ι mono]
  exact fiber_correct _ _ _ _ _

end Map

end CertifiedTopology.Quadric
