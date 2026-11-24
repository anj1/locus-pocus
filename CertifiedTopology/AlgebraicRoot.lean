module

public import CertifiedTopology.ExecutableIsolation

@[expose] public section

namespace CertifiedTopology.AlgebraicRoot

open Polynomial Set ExecutableIsolation
open DensePolynomial (Coefficients)

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable (f : K →+* ℝ) (mono : StrictMono f)

structure Represents (p : Polynomial ℝ) (x : ℝ) (w : Window) : Prop where
  inside : x ∈ w.region
  root : p.IsRoot x
  unique : ∀ y ∈ w.region, p.IsRoot y → y = x
  crosses : w.crosses p

/-- An exact algebraic root over the current coefficient field. The real
    interpretation is confined to its specification. -/
structure Root (model : RealModel K) where
  polynomial : Coefficients K
  window : Window
  isolated : ∃! x, x ∈ window.region ∧ (realPoly model.hom polynomial).IsRoot x
  crosses : window.crosses (realPoly model.hom polynomial)
  simple : ∀ x, (realPoly model.hom polynomial).IsRoot x →
    ¬(realPoly model.hom polynomial).derivative.IsRoot x

namespace Root

variable {model : RealModel K}

noncomputable def value (r : Root model) : ℝ := r.isolated.exists.choose

omit [IsStrictOrderedRing K] in
theorem represents (r : Root model) :
    Represents (realPoly model.hom r.polynomial) r.value r.window := by
  have h := r.isolated.exists.choose_spec
  refine ⟨h.1, h.2, ?_, r.crosses⟩
  intro y hy hz
  obtain ⟨z,_,hu⟩ := r.isolated
  exact (hu _ ⟨hy,hz⟩).trans (hu _ h).symm

end Root

def Root.ofWindow (model : RealModel K) (p : Coefficients K) {ws : List Window}
    (h : IsolatesOn (realPoly model.hom p) Set.univ ws)
    (simple : ∀ x, (realPoly model.hom p).IsRoot x → ¬(realPoly model.hom p).derivative.IsRoot x)
    (w : {w // w ∈ ws}) : Root model :=
  ⟨p, w.val, h.unique _ w.property, h.brackets _ w.property, simple⟩

@[simp] theorem Root.ofWindow_window (model : RealModel K) (p : Coefficients K) {ws : List Window}
    (h : IsolatesOn (realPoly model.hom p) Set.univ ws)
    (simple : ∀ x, (realPoly model.hom p).IsRoot x → ¬(realPoly model.hom p).derivative.IsRoot x)
    (w : {w // w ∈ ws}) : (Root.ofWindow model p h simple w).window = w.val := rfl

/-- Retain the exact root descriptions for later specialization. -/
def roots (model : RealModel K) (res : Result model.hom p) : List (Root model) :=
  match h : res.roots with
  | .all => []
  | .finite ws =>
    have cert : realPoly model.hom p ≠ 0 ∧ IsolatesOn (realPoly model.hom res.simplePoly) univ ws ∧
        (∀ x, (realPoly model.hom res.simplePoly).IsRoot x ↔ (realPoly model.hom p).IsRoot x) ∧
        ∀ x, (realPoly model.hom res.simplePoly).IsRoot x →
          ¬(realPoly model.hom res.simplePoly).derivative.IsRoot x := by
      have c := res.correct
      rw [h] at c
      exact c
    ws.attach.map (Root.ofWindow model res.simplePoly cert.2.1 cert.2.2.2)

section Refine

def width : Window → ℚ
  | .point _ => 0
  | .interval l u => u-l

def refine (p : Coefficients K) : Window → Window
  | .point q => .point q
  | .interval l u =>
    let m := ExecutableIsolation.midpoint l u
    let e := DensePolynomial.eval p (m : K)
    if e = 0 then .point m
    else if DensePolynomial.eval p (l : K) * e < 0 then .interval l m
    else .interval m u

theorem eval_zero_iff (p : Coefficients K) (a : ℚ) :
    DensePolynomial.eval p (a : K) = 0 ↔ (realPoly f p).IsRoot (a : ℝ) := by
  rw [IsRoot.def, ← map_eval f, map_eq_zero_iff f f.injective]

include mono

theorem bracket_iff (p : Coefficients K) (a b : ℚ) :
    DensePolynomial.eval p (a : K) * DensePolynomial.eval p (b : K) < 0 ↔
      (Window.interval a b).crosses (realPoly f p) := by
  rw [← mono.lt_iff_lt, map_mul, map_zero, map_eval f, map_eval f]
  rfl

omit mono [LinearOrder K] [IsStrictOrderedRing K] in
private theorem bracket_right {a b c : ℝ} (h : a*b < 0) (hn : c ≠ 0) (hl : ¬a*c < 0) :
    c*b < 0 := by
  rcases mul_neg_iff.mp h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · apply mul_neg_of_pos_of_neg _ hb
    by_contra! h
    exact hl (mul_neg_of_pos_of_neg ha (lt_of_le_of_ne h hn))
  · apply mul_neg_of_neg_of_pos _ hb
    by_contra! h
    exact hl (mul_neg_of_neg_of_pos ha (lt_of_le_of_ne h hn.symm))

theorem refine_correct {p : Coefficients K} {x : ℝ} {w : Window}
    (r : Represents (realPoly f p) x w) :
    Represents (realPoly f p) x (refine p w) ∧ (refine p w).region ⊆ w.region := by
  cases w with
  | point a => exact ⟨r, Subset.rfl⟩
  | interval l u =>
    let m := ExecutableIsolation.midpoint l u
    have hi : (l : ℝ) < (u : ℝ) := r.inside.1.trans r.inside.2
    have e : (m : ℝ) = ((l : ℝ) + (u : ℝ))/2 := by
      dsimp [m, ExecutableIsolation.midpoint]
      norm_cast
    have hl : (l : ℝ) < (m : ℝ) := by rw [e]; linarith
    have hu : (m : ℝ) < (u : ℝ) := by rw [e]; linarith
    have qc : Window.crosses (realPoly f p) (.interval l u) := r.crosses
    have fromSub (a : Window) (ha : a.region ⊆ (Window.interval l u).region)
        (hc : a.crosses (realPoly f p)) (hw : ∃ y ∈ a.region, (realPoly f p).IsRoot y) :
        Represents (realPoly f p) x a ∧ a.region ⊆ (Window.interval l u).region := by
      obtain ⟨y, hy, h⟩ := hw
      have eq := r.unique y (ha hy) h
      exact ⟨⟨eq ▸ hy, r.root, fun z hz => r.unique z (ha hz), hc⟩, ha⟩
    simp only [refine, ← show m = ExecutableIsolation.midpoint l u from rfl]
    by_cases he : DensePolynomial.eval p (m : K) = 0
    · rw [ite_eq_left he]
      exact fromSub (.point m) (fun y hy => by
        have eq : y = (m : ℝ) := hy
        rw [eq]
        exact ⟨hl, hu⟩) trivial
        ⟨(m : ℝ), rfl, (eval_zero_iff f p m).mp he⟩
    · rw [ite_eq_right he]
      by_cases hlc : DensePolynomial.eval p (l : K) * DensePolynomial.eval p (m : K) < 0
      · rw [ite_eq_left hlc]
        have hc := (bracket_iff f mono p l m).mp hlc
        exact fromSub (.interval l m) (fun _ h => ⟨h.1, h.2.trans hu⟩) hc
          (Isolation.crossing _ hl hc)
      · rw [ite_eq_right hlc]
        have hn : (realPoly f p).eval (m : ℝ) ≠ 0 := mt (eval_zero_iff f p m).mpr he
        have hc : (Window.interval m u).crosses (realPoly f p) :=
          bracket_right qc hn (mt (bracket_iff f mono p l m).mpr hlc)
        exact fromSub (.interval m u) (fun _ h => ⟨hl.trans h.1, h.2⟩) hc
          (Isolation.crossing _ hu hc)

omit mono [IsStrictOrderedRing K] in
theorem refine_width {p : Coefficients K} {w : Window} (hn : 0 ≤ width w) :
    width (refine p w) ≤ width w / 2 := by
  cases w with
  | point a => simp [refine, width]
  | interval l u =>
    simp only [refine]
    split
    · exact div_nonneg hn (by norm_num)
    · split <;> simp [width, ExecutableIsolation.midpoint] <;> linarith

def refineSteps (p : Coefficients K) : ℕ → Window → Window
  | 0, w => w
  | n+1, w => refine p (refineSteps p n w)

theorem refineSteps_correct {p : Coefficients K} {x : ℝ} {w : Window}
    (h : Represents (realPoly f p) x w) (n : ℕ) :
    Represents (realPoly f p) x (refineSteps p n w) ∧ (refineSteps p n w).region ⊆ w.region := by
  induction n with
  | zero => exact ⟨h, le_rfl⟩
  | succ n ih =>
    obtain ⟨hr, hs⟩ := refine_correct f mono ih.1
    exact ⟨hr, hs.trans ih.2⟩

omit mono in
private theorem width_nonneg_of_mem {w : Window} {x : ℝ} (h : x ∈ w.region) : 0 ≤ width w := by
  cases w with
  | point a => simp [width]
  | interval l u =>
    change x ∈ Ioo (l : ℝ) (u : ℝ) at h
    exact sub_nonneg.mpr (by exact_mod_cast (h.1.trans h.2).le)

theorem refineSteps_width {p : Coefficients K} {x : ℝ} {w : Window}
    (h : Represents (realPoly f p) x w) (n : ℕ) :
    width (refineSteps p n w) ≤ width w / 2^n := by
  induction n with
  | zero => simp [refineSteps]
  | succ n ih =>
    have hn := width_nonneg_of_mem (refineSteps_correct f mono h n).1.inside
    change width (refine p (refineSteps p n w)) ≤ _
    calc
      _ ≤ width (refineSteps p n w)/2 := refine_width hn
      _ ≤ (width w / 2^n)/2 := div_le_div_of_nonneg_right ih (by norm_num)
      _ = _ := by rw [pow_succ, div_div]

end Refine

section Sign

theorem divisor_crosses_iff {p q : Polynomial ℝ} {x : ℝ} {l u : ℚ}
    (r : Represents p x (.interval l u)) (hs : ¬p.derivative.IsRoot x) (hd : q ∣ p) :
    (Window.interval l u).crosses q ↔ q.IsRoot x := by
  have hlu : (l : ℝ) < (u : ℝ) := r.inside.1.trans r.inside.2
  obtain ⟨h, hp⟩ := hd
  constructor
  · intro cross
    obtain ⟨y, hy, hq⟩ := Isolation.crossing q hlu cross
    have hy' : p.IsRoot y := by simp only [hp, IsRoot.def, eval_mul, hq, zero_mul]
    rwa [r.unique y hy hy'] at hq
  · intro hroot
    obtain ⟨g,hg⟩ := (dvd_iff_isRoot.mpr hroot)
    have hn (y : ℝ) (hy : y ∈ Icc (l : ℝ) u) : g.eval y ≠ 0 := by
      intro hyz
      have qz : q.IsRoot y := by simp [hg, IsRoot.def, hyz]
      have pz : p.IsRoot y := by simp [hp, IsRoot.def, show q.eval y = 0 from qz]
      have cross : p.eval (l : ℝ) * p.eval (u : ℝ) < 0 := r.crosses
      have interior : y ∈ Ioo (l : ℝ) (u : ℝ) := by
        refine ⟨hy.1.lt_of_ne ?_, hy.2.lt_of_ne ?_⟩
        · intro e
          have hz : p.eval (l : ℝ) = 0 := e.symm ▸ pz
          simp [hz] at cross
        · intro e
          have hz : p.eval (u : ℝ) = 0 := e ▸ pz
          simp [hz] at cross
      have eq := r.unique y interior pz
      have gz : g.eval x = 0 := eq ▸ hyz
      apply hs
      simp [hp, hg, IsRoot.def, derivative_mul, gz]
    have b : 0 < g.eval (l : ℝ) * g.eval (u : ℝ) := by
      have nl := hn (l : ℝ) ⟨le_rfl, hlu.le⟩
      have nu := hn (u : ℝ) ⟨hlu.le, le_rfl⟩
      refine lt_of_le_of_ne (not_lt.mp fun hc => ?_) (mul_ne_zero nl nu).symm
      obtain ⟨y, hy, hz⟩ := Isolation.crossing g hlu hc
      exact hn y (Ioo_subset_Icc_self hy) hz
    change q.eval (l : ℝ) * q.eval (u : ℝ) < 0
    simp only [hg, eval_mul, eval_sub, eval_X, eval_C]
    calc
      _ = (((l : ℝ)-x)*((u : ℝ)-x)) * (g.eval (l : ℝ) * g.eval (u : ℝ)) := by ring
      _ < 0 := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos
        (sub_neg.mpr r.inside.1) (sub_pos.mpr r.inside.2)) b

variable (model : RealModel K)

/-- A gcd detects exact equality before refinement. Its root at the selected
    point is simple because it divides the squarefree source polynomial. -/
def zeroAtGeneral (r : Root model) (q : Coefficients K) : Bool :=
  match r.window with
  | .point a => decide (DensePolynomial.eval q (a : K) = 0)
  | .interval l u =>
    let g := DensePolynomial.gcd r.polynomial q
    decide (DensePolynomial.eval g (l : K) * DensePolynomial.eval g (u : K) < 0)

theorem zeroAtGeneral_correct (r : Root model) (q : Coefficients K) :
    zeroAtGeneral model r q = true ↔ (realPoly model.hom q).IsRoot r.value := by
  let f := model.hom
  have h := r.represents
  unfold zeroAtGeneral
  cases eq : r.window with
  | point a =>
    have e : r.value = (a : ℝ) := by
      rw [eq] at h
      exact h.inside
    simpa only [decide_eq_true_eq, e] using eval_zero_iff f q a
  | interval l u =>
    rw [eq] at h
    simp only [decide_eq_true_eq]
    let g := DensePolynomial.gcd r.polynomial q
    have cd : Quartic.CommonDivisors (realPoly f r.polynomial) (realPoly f q) (realPoly f g) :=
      DensePolynomial.gcd_spec f _ _
    rw [bracket_iff f model.strictMono g l u, divisor_crosses_iff h (r.simple _ h.root) cd.left]
    exact (cd.isRoot _).trans (and_iff_right h.root)

def zeroAt (r : Root model) : Coefficients K → Bool
  | [] => true
  | [a] => decide (a = 0)
  | a :: b :: q => zeroAtGeneral model r (a :: b :: q)

theorem zeroAt_correct (r : Root model) (q : Coefficients K) :
    zeroAt model r q = true ↔ (realPoly model.hom q).IsRoot r.value := by
  rcases q with _ | ⟨a, _ | ⟨b, q⟩⟩
  · simp [zeroAt, realPoly, DensePolynomial.polynomial, IsRoot.def]
  · simp [zeroAt, realPoly, DensePolynomial.polynomial, IsRoot.def, map_eq_zero_iff _ model.hom.injective]
  · exact zeroAtGeneral_correct model r _

/-- Replace a defining polynomial by a smaller common divisor when that
    divisor isolates the very same real root in the current window. -/
def Root.shrinkCore (r : Root model) (q : Coefficients K) : {s : Root model // s.value = r.value} := by
  let g := DensePolynomial.gcd r.polynomial q
  if hg : g.length < r.polynomial.length then
    have dvd : realPoly model.hom g ∣ realPoly model.hom r.polynomial :=
      ((DensePolynomial.gcd_spec model.hom r.polynomial q (realPoly model.hom g)).mp dvd_rfl).1
    have included : ∀ t, (realPoly model.hom g).IsRoot t →
        (realPoly model.hom r.polynomial).IsRoot t := by
      intro t h
      obtain ⟨d,hd⟩ := dvd
      rw [hd]
      simp [IsRoot.def, IsRoot.def.mp h]
    have simple (x : ℝ) (hx : (realPoly model.hom g).IsRoot x) :
        ¬(realPoly model.hom g).derivative.IsRoot x := by
      intro h
      apply r.simple x (included x hx)
      obtain ⟨d,hd⟩ := dvd
      rw [hd, derivative_mul]
      simp only [IsRoot.def, eval_add, eval_mul, IsRoot.def.mp h, IsRoot.def.mp hx, zero_mul, add_zero]
    let test := match r.window with
      | .point a => decide (DensePolynomial.eval g (a : K) = 0)
      | .interval l u =>
        decide (DensePolynomial.eval g (l : K) * DensePolynomial.eval g (u : K) < 0)
    if h : test = true then
      have rootAndCross : (realPoly model.hom g).IsRoot r.value ∧
          r.window.crosses (realPoly model.hom g) := by
        have v := r.represents
        dsimp only [test] at h
        cases e : r.window with
        | point a =>
          rw [e] at v h
          exact ⟨(show r.value = (a : ℝ) from v.inside).symm ▸
            (eval_zero_iff model.hom g a).mp (of_decide_eq_true h), trivial⟩
        | interval l u =>
          rw [e] at v h
          have cross := (bracket_iff model.hom model.strictMono g l u).mp (of_decide_eq_true h)
          exact ⟨(divisor_crosses_iff v (r.simple _ v.root) dvd).mp cross,cross⟩
      let s : Root model := ⟨g,r.window,⟨r.value,⟨r.represents.inside,rootAndCross.1⟩,
        fun x hx => r.represents.unique x hx.1 (included _ hx.2)⟩,rootAndCross.2,simple⟩
      exact ⟨s,r.represents.unique _ s.represents.inside (included _ s.represents.root)⟩
    else exact ⟨r,rfl⟩
  else exact ⟨r,rfl⟩

def Root.shrink (r : Root model) (q : Coefficients K) : {s : Root model // s.value = r.value} :=
  if q.length ≤ 1 || r.polynomial.length ≤ q.length then ⟨r,rfl⟩
  else r.shrinkCore model q

def Root.shrinkAll (r : Root model) :
    List (Coefficients K) → {s : Root model // s.value = r.value}
  | [] => ⟨r,rfl⟩
  | q :: qs =>
    let a := r.shrink model q
    let b := a.val.shrinkAll qs
    ⟨b.val,b.property.trans a.property⟩

include mono

omit mono in
def bounded (B : ℚ) : Window → Prop
  | .point a => -B ≤ a ∧ a ≤ B
  | .interval l u => -B ≤ l ∧ u ≤ B

omit mono in
def extent : Window → ℚ
  | .point a => |a|+1
  | .interval l u => max |l| |u| + 1

omit mono in
theorem extent_positive (w : Window) : 0 < extent w := by
  cases w with
  | point a => unfold extent; positivity
  | interval l u =>
    unfold extent
    have h : 0 ≤ max |l| |u| := (abs_nonneg l).trans (le_max_left _ _)
    linarith

omit mono in
theorem bounded_extent (w : Window) : bounded (extent w) w := by
  cases w with
  | point a =>
    unfold bounded extent
    exact ⟨by linarith [neg_abs_le a], by linarith [le_abs_self a]⟩
  | interval l u =>
    unfold bounded extent
    exact ⟨by linarith [neg_abs_le l, le_max_left |l| |u|],
      by linarith [le_abs_self u, le_max_right |l| |u|]⟩

omit mono [IsStrictOrderedRing K] in
theorem bounded_refine {B : ℚ} {p : Coefficients K} {w : Window} {x : ℝ}
    (h : bounded B w) (hx : x ∈ w.region) : bounded B (refine p w) := by
  cases w with
  | point a => exact h
  | interval l u =>
    have hlu : l ≤ u := by exact_mod_cast hx.1.le.trans hx.2.le
    have hm := show l ≤ ExecutableIsolation.midpoint l u ∧ ExecutableIsolation.midpoint l u ≤ u by
      unfold ExecutableIsolation.midpoint
      constructor <;> linarith
    simp only [refine]
    split
    · exact ⟨h.1.trans hm.1, hm.2.trans h.2⟩
    · split
      · exact ⟨h.1, hm.2.trans h.2⟩
      · exact ⟨h.1.trans hm.1, h.2⟩

theorem bounded_steps {B : ℚ} {p : Coefficients K} {w : Window} {x : ℝ}
    (h : bounded B w) (hr : Represents (realPoly f p) x w) (n : ℕ) :
    bounded B (refineSteps p n w) := by
  induction n with
  | zero => exact h
  | succ n ih => exact bounded_refine ih (refineSteps_correct f mono hr n).1.inside

/-- A sign is known at a rational point, or on an interval whose magnitude
    test excludes zero. The zero decision is a separate gcd test. -/
def probe (t : Test K) : Window → Option Side
  | .point a => some (side (DensePolynomial.eval t.poly (a : K)) 0)
  | .interval l u =>
    if t.noRoot l u then some (side (DensePolynomial.eval t.poly (l : K)) 0) else none

omit [IsStrictOrderedRing K] in
theorem map_side (a : K) : side a 0 = side (f a) 0 := by
  have h₁ : a < 0 ↔ f a < 0 := by simpa using (mono.lt_iff_lt (a := a) (b := 0)).symm
  have h₂ : a = 0 ↔ f a = 0 := by simp
  simp only [side, h₁, h₂]

theorem probe_correct (q : Coefficients K) {B : ℚ} {w : Window} {x : ℝ}
    (hb : 0 ≤ B) (h : bounded B w) (hx : x ∈ w.region) {s : Side}
    (he : probe (prepare q B) w = some s) : side ((realPoly f q).eval x) 0 = s := by
  cases w with
  | point a =>
    have eq : x = (a : ℝ) := hx
    simpa only [probe, prepare, Option.some.injEq, map_side f mono, map_eval f, eq] using he
  | interval l u =>
    simp only [probe] at he
    split at he
    · rename_i hg
      have g := sign_on q B f mono hb h.1 h.2 ((noRoot_iff q B f mono l u).mp hg)
      have hl : (l : ℝ) ∈ Icc (l : ℝ) u := ⟨le_rfl, hx.1.le.trans hx.2.le⟩
      have eq := Option.some.inj he
      rw [prepare, map_side f mono, map_eval f] at eq
      rw [← eq]
      rcases g with g | g
      · have ax := g x (Ioo_subset_Icc_self hx)
        have al := g (l : ℝ) hl
        simp [side, ax.not_gt, ax.ne', al.not_gt, al.ne']
      · have ax := g x (Ioo_subset_Icc_self hx)
        have al := g (l : ℝ) hl
        simp [side, ax, al]
    · contradiction

omit mono in
theorem probe_exists (r : Root model) (q : Coefficients K)
    (hn : ¬(realPoly model.hom q).IsRoot r.value) :
    ∃ n, (probe (prepare q (extent r.window)) (refineSteps r.polynomial n r.window)).isSome = true := by
  let f := model.hom
  have mono := model.strictMono
  let B := extent r.window
  let D := f (hornerBounds (B : K) q).2
  let y := (realPoly f q).eval r.value
  have hp : 0 < |y| := abs_pos.mpr hn
  have hB : (0 : ℚ) < B := extent_positive _
  have hD : 0 ≤ D := by
    have hb : (0 : K) ≤ (B : K) := by exact_mod_cast hB.le
    simpa [D] using mono.monotone (hornerBounds_nonneg hb q).2
  let δ := |y|/(2*D+1)
  have hdenom : 0 < 2*D+1 := by linarith
  have hd : 0 < δ := div_pos hp hdenom
  obtain ⟨n, hN⟩ := exists_nat_gt (((width r.window : ℚ) : ℝ)/δ)
  have growth : (n : ℝ) < (2 : ℝ)^n := by exact_mod_cast n.lt_two_pow_self
  have hw : (width (refineSteps r.polynomial n r.window) : ℝ) ≤ δ := by
    have h := (div_lt_iff₀ hd).mp (hN.trans growth)
    have w := refineSteps_width f mono r.represents n
    have w' : (width (refineSteps r.polynomial n r.window) : ℝ) ≤
        (width r.window : ℝ)/(2 : ℝ)^n := by exact_mod_cast w
    exact w'.trans ((div_lt_iff₀ (by positivity)).mpr (by rw [mul_comm]; exact h)).le
  let w := refineSteps r.polynomial n r.window
  have hbound : bounded B w := bounded_steps f mono (bounded_extent _) r.represents n
  have hx : r.value ∈ w.region := (refineSteps_correct f mono r.represents n).1.inside
  refine ⟨n, ?_⟩
  change (probe (prepare q B) w).isSome = _
  cases eq : w with
  | point a => simp [probe]
  | interval l u =>
    rw [eq] at hbound hx
    have yes : (prepare q B).noRoot l u = true := by
      rw [noRoot_iff q B f mono]
      by_contra! bad
      have wbound : (u : ℝ)-(l : ℝ) ≤ δ := by
        change (width w : ℝ) ≤ δ at hw
        simpa only [eq, width, Rat.cast_sub] using hw
      have ev := close_eval q B f mono hB.le hbound.1 hbound.2 (Ioo_subset_Icc_self hx)
      have tri : |y| ≤ |y-(realPoly f q).eval (l : ℝ)|+|(realPoly f q).eval (l : ℝ)| := by
        simpa only [sub_add_cancel] using abs_add_le (y-(realPoly f q).eval (l : ℝ))
          ((realPoly f q).eval (l : ℝ))
      have e : δ*(2*D+1) = |y| := div_mul_cancel₀ _ hdenom.ne'
      have span := mul_le_mul_of_nonneg_left wbound hD
      change |y-(realPoly f q).eval (l : ℝ)| ≤ D * ((u : ℝ)-l) at ev
      change |(realPoly f q).eval (l : ℝ)| ≤ D * ((u : ℝ)-l) at bad
      nlinarith only [ev, tri, span, bad, e, hd]
    simp [probe, yes]

omit mono in
/-- Exact evaluation sign at an algebraic root. A nonzero result is found
    by bisection of that root's own window, with a proof of termination. -/
def signGeneral (r : Root model) (q : Coefficients K) : Side :=
  if hz : zeroAt model r q = true then .on
  else
    let n := Nat.find (probe_exists model r q (mt (zeroAt_correct model r q).mpr hz))
    (probe (prepare q (extent r.window)) (refineSteps r.polynomial n r.window)).getD .on

omit mono in
theorem signGeneral_correct (r : Root model) (q : Coefficients K) :
    signGeneral model r q = side ((realPoly model.hom q).eval r.value) 0 := by
  rw [signGeneral]
  split
  · rename_i hz
    have h : (realPoly model.hom q).eval r.value = 0 := (zeroAt_correct model r q).mp hz
    simp [h]
  · rename_i hz
    let n := Nat.find (probe_exists model r q (mt (zeroAt_correct model r q).mpr hz))
    let w := refineSteps r.polynomial n r.window
    have ok : (probe (prepare q (extent r.window)) w).isSome = true :=
      Nat.find_spec (probe_exists model r q (mt (zeroAt_correct model r q).mpr hz))
    have bounded := bounded_steps model.hom model.strictMono (bounded_extent _) r.represents n
    have mem := (refineSteps_correct model.hom model.strictMono r.represents n).1.inside
    cases eq : probe (prepare q (extent r.window)) w with
    | none => simp [eq] at ok
    | some s =>
      change (probe (prepare q (extent r.window)) w).getD .on = _
      rw [eq]
      exact (probe_correct model.hom model.strictMono q (extent_positive _).le bounded mem eq).symm

omit mono in
def sign (r : Root model) : Coefficients K → Side
  | [] => .on
  | [a] => side a 0
  | a :: b :: q =>
    match r.window with
    | .point t => side (DensePolynomial.eval (a :: b :: q) (t : K)) 0
    | .interval _ _ => signGeneral model r (a :: b :: q)

omit mono in
theorem sign_correct (r : Root model) (q : Coefficients K) :
    sign model r q = side ((realPoly model.hom q).eval r.value) 0 := by
  rcases q with _ | ⟨a, _ | ⟨b, q⟩⟩
  · simp [sign, realPoly, DensePolynomial.polynomial]
  · simpa [sign, realPoly, DensePolynomial.polynomial] using map_side model.hom model.strictMono a
  · cases h : r.window with
    | point t =>
      have ht := r.represents.inside
      rw [h] at ht
      have e : r.value = (t : ℝ) := ht
      simp only [sign, h]
      rw [e, map_side model.hom model.strictMono, map_eval model.hom]
    | interval l u =>
      simpa only [sign, h] using signGeneral_correct model r (a :: b :: q)

end Sign
end CertifiedTopology.AlgebraicRoot
