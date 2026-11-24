module

public import CertifiedTopology.DensePolynomial
public import CertifiedTopology.Isolation
public import CertifiedTopology.QuarticProjection
public import Mathlib.Analysis.Polynomial.CauchyBound

@[expose] public section

namespace CertifiedTopology.ExecutableIsolation

open Set Polynomial
open DensePolynomial hiding polynomial eval add sub mul derivative gcd eval₂

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The embedding is needed in proofs. Erasing this witness keeps all real
    arithmetic out of the executable coefficient-field operations. -/
structure RealModel (K : Type) [Field K] [LinearOrder K] : Prop where
  exists_embedding : ∃ f : K →+* ℝ, StrictMono f

noncomputable def RealModel.hom (model : RealModel K) : K →+* ℝ :=
  model.exists_embedding.choose

omit [IsStrictOrderedRing K] in
theorem RealModel.strictMono (model : RealModel K) : StrictMono model.hom :=
  model.exists_embedding.choose_spec

theorem RealModel.rational : RealModel ℚ := ⟨Rat.castHom ℝ, Rat.cast_strictMono⟩

omit [IsStrictOrderedRing K] in
theorem RealModel.hom_eq (model : RealModel K) (g : K →+* ℝ) (hg : StrictMono g) :
    model.hom = g := by
  ext x
  rcases lt_trichotomy (model.hom x) (g x) with hx | hx | hx
  · obtain ⟨q, h₁, h₂⟩ := exists_rat_btwn hx
    have a : x < (q : K) := model.strictMono.lt_iff_lt.mp (by simpa using h₁)
    have b : (q : K) < x := hg.lt_iff_lt.mp (by simpa using h₂)
    exact (a.asymm b).elim
  · exact hx
  · obtain ⟨q, h₁, h₂⟩ := exists_rat_btwn hx
    have a : x < (q : K) := hg.lt_iff_lt.mp (by simpa using h₁)
    have b : (q : K) < x := model.strictMono.lt_iff_lt.mp (by simpa using h₂)
    exact (a.asymm b).elim

/-- A rational root, or an open rational interval containing one simple
    root. A root at a subdivision endpoint is represented only once. -/
inductive Window where
  | point (value : ℚ)
  | interval (lower upper : ℚ)
  deriving Repr, DecidableEq

def Window.region : Window → Set ℝ
  | .point q => {(q : ℝ)}
  | .interval l u => Ioo (l : ℝ) (u : ℝ)

def Window.crosses (p : Polynomial ℝ) : Window → Prop
  | .point _ => True
  | .interval l u => p.eval (l : ℝ) * p.eval (u : ℝ) < 0

def Window.precedes (w v : Window) : Prop :=
  ∀ x ∈ w.region, ∀ y ∈ v.region, x < y

structure IsolatesOn (p : Polynomial ℝ) (A : Set ℝ) (ws : List Window) : Prop where
  ordered : ws.Pairwise Window.precedes
  inside : ∀ w ∈ ws, w.region ⊆ A
  brackets : ∀ w ∈ ws, w.crosses p
  unique : ∀ w ∈ ws, ∃! x, x ∈ w.region ∧ p.IsRoot x
  covers : ∀ x ∈ A, p.IsRoot x → ∃ w ∈ ws, x ∈ w.region

/-- A bound on the magnitude on `[-B,B]` and a Lipschitz constant there.
    Both numbers are computed by one Horner pass. -/
def hornerBounds (B : K) : Coefficients K → K × K
  | [] => (0, 0)
  | a :: p =>
    let (m, d) := hornerBounds B p
    (|a| + B * m, m + B * d)

theorem hornerBounds_nonneg {B : K} (hB : 0 ≤ B) (p : Coefficients K) :
    0 ≤ (hornerBounds B p).1 ∧ 0 ≤ (hornerBounds B p).2 := by
  induction p with
  | nil => simp [hornerBounds]
  | cons a p ih =>
    simp only [hornerBounds]
    exact ⟨add_nonneg (abs_nonneg _) (mul_nonneg hB ih.1),
      add_nonneg ih.1 (mul_nonneg hB ih.2)⟩

private theorem hom_abs (f : K →+* ℝ) (mono : StrictMono f) (a : K) : f |a| = |f a| := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (by simpa using mono.monotone h)]
  · rw [abs_of_nonpos h, map_neg, abs_of_nonpos (by simpa using mono.monotone h)]

theorem hornerBounds_spec (f : K →+* ℝ) (mono : StrictMono f) (B : K) (p : Coefficients K) :
    (∀ x : ℝ, |x| ≤ f B → |DensePolynomial.eval₂ f x p| ≤ f (hornerBounds B p).1) ∧
    (∀ x y : ℝ, |x| ≤ f B → |y| ≤ f B →
      |DensePolynomial.eval₂ f x p - DensePolynomial.eval₂ f y p| ≤ f (hornerBounds B p).2 * |x-y|) := by
  induction p with
  | nil => simp [DensePolynomial.eval₂, hornerBounds]
  | cons a p ih =>
    let m := f (hornerBounds B p).1
    let d := f (hornerBounds B p).2
    constructor
    · intro x hx
      simp only [DensePolynomial.eval₂, hornerBounds, map_add, map_mul, hom_abs f mono]
      calc
        |f a + x * DensePolynomial.eval₂ f x p| ≤ |f a| + |x| * |DensePolynomial.eval₂ f x p| := by
          simpa only [abs_mul] using abs_add_le (f a) (x * DensePolynomial.eval₂ f x p)
        _ ≤ _ := add_le_add_right (mul_le_mul hx (ih.1 x hx) (abs_nonneg _) ((abs_nonneg x).trans hx)) _
    · intro x y hx hy
      have hb : 0 ≤ f B := (abs_nonneg x).trans hx
      simp only [DensePolynomial.eval₂, hornerBounds, map_add, map_mul]
      calc
        |f a + x * DensePolynomial.eval₂ f x p - (f a + y * DensePolynomial.eval₂ f y p)| =
            |x * (DensePolynomial.eval₂ f x p - DensePolynomial.eval₂ f y p) + (x-y) * DensePolynomial.eval₂ f y p| := by
              congr 1
              ring
        _ ≤ |x| * |DensePolynomial.eval₂ f x p - DensePolynomial.eval₂ f y p| + |x-y| * |DensePolynomial.eval₂ f y p| := by
          simpa only [abs_mul] using abs_add_le (x * (DensePolynomial.eval₂ f x p - DensePolynomial.eval₂ f y p)) ((x-y) * DensePolynomial.eval₂ f y p)
        _ ≤ f B * (d * |x-y|) + |x-y| * m := by
          exact add_le_add (mul_le_mul hx (ih.2 x y hx hy) (abs_nonneg _) hb)
            (mul_le_mul_of_nonneg_left (ih.1 y hy) (abs_nonneg _))
        _ = _ := by dsimp [m,d]; ring

section Subdivision

variable (p : Coefficients K) (B : ℚ)

/-- Prepared quantities are shared across all intervals in the subdivision. -/
structure Test (K : Type) where
  poly : Coefficients K
  deriv : Coefficients K
  lip : K
  derivLip : K

def prepare (p : Coefficients K) (B : ℚ) : Test K :=
  let deriv := DensePolynomial.derivative p
  ⟨p, deriv, (hornerBounds (B : K) p).2, (hornerBounds (B : K) deriv).2⟩

def Test.noRoot (t : Test K) (l u : ℚ) : Bool :=
  decide (t.lip * ((u-l : ℚ) : K) < |DensePolynomial.eval t.poly (l : K)|)

def Test.monotone (t : Test K) (l u : ℚ) : Bool :=
  decide (t.derivLip * ((u-l : ℚ) : K) < |DensePolynomial.eval t.deriv (l : K)|)

def Test.ready (t : Test K) (l u : ℚ) : Bool := t.noRoot l u || t.monotone l u

def Test.emit (t : Test K) (l u : ℚ) : List Window :=
  if t.noRoot l u then []
  else
    let a := DensePolynomial.eval t.poly (l : K)
    let b := DensePolynomial.eval t.poly (u : K)
    if b = 0 then [.point u]
    else if a*b < 0 then [.interval l u] else []

def midpoint (l u : ℚ) : ℚ := (l+u)/2

def Test.readyAt (t : Test K) : ℕ → ℚ → ℚ → Bool
  | 0, l, u => t.ready l u
  | n+1, l, u =>
    t.ready l u || (t.readyAt n l (midpoint l u) && t.readyAt n (midpoint l u) u)

/-- Refine only intervals that have not yet passed either local test. -/
def Test.run (t : Test K) : ℕ → ℚ → ℚ → List Window
  | 0, l, u => t.emit l u
  | n+1, l, u =>
    if t.ready l u then t.emit l u
    else t.run n l (midpoint l u) ++ t.run n (midpoint l u) u


variable (f : K →+* ℝ) (mono : StrictMono f)

noncomputable abbrev realPoly (f : K →+* ℝ) (p : Coefficients K) : Polynomial ℝ :=
  (DensePolynomial.polynomial p).map f

theorem map_eval (r : ℚ) (p : Coefficients K) :
    f (DensePolynomial.eval p (r : K)) = (realPoly f p).eval (r : ℝ) := by
  rw [← eval₂_correct]
  change f (DensePolynomial.eval₂ (RingHom.id K) (r : K) p) = DensePolynomial.eval₂ f (r : ℝ) p
  induction p with
  | nil => simp [DensePolynomial.eval₂]
  | cons a p ih => simp only [DensePolynomial.eval₂, RingHom.id_apply, map_add, map_mul, map_ratCast, ih]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem realPoly_derivative (p : Coefficients K) :
    realPoly f (DensePolynomial.derivative p) = (realPoly f p).derivative := by
  simp only [realPoly, polynomial_derivative, derivative_map]

include mono

theorem noRoot_iff (l u : ℚ) :
    (prepare p B).noRoot l u = true ↔
      f (hornerBounds (B : K) p).2 * ((u : ℝ)-l) < |(realPoly f p).eval (l : ℝ)| := by
  rw [Test.noRoot, decide_eq_true_eq, ← mono.lt_iff_lt]
  simp only [prepare, map_mul, map_ratCast, Rat.cast_sub, map_sub, hom_abs f mono, map_eval f]

private theorem monotone_iff (l u : ℚ) :
    (prepare p B).monotone l u = true ↔
      f (hornerBounds (B : K) (DensePolynomial.derivative p)).2 * ((u : ℝ)-l) <
        |(realPoly f p).derivative.eval (l : ℝ)| := by
  rw [Test.monotone, decide_eq_true_eq, ← mono.lt_iff_lt]
  simp only [prepare, map_mul, map_ratCast, Rat.cast_sub, map_sub, hom_abs f mono, map_eval f,
    realPoly_derivative]

theorem close_eval {l u : ℚ} {x : ℝ}
    (hB : (0 : ℚ) ≤ B) (hL : -B ≤ l) (hU : u ≤ B) (hx : x ∈ Icc (l : ℝ) u) :
    |(realPoly f p).eval x - (realPoly f p).eval (l : ℝ)| ≤
      f (hornerBounds (B : K) p).2 * ((u : ℝ)-l) := by
  have hL' : -(B : ℝ) ≤ (l : ℝ) := by exact_mod_cast hL
  have hU' : (u : ℝ) ≤ B := by exact_mod_cast hU
  have hB' : (0 : K) ≤ (B : K) := by exact_mod_cast hB
  obtain ⟨hl, hu⟩ := hx
  have ax : |x| ≤ f (B : K) := by simpa only [map_ratCast] using abs_le.mpr ⟨hL'.trans hl, hu.trans hU'⟩
  have al : |(l : ℝ)| ≤ f (B : K) := by
    simpa only [map_ratCast] using abs_le.mpr ⟨hL', hl.trans (hu.trans hU')⟩
  have bnd := (hornerBounds_spec f mono (B : K) p).2 x (l : ℝ) ax al
  rw [eval₂_correct, eval₂_correct, abs_of_nonneg (sub_nonneg.mpr hl)] at bnd
  exact bnd.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right hu _)
    (by simpa using mono.monotone (hornerBounds_nonneg hB' p).2))

theorem sign_on {l u : ℚ} (hB : (0 : ℚ) ≤ B) (hL : -B ≤ l) (hU : u ≤ B)
    (ht : f (hornerBounds (B : K) p).2 * ((u : ℝ)-l) < |(realPoly f p).eval (l : ℝ)|) :
    (∀ x ∈ Icc (l : ℝ) u, 0 < (realPoly f p).eval x) ∨
      (∀ x ∈ Icc (l : ℝ) u, (realPoly f p).eval x < 0) := by
  rcases le_total 0 ((realPoly f p).eval (l : ℝ)) with h | h
  · left
    intro x hx
    have d := (abs_lt.mp ((close_eval p B f mono hB hL hU hx).trans_lt ht)).1
    rw [abs_of_nonneg h] at d
    linarith
  · right
    intro x hx
    have d := (abs_lt.mp ((close_eval p B f mono hB hL hU hx).trans_lt ht)).2
    rw [abs_of_nonpos h] at d
    linarith

private theorem test_strict {l u : ℚ} (hB : (0 : ℚ) ≤ B) (hL : -B ≤ l) (hU : u ≤ B)
    (ht : (prepare p B).monotone l u = true) :
    StrictMonoOn (realPoly f p).eval (Icc (l : ℝ) u) ∨
      StrictAntiOn (realPoly f p).eval (Icc (l : ℝ) u) := by
  have H := sign_on (DensePolynomial.derivative p) B f mono hB hL hU
    (by
      rw [realPoly_derivative]
      exact (monotone_iff p B f mono l u).mp ht)
  simp only [realPoly_derivative] at H
  rcases H with H | H
  · left
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (realPoly f p).continuousOn
    intro x hx
    rw [(realPoly f p).deriv, interior_Icc] at *
    exact H x (Ioo_subset_Icc_self hx)
  · right
    apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (realPoly f p).continuousOn
    intro x hx
    rw [(realPoly f p).deriv, interior_Icc] at *
    exact H x (Ioo_subset_Icc_self hx)

omit mono in
private theorem IsolatesOn.empty {p : Polynomial ℝ} {A : Set ℝ}
    (no : ∀ x ∈ A, ¬p.IsRoot x) : IsolatesOn p A [] := by
  refine ⟨by simp, by simp, by simp, by simp, ?_⟩
  intro x hx he
  exact (no x hx he).elim

omit mono in
private theorem IsolatesOn.single {p : Polynomial ℝ} {A E : Set ℝ} {w : Window}
    (hsub : w.region ⊆ A) (hc : w.crosses p) (hw : ∃ x, x ∈ w.region ∧ p.IsRoot x)
    (hE : A ⊆ E) (inj : InjOn p.eval E) : IsolatesOn p A [w] := by
  obtain ⟨x, hx, he⟩ := hw
  have eq y (hy : y ∈ A) (h : p.IsRoot y) : y = x :=
    inj (hE hy) (hE (hsub hx)) (h.trans he.symm)
  refine ⟨by simp, by simpa using hsub, by simpa using hc, ?_, ?_⟩
  · simpa only [List.mem_singleton, forall_eq] using
      (show ∃! y, y ∈ w.region ∧ p.IsRoot y from
        ⟨x, ⟨hx, he⟩, fun y hy => eq y (hsub hy.1) hy.2⟩)
  · intro y hy h
    exact ⟨w, by simp, by rwa [eq y hy h]⟩

private theorem emit_correct {l u : ℚ} (hB : (0 : ℚ) ≤ B) (hL : -B ≤ l) (hU : u ≤ B)
    (hlu : l < u) (ht : (prepare p B).ready l u = true) :
    IsolatesOn (realPoly f p) (Ioc (l : ℝ) u) ((prepare p B).emit l u) := by
  unfold Test.emit
  have hlu' : (l : ℝ) < u := by exact_mod_cast hlu
  cases h : (prepare p B).noRoot l u with
  | true =>
    simp only [ite_true]
    have sg := sign_on p B f mono hB hL hU ((noRoot_iff p B f mono l u).mp h)
    apply IsolatesOn.empty
    intro x hx he
    rcases sg with sg | sg
    · exact (sg x (Ioc_subset_Icc_self hx)).ne' he
    · exact (sg x (Ioc_subset_Icc_self hx)).ne he
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hm : (prepare p B).monotone l u = true := by simpa [Test.ready, h] using ht
    let q := realPoly f p
    have strict := test_strict p B f mono hB hL hU hm
    have inj : InjOn q.eval (Icc (l : ℝ) u) := strict.elim StrictMonoOn.injOn StrictAntiOn.injOn
    have ev (r : ℚ) : f (DensePolynomial.eval (prepare p B).poly (r : K)) = q.eval (r : ℝ) :=
      map_eval f r p
    have e_zero : DensePolynomial.eval (prepare p B).poly (u : K) = 0 ↔ q.eval (u : ℝ) = 0 := by
      rw [← (map_eq_zero_iff f f.injective), ev]
    have e_cross :
        DensePolynomial.eval (prepare p B).poly (l : K) * DensePolynomial.eval (prepare p B).poly (u : K) < 0 ↔
          q.eval (l : ℝ) * q.eval (u : ℝ) < 0 := by
      rw [← mono.lt_iff_lt, map_mul, ev, ev, map_zero]
    rw [ite_congr (propext e_zero) (fun _ => rfl) (fun _ => rfl)]
    split
    · rename_i hu
      apply IsolatesOn.single (w := .point u) (E := Icc (l : ℝ) u) _ True.intro _ Ioc_subset_Icc_self inj
      · intro x hx
        have eq : x = (u : ℝ) := hx
        exact ⟨eq ▸ hlu', eq ▸ le_rfl⟩
      · exact ⟨(u : ℝ), by simp [Window.region], hu⟩
    · rename_i hn
      rw [ite_congr (propext e_cross) (fun _ => rfl) (fun _ => rfl)]
      split
      · rename_i hc
        exact IsolatesOn.single Ioo_subset_Ioc_self hc (Isolation.crossing q hlu' hc)
          Ioc_subset_Icc_self inj
      · rename_i hc
        apply IsolatesOn.empty
        intro x hx he
        have heq : q.eval x = 0 := he
        have hxu : x < (u : ℝ) := hx.2.lt_of_ne (fun e => hn (e ▸ heq))
        have hl : (l : ℝ) ∈ Icc (l : ℝ) u := ⟨le_rfl, hlu'.le⟩
        have hu : (u : ℝ) ∈ Icc (l : ℝ) u := ⟨hlu'.le, le_rfl⟩
        rcases strict with a | a
        · exact hc (mul_neg_of_neg_of_pos (lt_of_lt_of_eq (a hl (Ioc_subset_Icc_self hx) hx.1) heq)
            (heq ▸ a (Ioc_subset_Icc_self hx) hu hxu))
        · exact hc (mul_neg_of_pos_of_neg (heq ▸ a hl (Ioc_subset_Icc_self hx) hx.1)
            ((a (Ioc_subset_Icc_self hx) hu hxu).trans_eq heq))

omit mono in
private theorem IsolatesOn.append {q : Polynomial ℝ} {l m u : ℝ} {ws vs : List Window}
    (hl : l ≤ m) (hu : m ≤ u)
    (h : IsolatesOn q (Ioc l m) ws) (h' : IsolatesOn q (Ioc m u) vs) :
    IsolatesOn q (Ioc l u) (ws ++ vs) := by
  refine ⟨List.pairwise_append.mpr ⟨h.ordered, h'.ordered, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro w hw v hv x hx y hy
    exact ((h.inside w hw) hx).2.trans_lt ((h'.inside v hv) hy).1
  · intro w hw x hx
    rcases List.mem_append.mp hw with hw | hw
    · exact ⟨((h.inside w hw) hx).1, ((h.inside w hw) hx).2.trans hu⟩
    · exact ⟨hl.trans_lt ((h'.inside w hw) hx).1, ((h'.inside w hw) hx).2⟩
  · intro w hw
    exact (List.mem_append.mp hw).elim (h.brackets w) (h'.brackets w)
  · intro w hw
    exact (List.mem_append.mp hw).elim (h.unique w) (h'.unique w)
  · intro x hx hq
    by_cases hm : x ≤ m
    · obtain ⟨w,hw,he⟩ := h.covers x ⟨hx.1,hm⟩ hq
      exact ⟨w,List.mem_append_left _ hw,he⟩
    · obtain ⟨w,hw,he⟩ := h'.covers x ⟨lt_of_not_ge hm,hx.2⟩ hq
      exact ⟨w,List.mem_append_right _ hw,he⟩


omit mono in
private theorem midpoint_between {l u : ℚ} (h : l < u) :
    l < midpoint l u ∧ midpoint l u < u := by
  unfold midpoint
  constructor <;> linarith

theorem run_correct (n : ℕ) {l u : ℚ} (hB : (0 : ℚ) ≤ B) (hL : -B ≤ l) (hU : u ≤ B)
    (hlu : l < u) (ht : (prepare p B).readyAt n l u = true) :
    IsolatesOn (realPoly f p) (Ioc (l : ℝ) u) ((prepare p B).run n l u) := by
  induction n generalizing l u with
  | zero => exact emit_correct p B f mono hB hL hU hlu ht
  | succ n ih =>
    simp only [Test.readyAt, Test.run] at ht ⊢
    by_cases h : (prepare p B).ready l u = true
    · simpa only [h, ite_true] using emit_correct p B f mono hB hL hU hlu h
    · have eq : (prepare p B).ready l u = false := Bool.eq_false_iff.mpr h
      simp only [eq, Bool.false_or, Bool.and_eq_true] at ht
      have ⟨hl, hu⟩ := midpoint_between hlu
      have hl' : (l : ℝ) ≤ (midpoint l u : ℝ) := by exact_mod_cast hl.le
      have hu' : (midpoint l u : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu.le
      simp only [eq, Bool.false_eq_true, ite_false]
      exact IsolatesOn.append hl' hu' (ih hL (hu.le.trans hU) hl ht.1)
        (ih (hL.trans hl.le) hU hu ht.2)

private theorem positive_uniform_width (hB : (0 : ℚ) < B)
    (simple : ∀ x, (realPoly f p).IsRoot x → ¬(realPoly f p).derivative.IsRoot x) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ l u : ℚ, -B ≤ l → l < u → u ≤ B → (u : ℝ) - l ≤ δ →
      (prepare p B).ready l u = true := by
  let q := realPoly f p
  let quality := fun x : ℝ => max |q.eval x| |q.derivative.eval x|
  have cont : Continuous quality := q.continuous.abs.max q.derivative.continuous.abs
  have hb : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.mpr (by linarith : -(B : ℝ) ≤ (B : ℝ))) cont.continuousOn
  have pos : 0 < quality x₀ := by
    by_contra! h
    have e := max_le_iff.mp (show max |q.eval x₀| |q.derivative.eval x₀| ≤ 0 from h)
    have he : q.IsRoot x₀ := abs_eq_zero.mp (le_antisymm e.1 (abs_nonneg _))
    have he' : q.derivative.IsRoot x₀ := abs_eq_zero.mp (le_antisymm e.2 (abs_nonneg _))
    exact simple _ he he'
  let M := f (hornerBounds (B : K) p).2
  let N := f (hornerBounds (B : K) (DensePolynomial.derivative p)).2
  have hk : (0 : K) ≤ (B : K) := by exact_mod_cast hB.le
  have hm : 0 ≤ M := by simpa [M] using mono.monotone (hornerBounds_nonneg hk p).2
  have hn : 0 ≤ N := by
    simpa [N] using mono.monotone (hornerBounds_nonneg hk (DensePolynomial.derivative p)).2
  let δ := quality x₀ / (M+N+1)
  have hp : 0 < M + N + 1 := by linarith
  have hδ : 0 < δ := div_pos pos hp
  have eq : δ * (M+N+1) = quality x₀ := div_mul_cancel₀ _ hp.ne'
  refine ⟨δ, hδ, fun l u hl hlu hu hwidth => ?_⟩
  have left : (l : ℝ) ∈ Icc (-(B : ℝ)) (B : ℝ) := by
    exact ⟨by exact_mod_cast hl, by exact_mod_cast hlu.le.trans hu⟩
  have min : quality x₀ ≤ quality (l : ℝ) := hmin left
  have m : M * ((u : ℝ)-l) < quality x₀ := by
    calc
      _ ≤ M * δ := mul_le_mul_of_nonneg_left hwidth hm
      _ < δ * (M+N+1) := by rw [mul_comm M δ]; exact mul_lt_mul_of_pos_left (by linarith) hδ
      _ = _ := eq
  have n : N * ((u : ℝ)-l) < quality x₀ := by
    calc
      _ ≤ N * δ := mul_le_mul_of_nonneg_left hwidth hn
      _ < δ * (M+N+1) := by rw [mul_comm N δ]; exact mul_lt_mul_of_pos_left (by linarith) hδ
      _ = _ := eq
  rw [Test.ready, Bool.or_eq_true, noRoot_iff p B f mono, monotone_iff p B f mono]
  rcases le_total |q.eval (l : ℝ)| |q.derivative.eval (l : ℝ)| with h | h
  · have hd : quality x₀ ≤ |q.derivative.eval (l : ℝ)| := min.trans (max_eq_right h).le
    exact Or.inr (n.trans_le hd)
  · have hp : quality x₀ ≤ |q.eval (l : ℝ)| := min.trans (max_eq_left h).le
    exact Or.inl (m.trans_le hp)

omit mono [IsStrictOrderedRing K] in
private theorem readyAt_of_width (t : Test K) (B : ℚ) {δ : ℝ}
    (good : ∀ l u : ℚ, -B ≤ l → l < u → u ≤ B → (u : ℝ) - l ≤ δ → t.ready l u = true)
    (n : ℕ) (l u : ℚ) (hl : -B ≤ l) (hlu : l < u) (hu : u ≤ B)
    (w : (u : ℝ) - l ≤ (2 : ℝ)^n * δ) :
    t.readyAt n l u = true := by
  induction n generalizing l u with
  | zero => exact good l u hl hlu hu (by simpa using w)
  | succ n ih =>
    have ⟨h₁, h₂⟩ := midpoint_between hlu
    have e : (midpoint l u : ℝ) = ((l : ℝ) + (u : ℝ))/2 := by norm_cast
    rw [pow_succ] at w
    have w₁ : (midpoint l u : ℝ) - l ≤ (2 : ℝ)^n * δ := by rw [e]; linarith
    have w₂ : (u : ℝ) - (midpoint l u : ℝ) ≤ (2 : ℝ)^n * δ := by rw [e]; linarith
    simp [Test.readyAt, ih l (midpoint l u) hl h₁ (h₂.le.trans hu) w₁,
      ih (midpoint l u) u (hl.trans h₁.le) h₂ hu w₂]

theorem ready_exists (hB : (0 : ℚ) < B)
    (simple : ∀ x, (realPoly f p).IsRoot x → ¬(realPoly f p).derivative.IsRoot x) :
    ∃ n, (prepare p B).readyAt n (-B) B = true := by
  obtain ⟨δ, hδ, hg⟩ := positive_uniform_width p B f mono hB simple
  obtain ⟨n, hn⟩ := exists_nat_gt ((2*B : ℝ)/δ)
  have growth : (n : ℝ) < (2 : ℝ)^n := by exact_mod_cast n.lt_two_pow_self
  refine ⟨n, readyAt_of_width (prepare p B) B hg n (-B) B le_rfl (by linarith) le_rfl ?_⟩
  have h := (div_lt_iff₀ hδ).mp (hn.trans growth)
  push_cast
  linarith

def localRadius (l u : ℚ) : ℚ := max |l| |u|

omit mono in
private theorem local_bounds {l u : ℚ} :
    0 ≤ localRadius l u ∧ -localRadius l u ≤ l ∧ u ≤ localRadius l u := by
  have hl := le_max_left |l| |u|
  exact ⟨(abs_nonneg l).trans hl, (neg_le_neg hl).trans (neg_abs_le l),
    (le_abs_self u).trans (le_max_right _ _)⟩

omit mono in
theorem hornerBounds_mono (q : Coefficients K) {x y : K} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (hornerBounds x q).1 ≤ (hornerBounds y q).1 ∧
      (hornerBounds x q).2 ≤ (hornerBounds y q).2 := by
  induction q with
  | nil => simp [hornerBounds]
  | cons a q ih =>
    have h := hornerBounds_nonneg hx q
    exact ⟨add_le_add le_rfl (mul_le_mul hxy ih.1 h.1 (hx.trans hxy)),
      add_le_add ih.1 (mul_le_mul hxy ih.2 h.2 (hx.trans hxy))⟩

def localReady (l u : ℚ) : Bool := (prepare p (localRadius l u)).ready l u

def localReadyAt : ℕ → ℚ → ℚ → Bool
  | 0, l, u => localReady p l u
  | n+1, l, u =>
    localReady p l u || (localReadyAt n l (midpoint l u) && localReadyAt n (midpoint l u) u)

def localRun : ℕ → ℚ → ℚ → List Window
  | 0, l, u => (prepare p (localRadius l u)).emit l u
  | n+1, l, u =>
    if localReady p l u then (prepare p (localRadius l u)).emit l u
    else localRun n l (midpoint l u) ++ localRun n (midpoint l u) u

omit mono in
private theorem localReady_of_ready {l u : ℚ} (hl : -B ≤ l) (hlu : l < u) (hu : u ≤ B)
    (h : (prepare p B).ready l u = true) : localReady p l u = true := by
  have r : localRadius l u ≤ B := max_le (abs_le.mpr ⟨hl,hlu.le.trans hu⟩)
    (abs_le.mpr ⟨hl.trans hlu.le,hu⟩)
  have hb : 0 ≤ localRadius l u := local_bounds.1
  have hr : (0 : K) ≤ (localRadius l u : K) := by exact_mod_cast hb
  have hr' : (localRadius l u : K) ≤ (B : K) := by exact_mod_cast r
  have hw : (0 : K) ≤ ((u-l : ℚ) : K) := by exact_mod_cast sub_nonneg.mpr hlu.le
  simp only [localReady, Test.ready, Bool.or_eq_true, Test.noRoot, Test.monotone, prepare] at h ⊢
  exact h.imp
    (fun h => decide_eq_true ((mul_le_mul_of_nonneg_right (hornerBounds_mono p hr hr').2 hw).trans_lt
      (of_decide_eq_true h)))
    (fun h => decide_eq_true ((mul_le_mul_of_nonneg_right (hornerBounds_mono (DensePolynomial.derivative p)
      hr hr').2 hw).trans_lt (of_decide_eq_true h)))

omit mono in
private theorem localReadyAt_of_readyAt (n : ℕ) {l u : ℚ} (hl : -B ≤ l) (hlu : l < u) (hu : u ≤ B)
    (h : (prepare p B).readyAt n l u = true) : localReadyAt p n l u = true := by
  induction n generalizing l u with
  | zero => exact localReady_of_ready p B hl hlu hu h
  | succ n ih =>
    simp only [Test.readyAt, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h₁,h₂⟩
    · simp [localReadyAt, localReady_of_ready p B hl hlu hu h]
    · obtain ⟨hm,hm'⟩ := midpoint_between hlu
      simp [localReadyAt, ih hl hm (hm'.le.trans hu) h₁, ih (hl.trans hm.le) hm' hu h₂]

theorem localRun_correct (n : ℕ) {l u : ℚ} (hlu : l < u) (h : localReadyAt p n l u = true) :
    IsolatesOn (realPoly f p) (Ioc (l : ℝ) u) (localRun p n l u) := by
  have leaf {l u : ℚ} (hle : l < u) (h : localReady p l u = true) :=
    emit_correct p (localRadius l u) f mono local_bounds.1 local_bounds.2.1 local_bounds.2.2 hle h
  induction n generalizing l u with
  | zero => exact leaf hlu h
  | succ n ih =>
    by_cases hr : localReady p l u = true
    · simpa [localRun, hr] using leaf hlu hr
    · have e := Bool.eq_false_of_not_eq_true hr
      have hg : localReadyAt p n l (midpoint l u) = true ∧ localReadyAt p n (midpoint l u) u = true := by
        simpa [localReadyAt,e] using h
      obtain ⟨hm,hm'⟩ := midpoint_between hlu
      simp only [localRun,e,Bool.false_eq_true,ite_false]
      exact IsolatesOn.append (by exact_mod_cast hm.le) (by exact_mod_cast hm'.le)
        (ih hm hg.1) (ih hm' hg.2)

theorem local_ready_exists (hB : (0 : ℚ) < B)
    (simple : ∀ x, (realPoly f p).IsRoot x → ¬(realPoly f p).derivative.IsRoot x) :
    ∃ n, localReadyAt p n (-B) B = true := by
  obtain ⟨n,h⟩ := ready_exists p B f mono hB simple
  exact ⟨n,localReadyAt_of_readyAt p B n le_rfl (by linarith) le_rfl h⟩

/-- This search has no external fuel. Compactness and simplicity prove that
    some finite depth suffices, while the running code finds it by exact tests. -/
def isolateWithin (hB : (0 : ℚ) < B)
    (simple : ∀ x, (realPoly f p).IsRoot x → ¬(realPoly f p).derivative.IsRoot x) :
    {ws : List Window // IsolatesOn (realPoly f p) (Ioc (-(B : ℝ)) B) ws} := by
  let ex := local_ready_exists p B f mono hB simple
  let n := Nat.find ex
  refine ⟨localRun p n (-B) B, ?_⟩
  rw [← Rat.cast_neg]
  exact localRun_correct p f mono n (by linarith) (Nat.find_spec ex)

end Subdivision

variable (f : K →+* ℝ)

def squarefreePart (p : Coefficients K) : Coefficients K :=
  if (trim p).length ≤ 1 then p
  else (divmod p (DensePolynomial.gcd p (DensePolynomial.derivative p))).1

omit [IsStrictOrderedRing K] in
theorem squarefreePart_spec (p : Coefficients K) (hp : realPoly f p ≠ 0) :
    realPoly f (squarefreePart p) ≠ 0 ∧
      (∀ x, (realPoly f (squarefreePart p)).IsRoot x ↔ (realPoly f p).IsRoot x) ∧
      ∀ x, (realPoly f (squarefreePart p)).IsRoot x →
        ¬(realPoly f (squarefreePart p)).derivative.IsRoot x := by
  unfold squarefreePart
  split
  · rename_i small
    refine ⟨hp, fun _ => Iff.rfl, ?_⟩
    have hd : (realPoly f p).natDegree = 0 := by
      rw [realPoly, natDegree_map_eq_of_injective f.injective, degree_trim]
      omega
    have hc := eq_C_of_natDegree_eq_zero hd
    intro x hx
    rw [hc, IsRoot.def, eval_C] at hx
    exact (hp (hc.trans (by rw [hx]; exact map_zero C))).elim
  · rename_i large
    let g := DensePolynomial.gcd p (DensePolynomial.derivative p)
    have cd : Quartic.CommonDivisors (realPoly f p) (realPoly f p).derivative (realPoly f g) := by
      intro a
      rw [← realPoly_derivative]
      exact gcd_spec f p _ a
    have hg : realPoly f g ≠ 0 := fun he => hp ((cd.eq_zero_iff.mp he).1)
    obtain ⟨eq,hr⟩ := divmod_spec p g
    have castEq := congrArg (Polynomial.map f) eq
    simp only [Polynomial.map_mul, Polynomial.map_add] at castEq
    have deg (p : Coefficients K) : (realPoly f p).natDegree = (trim p).length - 1 := by
      rw [realPoly, natDegree_map_eq_of_injective f.injective, degree_trim]
    have hr0 : realPoly f (divmod p g).2 = 0 := by
      have hdiv : realPoly f g ∣ realPoly f (divmod p g).2 := by
        have hEq := eq_sub_of_add_eq' castEq.symm
        change realPoly f (divmod p g).2 = _ at hEq
        rw [hEq]
        exact dvd_sub cd.left (dvd_mul_left _ _)
      by_cases hz : realPoly f (divmod p g).2 = 0
      · exact hz
      · apply eq_zero_of_dvd_of_natDegree_lt hdiv
        rw [deg, deg]
        have hlen : 0 < (trim (divmod p g).2).length := by
          apply List.length_pos_iff.mpr
          intro he
          exact hz (by simp [realPoly, (trim_eq_nil _).mp he])
        have hglen := hr.resolve_left (by
          intro he
          exact hg (by simp [realPoly, (trim_eq_nil _).mp he]))
        omega
    have eqProd : C (1 : ℝ) * realPoly f p =
        realPoly f (divmod p g).1 * realPoly f g := by
      simp only [C_1, one_mul]
      simpa only [realPoly] using castEq.trans (by rw [show
        (DensePolynomial.polynomial (divmod p g).2).map f = 0 from hr0, add_zero])
    have hd : (realPoly f p).derivative ≠ 0 := by
      apply derivative_ne_zero.mpr
      rw [deg]
      omega
    exact Quartic.quotient_roots one_ne_zero hp hd cd eqProd

def cauchyEstimate (p : Coefficients K) : K :=
  1 + (hornerBounds 1 p).1 / |lead (trim p)|

private theorem coeff_le_magnitude (p : Coefficients K) (j : ℕ) :
    |(DensePolynomial.polynomial p).coeff j| ≤ (hornerBounds 1 p).1 := by
  induction p generalizing j with
  | nil => simp [DensePolynomial.polynomial, hornerBounds]
  | cons a p ih =>
    cases j with
    | zero =>
      rw [coeff_polynomial]
      simpa [hornerBounds] using (hornerBounds_nonneg (zero_le_one : (0 : K) ≤ 1) p).1
    | succ j =>
      simp only [coeff_polynomial, List.getElem?_cons_succ, hornerBounds, one_mul]
      rw [← coeff_polynomial]
      exact (ih j).trans (le_add_of_nonneg_left (abs_nonneg a))

variable (mono : StrictMono f)
include mono

open scoped NNReal in
theorem cauchyEstimate_correct (p : Coefficients K) :
    ((realPoly f p).cauchyBound : ℝ) ≤ f (cauchyEstimate p) := by
  let q := realPoly f p
  have hm : 0 ≤ f (hornerBounds (1 : K) p).1 := by
    simpa using mono.monotone (hornerBounds_nonneg (zero_le_one : (0 : K) ≤ 1) p).1
  have bs : (↑((Finset.range q.natDegree).sup fun i => ‖q.coeff i‖₊) : ℝ) ≤ f (hornerBounds (1 : K) p).1 := by
    rw [← NNReal.coe_mk _ hm, NNReal.coe_le_coe]
    apply Finset.sup_le
    intro j _
    rw [← NNReal.coe_le_coe, NNReal.coe_mk]
    change ‖q.coeff j‖ ≤ _
    rw [Real.norm_eq_abs, show q.coeff j = f ((DensePolynomial.polynomial p).coeff j) from coeff_map _ _,
      ← hom_abs f mono]
    exact mono.monotone (coeff_le_magnitude p j)
  have leadEq : (↑‖q.leadingCoeff‖₊ : ℝ) = f |lead (trim p)| := by
    change ‖q.leadingCoeff‖ = _
    rw [Real.norm_eq_abs, show q.leadingCoeff = f (lead (trim p)) by
      change ((DensePolynomial.polynomial p).map f).leadingCoeff = _
      rw [leadingCoeff_map_of_injective f.injective, leadingCoeff_trim], hom_abs f mono]
  simp only [cauchyBound, NNReal.coe_add, NNReal.coe_div, NNReal.coe_one, cauchyEstimate,
    map_add, map_one, map_div₀]
  rw [leadEq, add_comm 1]
  have hn : 0 ≤ f |lead (trim p)| := by
    rw [← leadEq]
    positivity
  exact add_le_add_left (div_le_div_of_nonneg_right bs hn) 1

omit [IsStrictOrderedRing K] in
theorem radius_exists (p : Coefficients K) :
    ∃ n : ℕ, max 1 (cauchyEstimate p) < ((2^n : ℕ) : K) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (f (max 1 (cauchyEstimate p)))
  have h₂ : (n : ℝ) < ((2^n : ℕ) : ℝ) := by exact_mod_cast n.lt_two_pow_self
  exact ⟨n, mono.lt_iff_lt.mp (by simpa only [map_natCast] using hn.trans h₂)⟩

def radiusFrom (p : Coefficients K)
    (h : ∃ n : ℕ, max 1 (cauchyEstimate p) < ((2^n : ℕ) : K)) : ℚ :=
  (2^(Nat.find h) : ℕ)

def radius (p : Coefficients K) : ℚ :=
  radiusFrom p (radius_exists f mono p)

omit [IsStrictOrderedRing K] in
theorem radius_positive (p : Coefficients K) : (0 : ℚ) < radius f mono p := by
  unfold radius radiusFrom
  positivity

open scoped NNReal in
theorem root_in_radius (p : Coefficients K) (hp : realPoly f p ≠ 0) (x : ℝ)
    (hx : (realPoly f p).IsRoot x) : x ∈ Ioc (-(radius f mono p : ℝ)) (radius f mono p : ℝ) := by
  have h := Nat.find_spec (radius_exists f mono p)
  have hb : f (cauchyEstimate p) < (radius f mono p : ℝ) := by
    simpa [radius, radiusFrom, map_ofNat] using mono ((le_max_right _ _).trans_lt h)
  have hr : |x| < (radius f mono p : ℝ) := by
    have b := NNReal.coe_lt_coe.mpr (hx.norm_lt_cauchyBound hp)
    rw [show (↑‖x‖₊ : ℝ) = |x| from Real.norm_eq_abs x] at b
    exact b.trans ((cauchyEstimate_correct f mono p).trans_lt hb)
  exact ⟨(abs_lt.mp hr).1, (abs_lt.mp hr).2.le⟩

/-- The zero polynomial has all roots. A nonzero polynomial returns an
    ordered finite list of exact root windows for its squarefree part. -/
inductive Roots where
  | all
  | finite (windows : List Window)
  deriving Repr

structure Result (f : K →+* ℝ) (p : Coefficients K) where
  simplePoly : Coefficients K
  roots : Roots
  correct : match roots with
    | .all => realPoly f p = 0
    | .finite ws => realPoly f p ≠ 0 ∧ IsolatesOn (realPoly f simplePoly) univ ws ∧
        (∀ x, (realPoly f simplePoly).IsRoot x ↔ (realPoly f p).IsRoot x) ∧
        ∀ x, (realPoly f simplePoly).IsRoot x → ¬(realPoly f simplePoly).derivative.IsRoot x

/-- Complete executable root isolation in an ordered coefficient field embedded in the reals. -/
def isolate (model : RealModel K) (p : Coefficients K) : Result model.hom p := by
  if hz : trim p = [] then
    exact ⟨[], .all, by simp only [realPoly, (trim_eq_nil p).mp hz, Polynomial.map_zero]⟩
  else
    let q := squarefreePart p
    have hp : realPoly model.hom p ≠ 0 := by
      rwa [ne_eq, realPoly, Polynomial.map_eq_zero_iff model.hom.injective, ← trim_eq_nil]
    have spec := squarefreePart_spec model.hom p hp
    let B := radiusFrom q (radius_exists model.hom model.strictMono q)
    have hB : 0 < B := radius_positive model.hom model.strictMono q
    have ready := local_ready_exists q B model.hom model.strictMono hB spec.2.2
    let n := Nat.find ready
    let ws := localRun q n (-B) B
    have h : IsolatesOn (realPoly model.hom q) (Ioc (-(B : ℝ)) B) ws := by
      rw [← Rat.cast_neg]
      exact localRun_correct q model.hom model.strictMono n (by linarith) (Nat.find_spec ready)
    have whole : IsolatesOn (realPoly model.hom q) univ ws :=
      ⟨h.ordered, fun _ _ => subset_univ _, h.brackets, h.unique,
        fun x _ hx => h.covers x (root_in_radius model.hom model.strictMono q spec.1 x hx) hx⟩
    exact ⟨q, .finite ws, hp, whole, spec.2⟩

end CertifiedTopology.ExecutableIsolation
