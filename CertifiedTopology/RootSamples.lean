module

public import CertifiedTopology.AlgebraicField

@[expose] public section

namespace CertifiedTopology.AlgebraicRoot

open ExecutableIsolation Set
open DensePolynomial (Coefficients)

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable (model : RealModel K)

omit [IsStrictOrderedRing K] in
theorem roots_ordered (res : Result model.hom p) :
    (roots model res).Pairwise (fun a b => a.value < b.value) := by
  unfold roots
  split
  · simp
  · rename_i ws he
    have cert := res.correct
    rw [he] at cert
    apply List.pairwise_map.mpr
    have ordered : ws.attach.Pairwise (fun a b => Window.precedes a.val b.val) := by
      have h : (ws.attach.map Subtype.val).Pairwise Window.precedes := by
        simpa using cert.2.1.ordered
      exact List.pairwise_map.mp h
    refine ordered.imp ?_
    intro a b hab
    let A := Root.ofWindow model res.simplePoly cert.2.1 cert.2.2.2 a
    let B := Root.ofWindow model res.simplePoly cert.2.1 cert.2.2.2 b
    exact hab A.value A.represents.inside B.value B.represents.inside

omit [IsStrictOrderedRing K] in
theorem roots_complete (res : Result model.hom p) {x : ℝ} (hn : realPoly model.hom p ≠ 0)
    (hr : (realPoly model.hom p).IsRoot x) : ∃ r ∈ roots model res, r.value = x := by
  have cert := res.correct
  unfold roots
  split
  · rename_i h
    rw [h] at cert
    exact (hn cert).elim
  · rename_i ws e
    rw [e] at cert
    have h₁ := (cert.2.2.1 _).mpr hr
    obtain ⟨w, hw, hx⟩ := cert.2.1.covers x (mem_univ _) h₁
    let a : {w // w ∈ ws} := ⟨w, hw⟩
    refine ⟨_, List.mem_map_of_mem (List.mem_attach ws a), ?_⟩
    exact ((Root.represents _).unique x hx h₁).symm

def lower : Window → ℚ
  | .point a => a
  | .interval a _ => a

def upper : Window → ℚ
  | .point a => a
  | .interval _ b => b

theorem endpoints {w : Window} {x : ℝ} (h : x ∈ w.region) :
    (lower w : ℝ) ≤ x ∧ x ≤ (upper w : ℝ) := by
  cases w with
  | point a =>
    have e : x = (a : ℝ) := h
    subst x
    exact ⟨le_rfl,le_rfl⟩
  | interval l u => exact ⟨h.1.le,h.2.le⟩

theorem width_eq (w : Window) : (width w : ℝ) = (upper w : ℝ) - (lower w : ℝ) := by
  cases w <;> simp [width, upper, lower]

def refinedWindow (r : Root model) (n : ℕ) : Window :=
  refineSteps r.polynomial n r.window

omit [IsStrictOrderedRing K] in
theorem window_contains (r : Root model) : r.value ∈ r.window.region := r.represents.inside

theorem refined_contains (r : Root model) (n : ℕ) : r.value ∈ (refinedWindow model r n).region :=
  (refineSteps_correct model.hom model.strictMono r.represents n).1.inside

theorem gap_exists (a b : Root model) (hab : a.value < b.value) :
    ∃ n : ℕ, upper (refinedWindow model a n) < lower (refinedWindow model b n) := by
  let δ := b.value - a.value
  have hδ : 0 < δ := sub_pos.mpr hab
  obtain ⟨n, hn⟩ := exists_nat_gt (((width a.window : ℝ) + (width b.window : ℝ)) / δ)
  have hg : (n : ℝ) < (2 : ℝ)^n := by exact_mod_cast n.lt_two_pow_self
  have w (r : Root model) : (width (refinedWindow model r n) : ℝ) ≤
      (width r.window : ℝ) / (2 : ℝ)^n := by
    have w := refineSteps_width model.hom model.strictMono r.represents n
    exact_mod_cast w
  have sum : (width (refinedWindow model a n) : ℝ) + (width (refinedWindow model b n) : ℝ) < δ := by
    calc
      _ ≤ (width a.window : ℝ)/(2 : ℝ)^n + (width b.window : ℝ)/(2 : ℝ)^n :=
        add_le_add (w a) (w b)
      _ = ((width a.window : ℝ) + (width b.window : ℝ))/(2 : ℝ)^n := (add_div _ _ _).symm
      _ < δ := (div_lt_iff₀ (by positivity)).mpr
        (by rw [mul_comm]; exact (div_lt_iff₀ hδ).mp (hn.trans hg))
  rw [width_eq, width_eq] at sum
  have ha := (endpoints (refined_contains model a n)).1
  have hb := (endpoints (refined_contains model b n)).2
  have order : (upper (refinedWindow model a n) : ℝ) < (lower (refinedWindow model b n) : ℝ) := by
    dsimp [δ] at sum
    linarith
  exact ⟨n, by exact_mod_cast order⟩

/-- Compute a rational sample in the sector between two algebraic roots. -/
def between (a b : Root model) (hab : a.value < b.value) :
    {q : ℚ // a.value < (q : ℝ) ∧ (q : ℝ) < b.value} := by
  let h := gap_exists model a b hab
  let n := Nat.find h
  let u := upper (refinedWindow model a n)
  let l := lower (refinedWindow model b n)
  refine ⟨ExecutableIsolation.midpoint u l, ?_⟩
  have hl : (u : ℝ) < (l : ℝ) := by exact_mod_cast Nat.find_spec h
  have ha := (endpoints (refined_contains model a n)).2
  have hb := (endpoints (refined_contains model b n)).1
  change a.value < _ ∧ _ < b.value
  unfold ExecutableIsolation.midpoint
  push_cast
  constructor <;> linarith


omit [IsStrictOrderedRing K] in
theorem roots_sound (res : Result model.hom p) {r : Root model} (hr : r ∈ roots model res) :
    (realPoly model.hom p).IsRoot r.value := by
  have h := res.correct
  unfold roots at hr
  split at hr
  · simp at hr
  · rename_i ws e
    rw [e] at h
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hr
    exact (h.2.2.1 _).mp (Root.represents _).root

def shrinkRoots (qs : List (Coefficients K)) : (rs : List (Root model)) →
    {ts : List (Root model) // ts.map Root.value = rs.map Root.value}
  | [] => ⟨[],rfl⟩
  | r :: rs =>
    let a := r.shrinkAll model qs
    let b := shrinkRoots qs rs
    ⟨a.val :: b.val, by simp only [List.map_cons,a.property,b.property]⟩

/-- Interpret the finite root data in the geometric lifting layer. -/
noncomputable def cutTable (res : Result model.hom p) :
    Univariate.CutTable [realPoly model.hom p] where
  roots := (roots model res).map Root.value
  sorted := List.pairwise_map.mpr (roots_ordered model res)
  covers := by
    intro q h hn x hx
    rw [List.mem_singleton.mp h] at hn hx
    obtain ⟨r, hr, e⟩ := roots_complete model res hn hx
    exact List.mem_map.mpr ⟨r,hr,e⟩

inductive Sample (model : RealModel K)
  | rational (q : ℚ)
  | base (a : K)
  | algebraic (r : Root model)

noncomputable def Sample.value : Sample model → ℝ
  | .rational q => q
  | .base a => model.hom a
  | .algebraic r => r.value

def rootSample (r : Root model) : {s : Sample model // s.value model = r.value} :=
  match e : r.polynomial with
  | [a,b] =>
    if hb : b = 0 then ⟨.algebraic r,rfl⟩
    else
      ⟨.base (-a/b), by
        have h : model.hom a + model.hom b * r.value = 0 := by
          simpa [e, realPoly, DensePolynomial.polynomial, Polynomial.IsRoot.def] using r.represents.root
        change model.hom (-a/b) = r.value
        rw [map_div₀, map_neg, div_eq_iff (fun hz => hb (model.hom.injective (hz.trans (map_zero _).symm)))]
        rw [mul_comm]
        linarith⟩
  | _ =>
    match e : refinedWindow model r 2 with
    | .point q => ⟨.rational q, by
        have h := (refineSteps_correct model.hom model.strictMono r.represents 2).1.inside
        change r.value ∈ (refinedWindow model r 2).region at h
        rw [e] at h
        exact (show r.value = (q : ℝ) from h).symm⟩
    | .interval _ _ => ⟨.algebraic r,rfl⟩

def gapSample (lo hi : Option (Root model))
    (ordered : ∀ a ∈ lo, ∀ b ∈ hi, a.value < b.value) :
    {s : Sample model // Univariate.contains
        (.sector (lo.map Root.value) (hi.map Root.value)) (s.value model)} := by
  cases lo with
  | none =>
    cases hi with
    | none =>
      exact ⟨.rational 0, by simp [Sample.value, Univariate.contains, Slice.Contains]⟩
    | some a =>
      refine ⟨.rational (lower a.window - 1), ?_⟩
      have h := (endpoints a.represents.inside).1
      simpa [Sample.value, Univariate.contains, Slice.Contains, Aff.eval] using
        (sub_lt_self _ (by norm_num : (0 : ℝ) < 1)).trans_le h
  | some a =>
    cases hi with
    | none =>
      refine ⟨.rational (upper a.window + 1), ?_⟩
      have h := (endpoints a.represents.inside).2
      simpa [Sample.value, Univariate.contains, Slice.Contains, Aff.eval] using
        h.trans_lt (lt_add_one (upper a.window : ℝ))
    | some b =>
      let s := between model a b (ordered a rfl b rfl)
      exact ⟨.rational s.val, by simpa [Sample.value, Univariate.contains, Slice.Contains, Aff.eval]
        using s.property⟩

/-- Sorted exact samples, alternating sectors and sections, with a check
    that each witness lies in its corresponding vertical cell. -/
def stackSamples (lo : Option (Root model)) (rs : List (Root model))
    (ord : rs.Pairwise (fun a b => a.value < b.value))
    (lowerOrder : ∀ a ∈ lo, ∀ b ∈ rs, a.value < b.value) :
    {ss : List (Sample model) // List.Forall₂ (fun s t => Univariate.contains t (s.value model)) ss
      (slices (n := 0) (lo.map Root.value) (rs.map Root.value))} := by
  cases rs with
  | nil =>
    let t := gapSample model lo none (by simp)
    exact ⟨[t.val], .cons t.property .nil⟩
  | cons a as =>
    let s := gapSample model lo (some a) (fun r hr b hb =>
      (show b = a by simpa using hb.symm) ▸ lowerOrder r hr a (by simp))
    let tail := stackSamples (some a) as (List.pairwise_cons.mp ord).2
      (fun r hr b hb => by
        have e : r = a := by simpa using hr.symm
        rw [e]
        exact (List.pairwise_cons.mp ord).1 _ hb)
    let r := rootSample model a
    exact ⟨s.val :: r.val :: tail.val,
      .cons s.property (.cons r.property tail.property)⟩
termination_by rs.length

end CertifiedTopology.AlgebraicRoot
