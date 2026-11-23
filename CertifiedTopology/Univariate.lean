module

public import CertifiedTopology.Formula
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace CertifiedTopology.Univariate
open Polynomial Set

/-- Exact mathematical root source. Zero polynomials impose no cuts. -/
noncomputable def cuts (fs : List (Polynomial ℝ)) : List ℝ :=
  fs.flatMap fun f => f.roots.toList

theorem mem_cuts {fs : List (Polynomial ℝ)} {f} (hf : f ∈ fs)
    (hne : f ≠ 0) {x} (hx : f.eval x = 0) : x ∈ cuts fs := by
  apply List.mem_flatMap.mpr
  exact ⟨f, hf, by simpa [Polynomial.mem_roots hne] using hx⟩

/-- A root source may supply extra cuts, for example from other polynomials in the family. -/
def Covers (rs : List ℝ) (fs : List (Polynomial ℝ)) :=
  ∀ f ∈ fs, f ≠ 0 → ∀ x, f.eval x = 0 → x ∈ rs

abbrev contains (s : Slice ℝ) (t : ℝ) := Slice.Contains (n := 0) () s t

private theorem between_mem {s : Slice ℝ} {x y z : ℝ} (hx : contains s x)
    (hy : contains s y) (hz : z ∈ uIcc x y) : contains s z := by
  cases s with
  | sectionAt r =>
    change x = r at hx
    change y = r at hy
    change z = r
    simpa [hx,hy] using hz
  | sector lo hi =>
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · exact lt_of_lt_of_le (lt_min (hx.1 r hr) (hy.1 r hr)) hz.1
    · exact lt_of_le_of_lt hz.2 (max_lt (hx.2 r hr) (hy.2 r hr))

private theorem at_cut {rs : List ℝ} {s : Slice ℝ} (hs : s ∈ stack (n := 0) () rs)
    {z x : ℝ} (hz : z ∈ rs) (hc : contains s z) (hx : contains s x) : x = z := by
  obtain ⟨ho,_,hm⟩ := ordered_spec (n := 0) () rs
  obtain ⟨r,hr,he⟩ := hm z hz
  have h := slice_sign ho ho none hs hx hc hr
  change r = z at he
  subst r
  exact (side_congr h).2.1.mpr rfl

theorem sign_invariant {rs : List ℝ} {fs : List (Polynomial ℝ)} (cover : Covers rs fs)
    {s : Slice ℝ} (hs : s ∈ stack (n := 0) () rs) {x y}
    (hx : contains s x) (hy : contains s y) {f} (hf : f ∈ fs) :
    side (f.eval x) 0 = side (f.eval y) 0 := by
  by_cases h : f = 0
  · simp [h]
  have H (hz : (0 : ℝ) ∈ uIcc (f.eval x) (f.eval y)) : x = y := by
    obtain ⟨z,hz',he⟩ := intermediate_value_uIcc f.continuous.continuousOn hz
    have ha := cover f hf h z he
    have hc := between_mem hx hy hz'
    exact (at_cut hs ha hc hx).trans (at_cut hs ha hc hy).symm
  by_cases e : x = y
  · rw [e]
  have hn := mt H e
  simp only [mem_uIcc] at hn
  unfold side
  split_ifs <;> first | rfl | exfalso; apply hn; grind

noncomputable def decompose (fs : List (Polynomial ℝ)) : List (Slice ℝ) :=
  stack (n := 0) () (cuts fs)

theorem decompose_correct (fs : List (Polynomial ℝ)) :
    (∀ x, ∃! s, s ∈ decompose fs ∧ contains s x) ∧
    (∀ s ∈ decompose fs, contains s (Slice.sample (n := 0) () s)) ∧
    (∀ s ∈ decompose fs, ∀ x, contains s x → ∀ f ∈ fs,
      side (f.eval x) 0 = side (f.eval (Slice.sample (n := 0) () s)) 0) := by
  have ho := (ordered_spec (n := 0) () (cuts fs)).1
  have hs {s} (h : s ∈ decompose fs) := slice_sample _ ho none (by simp [Lower]) h
  exact ⟨fun x => slice_partition _ ho none (by simp [Lower]) x (by simp [Lower]),
    fun _ h => hs h, fun _ h _ hx _ hf =>
      sign_invariant (fun _ hf hn _ hx => mem_cuts hf hn hx) h hx (hs h) hf⟩

/-- The root information required by lifting. Extra cuts are allowed, and
    zero specializations require no cuts. -/
structure CutTable (fs : List (Polynomial ℝ)) where
  roots : List ℝ
  sorted : roots.Pairwise (· < ·)
  covers : Covers roots fs

theorem ordered_eq {rs : List ℝ} (h : SortedAt (n := 0) () rs) :
    orderedRoots (n := 0) () rs = rs := by
  induction rs with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨ha,hp⟩ := List.pairwise_cons.mp h
    change insertRoot (K := ℝ) (n := 0) () a (orderedRoots (n := 0) () as) = a :: as
    rw [ih hp]
    cases as with
    | nil => rfl
    | cons b bs => simp [insertRoot,ha b (by simp)]

namespace CutTable

variable {fs : List (Polynomial ℝ)}

/-- A checked table is already strictly ordered, so lifting need not sort it. -/
def cells (d : CutTable fs) : List (Slice ℝ) := slices (n := 0) none d.roots

theorem partition (d : CutTable fs) (x : ℝ) :
    ∃! s, s ∈ d.cells ∧ contains s x :=
  slice_partition (n := 0) () d.sorted none (by simp [Lower]) x (by simp [Lower])

theorem sample_mem (d : CutTable fs) {s : Slice ℝ} (hs : s ∈ d.cells) :
    contains s (s.sample (n := 0) ()) :=
  slice_sample (n := 0) () d.sorted none (by simp [Lower]) hs

theorem invariant (d : CutTable fs) {s : Slice ℝ} (hs : s ∈ d.cells)
    {x y : ℝ} (hx : contains s x) (hy : contains s y) {f : Polynomial ℝ}
    (hf : f ∈ fs) : side (f.eval x) 0 = side (f.eval y) 0 := by
  apply sign_invariant d.covers _ hx hy hf
  simpa only [stack, ordered_eq d.sorted, cells] using hs

private theorem section_mem_slices {rs : List ℝ} {r : ℝ} (hr : r ∈ rs) (lo : Option ℝ) :
    Slice.sectionAt r ∈ slices (n := 0) lo rs := by
  induction rs generalizing lo with
  | nil => simp at hr
  | cons s rs ih =>
    rcases List.mem_cons.mp hr with rfl | h
    · simp [slices]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h (some s)))

theorem sector_avoids (d : CutTable fs) {l u : Option ℝ}
    (hs : Slice.sector l u ∈ d.cells) {f : Polynomial ℝ} (hf : f ∈ fs) (hn : f ≠ 0)
    {x : ℝ} (hx : contains (.sector l u) x) : f.eval x ≠ 0 := by
  intro hz
  have hsec : Slice.sectionAt x ∈ d.cells := section_mem_slices (d.covers f hf hn x hz) none
  obtain ⟨_, _, uniq⟩ := d.partition x
  have e := (uniq _ ⟨hsec, rfl⟩).trans (uniq _ ⟨hs, hx⟩).symm
  cases e

noncomputable def fromPolynomials (fs : List (Polynomial ℝ)) : CutTable fs where
  roots := orderedRoots (n := 0) () (cuts fs)
  sorted := (ordered_spec (n := 0) () (cuts fs)).1
  covers := by
    intro f hf hn x hx
    obtain ⟨r, hr, he⟩ := (ordered_spec (n := 0) () (cuts fs)).2.2 x (mem_cuts hf hn hx)
    change r = x at he
    exact he ▸ hr

end CutTable

end CertifiedTopology.Univariate
