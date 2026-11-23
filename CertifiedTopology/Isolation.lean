module

public import CertifiedTopology.Univariate
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

namespace CertifiedTopology.Isolation
open Set Polynomial

theorem crossing {l h : ℝ} (q : Polynomial ℝ) (hl : l < h)
    (cross : q.eval l * q.eval h < 0) :
    ∃ x ∈ Ioo l h, q.eval x = 0 := by
  have hb : (0:ℝ) ∈ uIcc (q.eval l) (q.eval h) := by
    rw [mul_neg_iff] at cross
    rcases cross with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;> simp [mem_uIcc] <;> grind
  obtain ⟨x,hx,he⟩ := intermediate_value_uIcc q.continuous.continuousOn hb
  rw [uIcc_of_le hl.le] at hx
  refine ⟨x,⟨hx.1.lt_of_ne ?_,hx.2.lt_of_ne ?_⟩,he⟩ <;> rintro rfl <;> simp [he] at cross

structure Box (q : Polynomial ℝ) (l h : ℝ) where
  root : ℝ
  interior : root ∈ Ioo l h
  zero : q.eval root = 0
  unique : ∀ x ∈ Ioo l h, q.eval x = 0 → x = root

noncomputable def isolate {l h : ℝ} (q : Polynomial ℝ) (hl : l < h)
    (cross : q.eval l * q.eval h < 0)
    (slope : (∀ x ∈ Ioo l h, 0 < q.derivative.eval x) ∨
             (∀ x ∈ Ioo l h, q.derivative.eval x < 0)) : Box q l h :=
  let existsRoot := crossing q hl cross
  let r := existsRoot.choose
  have hr := existsRoot.choose_spec
  have inj : Set.InjOn (fun x => q.eval x) (Icc l h) := by
    rcases slope with hp | hn
    · exact (strictMonoOn_of_deriv_pos (convex_Icc _ _) q.continuousOn
        (by simpa [interior_Icc,q.deriv] using hp)).injOn
    · exact (strictAntiOn_of_deriv_neg (convex_Icc _ _) q.continuousOn
        (by simpa [interior_Icc,q.deriv] using hn)).injOn
  ⟨r,hr.1,hr.2,fun _ hx he => inj (Ioo_subset_Icc_self hx)
    (Ioo_subset_Icc_self hr.1) (he.trans hr.2.symm)⟩

/-- A checkable sign table labels every real point, including its algebraic sections. -/
structure Diagram (fs : List (Polynomial ℝ)) where
  rows : List (Slice ℝ × List Side)
  partition : ∀ x, ∃! row, row ∈ rows ∧ Univariate.contains row.1 x
  valid : ∀ row ∈ rows, ∀ x, Univariate.contains row.1 x →
    fs.map (fun f => side (f.eval x) 0) = row.2

structure Label (fs : List (Polynomial ℝ)) where
  region : Slice ℝ
  signs : List Side
  witness : ℝ
  inside : Univariate.contains region witness
  checkSigns : fs.map (fun f => side (f.eval witness) 0) = signs

theorem ordered_eq {rs : List ℝ} (h : SortedAt (n := 0) () rs) :
    orderedRoots (n := 0) () rs = rs := Univariate.ordered_eq h

def finish {fs : List (Polynomial ℝ)} (rs : List ℝ) (sorted : rs.Pairwise (· < ·))
    (cover : Univariate.Covers rs fs) (labels : List (Label fs))
    (layout : labels.map Label.region = slices (n := 0) none rs) : Diagram fs := by
  let rows := labels.map fun r => (r.region,r.signs)
  have valid : ∀ row ∈ rows, ∀ x, Univariate.contains row.1 x →
      fs.map (fun f => side (f.eval x) 0) = row.2 := by
    intro row hr x hx
    obtain ⟨r,hr',rfl⟩ := List.mem_map.mp (show _ ∈ labels.map (fun r => (r.region,r.signs)) from hr)
    have hm : r.region ∈ stack (n := 0) () rs := by
      rw [stack,ordered_eq sorted,← layout]
      exact List.mem_map_of_mem hr'
    refine Eq.trans ?_ r.checkSigns
    exact List.map_congr_left (fun _ hf =>
      Univariate.sign_invariant cover hm hx r.inside hf)
  refine ⟨rows, ?_,valid⟩
  intro x
  obtain ⟨s,⟨hs,hx⟩,hu⟩ := slice_partition (n := 0) () sorted none (by simp [Lower]) x
    (by simp [Lower])
  rw [← layout] at hs
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hs
  have hm : (r.region,r.signs) ∈ rows := List.mem_map_of_mem hr
  refine ⟨_,⟨hm,hx⟩,?_⟩
  rintro row ⟨hd,hy⟩
  obtain ⟨d,hd',rfl⟩ := List.mem_map.mp hd
  have he := hu d.region ⟨layout ▸ List.mem_map_of_mem hd',hy⟩
  exact Prod.ext he ((valid _ hd x hy).symm.trans (valid _ hm x hx))

/-- Build a sign table from the mathematical univariate root source. Extra cuts
    can refine a chart without changing its sign labels. -/
noncomputable def fromProjection (fs extra : List (Polynomial ℝ)) : Diagram fs where
  rows := (Univariate.decompose (fs ++ extra)).map fun s =>
    (s, fs.map fun f => side (f.eval (Slice.sample (n := 0) () s)) 0)
  partition := by
    intro x
    obtain ⟨s, ⟨hs,hx⟩,hu⟩ := (Univariate.decompose_correct (fs ++ extra)).1 x
    refine ⟨_, ⟨List.mem_map_of_mem hs, hx⟩, ?_⟩
    rintro z ⟨hz,hxz⟩
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hz
    have e := hu t ⟨ht,hxz⟩
    subst t
    rfl
  valid := by
    intro row hr x hx
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    exact List.map_congr_left fun f hf =>
      (Univariate.decompose_correct (fs ++ extra)).2.2 s hs x hx f (by simp [hf])

end CertifiedTopology.Isolation
