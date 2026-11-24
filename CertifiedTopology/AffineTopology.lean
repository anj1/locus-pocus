module

public import CertifiedTopology.TopologyArtifact
public import CertifiedTopology.Extension
public import CertifiedTopology.Geometry
public import CertifiedTopology.Input

@[expose] public section

namespace CertifiedTopology

namespace Cell

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def sliceConstraints {n : ℕ} : Slice (Aff K n) → List (Aff K (n+1) × Side)
  | .sectionAt r => [((r, -1), .on)]
  | .sector lo hi => (lo.toList.map fun r => ((r, -1), .below)) ++
                     (hi.toList.map fun r => ((r, -1), .above))

/-- Affine equations and strict inequalities defining a cell. -/
def constraints : {n : ℕ} → Cell K n → List (Aff K n × Side)
  | 0, .origin => []
  | _+1, .lift b s =>
    (b.constraints.map fun (f, t) => ((f, 0), t)) ++ sliceConstraints s

omit [Field K] [IsStrictOrderedRing K] in
private theorem side_below (x y : K) : side x y = .below ↔ x < y := by
  unfold side
  split_ifs <;> simp_all

omit [Field K] [IsStrictOrderedRing K] in
private theorem side_on (x y : K) : side x y = .on ↔ x = y := by
  unfold side
  split_ifs <;> simp_all [ne_of_lt]

omit [Field K] [IsStrictOrderedRing K] in
private theorem side_above (x y : K) : side x y = .above ↔ y < x := by
  unfold side
  split_ifs <;> simp_all <;> order

theorem contains_iff_constraints {n} (c : Cell K n) (p : Point K n) :
    c.Contains p ↔ ∀ a ∈ c.constraints, side (Aff.eval a.1 p) 0 = a.2 := by
  induction c with
  | origin => simp [Contains, constraints]
  | lift b s ih =>
    obtain ⟨p, t⟩ := p
    rw [show (Cell.lift b s).Contains (p,t) ↔ b.Contains p ∧ s.Contains p t from Iff.rfl, ih]
    simp only [constraints, List.forall_mem_append, List.forall_mem_map]
    have base (a : Aff K _ × Side) :
        side (Aff.eval (n := _+1) (a.1, 0) (p,t)) 0 = side (Aff.eval a.1 p) 0 := by
      simp [Aff.eval]
    simp only [base]
    refine and_congr Iff.rfl ?_
    cases s with
    | sectionAt r =>
      simp only [sliceConstraints, List.forall_mem_singleton, Slice.Contains, Aff.eval,
        neg_one_mul, ← sub_eq_add_neg, side_on, sub_eq_zero]
      exact eq_comm
    | sector lo hi =>
      cases lo <;> cases hi <;> simp [sliceConstraints, Slice.Contains, Aff.eval, side_below,
        side_above, ← sub_eq_add_neg, sub_neg, sub_pos]

/-- Weaken each strict bound while keeping all section equations. -/
def weak (s : Side) (v : K) : Prop :=
  match s with
  | .below => v ≤ 0
  | .on => v = 0
  | .above => 0 ≤ v

instance (s : Side) (v : K) : Decidable (weak s v) := by
  cases s <;> unfold weak <;> infer_instance

def inWeak (c : Cell K n) (p : Point K n) : Bool :=
  c.constraints.all fun (f, s) => decide (weak s (Aff.eval f p))

omit [IsStrictOrderedRing K] in
@[simp] theorem inWeak_iff (c : Cell K n) (p : Point K n) :
    c.inWeak p = true ↔ ∀ a ∈ c.constraints, weak a.2 (Aff.eval a.1 p) := by
  simp [inWeak]

omit [IsStrictOrderedRing K] in
private theorem weak_of_side {s : Side} {v : K} (h : side v 0 = s) : weak s v := by
  subst s
  unfold side
  split_ifs <;> simp_all [weak, le_of_lt]

omit [IsStrictOrderedRing K] in
private theorem weak_congr (s : Side) {v w : K} (h : side v 0 = side w 0) :
    weak s v ↔ weak s w := by
  obtain ⟨hl, he, hg⟩ := side_congr h
  cases s <;> simp [weak, le_iff_lt_or_eq, hl, he, hg, eq_comm (a := (0 : K))]

private theorem sign_bound {a x y : K} (ha : a ≠ 0)
    (h : side (a*x) 0 = side (a*y) 0) : side x 0 = side y 0 := by
  obtain ⟨hl, he, hg⟩ := side_congr h
  have eq : x = 0 ↔ y = 0 := by simpa [ha] using he
  have lt : x < 0 ↔ y < 0 := by
    rcases lt_or_gt_of_ne ha with h | h
    · simpa only [mul_pos_iff, h.not_gt, h, false_and, true_and, false_or] using hg
    · simpa only [mul_neg_iff, h.not_gt, h, true_and, false_and, or_false] using hl
  simp only [side, eq, lt]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem slices_bounds {rs : List (Aff K n)} {lo : Option (Aff K n)} {s}
    (hs : s ∈ slices lo rs) : match s with
    | .sectionAt r => r ∈ rs
    | .sector l u => (∀ r ∈ l, r ∈ lo ∨ r ∈ rs) ∧ (∀ r ∈ u, r ∈ rs) := by
  induction rs generalizing lo with
  | nil =>
    have e : s = .sector lo none := by simpa [slices] using hs
    subst s
    simp
  | cons r rs ih =>
    simp only [slices, List.mem_cons] at hs
    obtain rfl | rfl | hs := hs
    · exact ⟨fun _ h => Or.inl h, fun a h => List.mem_cons.mpr (Or.inl (by simpa [eq_comm] using h))⟩
    · exact List.mem_cons_self
    · cases s with
      | sectionAt a => exact List.mem_cons_of_mem _ (ih hs)
      | sector l u =>
        obtain ⟨hl, hu⟩ := ih hs
        exact ⟨fun a h => Or.inr (List.mem_cons.mpr (by simpa [eq_comm] using hl a h)),
          fun a h => List.mem_cons_of_mem _ (hu a h)⟩

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem slices_nodup {rs : List (Aff K n)} (h : rs.Nodup) (lo : Option (Aff K n)) :
    (slices lo rs).Nodup := by
  induction rs generalizing lo with
  | nil => simp [slices]
  | cons r rs ih =>
    obtain ⟨hr, hrs⟩ := List.nodup_cons.mp h
    rw [slices, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, ih hrs (some r)⟩
    · intro hm
      rcases List.mem_cons.mp hm with h | h
      · cases h
      · have hb := slices_bounds h
        exact hr (hb.2 r rfl)
    · intro hm
      exact hr (slices_bounds hm)

omit [IsStrictOrderedRing K] in
theorem cad_nodup (n : ℕ) (fs : List (Aff K n)) : (cad n fs).Nodup := by
  induction n with
  | zero => simp [cad]
  | succ n ih =>
    change ((cad n (prune (project fs))).flatMap fun b =>
      (stack b.sample (roots fs)).map (Cell.lift b)).Nodup
    refine List.nodup_flatMap.mpr ⟨?_, ?_⟩
    · intro b _
      apply List.Nodup.map (fun _ _ h => (Cell.lift.inj h).2)
      apply slices_nodup
      have sorted := (ordered_spec b.sample (roots fs)).1
      exact sorted.imp fun {r s} (h : Aff.eval r b.sample < Aff.eval s b.sample) e =>
        h.ne (congrArg (fun r => Aff.eval r b.sample) e)
    · refine (ih _).imp ?_
      intro a b ne c ha hb
      obtain ⟨s,_,rfl⟩ := List.mem_map.mp ha
      obtain ⟨t,_,he⟩ := List.mem_map.mp hb
      exact ne (Cell.lift.inj he).1.symm

/-- All affine bounds used by one cell are sign-invariant on every cell of the same CAD. -/
theorem constraints_invariant (n : ℕ) (fs : List (Aff K n))
    {c d : Cell K n} (hc : c ∈ cad n fs) (hd : d ∈ cad n fs)
    {p : Point K n} (hp : d.Contains p) {a : Aff K n × Side} (ha : a ∈ c.constraints) :
    side (Aff.eval a.1 p) 0 = side (Aff.eval a.1 d.sample) 0 := by
  induction n with
  | zero => cases c; simp [constraints] at ha
  | succ n ih =>
    obtain ⟨b,hb,hs⟩ := List.mem_flatMap.mp hc
    obtain ⟨s,hss,rfl⟩ := List.mem_map.mp hs
    obtain ⟨e,he,ht⟩ := List.mem_flatMap.mp hd
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp ht
    obtain ⟨p,z⟩ := p
    have rootSign (r : Aff K n) (hr : r ∈ roots fs) :
        side (Aff.eval (n := n+1) (r, -1) (p,z)) 0 =
          side (Aff.eval (n := n+1) (r, -1) (Cell.lift e t).sample) 0 := by
      simp only [roots, List.mem_dedup, List.mem_map, List.mem_filter, bne, beq_eq_decide,
        Bool.not_eq_true', decide_eq_false_iff_not] at hr
      obtain ⟨f, ⟨hf, hn⟩, rfl⟩ := hr
      apply sign_bound hn
      have eq (q : Point K (n+1)) : f.2 * Aff.eval (n := n+1) (root f, -1) q = -Aff.eval f q := by
        obtain ⟨q,u⟩ := q
        simp only [Aff.eval, Aff.eval_scale]
        field_simp
        ring
      rw [eq, eq]
      have h := (cad_correct (n+1) fs).sign_invariant _ hd (p,z) hp f hf
      obtain ⟨_,h0,hp⟩ := side_congr h
      simp [side, hp, h0]
    simp only [constraints, List.mem_append] at ha
    rcases ha with ha | ha
    · obtain ⟨a', ha', rfl⟩ := List.mem_map.mp ha
      simpa [Aff.eval, sample] using ih _ hb he hp.1 ha'
    · have hm := (ordered_spec b.sample (roots fs)).2.1
      have bound := slices_bounds (lo := none) hss
      cases s with
      | sectionAt r =>
        have h : a = ((r, -1), .on) := List.mem_singleton.mp (by simpa only [sliceConstraints] using ha)
        rw [h]
        exact rootSign r (hm r bound)
      | sector l u =>
        rw [sliceConstraints] at ha
        obtain ha | ha := List.mem_append.mp ha
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
          exact rootSign r (hm r ((bound.1 r (by simpa using hr)).resolve_left (by simp)))
        · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
          exact rootSign r (hm r (bound.2 r (by simpa using hr)))

theorem inWeak_eq_sample {fs : List (Aff K n)} {c d : Cell K n}
    (hc : c ∈ cad n fs) (hd : d ∈ cad n fs) {p} (hp : d.Contains p) :
    c.inWeak p = c.inWeak d.sample := by
  apply Bool.eq_iff_iff.mpr
  simp only [inWeak_iff]
  exact forall₂_congr fun a ha => weak_congr a.2 (constraints_invariant n fs hc hd hp ha)


omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem constraints_map (φ : K →+* ℝ) (c : Cell K n) :
    (Extension.cell φ c).constraints = c.constraints.map fun (a, s) => (Extension.aff φ a, s) := by
  induction c with
  | origin => rfl
  | lift b s ih =>
    simp only [Extension.cell, constraints, ih, List.map_append, List.map_map, Function.comp_def]
    congr 1
    · simp [Extension.aff]
    · cases s with
      | sectionAt r => simp [Extension.slice, sliceConstraints, Extension.aff]
      | sector l u => cases l <;> cases u <;> simp [Extension.slice, sliceConstraints, Extension.aff]

theorem inWeak_map (φ : K →+* ℝ) (mono : StrictMono φ) (c : Cell K n) (p : Point K n) :
    (Extension.cell φ c).inWeak (Extension.point φ p) = c.inWeak p := by
  have le0 (x : K) : φ x ≤ 0 ↔ x ≤ 0 := by simpa using mono.le_iff_le (a := x) (b := 0)
  have zero_le (x : K) : 0 ≤ φ x ↔ 0 ≤ x := by simpa using mono.le_iff_le (a := 0) (b := x)
  have h (v : K) (s : Side) : weak s (φ v) ↔ weak s v := by cases s <;> simp [weak, le0, zero_le]
  simp [inWeak, constraints_map, List.all_map, Function.comp_def, h]

end Cell

namespace Geometry
open Set

@[fun_prop] theorem continuous_eval_coords {n} (f : Aff ℝ n) :
    Continuous (fun x : Fin n → ℝ => Aff.eval f (coords x)) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    change Continuous fun x : Fin (n+1) → ℝ =>
      Aff.eval f.1 (coords fun i => x i.castSucc) + f.2 * x (Fin.last n)
    exact ((ih f.1).comp (continuous_pi fun _ => continuous_apply _)).add
      (continuous_const.mul (continuous_apply _))

theorem locallyClosed_carrier {n} (c : Cell ℝ n) : IsLocallyClosed (carrier c) := by
  have h (fs : List (Aff ℝ n × Side)) :
      IsLocallyClosed {x | ∀ f ∈ fs, side (Aff.eval f.1 (coords x)) 0 = f.2} := by
    induction fs with
    | nil => simpa using (isOpen_univ (X := Fin n → ℝ)).isLocallyClosed
    | cons a as ih =>
      have eq : {x | ∀ f ∈ a :: as, side (Aff.eval f.1 (coords x)) 0 = f.2} =
          {x | side (Aff.eval a.1 (coords x)) 0 = a.2} ∩
            {x | ∀ f ∈ as, side (Aff.eval f.1 (coords x)) 0 = f.2} := by
        ext
        simp
      rw [eq]
      refine IsLocallyClosed.inter ?_ ih
      obtain ⟨f, s⟩ := a
      have cont := continuous_eval_coords f
      cases s
      · simpa only [Cell.side_below] using (isOpen_lt cont continuous_const).isLocallyClosed
      · simpa only [Cell.side_on] using (isClosed_eq cont continuous_const).isLocallyClosed
      · simpa only [Cell.side_above] using (isOpen_lt continuous_const cont).isLocallyClosed
  have eq : carrier c = {x | ∀ f ∈ c.constraints, side (Aff.eval f.1 (coords x)) 0 = f.2} := by
    ext x
    exact Cell.contains_iff_constraints c (coords x)
  rw [eq]
  exact h _

theorem mem_closure_iff_inWeak {n} (c : Cell ℝ n) (hc : (carrier c).Nonempty) (x : Fin n → ℝ) :
    x ∈ closure (carrier c) ↔ c.inWeak (coords x) = true := by
  simp only [Cell.inWeak_iff]
  constructor
  · intro hx a ha
    let S : Set (Fin n → ℝ) := {y | Cell.weak a.2 (Aff.eval a.1 (coords y))}
    have closed : IsClosed S := by
      unfold S
      obtain ⟨f, s⟩ := a
      cases s
      · exact isClosed_le (continuous_eval_coords f) continuous_const
      · exact isClosed_eq (continuous_eval_coords f) continuous_const
      · exact isClosed_le continuous_const (continuous_eval_coords f)
    exact closure_minimal (fun y hy => Cell.weak_of_side
      ((Cell.contains_iff_constraints c (coords y)).mp hy _ ha)) closed hx
  · intro hx
    obtain ⟨y, hy⟩ := hc
    have hseg : openSegment ℝ x y ⊆ carrier c := by
      rintro _ ⟨a, b, ha, hb, hab, rfl⟩
      apply (Cell.contains_iff_constraints c _).mpr
      intro f hf
      have h₁ := hx f hf
      have h₂ := (Cell.contains_iff_constraints c _).mp hy f hf
      rw [eval_combine _ _ _ hab]
      cases hs : f.2 with
      | below =>
        rw [hs] at h₁
        rw [hs, Cell.side_below] at h₂
        rw [Cell.side_below]
        exact add_neg_of_nonpos_of_neg (mul_nonpos_of_nonneg_of_nonpos ha.le h₁) (mul_neg_of_pos_of_neg hb h₂)
      | on =>
        rw [hs] at h₁
        rw [hs, Cell.side_on] at h₂
        rw [Cell.side_on]
        change Aff.eval f.1 (coords x) = 0 at h₁
        simp [h₁, h₂]
      | above =>
        rw [hs] at h₁
        rw [hs, Cell.side_above] at h₂
        rw [Cell.side_above]
        exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le h₁) (mul_pos hb h₂)
    exact closure_mono hseg (segment_subset_closure_openSegment (left_mem_segment ℝ x y))

end Geometry

namespace AffineTopology

open Set TopologyArtifact

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

def equations : List (Product K n) → Formula (Aff K n)
  | [] => .truth true
  | f :: fs => .conj (.atom f .on) (equations fs)

omit [IsStrictOrderedRing K] in
theorem equations_eval (fs : List (Product K n)) (p : Point K n) :
    (equations fs).eval p = true ↔ ∀ f ∈ fs, productEval f p = 0 := by
  induction fs with
  | nil => simp [equations, Formula.eval]
  | cons f fs ih =>
    simp [equations, Formula.eval, Cell.side_on, ih]

/-- Compute the affine CAD and its directed frontier table in the input field. -/
def solveFactors (fs : List (Product K n)) : Layout (Cell K n) :=
  Layout.ofCells (solve (equations fs)) fun c d => c.inWeak d.sample

def realLocus (φ : K →+* ℝ) (fs : List (Product K n)) : Set (Fin n → ℝ) :=
  {x | ∀ f ∈ fs, productEval (f.map (Extension.aff φ)) (Geometry.coords x) = 0}

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem realLocus_closed (φ : K →+* ℝ) (fs : List (Product K n)) :
    IsClosed (realLocus φ fs) := by
  have eq : realLocus φ fs = ⋂ f ∈ fs, {x | productEval (f.map (Extension.aff φ)) (Geometry.coords x) = 0} := by
    ext x
    simp [realLocus]
  rw [eq]
  apply isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
  have cont (gs : List (Aff ℝ n)) : Continuous fun x : Fin n → ℝ =>
      productEval gs (Geometry.coords x) := by
    induction gs with
    | nil => exact continuous_const
    | cons g gs ih => exact (Geometry.continuous_eval_coords g).mul ih
  exact cont _

theorem solveFactors_correct (φ : K →+* ℝ) (mono : StrictMono φ) (fs : List (Product K n)) :
    Valid (solveFactors fs) (Geometry.carrier ∘ Extension.cell φ) (realLocus φ fs) := by
  let F := equations fs
  let G := equations (fs.map (List.map (Extension.aff φ)))
  have eq : G = Extension.formula φ F := by
    induction fs with
    | nil => rfl
    | cons f fs ih =>
      change Formula.conj (.atom _ _) _ = Formula.conj (.atom _ _) _
      rw [ih]
  have cells : solve G = (solve F).map (Extension.cell φ) := by
    rw [eq, Extension.solve_map φ mono]
  let cs := solve F
  have getMem (i : Fin cs.length) : Extension.cell φ (cs.get i) ∈ solve G :=
    cells.symm ▸ List.mem_map_of_mem (List.get_mem cs i)
  have inCAD (i : Fin cs.length) : Extension.cell φ (cs.get i) ∈ cad n G.factors :=
    (List.mem_filter.mp (getMem i)).1
  have nonempty (i : Fin cs.length) : (Geometry.carrier (Extension.cell φ (cs.get i))).Nonempty := by
    let d := Extension.cell φ (cs.get i)
    obtain ⟨x,hx⟩ := Geometry.coords_surjective n d.sample
    exact ⟨x, show d.Contains (Geometry.coords x) from hx ▸ (cad_correct n G.factors).sample_mem _ (inCAD i)⟩
  have solution (x : Fin n → ℝ) :
      x ∈ realLocus φ fs ↔ G.eval (Geometry.coords x) = true := by
    simpa [G, realLocus] using (equations_eval (fs.map (List.map (Extension.aff φ))) (Geometry.coords x)).symm
  refine ⟨realLocus_closed φ fs, ?_, ?_, nonempty, fun _ => Geometry.locallyClosed_carrier _, ?_, ?_⟩
  · intro x
    rw [solution]
    constructor
    · intro hx
      obtain ⟨c,hc,hx⟩ := ((solve_correct G (Geometry.coords x)).mp hx).exists
      obtain ⟨d,hd,rfl⟩ := List.mem_map.mp (cells ▸ hc)
      obtain ⟨i,rfl⟩ := List.get_of_mem hd
      exact ⟨i,hx⟩
    · rintro ⟨i, hi⟩
      have hp := (cad_correct n G.factors).sign_invariant _ (inCAD i) _ hi
      exact (G.eval_congr hp).trans (List.mem_filter.mp (getMem i)).2
  · intro x i j hi hj
    have unique := (cad_correct n G.factors).partition (Geometry.coords x)
    obtain ⟨_,_,u⟩ := unique
    have hn : cs.Nodup := (Cell.cad_nodup n F.factors).filter _
    change (i : Fin cs.length) = j
    exact hn.injective_get (Extension.cell_injective φ
      ((u _ ⟨inCAD i, hi⟩).trans (u _ ⟨inCAD j, hj⟩).symm))
  · intro i
    exact Geometry.contractible_cell G.factors (inCAD i)
  · intro i j x hx
    change (Layout.ofCells cs fun c d => c.inWeak d.sample).incident i j = true ↔
      x ∈ closure (Geometry.carrier (Extension.cell φ (cs.get i)))
    rw [Layout.incident_ofCells cs (fun c d => c.inWeak d.sample) i j]
    rw [Geometry.mem_closure_iff_inWeak _ (nonempty i)]
    rw [Cell.inWeak_eq_sample (inCAD i) (inCAD j) hx, Extension.sample_cell, Cell.inWeak_map φ mono]

end AffineTopology
end CertifiedTopology
