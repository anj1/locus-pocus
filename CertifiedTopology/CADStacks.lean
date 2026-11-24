module

public import CertifiedTopology.CylindricalData

@[expose] public section

namespace CertifiedTopology.CADStacks

open Set Polynomial CylindricalData Plane

def mapSlice {A B : Type} (f : A → B) : Slice A → Slice B
  | .sectionAt r => .sectionAt (f r)
  | .sector l u => .sector (l.map f) (u.map f)

def slicesOf {A : Type} (lo : Option A) : List A → List (Slice A)
  | [] => [.sector lo none]
  | a :: as => .sector lo (some a) :: .sectionAt a :: slicesOf (some a) as

theorem slicesOf_map {A B : Type} (f : A → B) (lo : Option A) (rs : List A) :
    (slicesOf lo rs).map (mapSlice f) = slicesOf (lo.map f) (rs.map f) := by
  induction rs generalizing lo with
  | nil => rfl
  | cons a as ih => simp [slicesOf, mapSlice, ih]

theorem slicesOf_real (lo : Option ℝ) (rs : List ℝ) :
    slicesOf lo rs = slices (n := 0) lo rs := by
  induction rs generalizing lo with
  | nil => rfl
  | cons a as ih => simp [slicesOf, slices, ih]

def frame (m : ℕ) : List (Slice (Fin m)) := slicesOf none (List.finRange m)

private theorem upper_in_slices {A : Type} {lo l : Option A} {u : A} {rs : List A}
    (h : Slice.sector l (some u) ∈ slicesOf lo rs) : u ∈ rs := by
  induction rs generalizing lo with
  | nil => simp [slicesOf] at h
  | cons a rs ih =>
    simp only [slicesOf,List.mem_cons] at h
    rcases h with h | h | h
    · have e := Slice.sector.inj h
      exact List.mem_cons.mpr (Or.inl (Option.some.inj e.2))
    · cases h
    · exact List.mem_cons_of_mem _ (ih h)

private theorem section_in_slices {A : Type} {rs : List A} {a : A} {lo : Option A}
    (h : Slice.sectionAt a ∈ slicesOf lo rs) : a ∈ rs := by
  induction rs generalizing lo with
  | nil => simp [slicesOf] at h
  | cons b rs ih =>
    simp only [slicesOf,List.mem_cons] at h
    rcases h with h | h | h
    · cases h
    · exact List.mem_cons.mpr (Or.inl (Slice.sectionAt.inj h))
    · exact List.mem_cons_of_mem _ (ih h)

theorem slicesOf_nodup {A : Type} {rs : List A} (h : rs.Nodup) (lo : Option A) :
    (slicesOf lo rs).Nodup := by
  induction rs generalizing lo with
  | nil => simp [slicesOf]
  | cons a as ih =>
    obtain ⟨ha,hs⟩ := List.nodup_cons.mp h
    rw [slicesOf, List.nodup_cons, List.nodup_cons]
    refine ⟨?_, ?_, ih hs _⟩
    · intro hm
      rcases List.mem_cons.mp hm with h | h
      · cases h
      · exact ha (upper_in_slices h)
    · intro hm
      exact ha (section_in_slices hm)


theorem realStack_nodup (p : Polynomial ℝ) : (realStack p).Nodup := by
  rw [realStack, ← slicesOf_real]
  exact slicesOf_nodup ((sortedRoots_order p).imp LT.lt.ne) _

theorem section_mem_slicesOf {A : Type} {rs : List A} {a : A} (ha : a ∈ rs) (lo : Option A) :
    Slice.sectionAt a ∈ slicesOf lo rs := by
  induction rs generalizing lo with
  | nil => simp at ha
  | cons b bs ih =>
    rcases List.mem_cons.mp ha with rfl | h
    · simp [slicesOf]
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih h (some b)))

theorem section_mem_frame {m : ℕ} (i : Fin m) : .sectionAt i ∈ frame m :=
  section_mem_slicesOf (List.mem_finRange i) none

theorem frame_ordered {m : ℕ} {l u : Fin m} (h : Slice.sector (some l) (some u) ∈ frame m) :
    l < u := by
  have all_order {A : Type} [LinearOrder A] (xs : List A) (ord : xs.Pairwise (· < ·))
      (lo : Option A) (loord : ∀ a ∈ lo, ∀ b ∈ xs, a < b) {l u : A}
      (h : Slice.sector (some l) (some u) ∈ slicesOf lo xs) : l < u := by
    induction xs generalizing lo with
    | nil => simp [slicesOf] at h
    | cons x xs ih =>
      simp only [slicesOf, List.mem_cons] at h
      rcases h with e | e | h
      · obtain ⟨hl,hu⟩ := Slice.sector.inj e
        have eq := Option.some.inj hu
        exact eq.symm ▸ loord l hl.symm x (by simp)
      · cases e
      · exact ih (List.pairwise_cons.mp ord).2 (some x)
          (fun a ha b hb => by
            have e : a = x := by simpa using ha.symm
            exact e ▸ (List.pairwise_cons.mp ord).1 b hb) h
  exact all_order _ (List.pairwise_lt_finRange m) none (by simp) h

theorem realStack_of_family {B : Type} [TopologicalSpace B] [PreconnectedSpace B]
    (P : RootFamily B) (sample x : B) :
    realStack (P.poly x) =
      (frame (P.roots sample).card).map (mapSlice (fun i => P.rootSection sample i x)) := by
  rw [frame, slicesOf_map, slicesOf_real, realStack]
  congr 1
  refine (roots_eq_sorted (P.nonzero x) ?_ ?_).symm
  · apply List.pairwise_map.mpr
    exact (List.pairwise_lt_finRange _).imp (fun {i j} h => P.section_order sample x h)
  · intro y
    simp only [List.mem_map, List.mem_finRange, true_and]
    exact ⟨fun ⟨i,h⟩ => h ▸ (P.mem_roots x _).mp (P.section_mem sample x i),
      fun hy => P.exists_section sample x ((P.mem_roots x _).mpr hy)⟩

variable {n : ℕ} {A : Set (Fin n → ℝ)}

abbrev dropLast (p : Fin (n+1) → ℝ) : Fin n → ℝ := fun i => p i.castSucc

abbrev last (p : Fin (n+1) → ℝ) := p (Fin.last n)

theorem snoc_dropLast (p : Fin (n+1) → ℝ) : Fin.snoc (dropLast p) (last p) = p := by
  funext i
  cases i using Fin.lastCases <;> simp

def region {m : ℕ} (c : Fin m → A → ℝ) (s : Slice (Fin m)) : Set (Fin (n+1) → ℝ) :=
  {p | ∃ h : dropLast p ∈ A,
    Univariate.contains (mapSlice (fun i => c i ⟨dropLast p,h⟩) s) (last p)}

theorem region_snoc {m : ℕ} (c : Fin m → A → ℝ) (s : Slice (Fin m)) (x : Fin n → ℝ) (y : ℝ) :
    Fin.snoc x y ∈ region c s ↔ ∃ h : x ∈ A,
      Univariate.contains (mapSlice (fun i => c i ⟨x,h⟩) s) y := by
  have e : dropLast (Fin.snoc x y) = x := by
    funext i
    exact @Fin.snoc_castSucc n (fun _ => ℝ) y x i
  have l : last (Fin.snoc x y) = y := @Fin.snoc_last n (fun _ => ℝ) y x
  rw [region, mem_ofPred_eq, e, l]

@[fun_prop] theorem continuous_snoc {X : Type} [TopologicalSpace X]
    {x : X → Fin n → ℝ} {y : X → ℝ} (hx : Continuous x) (hy : Continuous y) :
    Continuous fun p => (Fin.snoc (x p) (y p) : Fin (n+1) → ℝ) := by
  apply continuous_pi
  intro i
  cases i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using hy
  | cast j => simpa only [Fin.snoc_castSucc, Function.comp_def] using (continuous_apply j).comp hx

private theorem region_section {m : ℕ} (c : Fin m → A → ℝ) (a : Fin m) :
    region c (.sectionAt a) = range (fun x : A => Fin.snoc x.val (c a x)) := by
  ext p
  have e : Fin.snoc (dropLast p) (last p) = p := snoc_dropLast p
  rw [← e, region_snoc]
  simp only [mapSlice, Univariate.contains, Slice.Contains, Aff.eval, mem_range]
  constructor
  · rintro ⟨h,hy⟩
    exact ⟨⟨dropLast p,h⟩, by rw [hy]⟩
  · rintro ⟨x,h⟩
    have hx : x.val = dropLast p := by
      funext j
      have eq := congrFun h j.castSucc
      simpa only [Fin.snoc_castSucc] using eq
    refine ⟨hx ▸ x.property, ?_⟩
    have ex : (⟨dropLast p, hx ▸ x.property⟩ : A) = x := Subtype.ext hx.symm
    rw [ex]
    have eq := congrFun h (Fin.last n)
    simpa only [Fin.snoc_last] using eq.symm

theorem isPreconnected_region {m : ℕ} (c : Fin m → A → ℝ) (s : Slice (Fin m))
    (hA : IsPreconnected A) (con : ∀ i, Continuous (c i))
    (ordered : ∀ x : A, StrictMono (fun i => c i x))
    (hbound : ∀ l u, s = .sector (some l) (some u) → l < u) :
    IsPreconnected (region c s) := by
  let : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp hA
  cases s with
  | sectionAt i =>
    rw [region_section]
    exact isPreconnected_range (continuous_snoc continuous_subtype_val (con i))
  | sector lo up =>
    -- Parameterize each kind of interval using a fixed real interval.
    let strip : Set ℝ := match lo, up with
      | none, none => univ
      | none, some _ | some _, none => Ioi 0
      | some _, some _ => Ioo 0 1
    let height (x : A) (t : ℝ) : ℝ := match lo, up with
      | none, none => t
      | none, some u => c u x - t
      | some l, none => c l x + t
      | some l, some u => c l x + t*(c u x - c l x)
    have cs : IsPreconnected strip := by
      cases lo <;> cases up <;> dsimp [strip] <;>
        first | exact isPreconnected_univ | exact (convex_Ioi _).isPreconnected |
          exact (convex_Ioo _ _).isPreconnected
    let : PreconnectedSpace strip := isPreconnected_iff_preconnectedSpace.mp cs
    let chart (p : A × strip) : Fin (n+1) → ℝ := Fin.snoc p.1.val (height p.1 p.2.val)
    have conH : Continuous (fun p : A × strip => height p.1 p.2.val) := by
      have h {i} := (con i).comp (continuous_fst (X := A) (Y := strip))
      have ht : Continuous (fun p : A × strip => p.2.val) := continuous_subtype_val.comp continuous_snd
      cases lo <;> cases up
      · exact ht
      · exact h.sub ht
      · exact h.add ht
      · exact h.add (ht.mul (h.sub h))
    have cont : Continuous chart :=
      continuous_snoc (continuous_subtype_val.comp continuous_fst) conH
    have onto (x : A) (y : ℝ) :
        Univariate.contains (mapSlice (fun i => c i x) (.sector lo up)) y ↔
          ∃ t : strip, height x t.val = y := by
      cases lo with
      | none =>
        cases up with
        | none =>
          refine ⟨fun _ => ⟨⟨y,mem_univ y⟩,rfl⟩, fun _ => ?_⟩
          simp [mapSlice, Univariate.contains, Slice.Contains]
        | some u =>
          have eq : Univariate.contains (mapSlice (fun i => c i x) (.sector none (some u))) y ↔ y < c u x := by
            simp [mapSlice, Univariate.contains, Slice.Contains, Aff.eval]
          rw [eq]
          constructor
          · intro hy
            exact ⟨⟨c u x - y, sub_pos.mpr hy⟩, by dsimp [height]; ring⟩
          · rintro ⟨t,rfl⟩
            change c u x - t.val < c u x
            exact sub_lt_self _ t.property
      | some l =>
        cases up with
        | none =>
          have eq : Univariate.contains (mapSlice (fun i => c i x) (.sector (some l) none)) y ↔ c l x < y := by
            simp [mapSlice, Univariate.contains, Slice.Contains, Aff.eval]
          rw [eq]
          constructor
          · intro hy
            exact ⟨⟨y - c l x, sub_pos.mpr hy⟩, by dsimp [height]; ring⟩
          · rintro ⟨t,rfl⟩
            change c l x < c l x + t.val
            exact lt_add_of_pos_right _ t.property
        | some u =>
          have eq : Univariate.contains (mapSlice (fun i => c i x) (.sector (some l) (some u))) y ↔
              c l x < y ∧ y < c u x := by
            simp [mapSlice, Univariate.contains, Slice.Contains, Aff.eval]
          rw [eq]
          have gap : 0 < c u x - c l x := sub_pos.mpr (ordered x (hbound l u rfl))
          constructor
          · rintro ⟨h₁,h₂⟩
            have norm : (y-c l x)/(c u x-c l x) ∈ Ioo (0 : ℝ) 1 :=
              ⟨div_pos (sub_pos.mpr h₁) gap, (div_lt_one gap).mpr (sub_lt_sub_right h₂ _)⟩
            refine ⟨⟨_, norm⟩, ?_⟩
            dsimp [height]
            rw [div_mul_cancel₀ _ gap.ne']
            ring
          · rintro ⟨t,rfl⟩
            have mulpos : 0 < t.val * (c u x - c l x) := mul_pos t.property.1 gap
            have mullt : t.val * (c u x - c l x) < c u x - c l x :=
              mul_lt_of_lt_one_left gap t.property.2
            change c l x < c l x + t.val * (c u x - c l x) ∧
              c l x + t.val * (c u x - c l x) < c u x
            constructor <;> linarith
    have eq : region c (.sector lo up) = range chart := by
      ext p
      have eta : Fin.snoc (dropLast p) (last p) = p := snoc_dropLast p
      rw [← eta, region_snoc]
      constructor
      · rintro ⟨h,hp⟩
        obtain ⟨t,ht⟩ := (onto ⟨dropLast p,h⟩ (last p)).mp hp
        exact ⟨(⟨dropLast p,h⟩,t), by simp [chart, ht]⟩
      · rintro ⟨⟨x,t⟩,ht⟩
        have hx : x.val = dropLast p := by
          funext j
          have h := congrFun ht j.castSucc
          simpa [chart] using h
        have hh : dropLast p ∈ A := hx ▸ x.property
        have ex : (⟨dropLast p,hh⟩ : A) = x := Subtype.ext hx.symm
        refine ⟨hh, (onto _ _).mpr ⟨t,?_⟩⟩
        rw [ex]
        have h := congrFun ht (Fin.last n)
        simpa [chart] using h
    rw [eq]
    exact isPreconnected_range cont

end CertifiedTopology.CADStacks
