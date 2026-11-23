module

public import CertifiedTopology.Stack

@[expose] public section

namespace CertifiedTopology

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

def Invariant (fs : List (Aff K n)) (c : Cell K n) :=
  ∀ p, c.Contains p → ∀ f ∈ fs, side (Aff.eval f p) 0 = side (Aff.eval f c.sample) 0

private theorem side_sub (a b : K) : side (a-b) 0 = side a b := by
  simp [side,sub_neg,sub_eq_zero]

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem compare_pair {rs : List (Aff K n)} {r s} (hr : r ∈ rs) (hs : s ∈ rs) :
    r = s ∨ Aff.sub r s ∈ differences rs ∨ Aff.sub s r ∈ differences rs := by
  induction rs with
  | nil => simp at hr
  | cons a as ih =>
    rcases List.mem_cons.mp hr with er | hr'
    · subst r
      rcases List.mem_cons.mp hs with es | hs'
      · exact Or.inl es.symm
      · exact Or.inr (Or.inl (List.mem_append_left _ (List.mem_map_of_mem hs')))
    rcases List.mem_cons.mp hs with es | hs'
    · subst s
      exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_map_of_mem hr')))
    rcases ih hr' hs' with e | h | h
    · exact Or.inl e
    · exact Or.inr (Or.inl (List.mem_append_right _ h))
    · exact Or.inr (Or.inr (List.mem_append_right _ h))

private theorem root_order {fs : List (Aff K (n+1))} {b : Cell K n}
    (hi : Invariant (project fs) b) {p} (hp : b.Contains p)
    {r s} (hr : r ∈ roots fs) (hs : s ∈ roots fs) :
    side (Aff.eval r p) (Aff.eval s p) = side (Aff.eval r b.sample) (Aff.eval s b.sample) := by
  have H (u v : Aff K n) (h : Aff.sub u v ∈ differences (roots fs)) :
      side (Aff.eval u p) (Aff.eval v p) = side (Aff.eval u b.sample) (Aff.eval v b.sample) := by
    simpa [side_sub] using hi p hp _ (List.mem_append_right _ h)
  rcases compare_pair hr hs with rfl | h | h
  · simp
  · exact H _ _ h
  · obtain ⟨_,he,hg⟩ := side_congr (H _ _ h)
    simp only [side,hg,eq_comm (a := Aff.eval r p),he,eq_comm (a := Aff.eval s b.sample)]

private theorem sorted_over {fs : List (Aff K (n+1))} {b : Cell K n}
    (hi : Invariant (project fs) b) {p} (hp : b.Contains p) :
    SortedAt p (orderedRoots b.sample (roots fs)) := by
  obtain ⟨ho,hm,_⟩ := ordered_spec b.sample (roots fs)
  apply ho.imp_of_mem
  intro r s hr hs h
  exact ((side_congr (root_order hi hp (hm r hr) (hm s hs))).1).mpr h

private theorem side_linear {a b c t u : K} (ha : a ≠ 0)
    (h : side t (-a⁻¹*b) = side u (-a⁻¹*c)) :
    side (b+a*t) 0 = side (c+a*u) 0 := by
  have hb : b + a*t = a*(t-(-a⁻¹*b)) := by field_simp; ring
  have hc : c + a*u = a*(u-(-a⁻¹*c)) := by field_simp; ring
  rw [hb,hc]
  rw [← side_sub, ← side_sub u] at h
  obtain ⟨hl,he,hg⟩ := side_congr h
  simp only [side, mul_neg_iff, mul_eq_zero, ha, false_or, hl, he, hg]

structure CADSpec (fs : List (Aff K n)) (cs : List (Cell K n)) : Prop where
  partition : ∀ p, ∃! c, c ∈ cs ∧ c.Contains p
  sample_mem : ∀ c ∈ cs, c.Contains c.sample
  sign_invariant : ∀ c ∈ cs, Invariant fs c

theorem cad_correct (m : ℕ) (fs : List (Aff K m)) : CADSpec fs (cad m fs) := by
  induction m with
  | zero =>
    constructor
    · intro _
      exact ⟨.origin, ⟨by simp [cad], trivial⟩, fun c hc => by simpa [cad] using hc.1⟩
    · intro c _; cases c; trivial
    · intro c _ p _ f _; cases c; rfl
  | succ m ih =>
    have base := ih (prune (project fs))
    have invariant (b) (hb : b ∈ cad m (prune (project fs))) : Invariant (project fs) b := by
      intro p hp f hf
      by_cases h : Aff.constant f
      · rw [Aff.eval_constant _ h p b.sample]
      · exact base.sign_invariant b hb p hp f (by simp [prune,hf,h])
    have spec (b : Cell K m) := ordered_spec b.sample (roots fs)
    constructor
    · rintro ⟨p,t⟩
      obtain ⟨b,⟨hb,hp⟩,ub⟩ := base.partition p
      obtain ⟨s,⟨hs,ht⟩,us⟩ := slice_partition p (sorted_over (invariant b hb) hp)
        none (by simp [Lower]) t (by simp [Lower])
      refine ⟨.lift b s, ⟨List.mem_flatMap.mpr ⟨b,hb,List.mem_map.mpr ⟨s,hs,rfl⟩⟩,hp,ht⟩, ?_⟩
      rintro z ⟨hz,hz'⟩
      obtain ⟨d,hd,k⟩ := List.mem_flatMap.mp hz
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp k
      obtain rfl := ub d ⟨hd,hz'.1⟩
      obtain rfl := us w ⟨hw,hz'.2⟩
      rfl
    · intro z hz
      obtain ⟨b,hb,k⟩ := List.mem_flatMap.mp hz
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp k
      exact ⟨base.sample_mem _ hb, slice_sample _ (spec b).1 none (by simp [Lower]) hs⟩
    · intro z hz
      obtain ⟨b,hb,k⟩ := List.mem_flatMap.mp hz
      obtain ⟨s,hs,rfl⟩ := List.mem_map.mp k
      rintro ⟨p,t⟩ ⟨hp,ht⟩ f hf
      have bi := invariant b hb
      change side (Aff.eval f.1 p + f.2*t) 0 =
        side (Aff.eval f.1 b.sample + f.2*s.sample b.sample) 0
      by_cases ha : f.2 = 0
      · simp only [ha,zero_mul,add_zero]
        apply bi p hp
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨f,by simp [hf,ha],rfl⟩
      have hr : root f ∈ roots fs := by
        simp only [roots,List.mem_dedup]
        apply List.mem_map.mpr
        exact ⟨f,by simp [hf,ha],rfl⟩
      obtain ⟨r,hm,he⟩ := (spec b).2.2 _ hr
      have he' := (side_congr (root_order bi hp ((spec b).2.1 _ hm) hr)).2.1.mpr he
      have h := slice_sign (sorted_over bi hp) (spec b).1 none hs ht
        (slice_sample _ (spec b).1 none (by simp [Lower]) hs) hm
      rw [he,he'] at h
      apply side_linear ha
      simpa using h

end CertifiedTopology
