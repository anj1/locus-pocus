module

public import CertifiedTopology.Affine

@[expose] public section

namespace CertifiedTopology
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}
abbrev SortedAt (p : Point K n) (rs : List (Aff K n)) :=
  rs.Pairwise fun a b => Aff.eval a p < Aff.eval b p

omit [IsStrictOrderedRing K] in
private theorem insert_mem (p : Point K n) (r s : Aff K n) (rs : List (Aff K n))
    (h : s ∈ insertRoot p r rs) : s = r ∨ s ∈ rs := by
  induction rs with
  | nil => simpa [insertRoot] using h
  | cons a as ih =>
    simp only [insertRoot] at h
    split at h
    · simpa using h
    split at h
    · exact Or.inr h
    rcases List.mem_cons.mp h with e | h
    · simp [e]
    rcases ih h with e | h <;> simp_all

omit [IsStrictOrderedRing K] in
private theorem insert_sorted (p : Point K n) (r : Aff K n) {rs : List (Aff K n)}
    (h : SortedAt p rs) : SortedAt p (insertRoot p r rs) := by
  induction rs with
  | nil => simp [insertRoot, SortedAt]
  | cons a as ih =>
    obtain ⟨ha,hs⟩ := List.pairwise_cons.mp h
    unfold insertRoot
    split
    · exact List.pairwise_cons.mpr ⟨by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · assumption
        · exact lt_trans (by assumption) (ha b hb), h⟩
    split
    · exact h
    · apply List.pairwise_cons.mpr
      refine ⟨?_, ih hs⟩
      intro b hb
      rcases insert_mem p r b as hb with rfl | hb
      · order
      · exact ha b hb

omit [IsStrictOrderedRing K] in
private theorem insert_values (p : Point K n) (r : Aff K n) (rs : List (Aff K n)) (v : K) :
    (∃ s ∈ insertRoot p r rs, Aff.eval s p = v) ↔
    Aff.eval r p = v ∨ ∃ s ∈ rs, Aff.eval s p = v := by
  induction rs with
  | nil => simp [insertRoot]
  | cons a as ih =>
    unfold insertRoot
    split
    · simp
    split
    · simp_all
    · simp [ih, or_left_comm]

omit [IsStrictOrderedRing K] in
theorem ordered_spec (p : Point K n) (rs : List (Aff K n)) :
    SortedAt p (orderedRoots p rs) ∧
    (∀ s ∈ orderedRoots p rs, s ∈ rs) ∧
    (∀ r ∈ rs, ∃ s ∈ orderedRoots p rs, Aff.eval s p = Aff.eval r p) := by
  induction rs with
  | nil => simp [orderedRoots, SortedAt]
  | cons r rs ih =>
    change SortedAt p (insertRoot p r _) ∧ _
    refine ⟨insert_sorted _ _ ih.1, ?_, ?_⟩
    · intro s hs
      rcases insert_mem p r s _ hs with rfl | hs
      · simp
      · exact List.mem_cons_of_mem _ (ih.2.1 _ hs)
    · intro s hs
      apply (insert_values p r _ _).mpr
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inl rfl
      · exact Or.inr (ih.2.2 _ hs)

abbrev Lower (p : Point K n) (lo : Option (Aff K n)) (t : K) :=
  ∀ l ∈ lo, Aff.eval l p < t

omit [IsStrictOrderedRing K] in
private theorem lower_of_mem {p : Point K n} {rs : List (Aff K n)} {lo}
    (hl : ∀ a ∈ rs, Lower p lo (Aff.eval a p))
    {s} (hs : s ∈ slices lo rs) {t} (ht : s.Contains p t) : Lower p lo t := by
  cases rs with
  | nil => simp [slices] at hs; subst s; exact ht.1
  | cons a as =>
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ht.1
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ht ▸ hl a (by simp)
    have hh : ∀ b ∈ as, Lower p lo (Aff.eval b p) := fun b hb => hl b (by simp [hb])
    -- Every tail slice starts at a root in the original list.
    suffices H : ∀ (prev : Aff K n), Lower p lo (Aff.eval prev p) →
        ∀ s ∈ slices (some prev) as, s.Contains p t → Lower p lo t by
      exact H a (hl a (by simp)) _ hs ht
    rename_i h₁ h₂
    clear h₁ h₂ hs hl ht s
    induction as with
    | nil =>
      intro prev hp z hz h
      simp [slices] at hz
      subst z
      exact fun l h => lt_trans (hp l h) (‹(Slice.sector _ _).Contains p t›.1 prev rfl)
    | cons b bs ih =>
      intro prev hp z hz h
      rcases List.mem_cons.mp hz with rfl | hz
      · exact fun l h' => lt_trans (hp l h') (h.1 prev rfl)
      rcases List.mem_cons.mp hz with rfl | hz
      · exact h ▸ hh b (by simp)
      exact ih (fun c hc => hh c (by simp [hc])) b (hh b (by simp)) z hz h

omit [IsStrictOrderedRing K] in
theorem slice_partition (p : Point K n) {rs : List (Aff K n)} (ho : SortedAt p rs)
    (lo) (hl : ∀ a ∈ rs, Lower p lo (Aff.eval a p)) (t : K) (ht : Lower p lo t) :
    ∃! s, s ∈ slices lo rs ∧ s.Contains p t := by
  induction rs generalizing lo with
  | nil =>
    refine ⟨.sector lo none, ⟨by simp [slices], ht, by simp⟩, ?_⟩
    intro z hz
    simpa [slices] using hz.1
  | cons a as ih =>
    obtain ⟨ha,hs⟩ := List.pairwise_cons.mp ho
    have hb : ∀ b ∈ as, Lower p (some a) (Aff.eval b p) := by simpa [Lower] using ha
    have tail : ∀ z ∈ slices (some a) as, z.Contains p t → Aff.eval a p < t :=
      fun _ hz h => lower_of_mem hb hz h a rfl
    rcases lt_trichotomy t (Aff.eval a p) with h | h | h
    · refine ⟨.sector lo (some a), ⟨by simp [slices], ht, by simpa using h⟩, ?_⟩
      rintro z ⟨hz,hz'⟩
      rcases List.mem_cons.mp hz with e | hz
      · exact e
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (h.ne hz').elim
      · exact (h.asymm (tail _ hz hz')).elim
    · refine ⟨.sectionAt a, ⟨by simp [slices], h⟩, ?_⟩
      rintro z ⟨hz,hz'⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ((hz'.2 a rfl).ne h).elim
      rcases List.mem_cons.mp hz with e | hz
      · exact e
      · exact ((tail _ hz hz').ne h.symm).elim
    · obtain ⟨s,⟨hm,hc⟩,hu⟩ := ih hs (some a) hb (by simpa [Lower] using h)
      refine ⟨s, ⟨by simp [slices,hm], hc⟩, ?_⟩
      rintro z ⟨hz,hz'⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (h.asymm (hz'.2 a rfl)).elim
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (h.ne (Eq.symm hz')).elim
      · exact hu _ ⟨hz,hz'⟩

theorem slice_sample (p : Point K n) {rs : List (Aff K n)} (ho : SortedAt p rs)
    (lo) (hl : ∀ a ∈ rs, Lower p lo (Aff.eval a p))
    {s} (hs : s ∈ slices lo rs) : s.Contains p (s.sample p) := by
  induction rs generalizing lo with
  | nil =>
    simp [slices] at hs
    subst s
    cases lo <;> simp [Slice.Contains,Slice.sample]
  | cons a as ih =>
    rcases List.mem_cons.mp hs with rfl | hs
    · have h := hl a (by simp)
      cases lo <;> simp_all [Slice.Contains,Slice.sample,Lower]; constructor <;> linarith
    rcases List.mem_cons.mp hs with rfl | hs
    · rfl
    · exact ih (List.pairwise_cons.mp ho).2 _ (by simpa [Lower] using (List.pairwise_cons.mp ho).1) hs

omit [Field K] [IsStrictOrderedRing K] in
private theorem compare_lt {a b c d : K} (h : a < b) (h' : c < d) :
    side a b = side c d := by simp [side,h,h']

omit [Field K] [IsStrictOrderedRing K] in
private theorem compare_gt {a b c d : K} (h : b < a) (h' : d < c) :
    side a b = side c d := by simp [side,h.not_gt,h.ne',h'.not_gt,h'.ne']

omit [IsStrictOrderedRing K] in
theorem slice_sign {p q : Point K n} {rs : List (Aff K n)}
    (hp : SortedAt p rs) (hq : SortedAt q rs) (lo)
    {s} (hs : s ∈ slices lo rs) {u v}
    (hu : s.Contains p u) (hv : s.Contains q v) {r} (hr : r ∈ rs) :
    side u (Aff.eval r p) = side v (Aff.eval r q) := by
  induction rs generalizing lo with
  | nil => simp at hr
  | cons a as ih =>
    obtain ⟨hap,hsp⟩ := List.pairwise_cons.mp hp
    obtain ⟨haq,hsq⟩ := List.pairwise_cons.mp hq
    rcases List.mem_cons.mp hs with rfl | hs
    · apply compare_lt
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact hu.2 _ rfl
        · exact lt_trans (hu.2 _ rfl) (hap r hr)
      · rcases List.mem_cons.mp hr with rfl | hr
        · exact hv.2 _ rfl
        · exact lt_trans (hv.2 _ rfl) (haq r hr)
    rcases List.mem_cons.mp hs with rfl | hs
    · change u = _ at hu
      change v = _ at hv
      subst u v
      rcases List.mem_cons.mp hr with rfl | hr
      · simp
      · exact compare_lt (hap _ hr) (haq _ hr)
    rcases List.mem_cons.mp hr with rfl | hr
    · exact compare_gt
        (lower_of_mem (lo := some r) (by simpa [Lower] using hap) hs hu r rfl)
        (lower_of_mem (lo := some r) (by simpa [Lower] using haq) hs hv r rfl)
    · exact ih hsp hsq _ hs hr

end CertifiedTopology
