module

public import CertifiedTopology.IndependentFibers
public import Mathlib.Data.List.MinMax

@[expose] public section

namespace CertifiedTopology.CADDecision

open Set ExecutableIsolation CylindricalData CADStacks AlgebraicRoot

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {model : RealModel K} {n : ℕ}

def SignFormula.atSample (p : ExactPoint model n) : SignFormula K n → Bool
  | .truth b => b
  | .atom f s => side (Multi.evalHom p.coefficients p.point f) 0 == s
  | .not f => !(atSample p f)
  | .and f g => atSample p f && atSample p g
  | .or f g => atSample p f || atSample p g

theorem SignFormula.atSample_correct (p : ExactPoint model n) (f : SignFormula K n) :
    f.atSample p = true ↔ f.holds model p.value := by
  induction f with
  | truth b => rfl
  | atom f s =>
    simp only [atSample,holds,beq_iff_eq]
    rw [AlgebraicRoot.map_side p.model.hom p.model.strictMono, p.value_eval]
  | not f ih => simp [atSample, holds, ← ih]
  | and f g ih jh => simp [atSample,holds,ih,jh]
  | or f g ih jh => simp [atSample,holds,ih,jh]

def compareLe (model : RealModel K) (a b : Root model) : Bool :=
  let sample := (ExactPoint.origin model).extend (rootSample model a).val
  !((isolatedCut model b .above).atSample sample)

theorem compareLe_correct (model : RealModel K) (a b : Root model) :
    compareLe model a b = true ↔ a.value ≤ b.value := by
  unfold compareLe
  let p := (ExactPoint.origin model).extend (rootSample model a).val
  change (!((isolatedCut model b .above).atSample p)) = true ↔ _
  have hx : p.value 0 = a.value := by
    have e := ExactPoint.value_extend (ExactPoint.origin model) (rootSample model a).val
    exact (congrFun e (Fin.last 0)).trans ((@Fin.snoc_last 0 (fun _ => ℝ) _ _).trans
      (rootSample model a).property)
  rw [Bool.not_eq_true', ← Bool.not_eq_true, SignFormula.atSample_correct, isolatedCut_correct,
    side_above, hx, sub_pos, not_lt]

def low {A : Type} : Slice A → Option A
  | .sectionAt r => some r
  | .sector l _ => l

def high {A : Type} : Slice A → Option A
  | .sectionAt r => some r
  | .sector _ u => u

def closedInterval (s : Slice ℝ) : Set ℝ :=
  {t | (∀ l ∈ low s, l ≤ t) ∧ (∀ u ∈ high s, t ≤ u)}

theorem closedInterval_eq (s : Slice ℝ) (hne : ∃ x, Univariate.contains s x) :
    closure {x | Univariate.contains s x} = closedInterval s := by
  cases s with
  | sectionAt r =>
    have e : {x | Univariate.contains (.sectionAt r) x} = {r} := rfl
    rw [e,closure_singleton]
    ext t
    simp only [mem_singleton_iff,closedInterval,mem_ofPred_eq,low,high,Option.mem_some,
      forall_eq']
    exact ⟨fun h => h ▸ ⟨le_rfl,le_rfl⟩,fun h => le_antisymm h.2 h.1⟩
  | sector l u =>
    cases l <;> cases u
    · simp [Univariate.contains,Slice.Contains,closedInterval,low,high]
    · rename_i u
      have e : {x | Univariate.contains (.sector none (some u)) x} = Iio u := by
        ext t; simp [Univariate.contains,Slice.Contains,Aff.eval]
      rw [e,closure_Iio]
      ext t
      simp [closedInterval,low,high]
    · rename_i l
      have e : {x | Univariate.contains (.sector (some l) none) x} = Ioi l := by
        ext t; simp [Univariate.contains,Slice.Contains,Aff.eval]
      rw [e,closure_Ioi]
      ext t
      simp [closedInterval,low,high]
    · rename_i l u
      have e : {x | Univariate.contains (.sector (some l) (some u)) x} = Ioo l u := by
        ext t; simp [Univariate.contains,Slice.Contains,Aff.eval]
      obtain ⟨x,hx⟩ := hne
      have xx : x ∈ Ioo l u := e ▸ hx
      rw [e,closure_Ioo (xx.1.trans xx.2).ne]
      ext t
      simp [closedInterval,low,high]

def checkBounds (model : RealModel K) : Option (Root model) → Option (Root model) → Bool
  | some a, some b => compareLe model a b
  | _, _ => true

theorem checkBounds_correct (model : RealModel K) (l u : Option (Root model)) :
    checkBounds model l u = true ↔ ∀ a ∈ l.map Root.value, ∀ b ∈ u.map Root.value, a ≤ b := by
  cases l <;> cases u <;> simp [checkBounds, compareLe_correct]

def intervalMeet (model : RealModel K) (a b : Slice (Root model)) : Bool :=
  checkBounds model (low a) (high b) && checkBounds model (low b) (high a)

theorem bounds_exist (ls us : List ℝ) :
    (∃ t : ℝ, (∀ l ∈ ls, l ≤ t) ∧ (∀ u ∈ us, t ≤ u)) ↔ ∀ l ∈ ls, ∀ u ∈ us, l ≤ u := by
  constructor
  · rintro ⟨t,hl,hu⟩ l hm u hn
    exact (hl l hm).trans (hu u hn)
  · intro h
    by_cases e : 0 < ls.length
    · exact ⟨ls.maximum_of_length_pos e, fun l hl => List.le_maximum_of_length_pos_of_mem hl e,
        fun u hu => h _ (List.maximum_of_length_pos_mem e) _ hu⟩
    · by_cases f : 0 < (us.map Neg.neg).length
      · refine ⟨-((us.map Neg.neg).maximum_of_length_pos f), ?_, fun u hu => ?_⟩
        · simp [List.eq_nil_of_length_eq_zero (by omega : ls.length = 0)]
        · have hn := List.le_maximum_of_length_pos_of_mem
            (List.mem_map_of_mem (f := Neg.neg) hu) f
          linarith
      · have hl : ls = [] := List.eq_nil_of_length_eq_zero (by omega)
        have hu : us = [] := List.eq_nil_of_length_eq_zero (by simpa using Nat.eq_zero_of_not_pos f)
        exact ⟨0,by simp [hl,hu]⟩

theorem intervalMeet_correct (model : RealModel K) (a b : Slice (Root model))
    (ha : ∃ x, Univariate.contains (mapSlice Root.value a) x)
    (hb : ∃ x, Univariate.contains (mapSlice Root.value b) x) :
    intervalMeet model a b = true ↔
      (closure {x | Univariate.contains (mapSlice Root.value a) x} ∩
        closure {x | Univariate.contains (mapSlice Root.value b) x}).Nonempty := by
  let A := mapSlice Root.value a
  let B := mapSlice Root.value b
  have lo (s : Slice (Root model)) : low (mapSlice Root.value s) = (low s).map Root.value := by cases s <;> rfl
  have hi (s : Slice (Root model)) : high (mapSlice Root.value s) = (high s).map Root.value := by cases s <;> rfl
  rw [intervalMeet,Bool.and_eq_true,checkBounds_correct,checkBounds_correct,← lo,← hi,← lo,← hi,
    closedInterval_eq _ ha,closedInterval_eq _ hb]
  change _ ↔ (closedInterval A ∩ closedInterval B).Nonempty
  have internal (s : Slice (Root model)) (hs : ∃ x, Univariate.contains (mapSlice Root.value s) x) :
      ∀ l ∈ low (mapSlice Root.value s), ∀ u ∈ high (mapSlice Root.value s), l ≤ u := by
    have eq := closedInterval_eq _ hs
    obtain ⟨x,hx⟩ := hs
    have h : x ∈ closedInterval (mapSlice Root.value s) :=
      eq ▸ subset_closure hx
    exact fun l hl u hu => (h.1 l hl).trans (h.2 u hu)
  have h := bounds_exist ((low A).toList ++ (low B).toList) ((high A).toList ++ (high B).toList)
  simp only [List.forall_mem_append,Option.mem_toList] at h
  rw [Set.nonempty_def]
  simp only [mem_inter_iff,closedInterval,mem_ofPred_eq]
  constructor
  · rintro ⟨hab,hba⟩
    obtain ⟨x, hx, hy⟩ := h.mpr ⟨fun l hl => ⟨internal a ha l hl,hab l hl⟩,
      fun l hl => ⟨hba l hl,internal b hb l hl⟩⟩
    exact ⟨x,⟨hx.1,hy.1⟩,⟨hx.2,hy.2⟩⟩
  · rintro ⟨x,hx,hy⟩
    exact ⟨fun l hl u hu => (hx.1 l hl).trans (hy.2 u hu),
      fun l hl u hu => (hy.1 l hl).trans (hx.2 u hu)⟩

inductive Box (model : RealModel K) : ℕ → Type
  | origin : Box model 0
  | lift {n : ℕ} (base : Box model n) (height : Slice (Root model)) : Box model (n+1)

namespace Box

noncomputable def carrier (model : RealModel K) : {n : ℕ} → Box model n → Set (Fin n → ℝ)
  | 0, .origin => univ
  | n+1, .lift b s => {x | dropLast x ∈ carrier model b ∧ Univariate.contains (mapSlice Root.value s) (last x)}

def fromCode (model : RealModel K) : {n : ℕ} → Code K n → Option (Box model n)
  | 0, .origin => some .origin
  | n+1, .lift b p i =>
    match fromCode model b, fixedSource p with
    | some a, some q => some (.lift a (fixedRow model q i))
    | _, _ => none

theorem fromCode_correct (model : RealModel K) : {n : ℕ} → (c : Code K n) →
    (h : ComputableCAD.RegularCode model c) → (b : Box model n) → fromCode model c = some b →
    carrier model b = c.carrier model
  | 0, .origin, _, b, _ => by cases b; rfl
  | n+1, .lift c p i, h, b, eq => by
    cases hc : fromCode model c with
    | none => simp [fromCode,hc] at eq
    | some a =>
      cases hf : fixedSource p with
      | none => simp [fromCode,hc,hf] at eq
      | some q =>
        have e : b = .lift a (fixedRow model q i) := (Option.some.inj
          (by simpa only [fromCode,hc,hf] using eq)).symm
        subst b
        ext x
        change (dropLast x ∈ carrier model a ∧ _) ↔ (dropLast x ∈ c.carrier model ∧ _)
        rw [fromCode_correct model c h.1 a hc]
        refine and_congr_right fun hx => ?_
        exact Iff.of_eq (congrArg (fun s => Univariate.contains s (last x))
          (fixedRow_correct model p (dropLast x) (h.2 _ hx).1 hf i))

theorem closure_lift (model : RealModel K) {b : Box model n} {s : Slice (Root model)}
    (x : Fin (n+1) → ℝ) :
    x ∈ closure (carrier model (.lift b s)) ↔
      dropLast x ∈ closure (carrier model b) ∧
        last x ∈ closure {t | Univariate.contains (mapSlice Root.value s) t} := by
  let F := splitCoordinates n
  let T := {t | Univariate.contains (mapSlice Root.value s) t}
  change x ∈ closure (F ⁻¹' (carrier model b ×ˢ T)) ↔ _
  rw [← Homeomorph.preimage_closure,closure_prod_eq]
  rfl

def meets (model : RealModel K) : {n : ℕ} → Box model n → Box model n → Bool
  | 0, _, _ => true
  | n+1, .lift a t, .lift b s => meets model a b && intervalMeet model t s

theorem meets_correct (model : RealModel K) : {n : ℕ} → (a b : Box model n) →
    (ha : (carrier model a).Nonempty) → (hb : (carrier model b).Nonempty) →
    meets model a b = true ↔ (closure (carrier model a) ∩ closure (carrier model b)).Nonempty
  | 0, .origin, .origin, _, _ => by
    exact ⟨fun _ => ⟨Fin.elim0,subset_closure (mem_univ _),subset_closure (mem_univ _)⟩,fun _ => rfl⟩
  | n+1, .lift a t, .lift b s, ⟨x,hx⟩, ⟨y,hy⟩ => by
    rw [meets,Bool.and_eq_true,meets_correct model a b ⟨dropLast x,hx.1⟩ ⟨dropLast y,hy.1⟩,
      intervalMeet_correct model t s ⟨last x,hx.2⟩ ⟨last y,hy.2⟩]
    constructor
    · rintro ⟨⟨p,hp,hq⟩,⟨r,hr,hs⟩⟩
      have e : dropLast (Fin.snoc p r) = p := by ext j; simp
      have e' : last (Fin.snoc p r) = r := @Fin.snoc_last n (fun _ => ℝ) r p
      refine ⟨Fin.snoc p r,(closure_lift model _).mpr ?_, (closure_lift model _).mpr ?_⟩
      · rw [e,e']
        exact ⟨hp,hr⟩
      · rw [e,e']
        exact ⟨hq,hs⟩
    · rintro ⟨p,hp,hq⟩
      have ep := (closure_lift model p).mp hp
      have eq := (closure_lift model p).mp hq
      exact ⟨⟨dropLast p,ep.1,eq.1⟩,⟨last p,ep.2,eq.2⟩⟩

end Box

def fastOverlap (model : RealModel K) (a b : Code K n) : Bool :=
  match Box.fromCode model a, Box.fromCode model b with
  | some p, some q => Box.meets model p q
  | _, _ => closuresOverlap model a b

theorem fastOverlap_correct (model : RealModel K) (a b : Code K n)
    (ha : ComputableCAD.RegularCode model a) (hb : ComputableCAD.RegularCode model b)
    (hna : (a.carrier model).Nonempty) (hnb : (b.carrier model).Nonempty) :
    fastOverlap model a b = true ↔ (closure (a.carrier model) ∩ closure (b.carrier model)).Nonempty := by
  unfold fastOverlap
  cases e : Box.fromCode model a <;> cases f : Box.fromCode model b
  all_goals try exact closuresOverlap_correct model a b ha hb
  rename_i p q
  have ea := Box.fromCode_correct model a ha p e
  have eb := Box.fromCode_correct model b hb q f
  exact (Box.meets_correct model p q (ea.symm ▸ hna) (eb.symm ▸ hnb)).trans (by rw [ea,eb])

end CertifiedTopology.CADDecision
