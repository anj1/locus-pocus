module

public import CertifiedTopology.CADClosure

@[expose] public section

namespace CertifiedTopology.CADDecision

open Set ExecutableIsolation CylindricalData CADStacks ComputableCAD

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def firstCut : {n : ℕ} → Code K (n+1) → Code K 1
  | 0, c => c
  | _+1, .lift b _ _ => firstCut b

def firstPoint : {n : ℕ} → (Fin (n+1) → ℝ) → Fin 1 → ℝ
  | 0, p => p
  | _+1, p => firstPoint (dropLast p)

theorem firstPoint_continuous (n : ℕ) : Continuous (@firstPoint n) := by
  induction n with
  | zero => exact continuous_id
  | succ n ih => exact ih.comp (continuous_pi (fun i => continuous_apply i.castSucc))

theorem first_membership (model : RealModel K) : {n : ℕ} → (c : Code K (n+1)) →
    (x : Fin (n+1) → ℝ) → x ∈ c.carrier model → firstPoint x ∈ (firstCut c).carrier model
  | 0, _, _, h => h
  | _+1, .lift b _ _, x, h => first_membership model b (dropLast x) h.1

theorem first_regular (model : RealModel K) : {n : ℕ} → (c : Code K (n+1)) →
    RegularCode model c → RegularCode model (firstCut c)
  | 0, _, h => h
  | _+1, .lift b _ _, h => first_regular model b h.1

def separatesFirst (a b : Code K 1) : Bool :=
  match a, b with
  | .lift .origin p i, .lift .origin q j => p == q && i % 2 == 1 && j % 2 == 1 && i != j

theorem first_rootCarrier (model : RealModel K) (p : ComputableCAD.Poly K 0) (i : ℕ)
    (v : RegularCode model (.lift .origin p i)) :
    ∃ h : i < (realStack (specialized model p Fin.elim0)).length,
      ∀ x : Fin 1 → ℝ, x ∈ (Code.lift .origin p i).carrier model ↔
        Univariate.contains ((realStack (specialized model p Fin.elim0)).get ⟨i,h⟩) (x 0) := by
  have hi := (v.2 Fin.elim0 (mem_univ _)).2
  refine ⟨hi,fun x => ?_⟩
  have e : dropLast x = Fin.elim0 := Subsingleton.elim _ _
  change (_ ∧ Univariate.contains ((realStack (specialized model p (dropLast x))).getD i _) (x 0)) ↔ _
  rw [e, List.getD_eq_getElem _ _ hi]
  exact and_iff_right (mem_univ _)

theorem first_section_closed (model : RealModel K) (p : ComputableCAD.Poly K 0) (i : ℕ)
    (v : RegularCode model (.lift .origin p i)) (odd : i % 2 = 1) :
    IsClosed ((Code.lift .origin p i).carrier model) := by
  obtain ⟨hi, hh⟩ := first_rootCarrier model p i v
  let res := realStack (specialized model p Fin.elim0)
  have dim : fibreDimension (res.get ⟨i,hi⟩) = 0 := by
    have e : slicesOf none (sortedRoots (specialized model p Fin.elim0)) = res := slicesOf_real _ _
    have bound : i < (slicesOf none (sortedRoots (specialized model p Fin.elim0))).length := e.symm ▸ hi
    have he := List.getElem_of_eq e bound
    have h := fibreDimension_get none (sortedRoots (specialized model p Fin.elim0)) i bound
    have k := congrArg fibreDimension he
    exact k.symm.trans (by simpa [odd] using h)
  cases h : res.get ⟨i,hi⟩ with
  | sector l u => rw [h] at dim; contradiction
  | sectionAt t =>
    have e : (Code.lift .origin p i).carrier model = {x | x 0 = t} := by
      ext x
      exact (hh x).trans (by rw [h]; rfl)
    rw [e]
    exact isClosed_eq (continuous_apply 0) continuous_const

theorem separated_first (model : RealModel K) (a b : Code K 1)
    (ha : RegularCode model a) (hb : RegularCode model b) (h : separatesFirst a b = true) :
    Disjoint (closure (a.carrier model)) (closure (b.carrier model)) := by
  cases a with
  | lift a p i =>
    cases a
    cases b with
    | lift b q j =>
      cases b
      simp only [separatesFirst, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
      obtain ⟨⟨⟨rfl,hi⟩,hj⟩,hd⟩ := h
      rw [(first_section_closed model p i ha hi).closure_eq, (first_section_closed model p j hb hj).closure_eq]
      refine disjoint_left.mpr fun x hx hy => ?_
      obtain ⟨ki,hi⟩ := first_rootCarrier model p i ha
      obtain ⟨kj,hj⟩ := first_rootCarrier model p j hb
      obtain ⟨_,_,unique⟩ := stack_partition (specialized model p Fin.elim0) (x 0)
      have eq := (unique _ ⟨List.get_mem _ _, (hi x).mp hx⟩).trans
        (unique _ ⟨List.get_mem _ _, (hj x).mp hy⟩).symm
      exact hd (congrArg Fin.val ((realStack_nodup _).injective_get eq))

theorem separated_closures (model : RealModel K) {n : ℕ} (a b : Code K (n+1))
    (ha : RegularCode model a) (hb : RegularCode model b)
    (h : separatesFirst (firstCut a) (firstCut b) = true) :
    ¬(closure (a.carrier model) ∩ closure (b.carrier model)).Nonempty := by
  rintro ⟨x,hx,hy⟩
  have mem (c : Code K (n+1)) (h : x ∈ closure (c.carrier model)) :
      firstPoint x ∈ closure ((firstCut c).carrier model) := by
    apply closure_mono (s := firstPoint '' c.carrier model)
    · rintro _ ⟨y,hy,rfl⟩
      exact first_membership model c y hy
    · exact image_closure_subset_closure_image (firstPoint_continuous n) ⟨x,h,rfl⟩
  exact (disjoint_left.mp (separated_first model _ _ (first_regular model a ha)
    (first_regular model b hb) h)) (mem a hx) (mem b hy)

/-- Distinct root sections of the first projection give a cheap disjointness test. -/
def closuresOverlap (model : RealModel K) : {n : ℕ} → Code K n → Code K n → Bool
  | 0, a, b => closuresMeet model a b
  | _+1, a, b =>
    if separatesFirst (firstCut a) (firstCut b) then false else closuresMeet model a b

theorem closuresOverlap_correct (model : RealModel K) {n : ℕ} (a b : Code K n)
    (ha : RegularCode model a) (hb : RegularCode model b) :
    closuresOverlap model a b = true ↔ (closure (a.carrier model) ∩ closure (b.carrier model)).Nonempty := by
  cases n with
  | zero => exact closuresMeet_correct model a b ha hb
  | succ n =>
    change (if separatesFirst (firstCut a) (firstCut b) then false else closuresMeet model a b) = true ↔ _
    by_cases h : separatesFirst (firstCut a) (firstCut b) = true
    · rw [ite_eq_left h]
      exact iff_of_false Bool.false_ne_true (separated_closures model a b ha hb h)
    · rw [ite_eq_right h]
      exact closuresMeet_correct model a b ha hb

end CertifiedTopology.CADDecision
