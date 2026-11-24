module

public import CertifiedTopology.ClosedDescriptions

@[expose] public section

namespace CertifiedTopology.CADDecision

open Set ExecutableIsolation CylindricalData

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ} {model : RealModel K}

/-- Nonempty, locally closed pieces with local Euclidean models and
    exact semialgebraic descriptions. -/
structure Stratum (model : RealModel K) (n : ℕ) where
  description : Prenex K n
  dimension : ℕ
  sample : ExactPoint model n
  sample_mem : sample.value ∈ description.carrier model
  locallyClosed : IsLocallyClosed (description.carrier model)
  modelSpace : ∃ u : Set (Fin dimension → ℝ), IsOpen u ∧ Nonempty (description.carrier model ≃ₜ u)

abbrev Stratum.carrier (s : Stratum model n) := s.description.carrier model

theorem Stratum.nonempty (s : Stratum model n) : s.carrier.Nonempty := ⟨s.sample.value, s.sample_mem⟩

def Stratum.ofCell (c : ComputableCAD.Cell model n) : Stratum model n :=
  ⟨describeCell c,c.code.dimension,c.sample,by
    rw [describeCell_correct]
    exact c.sample_mem,by
    rw [describeCell_correct]
    exact c.locallyClosed,by
    rw [describeCell_correct]
    exact ⟨univ,isOpen_univ,⟨c.euclidean.some.trans (Homeomorph.Set.univ _).symm⟩⟩⟩

theorem Stratum.ofCell_carrier (c : ComputableCAD.Cell model n) :
    (Stratum.ofCell c).carrier = c.carrier := describeCell_correct c

theorem Stratum.singleton_of_zero (s : Stratum model n) (h : s.dimension = 0) :
    s.carrier = {s.sample.value} := by
  obtain ⟨U,_,⟨F⟩⟩ := s.modelSpace
  have : Subsingleton (Fin s.dimension → ℝ) := by
    rw [h]
    infer_instance
  ext y
  constructor
  · intro hy
    exact congrArg Subtype.val
      (F.injective (Subsingleton.elim (F ⟨y,hy⟩) (F ⟨s.sample.value,s.sample_mem⟩)))
  · rintro rfl
    exact s.sample_mem

theorem Stratum.closed_of_zero (s : Stratum model n) (h : s.dimension = 0) : IsClosed s.carrier := by
  rw [s.singleton_of_zero h]
  exact isClosed_singleton

theorem remove_closed_model (c : ComputableCAD.Cell model n) {Z : Set (Fin n → ℝ)}
    (hZ : IsClosed Z) :
    ∃ u : Set (Fin c.code.dimension → ℝ), IsOpen u ∧ Nonempty (↥(c.carrier \ Z) ≃ₜ ↥u) := by
  let H := c.euclidean.some
  let U : Set c.carrier := {x | x.val ∉ Z}
  have op : IsOpen U := hZ.isOpen_compl.preimage continuous_subtype_val
  let P : ↥(c.carrier \ Z) ≃ₜ ↥U :=
    { toFun := fun x => ⟨⟨x.val,x.property.1⟩,x.property.2⟩
      invFun := fun x => ⟨x.val.val,x.val.property,x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
      continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
  exact ⟨H '' U,H.isOpenMap _ op,⟨P.trans (H.image U)⟩⟩

def firstSample (model : RealModel K) (f : Prenex K n) :
    Option {p : ExactPoint model n // p.value ∈ f.carrier model} :=
  match h : (f.regions model).head? with
  | none => none
  | some c =>
    some ⟨c.sample, (f.regions_correct model _).mpr ⟨c, List.mem_of_head? h, c.sample_mem⟩⟩

private theorem firstSample_exists (model : RealModel K) (f : Prenex K n) {x : Fin n → ℝ}
    (hx : x ∈ f.carrier model) : (firstSample model f).isSome = true := by
  obtain ⟨c,hc,_⟩ := (f.regions_correct model x).mp hx
  unfold firstSample
  split
  · rename_i h
    rw [List.head?_eq_none_iff.mp h] at hc
    cases hc
  · rfl

def preferredSample (model : RealModel K) (f : Prenex K n) (p : ExactPoint model n) :
    Option {p : ExactPoint model n // p.value ∈ f.carrier model} :=
  match f with
  | .matrix a =>
    if h : a.atSample p = true then some ⟨p,(a.atSample_correct p).mp h⟩
    else firstSample model (.matrix a)
  | .exists_ a => firstSample model (.exists_ a)
  | .forall_ a => firstSample model (.forall_ a)

private theorem preferredSample_exists (model : RealModel K) (f : Prenex K n) (p : ExactPoint model n)
    {x : Fin n → ℝ} (hx : x ∈ f.carrier model) : (preferredSample model f p).isSome = true := by
  cases f with
  | matrix a =>
    simp only [preferredSample]
    split
    · rfl
    · exact firstSample_exists model (.matrix a) hx
  | exists_ a => exact firstSample_exists model (.exists_ a) hx
  | forall_ a => exact firstSample_exists model (.forall_ a) hx

def makeStratum (c : ComputableCAD.Cell model n) (wall : Prenex K n)
    (closed : IsClosed (wall.carrier model)) : Option (Stratum model n) := by
  let desc := (describeCell c).subtract wall
  refine match preferredSample model desc c.sample with
  | none => none
  | some p =>
    some ⟨desc,c.code.dimension,p.val,p.property,?_,?_⟩
  · change IsLocallyClosed (((describeCell c).subtract wall).carrier model)
    rw [Prenex.carrier_subtract,describeCell_correct]
    exact c.locallyClosed.inter closed.isOpen_compl.isLocallyClosed
  · change ∃ u : Set (Fin c.code.dimension → ℝ), IsOpen u ∧
      Nonempty ((((describeCell c).subtract wall).carrier model) ≃ₜ u)
    rw [Prenex.carrier_subtract,describeCell_correct]
    exact remove_closed_model c closed

theorem makeStratum_spec (c : ComputableCAD.Cell model n) (wall : Prenex K n)
    (closed : IsClosed (wall.carrier model)) (s : Stratum model n)
    (h : makeStratum c wall closed = some s) : s.carrier = c.carrier \ wall.carrier model := by
  unfold makeStratum at h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    exact (Prenex.carrier_subtract _ _ _).trans (congrArg (· \ wall.carrier model) (describeCell_correct c))

theorem makeStratum_exists (c : ComputableCAD.Cell model n) (wall : Prenex K n)
    (closed : IsClosed (wall.carrier model)) {x : Fin n → ℝ}
    (h : x ∈ c.carrier \ wall.carrier model) :
    ∃ s, makeStratum c wall closed = some s ∧ x ∈ s.carrier := by
  unfold makeStratum
  dsimp only
  split
  · rename_i bad
    let d := (describeCell c).subtract wall
    have hx : x ∈ d.carrier model := by
      dsimp only [d]
      rw [Prenex.carrier_subtract,describeCell_correct]
      exact h
    have hs := preferredSample_exists model d c.sample hx
    rw [show preferredSample model d c.sample = none from bad] at hs
    cases hs
  · refine ⟨_,rfl,?_⟩
    change x ∈ ((describeCell c).subtract wall).carrier model
    rw [Prenex.carrier_subtract,describeCell_correct]
    exact h

/-- Every top piece avoids the residual's closure, and distinct top
    pieces are disjoint even from each other's closures. -/
structure Layer (model : RealModel K) (d : ℕ) (f : Prenex K n) (compatible : List (Prenex K n)) where
  lower : Prenex K n
  upper : List (Stratum model n)
  nodup : upper.Nodup
  thin : ThinAt d (lower.carrier model)
  partition : ∀ x, x ∈ f.carrier model ↔ x ∈ lower.carrier model ∨ ∃ s ∈ upper, x ∈ s.carrier
  avoidsLowerClosure : ∀ s ∈ upper, Disjoint s.carrier (closure (lower.carrier model))
  upperFrontier : ∀ a ∈ upper, ∀ b ∈ upper, a ≠ b → Disjoint b.carrier (closure a.carrier)
  compatible_upper : ∀ s ∈ upper, ∀ g ∈ compatible,
    s.carrier ⊆ g.carrier model ∨ Disjoint s.carrier (g.carrier model)

def cutLayer (model : RealModel K) (d : ℕ) (f : Prenex K n) (constraints : List (Prenex K n))
    (thin : ThinAt (d+1) (f.carrier model)) :
    Layer model d f constraints := by
  let cs := classify model f constraints
  let boundary (c : ComputableCAD.Cell model n) := (describeCellClosure c).subtract (describeCell c)
  let walls := cs.cells.map boundary
  let wall := Prenex.union walls
  have wall_eq : wall.carrier model =
      ⋃ i : Fin cs.cells.length, closure (cs.cells.get i).carrier \ (cs.cells.get i).carrier := by
    ext x
    simp only [wall,Prenex.carrier_union,mem_iUnion,exists_prop,walls,List.mem_map]
    constructor
    · rintro ⟨a,⟨c,hc,rfl⟩,hx⟩
      obtain ⟨i,rfl⟩ := List.get_of_mem hc
      rw [Prenex.carrier_subtract,describeCellClosure_correct,describeCell_correct] at hx
      exact ⟨i,hx⟩
    · rintro ⟨i,hx⟩
      refine ⟨boundary (cs.cells.get i),⟨cs.cells.get i,List.get_mem _ _,rfl⟩,?_⟩
      rw [Prenex.carrier_subtract,describeCellClosure_correct,describeCell_correct]
      exact hx
  have wallClosed : IsClosed (wall.carrier model) := by
    rw [wall_eq]
    apply isClosed_iUnion_of_finite
    intro i
    have h : IsOpen ((closure (cs.cells.get i).carrier \ (cs.cells.get i).carrier)ᶜ) :=
      (cs.cells.get i).locallyClosed.isOpen_coborder
    simpa only [compl_compl] using h.isClosed_compl
  let lower := f.both wall
  let upper := cs.cells.filterMap fun c => makeStratum c wall wallClosed
  have rule (s : Stratum model n) (hs : s ∈ upper) :
      ∃ c ∈ cs.cells, makeStratum c wall wallClosed = some s ∧ s.carrier = c.carrier \ wall.carrier model := by
    obtain ⟨c,hc,h⟩ := List.mem_filterMap.mp hs
    exact ⟨c,hc,h,makeStratum_spec c wall wallClosed s h⟩
  have wall_thin : ThinAt d (wall.carrier model) := by
    rw [wall_eq]
    apply ThinAt.iUnion
    intro i
    let c := cs.cells.get i
    have ht : ThinAt (d+1) ((describeCell c).carrier model) := by
      rw [describeCell_correct]
      exact thin.mono (cs.contained c (List.get_mem _ _))
    have h := boundary_thin model d (describeCell c) ht
    change ThinAt d (closure ((describeCell c).carrier model) \
      (describeCell c).carrier model) at h
    rwa [describeCell_correct] at h
  refine ⟨lower,upper,?_,?_,?_,?_,?_,?_⟩
  · apply nodup_filterMap _ _ cs.nodup
    intro a ha b hb s ea eb
    obtain ⟨x,hx⟩ := s.nonempty
    change x ∈ s.carrier at hx
    have h₁ : x ∈ a.carrier \ wall.carrier model := by
      rw [← makeStratum_spec a wall wallClosed s ea]
      exact hx
    have h₂ : x ∈ b.carrier \ wall.carrier model := by
      rw [← makeStratum_spec b wall wallClosed s eb]
      exact hx
    have inF := cs.contained a ha h₁.1
    obtain ⟨_,_,u⟩ := (cs.cover x).mp inF
    exact (u _ ⟨ha,h₁.1⟩).trans (u _ ⟨hb,h₂.1⟩).symm
  · rw [Prenex.carrier_both]
    exact wall_thin.mono inter_subset_right
  · intro x
    rw [Prenex.carrier_both]
    constructor
    · intro hx
      by_cases hw : x ∈ wall.carrier model
      · exact Or.inl ⟨hx,hw⟩
      · obtain ⟨c,hc,hxc⟩ := ((cs.cover x).mp hx).exists
        obtain ⟨s,hs,hxs⟩ := makeStratum_exists c wall wallClosed ⟨hxc,hw⟩
        exact Or.inr ⟨s,List.mem_filterMap.mpr ⟨c,hc,hs⟩,hxs⟩
    · rintro (hl | ⟨s,hs,hx⟩)
      · exact hl.1
      · obtain ⟨c,hc,_,eq⟩ := rule s hs
        rw [eq] at hx
        exact cs.contained c hc hx.1
  · intro s hs
    obtain ⟨c,_,_,eq⟩ := rule s hs
    rw [eq,Prenex.carrier_both]
    exact disjoint_left.mpr fun x hx hy => hx.2 (closure_minimal inter_subset_right wallClosed hy)
  · intro a ha b hb different
    obtain ⟨c,hc,hc',eqc⟩ := rule a ha
    obtain ⟨s,hs,hs',eqs⟩ := rule b hb
    have distinct : c ≠ s := by
      rintro rfl
      exact different (Option.some.inj (hc'.symm.trans hs'))
    refine disjoint_left.mpr fun x hx hy => ?_
    rw [eqs] at hx
    have sub : a.carrier ⊆ c.carrier := by rw [eqc]; exact sdiff_subset
    have hxc : x ∈ closure c.carrier := closure_mono sub hy
    have away : x ∉ c.carrier := by
      intro hm
      have input := cs.contained s hs hx.1
      obtain ⟨t,_,unique⟩ := (cs.cover x).mp input
      exact distinct ((unique _ ⟨hc,hm⟩).trans (unique _ ⟨hs,hx.1⟩).symm)
    obtain ⟨i,rfl⟩ := List.get_of_mem hc
    apply hx.2
    rw [wall_eq]
    exact mem_iUnion.mpr ⟨i,hxc,away⟩
  · intro s hs g hg
    obtain ⟨c,hc,_,eq⟩ := rule s hs
    have sub : s.carrier ⊆ c.carrier := by rw [eq]; exact sdiff_subset
    exact (cs.compatible c hc g hg).imp (fun h => sub.trans h)
      (fun h => h.mono_left sub)

structure Stratification (model : RealModel K) (f : Prenex K n) (constraints : List (Prenex K n)) where
  strata : List (Stratum model n)
  nodup : strata.Nodup
  cover : ∀ x, x ∈ f.carrier model ↔ ∃ s ∈ strata, x ∈ s.carrier
  disjoint_strata : ∀ a ∈ strata, ∀ b ∈ strata, a ≠ b → Disjoint a.carrier b.carrier
  frontier : ∀ a ∈ strata, ∀ b ∈ strata, b.carrier ⊆ closure a.carrier ∨ Disjoint b.carrier (closure a.carrier)
  compatible : ∀ a ∈ strata, ∀ g ∈ constraints, a.carrier ⊆ g.carrier model ∨ Disjoint a.carrier (g.carrier model)

def assemble {d : ℕ} {f : Prenex K n} {constraints : List (Prenex K n)}
    (layer : Layer model d f constraints)
    (rest : Stratification model layer.lower
      (constraints ++ layer.upper.map (fun s => describeClosure model s.description))) :
    Stratification model f constraints := by
  have below (a : Stratum model n) (ha : a ∈ rest.strata) : a.carrier ⊆ layer.lower.carrier model :=
    fun x hx => (rest.cover x).mpr ⟨a,ha,hx⟩
  have frontier (a : Stratum model n) (ha : a ∈ layer.upper ++ rest.strata)
      (b : Stratum model n) (hb : b ∈ layer.upper ++ rest.strata) :
      b.carrier ⊆ closure a.carrier ∨ Disjoint b.carrier (closure a.carrier) := by
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · by_cases h : a = b
      · subst b
        exact Or.inl subset_closure
      · exact Or.inr (layer.upperFrontier a ha b hb h)
    · have h := rest.compatible b hb (describeClosure model a.description)
        (List.mem_append_right _ (List.mem_map_of_mem ha))
      rwa [describeClosure_correct] at h
    · exact Or.inr ((layer.avoidsLowerClosure b hb).mono_right (closure_mono (below a ha)))
    · exact rest.frontier a ha b hb
  refine ⟨layer.upper ++ rest.strata,?_,?_,?_,frontier,?_⟩
  · rw [List.nodup_append']
    exact ⟨layer.nodup,rest.nodup,fun {a} ha hb => by
      obtain ⟨x,hx⟩ := a.nonempty
      exact disjoint_left.mp (layer.avoidsLowerClosure a ha) hx (subset_closure (below a hb hx))⟩
  · intro x
    rw [layer.partition,rest.cover]
    simp only [List.mem_append]
    exact ⟨fun h => h.elim (fun ⟨a,ha,hx⟩ => ⟨a,Or.inr ha,hx⟩)
      (fun ⟨a,ha,hx⟩ => ⟨a,Or.inl ha,hx⟩),
      fun ⟨a,ha,hx⟩ => ha.elim (fun hr => Or.inr ⟨a,hr,hx⟩) (fun hr => Or.inl ⟨a,hr,hx⟩)⟩
  · intro a ha b hb hne
    rcases List.mem_append.mp ha with ha | ha <;> rcases List.mem_append.mp hb with hb | hb
    · exact ((layer.upperFrontier a ha b hb hne).mono_right subset_closure).symm
    · exact (layer.avoidsLowerClosure a ha).mono_right ((below b hb).trans subset_closure)
    · exact ((layer.avoidsLowerClosure b hb).mono_right ((below a ha).trans subset_closure)).symm
    · exact rest.disjoint_strata a ha b hb hne
  · intro a ha g hg
    rcases List.mem_append.mp ha with ha | ha
    · exact layer.compatible_upper a ha g hg
    · exact rest.compatible a ha g (List.mem_append_left _ hg)

def emptyStratification (f : Prenex K n) (constraints : List (Prenex K n))
    (empty : f.carrier model = ∅) : Stratification model f constraints :=
  ⟨[],by simp,fun x => by simp [empty],by simp,by simp,by simp⟩

def stratifyCell (f : Prenex K n) (c : ComputableCAD.Cell model n)
    (eq : f.carrier model = c.carrier) : Stratification model f [] where
  strata := [Stratum.ofCell c]
  nodup := by simp
  cover x := by simp [eq, Stratum.ofCell_carrier]
  disjoint_strata a ha b hb ne := by
    simp only [List.mem_singleton] at ha hb
    exact (ne (ha.trans hb.symm)).elim
  frontier a ha b hb := by
    simp only [List.mem_singleton] at ha hb
    subst a b
    exact Or.inl subset_closure
  compatible := by simp

def stratifyPoints (f : Prenex K n) (constraints : List (Prenex K n))
    (cells : List (ComputableCAD.Cell model n)) (nodup : cells.Nodup)
    (partition : ∀ x, x ∈ f.carrier model ↔ ∃! c, c ∈ cells ∧ x ∈ c.carrier)
    (contained : ∀ c ∈ cells, c.carrier ⊆ f.carrier model)
    (allZero : ∀ c ∈ cells, c.code.dimension = 0) : Stratification model f constraints := by
  have unique (a b : ComputableCAD.Cell model n) (ha : a ∈ cells) (hb : b ∈ cells) {x : Fin n → ℝ}
      (hx : x ∈ a.carrier) (hy : x ∈ b.carrier) : a = b := by
    obtain ⟨_,_,u⟩ := (partition x).mp (contained a ha hx)
    exact (u _ ⟨ha,hx⟩).trans (u _ ⟨hb,hy⟩).symm
  have noOverlap (a : Stratum model n) (ha : a ∈ cells.map Stratum.ofCell)
      (b : Stratum model n) (hb : b ∈ cells.map Stratum.ofCell) (different : a ≠ b) :
      Disjoint a.carrier b.carrier := by
    obtain ⟨ca,hca,rfl⟩ := List.mem_map.mp ha
    obtain ⟨cb,hcb,rfl⟩ := List.mem_map.mp hb
    rw [Stratum.ofCell_carrier,Stratum.ofCell_carrier]
    exact disjoint_left.mpr fun x hx hy => different (congrArg Stratum.ofCell (unique ca cb hca hcb hx hy))
  refine ⟨cells.map Stratum.ofCell,?_,?_,noOverlap,?_,?_⟩
  · apply nodup.map_on
    intro a ha b hb he
    have h := congrArg Stratum.carrier he
    simp only [Stratum.ofCell_carrier] at h
    exact unique a b ha hb a.sample_mem (h ▸ a.sample_mem)
  · intro x
    constructor
    · intro h
      obtain ⟨c,hc,hx⟩ := ((partition x).mp h).exists
      exact ⟨Stratum.ofCell c,List.mem_map_of_mem hc,(Stratum.ofCell_carrier c).symm ▸ hx⟩
    · rintro ⟨a,ha,hx⟩
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
      rw [Stratum.ofCell_carrier] at hx
      exact contained c hc hx
  · intro a ha b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    rw [(Stratum.ofCell c).closed_of_zero (allZero c hc) |>.closure_eq]
    by_cases he : Stratum.ofCell c = b
    · exact Or.inl (he ▸ Subset.rfl)
    · exact Or.inr (noOverlap _ (List.mem_map_of_mem hc) _ hb he).symm
  · intro a ha g _
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp ha
    rw [(Stratum.ofCell c).singleton_of_zero (allZero c hc)]
    by_cases h : c.sample.value ∈ g.carrier model
    · exact Or.inl (singleton_subset_iff.mpr h)
    · exact Or.inr (disjoint_singleton_left.mpr h)

def pointStratification? (model : RealModel K) (f : Prenex K n) (constraints : List (Prenex K n)) :
    Option (Stratification model f constraints) :=
  match f with
  | .matrix a =>
    let d := classify model (.matrix a) []
    if h : d.cells.all (fun c => c.code.dimension == 0) = true then
      some (stratifyPoints (.matrix a) constraints d.cells d.nodup d.cover d.contained
        (fun c hc => beq_iff_eq.mp (List.all_eq_true.mp h c hc)))
    else none
  | _ => none

/-- Refine by all cell closure boundaries. The residual loses one
    coordinate dimension at every recursive call. -/
def stratifyWith (model : RealModel K) : (d : ℕ) → (f : Prenex K n) → (constraints : List (Prenex K n)) →
    ThinAt (d+1) (f.carrier model) → Stratification model f constraints
  | 0, f, cs, thin =>
    let layer := cutLayer model 0 f cs thin
    assemble layer (emptyStratification layer.lower _ ((ThinAt.zero_iff_empty _).mp layer.thin))
  | d+1, f, cs, thin =>
    let layer := cutLayer model (d+1) f cs thin
    if h : layer.lower.hasPoint model = true then
      match pointStratification? model layer.lower _ with
      | some points => assemble layer points
      | none => assemble layer (stratifyWith model d layer.lower _ layer.thin)
    else assemble layer (emptyStratification layer.lower _
      (not_nonempty_iff_eq_empty.mp fun hp => h ((Prenex.hasPoint_correct model layer.lower).mpr hp)))

def stratify (model : RealModel K) (f : Prenex K n) : Stratification model f [] :=
  stratifyWith model n f [] (ThinAt.aboveAmbient (Nat.lt_succ_self _) _)

namespace Stratification

variable {f : Prenex K n} {constraints : List (Prenex K n)} (s : Stratification model f constraints)

theorem unique (x : Fin n → ℝ) :
    x ∈ f.carrier model ↔ ∃! a, a ∈ s.strata ∧ x ∈ a.carrier := by
  constructor
  · intro hx
    obtain ⟨a,ha,ha'⟩ := (s.cover x).mp hx
    refine ⟨a,⟨ha,ha'⟩,?_⟩
    rintro b ⟨hb,hb'⟩
    by_contra ne
    exact disjoint_left.mp (s.disjoint_strata b hb a ha ne) hb' ha'
  · rintro ⟨a,⟨ha,hx⟩,_⟩
    exact (s.cover x).mpr ⟨a,ha,hx⟩

def checkContainment (b : Stratum model n) (f : Prenex K n) : Bool :=
  match f with
  | .matrix g => g.atSample b.sample
  | .exists_ g => b.description.inside model (.exists_ g)
  | .forall_ g => b.description.inside model (.forall_ g)

private theorem checkContainment_correct (b : Stratum model n) (f : Prenex K n)
    (h : b.carrier ⊆ f.carrier model ∨ Disjoint b.carrier (f.carrier model))
    {x : Fin n → ℝ} (hx : x ∈ b.carrier) :
    checkContainment b f = true ↔ x ∈ f.carrier model := by
  have alt : b.carrier ⊆ f.carrier model ↔ x ∈ f.carrier model :=
    ⟨fun hs => hs hx, fun hm => h.elim id (fun hdis => (disjoint_left.mp hdis hx hm).elim)⟩
  cases f with
  | matrix g =>
    refine (g.atSample_correct b.sample).trans ?_
    change b.sample.value ∈ (Prenex.matrix g).carrier model ↔ _
    exact ⟨fun hm => h.elim (fun hs => hs hx) (fun hdis => (disjoint_left.mp hdis b.sample_mem hm).elim),
      fun hm => alt.mpr hm b.sample_mem⟩
  | exists_ g => exact (Prenex.inside_correct model _ _).trans alt
  | forall_ g => exact (Prenex.inside_correct model _ _).trans alt

def incidenceRow (i : Fin s.strata.length) : Fin s.strata.length → Bool :=
  if s.strata.length ≤ 1 || (s.strata.get i).dimension == 0 then fun j => i == j
  else
    let desc := describeClosure model (s.strata.get i).description
    fun j => i == j || checkContainment (s.strata.get j) desc

def incidence (i j : Fin s.strata.length) : Bool := s.incidenceRow i j

theorem incidence_correct (i j : Fin s.strata.length) (x : Fin n → ℝ)
    (hx : x ∈ (s.strata.get j).carrier) :
    s.incidence i j = true ↔ x ∈ closure (s.strata.get i).carrier := by
  unfold incidence incidenceRow
  by_cases he : i = j
  · subst j
    split <;> simpa only [beq_self_eq_true, Bool.true_or, true_iff] using
      (show x ∈ closure (s.strata.get i).carrier from subset_closure hx)
  · split
    · rename_i h
      rw [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      rcases h with size | zero
      · exact (he (Fin.ext (by have := i.isLt; have := j.isLt; omega))).elim
      · rw [beq_iff_eq, ((s.strata.get i).closed_of_zero zero).closure_eq]
        exact iff_of_false he (fun h =>
          disjoint_left.mp (s.disjoint_strata _ (List.get_mem _ i) _ (List.get_mem _ j)
            (fun h => he (s.nodup.injective_get h))) h hx)
    · simp only [Bool.or_eq_true,beq_iff_eq,he,false_or]
      let f := describeClosure model (s.strata.get i).description
      have eq : f.carrier model = closure (s.strata.get i).carrier :=
        describeClosure_correct model _
      have h : (s.strata.get j).carrier ⊆ f.carrier model ∨
          Disjoint (s.strata.get j).carrier (f.carrier model) := by
        rw [eq]
        exact s.frontier _ (List.get_mem _ i) _ (List.get_mem _ j)
      exact (checkContainment_correct _ f h hx).trans (Iff.of_eq (congrArg (x ∈ ·) eq))

theorem relativeClosure_eq (i : Fin s.strata.length) :
    closure (s.strata.get i).carrier ∩ f.carrier model =
      ⋃ j : {j // s.incidence i j = true}, (s.strata.get j.val).carrier := by
  ext x
  simp only [mem_iUnion,Subtype.exists,exists_prop]
  constructor
  · rintro ⟨hx,hf⟩
    obtain ⟨a,ha,ha'⟩ := (s.cover x).mp hf
    obtain ⟨j,rfl⟩ := List.get_of_mem ha
    exact ⟨j,(s.incidence_correct i j x ha').mpr hx,ha'⟩
  · rintro ⟨j,hj,hx⟩
    exact ⟨(s.incidence_correct i j x hx).mp hj, (s.cover _).mpr ⟨_, List.get_mem _ j, hx⟩⟩

theorem closure_eq (closed : IsClosed (f.carrier model)) (i : Fin s.strata.length) :
    closure (s.strata.get i).carrier =
      ⋃ j : {j // s.incidence i j = true}, (s.strata.get j.val).carrier := by
  rw [← s.relativeClosure_eq i]
  exact (inter_eq_left.mpr (closure_minimal (fun _ hx =>
    (s.cover _).mpr ⟨_, List.get_mem _ i, hx⟩) closed)).symm

end Stratification

end CertifiedTopology.CADDecision
