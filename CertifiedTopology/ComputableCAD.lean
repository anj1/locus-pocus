module

public import CertifiedTopology.MovingRoots
public import CertifiedTopology.PrunedProjection
public import CertifiedTopology.CADCoordinates
public import Mathlib.Data.List.GetD

@[expose] public section

namespace CertifiedTopology.ComputableCAD

open Set Polynomial CylindricalData CADStacks ExecutableIsolation
open Quartic (Decision Fiber)
open ProjectionData (FiberData)

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {model : RealModel K} {n : ℕ}

def RegularCode (model : RealModel K) : {n : ℕ} → Code K n → Prop
  | 0, .origin => True
  | n+1, .lift b q row =>
    RegularCode model b ∧ ∀ x ∈ b.carrier model,
      let p := q.polynomial.map (Multi.evalHom model.hom x)
      p ≠ 0 ∧ row < (realStack p).length

def ContinuousLayers (model : RealModel K) : {n : ℕ} → Code K n → Prop
  | 0, .origin => True
  | n+1, .lift b q row =>
    ContinuousLayers model b ∧
      ∃ (m : ℕ) (s : Slice (Fin m)) (c : Fin m → b.carrier model → ℝ),
        (Code.lift b q row).carrier model = region c s ∧
        fibreDimension s = (if row % 2 = 0 then 1 else 0) ∧ ∀ i, Continuous (c i)

structure Cell (model : RealModel K) (n : ℕ) where
  code : Code K n
  sample : ExactPoint model n
  sample_mem : sample.value ∈ code.carrier model
  connected : IsPreconnected (code.carrier model)
  regular : RegularCode model code
  euclidean : Nonempty (code.carrier model ≃ₜ (Fin code.dimension → ℝ))
  locallyClosed : IsLocallyClosed (code.carrier model)
  freeChart : Nonempty (FreeChart (code.carrier model) code.dimension)
  layers : ContinuousLayers model code

noncomputable def Cell.carrier (c : Cell model n) : Set (Fin n → ℝ) := c.code.carrier model

def Cell.sign (c : Cell model n) (f : Multi K n) : Side :=
  side (Multi.evalHom c.sample.coefficients c.sample.point f) 0

theorem Cell.sign_correct (c : Cell model n) (f : Multi K n) :
    c.sign f = side (Multi.evalHom model.hom c.sample.value f) 0 :=
  (AlgebraicRoot.map_side c.sample.model.hom c.sample.model.strictMono _).trans
    (congrArg (side · 0) (c.sample.value_eval f))

def Cell.Invariant (c : Cell model n) (ps : List (Multi K n)) : Prop :=
  ∀ x ∈ c.carrier, ∀ f ∈ ps, side (Multi.evalHom model.hom x f) 0 = c.sign f

structure Diagram (model : RealModel K) (n : ℕ) (ps : List (Multi K n)) where
  cells : List (Cell model n)
  partition : ∀ x : Fin n → ℝ, ∃! c, c ∈ cells ∧ x ∈ c.carrier
  invariant : ∀ c ∈ cells, c.Invariant ps

abbrev Poly (K : Type) [Field K] [LinearOrder K] (n : ℕ) :=
  PolynomialData (Multi K n)

def knownZero (p : Multi K n) : Option Bool :=
  (Multi.constantValue p).map (fun a => decide (a = 0))

theorem knownZero_correct {F : Type} [Field F] {b : Bool} (φ : K →+* F) (x : Fin n → F)
    (p : Multi K n) (h : knownZero p = some b) : Multi.evalHom φ x p = 0 ↔ b = true := by
  unfold knownZero at h
  cases e : Multi.constantValue p with
  | none => simp [e] at h
  | some a =>
    simp only [e, Option.map_some, Option.some.injEq] at h
    rw [← h, Multi.constantValue_correct φ x p e, map_eq_zero_iff _ φ.injective, decide_eq_true_eq]

def singleProgram (p : Poly K n) : Decision (Multi K n) (FiberData (Multi K n)) :=
  ProjectionData.pruneSquarefree knownZero p p.natDegree

def pairProgram (p q : Poly K n) : Decision (Multi K n) (FiberData (Multi K n)) :=
  ProjectionData.pruneFiber knownZero p q

def rawTests (ps : List (Poly K n)) : List (Multi K n) :=
  let distinct := ps.dedup
  (distinct.flatMap fun p => (singleProgram p).tests ++
    distinct.flatMap fun q => (pairProgram p q).tests).dedup

def normalize (p : Multi K n) : Multi K n :=
  let a := Multi.leadingScalar p
  if a = 0 then p else Multi.constant a⁻¹ * p

theorem normalize_zero {F : Type} [Field F] (φ : K →+* F) (x : Fin n → F) (p : Multi K n) :
    Multi.evalHom φ x (normalize p) = 0 ↔ Multi.evalHom φ x p = 0 := by
  unfold normalize
  dsimp only
  split
  · rfl
  · simp_all [mul_eq_zero, map_eq_zero_iff _ φ.injective]

def isPowerOf (p q : Multi K n) : Bool :=
  let k := Multi.totalDegree p / Multi.totalDegree q
  1 < k && decide (normalize (q^k) = p)

def representative (pool : List (Multi K n)) (p : Multi K n) : Multi K n :=
  let r := normalize p
  (pool.find? (isPowerOf r)).getD r

theorem representative_zero {F : Type} [Field F] (φ : K →+* F) (x : Fin n → F)
    (pool : List (Multi K n)) (p : Multi K n) :
    Multi.evalHom φ x (representative pool p) = 0 ↔ Multi.evalHom φ x p = 0 := by
  unfold representative
  dsimp only
  cases he : pool.find? (isPowerOf (normalize p)) with
  | none => exact normalize_zero φ x p
  | some q =>
    have h := List.find?_some he
    simp only [isPowerOf, Bool.and_eq_true, decide_eq_true_eq] at h
    have hp := normalize_zero φ x (q ^ (Multi.totalDegree (normalize p) / Multi.totalDegree q))
    rw [h.2, map_pow, pow_eq_zero_iff (show Multi.totalDegree (normalize p) / Multi.totalDegree q ≠ 0 by omega)]
      at hp
    exact hp.symm.trans (normalize_zero φ x p)

def testPool (ps : List (Poly K n)) : List (Multi K n) :=
  ((rawTests ps).map normalize).dedup.mergeSort (fun a b => Multi.totalDegree a ≤ Multi.totalDegree b)

def project (ps : List (Poly K n)) : List (Multi K n) :=
  ((rawTests ps).map (representative (testPool ps))).dedup

theorem single_tests {ps : List (Poly K n)} {p : Poly K n} (hp : p ∈ ps)
    {c : Multi K n} (h : c ∈ (singleProgram p).tests) : c ∈ rawTests ps :=
  List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨p,List.mem_dedup.mpr hp,List.mem_append_left _ h⟩)

theorem pair_tests {ps : List (Poly K n)} {p q : Poly K n} (hp : p ∈ ps) (hq : q ∈ ps)
    {c : Multi K n} (h : c ∈ (pairProgram p q).tests) : c ∈ rawTests ps :=
  List.mem_dedup.mpr (List.mem_flatMap.mpr ⟨p,List.mem_dedup.mpr hp,
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨q,List.mem_dedup.mpr hq,h⟩)⟩)

namespace Cell

theorem branch {A : Type} (b : Cell model n) {ps : List (Poly K n)} (inv : b.Invariant (project ps))
    (d : Decision (Multi K n) A) (tests : ∀ c ∈ d.tests, c ∈ rawTests ps) (x : b.carrier) :
    d.run (Multi.evalHom model.hom x.val) = d.run (Multi.evalHom b.sample.coefficients b.sample.point) := by
  apply ProjectionData.QuarticDecision.run_zero_congr
  intro a ha
  let value := representative (testPool ps) a
  have hv : value ∈ project ps := List.mem_dedup.mpr (List.mem_map_of_mem (tests a ha))
  have h := inv x.val x.property value hv
  unfold Cell.sign at h
  rw [AlgebraicRoot.map_side b.sample.model.hom b.sample.model.strictMono] at h
  exact (representative_zero model.hom x.val _ _).symm.trans
    ((side_congr (K := ℝ) h).2.1.trans ((map_eq_zero_iff _ b.sample.model.hom.injective).trans
      (representative_zero b.sample.coefficients b.sample.point _ _)))

end Cell

noncomputable abbrev specialized (model : RealModel K) (p : Poly K n) (x : Fin n → ℝ) :=
  p.polynomial.map (Multi.evalHom model.hom x)

noncomputable def family (b : Cell model n) (q : Poly K n) (d : ℕ)
    (hd : ∀ x : b.carrier, (specialized model q x.val).natDegree = d)
    (hn : ∀ x : b.carrier, specialized model q x.val ≠ 0)
    (hs : ∀ (x : b.carrier) z, (specialized model q x.val).IsRoot z →
      ¬ (specialized model q x.val).derivative.IsRoot z) : Plane.RootFamily b.carrier :=
  Plane.RootFamily.ofCoefficients (fun x : b.carrier => specialized model q x.val) d
    (fun i => by
      simp only [specialized, coeff_map]
      exact (Multi.continuous_eval model.hom (q.polynomial.coeff i)).comp continuous_subtype_val)
    hd hn hs

theorem single_spec (b : Cell model n) {ps : List (Poly K n)} (inv : b.Invariant (project ps))
    {p : Poly K n} (hp : p ∈ ps) (x : b.carrier) :
    Fiber.Spec (Multi.evalHom model.hom x.val) (specialized model p x.val)
      (((singleProgram p).run (Multi.evalHom b.sample.coefficients b.sample.point)).interpret) := by
  letI := Multi.nontrivial (K := K) n
  rw [← b.branch inv _ (fun _ h => single_tests hp h) x]
  unfold singleProgram
  rw [ProjectionData.run_pruneSquarefree _ knownZero
    (fun c _ eq => knownZero_correct model.hom x.val c eq)]
  exact ProjectionData.squarefree_spec _ _

def stackSource (b : Cell model n) (ps : List (Poly K n)) : Poly K n :=
  ProjectionData.productAt (Multi.evalHom b.sample.coefficients b.sample.point) knownZero ps.dedup

theorem stackSource_spec (b : Cell model n) (ps : List (Poly K n)) (inv : b.Invariant (project ps))
    (x : b.carrier) :
    let q := specialized model (stackSource b ps) x.val
    q ≠ 0 ∧ ∀ t, q.IsRoot t ↔
      ∃ p ∈ ps, specialized model p x.val ≠ 0 ∧ (specialized model p x.val).IsRoot t := by
  letI := Multi.nontrivial (K := K) n
  have same (p : Poly K n) (hp : p ∈ ps) :
      (ProjectionData.pruneDegree knownZero p.natDegree p).run (Multi.evalHom model.hom x.val) =
      (ProjectionData.pruneDegree knownZero p.natDegree p).run (Multi.evalHom b.sample.coefficients b.sample.point) := by
    apply b.branch inv
    intro c hc
    apply single_tests hp
    unfold singleProgram ProjectionData.pruneSquarefree
    exact ProjectionData.QuarticDecision.tests_mem_bind hc
  have eqFor (qs : List (Poly K n))
      (h : ∀ p ∈ qs,
        (ProjectionData.pruneDegree knownZero p.natDegree p).run (Multi.evalHom model.hom x.val) =
        (ProjectionData.pruneDegree knownZero p.natDegree p).run
          (Multi.evalHom b.sample.coefficients b.sample.point)) :
      ProjectionData.productAt (Multi.evalHom model.hom x.val) knownZero qs =
      ProjectionData.productAt (Multi.evalHom b.sample.coefficients b.sample.point) knownZero qs := by
    induction qs with
    | nil => rfl
    | cons p qs ih =>
      simp only [ProjectionData.productAt, h p (by simp)]
      rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
  have eq : ProjectionData.productAt (Multi.evalHom model.hom x.val) knownZero ps.dedup = stackSource b ps :=
    eqFor ps.dedup (fun p hp => same p (List.mem_dedup.mp hp))
  rw [← eq]
  have h := ProjectionData.productAt_spec _ _ (fun c _ e => knownZero_correct model.hom x.val c e) ps.dedup
  exact ⟨h.1,fun t => (h.2 t).trans (by simp only [List.mem_dedup])⟩

theorem exists_singleFamily (b : Cell model n) {ps : List (Poly K n)} (inv : b.Invariant (project ps))
    {p : Poly K n} (hp : p ∈ ps) :
    ∃ P : Plane.RootFamily b.carrier, ∀ x t, (P.poly x).IsRoot t ↔
      specialized model p x.val ≠ 0 ∧ (specialized model p x.val).IsRoot t := by
  have spec := single_spec b inv hp
  cases h : (singleProgram p).run (Multi.evalHom b.sample.coefficients b.sample.point) with
  | line =>
    simp only [h, FiberData.interpret, Fiber.Spec] at spec
    exact ⟨Plane.RootFamily.ofCoefficients (fun _ => 1) 0 (fun _ => continuous_const)
      (by simp) (by simp) (by simp [IsRoot.def]), by simp [spec, IsRoot.def, Plane.RootFamily.ofCoefficients]⟩
  | empty =>
    simp only [h, FiberData.interpret, Fiber.Spec] at spec
    refine ⟨Plane.RootFamily.ofCoefficients (fun _ => 1) 0 (fun _ => continuous_const)
      (by simp) (by simp) (by simp), fun x t => ?_⟩
    change (1 : Polynomial ℝ).IsRoot t ↔ _
    exact iff_of_false (by simp [IsRoot.def]) (fun h => spec x t h.2)
  | roots q d =>
    simp only [h, FiberData.interpret, Fiber.Spec] at spec
    have nz (x : b.carrier) : specialized model p x.val ≠ 0 := by
      intro hzero
      apply (spec x).2.1
      apply Polynomial.funext
      intro a
      rw [eval_zero]
      exact IsRoot.def.mp (((spec x).2.2.1 a).mpr (by simp [hzero, IsRoot.def]))
    let P := family b q d (fun x => (spec x).1) (fun x => (spec x).2.1) (fun x => (spec x).2.2.2)
    exact ⟨P, fun x t => ((spec x).2.2.1 t).trans (and_iff_right (nz x)).symm⟩

theorem single_zero_stable (b : Cell model n) {ps : List (Poly K n)} (inv : b.Invariant (project ps))
    {p : Poly K n} (hp : p ∈ ps) (x y : b.carrier) :
    specialized model p x.val = 0 ↔ specialized model p y.val = 0 := by
  have s := single_spec b inv hp
  cases h : (singleProgram p).run (Multi.evalHom b.sample.coefficients b.sample.point) with
  | line => simp [h, FiberData.interpret, Fiber.Spec] at s; simp [s]
  | empty =>
    simp only [h, FiberData.interpret, Fiber.Spec] at s
    have nz (v : b.carrier) : specialized model p v.val ≠ 0 :=
      fun hz => s v 0 (by simp [hz, IsRoot.def])
    simp [nz]
  | roots q d =>
    simp only [h, FiberData.interpret, Fiber.Spec] at s
    have nz (v : b.carrier) : specialized model p v.val ≠ 0 := by
      intro hz
      apply (s v).2.1
      apply Polynomial.funext
      intro a
      rw [eval_zero]
      exact IsRoot.def.mp (((s v).2.2.1 a).mpr (by simp [hz, IsRoot.def]))
    simp [nz]

theorem exists_commonFamily (b : Cell model n) {ps : List (Poly K n)} (inv : b.Invariant (project ps))
    {p q : Poly K n} (hp : p ∈ ps) (hq : q ∈ ps)
    (P Q : Plane.RootFamily b.carrier)
    (pp : ∀ x t, (P.poly x).IsRoot t ↔ specialized model p x.val ≠ 0 ∧ (specialized model p x.val).IsRoot t)
    (qq : ∀ x t, (Q.poly x).IsRoot t ↔ specialized model q x.val ≠ 0 ∧ (specialized model q x.val).IsRoot t) :
    ∃ C : Plane.RootFamily b.carrier, ∀ x t, (C.poly x).IsRoot t ↔
      (P.poly x).IsRoot t ∧ (Q.poly x).IsRoot t := by
  letI := Multi.nontrivial (K := K) n
  let s : b.carrier := ⟨b.sample.value,b.sample_mem⟩
  let empty := Plane.RootFamily.ofCoefficients (B := b.carrier) (fun _ => 1) 0
    (fun _ => continuous_const) (by simp) (by simp) (by simp [IsRoot.def])
  have er (x : b.carrier) (t : ℝ) : ¬(empty.poly x).IsRoot t := by
    change ¬(1 : Polynomial ℝ).IsRoot t
    simp [IsRoot.def]
  by_cases zp : specialized model p s.val = 0
  · refine ⟨empty, fun x t => ?_⟩
    exact iff_of_false (er x t) (fun h => ((pp x t).mp h.1).1 ((single_zero_stable b inv hp s x).mp zp))
  by_cases zq : specialized model q s.val = 0
  · refine ⟨empty, fun x t => ?_⟩
    exact iff_of_false (er x t) (fun h => ((qq x t).mp h.2).1 ((single_zero_stable b inv hq s x).mp zq))
  let e := (pairProgram p q).run (Multi.evalHom b.sample.coefficients b.sample.point)
  have spec (x : b.carrier) (t : ℝ) :
      match e with
      | .line => ∀ r, (specialized model p x.val).IsRoot r ∧ (specialized model q x.val).IsRoot r
      | .empty => ¬((specialized model p x.val).IsRoot t ∧ (specialized model q x.val).IsRoot t)
      | .roots f d =>
        (specialized model f x.val).natDegree = d ∧ specialized model f x.val ≠ 0 ∧
        ((specialized model f x.val).IsRoot t ↔
          (specialized model p x.val).IsRoot t ∧ (specialized model q x.val).IsRoot t) ∧
        ((specialized model f x.val).IsRoot t → ¬(specialized model f x.val).derivative.IsRoot t) := by
    dsimp only [e]
    rw [← b.branch inv _ (fun _ h => pair_tests hp hq h) x]
    unfold pairProgram
    rw [ProjectionData.run_pruneFiber _ _ (fun c _ h => knownZero_correct model.hom x.val c h)]
    have h := ProjectionData.fiber_spec (Multi.evalHom model.hom x.val) p q t
    dsimp only at h
    cases hroute : (ProjectionData.fiberDecision p q).run (Multi.evalHom model.hom x.val) <;>
      simpa only [hroute] using h
  cases he : e with
  | line =>
    have hz : specialized model p s.val = 0 := by
      apply Polynomial.funext
      intro a
      rw [eval_zero]
      have sp : ∀ r, (specialized model p s.val).IsRoot r ∧ (specialized model q s.val).IsRoot r := by
        simpa only [he] using spec s 0
      exact (sp a).1
    exact (zp hz).elim
  | empty =>
    refine ⟨empty, fun x t => ⟨fun h => (er x t h).elim, fun ⟨h₁,h₂⟩ => ?_⟩⟩
    have h := spec x t
    simp only [he] at h
    exact (h ⟨((pp x t).mp h₁).2, ((qq x t).mp h₂).2⟩).elim
  | roots f d =>
    have run (x : b.carrier) (t : ℝ) := spec x t
    simp only [he] at run
    let C := family b f d (fun x => (run x 0).1) (fun x => (run x 0).2.1) (fun x t => (run x t).2.2.2)
    refine ⟨C, fun x t => ?_⟩
    rw [pp, qq]
    have np : specialized model p x.val ≠ 0 := mt (single_zero_stable b inv hp x s).mp zp
    have nq : specialized model q x.val ≠ 0 := mt (single_zero_stable b inv hq x s).mp zq
    exact ((run x t).2.2.1).trans (by simp [np,nq])

theorem exists_unionFamily (b : Cell model n) (ps : List (Poly K n)) (inv : b.Invariant (project ps)) :
    ∃ P : Plane.RootFamily b.carrier, ∀ x t, (P.poly x).IsRoot t ↔
      (specialized model (stackSource b ps) x.val).IsRoot t := by
  classical
  letI : PreconnectedSpace b.carrier := isPreconnected_iff_preconnectedSpace.mp b.connected
  let s : b.carrier := ⟨b.sample.value,b.sample_mem⟩
  let q := stackSource b ps
  let g (x : b.carrier) := specialized model q x.val
  let P (p : {p // p ∈ ps}) := (exists_singleFamily b inv p.property).choose
  have spec (p : {p // p ∈ ps}) := (exists_singleFamily b inv p.property).choose_spec
  have cover (x : b.carrier) (t : ℝ) : (g x).IsRoot t ↔ ∃ p : {p // p ∈ ps}, ((P p).poly x).IsRoot t := by
    rw [(stackSource_spec b ps inv x).2 t]
    exact ⟨fun ⟨p,hp,h⟩ => ⟨⟨p,hp⟩,(spec ⟨p,hp⟩ x t).mpr h⟩,
      fun ⟨p,h⟩ => ⟨p.val,p.property,(spec p x t).mp h⟩⟩
  let I := (g s).roots.toFinset
  have hh (i : I) : ∃ p : {p // p ∈ ps}, ∃ j, (P p).rootSection s j s = i.val := by
    have h := (Polynomial.mem_roots (stackSource_spec b ps inv s).1).mp (Multiset.mem_toFinset.mp i.property)
    obtain ⟨p,hp⟩ := (cover s i.val).mp h
    exact ⟨p,(P p).exists_section s s ((P p).mem_roots s i.val |>.mpr hp)⟩
  choose owner index original using hh
  let f (i : I) := (P (owner i)).rootSection s (index i)
  have cont (i : I) : Continuous (f i) := (P (owner i)).continuous_section s (index i)
  have eq (i : I) (p : {p // p ∈ ps}) (j : Fin ((P p).roots s).card) (x : b.carrier) :
      f i x = (P p).rootSection s j x ↔ f i s = (P p).rootSection s j s := by
    obtain ⟨C,hC⟩ := exists_commonFamily b inv (owner i).property p.property
      (P (owner i)) (P p) (spec (owner i)) (spec p)
    exact (P (owner i)).same_root (P p) C hC _ _ (cont i) ((P p).continuous_section s j)
      (fun x => ((P (owner i)).mem_roots x _).mp ((P (owner i)).section_mem s x (index i)))
      (fun x => ((P p).mem_roots x _).mp ((P p).section_mem s x j)) x s
  have inj (x : b.carrier) : Function.Injective (fun i => f i x) := by
    intro i j h
    have e := (eq i (owner j) (index j) x).mp h
    exact Subtype.ext ((original i).symm.trans (e.trans (original j)))
  refine ⟨Plane.RootFamily.ofSections f cont inj, fun x t => ?_⟩
  rw [Plane.RootFamily.ofSections_roots, cover]
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨owner i, ((P (owner i)).mem_roots x _).mp ((P (owner i)).section_mem s x (index i))⟩
  · rintro ⟨p,hp⟩
    obtain ⟨j,hj⟩ := (P p).exists_section s x (((P p).mem_roots x t).mpr hp)
    let v := (P p).rootSection s j s
    have hv := ((P p).mem_roots s v).mp ((P p).section_mem s s j)
    have hi : v ∈ I := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (stackSource_spec b ps inv s).1).mpr
      ((cover s v).mpr ⟨p,hv⟩))
    let i : I := ⟨v,hi⟩
    exact ⟨i, ((eq i p j x).mpr (original i)).trans hj⟩

theorem roots_on_row {B : Type} [TopologicalSpace B] [PreconnectedSpace B] {P : Plane.RootFamily B}
    (sample : B) (x : B) (s : Slice (Fin (P.roots sample).card)) (hm : s ∈ frame _)
    {z : ℝ} (hz : Univariate.contains (mapSlice (fun i => P.rootSection sample i x) s) z) :
    match s with
    | .sectionAt i => z = P.rootSection sample i x
    | .sector _ _ => ¬(P.poly x).IsRoot z := by
  cases s with
  | sectionAt i => exact hz
  | sector l u =>
    intro he
    obtain ⟨i, hi⟩ := P.exists_section sample x ((P.mem_roots x z).mpr he)
    have hs : .sectionAt (P.rootSection sample i x) ∈ realStack (P.poly x) := by
      rw [realStack_of_family P sample x]
      exact List.mem_map_of_mem (f := mapSlice fun j => P.rootSection sample j x) (section_mem_frame i)
    have hm' : mapSlice (fun j => P.rootSection sample j x) (.sector l u) ∈ realStack (P.poly x) := by
      rw [realStack_of_family P sample x]
      exact List.mem_map_of_mem hm
    obtain ⟨_,_,hu⟩ := stack_partition (P.poly x) z
    have e := (hu _ ⟨hs,hi.symm⟩).trans (hu _ ⟨hm',hz⟩).symm
    cases e


theorem invariant_row_zeros (b : Cell model n) (ps : List (Poly K n)) (inv : b.Invariant (project ps))
    {P : Plane.RootFamily b.carrier}
    (union : ∀ x : b.carrier, ∀ t, (P.poly x).IsRoot t ↔
      ∃ f ∈ ps, specialized model f x.val ≠ 0 ∧ (specialized model f x.val).IsRoot t)
    [PreconnectedSpace b.carrier] (sample : b.carrier)
    (s : Slice (Fin (P.roots sample).card)) (hm : s ∈ frame _)
    (x y : b.carrier) {z w : ℝ}
    (hz : Univariate.contains (mapSlice (fun i => P.rootSection sample i x) s) z)
    (hw : Univariate.contains (mapSlice (fun i => P.rootSection sample i y) s) w)
    {f : Poly K n} (hf : f ∈ ps) :
    (specialized model f x.val).IsRoot z ↔ (specialized model f y.val).IsRoot w := by
  letI := Multi.nontrivial (K := K) n
  let expr := singleProgram f
  let answer := expr.run (Multi.evalHom b.sample.coefficients b.sample.point)
  have spec (u : b.carrier) : Fiber.Spec (Multi.evalHom model.hom u.val)
      (specialized model f u.val) answer.interpret := by
    dsimp only [answer]
    rw [← b.branch inv expr (fun _ h => single_tests hf h) u]
    unfold expr singleProgram
    rw [ProjectionData.run_pruneSquarefree _ knownZero
      (fun c _ eq => knownZero_correct model.hom u.val c eq)]
    exact ProjectionData.squarefree_spec _ _
  cases route : answer with
  | line =>
    have zero (u : b.carrier) : specialized model f u.val = 0 := by
      simpa only [route, FiberData.interpret, Fiber.Spec] using spec u
    simp [zero, IsRoot.def]
  | empty =>
    have empty (u : b.carrier) : ∀ t, ¬(specialized model f u.val).IsRoot t := by
      simpa only [route, FiberData.interpret, Fiber.Spec] using spec u
    exact ⟨fun h => (empty x z h).elim, fun h => (empty y w h).elim⟩
  | roots p d =>
    have regular (u : b.carrier) :
        (specialized model p u.val).natDegree = d ∧ specialized model p u.val ≠ 0 ∧
        (∀ t, (specialized model p u.val).IsRoot t ↔ (specialized model f u.val).IsRoot t) ∧
        ∀ t, (specialized model p u.val).IsRoot t → ¬(specialized model p u.val).derivative.IsRoot t := by
      simpa only [route, FiberData.interpret, Fiber.Spec] using spec u
    have hnon (u : b.carrier) : specialized model f u.val ≠ 0 := by
      intro eq
      apply (regular u).2.1
      apply Polynomial.funext
      intro a
      rw [eval_zero]
      exact IsRoot.def.mp (((regular u).2.2.1 a).mpr (by simp [eq, IsRoot.def]))
    let Q := family b p d (fun u => (regular u).1) (fun u => (regular u).2.1)
      (fun u => (regular u).2.2.2)
    have included (u : b.carrier) : Q.roots u ⊆ P.roots u := by
      intro t ht
      exact (P.mem_roots u t).mpr ((union u t).mpr
        ⟨f,hf,hnon u, ((regular u).2.2.1 t).mp ((Q.mem_roots u t).mp ht)⟩)
    have hx := roots_on_row sample x s hm hz
    have hy := roots_on_row sample y s hm hw
    cases s with
    | sectionAt i =>
      dsimp only at hx hy
      subst z w
      let r := P.rootSection sample i
      have h := Plane.RootFamily.section_membership P Q included r (P.continuous_section sample i)
        (fun a => P.section_mem sample a i) x y
      exact (((regular x).2.2.1 (r x)).symm.trans (Q.mem_roots x (r x)).symm).trans
        (h.trans ((Q.mem_roots y (r y)).trans ((regular y).2.2.1 (r y))))
    | sector l u =>
      change ¬(P.poly x).IsRoot z at hx
      change ¬(P.poly y).IsRoot w at hy
      exact ⟨fun h => (hx ((union x z).mpr ⟨f,hf,hnon x,h⟩)).elim,
        fun h => (hy ((union y w).mpr ⟨f,hf,hnon y,h⟩)).elim⟩

structure Stack (b : Cell model n) (ps : List (Poly K n)) where
  cells : List (Cell model (n+1))
  base : ∀ c ∈ cells, ∀ p ∈ c.carrier, dropLast p ∈ b.carrier
  partition : ∀ x ∈ b.carrier, ∀ y, ∃! c, c ∈ cells ∧ Fin.snoc x y ∈ c.carrier
  surjects : ∀ c ∈ cells, ∀ x ∈ b.carrier, ∃ y, Fin.snoc x y ∈ c.carrier
  invariant : ∀ c ∈ cells, c.Invariant ps

structure Stack.Valid (b : Cell model n) (ps : List (Poly K n)) (cells : List (Cell model (n+1))) :
    Prop where
  base : ∀ c ∈ cells, ∀ p ∈ c.carrier, dropLast p ∈ b.carrier
  partition : ∀ x ∈ b.carrier, ∀ y, ∃! c, c ∈ cells ∧ Fin.snoc x y ∈ c.carrier
  surjects : ∀ c ∈ cells, ∀ x ∈ b.carrier, ∃ y, Fin.snoc x y ∈ c.carrier
  invariant : ∀ c ∈ cells, c.Invariant ps

def sampleStack (b : Cell model n) (ps : List (Poly K n)) (q : Poly K n) :
    List (AlgebraicRoot.Sample b.sample.model) :=
  let res := isolate b.sample.model (b.sample.fiber q).coefficients
  let rs := AlgebraicRoot.shrinkRoots b.sample.model (ps.dedup.map fun p => (b.sample.fiber p).coefficients)
    (AlgebraicRoot.roots b.sample.model res)
  (AlgebraicRoot.stackSamples b.sample.model none rs.val (by
    apply List.pairwise_map.mp
    rw [rs.property]
    exact List.pairwise_map.mpr (AlgebraicRoot.roots_ordered _ _)) (by simp)).val

structure ValidRow (b : Cell model n) (q : Poly K n) (ss : List (AlgebraicRoot.Sample b.sample.model))
    (i : Fin ss.length) : Prop where
  sample_mem : (b.sample.extend (ss.get i)).value ∈ (Code.lift b.code q i.val).carrier model
  connected : IsPreconnected ((Code.lift b.code q i.val).carrier model)
  regular : RegularCode model (.lift b.code q i.val)
  euclidean : Nonempty ((Code.lift b.code q i.val).carrier model ≃ₜ
    (Fin (Code.lift b.code q i.val).dimension → ℝ))
  locallyClosed : IsLocallyClosed ((Code.lift b.code q i.val).carrier model)
  freeChart : Nonempty (FreeChart ((Code.lift b.code q i.val).carrier model) (Code.lift b.code q i.val).dimension)
  layers : ContinuousLayers model (.lift b.code q i.val)

def rowCells (b : Cell model n) (q : Poly K n) (ss : List (AlgebraicRoot.Sample b.sample.model))
    (h : ∀ i, ValidRow b q ss i) : List (Cell model (n+1)) :=
  List.ofFn fun i => ⟨.lift b.code q i.val, b.sample.extend (ss.get i), (h i).sample_mem,
    (h i).connected, (h i).regular, (h i).euclidean, (h i).locallyClosed, (h i).freeChart, (h i).layers⟩

theorem lift_valid (b : Cell model n) (ps : List (Poly K n)) (inv : b.Invariant (project ps)) :
    let q := stackSource b ps
    let ss := sampleStack b ps q
    ∃ h : ∀ i, ValidRow b q ss i, Stack.Valid b ps (rowCells b q ss h) := by
  let q := stackSource b ps
  obtain ⟨P,hP⟩ := exists_unionFamily b ps inv
  have shared (x : b.carrier) := stackSource_spec b ps inv x
  have stackEq (x : b.carrier) : realStack (specialized model q x.val) = realStack (P.poly x) := by
    unfold realStack
    congr 1
    apply roots_eq_sorted (P.nonzero x) (sortedRoots_order _)
    intro t
    exact (mem_sortedRoots (shared x).1 t).trans (hP x t).symm
  let s₀ : b.carrier := ⟨b.sample.value, b.sample_mem⟩
  letI : PreconnectedSpace b.carrier := isPreconnected_iff_preconnectedSpace.mp b.connected
  let u := b.sample.fiber q
  let p := b.sample.model
  let res := isolate p u.coefficients
  let rs := AlgebraicRoot.shrinkRoots p (ps.dedup.map fun f => (b.sample.fiber f).coefficients)
    (AlgebraicRoot.roots p res)
  let ss := AlgebraicRoot.stackSamples p none rs.val (by
    apply List.pairwise_map.mp
    rw [rs.property]
    exact List.pairwise_map.mpr (AlgebraicRoot.roots_ordered _ _)) (by simp)
  have polyEq : realPoly p.hom u.coefficients = specialized model q s₀.val := b.sample.fiber_correct q
  have sorted : rs.val.map AlgebraicRoot.Root.value = sortedRoots (P.poly s₀) := by
    rw [rs.property]
    apply roots_eq_sorted (P.nonzero s₀) (List.pairwise_map.mpr (AlgebraicRoot.roots_ordered p res))
    intro z
    rw [List.mem_map, hP, ← polyEq]
    exact ⟨fun ⟨r,hr,e⟩ => e ▸ AlgebraicRoot.roots_sound p res hr,
      fun h => AlgebraicRoot.roots_complete p res (polyEq ▸ (shared s₀).1) h⟩
  have samples : List.Forall₂ (fun a s => Univariate.contains s (a.value p)) ss.val (realStack (P.poly s₀)) := by
    have h : slices (n := 0) none (rs.val.map AlgebraicRoot.Root.value) = realStack (P.poly s₀) :=
      congrArg (slices (n := 0) none) sorted
    exact Eq.mp (congrArg (List.Forall₂ (fun a s => Univariate.contains s (a.value p)) ss.val) h)
      ss.property
  let m := (P.roots s₀).card
  have length (x : b.carrier) : (realStack (P.poly x)).length = (frame m).length := by
    rw [realStack_of_family P s₀ x, List.length_map]
  have len := samples.length_eq.trans (length s₀)
  let shape (i : Fin ss.val.length) : Slice (Fin m) := (frame m).get (Fin.cast len i)
  have shape_mem (i : Fin ss.val.length) : shape i ∈ frame m := List.get_mem _ _
  have ind (x : b.carrier) (i : Fin ss.val.length) : i.val < (realStack (P.poly x)).length :=
    (len.trans (length x).symm) ▸ i.isLt
  have row (x : b.carrier) (i : Fin ss.val.length) :
      (realStack (P.poly x)).getD i.val (.sector none none) =
        mapSlice (fun j => P.rootSection s₀ j x) (shape i) := by
    rw [List.getD_eq_getElem _ _ (ind x i)]
    have e := realStack_of_family P s₀ x
    simp only [List.get_eq_getElem, shape]
    rw [List.getElem_of_eq e (ind x i), List.getElem_map]
    rfl
  have asRegion (i : Fin ss.val.length) :
      (Code.lift b.code q i.val).carrier model = region (P.rootSection s₀) (shape i) := by
    ext x
    change
      (dropLast x ∈ b.carrier ∧ Univariate.contains
        ((realStack (specialized model q (dropLast x))).getD i.val (.sector none none)) (last x)) ↔ _
    constructor
    · rintro ⟨hb,h⟩
      let a : b.carrier := ⟨dropLast x,hb⟩
      change Univariate.contains ((realStack (specialized model q a.val)).getD i.val (.sector none none)) (last x) at h
      rw [stackEq a, row a i] at h
      exact ⟨hb,h⟩
    · rintro ⟨hb,h⟩
      let a : b.carrier := ⟨dropLast x,hb⟩
      have e := congrArg (fun rs => rs.getD i.val (.sector none none)) (stackEq a)
      exact ⟨hb, (e.trans (row a i)).symm ▸ h⟩
  have valid (i : Fin ss.val.length) : ValidRow b q ss.val i := by
    have dim : fibreDimension (shape i) = if i.val % 2 = 0 then 1 else 0 :=
      fibreDimension_get none _ i.val (len ▸ i.isLt)
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    · rw [ExactPoint.value_extend, Code.carrier_lift_snoc]
      refine ⟨b.sample_mem, ?_⟩
      change Univariate.contains ((realStack (specialized model q s₀.val)).getD i.val (.sector none none))
        ((ss.val.get i).value p)
      rw [stackEq s₀, List.getD_eq_getElem _ _ (ind s₀ i)]
      exact samples.get i.isLt (ind s₀ i)
    · rw [asRegion i]
      apply isPreconnected_region _ _ b.connected (P.continuous_section s₀) (P.section_order s₀)
      intro l u e
      exact frame_ordered (e ▸ shape_mem i)
    · exact ⟨b.regular, fun x hx => ⟨(shared ⟨x,hx⟩).1, (stackEq ⟨x,hx⟩).symm ▸ ind ⟨x,hx⟩ i⟩⟩
    · change Nonempty ((Code.lift b.code q i.val).carrier model ≃ₜ
        (Fin (b.code.dimension + (if i.val % 2 = 0 then 1 else 0)) → ℝ))
      rw [asRegion i, ← dim]
      have hb := b.euclidean
      cases hs : shape i with
      | sectionAt j =>
        exact ⟨(sectionModel _ j (P.continuous_section s₀ j)).trans hb.some⟩
      | sector lo up =>
        have bound l u (hl : lo = some l) (hu : up = some u) : l < u :=
          frame_ordered ((hs.trans (congrArg₂ Slice.sector hl hu)) ▸ shape_mem i)
        let hm := sectorModel (P.rootSection s₀) lo up (P.continuous_section s₀) (P.section_order s₀) bound
        exact ⟨hm.trans ((hb.some.prodCongr (Homeomorph.funUnique (Fin 1) ℝ).symm).trans
          (Fin.appendHomeomorph b.code.dimension 1))⟩
    · rw [asRegion i]
      exact locallyClosed_region _ _ b.locallyClosed (P.continuous_section s₀)
    · change Nonempty (FreeChart ((Code.lift b.code q i.val).carrier model)
        (b.code.dimension + (if i.val % 2 = 0 then 1 else 0)))
      rw [asRegion i, ← dim]
      cases shape i with
      | sectionAt j => exact ⟨b.freeChart.some.sectionChart _ j (P.continuous_section s₀ j)⟩
      | sector l u => exact ⟨b.freeChart.some.sector _ l u (P.continuous_section s₀)⟩
    · exact ⟨b.layers, m, shape i, P.rootSection s₀, asRegion i, dim, P.continuous_section s₀⟩
  change ∃ h : ∀ i, ValidRow b q ss.val i, Stack.Valid b ps (rowCells b q ss.val h)
  let mk (i : Fin ss.val.length) : Cell model (n+1) :=
    ⟨.lift b.code q i.val, b.sample.extend (ss.val.get i), (valid i).sample_mem,
      (valid i).connected, (valid i).regular, (valid i).euclidean, (valid i).locallyClosed,
      (valid i).freeChart, (valid i).layers⟩
  refine ⟨valid, show Stack.Valid b ps (List.ofFn mk) from ⟨?_, ?_, ?_, ?_⟩⟩
  · intro c hc x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    rw [show (mk i).carrier = (Code.lift b.code q i.val).carrier model from rfl, asRegion] at hx
    exact hx.choose
  · intro x hx y
    let x' : b.carrier := ⟨x,hx⟩
    obtain ⟨s,⟨hm,hy⟩,hu⟩ := stack_partition (P.poly x') y
    obtain ⟨j,ej⟩ := List.get_of_mem hm
    let i : Fin ss.val.length := Fin.cast ((length x').trans len.symm) j
    have hrow : (realStack (P.poly x')).getD i.val (.sector none none) = s := by
      rw [List.getD_eq_getElem _ _ (ind x' i)]
      exact ej
    refine ⟨mk i, ⟨List.mem_ofFn.mpr ⟨i,rfl⟩, ?_⟩, ?_⟩
    · change Fin.snoc x y ∈ (Code.lift b.code q i.val).carrier model
      refine (Code.carrier_lift_snoc _ _ _ _ _ _).mpr ⟨hx, ?_⟩
      change Univariate.contains ((realStack (specialized model q x'.val)).getD i.val (.sector none none)) y
      rw [stackEq x', hrow]
      exact hy
    · rintro c ⟨hc,hcy⟩
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hc
      have hr := ((Code.carrier_lift_snoc model b.code q k.val x y).mp hcy).2
      let v : Fin (realStack (P.poly x')).length := ⟨k.val,ind x' k⟩
      change Univariate.contains ((realStack (specialized model q x'.val)).getD k.val (.sector none none)) y at hr
      rw [stackEq x'] at hr
      have vv := hu ((realStack (P.poly x')).get v) ⟨List.get_mem _ _, by
        rw [List.get_eq_getElem, ← List.getD_eq_getElem]
        exact hr⟩
      have hnd := realStack_nodup (P.poly x')
      have ji : v = j := hnd.injective_get (vv.trans ej.symm)
      have ke := congrArg Fin.val ji
      have ki : k = i := Fin.ext ke
      exact congrArg mk ki
  · intro c hc x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    let v : b.carrier := ⟨x,hx⟩
    let p' := P.poly v
    let s := (realStack p').get ⟨i.val, ind v i⟩
    have hs : s ∈ realStack p' := List.get_mem _ _
    have mem := slice_sample (n := 0) () (sortedRoots_order p') none (by simp [Lower]) hs
    refine ⟨Slice.sample (K := ℝ) (n := 0) () s, (Code.carrier_lift_snoc model b.code q i.val x _).mpr ⟨hx,?_⟩⟩
    change Univariate.contains ((realStack (specialized model q v.val)).getD i.val (.sector none none)) _
    rw [stackEq v, List.getD_eq_getElem _ _ (ind v i)]
    exact mem
  · intro c hc p' hp' f hf
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    rw [Cell.sign_correct]
    let c := mk i
    let G : c.carrier → ℝ := fun x => Multi.evalHom model.hom x.val f
    letI : PreconnectedSpace c.carrier := isPreconnected_iff_preconnectedSpace.mp c.connected
    have cg : Continuous G := (Multi.continuous_eval model.hom f).comp continuous_subtype_val
    let u : c.carrier := ⟨c.sample.value,c.sample_mem⟩
    let a : c.carrier := ⟨p', hp'⟩
    change side (G a) 0 = side (G u) 0
    apply Plane.same_sign_of_zero cg a u
    intro v
    have prop (w : c.carrier) : w.val ∈ region (P.rootSection s₀) (shape i) := asRegion i ▸ w.property
    have hv := prop v
    have hu := prop u
    let vx : b.carrier := ⟨dropLast v.val,hv.choose⟩
    let ux : b.carrier := ⟨dropLast u.val,hu.choose⟩
    have zero := invariant_row_zeros b ps inv
      (fun x t => (hP x t).trans ((shared x).2 t)) s₀ (shape i) (shape_mem i) vx ux hv.choose_spec hu.choose_spec hf
    have eval (w : c.carrier) : (specialized model f (dropLast w.val)).IsRoot (last w.val) ↔ G w = 0 := by
      rw [IsRoot.def]
      exact Iff.of_eq (congrArg (· = 0) (PolynomialData.evalHom_correct _ _ f).symm)
    exact (eval v).symm.trans (zero.trans (eval u))


/-- Compute exact sample rows and attach proofs of their real interpretation. -/
def lift (b : Cell model n) (ps : List (Poly K n)) (inv : b.Invariant (project ps)) : Stack b ps :=
  let q := stackSource b ps
  let ss := sampleStack b ps q
  let h := lift_valid b ps inv
  let v := h.choose_spec
  ⟨rowCells b q ss h.choose,
    v.base, v.partition, v.surjects, v.invariant⟩

theorem lift_nodup (b : Cell model n) (ps : List (Poly K n)) (inv : b.Invariant (project ps)) :
    (lift b ps inv).cells.Nodup := by
  change (rowCells b (stackSource b ps) (sampleStack b ps (stackSource b ps)) (lift_valid b ps inv).choose).Nodup
  apply List.nodup_ofFn_ofInjective
  intro i j he
  let row (c : Cell model (n+1)) : ℕ := match c.code with | .lift _ _ i => i
  exact Fin.ext (congrArg row he)

def origin (model : RealModel K) : Cell model 0 :=
  ⟨.origin, ExactPoint.origin model, mem_univ _, isPreconnected_univ, trivial, ⟨Homeomorph.Set.univ _⟩,
    isClosed_univ.isLocallyClosed, ⟨FreeChart.origin⟩, trivial⟩

/-- A sign-invariant CAD for any finite list of polynomials. Projection,
    exact samples, and lifting decisions are executable in the input field. -/
def cad (model : RealModel K) : (n : ℕ) → (ps : List (Multi K n)) → Diagram model n ps
  | 0, ps => ⟨[origin model], by
      intro x
      exact ⟨origin model, ⟨by simp,mem_univ _⟩, fun _ h => List.mem_singleton.mp h.1⟩, by
      intro c hc x _ p _
      obtain rfl := List.mem_singleton.mp hc
      have eq : x = (origin model).sample.value := by ext i; exact i.elim0
      rw [Cell.sign_correct, eq]⟩
  | n+1, ps => by
    let d := cad model n (project ps)
    let stack (b : {c // c ∈ d.cells}) := lift b.val ps (d.invariant _ b.property)
    let cells := d.cells.attach.flatMap fun b => (stack b).cells
    have member (c : Cell model (n+1)) :
        c ∈ cells ↔ ∃ b : {c // c ∈ d.cells}, c ∈ (stack b).cells := by
      simp [cells, List.mem_flatMap]
    refine ⟨cells, ?_, ?_⟩
    · intro p
      let x := dropLast p
      let y := last p
      have eta : Fin.snoc x y = p := snoc_dropLast p
      obtain ⟨b,⟨hb,hx⟩,unique⟩ := d.partition x
      let base : {c // c ∈ d.cells} := ⟨b,hb⟩
      obtain ⟨c,⟨hc,hp⟩,un⟩ := (stack base).partition x hx y
      refine ⟨c,⟨(member c).mpr ⟨base,hc⟩,eta ▸ hp⟩,?_⟩
      rintro a ⟨ha,ha'⟩
      obtain ⟨v,hv⟩ := (member a).mp ha
      have eq := unique v.val ⟨v.property,(stack v).base a hv p ha'⟩
      have he : v = base := Subtype.ext eq
      subst v
      exact un a ⟨hv,eta.symm ▸ ha'⟩
    · intro c hc
      obtain ⟨b,h⟩ := (member c).mp hc
      exact (stack b).invariant c h

def filteredIntersection (model : RealModel K) (p q : Multi K n) : List (Cell model n) :=
  (cad model n [p,q]).cells.filter fun c => c.sign p == .on && c.sign q == .on

theorem cad_nodup (model : RealModel K) : (n : ℕ) → (ps : List (Multi K n)) → (cad model n ps).cells.Nodup
  | 0, _ => List.nodup_singleton _
  | n+1, ps => by
    let d := cad model n (project ps)
    let stack (b : {c // c ∈ d.cells}) := lift b.val ps (d.invariant _ b.property)
    change (d.cells.attach.flatMap (fun b => (stack b).cells)).Nodup
    apply List.nodup_flatMap.mpr
    refine ⟨fun b _ => lift_nodup b.val ps _, ?_⟩
    have h := List.nodup_attach.mpr (cad_nodup model n (project ps))
    exact h.imp (fun {a b} different {c} ha hb => by
      let p := dropLast c.sample.value
      obtain ⟨_,_,unique⟩ := d.partition p
      have h₁ := unique a.val ⟨a.property,(stack a).base c ha _ c.sample_mem⟩
      have h₂ := unique b.val ⟨b.property,(stack b).base c hb _ c.sample_mem⟩
      exact different (Subtype.ext (h₁.trans h₂.symm)))

def pairCanMeet (b : Cell model n) (p q : Poly K n) : Bool :=
  match (pairProgram p q).run (Multi.evalHom b.sample.coefficients b.sample.point) with
  | .empty => false
  | _ => true

theorem pairEmpty (b : Cell model n) (p q : Poly K n) (inv : b.Invariant (project [p,q]))
    (h : pairCanMeet b p q = false) (x : b.carrier) (z : ℝ) :
    ¬((specialized model p x.val).IsRoot z ∧ (specialized model q x.val).IsRoot z) := by
  letI := Multi.nontrivial (K := K) n
  have e : (pairProgram p q).run (Multi.evalHom b.sample.coefficients b.sample.point) = .empty := by
    unfold pairCanMeet at h
    split at h <;> simp_all
  rw [← b.branch inv _ (fun _ a => pair_tests (by simp) (by simp) a) x] at e
  unfold pairProgram at e
  rw [ProjectionData.run_pruneFiber _ _ (fun c _ he => knownZero_correct model.hom x.val c he)] at e
  have hspec := ProjectionData.fiber_spec (Multi.evalHom model.hom x.val) p q z
  dsimp only at hspec
  simpa only [e] using hspec

/-- The final lift skips base cells on which the common zero set is empty. -/
def intersection (model : RealModel K) : {n : ℕ} → Multi K n → Multi K n → List (Cell model n)
  | 0, p, q => filteredIntersection model p q
  | n+1, p, q =>
    let base := cad model n (project [p,q])
    base.cells.attach.flatMap fun b =>
      if pairCanMeet b.val p q then
        (lift b.val [p,q] (base.invariant b.val b.property)).cells.filter fun c =>
          c.sign p == .on && c.sign q == .on
      else []

theorem intersection_eq (model : RealModel K) (p q : Multi K n) :
    intersection model p q = filteredIntersection model p q := by
  cases n with
  | zero => rfl
  | succ n =>
    unfold intersection filteredIntersection
    rw [cad, List.filter_flatMap]
    apply List.flatMap_congr
    intro b _
    split
    · rfl
    · rename_i bad
      have hb : pairCanMeet b.val p q = false := Bool.eq_false_of_not_eq_true bad
      symm
      apply List.filter_eq_nil_iff.mpr
      intro c hc
      have bv := (lift b.val [p,q] _).base c hc c.sample.value c.sample_mem
      have sz := pairEmpty b.val p q ((cad model n (project [p,q])).invariant b.val b.property)
        hb ⟨dropLast c.sample.value,bv⟩ (last c.sample.value)
      by_contra! h
      rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, Cell.sign_correct, Cell.sign_correct] at h
      apply sz
      have eq (t : Poly K n) : (specialized model t (dropLast c.sample.value)).eval (last c.sample.value) =
          Multi.evalHom model.hom c.sample.value t := (PolynomialData.evalHom_correct _ _ t).symm
      have on (t : ℝ) (h : side t 0 = .on) : t = 0 :=
        (side_congr (K := ℝ) (h.trans (side_self (0 : ℝ)).symm)).2.1.mpr rfl
      exact ⟨IsRoot.def.mpr ((eq p).trans (on _ h.1)), IsRoot.def.mpr ((eq q).trans (on _ h.2))⟩

theorem intersection_nodup (model : RealModel K) (p q : Multi K n) :
    (intersection model p q).Nodup := by
  rw [intersection_eq]
  exact (cad_nodup model n [p,q]).filter _

theorem intersection_correct (model : RealModel K) (p q : Multi K n) (x : Fin n → ℝ) :
    Multi.evalHom model.hom x p = 0 ∧ Multi.evalHom model.hom x q = 0 ↔
      ∃! c, c ∈ intersection model p q ∧ x ∈ c.carrier := by
  rw [intersection_eq]
  let d := cad model n [p,q]
  have signOn (t : ℝ) : side t 0 = .on ↔ t = 0 := by
    rcases lt_trichotomy t 0 with h | rfl | h
    · simp [side, h, h.ne]
    · simp [side]
    · simp [side, h.not_gt, h.ne']
  constructor
  · intro h
    obtain ⟨c, ⟨hc,hx⟩, unique⟩ := d.partition x
    have hsign := d.invariant c hc x hx
    refine ⟨c,⟨List.mem_filter.mpr ⟨hc, ?_⟩,hx⟩,?_⟩
    · rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, ← hsign p (by simp), ← hsign q (by simp)]
      exact ⟨(signOn _).mpr h.1, (signOn _).mpr h.2⟩
    · rintro c' ⟨hc', hx'⟩
      exact unique c' ⟨(List.mem_filter.mp hc').1,hx'⟩
  · intro h
    obtain ⟨c,⟨hc,hx⟩⟩ := h.exists
    obtain ⟨hc, hsign⟩ := List.mem_filter.mp hc
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hsign
    have sign := d.invariant c hc x hx
    exact ⟨(signOn _).mp ((sign p (by simp)).trans hsign.1),
      (signOn _).mp ((sign q (by simp)).trans hsign.2)⟩

end CertifiedTopology.ComputableCAD
