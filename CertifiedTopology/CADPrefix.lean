module

public import CertifiedTopology.ComputableCAD

@[expose] public section

namespace CertifiedTopology.ComputableCAD

open Set Topology ExecutableIsolation CylindricalData CADStacks

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {model : RealModel K}

def prefixPoint (d k : ℕ) (x : Fin (d+k) → ℝ) : Fin d → ℝ :=
  x ∘ Fin.castAdd k

theorem prefixPoint_continuous (d k : ℕ) : Continuous (prefixPoint d k) :=
  continuous_pi fun i => continuous_apply (Fin.castAdd k i)

theorem prefixPoint_open (d k : ℕ) : IsOpenMap (prefixPoint d k) := by
  have e : prefixPoint d k = Prod.fst ∘ (Fin.appendHomeomorph (X := ℝ) d k).symm := by
    funext x i
    rfl
  rw [e]
  exact isOpenMap_fst.comp (Fin.appendHomeomorph d k).symm.isOpenMap

theorem prefixPoint_drop (d k : ℕ) (x : Fin (d+k+1) → ℝ) :
    prefixPoint d k (dropLast x) = prefixPoint d (k+1) x := by
  funext i
  rfl

def prefixCode (d : ℕ) : (k : ℕ) → Code K (d+k) → Code K d
  | 0, c => c
  | k+1, .lift b _ _ => prefixCode d k b

theorem prefix_dimension (d : ℕ) : (k : ℕ) → (c : Code K (d+k)) →
    (prefixCode d k c).dimension ≤ c.dimension
  | 0, _ => le_rfl
  | k+1, .lift b _ _ => (prefix_dimension d k b).trans (Nat.le_add_right _ _)

theorem prefix_member (model : RealModel K) (d : ℕ) : (k : ℕ) → (c : Code K (d+k)) →
    (x : Fin (d+k) → ℝ) → x ∈ c.carrier model → prefixPoint d k x ∈ (prefixCode d k c).carrier model
  | 0, c, x, h => by
    change prefixPoint d 0 x ∈ c.carrier model
    exact h
  | k+1, .lift b _ _, x, h => by
    rw [← prefixPoint_drop]
    exact prefix_member model d k b (dropLast x) h.1

def projectPrefix (d : ℕ) : (k : ℕ) → List (Multi K (d+k)) → List (Multi K d)
  | 0, p => p
  | k+1, p => projectPrefix d k (project p)

theorem lift_code {n : ℕ} (b : Cell model n) (p : List (Poly K n))
    (inv : b.Invariant (project p)) {c : Cell model (n+1)} (h : c ∈ (lift b p inv).cells) :
    ∃ q i, c.code = .lift b.code q i := by
  change c ∈ rowCells b (stackSource b p) (sampleStack b p (stackSource b p)) (lift_valid b p inv).choose at h
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp h
  exact ⟨_,i.val,rfl⟩

theorem cad_prefix_mem (model : RealModel K) (d : ℕ) :
    (k : ℕ) → (ps : List (Multi K (d+k))) → (c : Cell model (d+k)) →
    c ∈ (cad model (d+k) ps).cells →
    ∃ b ∈ (cad model d (projectPrefix d k ps)).cells, prefixCode d k c.code = b.code
  | 0, _, c, hc => ⟨c,hc,rfl⟩
  | k+1, ps, c, hc => by
    let base := cad model (d+k) (project ps)
    let st (a : {a // a ∈ base.cells}) := lift a.val ps (base.invariant a.val a.property)
    change c ∈ base.cells.attach.flatMap (fun a => (st a).cells) at hc
    obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hc
    obtain ⟨q,i,hc⟩ := lift_code a.val ps _ ha
    obtain ⟨b,hb,eb⟩ := cad_prefix_mem model d k (project ps) a.val a.property
    refine ⟨b,hb,?_⟩
    rw [hc,prefixCode,eb]

theorem relative_closed_section {n m : ℕ} (A U : Set (Fin n → ℝ))
    (closed : IsClosed ((Subtype.val : U → Fin n → ℝ) ⁻¹' A))
    (g : Fin m → A → ℝ) (i : Fin m) (cont : Continuous (g i)) :
    IsClosed ((Subtype.val : (dropLast ⁻¹' U) → Fin (n+1) → ℝ) ⁻¹' region g (.sectionAt i)) := by
  let D := dropLast ⁻¹' U
  let E : Set D := (fun p : D => dropLast p.val) ⁻¹' A
  let base (p : D) : U := ⟨dropLast p.val,p.property⟩
  have cb : Continuous base :=
    (continuous_pi fun j => (continuous_apply j.castSucc).comp continuous_subtype_val).subtype_mk _
  have ec : IsClosed E := closed.preimage cb
  let down (p : E) : A := ⟨dropLast p.val.val,p.property⟩
  have cd : Continuous down :=
    (continuous_pi fun j => (continuous_apply j.castSucc).comp
      (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
  let H : Set E := {p | last p.val.val = g i (down p)}
  have hc : IsClosed H := isClosed_eq ((continuous_apply _).comp
    (continuous_subtype_val.comp continuous_subtype_val)) (cont.comp cd)
  have eq : ((Subtype.val : D → Fin (n+1) → ℝ) ⁻¹' region g (.sectionAt i)) = Subtype.val '' H := by
    ext p
    constructor
    · rintro ⟨hb,hs⟩
      exact ⟨⟨p,hb⟩,hs,rfl⟩
    · rintro ⟨⟨p,hp⟩,h,rfl⟩
      exact ⟨hp,h⟩
  rw [eq]
  exact ec.isClosedMap_subtype_val _ hc

theorem relative_closed_tail (model : RealModel K) (d : ℕ) :
    (k : ℕ) → (c : Code K (d+k)) → ContinuousLayers model c →
    c.dimension = (prefixCode d k c).dimension →
    IsClosed ((Subtype.val : (prefixPoint d k ⁻¹' (prefixCode d k c).carrier model) → Fin (d+k) → ℝ) ⁻¹'
      c.carrier model)
  | 0, c, _, _ => by
    let T := prefixPoint d 0 ⁻¹' (prefixCode d 0 c).carrier model
    have e : ((Subtype.val : T → Fin d → ℝ) ⁻¹' c.carrier model) = univ := by
      ext x
      exact iff_of_true x.property (mem_univ _)
    change IsClosed ((Subtype.val : T → Fin d → ℝ) ⁻¹' c.carrier model)
    rw [e]
    exact isClosed_univ
  | k+1, .lift b p i, h, hd => by
    have hs := prefix_dimension d k b
    change b.dimension + (if i % 2 = 0 then 1 else 0) = (prefixCode d k b).dimension at hd
    have odd : i % 2 ≠ 0 := by intro he; simp [he] at hd; omega
    have hb : b.dimension = (prefixCode d k b).dimension := by simpa [odd] using hd
    let U := prefixPoint d k ⁻¹' (prefixCode d k b).carrier model
    have down := relative_closed_tail model d k b h.1 hb
    obtain ⟨m,s,g,eq,dim,cont⟩ := h.2
    have dim0 : fibreDimension s = 0 := by simpa [odd] using dim
    have cylinder : prefixPoint d (k+1) ⁻¹' (prefixCode d k b).carrier model = dropLast ⁻¹' U := by
      ext x
      exact Iff.of_eq (congrArg (· ∈ (prefixCode d k b).carrier model) (prefixPoint_drop d k x).symm)
    change IsClosed ((Subtype.val :
      (prefixPoint d (k+1) ⁻¹' (prefixCode d k b).carrier model) → Fin (d+k+1) → ℝ) ⁻¹'
      (Code.lift b p i).carrier model)
    rw [eq,cylinder]
    cases s with
    | sectionAt j => exact relative_closed_section _ _ down g j (cont j)
    | sector l u => contradiction

end CertifiedTopology.ComputableCAD
