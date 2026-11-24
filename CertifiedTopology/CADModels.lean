module

public import CertifiedTopology.CADStacks
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.LocallyClosed

@[expose] public section

namespace CertifiedTopology.CADStacks

open Set Topology

variable {n m : ℕ} {A : Set (Fin n → ℝ)} (c : Fin m → A → ℝ)

noncomputable def splitCoordinates (n : ℕ) : (Fin (n+1) → ℝ) ≃ₜ (Fin n → ℝ) × ℝ where
  toFun x := (dropLast x,last x)
  invFun p := Fin.snoc p.1 p.2
  left_inv := snoc_dropLast
  right_inv p := Prod.ext (by ext i; simp) (by simp)
  continuous_toFun := (continuous_pi fun i => continuous_apply i.castSucc).prodMk (continuous_apply _)
  continuous_invFun := continuous_snoc continuous_fst continuous_snd

def fibreDimension {T : Type} : Slice T → ℕ
  | .sectionAt _ => 0
  | .sector _ _ => 1

theorem fibreDimension_get {T : Type} (lo : Option T) (rs : List T) (i : ℕ)
    (hi : i < (slicesOf lo rs).length) :
    fibreDimension ((slicesOf lo rs).get ⟨i,hi⟩) = if i % 2 = 0 then 1 else 0 := by
  induction rs generalizing lo i with
  | nil =>
    have e : i = 0 := by simpa [slicesOf, Nat.lt_one_iff] using hi
    subst i
    rfl
  | cons a rs ih =>
    cases i with
    | zero => rfl
    | succ i =>
      cases i with
      | zero => rfl
      | succ i =>
        have he : (i+1+1) % 2 = i % 2 := by omega
        rw [he]
        exact ih (some a) i (by simpa [slicesOf] using hi)

noncomputable def regionBase (s : Slice (Fin m)) (x : region c s) : A :=
  ⟨dropLast x.val,x.property.choose⟩

theorem regionBase_continuous (s : Slice (Fin m)) : Continuous (regionBase c s) := by
  apply Continuous.subtype_mk
  exact continuous_pi fun i => (continuous_apply i.castSucc).comp continuous_subtype_val

noncomputable def sectionModel (i : Fin m) (h : Continuous (c i)) : region c (.sectionAt i) ≃ₜ A where
  toFun := regionBase c (.sectionAt i)
  invFun a := ⟨Fin.snoc a.val (c i a), (region_snoc c _ _ _).mpr ⟨a.property,rfl⟩⟩
  left_inv x := by
    apply Subtype.ext
    have hx : last x.val = c i (regionBase c (.sectionAt i) x) := x.property.choose_spec
    change Fin.snoc (dropLast x.val) (c i (regionBase c (.sectionAt i) x)) = x.val
    rw [← hx]
    exact snoc_dropLast x.val
  right_inv a := Subtype.ext (by ext j; simp [regionBase])
  continuous_toFun := regionBase_continuous c _
  continuous_invFun :=
    (continuous_snoc continuous_subtype_val h).subtype_mk _

noncomputable def sectorChart (l u : Option (Fin m)) (S : Set ℝ)
    (height inverse : A → ℝ → ℝ)
    (hc : Continuous fun p : A × ℝ => height p.1 p.2)
    (ic : Continuous fun p : A × ℝ => inverse p.1 p.2)
    (spec : ∀ a : A, ∀ y : ℝ,
      Univariate.contains (mapSlice (fun i => c i a) (.sector l u)) y ↔ inverse a y ∈ S)
    (li : ∀ a t, inverse a (height a t) = t)
    (ri : ∀ a y, height a (inverse a y) = y) :
    region c (.sector l u) ≃ₜ A × S where
  toFun x := ⟨regionBase c _ x, ⟨inverse (regionBase c _ x) (last x.val),
    (spec _ _).mp x.property.choose_spec⟩⟩
  invFun p := ⟨Fin.snoc p.1.val (height p.1 p.2.val), (region_snoc c _ _ _).mpr
    ⟨p.1.property,(spec _ _).mpr (li _ _ ▸ p.2.property)⟩⟩
  left_inv x := by
    apply Subtype.ext
    simp only [ri]
    exact snoc_dropLast x.val
  right_inv p := by
    have e : regionBase c (.sector l u)
        ⟨Fin.snoc p.1.val (height p.1 p.2.val), (region_snoc c _ _ _).mpr
          ⟨p.1.property,(spec _ _).mpr (li _ _ ▸ p.2.property)⟩⟩ = p.1 :=
      Subtype.ext (by ext j; simp [regionBase])
    exact Prod.ext e (Subtype.ext (by simp only [e, Fin.snoc_last, li]))
  continuous_toFun := (regionBase_continuous c _).prodMk
    ((ic.comp ((regionBase_continuous c _).prodMk
      ((continuous_apply (Fin.last n)).comp continuous_subtype_val))).subtype_mk _)
  continuous_invFun :=
    (continuous_snoc (continuous_subtype_val.comp continuous_fst)
      (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))).subtype_mk _

noncomputable def sectorModel (lo up : Option (Fin m)) (con : ∀ i, Continuous (c i))
    (ordered : ∀ x : A, StrictMono (fun i => c i x))
    (hbound : ∀ l u, lo = some l → up = some u → l < u) :
    region c (.sector lo up) ≃ₜ A × ℝ := by
  have h {i} := (con i).comp (continuous_fst (X := A) (Y := ℝ))
  cases lo with
  | none =>
    cases up with
    | none =>
      exact (sectorChart c none none univ (fun _ t => t) (fun _ t => t)
        continuous_snd continuous_snd (by simp [mapSlice, Univariate.contains, Slice.Contains])
        (by simp) (by simp)).trans ((Homeomorph.refl _).prodCongr (Homeomorph.Set.univ ℝ))
    | some u =>
      refine (sectorChart c none (some u) (Ioi 0) (fun a t => c u a - t) (fun a t => c u a - t)
        (h.sub continuous_snd) (h.sub continuous_snd) ?_ (by intros; ring) (by intros; ring)).trans
        ((Homeomorph.refl _).prodCongr Real.expOrderIso.toHomeomorph.symm)
      intro a t
      simp [mapSlice, Univariate.contains, Slice.Contains, Aff.eval, sub_pos]
  | some l =>
    cases up with
    | none =>
      refine (sectorChart c (some l) none (Ioi 0) (fun a t => c l a + t) (fun a t => t - c l a)
        (h.add continuous_snd) (continuous_snd.sub h) ?_ (by intros; ring) (by intros; ring)).trans
        ((Homeomorph.refl _).prodCongr Real.expOrderIso.toHomeomorph.symm)
      intro a t
      simp [mapSlice, Univariate.contains, Slice.Contains, Aff.eval, sub_pos]
    | some u =>
      let d (a : A) := c u a - c l a
      have hd (a : A) : 0 < d a := sub_pos.mpr (ordered a (hbound l u rfl rfl))
      let height (a : A) (t : ℝ) := c l a + ((t+1)/2)*d a
      let inverse (a : A) (t : ℝ) := 2*((t-c l a)/d a)-1
      have hD : Continuous (fun p : A × ℝ => d p.1) := (h (i := u)).sub (h (i := l))
      have cH : Continuous (fun p : A × ℝ => height p.1 p.2) :=
        h.add (((continuous_snd.add continuous_const).div_const _).mul hD)
      have cI : Continuous (fun p : A × ℝ => inverse p.1 p.2) :=
        (continuous_const.mul ((continuous_snd.sub h).div hD (fun p => (hd p.1).ne'))).sub continuous_const
      refine (sectorChart c (some l) (some u) (Ioo (-1) 1) height inverse cH cI ?_ ?_ ?_).trans
        ((Homeomorph.refl _).prodCongr (orderIsoIooNegOneOne ℝ).toHomeomorph.symm)
      · intro a t
        have eq : Univariate.contains (mapSlice (fun i => c i a) (.sector (some l) (some u))) t ↔
            c l a < t ∧ t < c u a := by simp [mapSlice, Univariate.contains, Slice.Contains, Aff.eval]
        rw [eq]
        change _ ↔ (-1 : ℝ) < 2*((t-c l a)/d a)-1 ∧ 2*((t-c l a)/d a)-1 < 1
        have low (z : ℝ) : -1 < 2*z-1 ↔ 0 < z := by constructor <;> intro hz <;> linarith
        have high (z : ℝ) : 2*z-1 < 1 ↔ z < 1 := by constructor <;> intro hz <;> linarith
        rw [low, high, div_pos_iff_of_pos_right (hd a), sub_pos, div_lt_one (hd a)]
        exact and_congr Iff.rfl (sub_lt_sub_iff_right _).symm
      · intro a t
        dsimp [height, inverse]
        field_simp [(hd a).ne']
        ring
      · intro a t
        dsimp [height, inverse]
        field_simp [(hd a).ne']
        ring

theorem locallyClosed_region (s : Slice (Fin m)) (hA : IsLocallyClosed A)
    (con : ∀ i, Continuous (c i)) : IsLocallyClosed (region c s) := by
  let chart (p : A × ℝ) : Fin (n+1) → ℝ := Fin.snoc p.1.val p.2
  let strip := {p : A × ℝ | Univariate.contains (mapSlice (fun i => c i p.1) s) p.2}
  have emb : IsEmbedding chart :=
    (splitCoordinates n).symm.isEmbedding.comp
      (IsEmbedding.subtypeVal.prodMap (Homeomorph.refl ℝ).isEmbedding)
  have proj : Continuous (@dropLast n) := continuous_pi fun i => continuous_apply i.castSucc
  have full : range chart = dropLast ⁻¹' A := by
    ext p
    constructor
    · rintro ⟨⟨a,t⟩,rfl⟩
      have eq : dropLast (Fin.snoc a.val t) = a.val := by ext i; simp
      change dropLast (Fin.snoc a.val t) ∈ A
      rw [eq]
      exact a.property
    · intro h
      exact ⟨(⟨dropLast p,h⟩,last p),snoc_dropLast p⟩
  have image_eq : chart '' strip = region c s := by
    ext p
    rw [← snoc_dropLast p, region_snoc]
    constructor
    · rintro ⟨⟨a,t⟩,ha,h⟩
      have h₁ : a.val = dropLast p := by
        funext i
        simpa [chart] using congrFun h i.castSucc
      have h₂ : t = last p := by simpa [chart] using congrFun h (Fin.last n)
      have hp : dropLast p ∈ A := h₁ ▸ a.property
      have ee : a = ⟨dropLast p,hp⟩ := Subtype.ext h₁
      exact ⟨hp,ee ▸ h₂ ▸ ha⟩
    · rintro ⟨hp,h⟩
      exact ⟨(⟨dropLast p,hp⟩,last p),h,rfl⟩
  rw [← image_eq]
  refine IsLocallyClosed.image ?_ emb.isInducing (full.symm ▸ hA.preimage proj)
  have cont (i : Fin m) : Continuous fun p : A × ℝ => c i p.1 := (con i).comp continuous_fst
  cases s with
  | sectionAt i => exact (isClosed_eq continuous_snd (cont i)).isLocallyClosed
  | sector l u =>
    apply IsOpen.isLocallyClosed
    cases l with
    | none =>
      cases u with
      | none =>
        have e : strip = univ := by ext x; simp [strip,mapSlice,Univariate.contains,Slice.Contains]
        rw [e]; exact isOpen_univ
      | some u =>
        have e : strip = {p | p.2 < c u p.1} := by
          ext x; simp [strip,mapSlice,Univariate.contains,Slice.Contains,Aff.eval]
        rw [e]; exact isOpen_lt continuous_snd (cont u)
    | some l =>
      cases u with
      | none =>
        have e : strip = {p | c l p.1 < p.2} := by
          ext x; simp [strip,mapSlice,Univariate.contains,Slice.Contains,Aff.eval]
        rw [e]; exact isOpen_lt (cont l) continuous_snd
      | some u =>
        have e : strip = {p | c l p.1 < p.2} ∩ {p | p.2 < c u p.1} := by
          ext x; simp [strip,mapSlice,Univariate.contains,Slice.Contains,Aff.eval]
        rw [e]; exact (isOpen_lt (cont l) continuous_snd).inter (isOpen_lt continuous_snd (cont u))

end CertifiedTopology.CADStacks
