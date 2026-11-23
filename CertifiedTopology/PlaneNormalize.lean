module

public import CertifiedTopology.PlaneCharts

@[expose] public section

namespace CertifiedTopology.Plane

variable {B : Type} [TopologicalSpace B]

/-- A vertical change of coordinates on a cylinder. -/
structure Vertical (B : Type) [TopologicalSpace B] where
  homeo : B × ℝ ≃ₜ B × ℝ
  base : ∀ p, (homeo p).1 = p.1

namespace Vertical

def height (T : Vertical B) (x : B) (y : ℝ) : ℝ := (T.homeo (x,y)).2

theorem height_injective (T : Vertical B) (x : B) : Function.Injective (T.height x) := by
  intro a b h
  have eq : T.homeo (x,a) = T.homeo (x,b) :=
    Prod.ext ((T.base (x,a)).trans (T.base (x,b)).symm) h
  exact congrArg Prod.snd (T.homeo.injective eq)

def refl (B : Type) [TopologicalSpace B] : Vertical B := ⟨Homeomorph.refl _, fun _ => rfl⟩

def trans (T U : Vertical B) : Vertical B :=
  ⟨T.homeo.trans U.homeo, fun p => (U.base (T.homeo p)).trans (T.base p)⟩

theorem trans_height (T U : Vertical B) (x : B) (t : ℝ) :
    (T.trans U).height x t = U.height x (T.height x t) := by
  have he : T.homeo (x,t) = (x,T.height x t) := Prod.ext (T.base (x,t)) rfl
  change (U.homeo (T.homeo (x,t))).2 = _
  rw [he]
  rfl

noncomputable def hinge (a k t : ℝ) := min t a + k * max (t-a) 0

private theorem hinge_left {a k t : ℝ} (h : t ≤ a) : hinge a k t = t := by
  simp [hinge, min_eq_left h, max_eq_right (sub_nonpos.mpr h)]

private theorem hinge_right {a k t : ℝ} (h : a ≤ t) : hinge a k t = a + k*(t-a) := by
  simp [hinge, min_eq_right h, max_eq_left (sub_nonneg.mpr h)]

private theorem hinge_ge {a k t : ℝ} (hk : 0 < k) (h : a ≤ t) : a ≤ hinge a k t := by
  rw [hinge_right h]
  linarith [mul_nonneg hk.le (sub_nonneg.mpr h)]

theorem hinge_one (a t : ℝ) : hinge a 1 t = t := by
  rcases le_total t a with h | h
  · exact hinge_left h
  · rw [hinge_right h, one_mul, add_sub_cancel]

theorem hinge_inverse (a k t : ℝ) (hk : 0 < k) : hinge a k⁻¹ (hinge a k t) = t := by
  rcases le_total t a with h | h
  · rw [hinge_left h, hinge_left h]
  · rw [hinge_right (hinge_ge hk h), hinge_right h]
    rw [add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul, add_sub_cancel]

/-- Scale distances above a moving anchor by a positive factor. Points below
    the anchor are fixed. The inverse uses the reciprocal factor. -/
noncomputable def scaleAbove (a k : B → ℝ) (ha : Continuous a) (hk : Continuous k)
    (hpos : ∀ x, 0 < k x) : Vertical B where
  homeo :=
    { toFun := fun p => (p.1, hinge (a p.1) (k p.1) p.2)
      invFun := fun p => (p.1, hinge (a p.1) (k p.1)⁻¹ p.2)
      left_inv := fun p => Prod.ext rfl (hinge_inverse _ _ _ (hpos p.1))
      right_inv := by
        intro p
        refine Prod.ext rfl ?_
        simpa only [inv_inv] using hinge_inverse (a p.1) (k p.1)⁻¹ p.2 (inv_pos.mpr (hpos p.1))
      continuous_toFun := by
        unfold hinge
        fun_prop
      continuous_invFun := by
        have hkinv : Continuous fun x => (k x)⁻¹ := hk.inv₀ fun x => (hpos x).ne'
        exact continuous_fst.prodMk
          ((continuous_snd.min (ha.comp continuous_fst)).add
            ((hkinv.comp continuous_fst).mul
              ((continuous_snd.sub (ha.comp continuous_fst)).max continuous_const))) }
  base := fun _ => rfl

theorem scaleAbove_left (a k : B → ℝ) (ha : Continuous a) (hk : Continuous k)
    (hp : ∀ x, 0 < k x) (x : B) {t : ℝ} (ht : t ≤ a x) :
    (scaleAbove a k ha hk hp).height x t = t := hinge_left ht

theorem scaleAbove_right (a k : B → ℝ) (ha : Continuous a) (hk : Continuous k)
    (hp : ∀ x, 0 < k x) (x : B) {t : ℝ} (ht : a x ≤ t) :
    (scaleAbove a k ha hk hp).height x t = a x + k x * (t-a x) := hinge_right ht

noncomputable def matchAboveWithFixed {n : ℕ} (a b : Fin n → B → ℝ) (anchor : B → ℝ)
    (ha : ∀ i, Continuous (a i)) (hb : ∀ i, Continuous (b i)) (hc : Continuous anchor)
    (oa : ∀ x, StrictMono fun i => a i x) (ob : ∀ x, StrictMono fun i => b i x)
    (pa : ∀ x i, anchor x < a i x) (pb : ∀ x i, anchor x < b i x) :
    {T : Vertical B // (∀ x t, t ≤ anchor x → T.height x t = t) ∧
      (∀ x i, T.height x (a i x) = b i x) ∧
      (∀ x, (∀ i, a i x = b i x) → ∀ t, T.height x t = t)} := by
  induction n generalizing anchor with
  | zero => exact ⟨refl B, fun _ _ _ => rfl, fun _ i => Fin.elim0 i, fun _ _ _ => rfl⟩
  | succ n ih =>
    let k (x : B) := (b 0 x - anchor x) / (a 0 x - anchor x)
    have hk : Continuous k := ((hb 0).sub hc).div ((ha 0).sub hc)
      fun x => (sub_pos.mpr (pa x 0)).ne'
    have pk (x : B) : 0 < k x := div_pos (sub_pos.mpr (pb x 0)) (sub_pos.mpr (pa x 0))
    let S := scaleAbove anchor k hc hk pk
    have rule (x : B) (i : Fin (n+1)) :
        S.height x (a i x) = anchor x + k x * (a i x - anchor x) :=
      scaleAbove_right _ _ _ _ _ _ (pa x i).le
    have atFirst (x : B) : S.height x (a 0 x) = b 0 x := by
      rw [rule]
      simp [k, div_mul_cancel₀ _ (sub_pos.mpr (pa x 0)).ne']
    have mon (x : B) : StrictMono fun i => S.height x (a i x) := by
      intro i j hij
      change S.height x (a i x) < S.height x (a j x)
      rw [rule, rule]
      exact add_lt_add_right (mul_lt_mul_of_pos_left (sub_lt_sub_right (oa x hij) _) (pk x)) _
    let aa (i : Fin n) (x : B) := S.height x (a i.succ x)
    let bb (i : Fin n) (x : B) := b i.succ x
    have ca (i : Fin n) : Continuous (aa i) :=
      (S.homeo.continuous.comp (continuous_id.prodMk (ha i.succ))).snd
    have oa' (x : B) : StrictMono fun i => aa i x := (mon x).comp Fin.strictMono_succ
    have ob' (x : B) : StrictMono fun i => bb i x := (ob x).comp Fin.strictMono_succ
    have ha' (x : B) (i : Fin n) : b 0 x < aa i x := by
      rw [← atFirst]
      exact mon x (Fin.succ_pos i)
    have hb' (x : B) (i : Fin n) : b 0 x < bb i x := ob x (Fin.succ_pos i)
    let result := ih aa bb (b 0) ca (fun i => hb i.succ) (hb 0) oa' ob' ha' hb'
    let T := result.val
    have hfix := result.property.1
    have hmatch := result.property.2.1
    refine ⟨S.trans T, ?_, ?_, ?_⟩
    · intro x t ht
      rw [trans_height, scaleAbove_left _ _ _ _ _ _ ht, hfix x t (ht.trans (pb x 0).le)]
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [trans_height, atFirst, hfix x _ le_rfl]
      · rw [trans_height]
        exact hmatch x j
    · intro x h t
      have hk' : k x = 1 := by
        dsimp [k]
        rw [h 0, div_self (sub_pos.mpr (pb x 0)).ne']
      have hS (u : ℝ) : S.height x u = u := by
        change hinge (anchor x) (k x) u = u
        rw [hk', hinge_one]
      have hab (i : Fin n) : aa i x = bb i x := by
        change S.height x (a i.succ x) = b i.succ x
        rw [hS, h]
      rw [trans_height, hS, result.property.2.2 x hab]

/-- Match two finite, continuously moving, ordered configurations by an ambient
    homeomorphism that preserves the base coordinate. -/
noncomputable def matchSectionsWithFixed {n : ℕ} (a b : Fin n → B → ℝ)
    (ha : ∀ i, Continuous (a i)) (hb : ∀ i, Continuous (b i))
    (oa : ∀ x, StrictMono fun i => a i x) (ob : ∀ x, StrictMono fun i => b i x) :
    {T : Vertical B // (∀ x i, T.height x (a i x) = b i x) ∧
      (∀ x, (∀ i, a i x = b i x) → ∀ t, T.height x t = t)} := by
  cases n with
  | zero => exact ⟨refl B, fun _ i => Fin.elim0 i, fun _ _ _ => rfl⟩
  | succ n =>
    let anchor (x : B) := min (a 0 x) (b 0 x) - 1
    have hc : Continuous anchor := ((ha 0).min (hb 0)).sub continuous_const
    have h (x : B) : anchor x < min (a 0 x) (b 0 x) := by dsimp [anchor]; linarith
    have pa (x : B) (i : Fin (n+1)) : anchor x < a i x :=
      (h x).trans_le ((min_le_left _ _).trans ((oa x).monotone (Fin.zero_le i)))
    have pb (x : B) (i : Fin (n+1)) : anchor x < b i x :=
      (h x).trans_le ((min_le_right _ _).trans ((ob x).monotone (Fin.zero_le i)))
    let T := matchAboveWithFixed a b anchor ha hb hc oa ob pa pb
    exact ⟨T.val,T.property.2⟩

noncomputable def matchAbove {n : ℕ} (a b : Fin n → B → ℝ) (anchor : B → ℝ)
    (ha : ∀ i, Continuous (a i)) (hb : ∀ i, Continuous (b i)) (hc : Continuous anchor)
    (oa : ∀ x, StrictMono fun i => a i x) (ob : ∀ x, StrictMono fun i => b i x)
    (pa : ∀ x i, anchor x < a i x) (pb : ∀ x i, anchor x < b i x) :
    {T : Vertical B // (∀ x t, t ≤ anchor x → T.height x t = t) ∧
      ∀ x i, T.height x (a i x) = b i x} :=
  let T := matchAboveWithFixed a b anchor ha hb hc oa ob pa pb
  ⟨T.val, T.property.1, T.property.2.1⟩

noncomputable def matchSections {n : ℕ} (a b : Fin n → B → ℝ)
    (ha : ∀ i, Continuous (a i)) (hb : ∀ i, Continuous (b i))
    (oa : ∀ x, StrictMono fun i => a i x) (ob : ∀ x, StrictMono fun i => b i x) :
    {T : Vertical B // ∀ x i, T.height x (a i x) = b i x} :=
  let T := matchSectionsWithFixed a b ha hb oa ob
  ⟨T.val, T.property.1⟩

end Vertical
end CertifiedTopology.Plane
