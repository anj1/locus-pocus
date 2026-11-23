module

public import CertifiedTopology.Family
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace CertifiedTopology.Quadratic

def Kind.model : Kind → ℝ → Prop
  | .empty,_ => False
  | .line,_ => True
  | .point,t => t = 0
  | .twoPoints,t => t^2 = 1

private noncomputable def vertical {B : Type} [TopologicalSpace B] (center scale : B → ℝ)
    (hc : Continuous center) (hs : Continuous scale) (hn : ∀ x, scale x ≠ 0) :
    B × ℝ ≃ₜ B × ℝ where
  toFun := fun (x,t) => (x,center x + scale x*t)
  invFun := fun (x,t) => (x,(t-center x)/scale x)
  left_inv := by rintro ⟨x,t⟩; simp [hn]
  right_inv := by rintro ⟨x,t⟩; simp only [Prod.mk.injEq,true_and]; field_simp [hn x]; ring
  continuous_toFun := continuous_fst.prodMk ((hc.comp continuous_fst).add
    ((hs.comp continuous_fst).mul continuous_snd))
  continuous_invFun := continuous_fst.prodMk ((continuous_snd.sub (hc.comp continuous_fst)).div
    (hs.comp continuous_fst) fun z => hn z.1)

namespace Family

abbrev Base (s : Slice ℝ) := {x : ℝ // Univariate.contains s x}

/-- A single homeomorphism of the cylinder over a parameter cell identifies every zero fiber
    with the same model. It preserves the parameter coordinate exactly. -/
theorem trivialization (f : Family) (d : Isolation.Diagram f.projection)
    {row} (hr : row ∈ d.rows) :
    ∃ T : Base row.1 × ℝ ≃ₜ Base row.1 × ℝ, (∀ z, (T z).1 = z.1) ∧
      ∀ z, (kindOfSigns row.2).model z.2 ↔ f.value (T z).1.val (T z).2 = 0 := by
  let B := Base row.1
  let a (x : B) := f.a.eval x.val
  let b (x : B) := f.b.eval x.val
  let c (x : B) := f.c.eval x.val
  have ca : Continuous a := f.a.continuous.comp continuous_subtype_val
  have cb : Continuous b := f.b.continuous.comp continuous_subtype_val
  have cc : Continuous c := f.c.continuous.comp continuous_subtype_val
  have hk (x : B) : classify (a x) (b x) (c x) = kindOfSigns row.2 := by
    rw [← eval_kind, d.valid row hr x.val x.property]
  have realizes (x : B) := f.diagram_fiber d hr x.property
  cases hkind : kindOfSigns row.2 with
  | empty =>
    refine ⟨Homeomorph.refl _,fun _ => rfl,?_⟩
    rintro ⟨x,t⟩
    have h := realizes x
    rw [hkind] at h
    exact (iff_false_intro (h t)).symm
  | line =>
    refine ⟨Homeomorph.refl _,fun _ => rfl,?_⟩
    rintro ⟨x,t⟩
    have h := realizes x
    rw [hkind] at h
    exact ⟨fun _ => h t, fun _ => trivial⟩
  | point =>
    by_cases hz : ∃ x : B, a x = 0
    · obtain ⟨u,hu⟩ := hz
      have ha (x : B) : a x = 0 := by
        have he := (d.valid row hr x.val x.property).trans (d.valid row hr u.val u.property).symm
        have eq : side (a x) 0 = side (a u) 0 := (List.cons.inj he).1
        exact (side_congr eq).2.1.mpr hu
      have hb (x : B) : b x ≠ 0 := by
        intro e
        have h := (hk x).trans hkind
        simp [classify,ha x,e] at h
        split at h <;> contradiction
      let center (x : B) := -c x / b x
      refine ⟨vertical center (fun _ => 1) (cc.neg.div cb hb) continuous_const (by simp),
        fun _ => rfl,?_⟩
      rintro ⟨x,t⟩
      change t = 0 ↔ a x * ((center x + 1*t)*(center x + 1*t)) + b x * (center x + 1*t) + c x = 0
      simp only [ha,zero_mul,zero_add,center,one_mul]
      rw [mul_add, mul_div_cancel₀ _ (hb x)]
      constructor <;> intro h
      · simp [h]
      · exact (mul_eq_zero.mp (show b x*t = 0 by linarith)).resolve_left (hb x)
    · push Not at hz
      have hd (x : B) : discrim (a x) (b x) (c x) = 0 := by
        have h := (hk x).trans hkind
        simp [classify,hz x] at h
        split_ifs at h; simp_all
      let center (x : B) := -b x / (2*a x)
      refine ⟨vertical center (fun _ => 1) (cb.neg.div (continuous_const.mul ca)
        (fun x => mul_ne_zero two_ne_zero (hz x))) continuous_const (by simp),
        fun _ => rfl,?_⟩
      rintro ⟨x,t⟩
      change t = 0 ↔ a x * ((center x + 1*t)*(center x + 1*t)) + b x * (center x + 1*t) + c x = 0
      rw [quadratic_eq_zero_iff_of_discrim_eq_zero (hz x) (hd x)]
      simp [center]
  | twoPoints =>
    have good (x : B) : a x ≠ 0 ∧ 0 < discrim (a x) (b x) (c x) := by
      have h := (hk x).trans hkind
      unfold classify at h
      split_ifs at h; simp_all; order
    let D (x : B) := discrim (a x) (b x) (c x)
    let denom (x : B) := 2*a x
    let center (x : B) := -b x / denom x
    let scale (x : B) := Real.sqrt (D x) / denom x
    have cd : Continuous denom := continuous_const.mul ca
    have cn (x : B) : denom x ≠ 0 := mul_ne_zero two_ne_zero (good x).1
    have cD : Continuous D := (cb.pow 2).sub ((continuous_const.mul ca).mul cc)
    have sn (x : B) : scale x ≠ 0 := div_ne_zero ((Real.sqrt_pos.2 (good x).2).ne') (cn x)
    refine ⟨vertical center scale (cb.neg.div cd cn) ((Real.continuous_sqrt.comp cD).div cd cn) sn,
      fun _ => rfl,?_⟩
    rintro ⟨x,t⟩
    change t^2 = 1 ↔ a x * ((center x + scale x*t)*(center x + scale x*t)) + b x * (center x + scale x*t) + c x = 0
    rw [quadratic_eq_zero_iff_discrim_eq_sq (good x).1]
    have h : 2*a x*(center x + scale x*t) + b x = Real.sqrt (D x)*t := by
      dsimp only [center,scale,denom]
      field_simp [(good x).1]
      ring
    rw [h,mul_pow,Real.sq_sqrt (good x).2.le]
    change t^2 = 1 ↔ D x = D x * t^2
    constructor
    · rintro ht; simp [ht]
    · intro ht
      exact mul_left_cancel₀ (good x).2.ne' (by simpa using ht.symm : D x * t^2 = D x * 1)

end Family
end CertifiedTopology.Quadratic
