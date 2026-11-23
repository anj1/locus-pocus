module

public import CertifiedTopology.PlaneProjection
public import CertifiedTopology.Quadric

@[expose] public section

namespace CertifiedTopology.Quadric

open Plane (BiPoly value value_mul value_add value_sub value_pow)
open Polynomial

namespace Equation

noncomputable def linearPoly {K : Type} [Semiring K] (q : Equation K) : BiPoly K :=
  C (C q.xz * X + C q.z) + C (C q.yz) * X

noncomputable def offsetPoly {K : Type} [Semiring K] (q : Equation K) : BiPoly K :=
  C (C q.xx * X^2 + C q.x * X + C q.constant) +
    C (C q.xy * X + C q.y) * X + C (C q.yy) * X^2

end Equation


private theorem value_linear (q : Equation ℝ) (p : Plane) :
    value q.linearPoly p = q.linear p.1 p.2 := by
  simp [Plane.value_hom, Equation.linearPoly, Plane.specialize, Polynomial.mapRingHom, Equation.linear]
  ring

private theorem value_offset (q : Equation ℝ) (p : Plane) :
    value q.offsetPoly p = q.offset p.1 p.2 := by
  simp [Plane.value_hom, Equation.offsetPoly, Plane.specialize, Polynomial.mapRingHom, Equation.offset]
  ring

/-- A section height consists of a rational function and an optional radical term. -/
inductive Height where
  | quotient (slope offset : BiPoly ℝ)
  | radical (a : ℝ) (slope disc : BiPoly ℝ) (upper : Bool)

noncomputable def Height.eval (h : Height) (p : Plane) : ℝ :=
  match h with
  | .quotient b c => -value c p / value b p
  | .radical a b d upper =>
    let center := -value b p / (2*a)
    let radius := Real.sqrt (value d p) / |2*a|
    if upper then center + radius else center - radius

/-- The program branches only on signs of explicit planar polynomials. -/
inductive Program (K : Type := ℝ) [Semiring K]
  | empty
  | line
  | quotient (slope offset : BiPoly K)
  | quadratic (a : K) (slope disc : BiPoly K)
  | testZero (f : BiPoly K) (onZero onNonzero : Program K)

inductive Shape
  | sections (heights : List Height)
  | line

noncomputable def Shape.eval : Shape → Plane → ℝ → Prop
  | .sections hs, p, t => ∃ h ∈ hs, t = h.eval p
  | .line, _, _ => True

def Program.projection {K : Type} [Semiring K] : Program K → List (BiPoly K)
  | .empty | .line => []
  | .quotient b _ => [b]
  | .quadratic _ _ d => [d]
  | .testZero f y n => f :: (y.projection ++ n.projection)

noncomputable def Program.select : Program → Plane → Shape
  | .empty, _ => .sections []
  | .line, _ => .line
  | .quotient b c, p =>
    if value b p = 0 then .sections [] else .sections [.quotient b c]
  | .quadratic a b d, p =>
    if value d p < 0 then .sections []
    else if value d p = 0 then .sections [.quotient (C (C (2*a))) b]
    else .sections [.radical a b d false, .radical a b d true]
  | .testZero f y n, p => if value f p = 0 then y.select p else n.select p

/-- A constant guard can be discharged before any planar projection. -/
noncomputable def Program.test {K : Type} [Semiring K] [DecidableEq K]
    (f : BiPoly K) (y n : Program K) : Program K :=
  match Plane.constant? f with
  | none => .testZero f y n
  | some a => if a = 0 then y else n

private theorem Program.select_test (f : BiPoly ℝ) (y n : Program) (p : Plane) :
    (Program.test f y n).select p =
      if value f p = 0 then y.select p else n.select p := by
  unfold test
  split
  · rfl
  · next a h =>
    rw [Plane.constant?_correct h p]
    split_ifs <;> rfl

noncomputable def quadraticProgram {K : Type} [CommRing K] [DecidableEq K]
    (q r : Equation K) : Program K :=
  let a := q.zz
  let b := q.linearPoly
  let c := q.offsetPoly
  let l := C (C a) * r.linearPoly - C (C r.zz) * b
  let m := C (C a) * r.offsetPoly - C (C r.zz) * c
  let d := b^2 - C (C (4*a)) * c
  let h := C (C a) * m^2 - b*m*l + c*l^2
  .test l (.test m (.quadratic a b d) .empty)
    (.test h (.quotient l m) .empty)

noncomputable def linearProgram {K : Type} [CommRing K] [DecidableEq K]
    (q r : Equation K) : Program K :=
  let b := q.linearPoly
  let c := q.offsetPoly
  let e := r.linearPoly
  let f := r.offsetPoly
  .test b (.test c (.test e (.test f .line .empty) (.quotient e f)) .empty)
    (.test (b*f-e*c) (.quotient b c) .empty)

noncomputable def program {K : Type} [CommRing K] [DecidableEq K]
    (q r : Equation K) : Program K :=
  if q.zz = 0 then
    if r.zz = 0 then linearProgram q r else quadraticProgram r q
  else quadraticProgram q r

section Embedding

variable {K : Type} [Field K] (ι : K →+* ℝ)

private theorem embed_C (p : Polynomial K) :
    Plane.embedCoefficients ι (C p) = C (p.map ι) :=
  Polynomial.map_C _

private theorem embed_X : Plane.embedCoefficients ι (X : BiPoly K) = X :=
  Polynomial.map_X _

/-- Interpret an exact coefficient-field program in the real plane. -/
noncomputable def Program.embed : Program K → Program ℝ
  | .empty => .empty
  | .line => .line
  | .quotient b c => .quotient (Plane.embedCoefficients ι b) (Plane.embedCoefficients ι c)
  | .quadratic a b d => .quadratic (ι a) (Plane.embedCoefficients ι b) (Plane.embedCoefficients ι d)
  | .testZero f y n => .testZero (Plane.embedCoefficients ι f) (embed y) (embed n)

theorem Program.projection_embed (p : Program K) :
    (p.embed ι).projection = p.projection.map (Plane.embedCoefficients ι) := by
  induction p <;> simp_all [embed, projection]

private theorem map_linearPoly (q : Equation K) :
    Plane.embedCoefficients ι q.linearPoly = (q.map ι).linearPoly := by
  simp [Equation.linearPoly, Equation.map, embed_C, embed_X]

private theorem map_offsetPoly (q : Equation K) :
    Plane.embedCoefficients ι q.offsetPoly = (q.map ι).offsetPoly := by
  simp [Equation.offsetPoly, Equation.map, embed_C, embed_X]

private theorem constant?_embed (f : BiPoly K) :
    Plane.constant? (Plane.embedCoefficients ι f) = (Plane.constant? f).map ι := by
  have injective : Function.Injective (mapRingHom ι) := Polynomial.map_injective _ ι.injective
  have em (t : Polynomial K) : mapRingHom ι t = t.map ι := rfl
  change Plane.constant? (f.map (mapRingHom ι)) = _
  simp only [Plane.constant?, natDegree_map_eq_of_injective injective, coeff_map, em,
    natDegree_map_eq_of_injective ι.injective]
  split_ifs <;> rfl

variable [DecidableEq K]

private theorem Program.test_embed (f : BiPoly K) (y n : Program K) :
    (Program.test f y n).embed ι =
      Program.test (Plane.embedCoefficients ι f) (y.embed ι) (n.embed ι) := by
  simp only [test, constant?_embed]
  cases Plane.constant? f with
  | none => rfl
  | some a =>
    simp only [Option.map_some, map_eq_zero]
    split_ifs <;> rfl

private theorem quadraticProgram_embed (q r : Equation K) :
    (quadraticProgram q r).embed ι = quadraticProgram (q.map ι) (r.map ι) := by
  simp [quadraticProgram, Program.test_embed, Program.embed, embed_C, map_linearPoly,
    map_offsetPoly, map_ofNat]

private theorem linearProgram_embed (q r : Equation K) :
    (linearProgram q r).embed ι = linearProgram (q.map ι) (r.map ι) := by
  simp [linearProgram, Program.test_embed, Program.embed, map_linearPoly, map_offsetPoly]

theorem program_embed (q r : Equation K) :
    (program q r).embed ι = program (q.map ι) (r.map ι) := by
  by_cases hq : q.zz = 0
  · by_cases hr : r.zz = 0
    · simpa only [program, Equation.zz_map, map_eq_zero, hq, hr, ite_true]
        using linearProgram_embed ι q r
    · simpa only [program, Equation.zz_map, map_eq_zero, hq, hr, ite_true, ite_false]
        using quadraticProgram_embed ι r q
  · simpa only [program, Equation.zz_map, map_eq_zero, hq, ite_false]
      using quadraticProgram_embed ι q r

theorem projection_embed (q r : Equation K) :
    (program (q.map ι) (r.map ι)).projection =
      (program q r).projection.map (Plane.embedCoefficients ι) := by
  rw [← program_embed, Program.projection_embed]

end Embedding

private theorem value_const (p : Plane) (v : ℝ) : value (C (C v)) p = v := by
  simp [Plane.value_hom, Plane.specialize, Polynomial.mapRingHom]

private theorem shape_empty (p : Plane) (t : ℝ) :
    (Shape.sections []).eval p t ↔ False := by simp [Shape.eval]

private theorem shape_single (p : Plane) (t : ℝ) (h : Height) :
    (Shape.sections [h]).eval p t ↔ t = h.eval p := by simp [Shape.eval]

private theorem shape_pair (p : Plane) (t : ℝ) (a b : Height) :
    (Shape.sections [a,b]).eval p t ↔ t = a.eval p ∨ t = b.eval p := by
  simp [Shape.eval, or_and_right, exists_or]

private theorem quadraticProgram_correct (q r : Equation ℝ) (p : Plane) (t : ℝ) :
    ((quadraticProgram q r).select p).eval p t ↔
      (quadraticPivot q r p.1 p.2).Contains t := by
  simp only [quadraticProgram, quadraticPivot_eq, Program.select_test, Program.select, value_mul, value_sub,
    value_add, value_pow, value_const, value_linear, value_offset, slope, remainder,
    numerator, quadraticFiber, quadraticRoots, discrim]
  split_ifs <;> simp_all [shape_empty, shape_single, shape_pair, Height.eval, Fiber.Contains, Roots.overReal,
    value_mul, value_sub, value_linear, value_offset, value_pow, not_lt.mpr]

private theorem linearProgram_correct (q r : Equation ℝ) (p : Plane) (t : ℝ) :
    ((linearProgram q r).select p).eval p t ↔ (linearPivot q r p.1 p.2).Contains t := by
  simp only [linearProgram, linearPivot_eq, Program.select_test, Program.select, value_mul, value_sub,
    value_linear, value_offset]
  split_ifs <;> simp_all [Shape.eval, Height.eval, Fiber.Contains,
    value_linear, value_offset]

theorem program_correct (q r : Equation ℝ) (p : Plane) (t : ℝ) :
    ((program q r).select p).eval p t ↔ q.eval p.1 p.2 t = 0 ∧ r.eval p.1 p.2 t = 0 := by
  rw [← fiber_correct q r p.1 p.2 t]
  by_cases hq : q.zz = 0
  · by_cases hr : r.zz = 0
    · simpa only [program, fiber, roots, hq, hr, ite_true, linearPivot] using
        linearProgram_correct q r p t
    · simpa only [program, fiber, roots, hq, hr, ite_true, ite_false, quadraticPivot] using
        quadraticProgram_correct r q p t
  · simpa only [program, fiber, roots, hq, ite_false, quadraticPivot] using
      quadraticProgram_correct q r p t


private def InvariantOn (c : CertifiedTopology.Plane.Cell) (ps : List (BiPoly ℝ)) : Prop :=
  ∀ p ∈ c.carrier, ∀ f ∈ ps, side (value f p) 0 = side (value f c.sample) 0

private theorem Program.select_stable (prog : Program) (c : CertifiedTopology.Plane.Cell)
    (h : InvariantOn c prog.projection) (p : Plane) (hp : p ∈ c.carrier) :
    prog.select p = prog.select c.sample := by
  induction prog with
  | empty | line => rfl
  | quotient b c' =>
    have h₀ := (side_congr (h p hp b (by simp [projection]))).2.1
    simp [select, h₀]
  | quadratic a b d =>
    have h₀ := side_congr (h p hp d (by simp [projection]))
    simp [select, h₀.1, h₀.2.1]
  | testZero f y n iy ineg =>
    have h₀ := (side_congr (h p hp f (by simp [projection]))).2.1
    simp only [select, h₀]
    split_ifs
    · exact iy fun v hv g hg => h v hv g (by simp [projection, hg])
    · exact ineg fun v hv g hg => h v hv g (by simp [projection, hg])

private theorem continuous_quotient (c : CertifiedTopology.Plane.Cell) (b d : BiPoly ℝ)
    (h : ∀ p ∈ c.carrier, value b p ≠ 0) :
    Continuous fun p : c.carrier => (Height.quotient b d).eval p.1 := by
  exact ((Plane.continuous_value d).comp continuous_subtype_val).neg.div
    ((Plane.continuous_value b).comp continuous_subtype_val) fun p => h p.1 p.2

private theorem continuous_radical (c : CertifiedTopology.Plane.Cell) (a : ℝ)
    (b d : BiPoly ℝ) (upper : Bool) :
    Continuous fun p : c.carrier => (Height.radical a b d upper).eval p.1 := by
  have cb := (Plane.continuous_value b).comp (continuous_subtype_val (p := fun p => p ∈ c.carrier))
  have cd := (Plane.continuous_value d).comp (continuous_subtype_val (p := fun p => p ∈ c.carrier))
  have center := cb.neg.div_const (2*a)
  have radius := (Real.continuous_sqrt.comp cd).div_const |2*a|
  cases upper
  · exact center.sub radius
  · exact center.add radius

private def Program.Valid : Program → Prop
  | .quadratic a _ _ => a ≠ 0
  | .testZero _ y n => y.Valid ∧ n.Valid
  | _ => True

private theorem Program.valid_test (f : BiPoly ℝ) (y n : Program)
    (hy : y.Valid) (hn : n.Valid) : (test f y n).Valid := by
  unfold test
  split
  · exact ⟨hy, hn⟩
  · split_ifs <;> assumption

private theorem program_valid (q r : Equation ℝ) : (program q r).Valid := by
  have quad (a b : Equation ℝ) (ha : a.zz ≠ 0) : (quadraticProgram a b).Valid := by
    unfold quadraticProgram
    exact Program.valid_test _ _ _ (Program.valid_test _ _ _ ha trivial)
      (Program.valid_test _ _ _ trivial trivial)
  have lin : (linearProgram q r).Valid := by
    unfold linearProgram
    exact Program.valid_test _ _ _
      (Program.valid_test _ _ _
        (Program.valid_test _ _ _ (Program.valid_test _ _ _ trivial trivial) trivial) trivial)
      (Program.valid_test _ _ _ trivial trivial)
  unfold program
  split_ifs
  · exact lin
  · exact quad r q (by assumption)
  · exact quad q r (by assumption)

private theorem Program.sections_valid (prog : Program) (c : CertifiedTopology.Plane.Cell)
    (hs : InvariantOn c prog.projection) (hv : prog.Valid)
    {rs : List Height} (hr : prog.select c.sample = .sections rs) :
    (∀ h ∈ rs, Continuous fun p : c.carrier => h.eval p.1) ∧
    ∀ p ∈ c.carrier, rs.Pairwise (fun l u => l.eval p < u.eval p) := by
  induction prog generalizing rs with
  | empty =>
    cases hr
    simp
  | line => cases hr
  | quotient b d =>
    simp only [select] at hr
    split at hr
    · cases hr; simp
    · rename_i hn
      cases hr
      simp only [List.mem_singleton, forall_eq, List.pairwise_singleton, implies_true, and_true]
      apply continuous_quotient
      intro p hp
      exact (side_congr (hs p hp b (by simp [projection]))).2.1.not.mpr hn
  | quadratic a b d =>
    have ha : a ≠ 0 := hv
    simp only [select] at hr
    split_ifs at hr with hneg hz
    · cases hr; simp
    · cases hr
      simp only [List.mem_singleton, forall_eq, List.pairwise_singleton, implies_true, and_true]
      apply continuous_quotient
      intro p _
      rw [value_const]
      exact mul_ne_zero two_ne_zero ha
    · cases hr
      constructor
      · intro h hh
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
        rcases hh with rfl | rfl <;> apply continuous_radical
      · intro p hp
        have he := side_congr (hs p hp d (by simp [projection]))
        have hd : 0 < value d p := (he.2.2).mpr (lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hz))
        have radius : 0 < Real.sqrt (value d p) / |2*a| :=
          div_pos (Real.sqrt_pos.mpr hd) (abs_pos.mpr (mul_ne_zero two_ne_zero ha))
        constructor
        · intro h hh
          rw [List.mem_singleton] at hh
          subst h
          change (-value b p / (2*a) - Real.sqrt (value d p) / |2*a|) <
            (-value b p / (2*a) + Real.sqrt (value d p) / |2*a|)
          linarith
        · exact List.pairwise_singleton _ _
  | testZero f y n iy ineg =>
    simp only [select] at hr
    split at hr
    · exact iy (fun p hp g hg => hs p hp g (by simp [projection, hg])) hv.1 hr
    · exact ineg (fun p hp g hg => hs p hp g (by simp [projection, hg])) hv.2 hr

/-- A cell of the common zero set is either a graph or a full vertical cylinder. -/
structure Cell where
  base : CertifiedTopology.Plane.Cell
  height : Option Height

def Cell.carrier (c : Cell) : Set Space := {p | p.1 ∈ c.base.carrier ∧
  ∀ h ∈ c.height, p.2 = h.eval p.1}

noncomputable def Cell.sample (c : Cell) : Space :=
  (c.base.sample, c.height.elim 0 (fun h => h.eval c.base.sample))

theorem Cell.sample_mem (c : Cell) : c.sample ∈ c.carrier := by
  cases c with
  | mk b h =>
    cases h <;> simp [Cell.sample, Cell.carrier, b.sample_mem]

theorem Cell.base_projection (c : Cell) (p : Plane) :
    (∃ z, (p,z) ∈ c.carrier) ↔ p ∈ c.base.carrier := by
  constructor
  · rintro ⟨z,hz⟩
    exact hz.1
  · intro hp
    cases h : c.height with
    | none => exact ⟨0,hp,by simp [h]⟩
    | some f => exact ⟨f.eval p,hp,by simp [h]⟩

theorem Cell.image_fst (c : Cell) : Prod.fst '' c.carrier = c.base.carrier := by
  ext p
  constructor
  · rintro ⟨⟨b, z⟩, h, rfl⟩
    exact h.1
  · intro hp
    obtain ⟨z, hz⟩ := (c.base_projection p).mpr hp
    exact ⟨(p, z), hz, rfl⟩

def liftShape (b : CertifiedTopology.Plane.Cell) : Shape → List Cell
  | .sections hs => hs.map (fun h => ⟨b, some h⟩)
  | .line => [⟨b, none⟩]

private theorem mem_liftShape (b : CertifiedTopology.Plane.Cell) (s : Shape) (p : Space) :
    (∃ c ∈ liftShape b s, p ∈ c.carrier) ↔ p.1 ∈ b.carrier ∧ s.eval p.1 p.2 := by
  cases s with
  | line => simp [liftShape, Cell.carrier, Shape.eval]
  | sections =>
    simp [liftShape, Cell.carrier, Shape.eval]
    aesop

private theorem distinct_values {rs : List Height} {p : Plane}
    (ho : rs.Pairwise (fun a b => a.eval p < b.eval p)) :
    ∀ a ∈ rs, ∀ b ∈ rs, a.eval p = b.eval p → a = b := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    rw [List.pairwise_cons] at ho
    intro a ha b hb he
    rcases List.mem_cons.mp ha with ea | ha
    · subst a
      rcases List.mem_cons.mp hb with eb | hb
      · subst b; rfl
      · exact ((ho.1 b hb).ne he).elim
    · rcases List.mem_cons.mp hb with eb | hb
      · subst b
        exact ((ho.1 a ha).ne he.symm).elim
      · exact ih ho.2 a ha b hb he

private theorem mem_liftShape_unique (b : CertifiedTopology.Plane.Cell) (s : Shape) (p : Space)
    (ho : ∀ rs, s = .sections rs → rs.Pairwise (fun a b => a.eval p.1 < b.eval p.1))
    {c d : Cell} (hc : c ∈ liftShape b s) (hd : d ∈ liftShape b s)
    (hpc : p ∈ c.carrier) (hpd : p ∈ d.carrier) : c = d := by
  cases s with
  | line => simpa [liftShape] using (List.mem_singleton.mp hc).trans (List.mem_singleton.mp hd).symm
  | sections rs =>
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    have ea := hpc.2 a (by simp)
    have ee := hpd.2 e (by simp)
    rw [distinct_values (ho rs rfl) a ha e he (ea.symm.trans ee)]

private noncomputable def graphHomeomorph (b : CertifiedTopology.Plane.Cell) (h : Height)
    (hc : Continuous fun p : b.carrier => h.eval p.1) :
    (Cell.mk b (some h)).carrier ≃ₜ b.carrier where
  toFun := fun p => ⟨p.1.1, p.2.1⟩
  invFun := fun p => ⟨(p.1, h.eval p.1), p.2, by simp⟩
  left_inv := by
    intro p
    apply Subtype.ext
    exact Prod.ext rfl (p.2.2 h (by simp)).symm
  right_inv := fun _ => rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.prodMk hc).subtype_mk _

private noncomputable def cylinderHomeomorph (b : CertifiedTopology.Plane.Cell) :
    (Cell.mk b none).carrier ≃ₜ b.carrier × ℝ := by
  have eq : (Cell.mk b none).carrier = b.carrier ×ˢ (Set.univ : Set ℝ) := by
    ext p
    simp [Cell.carrier]
  rw [eq]
  exact (Homeomorph.Set.prod _ _).trans
    ((Homeomorph.refl b.carrier).prodCongr (Homeomorph.Set.univ ℝ))

private theorem liftShape_model (b : CertifiedTopology.Plane.Cell) (s : Shape)
    (hc : ∀ rs, s = .sections rs → ∀ h ∈ rs, Continuous fun p : b.carrier => h.eval p.1)
    {c : Cell} (hm : c ∈ liftShape b s) :
    match c.height with
    | none => Nonempty (c.carrier ≃ₜ c.base.carrier × ℝ)
    | some _ => Nonempty (c.carrier ≃ₜ c.base.carrier) := by
  cases s with
  | line =>
    obtain rfl : c = ⟨b, none⟩ := List.mem_singleton.mp hm
    exact ⟨cylinderHomeomorph b⟩
  | sections hs =>
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hm
    exact ⟨graphHomeomorph b h (hc hs rfl h hh)⟩

/-- Lift only cells in the common zero set. A generic planar CAD can supply the diagram,
    or a specialized solver can supply the same certificate. -/
noncomputable def solve (q r : Equation ℝ) (d : Plane.Diagram (program q r).projection) :
    List Cell := d.cells.flatMap fun b => liftShape b ((program q r).select b.sample)

theorem solve_correct (q r : Equation ℝ) (d : Plane.Diagram (program q r).projection)
    (p : Space) :
    (∃ c ∈ solve q r d, p ∈ c.carrier) ↔
      q.eval p.1.1 p.1.2 p.2 = 0 ∧ r.eval p.1.1 p.1.2 p.2 = 0 := by
  rw [← program_correct q r p.1 p.2]
  constructor
  · rintro ⟨c, hc, hp⟩
    obtain ⟨b, hb, hc⟩ := List.mem_flatMap.mp hc
    have h := (mem_liftShape b _ p).mp ⟨c, hc, hp⟩
    rw [Program.select_stable _ b (d.invariant b hb) p.1 h.1]
    exact h.2
  · intro h
    obtain ⟨b, ⟨hb, hp⟩, _⟩ := d.partition p.1
    rw [Program.select_stable _ b (d.invariant b hb) p.1 hp] at h
    obtain ⟨c, hc, hpc⟩ := (mem_liftShape b _ p).mpr ⟨hp, h⟩
    exact ⟨c, List.mem_flatMap.mpr ⟨b, hb, hc⟩, hpc⟩

/-- A section is homeomorphic to its base, and a full fiber is the product
    of its base with the real line. -/
theorem solve_cell_model (q r : Equation ℝ) (d : Plane.Diagram (program q r).projection)
    {c : Cell} (hc : c ∈ solve q r d) :
    match c.height with
    | none => Nonempty (c.carrier ≃ₜ c.base.carrier × ℝ)
    | some _ => Nonempty (c.carrier ≃ₜ c.base.carrier) := by
  obtain ⟨b, hb, hc⟩ := List.mem_flatMap.mp hc
  exact liftShape_model b _ (fun _ hr =>
    ((program q r).sections_valid b (d.invariant b hb) (program_valid q r) hr).1) hc

theorem solve_contractible (q r : Equation ℝ) (d : Plane.Diagram (program q r).projection)
    {c : Cell} (hc : c ∈ solve q r d) : ContractibleSpace c.carrier := by
  let := c.base.contractible
  have h := solve_cell_model q r d hc
  cases hh : c.height <;> rw [hh] at h <;> exact h.some.contractibleSpace

private theorem liftShape_base {b : CertifiedTopology.Plane.Cell} {s : Shape} {c : Cell}
    (hc : c ∈ liftShape b s) : c.base = b := by
  cases s with
  | line => simpa [liftShape] using congrArg Cell.base (List.mem_singleton.mp hc)
  | sections =>
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hc
    rfl

theorem solve_base_mem (q r : Equation ℝ) (d : Plane.Diagram (program q r).projection)
    {c : Cell} (hc : c ∈ solve q r d) : c.base ∈ d.cells := by
  obtain ⟨b, hb, h⟩ := List.mem_flatMap.mp hc
  rwa [liftShape_base h]

theorem solve_cylindrical (q r : Equation ℝ) (d : Plane.Diagram (program q r).projection)
    {c e : Cell} (hc : c ∈ solve q r d) (he : e ∈ solve q r d) :
    Prod.fst '' c.carrier = Prod.fst '' e.carrier ∨
      Disjoint (Prod.fst '' c.carrier) (Prod.fst '' e.carrier) := by
  rw [c.image_fst, e.image_fst]
  by_cases h : c.base = e.base
  · exact Or.inl (congrArg Plane.Cell.carrier h)
  · refine Or.inr (Set.disjoint_left.mpr fun p hp hpe => h ?_)
    obtain ⟨_, _, uniq⟩ := d.partition p
    exact (uniq _ ⟨solve_base_mem q r d hc, hp⟩).trans
      (uniq _ ⟨solve_base_mem q r d he, hpe⟩).symm

theorem solve_disjoint (q r : Equation ℝ) (d : Plane.Diagram (program q r).projection)
    {c e : Cell} (hc : c ∈ solve q r d) (he : e ∈ solve q r d)
    {p : Space} (hpc : p ∈ c.carrier) (hpe : p ∈ e.carrier) : c = e := by
  obtain ⟨b, hb, hc⟩ := List.mem_flatMap.mp hc
  obtain ⟨b', hb', he⟩ := List.mem_flatMap.mp he
  have hp : p.1 ∈ b.carrier := liftShape_base hc ▸ hpc.1
  have hp' : p.1 ∈ b'.carrier := liftShape_base he ▸ hpe.1
  obtain ⟨b₀, _, unique⟩ := d.partition p.1
  have eq := (unique b' ⟨hb', hp'⟩).trans (unique b ⟨hb, hp⟩).symm
  subst b'
  exact mem_liftShape_unique _ _ p (fun _ hr =>
    ((program q r).sections_valid b (d.invariant b hb) (program_valid q r) hr).2 p.1 hp)
    hc he hpc hpe

end CertifiedTopology.Quadric
