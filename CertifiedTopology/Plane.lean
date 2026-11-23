module

public import CertifiedTopology.Univariate
public import CertifiedTopology.Geometry
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

namespace CertifiedTopology.Plane

open Polynomial

/-- The outer variable is the second coordinate in the cylindrical order. -/
abbrev BiPoly (K : Type) [Semiring K] := Polynomial (Polynomial K)

noncomputable def specialize {K : Type} [CommSemiring K] (x : K) : BiPoly K →+* Polynomial K :=
  Polynomial.mapRingHom (Polynomial.evalRingHom x)

noncomputable def value {K : Type} [CommSemiring K] (p : BiPoly K) (s : K × K) : K :=
  (specialize s.1 p).eval s.2

theorem value_hom {K : Type} [CommSemiring K] (s : K × K) (p : BiPoly K) :
    value p s = ((Polynomial.evalRingHom s.2).comp (specialize s.1)) p := rfl

theorem value_add {K : Type} [CommSemiring K] (p : K × K) (f g : BiPoly K) :
    value (f+g) p = value f p + value g p := by simp only [value_hom, map_add]

theorem value_mul {K : Type} [CommSemiring K] (p : K × K) (f g : BiPoly K) :
    value (f*g) p = value f p * value g p := by simp only [value_hom, map_mul]

theorem value_sub {K : Type} [CommRing K] (p : K × K) (f g : BiPoly K) :
    value (f-g) p = value f p - value g p := by simp only [value_hom, map_sub]

theorem value_pow {K : Type} [CommSemiring K] (p : K × K) (f : BiPoly K) (n : ℕ) :
    value (f^n) p = value f p ^ n := by simp only [value_hom, map_pow]

theorem continuous_value (p : BiPoly ℝ) : Continuous (value p) := by
  classical
  have eq : value p = fun s => ∑ i ∈ p.support, (p.coeff i).eval s.1 * s.2^i := by
    funext s
    change ((p.map (evalRingHom s.1)).eval s.2) = _
    rw [eval_map, eval₂_eq_sum, sum_def]
    rfl
  rw [eq]
  fun_prop

/-- A planar cell carries its sample and its topological certificate. -/
structure Cell where
  carrier : Set (ℝ × ℝ)
  sample : ℝ × ℝ
  sample_mem : sample ∈ carrier
  contractible : ContractibleSpace carrier

/-- A certified decomposition for the requested projection polynomials. -/
structure Diagram (ps : List (BiPoly ℝ)) where
  cells : List Cell
  partition : ∀ p, ∃! c, c ∈ cells ∧ p ∈ c.carrier
  invariant : ∀ c ∈ cells, ∀ p, p ∈ c.carrier → ∀ f ∈ ps,
    side (value f p) 0 = side (value f c.sample) 0

open Set

def strip (s : Slice ℝ) : Set ℝ := {t | Univariate.contains s t}

theorem convex_strip (s : Slice ℝ) : Convex ℝ (strip s) := by
  cases s with
  | sectionAt r =>
    have e : strip (.sectionAt r) = {r} := rfl
    rw [e]
    exact convex_singleton r
  | sector lo hi =>
    cases lo with
    | none =>
      cases hi with
      | none =>
        convert (convex_univ : Convex ℝ (univ : Set ℝ)) using 1
        ext
        simp [strip, Univariate.contains, Slice.Contains]
      | some u =>
        convert (convex_Iio u : Convex ℝ (Iio u)) using 1
        ext
        simp [strip, Univariate.contains, Slice.Contains, Aff.eval]
    | some l =>
      cases hi with
      | none =>
        convert (convex_Ioi l : Convex ℝ (Ioi l)) using 1
        ext
        simp [strip, Univariate.contains, Slice.Contains, Aff.eval]
      | some u =>
        convert (convex_Ioo l u : Convex ℝ (Ioo l u)) using 1
        ext
        simp [strip, Univariate.contains, Slice.Contains, Aff.eval]

noncomputable def rectangle (s t : Slice ℝ)
    (hs : Slice.sample (n := 0) () s ∈ strip s)
    (ht : Slice.sample (n := 0) () t ∈ strip t) : Cell where
  carrier := strip s ×ˢ strip t
  sample := (Slice.sample (n := 0) () s, Slice.sample (n := 0) () t)
  sample_mem := ⟨hs, ht⟩
  contractible := ((convex_strip s).prod (convex_strip t)).contractibleSpace
    ⟨(Slice.sample (n := 0) () s, Slice.sample (n := 0) () t), ⟨hs, ht⟩⟩

@[simp] theorem value_x (p : Polynomial ℝ) (s : ℝ × ℝ) :
    value (C p) s = p.eval s.1 := by
  change ((C p).map (evalRingHom s.1)).eval s.2 = _
  simp

@[simp] theorem value_y (p : Polynomial ℝ) (s : ℝ × ℝ) :
    value (p.map (C : ℝ →+* Polynomial ℝ)) s = p.eval s.2 := by
  change ((p.map C).map (evalRingHom s.1)).eval s.2 = _
  rw [Polynomial.map_map]
  have eq : (evalRingHom s.1).comp (C : ℝ →+* Polynomial ℝ) = RingHom.id ℝ := by
    ext x
    simp
  rw [eq, Polynomial.map_id]

noncomputable def rectangles (xs ys : List (Polynomial ℝ)) : List Cell :=
  (Univariate.decompose xs).attach.flatMap fun s =>
    (Univariate.decompose ys).attach.map fun t =>
      rectangle s.1 t.1 ((Univariate.decompose_correct xs).2.1 _ s.2)
        ((Univariate.decompose_correct ys).2.1 _ t.2)

private theorem mem_rectangles (xs ys : List (Polynomial ℝ)) {c : Cell} :
    c ∈ rectangles xs ys ↔
      ∃ (s : {s // s ∈ Univariate.decompose xs})
        (t : {t // t ∈ Univariate.decompose ys}),
        c = rectangle s.1 t.1 ((Univariate.decompose_correct xs).2.1 _ s.2)
          ((Univariate.decompose_correct ys).2.1 _ t.2) := by
  simp [rectangles, eq_comm, List.mem_flatMap]

/-- The product of the two univariate diagrams suffices for axis-separated polynomials. -/
noncomputable def ofAxes (ps : List (BiPoly ℝ)) (xs ys : List (Polynomial ℝ))
    (h : ∀ f ∈ ps, (∃ x ∈ xs, f = C x) ∨
      (∃ y ∈ ys, f = y.map (C : ℝ →+* Polynomial ℝ))) : Diagram ps where
  cells := rectangles xs ys
  partition := by
    intro p
    obtain ⟨s, ⟨hs, hp⟩, su⟩ := (Univariate.decompose_correct xs).1 p.1
    obtain ⟨t, ⟨ht, hq⟩, tu⟩ := (Univariate.decompose_correct ys).1 p.2
    refine ⟨rectangle s t ((Univariate.decompose_correct xs).2.1 _ hs)
      ((Univariate.decompose_correct ys).2.1 _ ht),
      ⟨(mem_rectangles xs ys).mpr ⟨⟨s,hs⟩,⟨t,ht⟩,rfl⟩, ⟨hp,hq⟩⟩, ?_⟩
    rintro c ⟨hc, hpc⟩
    obtain ⟨⟨u, hu⟩,⟨v,hv⟩,rfl⟩ := (mem_rectangles xs ys).mp hc
    have e := su u ⟨hu, hpc.1⟩
    have e' := tu v ⟨hv, hpc.2⟩
    subst u v
    rfl
  invariant := by
    intro c hc p hp f hf
    obtain ⟨⟨s,hs⟩,⟨t,ht⟩,rfl⟩ := (mem_rectangles xs ys).mp hc
    rcases h f hf with ⟨f,hfa,rfl⟩ | ⟨f,hfa,rfl⟩
    · simp only [value_x]
      exact (Univariate.decompose_correct xs).2.2 s hs p.1 hp.1 f hfa
    · simp only [value_y]
      exact (Univariate.decompose_correct ys).2.2 t ht p.2 hp.2 f hfa

noncomputable def axes (ps : List (BiPoly ℝ)) : List (Polynomial ℝ) × List (Polynomial ℝ) :=
  (ps.map (fun f => f.coeff 0), ps.map (specialize 0))

/-- Recognize each axis independently, retaining exact coefficients. -/
noncomputable def solveAxes? (ps : List (BiPoly ℝ)) : Option (Diagram ps) := by
  classical
  let a := axes ps
  by_cases h : ∀ f ∈ ps, f = C (f.coeff 0) ∨ f = (specialize 0 f).map (C : ℝ →+* Polynomial ℝ)
  · apply Option.some
    refine ofAxes ps a.1 a.2 ?_
    intro f hf
    rcases h f hf with e | e
    · exact Or.inl ⟨f.coeff 0, List.mem_map_of_mem hf, e⟩
    · exact Or.inr ⟨specialize 0 f, List.mem_map_of_mem hf, e⟩
  · exact none

def Diagram.restrict {ps qs : List (BiPoly ℝ)} (d : Diagram qs)
    (h : ∀ f ∈ ps, f ∈ qs) : Diagram ps :=
  ⟨d.cells, d.partition, fun c hc p hp f hf => d.invariant c hc p hp f (h f hf)⟩

theorem const_coeff {f : BiPoly ℝ} (h : f.natDegree = 0) :
    f = C (f.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero h

noncomputable def constant? {K : Type} [Semiring K] (f : BiPoly K) : Option K :=
  if f.natDegree = 0 ∧ (f.coeff 0).natDegree = 0 then some ((f.coeff 0).coeff 0) else none

theorem constant?_correct {f : BiPoly ℝ} {a : ℝ} (h : constant? f = some a)
    (s : ℝ × ℝ) : value f s = a := by
  unfold constant? at h
  split at h
  · rename_i hd
    have he : f = C (C ((f.coeff 0).coeff 0)) :=
      (const_coeff hd.1).trans (congrArg C (Polynomial.eq_C_of_natDegree_eq_zero hd.2))
    calc
      value f s = (f.coeff 0).coeff 0 := by conv_lhs => rw [he, value_x, eval_C]
      _ = a := Option.some.inj h
  · contradiction

end CertifiedTopology.Plane
