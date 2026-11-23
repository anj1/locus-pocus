module

public import CertifiedTopology.Univariate
public import CertifiedTopology.Quadratic
public import CertifiedTopology.Isolation

@[expose] public section

namespace CertifiedTopology.Quadratic
open Polynomial

/-- Polynomials in the base parameter; y is the last (fiber) coordinate. -/
structure Family where
  a : Polynomial ℝ
  b : Polynomial ℝ
  c : Polynomial ℝ

namespace Family

noncomputable def projection (f : Family) := [f.a, f.b, f.c, discrim f.a f.b f.c]

def value (f : Family) (p y : ℝ) := f.a.eval p * (y*y) + f.b.eval p*y + f.c.eval p

/-- The finite base stratification, including all degree drops. -/
noncomputable def stratify (f : Family) : List (Slice ℝ × Kind) :=
  (Univariate.decompose f.projection).map fun s =>
    let p := Slice.sample (n := 0) () s
    (s,classify (f.a.eval p) (f.b.eval p) (f.c.eval p))

private theorem classify_congr {a b c d e f : ℝ}
    (ha : side a 0 = side d 0) (hb : side b 0 = side e 0)
    (hc : side c 0 = side f 0) (hD : side (discrim a b c) 0 = side (discrim d e f) 0) :
    classify a b c = classify d e f := by
  simp only [classify, (side_congr ha).2.1, (side_congr hb).2.1, (side_congr hc).2.1,
    (side_congr hD).1, (side_congr hD).2.1]

theorem stratify_correct (f : Family) :
    (∀ p, ∃! row, row ∈ f.stratify ∧ Univariate.contains row.1 p) ∧
    (∀ row ∈ f.stratify, ∀ p, Univariate.contains row.1 p → Realizes (f.value p) row.2) := by
  obtain ⟨cover,_,sign⟩ := Univariate.decompose_correct f.projection
  constructor
  · intro p
    obtain ⟨s,⟨hs,hp⟩,hu⟩ := cover p
    refine ⟨_, ⟨List.mem_map.mpr ⟨s,hs,rfl⟩, hp⟩, ?_⟩
    rintro row ⟨hr,hq⟩
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
    obtain rfl := hu t ⟨ht,hq⟩
    rfl
  · intro row hr
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    intro p hp
    have h := sign s hs p hp
    have hd := h (discrim f.a f.b f.c) (by simp [projection])
    simp only [discrim,eval_sub,eval_pow,eval_mul,eval_ofNat] at hd
    have he := classify_congr (h f.a (by simp [projection])) (h f.b (by simp [projection]))
      (h f.c (by simp [projection])) hd
    change Realizes (f.value p) (classify _ _ _)
    rw [← he]
    exact classify_correct _ _ _

/-- Interpret the four projected signs in coefficient order. Valid diagrams
    always supply exactly four entries. -/
def kindOfSigns : List Side → Kind
  | [.on,.on,.on,_] => .line
  | [.on,.on,_,_] => .empty
  | [.on,_,_,_] => .point
  | [_,_,_,.below] => .empty
  | [_,_,_,.on] => .point
  | [_,_,_,.above] => .twoPoints
  | _ => .empty

theorem eval_kind (f : Family) (x : ℝ) :
    kindOfSigns (f.projection.map fun p => side (p.eval x) 0) =
    classify (f.a.eval x) (f.b.eval x) (f.c.eval x) := by
  simp only [projection,List.map_cons,List.map_nil,discrim,eval_sub,eval_pow,eval_mul,eval_ofNat]
  generalize f.a.eval x = a
  generalize f.b.eval x = b
  generalize f.c.eval x = c
  unfold classify side discrim
  split_ifs <;> simp_all [kindOfSigns]

theorem diagram_fiber (f : Family) (d : Isolation.Diagram f.projection)
    {row} (h : row ∈ d.rows) {x} (hx : Univariate.contains row.1 x) :
    Realizes (f.value x) (kindOfSigns row.2) := by
  rw [← d.valid row h x hx,eval_kind]
  exact classify_correct _ _ _

end Family
end CertifiedTopology.Quadratic
