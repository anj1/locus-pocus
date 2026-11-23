module

public import CertifiedTopology.Plane

@[expose] public section

namespace CertifiedTopology.Plane

open Polynomial

noncomputable def affinePoly (a : Aff ℝ 2) : BiPoly ℝ :=
  C (C a.1.1 + C a.1.2 * X) + C (C a.2) * X

noncomputable def affineCoeffs (p : BiPoly ℝ) : Aff ℝ 2 :=
  (((p.coeff 0).coeff 0, (p.coeff 0).coeff 1), (p.coeff 1).coeff 0)

def pack (p : ℝ × ℝ) : Point ℝ 2 := (((),p.1),p.2)

def unpack (p : Point ℝ 2) : ℝ × ℝ := (p.1.2,p.2)

@[simp] theorem pack_unpack (p : Point ℝ 2) : pack (unpack p) = p := by
  rcases p with ⟨⟨⟨⟩,x⟩,y⟩
  rfl

theorem value_affine (a : Aff ℝ 2) (p : ℝ × ℝ) :
    value (affinePoly a) p = Aff.eval a (pack p) := by
  change (((affinePoly a).map (evalRingHom p.1)).eval p.2) = _
  simp [affinePoly, Aff.eval, pack]

noncomputable def planeVector : (ℝ × ℝ) →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun p i := if i = 0 then p.1 else p.2
  map_add' p q := by ext i; fin_cases i <;> rfl
  map_smul' k p := by ext i; fin_cases i <;> rfl

noncomputable def affineCell (c : CertifiedTopology.Cell ℝ 2) (h : c.Contains c.sample) : Cell where
  carrier := {p | c.Contains (pack p)}
  sample := unpack c.sample
  sample_mem := by change c.Contains (pack (unpack c.sample)); simpa using h
  contractible := by
    have conv : Convex ℝ {p | c.Contains (pack p)} := by
      have equ : {p | c.Contains (pack p)} = planeVector ⁻¹' Geometry.carrier c := by
        rfl
      rw [equ]
      exact (Geometry.convex_carrier c).linear_preimage planeVector
    exact conv.contractibleSpace ⟨unpack c.sample, by
      change c.Contains (pack (unpack c.sample))
      simpa using h⟩

noncomputable def affineCells (fs : List (Aff ℝ 2)) : List Cell :=
  (cad 2 fs).attach.map fun c => affineCell c.val ((cad_correct 2 fs).sample_mem _ c.property)

private theorem mem_affineCells (fs : List (Aff ℝ 2)) {c : Cell} :
    c ∈ affineCells fs ↔ ∃ d, ∃ hm : d ∈ cad 2 fs,
      c = affineCell d ((cad_correct 2 fs).sample_mem _ hm) := by
  simp [affineCells, eq_comm]

/-- Reuse the affine projection and lifting engine for any affine planar input. -/
noncomputable def ofAffines (fs : List (Aff ℝ 2)) : Diagram (fs.map affinePoly) where
  cells := affineCells fs
  partition := by
    intro p
    obtain ⟨c, ⟨hc,hp⟩, unique⟩ := (cad_correct 2 fs).partition (pack p)
    refine ⟨affineCell c ((cad_correct 2 fs).sample_mem c hc),
      ⟨(mem_affineCells fs).mpr ⟨c,hc,rfl⟩, hp⟩, ?_⟩
    rintro d ⟨hd,hpd⟩
    obtain ⟨e,he,rfl⟩ := (mem_affineCells fs).mp hd
    have eq := unique e ⟨he,hpd⟩
    subst e
    rfl
  invariant := by
    intro c hc p hp g hg
    obtain ⟨d,hd,rfl⟩ := (mem_affineCells fs).mp hc
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
    simp only [value_affine]
    change side (Aff.eval f (pack p)) 0 = side (Aff.eval f (pack (unpack d.sample))) 0
    rw [pack_unpack]
    exact (cad_correct 2 fs).sign_invariant d hd (pack p) hp f hf

noncomputable def solveAffine? (ps : List (BiPoly ℝ)) : Option (Diagram ps) := by
  classical
  let fs := ps.map affineCoeffs
  by_cases h : ∀ f ∈ ps, affinePoly (affineCoeffs f) = f
  · refine some ((ofAffines fs).restrict fun f hf => ?_)
    rw [← h f hf]
    exact List.mem_map_of_mem (List.mem_map_of_mem hf)
  · exact none

end CertifiedTopology.Plane
