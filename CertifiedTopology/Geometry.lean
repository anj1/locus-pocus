module

public import CertifiedTopology.Correctness
public import Mathlib.Analysis.Convex.Contractible

@[expose] public section

namespace CertifiedTopology.Geometry

/-- Read coordinates in their cylindrical order. -/
def coords : {n : ℕ} → (Fin n → ℝ) → Point ℝ n
  | 0,_ => ()
  | n+1,x => (coords (fun i => x i.castSucc), x (Fin.last n))

theorem coords_surjective (n) : Function.Surjective (@coords n) := by
  induction n with
  | zero => exact fun _ => ⟨Fin.elim0,rfl⟩
  | succ n ih =>
    rintro ⟨p,t⟩
    obtain ⟨x,rfl⟩ := ih p
    exact ⟨Fin.snoc x t, by simp [coords]⟩

def carrier {n} (c : Cell ℝ n) : Set (Fin n → ℝ) := {x | c.Contains (coords x)}

theorem eval_combine {n} (f : Aff ℝ n) (x y : Fin n → ℝ) {a b : ℝ} (hab : a+b=1) :
    Aff.eval f (coords (a • x + b • y)) =
      a * Aff.eval f (coords x) + b * Aff.eval f (coords y) := by
  induction n with
  | zero => change (f : ℝ) = a*f+b*f; rw [← add_mul,hab,one_mul]
  | succ n ih =>
    change Aff.eval f.1 (coords (a • (fun i : Fin n => x i.castSucc) +
      b • (fun i : Fin n => y i.castSucc))) + _ = _
    rw [ih]
    simp [coords,Aff.eval]
    ring

private theorem weighted_lt {a b x y s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (h : x < s) (h' : y < t) : a*x+b*y < a*s+b*t := by
  rcases ha.eq_or_lt with e | e
  · subst a; norm_num at hab; simpa [hab] using h'
  · exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left h e) (mul_le_mul_of_nonneg_left h'.le hb)

theorem convex_carrier {n} (c : Cell ℝ n) : Convex ℝ (carrier c) := by
  induction c with
  | origin => intro _ _ _ _ _ _ _ _ _; trivial
  | @lift n b s ih =>
    intro x hx y hy a d ha hd had
    refine ⟨ih hx.1 hy.1 ha hd had, ?_⟩
    let X : Fin n → ℝ := fun i => x i.castSucc
    let Y : Fin n → ℝ := fun i => y i.castSucc
    change s.Contains (coords (a • X + d • Y)) (a*x (Fin.last n)+d*y (Fin.last n))
    cases s with
    | sectionAt r =>
      change _ = _
      rw [eval_combine _ _ _ had]
      exact congrArg₂ (· + ·) (congrArg (a * ·) hx.2) (congrArg (d * ·) hy.2)
    | sector lo hi =>
      constructor
      · intro r hr
        rw [eval_combine _ _ _ had]
        exact weighted_lt ha hd had (hx.2.1 r hr) (hy.2.1 r hr)
      · intro r hr
        rw [eval_combine _ _ _ had]
        exact weighted_lt ha hd had (hx.2.2 r hr) (hy.2.2 r hr)

/-- Each output cell is contractible in the usual real topology. -/
theorem contractible_cell {n} (fs : List (Aff ℝ n)) {c} (hc : c ∈ cad n fs) :
    ContractibleSpace (carrier c) := by
  obtain ⟨x,hx⟩ := coords_surjective n c.sample
  apply (convex_carrier c).contractibleSpace
  exact ⟨x, show c.Contains (coords x) from hx ▸ (cad_correct n fs).sample_mem c hc⟩

end CertifiedTopology.Geometry
