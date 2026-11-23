module

public import CertifiedTopology.Input
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

namespace CertifiedTopology.Expr
variable {K ι κ : Type}

def rename (σ : ι → κ) : Expr K ι → Expr K κ
  | .var i => .var (σ i)
  | .const c => .const c
  | .neg f => .neg (f.rename σ)
  | .add f g => .add (f.rename σ) (g.rename σ)
  | .mul f g => .mul (f.rename σ) (g.rename σ)

theorem eval_rename [Ring K] (e : Expr K ι) (σ : ι → κ) (x : κ → K) :
    (e.rename σ).eval x = e.eval (x ∘ σ) := by
  induction e <;> simp_all [rename,eval,Function.comp_def]

/-- Real and imaginary coordinates can be interleaved in any user-selected variable order. -/
def complexEquation {n} (σ : ι ⊕ ι ≃ Fin n) (e : Expr ℂ ι) : Predicate ℝ (Fin n) :=
  match e with
  | .mul f g => .disj (complexEquation σ f) (complexEquation σ g)
  | .neg f => complexEquation σ f
  | _ => .conj (.atom (e.realify.1.rename σ) .on) (.atom (e.realify.2.rename σ) .on)

theorem complexEquation_correct {n} (σ : ι ⊕ ι ≃ Fin n) (e : Expr ℂ ι) (p : ι → ℂ) :
    (complexEquation σ e).eval ((Sum.elim (fun i => (p i).re) (fun i => (p i).im)) ∘ σ.symm) =
      true ↔ e.eval p = 0 := by
  have zero (x : ℝ) : side x 0 = .on ↔ x = 0 := by
    unfold side
    split_ifs <;> simp_all; order
  induction e with
  | mul f g ih jh => simp [complexEquation,Predicate.eval,eval,ih,jh,mul_eq_zero]
  | neg f ih => simpa [complexEquation,eval] using ih
  | const | var | add =>
    apply Iff.trans _ (realify_zero _ p).symm
    simp [complexEquation,Predicate.eval,eval_rename,Function.comp_assoc,zero]

end CertifiedTopology.Expr
