module

public import CertifiedTopology.Correctness

@[expose] public section

namespace CertifiedTopology
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- A product in factored form. The empty product is one. Factors may repeat. -/
abbrev Product (K : Type) (n : ℕ) := List (Aff K n)

def productEval (fs : Product K n) (p : Point K n) : K :=
  (fs.map (Aff.eval · p)).prod

inductive Formula (A : Type) where
  | atom (factors : List A) (test : Side)
  | truth (value : Bool)
  | neg (f : Formula A)
  | conj (f g : Formula A)
  | disj (f g : Formula A)

namespace Formula

def factors {A} : Formula A → List A
  | .atom fs _ => fs
  | .truth _ => []
  | .neg f => f.factors
  | .conj f g | .disj f g => f.factors ++ g.factors

def eval (p : Point K n) : Formula (Aff K n) → Bool
  | .atom fs test => side (productEval fs p) 0 == test
  | .truth v => v
  | .neg f => !(f.eval p)
  | .conj f g => f.eval p && g.eval p
  | .disj f g => f.eval p || g.eval p

private theorem product_sign {p q : Point K n} (fs : Product K n)
    (h : ∀ a ∈ fs, side (Aff.eval a p) 0 = side (Aff.eval a q) 0) :
    side (productEval fs p) 0 = side (productEval fs q) 0 := by
  induction fs with
  | nil => rfl
  | cons a as ih =>
    obtain ⟨al,ae,ag⟩ := side_congr (h a (by simp))
    obtain ⟨bl,be,bg⟩ := side_congr (ih fun b hb => h b (by simp [hb]))
    change side (Aff.eval a p * productEval as p) 0 = side (Aff.eval a q * productEval as q) 0
    simp only [side,mul_neg_iff,mul_eq_zero,al,ae,ag,bl,be,bg]

theorem eval_congr {p q : Point K n} (f : Formula (Aff K n))
    (h : ∀ a ∈ f.factors, side (Aff.eval a p) 0 = side (Aff.eval a q) 0) :
    f.eval p = f.eval q := by
  induction f with
  | truth => rfl
  | atom fs test => simp only [eval,product_sign fs h]
  | neg f ih => simp only [eval,ih h]
  | conj f g ih jh | disj f g ih jh =>
    simp only [eval, ih (fun a ha => h a (List.mem_append_left _ ha)),
      jh (fun a ha => h a (List.mem_append_right _ ha))]

end Formula

/-- Cells of the cylindrical partition on which the formula holds. -/
def solve (f : Formula (Aff K n)) : List (Cell K n) :=
  (cad n f.factors).filter fun c => f.eval c.sample

theorem solve_correct (f : Formula (Aff K n)) (p : Point K n) :
    f.eval p = true ↔ ∃! c, c ∈ solve f ∧ c.Contains p := by
  have h := cad_correct n f.factors
  obtain ⟨c,⟨hc,hp⟩,hu⟩ := h.partition p
  constructor
  · intro hf
    have he := f.eval_congr (h.sign_invariant _ hc p hp)
    exact ⟨c,⟨List.mem_filter.mpr ⟨hc, he ▸ hf⟩,hp⟩,
      fun d hd => hu d ⟨(List.mem_filter.mp hd.1).1,hd.2⟩⟩
  · rintro ⟨d,⟨hd,hp'⟩,_⟩
    obtain ⟨hd,he⟩ := List.mem_filter.mp hd
    exact (f.eval_congr (h.sign_invariant _ hd p hp')).trans he

end CertifiedTopology
