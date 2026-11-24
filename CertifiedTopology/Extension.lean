module

public import CertifiedTopology.Formula
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.Algebra.Order.Field.Subfield

@[expose] public section

namespace CertifiedTopology
variable {K L : Type} [Field K] [Field L] [LinearOrder K] [LinearOrder L]
  [IsStrictOrderedRing K] [IsStrictOrderedRing L]

namespace Extension
variable (φ : K →+* L)

def aff : {n : ℕ} → Aff K n → Aff L n
  | 0,c => φ c
  | _+1,(b,a) => (aff b,φ a)

def point : {n : ℕ} → Point K n → Point L n
  | 0,_ => ()
  | _+1,(p,t) => (point p,φ t)

def slice {n} : Slice (Aff K n) → Slice (Aff L n)
  | .sectionAt a => .sectionAt (aff φ a)
  | .sector lo hi => .sector (lo.map (aff φ)) (hi.map (aff φ))

def cell : {n : ℕ} → Cell K n → Cell L n
  | 0,.origin => .origin
  | _+1,.lift b s => .lift (cell b) (slice φ s)

variable {n : ℕ}

omit [LinearOrder K] [LinearOrder L] [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
theorem aff_injective : Function.Injective (aff φ (n := n)) := by
  induction n with
  | zero => exact φ.injective
  | succ n ih =>
    rintro ⟨b,a⟩ ⟨d,e⟩ h
    exact Prod.ext (ih (congrArg Prod.fst h)) (φ.injective (congrArg Prod.snd h))

omit [LinearOrder K] [LinearOrder L] [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
theorem cell_injective : Function.Injective (cell φ (n := n)) := by
  induction n with
  | zero => intro c d _; cases c; cases d; rfl
  | succ n ih =>
    rintro ⟨_⟩ ⟨_⟩ h
    rename_i b s d t
    simp only [cell, Cell.lift.injEq] at h
    obtain rfl := ih h.1
    congr 1
    have opt : Function.Injective (Option.map (aff φ (n := n))) :=
      by
        intro a b h
        cases a <;> cases b <;> simp_all [(aff_injective φ).eq_iff]
    cases s <;> cases t <;> simp_all [slice, (aff_injective φ).eq_iff, opt.eq_iff]

@[simp] theorem eval_map (f : Aff K n) (p : Point K n) :
    Aff.eval (aff φ f) (point φ p) = φ (Aff.eval f p) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [aff,point,Aff.eval,ih]

omit [LinearOrder K] [LinearOrder L] [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
@[simp] theorem scale_map (f : Aff K n) (s : K) :
    Aff.scale (φ s) (aff φ f) = aff φ (Aff.scale s f) := by
  induction n with
  | zero => exact (map_mul φ _ _).symm
  | succ n ih => simp [Aff.scale,aff,ih]

omit [LinearOrder K] [LinearOrder L] [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
@[simp] theorem sub_map (f g : Aff K n) :
    Aff.sub (aff φ f) (aff φ g) = aff φ (Aff.sub f g) := by
  induction n with
  | zero => exact (map_sub φ _ _).symm
  | succ n ih => simp [Aff.sub,aff,ih]

@[simp] theorem root_map (f : Aff K (n+1)) : root (aff φ f) = aff φ (root f) := by
  simp only [root,aff, ← map_inv₀, ← map_neg, scale_map]

omit [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
@[simp] theorem constant_map (f : Aff K n) : Aff.constant (aff φ f) = Aff.constant f := by
  induction n with
  | zero => rfl
  | succ n ih => by_cases h : f.2 = 0 <;> simp [aff,Aff.constant,ih,h,beq_eq_decide]

omit [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
@[simp] theorem prune_map (fs : List (Aff K n)) :
    prune (fs.map (aff φ)) = (prune fs).map (aff φ) := by
  simp [prune,List.filter_map,Function.comp_def,List.dedup_map_of_injective (aff_injective φ)]

@[simp] theorem roots_map (fs : List (Aff K (n+1))) :
    roots (fs.map (aff φ)) = (roots fs).map (aff φ) := by
  simp only [roots,List.filter_map,List.map_map,Function.comp_def]
  have hh (f : Aff K (n+1)) : ((aff φ f).2 != 0) = (f.2 != 0) := by
    by_cases h : f.2 = 0 <;> simp [aff,h,bne,beq_eq_decide]
  rw [← List.dedup_map_of_injective (aff_injective φ)]
  simp [hh,List.map_map,Function.comp_def]

omit [LinearOrder K] [LinearOrder L] [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
theorem differences_map (rs : List (Aff K n)) :
    differences (rs.map (aff φ)) = (differences rs).map (aff φ) := by
  induction rs with
  | nil => rfl
  | cons a as ih => simp [differences,ih,List.map_map,Function.comp_def]

@[simp] theorem project_map (fs : List (Aff K (n+1))) :
    project (fs.map (aff φ)) = (project fs).map (aff φ) := by
  have hh (f : Aff K (n+1)) : ((aff φ f).2 == 0) = (f.2 == 0) := by
    by_cases h : f.2 = 0 <;> simp [aff,h,beq_eq_decide]
  simp only [project,roots_map φ fs,List.filter_map,List.map_append,differences_map,
    List.map_map,Function.comp_def,hh]
  rfl

variable (mono : StrictMono φ)
include mono

@[simp] theorem insert_map (p : Point K n) (r : Aff K n) (rs : List (Aff K n)) :
    insertRoot (point φ p) (aff φ r) (rs.map (aff φ)) = (insertRoot p r rs).map (aff φ) := by
  induction rs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.map_cons,insertRoot,eval_map,mono.lt_iff_lt,φ.injective.eq_iff]
    split_ifs <;> simp [ih]

theorem ordered_map (p : Point K n) (rs : List (Aff K n)) :
    orderedRoots (point φ p) (rs.map (aff φ)) = (orderedRoots p rs).map (aff φ) := by
  induction rs with
  | nil => rfl
  | cons a as ih => simp only [List.map_cons,orderedRoots,List.foldr_cons] at *; rw [ih,insert_map φ mono]

omit mono [LinearOrder K] [LinearOrder L] [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
theorem slices_map (lo : Option (Aff K n)) (rs : List (Aff K n)) :
    slices (lo.map (aff φ)) (rs.map (aff φ)) = (slices lo rs).map (slice φ) := by
  induction rs generalizing lo with
  | nil => rfl
  | cons a as ih => simp [slices,slice,← ih]

@[simp] theorem stack_map (p : Point K n) (rs : List (Aff K n)) :
    stack (point φ p) (rs.map (aff φ)) = (stack p rs).map (slice φ) := by
  rw [stack,ordered_map φ mono,slice_none]
  where slice_none : slices none ((orderedRoots p rs).map (aff φ)) =
          (stack p rs).map (slice φ) := slices_map φ none _

omit mono in
@[simp] theorem sample_slice (p : Point K n) (s : Slice (Aff K n)) :
    (slice φ s).sample (point φ p) = φ (s.sample p) := by
  cases s with
  | sectionAt a => exact eval_map _ _ _
  | sector lo hi => cases lo <;> cases hi <;> simp [slice,Slice.sample,map_ofNat]

omit mono in
@[simp] theorem sample_cell (c : Cell K n) : (cell φ c).sample = point φ c.sample := by
  induction c with
  | origin => rfl
  | lift b s ih => simp [cell,Cell.sample,point,ih]

theorem cad_map (m : ℕ) (fs : List (Aff K m)) :
    cad m (fs.map (aff φ)) = (cad m fs).map (cell φ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [cad, project_map φ fs, prune_map φ (project fs), ih (prune (project fs)), List.flatMap_map,List.map_flatMap,
      Function.comp_def, sample_cell,roots_map φ fs,stack_map φ mono,List.map_map]
    rfl

def formula : Formula (Aff K n) → Formula (Aff L n)
  | .atom fs t => .atom (fs.map (aff φ)) t
  | .truth b => .truth b
  | .neg f => .neg (formula f)
  | .conj f g => .conj (formula f) (formula g)
  | .disj f g => .disj (formula f) (formula g)

omit mono [LinearOrder K] [LinearOrder L] [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
theorem factors_map (f : Formula (Aff K n)) :
    (formula φ f).factors = f.factors.map (aff φ) := by
  induction f <;> simp_all [formula,Formula.factors]

theorem eval_formula (f : Formula (Aff K n)) (p : Point K n) :
    (formula φ f).eval (point φ p) = f.eval p := by
  induction f with
  | atom fs t =>
    have h : productEval (fs.map (aff φ)) (point φ p) = φ (productEval fs p) := by
      induction fs with
      | nil => simp [productEval]
      | cons a as ih =>
        change Aff.eval (aff φ a) (point φ p) * productEval _ _ = φ (Aff.eval a p * productEval as p)
        rw [eval_map,ih,map_mul]
    have hl (x : K) : φ x < 0 ↔ x < 0 := by simpa using (mono.lt_iff_lt (a := x) (b := 0))
    simp only [formula,Formula.eval,h,side,hl,map_eq_zero]
  | truth => rfl
  | neg | conj | disj => simp_all [formula,Formula.eval]

/-- Rational cell output describes the full real solution after interpreting its coefficients. -/
theorem solve_map (f : Formula (Aff K n)) :
    solve (formula φ f) = (solve f).map (cell φ) := by
  simp only [solve, factors_map, cad_map φ mono, List.filter_map,Function.comp_def,
    sample_cell,eval_formula φ mono]

end Extension

/-- The embedded field of real algebraic numbers. -/
noncomputable abbrev RealAlg := algebraicClosure ℚ ℝ

theorem solve_realAlg {n} (f : Formula (Aff RealAlg n)) :
    let φ := (algebraicClosure ℚ ℝ).toSubfield.subtype
    solve (Extension.formula φ f) = (solve f).map (Extension.cell φ) :=
  Extension.solve_map (algebraicClosure ℚ ℝ).toSubfield.subtype (fun _ _ h => h) f

end CertifiedTopology
