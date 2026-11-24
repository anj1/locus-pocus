module

public import CertifiedTopology.RootFormula

@[expose] public section

namespace CertifiedTopology.CADDecision

open Set Polynomial ExecutableIsolation CylindricalData ComputableCAD

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n m : ℕ}

def rootAt (p : ComputableCAD.Poly K n) (base : Fin n → Fin m) (z : Fin m) : SignFormula K m :=
  .atom (Multi.substitute (n := n+1) p (Multi.coordinate ∘ Fin.snoc base z)) .on

theorem rootAt_correct (model : RealModel K) (x : Fin m → ℝ)
    (p : ComputableCAD.Poly K n) (base : Fin n → Fin m) (z : Fin m) :
    (rootAt p base z).holds model x ↔ (specialized model p (x ∘ base)).IsRoot (x z) := by
  have e : (fun i => x (@Fin.snoc n (fun _ => Fin m) base z i)) = Fin.snoc (x ∘ base) (x z) := by
    funext i
    cases i using Fin.lastCases <;> simp [Function.comp_def]
  unfold rootAt SignFormula.holds
  let p' : Multi K (n+1) := p
  change side (Multi.evalHom model.hom x (Multi.substitute p' _)) 0 = .on ↔ _
  rw [side_on, Multi.substitute_correct]
  simp only [Function.comp_apply, Multi.eval_coordinate, e, Multi.evalHom_snoc, IsRoot.def]
  exact Iff.of_eq (congrArg (· = 0) (PolynomialData.evalHom_correct _ _ p))

def below {m : ℕ} (i j : Fin m) : SignFormula K m :=
  .atom (Multi.coordinate i - Multi.coordinate j) .below

theorem below_correct (model : RealModel K) (x : Fin m → ℝ) (i j : Fin m) :
    (below i j).holds model x ↔ x i < x j := by
  simp [below, SignFormula.holds, side_below]

/-- There are at least k distinct roots strictly below the displayed coordinate.
    Witnesses are introduced in decreasing order. -/
def atLeast (p : ComputableCAD.Poly K n) : (k : ℕ) → {m : ℕ} →
    (Fin n → Fin m) → Fin m → Prenex K m
  | 0, _, _, _ => .matrix (.truth true)
  | k+1, m, base, bound =>
    let b := Fin.castSucc ∘ base
    let r := Fin.last m
    .exists_ (Prenex.matrixAnd (.and (rootAt p b r) (below r bound.castSucc)) (atLeast p k b r))

theorem atLeast_correct (model : RealModel K) (p : ComputableCAD.Poly K n) :
    (k : ℕ) → {m : ℕ} → (base : Fin n → Fin m) → (z : Fin m) → (x : Fin m → ℝ) →
    (h : specialized model p (x ∘ base) ≠ 0) →
    (atLeast p k base z).holds model x ↔ k ≤ countBelow (sortedRoots (specialized model p (x ∘ base))) (x z)
  | 0, _, _, _, _, _ => by simp [atLeast, Prenex.holds, SignFormula.holds]
  | k+1, m, base, z, x, h => by
    change (∃ t : ℝ, (Prenex.matrixAnd _ _).holds model (Fin.snoc x t)) ↔ _
    rw [countBelow_succ (sortedRoots_order _)]
    apply exists_congr
    intro t
    let b := Fin.castSucc ∘ base
    let r := Fin.last m
    have e : Fin.snoc x t ∘ b = x ∘ base := by
      funext i
      exact @Fin.snoc_castSucc m (fun _ => ℝ) t x (base i)
    rw [Prenex.matrixAnd_correct, SignFormula.holds, rootAt_correct, below_correct]
    rw [atLeast_correct model p k b r _ (e.symm ▸ h)]
    rw [e, Fin.snoc_last, Fin.snoc_castSucc, mem_sortedRoots h]
    exact and_assoc

def rankedRow (p : ComputableCAD.Poly K n) (i : ℕ) (base : Fin n → Fin m) (z : Fin m) :
    Prenex K m :=
  let test := rootAt p base z
  let parity := if i % 2 = 1 then test else .not test
  Prenex.matrixAnd parity ((atLeast p (i / 2) base z).both (atLeast p (i / 2 + 1) base z).neg)

theorem rankedRow_correct (model : RealModel K) (p : ComputableCAD.Poly K n) (i : ℕ)
    (base : Fin n → Fin m) (z : Fin m) (x : Fin m → ℝ)
    (hn : specialized model p (x ∘ base) ≠ 0) :
    (rankedRow p i base z).holds model x ↔ rowIndex (sortedRoots (specialized model p (x ∘ base))) (x z) = i := by
  unfold rankedRow
  rw [Prenex.matrixAnd_correct, Prenex.both_correct, Prenex.neg_correct,
    atLeast_correct model p _ base z x hn, atLeast_correct model p _ base z x hn]
  have test := rootAt_correct model x p base z
  unfold rowIndex
  by_cases hr : (specialized model p (x ∘ base)).IsRoot (x z)
  · have hm := (mem_sortedRoots hn (x z)).mpr hr
    have ht := test.mpr hr
    by_cases hi : i % 2 = 1
    · simp only [hi, ite_true, ht, true_and, hm]
      omega
    · rw [ite_eq_right hi]
      change (¬ (rootAt p base z).holds model x ∧ _) ↔ _
      simp only [ht, not_true_eq_false, false_and, hm, ite_true]
      exact ⟨False.elim, fun h => by omega⟩
  · have hm := mt (mem_sortedRoots hn (x z)).mp hr
    have ht := mt test.mp hr
    by_cases hi : i % 2 = 1
    · simp only [hi, ite_true, ht, false_and, hm, ite_false]
      exact ⟨False.elim, fun h => by omega⟩
    · rw [ite_eq_right hi]
      change (¬ (rootAt p base z).holds model x ∧ _) ↔ _
      simp only [ht, not_false_eq_true, true_and, hm, ite_false, add_zero]
      omega

def monomialRow (i : ℕ) (z : Fin m) : SignFormula K m :=
  match i with
  | 0 => .atom (Multi.coordinate z) .below
  | 1 => .atom (Multi.coordinate z) .on
  | 2 => .atom (Multi.coordinate z) .above
  | _ => .truth false

theorem monomialRow_correct (model : RealModel K) (i : ℕ) (z : Fin m) (x : Fin m → ℝ) :
    (monomialRow i z).holds model x ↔ rowIndex [0] (x z) = i := by
  have rank : rowIndex [0] (x z) = if x z < 0 then 0 else if x z = 0 then 1 else 2 := by
    rcases lt_trichotomy (x z) 0 with h | h | h
    · simp [rowIndex, countBelow, h, h.not_gt, h.ne]
    · simp [rowIndex, countBelow, h]
    · simp [rowIndex, countBelow, h, h.not_gt, h.ne']
  rw [rank]
  rcases i with _ | ⟨⟩ | ⟨⟩ | i <;> rcases lt_trichotomy (x z) 0 with hl | he | hg
  all_goals first
    | simp [monomialRow, SignFormula.holds, side_on, side_below, side_above, hl, hl.ne, hl.le]
    | simp [monomialRow, SignFormula.holds, side_on, side_below, side_above, he]
    | simp [monomialRow, SignFormula.holds, side_on, side_below, side_above, hg, hg.ne', hg.not_gt]

def atRow (p : ComputableCAD.Poly K n) (i : ℕ) (base : Fin n → Fin m) (z : Fin m) : Prenex K m :=
  if p.coefficients.length ≤ 1 then .matrix (.truth (i == 0))
  else if p = ProjectionData.term p.natDegree (p.coefficient p.natDegree) then .matrix (monomialRow i z)
  else rankedRow p i base z

theorem atRow_correct (model : RealModel K) (p : ComputableCAD.Poly K n) (i : ℕ)
    (base : Fin n → Fin m) (z : Fin m) (x : Fin m → ℝ)
    (hn : specialized model p (x ∘ base) ≠ 0) :
    (atRow p i base z).holds model x ↔ rowIndex (sortedRoots (specialized model p (x ∘ base))) (x z) = i := by
  unfold atRow
  split
  · rename_i short
    have noRoot (t : ℝ) : ¬(specialized model p (x ∘ base)).IsRoot t := by
      cases e : p.coefficients with
      | nil => exact (hn (by simp [specialized, PolynomialData.polynomial, DensePolynomial.polynomial, e])).elim
      | cons a as =>
        cases as with
        | nil =>
          let b := Multi.evalHom model.hom (x ∘ base) a
          have he : specialized model p (x ∘ base) = C b := by
            simp [specialized, PolynomialData.polynomial, DensePolynomial.polynomial, e, b]
          have nb : b ≠ 0 := fun h => hn (by simp [he,h])
          simpa only [he, IsRoot.def, eval_C] using nb
        | cons a' as => simp [e] at short
    have empty : sortedRoots (specialized model p (x ∘ base)) = [] :=
      List.eq_nil_iff_forall_not_mem.mpr fun t => mt (mem_sortedRoots hn t).mp (noRoot t)
    rw [empty]
    change (i == 0) = true ↔ 0 = i
    exact beq_iff_eq.trans eq_comm
  · rename_i long
    split
    · rename_i mono
      have hd : p.natDegree ≠ 0 := by
        unfold PolynomialData.natDegree
        omega
      have poly : specialized model p (x ∘ base) =
          C (Multi.evalHom model.hom (x ∘ base) (p.coefficient p.natDegree)) * X^p.natDegree := by
        conv_lhs => rw [mono]
        simp [specialized]
      have lead : Multi.evalHom model.hom (x ∘ base) (p.coefficient p.natDegree) ≠ 0 :=
        fun h => hn (by rw [poly,h,C_0,zero_mul])
      have hs : [0] = sortedRoots (specialized model p (x ∘ base)) := by
        apply roots_eq_sorted hn (by simp)
        intro t
        simp only [List.mem_singleton,poly,IsRoot.def,eval_mul,eval_C,eval_pow,eval_X,mul_eq_zero,
          lead,false_or,pow_eq_zero_iff hd]
      change (monomialRow i z).holds model x ↔ _
      rw [← hs]
      exact monomialRow_correct model i z x
    · exact rankedRow_correct model p i base z x hn

def cellFormula (model : RealModel K) : {n : ℕ} → Code K n → Prenex K n
  | 0, .origin => .matrix (.truth true)
  | 1, .lift .origin p i => .matrix (univariateCell model p i)
  | n+2, .lift b p i => (cellFormula model b).weaken.both (atRow p i Fin.castSucc (Fin.last (n+1)))

theorem cellFormula_correct (model : RealModel K) : {n : ℕ} → (c : Code K n) →
    (h : RegularCode model c) → (x : Fin n → ℝ) →
    (cellFormula model c).holds model x ↔ x ∈ c.carrier model
  | 0, .origin, _, _ => by simp [cellFormula, Prenex.holds, SignFormula.holds, Code.carrier]
  | 1, .lift .origin p i, h, x =>
    univariateCell_correct model p i x (h.2 Fin.elim0 (mem_univ _)).1
  | n+2, .lift b p i, h, x => by
    rw [← CADStacks.snoc_dropLast x, cellFormula, Prenex.both_correct, Prenex.weaken_correct,
      cellFormula_correct model b h.1, Code.carrier_lift_snoc]
    refine and_congr_right fun hb => ?_
    let y := CADStacks.dropLast x
    let t := CADStacks.last x
    have e : Fin.snoc y t ∘ Fin.castSucc = y := by
      funext j
      exact @Fin.snoc_castSucc (n+1) (fun _ => ℝ) t y j
    have hh := h.2 y hb
    have nz : specialized model p (Fin.snoc y t ∘ Fin.castSucc) ≠ 0 := e.symm ▸ hh.1
    rw [atRow_correct model p i _ _ _ nz, e, Fin.snoc_last, realStack_rank, or_iff_right hh.2.not_ge]

end CertifiedTopology.CADDecision
