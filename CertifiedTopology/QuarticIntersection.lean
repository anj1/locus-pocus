module

public import CertifiedTopology.PlaneGeneral
public import CertifiedTopology.QuarticProjection
public import CertifiedTopology.Extension

@[expose] public section

namespace CertifiedTopology.Quartic

open Polynomial Set Filter
open scoped Topology

abbrev Base := ℝ × ℝ
abbrev Space := Base × ℝ

noncomputable def coefficientsAt {K : Type} [Field K] (ι : K →+* ℝ) (p : Base) :
    Plane.BiPoly K →+* ℝ :=
  ((evalRingHom p.2).comp (Plane.specialize p.1)).comp (Plane.embedCoefficients ι)

noncomputable def fiberAt {K : Type} [Field K] (ι : K →+* ℝ)
    (f : TriPoly K) (p : Base) : Polynomial ℝ :=
  f.map (coefficientsAt ι p)

noncomputable def value {K : Type} [Field K] (ι : K →+* ℝ) (f : TriPoly K) (p : Space) : ℝ :=
  (fiberAt ι f p.1).eval p.2

def locus {K : Type} [Field K] (ι : K →+* ℝ) (f g : TriPoly K) : Set Space :=
  {p | value ι f p = 0 ∧ value ι g p = 0}

theorem continuous_value {K : Type} [Field K] (ι : K →+* ℝ) (f : TriPoly K) :
    Continuous (value ι f) := by
  have e : value ι f = fun p => ∑ i ∈ Finset.range (f.natDegree+1),
      Plane.value (Plane.embedCoefficients ι (f.coeff i)) p.1 * p.2^i := by
    funext p
    exact (eval_map _ _).trans (eval₂_eq_sum_range _ _)
  rw [e]
  apply continuous_finsetSum _
  intro i _
  exact ((Plane.continuous_value _).comp continuous_fst).mul (continuous_snd.pow i)

theorem isClosed_locus {K : Type} [Field K] (ι : K →+* ℝ) (f g : TriPoly K) :
    IsClosed (locus ι f g) :=
  (isClosed_eq (continuous_value ι f) continuous_const).inter
    (isClosed_eq (continuous_value ι g) continuous_const)

namespace Decision

/-- Discharge constant tests before sending the remaining tests to planar CAD. -/
noncomputable def prune {K A : Type} [Field K] [DecidableEq K] :
    Decision (Plane.BiPoly K) A → Decision (Plane.BiPoly K) A
  | .leaf a => .leaf a
  | .test c z nz =>
    match Plane.constant? c with
    | none => .test c z.prune nz.prune
    | some a => if a = 0 then z.prune else nz.prune

theorem run_prune {K A : Type} [Field K] [DecidableEq K] (ι : K →+* ℝ) (p : Base)
    (d : Decision (Plane.BiPoly K) A) :
    d.prune.run (coefficientsAt ι p) = d.run (coefficientsAt ι p) := by
  induction d with
  | leaf => rfl
  | test c z nz hz hn =>
    cases hc : Plane.constant? c with
    | none => simp [prune, hc, run, hz, hn]
    | some a =>
      have he : coefficientsAt ι p c = ι a := by
        unfold Plane.constant? at hc
        split at hc
        · rename_i hd
          have e : c = C (C ((c.coeff 0).coeff 0)) :=
            (eq_C_of_natDegree_eq_zero hd.1).trans (congrArg C (eq_C_of_natDegree_eq_zero hd.2))
          have ha := Option.some.inj hc
          change Plane.value (Plane.embedCoefficients ι c) p = _
          rw [e, ← ha]
          simp [Plane.embedCoefficients]
        · contradiction
      simp only [prune, hc, run, he, map_eq_zero]
      split <;> assumption

end Decision

noncomputable def program {K : Type} [Field K] [DecidableEq K] (f g : TriPoly K) :
    Decision (Plane.BiPoly K) (Fiber (Plane.BiPoly K)) :=
  (fiberDecision f g).prune

noncomputable def projection {K : Type} [Field K] [DecidableEq K] (f g : TriPoly K) :
    List (Plane.BiPoly K) := (program f g).tests.dedup

/-- The inputs use the cylindrical order x, y, z. The degree bound is checked
    coefficient by coefficient and includes all total degrees below four. -/
structure Equation (K : Type) [Field K] where
  poly : TriPoly K
  degree_le_four : ∀ i j k, 4 < i+j+k → ((poly.coeff k).coeff j).coeff i = 0

/-- A sparse monomial with its total-degree bound. -/
structure Term (K : Type) where
  x : ℕ
  y : ℕ
  z : ℕ
  coefficient : K
  degree_le_four : x+y+z ≤ 4

noncomputable def Term.poly {K : Type} [Field K] (t : Term K) : TriPoly K :=
  monomial t.z (monomial t.y (monomial t.x t.coefficient))

theorem Term.coeff_eq_zero {K : Type} [Field K] (t : Term K) {i j k : ℕ}
    (h : 4 < i+j+k) : ((t.poly.coeff k).coeff j).coeff i = 0 := by
  have ht := t.degree_le_four
  by_cases hz : t.z = k
  · by_cases hy : t.y = j
    · by_cases hx : t.x = i
      · omega
      · simp [Term.poly, coeff_monomial, hz, hy, hx]
    · simp [Term.poly, coeff_monomial, hz, hy]
  · simp [Term.poly, coeff_monomial, hz]

/-- Build a quartic from sparse terms. Repeated monomials are added. -/
noncomputable def Equation.ofTerms {K : Type} [Field K] (terms : List (Term K)) :
    Equation K where
  poly := (terms.map Term.poly).sum
  degree_le_four := by
    intro i j k h
    induction terms with
    | nil => simp
    | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons, coeff_add, t.coeff_eq_zero h, ih, add_zero]

theorem Term.value {K : Type} [Field K] (ι : K →+* ℝ) (t : Term K) (p : Space) :
    value ι t.poly p =
      ι t.coefficient * p.1.1^t.x * p.1.2^t.y * p.2^t.z := by
  simp [Quartic.value, fiberAt, coefficientsAt, Term.poly, Plane.embedCoefficients, Plane.specialize,
    Polynomial.map_monomial, eval_monomial]

theorem Equation.value_ofTerms {K : Type} [Field K] (ι : K →+* ℝ)
    (terms : List (Term K)) (p : Space) :
    value ι (Equation.ofTerms terms).poly p =
      (terms.map (fun t => ι t.coefficient * p.1.1^t.x * p.1.2^t.y * p.2^t.z)).sum := by
  induction terms with
  | nil => simp [Equation.ofTerms, value, fiberAt]
  | cons t ts ih =>
    change value ι (t.poly + (Equation.ofTerms ts).poly) p = _
    have ev (a b : TriPoly K) : value ι (a+b) p = value ι a p + value ι b p := by
      simp [value, fiberAt, Polynomial.map_add]
    rw [ev, t.value, ih]
    simp

theorem Equation.fiber_degree {K : Type} [Field K] (ι : K →+* ℝ)
    (q : Equation K) (p : Base) : (fiberAt ι q.poly p).natDegree ≤ 4 := by
  apply natDegree_map_le.trans
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  ext j i
  simp only [coeff_zero]
  exact q.degree_le_four i j k (by omega)

/-- A quartic common fiber is an entire line or has at most four points. -/
theorem fiber_finite_or_line {K : Type} [Field K] (ι : K →+* ℝ)
    (q r : Equation K) (p : Base) :
    (∀ z, (p,z) ∈ locus ι q.poly r.poly) ∨
      ∃ ts : Finset ℝ, ts.card ≤ 4 ∧ ∀ z, z ∈ ts ↔ (p,z) ∈ locus ι q.poly r.poly := by
  classical
  let S := locus ι q.poly r.poly
  have finiteOf (f : Equation K) (hf : fiberAt ι f.poly p ≠ 0)
      (hr : ∀ z, (p,z) ∈ S → (fiberAt ι f.poly p).IsRoot z) :
      ∃ ts : Finset ℝ, ts.card ≤ 4 ∧ ∀ z, z ∈ ts ↔ (p,z) ∈ S := by
    let roots := (fiberAt ι f.poly p).roots.toFinset
    refine ⟨roots.filter (fun z => (p,z) ∈ S), ?_, ?_⟩
    · exact (Finset.card_filter_le ..).trans
        ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans (f.fiber_degree ι p)))
    · intro z
      simp only [Finset.mem_filter, roots, Multiset.mem_toFinset, Polynomial.mem_roots hf]
      exact ⟨And.right, fun hz => ⟨hr z hz, hz⟩⟩
  by_cases hq : fiberAt ι q.poly p = 0
  · by_cases hr : fiberAt ι r.poly p = 0
    · left
      intro z
      change (fiberAt ι q.poly p).eval z = 0 ∧ (fiberAt ι r.poly p).eval z = 0
      simp [hq, hr]
    · exact Or.inr (finiteOf r hr fun _ h => h.2)
  · exact Or.inr (finiteOf q hq fun _ h => h.1)

noncomputable def projectedFiber {K : Type} [Field K] [DecidableEq K] (ι : K →+* ℝ)
    (f g : TriPoly K) (p : Base) : Fiber (Plane.BiPoly K) :=
  (program f g).run (coefficientsAt ι p)

theorem projectedFiber_spec {K : Type} [Field K] [DecidableEq K] (ι : K →+* ℝ)
    (f g : TriPoly K) (p : Base) :
    match projectedFiber ι f g p with
    | .line => ∀ t, (p,t) ∈ locus ι f g
    | .empty => ∀ t, (p,t) ∉ locus ι f g
    | .roots q d =>
      (fiberAt ι q p).natDegree = d ∧ fiberAt ι q p ≠ 0 ∧
      (∀ t, (fiberAt ι q p).IsRoot t ↔ (p,t) ∈ locus ι f g) ∧
      ∀ t, (fiberAt ι q p).IsRoot t → ¬(fiberAt ι q p).derivative.IsRoot t := by
  obtain ⟨hd, hs⟩ := fiberDecision_spec (coefficientsAt ι p) f g
  have heq (t : ℝ) := hd.isRoot t
  rw [← Decision.run_prune ι p (fiberDecision f g)] at hs
  change Fiber.Spec (coefficientsAt ι p) _ (projectedFiber ι f g p) at hs
  cases h : projectedFiber ι f g p <;> rw [h] at hs
  case line =>
    change _ = 0 at hs
    intro t
    exact (heq t).mp (by simp [hs, IsRoot.def])
  case empty =>
    intro t ht
    exact hs t ((heq t).mpr ht)
  case roots q d =>
    obtain ⟨hdegree, hn, hroots, hsimple⟩ := hs
    exact ⟨hdegree, hn, fun t => (hroots t).trans (heq t), hsimple⟩

variable {K : Type} [Field K] [DecidableEq K] (ι : K →+* ℝ) (f g : TriPoly K)

theorem projectedFiber_constant
    (d : Plane.Diagram ((projection f g).map (Plane.embedCoefficients ι)))
    {b : Plane.Cell} (hb : b ∈ d.cells) (p : b.carrier) :
    projectedFiber ι f g p.val = projectedFiber ι f g b.sample := by
  apply (program f g).run_congr
  intro c hc
  have hs := d.invariant b hb p.val p.property (Plane.embedCoefficients ι c)
    (List.mem_map_of_mem (by simpa [projection] using hc))
  exact (side_congr hs).2.1

/-- The degree remains fixed on the entire base cell, including when the
    selected polynomial has a different degree off the cell. -/
noncomputable def rootFamily (q : TriPoly K) {b : Plane.Cell} (n : ℕ)
    (hd : ∀ p : b.carrier, (fiberAt ι q p.val).natDegree = n)
    (hn : ∀ p : b.carrier, fiberAt ι q p.val ≠ 0)
    (hs : ∀ (p : b.carrier) t, (fiberAt ι q p.val).IsRoot t →
      ¬(fiberAt ι q p.val).derivative.IsRoot t) : Plane.RootFamily b.carrier where
  poly p := fiberAt ι q p.val
  nonzero := hn
  eval_continuous := (continuous_value ι q).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  derivative_continuous := by
    have e (p : b.carrier × ℝ) : (fiberAt ι q p.1.val).derivative.eval p.2 =
        value ι q.derivative (p.1.val,p.2) :=
      congrArg (eval p.2) (derivative_map q (coefficientsAt ι p.1.val))
    simp only [e]
    exact (continuous_value ι q.derivative).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  simple := hs
  locally_bounded p := by
    open scoped NNReal in
    have cb : Continuous (fun x : b.carrier => (fiberAt ι q x.val).cauchyBound) := by
      have e : (fun x : b.carrier => (fiberAt ι q x.val).cauchyBound) =
          fun x => (Finset.range n).sup
            (fun i => ‖Plane.value (Plane.embedCoefficients ι (q.coeff i)) x.val‖₊) /
            ‖Plane.value (Plane.embedCoefficients ι (q.coeff n)) x.val‖₊ + 1 := by
        funext x
        rw [cauchyBound, leadingCoeff, hd x]
        simp only [fiberAt, coeff_map]
        rfl
      rw [e]
      have hnorm (i : ℕ) : Continuous (fun x : b.carrier =>
          ‖Plane.value (Plane.embedCoefficients ι (q.coeff i)) x.val‖₊) :=
        ((Plane.continuous_value _).comp continuous_subtype_val).nnNorm
      apply Continuous.add ?_ continuous_const
      apply (Continuous.finset_sup_apply (fun i _ => hnorm i)).div₀ (hnorm n)
      intro x hz
      have hzero : (fiberAt ι q x.val).leadingCoeff = 0 := by
        rw [leadingCoeff, hd x]
        have h := nnNorm_eq_zero.mp hz
        rw [fiberAt, coeff_map]
        change coefficientsAt ι x.val (q.coeff n) = 0 at h
        exact h
      exact hn x (leadingCoeff_eq_zero.mp hzero)
    let M := ((fiberAt ι q p.val).cauchyBound : ℝ) + 1
    have hM : ((fiberAt ι q p.val).cauchyBound : ℝ) < M := by dsimp [M]; linarith
    have ev : ∀ᶠ u in 𝓝 p, ((fiberAt ι q u.val).cauchyBound : ℝ) < M :=
      (isOpen_lt (NNReal.continuous_coe.comp cb) continuous_const).mem_nhds hM
    refine ⟨M, ev.mono fun u hu y hy => ?_⟩
    have hb := (IsRoot.norm_lt_cauchyBound (hn u) (show (fiberAt ι q u.val).IsRoot y from hy))
    have hb' : ‖y‖ < ((fiberAt ι q u.val).cauchyBound : ℝ) := hb
    have hh : |y| < M := (Real.norm_eq_abs y ▸ hb').trans hu
    exact ⟨(abs_lt.mp hh).1.le, (abs_lt.mp hh).2.le⟩

/-- Cells are continuous graphs over a planar cell, or its full cylinder. -/
structure Cell where
  base : Plane.Cell
  height : Option {r : base.carrier → ℝ // Continuous r}

def Cell.carrier (c : Cell) : Set Space :=
  {p | ∃ hp : p.1 ∈ c.base.carrier, ∀ r ∈ c.height, p.2 = r.val ⟨p.1, hp⟩}

def Cell.sample (c : Cell) : Space :=
  (c.base.sample, c.height.elim 0 fun r => r.val ⟨c.base.sample, c.base.sample_mem⟩)

theorem Cell.sample_mem (c : Cell) : c.sample ∈ c.carrier := by
  cases c with
  | mk b h =>
    cases h <;> simp [Cell.sample, Cell.carrier, b.sample_mem]

theorem Cell.image_fst (c : Cell) : Prod.fst '' c.carrier = c.base.carrier := by
  ext p
  constructor
  · rintro ⟨⟨b,t⟩, ⟨hb,_⟩, rfl⟩
    exact hb
  · intro hp
    refine ⟨(p, c.height.elim 0 fun r => r.val ⟨p,hp⟩), ⟨hp,?_⟩, rfl⟩
    cases c.height <;> simp

noncomputable def Cell.graphHomeomorph (b : Plane.Cell) (r : b.carrier → ℝ) (hr : Continuous r) :
    (Cell.mk b (some ⟨r,hr⟩)).carrier ≃ₜ b.carrier where
  toFun p := ⟨p.val.1, p.property.choose⟩
  invFun p := ⟨(p.val, r p), p.property, by simp⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (p.property.choose_spec ⟨r,hr⟩ (by simp)).symm
  right_inv _ := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.prodMk hr).subtype_mk _

noncomputable def Cell.cylinderHomeomorph (b : Plane.Cell) :
    (Cell.mk b none).carrier ≃ₜ b.carrier × ℝ := by
  have eq : (Cell.mk b none).carrier = b.carrier ×ˢ (Set.univ : Set ℝ) := by
    ext
    simp [Cell.carrier]
  rw [eq]
  exact (Homeomorph.Set.prod _ _).trans
    ((Homeomorph.refl b.carrier).prodCongr (Homeomorph.Set.univ ℝ))

theorem Cell.contractible (c : Cell) : ContractibleSpace c.carrier := by
  obtain ⟨b, h⟩ := c
  let := b.contractible
  cases h with
  | none => exact (Cell.cylinderHomeomorph b).contractibleSpace
  | some r => exact (Cell.graphHomeomorph b r.val r.property).contractibleSpace

/-- A checked stack over one planar cell, restricted to the common zero set. -/
structure Stack (b : Plane.Cell) (S : Set Space) where
  cells : List Cell
  base_eq : ∀ c ∈ cells, c.base = b
  covers : ∀ (p : b.carrier) t, (p.val,t) ∈ S ↔ ∃ c ∈ cells, (p.val,t) ∈ c.carrier
  unique : ∀ (p : b.carrier) t, ∀ c ∈ cells, ∀ e ∈ cells,
    (p.val,t) ∈ c.carrier → (p.val,t) ∈ e.carrier → c = e

def Stack.empty (b : Plane.Cell) (S : Set Space) (h : ∀ (p : b.carrier) t, (p.val,t) ∉ S) :
    Stack b S where
  cells := []
  base_eq := by simp
  covers p t := by simpa using h p t
  unique := by simp

def Stack.line (b : Plane.Cell) (S : Set Space) (h : ∀ (p : b.carrier) t, (p.val,t) ∈ S) :
    Stack b S where
  cells := [⟨b, none⟩]
  base_eq := by simp
  covers p t := by simp [Cell.carrier, p.property, h p t]
  unique := by simp

def Stack.ofSections (b : Plane.Cell) (S : Set Space) {n : ℕ}
    (sections : Fin n → b.carrier → ℝ) (hcont : ∀ i, Continuous (sections i))
    (hinj : ∀ p, Function.Injective fun i => sections i p)
    (h : ∀ (p : b.carrier) t, (p.val,t) ∈ S ↔ ∃ i, sections i p = t) : Stack b S := by
  let cell (i : Fin n) : Cell := ⟨b, some ⟨sections i, hcont i⟩⟩
  have mem (p : b.carrier) (t : ℝ) (i : Fin n) :
      (p.val,t) ∈ (cell i).carrier ↔ t = sections i p := by
    simp [Cell.carrier, cell, p.property]
  refine ⟨(List.finRange _).map cell, ?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
    rfl
  · intro p t
    rw [h p t]
    constructor
    · rintro ⟨i,hi⟩
      exact ⟨cell i, List.mem_map_of_mem (by simp), (mem p t i).mpr hi.symm⟩
    · rintro ⟨c,hc,ht⟩
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
      exact ⟨i, ((mem p t i).mp ht).symm⟩
  · intro p t c hc e he hpc hpe
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hc
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp he
    exact congrArg cell (hinj p
      (((mem p t i).mp hpc).symm.trans ((mem p t j).mp hpe)))

/-- An exact root table for the selected polynomial at the base sample. -/
structure RootTable (q : Polynomial ℝ) where
  roots : List ℝ
  sorted : roots.Pairwise (· < ·)
  exactRoots : ∀ t, t ∈ roots ↔ q.IsRoot t

/-- A univariate covering table can contain auxiliary cuts. Keep exactly
    the sections where the chosen polynomial vanishes. -/
noncomputable def RootTable.ofCutTable {q : Polynomial ℝ} (hq : q ≠ 0)
    (d : Univariate.CutTable [q]) : RootTable q where
  roots := d.roots.filter fun t => decide (q.IsRoot t)
  sorted := d.sorted.filter _
  exactRoots t := by
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun h => ⟨d.covers q (by simp) hq t h, h⟩⟩

noncomputable def Stack.ofRoots (b : Plane.Cell) (S : Set Space)
    (P : Plane.RootFamily b.carrier)
    (h : ∀ (p : b.carrier) t, t ∈ P.roots p ↔ (p.val,t) ∈ S)
    (table : Option (RootTable (P.poly ⟨b.sample, b.sample_mem⟩)) := none) : Stack b S := by
  letI := b.contractible
  let p₀ : b.carrier := ⟨b.sample, b.sample_mem⟩
  let n := (P.roots p₀).card
  let build {m : ℕ} (e : Fin m ≃ Fin n) (sections : Fin m → b.carrier → ℝ)
      (he : sections = fun i => P.rootSection p₀ (e i)) :=
    Stack.ofSections b S sections
      (fun i => by rw [he]; exact P.continuous_section p₀ (e i))
      (fun p => by rw [he]; exact (P.section_order p₀ p).injective.comp e.injective)
      (fun p t => by
        rw [he]
        refine (h p t).symm.trans ⟨?_, fun ⟨i,hi⟩ => hi ▸ P.section_mem p₀ p (e i)⟩
        intro ht
        obtain ⟨i,hi⟩ := P.exists_section p₀ p ht
        exact ⟨e.symm i, by simpa only [Equiv.apply_symm_apply] using hi⟩)
  cases table with
  | none => exact build (Equiv.refl (Fin n)) (P.rootSection p₀) rfl
  | some cert =>
    have hset : cert.roots.toFinset = P.roots p₀ := by
      ext t
      rw [List.mem_toFinset, cert.exactRoots, P.mem_roots]
      rfl
    have hlen : cert.roots.length = n := by
      rw [← List.toFinset_card_of_nodup (cert.sorted.imp (fun h => h.ne)), hset]
    let e := (Fin.castOrderIso hlen).toEquiv
    have hsample : cert.roots.get = fun i => P.rootSection p₀ (e i) p₀ :=
      (Finset.orderEmbOfFin_unique hlen.symm
        (fun i => (P.mem_roots p₀ _).mpr ((cert.exactRoots _).mp (List.get_mem _ i)))
        (fun _ _ hi => cert.sorted.rel_get_of_lt hi)).trans
        (Finset.orderEmbOfFin_unique hlen.symm (fun i => P.section_mem p₀ p₀ (e i))
          ((P.section_order p₀ p₀).comp (Fin.castOrderIso hlen).strictMono)).symm
    let sections (i : Fin cert.roots.length) (p : b.carrier) :=
      if p = p₀ then cert.roots.get i else P.rootSection p₀ (e i) p
    refine build e sections ?_
    funext i p
    by_cases hp : p = p₀
    · subst p
      simpa [sections] using congrFun hsample i
    · simp only [sections, ite_eq_right hp]

theorem Stack.ofRoots_table_samples (b : Plane.Cell) (S : Set Space)
    (P : Plane.RootFamily b.carrier)
    (h : ∀ (p : b.carrier) t, t ∈ P.roots p ↔ (p.val,t) ∈ S)
    (table : RootTable (P.poly ⟨b.sample, b.sample_mem⟩)) :
    ((ofRoots b S P h (some table)).cells.map (fun c => c.sample.2)) = table.roots := by
  simp [ofRoots, ofSections, Cell.sample, List.finRange, List.map_ofFn, Function.comp_def]

/-- A linear fiber can be lifted by evaluation and division at every point. -/
noncomputable def Stack.ofLinear (b : Plane.Cell) (S : Set Space) (q : TriPoly K)
    (hd : ∀ p : b.carrier, (fiberAt ι q p.val).natDegree = 1)
    (hroot : ∀ (p : b.carrier) t, (fiberAt ι q p.val).IsRoot t ↔ (p.val,t) ∈ S) : Stack b S := by
  let a (p : b.carrier) := Plane.value (Plane.embedCoefficients ι (q.coeff 1)) p.val
  let c (p : b.carrier) := Plane.value (Plane.embedCoefficients ι (q.coeff 0)) p.val
  have hcoeff (p : b.carrier) (i : ℕ) :
      (fiberAt ι q p.val).coeff i = Plane.value (Plane.embedCoefficients ι (q.coeff i)) p.val := by
    rw [fiberAt, coeff_map]
    rfl
  have ha (p : b.carrier) : a p ≠ 0 := by
    have hpos : 0 < (fiberAt ι q p.val).natDegree := by simp [hd p]
    have hn : fiberAt ι q p.val ≠ 0 := by
      intro hz
      rw [hz, natDegree_zero] at hpos
      exact (lt_irrefl _ hpos)
    dsimp [a]
    rw [← hcoeff p 1, ← hd p, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hn
  let height (p : b.carrier) := -c p / a p
  have cont : Continuous height :=
    (((Plane.continuous_value _).comp continuous_subtype_val).neg).div
      ((Plane.continuous_value _).comp continuous_subtype_val) ha
  refine Stack.ofSections b S (n := 1) (fun _ => height) (fun _ => cont)
    (fun _ _ _ _ => Subsingleton.elim _ _) fun p t => ?_
  have ev : (fiberAt ι q p.val).eval t = c p + a p * t := by
    rw [eval_eq_sum_range, hd p]
    simp [Finset.sum_range_succ, hcoeff, c, a]
  rw [← hroot, IsRoot.def, ev]
  have iff₀ : c p + a p * t = 0 ↔ height p = t := by
    change _ ↔ -c p / a p = t
    rw [div_eq_iff (ha p)]
    constructor <;> intro h <;> linarith [mul_comm (a p) t]
  exact iff₀.trans ⟨fun h => ⟨0,h⟩, fun ⟨_,h⟩ => h⟩

/-- The sample chooses one fiber decision for the entire planar cell. -/
noncomputable def lift (d : Plane.Diagram ((projection f g).map (Plane.embedCoefficients ι)))
    (b : Plane.Cell) (hb : b ∈ d.cells)
    (tables : (q : TriPoly K) → Option (RootTable (fiberAt ι q b.sample)) := fun _ => none) :
    Stack b (locus ι f g) := by
  have spec (p : b.carrier) := projectedFiber_spec ι f g p.val
  have hc (p : b.carrier) := projectedFiber_constant ι f g d hb p
  cases h : projectedFiber ι f g b.sample with
  | line =>
    exact Stack.line b _ fun p => by
      simpa only [hc p, h] using spec p
  | empty =>
    exact Stack.empty b _ fun p => by
      simpa only [hc p, h] using spec p
  | roots q n =>
    have hr (p : b.carrier) : (fiberAt ι q p.val).natDegree = n ∧ fiberAt ι q p.val ≠ 0 ∧
        (∀ t, (fiberAt ι q p.val).IsRoot t ↔ (p.val,t) ∈ locus ι f g) ∧
        ∀ t, (fiberAt ι q p.val).IsRoot t → ¬(fiberAt ι q p.val).derivative.IsRoot t := by
      simpa only [hc p, h] using spec p
    by_cases hlinear : n = 1
    · exact Stack.ofLinear ι b _ q (fun p => (hr p).1.trans hlinear) (fun p => (hr p).2.2.1)
    let P := rootFamily ι q n (fun p => (hr p).1) (fun p => (hr p).2.1)
      (fun p => (hr p).2.2.2)
    exact Stack.ofRoots b _ P (fun p t => (P.mem_roots p t).trans ((hr p).2.2.1 t))
      (tables q)

variable (d : Plane.Diagram ((projection f g).map (Plane.embedCoefficients ι)))

abbrev SampleTables :=
  (b : Plane.Cell) → b ∈ d.cells → (q : TriPoly K) → Option (RootTable (fiberAt ι q b.sample))

noncomputable def solve (tables : SampleTables ι f g d := fun _ _ _ => none) : List Cell :=
  d.cells.attach.flatMap fun b => (lift ι f g d b.val b.property (tables b.val b.property)).cells

variable (tables : SampleTables ι f g d)

theorem mem_solve {c : Cell} :
    c ∈ solve ι f g d tables ↔ ∃ (b : Plane.Cell) (hb : b ∈ d.cells),
      c ∈ (lift ι f g d b hb (tables b hb)).cells := by
  simp [solve, List.mem_flatMap]

theorem solve_base_mem {c : Cell} (hc : c ∈ solve ι f g d tables) : c.base ∈ d.cells := by
  obtain ⟨b,hb,hm⟩ := (mem_solve ι f g d tables).mp hc
  simpa only [(lift ι f g d b hb (tables b hb)).base_eq c hm] using hb

theorem solve_cover (p : Space) :
    p ∈ locus ι f g ↔ ∃ c ∈ solve ι f g d tables, p ∈ c.carrier := by
  constructor
  · intro hp
    obtain ⟨b,⟨hb,hpb⟩,_⟩ := d.partition p.1
    obtain ⟨c,hc,hpc⟩ := ((lift ι f g d b hb (tables b hb)).covers ⟨p.1,hpb⟩ p.2).mp hp
    exact ⟨c,(mem_solve ι f g d tables).mpr ⟨b,hb,hc⟩,hpc⟩
  · rintro ⟨c,hc,hp⟩
    obtain ⟨b,hb,hm⟩ := (mem_solve ι f g d tables).mp hc
    let l := lift ι f g d b hb (tables b hb)
    have hpb : p.1 ∈ b.carrier := (l.base_eq c hm) ▸ hp.choose
    exact (l.covers ⟨p.1,hpb⟩ p.2).mpr ⟨c,hm,hp⟩

theorem solve_disjoint {c e : Cell} (hc : c ∈ solve ι f g d tables)
    (he : e ∈ solve ι f g d tables) (hne : c ≠ e) : Disjoint c.carrier e.carrier := by
  refine disjoint_left.mpr ?_
  intro p hpc hpe
  obtain ⟨b,hb,hm⟩ := (mem_solve ι f g d tables).mp hc
  obtain ⟨a,ha,hn⟩ := (mem_solve ι f g d tables).mp he
  have hpb : p.1 ∈ b.carrier := (lift ι f g d b hb (tables b hb)).base_eq c hm ▸ hpc.choose
  have hpa : p.1 ∈ a.carrier := (lift ι f g d a ha (tables a ha)).base_eq e hn ▸ hpe.choose
  obtain ⟨_,_,unique⟩ := d.partition p.1
  have eq : a = b := (unique _ ⟨ha,hpa⟩).trans (unique _ ⟨hb,hpb⟩).symm
  subst a
  exact hne ((lift ι f g d b hb (tables b hb)).unique ⟨p.1,hpb⟩ p.2 c hm e hn hpc hpe)

theorem solve_correct (p : Space) (hp : p ∈ locus ι f g) :
    ∃! c, c ∈ solve ι f g d tables ∧ p ∈ c.carrier := by
  obtain ⟨c,hc,hpc⟩ := (solve_cover ι f g d tables p).mp hp
  refine ⟨c,⟨hc,hpc⟩,?_⟩
  rintro e ⟨he,hpe⟩
  by_contra hne
  exact (disjoint_left.mp (solve_disjoint ι f g d tables he hc hne)) hpe hpc

theorem solve_cylindrical {c e : Cell} (hc : c ∈ solve ι f g d tables)
    (he : e ∈ solve ι f g d tables) :
    Prod.fst '' c.carrier = Prod.fst '' e.carrier ∨
      Disjoint (Prod.fst '' c.carrier) (Prod.fst '' e.carrier) := by
  rw [Cell.image_fst, Cell.image_fst]
  by_cases h : c.base = e.base
  · exact Or.inl (congrArg Plane.Cell.carrier h)
  · right
    refine disjoint_left.mpr fun p hp he' => ?_
    obtain ⟨_,_,unique⟩ := d.partition p
    exact h ((unique _ ⟨solve_base_mem ι f g d tables hc,hp⟩).trans
      (unique _ ⟨solve_base_mem ι f g d tables he,he'⟩).symm)


theorem Cell.cell_model {c : Cell}
    {s t : Slice ℝ} (h : Nonempty (c.base.carrier ≃ₜ Plane.strip s × Plane.strip t)) :
    ∃ u : Slice ℝ, Nonempty (c.carrier ≃ₜ (Plane.strip s × Plane.strip t) × Plane.strip u) := by
  obtain ⟨e⟩ := h
  obtain ⟨b, ht⟩ := c
  cases ht with
  | none =>
    have eq : Plane.strip (.sector none none) = (Set.univ : Set ℝ) := by
      ext
      simp [Plane.strip, Univariate.contains, Slice.Contains]
    refine ⟨.sector none none, ⟨(Cell.cylinderHomeomorph b).trans ?_⟩⟩
    rw [eq]
    exact e.prodCongr (Homeomorph.Set.univ ℝ).symm
  | some r =>
    have eq : Plane.strip (.sectionAt 0) = ({0} : Set ℝ) := rfl
    refine ⟨.sectionAt 0, ⟨(Cell.graphHomeomorph b r.val r.property).trans ?_⟩⟩
    rw [eq]
    exact e.trans (Homeomorph.prodUnique _ _).symm

theorem solve_cylindrical_x
    (hx : ∀ b ∈ d.cells, ∀ a ∈ d.cells,
      Prod.fst '' b.carrier = Prod.fst '' a.carrier ∨
        Disjoint (Prod.fst '' b.carrier) (Prod.fst '' a.carrier))
    {c e : Cell} (hc : c ∈ solve ι f g d tables) (he : e ∈ solve ι f g d tables) :
    (fun p : Space => p.1.1) '' c.carrier = (fun p : Space => p.1.1) '' e.carrier ∨
      Disjoint ((fun p : Space => p.1.1) '' c.carrier) ((fun p : Space => p.1.1) '' e.carrier) := by
  rw [← Set.image_image Prod.fst Prod.fst c.carrier, ← Set.image_image Prod.fst Prod.fst e.carrier,
    c.image_fst, e.image_fst]
  exact hx c.base (solve_base_mem ι f g d tables hc) e.base (solve_base_mem ι f g d tables he)

/-- Total specification over any coefficient field embedded in the reals.
    Both projection levels can operate in the coefficient field. -/
noncomputable def decomposeOver [CharZero K] (q r : Equation K) : List Cell :=
  solve ι q.poly r.poly (Plane.solveOver ι (projection q.poly r.poly))

theorem decomposeOver_cover [CharZero K] (q r : Equation K) (p : Space) :
    p ∈ locus ι q.poly r.poly ↔ ∃ c ∈ decomposeOver ι q r, p ∈ c.carrier :=
  solve_cover ι _ _ _ (fun _ _ _ => none) p

theorem decomposeOver_correct [CharZero K] (q r : Equation K) (p : Space)
    (hp : p ∈ locus ι q.poly r.poly) :
    ∃! c, c ∈ decomposeOver ι q r ∧ p ∈ c.carrier :=
  solve_correct ι _ _ _ (fun _ _ _ => none) p hp

theorem decomposeOver_cell_model [CharZero K] (q r : Equation K)
    {c : Cell} (hc : c ∈ decomposeOver ι q r) :
    ∃ s t u : Slice ℝ, Nonempty
      (c.carrier ≃ₜ (Plane.strip s × Plane.strip t) × Plane.strip u) := by
  have hb := solve_base_mem ι _ _ _ (fun _ _ _ => none) hc
  obtain ⟨s,_,t,hm,_⟩ := Plane.solveWith_cell_model (Plane.Projection.fromEmbedded ι _) hb
  obtain ⟨u,hu⟩ := Cell.cell_model hm
  exact ⟨s,t,u,hu⟩

theorem decomposeOver_cylindrical [CharZero K] (q r : Equation K)
    {c e : Cell} (hc : c ∈ decomposeOver ι q r) (he : e ∈ decomposeOver ι q r) :
    (Prod.fst '' c.carrier = Prod.fst '' e.carrier ∨
      Disjoint (Prod.fst '' c.carrier) (Prod.fst '' e.carrier)) ∧
    ((fun p : Space => p.1.1) '' c.carrier = (fun p : Space => p.1.1) '' e.carrier ∨
      Disjoint ((fun p : Space => p.1.1) '' c.carrier) ((fun p : Space => p.1.1) '' e.carrier)) :=
  ⟨solve_cylindrical ι _ _ _ (fun _ _ _ => none) hc he,
    solve_cylindrical_x ι _ _ _ (fun _ _ _ => none)
      (fun _ hb _ ha => Plane.solveWith_cylindrical (Plane.Projection.fromEmbedded ι _) hb ha) hc he⟩

noncomputable def decompose (q r : Equation ℝ) : List Cell :=
  decomposeOver (RingHom.id ℝ) q r

noncomputable def decomposeRealAlg (q r : Equation RealAlg) : List Cell :=
  decomposeOver (algebraMap RealAlg ℝ) q r

end CertifiedTopology.Quartic
