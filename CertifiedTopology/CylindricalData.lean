module

public import CertifiedTopology.MultivariateData
public import CertifiedTopology.RootSamples
public import CertifiedTopology.PlaneNormalize
public import CertifiedTopology.PlaneRoots

@[expose] public section

namespace CertifiedTopology.CylindricalData

open Polynomial Set ExecutableIsolation

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A sample point with an executable coefficient field at this node.
    Different branches can use different finite algebraic extensions. -/
structure ExactPoint (original : RealModel K) (n : ℕ) where
  field : Type
  [arithmetic : Field field]
  [order : LinearOrder field]
  [orderedRing : IsStrictOrderedRing field]
  model : RealModel field
  coefficients : K →+* field
  point : Fin n → field
  compatible : model.hom.comp coefficients = original.hom

attribute [instance] ExactPoint.arithmetic ExactPoint.order ExactPoint.orderedRing

namespace ExactPoint

variable {model : RealModel K} {n : ℕ}

noncomputable def value (p : ExactPoint model n) : Fin n → ℝ := p.model.hom ∘ p.point

def origin (model : RealModel K) : ExactPoint model 0 :=
  ⟨K, model, RingHom.id K, Fin.elim0, by ext; rfl⟩

def extend (p : ExactPoint model n) : AlgebraicRoot.Sample p.model → ExactPoint model (n+1)
  | .rational q =>
    ⟨p.field, p.model, p.coefficients, Fin.snoc p.point (q : p.field), p.compatible⟩
  | .base a =>
    ⟨p.field, p.model, p.coefficients, Fin.snoc p.point a, p.compatible⟩
  | .algebraic r =>
    ⟨AlgebraicField.Number r, AlgebraicField.realModel r,
      (AlgebraicField.baseMap r).comp p.coefficients,
      Fin.snoc (AlgebraicField.baseMap r ∘ p.point) (AlgebraicField.generator r), by
        rw [AlgebraicField.realModel_hom, ← RingHom.comp_assoc]
        have eq : (AlgebraicField.embedding r).comp (AlgebraicField.baseMap r) = p.model.hom := by
          ext x
          exact AlgebraicField.embedding_baseMap r x
        rw [eq, p.compatible]⟩

theorem value_extend (p : ExactPoint model n) (a : AlgebraicRoot.Sample p.model) :
    (p.extend a).value = Fin.snoc p.value (a.value p.model) := by
  funext i
  cases a with
  | rational q =>
    cases i using Fin.lastCases with
    | last =>
      simp only [extend, value, AlgebraicRoot.Sample.value, Function.comp_apply, Fin.snoc_last]
      exact map_ratCast p.model.hom q
    | cast j =>
      simp only [extend, value, Function.comp_apply, Fin.snoc_castSucc]
      rfl
  | base a =>
    cases i using Fin.lastCases <;> simp [extend, value, AlgebraicRoot.Sample.value, Function.comp_apply] <;> rfl
  | algebraic a =>
    cases i using Fin.lastCases with
    | last =>
      simp only [extend, value, AlgebraicRoot.Sample.value, Function.comp_apply, Fin.snoc_last,
        AlgebraicField.realModel_hom]
      exact AlgebraicField.embedding_generator a
    | cast j =>
      simp only [extend, value, Function.comp_apply, Fin.snoc_castSucc, AlgebraicField.realModel_hom]
      exact AlgebraicField.embedding_baseMap a (p.point j)

omit [IsStrictOrderedRing K] in
theorem value_eval (p : ExactPoint model n) (f : Multi K n) :
    p.model.hom (Multi.evalHom p.coefficients p.point f) = Multi.evalHom model.hom p.value f := by
  rw [Multi.evalHom_comp, p.compatible]
  rfl

def fiber (p : ExactPoint model n) (f : PolynomialData (Multi K n)) : PolynomialData p.field :=
  PolynomialData.mapData (Multi.evalHom p.coefficients p.point) f

omit [IsStrictOrderedRing K] in
theorem fiber_correct (p : ExactPoint model n) (f : PolynomialData (Multi K n)) :
    realPoly p.model.hom (p.fiber f).coefficients = f.polynomial.map (Multi.evalHom model.hom p.value) := by
  change ((p.fiber f).polynomial.map p.model.hom) = _
  rw [fiber, PolynomialData.polynomial_mapData, Polynomial.map_map]
  congr 1
  ext a
  exact value_eval p a

end ExactPoint

noncomputable def sortedRoots (p : Polynomial ℝ) : List ℝ :=
  List.ofFn (fun i => (p.roots.toFinset.orderEmbOfFin rfl i : ℝ))

theorem sortedRoots_order (p : Polynomial ℝ) : (sortedRoots p).Pairwise (· < ·) := by
  apply List.pairwise_ofFn.mpr
  exact (p.roots.toFinset.orderEmbOfFin rfl).strictMono

theorem mem_sortedRoots {p : Polynomial ℝ} (hn : p ≠ 0) (x : ℝ) :
    x ∈ sortedRoots p ↔ p.IsRoot x := by
  rw [sortedRoots, List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩
    exact (Polynomial.mem_roots hn).mp (Multiset.mem_toFinset.mp (Finset.orderEmbOfFin_mem _ _ _))
  · intro hx
    have hm : x ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hn).mpr hx)
    let e := p.roots.toFinset.orderIsoOfFin rfl
    exact ⟨e.symm ⟨x,hm⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x,hm⟩)⟩

theorem roots_eq_sorted {p : Polynomial ℝ} (hn : p ≠ 0) {rs : List ℝ}
    (ord : rs.Pairwise (· < ·)) (members : ∀ x, x ∈ rs ↔ p.IsRoot x) : rs = sortedRoots p := by
  classical
  have nd : rs.Nodup := ord.imp LT.lt.ne
  have nd' : (sortedRoots p).Nodup := (sortedRoots_order _).imp LT.lt.ne
  have perm : rs.Perm (sortedRoots p) :=
    List.perm_ext_iff_of_nodup nd nd' |>.mpr fun x => (members x).trans (mem_sortedRoots hn x).symm
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => (hab.asymm hba).elim) ord
    (sortedRoots_order _) perm

noncomputable def realStack (p : Polynomial ℝ) : List (Slice ℝ) :=
  slices (n := 0) none (sortedRoots p)

theorem stack_partition (p : Polynomial ℝ) (x : ℝ) :
    ∃! s, s ∈ realStack p ∧ Univariate.contains s x :=
  slice_partition (n := 0) () (sortedRoots_order p) none (by simp [Lower]) x (by simp [Lower])

/-- A stack cell stores the polynomial and its section/sector index.
    Its real interpretation uses the ordered roots at the given base point. -/
inductive Code (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K] : ℕ → Type
  | origin : Code K 0
  | lift {n : ℕ} (base : Code K n) (source : PolynomialData (Multi K n)) (row : ℕ) : Code K (n+1)

namespace Code

def dimension : {n : ℕ} → Code K n → ℕ
  | 0, .origin => 0
  | n+1, .lift base _ row => base.dimension + if row % 2 = 0 then 1 else 0

noncomputable def carrier (model : RealModel K) : {n : ℕ} → Code K n → Set (Fin n → ℝ)
  | 0, .origin => univ
  | n+1, .lift base source row =>
    {p |
      let x := fun i : Fin n => p i.castSucc
      x ∈ carrier model base ∧
        Univariate.contains
          ((realStack (source.polynomial.map (Multi.evalHom model.hom x))).getD row (.sector none none))
          (p (Fin.last n)) }

theorem carrier_lift_snoc (model : RealModel K) {n : ℕ} (b : Code K n)
    (q : PolynomialData (Multi K n)) (i : ℕ) (x : Fin n → ℝ) (y : ℝ) :
    Fin.snoc x y ∈ carrier model (.lift b q i) ↔
      x ∈ b.carrier model ∧
        Univariate.contains
          ((realStack (q.polynomial.map (Multi.evalHom model.hom x))).getD i (.sector none none)) y := by
  simp only [carrier, mem_ofPred_eq, Fin.snoc_castSucc, Fin.snoc_last]

end Code
end CertifiedTopology.CylindricalData
