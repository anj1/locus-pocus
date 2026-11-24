module

public import CertifiedTopology.Isolation
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.Data.Finset.Sort
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

namespace CertifiedTopology.Plane

open Filter Set Polynomial
open scoped Topology

/-- A continuous family with simple roots and a local bound on their heights. -/
structure RootFamily (B : Type) [TopologicalSpace B] where
  poly : B → Polynomial ℝ
  nonzero : ∀ x, poly x ≠ 0
  eval_continuous : Continuous fun p : B × ℝ => (poly p.1).eval p.2
  derivative_continuous : Continuous fun p : B × ℝ => (poly p.1).derivative.eval p.2
  simple : ∀ x y, (poly x).eval y = 0 → (poly x).derivative.eval y ≠ 0
  locally_bounded : ∀ x, ∃ M : ℝ, ∀ᶠ u in 𝓝 x, ∀ y, (poly u).eval y = 0 → y ∈ Icc (-M) M

/-- A continuous polynomial family of fixed degree has a local Cauchy
    bound, including when the same formula has higher degree off the base. -/
noncomputable def RootFamily.ofCoefficients {B : Type} [TopologicalSpace B]
    (p : B → Polynomial ℝ) (n : ℕ) (hc : ∀ i, Continuous (fun b => (p b).coeff i))
    (hd : ∀ b, (p b).natDegree = n) (hn : ∀ b, p b ≠ 0)
    (hs : ∀ b z, (p b).eval z = 0 → (p b).derivative.eval z ≠ 0) : RootFamily B := by
  have evalCont (q : B → Polynomial ℝ) (bound : ℕ)
      (coeffCont : ∀ i, Continuous (fun b => (q b).coeff i))
      (degreeBound : ∀ b, (q b).natDegree ≤ bound) :
      Continuous fun x : B × ℝ => (q x.1).eval x.2 := by
    have eq : (fun x : B × ℝ => (q x.1).eval x.2) =
        fun x => ∑ i ∈ Finset.range (bound+1), (q x.1).coeff i * x.2^i := by
      funext x
      exact eval_eq_sum_range' (Nat.lt_succ_of_le (degreeBound x.1)) x.2
    rw [eq]
    exact continuous_finsetSum _ fun i _ => ((coeffCont i).comp continuous_fst).mul
      (continuous_snd.pow i)
  refine ⟨p, hn, evalCont p n hc (fun b => (hd b).le), ?_, hs, ?_⟩
  · apply evalCont (fun b => (p b).derivative) n
    · intro i
      simp only [coeff_derivative]
      exact (hc (i+1)).mul continuous_const
    · exact fun b => (natDegree_derivative_le (p b)).trans ((Nat.sub_le _ _).trans (hd b).le)
  · intro b
    open scoped NNReal in
    have cb : Continuous (fun x => (p x).cauchyBound) := by
      have e : (fun x => (p x).cauchyBound) = fun x =>
          (Finset.range n).sup (fun i => ‖(p x).coeff i‖₊) / ‖(p x).coeff n‖₊ + 1 := by
        funext x
        rw [cauchyBound, leadingCoeff, hd x]
      rw [e]
      apply Continuous.add ?_ continuous_const
      apply (Continuous.finset_sup_apply (fun i _ => (hc i).nnNorm)).div₀ (hc n).nnNorm
      intro x hz
      exact (leadingCoeff_ne_zero.mpr (hn x))
        (by rw [leadingCoeff, hd x]; exact nnNorm_eq_zero.mp hz)
    let M := ((p b).cauchyBound : ℝ) + 1
    have ev : ∀ᶠ x in 𝓝 b, ((p x).cauchyBound : ℝ) < M :=
      (isOpen_lt (NNReal.continuous_coe.comp cb) continuous_const).mem_nhds (by dsimp [M]; linarith)
    refine ⟨M, ev.mono fun x hx y hy => ?_⟩
    have hb : ‖y‖ < ((p x).cauchyBound : ℝ) := (IsRoot.norm_lt_cauchyBound (hn x) hy)
    rw [Real.norm_eq_abs] at hb
    obtain ⟨hl, hu⟩ := abs_lt.mp (hb.trans hx)
    exact ⟨hl.le, hu.le⟩

namespace RootFamily

variable {B : Type} [TopologicalSpace B] (P : RootFamily B)

noncomputable def roots (x : B) : Finset ℝ := (P.poly x).roots.toFinset

theorem mem_roots (x : B) (y : ℝ) : y ∈ P.roots x ↔ (P.poly x).eval y = 0 := by
  simp [roots, Polynomial.mem_roots (P.nonzero x), IsRoot.def]

private theorem positive_box {x : B} {r δ : ℝ} (hr : (P.poly x).eval r = 0)
    (hpos : 0 < (P.poly x).derivative.eval r) (hδ : 0 < δ) :
    ∃ l u, r-δ < l ∧ l < r ∧ r < u ∧ u < r+δ ∧
      ∀ᶠ v in 𝓝 x, ∃! y, y ∈ Ioo l u ∧ (P.poly v).eval y = 0 := by
  have ho : {p : B × ℝ | 0 < (P.poly p.1).derivative.eval p.2} ∈ 𝓝 (x,r) :=
    (isOpen_lt continuous_const P.derivative_continuous).mem_nhds hpos
  obtain ⟨U,hU,V,hV,huv⟩ := mem_nhds_prod_iff.mp ho
  obtain ⟨ε,hε,hsub⟩ := Metric.mem_nhds_iff.mp hV
  let e := min ε δ / 2
  have ep : 0 < e := half_pos (lt_min hε hδ)
  have eε : e < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
  have eδ : e < δ := (half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _)
  let l := r-e
  let u := r+e
  have hl : l < r := by dsimp [l]; linarith
  have hu : r < u := by dsimp [u]; linarith
  have mono (v : B) (hv : v ∈ U) : StrictMonoOn (P.poly v).eval (Icc l u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (P.poly v).continuousOn
    intro y hy
    rw [interior_Icc] at hy
    rw [(P.poly v).deriv]
    refine huv (show (v,y) ∈ U ×ˢ V from ⟨hv,hsub ?_⟩)
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [l,u] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have xU := mem_of_mem_nhds hU
  have hn : (P.poly x).eval l < 0 := by
    rw [← hr]
    exact mono x xU ⟨le_rfl,(hl.trans hu).le⟩ ⟨hl.le,hu.le⟩ hl
  have hp : 0 < (P.poly x).eval u := by
    rw [← hr]
    exact mono x xU ⟨hl.le,hu.le⟩ ⟨(hl.trans hu).le,le_rfl⟩ hu
  have ev (t : ℝ) : Continuous fun v : B => (P.poly v).eval t :=
    P.eval_continuous.comp (continuous_id.prodMk continuous_const)
  refine ⟨l,u,by dsimp [l]; linarith,hl,hu,by dsimp [u]; linarith,?_⟩
  filter_upwards [hU,(isOpen_lt (ev l) continuous_const).mem_nhds hn,
    (isOpen_lt continuous_const (ev u)).mem_nhds hp] with v hv hvl hvu
  obtain ⟨y,hy,hzero⟩ := Isolation.crossing (P.poly v) (hl.trans hu) (mul_neg_of_neg_of_pos hvl hvu)
  exact ⟨y,⟨hy,hzero⟩,fun z hz => (mono v hv).injOn
    (Ioo_subset_Icc_self hz.1) (Ioo_subset_Icc_self hy) (hz.2.trans hzero.symm)⟩

private noncomputable def negated : RootFamily B where
  poly x := -P.poly x
  nonzero x := neg_ne_zero.mpr (P.nonzero x)
  eval_continuous := by
    simp only [eval_neg]
    exact (continuous_neg.comp P.eval_continuous)
  derivative_continuous := by
    simp only [derivative_neg, eval_neg]
    exact (continuous_neg.comp P.derivative_continuous)
  simple x y := by
    simp only [derivative_neg, eval_neg, neg_ne_zero, neg_eq_zero]
    exact P.simple x y
  locally_bounded x := by simpa only [eval_neg, neg_eq_zero] using P.locally_bounded x

/-- A simple root has a unique nearby root in an arbitrarily small fixed box. -/
theorem root_box {x : B} {r δ : ℝ} (hr : (P.poly x).eval r = 0) (hδ : 0 < δ) :
    ∃ l u, r-δ < l ∧ l < r ∧ r < u ∧ u < r+δ ∧
      ∀ᶠ v in 𝓝 x, ∃! y, y ∈ Ioo l u ∧ (P.poly v).eval y = 0 := by
  rcases lt_or_gt_of_ne (P.simple x r hr) with h | h
  · simpa only [negated, eval_neg, neg_eq_zero] using
      P.negated.positive_box (by simpa [negated] using hr)
        (by simpa [negated] using neg_pos.mpr h) hδ
  · exact P.positive_box hr h hδ

/-- Compactness excludes new roots outside the boxes selected at the base point.
    The local bound excludes roots that otherwise could escape to infinity. -/
theorem eventually_roots_in {x : B} {V : Set ℝ} (hV : IsOpen V)
    (hcover : (↑(P.roots x) : Set ℝ) ⊆ V) :
    ∀ᶠ u in 𝓝 x, ∀ y, y ∈ P.roots u → y ∈ V := by
  obtain ⟨M,hM⟩ := P.locally_bounded x
  let K := Icc (-M) M \ V
  have hK : IsCompact K := isCompact_Icc.diff hV
  let Z := {p : B × K | (P.poly p.1).eval p.2.val = 0}
  have hZ : IsClosed Z := isClosed_eq
    (P.eval_continuous.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
    continuous_const
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : IsClosed (Prod.fst '' Z) := isClosedMap_fst_of_compactSpace Z hZ
  have hx : x ∉ Prod.fst '' Z := by
    rintro ⟨⟨u,y⟩,hxy,rfl⟩
    exact y.property.2 (hcover ((P.mem_roots u y.val).2 hxy))
  filter_upwards [hc.isOpen_compl.mem_nhds hx,hM] with u hu hb y hy
  by_contra hn
  have hz := (P.mem_roots u y).1 hy
  exact hu ⟨(u,⟨y,hb y hz,hn⟩),hz,rfl⟩

private theorem separated (x : B) {ε : ℝ} (he : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ < ε ∧ ∀ r ∈ P.roots x, ∀ s ∈ P.roots x, r < s → r+δ < s-δ := by
  have aux : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), ∀ r ∈ P.roots x, ∀ s ∈ P.roots x,
      r < s → r+t < s-t := by
    apply (eventually_all_finset _).2
    intro r _
    apply (eventually_all_finset _).2
    intro s _
    by_cases hrs : r < s
    · have op : IsOpen {t : ℝ | r+t < s-t} :=
        isOpen_lt (continuous_const.add continuous_id) (continuous_const.sub continuous_id)
      have hn : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), r+t < s-t :=
        op.mem_nhds (show (0 : ℝ) ∈ {t : ℝ | r+t < s-t} from by simpa using hrs)
      exact hn.mono fun _ ht _ => ht
    · exact Eventually.of_forall fun _ hh => (hrs hh).elim
  have hε : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t < ε := Iio_mem_nhds he
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have H := hpos.and ((hε.and aux).filter_mono nhdsWithin_le_nhds)
  exact H.exists

/-- Nearby fibers have the same number of distinct real roots, and the
    order-preserving matching moves each root by less than the given distance. -/
theorem eventually_match (x : B) {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ u in 𝓝 x, ∃ e : (P.roots x) ≃o (P.roots u),
      ∀ r : P.roots x, dist (e r).val r.val < ε := by
  classical
  obtain ⟨δ,hδ,hδε,hsep⟩ := P.separated x he
  choose l u hb using fun r : P.roots x => P.root_box ((P.mem_roots x r.val).mp r.property) hδ
  let V := ⋃ r : P.roots x, Ioo (l r) (u r)
  have hV : IsOpen V := isOpen_iUnion fun _ => isOpen_Ioo
  have hcv : ↑(P.roots x) ⊆ V := by
    intro r hr
    exact mem_iUnion.mpr ⟨⟨r,hr⟩,(hb ⟨r,hr⟩).2.1,(hb ⟨r,hr⟩).2.2.1⟩
  have hboxes : ∀ᶠ v in 𝓝 x, ∀ r : P.roots x,
      ∃! y, y ∈ Ioo (l r) (u r) ∧ (P.poly v).eval y = 0 :=
    eventually_all.2 fun r => (hb r).2.2.2.2
  filter_upwards [hboxes, P.eventually_roots_in hV hcv] with v hx hv
  choose f hf huniq using hx
  let F (r : P.roots x) : P.roots v := ⟨f r, (P.mem_roots v _).2 (hf r).2⟩
  have hmono : StrictMono F := by
    intro r s hrs
    change f r < f s
    exact (hf r).1.2.trans ((hb r).2.2.2.1.trans
      ((hsep r.val r.property s.val s.property hrs).trans ((hb s).1.trans (hf s).1.1)))
  have hsurj : Function.Surjective F := by
    intro y
    obtain ⟨r,hr⟩ := mem_iUnion.mp (hv y.val y.property)
    exact ⟨r,Subtype.ext (huniq r y.val ⟨hr,(P.mem_roots v _).mp y.property⟩).symm⟩
  let E : (P.roots x) ≃o (P.roots v) :=
    { Equiv.ofBijective F ⟨hmono.injective,hsurj⟩ with
      map_rel_iff' := hmono.le_iff_le }
  refine ⟨E,fun r => ?_⟩
  change dist (f r) r.val < ε
  rw [Real.dist_eq,abs_lt]
  constructor
  · linarith [(hb r).1, (hf r).1.1]
  · linarith [(hb r).2.2.2.1, (hf r).1.2]

theorem locally_constant_count : IsLocallyConstant (fun x => (P.roots x).card) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  filter_upwards [P.eventually_match x zero_lt_one] with y hy
  obtain ⟨e,_⟩ := hy
  simpa using (Fintype.card_congr e.toEquiv).symm

/-- Continuous real root sections in increasing order, indexed by the roots
    at one sample. Taking a finite set removes multiplicity. -/
noncomputable def rootSection [PreconnectedSpace B] (sample : B) (i : Fin (P.roots sample).card)
    (x : B) : ℝ :=
  (P.roots x).orderEmbOfFin (P.locally_constant_count.apply_eq_of_preconnectedSpace x sample) i

theorem section_order [PreconnectedSpace B] (sample x : B) :
    StrictMono (fun i => P.rootSection sample i x) :=
  (Finset.orderEmbOfFin _ _).strictMono

theorem section_mem [PreconnectedSpace B] (sample x : B) (i : Fin (P.roots sample).card) :
    P.rootSection sample i x ∈ P.roots x := Finset.orderEmbOfFin_mem _ _ _

theorem exists_section [PreconnectedSpace B] (sample x : B) {y : ℝ} (hy : y ∈ P.roots x) :
    ∃ i, P.rootSection sample i x = y := by
  let e := (P.roots x).orderIsoOfFin (P.locally_constant_count.apply_eq_of_preconnectedSpace x sample)
  exact ⟨e.symm ⟨y,hy⟩, congrArg Subtype.val (e.apply_symm_apply ⟨y,hy⟩)⟩

theorem continuous_section [PreconnectedSpace B] (sample : B) (i : Fin (P.roots sample).card) :
    Continuous (P.rootSection sample i) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.continuousAt_iff'.mpr
  intro ε he
  filter_upwards [P.eventually_match x he] with u hu
  obtain ⟨e,h⟩ := hu
  let f (j : Fin (P.roots sample).card) : ℝ :=
    (e ⟨P.rootSection sample j x, P.section_mem sample x j⟩).val
  have hn : StrictMono f := fun j k hjk => e.strictMono (P.section_order sample x hjk)
  have hf : f = fun j => P.rootSection sample j u :=
    Finset.orderEmbOfFin_unique _ (fun j => (e ⟨_,P.section_mem sample x j⟩).property) hn
  change dist (P.rootSection sample i u) (P.rootSection sample i x) < ε
  rw [← congrFun hf i]
  exact h _

/-- Ownership of a continuous section by a subfamily is constant whenever
    both sets of roots persist and every root of the subfamily is shared. -/
theorem section_membership {B : Type} [TopologicalSpace B] [PreconnectedSpace B]
    (P Q : RootFamily B) (subset : ∀ x, Q.roots x ⊆ P.roots x)
    (r : B → ℝ) (hr : Continuous r) (hm : ∀ x, r x ∈ P.roots x) (a b : B) :
    r a ∈ Q.roots a ↔ r b ∈ Q.roots b := by
  have lc : IsLocallyConstant (fun x => r x ∈ Q.roots x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : r x ∈ Q.roots x
    · obtain ⟨l, u, hi⟩ := P.root_box ((P.mem_roots x _).mp (hm x)) zero_lt_one
      let ε := min (r x-l) (u-r x)
      have hε : 0 < ε := lt_min (sub_pos.mpr hi.2.1) (sub_pos.mpr hi.2.2.1)
      have region : ∀ᶠ y in 𝓝 x, r y ∈ Ioo l u :=
        (isOpen_Ioo.preimage hr).mem_nhds ⟨hi.2.1, hi.2.2.1⟩
      filter_upwards [hi.2.2.2.2, region, Q.eventually_match x hε] with y uniqu hy ⟨e, close⟩
      let t := e ⟨r x,hx⟩
      have near := close ⟨r x,hx⟩
      change dist (t : ℝ) (r x) < ε at near
      rw [Real.dist_eq, abs_lt] at near
      have ht : (t : ℝ) ∈ Ioo l u := by
        have h₁ : ε ≤ r x-l := min_le_left _ _
        have h₂ : ε ≤ u-r x := min_le_right _ _
        exact ⟨by linarith [near.1], by linarith [near.2]⟩
      have eq := uniqu.unique ⟨ht, (P.mem_roots y _).mp (subset y t.property)⟩
        ⟨hy, (P.mem_roots y _).mp (hm y)⟩
      exact propext ⟨fun _ => hx, fun _ => eq ▸ t.property⟩
    · have hc := Q.eval_continuous.comp (continuous_id.prodMk hr)
      have hn := fun h => hx ((Q.mem_roots x _).mpr h)
      filter_upwards [(isOpen_ne_fun hc continuous_const).mem_nhds hn] with y hy
      exact propext ⟨fun hz => (hy ((Q.mem_roots y _).mp hz)).elim, fun hz => (hx hz).elim⟩
  exact Iff.of_eq (lc.apply_eq_of_preconnectedSpace a b)

end RootFamily
end CertifiedTopology.Plane
