module

public import CertifiedTopology.CADStacks

@[expose] public section

namespace CertifiedTopology.Plane.RootFamily

open Set Filter Polynomial
open scoped Topology

variable {B : Type} [TopologicalSpace B]

/-- Roots that share a regular common-root family cannot split inside the base cell. -/
theorem same_root (P Q C : RootFamily B) [PreconnectedSpace B]
    (shared : ∀ x t, (C.poly x).IsRoot t ↔ (P.poly x).IsRoot t ∧ (Q.poly x).IsRoot t)
    (r s : B → ℝ) (hr : Continuous r) (hs : Continuous s)
    (rp : ∀ x, (P.poly x).IsRoot (r x)) (sq : ∀ x, (Q.poly x).IsRoot (s x))
    (a b : B) : r a = s a ↔ r b = s b := by
  have eq : IsLocallyConstant (fun x => r x = s x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases h : r x = s x
    · obtain ⟨l,u,_,hl,hu,_,hb⟩ := P.root_box (rp x) zero_lt_one
      obtain ⟨l',u',_,hl',hu',_,hc⟩ := Q.root_box (sq x) zero_lt_one
      have il : r x ∈ Ioo l u := ⟨hl,hu⟩
      have iu : s x ∈ Ioo l' u' := ⟨hl',hu'⟩
      let δ := min (min (r x-l) (u-r x)) (min (r x-l') (u'-r x))
      have hδ : 0 < δ := by
        apply lt_min <;> apply lt_min <;> linarith
      have ht := (shared x (r x)).mpr ⟨rp x, h.symm ▸ sq x⟩
      obtain ⟨a,b,hla,_,_,hub,hd⟩ := C.root_box ht hδ
      have sr := (isOpen_Ioo.preimage hr).mem_nhds il
      have ss := (isOpen_Ioo.preimage hs).mem_nhds iu
      filter_upwards [hb,hc,hd,sr,ss] with y hy hz hw hya hza
      obtain ⟨t,ht,_⟩ := hw
      have both := (shared y t).mp ht.2
      have ilt : t ∈ Ioo l u := by
        have h₁ : δ ≤ r x-l := (min_le_left _ _).trans (min_le_left _ _)
        have h₂ : δ ≤ u-r x := (min_le_left _ _).trans (min_le_right _ _)
        exact ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
      have iut : t ∈ Ioo l' u' := by
        have h₁ : δ ≤ r x-l' := (min_le_right _ _).trans (min_le_left _ _)
        have h₂ : δ ≤ u'-r x := (min_le_right _ _).trans (min_le_right _ _)
        exact ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
      exact propext ⟨fun _ => h, fun _ =>
        (hy.unique ⟨hya,rp y⟩ ⟨ilt,both.1⟩).trans (hz.unique ⟨hza,sq y⟩ ⟨iut,both.2⟩).symm⟩
    · filter_upwards [(isClosed_eq hr hs).isOpen_compl.mem_nhds h] with y hy
      exact propext ⟨fun e => False.elim (hy e), fun e => False.elim (h e)⟩
  exact Iff.of_eq (eq.apply_eq_of_preconnectedSpace a b)

/-- Finite continuously varying, distinct roots give a regular monic polynomial family. -/
noncomputable def ofSections {ι : Type} [Fintype ι] (s : ι → B → ℝ)
    (hc : ∀ i, Continuous (s i)) (hi : ∀ x, Function.Injective fun i => s i x) : RootFamily B := by
  classical
  let f := fun x => ∏ i, (X - C (s i x))
  have monic (x : B) : (f x).Monic := monic_prod_X_sub_C (fun i => s i x) Finset.univ
  have coeff (j : ℕ) : Continuous fun x => (f x).coeff j := by
    have aux (t : Finset ι) (k : ℕ) : Continuous fun x => (∏ i ∈ t, (X - C (s i x))).coeff k := by
      induction t using Finset.induction generalizing k with
      | empty => simp; exact continuous_const
      | insert a t h ih =>
        simp only [Finset.prod_insert h, coeff_sub, sub_mul, coeff_C_mul]
        cases k with
        | zero =>
          simp only [coeff_X_mul_zero]
          exact continuous_const.sub ((hc a).mul (ih 0))
        | succ k =>
          simp only [coeff_X_mul]
          exact (ih k).sub ((hc a).mul (ih (k+1)))
    exact aux Finset.univ j
  have deg (x : B) : (f x).natDegree = Fintype.card ι := by
    simp [f, natDegree_prod_of_monic, monic_X_sub_C]
  refine ofCoefficients f _ coeff deg (fun x => (monic x).ne_zero) ?_
  intro x z hz
  let ts := Finset.univ.image fun i => s i x
  have ee : f x = ∏ a ∈ ts, (X - C a) := by
    rw [Finset.prod_image]
    exact fun _ _ _ _ h => hi x h
  have hz' : z ∈ ts := by
    have hr : z ∈ (f x).roots := (Polynomial.mem_roots (monic x).ne_zero).2 hz
    rw [ee, roots_prod_X_sub_C] at hr
    exact hr
  rw [ee]
  change eval z (derivative (ts.val.map (fun t => X - C t)).prod) ≠ 0
  rw [eval_multiset_prod_X_sub_C_derivative (show z ∈ ts.val from hz')]
  apply Multiset.prod_ne_zero
  intro ha
  obtain ⟨b,hb,he⟩ := Multiset.mem_map.mp ha
  have e := sub_eq_zero.mp he
  exact ts.nodup.notMem_erase (e.symm ▸ hb)

theorem ofSections_roots {ι : Type} [Fintype ι] (s : ι → B → ℝ)
    (hc : ∀ i, Continuous (s i)) (hi : ∀ x, Function.Injective fun i => s i x) (x : B) (z : ℝ) :
    ((ofSections s hc hi).poly x).IsRoot z ↔ ∃ i, s i x = z := by
  classical
  have eq : (ofSections s hc hi).poly x = ∏ i, (X - C (s i x)) := by
    unfold ofSections ofCoefficients
    rfl
  rw [eq]
  simp only [IsRoot.def, eval_prod, eval_sub, eval_X, eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and,
    sub_eq_zero]
  exact exists_congr fun _ => eq_comm

end CertifiedTopology.Plane.RootFamily
