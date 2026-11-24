module

public import CertifiedTopology.CADStacks
public import Mathlib.Data.List.GetD

@[expose] public section

namespace CertifiedTopology.CylindricalData

open Polynomial CADStacks

noncomputable def countBelow (rs : List ℝ) (z : ℝ) : ℕ :=
  (rs.filter fun t => t < z).length

noncomputable def rowIndex (rs : List ℝ) (z : ℝ) : ℕ :=
  2 * countBelow rs z + if z ∈ rs then 1 else 0

theorem slicesOf_length {A : Type} (lo : Option A) (rs : List A) :
    (slicesOf lo rs).length = 2 * rs.length + 1 := by
  induction rs generalizing lo with
  | nil => rfl
  | cons a rs ih =>
    simp only [slicesOf, List.length_cons, ih]
    omega

private theorem countBelow_zero {rs : List ℝ} {z : ℝ} (h : ∀ x ∈ rs, z ≤ x) :
    countBelow rs z = 0 := by
  have e : rs.filter (fun t => decide (t < z)) = [] := List.filter_eq_nil_iff.mpr
    (fun x hx => by simp [(h x hx).not_gt])
  simp [countBelow, e]

private theorem countBelow_cons_of_lt {a z : ℝ} (h : a < z) (rs : List ℝ) :
    countBelow (a :: rs) z = countBelow rs z + 1 := by
  simp [countBelow, h]

theorem countBelow_succ {rs : List ℝ} (ord : rs.Pairwise (· < ·)) (z : ℝ) (k : ℕ) :
    k+1 ≤ countBelow rs z ↔ ∃ a ∈ rs, a < z ∧ k ≤ countBelow rs a := by
  induction rs generalizing z k with
  | nil => simp [countBelow]
  | cons a rs ih =>
    obtain ⟨head,tail⟩ := List.pairwise_cons.mp ord
    by_cases ha : a < z
    · rw [countBelow_cons_of_lt ha]
      cases k with
      | zero => exact ⟨fun _ => ⟨a,by simp,ha,Nat.zero_le _⟩, fun _ => Nat.succ_le_succ (Nat.zero_le _)⟩
      | succ k =>
        constructor
        · intro h
          obtain ⟨t,ht,htz,hk⟩ := (ih tail z k).mp (Nat.le_of_succ_le_succ h)
          exact ⟨t,List.mem_cons_of_mem _ ht,htz,by
            rw [countBelow_cons_of_lt (head _ ht)]
            omega⟩
        · rintro ⟨t,ht,htz,hk⟩
          rcases List.mem_cons.mp ht with rfl | ht'
          · have e := countBelow_zero (rs := t :: rs)
                (fun w hw => (List.mem_cons.mp hw).elim (fun eq => eq ▸ le_rfl) (fun h => (head w h).le))
            omega
          · rw [countBelow_cons_of_lt (head _ ht')] at hk
            exact Nat.succ_le_succ ((ih tail z k).mpr ⟨t,ht',htz,Nat.le_of_succ_le_succ hk⟩)
    · have h : ∀ t ∈ a :: rs, z ≤ t :=
        fun t ht => (List.mem_cons.mp ht).elim (fun eq => eq ▸ le_of_not_gt ha)
          (fun ht' => (le_of_not_gt ha).trans (head t ht').le)
      rw [countBelow_zero h]
      exact ⟨fun h => (Nat.not_succ_le_zero _ h).elim,
        fun ⟨t,ht,htz,_⟩ => ((h t ht).not_gt htz).elim⟩

private theorem find_row (lo : Option ℝ) (rs : List ℝ) (z : ℝ) (hlo : ∀ l ∈ lo, l < z)
    (ord : rs.Pairwise (· < ·)) :
    ∃ h : rowIndex rs z < (slicesOf lo rs).length,
      Univariate.contains ((slicesOf lo rs).get ⟨rowIndex rs z,h⟩) z := by
  induction rs generalizing lo with
  | nil =>
    refine ⟨by simp [rowIndex, countBelow, slicesOf], ?_⟩
    exact ⟨hlo, by simp⟩
  | cons a rs ih =>
    rcases List.pairwise_cons.mp ord with ⟨ha, hrs⟩
    rcases lt_trichotomy z a with h | rfl | h
    · have e : rowIndex (a :: rs) z = 0 := by
        have hh : ∀ q ∈ a :: rs, z < q := fun q hq =>
          (List.mem_cons.mp hq).elim (fun e => e ▸ h) (fun hm => h.trans (ha q hm))
        rw [rowIndex, countBelow_zero (fun q hq => (hh q hq).le), if_neg fun hb => (hh z hb).false]
      simp only [e, slicesOf]
      refine ⟨by simp, ⟨hlo,?_⟩⟩
      intro t ht
      have ht' : a = t := by simpa using ht
      exact ht' ▸ h
    · have e : rowIndex (z :: rs) z = 1 := by
        have hh : ∀ q ∈ z :: rs, z ≤ q := fun q hq =>
          (List.mem_cons.mp hq).elim (fun e => e ▸ le_rfl) (fun hm => (ha q hm).le)
        simp [rowIndex, countBelow_zero hh]
      simp only [e, slicesOf]
      exact ⟨by simp, rfl⟩
    · have e : rowIndex (a :: rs) z = rowIndex rs z + 2 := by
        simp only [rowIndex, countBelow, List.filter_cons, h, decide_true, Bool.true_eq, ite_true,
          List.length_cons, List.mem_cons, h.ne', false_or]
        omega
      obtain ⟨hb,hs⟩ := ih (some a) (by simpa using h) hrs
      rw [e]
      exact ⟨by simpa [slicesOf] using Nat.add_lt_add_right hb 2, hs⟩

theorem realStack_length (p : Polynomial ℝ) : (realStack p).length = 2 * (sortedRoots p).length + 1 := by
  rw [realStack, ← slicesOf_real, slicesOf_length]

theorem realStack_rank (p : Polynomial ℝ) (i : ℕ) (z : ℝ) :
    Univariate.contains ((realStack p).getD i (.sector none none)) z ↔
      (realStack p).length ≤ i ∨ rowIndex (sortedRoots p) z = i := by
  by_cases hi : i < (realStack p).length
  · obtain ⟨j₀,hj⟩ := find_row none (sortedRoots p) z (by simp) (sortedRoots_order p)
    have eq : slicesOf none (sortedRoots p) = realStack p := slicesOf_real _ _
    have j : rowIndex (sortedRoots p) z < (realStack p).length := eq ▸ j₀
    have hj' : Univariate.contains ((realStack p).get ⟨rowIndex (sortedRoots p) z,j⟩) z := by
      have e := List.getElem_of_eq eq j₀
      exact Eq.mp (congrArg (fun s => Univariate.contains s z) e) hj
    rw [or_iff_right hi.not_ge, List.getD_eq_getElem _ _ hi]
    constructor
    · intro h
      obtain ⟨_,_,unique⟩ := stack_partition p z
      have eq := (unique _ ⟨List.get_mem _ _,hj'⟩).trans
        (unique _ ⟨List.getElem_mem hi,h⟩).symm
      exact congrArg Fin.val ((realStack_nodup p).injective_get eq)
    · rintro rfl
      exact hj'
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt hi)]
    exact iff_of_true ⟨by simp, by simp⟩ (Or.inl (Nat.le_of_not_gt hi))

theorem mem_sortedRoots_iff (p : Polynomial ℝ) (z : ℝ) :
    z ∈ sortedRoots p ↔ p ≠ 0 ∧ p.IsRoot z := by
  classical
  by_cases hp : p = 0
  · simp [hp, sortedRoots]
  · simp [mem_sortedRoots hp, hp]

end CertifiedTopology.CylindricalData
