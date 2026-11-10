import A401948Lean.Classification
import A401948Lean.CountingDP
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-! The end-to-end connection between the geometric count and the DP. -/

namespace Erdos607

open Finset
open scoped BigOperators

private theorem prefixCost_reverse_ofFn (r : ℕ) {i : ℕ} (s : Fin i → ℕ) :
    prefixCost r (List.ofFn s).reverse = ∑ j : Fin i, contribution r (j.val+1) (s j) := by
  induction i with
  | zero => simp [prefixCost]
  | succ i ih =>
    rw [List.ofFn_succ']
    simp only [List.concat_eq_append, List.reverse_append, List.reverse_singleton,
      List.singleton_append, prefixCost, List.length_reverse, List.length_ofFn]
    rw [ih, Fin.sum_univ_castSucc]
    simp

private def listProfile (xs : List ℕ) : Set ℕ :=
  insert 2 {a | a ∈ xs}

private theorem countByLength_eq_lists (n r : ℕ) (hr : 2 ≤ r) :
    countByLength n r = (completedLists n r).ncard := by
  let S := completedLists n r
  let T := {A | ∃ s : Fin r → ℕ, 2 ≤ r ∧ StrictMono s ∧ (∀ i, 3 ≤ s i) ∧
    required s ≤ n ∧ A = insert 2 (Set.range s)}
  change T.ncard = S.ncard
  symm
  apply Set.ncard_congr (fun xs _ => listProfile xs)
  · intro xs hx
    obtain ⟨hlen,hpair,hge,hcost⟩ := hx
    have hlen' : xs.reverse.length = r := by simp [hlen]
    let s (i : Fin r) := xs.reverse.get (Fin.cast hlen'.symm i)
    have he : List.ofFn s = xs.reverse := by
      exact (List.ofFn_congr hlen' (List.get xs.reverse)).symm.trans (List.ofFn_get _)
    have hs : StrictMono s := by
      have hp : (List.ofFn s).Pairwise (· < ·) := by rw [he]; exact List.pairwise_reverse.mpr hpair
      exact List.pairwise_ofFn.mp hp
    have hrange (a : ℕ) : a ∈ Set.range s ↔ a ∈ xs := by
      rw [← List.mem_ofFn',he,List.mem_reverse]
    refine ⟨s,hr,hs,fun i => hge _ ((hrange _).mp ⟨i,rfl⟩),?_,?_⟩
    · have h := prefixCost_reverse_ofFn r s
      rw [he,List.reverse_reverse] at h
      exact (show prefixCost r xs = required s from h) ▸ hcost
    · ext a
      exact or_congr Iff.rfl (hrange a).symm
  · intro xs ys hx hy he
    obtain ⟨_,hpx,hxge,_⟩ := hx
    obtain ⟨_,hpy,hyge,_⟩ := hy
    have hmem (a : ℕ) : a ∈ xs ↔ a ∈ ys := by
      have heq : a ∈ listProfile xs ↔ a ∈ listProfile ys := by rw [he]
      change (a = 2 ∨ a ∈ xs) ↔ (a = 2 ∨ a ∈ ys) at heq
      constructor
      · intro hx
        have := hxge a hx
        exact (heq.mp (Or.inr hx)).resolve_left (by omega)
      · intro hy
        have := hyge a hy
        exact (heq.mpr (Or.inr hy)).resolve_left (by omega)
    have hp := (List.perm_ext_iff_of_nodup (hpx.imp (fun h => ne_of_gt h))
      (hpy.imp (fun h => ne_of_gt h))).mpr hmem
    exact hp.eq_of_pairwise' (hpx.imp (fun h => le_of_lt h)) (hpy.imp (fun h => le_of_lt h))
  · rintro A ⟨s,_,hs,hmin,hcost,rfl⟩
    let xs := (List.ofFn s).reverse
    have hx : xs ∈ S := by
      refine ⟨by simp [xs],?_,?_,?_⟩
      · exact List.pairwise_reverse.mpr (List.pairwise_ofFn.mpr hs)
      · intro x hx
        obtain ⟨i,rfl⟩ := (List.mem_ofFn' s x).mp (List.mem_reverse.mp hx)
        exact hmin i
      · rw [show prefixCost r xs = required s from prefixCost_reverse_ofFn r s]
        exact hcost
    refine ⟨xs,hx,?_⟩
    ext a
    change (a = 2 ∨ a ∈ xs) ↔ (a = 2 ∨ a ∈ Set.range s)
    simp [xs,List.mem_ofFn']

/-- The executable reference count, using the verified DP recurrence. -/
def certifiedCount (n : ℕ) : ℕ :=
  max 1 (n-1) + ∑ r ∈ Icc 2 n, dpAtLength n r

/-- The reference count computes the geometric definition of `F(n)` for every positive input. -/
theorem certifiedCount_eq_F (n : ℕ) (hn : 1 ≤ n) :
    certifiedCount n = F n := by
  rw [certifiedCount,F_eq_countByLength n hn]
  congr 1
  apply sum_congr rfl
  intro r h
  have hr := (mem_Icc.mp h).1
  rw [dpAtLength_eq_count n r (by omega),countByLength_eq_lists n r hr]


/-- The Python length cutoff evaluates the point cost of the smallest sizes. -/
def minimalCost (r : ℕ) : ℕ :=
  required (fun i : Fin r => i.val + 3)

private theorem minimalCost_le {r : ℕ} {s : Fin r → ℕ} (hs : StrictMono s)
    (hmin : ∀ i, 3 ≤ s i) : minimalCost r ≤ required s := by
  unfold minimalCost required
  apply sum_le_sum
  intro i _
  exact Nat.sub_le_sub_right (Nat.add_le_add_right (index_le_size hs hmin i) _) _

theorem minimalCost_mono : Monotone minimalCost := by
  apply monotone_nat_of_le_succ
  intro r
  unfold minimalCost required
  rw [Fin.sum_univ_succ]
  apply le_trans _ (Nat.le_add_left _ _)
  apply sum_le_sum
  intro i _
  simp only [Fin.val_succ]
  omega

/-- Once the smallest sizes exceed the budget, every later length contributes zero. -/
theorem dpAtLength_zero_after_cutoff {n r k : ℕ} (hr : 2 ≤ r) (hk : r ≤ k)
    (hbudget : n < minimalCost r) : dpAtLength n k = 0 := by
  have hk2 : 2 ≤ k := hr.trans hk
  rw [dpAtLength_eq_count n k (by omega), ← countByLength_eq_lists n k hk2]
  unfold countByLength
  have he : {A | ∃ s : Fin k → ℕ, 2 ≤ k ∧ StrictMono s ∧ (∀ i, 3 ≤ s i) ∧
      required s ≤ n ∧ A = insert 2 (Set.range s)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro A ⟨s,_,hs,hmin,hcost,_⟩
    exact (not_le_of_gt hbudget) ((minimalCost_mono hk).trans
      ((minimalCost_le hs hmin).trans hcost))
  rw [he,Set.ncard_empty]

end Erdos607
