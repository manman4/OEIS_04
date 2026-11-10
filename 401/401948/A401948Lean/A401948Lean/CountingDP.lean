import A401948Lean.Definitions
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Card

/-! The recurrence for the counts of increasing prefixes, stored in reverse order. -/

namespace Erdos607

open Finset
open scoped BigOperators

/-- The contribution to the required point count at one-based position `i`. -/
def contribution (r i size : ℕ) : ℕ := size + i - r

/-- The point count contributed by a prefix, with the last size first. -/
def prefixCost (r : ℕ) : List ℕ → ℕ
  | [] => 0
  | size :: tail => prefixCost r tail + contribution r (tail.length + 1) size

/-- DP cell indexed by prefix length, last size, and accumulated point count. -/
def dp (r : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, size, cost => if size = 2 ∧ cost = 0 then 1 else 0
  | i+1, size, cost =>
      if 3 ≤ size ∧ contribution r (i+1) size ≤ cost then
        ∑ smaller ∈ Ico 2 size, dp r i smaller (cost - contribution r (i+1) size)
      else 0

private def prefixes (r : ℕ) : ℕ → ℕ → ℕ → Finset (List ℕ)
  | 0, size, cost => if size = 2 ∧ cost = 0 then {[]} else ∅
  | i+1, size, cost =>
      if 3 ≤ size ∧ contribution r (i+1) size ≤ cost then
        (Ico 2 size).biUnion fun smaller =>
          (prefixes r i smaller (cost - contribution r (i+1) size)).image (List.cons size)
      else ∅

private theorem mem_prefixes {r i size cost : ℕ} {xs : List ℕ} :
    xs ∈ prefixes r i size cost ↔
      xs.length = i ∧ xs.headD 2 = size ∧ xs.Pairwise (· > ·) ∧
        (∀ x ∈ xs, 3 ≤ x) ∧ prefixCost r xs = cost := by
  induction i generalizing size cost xs with
  | zero =>
    cases xs <;> by_cases h : size = 2 ∧ cost = 0 <;>
      simp [prefixes, prefixCost, h]
    all_goals aesop
  | succ i ih =>
    cases xs with
    | nil => simp [prefixes]; split <;> simp
    | cons head tail =>
      simp only [List.length_cons, Nat.succ.injEq, List.headD_cons, List.pairwise_cons,
        List.forall_mem_cons, prefixCost]
      rw [prefixes]
      split
      · rename_i guard
        constructor
        · intro h
          obtain ⟨t,ht,him⟩ := mem_biUnion.mp h
          obtain ⟨ys,hy,he⟩ := mem_image.mp him
          obtain ⟨hhead,htail⟩ := List.cons.inj he
          subst head
          subst ys
          obtain ⟨hlen,hlast,hpair,hge,hcost⟩ := ih.mp hy
          refine ⟨hlen,rfl,⟨?_,hpair⟩,⟨guard.1,hge⟩,?_⟩
          · intro x hx
            have hlt := (mem_Ico.mp ht).2
            cases tail with
            | nil => simp at hx
            | cons first rest =>
              simp only [List.headD_cons] at hlast
              rw [← hlast] at hlt
              rcases List.mem_cons.mp hx with rfl | hx
              · exact hlt
              · exact ((List.pairwise_cons.mp hpair).1 x hx).trans hlt
          · rw [hlen,hcost]
            omega
        · rintro ⟨hlen,rfl,⟨hlt,hpair⟩,⟨hsize,hge⟩,hcost⟩
          have ht : tail.headD 2 ∈ Ico 2 head := by
            apply mem_Ico.mpr
            cases tail with
            | nil => simp; omega
            | cons first rest =>
              exact ⟨le_trans (by decide : 2 ≤ 3) (hge first (by simp)), hlt first (by simp)⟩
          refine mem_biUnion.mpr ⟨tail.headD 2,ht,mem_image.mpr ⟨tail,ih.mpr ?_,rfl⟩⟩
          refine ⟨hlen,rfl,hpair,hge,?_⟩
          rw [hlen] at hcost
          omega
      · rename_i guard
        simp only [notMem_empty, false_iff]
        rintro ⟨hlen,rfl,_,⟨hsize,_⟩,hcost⟩
        apply guard
        rw [hlen] at hcost
        omega

private theorem dp_eq_card (r i size cost : ℕ) :
    dp r i size cost = (prefixes r i size cost).card := by
  induction i generalizing size cost with
  | zero => by_cases h : size = 2 ∧ cost = 0 <;> simp [dp,prefixes,h]
  | succ i ih =>
    by_cases h : 3 ≤ size ∧ contribution r (i+1) size ≤ cost
    · simp only [dp,prefixes,if_pos h]
      rw [card_biUnion]
      · simp only [ih, card_image_of_injective _ List.cons_injective]
      · intro x _ y _ hne
        apply disjoint_left.mpr
        intro zs hx hy
        obtain ⟨xs,hxs,he⟩ := mem_image.mp hx
        obtain ⟨ys,hys,he'⟩ := mem_image.mp hy
        have he'' := (List.cons.inj (he.trans he'.symm)).2
        exact hne ((mem_prefixes.mp hxs).2.1.symm.trans
          (he'' ▸ (mem_prefixes.mp hys).2.1))
    · simp [dp,prefixes,h]

/-- Each DP cell counts exactly the decreasing lists with the specified length,
head, and point cost. These lists record increasing size prefixes in reverse. -/
theorem dp_eq_count (r i size cost : ℕ) :
    dp r i size cost = ({xs : List ℕ | xs.length = i ∧ xs.headD 2 = size ∧
      xs.Pairwise (· > ·) ∧ (∀ x ∈ xs, 3 ≤ x) ∧ prefixCost r xs = cost} : Set (List ℕ)).ncard := by
  rw [dp_eq_card]
  have he : ((prefixes r i size cost : Finset (List ℕ)) : Set (List ℕ)) =
      {xs : List ℕ | xs.length = i ∧ xs.headD 2 = size ∧ xs.Pairwise (· > ·) ∧
        (∀ x ∈ xs, 3 ≤ x) ∧ prefixCost r xs = cost} := by
    ext xs
    exact mem_prefixes
  rw [← he, Set.ncard_coe_finset]

/-- The candidates of a given length and point budget, with largest size first. -/
def completedLists (n r : ℕ) : Set (List ℕ) :=
  {xs | xs.length = r ∧ xs.Pairwise (· > ·) ∧ (∀ x ∈ xs, 3 ≤ x) ∧ prefixCost r xs ≤ n}

/-- The sum of the terminal DP cells for a fixed length. -/
def dpAtLength (n r : ℕ) : ℕ :=
  ∑ size ∈ range (n+1), ∑ cost ∈ range (n+1), dp r r size cost

/-- Summing the terminal cells counts every candidate once. -/
theorem dpAtLength_eq_count (n r : ℕ) (hr : 1 ≤ r) :
    dpAtLength n r = (completedLists n r).ncard := by
  let bounds := range (n+1)
  let cell (sc : ℕ × ℕ) := prefixes r r sc.1 sc.2
  let all := (bounds ×ˢ bounds).biUnion cell
  have hsets : (all : Set (List ℕ)) = completedLists n r := by
    ext xs
    change xs ∈ all ↔ xs.length = r ∧ xs.Pairwise (· > ·) ∧
      (∀ x ∈ xs, 3 ≤ x) ∧ prefixCost r xs ≤ n
    constructor
    · intro h
      obtain ⟨⟨s,c⟩,hsc,hxs⟩ := mem_biUnion.mp h
      obtain ⟨hlen,_,hpair,hge,hcost⟩ := mem_prefixes.mp hxs
      have hc := mem_range.mp (mem_product.mp hsc).2
      exact ⟨hlen,hpair,hge,by omega⟩
    · rintro ⟨hlen,hpair,hge,hcost⟩
      have hs : xs.headD 2 ≤ n := by
        cases xs with
        | nil => simp at hlen; omega
        | cons head tail =>
          simp only [List.length_cons] at hlen
          simp only [List.headD_cons]
          simp only [prefixCost, contribution] at hcost
          omega
      exact mem_biUnion.mpr ⟨(xs.headD 2,prefixCost r xs),
        mem_product.mpr ⟨mem_range.mpr (by omega),mem_range.mpr (by omega)⟩,
        mem_prefixes.mpr ⟨hlen,rfl,hpair,hge,rfl⟩⟩
  have hdisj : ((bounds ×ˢ bounds : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).PairwiseDisjoint cell := by
    intro a _ b _ hne
    apply disjoint_left.mpr
    intro xs ha hb
    obtain ⟨_,hsa,_,_,hca⟩ := mem_prefixes.mp ha
    obtain ⟨_,hsb,_,_,hcb⟩ := mem_prefixes.mp hb
    exact hne (Prod.ext (hsa.symm.trans hsb) (hca.symm.trans hcb))
  rw [← hsets, Set.ncard_coe_finset, card_biUnion hdisj]
  simpa [dpAtLength,cell,bounds,dp_eq_card] using
    (Finset.sum_product (s := bounds) (t := bounds) fun sc => (cell sc).card).symm

end Erdos607
