import A401948Lean.ProfileEncoding
import A401948Lean.Verification
import Mathlib.Algebra.BigOperators.Intervals

/-! Verification of the integer-partition algorithm for the geometric sequence. -/

namespace Erdos607

open Finset
open scoped BigOperators

private def tailChoices (m : ℕ) : Finset (Finset ℕ) := (Ico 3 m).powerset

private theorem card_tailChoices (m : ℕ) : (tailChoices m).card = 2^(m-3) := by
  simp [tailChoices]

private def active (n m : ℕ) (b : Bool) : Prop :=
  (b = true ∨ 3 ≤ m) ∧ profileOffset m b ≤ n

private instance (n m : ℕ) (b : Bool) : Decidable (active n m b) :=
  inferInstanceAs (Decidable ((_ ∨ _) ∧ _ ≤ _))

private noncomputable def dataFor (n m : ℕ) (b : Bool) :
    Finset (Σ _ : ℕ, List ℕ × Finset ℕ) := by
  classical
  exact if active n m b then
    (range (n-profileOffset m b+1)).sigma fun e =>
      (paddedPartitions_finite m e).toFinset ×ˢ tailChoices m
    else ∅

private noncomputable def codes (n : ℕ) :
    Finset (Σ _ : ℕ, Σ _ : Bool, Σ _ : ℕ, List ℕ × Finset ℕ) := by
  classical
  exact (Icc 2 n.sqrt).sigma fun m => (univ : Finset Bool).sigma fun b => dataFor n m b

private theorem mem_codes {n m e : ℕ} {b : Bool} {p : List ℕ} {s : Finset ℕ} :
    ⟨m,b,e,p,s⟩ ∈ codes n ↔
      2 ≤ m ∧ (b = true ∨ 3 ≤ m) ∧ profileOffset m b+e ≤ n ∧
        p ∈ paddedPartitions m e ∧ s ⊆ Ico 3 m := by
  classical
  simp only [codes,mem_sigma,mem_Icc,mem_univ,true_and]
  unfold dataFor
  by_cases h : active n m b
  · rw [if_pos h]
    simp only [mem_sigma,mem_range,mem_product,Set.Finite.mem_toFinset,tailChoices,mem_powerset]
    have hb := h.1
    have hbase : m*m ≤ profileOffset m b := Nat.le_add_right _ _
    have hs := Nat.le_sqrt.mpr (hbase.trans h.2)
    have he : e < n-profileOffset m b+1 ↔ profileOffset m b+e ≤ n := by
      have := h.2
      omega
    simp [he,hb,hs]
  · rw [if_neg h]
    simp only [notMem_empty,and_false,false_iff]
    rintro ⟨_,hb,hc,_,_⟩
    exact h ⟨hb,by omega⟩

private def decodeCode (c : Σ _ : ℕ, Σ _ : Bool, Σ _ : ℕ, List ℕ × Finset ℕ) : List ℕ :=
  decodeProfile c.1 c.2.1 c.2.2.2.1 c.2.2.2.2

private noncomputable def listsFor (n : ℕ) : Finset (List ℕ) := (codes n).image decodeCode

private theorem card_listsFor (n : ℕ) : (listsFor n).card = (codes n).card := by
  unfold listsFor
  apply card_image_of_injOn
  intro a ha b hb he
  obtain ⟨m,i,e,p,s⟩ := a
  obtain ⟨m',i',e',p',s'⟩ := b
  obtain ⟨hm,hi,_,hp,hs⟩ := mem_codes.mp ha
  obtain ⟨hm',hi',_,hp',hs'⟩ := mem_codes.mp hb
  obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := decodeProfile_inj hm hm' hi hi' hp hp' hs hs' he
  rfl

private theorem mem_listsFor {n : ℕ} {xs : List ℕ} :
    xs ∈ listsFor n ↔ 2 ≤ xs.length ∧ xs.Pairwise (· > ·) ∧
      (∀ x ∈ xs, 3 ≤ x) ∧ descendingCost 0 xs ≤ n := by
  constructor
  · intro h
    obtain ⟨⟨m,b,e,p,s⟩,hc,rfl⟩ := mem_image.mp h
    obtain ⟨hm,hb,hle,hp,hs⟩ := mem_codes.mp hc
    obtain ⟨hl,hp',hmin,_,hc'⟩ := decodeProfile_spec hm hb hp hs
    exact ⟨hl,hp',hmin,hc' ▸ hle⟩
  · rintro ⟨hl,hp,hmin,hle⟩
    obtain ⟨m,b,e,p,s,hm,hb,hp',hs,rfl⟩ := decodeProfile_surj hl hp hmin
    have hc := (decodeProfile_spec hm hb hp' hs).2.2.2.2
    exact mem_image.mpr ⟨⟨m,b,e,p,s⟩,mem_codes.mpr ⟨hm,hb,hc ▸ hle,hp',hs⟩,rfl⟩

private theorem length_le_of_mem_listsFor {n : ℕ} {xs : List ℕ} (hx : xs ∈ listsFor n) :
    xs.length ≤ n := by
  obtain ⟨hl,hp,hmin,hcost⟩ := mem_listsFor.mp hx
  cases xs with
  | nil => simp
  | cons a xs =>
    have h₁ : 0 < (a::xs).length := by simp
    have h₂ : xs.length < (a::xs).length := by simp
    have h₃ := staircase_bound hp h₁ h₂ (Nat.zero_le _)
    have h₄ := hmin _ (List.getElem_mem h₂)
    simp only [List.getElem_cons_zero,Nat.sub_zero] at h₃
    simp only [descendingCost,Nat.sub_zero] at hcost
    simp only [List.length_cons]
    omega

private theorem card_listsFor_eq_reference (n : ℕ) :
    (listsFor n).card = ∑ r ∈ Icc 2 n, dpAtLength n r := by
  rw [card_eq_sum_card_fiberwise (f := List.length) (s := listsFor n) (t := Icc 2 n)
    (fun xs hx => mem_Icc.mpr ⟨(mem_listsFor.mp hx).1,length_le_of_mem_listsFor hx⟩)]
  apply sum_congr rfl
  intro r hr
  rw [dpAtLength_eq_count n r (by have := (mem_Icc.mp hr).1; omega)]
  have he : ((listsFor n).filter (fun xs => xs.length = r) : Set (List ℕ)) =
      completedLists n r := by
    ext xs
    change xs ∈ (listsFor n).filter (fun xs => xs.length = r) ↔ _
    rw [mem_filter,mem_listsFor,descendingCost_eq_prefixCost,Nat.zero_add]
    constructor
    · rintro ⟨⟨_,hp,hmin,hc⟩,hl⟩
      exact ⟨hl,hp,hmin,hl ▸ hc⟩
    · rintro ⟨rfl,hp,hmin,hc⟩
      exact ⟨⟨(mem_Icc.mp hr).1,hp,hmin,hc⟩,rfl⟩
  rw [← he,Set.ncard_coe_finset]

private theorem card_dataFor (n m : ℕ) (b : Bool) :
    (dataFor n m b).card = if active n m b then
      ∑ e ∈ range (n-profileOffset m b+1), 2^(m-3)*partitionCount m e else 0 := by
  classical
  by_cases h : active n m b
  · simp only [dataFor,if_pos h,card_sigma,card_product,card_tailChoices]
    apply sum_congr rfl
    intro e _
    rw [← Set.ncard_eq_toFinset_card _ (paddedPartitions_finite m e), ← partitionCount_eq_ncard,Nat.mul_comm]
  · simp [dataFor,h]

/-- The verified partition-table calculation for one output index.
The row bounds are determined by `limit`, as in the batch Python implementation. -/
def fastPartitionCount (limit n : ℕ) : ℕ :=
  max 1 (n-1) + ∑ m ∈ Icc 2 n.sqrt, ∑ b : Bool,
    if active n m b then
      ∑ e ∈ range (n-profileOffset m b+1), 2^(m-3)*(partitionTable limit m)[e]?.getD 0
    else 0

theorem fastPartitionCount_eq_certifiedCount {limit n : ℕ} (hn : n ≤ limit) :
    fastPartitionCount limit n = certifiedCount n := by
  rw [fastPartitionCount,certifiedCount,← card_listsFor_eq_reference,card_listsFor]
  congr 1
  simp only [codes,card_sigma]
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro b _
  rw [card_dataFor]
  by_cases h : active n m b
  · simp only [if_pos h]
    apply sum_congr rfl
    intro e he
    have hsq : m*m ≤ n := Nat.le_sqrt.mp (mem_Icc.mp hm).2
    have he' := mem_range.mp he
    have hbase : m*m ≤ profileOffset m b := Nat.le_add_right _ _
    have hcost := h.2
    rw [partitionTable_correct (hsq.trans hn) (by omega)]
  · simp [h]

/-- The fast partition DP computes the geometric number of profiles. -/
theorem fastPartitionCount_eq_F {limit n : ℕ} (hn : 1 ≤ n) (hlimit : n ≤ limit) :
    fastPartitionCount limit n = F n :=
  (fastPartitionCount_eq_certifiedCount hlimit).trans (certifiedCount_eq_F n hn)

private def histogramCell (limit m : ℕ) (b : Bool) (c : ℕ) : ℕ :=
  if active c m b then
    2^(m-3)*(partitionTable limit m)[c-profileOffset m b]?.getD 0
  else 0

/-- The contributions whose first feasible point count is exactly `c`. -/
def partitionHistogram (limit c : ℕ) : ℕ :=
  ∑ m ∈ Icc 2 limit.sqrt, ∑ b : Bool, histogramCell limit m b c

/-- The output is the cumulative histogram plus the profiles with at most one large size. -/
def partitionHistogramCount (limit n : ℕ) : ℕ :=
  max 1 (n-1) + ∑ c ∈ Icc 1 n, partitionHistogram limit c

private theorem sum_histogramCell (limit n m : ℕ) (b : Bool) (hm : 2 ≤ m) :
    ∑ c ∈ Icc 1 n, histogramCell limit m b c =
      if active n m b then
        ∑ e ∈ range (n-profileOffset m b+1), 2^(m-3)*(partitionTable limit m)[e]?.getD 0
      else 0 := by
  have hbase : m*m ≤ profileOffset m b := Nat.le_add_right _ _
  have hm' : 1 ≤ profileOffset m b := (by decide : 1 ≤ 2*2).trans ((Nat.mul_le_mul hm hm).trans hbase)
  by_cases h : active n m b
  · rw [if_pos h]
    have he : Ico (profileOffset m b) (n+1) ⊆ Icc 1 n := by
      intro c hc
      have ⟨hl,hr⟩ := mem_Ico.mp hc
      exact mem_Icc.mpr ⟨hm'.trans hl,by omega⟩
    rw [← sum_subset he (fun c hc hnc => by
      have hc' := (mem_Icc.mp hc).2
      have hnot : ¬active c m b := fun ha => hnc (mem_Ico.mpr ⟨ha.2,by omega⟩)
      simp [histogramCell,hnot])]
    rw [sum_Ico_eq_sum_range]
    have hsize : n+1-profileOffset m b = n-profileOffset m b+1 := by
      have := h.2
      omega
    rw [hsize]
    apply sum_congr rfl
    intro e _
    have hactive : active (profileOffset m b+e) m b := ⟨h.1,Nat.le_add_right _ _⟩
    simp [histogramCell,hactive]
  · rw [if_neg h]
    apply sum_eq_zero
    intro c hc
    have hnot : ¬active c m b := fun ha => h ⟨ha.1,ha.2.trans (mem_Icc.mp hc).2⟩
    simp [histogramCell,hnot]

theorem partitionHistogramCount_eq_fastPartitionCount {limit n : ℕ} (hn : n ≤ limit) :
    partitionHistogramCount limit n = fastPartitionCount limit n := by
  unfold partitionHistogramCount partitionHistogram fastPartitionCount
  congr 1
  rw [sum_comm]
  have hs : Icc 2 n.sqrt ⊆ Icc 2 limit.sqrt := by
    intro m hm
    exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans (Nat.sqrt_le_sqrt hn)⟩
  rw [← sum_subset hs (fun m hm hnm => by
    apply sum_eq_zero
    intro c hc
    apply sum_eq_zero
    intro b _
    have hbase : m*m ≤ profileOffset m b := Nat.le_add_right _ _
    have ha : ¬active c m b := fun ha => hnm (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,
      Nat.le_sqrt.mpr (hbase.trans (ha.2.trans (mem_Icc.mp hc).2))⟩)
    simp [histogramCell,ha])]
  apply sum_congr rfl
  intro m hm
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  exact sum_histogramCell limit n m b (mem_Icc.mp hm).1

/-- The partition DP and histogram accumulation compute the geometric count for each batch index. -/
theorem partitionHistogramCount_eq_F {limit n : ℕ} (hn : 1 ≤ n) (hlimit : n ≤ limit) :
    partitionHistogramCount limit n = F n :=
  (partitionHistogramCount_eq_fastPartitionCount hlimit).trans (fastPartitionCount_eq_F hn hlimit)

end Erdos607
