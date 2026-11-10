import A401948Lean.PartitionDP
import Mathlib.Data.Set.Finite.Range

/-! The partition recurrence counts lists of parts padded with zeros. -/

namespace Erdos607

/-- Partitions of `e` into at most `m` positive parts, in ascending order and padded with zeros. -/
def paddedPartitions (m e : ℕ) : Set (List ℕ) :=
  {xs | xs.length = m ∧ xs.Pairwise (· ≤ ·) ∧ xs.sum = e}

theorem paddedPartitions_finite (m e : ℕ) : (paddedPartitions m e).Finite := by
  let f (v : Fin m → Fin (e+1)) := List.ofFn fun i => (v i).val
  apply (Set.finite_range f).subset
  intro xs hx
  obtain ⟨hlen,_,hsum⟩ := hx
  let g (i : Fin xs.length) : Fin (e+1) :=
    ⟨xs.get i, by
      have h := List.le_sum_of_mem (List.get_mem xs i)
      omega⟩
  refine ⟨fun i => g (Fin.cast hlen.symm i),?_⟩
  change List.ofFn (fun i => xs.get (Fin.cast hlen.symm i)) = xs
  subst m
  simp

theorem sum_map_succ (xs : List ℕ) : (xs.map (·+1)).sum = xs.sum + xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,ih]; omega

theorem pred_map_of_positive (xs : List ℕ) (h : ∀ a ∈ xs, 0 < a) :
    (xs.map (·-1)).map (·+1) = xs := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id xs]
  apply List.map_congr_left
  intro a ha
  have := h a ha
  simp only [Function.comp_apply,id_eq]
  omega

private def zeroParts (m e : ℕ) := {xs ∈ paddedPartitions (m+1) e | xs.headD 0 = 0}

private def positiveParts (m e : ℕ) := {xs ∈ paddedPartitions (m+1) e | xs.headD 0 ≠ 0}

private theorem ncard_zeroParts (m e : ℕ) : (zeroParts m e).ncard = (paddedPartitions m e).ncard := by
  symm
  apply Set.ncard_congr (fun xs _ => 0::xs)
  · intro xs ⟨hl,hp,hs⟩
    exact ⟨⟨by simp [hl], List.pairwise_cons.mpr ⟨fun _ _ => Nat.zero_le _,hp⟩,by simpa using hs⟩,rfl⟩
  · intro a b _ _ h
    exact (List.cons.inj h).2
  · intro xs hx
    obtain ⟨⟨hl,hp,hs⟩,hh⟩ := hx
    cases xs with
    | nil => simp at hl
    | cons a xs =>
      change a = 0 at hh
      subst a
      exact ⟨xs,⟨by simpa using hl,(List.pairwise_cons.mp hp).2,by simpa using hs⟩,rfl⟩

private theorem all_positive_of_mem_positiveParts {m e : ℕ} {xs : List ℕ}
    (hx : xs ∈ positiveParts m e) : ∀ x ∈ xs, 0 < x := by
  obtain ⟨⟨_,hp,_⟩,hh⟩ := hx
  cases xs with
  | nil => simp
  | cons a xs =>
    change a ≠ 0 at hh
    have ha := Nat.pos_of_ne_zero hh
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact ha.trans_le ((List.pairwise_cons.mp hp).1 x hx)

private theorem ncard_positiveParts (m e : ℕ) :
    (positiveParts m e).ncard = if m+1 ≤ e then (paddedPartitions (m+1) (e-(m+1))).ncard else 0 := by
  by_cases h : m+1 ≤ e
  · rw [if_pos h]
    symm
    apply Set.ncard_congr (fun xs _ => xs.map (·+1))
    · intro xs ⟨hl,hp,hs⟩
      refine ⟨⟨by simp [hl],List.pairwise_map.mpr (hp.imp fun h => by omega),?_⟩,?_⟩
      · rw [sum_map_succ,hs,hl]; omega
      · cases xs with
        | nil => simp at hl
        | cons a xs => exact Nat.succ_ne_zero a
    · intro a b _ _ hab
      exact (List.map_injective_iff.mpr (fun _ _ h => by omega)) hab
    · intro xs hx
      have hm := pred_map_of_positive xs (all_positive_of_mem_positiveParts hx)
      obtain ⟨⟨hl,hp,hs⟩,_⟩ := hx
      refine ⟨xs.map (·-1),⟨by simp [hl],List.pairwise_map.mpr (hp.imp fun h => by omega),?_⟩,hm⟩
      have hsum := congrArg List.sum hm
      rw [sum_map_succ,List.length_map,hl,hs] at hsum
      omega
  · rw [if_neg h]
    have he : positiveParts m e = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro xs hx
      have hm := pred_map_of_positive xs (all_positive_of_mem_positiveParts hx)
      obtain ⟨⟨hl,_,hs⟩,_⟩ := hx
      have hsum := congrArg List.sum hm
      rw [sum_map_succ,List.length_map,hl,hs] at hsum
      omega
    rw [he,Set.ncard_empty]

private theorem ncard_paddedPartitions_succ (m e : ℕ) :
    (paddedPartitions (m+1) e).ncard = (paddedPartitions m e).ncard +
      if m+1 ≤ e then (paddedPartitions (m+1) (e-(m+1))).ncard else 0 := by
  have hu : zeroParts m e ∪ positiveParts m e = paddedPartitions (m+1) e := by
    ext xs
    change (_ ∧ xs.headD 0 = 0) ∨ (_ ∧ xs.headD 0 ≠ 0) ↔ _
    tauto
  have hd : Disjoint (zeroParts m e) (positiveParts m e) :=
    Set.disjoint_left.mpr fun _ hz hp => hp.2 hz.2
  have hf := paddedPartitions_finite (m+1) e
  rw [← hu,Set.ncard_union_eq hd (hf.subset fun _ h => h.1)
    (hf.subset fun _ h => h.1), ncard_zeroParts, ncard_positiveParts]

theorem partitionCount_eq_ncard (m e : ℕ) : partitionCount m e = (paddedPartitions m e).ncard := by
  cases m with
  | zero =>
    rw [partitionCount]
    by_cases he : e = 0
    · subst e
      have h : paddedPartitions 0 0 = {[]} := by
        ext xs
        simp [paddedPartitions]
        aesop
      simp [h]
    · have h : paddedPartitions 0 e = ∅ := by
        ext xs
        simp [paddedPartitions]
        aesop
      simp [he,h]
  | succ m =>
    rw [partitionCount,ncard_paddedPartitions_succ,partitionCount_eq_ncard m e]
    by_cases he : m+1 ≤ e
    · simp only [if_pos he]
      rw [partitionCount_eq_ncard (m+1) (e-(m+1))]
    · simp [he]
termination_by m+e
decreasing_by all_goals omega

end Erdos607
