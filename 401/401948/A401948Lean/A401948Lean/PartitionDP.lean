import A401948Lean.CountingDP
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring

/-! The one-array recurrence used to count partitions of an excess point budget. -/

namespace Erdos607

open Finset

/-- Number of partitions of an excess into parts of size at most `m`. -/
def partitionCount : ℕ → ℕ → ℕ
  | 0, e => if e = 0 then 1 else 0
  | m+1, e => partitionCount m e +
      if m+1 ≤ e then partitionCount (m+1) (e-(m+1)) else 0
termination_by m e => m+e

private def entry (row : Array ℕ) (e : ℕ) : ℕ := row[e]?.getD 0

private def addPart (m : ℕ) : ℕ → Array ℕ → Array ℕ
  | 0, row => row
  | k+1, row =>
    let current := addPart m k row
    let e := m+k
    current.setIfInBounds e (entry current e + entry current (e-m))

private theorem addPart_size (m k : ℕ) (row : Array ℕ) :
    (addPart m k row).size = row.size := by
  induction k with
  | zero => rfl
  | succ k ih => simp [addPart,ih]

private theorem entry_set_self (a : Array ℕ) (i v : ℕ) (h : i < a.size) :
    entry (a.setIfInBounds i v) i = v := by
  simp [entry,Array.getElem?_setIfInBounds_self_of_lt h]

private theorem entry_set_ne (a : Array ℕ) (i j v : ℕ) (h : i ≠ j) :
    entry (a.setIfInBounds i v) j = entry a j := by
  simp [entry,Array.getElem?_setIfInBounds_ne h]

private theorem addPart_correct (m k bound : ℕ) (row : Array ℕ) (hm : 0 < m)
    (hbound : bound < row.size) (hk : k ≤ bound+1-m)
    (hprev : ∀ e ≤ bound, entry row e = partitionCount (m-1) e)
    (e : ℕ) (he : e ≤ bound) :
    entry (addPart m k row) e =
      if e < m+k then partitionCount m e else partitionCount (m-1) e := by
  have hstep (j : ℕ) :
      partitionCount m j = partitionCount (m-1) j +
        if m ≤ j then partitionCount m (j-m) else 0 := by
    cases m with
    | zero => omega
    | succ m => rw [partitionCount]; simp
  induction k generalizing e with
  | zero =>
    rw [addPart,hprev e he]
    by_cases h : e < m
    · simp [h,hstep e,not_le_of_gt h]
    · simp [h]
  | succ k ih =>
    have hk' : k ≤ bound+1-m := by omega
    by_cases he' : e = m+k
    · subst e
      rw [addPart,entry_set_self _ _ _ (by rw [addPart_size]; omega)]
      rw [ih hk' _ he,ih hk' _ (by omega : m+k-m ≤ bound)]
      simp only [if_neg (Nat.lt_irrefl _), if_pos (show m+k-m < m+k by omega),
        if_pos (show m+k < m+(k+1) by omega)]
      rw [hstep (m+k),if_pos (by omega)]
    · rw [addPart,entry_set_ne _ _ _ _ (Ne.symm he'),ih hk' e he]
      by_cases h : e < m+k
      · simp [h, show e < m+(k+1) by omega]
      · simp [h, show ¬ e < m+(k+1) by omega]

/-- Row `m` of the same truncated, ascending in-place update as the Python DP. -/
def partitionTable (limit : ℕ) : ℕ → Array ℕ
  | 0 => (Array.replicate (limit+1) 0).setIfInBounds 0 1
  | m+1 => addPart (m+1) (limit-(m+1)*(m+1)+1-(m+1)) (partitionTable limit m)

private theorem partitionTable_size (limit m : ℕ) :
    (partitionTable limit m).size = limit+1 := by
  induction m with
  | zero => simp [partitionTable]
  | succ m ih => simp [partitionTable,addPart_size,ih]

/-- Every retained array entry is the corresponding exact partition count. -/
theorem partitionTable_correct {limit m e : ℕ} (hm : m*m ≤ limit)
    (he : e ≤ limit-m*m) :
    (partitionTable limit m)[e]?.getD 0 = partitionCount m e := by
  induction m generalizing e with
  | zero =>
    change entry (partitionTable limit 0) e = _
    by_cases h : e = 0
    · subst e
      simp [partitionTable,entry_set_self,partitionCount]
    · rw [partitionTable,entry_set_ne _ _ _ _ (Ne.symm h),partitionCount]
      simp [entry,h,show e ≤ limit by omega]
  | succ m ih =>
    change entry (partitionTable limit (m+1)) e = _
    rw [partitionTable]
    have hsq : m*m ≤ (m+1)*(m+1) := Nat.mul_le_mul (by omega) (by omega)
    have hbound : limit-(m+1)*(m+1) < (partitionTable limit m).size := by
      rw [partitionTable_size]
      omega
    have hprev (j : ℕ) (hj : j ≤ limit-(m+1)*(m+1)) :
        entry (partitionTable limit m) j = partitionCount (m+1-1) j := by
      have h' : j ≤ limit-m*m := hj.trans (Nat.sub_le_sub_left hsq limit)
      simpa [entry] using ih (hsq.trans hm) h'
    rw [addPart_correct (m+1) _ _ _ (by omega) hbound le_rfl hprev e he]
    exact if_pos (by omega)

end Erdos607
