import A401948Lean.CountingDP
import Mathlib.Tactic.Ring

/-! Decomposition into sizes with positive point cost and a zero-cost tail. -/

namespace Erdos607

/-- Point cost in descending order, starting at zero-based position `j`. -/
def descendingCost (j : ℕ) : List ℕ → ℕ
  | [] => 0
  | x::xs => (x-j) + descendingCost (j+1) xs

theorem descendingCost_eq_prefixCost (j : ℕ) (xs : List ℕ) :
    descendingCost j xs = prefixCost (j+xs.length) xs := by
  induction xs generalizing j with
  | nil => rfl
  | cons x xs ih =>
    simp only [descendingCost,prefixCost,contribution,List.length_cons]
    rw [ih (j+1)]
    rw [show j+1+xs.length = j+(xs.length+1) by omega]
    omega

theorem descendingCost_append (j : ℕ) (xs ys : List ℕ) :
    descendingCost j (xs ++ ys) = descendingCost j xs + descendingCost (j+xs.length) ys := by
  induction xs generalizing j with
  | nil => simp [descendingCost]
  | cons x xs ih =>
    simp only [List.cons_append,descendingCost,ih,List.length_cons]
    rw [show j+1+xs.length = j+(xs.length+1) by omega]
    omega

theorem descendingCost_zero (j : ℕ) (xs : List ℕ) (h : ∀ x ∈ xs, x ≤ j) :
    descendingCost j xs = 0 := by
  induction xs generalizing j with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    rw [descendingCost,ih (j+1) (fun a ha => (h a (by simp [ha])).trans (Nat.le_succ j))]
    omega

/-- Length of the initial run of positive contributions. -/
def positiveLength (j : ℕ) : List ℕ → ℕ
  | [] => 0
  | x::xs => if j < x then 1 + positiveLength (j+1) xs else 0

theorem positiveLength_spec {j : ℕ} {xs : List ℕ} (hp : xs.Pairwise (· > ·)) :
    let m := positiveLength j xs
    m ≤ xs.length ∧ (∀ x ∈ xs.take m, j+m ≤ x) ∧ (∀ x ∈ xs.drop m, x ≤ j+m) := by
  induction xs generalizing j with
  | nil => simp [positiveLength]
  | cons a xs ih =>
    obtain ⟨hgt,hpx⟩ := List.pairwise_cons.mp hp
    by_cases ha : j < a
    · simp only [positiveLength,if_pos ha]
      obtain ⟨hle,hfront,htail⟩ := ih (j := j+1) hpx
      set m := positiveLength (j+1) xs with hm
      rw [Nat.add_comm 1 m]
      simp only [List.length_cons,List.take_succ_cons,List.drop_succ_cons,List.forall_mem_cons]
      refine ⟨by omega,⟨?_,fun x hx => by have := hfront x hx; omega⟩,fun x hx => by
        have := htail x hx
        omega⟩
      by_cases hz : m = 0
      · omega
      · cases xs with
        | nil => simp at hle; omega
        | cons x xs =>
          have hx : x ∈ (x::xs).take m := by
            obtain ⟨k,hk⟩ : ∃ k, m = k+1 := ⟨m-1,by omega⟩
            rw [hk]
            simp
          have h₁ := hfront x hx
          have h₂ := hgt x (by simp)
          omega
    · simp only [positiveLength,if_neg ha,List.take_zero,List.drop_zero,List.not_mem_nil,
        false_implies,implies_true, true_and, Nat.add_zero, Nat.zero_le]
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · omega
      · have := hgt x hx
        omega

theorem positiveLength_append {j : ℕ} {front tail : List ℕ}
    (hf : ∀ x ∈ front, j+front.length ≤ x) (ht : ∀ x ∈ tail, x ≤ j+front.length) :
    positiveLength j (front ++ tail) = front.length := by
  induction front generalizing j with
  | nil =>
    cases tail with
    | nil => rfl
    | cons a xs => have := ht a (by simp); simp [positiveLength,show ¬ j < a by simpa using this]
  | cons a xs ih =>
    have ha := hf a (by simp)
    simp only [List.cons_append,positiveLength,if_pos (show j < a by simp only [List.length_cons] at ha; omega),List.length_cons]
    rw [ih (j := j+1) (fun x hx => by have := hf x (by simp [hx]); simp at this; omega)
      (fun x hx => by have := ht x hx; simp at this; omega)]
    omega

/-- Restore the strictly decreasing staircase to a descending partition. -/
def stairs (m : ℕ) : List ℕ → List ℕ
  | [] => []
  | x::xs => (m+xs.length+x)::stairs m xs

/-- Remove the strictly decreasing staircase from the positive-cost sizes. -/
def unstairs (m : ℕ) : List ℕ → List ℕ
  | [] => []
  | x::xs => (x-(m+xs.length))::unstairs m xs

@[simp] theorem length_stairs (m : ℕ) (xs : List ℕ) : (stairs m xs).length = xs.length := by
  induction xs <;> simp [stairs, *]

@[simp] theorem length_unstairs (m : ℕ) (xs : List ℕ) : (unstairs m xs).length = xs.length := by
  induction xs <;> simp [unstairs, *]

@[simp] theorem unstairs_stairs (m : ℕ) (xs : List ℕ) : unstairs m (stairs m xs) = xs := by
  induction xs <;> simp [stairs,unstairs, *]

theorem getElem_stairs (m : ℕ) (xs : List ℕ) (i : ℕ) (hi : i < (stairs m xs).length) :
    (stairs m xs)[i] = m+(xs.length-1-i)+xs[i]'(by simpa using hi) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp [stairs]
    | succ i =>
      simp only [stairs,List.getElem_cons_succ,List.length_cons] at *
      rw [ih i (by simpa using hi)]
      omega

theorem getElem_unstairs (m : ℕ) (xs : List ℕ) (i : ℕ) (hi : i < (unstairs m xs).length) :
    (unstairs m xs)[i] = xs[i]'(by simpa using hi)-(m+(xs.length-1-i)) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => simp [unstairs]
    | succ i =>
      simp only [unstairs,List.getElem_cons_succ,List.length_cons] at *
      rw [ih i (by simpa using hi)]
      omega

theorem stairs_lower (m : ℕ) (xs : List ℕ) : ∀ x ∈ stairs m xs, m ≤ x := by
  intro x hx
  obtain ⟨i,hi,rfl⟩ := List.mem_iff_getElem.mp hx
  rw [getElem_stairs]
  omega

theorem stairs_pairwise {m : ℕ} {xs : List ℕ} (hp : xs.Pairwise (· ≥ ·)) :
    (stairs m xs).Pairwise (· > ·) := by
  rw [List.pairwise_iff_getElem] at hp ⊢
  intro i j hi hj hij
  rw [getElem_stairs,getElem_stairs]
  simp only [length_stairs] at hi hj
  have := hp i j hi hj hij
  omega

theorem staircase_bound {xs : List ℕ} (hp : xs.Pairwise (· > ·)) {i j : ℕ}
    (hi : i < xs.length) (hj : j < xs.length) (hij : i ≤ j) :
    xs[j]+(j-i) ≤ xs[i] := by
  induction j generalizing i with
  | zero =>
    have h : i = 0 := by omega
    subst i
    simp
  | succ j ih =>
    by_cases he : i = j+1
    · subst i; simp
    · have hj' : j < xs.length := by omega
      have h₁ := ih hi hj' (by omega)
      have h₂ := List.pairwise_iff_getElem.mp hp j (j+1) hj' hj (by omega)
      omega

theorem stairs_unstairs {m : ℕ} {xs : List ℕ} (hp : xs.Pairwise (· > ·))
    (hm : ∀ x ∈ xs, m ≤ x) : stairs m (unstairs m xs) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hix
    rw [getElem_stairs,getElem_unstairs]
    simp only [length_unstairs]
    have hl : xs.length-1 < xs.length := by omega
    have := staircase_bound hp hix hl (by omega)
    have := hm xs[xs.length-1] (List.getElem_mem hl)
    omega

theorem unstairs_pairwise {m : ℕ} {xs : List ℕ} (hp : xs.Pairwise (· > ·)) :
    (unstairs m xs).Pairwise (· ≥ ·) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [getElem_unstairs,getElem_unstairs]
  simp only [length_unstairs] at hi hj
  have := staircase_bound hp hi hj (by omega)
  omega

theorem not_mem_stairs_floor {m : ℕ} {xs : List ℕ} (hp : xs.Pairwise (· ≥ ·)) :
    m ∉ stairs m xs ↔ 0 ∉ xs := by
  constructor
  · intro h hz
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hz
    have hl : xs.length-1 < xs.length := by omega
    have hlast : xs[xs.length-1] = 0 := by
      by_cases hi' : i = xs.length-1
      · simpa [hi'] using he
      · have := List.pairwise_iff_getElem.mp hp i (xs.length-1) hi hl (by omega)
        omega
    apply h
    have hls : xs.length-1 < (stairs m xs).length := by simpa using hl
    have hh := getElem_stairs m xs (xs.length-1) hls
    rw [Nat.sub_self,hlast] at hh
    simp only [Nat.add_zero] at hh
    have hmem := List.getElem_mem hls
    rwa [hh] at hmem
  · intro h hx
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
    rw [getElem_stairs] at he
    have hzero : xs[i]'(by simpa using hi) = 0 := by omega
    exact h (hzero ▸ List.getElem_mem (by simpa using hi))

theorem descendingCost_stairs (j : ℕ) (xs : List ℕ) :
    descendingCost j (stairs (j+xs.length) xs) = xs.length*xs.length+xs.sum := by
  induction xs generalizing j with
  | nil => simp [descendingCost,stairs]
  | cons x xs ih =>
    simp only [List.length_cons,List.sum_cons,stairs,descendingCost]
    rw [show j+(xs.length+1) = j+1+xs.length by omega,ih (j+1)]
    rw [show j+1+xs.length+xs.length+x-j = 2*xs.length+1+x by omega]
    ring

end Erdos607
