import A401948Lean.PartitionCount
import A401948Lean.ProfileSplit
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith

/-! Encode a profile by a padded partition, a shift flag, and a subset of zero-cost sizes. -/

namespace Erdos607

open Finset

def profileOffset (m : ℕ) (shift : Bool) : ℕ := m*m + if shift then m else 0

def profileFront (m : ℕ) (shift : Bool) (parts : List ℕ) : List ℕ :=
  stairs m (if shift then (parts.map (·+1)).reverse else parts.reverse)

def profileTail (m : ℕ) (shift : Bool) (small : Finset ℕ) : List ℕ :=
  let tail := small.sort (· ≥ ·)
  if shift && 3 ≤ m then m::tail else tail

def decodeProfile (m : ℕ) (shift : Bool) (parts : List ℕ) (small : Finset ℕ) : List ℕ :=
  profileFront m shift parts ++ profileTail m shift small

theorem length_profileFront (m : ℕ) (b : Bool) (p : List ℕ) :
    (profileFront m b p).length = p.length := by cases b <;> simp [profileFront]

theorem profileFront_bound {m : ℕ} {b : Bool} {p : List ℕ} {x : ℕ}
    (hx : x ∈ profileFront m b p) : m ≤ x := stairs_lower _ _ _ hx

theorem profileFront_strict {m : ℕ} {b : Bool} {p : List ℕ} {x : ℕ}
    (hb : b = true) (hx : x ∈ profileFront m b p) : m < x := by
  subst b
  change x ∈ stairs m (p.map (·+1)).reverse at hx
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
  rw [getElem_stairs] at he
  have hh : (p.map (·+1)).reverse[i]'(by simpa using hi) ∈ (p.map (·+1)).reverse :=
    List.getElem_mem (by simpa using hi)
  obtain ⟨a,_,ha⟩ := List.mem_map.mp (List.mem_reverse.mp hh)
  omega

theorem profileFront_pairwise {m : ℕ} {b : Bool} {p : List ℕ} (hp : p.Pairwise (· ≤ ·)) :
    (profileFront m b p).Pairwise (· > ·) := by
  cases b
  · exact stairs_pairwise (List.pairwise_reverse.mpr hp)
  · apply stairs_pairwise
    apply List.pairwise_reverse.mpr
    exact List.pairwise_map.mpr (hp.imp fun h => by omega)

theorem profileFront_cost {m e : ℕ} {b : Bool} {p : List ℕ} (hp : p ∈ paddedPartitions m e) :
    descendingCost 0 (profileFront m b p) = profileOffset m b + e := by
  obtain ⟨hl,_,hs⟩ := hp
  cases b
  · have hc := descendingCost_stairs 0 p.reverse
    simpa [profileFront,profileOffset,hl,hs,List.sum_reverse_nat] using hc
  · have hc := descendingCost_stairs 0 (p.map (·+1)).reverse
    simp [hl,hs] at hc
    simp [profileFront,profileOffset]
    omega

theorem mem_profileTail {m : ℕ} {b : Bool} {s : Finset ℕ} {x : ℕ} :
    x ∈ profileTail m b s ↔ x ∈ s ∨ (b = true ∧ 3 ≤ m ∧ x = m) := by
  cases b <;> by_cases hm : 3 ≤ m <;>
    simp [profileTail,hm,or_comm]

theorem profileTail_bound {m : ℕ} {b : Bool} {s : Finset ℕ} (hs : s ⊆ Ico 3 m)
    {x : ℕ} (hx : x ∈ profileTail m b s) : 3 ≤ x ∧ x ≤ m := by
  rcases mem_profileTail.mp hx with h | ⟨_,hm,rfl⟩
  · exact ⟨(mem_Ico.mp (hs h)).1,(mem_Ico.mp (hs h)).2.le⟩
  · exact ⟨hm,le_rfl⟩

theorem profileTail_pairwise {m : ℕ} {b : Bool} {s : Finset ℕ} (hs : s ⊆ Ico 3 m) :
    (profileTail m b s).Pairwise (· > ·) := by
  -- A sorted finset list has distinct entries.
  have hsort : (s.sort (· ≥ ·)).Pairwise (· > ·) := by
    have h := (s.pairwise_sort (· ≥ ·)).and (s.sort_nodup (· ≥ ·))
    exact h.imp fun ⟨hle,hne⟩ => lt_of_le_of_ne hle (Ne.symm hne)
  unfold profileTail
  split
  · exact List.pairwise_cons.mpr ⟨fun _ hx => (mem_Ico.mp (hs ((mem_sort (· ≥ ·)).mp hx))).2,hsort⟩
  · exact hsort

theorem decodeProfile_spec {m e : ℕ} {b : Bool} {p : List ℕ} {s : Finset ℕ}
    (hm : 2 ≤ m) (hb : b = true ∨ 3 ≤ m) (hp : p ∈ paddedPartitions m e)
    (hs : s ⊆ Ico 3 m) :
    let xs := decodeProfile m b p s
    2 ≤ xs.length ∧ xs.Pairwise (· > ·) ∧ (∀ x ∈ xs, 3 ≤ x) ∧
      positiveLength 0 xs = m ∧ descendingCost 0 xs = profileOffset m b + e := by
  have hl := (length_profileFront m b p).trans hp.1
  have hfront : ∀ x ∈ profileFront m b p, m ≤ x := fun _ => profileFront_bound
  have htail : ∀ x ∈ profileTail m b s, x ≤ m := fun _ hx => (profileTail_bound hs hx).2
  dsimp only [decodeProfile]
  refine ⟨by simp [hl]; omega,?_,?_,?_,?_⟩
  · apply List.pairwise_append.mpr
    refine ⟨profileFront_pairwise hp.2.1,profileTail_pairwise hs,?_⟩
    intro x hx y hy
    rcases mem_profileTail.mp hy with hy | ⟨hb',_,rfl⟩
    · exact (mem_Ico.mp (hs hy)).2.trans_le (hfront _ hx)
    · exact profileFront_strict hb' hx
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases hb with hb | hb
      · have := profileFront_strict hb hx
        omega
      · exact hb.trans (hfront _ hx)
    · exact (profileTail_bound hs hx).1
  · rw [positiveLength_append (j := 0) (by simpa [hl] using hfront) (by simpa [hl] using htail),hl]
  · rw [descendingCost_append,profileFront_cost hp, Nat.zero_add,hl,descendingCost_zero _ _ htail,
      Nat.add_zero]

theorem pairwise_gt_eq_of_mem {xs ys : List ℕ} (hx : xs.Pairwise (· > ·))
    (hy : ys.Pairwise (· > ·)) (h : ∀ x, x ∈ xs ↔ x ∈ ys) : xs = ys := by
  have hp := (List.perm_ext_iff_of_nodup (hx.imp fun h => ne_of_gt h)
    (hy.imp fun h => ne_of_gt h)).mpr h
  exact hp.eq_of_pairwise' (hx.imp fun h => le_of_lt h) (hy.imp fun h => le_of_lt h)

theorem decodeProfile_inj {m m' e e' : ℕ} {b b' : Bool} {p p' : List ℕ} {s s' : Finset ℕ}
    (hm : 2 ≤ m) (hm' : 2 ≤ m') (hb : b = true ∨ 3 ≤ m) (hb' : b' = true ∨ 3 ≤ m')
    (hp : p ∈ paddedPartitions m e) (hp' : p' ∈ paddedPartitions m' e')
    (hs : s ⊆ Ico 3 m) (hs' : s' ⊆ Ico 3 m')
    (heq : decodeProfile m b p s = decodeProfile m' b' p' s') :
    m = m' ∧ b = b' ∧ e = e' ∧ p = p' ∧ s = s' := by
  have h₁ := (decodeProfile_spec hm hb hp hs).2.2.2
  have h₂ := (decodeProfile_spec hm' hb' hp' hs').2.2.2
  have hme : m = m' := h₁.1.symm.trans (heq ▸ h₂.1)
  subst m'
  have hl := (length_profileFront m b p).trans hp.1
  have hl' := (length_profileFront m b' p').trans hp'.1
  have ht : profileTail m b s = profileTail m b' s' := by
    have h := congrArg (List.drop m) heq
    change (profileFront m b p ++ profileTail m b s).drop m =
      (profileFront m b' p' ++ profileTail m b' s').drop m at h
    have hta : (profileFront m b p ++ profileTail m b s).drop m = profileTail m b s := by
      exact List.drop_left' hl
    have htb : (profileFront m b' p' ++ profileTail m b' s').drop m = profileTail m b' s' := by
      exact List.drop_left' hl'
    rwa [hta,htb] at h
  have hbEq : b = b' := by
    by_cases h : 3 ≤ m
    · have hx : m ∈ profileTail m b s ↔ b = true := by
        simp [mem_profileTail,h,show m ∉ s from fun hh => (lt_irrefl m) (mem_Ico.mp (hs hh)).2]
      have hy : m ∈ profileTail m b' s' ↔ b' = true := by
        simp [mem_profileTail,h,show m ∉ s' from fun hh => (lt_irrefl m) (mem_Ico.mp (hs' hh)).2]
      cases b <;> cases b' <;> simp_all
    · exact (hb.resolve_right h).trans (hb'.resolve_right h).symm
  subst b'
  refine ⟨rfl,rfl,?_,?_,?_⟩
  · rw [heq,h₂.2] at h₁
    omega
  · have hf := congrArg (List.take m) heq
    change (profileFront m b p ++ profileTail m b s).take m =
      (profileFront m b p' ++ profileTail m b s').take m at hf
    have hfa : (profileFront m b p ++ profileTail m b s).take m = profileFront m b p := by
      exact List.take_left' hl
    have hfb : (profileFront m b p' ++ profileTail m b s').take m = profileFront m b p' := by
      exact List.take_left' hl'
    rw [hfa,hfb] at hf
    have h := congrArg (unstairs m) hf
    cases b
    · simpa [profileFront] using h
    · have hm' : p.map (·+1) = p'.map (·+1) := by
        simpa [profileFront] using h
      exact (List.map_injective_iff.mpr (fun _ _ h => by omega)) hm'
  · ext x
    by_cases hx : x = m
    · subst x
      exact iff_of_false (fun hx => (lt_irrefl m) (mem_Ico.mp (hs hx)).2)
        (fun hx => (lt_irrefl m) (mem_Ico.mp (hs' hx)).2)
    · simpa only [mem_profileTail,hx,and_false,or_false] using
        (show x ∈ profileTail m b s ↔ x ∈ profileTail m b s' by rw [ht])

/-- Every admissible list of sizes has one of the two partition forms. -/
theorem decodeProfile_surj {xs : List ℕ} (hlen : 2 ≤ xs.length) (hp : xs.Pairwise (· > ·))
    (hmin : ∀ x ∈ xs, 3 ≤ x) :
    ∃ (m : ℕ) (b : Bool) (e : ℕ) (p : List ℕ) (s : Finset ℕ),
      2 ≤ m ∧ (b = true ∨ 3 ≤ m) ∧ p ∈ paddedPartitions m e ∧ s ⊆ Ico 3 m ∧
      decodeProfile m b p s = xs := by
  let m := positiveLength 0 xs
  have hm : 2 ≤ m := by
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      cases xs with
      | nil => simp at hlen
      | cons y xs =>
        have hx := hmin x (by simp)
        have hy := hmin y (by simp)
        dsimp [m]
        rw [positiveLength,if_pos (by omega),positiveLength,if_pos (by omega)]
        omega
  let front := xs.take m
  let tail := xs.drop m
  have hsplit : front ++ tail = xs := List.take_append_drop m xs
  obtain ⟨hle,hfront,htail⟩ := positiveLength_spec (j := 0) hp
  change m ≤ xs.length at hle
  have hf : ∀ x ∈ front, m ≤ x := by simpa [front,m] using hfront
  have ht : ∀ x ∈ tail, x ≤ m := by simpa [tail,m] using htail
  have hfl : front.length = m := List.length_take_of_le hle
  have hpp := List.pairwise_append.mp (hsplit.symm ▸ hp)
  let v := unstairs m front
  have hv : v.Pairwise (· ≥ ·) := unstairs_pairwise hpp.1
  have hstairs : stairs m v = front := stairs_unstairs hpp.1 hf
  let b := decide (m = 2 ∨ m ∈ tail)
  have hbc : b = true ↔ m = 2 ∨ m ∈ tail := by simp [b]
  have hb : b = true ∨ 3 ≤ m := by
    by_cases h : m = 2
    · exact Or.inl (hbc.mpr (Or.inl h))
    · exact Or.inr (by omega)
  let s := tail.toFinset.erase m
  have hs : s ⊆ Ico 3 m := by
    intro x hx
    obtain ⟨hne,hmem⟩ := mem_erase.mp hx
    have hx' := List.mem_toFinset.mp hmem
    exact mem_Ico.mpr ⟨hmin _ (List.mem_of_mem_drop hx'),lt_of_le_of_ne (ht _ hx') hne⟩
  have htailEq : profileTail m b s = tail := by
    apply pairwise_gt_eq_of_mem (profileTail_pairwise hs) hpp.2.1
    intro x
    rw [mem_profileTail]
    constructor
    · rintro (h | ⟨hb',hm',rfl⟩)
      · exact List.mem_toFinset.mp (mem_of_mem_erase h)
      · exact (hbc.mp hb').resolve_left (by omega)
    · intro hx
      by_cases he : x = m
      · subst x
        exact Or.inr ⟨hbc.mpr (Or.inr hx),hmin _ (List.mem_of_mem_drop hx),rfl⟩
      · exact Or.inl (mem_erase.mpr ⟨he,List.mem_toFinset.mpr hx⟩)
  by_cases hshift : b = true
  · have hnom : m ∉ front := by
      intro hmem
      rcases hbc.mp hshift with htwo | hmem'
      · have := hmin _ (List.mem_of_mem_take hmem)
        omega
      · exact (lt_irrefl m) (hpp.2.2 _ hmem _ hmem')
    have hzero : 0 ∉ v := (not_mem_stairs_floor hv).mp (hstairs.symm ▸ hnom)
    have hpos : ∀ a ∈ v.reverse, 0 < a := fun a ha =>
      Nat.pos_of_ne_zero (fun he => hzero (he ▸ List.mem_reverse.mp ha))
    let p := v.reverse.map (·-1)
    have hpmap : p.map (·+1) = v.reverse := pred_map_of_positive _ hpos
    refine ⟨m,b,p.sum,p,s,hm,hb,⟨by simp [p,v,hfl],?_,rfl⟩,hs,?_⟩
    · exact List.pairwise_map.mpr ((List.pairwise_reverse.mpr hv).imp fun h => by omega)
    · rw [decodeProfile,htailEq,profileFront,if_pos hshift,hpmap,List.reverse_reverse,hstairs,hsplit]
  · have hbf : b = false := Bool.eq_false_iff.mpr hshift
    refine ⟨m,b,v.reverse.sum,v.reverse,s,hm,hb,⟨by simp [v,hfl],List.pairwise_reverse.mpr hv,rfl⟩,hs,?_⟩
    rw [decodeProfile,htailEq,profileFront,hbf]
    simpa only [Bool.false_eq_true,if_false,List.reverse_reverse,hstairs] using hsplit

end Erdos607
