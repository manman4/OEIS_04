import A401948Lean.OrdinaryLine
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Set.Card

/-! Classification and exact count of the realizable line-size profiles. -/

namespace Erdos607

open Finset
open scoped BigOperators

noncomputable section
open Classical

def Realized (n : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset Point, P.card = n ∧ profile P = A

private theorem linePoints_subset (P : Finset Point) (l : Line) :
    linePoints P l ⊆ P := fun _ hp => (mem_linePoints.mp hp).1

private theorem profile_singleton_of_collinear {P : Finset Point} (hc : 2 ≤ P.card)
    {l : Line} (hl : ∀ p ∈ P, On l p) : profile P = {P.card} := by
  ext k
  change (2 ≤ k ∧ ∃ m : Line, (linePoints P m).card = k) ↔ k = P.card
  have hline : linePoints P l = P := by
    ext p
    exact mem_linePoints.trans ⟨And.left, fun hp => ⟨hp,hl p hp⟩⟩
  constructor
  · rintro ⟨hk,m,hm⟩
    obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (by omega : 1 < (linePoints P m).card)
    obtain ⟨ha,ham⟩ := mem_linePoints.mp ha
    obtain ⟨hb,hbm⟩ := mem_linePoints.mp hb
    have he := line_eq_of_points hab ham hbm (hl a ha) (hl b hb)
    rw [he,hline] at hm
    exact hm.symm
  · rintro rfl
    exact ⟨hc,l,by rw [hline]⟩

private theorem profile_empty_of_small {P : Finset Point} (hc : P.card < 2) :
    profile P = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro k ⟨hk,l,hl⟩
  have := card_le_card (linePoints_subset P l)
  omega

private theorem profile_lt_card_of_noncollinear {P : Finset Point}
    (hn : ¬ ∃ l : Line, ∀ p ∈ P, On l p) {k : ℕ} (hk : k ∈ profile P) : k < P.card := by
  obtain ⟨_,l,hl⟩ := hk
  rw [← hl]
  apply card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨linePoints_subset P l,?_⟩
  intro he
  apply hn
  exact ⟨l, fun p hp => (mem_linePoints.mp (he.symm ▸ hp)).2⟩

private def horizontal : Line := .graph 0 0
private def row (n : ℕ) : Finset Point :=
  (range n).map ⟨fun k : ℕ => ((k : ℝ),0), fun _ _ h => Nat.cast_injective (congrArg Prod.fst h)⟩

private theorem card_row (n : ℕ) : (row n).card = n := by
  simp [row]

private theorem on_row {n : ℕ} {p : Point} (h : p ∈ row n) : On horizontal p := by
  obtain ⟨k,_,rfl⟩ := mem_map.mp h
  simp [horizontal,On]

private theorem realized_pair {s n : ℕ} (hs : 2 ≤ s) (hn : s < n) :
    Realized n {2,s} := by
  let p : Point := (0,1)
  let P := insert p (row s)
  have hoff : ¬ On horizontal p := by norm_num [p,horizontal,On]
  have hpc : P.card = s+1 := by rw [card_insert_of_notMem (fun h => hoff (on_row h)),card_row]
  have hhor : (linePoints P horizontal).card = s := by
    rw [linePoints_insert, if_neg hoff]
    have he : linePoints (row s) horizontal = row s := by
      ext q
      exact mem_linePoints.trans ⟨And.left, fun h => ⟨h,on_row h⟩⟩
    rw [he,card_row]
  have hrest (l : Line) (hl : l ≠ horizontal) : (linePoints P l).card ≤ 2 := by
    have hle : (linePoints (row s) l).card ≤ 1 := by
      apply card_le_one.mpr
      intro a ha b hb
      by_contra hab
      obtain ⟨ha,hal⟩ := mem_linePoints.mp ha
      obtain ⟨hb,hbl⟩ := mem_linePoints.mp hb
      exact hl (line_eq_of_points hab hal hbl (on_row ha) (on_row hb))
    unfold P
    rw [linePoints_insert]
    split
    · exact (card_insert_le _ _).trans (by omega)
    · omega
  have hnon : ¬ ∃ l : Line, ∀ q ∈ P, On l q := by
    rintro ⟨l,hl⟩
    have hlne : l ≠ horizontal := fun he => hoff (he ▸ hl p (mem_insert_self ..))
    have he : linePoints P l = P := by
      ext q
      exact mem_linePoints.trans ⟨And.left,fun h => ⟨h,hl q h⟩⟩
    have hc := hrest l hlne
    rw [he,hpc] at hc
    omega
  have htwo := two_mem_profile_of_noncollinear (P := P) (by omega) hnon
  have hprof : profile P = {2,s} := by
    ext k
    change (2 ≤ k ∧ ∃ l : Line, (linePoints P l).card = k) ↔ k = 2 ∨ k = s
    constructor
    · rintro ⟨hk,l,hl⟩
      by_cases he : l = horizontal
      · rw [he,hhor] at hl
        exact Or.inr hl.symm
      · have := hrest l he
        exact Or.inl (by omega)
    · rintro (rfl | rfl)
      · exact htwo
      · exact ⟨hs,horizontal,hhor⟩
  obtain ⟨Q,hQ,hQprof⟩ := exists_padding P htwo (n-(s+1))
  exact ⟨Q,by omega,hQprof.trans hprof⟩

/-- The profiles with at least two distinct sizes greater than two. -/
def LargeProfile (n : ℕ) (A : Set ℕ) : Prop :=
  ∃ (r : ℕ) (sizes : Fin r → ℕ), 2 ≤ r ∧ StrictMono sizes ∧
    (∀ i, 3 ≤ sizes i) ∧ required sizes ≤ n ∧ A = insert 2 (Set.range sizes)

/-- The profiles with zero or one size greater than two, and the collinear profiles. -/
def smallProfiles (n : ℕ) : Finset (Set ℕ) :=
  if n = 1 then {∅} else if n = 2 then {{2}} else
    insert {n} (insert {2} ((Ico 3 n).image fun k => ({2,k} : Set ℕ)))

private theorem smallProfiles_mem_of_pair {n s : ℕ} (hs : 3 ≤ s) (hn : s < n) :
    ({2,s} : Set ℕ) ∈ smallProfiles n := by
  have h1 : n ≠ 1 := by omega
  have h2 : n ≠ 2 := by omega
  simp only [smallProfiles,h1,h2,if_false,mem_insert]
  exact Or.inr (Or.inr (mem_image.mpr ⟨s,mem_Ico.mpr ⟨hs,hn⟩,rfl⟩))

/-- The small cases and the exact point bound exhaust all realizable profiles. -/
theorem realized_iff_classified {n : ℕ} (hn : 1 ≤ n) (A : Set ℕ) :
    Realized n A ↔ A ∈ smallProfiles n ∨ LargeProfile n A := by
  constructor
  · rintro ⟨P,hP,rfl⟩
    by_cases hn1 : n = 1
    · left
      have he := profile_empty_of_small (P := P) (by omega)
      simp [smallProfiles,hn1,he]
    have hn2 : 2 ≤ n := by omega
    by_cases hc : ∃ l : Line, ∀ p ∈ P, On l p
    · left
      obtain ⟨l,hl⟩ := hc
      rw [profile_singleton_of_collinear (P := P) (by omega) hl,hP]
      by_cases h2 : n = 2 <;> simp [smallProfiles,hn1,h2]
    have htwo := two_mem_profile_of_noncollinear (P := P) (by omega) hc
    have hn3 : 3 ≤ n := by
      have h := profile_lt_card_of_noncollinear hc htwo
      omega
    have h2 : n ≠ 2 := by omega
    let S := (Ico 3 n).filter fun k => k ∈ profile P
    have hset : profile P = insert 2 (S : Set ℕ) := by
      ext k
      constructor
      · intro hk
        by_cases he : k = 2
        · exact Or.inl he
        · have hl := profile_lt_card_of_noncollinear hc hk
          have hk2 := hk.1
          exact Or.inr (mem_filter.mpr ⟨mem_Ico.mpr ⟨by omega,by omega⟩,hk⟩)
      · rintro (rfl | hk)
        · exact htwo
        · change k ∈ S at hk
          exact (mem_filter.mp hk).2
    by_cases h0 : S.card = 0
    · left
      rw [card_eq_zero.mp h0] at hset
      have he : profile P = {2} := by simpa using hset
      simp [he,smallProfiles,hn1,h2]
    by_cases h1 : S.card = 1
    · left
      obtain ⟨s,he⟩ := card_eq_one.mp h1
      have hs : s ∈ S := by simp [he]
      have hsr := mem_Ico.mp (mem_filter.mp hs).1
      rw [he] at hset
      have he' : profile P = {2,s} := by simpa using hset
      rw [he']
      exact smallProfiles_mem_of_pair hsr.1 hsr.2
    · right
      let s := S.orderEmbOfFin rfl
      have hs : StrictMono s := s.strictMono
      have hmin (i : Fin S.card) : 3 ≤ s i :=
        (mem_Ico.mp (mem_filter.mp (S.orderEmbOfFin_mem rfl i)).1).1
      have hrange : Set.range s = (S : Set ℕ) := S.range_orderEmbOfFin rfl
      exact ⟨S.card,s,by omega,hs,hmin,by
        rw [← hP]
        apply required_le_card_of_sizes hs
        rw [hrange,hset]
        exact Set.subset_insert _ _,by rw [hrange]; exact hset⟩
  · rintro (h | ⟨r,s,hr,hs,hmin,hL,rfl⟩)
    · by_cases hn1 : n = 1
      · have he : A = ∅ := by simpa [smallProfiles,hn1] using h
        subst A
        refine ⟨{(0,0)},by simp [hn1],profile_empty_of_small (by simp)⟩
      by_cases hn2 : n = 2
      · have he : A = {2} := by simpa [smallProfiles,hn1,hn2] using h
        subst A
        refine ⟨row n,card_row n,?_⟩
        rw [profile_singleton_of_collinear (P := row n) (by rw [card_row,hn2]) (fun _ => on_row),
          card_row,hn2]
      simp only [smallProfiles,hn1,hn2,if_false,mem_insert] at h
      rcases h with rfl | rfl | h
      · exact ⟨row n,card_row n,by
          rw [profile_singleton_of_collinear (P := row n) (by rw [card_row]; omega)
            (fun _ => on_row),card_row]⟩
      · simpa using realized_pair (s := 2) (by decide) (by omega : 2 < n)
      · obtain ⟨s,hs,rfl⟩ := mem_image.mp h
        exact realized_pair (by have := (mem_Ico.mp hs).1; omega) (mem_Ico.mp hs).2
    · exact (realizable_iff hr hs hmin).mpr hL


private theorem profile_subset_interval {n : ℕ} {A : Set ℕ} (h : Realized n A) :
    A ⊆ (Icc 2 n : Finset ℕ) := by
  obtain ⟨P,hP,rfl⟩ := h
  rintro k ⟨hk,l,hl⟩
  have hbound := card_le_card (linePoints_subset P l)
  exact mem_Icc.mpr ⟨hk,by omega⟩

private theorem realized_finite (n : ℕ) : {A | Realized n A}.Finite :=
  (Icc 2 n).finite_toSet.finite_subsets.subset (fun _ => profile_subset_interval)

private theorem ncard_insert_range {r : ℕ} {s : Fin r → ℕ} (hs : StrictMono s)
    (hmin : ∀ i, 3 ≤ s i) : (insert 2 (Set.range s)).ncard = r+1 := by
  have hnot : 2 ∉ Set.range s := by
    rintro ⟨i,hi⟩
    have := hmin i
    omega
  rw [Set.ncard_insert_of_notMem hnot, Set.ncard_range_of_injective hs.injective]
  simp

private theorem smallProfiles_card (n : ℕ) (hn : 1 ≤ n) :
    (smallProfiles n).card = max 1 (n-1) := by
  by_cases h1 : n = 1
  · simp [smallProfiles,h1]
  by_cases h2 : n = 2
  · simp [smallProfiles,h2]
  let pairs := (Ico 3 n).image fun k => ({2,k} : Set ℕ)
  have hpair (s : ℕ) (hs : s ∈ Ico 3 n) : 2 ∈ ({2,s} : Set ℕ) := by simp
  have hnot2 : ({2} : Set ℕ) ∉ pairs := by
    intro h
    obtain ⟨s,hs,he⟩ := mem_image.mp h
    have he' : s ∈ ({2} : Set ℕ) := he ▸ (by simp : s ∈ ({2,s} : Set ℕ))
    simp at he'
    have := (mem_Ico.mp hs).1
    omega
  have hnotn : ({n} : Set ℕ) ∉ insert ({2} : Set ℕ) pairs := by
    intro h
    have hmem : 2 ∈ ({n} : Set ℕ) := by
      rcases mem_insert.mp h with he | hp
      · rw [he]; simp
      · obtain ⟨s,hs,he⟩ := mem_image.mp hp
        exact he ▸ hpair s hs
    exact h2 (by simpa [eq_comm] using hmem)
  have hpairs : pairs.card = n-3 := by
    rw [show pairs.card = (Ico 3 n).card from card_image_iff.mpr (by
      intro a ha b hb he
      change ({2,a} : Set ℕ) = {2,b} at he
      have ham : a ∈ ({2,b} : Set ℕ) := he ▸ (by simp : a ∈ ({2,a} : Set ℕ))
      have hamin : 3 ≤ a := (mem_Ico.mp ha).1
      simp at ham
      omega),Nat.card_Ico]
  change (if n = 1 then _ else if n = 2 then _ else insert {n} (insert {2} pairs)).card = _
  rw [if_neg h1,if_neg h2,card_insert_of_notMem hnotn,card_insert_of_notMem hnot2,hpairs]
  omega

private theorem smallProfiles_size_le {n : ℕ} {A : Set ℕ} (h : A ∈ smallProfiles n) :
    A.ncard ≤ 2 := by
  unfold smallProfiles at h
  split at h
  · obtain rfl := mem_singleton.mp h
    simp
  split at h
  · obtain rfl := mem_singleton.mp h
    simp
  simp only [mem_insert] at h
  rcases h with rfl | rfl | h
  · simp
  · simp
  obtain ⟨s,hs,rfl⟩ := mem_image.mp h
  rw [Set.ncard_pair (show 2 ≠ s by have := (mem_Ico.mp hs).1; omega)]

/-- Number of line-size sets realized by exactly `n` distinct planar points. -/
def F (n : ℕ) : ℕ := {A | Realized n A}.ncard

/-- Number of large profiles with exactly `r` sizes greater than two. -/
def countByLength (n r : ℕ) : ℕ :=
  {A | ∃ s : Fin r → ℕ, 2 ≤ r ∧ StrictMono s ∧ (∀ i, 3 ≤ s i) ∧
    required s ≤ n ∧ A = insert 2 (Set.range s)}.ncard

/-- The geometric count equals the small cases plus the counts by length. -/
theorem F_eq_countByLength (n : ℕ) (hn : 1 ≤ n) :
    F n = max 1 (n-1) + ∑ r ∈ Icc 2 n, countByLength n r := by
  let L : Set (Set ℕ) := {A | LargeProfile n A}
  have hset : {A | Realized n A} = ((smallProfiles n : Finset (Set ℕ)) : Set (Set ℕ)) ∪ L := by
    ext A
    exact realized_iff_classified hn A
  have hfin : L.Finite := (realized_finite n).subset
    (fun A h => (realized_iff_classified hn A).mpr (Or.inr h))
  have hdisj : Disjoint ((smallProfiles n : Finset (Set ℕ)) : Set (Set ℕ)) L := by
    apply Set.disjoint_left.mpr
    rintro A hA ⟨r,s,hr,hs,hmin,_,rfl⟩
    have hc := smallProfiles_size_le hA
    rw [ncard_insert_range hs hmin] at hc
    omega
  unfold F
  rw [hset,Set.ncard_union_eq hdisj (smallProfiles n).finite_toSet hfin,
    Set.ncard_coe_finset,smallProfiles_card n hn]
  congr 1
  let S := hfin.toFinset
  have hS : (S : Set (Set ℕ)) = L := hfin.coe_toFinset
  rw [← hS,Set.ncard_coe_finset]
  have hmaps : Set.MapsTo (fun A : Set ℕ => A.ncard-1) S (Icc 2 n : Finset ℕ) := by
    intro A hA
    rw [hS] at hA
    obtain ⟨r,s,hr,hs,hmin,hL,rfl⟩ := hA
    change (insert 2 (Set.range s)).ncard - 1 ∈ Icc 2 n
    rw [ncard_insert_range hs hmin]
    have hreal := (realizable_iff hr hs hmin).mpr hL
    have hb := Set.ncard_le_ncard (profile_subset_interval hreal) (Icc 2 n).finite_toSet
    rw [ncard_insert_range hs hmin,Set.ncard_coe_finset,Nat.card_Icc] at hb
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  rw [card_eq_sum_card_fiberwise hmaps]
  apply sum_congr rfl
  intro r _
  have he : ((S.filter (fun A => A.ncard-1 = r) : Finset (Set ℕ)) : Set (Set ℕ)) =
      {A | ∃ s : Fin r → ℕ, 2 ≤ r ∧ StrictMono s ∧ (∀ i, 3 ≤ s i) ∧
        required s ≤ n ∧ A = insert 2 (Set.range s)} := by
    ext A
    change A ∈ S.filter (fun B => B.ncard-1 = r) ↔ _
    have hm : A ∈ S ↔ LargeProfile n A := by
      change A ∈ (S : Set (Set ℕ)) ↔ _
      rw [hS]
      rfl
    rw [mem_filter,hm]
    change (LargeProfile n A ∧ A.ncard-1 = r) ↔
      ∃ s : Fin r → ℕ, 2 ≤ r ∧ StrictMono s ∧ (∀ i, 3 ≤ s i) ∧
        required s ≤ n ∧ A = insert 2 (Set.range s)
    constructor
    · rintro ⟨⟨k,s,hk,hs,hmin,hL,rfl⟩,hc⟩
      rw [ncard_insert_range hs hmin] at hc
      have heq : k = r := by omega
      subst k
      exact ⟨s,hk,hs,hmin,hL,rfl⟩
    · rintro ⟨s,hr,hs,hmin,hL,rfl⟩
      exact ⟨⟨r,s,hr,hs,hmin,hL,rfl⟩,by rw [ncard_insert_range hs hmin]; omega⟩
  unfold countByLength
  rw [← he,Set.ncard_coe_finset]

end
end Erdos607
