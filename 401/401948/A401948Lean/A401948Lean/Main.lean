import A401948Lean.Definitions
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Realizability of line-size sets in Erdős Problem 607
-/

namespace Erdos607

open Finset
open scoped BigOperators

noncomputable section
open Classical

private instance : Infinite ℝ :=
  Infinite.of_injective (fun n : ℕ => (n : ℝ)) Nat.cast_injective

theorem line_eq_of_points {l m : Line} {p q : Point} (hpq : p ≠ q)
    (hp : On l p) (hq : On l q) (hp' : On m p) (hq' : On m q) : l = m := by
  cases l with
  | vertical a =>
    cases m with
    | vertical b =>
      simp only [On] at hp hp'
      congr 1
      exact hp.symm.trans hp'
    | graph s b =>
      simp only [On] at hp hq hp' hq'
      exact (hpq (Prod.ext (hp.trans hq.symm) (by rw [hp', hq', hp, hq]))).elim
  | graph s b =>
    cases m with
    | vertical a =>
      simp only [On] at hp hq hp' hq'
      exact (hpq (Prod.ext (hp'.trans hq'.symm) (by rw [hp, hq, hp', hq']))).elim
    | graph t c =>
      simp only [On] at hp hq hp' hq'
      have hprod : (s - t) * (p.1 - q.1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hprod with hst | hx
      · have h : s = t := sub_eq_zero.mp hst
        subst t
        have : b = c := by linarith
        subst c
        rfl
      · have h : p.1 = q.1 := sub_eq_zero.mp hx
        exact (hpq (Prod.ext h (by rw [hp, hq, h]))).elim

theorem exists_line (p q : Point) : ∃ l : Line, On l p ∧ On l q := by
  by_cases h : p.1 = q.1
  · exact ⟨.vertical p.1, rfl, h.symm⟩
  · let m := (q.2 - p.2) / (q.1 - p.1)
    have hm : m * (q.1 - p.1) = q.2 - p.2 :=
      div_mul_cancel₀ _ (sub_ne_zero.mpr (Ne.symm h))
    refine ⟨.graph m (p.2 - m * p.1), ?_, ?_⟩ <;> simp only [On] <;> nlinarith

private theorem card_line_inter_le_one (P : Finset Point) {l m : Line} (h : l ≠ m) :
    ((linePoints P l) ∩ (linePoints P m)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra hpq
  simp only [mem_inter, mem_linePoints] at hp hq
  exact h (line_eq_of_points hpq hp.1.2 hq.1.2 hp.2.2 hq.2.2)

private theorem bound_card {r : ℕ} (P : Finset Point) (S : Fin r → Finset Point)
    (hP : ∀ i, S i ⊆ P) (hS : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) :
    (∑ i : Fin r, ((S i).card + (i.val + 1) - r)) ≤ P.card := by
  classical
  let later (i : Fin r) : Finset Point := (Ioi i).biUnion S
  let fresh (i : Fin r) : Finset Point := S i \ later i
  have hf (i : Fin r) : (S i).card + (i.val + 1) - r ≤ (fresh i).card := by
    have hsub : S i ∩ later i ⊆ (Ioi i).biUnion (fun j => S i ∩ S j) := by
      intro p hp
      obtain ⟨hi, hj⟩ := mem_inter.mp hp
      obtain ⟨j, hj, hpj⟩ := mem_biUnion.mp hj
      exact mem_biUnion.mpr ⟨j, hj, mem_inter.mpr ⟨hi, hpj⟩⟩
    have hb : (S i ∩ later i).card ≤ r - (i.val + 1) := calc
      _ ≤ ((Ioi i).biUnion (fun j => S i ∩ S j)).card := card_le_card hsub
      _ ≤ ∑ j ∈ Ioi i, (S i ∩ S j).card := card_biUnion_le
      _ ≤ ∑ _j ∈ Ioi i, 1 := sum_le_sum (fun j hj => hS i j (ne_of_lt (mem_Ioi.mp hj)))
      _ = _ := by simp [Fin.card_Ioi, Nat.sub_sub, Nat.add_comm]
    have he := card_sdiff_add_card_inter (S i) (later i)
    change (fresh i).card + (S i ∩ later i).card = (S i).card at he
    have hlt := i.isLt
    omega
  have hdisj : ((univ : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint fresh := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro p hi hj
    obtain ⟨hiS, hiN⟩ := mem_sdiff.mp hi
    obtain ⟨hjS, hjN⟩ := mem_sdiff.mp hj
    rcases lt_or_gt_of_ne hij with h | h
    · exact hiN (mem_biUnion.mpr ⟨j, mem_Ioi.mpr h, hjS⟩)
    · exact hjN (mem_biUnion.mpr ⟨i, mem_Ioi.mpr h, hiS⟩)
  calc
    _ ≤ ∑ i : Fin r, (fresh i).card := sum_le_sum (fun i _ => hf i)
    _ = ((univ : Finset (Fin r)).biUnion fresh).card := (card_biUnion hdisj).symm
    _ ≤ P.card := card_le_card (by
      intro p hp
      obtain ⟨i, _, hi⟩ := mem_biUnion.mp hp
      exact hP i (mem_sdiff.mp hi).1)

/-- Each realizable profile must satisfy the proposed point bound. -/
theorem required_le_card_of_sizes {r : ℕ} {sizes : Fin r → ℕ} (hs : StrictMono sizes)
    {P : Finset Point}
    (h : Set.range sizes ⊆ profile P) : required sizes ≤ P.card := by
  classical
  have hlines (i : Fin r) : ∃ l : Line, (linePoints P l).card = sizes i :=
    (h ⟨i, rfl⟩).2
  choose l hl using hlines
  have hne (i j : Fin r) (hij : i ≠ j) : l i ≠ l j := by
    intro he
    apply hij
    apply hs.injective
    rw [← hl i, ← hl j, he]
  simpa only [required, hl] using
    bound_card P (fun i => linePoints P (l i))
      (fun i p hp => (mem_linePoints.mp hp).1)
      (fun i j hij => card_line_inter_le_one P (hne i j hij))

private noncomputable def join (p q : Point) : Line := (exists_line p q).choose

private theorem on_join_left (p q : Point) : On (join p q) p :=
  (exists_line p q).choose_spec.1

private theorem on_join_right (p q : Point) : On (join p q) q :=
  (exists_line p q).choose_spec.2

private def carrier (a : ℝ) : Line := .graph a (-a^2)

private theorem carrier_injective : Function.Injective carrier := by
  intro a b h
  simpa [carrier] using congrArg (fun l => match l with
    | .graph m _ => m
    | .vertical x => x) h

private def atX (a x : ℝ) : Point := (x, a*x - a^2)

private theorem atX_on (a x : ℝ) : On (carrier a) (atX a x) := by
  simp [carrier, On, atX, sub_eq_add_neg]

private theorem atX_injective (a : ℝ) : Function.Injective (atX a) :=
  fun _ _ h => congrArg Prod.fst h

private def cross (a b : ℝ) : Point := (a+b, a*b)

private theorem cross_eq_atX (a b : ℝ) : cross a b = atX a (a+b) := by
  unfold cross atX
  congr 1
  ring

private theorem cross_comm (a b : ℝ) : cross a b = cross b a := by
  simp [cross, add_comm, mul_comm]

private theorem on_cross_iff (a b c : ℝ) : On (carrier c) (cross a b) ↔ c = a ∨ c = b := by
  change a*b = c*(a+b) + -c^2 ↔ _
  constructor
  · intro h
    have hzero : (c-a)*(c-b) = 0 := by nlinarith
    exact (mul_eq_zero.mp hzero).imp sub_eq_zero.mp sub_eq_zero.mp
  · rintro (rfl | rfl) <;> ring

private def crossings (ts : Finset ℝ) : Finset Point :=
  ((ts ×ˢ ts).filter (fun p => p.1 ≠ p.2)).image (fun p => cross p.1 p.2)

private theorem mem_crossings {ts : Finset ℝ} {p : Point} :
    p ∈ crossings ts ↔ ∃ a ∈ ts, ∃ b ∈ ts, a ≠ b ∧ p = cross a b := by
  simp only [crossings, mem_image, mem_filter, mem_product, Prod.exists]
  grind

private theorem on_crossings_insert {ts : Finset ℝ} {p : Point} {t : ℝ}
    (hp : p ∈ crossings (insert t ts)) (hold : p ∉ crossings ts) :
    ∃ a ∈ ts, p = cross a t := by
  obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_crossings.mp hp
  rcases mem_insert.mp ha with he | ha
  · subst a
    have hb' : b ∈ ts := (mem_insert.mp hb).resolve_left (Ne.symm hab)
    exact ⟨b, hb', cross_comm t b⟩
  · rcases mem_insert.mp hb with he | hb
    · subst b
      exact ⟨a, ha, rfl⟩
    · exact (hold (mem_crossings.mpr ⟨a, ha, b, hb, hab, rfl⟩)).elim

private def supported (ts : Finset ℝ) (P : Finset Point) : Prop :=
  ∀ l : Line, 2 < (linePoints P l).card → ∃ a ∈ ts, l = carrier a

private theorem finite_bad {α β : Type*} [Infinite α] (S : Finset β) (B : β → Set α)
    (h : ∀ i ∈ S, ∀ a ∈ B i, ∀ b ∈ B i, a = b) :
    (⋃ i ∈ (S : Set β), B i).Finite := by
  apply S.finite_toSet.biUnion
  intro i hi
  by_cases he : (B i).Nonempty
  · obtain ⟨a, ha⟩ := he
    exact (Set.finite_singleton a).subset (fun b hb => h i hi b hb a ha)
  · rw [Set.not_nonempty_iff_eq_empty.mp he]
    exact Set.finite_empty

private theorem exists_new_parameter (ts : Finset ℝ) :
    ∃ t ∉ ts, ∀ a ∈ ts, ∀ p ∈ crossings ts, ∀ q ∈ crossings ts,
      join p q ≠ carrier a → ¬On (join p q) (cross a t) := by
  let I := ts ×ˢ (crossings ts ×ˢ crossings ts)
  let B (i : ℝ × (Point × Point)) : Set ℝ :=
    {t | join i.2.1 i.2.2 ≠ carrier i.1 ∧ On (join i.2.1 i.2.2) (cross i.1 t)}
  have hf : (⋃ i ∈ (I : Set _), B i).Finite := by
    apply finite_bad
    intro i _ a ha b hb
    by_contra hab
    have hc : cross i.1 a ≠ cross i.1 b := by
      intro h
      have hx := congrArg Prod.fst h
      dsimp [cross] at hx
      exact hab (add_left_cancel hx)
    exact ha.1 (line_eq_of_points hc ha.2 hb.2
      ((cross_eq_atX i.1 a).symm ▸ atX_on i.1 (i.1+a))
      ((cross_eq_atX i.1 b).symm ▸ atX_on i.1 (i.1+b)))
  obtain ⟨t, ht⟩ := (ts.finite_toSet.union hf).exists_notMem
  refine ⟨t, fun h => ht (Or.inl h), ?_⟩
  intro a ha p hp q hq hne hon
  apply ht
  right
  exact Set.mem_iUnion₂.mpr ⟨(a,p,q), by simpa [I] using And.intro ha (And.intro hp hq),
    ⟨hne, hon⟩⟩

private theorem supported_crossings_insert {ts : Finset ℝ} (h : supported ts (crossings ts)) :
    ∃ t ∉ ts, supported (insert t ts) (crossings (insert t ts)) := by
  obtain ⟨t, ht, havoid⟩ := exists_new_parameter ts
  refine ⟨t, ht, ?_⟩
  intro l hl
  obtain ⟨p, hp, q, hq, z, hz, hpq, hpz, hqz⟩ := two_lt_card.mp hl
  simp only [mem_linePoints] at hp hq hz
  have hcase (p q z : Point)
      (hp : p ∈ crossings (insert t ts) ∧ On l p)
      (hq : q ∈ crossings (insert t ts) ∧ On l q)
      (hz : z ∈ crossings (insert t ts) ∧ On l z)
      (hpq : p ≠ q) (hpz : p ≠ z) (hqz : q ≠ z) :
      p ∉ crossings ts → ∃ a ∈ insert t ts, l = carrier a := by
    intro hpn
    obtain ⟨a, ha, rfl⟩ := on_crossings_insert hp.1 hpn
    have hon (x : Point) (hx : x ∈ crossings (insert t ts)) (hxo : x ∉ crossings ts) :
        On (carrier t) x := by
      obtain ⟨b, _, rfl⟩ := on_crossings_insert hx hxo
      exact (on_cross_iff b t t).mpr (Or.inr rfl)
    have htOn : On (carrier t) (cross a t) := (on_cross_iff a t t).mpr (Or.inr rfl)
    by_cases hqo : q ∈ crossings ts
    · by_cases hzo : z ∈ crossings ts
      · have hj : l = join q z := line_eq_of_points hqz hq.2 hz.2
          (on_join_left q z) (on_join_right q z)
        have hc : join q z = carrier a := by
          by_contra he
          exact havoid a ha q hqo z hzo he (hj ▸ hp.2)
        exact ⟨a, mem_insert_of_mem ha, hj.trans hc⟩
      · exact ⟨t, mem_insert_self _ _, line_eq_of_points hpz hp.2 hz.2 htOn (hon z hz.1 hzo)⟩
    · exact ⟨t, mem_insert_self _ _, line_eq_of_points hpq hp.2 hq.2 htOn (hon q hq.1 hqo)⟩
  by_cases hpo : p ∈ crossings ts
  · by_cases hqo : q ∈ crossings ts
    · by_cases hzo : z ∈ crossings ts
      · obtain ⟨a, ha, he⟩ := h l (two_lt_card.mpr
          ⟨p, mem_linePoints.mpr ⟨hpo, hp.2⟩, q, mem_linePoints.mpr ⟨hqo, hq.2⟩,
           z, mem_linePoints.mpr ⟨hzo, hz.2⟩, hpq, hpz, hqz⟩)
        exact ⟨a, mem_insert_of_mem ha, he⟩
      · exact hcase z p q hz hp hq hpz.symm hqz.symm hpq hzo
    · exact hcase q p z hq hp hz hpq.symm hqz hpz hqo
  · exact hcase p q z hp hq hz hpq hpz hqz hpo

/-- The parameter lines can be chosen without unintended collinear triples of intersections. -/
private theorem exists_supported_crossings (r : ℕ) :
    ∃ ts : Finset ℝ, ts.card = r ∧ supported ts (crossings ts) := by
  induction r with
  | zero => exact ⟨∅, rfl, by simp [supported, crossings, linePoints]⟩
  | succ r ih =>
    obtain ⟨ts, hcard, h⟩ := ih
    obtain ⟨t, ht, hs⟩ := supported_crossings_insert h
    exact ⟨insert t ts, by rw [card_insert_of_notMem ht, hcard], hs⟩


private theorem exists_fresh_on_graph (P : Finset Point) (m b : ℝ) (S : Finset Line) :
    ∃ p ∉ P, On (.graph m b) p ∧ ∀ l ∈ S, l ≠ .graph m b → ¬On l p := by
  let point (x : ℝ) : Point := (x, m*x+b)
  let B (l : Line) : Set ℝ := {x | l ≠ .graph m b ∧ On l (point x)}
  have hf : (⋃ l ∈ (S : Set Line), B l).Finite := by
    apply finite_bad
    intro l _ x hx y hy
    by_contra hne
    have hp : point x ≠ point y := fun h => hne (congrArg Prod.fst h)
    exact hx.1 (line_eq_of_points hp hx.2 hy.2 rfl rfl)
  obtain ⟨x, hx⟩ := ((P.image Prod.fst).finite_toSet.union hf).exists_notMem
  refine ⟨point x, fun hp => hx (Or.inl (mem_image.mpr ⟨point x, hp, rfl⟩)), rfl, ?_⟩
  intro l hl hne hon
  exact hx (Or.inr (Set.mem_iUnion₂.mpr ⟨l, hl, ⟨hne, hon⟩⟩))

theorem linePoints_insert (P : Finset Point) (x : Point) (l : Line) :
    linePoints (insert x P) l =
      if On l x then insert x (linePoints P l) else linePoints P l := by
  ext p
  by_cases h : On l x <;> simp [h] <;> grind

private def pairLines (P : Finset Point) : Finset Line :=
  ((P ×ˢ P).filter (fun p => p.1 ≠ p.2)).image (fun p => join p.1 p.2)

private theorem mem_pairLines_iff {P : Finset Point} {l : Line} :
    l ∈ pairLines P ↔ 2 ≤ (linePoints P l).card := by
  rw [show 2 ≤ (linePoints P l).card ↔ 1 < (linePoints P l).card by omega, one_lt_card]
  constructor
  · intro h
    obtain ⟨⟨p,q⟩, hpq, rfl⟩ := mem_image.mp h
    obtain ⟨hp, hn⟩ := mem_filter.mp hpq
    obtain ⟨hp, hq⟩ := mem_product.mp hp
    exact ⟨p, mem_linePoints.mpr ⟨hp, on_join_left p q⟩,
      q, mem_linePoints.mpr ⟨hq, on_join_right p q⟩, hn⟩
  · rintro ⟨p, hp, q, hq, hpq⟩
    simp only [mem_linePoints] at hp hq
    exact mem_image.mpr ⟨(p,q), mem_filter.mpr ⟨mem_product.mpr ⟨hp.1,hq.1⟩, hpq⟩,
      line_eq_of_points hpq (on_join_left p q) (on_join_right p q) hp.2 hq.2⟩

private theorem exists_add_to_carrier (ts : Finset ℝ) (P : Finset Point) (a : ℝ)
    (ha : a ∈ ts) (hP : supported ts P) :
    ∃ Q : Finset Point, Q.card = P.card + 1 ∧ supported ts Q ∧
      ∀ b ∈ ts, (linePoints Q (carrier b)).card =
        (linePoints P (carrier b)).card + if b = a then 1 else 0 := by
  obtain ⟨p, hp, hon, havoid⟩ :=
    exists_fresh_on_graph P a (-a^2) (pairLines P ∪ ts.image carrier)
  change On (carrier a) p at hon
  refine ⟨insert p P, card_insert_of_notMem hp, ?_, ?_⟩
  · intro l hl
    by_cases hla : l = carrier a
    · exact ⟨a, ha, hla⟩
    rw [linePoints_insert] at hl
    by_cases h : On l p
    · rw [if_pos h] at hl
      have hle := card_insert_le p (linePoints P l)
      have hcard : 2 ≤ (linePoints P l).card := by omega
      exact (havoid l (mem_union_left _ (mem_pairLines_iff.mpr hcard)) hla h).elim
    · exact hP l (by simpa [h] using hl)
  · intro b hb
    rw [linePoints_insert]
    by_cases hba : b = a
    · subst b
      rw [if_pos hon, if_pos rfl, card_insert_of_notMem (fun h => hp (mem_linePoints.mp h).1)]
    · have h := havoid (carrier b) (mem_union_right _ (mem_image.mpr ⟨b,hb,rfl⟩))
        (fun he => hba (carrier_injective he))
      simp [h, hba]

private theorem exists_add_off_pairs (P : Finset Point) :
    ∃ Q : Finset Point, Q.card = P.card + 1 ∧
      (2 ∈ profile P → profile Q = profile P) := by
  obtain ⟨b,hb⟩ := (P.image Prod.snd).exists_notMem
  obtain ⟨p, hp, _, havoid⟩ := exists_fresh_on_graph P 0 b (pairLines P)
  have hguide : (linePoints P (.graph 0 b)) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨hq, hqOn⟩ := mem_linePoints.mp hq
    exact hb (mem_image.mpr ⟨q, hq, by simpa [On] using hqOn⟩)
  have hoff (l : Line) (hl : 2 ≤ (linePoints P l).card) : ¬ On l p := by
    apply havoid l (mem_pairLines_iff.mpr hl)
    intro he
    rw [he, hguide, card_empty] at hl
    omega
  refine ⟨insert p P, card_insert_of_notMem hp, ?_⟩
  intro htwo
  ext s
  change (2 ≤ s ∧ ∃ l : Line, (linePoints (insert p P) l).card = s) ↔
    (2 ≤ s ∧ ∃ l : Line, (linePoints P l).card = s)
  constructor
  · rintro ⟨hs, l, hl⟩
    by_cases hlp : On l p
    · have hcard : (linePoints P l).card < 2 := by
        by_contra he
        exact hoff l (by omega) hlp
      rw [linePoints_insert, if_pos hlp] at hl
      have hle := card_insert_le (s := linePoints P l) p
      have he : s = 2 := by omega
      rw [he]
      exact htwo
    · exact ⟨hs, l, by simpa [linePoints_insert, hlp] using hl⟩
  · rintro ⟨hs,l,hl⟩
    exact ⟨hs,l,by simp [linePoints_insert, hoff l (hl.symm ▸ hs), hl]⟩

theorem exists_padding (P : Finset Point) (h : 2 ∈ profile P) (m : ℕ) :
    ∃ Q : Finset Point, Q.card = P.card + m ∧ profile Q = profile P := by
  induction m with
  | zero => exact ⟨P, by simp, rfl⟩
  | succ m ih =>
    obtain ⟨Q, hQ, hprof⟩ := ih
    obtain ⟨R, hR, he⟩ := exists_add_off_pairs Q
    exact ⟨R, by omega, (he (hprof.symm ▸ h)).trans hprof⟩


private def edges {r : ℕ} (s : Fin r → ℕ) : Finset (Fin r × Fin r) :=
  univ.filter (fun ij => ij.1 < ij.2 ∧ r < ij.2.val + 1 + s ij.1)

private def outgoing {r : ℕ} (s : Fin r → ℕ) (i : Fin r) : Finset (Fin r) :=
  univ.filter (fun j => i < j ∧ r < j.val + 1 + s i)

private def incoming {r : ℕ} (s : Fin r → ℕ) (i : Fin r) : Finset (Fin r) :=
  univ.filter (fun j => j < i ∧ r < i.val + 1 + s j)

private theorem card_outgoing {r : ℕ} (s : Fin r → ℕ) (hmin : ∀ i, 3 ≤ s i)
    (i : Fin r) : (outgoing s i).card = min (s i) (r - (i.val+1)) := by
  have hi := i.isLt
  by_cases h : i.val+1 < r
  · let j : Fin r := ⟨max (i.val+1) (r - s i), by have := hmin i; omega⟩
    have he : outgoing s i = Ici j := by
      ext k
      simp only [outgoing, mem_filter, mem_univ, true_and, mem_Ici, ← Fin.val_fin_le,
        ← Fin.val_fin_lt]
      dsimp [j]
      omega
    rw [he, Fin.card_Ici]
    dsimp [j]
    omega
  · have he : outgoing s i = ∅ := by
      ext j
      simp only [outgoing, mem_filter, mem_univ, true_and, notMem_empty, iff_false,
        ← Fin.val_fin_lt]
      have hj := j.isLt
      omega
    rw [he, card_empty]
    omega

private theorem card_incoming_le {r : ℕ} {s : Fin r → ℕ} (hs : StrictMono s)
    (i : Fin r) : (incoming s i).card ≤ s i - (r-(i.val+1)) - 1 := by
  rw [← Nat.card_Ioo]
  apply card_le_card_of_injOn s
  · intro j hj
    change j ∈ incoming s i at hj
    change s j ∈ Ioo (r-(i.val+1)) (s i)
    simp only [incoming, mem_filter, mem_univ, true_and, mem_Ioo] at hj ⊢
    have hlt := hs hj.1
    omega
  · exact hs.injective.injOn

private def incident {r : ℕ} (s : Fin r → ℕ) (i : Fin r) : Finset (Fin r × Fin r) :=
  (edges s).filter (fun e => e.1 = i ∨ e.2 = i)

private theorem card_incident {r : ℕ} (s : Fin r → ℕ) (i : Fin r) :
    (incident s i).card = (outgoing s i).card + (incoming s i).card := by
  let left : Fin r ↪ Fin r × Fin r := ⟨fun j => (i,j), fun _ _ h => congrArg Prod.snd h⟩
  let right : Fin r ↪ Fin r × Fin r := ⟨fun j => (j,i), fun _ _ h => congrArg Prod.fst h⟩
  have he : incident s i = ((outgoing s i).map left) ∪ ((incoming s i).map right) := by
    ext ⟨a,b⟩
    simp only [incident, edges, outgoing, incoming, mem_filter, mem_univ, true_and,
      mem_union, mem_map, left, right, Function.Embedding.coeFn_mk, Prod.mk.injEq]
    aesop
  rw [he, card_union_of_disjoint, card_map, card_map]
  apply disjoint_left.mpr
  intro e hl hr
  obtain ⟨j,hj,he⟩ := mem_map.mp hl
  obtain ⟨k,_,hk⟩ := mem_map.mp hr
  have hj' := (mem_filter.mp hj).2.1
  have h := Prod.mk.inj (he.trans hk.symm)
  exact (ne_of_lt hj') h.2.symm

private theorem card_incident_le {r : ℕ} {s : Fin r → ℕ} (hs : StrictMono s)
    (hmin : ∀ i, 3 ≤ s i) (i : Fin r) : (incident s i).card ≤ s i := by
  rw [card_incident, card_outgoing s hmin]
  have hi := card_incoming_le hs i
  omega

private theorem sum_card_incident {r : ℕ} (s : Fin r → ℕ) :
    (∑ i : Fin r, (incident s i).card) = 2 * (edges s).card := by
  calc
    _ = ∑ i : Fin r, ∑ e ∈ edges s, (if e.1 = i ∨ e.2 = i then 1 else 0) := by
      simp only [incident, card_filter]
    _ = ∑ e ∈ edges s, ∑ i : Fin r, (if e.1 = i ∨ e.2 = i then 1 else 0) := sum_comm
    _ = _ := by
      have h (e : Fin r × Fin r) (he : e ∈ edges s) :
          (∑ i : Fin r, (if e.1 = i ∨ e.2 = i then 1 else 0)) = 2 := by
        have hn := ne_of_lt (mem_filter.mp he).2.1
        have heq (i : Fin r) :
            (if e.1 = i ∨ e.2 = i then 1 else 0) =
              (if e.1 = i then 1 else 0) + (if e.2 = i then 1 else 0) := by
          by_cases h1 : e.1 = i <;> by_cases h2 : e.2 = i <;> simp_all
        simp [heq, sum_add_distrib]
      simp [sum_congr rfl h, Nat.mul_comm]

private theorem card_edges {r : ℕ} (s : Fin r → ℕ) :
    (edges s).card = ∑ i : Fin r, (outgoing s i).card := by
  let row (i : Fin r) : Finset (Fin r × Fin r) :=
    (outgoing s i).map ⟨fun j => (i,j), fun _ _ h => congrArg Prod.snd h⟩
  have he : edges s = (univ : Finset (Fin r)).biUnion row := by
    ext ⟨a,b⟩
    simp [edges, row, outgoing, Function.Embedding.coeFn_mk]
  have hd : ((univ : Finset (Fin r)) : Set (Fin r)).PairwiseDisjoint row := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro e he hf
    obtain ⟨a, _, ha⟩ := mem_map.mp he
    obtain ⟨b, _, hb⟩ := mem_map.mp hf
    exact hij (congrArg Prod.fst (ha.trans hb.symm))
  rw [he, card_biUnion hd]
  simp [row]

private theorem cross_inj_on_edges {r : ℕ} {t : Fin r → ℝ} (ht : Function.Injective t)
    (s : Fin r → ℕ) :
    Set.InjOn (fun e : Fin r × Fin r => cross (t e.1) (t e.2)) (edges s : Set _) := by
  intro a ha b hb he
  change cross (t a.1) (t a.2) = cross (t b.1) (t b.2) at he
  have hal := (mem_filter.mp ha).2.1
  have hbl := (mem_filter.mp hb).2.1
  have h1 := (on_cross_iff (t b.1) (t b.2) (t a.1)).mp
    (he ▸ (on_cross_iff (t a.1) (t a.2) (t a.1)).mpr (Or.inl rfl))
  have h2 := (on_cross_iff (t b.1) (t b.2) (t a.2)).mp
    (he ▸ (on_cross_iff (t a.1) (t a.2) (t a.2)).mpr (Or.inr rfl))
  rcases h1.imp (fun h => ht h) (fun h => ht h) with h1 | h1 <;> rcases h2.imp (fun h => ht h) (fun h => ht h) with h2 | h2
  · exact (ne_of_lt hal (h1.trans h2.symm)).elim
  · exact Prod.ext h1 h2
  · exact (not_lt_of_ge (by rw [h1,h2]; exact le_of_lt hbl) hal).elim
  · exact (ne_of_lt hal (h1.trans h2.symm)).elim

private def initial {r : ℕ} (s : Fin r → ℕ) (t : Fin r → ℝ) : Finset Point :=
  (edges s).image (fun e => cross (t e.1) (t e.2))

private theorem card_initial_line {r : ℕ} {t : Fin r → ℝ} (ht : Function.Injective t)
    (s : Fin r → ℕ) (i : Fin r) :
    (linePoints (initial s t) (carrier (t i))).card = (incident s i).card := by
  have he : linePoints (initial s t) (carrier (t i)) =
      (incident s i).image (fun e => cross (t e.1) (t e.2)) := by
    ext p
    simp only [mem_linePoints, initial, incident, mem_image, mem_filter]
    constructor
    · rintro ⟨⟨e,he,rfl⟩,hp⟩
      have hh := ((on_cross_iff _ _ _).mp hp).imp (fun h => ht h) (fun h => ht h)
      exact ⟨e, ⟨he, hh.imp Eq.symm Eq.symm⟩, rfl⟩
    · rintro ⟨e, ⟨he, hi⟩, rfl⟩
      refine ⟨⟨e,he,rfl⟩, (on_cross_iff _ _ _).mpr ?_⟩
      exact hi.imp (fun h => congrArg t h.symm) (fun h => congrArg t h.symm)
  rw [he, card_image_iff]
  exact (cross_inj_on_edges ht s).mono (fun _ h => (mem_filter.mp h).1)


private def deficit {r : ℕ} (s : Fin r → ℕ) (t : Fin r → ℝ) (P : Finset Point) (i : Fin r) :
    ℕ := s i - (linePoints P (carrier (t i))).card

private theorem exists_fill {r : ℕ} {s : Fin r → ℕ} {t : Fin r → ℝ} (ht : Function.Injective t)
    {ts : Finset ℝ} (hmem : ∀ i, t i ∈ ts) (P : Finset Point)
    (hP : supported ts P) (hle : ∀ i, (linePoints P (carrier (t i))).card ≤ s i) :
    ∃ Q : Finset Point, supported ts Q ∧
      (∀ i, (linePoints Q (carrier (t i))).card = s i) ∧
      Q.card = P.card + ∑ i : Fin r, deficit s t P i := by
  generalize hsum : (∑ i : Fin r, deficit s t P i) = d
  induction d generalizing P with
  | zero =>
    refine ⟨P,hP,?_,by simp⟩
    intro i
    have hi : deficit s t P i ≤ ∑ j : Fin r, deficit s t P j :=
      single_le_sum (fun j _ => Nat.zero_le (deficit s t P j)) (mem_univ i)
    rw [hsum] at hi
    have := hle i
    unfold deficit at hi
    omega
  | succ d ih =>
    have hex : ∃ i, (linePoints P (carrier (t i))).card < s i := by
      by_contra! h
      simp [deficit, fun i => Nat.sub_eq_zero_of_le (h i)] at hsum
    obtain ⟨i,hi⟩ := hex
    obtain ⟨Q, hcard, hQ, hcounts⟩ := exists_add_to_carrier ts P (t i) (hmem i) hP
    have hQi (j : Fin r) : (linePoints Q (carrier (t j))).card =
        (linePoints P (carrier (t j))).card + if j = i then 1 else 0 := by
      simpa [ht.eq_iff] using hcounts (t j) (hmem j)
    have hQle (j : Fin r) : (linePoints Q (carrier (t j))).card ≤ s j := by
      by_cases h : j = i
      · subst j
        rw [hQi, if_pos rfl]
        omega
      · simpa [hQi, h] using hle j
    have hdelta (j : Fin r) : deficit s t P j = deficit s t Q j + if j = i then 1 else 0 := by
      simp only [deficit, hQi]
      split
      · rename_i h
        subst j
        omega
      · omega
    have hnew : (∑ j : Fin r, deficit s t Q j) = d := by
      have hsum' : (∑ j : Fin r, deficit s t P j) =
          (∑ j : Fin r, deficit s t Q j) + 1 := by
        simp only [hdelta, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
      omega
    obtain ⟨R,hR,hRs,hRc⟩ := ih Q hQ hQle hnew
    exact ⟨R,hR,hRs,by omega⟩

private theorem exists_private_point {r : ℕ} {t : Fin r → ℝ} (ht : Function.Injective t)
    (P : Finset Point) (i : Fin r) (hi : r-1 < (linePoints P (carrier (t i))).card) :
    ∃ p ∈ P, On (carrier (t i)) p ∧ ∀ j, On (carrier (t j)) p → j = i := by
  let C (j : Fin r) := linePoints P (carrier (t i)) ∩ linePoints P (carrier (t j))
  let U := (univ.erase i).biUnion C
  have hU : U.card ≤ r-1 := calc
    _ ≤ ∑ j ∈ univ.erase i, (C j).card := card_biUnion_le
    _ ≤ ∑ _j ∈ (univ : Finset (Fin r)).erase i, 1 := sum_le_sum (by
      intro j hj
      have hn : t i ≠ t j := fun he => (mem_erase.mp hj).1 ((ht he).symm)
      exact card_line_inter_le_one P (fun h => hn (carrier_injective h)))
    _ = _ := by simp [card_erase_of_mem (mem_univ i)]
  have hex : ∃ p ∈ linePoints P (carrier (t i)), p ∉ U := by
    by_contra! h
    have hc := card_le_card h
    omega
  obtain ⟨p,hp,hpU⟩ := hex
  obtain ⟨hpP,hpon⟩ := mem_linePoints.mp hp
  refine ⟨p,hpP,hpon,?_⟩
  intro j hpj
  by_contra hji
  exact hpU (mem_biUnion.mpr ⟨j, mem_erase.mpr ⟨hji,mem_univ _⟩,
    mem_inter.mpr ⟨hp,mem_linePoints.mpr ⟨hpP,hpj⟩⟩⟩)

theorem index_le_size {r : ℕ} {s : Fin r → ℕ} (hs : StrictMono s)
    (hmin : ∀ i, 3 ≤ s i) (i : Fin r) : i.val + 3 ≤ s i := by
  have h : (Iic i).card ≤ (Icc 3 (s i)).card := by
    apply card_le_card_of_injOn s
    · intro j hj
      exact mem_Icc.mpr ⟨hmin j, hs.monotone (mem_Iic.mp hj)⟩
    · exact hs.injective.injOn
  rw [Fin.card_Iic, Nat.card_Icc] at h
  have := hmin i
  omega

private theorem two_mem_of_supported {r : ℕ} {s : Fin r → ℕ} {t : Fin r → ℝ}
    {ts : Finset ℝ} (hr : 2 ≤ r) (hs : StrictMono s) (hmin : ∀ i, 3 ≤ s i)
    (ht : Function.Injective t) (hsurj : ∀ a ∈ ts, ∃ i, t i = a)
    {P : Finset Point} (hP : supported ts P)
    (hcounts : ∀ i, (linePoints P (carrier (t i))).card = s i) :
    2 ∈ profile P := by
  let i : Fin r := ⟨r-2,by omega⟩
  let j : Fin r := ⟨r-1,by omega⟩
  have hij : i ≠ j := by
    intro h
    have he := congrArg Fin.val h
    dsimp [i,j] at he
    omega
  have hbigI : r-1 < (linePoints P (carrier (t i))).card := by
    rw [hcounts]
    have := index_le_size hs hmin i
    dsimp [i] at this ⊢
    omega
  have hbigJ : r-1 < (linePoints P (carrier (t j))).card := by
    rw [hcounts]
    have := index_le_size hs hmin j
    dsimp [j] at this ⊢
    omega
  obtain ⟨p,hp,hpi,hu⟩ := exists_private_point ht P i hbigI
  obtain ⟨q,hq,hqj,hv⟩ := exists_private_point ht P j hbigJ
  have hpq : p ≠ q := by
    intro h
    exact hij (hu j (h.symm ▸ hqj)).symm
  let l := join p q
  have hle : 2 ≤ (linePoints P l).card := by
    have : 1 < (linePoints P l).card := one_lt_card.mpr
      ⟨p, mem_linePoints.mpr ⟨hp,on_join_left p q⟩,
       q, mem_linePoints.mpr ⟨hq,on_join_right p q⟩, hpq⟩
    omega
  refine ⟨by decide, l, le_antisymm ?_ hle⟩
  by_contra! hgt
  obtain ⟨a,ha,hl⟩ := hP l hgt
  obtain ⟨k,hk⟩ := hsurj a ha
  have hlk : l = carrier (t k) := by rw [hk,hl]
  exact hij ((hu k (hlk ▸ on_join_left p q)).symm.trans (hv k (hlk ▸ on_join_right p q)))


private theorem exists_exact {r : ℕ} {s : Fin r → ℕ} (hr : 2 ≤ r)
    (hs : StrictMono s) (hmin : ∀ i, 3 ≤ s i) :
    ∃ P : Finset Point, P.card = required s ∧ profile P = insert 2 (Set.range s) := by
  obtain ⟨ts,hcard,hcross⟩ := exists_supported_crossings r
  let e : Fin r ≃ ↥ts := (ts.equivFin.trans (finCongr hcard)).symm
  let t (i : Fin r) : ℝ := (e i).val
  have ht : Function.Injective t := fun _ _ he => e.injective (Subtype.ext he)
  have hmem (i : Fin r) : t i ∈ ts := (e i).property
  have hsurj (a : ℝ) (ha : a ∈ ts) : ∃ i, t i = a := by
    obtain ⟨i,hi⟩ := e.surjective ⟨a,ha⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  let P₀ := initial s t
  have hPsub : P₀ ⊆ crossings ts := by
    intro p hp
    obtain ⟨ij,hij,rfl⟩ := mem_image.mp hp
    exact mem_crossings.mpr ⟨t ij.1,hmem _,t ij.2,hmem _,
      fun h => (ne_of_lt (mem_filter.mp hij).2.1) (ht h),rfl⟩
  have hP₀ : supported ts P₀ := by
    intro l hl
    apply hcross l
    exact lt_of_lt_of_le hl (card_le_card fun p hp =>
      mem_linePoints.mpr ⟨hPsub (mem_linePoints.mp hp).1,(mem_linePoints.mp hp).2⟩)
  have hcount (i : Fin r) : (linePoints P₀ (carrier (t i))).card ≤ s i := by
    rw [card_initial_line ht]
    exact card_incident_le hs hmin i
  obtain ⟨P,hP,hPcounts,hPcard⟩ := exists_fill ht hmem P₀ hP₀ hcount
  have hdef : (∑ i : Fin r, deficit s t P₀ i) + 2 * (edges s).card = ∑ i : Fin r, s i := by
    rw [← sum_card_incident, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    have h := hcount i
    rw [deficit, card_initial_line ht] at *
    omega
  have hcount₀ : P₀.card = (edges s).card := card_image_iff.mpr (cross_inj_on_edges ht s)
  have hreq : required s + (edges s).card = ∑ i : Fin r, s i := by
    rw [required, card_edges, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [card_outgoing s hmin]
    have hi := i.isLt
    omega
  have h2 : 2 ∈ profile P := two_mem_of_supported hr hs hmin ht hsurj hP hPcounts
  refine ⟨P, by omega, ?_⟩
  ext k
  change (2 ≤ k ∧ ∃ l : Line, (linePoints P l).card = k) ↔ k = 2 ∨ k ∈ Set.range s
  constructor
  · rintro ⟨hk,l,hl⟩
    by_cases he : k = 2
    · exact Or.inl he
    · obtain ⟨a,ha,hlc⟩ := hP l (by omega)
      obtain ⟨i,hi⟩ := hsurj a ha
      refine Or.inr ⟨i,?_⟩
      rw [← hPcounts i,hi,← hlc,hl]
  · rintro (rfl | ⟨i,rfl⟩)
    · exact h2
    · exact ⟨by have := hmin i; omega,carrier (t i),hPcounts i⟩

/-- A profile with at least two sizes greater than two is realizable by exactly
`n` distinct points if and only if its required point count is at most `n`. -/
theorem realizable_iff {r n : ℕ} {sizes : Fin r → ℕ}
    (hr : 2 ≤ r) (hs : StrictMono sizes) (hmin : ∀ i, 3 ≤ sizes i) :
    (∃ P : Finset Point, P.card = n ∧ profile P = insert 2 (Set.range sizes)) ↔
      required sizes ≤ n := by
  constructor
  · rintro ⟨P,hcard,hprof⟩
    rw [← hcard]
    apply required_le_card_of_sizes hs
    intro x hx
    rw [hprof]
    exact Or.inr hx
  · intro hn
    obtain ⟨P,hcard,hprof⟩ := exists_exact hr hs hmin
    have h2 : 2 ∈ profile P := by simp [hprof]
    obtain ⟨Q,hQ,hQprof⟩ := exists_padding P h2 (n - required sizes)
    exact ⟨Q,by omega,hQprof.trans hprof⟩

end
end Erdos607
