import A401948Lean.Main
import Mathlib.Data.Finset.Max

/-! An ordinary line for a finite noncollinear configuration. -/

namespace Erdos607

open Finset

noncomputable section
open Classical

private def det (a b p : Point) : ℝ :=
  (b.1-a.1)*(p.2-a.2) - (b.2-a.2)*(p.1-a.1)

private def lengthSq (a b : Point) : ℝ := (b.1-a.1)^2 + (b.2-a.2)^2

private def distanceSq (a b p : Point) : ℝ := det a b p ^ 2 / lengthSq a b

private def along (a b : Point) (t : ℝ) : Point :=
  (a.1+t*(b.1-a.1), a.2+t*(b.2-a.2))

private theorem lengthSq_pos {a b : Point} (h : a ≠ b) : 0 < lengthSq a b := by
  by_cases hx : a.1 = b.1
  · have hy : b.2-a.2 ≠ 0 := sub_ne_zero.mpr (fun h' => h (Prod.ext hx h'.symm))
    unfold lengthSq
    positivity
  · have hx' : b.1-a.1 ≠ 0 := sub_ne_zero.mpr (fun he => hx he.symm)
    unfold lengthSq
    positivity

private theorem det_ne_imp_ne {a b p : Point} (h : det a b p ≠ 0) : a ≠ b := by
  rintro rfl
  exact h (by simp [det])

private theorem along_of_det_zero {a b x : Point} (hab : a ≠ b) (h : det a b x = 0) :
    ∃ t, along a b t = x := by
  by_cases hx : b.1 = a.1
  · have hy : b.2-a.2 ≠ 0 :=
      sub_ne_zero.mpr (fun he => hab (Prod.ext hx.symm he.symm))
    let t := (x.2-a.2)/(b.2-a.2)
    have ht : t*(b.2-a.2) = x.2-a.2 := div_mul_cancel₀ _ hy
    have hz : (b.2-a.2)*(x.1-a.1) = 0 := by simpa [det, hx] using h
    have hxa := sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hy)
    exact ⟨t, Prod.ext (by simp [along, hx, hxa]) (by dsimp [along]; linarith)⟩
  · let t := (x.1-a.1)/(b.1-a.1)
    have ht : t*(b.1-a.1) = x.1-a.1 := div_mul_cancel₀ _ (sub_ne_zero.mpr hx)
    have hxy : (b.1-a.1)*(x.2-a.2 - t*(b.2-a.2)) = 0 := by
      calc
        _ = (b.1-a.1)*(x.2-a.2) - (b.2-a.2)*(t*(b.1-a.1)) := by ring
        _ = det a b x := by rw [ht]; rfl
        _ = 0 := h
    have hya := sub_eq_zero.mp ((mul_eq_zero.mp hxy).resolve_left (sub_ne_zero.mpr hx))
    exact ⟨t, Prod.ext (by dsimp [along]; linarith) (by dsimp [along]; linarith)⟩

private theorem det_zero_on_line {l : Line} {a b p : Point}
    (ha : On l a) (hb : On l b) (hp : On l p) : det a b p = 0 := by
  cases l <;> simp only [On] at ha hb hp
  · simp [det, ha, hb, hp]
  · rw [det, ha, hb, hp]
    ring

private theorem det_eq_zero_iff {l : Line} {a b p : Point} (h : a ≠ b)
    (ha : On l a) (hb : On l b) : det a b p = 0 ↔ On l p := by
  refine ⟨fun he => ?_, det_zero_on_line ha hb⟩
  obtain ⟨t,rfl⟩ := along_of_det_zero h he
  cases l <;> simp only [On] at ha hb ⊢
  · simp [along, ha, hb]
  · simp only [along]
    rw [ha,hb]
    ring

private def dotAlong (a b q p : Point) : ℝ :=
  (b.1-a.1)*(q.1-p.1) + (b.2-a.2)*(q.2-p.2)

private theorem closer (a b p : Point) (hd : det a b p ≠ 0) (x y : ℝ)
    (hxy : x ≠ y) (hside : 0 ≤ (y-x)*dotAlong a b (along a b x) p) :
    det p (along a b y) (along a b x) ≠ 0 ∧
      distanceSq p (along a b y) (along a b x) < distanceSq a b p := by
  have hdet : det p (along a b y) (along a b x) = (x-y)*det a b p := by
    simp only [det,along]
    ring
  have hn : det p (along a b y) (along a b x) ≠ 0 := by
    rw [hdet]
    exact mul_ne_zero (sub_ne_zero.mpr hxy) hd
  have hbx : p ≠ along a b x := by
    intro he
    apply hd
    rw [he]
    simp only [det,along]
    ring
  have hlen : lengthSq p (along a b y) =
      (x-y)^2 * lengthSq a b + lengthSq p (along a b x) +
        2*((y-x)*dotAlong a b (along a b x) p) := by
    simp only [lengthSq, dotAlong, along]
    ring
  refine ⟨hn, ?_⟩
  unfold distanceSq
  rw [hdet, mul_pow, div_lt_div_iff₀ (lengthSq_pos (det_ne_imp_ne hn))
    (lengthSq_pos (det_ne_imp_ne hd))]
  rw [hlen]
  have hp := lengthSq_pos hbx
  have hd' : 0 < det a b p ^ 2 := by positivity
  have hadd : 0 < lengthSq p (along a b x) + 2*((y-x)*dotAlong a b (along a b x) p) := by
    linarith
  have hprod := mul_pos hd' hadd
  linarith only [hprod]

private theorem ordered_three {x y z : ℝ} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ u v w, u < v ∧ v < w ∧ u ∈ ({x,y,z} : Finset ℝ) ∧
      v ∈ ({x,y,z} : Finset ℝ) ∧ w ∈ ({x,y,z} : Finset ℝ) := by
  rcases lt_or_gt_of_ne hxy with h | h <;> rcases lt_or_gt_of_ne hxz with hx | hx <;>
    rcases lt_or_gt_of_ne hyz with hy | hy
  · exact ⟨x,y,z,h,hy,by simp,by simp,by simp⟩
  · exact ⟨x,z,y,hx,hy,by simp,by simp,by simp⟩
  · exact (lt_asymm (h.trans hy) hx).elim
  · exact ⟨z,x,y,hx,h,by simp,by simp,by simp⟩
  · exact ⟨y,x,z,h,hx,by simp,by simp,by simp⟩
  · exact (lt_asymm (h.trans hx) hy).elim
  · exact ⟨y,z,x,hy,hx,by simp,by simp,by simp⟩
  · exact ⟨z,y,x,hy,h,by simp,by simp,by simp⟩

/-- A finite set with a noncollinear triple determines a line through exactly two of its points. -/
private theorem ordinary_line {P : Finset Point}
    (hP : ∃ a ∈ P, ∃ b ∈ P, ∃ p ∈ P, det a b p ≠ 0) :
    2 ∈ profile P := by
  let triples := (P ×ˢ (P ×ˢ P)).filter (fun t => det t.1 t.2.1 t.2.2 ≠ 0)
  have hnonempty : triples.Nonempty := by
    obtain ⟨a,ha,b,hb,p,hp,hd⟩ := hP
    exact ⟨(a,b,p),mem_filter.mpr ⟨mem_product.mpr ⟨ha,mem_product.mpr ⟨hb,hp⟩⟩,hd⟩⟩
  obtain ⟨⟨a,b,p⟩,ht,hmin⟩ :=
    exists_min_image triples (fun t => distanceSq t.1 t.2.1 t.2.2) hnonempty
  obtain ⟨ht,hd⟩ := mem_filter.mp ht
  obtain ⟨ha,hb,hp⟩ := by simpa only [mem_product] using ht
  have hab := det_ne_imp_ne hd
  obtain ⟨l,hal,hbl⟩ := exists_line a b
  have hlower : 2 ≤ (linePoints P l).card := by
    have := one_lt_card.mpr
      ⟨a,mem_linePoints.mpr ⟨ha,hal⟩,b,mem_linePoints.mpr ⟨hb,hbl⟩,hab⟩
    omega
  refine ⟨le_rfl,l,le_antisymm ?_ hlower⟩
  by_contra! h
  obtain ⟨q,hq,r,hr,s,hs,hqr,hqs,hrs⟩ := two_lt_card.mp h
  simp only [mem_linePoints] at hq hr hs
  obtain ⟨x,hx⟩ := along_of_det_zero hab (det_zero_on_line hal hbl hq.2)
  obtain ⟨y,hy⟩ := along_of_det_zero hab (det_zero_on_line hal hbl hr.2)
  obtain ⟨z,hz⟩ := along_of_det_zero hab (det_zero_on_line hal hbl hs.2)
  have hxy : x ≠ y := fun he => hqr (by rw [← hx,← hy,he])
  have hxz : x ≠ z := fun he => hqs (by rw [← hx,← hz,he])
  have hyz : y ≠ z := fun he => hrs (by rw [← hy,← hz,he])
  obtain ⟨u,v,w,huv,hvw,hu,hv,hw⟩ := ordered_three hxy hxz hyz
  have hin (i : ℝ) (hi : i ∈ ({x,y,z} : Finset ℝ)) : along a b i ∈ P := by
    simp only [mem_insert,mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rw [hx]; exact hq.1
    · rw [hy]; exact hr.1
    · rw [hz]; exact hs.1
  let d := dotAlong a b (along a b v) p
  have bad (j : ℝ) (hj : j ∈ ({x,y,z} : Finset ℝ)) (hn : v ≠ j)
      (hpos : 0 ≤ (j-v)*d) : False := by
    obtain ⟨hne,hlt⟩ := closer a b p hd v j hn hpos
    apply not_lt_of_ge (hmin (p,along a b j,along a b v) ?_) hlt
    exact mem_filter.mpr ⟨mem_product.mpr ⟨hp,mem_product.mpr ⟨hin j hj,hin v hv⟩⟩,hne⟩
  by_cases hd0 : 0 ≤ d
  · exact bad w hw hvw.ne (mul_nonneg (sub_nonneg.mpr hvw.le) hd0)
  · exact bad u hu huv.ne.symm (mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr huv.le) (le_of_not_ge hd0))

/-- Sylvester–Gallai for the line and point model of this project. -/
theorem two_mem_profile_of_noncollinear {P : Finset Point} (hcard : 2 ≤ P.card)
    (hn : ¬ ∃ l : Line, ∀ p ∈ P, On l p) : 2 ∈ profile P := by
  obtain ⟨a,ha,b,hb,hab⟩ := one_lt_card.mp (by omega : 1 < P.card)
  obtain ⟨l,hal,hbl⟩ := exists_line a b
  apply ordinary_line
  refine ⟨a,ha,b,hb,?_⟩
  by_contra! h
  exact hn ⟨l, fun p hp => (det_eq_zero_iff hab hal hbl).mp (h p hp)⟩

end
end Erdos607
