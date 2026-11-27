import Mathlib

namespace OMA.Maxwell3

/-- monotonicity of the ratio `α^2/β^2` under a shift by `h > 0` (with `α > 0`, `|α| < |β|`,
and no sign change of `β`). -/
lemma ratio_up (α β h : ℝ) (hh : 0 < h) (hα : 0 < α) (hab : α^2 < β^2)
    (hβ : 0 < β * (β + h)) : α^2 * (β + h)^2 < (α + h)^2 * β^2 := by
  rcases lt_or_gt_of_ne (show β ≠ 0 by rintro rfl; simp at hβ) with hb | hb
  · have hb' : β + h < 0 := by nlinarith
    have h1 : α < -β := by nlinarith
    have k : α * (-(β + h)) < (α + h) * (-β) := by nlinarith
    have k0 : 0 ≤ α * (-(β + h)) := by nlinarith
    nlinarith
  · have h1 : α < β := by nlinarith
    have k : α * (β + h) < (α + h) * β := by nlinarith
    have k0 : 0 ≤ α * (β + h) := by nlinarith
    nlinarith

lemma key_pos (α β γ h : ℝ) (hh : 0 < h) (hα : 0 < α)
    (hβ : 0 < β * (β + h)) (hγ : 0 < γ * (γ + h))
    (e1 : 1 / α^2 = 1 / β^2 + 1 / γ^2)
    (e2 : 1 / (α + h)^2 = 1 / (β + h)^2 + 1 / (γ + h)^2) : False := by
  have hb0 : β ≠ 0 := by rintro rfl; simp at hβ
  have hc0 : γ ≠ 0 := by rintro rfl; simp at hγ
  have hbh : β + h ≠ 0 := by intro h0; rw [h0] at hβ; simp at hβ
  have hch : γ + h ≠ 0 := by intro h0; rw [h0] at hγ; simp at hγ
  have ha0 : α ≠ 0 := hα.ne'
  have hah : α + h ≠ 0 := by linarith
  have pa : 0 < α^2 := by positivity
  have pb : 0 < β^2 := by positivity
  have pc : 0 < γ^2 := by positivity
  have pbh : 0 < (β+h)^2 := by positivity
  have pch : 0 < (γ+h)^2 := by positivity
  have pah : 0 < (α+h)^2 := by positivity
  -- clear denominators
  have f1 : β^2 * γ^2 = α^2 * γ^2 + α^2 * β^2 := by
    field_simp at e1; linarith
  have f2 : (β+h)^2 * (γ+h)^2 = (α+h)^2 * (γ+h)^2 + (α+h)^2 * (β+h)^2 := by
    field_simp at e2; linarith
  have hab : α^2 < β^2 := by nlinarith
  have hac : α^2 < γ^2 := by nlinarith
  have rb := ratio_up α β h hh hα hab hβ
  have rc := ratio_up α γ h hh hα hac hγ
  -- divide: α²/β² + α²/γ² = 1 and (α+h)²/(β+h)² + (α+h)²/(γ+h)² = 1
  have g1 : α^2 / β^2 + α^2 / γ^2 = 1 := by
    field_simp; linarith
  have g2 : (α+h)^2 / (β+h)^2 + (α+h)^2 / (γ+h)^2 = 1 := by
    field_simp; linarith
  have i1 : α^2 / β^2 < (α+h)^2 / (β+h)^2 := by
    rw [div_lt_div_iff₀ pb pbh]; linarith
  have i2 : α^2 / γ^2 < (α+h)^2 / (γ+h)^2 := by
    rw [div_lt_div_iff₀ pc pch]; linarith
  linarith

lemma key (α β γ h : ℝ) (hh : 0 < h) (hα : 0 < α * (α + h))
    (hβ : 0 < β * (β + h)) (hγ : 0 < γ * (γ + h))
    (e1 : 1 / α^2 = 1 / β^2 + 1 / γ^2)
    (e2 : 1 / (α + h)^2 = 1 / (β + h)^2 + 1 / (γ + h)^2) : False := by
  rcases lt_or_gt_of_ne (show α ≠ 0 by rintro rfl; simp at hα) with ha | ha
  · -- reflect
    have hah : α + h < 0 := by nlinarith
    apply key_pos (-(α+h)) (-(β+h)) (-(γ+h)) h hh (by linarith)
      (by nlinarith) (by nlinarith)
    · rw [neg_sq, neg_sq, neg_sq]; exact e2
    · have h1 : -(α+h) + h = -α := by ring
      have h2 : -(β+h) + h = -β := by ring
      have h3 : -(γ+h) + h = -γ := by ring
      rw [h1, h2, h3, neg_sq, neg_sq, neg_sq]; exact e1
  · exact key_pos α β γ h hh ha hβ hγ e1 e2

/-- Inside one cell: two distinct roots in the same cell are impossible. -/
lemma cell (k δ : Fin 3 → ℝ) (h : ℝ) (hh : 0 < h) (hδ : ∀ j, 0 < δ j * (δ j + h))
    (m : ℝ) (hm : 0 < m) (hk : ∀ j, k j = m ∨ k j = -m)
    (e1 : ∑ j, k j / (δ j)^2 = 0) (e2 : ∑ j, k j / (δ j + h)^2 = 0) : False := by
  simp only [Fin.sum_univ_three] at e1 e2
  have p (j : Fin 3) : 0 < (δ j)^2 := by
    have : δ j ≠ 0 := by intro h0; have := hδ j; rw [h0] at this; simp at this
    positivity
  have p' (j : Fin 3) : 0 < (δ j + h)^2 := by
    have : δ j + h ≠ 0 := by intro h0; have := hδ j; rw [h0] at this; simp at this
    positivity
  have hm0 : m ≠ 0 := hm.ne'
  have d1 (x : ℝ) : m / x = m * (1 / x) := by ring
  have d2 (x : ℝ) : -m / x = -(m * (1 / x)) := by ring
  rcases hk 0 with h0 | h0 <;> rcases hk 1 with h1 | h1 <;> rcases hk 2 with h2 | h2 <;>
    rw [h0, h1, h2] at e1 e2 <;> simp only [d1, d2] at e1 e2
  · have := p 0; have := p 1; have := p 2
    have : 0 < 1 / (δ 0)^2 := by positivity
    have : 0 < 1 / (δ 1)^2 := by positivity
    have : 0 < 1 / (δ 2)^2 := by positivity
    nlinarith
  · exact key (δ 2) (δ 0) (δ 1) h hh (hδ 2) (hδ 0) (hδ 1)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / δ 2 ^ 2) = m * (1 / δ 0 ^ 2 + 1 / δ 1 ^ 2) by linarith); exact this)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / (δ 2 + h) ^ 2) = m * (1 / (δ 0 + h) ^ 2 + 1 / (δ 1 + h) ^ 2) by linarith); exact this)
  · exact key (δ 1) (δ 0) (δ 2) h hh (hδ 1) (hδ 0) (hδ 2)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / δ 1 ^ 2) = m * (1 / δ 0 ^ 2 + 1 / δ 2 ^ 2) by linarith); exact this)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / (δ 1 + h) ^ 2) = m * (1 / (δ 0 + h) ^ 2 + 1 / (δ 2 + h) ^ 2) by linarith); exact this)
  · exact key (δ 0) (δ 1) (δ 2) h hh (hδ 0) (hδ 1) (hδ 2)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / δ 0 ^ 2) = m * (1 / δ 1 ^ 2 + 1 / δ 2 ^ 2) by linarith); exact this)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / (δ 0 + h) ^ 2) = m * (1 / (δ 1 + h) ^ 2 + 1 / (δ 2 + h) ^ 2) by linarith); exact this)
  · exact key (δ 0) (δ 1) (δ 2) h hh (hδ 0) (hδ 1) (hδ 2)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / δ 0 ^ 2) = m * (1 / δ 1 ^ 2 + 1 / δ 2 ^ 2) by linarith); exact this)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / (δ 0 + h) ^ 2) = m * (1 / (δ 1 + h) ^ 2 + 1 / (δ 2 + h) ^ 2) by linarith); exact this)
  · exact key (δ 1) (δ 0) (δ 2) h hh (hδ 1) (hδ 0) (hδ 2)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / δ 1 ^ 2) = m * (1 / δ 0 ^ 2 + 1 / δ 2 ^ 2) by linarith); exact this)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / (δ 1 + h) ^ 2) = m * (1 / (δ 0 + h) ^ 2 + 1 / (δ 2 + h) ^ 2) by linarith); exact this)
  · exact key (δ 2) (δ 0) (δ 1) h hh (hδ 2) (hδ 0) (hδ 1)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / δ 2 ^ 2) = m * (1 / δ 0 ^ 2 + 1 / δ 1 ^ 2) by linarith); exact this)
      (by have := mul_left_cancel₀ hm0 (show m * (1 / (δ 2 + h) ^ 2) = m * (1 / (δ 0 + h) ^ 2 + 1 / (δ 1 + h) ^ 2) by linarith); exact this)
  · have := p 0; have := p 1; have := p 2
    have : 0 < 1 / (δ 0)^2 := by positivity
    have : 0 < 1 / (δ 1)^2 := by positivity
    have : 0 < 1 / (δ 2)^2 := by positivity
    nlinarith


lemma term_eq (q δ : ℝ) (hδ : δ ≠ 0) :
    q / |δ|^3 * δ = (q * (if 0 < δ then 1 else -1)) / δ^2 := by
  rcases lt_or_gt_of_ne hδ with h | h
  · rw [abs_of_neg h, if_neg (not_lt.mpr h.le)]
    field_simp
  · rw [abs_of_pos h, if_pos h]
    field_simp

/-- **Lemma L**: for three charges of equal magnitude on a line, the scalar field equation has
at most one root in each of the four cells, hence at most four roots. -/
lemma oneD_count (r q : Fin 3 → ℝ) (hq : ∀ j, q j ≠ 0) (hq' : ∀ i j, |q i| = |q j|) :
    {s : ℝ | (∀ j, s ≠ r j) ∧ ∑ j, q j / |s - r j|^3 * (s - r j) = 0}.encard ≤ 4 := by
  set S := {s : ℝ | (∀ j, s ≠ r j) ∧ ∑ j, q j / |s - r j|^3 * (s - r j) = 0}
  let φ : ℝ → ℕ := fun s => (Finset.univ.filter (fun j => r j < s)).card
  have hmaps : Set.MapsTo φ S ((Finset.range 4 : Finset ℕ) : Set ℕ) := by
    intro s _
    simp only [Finset.coe_range, Set.mem_Iio, φ]
    have := Finset.card_filter_le (Finset.univ : Finset (Fin 3)) (fun j => r j < s)
    simp at this
    omega
  -- main step: two roots with s < s' and equal φ are impossible
  have hcell : ∀ s ∈ S, ∀ s' ∈ S, s < s' → φ s = φ s' → False := by
    intro s hs s' hs' hlt heq
    have hsub : Finset.univ.filter (fun j => r j < s) ⊆ Finset.univ.filter (fun j => r j < s') := by
      intro j; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; intro h; linarith
    have hEq := Finset.eq_of_subset_of_card_le hsub (le_of_eq heq.symm)
    have hiff (j : Fin 3) : r j < s ↔ r j < s' := by
      constructor
      · intro h; linarith
      · intro h
        have : j ∈ Finset.univ.filter (fun j => r j < s') := by simp [h]
        rw [← hEq] at this; simpa using this
    have hd (j : Fin 3) : s - r j ≠ 0 := sub_ne_zero.mpr (hs.1 j)
    have hd' (j : Fin 3) : s' - r j ≠ 0 := sub_ne_zero.mpr (hs'.1 j)
    have hsg (j : Fin 3) : (0 < s - r j) ↔ (0 < s' - r j) := by
      rw [sub_pos, sub_pos]; exact hiff j
    apply cell (fun j => q j * (if 0 < s - r j then 1 else -1)) (fun j => s - r j) (s' - s)
      (by linarith) (m := |q 0|) (hm := abs_pos.mpr (hq 0))
    · intro j
      have e : s - r j + (s' - s) = s' - r j := by ring
      rw [e]
      rcases lt_or_gt_of_ne (hd j) with h | h
      · have h' : s' - r j < 0 := by
          rcases lt_or_gt_of_ne (hd' j) with h2 | h2
          · exact h2
          · exact absurd ((hsg j).mpr h2) (not_lt.mpr h.le)
        nlinarith
      · have h' : 0 < s' - r j := (hsg j).mp h
        nlinarith
    · intro j
      have hqj := hq' j 0
      rcases (abs_eq (abs_nonneg _)).mp hqj with h | h <;> split_ifs <;> simp [h]
    · refine Eq.trans ?_ hs.2
      apply Finset.sum_congr rfl
      intro j _
      rw [term_eq _ _ (hd j)]
    · refine Eq.trans ?_ hs'.2
      apply Finset.sum_congr rfl
      intro j _
      have e : s - r j + (s' - s) = s' - r j := by ring
      rw [e, term_eq _ _ (hd' j)]
      by_cases h : 0 < s - r j
      · simp [h, (hsg j).mp h]
      · simp [h, mt (hsg j).mpr h]
  have hinj : Set.InjOn φ S := by
    intro s hs s' hs' heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hcell s hs s' hs' h heq
    · exact hcell s' hs' s hs h heq.symm
  calc S.encard ≤ ((Finset.range 4 : Finset ℕ) : Set ℕ).encard :=
        Set.encard_le_encard_of_injOn hmaps hinj
    _ = 4 := by rw [Set.encard_coe_eq_coe_finsetCard]; simp

end OMA.Maxwell3
