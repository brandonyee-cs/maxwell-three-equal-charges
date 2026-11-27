import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture

/-!
# Reduction of Maxwell's conjecture for three charges of equal magnitude to the plane (Tsai 2015)

`main` proves the 3-D target from two purely planar hypotheses about the normalised triangle
with vertices (0,0), (1,0), (u,w), where w is non-zero.
* The collinear case is proved in full. Off-axis equilibria of collinear charges have a degenerate
  Hessian, and on the axis each cell between consecutive charges holds at most one equilibrium.
* For non-collinear charges every equilibrium lies in the plane of the charges.
* An orthogonal frame (rigid motion plus scaling) carries the configuration to the normalised one.
  Equilibria correspond to zeros of the 2-D field. A 2-D Hessian kernel vector gives a 3-D Hessian
  kernel vector, so 3-D non-degeneracy yields a non-zero 2-D Hessian determinant.
* `H1` (known, Tsai 2015): three equal non-zero charges at (0,0), (1,0), (u,w), all of whose planar
  equilibria have a non-singular 2-D Hessian, have at most four planar equilibria.
* `H2` (known, Tsai 2015): the same for equal magnitudes with mixed signs (ratio 1:1:-1).
-/

open InnerProductSpace
open scoped RealInnerProductSpace Gradient

namespace OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1
open Arxiv.«2607.27197»

-- Tsai (2015), planar normalised form, equal charges.
def H1 : Prop :=
  ∀ (q : Fin 3 → ℝ) (u w : ℝ), w ≠ 0 → (∀ j, q j ≠ 0) → (∀ i j, q i = q j) →
    (∀ p : ℝ × ℝ, (∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) →
      ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 →
      ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 →
      (∑ j, q j * (2 * (p.1 - ![0, 1, u] j)^2 - (p.2 - ![0, 0, w] j)^2) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5) *
        (∑ j, q j * (2 * (p.2 - ![0, 0, w] j)^2 - (p.1 - ![0, 1, u] j)^2) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5) -
        (∑ j, q j * (3 * (p.1 - ![0, 1, u] j) * (p.2 - ![0, 0, w] j)) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5)^2 ≠ 0) →
    {p : ℝ × ℝ | (∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) ∧
      ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 ∧
      ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0}.encard ≤ 4

-- Tsai (2015), planar normalised form, equal magnitudes with mixed signs.
def H2 : Prop :=
  ∀ (q : Fin 3 → ℝ) (u w : ℝ), w ≠ 0 → (∀ j, q j ≠ 0) → (∀ i j, |q i| = |q j|) → (∃ i j, q i ≠ q j) →
    (∀ p : ℝ × ℝ, (∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) →
      ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 →
      ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 →
      (∑ j, q j * (2 * (p.1 - ![0, 1, u] j)^2 - (p.2 - ![0, 0, w] j)^2) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5) *
        (∑ j, q j * (2 * (p.2 - ![0, 0, w] j)^2 - (p.1 - ![0, 1, u] j)^2) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5) -
        (∑ j, q j * (3 * (p.1 - ![0, 1, u] j) * (p.2 - ![0, 0, w] j)) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5)^2 ≠ 0) →
    {p : ℝ × ℝ | (∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) ∧
      ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 ∧
      ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0}.encard ≤ 4


lemma charge_hasGradient (q : ℝ) (a x : (EuclideanSpace ℝ (Fin 3))) (hxa : x ≠ a) :
    HasGradientAt (fun y : (EuclideanSpace ℝ (Fin 3)) => q / dist y a) ((-q / ‖x-a‖^3) • (x-a)) x := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hs : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖^2) (2 • innerSL ℝ (x-a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  have hd : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖) (‖x-a‖⁻¹ • innerSL ℝ (x-a)) x := by
    convert! hs.sqrt (pow_ne_zero 2 hn) using 1
    · funext y; exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      field_simp
      <;> norm_num
  have hi := ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul q
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hi using 1 <;> ext v <;>
    simp [dist_eq_norm, div_eq_mul_inv, toDual_apply_apply, inner_smul_left, smul_smul]
  <;> field_simp [hn]
  <;> simp
  <;> ring

lemma potential_hasGradient (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∉ Set.range a) :
    HasGradientAt (Arxiv.«2607.27197».potential q a) (-((∑ j, (q j / ‖x - a j‖^3) • (x - a j)))) x := by
  have hn (j : Fin 3) : x ≠ a j := fun h => hx ⟨j, h.symm⟩
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hf : Arxiv.«2607.27197».potential q a = fun y => ∑ j, q j / dist y (a j) := rfl
  rw [hf]
  have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (charge_hasGradient (q j) (a j) x (hn j)).hasFDerivAt)
  have key : (toDual ℝ (EuclideanSpace ℝ (Fin 3))) (-((∑ j, (q j / ‖x - a j‖^3) • (x - a j)))) =
      ∑ i, (toDual ℝ (EuclideanSpace ℝ (Fin 3))) ((-q i / ‖x - a i‖ ^ 3) • (x - a i)) := by
    rw [← Finset.sum_neg_distrib, map_sum]
    simp only [neg_div, neg_smul]
  rw [key]
  exact this

lemma mem_equilibria_iff (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) :
    x ∈ Arxiv.«2607.27197».equilibria q a ↔ x ∉ Set.range a ∧ (∑ j, (q j / ‖x - a j‖^3) • (x - a j)) = 0 := by
  constructor
  · rintro ⟨hx, hg⟩
    refine ⟨hx, ?_⟩
    have := (potential_hasGradient q a x hx).gradient
    rw [hg] at this
    exact neg_eq_zero.mp this.symm
  · rintro ⟨hx, hg⟩
    refine ⟨hx, ?_⟩
    rw [(potential_hasGradient q a x hx).gradient, hg, neg_zero]


lemma norm_sub_hasFDerivAt (a x : (EuclideanSpace ℝ (Fin 3))) (hxa : x ≠ a) :
    HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖) (‖x-a‖⁻¹ • innerSL ℝ (x-a)) x := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hs : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖^2) (2 • innerSL ℝ (x-a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  convert! hs.sqrt (pow_ne_zero 2 hn) using 1
  · funext y; exact (Real.sqrt_sq (norm_nonneg _)).symm
  · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
    norm_num

/-- the coefficient `q / ‖y - a‖^3` has a derivative that kills every vector orthogonal to `x - a`. -/
lemma coeff_hasFDerivAt (q : ℝ) (a x : (EuclideanSpace ℝ (Fin 3))) (hxa : x ≠ a) :
    ∃ C : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ, HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => q / ‖y-a‖^3) C x ∧
      ∀ u : (EuclideanSpace ℝ (Fin 3)), ⟪x - a, u⟫ = 0 → C u = 0 := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hg : DifferentiableAt ℝ (fun r : ℝ => q / r^3) ‖x-a‖ :=
    (differentiableAt_const q).div (differentiableAt_pow 3) (pow_ne_zero 3 hn)
  refine ⟨deriv (fun r : ℝ => q / r^3) ‖x-a‖ • (‖x-a‖⁻¹ • innerSL ℝ (x-a)), ?_, ?_⟩
  · have h := hg.hasDerivAt.comp_hasFDerivAt (f := fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖) x
      (norm_sub_hasFDerivAt a x hxa)
    exact h
  · intro u hu
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply, hu]
    simp

lemma field_hasFDerivAt (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∉ Set.range a) :
    ∃ D : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (EuclideanSpace ℝ (Fin 3)), HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => (∑ j, (q j / ‖y - a j‖^3) • (y - a j))) D x ∧
      ∀ u : (EuclideanSpace ℝ (Fin 3)), (∀ j, ⟪x - a j, u⟫ = 0) → D u = (∑ j, q j / ‖x - a j‖^3) • u := by
  have hn (j : Fin 3) : x ≠ a j := fun h => hx ⟨j, h.symm⟩
  choose C hC hCu using fun j => coeff_hasFDerivAt (q j) (a j) x (hn j)
  have hj (j : Fin 3) : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => (q j / ‖y - a j‖^3) • (y - a j))
      ((q j / ‖x - a j‖^3) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + (C j).smulRight (x - a j)) x :=
    (hC j).fun_smul ((hasFDerivAt_id x).sub_const (a j))
  refine ⟨∑ j, ((q j / ‖x - a j‖^3) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + (C j).smulRight (x - a j)),
    ?_, ?_⟩
  · have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hj j)
    exact this
  · intro u hu
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq,
      ContinuousLinearMap.smulRight_apply, hCu _ u (hu _), zero_smul, add_zero, Finset.sum_smul]

/-- **Lemma D**: an equilibrium at which some nonzero `u` is orthogonal to all `x - a j` while
`∑ q j / r_j^3 = 0` is degenerate. -/
lemma not_nondegenerate (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∉ Set.range a)
    (u : (EuclideanSpace ℝ (Fin 3))) (hu : u ≠ 0) (horth : ∀ j, ⟪x - a j, u⟫ = 0)
    (hsum : ∑ j, q j / ‖x - a j‖^3 = 0) :
    ¬ Arxiv.«2607.27197».HasNondegenerateHessianAt (Arxiv.«2607.27197».potential q a) x := by
  intro hnd
  obtain ⟨D, hD, hDu⟩ := field_hasFDerivAt q a x hx
  have hopen : IsOpen (Set.range a)ᶜ := (Set.finite_range a).isClosed.isOpen_compl
  have hev : fderiv ℝ (Arxiv.«2607.27197».potential q a) =ᶠ[nhds x]
      fun y => -(innerSL ℝ ((∑ j, (q j / ‖y - a j‖^3) • (y - a j)))) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [(potential_hasGradient q a y hy).hasFDerivAt.fderiv]
    ext w
    simp [toDual_apply_apply, innerSL_apply_apply, inner_neg_left]
  have hF : HasFDerivAt (fun y => -(innerSL ℝ ((∑ j, (q j / ‖y - a j‖^3) • (y - a j))))) (-((innerSL ℝ).comp D)) x :=
    (((innerSL ℝ : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ).hasFDerivAt).comp x hD).neg
  obtain ⟨w, hw⟩ := hnd u hu
  apply hw
  rw [iteratedFDeriv_two_apply, hev.fderiv_eq, hF.fderiv]
  simp [hDu u horth, hsum]




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




lemma exists_orth (d v : (EuclideanSpace ℝ (Fin 3))) : ∃ u : (EuclideanSpace ℝ (Fin 3)), u ≠ 0 ∧ ⟪d, u⟫ = 0 ∧ ⟪v, u⟫ = 0 := by
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.span ℝ (Set.range ![d, v])
  have hK : Module.finrank ℝ K ≤ 2 := by
    have := finrank_range_le_card (R := ℝ) ![d, v]
    simpa [Set.finrank] using this
  have hsum := Submodule.finrank_add_finrank_orthogonal K
  rw [finrank_euclideanSpace_fin] at hsum
  have hne : Kᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨u, hu0, ?_, ?_⟩
  · exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (show d ∈ Set.range ![d, v] from ⟨0, rfl⟩)) hu
  · exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (show v ∈ Set.range ![d, v] from ⟨1, rfl⟩)) hu

/-- Collinear charges of equal magnitude, all equilibria non-degenerate: at most four equilibria. -/
lemma collinear_case (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (ha : Function.Injective a)
    (hq : ∀ j, q j ≠ 0) (hq' : ∀ i j, |q i| = |q j|)
    (hnd : ∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x)
    (hcol : Collinear ℝ (Set.range a)) : (equilibria q a).encard ≤ 4 := by
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hcol
  choose r hr using fun j => hv (a j) ⟨j, rfl⟩
  simp only [vadd_eq_add] at hr
  have hv0 : v ≠ 0 := by
    intro h0
    have : a 0 = a 1 := by rw [hr 0, hr 1, h0]; simp
    exact absurd (ha this) (by decide)
  have hvv : ⟪v, v⟫ ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0)
  -- every equilibrium lies on the line
  have hline : ∀ x ∈ equilibria q a, x = (⟪x - p₀, v⟫ / ⟪v, v⟫) • v + p₀ := by
    intro x hx
    by_contra hoff
    have hx' := (mem_equilibria_iff q a x).mp hx
    obtain ⟨d, hd⟩ : ∃ d, d = x - p₀ := ⟨_, rfl⟩
    set c : Fin 3 → ℝ := fun j => q j / ‖x - a j‖^3
    have hxa (j : Fin 3) : x - a j = d - r j • v := by rw [hd, hr j]; abel
    have hF : (∑ j, c j) • d - (∑ j, c j * r j) • v = 0 := by
      have := hx'.2
      simp only [hxa] at this
      rw [← this, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp only [c, smul_sub, smul_smul]
      rw [hxa j]
    have hS : ∑ j, c j = 0 := by
      by_contra hS
      apply hoff
      have : d = ((∑ j, c j * r j) / ∑ j, c j) • v := by
        rw [sub_eq_zero] at hF
        rw [div_eq_inv_mul, mul_smul, ← hF, smul_smul, inv_mul_cancel₀ hS, one_smul]
      have h2 : ⟪d, v⟫ / ⟪v, v⟫ = (∑ j, c j * r j) / ∑ j, c j := by
        rw [this, real_inner_smul_left, mul_div_assoc, div_self hvv, mul_one]
      rw [← hd, h2, ← this, hd, sub_add_cancel]
    obtain ⟨u, hu0, hdu, hvu⟩ := exists_orth d v
    apply not_nondegenerate q a x hx'.1 u hu0 _ hS (hnd x hx)
    intro j
    rw [hxa, inner_sub_left, real_inner_smul_left, hdu, hvu]; ring
  -- map to the line parameter
  let g : (EuclideanSpace ℝ (Fin 3)) → ℝ := fun x => ⟪x - p₀, v⟫ / ⟪v, v⟫
  have hmaps : Set.MapsTo g (equilibria q a)
      {s : ℝ | (∀ j, s ≠ r j) ∧ ∑ j, q j / |s - r j|^3 * (s - r j) = 0} := by
    intro x hx
    have hx' := (mem_equilibria_iff q a x).mp hx
    have hxl := hline x hx
    set s := g x
    have hxa (j : Fin 3) : x - a j = (s - r j) • v := by
      rw [hr j]; conv_lhs => rw [hxl]
      rw [sub_smul]; abel
    refine ⟨fun j hj => hx'.1 ⟨j, ?_⟩, ?_⟩
    · have := hxa j; rw [hj, sub_self, zero_smul] at this; exact (sub_eq_zero.mp this).symm
    · have h0 := hx'.2
      simp only [hxa, norm_smul, Real.norm_eq_abs, smul_smul, ← Finset.sum_smul] at h0
      have h1 := (smul_eq_zero.mp h0).resolve_right hv0
      have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
      have : ∑ j, q j / |s - r j|^3 * (s - r j) = ‖v‖^3 * ∑ j, q j / (|s - r j| * ‖v‖)^3 * (s - r j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow]
        field_simp
      rw [this, h1, mul_zero]
  have hinj : Set.InjOn g (equilibria q a) := by
    intro x hx y hy hxy
    rw [hline x hx, hline y hy]
    simp only [g] at hxy
    rw [hxy]
  calc (equilibria q a).encard
      ≤ {s : ℝ | (∀ j, s ≠ r j) ∧ ∑ j, q j / |s - r j|^3 * (s - r j) = 0}.encard :=
        Set.encard_le_encard_of_injOn hmaps hinj
    _ ≤ 4 := oneD_count r q hq hq'

/-- **Lemma P**: for affinely independent charge positions every equilibrium lies in the plane of
the charges. -/
lemma equilibria_subset_affineSpan (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (hq : ∀ j, q j ≠ 0)
    (hind : AffineIndependent ℝ a) :
    equilibria q a ⊆ (affineSpan ℝ (Set.range a) : Set (EuclideanSpace ℝ (Fin 3))) := by
  intro x hx
  have hx' := (mem_equilibria_iff q a x).mp hx
  have hxa (j : Fin 3) : x - a j ≠ 0 := sub_ne_zero.mpr (fun h => hx'.1 ⟨j, h.symm⟩)
  set c : Fin 3 → ℝ := fun j => q j / ‖x - a j‖^3
  have hc (j : Fin 3) : c j ≠ 0 :=
    div_ne_zero (hq j) (pow_ne_zero 3 (norm_ne_zero_iff.mpr (hxa j)))
  have hF : (∑ j, c j) • x = ∑ j, c j • a j := by
    have := hx'.2
    rw [Finset.sum_smul, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← this]
    apply Finset.sum_congr rfl
    intro j _
    simp only [c, smul_sub]
  by_cases hS : ∑ j, c j = 0
  · exfalso
    have h0 : (Finset.univ : Finset (Fin 3)).weightedVSub a c = (0 : (EuclideanSpace ℝ (Fin 3))) := by
      rw [Finset.weightedVSub_eq_linear_combination _ hS, ← hF, hS, zero_smul]
    exact hc 0 (hind Finset.univ c hS h0 0 (Finset.mem_univ _))
  · have hw : ∑ j, c j / ∑ i, c i = 1 := by
      rw [← Finset.sum_div, div_self hS]
    have hmem := affineCombination_mem_affineSpan (k := ℝ) hw a
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at hmem
    convert hmem using 1
    have e : ∑ j, (c j / ∑ i, c i) • a j = (∑ i, c i)⁻¹ • ∑ j, c j • a j := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [div_eq_inv_mul, mul_smul]
    rw [e, ← hF, smul_smul, inv_mul_cancel₀ hS, one_smul]
    rfl




lemma coeff_hasFDerivAt' (q : ℝ) (a x : (EuclideanSpace ℝ (Fin 3))) (hxa : x ≠ a) :
    HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => q / ‖y-a‖^3)
      ((-(3*q) / ‖x-a‖^5) • innerSL ℝ (x-a)) x := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have h := (((hasDerivAt_pow 3 ‖x-a‖).inv (pow_ne_zero 3 hn)).const_mul q).comp_hasFDerivAt x
    (norm_sub_hasFDerivAt a x hxa)
  have hfun : (fun y : (EuclideanSpace ℝ (Fin 3)) => q / ‖y-a‖^3) = (fun r : ℝ => q * (r^3)⁻¹) ∘ (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖) := by
    funext y; simp [div_eq_mul_inv]
  rw [hfun]
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  field_simp
  ring

lemma field_hasFDerivAt' (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∉ Set.range a) :
    ∃ D : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (EuclideanSpace ℝ (Fin 3)), HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => (∑ j, (q j / ‖y - a j‖^3) • (y - a j))) D x ∧
      ∀ u : (EuclideanSpace ℝ (Fin 3)), D u = ∑ j, ((q j / ‖x - a j‖^3) • u +
        ((-(3 * q j) / ‖x - a j‖^5) * ⟪x - a j, u⟫) • (x - a j)) := by
  have hn (j : Fin 3) : x ≠ a j := fun h => hx ⟨j, h.symm⟩
  have hj (j : Fin 3) : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => (q j / ‖y - a j‖^3) • (y - a j))
      ((q j / ‖x - a j‖^3) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) +
        ((-(3*q j) / ‖x - a j‖^5) • innerSL ℝ (x - a j)).smulRight (x - a j)) x :=
    (coeff_hasFDerivAt' (q j) (a j) x (hn j)).fun_smul ((hasFDerivAt_id x).sub_const (a j))
  refine ⟨∑ j, ((q j / ‖x - a j‖^3) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) +
        ((-(3*q j) / ‖x - a j‖^5) • innerSL ℝ (x - a j)).smulRight (x - a j)), ?_, ?_⟩
  · exact HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hj j)
  · intro u
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_eq_mul]

/-- A nonzero kernel vector of the Hessian makes the equilibrium degenerate. -/
lemma not_nondegenerate' (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∉ Set.range a)
    (u : (EuclideanSpace ℝ (Fin 3))) (hu : u ≠ 0)
    (hker : ∑ j, ((q j / ‖x - a j‖^3) • u +
        ((-(3 * q j) / ‖x - a j‖^5) * ⟪x - a j, u⟫) • (x - a j)) = 0) :
    ¬ HasNondegenerateHessianAt (potential q a) x := by
  intro hnd
  obtain ⟨D, hD, hDu⟩ := field_hasFDerivAt' q a x hx
  have hopen : IsOpen (Set.range a)ᶜ := (Set.finite_range a).isClosed.isOpen_compl
  have hev : fderiv ℝ (potential q a) =ᶠ[nhds x]
      fun y => -(innerSL ℝ ((∑ j, (q j / ‖y - a j‖^3) • (y - a j)))) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [(potential_hasGradient q a y hy).hasFDerivAt.fderiv]
    ext w
    simp [toDual_apply_apply, innerSL_apply_apply, inner_neg_left]
  have hF : HasFDerivAt (fun y => -(innerSL ℝ ((∑ j, (q j / ‖y - a j‖^3) • (y - a j))))) (-((innerSL ℝ).comp D)) x :=
    (((innerSL ℝ : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ).hasFDerivAt).comp x hD).neg
  obtain ⟨w, hw⟩ := hnd u hu
  apply hw
  rw [iteratedFDeriv_two_apply, hev.fderiv_eq, hF.fderiv]
  simp [hDu u, hker]




section Frame
variable (f1 f2 : (EuclideanSpace ℝ (Fin 3)))

lemma frame_norm (hf : ⟪f1, f2⟫ = 0) (hn : ‖f2‖ = ‖f1‖) (α β : ℝ) :
    ‖α • f1 + β • f2‖ = ‖f1‖ * Real.sqrt (α^2 + β^2) := by
  have h2 : ‖α • f1 + β • f2‖^2 = ‖f1‖^2 * (α^2 + β^2) := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hf, hn]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [← Real.sqrt_sq (norm_nonneg _), h2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma frame_inner (hf : ⟪f1, f2⟫ = 0) (hn : ‖f2‖ = ‖f1‖) (α β γ δ : ℝ) :
    ⟪α • f1 + β • f2, γ • f1 + δ • f2⟫ = ‖f1‖^2 * (α * γ + β * δ) := by
  have hf' : ⟪f2, f1⟫ = 0 := by rw [real_inner_comm]; exact hf
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hf, hf',
    real_inner_self_eq_norm_sq, hn]
  ring

lemma frame_eq_zero (hf : ⟪f1, f2⟫ = 0) (hn : ‖f2‖ = ‖f1‖) (h1 : f1 ≠ 0) (α β : ℝ)
    (h : α • f1 + β • f2 = 0) : α = 0 ∧ β = 0 := by
  have hL : ‖f1‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h1)
  have e1 := frame_inner f1 f2 hf hn α β 1 0
  have e2 := frame_inner f1 f2 hf hn α β 0 1
  rw [h, inner_zero_left] at e1 e2
  constructor
  · have : ‖f1‖^2 * α = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hL
  · have : ‖f1‖^2 * β = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hL

end Frame

/-- An orthogonal frame adapted to a non-degenerate triangle: `a 1 = a 0 + f1`,
`a 2 = a 0 + u f1 + w f2`, with `f1 ⊥ f2`, `‖f1‖ = ‖f2‖`, `w ≠ 0`. -/
lemma exists_frame (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (hind : AffineIndependent ℝ a) :
    ∃ (f1 f2 : (EuclideanSpace ℝ (Fin 3))) (u w : ℝ), f1 ≠ 0 ∧ ⟪f1, f2⟫ = 0 ∧ ‖f2‖ = ‖f1‖ ∧ w ≠ 0 ∧
      a 1 = a 0 + f1 ∧ a 2 = a 0 + u • f1 + w • f2 := by
  set f1 := a 1 - a 0
  have hf1 : f1 ≠ 0 := sub_ne_zero.mpr (fun h => absurd (hind.injective h) (by decide))
  have hL : ‖f1‖ ≠ 0 := norm_ne_zero_iff.mpr hf1
  have hff : ⟪f1, f1⟫ ≠ 0 := by rw [real_inner_self_eq_norm_sq]; exact pow_ne_zero 2 hL
  set t := ⟪a 2 - a 0, f1⟫ / ⟪f1, f1⟫
  set g := (a 2 - a 0) - t • f1
  have hg : g ≠ 0 := by
    intro hg0
    have hsum : ∑ i, (![t - 1, -t, 1] : Fin 3 → ℝ) i = 0 := by
      simp [Fin.sum_univ_three]; ring
    have hv : (Finset.univ : Finset (Fin 3)).weightedVSub a (![t - 1, -t, 1] : Fin 3 → ℝ) = (0 : (EuclideanSpace ℝ (Fin 3))) := by
      rw [Finset.weightedVSub_eq_linear_combination _ hsum, ← hg0]
      simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, g, f1]
      module
    have := hind Finset.univ _ hsum hv 2 (Finset.mem_univ _)
    simp at this
  have hgn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  refine ⟨f1, (‖f1‖ / ‖g‖) • g, t, ‖g‖ / ‖f1‖, hf1, ?_, ?_, div_ne_zero hgn hL, by simp [f1], ?_⟩
  · rw [real_inner_smul_right]
    have : ⟪f1, g⟫ = 0 := by
      rw [show g = (a 2 - a 0) - t • f1 from rfl, inner_sub_right, real_inner_smul_right,
        real_inner_comm (a 2 - a 0) f1]
      simp only [t]
      rw [div_mul_cancel₀ _ hff, sub_self]
    rw [this, mul_zero]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
    field_simp
  · rw [smul_smul, div_mul_div_comm, mul_comm ‖g‖ ‖f1‖, div_self (mul_ne_zero hL hgn), one_smul]
    simp only [g]
    abel

section Coords
variable (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (a0 f1 f2 : (EuclideanSpace ℝ (Fin 3))) (X Y : Fin 3 → ℝ)

lemma coords_sub (ha : ∀ j, a j = a0 + X j • f1 + Y j • f2) (s t : ℝ) (j : Fin 3) :
    (a0 + s • f1 + t • f2) - a j = (s - X j) • f1 + (t - Y j) • f2 := by
  rw [ha j]; module

lemma coords_field (hf : ⟪f1, f2⟫ = 0) (hn : ‖f2‖ = ‖f1‖)
    (ha : ∀ j, a j = a0 + X j • f1 + Y j • f2) (s t : ℝ) :
    (∑ j, (q j / ‖(a0 + s • f1 + t • f2) - a j‖^3) • ((a0 + s • f1 + t • f2) - a j)) = (‖f1‖^3)⁻¹ •
      ((∑ j, q j * (s - X j) / Real.sqrt ((s - X j)^2 + (t - Y j)^2)^3) • f1 +
       (∑ j, q j * (t - Y j) / Real.sqrt ((s - X j)^2 + (t - Y j)^2)^3) • f2) := by
  simp only [coords_sub a a0 f1 f2 X Y ha, frame_norm f1 f2 hf hn, Fin.sum_univ_three]
  module

/-- the 2-D Hessian entries -/
lemma coords_kernel (hf : ⟪f1, f2⟫ = 0) (hn : ‖f2‖ = ‖f1‖) (h1 : f1 ≠ 0)
    (ha : ∀ j, a j = a0 + X j • f1 + Y j • f2) (s t : ℝ)
    (hR : ∀ j, (s - X j)^2 + (t - Y j)^2 ≠ 0) (v1 v2 : ℝ) :
    ∑ j, ((q j / ‖(a0 + s • f1 + t • f2) - a j‖^3) • (v1 • f1 + v2 • f2) +
        ((-(3 * q j) / ‖(a0 + s • f1 + t • f2) - a j‖^5) *
          ⟪(a0 + s • f1 + t • f2) - a j, v1 • f1 + v2 • f2⟫) • ((a0 + s • f1 + t • f2) - a j)) =
    (‖f1‖^3)⁻¹ •
      ((-((∑ j, q j * (2 * (s - X j)^2 - (t - Y j)^2) / Real.sqrt ((s - X j)^2 + (t - Y j)^2)^5) * v1 +
          (∑ j, q j * (3 * (s - X j) * (t - Y j)) / Real.sqrt ((s - X j)^2 + (t - Y j)^2)^5) * v2)) • f1 +
       (-((∑ j, q j * (3 * (s - X j) * (t - Y j)) / Real.sqrt ((s - X j)^2 + (t - Y j)^2)^5) * v1 +
          (∑ j, q j * (2 * (t - Y j)^2 - (s - X j)^2) / Real.sqrt ((s - X j)^2 + (t - Y j)^2)^5) * v2)) • f2) := by
  have hL : ‖f1‖ ≠ 0 := norm_ne_zero_iff.mpr h1
  -- per-term identity
  have term : ∀ (c δ1 δ2 : ℝ), δ1^2 + δ2^2 ≠ 0 →
      (c / (‖f1‖ * Real.sqrt (δ1^2 + δ2^2))^3) • (v1 • f1 + v2 • f2) +
        ((-(3 * c) / (‖f1‖ * Real.sqrt (δ1^2 + δ2^2))^5) * (‖f1‖^2 * (δ1 * v1 + δ2 * v2))) •
          (δ1 • f1 + δ2 • f2) =
      (‖f1‖^3)⁻¹ • ((-(c * (2 * δ1^2 - δ2^2) / Real.sqrt (δ1^2 + δ2^2)^5 * v1 +
          c * (3 * δ1 * δ2) / Real.sqrt (δ1^2 + δ2^2)^5 * v2)) • f1 +
        (-(c * (3 * δ1 * δ2) / Real.sqrt (δ1^2 + δ2^2)^5 * v1 +
          c * (2 * δ2^2 - δ1^2) / Real.sqrt (δ1^2 + δ2^2)^5 * v2)) • f2) := by
    intro c δ1 δ2 hd
    set R := Real.sqrt (δ1^2 + δ2^2) with hRdef
    have hR2 : R^2 = δ1^2 + δ2^2 := Real.sq_sqrt (by positivity)
    have hR0 : R ≠ 0 := by
      intro h0; apply hd; rw [← hR2, h0]; ring
    have e1 : c / (‖f1‖ * R)^3 * v1 + (-(3 * c) / (‖f1‖ * R)^5) * (‖f1‖^2 * (δ1 * v1 + δ2 * v2)) * δ1
        = (‖f1‖^3)⁻¹ * (-(c * (2 * δ1^2 - δ2^2) / R^5 * v1 + c * (3 * δ1 * δ2) / R^5 * v2)) := by
      field_simp
      linear_combination (c * v1) * hR2
    have e2 : c / (‖f1‖ * R)^3 * v2 + (-(3 * c) / (‖f1‖ * R)^5) * (‖f1‖^2 * (δ1 * v1 + δ2 * v2)) * δ2
        = (‖f1‖^3)⁻¹ * (-(c * (3 * δ1 * δ2) / R^5 * v1 + c * (2 * δ2^2 - δ1^2) / R^5 * v2)) := by
      field_simp
      linear_combination (c * v2) * hR2
    calc _ = (c / (‖f1‖ * R)^3 * v1 + (-(3 * c) / (‖f1‖ * R)^5) * (‖f1‖^2 * (δ1 * v1 + δ2 * v2)) * δ1) • f1
          + (c / (‖f1‖ * R)^3 * v2 + (-(3 * c) / (‖f1‖ * R)^5) * (‖f1‖^2 * (δ1 * v1 + δ2 * v2)) * δ2) • f2 := by
            module
      _ = _ := by rw [e1, e2]; module
  simp only [coords_sub a a0 f1 f2 X Y ha, frame_norm f1 f2 hf hn, frame_inner f1 f2 hf hn]
  rw [Fin.sum_univ_three, term _ _ _ (hR 0), term _ _ _ (hR 1), term _ _ _ (hR 2)]
  simp only [Fin.sum_univ_three]
  module

end Coords




lemma kernel2 (A B C : ℝ) (h : A * C - B^2 = 0) :
    ∃ v1 v2 : ℝ, ¬(v1 = 0 ∧ v2 = 0) ∧ A * v1 + B * v2 = 0 ∧ B * v1 + C * v2 = 0 := by
  by_cases hab : A = 0 ∧ B = 0
  · refine ⟨1, 0, by simp, ?_, ?_⟩ <;> simp [hab.1, hab.2]
  · refine ⟨B, -A, ?_, by ring, by linear_combination -h⟩
    intro h'; apply hab; exact ⟨by linarith [h'.2], h'.1⟩

lemma eq_coords (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (hq : ∀ j, q j ≠ 0)
    (hind : AffineIndependent ℝ a) (a0 f1 f2 : (EuclideanSpace ℝ (Fin 3))) (X Y : Fin 3 → ℝ)
    (ha : ∀ j, a j = a0 + X j • f1 + Y j • f2) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∈ equilibria q a) :
    ∃ s t : ℝ, x = a0 + s • f1 + t • f2 := by
  have hx' := (mem_equilibria_iff q a x).mp hx
  have hxa (j : Fin 3) : x - a j ≠ 0 := sub_ne_zero.mpr (fun h => hx'.1 ⟨j, h.symm⟩)
  set c : Fin 3 → ℝ := fun j => q j / ‖x - a j‖^3
  have hc (j : Fin 3) : c j ≠ 0 :=
    div_ne_zero (hq j) (pow_ne_zero 3 (norm_ne_zero_iff.mpr (hxa j)))
  have hF : (∑ j, c j) • x = ∑ j, c j • a j := by
    have := hx'.2
    rw [Finset.sum_smul, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← this]
    apply Finset.sum_congr rfl
    intro j _
    simp only [c, smul_sub]
  have hS : ∑ j, c j ≠ 0 := by
    intro hS
    have h0 : (Finset.univ : Finset (Fin 3)).weightedVSub a c = (0 : (EuclideanSpace ℝ (Fin 3))) := by
      rw [Finset.weightedVSub_eq_linear_combination _ hS, ← hF, hS, zero_smul]
    exact hc 0 (hind Finset.univ c hS h0 0 (Finset.mem_univ _))
  have hF2 : (∑ j, c j) • x = (∑ j, c j) • a0 + (∑ j, c j * X j) • f1 + (∑ j, c j * Y j) • f2 := by
    rw [hF]
    simp only [ha, Fin.sum_univ_three]
    module
  refine ⟨(∑ j, c j)⁻¹ * (∑ j, c j * X j), (∑ j, c j)⁻¹ * (∑ j, c j * Y j), ?_⟩
  have := congrArg (fun z : (EuclideanSpace ℝ (Fin 3)) => (∑ j, c j)⁻¹ • z) hF2
  simp only [smul_add, smul_smul, inv_mul_cancel₀ hS, one_smul] at this
  exact this

/-- **Planar transfer**: a non-collinear configuration is carried by an orthogonal frame to the
normalised plane configuration `(0,0), (1,0), (u,w)`; its equilibria map onto the 2-D equilibria and
3-D non-degeneracy gives non-vanishing of the 2-D Hessian determinant. -/
lemma planar_transfer (q : Fin 3 → ℝ) (a : Fin 3 → (EuclideanSpace ℝ (Fin 3))) (hq : ∀ j, q j ≠ 0)
    (hind : AffineIndependent ℝ a)
    (hnd : ∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x) :
    ∃ u w : ℝ, w ≠ 0 ∧ (∀ p : ℝ × ℝ, (∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) →
      ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 →
      ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 →
      (∑ j, q j * (2 * (p.1 - ![0, 1, u] j)^2 - (p.2 - ![0, 0, w] j)^2) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5) *
        (∑ j, q j * (2 * (p.2 - ![0, 0, w] j)^2 - (p.1 - ![0, 1, u] j)^2) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5) -
        (∑ j, q j * (3 * (p.1 - ![0, 1, u] j) * (p.2 - ![0, 0, w] j)) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^5)^2 ≠ 0) ∧
      (equilibria q a).encard ≤ {p : ℝ × ℝ | (∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) ∧
      ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 ∧
      ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0}.encard := by
  obtain ⟨f1, f2, u, w, h1, hf, hn, hw, ha1, ha2⟩ := exists_frame a hind
  have ha : ∀ j, a j = a 0 + (![0, 1, u] j) • f1 + (![0, 0, w] j) • f2 := by
    intro j; fin_cases j
    · simp
    · simp [ha1]
    · simp [ha2]
  have hL : ‖f1‖ ≠ 0 := norm_ne_zero_iff.mpr h1
  -- the embedding of the plane
  let ψ : ℝ × ℝ → (EuclideanSpace ℝ (Fin 3)) := fun p => a 0 + p.1 • f1 + p.2 • f2
  have hnorm : ∀ (p : ℝ × ℝ) j, ‖ψ p - a j‖ = ‖f1‖ * Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2) := by
    intro p j
    simp only [ψ]
    rw [coords_sub a (a 0) f1 f2 _ _ ha, frame_norm f1 f2 hf hn]
  have hnotin : ∀ p : ℝ × ℝ, (∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) → ψ p ∉ Set.range a := by
    rintro p hp ⟨j, hj⟩
    have h0 := hnorm p j
    rw [hj, sub_self, norm_zero] at h0
    have hpos : 0 < Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2) := Real.sqrt_pos.mpr (lt_of_le_of_ne (by positivity) (Ne.symm (hp j)))
    have := mul_pos (norm_pos_iff.mpr h1) hpos
    linarith
  have hfield : ∀ p : ℝ × ℝ, (∑ j, (q j / ‖(ψ p) - a j‖^3) • ((ψ p) - a j)) = (‖f1‖^3)⁻¹ •
      ((∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3) • f1 + (∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3) • f2) := by
    intro p
    exact coords_field q a (a 0) f1 f2 _ _ hf hn ha p.1 p.2
  have hmem : ∀ p ∈ {p : ℝ × ℝ | (∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) ∧
      ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 ∧
      ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0}, ψ p ∈ equilibria q a := by
    rintro p ⟨hp, he1, he2⟩
    rw [mem_equilibria_iff]
    refine ⟨hnotin p hp, ?_⟩
    rw [hfield p, he1, he2, zero_smul, zero_smul, add_zero, smul_zero]
  refine ⟨u, w, hw, ?_, ?_⟩
  · intro p hp he1 he2 hdet
    obtain ⟨v1, v2, hv0, hk1, hk2⟩ := kernel2 _ _ _ hdet
    have hv : v1 • f1 + v2 • f2 ≠ 0 := fun h0 => hv0 (frame_eq_zero f1 f2 hf hn h1 v1 v2 h0)
    apply not_nondegenerate' q a (ψ p) (hnotin p hp) _ hv _ (hnd _ (hmem p ⟨hp, he1, he2⟩))
    have := coords_kernel q a (a 0) f1 f2 _ _ hf hn h1 ha p.1 p.2 hp v1 v2
    simp only [ψ]
    rw [this, hk1, hk2, neg_zero, zero_smul, zero_smul, add_zero, smul_zero]
  · have hsub : equilibria q a ⊆ ψ '' {p : ℝ × ℝ | (∀ j, (p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2 ≠ 0) ∧
      ∑ j, q j * (p.1 - ![0, 1, u] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0 ∧
      ∑ j, q j * (p.2 - ![0, 0, w] j) / Real.sqrt ((p.1 - ![0, 1, u] j)^2 + (p.2 - ![0, 0, w] j)^2)^3 = 0} := by
      intro x hx
      obtain ⟨s, t, rfl⟩ := eq_coords q a hq hind (a 0) f1 f2 _ _ ha x hx
      have hx' := (mem_equilibria_iff q a _).mp hx
      have hp : ∀ j, (s - ![0, 1, u] j)^2 + (t - ![0, 0, w] j)^2 ≠ 0 := by
        intro j h0
        have h := hnorm (s, t) j
        simp only at h
        rw [h0, Real.sqrt_zero, mul_zero, norm_eq_zero, sub_eq_zero] at h
        exact hx'.1 ⟨j, h.symm⟩
      have hz := hx'.2
      rw [show a 0 + s • f1 + t • f2 = ψ (s, t) from rfl, hfield (s, t)] at hz
      have hz' := (smul_eq_zero.mp hz).resolve_left (inv_ne_zero (pow_ne_zero 3 hL))
      obtain ⟨e1, e2⟩ := frame_eq_zero f1 f2 hf hn h1 _ _ hz'
      exact ⟨(s, t), ⟨hp, e1, e2⟩, rfl⟩
    exact (Set.encard_le_encard hsub).trans (Set.encard_image_le _ _)


theorem main : H1 → H2 → type_of% @Arxiv.«2607.27197».maxwell_conjecture.variants.three_equal_magnitudes := by
  intro h1 h2 q a ha hq hq' hnd
  by_cases hind : AffineIndependent ℝ a
  · obtain ⟨u, w, hw, hdet, hle⟩ := planar_transfer q a hq hind hnd
    refine hle.trans ?_
    by_cases hall : ∀ i j, q i = q j
    · exact h1 q u w hw hq hall hdet
    · push_neg at hall
      exact h2 q u w hw hq hq' hall hdet
  · exact collinear_case q a ha hq hq' hnd (collinear_iff_not_affineIndependent.mpr hind)

end OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1
