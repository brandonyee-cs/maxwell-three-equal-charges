import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture

open InnerProductSpace
open scoped RealInnerProductSpace Gradient

namespace OMA.Maxwell3
abbrev E := EuclideanSpace ℝ (Fin 3)

lemma charge_hasGradient (q : ℝ) (a x : E) (hxa : x ≠ a) :
    HasGradientAt (fun y : E => q / dist y a) ((-q / ‖x-a‖^3) • (x-a)) x := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hs : HasFDerivAt (fun y : E => ‖y-a‖^2) (2 • innerSL ℝ (x-a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  have hd : HasFDerivAt (fun y : E => ‖y-a‖) (‖x-a‖⁻¹ • innerSL ℝ (x-a)) x := by
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

/-- The electric field (minus the gradient of the potential). -/
noncomputable def field (q : Fin 3 → ℝ) (a : Fin 3 → E) (y : E) : E :=
  ∑ j, (q j / ‖y - a j‖^3) • (y - a j)

lemma potential_hasGradient (q : Fin 3 → ℝ) (a : Fin 3 → E) (x : E) (hx : x ∉ Set.range a) :
    HasGradientAt (Arxiv.«2607.27197».potential q a) (-(field q a x)) x := by
  have hn (j : Fin 3) : x ≠ a j := fun h => hx ⟨j, h.symm⟩
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hf : Arxiv.«2607.27197».potential q a = fun y => ∑ j, q j / dist y (a j) := rfl
  rw [hf]
  have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (charge_hasGradient (q j) (a j) x (hn j)).hasFDerivAt)
  have key : (toDual ℝ E) (-(field q a x)) =
      ∑ i, (toDual ℝ E) ((-q i / ‖x - a i‖ ^ 3) • (x - a i)) := by
    unfold field
    rw [← Finset.sum_neg_distrib, map_sum]
    simp only [neg_div, neg_smul]
  rw [key]
  exact this

lemma mem_equilibria_iff (q : Fin 3 → ℝ) (a : Fin 3 → E) (x : E) :
    x ∈ Arxiv.«2607.27197».equilibria q a ↔ x ∉ Set.range a ∧ field q a x = 0 := by
  constructor
  · rintro ⟨hx, hg⟩
    refine ⟨hx, ?_⟩
    have := (potential_hasGradient q a x hx).gradient
    rw [hg] at this
    exact neg_eq_zero.mp this.symm
  · rintro ⟨hx, hg⟩
    refine ⟨hx, ?_⟩
    rw [(potential_hasGradient q a x hx).gradient, hg, neg_zero]


lemma norm_sub_hasFDerivAt (a x : E) (hxa : x ≠ a) :
    HasFDerivAt (fun y : E => ‖y-a‖) (‖x-a‖⁻¹ • innerSL ℝ (x-a)) x := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hs : HasFDerivAt (fun y : E => ‖y-a‖^2) (2 • innerSL ℝ (x-a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  convert! hs.sqrt (pow_ne_zero 2 hn) using 1
  · funext y; exact (Real.sqrt_sq (norm_nonneg _)).symm
  · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
    norm_num

/-- the coefficient `q / ‖y - a‖^3` has a derivative that kills every vector orthogonal to `x - a`. -/
lemma coeff_hasFDerivAt (q : ℝ) (a x : E) (hxa : x ≠ a) :
    ∃ C : E →L[ℝ] ℝ, HasFDerivAt (fun y : E => q / ‖y-a‖^3) C x ∧
      ∀ u : E, ⟪x - a, u⟫ = 0 → C u = 0 := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hg : DifferentiableAt ℝ (fun r : ℝ => q / r^3) ‖x-a‖ :=
    (differentiableAt_const q).div (differentiableAt_pow 3) (pow_ne_zero 3 hn)
  refine ⟨deriv (fun r : ℝ => q / r^3) ‖x-a‖ • (‖x-a‖⁻¹ • innerSL ℝ (x-a)), ?_, ?_⟩
  · have h := hg.hasDerivAt.comp_hasFDerivAt (f := fun y : E => ‖y-a‖) x
      (norm_sub_hasFDerivAt a x hxa)
    exact h
  · intro u hu
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply, hu]
    simp

lemma field_hasFDerivAt (q : Fin 3 → ℝ) (a : Fin 3 → E) (x : E) (hx : x ∉ Set.range a) :
    ∃ D : E →L[ℝ] E, HasFDerivAt (field q a) D x ∧
      ∀ u : E, (∀ j, ⟪x - a j, u⟫ = 0) → D u = (∑ j, q j / ‖x - a j‖^3) • u := by
  have hn (j : Fin 3) : x ≠ a j := fun h => hx ⟨j, h.symm⟩
  choose C hC hCu using fun j => coeff_hasFDerivAt (q j) (a j) x (hn j)
  have hj (j : Fin 3) : HasFDerivAt (fun y : E => (q j / ‖y - a j‖^3) • (y - a j))
      ((q j / ‖x - a j‖^3) • ContinuousLinearMap.id ℝ E + (C j).smulRight (x - a j)) x :=
    (hC j).fun_smul ((hasFDerivAt_id x).sub_const (a j))
  refine ⟨∑ j, ((q j / ‖x - a j‖^3) • ContinuousLinearMap.id ℝ E + (C j).smulRight (x - a j)),
    ?_, ?_⟩
  · have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hj j)
    exact this
  · intro u hu
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq,
      ContinuousLinearMap.smulRight_apply, hCu _ u (hu _), zero_smul, add_zero, Finset.sum_smul]

/-- **Lemma D**: an equilibrium at which some nonzero `u` is orthogonal to all `x - a j` while
`∑ q j / r_j^3 = 0` is degenerate. -/
lemma not_nondegenerate (q : Fin 3 → ℝ) (a : Fin 3 → E) (x : E) (hx : x ∉ Set.range a)
    (u : E) (hu : u ≠ 0) (horth : ∀ j, ⟪x - a j, u⟫ = 0)
    (hsum : ∑ j, q j / ‖x - a j‖^3 = 0) :
    ¬ Arxiv.«2607.27197».HasNondegenerateHessianAt (Arxiv.«2607.27197».potential q a) x := by
  intro hnd
  obtain ⟨D, hD, hDu⟩ := field_hasFDerivAt q a x hx
  have hopen : IsOpen (Set.range a)ᶜ := (Set.finite_range a).isClosed.isOpen_compl
  have hev : fderiv ℝ (Arxiv.«2607.27197».potential q a) =ᶠ[nhds x]
      fun y => -(innerSL ℝ (field q a y)) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [(potential_hasGradient q a y hy).hasFDerivAt.fderiv]
    ext w
    simp [toDual_apply_apply, innerSL_apply_apply, inner_neg_left]
  have hF : HasFDerivAt (fun y => -(innerSL ℝ (field q a y))) (-((innerSL ℝ).comp D)) x :=
    (((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt).comp x hD).neg
  obtain ⟨w, hw⟩ := hnd u hu
  apply hw
  rw [iteratedFDeriv_two_apply, hev.fderiv_eq, hF.fderiv]
  simp [hDu u horth, hsum]

end OMA.Maxwell3
