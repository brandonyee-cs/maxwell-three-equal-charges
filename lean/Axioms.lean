import MaxwellThreeEqual

/-! Prints the axioms used by the main theorems of `MaxwellThreeEqual`. -/

-- Run with `lake env lean Axioms.lean` after `lake build`.
-- The registry reduction: H1 → H2 → three_equal_magnitudes.
#print axioms OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1.main
-- Unconditional pieces used by `main`.
#print axioms OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1.collinear_case
#print axioms OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1.equilibria_subset_affineSpan
#print axioms OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1.planar_transfer
#print axioms OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1.oneD_count
-- The first version: PlanarTsai → three_equal_magnitudes.
#print axioms OMA.Maxwell3.three_equal_magnitudes_of_planar
