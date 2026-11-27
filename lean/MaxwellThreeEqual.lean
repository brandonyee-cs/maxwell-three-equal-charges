import MaxwellThreeEqual.Reduction
import MaxwellThreeEqual.ThreeEqual

/-!
# Maxwell's conjecture for three charges of equal magnitude: reduction to the planar cases

Work on `Arxiv.«2607.27197».maxwell_conjecture.variants.three_equal_magnitudes` (formal-conjectures).

* `MaxwellThreeEqual.Reduction`: a copy, as a module, of the registry file in `oma/`.
  `main : H1 → H2 → type_of% @...three_equal_magnitudes`, where `H1` (charges 1:1:1) and `H2`
  (mixed signs, 1:1:-1) are planar statements about the triangle (0,0), (1,0), (u,w), w ≠ 0.
* `MaxwellThreeEqual.ThreeEqual`: the first version, with a single 3-D hypothesis `PlanarTsai`.

`H1`, `H2` and `PlanarTsai` are cases of Tsai's theorem (Physica D 309 (2015)) and are not proved here.
-/
