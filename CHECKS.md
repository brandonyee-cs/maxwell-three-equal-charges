# Independent checks — maxwell_conjecture.variants.three_equal_magnitudes.R1 (reduction)

## 2026-11-27 — Coordinator: registry lint ok (type reduction, kind known); registry tools/check.sh ACCEPTED
(kernel accepted; axioms within propext, Classical.choice, Quot.sound).

## 2026-11-27 — Adversarial audit (fresh subagent)
Recommendation: submit, borderline on value.
- Correct: compiles, standard axioms only; main pinned via type_of%; no other reduction of this target exists.
- Proof does real work: off-plane equilibria ruled out (affine-independence argument), collinear case fully proved
  (off-axis equilibria degenerate; ≤ 1 on-axis equilibrium per interval). No junk-value reliance; hypotheses consistent.
- H1/H2 appear TRUE: Tsai, Physica D 309 (2015) bound 4 for equal magnitudes (1:1:1, 1:-1:-1), cited by
  Gabrielov–Novikov–Novikov–Shapiro arXiv:2607.28785; reviewer's own Newton search (2000 random planar
  configurations) found max 4. Full text of Tsai not accessible (secondary sources only).
- (moderate) H1 ∧ H2 = target restricted to non-collinear triangles; split moves only the easy part. Acceptable but thin.
- (low) steps stated in 3-D; a 2-D normalised form would be friendlier. (cosmetic) deprecation warnings.

## 2026-11-27 — Reduction v2 (2-D hypotheses): coordinator registry lint ok + check.sh ACCEPTED
## 2026-11-27 — Reduction v2 adversarial audit (fresh subagent): SUBMIT
- 2-D field/Hessian formulas exact (det = AC − B², 3q factor, R⁵ powers); 2-D det ≠ 0 ⇔ 3-D nondegeneracy at planar
  equilibria of non-collinear charges (normal eigenvalue Σq/R³ cannot vanish there, by affine independence), so H1/H2 are
  exactly the non-collinear planar instances of Tsai's statement. H2 covers −1 at any vertex and global sign flips.
- Numerics (independent damped Newton): equilateral 1:1:1 → 4; ~540 random triangles × 4–6 sign patterns → 2; never > 4.
- Not vacuous; registry rules respected; compiles, main axioms standard; lint ok.
- (low) deprecated names / style warnings; (low) split still carries Tsai's core (judgement, not an error).

## The reviewer's numerical solvers (`independent-checks/`)
The four Python files in `independent-checks/` were written by a separate Claude session reviewing the
reduction, independently of `scripts/`. `solve.py` (standard library) is a damped Newton solver for the
planar field of charges at (0,0), (1,0), (u,w), seeded on log-polar clouds around the charges and the
centroid and along the triangle's edge lines. `dense.py` runs it on random triangles for the sign patterns
1:1:1, 1:1:−1, 1:−1:1 and −1:1:1, and `grid.py` on a grid of triangles near the equilateral one.
`num2.py` (NumPy) is a second, vectorised Newton solver started from a grid. Their outputs are in
`logs/independent-checks/`: never more than 4 equilibria; 4 only for 1:1:1 near the equilateral
triangle; otherwise 2. A few `num2` runs report 1 equilibrium, which index theory excludes, so the
solver missed one there. These are floating-point heuristics.

## 2026-11-27: repository rebuild
The library in `lean/` (`MaxwellThreeEqual.Reduction`, a module copy of the file in `oma/`, and
`MaxwellThreeEqual.ThreeEqual`) was rebuilt from scratch against formal-conjectures at commit `9097e2f9`
with `lake build` (success; only linter and deprecation warnings, `logs/lean_build.log`).
`lake env lean Axioms.lean` gives `[propext, Classical.choice, Quot.sound]` for `main`, `collinear_case`,
`equilibria_subset_affineSpan`, `planar_transfer`, `oneD_count` and `three_equal_magnitudes_of_planar`
(`logs/axioms.log`). `python3 -I scripts/make_reduction2.py` regenerates the file in `oma/` byte for byte
from `lean/parts/`.

## 2026-11-27: registry pull request #4101
The `check-proof` CI job on https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4101 completed
with SUCCESS (07:51 UTC). The registry bot then posted ACCEPTED (kernel accepted; axioms within propext,
Classical.choice, Quot.sound) and the pull request was merged at 08:09 UTC.
