# Maxwell's conjecture for three equal charges: a Lean reduction to the planar cases

This repository contains Lean 4 work on the statement
`maxwell_conjecture.variants.three_equal_magnitudes` in Google DeepMind's
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) collection: three point
charges of equal magnitude in R³, all of whose equilibria are non-degenerate, have at most 4
equilibria. This case is a known theorem (Y.-L. Tsai, Physica D 309 (2015)), and the registry lists
the target as kind "known".

**This is not a proof of Maxwell's conjecture, and it is not a proof of the three-equal-magnitudes
case.** What the repository contains is a sorry-free Lean reduction of the 3-D statement to two
self-contained planar statements, H1 and H2, which are cases of Tsai's theorem and are not proved
here. H1 and H2 carry the analytic core of Tsai's theorem. The parts that are proved outright are
the easier ones: planarity, the collinear case, and the passage from 3-D to 2-D.

## The problem and what was done

Charges q_j at points a_j in R³ produce the potential V(x) = Σ q_j / |x − a_j|. Its equilibria are
the critical points of V away from the charges. In the form of Gabrielov, Novikov and Shapiro,
Maxwell's conjecture says that if all equilibria of n charges are non-degenerate there are at most
(n − 1)² of them. Arathoon, Ball and Kvalheim (arXiv:2607.27197, 2026) disproved the general
conjecture with five positive charges whose potential has at least 24 > 16 non-degenerate
equilibria. For three charges the question is still open: Gabrielov, D. Novikov, T. Novikov and
Shapiro (arXiv:2607.28785, 2026) prove the bound 6 for three positive charges. Tsai proved the bound
4 for three charges of equal magnitude (ratios 1:1:1 and 1:−1:−1).

The work here:

1. **The reduction (Lean).** The registry file in `oma/` proves

   ```lean
   theorem main : H1 → H2 → type_of% @Arxiv.«2607.27197».maxwell_conjecture.variants.three_equal_magnitudes
   ```

   H1 and H2 are real 2-D statements about charges at (0,0), (1,0) and (u,w) with w ≠ 0. Each says:
   if the 2-D Hessian determinant of V is non-zero at every planar equilibrium, there are at most 4
   planar equilibria. H1 covers equal charges (1:1:1) and H2 equal magnitudes with mixed signs.
   Both follow from Tsai's theorem (see [PROOF.md](PROOF.md)). Neither is proved here.
2. **What is proved outright (Lean).**
   - *Planarity.* If the charges are not collinear, every equilibrium lies in their plane.
   - *The collinear case, in full.* Off-axis equilibria of collinear charges have a degenerate
     Hessian, and on the axis each interval between consecutive charges holds at most one
     equilibrium. So collinear equal-magnitude charges have at most 4 equilibria.
   - *The 3-D → 2-D transfer.* An orthogonal frame carries any non-collinear configuration to the
     normalised triangle. Equilibria correspond to zeros of the 2-D field, and a kernel vector of the
     2-D Hessian gives a kernel vector of the 3-D Hessian, so 3-D non-degeneracy gives a non-zero
     2-D determinant.
3. **An earlier version (Lean).** `lean/MaxwellThreeEqual/ThreeEqual.lean` proves the target from a
   single 3-D hypothesis `PlanarTsai` (at most 4 equilibria in the plane of a non-degenerate
   triangle). The registry file replaced it after an audit asked for 2-D hypotheses.
4. **Numerical search (Python, floating point).** For the main open statement
   `maxwell_conjecture.variants.three_charges` (any non-zero charges), multistart Newton searches
   over about 30000 random planar configurations and a random walk of about 17000 steps found no
   configuration with more than 4 equilibria. The same holds for 1200 random equal-magnitude
   configurations. This is only a search: it gives no proof, and it found no counterexample.

## Status

- **Lean.** Items 1–3 are proved in Lean 4 against the unmodified upstream definitions
  (formal-conjectures at commit `9097e2f9`), with no `sorry` and no `native_decide`.
  `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `main` and for the
  unconditional lemmas (`logs/axioms.log`). H1, H2 and `PlanarTsai` are hypotheses, not theorems.
- **Registry submission.** The reduction was submitted to the
  [open-math-agents](https://github.com/GuillaumeBAUD-coder/open-math-agents) registry as
  [pull request #4101](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4101), as a
  reduction of a known target. The local registry check accepted it, and the registry's automated
  `check-proof` CI job on the pull request passed, and the registry bot accepted and merged it
  (2026-11-27: "kernel accepted; axioms within propext, Classical.choice, Quot.sound"). The main target `three_charges` is untouched apart from the numerical search.
- **Paper proofs.** The statements of H1 and H2, why they follow from Tsai's theorem, and the proofs
  of what the Lean files prove are in [PROOF.md](PROOF.md). They have **not been checked by a human
  expert**. Tsai's full text was not available to us, so the link to his theorem rests on the
  abstract and on citing papers.
- **AI assistance.** This work was found and written with the help of Claude (Anthropic). Separate
  Claude sessions audited the reduction adversarially, twice. The first audit found the original
  3-D hypothesis thin and hard to read, which led to the 2-D form of H1 and H2. A separate reviewing
  session wrote the numerical solvers in `independent-checks/`. No expert in the subject has checked
  any of it. See [CHECKS.md](CHECKS.md).
- **Computer checks.** The searches in item 4 and in `independent-checks/` are floating-point
  heuristics. They are evidence, not proof.

I take responsibility for the claims made here. Corrections and references to earlier work are
welcome.

## Reproducing

Python ≥ 3.10. The scripts in `scripts/` and `independent-checks/num2.py` need NumPy; the other
files in `independent-checks/` use the standard library only.

```bash
python3 -I scripts/search3.py 15000 11 > logs/search3_11.log    # random planar configurations, general charges
python3 -I scripts/search_walk.py 17500 1 > logs/walk_1.log     # random walk inside the region with 4 equilibria
python3 -I scripts/equal_stats.py 300 0 > logs/equal_stats.log  # equal-magnitude charges on random triangles
python3 -I scripts/make_reduction2.py                           # regenerates oma/*.R1.lean from lean/parts/ (byte-identical)
cd independent-checks
python3 -I dense.py 1 120   # random triangles, 4 sign patterns      (cf. logs/independent-checks/dense_1.out)
python3 -I grid.py 0        # grid near the equilateral triangle     (cf. logs/independent-checks/grid_0.out)
python3 -I num2.py 11 250   # vectorised Newton, 1:1:1 and -1:1:1    (cf. logs/independent-checks/num2_11.out)
```

The exact seeds and step counts of the logged runs were not all recorded, so a rerun gives
comparable histograms rather than identical logs. Some `num2` histograms contain configurations
with 1 equilibrium. Index theory rules this out when Σq ≠ 0, so these are equilibria the solver
missed, which is a reminder that these searches are heuristics.

Lean (toolchain in `lean/lean-toolchain`, formal-conjectures at commit `9097e2f9`, which depends
on Mathlib `v4.33.1`):

```bash
cd lean && lake exe cache get && lake build && lake env lean Axioms.lean
```

`lake exe cache get` downloads the Mathlib build; the part of formal-conjectures that is needed is
compiled from source by `lake build`.

## Contents

- `PROOF.md`: the reduction, H1 and H2 and why they follow from Tsai's theorem, the proofs of the
  Lean results, faithfulness of the upstream statement, literature, and the numerical search
- `CHECKS.md`: the registry checks, the two adversarial audits, and the repository rebuild
- `lean/`: the Lean 4 project, depending on formal-conjectures
  (`MaxwellThreeEqual/Reduction.lean`, a module copy of the registry file;
  `MaxwellThreeEqual/ThreeEqual.lean`, the earlier `PlanarTsai` version; `Axioms.lean`).
  `lean/parts/` holds the source pieces from which `scripts/make_reduction2.py` generates the
  registry file; they are not part of the library.
- `oma/`: the reduction exactly as submitted to the open-math-agents registry
- `scripts/`, `logs/`: the search scripts, the generator, their logs, and the Lean build and axiom
  logs. `logs/independent-checks/` holds the outputs of the reviewer's solvers.
- `independent-checks/`: numerical solvers for the planar equilibria, written by a separate
  reviewing session and sharing no code with `scripts/`

## References

- P. Arathoon, G. Ball, M. D. Kvalheim, *The Maxwell conjecture is false*, arXiv:2607.27197 (2026),
  https://arxiv.org/abs/2607.27197.
- Y.-L. Tsai, *Maxwell's conjecture on three point charges with equal magnitudes*, Physica D 309
  (2015), 86–98, https://doi.org/10.1016/j.physd.2015.07.007.
- A. Gabrielov, D. Novikov, B. Shapiro, *Mystery of point charges*, Proc. London Math. Soc. 95
  (2007), 443–472, https://doi.org/10.1112/plms/pdm012.
- A. Gabrielov, D. Novikov, T. Novikov, B. Shapiro, arXiv:2607.28785 (2026),
  https://arxiv.org/abs/2607.28785.
- The Lean statement: formal-conjectures,
  [`FormalConjectures/Arxiv/2607.27197/MaxwellConjecture.lean`](https://github.com/google-deepmind/formal-conjectures/blob/9097e2f90e66d2f6244209cb1c07f7120d17ec53/FormalConjectures/Arxiv/2607.27197/MaxwellConjecture.lean).
