"""Generate the registry reduction file (2-D hypotheses) from the lean/parts/ sources.
Run from the repository root: python3 scripts/make_reduction2.py  (writes oma/<registry file>).
Registry reductions may declare no defs besides H1..Hk, so `abbrev E` and `def field` are inlined."""
import re, sys
sys.path.insert(0, 'scripts')
from templates import NONDEG, SET
L = 'lean/parts/'
parts = [open(L + f).read() for f in ['Part1.lean', 'OneD.lean']]
asm = open(L + 'Assembly.part').read().split('/-- The single remaining hypothesis')[0] + 'end OMA.Maxwell3\n'
parts += [asm] + [open(L + f).read() for f in ['Planar1.part', 'Planar2.part', 'Planar3.part']]
body = '\n'.join(parts)
body = body.split('namespace OMA.Maxwell3', 1)[1]
for junk in ['import Mathlib\n', 'import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture\n',
             'open InnerProductSpace\n', 'open scoped RealInnerProductSpace Gradient\n']:
    body = body.replace(junk, '')
body = body.replace('abbrev E := EuclideanSpace ℝ (Fin 3)\n', '', 1)
body = re.sub(r'/-- The electric field.*?\n\n', '', body, count=1, flags=re.S)
body = re.sub(r'\n\s*unfold field( at \w+)?', '', body)
body = re.sub(r'(?m)^(end|namespace) OMA\.Maxwell3\n', '', body)
body = re.sub(r'(?m)^open Arxiv\.«2607\.27197»\n', '', body)
def F(v): return f'(∑ j, (q j / ‖{v} - a j‖^3) • ({v} - a j))'
body = body.replace('HasFDerivAt (field q a) D x', 'HasFDerivAt (fun y : E => ' + F('y') + ') D x')
out = []; i = 0; key = 'field q a '
while True:
    k = body.find(key, i)
    if k < 0: out.append(body[i:]); break
    if k > 0 and (body[k-1].isalnum() or body[k-1] in '_.'):
        out.append(body[i:k + len(key)]); i = k + len(key); continue
    out.append(body[i:k]); j = k + len(key)
    if body[j] == '(':
        d = 0; m = j
        while True:
            if body[m] == '(': d += 1
            elif body[m] == ')':
                d -= 1
                if d == 0: break
            m += 1
        arg = body[j:m + 1]; i = m + 1
    else:
        mm = re.match(r'\w+', body[j:]); arg = mm.group(0); i = j + len(arg)
    out.append(F(arg))
body = ''.join(out)
assert not re.search(r'(?<![\w.])field q a', body), 'unsubstituted field'
body = re.sub(r'(?<![\w.])E(?![\w])', '(EuclideanSpace ℝ (Fin 3))', body)
ns = 'OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_three_equal_magnitudes_R1'
H = lambda extra: f'''  ∀ (q : Fin 3 → ℝ) (u w : ℝ), w ≠ 0 → (∀ j, q j ≠ 0) → {extra}
    {NONDEG} →
    {SET}.encard ≤ 4'''
head = f'''import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture

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

namespace {ns}
open Arxiv.«2607.27197»

-- Tsai (2015), planar normalised form, equal charges.
def H1 : Prop :=
{H('(∀ i j, q i = q j) →')}

-- Tsai (2015), planar normalised form, equal magnitudes with mixed signs.
def H2 : Prop :=
{H('(∀ i j, |q i| = |q j|) → (∃ i j, q i ≠ q j) →')}
'''
tail = f'''
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

end {ns}
'''
open('oma/Arxiv.2607.27197.maxwell_conjecture.variants.three_equal_magnitudes.R1.lean', 'w').write(head + body + tail)
