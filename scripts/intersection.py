#!/usr/bin/env python3
"""Compute and Lean-check a real intersection of two sparse polynomials."""
import argparse
import itertools
import json
import math
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path

from univariate import ROOT, check, derivative, evaluate, exact
from univariate import gcd, generate, mul, poly, polynomial, rat, split_intervals


ORIGIN = (0, 0, 0)
UNITS = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]


GENERATED_OPTIONS = """set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
"""


def read_equation(rows):
    if not isinstance(rows, list):
        raise ValueError('each equation must be a list of [x exponent, y exponent, z exponent, coefficient]')
    result = {}
    for row in rows:
        if not isinstance(row, list) or len(row) != 4:
            raise ValueError('expected four entries per term')
        powers = tuple(row[:3])
        if any(type(p) is not int or p < 0 for p in powers) or sum(powers) > 4:
            raise ValueError('exponents must be nonnegative and have total degree at most four')
        if type(row[3]) not in (int, str, Fraction):
            raise ValueError('expected a rational coefficient')
        result[powers] = result.get(powers, 0) + Fraction(row[3])
    return {p: c for p, c in result.items() if c}


def factors_as_equation(factor):
    return {p: c for p, c in zip([ORIGIN, *UNITS], factor) if c}


def affine_division(f, a):
    divisor = factors_as_equation(a)
    top = max(divisor)
    remainder, quotient = f.copy(), {}
    while remainder:
        term = max(remainder)
        exp = tuple(i-j for i, j in zip(term, top))
        if min(exp) < 0:
            return None
        c = remainder[term]/divisor[top]
        quotient[exp] = c
        for p, d in divisor.items():
            k = tuple(i+j for i, j in zip(p, exp))
            value = remainder.get(k, 0) - c*d
            if value:
                remainder[k] = value
            else:
                remainder.pop(k, None)
    return quotient


def rational_roots(f):
    """Recover candidate rational roots from isolating intervals and the leading coefficient."""
    simple = exact(f, gcd(f, derivative(f)))
    _, segments = split_intervals(simple, [], [])
    denominator = math.lcm(*(c.denominator for c in f))
    limit = abs(int(f[-1]*denominator))
    tolerance = Fraction(1, limit**2)
    roots = []
    for l, h, has_root in segments:
        if not has_root:
            continue
        left = evaluate(simple, l)
        while h-l >= tolerance:
            mid = (l+h)/2
            value = evaluate(simple, mid)
            if value == 0:
                l = h = mid
                break
            if left*value > 0:
                l, left = mid, value
            else:
                h = mid
        candidate = ((l+h)/2).limit_denominator(limit)
        if not evaluate(f, candidate):
            roots.append(candidate)
    return roots


def restrict_line(f, direction, offset):
    result = [Fraction(0)] * (1 + max(map(sum, f)))
    for p, c in f.items():
        term = (c,)
        for k, a, b in zip(p, offset, direction):
            for _ in range(k):
                term = mul(term, poly([a, b]))
        for i, coefficient in enumerate(term):
            result[i] += coefficient
    return poly(result)


def affine_factors(f):
    if not f:
        return [[0, 0, 0, 0]]
    if max(map(sum, f)) <= 1:
        return [[f.get(p, 0) for p in (ORIGIN, *UNITS)]]
    degree = max(map(sum, f))
    for t in itertools.count():
        v = (1, t, t**(degree+1))
        origin_line = restrict_line(f, v, ORIGIN)
        if len(origin_line) == degree+1:
            break
    roots = rational_roots(origin_line)
    if not roots:
        return None
    y_roots = rational_roots(restrict_line(f, v, UNITS[1]))
    z_roots = rational_roots(restrict_line(f, v, UNITS[2]))
    factors = []
    for r, y, z in itertools.product(roots, y_roots, z_roots):
        dy, dz = y-r, z-r
        a = [-r, 1+dy*v[1]+dz*v[2], -dy, -dz]
        quotient = affine_division(f, a)
        while quotient is not None:
            factors.append(a)
            f = quotient
            if max(map(sum, f)) <= 1:
                rest = affine_factors(f)
                return factors + ([] if rest == [[1, 0, 0, 0]] else rest)
            quotient = affine_division(f, a)
    return None


def sparse_expression(f, coordinates):
    return ' + '.join(' * '.join([rat(c), *[
        f'({a})^{k}' for a, k in zip(coordinates, powers) if k
    ]]) for powers, c in sorted(f.items())) or '0'


def system_def(equations, coordinates, space):
    return '\n'.join(f'def input{i} (p : {space}) : ℝ := {sparse_expression(f, coordinates)}'
                     for i, f in enumerate(equations))


def affine_source(equations, factors):
    factors_literal = ', '.join('[' + ', '.join(
        f'((({rat(c)}, {rat(x)}), {rat(y)}), {rat(z)})' for c, x, y, z in fs) + ']' for fs in factors)
    proofs = '\n'.join(f'''
theorem input{i}_factor (p : Fin 3 → ℝ) :
    productEval ((factors.get ⟨{i}, by decide⟩).map (Extension.aff (Rat.castHom ℝ)))
      (Geometry.coords p) = input{i} p := by
  norm_num [factors, input{i}, productEval, Extension.aff, Aff.eval, Geometry.coords]
  <;> ring
''' for i in range(2))
    return f"""import CertifiedTopology.IntersectionIO

{GENERATED_OPTIONS}
open CertifiedTopology CertifiedTopology.TopologyArtifact

namespace CertifiedIntersection

{system_def(equations, ['p 0', 'p 1', 'p 2'], 'Fin 3 → ℝ')}
def factors : List (Product ℚ 3) := [{factors_literal}]
{proofs}
def artifact := AffineTopology.solveFactors factors

def locus : Set (Fin 3 → ℝ) := {{p | input0 p = 0 ∧ input1 p = 0}}

theorem certified : Valid artifact (Geometry.carrier ∘ Extension.cell (Rat.castHom ℝ)) locus := by
  have eq : AffineTopology.realLocus (Rat.castHom ℝ) factors = locus := by
    ext p
    have h₀ := input0_factor p
    have h₁ := input1_factor p
    simp only [AffineTopology.realLocus, locus, Set.mem_ofPred_eq, factors, List.forall_mem_cons,
      List.not_mem_nil, false_implies, implies_true, and_true]
    exact and_congr (congrArg (· = 0) h₀).to_iff (congrArg (· = 0) h₁).to_iff
  rw [← eq]
  exact AffineTopology.solveFactors_correct (Rat.castHom ℝ) Rat.cast_strictMono factors

end CertifiedIntersection

def main : IO Unit :=
  IO.println (CertifiedIntersection.artifact.toJson affine3Json).compress
"""


@dataclass
class GraphReduction:
    index: int
    axes: tuple
    multiple: Fraction
    graph: list
    center: tuple
    radicand: tuple
    graph_scale: Fraction
    height_scale: Fraction
    power: int


def add_term(f, powers, c):
    v = f.get(powers, 0) + c
    if v:
        f[powers] = v
    else:
        f.pop(powers, None)


def multiply_sparse(f, g):
    result = {}
    for p, c in f.items():
        for q, d in g.items():
            add_term(result, tuple(x+y for x, y in zip(p,q)), c*d)
    return result


def height_coefficients(terms):
    result = [[] for _ in range(1+max((z for _, z in terms), default=0))]
    for (x,z), c in terms.items():
        result[z].extend([0]*max(0, x+1-len(result[z])))
        result[z][x] = c
    return [poly(p) for p in result]


def graph_reduction(equations):
    for i in range(2):
        first, other = equations[i], equations[1-i]
        for y in range(3):
            # A constant linear pivot may be present or exposed by subtraction.
            obstructions = [p for p in first if p[y] and p != UNITS[y]]
            multiples = [Fraction(0)]
            if obstructions and obstructions[0] in other:
                p = obstructions[0]
                multiples.append(first[p]/other[p])
            for multiple in multiples:
                equation = first.copy()
                for powers, c in other.items():
                    add_term(equation, powers, -multiple*c)
                a = equation.get(UNITS[y], 0)
                if not a or any(p[y] and p != UNITS[y] for p in equation):
                    continue
                for z in range(3):
                    if z == y:
                        continue
                    x = 3-y-z
                    graph = {(p[x], p[z]): -c/a for p, c in equation.items() if p != UNITS[y]}
                    powers_of_graph = [{(0, 0): Fraction(1)}]
                    for _ in range(max((p[y] for p in other), default=0)):
                        powers_of_graph.append(multiply_sparse(powers_of_graph[-1], graph))
                    value = {}
                    for p, c in other.items():
                        for (j,k), value_coefficient in powers_of_graph[p[y]].items():
                            add_term(value, (j+p[x], k+p[z]), c*value_coefficient)
                    coeffs = height_coefficients(value)
                    if len(coeffs) == 3 and len(coeffs[2]) == 1:
                        c, b, (scale,) = coeffs
                        center = poly(-v/(2*scale) for v in b)
                        square = mul(center, center)
                        radicand = poly((square[j] if j < len(square) else 0) -
                                        (c[j]/scale if j < len(c) else 0)
                                        for j in range(max(len(square), len(c))))
                        return GraphReduction(i, (x,y,z), multiple, height_coefficients(graph),
                                              center, radicand, a, scale, 2)
                    if len(coeffs) == 5 and len(coeffs[4]) == 1:
                        c, b, square_coeff, cube_coeff, (scale,) = coeffs
                        center = poly(-v/(4*scale) for v in cube_coeff)
                        square = mul(center, center)
                        if (square_coeff != poly(6*scale*v for v in square)
                                or b != poly(-4*scale*v for v in mul(square, center))):
                            continue
                        fourth = mul(square, square)
                        radicand = poly((fourth[j] if j < len(fourth) else 0) -
                                        (c[j]/scale if j < len(c) else 0)
                                        for j in range(max(len(fourth), len(c))))
                        return GraphReduction(i, (x,y,z), multiple, height_coefficients(graph),
                                              center, radicand, a, scale, 4)
                    if len(coeffs) == 2 and len(coeffs[1]) == 1:
                        c, (scale,) = coeffs
                        return GraphReduction(i, (x,y,z), multiple, height_coefficients(graph),
                                              poly(-v/scale for v in c), (), a, scale, 1)
    return None


def bipoly(coefficients):
    terms = []
    for n, c in enumerate(coefficients):
        if c:
            term = f'C ({polynomial(c)} : Polynomial ℝ)'
            terms.append(f'{term} * X^{n}' if n else term)
    return '(' + (' + '.join(terms) or '0') + ' : Plane.BiPoly ℝ)'


def graph_source(equations, reduction):
    i = reduction.index
    x, y, z = reduction.axes
    graph, center, radicand = reduction.graph, reduction.center, reduction.radicand
    a, scale = reduction.graph_scale, reduction.height_scale
    source, rows = generate([radicand])
    source = source.replace('import CertifiedTopology.Isolation',
                            'import CertifiedTopology.PowerGraph\nimport CertifiedTopology.IntersectionIO\n\n'
                            + GENERATED_OPTIONS + 'set_option maxHeartbeats 0\n')
    sign_literal = ', '.join({-1: '.below', 0: '.on', 1: '.above'}[r['signs'][0]] for r in rows)
    row_names = [f'row{k}' for k in range(len(rows))]
    shapes = ', '.join(f'{r}.region' for r in row_names)
    section_count = (len(rows)-1)//2
    order = []
    for k in range(section_count):
        order.append(f'  have ⟨l{k}, u{k}⟩ := box{k}.interior')
    inequalities = []
    for k in range(section_count):
        for j in range(k+1, section_count):
            order.append(f'  have ord{k}_{j} : box{k}.root < box{j}.root := by linarith')
            order.append(f'  have ne{k}_{j} := ord{k}_{j}.ne')
            inequalities.extend([f'ord{k}_{j}', f'ne{k}_{j}', f'ord{k}_{j}.ne\''])
    row_defs = ', '.join(row_names)
    distinct = ', '.join(inequalities) + (', ' if inequalities else '')
    coords = ['']*3
    for k, coordinate in [(x, 'p.1.1'), (y, 'p.1.2'), (z, 'p.2')]:
        coords[k] = coordinate
    gpoly = bipoly(graph)
    cpoly = f'({polynomial(center)} : Polynomial ℝ)'
    substituted = '((t, Plane.value q.graph (t,h)),h)'
    if reduction.power == 1:
        normalized = f'{rat(scale)} * (h - q.center.eval t)'
        height_equiv = ('rw [mul_eq_zero, show q.radicand.eval t = 0 by simp [q, p0]]\n'
                        '    norm_num [q, Equation.power, pow_eq_zero_iff]')
    else:
        normalized = f'{rat(scale)} * (q.power (h - q.center.eval t) - q.radicand.eval t)'
        height_equiv = 'rw [mul_eq_zero]; norm_num; exact sub_eq_zero'
    return source + f"""
open CertifiedTopology.PowerGraph TopologyArtifact

namespace CertifiedIntersection

open CertifiedDiagram

{system_def(equations, coords, 'PowerGraph.Space')}

noncomputable def q : PowerGraph.Equation := ⟨{gpoly}, {cpoly}, p0, {str(reduction.power == 4).lower()}⟩

def signs : List Side := [{sign_literal}]
def incident (i j : Fin signs.length) : Bool :=
  decide (i = j ∨ i.val % 2 = 0 ∧ j.val % 2 = 1 ∧
    (i.val + 1 = j.val ∨ j.val + 1 = i.val))
noncomputable def shape (i : Fin signs.length) : Slice ℝ :=
  [{shapes}].getD i.val (.sector none none)

private theorem shape_injective : Function.Injective shape := by
  intro i j e
{chr(10).join(order)}
  fin_cases i <;> fin_cases j <;>
    simp [shape, signs, {row_defs}, {distinct}Slice.sectionAt.injEq, Slice.sector.injEq] at e ⊢

private theorem shape_nonempty (i : Fin signs.length) : (Plane.strip (shape i)).Nonempty := by
  fin_cases i
{chr(10).join(f'  · exact ⟨{r}.witness, {r}.inside⟩' for r in row_names)}

private theorem incident_correct (i j : Fin signs.length) (t : ℝ)
    (ht : t ∈ Plane.strip (shape j)) :
    incident i j = true ↔ t ∈ closure (Plane.strip (shape i)) := by
{chr(10).join(order)}
  fin_cases i <;> fin_cases j <;>
    simp [incident, signs, shape, {row_defs}, {distinct}PowerGraph.strip_section,
      PowerGraph.strip_unbounded, PowerGraph.strip_lower, PowerGraph.strip_upper,
      PowerGraph.strip_bounded, closure_Ioo] at ht ⊢ <;>
    (try subst t) <;> (try simp_all) <;> (try constructor!) <;> (try intro h) <;> linarith

noncomputable def base : Base q :=
  Base.ofDiagram diagram signs shape shape_injective rfl shape_nonempty incident incident_correct

def artifact := Base.compute signs incident

def locus : Set PowerGraph.Space := {{p | input0 p = 0 ∧ input1 p = 0}}

def eliminated (p : PowerGraph.Space) : ℝ := input{i} p - {rat(reduction.multiple)} * input{1-i} p

private theorem normalized_graph (t w h : ℝ) :
    eliminated ((t,w),h) = {rat(a)} * (w - Plane.value q.graph (t,h)) := by
  norm_num [eliminated, input0, input1, q, Plane.value, Plane.specialize] <;> ring

private theorem normalized_height (t h : ℝ) :
    input{1-i} {substituted} = {normalized} := by
  norm_num [input{1-i}, q, p0, Equation.power, Plane.value, Plane.specialize] <;> ring

theorem certified : Valid artifact base.carrier locus := by
  have eq : q.locus = locus := by
    ext p
    obtain ⟨⟨t,w⟩,h⟩ := p
    change (w = Plane.value q.graph (t,h) ∧ q.power (h - q.center.eval t) = q.radicand.eval t) ↔
      input0 ((t,w),h) = 0 ∧ input1 ((t,w),h) = 0
    have system : (eliminated ((t,w),h) = 0 ∧ input{1-i} ((t,w),h) = 0) ↔
        input0 ((t,w),h) = 0 ∧ input1 ((t,w),h) = 0 := by
      unfold eliminated
      constructor <;> rintro ⟨h₀,h₁⟩ <;> constructor <;> linarith
    apply Iff.trans _ system
    have hg : eliminated ((t,w),h) = 0 ↔ w = Plane.value q.graph (t,h) := by
      rw [normalized_graph, mul_eq_zero]
      norm_num
      exact sub_eq_zero
    rw [hg]
    apply and_congr_right
    intro hy
    subst w
    rw [normalized_height]
    symm
    {height_equiv}
  rw [← eq]
  exact base.solve_correct

end CertifiedIntersection

def main : IO Unit := do
  let result := CertifiedIntersection.artifact.toJson fun (i, upper) =>
    Lean.Json.mkObj [("base_row", Lean.toJson i.val), ("upper", Lean.toJson upper),
      ("dimension", Lean.toJson (if i.val % 2 = 0 then (1 : Nat) else 0))]
  IO.println result.compress
""", rows


def read_algebraic(rows, roots):
    if not isinstance(rows, list):
        raise ValueError('each equation must be a list of sparse terms')
    terms = []
    for row in rows:
        if not isinstance(row, list) or len(row) != 4:
            raise ValueError('expected four entries per term')
        powers = tuple(row[:3])
        if any(type(p) is not int or p < 0 for p in powers) or sum(powers) > 4:
            raise ValueError('exponents must be nonnegative and have total degree at most four')
        c = row[3]
        if not isinstance(c, dict):
            if type(c) not in (int, str, Fraction):
                raise ValueError('expected a rational or algebraic coefficient')
            c = Fraction(c)
            if c:
                terms.append((powers, c, False))
            continue
        if set(c) != {'polynomial', 'root'} or not isinstance(c['polynomial'], list):
            raise ValueError('an algebraic coefficient needs a polynomial and a root index')
        values = c['polynomial']
        k = c['root']
        if type(k) is not int or k < 0 or any(type(a) not in (int, str, Fraction) for a in values):
            raise ValueError('a root index must be nonnegative and the polynomial must have rational coefficients')
        spec = (poly(values), k)
        if len(spec[0]) < 2:
            raise ValueError('a defining polynomial for an algebraic coefficient must have positive degree')
        if spec not in roots:
            roots.append(spec)
        terms.append((powers, roots.index(spec), True))
    return terms


def computed_source(equations, roots, refine=False):
    def equation(terms):
        return '[' + ', '.join(
            f'⟨{x}, {y}, {z}, ' + (f'.inr ⟨{c}, by decide⟩' if algebraic else f'.inl {rat(c)}') + '⟩'
            for (x, y, z), c, algebraic in terms
        ) + ']'

    specs = ', '.join(f'⟨[{", ".join(map(rat, ps))}], {i}⟩' for ps, i in roots)
    definitions = (f'abbrev rootSpecs : List RootSpec := [{specs}]\n'
                   f'def input0 : List (SparseTerm rootSpecs.length) := {equation(equations[0])}\n'
                   f'def input1 : List (SparseTerm rootSpecs.length) := {equation(equations[1])}\n')
    if roots:
        run = """def main : IO Unit :=
  match selectedCoefficients with
  | none => throw (IO.userError "a defining polynomial has no real root at the requested index")
  | some coeffs => IO.println ((artifact coeffs).toJson none).compress
"""
    else:
        run = """def main : IO Unit := IO.println (rationalJson input0 input1).compress
"""
    if refine and roots:
        run = """def main : IO Unit :=
  match selectedCoefficients with
  | none => throw (IO.userError "a defining polynomial has no real root at the requested index")
  | some coeffs =>
    let a := artifact coeffs
    IO.println (Lean.Json.mkObj [
      ("cells", a.toJson none),
      ("strata", ComputedTopology.strataJson a.refine)]).compress
"""
    elif refine:
        run = """def main : IO Unit :=
  let a := artifact (.origin RealModel.rational)
  IO.println (Lean.Json.mkObj [
    ("cells", a.toJson (some fun c => Lean.toJson (toString (show ℚ from c)))),
    ("strata", ComputedTopology.strataJson a.refine)]).compress
"""
    solution = """def selectedCoefficients := coefficients rootSpecs

theorem certifiedCoefficients (coeffs : ExactPoint RealModel.rational rootSpecs.length)
    (h : selectedCoefficients = some coeffs) (i : Fin rootSpecs.length) :
    (rootSpecs.get i).realValue = some (coeffs.value i.rev) :=
  coefficients_correct h i

def artifact (coeffs : ExactPoint RealModel.rational rootSpecs.length) :=
  ComputedInput.solve coeffs input0 input1

def refinement (coeffs : ExactPoint RealModel.rational rootSpecs.length) :=
  ComputedInput.solveStrata coeffs input0 input1

noncomputable def inputLocus : Set (Fin 3 → ℝ) :=
  {x | (input0.map (fun t => t.evalSpec rootSpecs x)).sum = 0 ∧
       (input1.map (fun t => t.evalSpec rootSpecs x)).sum = 0}

theorem certifiedLocus (coeffs : ExactPoint RealModel.rational rootSpecs.length)
    (h : selectedCoefficients = some coeffs) :
    ComputedTopology.locus coeffs.model (sparse coeffs input0) (sparse coeffs input1) = inputLocus := by
  ext x
  simp only [ComputedTopology.locus, inputLocus, Set.mem_ofPred_eq, sparse_correct, SparseTerm.eval_spec h]

theorem certified (coeffs : ExactPoint RealModel.rational rootSpecs.length)
    (h : selectedCoefficients = some coeffs) (x : Fin 3 → ℝ) :
    x ∈ inputLocus ↔
      ∃! c, c ∈ (artifact coeffs).cells ∧ x ∈ c.carrier := by
  rw [← certifiedLocus coeffs h]
  exact (artifact coeffs).partition x

theorem certifiedComponents (coeffs : ExactPoint RealModel.rational rootSpecs.length)
    (h : selectedCoefficients = some coeffs)
    (i : Fin (artifact coeffs).cells.length) {x : Fin 3 → ℝ}
    (hx : x ∈ ComputedTopology.carrier (artifact coeffs).cells i) :
    connectedComponentIn inputLocus x =
      ⋃ j : {j // (artifact coeffs).labels.get i = (artifact coeffs).labels.get j},
        ComputedTopology.carrier (artifact coeffs).cells j.val := by
  rw [← certifiedLocus coeffs h]
  exact (artifact coeffs).component_correct i hx

theorem certifiedStrata (coeffs : ExactPoint RealModel.rational rootSpecs.length)
    (h : selectedCoefficients = some coeffs) (x : Fin 3 → ℝ) :
    x ∈ inputLocus ↔
      ∃! s, s ∈ (refinement coeffs).strata ∧ x ∈ s.carrier := by
  rw [← certifiedLocus coeffs h]
  exact ComputedTopology.stratifyIntersection_correct coeffs.model
    (sparse coeffs input0) (sparse coeffs input1) x

theorem certifiedStratumClosure (coeffs : ExactPoint RealModel.rational rootSpecs.length)
    (i : Fin (refinement coeffs).strata.length) :
    closure ((refinement coeffs).strata.get i).carrier =
      ⋃ j : {j // (refinement coeffs).incidence i j = true},
        ((refinement coeffs).strata.get j.val).carrier :=
  (refinement coeffs).closure_eq (by
    rw [ComputedTopology.zeroSetFormula_correct]
    exact ComputedTopology.locus_closed _ _ _) i

""" + run
    return f"""import CertifiedTopology.ComputedInput

open CertifiedTopology CertifiedTopology.ComputedInput
open CertifiedTopology.ExecutableIsolation CertifiedTopology.CylindricalData

{definitions}
{solution}"""


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='JSON array containing the two sparse equations')
    parser.add_argument('--lean', type=Path, help='save the checked Lean artifact')
    parser.add_argument('--stratify', action='store_true',
                        help='compute the frontier refinement and exact closure table on the CAD route')
    args = parser.parse_args()
    try:
        raw = json.loads(args.input.read_text(), parse_float=Fraction)
        if not isinstance(raw, list) or len(raw) != 2:
            raise ValueError('expected exactly two equations')
        roots = []
        terms = [read_algebraic(f, roots) for f in raw]
        equations = None if roots else [read_equation(f) for f in raw]
    except (ValueError, OSError, ZeroDivisionError) as error:
        parser.error(str(error))
    factors = [affine_factors(f) for f in equations] if equations is not None else None
    if factors is not None and all(f is not None for f in factors):
        source = affine_source(equations, factors)
        report = {'route': 'affine'}
        targets = ['CertifiedTopology.IntersectionIO']
    elif equations is not None and (reduction := graph_reduction(equations)):
        source, rows = graph_source(equations, reduction)
        report = {'route': 'power_graph', 'axes': reduction.axes, 'base': rows,
                  'power': max(2, reduction.power),
                  'graph': [list(map(str, c)) for c in reduction.graph],
                  'center': list(map(str, reduction.center)),
                  'radicand': list(map(str, reduction.radicand))}
        targets = ['CertifiedTopology.IntersectionIO', 'CertifiedTopology.PowerGraph']
    else:
        source = computed_source(terms, roots, args.stratify)
        report = {'route': 'cad'}
        targets = ['CertifiedTopology.ComputedInput']
    check(['lake', 'build', *targets])
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp)/'Intersection.lean'
        path.write_text(source)
        if args.lean:
            check(['lake', 'env', 'lean', str(path)])
            args.lean.write_text(source)
        lean = subprocess.run(['lake', 'env', 'lean', '--run', str(path)], cwd=ROOT,
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        if lean.returncode:
            sys.stderr.write(lean.stdout)
            raise SystemExit(lean.returncode)
        output = json.loads(lean.stdout.splitlines()[-1])
        if args.stratify and report['route'] == 'cad':
            report.update(output)
        else:
            report['cells'] = output
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
