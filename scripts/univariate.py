#!/usr/bin/env python3
"""Emit and kernel-check a univariate rational sign diagram."""
import argparse
import json
import subprocess
import sys
import tempfile
from fractions import Fraction
from math import comb
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def poly(values):
    result = list(map(Fraction, values))
    while result and not result[-1]:
        result.pop()
    return tuple(result)


ONE = poly([1])


def mul(a, b):
    terms = [0] * (len(a) + len(b))
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            terms[i+j] += x*y
    return poly(terms)


def division(a, b):
    if not b:
        raise ZeroDivisionError
    quotient = [0] * max(0, len(a)-len(b)+1)
    while a and len(a) >= len(b):
        i = len(a)-len(b)
        c = a[-1]/b[-1]
        quotient[i] = c
        a = poly(list(a[:i]) + [x-c*y for x, y in zip(a[i:], b)])
    return poly(quotient), a


def exact(a, b):
    q, rem = division(a, b)
    assert not rem
    return q


def gcd(a, b):
    while b:
        a, b = b, division(a, b)[1]
    return poly(x/a[-1] for x in a) if a else ()


def derivative(a):
    return poly(i*a[i] for i in range(1, len(a)))


def evaluate(a, x):
    v = Fraction(0)
    for c in reversed(a):
        v = v*x+c
    return v


def shift(a, x, step):
    """Power coefficients after x + step*t substitution."""
    return [sum(a[j]*comb(j, i)*x**(j-i)*step**i for j in range(i, len(a)))
            for i in range(len(a))]


def bernstein(a, l, h):
    n = len(a)-1
    d = shift(a, l, h-l)
    return [sum(d[i]*comb(k, i)/comb(n, i) for i in range(k+1))
            * comb(n, k)/(h-l)**n for k in range(n+1)]


def direction(coeffs):
    if any(coeffs):
        if all(c >= 0 for c in coeffs):
            return 1
        if all(c <= 0 for c in coeffs):
            return -1
    return 0


def sign(x):
    return (x > 0) - (x < 0)


def split_intervals(q, fs, simple):
    bound = Fraction(1)
    while not all(direction(shift(q, t*bound, t)) and evaluate(q, t*bound)
                  for t in [-1, 1]):
        bound *= 2
    todo = [(-bound, bound)]
    segments = []
    while todo:
        l, h = todo.pop()
        if direction(bernstein(q, l, h)):
            segments.append((l, h, False))
            continue
        if (evaluate(q, l)*evaluate(q, h) < 0 and direction(bernstein(derivative(q), l, h))
                and all(not f or evaluate(g, l)*evaluate(g, h) < 0
                        or direction(bernstein(f, l, h)) for f, g in zip(fs, simple))):
            segments.append((l, h, True))
            continue
        mid = (l+h)/2
        while not evaluate(q, mid):
            mid = (l+mid)/2
        todo.extend([(mid,h), (l,mid)])
    return bound, segments


def rat(v):
    v = Fraction(v)
    if v.denominator == 1:
        return str(v.numerator) if v >= 0 else f'({v.numerator})'
    return f'({v.numerator}/{v.denominator})'


def power(base, i):
    return base if i == 1 else f'({base})^{i}'


def series(a, make_term):
    return ' + '.join(f'{rat(c)} * ({make_term(i)})' for i, c in enumerate(a) if c) or '0'


def polynomial(a):
    return ' + '.join(f'C ({rat(c)} : ℝ) * X^{i}' for i, c in enumerate(a) if c) or '0'


def expression(a, variable='x'):
    return series(a, lambda i: power(variable, i))


def listlit(items):
    return '[' + ', '.join(items) + ']'


def positive_proof(f, l, h, target, simp_defs):
    if l is None or h is None:
        endpoint, step = (h, -1) if l is None else (l, 1)
        coeff = shift(f, endpoint, step)
        base = f'{rat(h)} - x' if l is None else f'x - {rat(l)}'
        basis = lambda i: power(base, i)
    else:
        coeff = bernstein(f,l,h)
        n = len(f)-1
        basis = lambda i: f'({power(f"x - {rat(l)}", i)}) * ({power(f"{rat(h)} - x", n-i)})'
    d = direction(coeff)
    assert d
    expansion = series([v*d for v in coeff], basis)
    lhs = target if d == 1 else f'-({target})'
    conditions = []
    if l is not None:
        conditions.append(f'have hL : 0 < x - {rat(l)} := sub_pos.mpr hl')
    if h is not None:
        conditions.append(f'have hH : 0 < {rat(h)} - x := sub_pos.mpr hh')
    return conditions + [
        f'have ident : {lhs} = {expansion} := by norm_num [{simp_defs}] <;> ring_nf <;> simp',
        f'have hp : 0 < {lhs} := by rw [ident]; positivity',
        'linarith']


def generate(fs):
    simple = [exact(f,gcd(f,derivative(f))) if f else ONE for f in fs]
    q = ONE
    for g in simple:
        q = mul(q,exact(g,gcd(q,g)))
    bound, parts = split_intervals(q,fs,simple)
    boxes = [(l,h) for l,h,root in parts if root]
    out = ['import CertifiedTopology.Isolation', '', 'open CertifiedTopology Polynomial Set',
           'namespace CertifiedDiagram', 'noncomputable section']
    line = out.append
    def proof(lines, indent=2):
        out.extend(' '*indent + s for s in lines)
    names = [f'p{i}' for i in range(len(fs))]
    for name, f in zip(names,fs):
        line(f'def {name} : Polynomial ℝ := {polynomial(f)}')
    line(f'def inputs : List (Polynomial ℝ) := {listlit(names)}')
    line(f'def q : Polynomial ℝ := {polynomial(q)}')
    line('')
    cuts = [f'box{i}.root' for i in range(len(boxes))]
    for i,(l,h) in enumerate(boxes):
        d = direction(bernstein(derivative(q),l,h))
        line(f'def box{i} : Isolation.Box q {rat(l)} {rat(h)} := by')
        proof([f'apply Isolation.isolate q (by norm_num) (by norm_num [q])',
               'left' if d == 1 else 'right', 'rintro x ⟨hl,hh⟩'])
        proof(positive_proof(derivative(q),l,h,'q.derivative.eval x','q'))
    line(f'def cuts : List ℝ := {listlit(cuts)}')
    line('private theorem coversQ (x : ℝ) (hx : q.eval x = 0) : x ∈ cuts := by')
    indexed_parts = [(None,-bound,False)] + parts + [(bound,None,False)]
    idx = 0
    for l,h,root in indexed_parts:
        if h is not None:
            proof([f'rcases lt_trichotomy x ({rat(h)} : ℝ) with hh | e | hlNext'])
            indent = 4
            line('  · ' + ('have hroot := ' + f'box{idx}.unique x ⟨hl,hh⟩ hx' if root else 'exfalso'))
        else:
            indent = 2
        if root:
            proof([f'simp [cuts,hroot]'], indent)
            idx += 1
        else:
            d = direction(bernstein(q,l,h) if l is not None and h is not None
                          else shift(q, h if l is None else l, -1 if l is None else 1))
            ineq = '0 < q.eval x' if d == 1 else 'q.eval x < 0'
            proof([f'have hn : {ineq} := by'], indent)
            proof(positive_proof(q,l,h,'q.eval x','q'),indent+2)
            proof(['linarith'],indent)
        if h is not None:
            line('  · subst x; norm_num [q] at hx')
            proof([f'have hl : ({rat(h)} : ℝ) < x := hlNext'])
    line('private theorem cover : Univariate.Covers cuts inputs := by')
    proof(['intro f hf hn x hx'])
    if fs:
        proof(['simp only [inputs,List.mem_cons,List.not_mem_nil,or_false] at hf'])
        proof(['rcases hf with ' + ' | '.join(['rfl']*len(fs))] if len(fs)>1 else ['subst f'])
        for name,f in zip(names,fs):
            if not f:
                line(f'  · exact (hn (by simp [{name}])).elim' if len(fs)>1 else f'  exact (hn (by simp [{name}])).elim')
                continue
            indent = 4 if len(fs)>1 else 2
            if len(fs)>1:
                line('  · apply coversQ')
            else:
                proof(['apply coversQ'])
            layers = []
            rest = f
            while len(rest)>1:
                g = gcd(q,rest)
                assert len(g)>1
                layers.append(g)
                rest = exact(rest,g)
            polys = [f'({expression(g)})' for g in layers]
            factors = ' * ('.join(polys + [rat(rest[0])]) + ')'*len(polys)
            proof([f'have e : {name}.eval x = ' + factors +
                   f' := by simp [{name}] <;> ring','rw [e] at hx'],indent)
            if not layers:
                proof(['norm_num at hx'],indent)
            else:
                for g in layers:
                    proof(['rcases mul_eq_zero.mp hx with h | hx',
                           f'· have idn : q.eval x = ({expression(g)}) * ({expression(exact(q,g))}) := by simp [q] <;> ring',
                           '  rw [idn,h,zero_mul]'],indent)
                proof(['norm_num at hx'],indent)
    else:
        proof(['simp [inputs] at hf'])
    rows, descriptions = [], []
    signnames = {-1:'.below',0:'.on',1:'.above'}
    def row(region,witness,values,inside,checks,description):
        name = f'row{len(rows)}'
        signs = list(map(signnames.get,values))
        rows.append(name)
        descriptions.append({'cell':description,'signs':values})
        line(f'def {name} : Isolation.Label inputs where')
        proof([f'region := {region}',f'signs := {listlit(signs)}',f'witness := {witness}',
               'inside := by'])
        proof(inside,4)
        proof(['checkSigns := by'])
        proof(checks,4)
    for i in range(len(boxes)+1):
        lo = f'(some {cuts[i-1]})' if i else 'none'
        hi = f'(some {cuts[i]})' if i<len(boxes) else 'none'
        sample = (boxes[i-1][1]+boxes[i][0])/2 if 0<i<len(boxes) else (
            boxes[i-1][1] if i else boxes[0][0] if boxes else Fraction(0))
        inside = ['simp [Univariate.contains,Slice.Contains,Aff.eval]']
        for j in [i-1,i]:
            if 0<=j<len(boxes):
                inside.insert(0,f'have ⟨hL{j},hH{j}⟩ := box{j}.interior')
        inside[-1] += ' <;> (try constructor) <;> linarith'
        row(f'.sector {lo} {hi}',rat(sample),[sign(evaluate(f,sample)) for f in fs],inside,
            ['norm_num [inputs,side'+ ''.join(','+name for name in names) +']'],
            {'sector':[i-1 if i else None,i if i<len(boxes) else None],'sample':str(sample)})
        if i==len(boxes):
            break
        l,h = boxes[i]
        checks = [f'let x := box{i}.root',f'have ⟨hl,hh⟩ := box{i}.interior',
                  f'change {rat(l)} < x at hl',f'change x < {rat(h)} at hh']
        values=[]
        for j,(name,f,g) in enumerate(zip(names,fs,simple)):
            if not f:
                v=0
                checks.append(f'have e{j} : {name}.eval x = 0 := by simp [{name}]')
            elif evaluate(g,l)*evaluate(g,h)<0:
                v=0
                gp = f'({polynomial(g)} : Polynomial ℝ)'
                checks.extend([f'have e{j} : {name}.eval x = 0 := by',
                    f'  obtain ⟨z,hz,hg⟩ := Isolation.crossing (l := {rat(l)}) (h := {rat(h)}) {gp} (by norm_num) (by norm_num)',
                    f'  have eg : ({expression(g,"z")}) = 0 := by simpa using hg',
                    f'  have idq : q.eval z = ({expression(g,"z")}) * ({expression(exact(q,g),"z")}) := by simp [q] <;> ring',
                    f'  have ez : z = x := box{i}.unique z hz (by rw [idq,eg,zero_mul])',
                    f'  have idf : {name}.eval z = ({expression(g,"z")}) * ({expression(exact(f,g),"z")}) := by simp [{name}] <;> ring',
                    '  rw [← ez,idf,eg,zero_mul]'])
            else:
                v=direction(bernstein(f,l,h))
                ineq = f'0 < {name}.eval x' if v==1 else f'{name}.eval x < 0'
                checks.append(f'have e{j} : {ineq} := by')
                checks.extend('  '+s for s in positive_proof(f,l,h,f'{name}.eval x',name))
            values.append(v)
        checks.append('change inputs.map (fun f => side (f.eval x) 0) = _')
        checks.append('simp [inputs,side' + ''.join(f',e{j}' +
            (f',e{j}.not_gt,e{j}.ne\'' if v==1 else '') for j,v in enumerate(values)) + ']')
        row(f'.sectionAt {cuts[i]}',cuts[i],values,['rfl'],checks,
            {'section':i,'isolating_interval':[str(l),str(h)]})
    line('def cutTable : Univariate.CutTable inputs where')
    proof(['roots := cuts', 'covers := cover', 'sorted := by'])
    for i in range(len(boxes)):
        proof([f'have ⟨l{i},h{i}⟩ := box{i}.interior'], 4)
    proof(['simp [cuts] <;> (repeat\' constructor) <;> linarith'], 4)
    line('def diagram : Isolation.Diagram inputs :=')
    proof([f'Isolation.finish cuts cutTable.sorted cutTable.covers {listlit(rows)} rfl'])
    line('end\nend CertifiedDiagram')
    return '\n'.join(out)+'\n', descriptions


def quadratic_family(coeffs):
    a, b, c = coeffs
    b2, ac = mul(b,b), mul(a,c)
    discr = poly((b2[i] if i < len(b2) else 0) - 4*(ac[i] if i < len(ac) else 0)
                 for i in range(max(len(b2),len(ac))))
    source, rows = generate([a,b,c,discr])
    source = source.replace('import CertifiedTopology.Isolation', 'import CertifiedTopology.Family')
    source += """
namespace CertifiedDiagram
open CertifiedTopology Quadratic
noncomputable section
def family : Family := ⟨p0,p1,p2⟩
theorem family_projection : family.projection = inputs := by
  have hd : discrim p0 p1 p2 = p3 := by
    apply Polynomial.funext
    intro x
    norm_num [p0,p1,p2,p3,discrim] <;> ring
  simp only [Family.projection,family,inputs,hd]

def familyDiagram : Isolation.Diagram family.projection where
  rows := diagram.rows
  partition := diagram.partition
  valid := by rw [family_projection]; exact diagram.valid
theorem fibers {row} (hr : row ∈ familyDiagram.rows) {x} (hx : Univariate.contains row.1 x) :
    Realizes (family.value x) (Family.kindOfSigns row.2) :=
  family.diagram_fiber familyDiagram hr hx
end
end CertifiedDiagram
"""
    for row in rows:
        sa,sb,sc,sd = row['signs']
        if sa:
            kind = {-1:'empty',0:'point',1:'twoPoints'}[sd]
        elif sb:
            kind = 'point'
        else:
            kind = 'empty' if sc else 'line'
        row['fiber'] = kind
    kinds = listlit('.' + row['fiber'] for row in rows)
    source += f'''
theorem CertifiedDiagram.reportedKinds :
    CertifiedDiagram.familyDiagram.rows.map (fun r => CertifiedTopology.Quadratic.Family.kindOfSigns r.2) =
      {kinds} := rfl
'''
    return source, rows


def check(command):
    result = subprocess.run(command, cwd=ROOT, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, text=True)
    if result.returncode:
        sys.stderr.write(result.stdout)
        raise SystemExit(result.returncode)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input', type=Path, help='JSON array of polynomials in ascending power order')
    parser.add_argument('--lean', type=Path, help='save the verified Lean certificate')
    parser.add_argument('--quadratic-family', action='store_true',
                        help='interpret input as [a(x), b(x), c(x)] for a(x)y²+b(x)y+c(x)=0')
    args = parser.parse_args()
    try:
        data = json.loads(args.input.read_text(), parse_float=Fraction)
    except (ValueError, OSError) as error:
        parser.error(str(error))
    if not isinstance(data,list) or any(not isinstance(f,list) for f in data):
        parser.error('expected an array of coefficient arrays')
    if any(type(c) not in (int, str, Fraction) for f in data for c in f):
        parser.error('coefficients must be integers, decimal numbers or rational strings')
    try:
        fs = [poly(f) for f in data]
    except (ValueError, ZeroDivisionError) as error:
        parser.error(str(error))
    if args.quadratic_family and len(fs) != 3:
        parser.error('quadratic family input requires three coefficient arrays')
    source, rows = quadratic_family(fs) if args.quadratic_family else generate(fs)
    target = 'CertifiedTopology.Family' if args.quadratic_family else 'CertifiedTopology.Isolation'
    check(['lake', 'build', target])
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp)/'Certificate.lean'
        path.write_text(source)
        check(['lake', 'env', 'lean', str(path)])
    if args.lean:
        args.lean.write_text(source)
    print(json.dumps(rows,indent=2))


if __name__ == '__main__':
    main()
