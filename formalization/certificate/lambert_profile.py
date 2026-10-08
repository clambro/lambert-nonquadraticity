#!/usr/bin/env python3
"""Reproduce the 400-cell Lambert profile certificate using exact rational arithmetic.

Usage:
    python3 certificate/lambert_profile.py --check
    python3 certificate/lambert_profile.py --output /tmp/ProfileData.lean
    python3 certificate/lambert_profile.py --h 500 --k 27 --L 516 --s 41 --json

The script is a certificate producer, not a proof checker. Lean independently
checks the selected affine intervals, disjointness, and rounded integrals.
No generated cell, endpoint table, or input Lean file is used by the producer.

The finite search starts at n/N=5, takes the union of window-boundary grids,
refines crossings of internal maxima and zeros of the winning correction,
and selects the largest midpoint correction (ties use the first presentation).
It deliberately retains redundant grid cuts: these determine the exact rounding
and reproduce the existing certificate. Retuning emits JSON; changing the Lean
parameters also requires updating Orbit and ProfileExpressions.
"""
from fractions import Fraction as Q
from functools import cache
from pathlib import Path
import argparse
import json
import sys

def linear(a, b=0):
    return ('lin', Q(a), Q(b))


def deficit(k, capacity=1):
    return ('def', k, capacity)


def residue_prefix(m, d):
    return ('res', m, d)


def add(f, g):
    return ('add', f, g)


def sub(f, g):
    return ('sub', f, g)


def maximum(f, g):
    return ('max', f, g)


def presentation_exponent(h, A, b, d, s):
    """The bordered filtration bound in ProfileExpressions.lean."""
    residue = sub(residue_prefix(s+h+A, d), residue_prefix(s, d))
    tail = maximum(sub(linear(b+h+d), maximum(linear(b), linear(0, 1))), linear(0))
    correction = maximum(deficit(h+d+A, 2),
                         maximum(sub(sub(linear(h), residue), tail), linear(0)))
    return sub(add(add(linear(h), deficit(h+d)), deficit(A)), correction)


def transport_exponent(h, A, d):
    """The cyclotomic exponent incurred by the bordered transposition."""
    return sub(sub(add(deficit(h+A), deficit(d)), deficit(h+d)), deficit(A))


def expressions(h, k, length, shift):
    d, s = length-h, shift
    if not (h > 0 and k >= 0 and 0 <= d <= s <= k+d):
        raise ValueError("require h>0, k>=0, and 0<=L-h<=s<=k+L-h")
    states = [(0,k,d,s), (d,s,0,k), (s,k+d,s-d,0),
              (0,s-d,d,k+d), (d,k+d,0,s-d), (s-d,k,s,d)]
    t,u,v = transport_exponent(h,0,d),transport_exponent(h,k,k+d),transport_exponent(h,s,s-d)
    raw = [presentation_exponent(h,*state) for state in states]
    transported = [raw[0],sub(raw[1],t),sub(raw[2],u),
                   sub(sub(raw[3],v),u),sub(sub(sub(raw[4],u),v),t),
                   sub(sub(raw[5],v),t)]
    base = sub(add(linear(h),deficit(length)),deficit(length,2))
    return [sub(base,maximum(e,linear(0))) for e in transported], states


def affine(e, x, lower, upper, crossings):
    """Affine germ at x; collect crossings of internal max branches in the cell."""
    op = e[0]
    if op == 'lin':
        return e[1:]
    if op == 'def':
        k,c = e[1:]
        m = int(Q(k,c)/x)
        return Q(m*k), Q(-m*(m+1)*c,2)
    if op == 'res':
        M,d = e[1:]
        if x <= d or M <= x:
            return Q(0),Q(0)
        m = int(Q(M)/x)
        # The prefix's positive-part branch changes at (M-d)/m;
        # all such cuts are already in the initial grid.
        if M-d-m*x >= 0:
            return Q(M-m*d),Q(-1)
        return Q(-(m-1)*d),Q(m-1)
    f = affine(e[1],x,lower,upper,crossings)
    g = affine(e[2],x,lower,upper,crossings)
    if op == 'add':
        return f[0]+g[0],f[1]+g[1]
    if op == 'sub':
        return f[0]-g[0],f[1]-g[1]
    if f[1] != g[1]:
        q = (g[0]-f[0])/(f[1]-g[1])
        if lower < q < upper:
            crossings.add(q)
    return f if f[0]+f[1]*x >= g[0]+g[1]*x else g


def generate(h=500, k=27, length=516, shift=41, minimum=Q(5)):
    ex, states = expressions(h,k,length,shift)
    lo, hi = minimum,Q(k+length)
    if not 0 < lo < hi:
        raise ValueError("require 0<minimum<k+L")
    points = {lo,hi}
    def addpoint(q):
        if lo < q < hi:
            points.add(q)
    def grid(K,c=1):
        for m in range(1,int(Q(K,c)/lo)+1):
            addpoint(Q(K,c*m))
    @cache
    def walk(e):
        if e[0] == 'def':
            grid(*e[1:])
        elif e[0] == 'res':
            M,d=e[1:]
            addpoint(Q(d))
            grid(M)
            grid(M-d)
        elif e[0] != 'lin':
            walk(e[1]);walk(e[2])
    for e in ex:
        walk(e)
    # Window endpoints and row/pole counts supply a common refinement;
    # this is derived from the six presentations, not a saved cell table.
    boundaries = {h}
    for A,b,d,s in states:
        boundaries.update((A,b,d,s,h+A,h+d,b+h+d,s+h+A))
    for K in boundaries:
        grid(K)
    while True:
        before = len(points)
        xs = sorted(points)
        for lower,upper in zip(xs,xs[1:]):
            mid = (lower+upper)/2
            fs = [affine(e,mid,lower,upper,points) for e in ex]
            j = max(range(6),key=lambda j:fs[j][0]+fs[j][1]*mid)
            a,b = fs[j]
            if b and lower < -a/b < upper:
                points.add(-a/b)
        if len(points) == before:
            break
    cells = []
    xs = sorted(points)
    for lower,upper in zip(xs,xs[1:]):
        mid = (lower+upper)/2
        fs = [affine(e,mid,lower,upper,set()) for e in ex]
        j = max(range(6),key=lambda j:fs[j][0]+fs[j][1]*mid)
        a,b = fs[j]
        if a+b*mid <= 0:
            continue
        assert a+b*lower >= 0 and a+b*upper >= 0
        integral = a*(upper**2-lower**2)/2+b*(upper**3-lower**3)/3
        cells.append((lower,upper,j,a,b,int(integral*10**12)))
    return cells


def rational(q):
    return str(q.numerator) if q.denominator == 1 else f"({q.numerator}/{q.denominator})"


def render(cells):
    """Render the established Lean interface and its kernel-checked proofs."""
    if len(cells) != 400:
        raise ValueError("the existing Lean interface requires exactly 400 cells")
    out = ["import Lambert.Refinement.ProfileCells\n\n",
           "/-! # Exact rational certificates for the Lambert profile correction -/\n",
           "namespace Lambert\nnoncomputable section\n\n"]
    for group in range(10):
        out.append(f"private def profileCells{group} : List LambertRefinementProfileCell := [\n")
        rows=[]
        for l,u,j,a,b,mass in cells[40*group:40*(group+1)]:
            rows.append(f"  ⟨{rational(l)}, {rational(u)}, {j}, ({rational(a)}, {rational(b)}), {mass}⟩")
        out.append(",\n".join(rows)+"]\n\n")
        out.append("set_option maxRecDepth 4096 in\nset_option maxHeartbeats 4000000 in\n")
        out.append(f"private theorem profileCells{group}_valid : ∀ c ∈ profileCells{group}, c.Valid := by\n  decide +kernel\n\n")
    out.append(FOOTER)
    return ''.join(out)

FOOTER = """/-- Four hundred disjoint rational intervals certify the finite correction to the original filtration bound. -/
def lambertRefinementProfileCells : List LambertRefinementProfileCell :=
  profileCells0 ++ profileCells1 ++ profileCells2 ++ profileCells3 ++ profileCells4 ++ profileCells5 ++ profileCells6 ++ profileCells7 ++ profileCells8 ++ profileCells9

/-- Every listed profile interval passes the exact arithmetic and rounded-integral checks. -/
theorem lambertRefinementProfileCells_valid : ∀ c ∈ lambertRefinementProfileCells, c.Valid := by
  intro c hc
  simp only [lambertRefinementProfileCells, List.mem_append, or_assoc] at hc
  rcases hc with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  · exact profileCells0_valid c h0
  · exact profileCells1_valid c h1
  · exact profileCells2_valid c h2
  · exact profileCells3_valid c h3
  · exact profileCells4_valid c h4
  · exact profileCells5_valid c h5
  · exact profileCells6_valid c h6
  · exact profileCells7_valid c h7
  · exact profileCells8_valid c h8
  · exact profileCells9_valid c h9


set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
/-- The certified correction intervals are disjoint and ordered. -/
theorem lambertRefinementProfileCells_ordered :
    lambertRefinementProfileCells.Pairwise (fun c d => c.upper≤d.lower) := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
/-- The sum of the independently rounded interval integrals exceeds the required rational correction. -/
theorem lambertRefinementProfileCells_integral_numerators :
    30625855746750000000 ≤ (lambertRefinementProfileCells.map
      LambertRefinementProfileCell.integralNumerator).sum := by
  decide +kernel

end
end Lambert
"""

def main():
    parser=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--h',type=int,default=500)
    parser.add_argument('--k',type=int,default=27)
    parser.add_argument('--L',type=int,default=516)
    parser.add_argument('--s',type=int,default=41)
    parser.add_argument('--minimum',type=Q,default=Q(5))
    modes=parser.add_mutually_exclusive_group(required=True)
    modes.add_argument('--check',action='store_true')
    modes.add_argument('--output',type=Path)
    modes.add_argument('--json',action='store_true')
    args=parser.parse_args()
    cells=generate(args.h,args.k,args.L,args.s,args.minimum)
    if args.json:
        print(json.dumps([[str(l),str(u),j,str(a),str(b),mass] for l,u,j,a,b,mass in cells],indent=2))
        return
    if (args.h,args.k,args.L,args.s,args.minimum)!=(500,27,516,41,Q(5)):
        parser.error('retuned parameters require --json; the Lean expressions have fixed parameters')
    output=render(cells)
    if args.output:
        args.output.write_text(output,encoding='utf-8')
    else:
        target=Path(__file__).resolve().parents[1]/'Lambert/Refinement/ProfileData.lean'
        if target.read_bytes()!=output.encode('utf-8'):
            sys.exit('certificate differs from generated output')
        print('400 cells regenerated; Lean file matches byte for byte.')
        print(f'Rounded integral numerator sum: {sum(c[-1] for c in cells)}')

if __name__=='__main__':
    main()
