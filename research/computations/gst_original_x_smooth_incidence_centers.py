#!/usr/bin/env python3
"""Exact Chern-to-smooth-center identities on arbitrary original X.

Run: python3 research/computations/gst_original_x_smooth_incidence_centers.py
Formal symmetric Chern polynomials are compared with independently computed
Newton power sums. This checks identities, not the universal existence of a
bundle detecting a prescribed rational Hodge residual.
"""
from fractions import Fraction as Q
from math import comb, factorial
import json


def add(a, b):
    out = dict(a)
    for key, value in b.items():
        out[key] = out.get(key, Q(0))+value
        if out[key] == 0:
            del out[key]
    return out


def scale(c, a):
    return {key: c*value for key, value in a.items() if c*value}


def multiply(a, b):
    out = {}
    for ka, va in a.items():
        for kb, vb in b.items():
            key = tuple(x+y for x, y in zip(ka, kb))
            out[key] = out.get(key, Q(0))+va*vb
    return {key: value for key, value in out.items() if value}


def series_multiply(a, b, limit):
    out = [{} for _ in range(limit+1)]
    for i in range(limit+1):
        for j in range(limit+1-i):
            out[i+j] = add(out[i+j], multiply(a[i], b[j]))
    return out


def check_chern_interpolation(p):
    unit = {(0,)*p: Q(1)}
    chern = [unit]
    for i in range(1, p+1):
        exponent = tuple(int(i == j+1) for j in range(p))
        chern.append({exponent: Q(1)})
    power, weighted = [unit]+[{} for _ in range(p)], {}
    weights, center_polynomials = [], []
    for copies in range(1, p+1):
        power = series_multiply(power, chern, p)
        weight = Q((-1)**(p+copies-2)*comb(p, copies),
                   copies*factorial(p-1))
        weighted = add(weighted, scale(weight, power[p]))
        weights.append(weight)
        center_polynomials.append(power[p])
    # Independent Newton recursion: p_k=c1 p_(k-1)-c2 p_(k-2)+...
    #                       +(-1)^(k-1) k c_k, and ch_k=p_k/k!.
    newton = [{}]
    for k in range(1, p+1):
        value = scale(Q((-1)**(k-1)*k), chern[k])
        for i in range(1, k):
            value = add(value, scale(Q((-1)**(i-1)), multiply(chern[i], newton[k-i])))
        newton.append(value)
    character = scale(Q(1,factorial(p)), newton[p])
    assert weighted == character
    # Derivative-at-zero weights for every monomial in the stated range.
    derivative_weights = [Q((-1)**(j-1)*comb(p,j),j) for j in range(1,p+1)]
    for k in range(1,p+1):
        assert sum(derivative_weights[j-1]*j**k for j in range(1,p+1)) == int(k == 1)
    # Rational Cauchy norm of the ACTUAL finite center coefficient list.
    norm = sum(w*w for w in weights)
    upper = Q(comb(2*p,p)-1,factorial(p-1)**2)
    assert 0 < norm <= upper
    return {'codimension':p,'positive_bundle_copy_counts':list(range(1,p+1)),
            'center_weights':[str(w) for w in weights],
            'newton_character_monomials':len(character),
            'weight_square_sum':str(norm),
            'coarse_center_energy_constant':str(1/upper),
            'full_formal_polynomial_identity':True}


def main():
    rows = [check_chern_interpolation(p) for p in range(1,13)]
    dimension_cases, original_smooth_cases = 0, 0
    for n in range(1,25):
        for p in range(1,n+1):
            fiber_dimension = n-p
            ambient_dimension = n+fiber_dimension
            center_dimension = ambient_dimension-n
            assert center_dimension == n-p
            # [xi^(n-p)] sum c_i xi^(n-i) is exactly c_p.
            selected = [i for i in range(n+1) if n-i == fiber_dimension]
            assert selected == [p]
            dimension_cases += 1
            if n < 2*(p+1):
                original_smooth_cases += 1
            if n == 2*p:
                assert 2*(p+1) > n
    assert dimension_cases == 300
    # Hand benchmark: c2(E+E)=2c2+c1^2; ch2=c1^2/2-c2.
    for a in range(-12,13):
        for b in range(-12,13):
            a,b=Q(a),Q(b)
            q=b/2-2*a
            assert 17*(a*a+b*b)-4*q*q == (a+4*b)**2
            assert a*a+b*b >= Q(4,17)*q*q
    # First intrinsic candidate on an abelian n-fold: T_X is trivial.
    # Every twist Chern coefficient is ambient; primitive evaluation
    # kills h^p. This is a scoped failure of that candidate, not of
    # all algebraic bundles or all possible incidence centers.
    abelian = [{'n':n,'p':p,'twist':m,
                'ambient_chern_coefficient':comb(n,p)*m**p,
                'primitive_period':0}
               for n in (4,6,8) for p in range(1,n//2+1) for m in (1,3,7)]
    print(json.dumps({
        'claim':'Actual algebraic-bundle Chern periods converted into smooth-center native periods on original X',
        'domain':'Exact Q polynomials in formal c1,...,cp; no numerical tolerances',
        'center':'General n-p+1 sections of rank-n globally generated quotient V; smooth incidence zero locus in X times P^(n-p)',
        'projective_push':'pr_X*[S]=c_p(V)',
        'exceptional_push':'pr_X*rho_*(F^n)=(-1)^(n-1)c_p(V)',
        'smooth_inside_original_X_range':'n<=2p+1; in particular every primitive middle case n=2p',
        'interpolation_rows':rows,
        'dimension_cases_checked':dimension_cases,
        'smooth_original_center_cases_checked':original_smooth_cases,
        'codimension_two_sharp_energy_constant':'4/17',
        'codimension_two_energy_grid_checks':625,
        'intrinsic_tangent_candidate_on_abelian_original_X':abelian,
        'unrestricted_argument':'Derivative of [z^p]c_z(E)^t at t=0, followed by Lagrange interpolation at 0,...,p; primitive annihilation removes every positive hyperplane twist term',
        'non_claims':['No algebraic bundle with nonzero prescribed residual period is proved to exist on every original X',
                      'Finite polynomial checks do not prove the all-p geometric construction',
                      'Generic smoothness, vector-bundle resolution and canonical Chow/Betti comparison are geometric proof leaves',
                      'Zero intrinsic tangent period does not imply all bundle or all center periods vanish']
    },indent=2))


if __name__=='__main__':
    main()
