import sage
from sage.all import *

from .sassy import verbose_iter


def isomorphic(des1, des2):
    return IncidenceStructure(des1).is_isomorphic(IncidenceStructure(des2))


def simple_designs(t, v, k, lamb, verbosity=0):
    """Search for all simple t-(v,k,lamb) designs.
    Method: one-point extension by integer-programming."""
    if k <= 2:
        if verbosity > 0:
            print(f'Outsourcing {t}-({v}, {k}, {lamb}) to GAP...')
        return gap_designs(t, v, k, lamb)
    designs = []
    if any(lamb * binomial(v-i, t-i) % binomial(k-i, t-i) != 0 for i in range(0, t)):
        return designs
    num_blocks = lamb * binomial(v, t) / binomial(k, t)
    if t == 0:
        designs.extend(Subsets(Subsets(v, k), lamb))
    else:
        contractions = simple_designs(t-1, v-1, k-1, lamb, verbosity=verbosity-1)
        for con in verbose_iter(contractions, verbosity > 0, f'Trying to extend to {v} points...'):
            p = MixedIntegerLinearProgram()
            x = p.new_variable(binary=True)
            for block in con:
                p.add_constraint(x[block | Set([v])] == 1)
            for t_set in Subsets(v, t):
                p.add_constraint(sum(x[k_set] for k_set in Subsets(v, k) if t_set.issubset(k_set)) == lamb)

            while True:
                try:
                    p.solve()
                except sage.numerical.mip.MIPSolverException as e:
                    # attempt to read the error message produced by different possible MILP backends
                    if 'no feasible solution' in str(e) or 'infeasible' in str(e):
                        break
                    raise e
                values = p.get_values(x)
                soln = [k_set for k_set in Subsets(v, k) if values[k_set] > 0]
                designs.append(soln)
                p.add_constraint(sum(x[k_set] for k_set in soln) <= num_blocks - 1)
    output = []
    for des in verbose_iter(designs, verbosity > 0, 'Computing canonical forms...'):
        des = IncidenceStructure(des)
        des.relabel(des.canonical_label())
        if des not in output:
            output.append(des)
    return [[Set(block) for block in des.blocks()] for des in output]


def gap_designs(t, v, k, lamb):
    return [[Set([int(x) for x in block]) for block in des.attribute('blocks')]
            for des in gap(f'BlockDesigns(rec(v:={v},blockSizes:=[{k}],tSubsetStructure:=rec(t:={t},'
                           f'lambdas:=[{lamb}]),blockMaxMultiplicities:=[1]))')]
