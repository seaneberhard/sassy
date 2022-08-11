from sage.all import *


def designs(n, color1, other_colors):
    """Search for all 'designs' in the given color. By convention we only look for <= half-sized designs.
    A design in color 1 is a set of 1-colored edges such that every edge of every edge of every other color is contained
    in a constant number of edges of the design. This definition generalizes the concept of a combinatorial t-design."""
    k = len(color1[0])
    homogeneous = len([c for c in other_colors if len(c[0]) == 1]) == 1
    if k == 2 and homogeneous:
        # seems to be better to use simple backtracking to look for regular graphs
        yield from regular_graphs(n, container=color1)
        return

    for size in range(1, len(color1) // 2 + 1):
        p = MixedIntegerLinearProgram()
        x = p.new_variable(binary=True)
        d = p.new_variable(integer=True)
        p.add_constraint(sum(x[k_set] for k_set in color1) == size)
        for i, color2 in enumerate(other_colors):
            for t_set in color2:
                p.add_constraint(sum(x[k_set] for k_set in color1 if t_set.issubset(k_set)) == d[i])

        while True:
            try:
                p.solve()
            except sage.numerical.mip.MIPSolverException as e:
                # attempt to read the error message produced by different possible MILP backends
                if 'no feasible solution' in str(e) or 'infeasible' in str(e):
                    break
                raise e
            values = p.get_values(x)
            soln = [k_set for k_set in color1 if values[k_set] > 0]
            yield soln
            p.add_constraint(sum(x[k_set] for k_set in soln) <= size - 1)


def regular_graphs(n, d=None, container=None):
    """Generate all d-regular graphs on [1..n] (or contained in container) by backtracking."""
    if d is None:
        for d in range(1, floor(len(container) / n) + 1):
            yield from regular_graphs(n, d, container)
        return
    if n * d % 2 != 0:
        return
    if container is None:
        container = Subsets(n, 2)

    def recursor(deg, start_index):
        if any(d < 0 for d in deg):
            return
        if all(d == 0 for d in deg):
            yield set()
            return
        for i in range(start_index, len(container)):
            e = container[i]
            for v in e:
                deg[v - 1] -= 1
            for graph in recursor(deg, start_index=i + 1):
                yield {e} | graph
            for v in e:
                deg[v - 1] += 1

    yield from recursor([d] * n, 0)
