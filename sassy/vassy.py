import itertools
import json
import os

from sage.all import *
from sage.combinat.partition import Partitions
from sage.groups.perm_gps.permgroup import PermutationGroup
from sage.groups.perm_gps.permgroup_named import SymmetricGroup, TransitiveGroups
from sage.numerical.mip import MixedIntegerLinearProgram, MIPSolverException

from .tools import verbose_iter
from .union_find import find_orbits


class VAS:
    def __init__(self, k, d):
        self.k, self.d = k, d
        self.vertices = set(range(1, self.d + 1))
        self.cube = list(itertools.product(range(k+1), repeat=d))
        self.chi = {x: tuple(sorted(x)) for x in self.cube}
        self.ranks = {tuple(sorted(x)): 0 for x in self.cube}
        self.relabel()
        self.aut = None
        self.weak_aut = None

    def relabel(self):
        """recompute ranks and rename colors 0,...,rank-1"""
        self.ranks = {level: 0 for level in self.ranks}
        color_map = {}
        next_color = 0
        for x in self.cube:
            if self.chi[x] not in color_map:
                color_map[self.chi[x]] = next_color
                next_color += 1
                self.ranks[tuple(sorted(x))] += 1
        self.chi = {x: color_map[v] for x, v in self.chi.items()}

    def rank(self):
        return sum(self.ranks.values())

    def __repr__(self):
        return f'<VAS of type {(self.k, self.d)} and rank {self.rank()}>'

    def __eq__(self, other):
        return self <= other <= self

    def __le__(self, other):
        if self.d != other.d or self.k != other.k:
            return False
        return all(other.chi[x] == other.chi[c[0]] for c in self.color_classes() for x in c[1:])

    def image(self, perm):
        im = VAS(self.k, self.d)
        im.separate([[perm(v) for v in cell] for cell in self.color_classes()])
        return im

    def color_classes(self):
        arr = [[] for _ in range(self.rank())]
        for x in self.cube:
            arr[self.chi[x]].append(x)
        return arr

    def color_class(self, i):
        return [x for x in self.chi if self.chi[x] == i]

    def is_homogeneous(self):
        return self.d > 0 and self.ranks[(0,) * (self.d-1) + (1,)] == 1

    def automorphism_group(self):
        """Compute the (strong) automorphism group.
        Warning: Naive implementation.
        How do you get the automorphism group of a colored incidence structure in sage? Let me know.
        """
        if self.aut is None:
            g_list = [g for g in SymmetricGroup(self.d) if all(self.chi[g(v)] == self.chi[v] for v in self.cube)]
            self.aut = PermutationGroup(g_list, domain=range(1, self.d + 1))  # ensure degree = d
        return self.aut

    def weak_automorphism_group(self):
        """The weak automorphism group is defined to be the group of permutations of [n] permuting the color classes.
        If the scheme is schurian, this is the normalizer of the automorphism group in Sym(n).
        Warning: Naive implementation."""
        if self.weak_aut is None:
            if self.is_schurian():
                self.weak_aut = SymmetricGroup(self.d).normalizer(self.automorphism_group())
            else:
                # naive implementation
                cc = self.color_classes()
                g_list = []
                for g in SymmetricGroup(self.d):
                    for c in cc:
                        c_image = [g(v) for v in c]
                        color = self.chi[c_image[0]]
                        if not all(self.chi[v] == color for v in c_image[1:]):
                            break
                    else:
                        g_list.append(g)
                self.weak_aut = PermutationGroup(g_list, domain=range(1, self.d+1))
        return self.weak_aut

    def is_schurian(self):
        return self.rank() == len(vector_orbits(self.k, self.automorphism_group()))

    def summary(self):
        aut_structure = self.automorphism_group().structure_description()
        return self.k, self.d, self.rank(), self.is_homogeneous(), self.is_schurian(), aut_structure

    def separate(self, cells):
        """separate off cells and their oppositesas their own color classes (can also be used to join)"""
        for i, cell in enumerate(cells):
            cell = [tuple(int(vi) for vi in v) for v in cell]
            complement = [tuple(self.k - vi for vi in v) for v in cell]
            self.chi.update({v: f'_{i}' for v in cell})
            self.chi.update({v: f'_{i}^c' for v in complement})
        self.relabel()
        self.aut = None
        self.weak_aut = None


    def wl_step(self, aut_aware=True, log_progress=False):
        """One step of Weisfeiler--Leman. Return rank increase."""
        raise NotImplementedError()

    def wl_full(self, **kwargs):
        while self.wl_step(**kwargs) > 0:
            pass

    def biregulate(self, aut_aware=True, log_progress=False):
        """One step of Weisfeiler--Leman. Return rank increase."""
        old_rank = self.rank()
        aut_classes = vector_orbits(self.k, self.automorphism_group()) if aut_aware else {x: {x} for x in self.cube}

        structure = {a: dict() for a in aut_classes}  # restricted structure constants
        # structure[a] will be a dictionary color --> count
        # where count = number of b's of that color such that b-a has singleton support
        # constancy of this count is equivalent to biregularity
        triples = itertools.product(aut_classes, range(self.d), range(self.k+1))
        for a, i, bi in verbose_iter(triples, condition=log_progress, message=f'Checking biregularity',
                                     total=int(len(aut_classes) * self.d * (self.k+1))):
            b = list(a)
            b[i] = bi
            b = tuple(b)
            color = self.chi[b]
            structure[a][color] = structure[a].get(color, 0) + 1

        chi = {a: (self.chi[a],) + tuple(sorted(d.items())) for a, d in structure.items()}
        chi = {ai: chi[a] for a, ais in aut_classes.items() for ai in ais}
        self.chi = chi
        self.relabel()

        if log_progress:
            print(f'Rank: {old_rank} --> {self.rank()}')
        rank_diff = self.rank() - old_rank
        assert rank_diff >= 0, 'WL decreased rank. That should never happen.'
        return rank_diff

    def copy(self):
        return self.image(lambda x: x)

    @classmethod
    def orbital_scheme(cls, k, group):
        vas = cls(k, group.degree())
        vas.separate(vector_orbits(k, group).values())
        return vas

    @classmethod
    def schurian_scheme(cls, k, group):
        return cls.orbital_scheme(k, group)

    @classmethod
    def schurian_schemes(cls, k, d, homogeneous_only=True):
        if homogeneous_only or d == 1:
            gps = TransitiveGroups(d)
        else:
            gps = SymmetricGroup(d).conjugacy_classes_subgroups()
        for gp in gps:
            s = cls.orbital_scheme(k, gp)
            if s.automorphism_group().order() == gp.order():  # check gp is k-set-closed
                yield s

    def level_reps(self):
        return level_reps(self.k, self.d)

    def refinements(self, level=0, verbosity=0):
        """Search exhaustively for refinements (up to iso) obtainable by splitting off a cell and biregulating.
        The cell will be split from the nominated level, and it is required earlier cells do not split during the
        biregulate process. Yielded schemes may include repeats."""
        reps = self.level_reps()
        lower_cells = [cell for cell in self.color_classes() if level_rep(cell[0]) in reps[:level]]
        cells_to_split = [cell for cell in self.color_classes() if reps[level] in cell]
        cells_to_separate = []
        for i, cell in enumerate(cells_to_split):
            cells_to_separate.extend(list(verbose_iter(
                designs(self.d, self.k, cell, lower_cells + cells_to_separate[:i]),
                verbosity > 1,
                f'Enumerating designs in cell [{cell[0]}]')))

        # discard isomorphs
        cells_to_separate = find_orbits(
            gens=self.automorphism_group().gens(),
            space=[frozenset(cell) for cell in cells_to_separate],
            action=lambda g, cell: frozenset(g(v) for v in cell)
        )

        for design in verbose_iter(cells_to_separate, verbosity > 0,
                                 f'Testing {len(cells_to_separate)} designs with biregulate...'):
            scheme = self.copy()
            scheme.separate([design])

            lower_rank = sum(scheme.ranks[rep] for rep in reps[:level])  # number of cells in lower levels

            while True:
                # quick checks
                if sum(scheme.ranks[rep] for rep in reps[:level]) > lower_rank:
                    break  # some lower level has split, abandon this case
                if len(set(scheme.chi[v] for v in design)) > 1:
                    break  # given cell has split, abandon this case
                if scheme.is_schurian():
                    yield scheme
                    break  # schurian scheme, therefore coherent
                # do a biregulate step
                if scheme.biregulate(log_progress=verbosity > 3) == 0:
                    yield scheme
                    break

    @classmethod
    def find_all(cls, k, d, homogeneous_only=False, verbosity=0, **kwargs):
        raise NotImplementedError()

    @classmethod
    def nonschurian_scheme(cls, k, d, i):
        """Census of known nonschurian examples. Cartesian products of smaller examples are excluded."""
        filename = os.path.join(os.path.abspath(os.path.dirname(__file__)), 'library', 'vas', f'{k}-{d}-{i}.json')
        try:
            return cls.load(filename)
        except FileNotFoundError:
            pass
        raise NotImplementedError(f'{k}-{d}-{i} is not in the library')

    @classmethod
    def nonschurian_schemes(cls, k, d):
        """Census of known nonschurian examples. Cartesian products of smaller examples are excluded."""
        for i in itertools.count(1):
            try:
                yield cls.nonschurian_scheme(k, d, i)
            except NotImplementedError:
                return

    def save(self, filename):
        with open(filename, 'w') as f:
            json.dump(self.color_classes(), f)

    @classmethod
    def load(cls, filename):
        with open(filename, 'r') as f:
            color_classes = json.load(f)
        color_classes = [[tuple(v) for v in cell] for cell in color_classes]
        k = max(cell[0][0] for cell in color_classes if len(cell) == 1)  # some cell is [(k,...,k)]
        d = len(color_classes[0][0])
        vas = cls(k, d)
        vas.separate(color_classes)
        return vas


def vector_orbits(k, group):
    d = group.degree()
    cube = itertools.product(range(k+1), repeat=d)
    return find_orbits(group.gens(), cube, lambda g, x: g(x))


def diff_type(v, w):
    return tuple(sorted(vi - wi for vi, wi in zip(v, w)))


def partition_to_rep(p):
    rep = ()
    for x, mult in enumerate(p):
        rep += (x,) * mult
    return rep


def level_rep(v):
    k = max(v)
    p = sorted([v.count(i) for i in range(k+1)])[::-1]
    return partition_to_rep(p)


def level_reps(k, d):
    """List of representatives of Sym(k+1)-orbits of levels"""
    return sorted([partition_to_rep(p) for p in Partitions(d, max_length=k + 1)], key=max)


def designs(d, k, cell, other_cells):
    """Search for all 'designs' in the given cell. By convention we only look for <= half-sized designs. A design
    is defined to be a subset of the cell such that for every cell2 in other_cells, the bipartite graphs defined by
    cell and other_cells and a given support-one difference type are all biregular. This definition is analogous to the
    definition of a combinatorial t-design. We assume that the initial cell is a already a design in this sense."""
    constraints = {}

    lower_elts = set(b for other_cell in other_cells for b in other_cell)

    for a in cell:
        for i in range(d):
            for bi in range(0, k+1):
                b = list(a)
                b[i] = bi
                b = tuple(b)
                if b in lower_elts:
                    if b not in constraints:
                        constraints[b] = []
                    constraints[b].append(a)

    constraints = list(constraints.values())
    # constraints indicate that we should be X-Y biregular against some lower cell
    # In the case of the original cell we have X = len(row), so Y = len(row) * len(lower_cell) / len(cell).
    # Hence in the case of the new cell we have Y = same and X = len(row) * len(new_cell) / len(cell)
    # Therefore the size of the new cell must be divisible by all the len(cell) / gcd(len(row), len(cell))
    m = lcm([len(cell) / gcd(len(cell), len(con)) for con in constraints])
    for size in range(m, len(cell) // 2 + 1, m):
        p = MixedIntegerLinearProgram()
        x = p.new_variable(binary=True)
        for row in constraints:
            p.add_constraint(sum(x[i] for i in row) == len(row) * size / len(cell))
        yield from gen_01_solns(p, x)


def gen_01_solns(p, x):
    """Generate all binary solutions to IP given by p with variable x. It is assumed that the solutions form an
    antichain, so that each previous solution can be avoided by adding one constraint."""
    while True:
        try:
            p.solve()
        except MIPSolverException as e:
            # attempt to read the error message produced by different possible MILP backends
            if 'no feasible solution' in str(e) or 'infeasible' in str(e):
                break
            raise e
        values = p.get_values(x)
        soln = [v for v in x.keys() if values[v] > 0]
        yield soln
        p.add_constraint(sum(x[v] for v in soln) <= len(soln) - 1)
