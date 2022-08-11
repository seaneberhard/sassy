import functools
import itertools

from sage.all import *
from tqdm.notebook import tqdm

from .union_find import find_orbits


class SAS:
    def __init__(self, n, sets=None):
        self.n = n
        self.vertices = set(range(1, self.n + 1))
        self.cube = Subsets(self.vertices)
        self.vertices = self.cube(self.vertices)
        self.chi = {x: len(x) for x in self.cube}
        self.ranks = None
        if sets is not None:
            for idx, s in enumerate(sets):
                s = [self.cube(x) for x in s]
                self.chi.update({x: (self.chi[x], idx) for x in s})
        self.relabel()
        self.aut = None

    def __repr__(self):
        return f'<SAS of degree {self.n} and ranks {self.ranks}>'

    def __eq__(self, other):
        return self.n == other.n and all(self.chi[x] == other.chi[x] for x in self.cube)

    def __le__(self, other):
        return self.n == other.n and all(other.chi[x] == other.chi[c[0]] for c in self.color_classes() for x in c)

    def relabel(self):
        """recompute ranks and rename colors 0,...,total_rank-1"""
        color_map = {}
        self.ranks = [0 for _ in range(self.n + 1)]
        next_color = 0
        for x in self.cube:
            if self.chi[x] not in color_map:
                color_map[self.chi[x]] = next_color
                next_color += 1
                self.ranks[len(x)] += 1
        self.chi = {x: color_map[v] for x, v in self.chi.items()}

    def image(self, perm):
        im = SAS(self.n)
        im.chi = {x: self.chi[self.cube(list(map(perm, x)))] for x in self.cube}
        im.relabel()
        return im

    def color_classes(self):
        arr = [[] for _ in range(self.total_rank())]
        for x in self.cube:
            arr[self.chi[x]].append(x)
        return arr

    def color_class(self, i):
        return [x for x in self.chi if self.chi[x] == i]

    def lower_colors(self):
        """A color is called lower if it is <= its complementary color. This method returns the lower colors."""
        cc = self.color_classes()
        return [idx for idx, c in enumerate(cc) if idx <= self.chi[self.vertices - c[0]]]

    def total_rank(self):
        return sum(self.ranks)

    def is_homogeneous(self):
        return self.n > 0 and self.ranks[1] == 1

    def automorphism_group(self):
        """Compute the (strong) automorphism group."""
        if self.aut is None:
            aut = SymmetricGroup(self.n)
            for i in range(1, self.total_rank()):
                relation = self.color_class(i)
                inc_struct = IncidenceStructure(self.vertices, relation + [self.vertices])
                aut = aut.intersection(inc_struct.automorphism_group())
            self.aut = PermutationGroup(aut.gens(), domain=range(1, self.n + 1))  # ensure degree = n
        return self.aut

    def weak_automorphism_group(self):
        """The weak automorphism group is defined to be the group of permutations of [n] permuting the color classes.
        If the scheme is schurian, this is the normalizer of the automorphism group in Sym(n).
        Warning: If the scheme is nonschurian, this may be difficult so we just return the automorphism group."""
        if self.is_schurian():
            return SymmetricGroup(self.n).normalizer(self.automorphism_group())
        else:
            return self.automorphism_group()

    def is_schurian(self):
        return self.total_rank() == num_orbits(self.automorphism_group())

    def summary(self):
        return (self.n, self.total_rank(), self.ranks, self.is_homogeneous(), self.is_schurian(),
                self.automorphism_group().structure_description())

    def separate(self, family):
        """separate off family and its opposite as their own color classes (can also be used to join)"""
        family = [self.cube(x) for x in family]
        self.chi.update({x: '*' for x in family})
        self.chi.update({self.vertices - x: '**' for x in family})
        self.relabel()
        self.aut = None

    def wl_step(self, k1=None, k2=None, k3=None, aut_aware=True, triangles_only=True, log_progress=False):
        """One step of Weisfeiler--Leman. Return rank increase."""
        old_rank = self.total_rank()
        chi = self.chi
        if triangles_only:
            upper_limit = self.n

            def ttype(x, y, z):
                if (x | y | z).issubset(x & y | x & z | y & z):  # is it a triangle?
                    return chi[y], chi[z], len(x & y & z)
                else:
                    return ()  # not a triangle
        else:
            upper_limit = self.n / 2  # only need to check full coherence up to here

            def ttype(x, y, z):
                return chi[y], chi[z], len(x & y), len(x & z), len(y & z), len(x & y & z)
        aut_classes = set_orbits(self.automorphism_group()) if aut_aware else {x: {x} for x in self.cube}
        data = {a: dict() for a in aut_classes}
        triples = itertools.product(
            filter((lambda a: len(a) <= upper_limit) if k1 is None else (lambda a: len(a) == k1), data),
            filter((lambda a: len(a) <= upper_limit) if k2 is None else (lambda a: len(a) == k2), chi),
            filter((lambda a: len(a) <= upper_limit) if k3 is None else (lambda a: len(a) == k3), chi))
        if k2 is None and k3 is None:
            triples = filter(lambda trip: len(trip[1]) <= len(trip[2]), triples)
        description = 'full' if k1 is None and k2 is None and k3 is None else f'{k1}, {k2}, {k3}'
        for a, b, c in verbose_iter(list(triples), condition=log_progress, message=f'WL step ({description}):'):
            t = ttype(a, b, c)
            data[a][t] = data[a].get(t, 0) + 1
        chi = {a: (chi[a],) + tuple(sorted(d.items())) for a, d in data.items()}
        chi = {ai: chi[a] for a, ais in aut_classes.items() for ai in ais}
        chi = {a: (chi[a], chi[self.vertices - a]) for a in chi}  # symmetrize
        self.chi = chi
        self.relabel()
        if log_progress:
            print(f'Rank: {old_rank} --> {self.total_rank()}')
        rank_diff = self.total_rank() - old_rank
        assert rank_diff >= 0, 'WL decreased rank. That should never happen.'
        return rank_diff

    def wl_full(self, **kwargs):
        while self.wl_step(**kwargs) > 0:
            pass

    def copy(self):
        return self.image(lambda x: x)

    def dual(self):
        d = SAS(self.n)
        color_classes = self.color_classes()
        d.chi = {x: tuple(
            sum((-1) ** len(x & t) for t in c)
            for c in color_classes
        ) for x in self.cube}
        d.relabel()
        return d

    def cartesian_product(self, other):
        p = SAS(self.n + other.n)
        for x in p.cube:
            half1 = self.cube(set(xi for xi in x if xi <= self.n))
            half2 = other.cube(set(xi - self.n for xi in x if xi > self.n))
            p.chi[x] = (self.chi[half1], other.chi[half2])
        p.relabel()
        return p

    def wreath_product(self, d):
        w = SAS(self.n * d)
        for x in w.cube:
            count = [0] * self.total_rank()
            for i in range(d):
                xsub = self.cube(set(xi - self.n * i for xi in x if self.n * i < xi <= self.n * (i + 1)))
                count[self.chi[xsub]] += 1
            w.chi[x] = tuple(count)
        w.relabel()
        return w

    def to_incidence_structure(self):
        return IncidenceStructure([a | Set([-i]) for i, alpha in enumerate(self.color_classes()) for a in alpha])

    def is_isomorphic(self, other):
        """Test for (weak) isomorphism of two SAS.

        Warning: if you are sage version < 9.3 you may not bliss installed and this might be really slow. Otherwise
        it should be OK up to n=12 or so."""

        # quick checks
        if (self.ranks != other.ranks or self.is_schurian() != other.is_schurian()
                or not self.automorphism_group().is_isomorphic(other.automorphism_group())):
            return False

        return self.to_incidence_structure().is_isomorphic(other.to_incidence_structure())

    @classmethod
    def orbital_scheme(cls, group):
        return cls(group.degree(), set_orbits(group).values())

    @classmethod
    def schurian_scheme(cls, group):
        return cls.orbital_scheme(group)

    @classmethod
    def nonschurian_scheme(cls, n, i):
        if n == 8:
            half = [{1, 2, 3, 4}, {8, 1, 2, 7}, {8, 1, 3, 6}, {1, 4, 6, 7},
                    {8, 2, 3, 5}, {2, 4, 5, 7}, {3, 4, 5, 6}, {8, 5, 6, 7}]
            whole = [{1, 2, 3, 4}, {8, 1, 2, 3}, {1, 2, 4, 7}, {8, 1, 2, 7},
                     {1, 3, 4, 6}, {8, 1, 3, 6}, {1, 4, 6, 7}, {8, 1, 6, 7},
                     {2, 3, 4, 5}, {8, 2, 3, 5}, {2, 4, 5, 7}, {8, 2, 5, 7},
                     {3, 4, 5, 6}, {8, 3, 5, 6}, {4, 5, 6, 7}, {8, 5, 6, 7}]
            if i == 1:
                # summary: (8, 25, [1, 1, 3, 4, 7, 4, 3, 1, 1], True, False, '(C4 x C2) : C2')
                s = SAS.orbital_scheme(TransitiveGroup(8, 15))  # affine group (Z/8Z) : (Z/8Z)^* of order 32
                s.separate(half)
                return s
            elif i == 2:
                # summary: (8, 30, [1, 1, 4, 5, 8, 5, 4, 1, 1], True, False, '(C4 x C2) : C2')
                s = SAS.orbital_scheme(PermutationGroup(['(2,6)(4,8)', '(1,2,5,6)(3,8,7,4)', '(1,3,5,7)(2,8,6,4)']))
                s.separate(whole)
                return s
            elif i == 3:
                # summary: (8, 28, [1, 1, 3, 5, 8, 5, 3, 1, 1], True, False, 'Q8')
                s = SAS.orbital_scheme(TransitiveGroup(8, 8))  # quasidihedral group of order 16
                s.separate(half)
                return s
            elif i == 4:
                # summary: (8, 36, [1, 1, 4, 7, 10, 7, 4, 1, 1], True, False, 'Q8')
                s = SAS.orbital_scheme(PermutationGroup(['(1,2,5,6)(3,8,7,4)', '(1,3,5,7)(2,4,6,8)']))
                s.separate(whole)  # fusion
                return s
            elif i == 5:
                # summary: (8, 28, [1, 1, 3, 5, 8, 5, 3, 1, 1], True, False, 'C4 x C2')
                s = SAS.orbital_scheme(TransitiveGroup(8, 7))  # modular group of order 16
                s.separate(half)
                return s
            elif i == 6:
                # summary: (8, 51, [1, 2, 6, 10, 13, 10, 6, 2, 1], False, False, 'C4 x C2')
                s = SAS.orbital_scheme(PermutationGroup(['(2,6)(4,8)', '(1,3,5,7)(2,8,6,4)']))  # C_4 x C_2
                s.separate(whole)  # fusion
                return s
            elif i == 7:
                # summary: (8, 43, [1, 2, 5, 8, 11, 8, 5, 2, 1], False, False, 'C4 x C2')
                s = SAS.orbital_scheme(PermutationGroup(['(2,6)(4,8)', '(1,3,5,7)(2,8,6,4)']))  # C_4 x C_2
                new_colors = [s.color_class(a) + s.color_class(b)
                              for a, b in [[3, 5], [11, 16], [12, 17], [20, 22], [25, 26], [27, 31]]]
                for c in new_colors:
                    s.separate(c)
                return s
            elif i == 8:
                # summary: (8, 49, [1, 2, 6, 9, 13, 9, 6, 2, 1], False, False, 'C4 x C2')
                s = SAS.orbital_scheme(PermutationGroup(['(2,6)(4,8)', '(1,3,5,7)(2,8,6,4)']))  # C_4 x C_2
                new_colors = [s.color_class(a) + s.color_class(b) for a, b in [[9, 13], [21, 29]]]
                for c in new_colors:
                    s.separate(c)
                return s
        elif n == 9:
            if i == 1:
                # summary: (9, 24, [1, 1, 2, 3, 5, 5, 3, 2, 1, 1], True, False, 'C9 : C3')
                s = SAS.orbital_scheme(TransitiveGroup(9, 6))
                c1 = s.color_class(5) + s.color_class(6)
                c2 = s.color_class(12) + s.color_class(13)
                s.separate(c1)
                s.separate(c2)
                return s
            elif i == 2:
                # summary: (9, 26, [1, 1, 2, 4, 5, 5, 4, 2, 1, 1], True, False, 'C9 : C3')
                s = SAS.orbital_scheme(TransitiveGroup(9, 6))
                s.separate(s.color_class(9) + s.color_class(10))
                return s
            elif i == 3:
                # summary: (9, 44, [1, 2, 4, 6, 9, 9, 6, 4, 2, 1], False, False, 'C4 x C2')
                s = SAS.orbital_scheme(PermutationGroup(['(2,7)(3,5)', '(1,6)', '(1,8,6,4)(2,9,5,3)']))  # (C10 x C2) : C4
                s.separate(
                    [{1, 2, 3, 4}, {1, 2, 4, 5}, {8, 1, 2, 7}, {8, 1, 2, 9}, {1, 3, 4, 9}, {8, 1, 3, 5}, {8, 1, 3, 7},
                     {1, 4, 5, 7}, {1, 4, 9, 7}, {8, 1, 5, 9}, {8, 2, 3, 6}, {2, 4, 6, 7}, {9, 2, 4, 6}, {8, 2, 5, 6},
                     {3, 4, 5, 6}, {3, 4, 6, 7}, {8, 9, 3, 6}, {9, 4, 5, 6}, {8, 5, 6, 7}, {8, 9, 6, 7}])
                return s
            elif 4 <= i <= 11:
                return cls.nonschurian_scheme(8, i-3).cartesian_product(SAS(1))
        raise NotImplementedError()

    def refinements(self, triangles_only=True, starting_level=0, verbosity=0):
        """Search exhaustively for refinements (up to iso) obtainable by separating a single class and running WL.
        Warning: Yielded schemes may include repeats."""
        color_classes = self.color_classes()
        mono_designs = []
        for k in range(starting_level, self.n // 2 + 1):
            mono_designs.extend(list(verbose_iter(itertools.chain(
                *(designs(self.n, color_classes[idx], color_classes[:idx])
                  for idx in self.lower_colors()
                  if len(color_classes[idx][0]) == k)),
                verbosity > 1,
                f'Enumerating monochromatic designs on level {k}')))

        mono_designs = find_orbits(
            gens=self.weak_automorphism_group().gens(),
            space=[frozenset(des) for des in mono_designs],
            action=lambda g, des: frozenset([k_set.parent()(list(map(g, k_set))) for k_set in des])
        )

        for des in verbose_iter(
                mono_designs, verbosity > 0,
                f'Testing {len(mono_designs)} designs with WL...' + (' (triangles only)' if triangles_only else '')):
            k = len(next(iter(des)))
            scheme = self.copy()
            scheme.separate(des)

            small_rank = sum(scheme.ranks[:k])  # number of cells at level < k

            while True:
                # quick checks
                if sum(scheme.ranks[:k]) > small_rank:
                    break  # some lower level has split, abandon this case
                if len(set(scheme.chi[a] for a in des)) > 1:
                    break  # cell given by des has split, abandon this case
                if scheme.is_schurian():
                    yield scheme, k
                    break  # schurian scheme, therefore coherent
                # try for cheap rank increase
                if scheme.wl_step(None, 0, triangles_only=False, log_progress=verbosity > 3) > 0:
                    # triangles_only = False is acceptable because k2 = 0, so always equivalent to a triangle
                    continue
                if scheme.wl_step(k, k, triangles_only=triangles_only, log_progress=verbosity > 3) > 0:
                    continue
                # last resort: do a full WL step
                if scheme.wl_step(triangles_only=triangles_only, log_progress=verbosity > 2) == 0:
                    yield scheme, k
                    break

    @classmethod
    def all_schurians(cls, n, homogeneous_only=False):
        gps = TransitiveGroups(n) if homogeneous_only or n == 1 else SymmetricGroup(n).conjugacy_classes_subgroups()
        schurians = []
        for gp in gps:
            s = SAS.orbital_scheme(gp)
            if s.automorphism_group() == gp:  # check gp is set-closed
                schurians.append(s)
        return schurians

    @classmethod
    def find_all(cls, n, check_for_dupes=True, homogeneous_only=False, verbosity=0, **kwargs):
        kwargs['verbosity'] = verbosity

        starting_sas = [cls(n)]
        if not homogeneous_only:
            for p in Partitions(n):
                if max(p) < n:
                    s = functools.reduce(lambda x, y: x.cartesian_product(y), [SAS(m) for m in p])
                    starting_sas.append(s)

        for s in starting_sas:
            yield s
            refinements = [(s, 2)]
            for s, k in refinements:
                for t, k1 in verbose_iter(s.refinements(starting_level=k, **kwargs), verbosity > 0,
                                          f'Searching for coherent refinements of {s}\nSummary: {s.summary()}'):
                    if check_for_dupes and any(t.is_isomorphic(t1) for t1, _ in refinements):
                        continue
                    if verbosity > 0:
                        print('Found:', t)
                        print('Summary:', t.summary())
                    refinements.append((t, k1))
                    yield t



def partition_to_mult(p):
    mult = {x: 0 for x in p}
    for x in p:
        mult[x] += 1
    return mult


def num_orbits(group, k=None):
    if k is None:
        return sum(
            2 ** len(c.representative().cycle_type()) * len(c)
            for c in group.conjugacy_classes()
        ) / group.order()
    else:
        return sum(
            prod(binomial(mult.get(x, 0), m) for x, m in partition_to_mult(p).items()) * len(c)
            for c in group.conjugacy_classes()
            for mult in [partition_to_mult(c.representative().cycle_type())]
            for p in Partitions(k)
        ) / group.order()


def set_orbits(group, k=None):
    cube = Subsets(range(1, group.degree() + 1), k=k)
    return find_orbits(
        group.gens(),
        cube,
        lambda g, x: cube(set(map(g, x)))
    )


def verbose_iter(iterator, condition, message):
    if condition:
        print(message)
        return tqdm(iterator)
    return iterator


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
