class UnionFind:
    def __init__(self, X):
        self.parent = {x: x for x in X}
        self.rank = {x: 0 for x in X}
        self.size = {x: 1 for x in X}

    def find(self, x):
        y = self.parent[x]
        if self.parent[y] != y:
            y = self.parent[x] = self.find(y)
        return y

    def union(self, x, y):
        x, y = self.find(x), self.find(y)
        if x == y:
            return
        if self.rank[x] < self.rank[y]:
            x, y = y, x
        elif self.rank[x] == self.rank[y]:
            self.rank[x] += 1
        self.parent[y] = x
        self.size[x] += self.size[y]
        del self.rank[y]

    def reps(self):
        return set(self.rank)

    def __len__(self):
        return len(self.reps())

    def __iter__(self):
        return iter(self.reps())


def find_orbits(gens, space, action):
    """find orbits of a general group action"""
    uf = UnionFind(space)
    for g in gens:
        for x in space:
            y = action(g, x)
            uf.union(x, y)
    orbits = {rep: set() for rep in uf.reps()}
    for x in space:
        orbits[uf.find(x)].add(x)
    return orbits


# Dual structure
class PartitionRefinement:
    def __init__(self, X):
        X = set(X)
        self.clr = {x: 0 for x in X}
        self.next_clr = 1
        self.part = {0: X}

    def find(self, x):
        return self.clr[x]

    def split(self, subset):
        new_clr = {}
        for x in subset:
            c = self.find(x)
            if c not in new_clr:
                new_clr[c] = self.next_clr
                self.part[self.next_clr] = set()
                self.next_clr += 1
            self.clr[x] = new_c = new_clr[c]
            self.part[c].remove(x)
            self.part[new_c].add(x)
        for c in new_clr:
            if len(self.part[c]) == 0:
                del self.part[c]
