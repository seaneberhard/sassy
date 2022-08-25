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
    space = list(space)
    uf = UnionFind(space)
    for g in gens:
        for x in space:
            y = action(g, x)
            uf.union(x, y)
    orbits = {rep: set() for rep in uf.reps()}
    for x in space:
        orbits[uf.find(x)].add(x)
    return orbits
