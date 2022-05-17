import itertools
from copy import deepcopy
from sage.all import *
from collections import Counter
from tqdm import tqdm

G = Graph(r"LJ]lmZRnn]]\v[")
G = graphs.ClebschGraph()
G = graphs.SchlaefliGraph()
G = G.canonical_label()
automs = G.automorphism_group()
nautoms = automs.order()

def defines_bipartite_graph(X, v1, v2):
    if isinstance(X, Graph):
        if not X.is_subgraph(G, induced=True):
            X = G.subgraph_search(X, induced=True)
            assert uniquely_embeds(X)
        if X is None: return False
        X = X.vertices()
    if v1==v2:
        ref_neighborhood = neighbors(v1, X)
        for v in G.vertices():
            if v == v1: continue
            if neighbors(v, X) == ref_neighborhood: return False
    else:
        ref1 = neighbors(v1, X)
        ref2 = neighbors(v2, X)

        if ref1 == ref2: return False

        class1 = []
        class2 = []

        for v in G.vertices():
            neighborhood = neighbors(v, X)
            if neighborhood == ref1: class1.append(v)
            if neighborhood == ref2: class2.append(v)

        if len(G.subgraph(class1).edges()) != 0: return False
        if len(G.subgraph(class2).edges()) != 0: return False
        if len(G.subgraph(class1+class2).edges()) not in [0, len(class1)*len(class2)]: return False

    return True

def graph_to_string(H):
    alphabet = '0123456789abcdefghijklmnopqrstuvwxyz'
    H = H.canonical_label()
    return f"{alphabet[H.order()]}:{''.join([f'{alphabet[v1]}{alphabet[v2]}' for v1,v2,_ in H.edges()])}"

def neighbors(v, X):
    return tuple(sorted([x for x in G.neighbors(v) if x in X]))

def defines_unique_neighborhoods(X):
    if isinstance(X, Graph):
        if not X.is_subgraph(G, induced=True):
            X = G.subgraph_search(X, induced=True)
            assert uniquely_embeds(X)
        if X is None: return False
        X = X.vertices()
    neighborhoods = []
    for v in G.vertices():
        neighborhood = neighbors(v, X)
        if neighborhood in neighborhoods: return False
        neighborhoods.append(neighborhood)
    return True

def uniquely_embeds(H):
    if isinstance(H, list) or isinstance(H, tuple): H = G.subgraph(H)
    if not H.is_subgraph(G, induced=True): H = G.subgraph_search(H, induced=True)
    if H is None: return False
    nsubgraphs = G.subgraph_search_count(H, induced=True)
    if nsubgraphs > nautoms: return False
    subautoms = [tuple(sorted([P.dict()[h] for h in H.vertices()])) for P in automs]
    nsubautoms = len(set(subautoms))*H.automorphism_group().order()
    return nsubautoms == nsubgraphs

def basic_condition(H):
    return uniquely_embeds(H) and defines_unique_neighborhoods(H)

def pikhurko_clebsch_condition(H):
    if basic_condition(H):
        assert G.subgraph_search_count(H, induced=True) == nautoms

        for v in H.vertices():
            Hc = deepcopy(H)
            Hc.delete_vertex(v)
            if not uniquely_embeds(Hc): return False

        H = G.subgraph_search(H, induced=True)

        for v in G.vertices():
            for X in itertools.combinations(H.vertices(), H.order()-1):
                if defines_bipartite_graph(X, v, v): break
            else:
                return False

        for v1, v2 in itertools.combinations(G.vertices(), 2):
            for X in itertools.combinations(H.vertices(), H.order()-1):
                if defines_bipartite_graph(X, v1, v2): break
            else:
                return False

            return True
    return False

def pikhurko_clebsch_condition_plus(H):
    if basic_condition(H):
        assert G.subgraph_search_count(H, induced=True) == nautoms

        H = G.subgraph_search(H, induced=True)

        for v in G.vertices():
            for X in itertools.combinations(H.vertices(), H.order()-1):
                if uniquely_embeds(list(X)+[v]) and defines_bipartite_graph(X, v, v): break
            else:
                return False

        for v1, v2 in itertools.combinations(G.vertices(), 2):
            for X in itertools.combinations(H.vertices(), H.order()-1):
                if (uniquely_embeds(list(X)+[v1]) or uniquely_embeds(list(X)+[v2])) and defines_bipartite_graph(X, v1, v2): break
            else:
                return False

            return True
    return False

# note that this assume that G[X] also uniquely embeds
def our_condition(H):
    if basic_condition(H):
        H = G.subgraph_search(H, induced=True)
        X = H.vertices()
        l = len(X)
        for Xd in itertools.combinations(X, l-2):
            if defines_unique_neighborhoods(Xd):
                for x in X:
                    if x in Xd: continue
                    if not uniquely_embeds(list(Xd)+[x]): break
                else:
                    break
        else:
            return False
        
        for v in G.vertices():
            for Xdd in itertools.combinations(X, l-2):
                if uniquely_embeds(list(Xdd)+[v]) and defines_bipartite_graph(Xdd, v, v): break
            else:
                return False

        for v1, v2 in itertools.combinations(G.vertices(), 2):
            for Xdd in itertools.combinations(X, l-2):
                if (uniquely_embeds(list(Xdd)+[v1]) or uniquely_embeds(list(Xdd)+[v2])) and defines_bipartite_graph(Xdd, v1, v2): break
            else:
                return False

            return True
    return False

for n in range(6, 9):
    print(f"\nn={n} ---")
    for H in graphs.nauty_geng(f'{n}'):
        l = H.canonical_label().graph6_string() + " (" + graph_to_string(H.canonical_label()) + ")"
        if basic_condition(H):
            if our_condition(H): print(f"{l} satisfies our condition -> m={n}")
            elif pikhurko_clebsch_condition(H): print(f"{l} satisfies (3) -> m={n+1}")
            elif pikhurko_clebsch_condition_plus(H): print(f"{l} satisfies (3+) -> m={n+1}")
            else: print(f"{l} satisfies (2) -> m={n+2}")

#for k in range(2, 7):
#    seen = []
#    print(f"\nk={k}")
#    for X in itertools.combinations(G.vertices(), k):
#        H = G.subgraph(X)
#        H_label = H.canonical_label().graph6_string()
#        if H_label in seen: continue
#        seen.append(H_label)
#        if defines_unique_neighborhoods(X):
#            if G.subgraph_search_count(H, induced=True) == nautoms:
#                assert uniquely_embeds(H)
#                print(H_label)

#                H = G.subgraph_search(Graph(H_label), induced=True)
#                assert uniquely_embeds(H)
#                assert defines_unique_neighborhoods(H.vertices())
#                assert G.subgraph_search_count(H, induced=True) == nautoms



