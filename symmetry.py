import itertools
from copy import deepcopy
from sage.all import *
from collections import Counter
from tqdm import tqdm

# G = graphs.CompleteGraph(4)

# G = Graph(r"LJ]lmZRnn]]\v[")
# good_types = [r"D_K", r"DK{"]

# G = graphs.ClebschGraph()

G = graphs.SchlaefliGraph()
good_types = [r"D?C", r"D@K", r"D_K", r"D@s", r"D@{", r"DBg", r"DBk", r"DIk", r"DB{", r"D`K", r"DK[", r"DK{", r"DJ[", r"DJk", r"DJ{", r"DLo", r"Dbk", r"DL{", r"DNw", r"DN{"]

# G = graphs.SchlaefliGraph().complement()
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
    return f"{alphabet[H.order()]}:{''.join([f'{alphabet[v1+1]}{alphabet[v2+1]}' for v1,v2,_ in H.edges()])}"

def neighbors(v, X):
    return tuple(sorted([x for x in G.neighbors(v) if x in X]))

def unique_neighborhoods(X):
    if isinstance(X, Graph):
        if not X.is_subgraph(G, induced=True):
            X = G.subgraph_search(X, induced=True)
            assert uniquely_embeds(X)
        if X is None: return False
        X = X.vertices()
    neighborhoods = {}
    for v in G.vertices():
        neighborhood = neighbors(v, X)
        neighborhoods[neighborhood] = neighborhoods.get(neighborhood, []) + [v]
    output = []
    for k,v in neighborhoods.items():
        if len(v)==1: output+=v
    return output

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
    # print(nsubgraphs, nautoms, H.automorphism_group().order())
    if nsubgraphs / H.automorphism_group().order() > nautoms: return False
    subautoms = [tuple(sorted([P.dict()[h] for h in H.vertices()])) for P in automs]
    # print(len(subautoms), len(set(subautoms)))
    nsubautoms = len(set(subautoms))*H.automorphism_group().order()
    return nsubautoms == nsubgraphs

def nembeddings(H):
    H = H.canonical_label()
    temp = []
    #for S in itertools.combinations(G.vertices(), H.order()):
    #    if G.subgraph(S).canonical_label() == H: temp.append(S)
    for S in G.subgraph_search_iterator(H, induced=True):
        S = tuple(sorted(S))
        if S not in temp: temp.append(S)
    assert len(temp) * H.automorphism_group().order() == G.subgraph_search_count(H, induced=True), (temp, len(temp), H.automorphism_group().order(), G.subgraph_search_count(H, induced=True), len(automs))
    c = 0
    while len(temp) > 0:
        c += 1
        isoms = [tuple(sorted([P.dict()[h] for h in temp[0]])) for P in automs]
        temp = [x for x in temp if x not in isoms]
    return c

def basic_condition(H):
    return uniquely_embeds(H) and defines_unique_neighborhoods(H)

def pikhurko_clebsch_condition(H):
    if basic_condition(H):
        # assert G.subgraph_search_count(H, induced=True) == nautoms

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
        # assert G.subgraph_search_count(H, induced=True) == nautoms

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


print(f"Starting with {G.graph6_string()} (canonical is {G.canonical_label().graph6_string()})")

good_types = [Graph(l).canonical_label().graph6_string() for l in good_types]

for l in good_types:
    H = Graph(l)
    if uniquely_embeds(H):
        H = G.subgraph_search(H)
        X1 = list(H.vertices())
        settled = unique_neighborhoods(X1)
        print(f"\nStarting with {l} ({graph_to_string(Graph(l))}) through {X1} giving {len(settled)} ({settled})")
        while len(settled) < G.order():
            nextX = {}
            for Xcand in itertools.combinations(X1+settled, 5):
                lcand = G.subgraph(Xcand).canonical_label().graph6_string()
                if lcand in good_types:
                    nextX[Xcand] = len([x for x in unique_neighborhoods(Xcand) if x not in settled])
                    if nextX[Xcand] == G.order()-len(settled): break
            if len(nextX) == 0 or max(nextX.values())==0:
                print(f"failed!")
                break
            best_nextX = max(nextX, key=nextX.get)
            best_l = G.subgraph(best_nextX).canonical_label().graph6_string()
            assert best_l in good_types
            new = [x for x in unique_neighborhoods(Xcand) if x not in settled]
            settled += new
            print(f"Adding {best_l} ({graph_to_string(Graph(best_l))}) through {best_nextX} giving {nextX[best_nextX]} ({new}) for {len(settled)}")
