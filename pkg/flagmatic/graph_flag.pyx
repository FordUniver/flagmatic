"""

flagmatic 2

Copyright (c) 2012, E. R. Vaughan. All rights reserved.

Redistribution and use in source and binary forms, with or without modification,
are permitted provided that the following conditions are met:

1) Redistributions of source code must retain the above copyright notice, this
list of conditions and the following disclaimer.

2) Redistributions in binary form must reproduce the above copyright notice,
this list of conditions and the following disclaimer in the documentation and/or
other materials provided with the distribution.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR
ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
(INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON
ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

Further development of Flagmatic is supported by ERC.
http://cordis.europa.eu/project/rcn/104324_en.html
"""

from sage.arith.all import binomial
from sage.graphs.graph import Graph
from hypergraph_flag cimport HypergraphFlag

cdef class GraphFlag (HypergraphFlag):


        def __init__(self, representation=None):

                if type(representation) is Graph:
                        g = representation
                        super(GraphFlag, self).__init__(g.order(), r=2, oriented=False)
                        vertices = g.vertices()
                        for edge in g.edge_iterator():
                                self.add_edge(list(map(lambda i : vertices.index(i) + 1, edge[:2])))
                else:
                        super(GraphFlag, self).__init__(representation=representation, r=2, oriented=False)
                        

        def __reduce__(self):
                return (type(self), (self._repr_(),))


        @classmethod
        def description(cls):
                return "2-graph"
        

        @classmethod
        def default_density_graph(cls):
                return cls("2:12")


        @classmethod
        def max_number_edges(cls, n):
                return binomial(n, 2)


        @classmethod
        def generate_flags(cls, n, tg, forbidden_edge_numbers=None, forbidden_graphs=None, forbidden_induced_graphs=None):
                return HypergraphFlag.generate_flags(n, tg, r=2, oriented=False, forbidden_edge_numbers=forbidden_edge_numbers,
                        forbidden_graphs=forbidden_graphs, forbidden_induced_graphs=forbidden_induced_graphs)


        @classmethod
        def generate_graphs(cls, n, forbidden_edge_numbers=None, forbidden_graphs=None, forbidden_induced_graphs=None, use_mp=False, show_progress=False):
                return HypergraphFlag.generate_flags(n, cls(), r=2, oriented=False, forbidden_edge_numbers=forbidden_edge_numbers,
                        forbidden_graphs=forbidden_graphs, forbidden_induced_graphs=forbidden_induced_graphs, use_mp=use_mp, show_progress=show_progress)


        def Graph(self):
                """
                Returns a Sage Graph object.
                """
                
                g = Graph()
                g.add_vertices(range(1, self._n + 1))
                g.add_edges(self.edges)
                return g


        def automorphism_group_gens(self):
                # This function is not very necessary. Just to keep things compatible with Emil's code.
                # New Sage 6.4.1+ does not relabel graphs to compute automorphism group.
                
                G = self.Graph().automorphism_group()
                trans_gens = [gen.cycle_tuples() for gen in G.gens()]
                gens = sorted([tuple(sorted(tuple(sorted(cy)) for cy in gen)) for gen in trans_gens])

                return gens

        

cdef class NautyGraphFlag (GraphFlag):
        
        # overwrite make_minimal_isomorph and is_labelled_isomorphic with nauty's methods
        def make_minimal_isomorph(self):
                self._require_mutable()

                if self._certified_minimal_isomorph: return

                new_edges = []
                canonical_sage_graph = self.Graph().canonical_label()
                for (v1, v2, _) in canonical_sage_graph.edges():
                        new_edges.append((v1+1, v2+1))

                for edge in self.edges: self.delete_edge(edge)
                for edge in new_edges: self.add_edge(edge)

                self._certified_minimal_isomorph = True


        def is_labelled_isomorphic(self, GraphFlag other):
                return self.Graph() == other.Graph()
                