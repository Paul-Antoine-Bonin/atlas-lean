module

public import MathlibExt.Combinatorics.SimpleGraph.VertexTransitive

@[expose] public section

open SimpleGraph

example (G : SimpleGraph (Fin 1)) : G.IsVertexTransitive := by simp
