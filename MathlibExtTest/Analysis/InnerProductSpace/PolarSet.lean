module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import MathlibExt.Analysis.InnerProductSpace.PolarSet

@[expose] public section

open MetaMathlibExt

-- Ordinary example: the origin is polar to the whole space.
example : (0 : EuclideanSpace ℝ (Fin 2)) ∈ polarSet Set.univ :=
  zero_mem_polarSet _

-- Boundary example: the polar of the empty set is the whole space.
example : polarSet (∅ : Set (EuclideanSpace ℝ (Fin 2))) = Set.univ :=
  polarSet_empty
