/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Perfect-graph NP characterization
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.PerfectGraph

@[expose] public section

namespace MathlibExt.Combinatorics.PerfectGraphNPWanted

/-! Source record `AIM-COMBINATORICS-0270__20001145`. -/

/-!
# AIM Combinatorics 0270: NP Description of Perfect Graphs

Source identifiers: [AIM-COMBINATORICS-0270], Source item 4,
Canonical location aim-combinatorics-notes.json notes[269], Canonical tag problem,
Source URL https://aimath.org/WWN/perfectgraph/perfectgraph.pdf,
Collection AIM Problem Lists, Type PDF, Domain Combinatorics,
Workshop The Perfect Graph Conjecture, Section A.4 NP Description of Perfect Graphs,
Contributor Jack Edmonds.

Question from source: Give an NP description of perfect graphs.

Clause list (all hypotheses, side conditions, quantifier domains):
1. Domain: finite simple undirected loopless graphs on vertices `Fin n`.
2. Perfectness is the repository's
   `MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect`
   (every induced subgraph has `chromaticNumber = cliqueNum`); no custom
   clique/coloring hierarchy is introduced.
3. Valid graph instances convert from explicit Boolean adjacency data to
   `SimpleGraph (Fin n)` (`PerfectGraphInstance.toSimpleGraph`).
4. Graph instances are encoded as bitstrings via the repository's
   `MetaMathlibExt.BitstringEncoding` (vertex count plus row-major
   adjacency bits); no new global encoding instances are declared.
5. The perfect-graph decision language is a repository
   `MetaMathlibExt.ComplexityTheory.DecisionProblem` over bitstrings.
6. The NP description is membership of that language in the repository's
   `MetaMathlibExt.ComplexityTheory.NP` (polynomial certificates with a
   polynomial-time verifier backed by Mathlib Turing machines).

Resolution note: perfect-graph recognition is in P (Chudnovsky et al.,
"Recognizing Berge graphs", plus the Strong Perfect Graph Theorem), so
the requested NP description exists; the entry is marked resolved.
-/

/-- Perfect-graph instance presented by explicit adjacency data (no proof
fields, so instances admit bitstring encodings): vertex count `n` and a
Boolean adjacency matrix. Validity (symmetry, no loops) is recorded
separately by `PerfectGraphInstance.Valid`.
Cites [AIM-COMBINATORICS-0270] Source item 4, notes[269], Section A.4. -/
structure PerfectGraphInstance where
  n : Nat
  adj : Fin n → Fin n → Bool

/-- Validity of a perfect-graph instance: symmetric adjacency, no loops. -/
def PerfectGraphInstance.Valid (I : PerfectGraphInstance) : Prop :=
  (∀ x y : Fin I.n, I.adj x y = true → I.adj y x = true) ∧
    ∀ x : Fin I.n, I.adj x x = false

/-- A valid instance determines a finite simple undirected loopless graph
(`SimpleGraph`), on which the repository's `IsPerfect` is evaluated. -/
def PerfectGraphInstance.toSimpleGraph (I : PerfectGraphInstance)
    (h : I.Valid) : SimpleGraph (Fin I.n) where
  Adj x y := I.adj x y = true
  symm := ⟨fun a b hab => h.1 a b hab⟩
  loopless := ⟨fun a ha => by simp [h.2 a] at ha⟩

open MetaMathlibExt in
/-- Bitstring encoding of perfect-graph instances: the payload is the
vertex count (as a unary-length bit list) plus the row-major adjacency
matrix as a list of bit lists, under the repository's product and list
encodings. No new global encoding instances are declared; only the
repository's `Bool`/`List`/product instances are used. -/
instance : MetaMathlibExt.BitstringEncoding PerfectGraphInstance where
  encode I := MetaMathlibExt.BitstringEncoding.bitEncode
    (List.replicate I.n true, List.ofFn (fun i => List.ofFn (I.adj i)))
  decode l := (MetaMathlibExt.BitstringEncoding.bitDecode
    (α := List Bool × List (List Bool)) l).map
    fun p => ⟨p.1.length,
      fun i j => ((p.2.getD i.val [])[j.val]?.getD false)⟩
  decode_encode I := by
    obtain ⟨n, adj⟩ := I
    simp only [MetaMathlibExt.BitstringEncoding.bitDecode_bitEncode, Option.map_some]
    rw [List.length_replicate]
    rw [Option.some_inj, PerfectGraphInstance.mk.injEq]
    refine ⟨rfl, ?_⟩
    apply heq_of_eq
    funext i j
    simp [List.getD_eq_getElem?_getD, i.isLt, j.isLt]

open Classical in
/-- The perfect-graph decision problem as a bitstring decision problem:
decode an instance, and accept exactly the valid instances whose graph
is perfect in the repository's `IsPerfect` sense.
Cites [AIM-COMBINATORICS-0270] Source item 4, notes[269], Section A.4. -/
noncomputable def perfectGraphProblem :
    MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun l => match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PerfectGraphInstance) l with
    | some I => if h : I.Valid then
        (if MathlibExt.Combinatorics.SimpleGraph.PerfectGraphWanted.IsPerfect
          (I.toSimpleGraph h) then true else false) else false
    | none => false

/-- NP description of perfect graphs from the source: the encoded
perfect-graph decision language lies in the repository's `NP` class
(polynomial certificates with a polynomial-time verifier).
Cites [AIM-COMBINATORICS-0270] Source item 4, notes[269], Section A.4, Contributor Jack Edmonds. -/
def conjecture : Prop :=
  perfectGraphProblem ∈ MetaMathlibExt.ComplexityTheory.NP

/--
Resolved true: Resolved: Chudnovsky-Cornuejols-Liu-Seymour-Vuskovic recognize Berge graphs in
polynomial time, and the Strong Perfect Graph Theorem identifies Berge graphs with perfect
graphs; hence perfect-graph recognition is in P and the requested NP description exists. Source:
Maria Chudnovsky, Gerard Cornuejols, Xinming Liu, Paul Seymour, Kristina Vuskovic, Recognizing
Berge graphs, Combinatorica 25 (2005), 143-186, https://doi.org/10.1007/s00493-005-0012-8; Maria
Chudnovsky, Neil Robertson, Paul Seymour, Robin Thomas, The strong perfect graph theorem, Annals
of Mathematics 164 (2006), 51-229, https://doi.org/10.4007/annals.2006.164.51. Moved from
`OpenConjectures/Combinatorics/PerfectGraphNP`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Combinatorics.PerfectGraphNPWanted
