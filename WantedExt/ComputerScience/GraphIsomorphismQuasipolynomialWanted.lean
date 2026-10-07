/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
ALG-016: Babai's theorem on graph isomorphism (resolved). Graph isomorphism
is decidable in quasi-polynomial time for all graphs.

A finite simple graph is presented as a vertex count `n` plus a symmetric,
loop-free adjacency matrix on `Fin n` (`GraphCode`). A decision input is a
pair of such codes, serialized by a transparent prefix-free bit scheme
(`encodePair`: unary lengths, binary magnitudes, row-major adjacency bits).
`Isomorphic G H` holds when the vertex counts agree and some vertex
permutation carries one adjacency matrix to the other. The proposition asks
for one fixed deterministic machine (Mathlib's bundled
`Turing.TM2ComputableInTime`) deciding isomorphism on all pairs, whose time
function is pointwise bounded by the quasipolynomial `qpTime c` for some
fixed exponent `c`, measured in encoded input length.

Representation notes: the quasipolynomial bound `2 ^ ((log2(len+2)+2)^c)`
is stated in the encoded bit length `len`, which is polynomially related
to the vertex count, so this matches the standard `exp((log n)^O(1))`
formulation. Babai's quasipolynomial algorithm itself is NOT formalized
here; this file states only the existence claim, which Babai proved
(STOC 2016; see the registry entry).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Computability.Encoding
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Nat.Log
public import Mathlib.Logic.Equiv.Defs

@[expose] public section

namespace MathlibExt.ComputerScience.GraphIsomorphismQuasipolynomialWanted

/-! Source record `ALG-016`. -/

/-- A finite simple graph code: vertex count plus a symmetric, loop-free
adjacency matrix on `Fin n`. -/
structure GraphCode where
  n : ℕ
  adj : Fin n → Fin n → Bool
  symm : ∀ i j, adj i j = adj j i
  irrefl : ∀ i, adj i i = false

/-- Binary digits of `n`, most significant first. -/
def natBits (n : ℕ) : List Bool :=
  (Nat.toDigits 2 n).map (fun d => decide (d = '1'))

/-- Prefix-free encoding of `n`: unary length, separator, binary digits. -/
def natToBits (n : ℕ) : List Bool :=
  List.replicate (natBits n).length true ++ [false] ++ natBits n

/-- Bit serialization of a graph code: vertex count then row-major adjacency. -/
def encode (G : GraphCode) : List Bool :=
  natToBits G.n ++
    ((List.finRange G.n).map fun i =>
      (List.finRange G.n).map fun j => G.adj i j).flatten

/-- Bit serialization of a graph pair: concatenation of the two codes. -/
def encodePair (p : GraphCode × GraphCode) : List Bool :=
  encode p.1 ++ encode p.2

/-- Graph isomorphism: equal vertex counts and a permutation of vertices
carrying one adjacency matrix to the other. -/
def Isomorphic (G H : GraphCode) : Prop :=
  ∃ h : G.n = H.n, ∃ σ : Equiv.Perm (Fin H.n), ∀ i j : Fin G.n,
    G.adj i j = H.adj (σ (Fin.cast h i)) (σ (Fin.cast h j))

/-- Quasipolynomial time bound in the encoded input length `n`, with fixed
exponent `c`: `2 ^ ((log2(n+2)+2)^c)`. -/
def qpTime (c n : ℕ) : ℕ :=
  2 ^ ((Nat.log 2 (n + 2) + 2) ^ c)

/-- [ALG-016] There is one fixed deterministic algorithm deciding graph
isomorphism on all graph pairs in quasipolynomial time. -/
def conjecture : Prop :=
  ∃ decideGI : GraphCode × GraphCode → Bool, ∃ c : ℕ,
    ∃ h : Turing.TM2ComputableInTime encodePair Computability.encodeBool decideGI,
      (∀ n : ℕ, h.time n ≤ qpTime c n) ∧
      ∀ G H : GraphCode, decideGI (G, H) = true ↔ Isomorphic G H

/--
Resolved true: Babai (STOC 2016) gave a deterministic quasipolynomial-time graph-isomorphism
algorithm; the corrected proof retains that complexity. Source: Babai, L., Graph isomorphism in
quasipolynomial time, Proc. 48th ACM Symp. Theory Comput. (STOC 2016), 684-697;
arXiv:1512.03547, https://arxiv.org/abs/1512.03547. Moved from
`OpenConjectures/ComputerScience/GraphIsomorphismQuasipolynomial`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.ComputerScience.GraphIsomorphismQuasipolynomialWanted
