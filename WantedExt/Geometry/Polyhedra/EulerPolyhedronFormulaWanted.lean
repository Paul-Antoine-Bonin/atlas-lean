module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Batteries.Util.ProofWanted

namespace MetaMathlibExt

@[expose] public section

/-- Euler's polyhedron formula (statement `euler-polyhedron-s1`, canonical name
"Euler's polyhedron formula") for a supplied finite polygonal cellulation of the
boundary of a three-dimensional convex polyhedron: if the cellulation has `V`
vertices, `E` edges, and `F` faces, then `V - E + F = 2`.

Here `P` is the convex hull of all embedded cellulation vertices in
`EuclideanSpace Real (Fin 3)` and has nonempty interior. The vertex set `V`
may include non-extreme subdivision vertices, for instance vertices introduced
along an edge or inside an exposed face, so no hypothesis requires every
embedded vertex to be an extreme point of `P`. The remaining hypotheses encode
the incidence data of a boundary cellulation: listed edges are atomic (they
contain no listed vertex in their relative interior), distinct listed edges
meet only at a shared endpoint, each listed edge lies in exactly two listed
faces, the faces cover the frontier and meet only along listed vertices or
edges, and each face has the stated boundary incidence. Edge completeness is
imposed only on atomic boundary segments. The data may describe a subdivision
of an exposed polyhedron face (for example by adding a diagonal); the theorem
concerns the resulting cellulation and does not claim that `E` and `F` are
exactly the maximal exposed edges and faces of `P`.
Source: https://en.wikipedia.org/wiki/Euler_characteristic. -/
theorem_wanted euler_polyhedron_formula
    {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    (P : Set (EuclideanSpace Real (Fin 3)))
    (emb : V → EuclideanSpace Real (Fin 3))
    (hemb : Function.Injective emb)
    (hP : P = convexHull Real (Set.range emb))
    (hinterior : (interior P).Nonempty)
    (edgeEndpoints : E → V × V)
    (hEdge : ∀ e, segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2) ⊆ P)
    (hEdge_ne : ∀ e, (edgeEndpoints e).1 ≠ (edgeEndpoints e).2)
    (hEdge_atomic : ∀ (e : E) (v : V),
      emb v ∈ segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2) →
      v = (edgeEndpoints e).1 ∨ v = (edgeEndpoints e).2)
    (hEdge_inter : ∀ e₁ e₂, e₁ ≠ e₂ → ∀ x,
      x ∈ segment Real (emb (edgeEndpoints e₁).1) (emb (edgeEndpoints e₁).2) →
      x ∈ segment Real (emb (edgeEndpoints e₂).1) (emb (edgeEndpoints e₂).2) →
      ∃ v : V, emb v = x ∧
        (v = (edgeEndpoints e₁).1 ∨ v = (edgeEndpoints e₁).2) ∧
        (v = (edgeEndpoints e₂).1 ∨ v = (edgeEndpoints e₂).2))
    (faceVertices : F → Finset V)
    (hFace : ∀ f, convexHull Real (emb '' ↑(faceVertices f)) ⊆ P)
    (hFace_card : ∀ f, 3 ≤ (faceVertices f).card)
    (hVert_edge : ∀ v, ∃ e, (edgeEndpoints e).1 = v ∨ (edgeEndpoints e).2 = v)
    (hFace_bdry : ∀ f, convexHull Real (emb '' ↑(faceVertices f)) ∩ interior P = ∅)
    (hFace_dim : ∀ f, Module.finrank Real
      (affineSpan Real (convexHull Real (emb '' ↑(faceVertices f)))).direction = 2)
    (hFace_cover : frontier P ⊆
      Set.iUnion (fun f => convexHull Real (emb '' ↑(faceVertices f))))
    (hEdge_two_faces : ∀ e, ∃ f₁ f₂, f₁ ≠ f₂ ∧
      (edgeEndpoints e).1 ∈ faceVertices f₁ ∧
      (edgeEndpoints e).2 ∈ faceVertices f₁ ∧
      segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2) ⊆
        convexHull Real (emb '' ↑(faceVertices f₁)) ∧
      (edgeEndpoints e).1 ∈ faceVertices f₂ ∧
      (edgeEndpoints e).2 ∈ faceVertices f₂ ∧
      segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2) ⊆
        convexHull Real (emb '' ↑(faceVertices f₂)) ∧
      ∀ f, ((edgeEndpoints e).1 ∈ faceVertices f ∧
        (edgeEndpoints e).2 ∈ faceVertices f ∧
        segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2) ⊆
          convexHull Real (emb '' ↑(faceVertices f))) → f = f₁ ∨ f = f₂)
    (hEdge_no_rev : ∀ e₁ e₂, (edgeEndpoints e₁ = edgeEndpoints e₂ ∨
      ((edgeEndpoints e₁).1 = (edgeEndpoints e₂).2 ∧
       (edgeEndpoints e₁).2 = (edgeEndpoints e₂).1)) → e₁ = e₂)
    (hEdge_complete : ∀ v₁ v₂ : V, v₁ ≠ v₂ →
      segment Real (emb v₁) (emb v₂) ⊆ P →
      segment Real (emb v₁) (emb v₂) ∩ interior P = ∅ →
      (∀ v : V, emb v ∈ segment Real (emb v₁) (emb v₂) → v = v₁ ∨ v = v₂) →
      (∃ f₁ f₂ : F,
        f₁ ≠ f₂ ∧ v₁ ∈ faceVertices f₁ ∧ v₂ ∈ faceVertices f₁ ∧
        segment Real (emb v₁) (emb v₂) ⊆
          convexHull Real (emb '' ↑(faceVertices f₁)) ∧
        v₁ ∈ faceVertices f₂ ∧ v₂ ∈ faceVertices f₂ ∧
        segment Real (emb v₁) (emb v₂) ⊆
          convexHull Real (emb '' ↑(faceVertices f₂)) ∧
        ∀ f : F, (v₁ ∈ faceVertices f ∧ v₂ ∈ faceVertices f ∧
          segment Real (emb v₁) (emb v₂) ⊆
            convexHull Real (emb '' ↑(faceVertices f))) → f = f₁ ∨ f = f₂) →
      ∃ e : E, edgeEndpoints e = (v₁, v₂) ∨ edgeEndpoints e = (v₂, v₁))
    (hFace_incomparable :
      ∀ f₁ f₂, f₁ ≠ f₂ → ¬ (faceVertices f₁ ⊆ faceVertices f₂))
    (hFace_inter : ∀ f₁ f₂, f₁ ≠ f₂ → ∀ x,
      x ∈ convexHull Real (emb '' ↑(faceVertices f₁)) →
      x ∈ convexHull Real (emb '' ↑(faceVertices f₂)) →
      (∃ v, emb v = x) ∨
        (∃ e, x ∈ segment Real (emb (edgeEndpoints e).1) (emb (edgeEndpoints e).2)))
    (hFace_boundary : ∀ f, ∀ v ∈ faceVertices f, ∃ e₁ e₂, e₁ ≠ e₂ ∧
      ((edgeEndpoints e₁).1 = v ∨ (edgeEndpoints e₁).2 = v) ∧
      ((edgeEndpoints e₂).1 = v ∨ (edgeEndpoints e₂).2 = v) ∧
      segment Real (emb (edgeEndpoints e₁).1) (emb (edgeEndpoints e₁).2) ⊆
        convexHull Real (emb '' ↑(faceVertices f)) ∧
      segment Real (emb (edgeEndpoints e₂).1) (emb (edgeEndpoints e₂).2) ⊆
        convexHull Real (emb '' ↑(faceVertices f)))
    : (Fintype.card V : Int) - (Fintype.card E : Int) + (Fintype.card F : Int) = 2

end

end MetaMathlibExt
