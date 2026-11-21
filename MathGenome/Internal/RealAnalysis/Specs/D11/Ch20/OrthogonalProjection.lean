import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
Independent statement for paper.tex, Chapter 20, `d11:20:orthogonal-projection`.
The scalar type is any `RCLike` field, in particular ℝ and ℂ. There is no
dimension, separability, or measure-space hypothesis.
-/

namespace D11.Ch20.OrthogonalProjection

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The paper's inner product, linear in its first argument. Mathlib's
inner product has the opposite argument convention. -/
def innerFirst (x y : H) : 𝕜 := inner 𝕜 y x

/-- Full conclusions for a single projection. The bundled continuous linear
map includes scalar linearity; the two identities spell it out as well.
The orthogonal complement is the usual submodule, with its convention
identified explicitly by `orthogonal_iff` below. -/
structure ProjectionProperties (V : Submodule 𝕜 H) (P : H →L[𝕜] H) : Prop where
  mem : ∀ x, P x ∈ V
  minimizing : ∀ x w, w ∈ V → ‖x - P x‖ ≤ ‖x - w‖
  unique_minimizer : ∀ x w, w ∈ V →
    (∀ v, v ∈ V → ‖x - w‖ ≤ ‖x - v‖) → w = P x
  orthogonal_iff : ∀ z, z ∈ Vᗮ ↔ ∀ w, w ∈ V → innerFirst (𝕜 := 𝕜) z w = 0
  residual : ∀ x, x - P x ∈ Vᗮ
  additive : ∀ x y, P (x + y) = P x + P y
  scalar_linear : ∀ (a : 𝕜) x, P (a • x) = a • P x
  fixes_subspace : ∀ x, x ∈ V → P x = x
  idempotent : ∀ x, P (P x) = P x
  contractive : ∀ x, ‖P x‖ ≤ ‖x‖
  decomposition : ∀ x, ∃! yz : V × Vᗮ, x = (yz.1 : H) + (yz.2 : H)
  canonical_decomposition : ∀ x, x = P x + (x - P x)
  zero : P 0 = 0
  bot : V = ⊥ → ∀ x, P x = 0
  top : V = ⊤ → ∀ x, P x = x

/-- Projection onto any closed subspace of any real or complex Hilbert space. -/
def statement : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (H : Type v) [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (V : Submodule 𝕜 H), IsClosed (V : Set H) →
      ∃ P : H →L[𝕜] H, ProjectionProperties V P

end D11.Ch20.OrthogonalProjection
