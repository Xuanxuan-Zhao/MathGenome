import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.NonsymmetricResolvent

/-! Full parameter alternative for the canonical nonsymmetric Dirichlet operator.
Graph membership includes the actual operator domain; no regularity of solutions
beyond that domain is imposed. -/
noncomputable section
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace ComplexConjugate
universe u
namespace P201Specs.Fredholm
open P201.Elliptic

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The ambient eigenspace, including domain membership. -/
def eigenKernel (L : ExpandedFA.Unbounded.Operator ℂ H H) (z : ℂ) : Submodule ℂ H :=
  L.graph.comap (LinearMap.id.prod (z • LinearMap.id))

/-- `(L-zI)u=f` on the canonical domain. -/
def Solves (L : ExpandedFA.Unbounded.Operator ℂ H H) (z : ℂ) (f u : H) : Prop :=
  (u, f + z • u) ∈ L.graph

/-- Orthogonal compatibility, both finite kernels, the entire affine solution
set, and unique solvability at every non-eigenvalue. -/
def Alternative (L : ExpandedFA.Unbounded.Operator ℂ H H) : Prop :=
  ∀ z : ℂ,
    FiniteDimensional ℂ (eigenKernel L z) ∧
    FiniteDimensional ℂ (eigenKernel L.adjoint (conj z)) ∧
    (∀ f : H, (∃ u, Solves L z f u) ↔
      ∀ v ∈ eigenKernel L.adjoint (conj z), inner ℂ v f = 0) ∧
    (∀ (f u₀ : H), Solves L z f u₀ →
      ∀ u, Solves L z f u ↔ ∃ v ∈ eigenKernel L z, u = u₀ + v) ∧
    (eigenKernel L z = ⊥ → ∀ f : H, ∃! u, Solves L z f u)

/-- Retains the dense closed realization and compact inverses for every
sufficiently large real shift, on the very same graph as the alternative. -/
def Full (L : ExpandedFA.Unbounded.Operator ℂ H H) : Prop :=
  Dense (L.domain : Set H) ∧ L.IsClosed ∧
  (∃ C : ℝ, ∀ μ : ℝ, C < μ → ∃ T : H →L[ℂ] H,
    IsCompactOperator T ∧
    ∀ u f, (u, f - (μ : ℂ) • u) ∈ L.graph ↔ T f = u) ∧
  Alternative L

def PDE : Prop :=
  ∀ (m : ℕ) (Ω : Domain (m + 1)), IsBoundedLipschitzOpen Ω →
    ∀ (q : Nonsymmetric.Coefficients (m + 1) ℂ), Nonsymmetric.Bounded Ω q →
    ∀ lam : ℝ, 0 < lam → Nonsymmetric.Elliptic Ω q lam →
    ∃ (B : H10 ℂ Ω →L[ℂ] H10 ℂ Ω →L⋆[ℂ] ℂ)
      (hi : Function.Injective (hZeroUnderlying (𝕜 := ℂ) Ω))
      (hd : DenseRange (hZeroUnderlying (𝕜 := ℂ) Ω)),
      let a := P201.Elliptic.NonsymmetricExpected.embeddedForm
        (𝕜 := ℂ) (H := Lp ℂ Ω 2) (V := H10 ℂ Ω)
        (hZeroUnderlying (𝕜 := ℂ) Ω) hi hd B
      (∀ u v, B u v = Nonsymmetric.form Ω q u v) ∧ Full a.associatedOperator

end P201Specs.Fredholm
