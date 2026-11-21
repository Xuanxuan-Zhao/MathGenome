import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.HomotopyOperator
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch06.SmoothingHomotopies
import Mathlib.Analysis.Convex.Contractible

/-! M11.02, paper.tex 2213–2269. Ordinary intrinsic smooth forms and the
ordinary de Rham quotient are the shared objects of M11.01. Homotopies in
these statements are continuous; both manifolds may have boundary.
The Euclidean statement is given in arbitrary linear coordinates on a real
normed space `V ≃L[ℝ] Euclidean n`, so it includes the standard ℝⁿ verbatim.
-/
set_option autoImplicit false
noncomputable section
namespace Specs.SmoothManifolds.DeRham.HomotopyInvariance
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.TangentData _root_.SmoothManifolds.DifferentialData
  _root_.SmoothManifolds.BundleOperationsData _root_.SmoothManifolds.CovectorData
  _root_.SmoothManifolds.ExteriorData _root_.SmoothManifolds.DeRhamData
  _root_.SmoothManifolds.InteriorHomotopyData
universe u

def homotopy_invarianceType : Prop :=
  ∀ {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold n a M) (T : SmoothManifold m b N)
    (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (A : CotangentBundle T) (E : ∀ k, FormBundle A k)
    (K : Calculus C B) (J : Calculus A E)
    (f₀ f₁ : M → N), IsSmoothMap S T f₀ → IsSmoothMap S T f₁ →
    (∃ H : HomotopyTime × M → N, Continuous H ∧
      (∀ p, H (timeZero, p) = f₀ p) ∧ (∀ p, H (timeOne, p) = f₁ p)) →
    ∀ (L₀ : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f₀ p))
      (L₁ : ∀ p, TangentSpace S p →ₗ[ℝ] TangentSpace T (f₁ p)),
    (∀ p, IsDifferential S T f₀ p (L₀ p)) →
    (∀ p, IsDifferential S T f₁ p (L₁ p)) →
    ∀ (P₀ P₁ : ∀ k, J.Cohomology k →ₗ[ℝ] K.Cohomology k),
    IsCohomologyPullback C B K J f₀ L₀ P₀ →
    IsCohomologyPullback C B K J f₁ L₁ P₁ → ∀ k, P₀ k = P₁ k

/-- A continuous contraction suffices. There is no vanishing claim in degree zero. -/
def contractible_vanishingType : Prop :=
  ∀ {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
    [Nonempty M] [ContractibleSpace M]
    (S : SmoothManifold n a M) (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
    (K : Calculus C B) (k : ℕ), 0 < k → Subsingleton (K.Cohomology k)

/-- Exactness includes an actual smooth primitive, encoded by the image of d.
The assertion holds for every smooth structure on this star-shaped open space,
in particular its standard restricted Euclidean smooth structure. -/
def poincare_lemmaType : Prop :=
  ∀ {n : ℕ} {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (_coordinates : V ≃L[ℝ] Euclidean n) (U : Set V), IsOpen U →
    ∀ x : V, x ∈ U → StarConvex ℝ x U →
    ∀ (S : SmoothManifold n .euclidean U)
      (C : CotangentBundle S) (B : ∀ k, FormBundle C k)
      (K : Calculus C B) (k : ℕ), 0 < k →
      ∀ ω : K.closed k, ω.val ∈ K.exact k

end Specs.SmoothManifolds.DeRham.HomotopyInvariance
