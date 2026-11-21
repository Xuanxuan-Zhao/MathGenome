import MathGenome.Internal.Specs.D05.M06.Projection
import MathGenome.Internal.Specs.D05.M12.BestApproximation.Conditional
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
Independent statements for the contractive-projection corollary,
K05.12.best_approximation, paper.tex:2054–2059.

The endomorphism is an arbitrary algebraic linear map. Contractivity is the
pointwise norm inequality, not an assumed continuity or operator-norm bound.
Orthogonality uses the shared first-slot-linear `D05.firstInner u z = inner F z u`.
No finite-dimensional, closed-range, or completeness hypothesis is imposed.
The final statement identifies the map with the canonical orthogonal projection;
its required existence instance is a conclusion, not a premise.
-/

namespace Specs.D05.M12.BestApproximation.Contractive

universe u v

/-- For an idempotent, contractivity is equivalent to orthogonality of its
actual image and kernel, quantified over every vector in each subspace. -/
def contractive_iff_range_orthogonal_kernel : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (P : Module.End F V), P ^ 2 = P →
      ((∀ x : V, ‖P x‖ ≤ ‖x‖) ↔
        ∀ u ∈ LinearMap.range P, ∀ z ∈ LinearMap.ker P,
          _root_.D05.firstInner (F := F) u z = 0)

/-- In the contractive case the kernel is exactly the orthogonal complement
of the image, and the algebraic decomposition is the orthogonal decomposition. -/
def orthogonal_decomposition : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (P : Module.End F V), P ^ 2 = P →
      (∀ x : V, ‖P x‖ ≤ ‖x‖) →
      LinearMap.ker P = (LinearMap.range P).orthogonal ∧
        ∀ x : V, P x ∈ LinearMap.range P ∧
          x - P x ∈ (LinearMap.range P).orthogonal ∧ x = P x + (x - P x)

/-- The image admits an orthogonal projection even in an incomplete ambient
space, and that canonical projection, as a linear endomorphism, equals P. -/
def eq_starProjection : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] (P : Module.End F V), P ^ 2 = P →
      (∀ x : V, ‖P x‖ ≤ ‖x‖) →
      ∃ h : (LinearMap.range P).HasOrthogonalProjection,
        letI := h
        P = (LinearMap.range P).starProjection.toLinearMap

end Specs.D05.M12.BestApproximation.Contractive
