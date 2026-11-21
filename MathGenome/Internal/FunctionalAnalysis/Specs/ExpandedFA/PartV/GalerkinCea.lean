import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Independent statements for paper.tex 22967–23001, fa2:p5:galerkin/cea.
Ritz energy geometry and the dense-union counterexample belong to app_ritz.
Closed trial spaces need not be finite dimensional or nonzero. -/
noncomputable section
open scoped BigOperators Topology ComplexConjugate

namespace ExpandedFA.PartV.GalerkinCea.Spec
open ExpandedFA.Hilbert.Conventions.Spec
universe u v

/-- Restrict the variational problem to any closed trial space. -/
def GalerkinSolvability : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : BoundedSesquilinearFormValue 𝕜 H H) (α : ℝ),
    FormCoerciveValue 𝕜 H a α → ∀ (F : ContinuousAntidualValue 𝕜 H)
    (W : Submodule 𝕜 H), IsClosed (W : Set H) →
      ∃ w : W, (∀ z : W, a (z : H) (w : H) = F (z : H)) ∧
        ‖(w : H)‖ ≤ ‖F‖ / α ∧
        ∀ w' : W, (∀ z : W, a (z : H) (w' : H) = F (z : H)) → w' = w

/-- Orthogonality in the test slot and the actual metric best-approximation bound. -/
def QuasiOptimality : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : BoundedSesquilinearFormValue 𝕜 H H) (M α : ℝ),
    (∀ x y : H, ‖a x y‖ ≤ M * ‖x‖ * ‖y‖) → FormCoerciveValue 𝕜 H a α →
    ∀ (F : ContinuousAntidualValue 𝕜 H) (W : Submodule 𝕜 H),
    IsClosed (W : Set H) → ∀ (u : H) (w : W),
    (∀ z : H, a z u = F z) → (∀ z : W, a (z : H) (w : H) = F (z : H)) →
      (∀ z : W, a (z : H) (u - (w : H)) = 0) ∧
      ‖u - (w : H)‖ ≤ (M / α) * Metric.infDist u (W : Set H)

/-- Eventual approximation of every vector yields solutions converging in norm
for every datum; no nesting or finite dimension assumption is imposed. -/
def SequenceConvergence : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (a : BoundedSesquilinearFormValue 𝕜 H H) (M α : ℝ),
    (∀ x y : H, ‖a x y‖ ≤ M * ‖x‖ * ‖y‖) → FormCoerciveValue 𝕜 H a α →
    ∀ (W : ℕ → Submodule 𝕜 H), (∀ n, IsClosed (W n : Set H)) →
    (∀ x : H, Filter.Tendsto (fun n => Metric.infDist x (W n : Set H))
      Filter.atTop (𝓝 0)) → ∀ F : ContinuousAntidualValue 𝕜 H,
    ∃ (u : H) (w : ∀ n, W n), (∀ z : H, a z u = F z) ∧
      (∀ n (z : W n), a (z : H) (w n : H) = F (z : H)) ∧
      Filter.Tendsto (fun n => (w n : H)) Filter.atTop (𝓝 u)

section Coordinates
variable {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 H] {m : ℕ} {W : Submodule 𝕜 H}

def synthesis (e : Module.Basis (Fin m) 𝕜 W) (c : Fin m → 𝕜) : W :=
  ∑ j, c j • e j

def formMatrix (a : BoundedSesquilinearFormValue 𝕜 H H)
    (e : Module.Basis (Fin m) 𝕜 W) : Matrix (Fin m) (Fin m) 𝕜 :=
  fun i j => a (e i : H) (e j : H)

def loadVector (F : ContinuousAntidualValue 𝕜 H)
    (e : Module.Basis (Fin m) 𝕜 W) : Fin m → 𝕜 := fun i => F (e i : H)
end Coordinates

/-- Every finite basis, including the empty basis, gives the stated invertible
matrix, with its equations equivalent to the variational equations. -/
def MatrixConclusion : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (a : BoundedSesquilinearFormValue 𝕜 H H) (α : ℝ),
    FormCoerciveValue 𝕜 H a α → ∀ (F : ContinuousAntidualValue 𝕜 H)
      (W : Submodule 𝕜 H) (m : ℕ) (e : Module.Basis (Fin m) 𝕜 W),
    IsUnit (formMatrix a e) ∧
      ∀ c, (∀ z : W, a (z : H) (synthesis e c : H) = F (z : H)) ↔
        (formMatrix a e).mulVec c = loadVector F e

end ExpandedFA.PartV.GalerkinCea.Spec
