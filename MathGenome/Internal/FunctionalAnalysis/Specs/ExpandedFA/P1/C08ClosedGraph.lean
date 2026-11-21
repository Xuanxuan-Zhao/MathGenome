import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
Independent statements for Theorem `fa2:p1:c08:closed-graph`, paper.tex
1605–1612. The algebraic linear map has all of E as its domain. Boundedness
means a finite nonnegative global norm bound, not an assumed continuity
certificate. Both spaces in the boundedness equivalence are Banach.

`WithLp 1 (E × F)` is the Cartesian product with its actual sum norm.
The first statement identifies that norm and explicitly transports closedness
to the native product (whose norm is the maximum). The graph condition and
its sequential characterization use the original coordinates. Zero spaces
are not excluded. The closedness/sequential equivalence itself needs no
completeness.
-/

open Filter Topology

universe u v w

namespace ExpandedFA.P1.C08ClosedGraph.Spec

/-- The sum norm and its coordinate-preserving closed-set transport. -/
def SumProductGeometry : Prop :=
  ∀ (E : Type v) (F : Type w) [NormedAddCommGroup E] [NormedAddCommGroup F],
    (∀ z : WithLp 1 (E × F),
      ‖z‖ = ‖(WithLp.ofLp z).1‖ + ‖(WithLp.ofLp z).2‖) ∧
    (∀ s : Set (E × F),
      IsClosed ((WithLp.ofLp : WithLp 1 (E × F) → E × F) ⁻¹' s) ↔ IsClosed s)

/-- Boundedness is equivalent to closedness of the graph in the sum norm. -/
def ClosedGraph : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [CompleteSpace E] [CompleteSpace F]
    (T : E →ₗ[𝕜] F),
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, ‖T x‖ ≤ C * ‖x‖) ↔
      IsClosed {z : WithLp 1 (E × F) | (WithLp.ofLp z).2 = T (WithLp.ofLp z).1}

/-- Closedness in the sum norm is exactly the stated sequential condition.
No continuity or existence of limits of arbitrary image sequences is assumed. -/
def ClosedGraphSequential : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] (T : E →ₗ[𝕜] F),
    IsClosed {z : WithLp 1 (E × F) | (WithLp.ofLp z).2 = T (WithLp.ofLp z).1} ↔
      ∀ (x : ℕ → E) (a : E) (b : F),
        Tendsto x atTop (𝓝 a) → Tendsto (fun n => T (x n)) atTop (𝓝 b) → b = T a

end ExpandedFA.P1.C08ClosedGraph.Spec
