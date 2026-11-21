import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Topology.GDelta.Basic

/-!
Independent statements for paper.tex:6124–6133 and its explicit hyperplane
qualification (proof at 6150–6168). Algebraic codimension is the dimension of
the algebraic quotient by the actual range, with no closedness assumption.
The scalar field may be real or complex. Zero spaces remain allowed in the
two positive assertions; only the counterexample assumes infinite dimension.
-/

namespace ExpandedFA.Supplements.FiniteCodimensionalRanges.Spec

universe u v w

/-- Nonmeagreness is measured in the original, merely normed codomain. -/
def NonmeagreRange : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (T : E →L[𝕜] F),
    ¬ IsMeagre (Set.range T) →
      Function.Surjective T ∧ IsOpenMap T ∧ CompleteSpace F

/-- A bounded linear range of finite algebraic codimension between Banach
spaces is closed. The quotient is not assumed Hausdorff or normed. -/
def FiniteCodimensionalRangeClosed : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F),
    FiniteDimensional 𝕜 (F ⧸ T.range) → IsClosed (T.range : Set F)

/-- In every infinite-dimensional Banach space, an algebraic scalar-linear
functional unbounded on the unit sphere has a nonclosed kernel of algebraic
codimension exactly one. In particular finite codimension alone does not
force a subspace to be closed. -/
def NonclosedHyperplane : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E],
    ¬ FiniteDimensional 𝕜 E →
    ∃ f : E →ₗ[𝕜] 𝕜,
      ¬ Bornology.IsBounded (f '' Metric.sphere (0 : E) 1) ∧
      ¬ Continuous f ∧
      FiniteDimensional 𝕜 (E ⧸ f.ker) ∧
      Module.finrank 𝕜 (E ⧸ f.ker) = 1 ∧
      ¬ IsClosed (f.ker : Set E)

end ExpandedFA.Supplements.FiniteCodimensionalRanges.Spec
