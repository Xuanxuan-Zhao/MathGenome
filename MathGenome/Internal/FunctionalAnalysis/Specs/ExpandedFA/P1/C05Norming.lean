import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C05NormExtension
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientNorm

/-!
Independent statements for Corollary `fa2:p1:c05:norming`, paper.tex:943–950.
The dual is the continuous scalar-linear dual, including over complex scalars.
Real norms and distances are embedded into the scalar field in value equalities.
There is no completeness assumption, and the subspace need not be closed.
The zero case explicitly uses the zero functional, including on the zero space.
-/

namespace ExpandedFA.P1.C05Norming.Spec

universe u v

/-- A nonzero vector is normed by a functional of norm exactly one. -/
def NonzeroNormingFunctional : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E),
    x ≠ 0 → ∃ f : E →L[𝕜] 𝕜, ‖f‖ = 1 ∧ f x = (‖x‖ : 𝕜)

/-- At zero, the zero functional has norm at most one and the required value. -/
def ZeroNormingFunctional : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E),
    x = 0 →
      ‖(0 : E →L[𝕜] 𝕜)‖ ≤ 1 ∧ (0 : E →L[𝕜] 𝕜) x = (‖x‖ : 𝕜)

/-- The combined assertion, valid for every vector without nontriviality. -/
def NormingFunctional : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E),
    ∃ f : E →L[𝕜] 𝕜, ‖f‖ ≤ 1 ∧ f x = (‖x‖ : 𝕜)

/-- Distance uses the original subspace and its original norm distances. -/
def SubspaceDistanceFormulas : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (x : E),
    Metric.infDist x (closure (M : Set E)) = Metric.infDist x (M : Set E) ∧
    Metric.infDist x (M : Set E) =
      sInf ((fun m : E => ‖x - m‖) '' (M : Set E))

/-- Outside the norm closure, a norm-one annihilator attains the positive
distance to the original subspace, with its actual positive real scalar value. -/
def DistanceNormingFunctional : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (x : E),
    x ∉ closure (M : Set E) →
    ∃ f : E →L[𝕜] 𝕜,
      (∀ m ∈ M, f m = 0) ∧ ‖f‖ = 1 ∧
      f x = (Metric.infDist x (M : Set E) : 𝕜) ∧
      0 < Metric.infDist x (M : Set E)

end ExpandedFA.P1.C05Norming.Spec
