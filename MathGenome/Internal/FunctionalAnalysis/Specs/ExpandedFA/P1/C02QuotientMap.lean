import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C02QuotientNorm
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.QuotientFactorization

/-!
Independent statements for `fa2:p1:c02:quotient-map`, paper.tex 370–396.
The quotient is by the original subspace, including when it is not closed.
Its native pseudometric is induced by the distance seminorm already specified
in `C02QuotientNorm`. For closed subspaces this is the same genuine norm and
metric. No completeness or nontriviality assumption is imposed.

The projection and strict-ball assertions are stated more generally for all
subspaces (and all real radii), so include the manuscript's closed case.
The two factorization statements reuse the independent upstream propositions.
-/

noncomputable section

namespace ExpandedFA.P1.C02QuotientMap.Spec

universe u v w

/-- Equal cosets give the same value of both expressions in the defining
distance formula. -/
def RepresentativeIndependence : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (x y : E),
    C02QuotientNorm.Spec.quotientMapValue 𝕜 E M x =
      C02QuotientNorm.Spec.quotientMapValue 𝕜 E M y →
    sInf ((fun m : E => ‖x - m‖) '' (M : Set E)) =
      sInf ((fun m : E => ‖y - m‖) '' (M : Set E)) ∧
    Metric.infDist x (M : Set E) = Metric.infDist y (M : Set E)

def QuotientSeminormAxioms : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E),
    C01Norm.SeminormAxioms 𝕜
      (C02QuotientNorm.Spec.distanceSeminormValue 𝕜 E M : E ⧸ M → ℝ)

/-- This identifies exactly the null cosets, without replacing the algebraic
quotient by the quotient by the closure. -/
def NullCosets : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (x : E),
    C02QuotientNorm.Spec.distanceSeminormValue 𝕜 E M
      (C02QuotientNorm.Spec.quotientMapValue 𝕜 E M x) = 0 ↔
      x ∈ closure (M : Set E)

def QuotientNormIffClosed : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E),
    C01Norm.NormAxioms 𝕜
      (C02QuotientNorm.Spec.distanceSeminormValue 𝕜 E M : E ⧸ M → ℝ) ↔
      IsClosed (M : Set E)

/-- Scalar linearity, surjectivity and contractivity of the very same
projection as in the distance formula. The Lipschitz conclusion expresses
contractivity for arbitrary pairs of points, and also gives continuity. -/
def ProjectionProperties : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E),
    let q := C02QuotientNorm.Spec.quotientMapValue 𝕜 E M
    (∀ x y, q (x + y) = q x + q y) ∧
    (∀ (a : 𝕜) x, q (a • x) = a • q x) ∧
    Function.Surjective q ∧
    (∀ x, ‖q x‖ ≤ ‖x‖) ∧
    LipschitzWith 1 q ∧ Continuous q

def BallImage : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (x : E) (r : ℝ),
    C02QuotientNorm.Spec.quotientMapValue 𝕜 E M '' Metric.ball x r =
      Metric.ball (C02QuotientNorm.Spec.quotientMapValue 𝕜 E M x) r

def OpenProjection : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E),
    IsOpenMap (C02QuotientNorm.Spec.quotientMapValue 𝕜 E M)

/-- Unique linear factorization, with no norm or closedness hypothesis. -/
def AlgebraicFactorization : Prop := QuotientFactorization.Spec.AlgebraicFactorization.{u, v, w}

/-- For closed subspaces, bounded factorization with equality of operator
norms and uniqueness among all bounded linear factorizations. -/
def BoundedFactorization : Prop := QuotientFactorization.Spec.BoundedFactorization.{u, v, w}

end ExpandedFA.P1.C02QuotientMap.Spec
