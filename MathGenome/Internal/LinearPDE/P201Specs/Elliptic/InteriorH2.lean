import MathGenome.Internal.LinearPDE.P201Specs.Common.SpatialInterfaces
import MathGenome.Internal.LinearPDE.P201Specs.Common.DifferenceQuotients
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-! Interior H² regularity, paper.tex, `pde:elliptic-interior-h2`.
These statements use the common full Hilbert norms and actual distribution-defined
Sobolev classes. Ambient representatives are compared only almost everywhere on
the relevant open set. No boundary condition or coefficient symmetry is imposed.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped NNReal ENNReal InnerProductSpace
namespace P201Specs.InteriorH2

abbrev RelativelyCompactIn {n : ℕ} (U V : Domain n) : Prop :=
  P102.U4.DifferenceQuotient.RelativelyCompactIn U V

/-- H^k locally means that every relatively compact restriction has a genuine
H^k representative, including all its distributional derivative coordinates. -/
def LocallyH {n : ℕ} (Ω : Domain n) (k : ℕ) (u : Space n → ℝ) : Prop :=
  ∀ V : Domain n, RelativelyCompactIn V Ω →
    ∃ v : H ℝ V k, (hUnderlying V k v : Space n → ℝ) =ᵐ[domainMeasure V] u

/-- Local uniform ellipticity on every compact subset. The matrix need not be symmetric. -/
def LocallyUniformlyElliptic {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) : Prop :=
  ∀ K : Set (Space n), IsCompact K → K ⊆ Ω →
    ∃ theta : ℝ, 0 < theta ∧ ∀ x ∈ K, ∀ ξ : Space n,
      theta * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ

/-- Quantitative coefficient data on the comparison set. Operator norms use
Euclidean source and target norms. Lipschitz and ellipticity bounds are separate. -/
def CoefficientBounds {n : ℕ} (V : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (M L : ℝ≥0) (theta : ℝ) : Prop :=
  (∀ x ∈ V, ‖A x‖ ≤ M) ∧ LipschitzOnWith L A V ∧
    ∀ x ∈ V, ∀ ξ : Space n, theta * ‖ξ‖ ^ 2 ≤ inner ℝ (A x ξ) ξ

/-- The interior weak equation on an H¹ class; there is no boundary datum.
The source is L² and is never differentiated. -/
def WeakEquation {n : ℕ} (V : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (v : H ℝ V 1)
    (f : Space n → ℝ) : Prop :=
  ∀ φ : Test ℝ V,
    (∫ x in V, inner ℝ (A x (hGradient v x)) (gradient φ x)) =
      ∫ x in V, f x * φ x

/-- The weak equation for a locally H¹ representative. Equality is required for
all its local classes; uniqueness of the underlying-class map makes this
independent of any choice of representatives. -/
def LocalWeakEquation {n : ℕ} (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n) (u f : Space n → ℝ) : Prop :=
  ∀ V : Domain n, RelativelyCompactIn V Ω → ∀ v : H ℝ V 1,
    (hUnderlying V 1 v : Space n → ℝ) =ᵐ[domainMeasure V] u →
      WeakEquation V A v f

/-- The qualitative conclusion on arbitrary open sets, with exactly local
coefficient regularity and local L² forcing. -/
def interiorH2RegularityStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω : Domain n)
    (A : Space n → Space n →L[ℝ] Space n),
    LocallyLipschitzOn (Ω : Set (Space n)) A → LocallyUniformlyElliptic Ω A →
    ∀ u f : Space n → ℝ, LocallyH Ω 1 u →
    P102.U4.DifferenceQuotient.LocallyMemLp Ω 2 f →
    LocalWeakEquation Ω A u f → LocallyH Ω 2 u

/-- The constant is chosen before A, u and f. Thus it depends only on the nested
sets, dimension, and coefficient/Lipschitz/ellipticity bounds. This stronger local
form applies to the restrictions of every solution in the qualitative theorem. -/
def interiorH2EstimateStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω V U : Domain n),
    RelativelyCompactIn U V → RelativelyCompactIn V Ω →
    ∀ (M L : ℝ≥0) (theta : ℝ), 0 < theta → ∃ C : ℝ, 0 < C ∧
    ∀ A : Space n → Space n →L[ℝ] Space n, CoefficientBounds V A M L theta →
    ∀ (v : H ℝ V 1) (f : Lp ℝ V 2), WeakEquation V A v f →
      ∃ w : H ℝ U 2,
        (hUnderlying U 2 w : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 v ∧
        ‖w‖ ≤ C * (‖v‖ + ‖f‖)

/-- All components of the weak gradient have uniformly bounded quotients.
This is an intermediate proof interface, not an additional assumption of either
source theorem. `HasBound` includes admissibility of both signs of the step. -/
def GradientQuotientBound {n : ℕ} (V U : Domain n) (v : H ℝ V 1) (B : ℝ≥0) : Prop :=
  ∀ j k : Fin n, P102.U4.DifferenceQuotient.HasBound V U k 2
    (hFirstDerivative v j) B

/-- Reconstruction interface using distributional identities only. The norm
bound uses the number of multi-indices, and is deliberately nonoptimal. -/
def h2FromWeakDerivativesStatement : Prop :=
  ∀ {n : ℕ} (U : Domain n) (u : Lp ℝ U 2)
    (d : Fin n → Lp ℝ U 2) (g : Fin n → Fin n → Lp ℝ U 2) (B : ℝ),
    (∀ j, distributionDerivative {j} (regularDistribution U u) = regularDistribution U (d j)) →
    (∀ j k, distributionDerivative {k} (regularDistribution U (d j)) =
      regularDistribution U (g j k)) →
    ‖u‖ ≤ B → (∀ j, ‖d j‖ ≤ B) → (∀ j k, ‖g j k‖ ≤ B) →
    ∃ w : H ℝ U 2, hUnderlying U 2 w = u ∧
      ‖w‖ ≤ (Fintype.card (P102.U4.SobolevIndex n 2) : ℝ) * B

/-- Quantitative reconstruction from uniform quotients of every weak-gradient
component. No PDE or coefficient assumption is needed for this step. -/
def h2FromQuotientsStatement : Prop :=
  ∀ {n : ℕ} (V U : Domain n), RelativelyCompactIn U V →
    ∀ (v : H ℝ V 1) (B : ℝ≥0), GradientQuotientBound V U v B →
    ∃ w : H ℝ U 2,
      (hUnderlying U 2 w : Space n → ℝ) =ᵐ[domainMeasure U] hUnderlying V 1 v ∧
      ‖w‖ ≤ (Fintype.card (P102.U4.SobolevIndex n 2) : ℝ) * (‖v‖ + B)

/-- Uniform energy control of the gradient quotients. Its coefficient and PDE
hypotheses are precisely those of the quantitative theorem. -/
def gradientQuotientEstimateStatement : Prop :=
  ∀ {n : ℕ}, 1 ≤ n → ∀ (Ω V U : Domain n),
    RelativelyCompactIn U V → RelativelyCompactIn V Ω →
    ∀ (M L : ℝ≥0) (theta : ℝ), 0 < theta → ∃ C : ℝ≥0,
    ∀ A : Space n → Space n →L[ℝ] Space n, CoefficientBounds V A M L theta →
    ∀ (v : H ℝ V 1) (f : Lp ℝ V 2), WeakEquation V A v f →
      GradientQuotientBound V U v (C * (‖v‖₊ + ‖f‖₊))

end P201Specs.InteriorH2
