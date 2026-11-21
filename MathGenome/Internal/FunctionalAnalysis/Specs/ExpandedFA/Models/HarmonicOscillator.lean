import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.HermiteBasis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.ConfiningCompactResolvent
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.OperatorDomains
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! Independent statements for the operator and ground-state clauses of
`fa2:p3:hermite-oscillator`, paper.tex:16101--16171. The underlying line and
energy space are exactly those of the preceding confining-potential theorem.
The Hermite functions retain the Rodrigues definition and normalization. -/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace

namespace ExpandedFA.Models.HarmonicOscillator
open WeightedConfiningEnergySpace ConfiningSchrodingerRealization

def potential : Potential where
  toContinuousMap := ⟨fun x => x ^ 2, continuous_id.pow 2⟩
  nonneg := sq_nonneg

/-- The actual confining differential realization, including its exact domain
and action. This definition contains no spectral or self-adjointness assertion. -/
def IsRealization {𝕜 : Type} [RCLike 𝕜] (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜) : Prop :=
  ∀ u f : L2 𝕜, (u, f) ∈ A.graph ↔
    ∃ v : Space 𝕜 potential, value v = u ∧ DistributionEquation v f

/-- A basis with the original Hermite representatives in the upstream line
coordinates. This explicitly bridges the two L² realizations. -/
def IsHermiteBasis {𝕜 : Type} [RCLike 𝕜] (b : HilbertBasis ℕ 𝕜 (L2 𝕜)) : Prop :=
  ∀ n, (fun x => b n x) =ᵐ[lineMeasure]
    fun x => (HermiteBasis.h n (x 0) : 𝕜)

/-- The signed multiplication xu, as an actual L² vector. Membership and the
identity with the √(x²) component's norm are separate proof obligations. -/
def IsPosition {𝕜 : Type} [RCLike 𝕜] (u : Space 𝕜 potential) (w : L2 𝕜) : Prop :=
  w =ᵐ[lineMeasure] fun x => (x 0 : 𝕜) * value u x

/-- Literal Schwartz differential graph. The first and second directional
derivatives are in the sole real coordinate, and both coordinates are L²
classes. No domain, closedness or symmetry certificate is built into it. -/
def schwartzGraph (𝕜 : Type) [RCLike 𝕜] : Set (L2 𝕜 × L2 𝕜) :=
  {z | ∃ φ : SchwartzMap Line 𝕜,
    (z.1 =ᵐ[lineMeasure] φ) ∧
    (z.2 =ᵐ[lineMeasure] fun x =>
      -fderiv ℝ (fun y => fderiv ℝ φ y (fun _ => 1)) x (fun _ => 1) +
        ((x 0)^2 : 𝕜) * φ x)}

namespace Spec

def Confining : Prop := ConfiningCompactResolvent.IsConfining potential

def HermiteBasisExists : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  ∃ b : HilbertBasis ℕ 𝕜 (L2 𝕜), IsHermiteBasis b

/-- Existence is not hidden in the hypotheses of the spectral statements.
The compact resolvent is in the upstream convention (ζI−A)⁻¹, here ζ=0. -/
def RealizationAndCompactResolvent : Prop := ∀ (𝕜 : Type) [RCLike 𝕜],
  ∃ A : L2 𝕜 →ₗ.[𝕜] L2 𝕜,
    IsRealization A ∧ Dense (A.domain : Set (L2 𝕜)) ∧ A.adjoint = A ∧
    (∀ u : A.domain, 0 ≤ RCLike.re ⟪(u : L2 𝕜), A u⟫_𝕜) ∧
    ∃ R : ExpandedFA.Unbounded.ResolventInverse A 0, IsCompactOperator R.inverse

def AllResolventsCompact : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
  (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜), IsRealization A →
  ∀ (ζ : 𝕜) (R : ExpandedFA.Unbounded.ResolventInverse A ζ),
    IsCompactOperator R.inverse

def Eigenvectors : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
  (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜), IsRealization A →
  ∀ (b : HilbertBasis ℕ 𝕜 (L2 𝕜)), IsHermiteBasis b → ∀ n : ℕ,
    (b n, ((2 * (n : ℝ) + 1 : ℝ) : 𝕜) • b n) ∈ A.graph

/-- Every vector already has its unique Hilbert expansion. This is the exact
weighted coefficient criterion for membership, without any regularity premise. -/
def SpectralDomain : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
  (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜), IsRealization A →
  ∀ (b : HilbertBasis ℕ 𝕜 (L2 𝕜)), IsHermiteBasis b → ∀ u : L2 𝕜,
    u ∈ A.domain ↔ Summable (fun n : ℕ => (2 * (n : ℝ) + 1)^2 * ‖⟪b n, u⟫_𝕜‖^2)

/-- The graph relation is exactly the restriction to all Schwartz functions;
its closure is the original realization, and that closure is self-adjoint. -/
def EssentialSelfAdjointness : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
  (A : L2 𝕜 →ₗ.[𝕜] L2 𝕜), IsRealization A →
    schwartzGraph 𝕜 ⊆ (A.graph : Set (L2 𝕜 × L2 𝕜)) ∧
    closure (schwartzGraph 𝕜) = (A.graph : Set (L2 𝕜 × L2 𝕜)) ∧
    A.adjoint = A

def PositionExists : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (u : Space 𝕜 potential),
  ∃ w : L2 𝕜, IsPosition u w ∧ ‖w‖ = ‖weighted u‖

def GroundStateIdentity : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
  (u : Space 𝕜 potential) (w : L2 𝕜), IsPosition u w →
    ‖derivative u + w‖^2 = ‖derivative u‖^2 + ‖w‖^2 - ‖value u‖^2

def GroundStateInequality : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
  (u : Space 𝕜 potential) (w : L2 𝕜), IsPosition u w →
    ‖value u‖^2 ≤ ‖derivative u‖^2 + ‖w‖^2

/-- Equality on the entire energy space, not just Schwartz or operator-domain
vectors, with exactly the unnormalized Gaussian multiples (including zero). -/
def GroundStateEquality : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
  (u : Space 𝕜 potential) (w : L2 𝕜), IsPosition u w →
    (‖derivative u‖^2 + ‖w‖^2 = ‖value u‖^2 ↔
      ∃ c : 𝕜, value u =ᵐ[lineMeasure]
        fun x => c * (Real.exp (-((x 0)^2)/2) : 𝕜))

end Spec
end ExpandedFA.Models.HarmonicOscillator
