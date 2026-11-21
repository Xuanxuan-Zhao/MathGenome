import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevSmoothingAndDensity
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.C1DomainExtension
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.HalfSpaceExtension
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The first-order Morrey clauses of `fa2:p4:sobolev-embedding`,
paper.tex:17806–17810 and 17840–17855. The scalar field is real or complex;
the exponent includes infinity, with 1/∞ = 0. Dimension zero is retained.
Distances and pointwise gradient lengths use the Euclidean (l²) norm.
The upstream Sobolev norm itself remains the stipulated sum norm. -/

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal

namespace ExpandedFA.Sobolev.Morrey
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Exactly the nonzero multi-indices of order at most one. -/
abbrev GradientIndex (d : ℕ) := {α : DerivativeIndex d 1 // α ≠ zeroIndex d 1}

/-- The actual vector of first weak derivatives; no order-zero term occurs. -/
def gradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p) (x : Domain d) :
    PiLp 2 (fun _ : GradientIndex d => 𝕜) :=
  WithLp.toLp 2 (fun α => u.val α.val x)

/-- Lp norm of the Euclidean gradient, including its essential supremum at ∞. -/
def gradientNorm {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p) : ℝ :=
  (eLpNorm (gradient u) p (volume.restrict (Ω : Set (Domain d)))).toReal

def euclideanNorm {d : ℕ} (x : Domain d) : ℝ :=
  ‖WithLp.toLp 2 x‖

def exponent (d : ℕ) (p : ℝ≥0∞) : ℝ := 1 - (d : ℝ) / p.toReal

def Represents {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p)
    (f : Domain d → 𝕜) : Prop :=
  u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f

end ExpandedFA.Sobolev.Morrey

namespace Specs.ExpandedFA.Sobolev.MorreyEmbedding
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Distributions
open _root_.ExpandedFA.Sobolev.Morrey _root_.ExpandedFA.Sobolev.C1Extension
open WeakDerivativeSpaces

def WholeSpace : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)], (d : ℝ≥0∞) < p →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d ⊤ 1 p,
    ∃ f : Domain d → 𝕜, Continuous f ∧ Represents u f ∧
      ∀ x y, ‖f x - f y‖ ≤ C * gradientNorm u * euclideanNorm (x - y) ^ exponent d p

/-- Finite-p part, separated from the endpoint for proof assembly. -/
def FiniteWholeSpace : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → (d : ℝ≥0∞) < p →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d ⊤ 1 p,
    ∃ f : Domain d → 𝕜, Continuous f ∧ Represents u f ∧
      ∀ x y, ‖f x - f y‖ ≤ C * gradientNorm u * euclideanNorm (x - y) ^ exponent d p

/-- The endpoint is a representative of the actual W¹,∞ class, with a bound
using only the weak gradient. There is no norm-density premise at infinity. -/
def InfinityWholeSpace : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ),
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d ⊤ 1 ∞,
    ∃ f : Domain d → 𝕜, Continuous f ∧ Represents u f ∧
      ∀ x y, ‖f x - f y‖ ≤ C * gradientNorm u * euclideanNorm (x - y)

/-- A proof-internal smooth estimate. The function represents a member of the
accepted weak derivative graph, so its gradient is not separately assumed. -/
def SmoothEstimate : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → (d : ℝ≥0∞) < p →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SpaceValue 𝕜 d ⊤ 1 p) (f : Domain d → 𝕜),
    ContDiff ℝ (⊤ : ℕ∞) f → Represents u f →
      ∀ x y, ‖f x - f y‖ ≤ C * gradientNorm u * euclideanNorm (x - y) ^ exponent d p

/-- Any bounded extension gives the claimed full-norm estimate. The ambient
representative restricts continuously to the closure, including its boundary. -/
def ExtensionDomains : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)], (d : ℝ≥0∞) < p →
  ∀ E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d ⊤ 1 p,
    IsExtension Ω E → ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d Ω 1 p,
      ∃ f : Domain d → 𝕜, Continuous f ∧ Represents u f ∧
        ∀ x ∈ closure (Ω : Set (Domain d)), ∀ y ∈ closure (Ω : Set (Domain d)),
          ‖f x - f y‖ ≤ C * ‖u‖ * euclideanNorm (x - y) ^ exponent d p

def C1Domains : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (Ω : Opens (Domain d)), IsC1Domain Ω → IsCompact (frontier (Ω : Set (Domain d))) →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], (d : ℝ≥0∞) < p →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d Ω 1 p,
      ∃ f : Domain d → 𝕜, Continuous f ∧ Represents u f ∧
        ∀ x ∈ closure (Ω : Set (Domain d)), ∀ y ∈ closure (Ω : Set (Domain d)),
          ‖f x - f y‖ ≤ C * ‖u‖ * euclideanNorm (x - y) ^ exponent d p

def HalfSpaces : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (a : Fin d → ℝ), a ≠ 0 → ∀ (c : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    (d : ℝ≥0∞) < p →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : SpaceValue 𝕜 d (HalfSpace.affineHalfSpace a c) 1 p,
      ∃ f : Domain d → 𝕜, Continuous f ∧ Represents u f ∧
        ∀ x ∈ closure (HalfSpace.affineHalfSpace a c : Set (Domain d)),
        ∀ y ∈ closure (HalfSpace.affineHalfSpace a c : Set (Domain d)),
          ‖f x - f y‖ ≤ C * ‖u‖ * euclideanNorm (x - y) ^ exponent d p

def ZeroDimension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : SpaceValue 𝕜 0 ⊤ 1 p),
    ∃ f : Domain 0 → 𝕜, Continuous f ∧ Represents u f ∧
      ∀ x y, ‖f x - f y‖ ≤ (0 : ℝ) * gradientNorm u * euclideanNorm (x - y) ^ exponent 0 p

/-- In dimension one the accepted primitive theorem gives the bound with
constant one, for every p>1 including infinity. -/
def OneDimension : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p →
    ∀ u : SpaceValue 𝕜 1 ⊤ 1 p,
    ∃ f : Domain 1 → 𝕜, Continuous f ∧ Represents u f ∧
      ∀ x y, ‖f x - f y‖ ≤ gradientNorm u * euclideanNorm (x - y) ^ exponent 1 p

/-- Once the smooth finite-p estimate is proved, all the required embeddings
follow; the infinity endpoint is established separately in the implementation. -/
def EmbeddingOfSmoothEstimate : Prop := SmoothEstimate →
  WholeSpace ∧ ExtensionDomains ∧ C1Domains ∧ HalfSpaces

def WholeSpaceAssembly : Prop := FiniteWholeSpace → InfinityWholeSpace → WholeSpace
def ExtensionConsequence : Prop := WholeSpace → ExtensionDomains
def C1Consequence : Prop := ExtensionDomains → C1Domains
def HalfSpaceConsequence : Prop := ExtensionDomains → HalfSpaces
def FiniteDensityConsequence : Prop := SmoothEstimate → FiniteWholeSpace

/-- Proof assembly only: neither analytic input is assumed by the main
`WholeSpace` specification. -/
def EmbeddingAssembly : Prop := SmoothEstimate → InfinityWholeSpace →
  WholeSpace ∧ ExtensionDomains ∧ C1Domains ∧ HalfSpaces

/-- The complete assigned first-order embedding conclusion. -/
def Embedding : Prop := WholeSpace ∧ ExtensionDomains ∧ C1Domains ∧ HalfSpaces

end Specs.ExpandedFA.Sobolev.MorreyEmbedding
