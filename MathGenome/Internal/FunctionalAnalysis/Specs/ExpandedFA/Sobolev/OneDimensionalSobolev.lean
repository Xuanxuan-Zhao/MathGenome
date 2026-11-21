import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent statements for `fa2:p4:one-dimensional-sobolev`.
An interval is its open interior, in accordance with the upstream definition
of W^{m,p} on open sets. Closed and half-open nondegenerate intervals have the
same a.e. data. Continuous representatives are compared on the closure,
thereby recording both finite endpoint traces. Rays and the whole line are
included; no boundedness of the interval is imposed on the main theorem. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

namespace ExpandedFA.Sobolev.OneDimensional
open ExpandedFA.Distributions

/-- The canonical point of R¹ over the real coordinate t. -/
def linePoint (t : ℝ) : Domain 1 := fun _ => t

/-- Pull back an open real interval to the accepted Euclidean domain. -/
def lineDomain (I : Opens ℝ) : Opens (Domain 1) :=
  ⟨{z | z 0 ∈ I}, I.isOpen.preimage (continuous_apply 0)⟩

abbrev W1p (𝕜 : Type) [RCLike 𝕜] (I : Opens ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 1 (lineDomain I) 1 p

/-- The unique nonzero multi-index in dimension one and order one. -/
def firstIndex : DerivativeIndex 1 1 := ⟨fun _ => 1, by simp⟩

abbrev baseLp {𝕜 : Type} [RCLike 𝕜] {I : Opens ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1p 𝕜 I p) : DomainLp 𝕜 (lineDomain I) p :=
  u.val (zeroIndex 1 1)

abbrev derivativeLp {𝕜 : Type} [RCLike 𝕜] {I : Opens ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1p 𝕜 I p) : DomainLp 𝕜 (lineDomain I) p :=
  u.val firstIndex

/-- An ordinary real-variable version of any of the Lp classes. Its a.e.
meaning is justified by the volume-preserving R ≃ R¹ identification. -/
def lineFunction {𝕜 : Type} [RCLike 𝕜] {I : Opens ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (v : DomainLp 𝕜 (lineDomain I) p) : ℝ → 𝕜 :=
  fun t => v (linePoint t)

/-- Equality to the actual upstream Lp class, not a separately postulated weak
Sobolev predicate. Values outside the domain are immaterial. -/
def Represents {𝕜 : Type} [RCLike 𝕜] {I : Opens ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (v : DomainLp 𝕜 (lineDomain I) p) (f : ℝ → 𝕜) : Prop :=
  v =ᵐ[volume.restrict (lineDomain I : Set (Domain 1))] (fun z => f (z 0))

/-- The endpoint extension and fundamental theorem are assertions about the
same representative. Local AC means AC on every compact interior interval.
The integral is of the weak derivative extracted from the accepted graph. -/
def PrimitiveRepresentative {𝕜 : Type} [RCLike 𝕜] {I : Opens ℝ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u : W1p 𝕜 I p) (f : ℝ → 𝕜) : Prop :=
  ContinuousOn f (closure (I : Set ℝ)) ∧ Represents (baseLp u) f ∧
    (∀ a ∈ I, ∀ b ∈ I, AbsolutelyContinuousOnInterval f a b) ∧
    ∀ x ∈ closure (I : Set ℝ), ∀ y ∈ closure (I : Set ℝ),
      IntervalIntegrable (lineFunction (derivativeLp u)) volume y x ∧
      f x - f y = ∫ t in y..x, lineFunction (derivativeLp u) t

/-- Reciprocal exponent, with the required convention 1/∞ = 0. -/
def reciprocalExponent (p : ℝ≥0∞) : ℝ := 1 / p.toReal

end ExpandedFA.Sobolev.OneDimensional

namespace Specs.ExpandedFA.Sobolev.OneDimensionalSobolev
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Sobolev.OneDimensional
open _root_.ExpandedFA.Distributions

def RepresentativeExistence : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (I : Opens ℝ), OrdConnected (I : Set ℝ) →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : W1p 𝕜 I p),
    ∃ f : ℝ → 𝕜, PrimitiveRepresentative u f

/-- Uniqueness concerns the whole closed interval, including finite endpoints;
there is no assertion of uniqueness of arbitrarily assigned outside values. -/
def RepresentativeUniqueness : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (I : Opens ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (v : DomainLp 𝕜 (lineDomain I) p) (f g : ℝ → 𝕜),
    ContinuousOn f (closure (I : Set ℝ)) → ContinuousOn g (closure (I : Set ℝ)) →
    Represents v f → Represents v g → EqOn f g (closure (I : Set ℝ))

/-- The pointwise supremum estimate, hence also the essential supremum estimate.
Both p=1 and p=∞ are included, with exactly the source coefficients. -/
def FiniteIntervalEstimate : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (a b : ℝ) (_hab : a < b) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p) (f : ℝ → 𝕜),
    PrimitiveRepresentative u f → ∀ x ∈ Icc a b,
      ‖f x‖ ≤ (b - a) ^ (-reciprocalExponent p) * ‖baseLp u‖ +
        (b - a) ^ (1 - reciprocalExponent p) * ‖derivativeLp u‖

/-- The same finite-interval bound on the essential supremum of the original
Lp class, in ENNReal form so finiteness is part of the conclusion. -/
def FiniteIntervalEssentialSupremum : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (a b : ℝ) (_hab : a < b) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : W1p 𝕜 ⟨Ioo a b, isOpen_Ioo⟩ p) (f : ℝ → 𝕜),
    PrimitiveRepresentative u f →
      eLpNorm (baseLp u) ∞ (volume.restrict (lineDomain ⟨Ioo a b, isOpen_Ioo⟩ :
        Set (Domain 1))) ≤ ENNReal.ofReal
          ((b - a) ^ (-reciprocalExponent p) * ‖baseLp u‖ +
            (b - a) ^ (1 - reciprocalExponent p) * ‖derivativeLp u‖)

/-- A quantitative statement for the representative delivered by existence.
Endpoints are included, and I can be unbounded. -/
def HolderEstimate : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (I : Opens ℝ), OrdConnected (I : Set ℝ) →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p →
    ∀ (u : W1p 𝕜 I p) (f : ℝ → 𝕜), PrimitiveRepresentative u f →
    ∀ x ∈ closure (I : Set ℝ), ∀ y ∈ closure (I : Set ℝ),
      ‖f x - f y‖ ≤ ‖derivativeLp u‖ * |x - y| ^ (1 - reciprocalExponent p)

/-- Forward Lipschitz bound, with the actual derivative norm. -/
def LipschitzBound : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (I : Opens ℝ), OrdConnected (I : Set ℝ) →
    ∀ (u : W1p 𝕜 I ∞) (f : ℝ → 𝕜), PrimitiveRepresentative u f →
      LipschitzOnWith ‖derivativeLp u‖₊ f (closure (I : Set ℝ))

/-- Keeping v in global L∞ is essential on unbounded intervals. The right side
asserts existence of a Lipschitz representative of this globally bounded class. -/
def LipschitzCharacterization : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (I : Opens ℝ), OrdConnected (I : Set ℝ) →
    ∀ v : DomainLp 𝕜 (lineDomain I) ∞,
      (∃ u : W1p 𝕜 I ∞, baseLp u = v) ↔
      ∃ (f : ℝ → 𝕜) (K : ℝ≥0), Represents v f ∧ LipschitzOnWith K f (I : Set ℝ)

/-- Every Lipschitz representative has constant at least the weak derivative
norm. Together with existence and LipschitzBound this proves the least constant
is exactly ‖u′‖∞; it does not merely give an unspecified Lipschitz constant. -/
def OptimalLipschitzConstant : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (I : Opens ℝ), OrdConnected (I : Set ℝ) →
    ∀ (u : W1p 𝕜 I ∞) (f : ℝ → 𝕜) (K : ℝ≥0),
      Represents (baseLp u) f → LipschitzOnWith K f (I : Set ℝ) →
      ‖derivativeLp u‖ ≤ (K : ℝ)

end Specs.ExpandedFA.Sobolev.OneDimensionalSobolev
