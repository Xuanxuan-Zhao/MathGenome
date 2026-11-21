import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.PoincareInequality
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarLpDuality

/-! Independent statements for `fa2:p4:negative-sobolev` (paper.tex:17941–17974).
The original W₀ has the full sum-component norm. `Option (Fin d)` labels
its order-zero and d first-derivative coordinates. Function-space norms on
coefficient families are the finite maximum, including the empty family.
The gradient range below carries the sum-of-derivatives norm, on precisely
the original W₀ elements; it imposes no new boundary or regularity condition. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal Distributions

namespace ExpandedFA.Sobolev.NegativeSobolev
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

abbrev W0 (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) := ZeroSpaceValue 𝕜 d Ω 1 p hp

abbrev FirstProduct (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] := PiLp 1 (fun _ : Option (Fin d) => DomainLp 𝕜 Ω p)

abbrev GradientProduct (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] := PiLp 1 (fun _ : Fin d => DomainLp 𝕜 Ω p)

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] {hp : p ≠ ∞}

def firstIndex : Option (Fin d) → DerivativeIndex d 1
  | none => zeroIndex d 1
  | some i => coordinateIndex i

def firstJet : W0 𝕜 Ω p hp →ₗ[𝕜] FirstProduct 𝕜 Ω p where
  toFun u := WithLp.toLp 1 (fun i => u.val.val (firstIndex i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def gradientJet : W0 𝕜 Ω p hp →ₗ[𝕜] GradientProduct 𝕜 Ω p where
  toFun u := WithLp.toLp 1 (fun i => u.val.val (coordinateIndex i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

abbrev GradientSpace (𝕜 : Type) [RCLike 𝕜] {d : ℕ} (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :=
  LinearMap.range (gradientJet (𝕜 := 𝕜) (Ω := Ω) (p := p) (hp := hp))

/-- The same original elements, viewed with their derivative sum norm. -/
def gradientIntoRange : W0 𝕜 Ω p hp →ₗ[𝕜] GradientSpace 𝕜 Ω p hp :=
  gradientJet.rangeRestrict

def coefficientDistribution (f : Option (Fin d) → DomainLp 𝕜 Ω q) :
    ScalarDistribution 𝕜 Ω :=
  lpDistribution (f none) - ∑ i : Fin d,
    Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue 𝕜 d Ω [i]
      (lpDistribution (f (some i)))

end ExpandedFA.Sobolev.NegativeSobolev

namespace Specs.ExpandedFA.Sobolev.NegativeSobolevRepresentation
open _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Distributions
open _root_.ExpandedFA.Sobolev.NegativeSobolev

/-- The displayed d+1-component map is an isometry for the original norm. -/
def FullNorm : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (u : W0 𝕜 Ω p hp),
  ‖u‖ = ‖u.val.val (zeroIndex d 1)‖ + ∑ i : Fin d, ‖u.val.val (coordinateIndex i)‖

/-- The coefficients have exactly the original full dual norm. Native Pi norms
are maxima of finitely many coordinate norms. Products are integrable. -/
def FullRepresentation : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [ENNReal.HolderConjugate p q] (hp : p ≠ ∞) (F : W0 𝕜 Ω p hp →L[𝕜] 𝕜),
  ∃ f : Option (Fin d) → DomainLp 𝕜 Ω q,
    (∀ (u : W0 𝕜 Ω p hp) i,
      Integrable (fun x => u.val.val (firstIndex i) x * f i x)
        (volume.restrict (Ω : Set (Domain d)))) ∧
    (∀ u, F u = (∫ x, u.val.val (zeroIndex d 1) x * f none x
        ∂(volume.restrict (Ω : Set (Domain d)))) +
      ∑ i : Fin d, ∫ x, u.val.val (coordinateIndex i) x * f (some i) x
        ∂(volume.restrict (Ω : Set (Domain d)))) ∧
    ‖f‖ = ‖F‖

/-- Every compact test is an element of the original W₀. -/
def TestInclusion : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
  (φ : Tests 𝕜 Ω), ∃ u : W0 𝕜 Ω p hp,
    u.val.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] φ

/-- The representation really is the scalar-linear distribution f₀−Σ∂ⱼfⱼ,
acting on the very same compact tests in the original Sobolev space. -/
def DistributionInterpretation : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
  [ENNReal.HolderConjugate p q] (hp : p ≠ ∞)
  (F : W0 𝕜 Ω p hp →L[𝕜] 𝕜) (f : Option (Fin d) → DomainLp 𝕜 Ω q),
  (∀ u : W0 𝕜 Ω p hp, F u = ∑ i : Option (Fin d),
    ∫ x, u.val.val (firstIndex i) x * f i x
      ∂(volume.restrict (Ω : Set (Domain d)))) →
  ∀ (φ : Tests 𝕜 Ω) (u : W0 𝕜 Ω p hp),
    u.val.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] φ →
    F u = coefficientDistribution f φ

/-- On exactly the corrected bounded-domain scope the gradient is injective,
and its norm is equivalent to the original full norm, uniformly in p. -/
def DerivativeNormEquivalence : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
  (0 < d ∨ (Ω : Set (Domain d)) = ∅) →
  ∃ K : ℝ, 1 ≤ K ∧ ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞),
    Function.Injective (gradientJet (𝕜 := 𝕜) (Ω := Ω) (p := p) (hp := hp)) ∧
    ∀ u : W0 𝕜 Ω p hp, ‖gradientJet u‖ ≤ ‖u‖ ∧ ‖u‖ ≤ K * ‖gradientJet u‖

/-- The continuous dual for the derivative norm has the exact maximum
coefficient norm. Comparing with the original dual gives equivalent bounds,
without asserting equality for its full norm. Empty Ω and d=0 are retained. -/
def DerivativeRepresentation : Prop := ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
  (Ω : Opens (Domain d)), Bornology.IsBounded (Ω : Set (Domain d)) →
  (0 < d ∨ (Ω : Set (Domain d)) = ∅) →
  ∃ K : ℝ, 1 ≤ K ∧ ∀ (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (hp : p ≠ ∞) (F : W0 𝕜 Ω p hp →L[𝕜] 𝕜),
    ∃ (G : GradientSpace 𝕜 Ω p hp →L[𝕜] 𝕜) (f : Fin d → DomainLp 𝕜 Ω q),
      (∀ u : W0 𝕜 Ω p hp, G (gradientIntoRange u) = F u) ∧
      (∀ (u : W0 𝕜 Ω p hp) i, Integrable
        (fun x => u.val.val (coordinateIndex i) x * f i x)
        (volume.restrict (Ω : Set (Domain d)))) ∧
      (∀ u : W0 𝕜 Ω p hp, F u = ∑ i : Fin d,
        ∫ x, u.val.val (coordinateIndex i) x * f i x
          ∂(volume.restrict (Ω : Set (Domain d)))) ∧
      ‖f‖ = ‖G‖ ∧ ‖F‖ ≤ ‖G‖ ∧ ‖G‖ ≤ K * ‖F‖

end Specs.ExpandedFA.Sobolev.NegativeSobolevRepresentation
