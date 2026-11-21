import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.SpectralGapDecayObstruction
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.RealSelfAdjointSpectralTheorem

/-! Real specialization of `fa2:p3:spectral-gap-decay-obstruction`.
The spectrum is the intrinsic real bounded-inverse spectrum, and the
complexification is the single canonical pair model with its exact domain.
All time regularity is on the closed positive half-line, including zero. -/
noncomputable section
open MeasureTheory Filter Topology
namespace ExpandedFA.Semigroups.RealSpectralGapDecay
open Unbounded
open TraceIdeals.RealComplexification (Space)
open TraceIdeals.RealComplexification.Spec (inclusion conjugation)
open RealOperatorComplexification.Spec (complexifyValue)
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
local instance : CompleteSpace (Space H) := TraceIdeals.RealComplexification.Spec.completeSpace
local instance : ContinuousSMul ℝ (Space H) := IsScalarTower.continuousSMul ℂ

/-- A form bound on the complete original domain; no positivity assumption. -/
def FormUpperBound (G : Operator ℝ H H) (ω : ℝ) : Prop :=
  ∀ x : G.domain, inner ℝ (x : H) (G x) ≤ ω * ‖(x : H)‖ ^ 2

/-- The embedded trajectory belongs to exactly the coordinate domain. -/
def inclusionDomain (G : Operator ℝ H H) (u : ℝ → H)
    (hD : ∀ t ∈ Set.Ici (0 : ℝ), u t ∈ G.domain)
    (t : ℝ) (ht : t ∈ Set.Ici (0 : ℝ)) :
    inclusion (u t) ∈ (complexifyValue G).domain :=
  ⟨hD t ht, G.domain.zero_mem⟩

namespace Spec

def SpectralTransport : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (G : Operator ℝ H H), Dense (G.domain : Set H) →
  HilbertAdjointSpec.adjointValue G = G → ∀ ω : ℝ, FormUpperBound G ω →
  letI := TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
  Dense ((complexifyValue G).domain : Set (Space H)) ∧
  HilbertAdjointSpec.adjointValue (complexifyValue G) = complexifyValue G ∧
  (∀ p : (complexifyValue G).domain,
    (inner ℂ (p : Space H) (complexifyValue G p)).re ≤ ω * ‖(p : Space H)‖ ^ 2) ∧
  (∀ z ∈ UnboundedNormalSpectralTheorem.operatorSpectrum (complexifyValue G), z.im = 0) ∧
  RealSelfAdjointSpectralTheorem.operatorSpectrum G = Complex.ofReal ⁻¹'
    (UnboundedNormalSpectralTheorem.operatorSpectrum (complexifyValue G))

/-- Explicit transport of every trajectory hypothesis and every weighted integral. -/
def TrajectoryTransport : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (G : Operator ℝ H H) (u du : ℝ → H),
  ContinuousOn u (Set.Ici 0) → ContinuousOn du (Set.Ici 0) →
  (∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt u (du t) (Set.Ici 0) t) →
  ∀ (hD : ∀ t ∈ Set.Ici (0 : ℝ), u t ∈ G.domain),
  Continuous (fun t : Set.Ici (0 : ℝ) => G ⟨u t, hD t t.property⟩) →
  letI := TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
  letI : Module ℝ (Space H) := Module.restrictScalars ℝ ℂ (Space H)
  letI : NormedSpace ℝ (Space H) := NormedSpace.restrictScalars ℝ ℂ (Space H)
  ContinuousOn (fun t => inclusion (u t)) (Set.Ici 0) ∧
  ContinuousOn (fun t => inclusion (du t)) (Set.Ici 0) ∧
  (∀ t ∈ Set.Ici (0 : ℝ),
    HasDerivWithinAt (fun s => inclusion (u s)) (inclusion (du t)) (Set.Ici 0) t) ∧
  Continuous (fun t : Set.Ici (0 : ℝ) =>
    complexifyValue G ⟨inclusion (u t), inclusionDomain G u hD t t.property⟩) ∧
  (∀ t (ht : t ∈ Set.Ici (0 : ℝ)),
    ‖inclusion (du t) - complexifyValue G ⟨inclusion (u t), inclusionDomain G u hD t ht⟩‖ =
      ‖du t - G ⟨u t, hD t ht⟩‖) ∧
  (∀ t : ℝ, ‖inclusion (u t)‖ = ‖u t‖) ∧
  (∀ b : ℝ, (∫⁻ t in Set.Ici (0 : ℝ),
      ENNReal.ofReal (‖inclusion (u t)‖ ^ 2 * Real.exp (b * t))) =
    (∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (‖u t‖ ^ 2 * Real.exp (b * t))))

def GenerationAndLines : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (G : Operator ℝ H H), Dense (G.domain : Set H) →
  HilbertAdjointSpec.adjointValue G = G → (∃ ω : ℝ, FormUpperBound G ω) →
  ∀ (ξ : ℕ → ℝ), Tendsto ξ atTop atBot → ∀ (d : ℝ), 0 < d →
  (∀ n (s : ℝ), s ∈ Set.Ioo (ξ n - d) (ξ n + d) →
    s ∉ RealSelfAdjointSpectralTheorem.operatorSpectrum G) →
  letI := TraceIdeals.RealComplexification.Spec.completeSpace (H := H)
  ∃ (T : C0Semigroup ℝ H) (S : C0Semigroup ℂ (Space H)),
    C0SemigroupSpec.generatesValue G T ∧
    C0SemigroupSpec.generatesValue (complexifyValue G) S ∧
    (∀ t p, conjugation (S.operators t p) = S.operators t (conjugation p)) ∧
    (∀ t x, S.operators t (inclusion x) = inclusion (T.operators t x)) ∧
    (∀ x y : H, (x, y) ∈ (C0SemigroupSpec.generatorValue T).graph ↔
      (inclusion x, inclusion y) ∈ (C0SemigroupSpec.generatorValue S).graph) ∧
    ∀ n, WeightedResolvent.LineBound (complexifyValue G) (ξ n) d

def DecayObstruction : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
  ∀ (G : Operator ℝ H H), Dense (G.domain : Set H) →
  HilbertAdjointSpec.adjointValue G = G → (∃ ω : ℝ, FormUpperBound G ω) →
  ∀ (ξ : ℕ → ℝ), Tendsto ξ atTop atBot → ∀ (d : ℝ), 0 < d →
  (∀ n (s : ℝ), s ∈ Set.Ioo (ξ n - d) (ξ n + d) →
    s ∉ RealSelfAdjointSpectralTheorem.operatorSpectrum G) →
  ∀ (u du : ℝ → H),
  ContinuousOn u (Set.Ici 0) → ContinuousOn du (Set.Ici 0) →
  (∀ t ∈ Set.Ici (0 : ℝ), HasDerivWithinAt u (du t) (Set.Ici 0) t) →
  ∀ (hD : ∀ t ∈ Set.Ici (0 : ℝ), u t ∈ G.domain),
  Continuous (fun t : Set.Ici (0 : ℝ) => G ⟨u t, hD t t.property⟩) →
  ∀ (k : ℝ), k < d →
  (∀ t (ht : t ∈ Set.Ici (0 : ℝ)),
    ‖du t - G ⟨u t, hD t ht⟩‖ ≤ k * ‖u t‖) →
  (∀ t ∈ Set.Ici (0 : ℝ), u t = 0) ∨
    ∃ b : ℝ, 0 < b ∧
      (∫⁻ t in Set.Ici (0 : ℝ),
        ENNReal.ofReal (‖u t‖ ^ 2 * Real.exp (b * t))) = ⊤

def FullScalarCorollary : Prop :=
  SpectralGapDecay.Spec.GenerationAndLines.{u} ∧
  SpectralGapDecay.Spec.DecayObstruction.{u} ∧ GenerationAndLines.{u} ∧ DecayObstruction.{u}
end Spec
end ExpandedFA.Semigroups.RealSpectralGapDecay
