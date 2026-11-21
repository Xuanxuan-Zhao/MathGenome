import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.OrderedSpectral.PerronEigenstructure
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Complex.Basic

/-! The remaining assertions of `fa2:p2:perron-cq`, paper.tex:11698–11765.
The dual and its representing measures are the scalar-linear Radon dual of C(Q).
Convergence is in the operator norm. The complex statements are followed by
the real statements and the canonical continuous-function complexification. -/
noncomputable section
namespace ExpandedFA.OrderedSpectral.PerronPowers.Spec
open MeasureTheory Filter
open scoped Topology
open PerronEigenstructure.Spec
universe u
variable {Q : Type u} [TopologicalSpace Q] [CompactSpace Q]

/-- The explicitly normalized eigenprojection, without conjugating the dual. -/
def eigenprojection (u : C(Q, ℂ)) (φ : C(Q, ℂ) →L[ℂ] ℂ) :
    C(Q, ℂ) →L[ℂ] C(Q, ℂ) :=
  φ.smulRight ((φ u)⁻¹ • u)

variable [MeasurableSpace Q]

/-- Invariant probability in the Radon dual of C(Q). -/
def InvariantProbability (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) (ν : Measure Q) : Prop :=
  FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon ν ∧
  ν Set.univ = 1 ∧
  ∀ f : C(Q, ℂ), (∫ q, K f q ∂ν) = ∫ q, f q ∂ν

def PowerConclusion (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)) : Prop :=
  0 < radius K ∧
  ∃ (u : C(Q, ℂ)) (φ : C(Q, ℂ) →L[ℂ] ℂ) (μ : Measure Q),
    StrictlyPositive u ∧ K u = (radius K : ℂ) • u ∧
    AlgebraicallySimple K (radius K) u ∧
    Eigenmeasure K (radius K) φ μ ∧
    (φ u).im = 0 ∧ 0 < (φ u).re ∧
    (∀ (ζ : ℂ) (z : C(Q, ℂ)), z ≠ 0 → K z = ζ • z →
      ζ ≠ (radius K : ℂ) → ‖ζ‖ < radius K) ∧
    Tendsto (fun n : ℕ => ((radius K : ℂ)⁻¹ ^ n) • K ^ n) atTop
      (𝓝 (eigenprojection u φ)) ∧
    (∀ f q, eigenprojection u φ f q = u q * φ f / φ u)

def PowersTheorem : Prop :=
  ∀ (Q : Type u) [TopologicalSpace Q] [T2Space Q] [CompactSpace Q] [Nonempty Q]
    [MeasurableSpace Q] [BorelSpace Q] (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)),
    IsCompactOperator K → PreservesReal K → StronglyPositive K → PowerConclusion K

/-- In the Markov case the eigenfunction can be chosen to be the constant one;
the normalized eigenmeasure is unique, including as a measure. -/
def MarkovTheorem : Prop :=
  ∀ (Q : Type u) [TopologicalSpace Q] [T2Space Q] [CompactSpace Q] [Nonempty Q]
    [MeasurableSpace Q] [BorelSpace Q] (K : C(Q, ℂ) →L[ℂ] C(Q, ℂ)),
    IsCompactOperator K → PreservesReal K → StronglyPositive K → K 1 = 1 →
    radius K = 1 ∧
    ∃ (φ : C(Q, ℂ) →L[ℂ] ℂ) (μ : Measure Q),
      StrictlyPositive (1 : C(Q, ℂ)) ∧ K 1 = (radius K : ℂ) • (1 : C(Q, ℂ)) ∧
      AlgebraicallySimple K (radius K) (1 : C(Q, ℂ)) ∧
      Eigenmeasure K (radius K) φ μ ∧ φ 1 = 1 ∧
      InvariantProbability K μ ∧
      (∀ ν : Measure Q, InvariantProbability K ν → ν = μ) ∧
      Tendsto (fun n : ℕ => K ^ n) atTop (𝓝 (φ.smulRight 1))

end ExpandedFA.OrderedSpectral.PerronPowers.Spec

namespace ExpandedFA.OrderedSpectral.PerronPowers.Real
open MeasureTheory Filter
open scoped Topology
universe u
variable {Q : Type u} [TopologicalSpace Q] [CompactSpace Q]

/-- The real and imaginary coordinate maps on C(Q,ℂ), in the supremum norm. -/
def realCoord : C(Q, ℂ) →L[ℝ] C(Q, ℝ) :=
  Complex.reCLM.compLeftContinuous ℝ Q

def imagCoord : C(Q, ℂ) →L[ℝ] C(Q, ℝ) :=
  Complex.imCLM.compLeftContinuous ℝ Q

/-- Inclusion of real functions into complex functions. -/
def complexEmbed : C(Q, ℝ) →L[ℝ] C(Q, ℂ) :=
  Complex.ofRealCLM.compLeftContinuous ℝ Q

/-- Complexification of an arbitrary bounded real operator, on the actual
complex continuous-function space, rather than an assumed extension. -/
def complexify (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) : C(Q, ℂ) →L[ℂ] C(Q, ℂ) where
  toFun f := complexEmbed (K (realCoord f)) + Complex.I • complexEmbed (K (imagCoord f))
  map_add' f g := by simp only [map_add, smul_add]; abel
  map_smul' c f := by
    have hre : realCoord (c • f) = c.re • realCoord f - c.im • imagCoord f := by
      ext q; simp [realCoord, imagCoord, Complex.mul_re]
    have him : imagCoord (c • f) = c.im • realCoord f + c.re • imagCoord f := by
      ext q; simp [realCoord, imagCoord, Complex.mul_im]
      ring
    rw [hre, him, map_sub, map_add, map_smul, map_smul, map_smul, map_smul]
    ext q
    apply Complex.ext <;>
      simp [complexEmbed, Complex.mul_re, Complex.mul_im] <;> ring
  cont := ((complexEmbed.comp (K.comp realCoord)).continuous).add
    (((complexEmbed.comp (K.comp imagCoord)).continuous).const_smul Complex.I)

/-- For a real Banach operator the spectral radius uses its complexification. -/
def radius (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) : ℝ :=
  PerronEigenstructure.Spec.radius (complexify K)

def StronglyPositive (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) : Prop :=
  ∀ f : C(Q, ℝ), (∀ q, 0 ≤ f q) → f ≠ 0 → ∀ q, 0 < K f q

def AlgebraicallySimple (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (r : ℝ)
    (u : C(Q, ℝ)) : Prop :=
  ∀ n : ℕ, 0 < n →
    LinearMap.ker ((r • LinearMap.id - K.toLinearMap) ^ n) = Submodule.span ℝ {u}

def eigenprojection (u : C(Q, ℝ)) (φ : C(Q, ℝ) →L[ℝ] ℝ) :
    C(Q, ℝ) →L[ℝ] C(Q, ℝ) := φ.smulRight ((φ u)⁻¹ • u)

variable [MeasurableSpace Q]

def Eigenmeasure (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (r : ℝ)
    (φ : C(Q, ℝ) →L[ℝ] ℝ) (μ : Measure Q) : Prop :=
  FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon μ ∧ μ Set.univ = 1 ∧
  (∀ f : C(Q, ℝ), Integrable f μ ∧ φ f = ∫ q, f q ∂μ) ∧
  (∀ f : C(Q, ℝ), φ (K f) = r * φ f)

def InvariantProbability (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) (μ : Measure Q) : Prop :=
  FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon μ ∧ μ Set.univ = 1 ∧
  ∀ f : C(Q, ℝ), (∫ q, K f q ∂μ) = ∫ q, f q ∂μ

def PowerConclusion (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)) : Prop :=
  0 < radius K ∧
  ∃ (u : C(Q, ℝ)) (φ : C(Q, ℝ) →L[ℝ] ℝ) (μ : Measure Q),
    (∀ q, 0 < u q) ∧ K u = radius K • u ∧
    AlgebraicallySimple K (radius K) u ∧ Eigenmeasure K (radius K) φ μ ∧
    0 < φ u ∧
    (∀ (ζ : ℂ) (z : C(Q, ℂ)), z ≠ 0 → complexify K z = ζ • z →
      ζ ≠ (radius K : ℂ) → ‖ζ‖ < radius K) ∧
    Tendsto (fun n : ℕ => (radius K)⁻¹ ^ n • K ^ n) atTop
      (𝓝 (eigenprojection u φ)) ∧
    (∀ f q, eigenprojection u φ f q = u q * φ f / φ u)

def PowersTheorem : Prop :=
  ∀ (Q : Type u) [TopologicalSpace Q] [T2Space Q] [CompactSpace Q] [Nonempty Q]
    [MeasurableSpace Q] [BorelSpace Q] (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)),
    IsCompactOperator K → StronglyPositive K → PowerConclusion K

def MarkovTheorem : Prop :=
  ∀ (Q : Type u) [TopologicalSpace Q] [T2Space Q] [CompactSpace Q] [Nonempty Q]
    [MeasurableSpace Q] [BorelSpace Q] (K : C(Q, ℝ) →L[ℝ] C(Q, ℝ)),
    IsCompactOperator K → StronglyPositive K → K 1 = 1 →
    radius K = 1 ∧ ∃ (φ : C(Q, ℝ) →L[ℝ] ℝ) (μ : Measure Q),
      (∀ q, 0 < (1 : C(Q, ℝ)) q) ∧ K 1 = radius K • (1 : C(Q, ℝ)) ∧
      AlgebraicallySimple K (radius K) (1 : C(Q, ℝ)) ∧
      Eigenmeasure K (radius K) φ μ ∧ φ 1 = 1 ∧ InvariantProbability K μ ∧
      (∀ ν : Measure Q, InvariantProbability K ν → ν = μ) ∧
      Tendsto (fun n : ℕ => K ^ n) atTop (𝓝 (φ.smulRight 1))

end ExpandedFA.OrderedSpectral.PerronPowers.Real
