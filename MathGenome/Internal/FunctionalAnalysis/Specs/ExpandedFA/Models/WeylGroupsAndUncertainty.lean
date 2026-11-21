import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.PositionAndMomentum
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.StoneTheorem

/-! The group and uncertainty clauses of `fa2:p3:position-momentum`.
All identities on L² representatives are almost everywhere identities.
The weak identity and the uncertainty bound require only the common domain. -/
noncomputable section
open MeasureTheory
open scoped SchwartzMap

namespace ExpandedFA.Models.WeylGroupsAndUncertainty
open PositionMomentum ExpandedFA.Fourier ExpandedFA.Semigroups.Stone

namespace Spec

def Groups : Prop := ∃ U V : UnitaryGroup H,
  SpectralExponential canonicalPosition U ∧ DerivativeGraph U canonicalPosition ∧
  SpectralExponential canonicalMomentum V ∧ DerivativeGraph V canonicalMomentum ∧
  (∀ (a : ℝ) (f : H), (U.operators a f : Euclidean 1 → ℂ) =ᵐ[volume]
    fun x => Complex.exp (Complex.I * (a : ℂ) * (x 0 : ℂ)) * f x) ∧
  (∀ (b : ℝ) (f : H), (V.operators b f : Euclidean 1 → ℂ) =ᵐ[volume]
    fun x => f (x + b • basisVector (d := 1) 0)) ∧
  (∀ (a b : ℝ) (f : H), U.operators a (V.operators b f) =
    Complex.exp (-Complex.I * (a : ℂ) * (b : ℂ)) • V.operators b (U.operators a f))

def WeakCommutator : Prop := ∀ (f : H) (hq : f ∈ canonicalPosition.domain)
    (hp : f ∈ canonicalMomentum.domain),
  inner ℂ (canonicalPosition ⟨f, hq⟩) (canonicalMomentum ⟨f, hp⟩) -
    inner ℂ (canonicalMomentum ⟨f, hp⟩) (canonicalPosition ⟨f, hq⟩) =
      Complex.I * (‖f‖ ^ 2 : ℝ)

def RealMeans : Prop := ∀ (f : H) (hq : f ∈ canonicalPosition.domain)
    (hp : f ∈ canonicalMomentum.domain),
  (inner ℂ f (canonicalPosition ⟨f, hq⟩)).im = 0 ∧
  (inner ℂ f (canonicalMomentum ⟨f, hp⟩)).im = 0

def Uncertainty : Prop := ∀ (f : H) (hq : f ∈ canonicalPosition.domain)
    (hp : f ∈ canonicalMomentum.domain), ‖f‖ = 1 →
  let q := (inner ℂ f (canonicalPosition ⟨f, hq⟩)).re
  let p := (inner ℂ f (canonicalMomentum ⟨f, hp⟩)).re
  (1 / 2 : ℝ) ≤ ‖canonicalPosition ⟨f, hq⟩ - (q : ℂ) • f‖ *
    ‖canonicalMomentum ⟨f, hp⟩ - (p : ℂ) • f‖

end Spec
end ExpandedFA.Models.WeylGroupsAndUncertainty
