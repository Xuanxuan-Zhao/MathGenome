import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.MultiplierTranspose
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.FourierHilbertScale
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Position and momentum on the real line, represented in the existing
one-dimensional Euclidean coordinates. A point `x` has real coordinate `x 0`.
The Fourier transform is the accepted negative-2πi unitary. Definitions below
carry domains; the weak graph assertion identifies the spectral construction
of momentum with exactly the distributional first derivative. -/

noncomputable section
open MeasureTheory
open scoped SchwartzMap FourierTransform

namespace ExpandedFA.Models.PositionMomentum
open ExpandedFA.Fourier Multiplication Unbounded Sobolev

abbrev H := L2 1
abbrev S := Schwartz ℂ 1

/-- Pull an operator back by a unitary. Its domain is the full inverse image. -/
def unitaryPullback {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (U : E ≃ₗᵢ[ℂ] E) (A : Operator ℂ E E) : Operator ℂ E E where
  domain := A.domain.comap U.toLinearEquiv.toLinearMap
  toFun := U.symm.toLinearEquiv.toLinearMap.comp
    (A.toFun.comp (U.toLinearEquiv.toLinearMap.domRestrict
      (A.domain.comap U.toLinearEquiv.toLinearMap) |>.codRestrict A.domain (fun x => x.2)))

def canonicalPosition : Operator ℂ H H :=
  maximalMultiplier volume 2 (fun x : Euclidean 1 => (x 0 : ℂ))

def frequencyPosition : Operator ℂ H H :=
  maximalMultiplier volume 2 (fun ξ : Euclidean 1 => (2 * Real.pi * ξ 0 : ℝ))

def canonicalMomentum : Operator ℂ H H := unitaryPullback (l2Fourier 1) frequencyPosition

/-- Equality of regular distributions on all compactly supported smooth tests.
No conjugation and no boundary condition occur. -/
def HasWeakDerivative (f g : H) : Prop :=
  let toDomain : H →ₗᵢ[ℂ] DomainLp ℂ
      (⊤ : TopologicalSpace.Opens (Distributions.Domain 1)) 2 :=
    Lp.compMeasurePreservingₗᵢ ℂ (@WithLp.toLp 2 (Fin 1 → ℝ))
      (by simpa using PiLp.volume_preserving_toLp (Fin 1))
  lpDistribution (toDomain g) =
    Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue ℂ 1 ⊤ [0]
      (lpDistribution (toDomain f))

def H1 (f : H) : Prop := ∃ g : H, HasWeakDerivative f g

def schwartzSubmodule : Submodule ℂ H := (SchwartzMap.toLpCLM ℂ ℂ (E := Euclidean 1) 2 volume).range

def schwartzPosition (φ : S) : S := coordinateMultiply 0 φ

def schwartzMomentum (φ : S) : S :=
  (-Complex.I) • LineDeriv.lineDerivOpCLM ℂ S (basisVector (d := 1) 0) φ

namespace Spec

def positionType := Operator ℂ H H
def positionValue : positionType := canonicalPosition
def momentumType := Operator ℂ H H
def momentumValue : momentumType := canonicalMomentum

def PositionDomain : Prop := ∀ f : H,
  f ∈ canonicalPosition.domain ↔ MemLp (fun x => (x 0 : ℂ) * f x) 2 volume

def PositionApply : Prop := ∀ f : canonicalPosition.domain,
  (canonicalPosition f : Euclidean 1 → ℂ) =ᵐ[volume] fun x => (x 0 : ℂ) * (f : H) x

def WeakGraph : Prop := ∀ f g : H,
  (f, g) ∈ canonicalMomentum.graph ↔ HasWeakDerivative f (Complex.I • g)

def MomentumDomain : Prop := ∀ f : H, f ∈ canonicalMomentum.domain ↔ H1 f

def MomentumApply : Prop := ∀ (f : canonicalMomentum.domain) (g : H),
  HasWeakDerivative (f : H) g → canonicalMomentum f = (-Complex.I) • g

def SelfAdjoint : Prop := IsSelfAdjoint canonicalPosition ∧ IsSelfAdjoint canonicalMomentum

def FourierConjugation : Prop :=
  unitaryPullback (l2Fourier 1).symm canonicalMomentum = frequencyPosition

def Invariance : Prop := ∀ φ : S,
  (φ.toLp 2 volume, (schwartzPosition φ).toLp 2 volume) ∈ canonicalPosition.graph ∧
  (φ.toLp 2 volume, (schwartzMomentum φ).toLp 2 volume) ∈ canonicalMomentum.graph

def Cores : Prop :=
  OperatorDomainsSpec.coreValue canonicalPosition schwartzSubmodule ∧
  OperatorDomainsSpec.coreValue canonicalMomentum schwartzSubmodule

/-- Simultaneous approximation in the sum of both graph norms. -/
def JointCore : Prop := ∀ (f : H) (hq : f ∈ canonicalPosition.domain)
    (hp : f ∈ canonicalMomentum.domain) (ε : ℝ), 0 < ε → ∃ φ : S,
  ‖φ.toLp 2 volume - f‖ +
    ‖(schwartzPosition φ).toLp 2 volume - canonicalPosition ⟨f, hq⟩‖ +
    ‖(schwartzMomentum φ).toLp 2 volume - canonicalMomentum ⟨f, hp⟩‖ < ε

end Spec
end ExpandedFA.Models.PositionMomentum
