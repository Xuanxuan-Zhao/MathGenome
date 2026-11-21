import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SymmetryAndDeficiencies
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.MeasurableSpectralCalculus

/-! Stone's theorem, paper.tex `fa2:p3:stone`, 15039–15065.
The Hilbert space is arbitrary, including nonseparable and zero spaces.
Time runs over all of ℝ. The spectral exponential is the bounded integral
of exp(itλ) against an actual real-base PVM resolving the operator.
The derivative is a two-sided norm limit on its full existence domain. -/
noncomputable section
open Filter Topology

namespace ExpandedFA.Semigroups.Stone
open Unbounded Unbounded.SymmetryAndDeficienciesSpec
open Unbounded.MeasurableSpectralCalculus
universe u

/-- A strongly continuous unitary group, with no assumed generator. -/
structure UnitaryGroup (H : Type u) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  operators : ℝ → H ≃ₗᵢ[ℂ] H
  at_zero : ∀ x, operators 0 x = x
  add_time : ∀ t s x, operators (t + s) x = operators t (operators s x)
  continuous_orbit : ∀ x, Continuous (fun t => operators t x)

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Full real-time norm difference quotient, punctured at h=0 below. -/
def differenceQuotient (U : UnitaryGroup H) (h : ℝ) (x : H) : H :=
  (h : ℂ)⁻¹ • (U.operators h x - x)

def HasDerivative (U : UnitaryGroup H) (x y : H) : Prop :=
  Tendsto (fun h => differenceQuotient U h x) (𝓝[≠] (0 : ℝ)) (𝓝 y)

/-- Equality with the derivative graph includes both necessity and sufficiency
of membership in D(A), and the value iAx whenever the derivative exists. -/
def DerivativeGraph (U : UnitaryGroup H) (A : Operator ℂ H H) : Prop :=
  ∀ x y, HasDerivative U x y ↔ (x, y) ∈ (Complex.I • A).graph

/-- The PVM formula U(t)=exp(itA), with the exact spectral domain in RealResolves. -/
def SpectralExponential (A : Operator ℂ H H) (U : UnitaryGroup H) : Prop :=
  ∃ (E : SpectralMeasure.ProjectionValuedMeasure ℝ H) (C : BoundedRealization E),
    measurableIntegral C (fun r : ℝ => (r : ℂ)) = A ∧
    ∀ t, (U.operators t).toLinearIsometry.toContinuousLinearMap =
      C.integral (fun r : ℝ => Complex.exp (Complex.I * (t : ℂ) * (r : ℂ)))

namespace Spec

/-- Both existence and uniqueness for an arbitrary given group, and its
exact two-sided derivative graph. Uniqueness applies to every self-adjoint
operator having the PVM formula, without assuming its derivative domain. -/
def Forward : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : UnitaryGroup H),
    ∃ A : Operator ℂ H H, selfAdjointValue A ∧ SpectralExponential A U ∧
      DerivativeGraph U A ∧ ∀ B : Operator ℂ H H,
        selfAdjointValue B → SpectralExponential B U → B = A

/-- Every self-adjoint operator yields a strongly continuous unitary group
through its PVM, with exactly its given domain as derivative domain. -/
def Converse : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : Operator ℂ H H), selfAdjointValue A →
    ∃ U : UnitaryGroup H, SpectralExponential A U ∧ DerivativeGraph U A

/-- For any PVM formula, not merely a selected constructed group. -/
def SpectralDerivative : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : Operator ℂ H H) (U : UnitaryGroup H),
    selfAdjointValue A → SpectralExponential A U → DerivativeGraph U A

def FullTheorem : Prop := Forward.{u} ∧ Converse.{u}

end Spec
end ExpandedFA.Semigroups.Stone
