import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Independent statements for the radius stage of `fa2:p2:spectrum-radius`,
paper.tex:10041–10068. The radius is the accepted real supremum of the norms
of the algebraic spectrum. The chapter assumes a complete, nonzero complex
unital normed algebra with ‖1‖ = 1; commutativity is not required.

Positive exponents are enumerated as n+1, n : ℕ. Thus the infimum excludes
n=0, and real powers of nonnegative norms include zero and nilpotent elements.
No nonvanishing assumption on the radius or on any power is made.
-/

namespace Specs.ExpandedFA.BanachAlgebra.SpectralRadius

open Conventions Filter
open scoped Topology

universe u

def RadiusMaximum : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ a : A,
    (∃ z ∈ AlgebraSpectrumValue ℂ A a, ‖z‖ = AlgebraSpectralRadiusValue ℂ A a) ∧
      (∀ z ∈ AlgebraSpectrumValue ℂ A a, ‖z‖ ≤ AlgebraSpectralRadiusValue ℂ A a) ∧
      0 ≤ AlgebraSpectralRadiusValue ℂ A a ∧ AlgebraSpectralRadiusValue ℂ A a ≤ ‖a‖

def RadiusNativeIdentification : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ a : A, ENNReal.ofReal (AlgebraSpectralRadiusValue ℂ A a) = spectralRadius ℂ a

def RootLimit : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ a : A,
    Tendsto (fun n : ℕ => ‖a ^ (n + 1)‖ ^ (1 / ((n + 1 : ℕ) : ℝ))) atTop
      (𝓝 (AlgebraSpectralRadiusValue ℂ A a))

def RootInfimum : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ a : A,
    sInf (Set.range (fun n : ℕ => ‖a ^ (n + 1)‖ ^ (1 / ((n + 1 : ℕ) : ℝ)))) =
      AlgebraSpectralRadiusValue ℂ A a

end Specs.ExpandedFA.BanachAlgebra.SpectralRadius
