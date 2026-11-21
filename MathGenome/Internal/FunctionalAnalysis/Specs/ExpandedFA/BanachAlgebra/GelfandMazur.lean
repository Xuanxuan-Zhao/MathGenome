import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.NeumannResolvent
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.SpectralRadius
import Mathlib.Algebra.Algebra.Equiv

/-!
Independent statements for the complete theorem `fa2:p2:spectrum-radius`,
paper.tex:10041–10072. The chapter's unital Banach convention is complete,
nonzero, complex, and normalized by ‖1‖ = 1. No commutativity is assumed.

Division is expressed by invertibility of every nonzero element. In particular
we do not impose the stronger multiplicative-norm axiom of `NormedDivisionRing`.
The unique scalar representation and the unique isometric algebra equivalence
express the canonical identification with ℂ. Positive power roots are indexed
by n+1, so the infimum includes exactly the positive integers.
-/

namespace Specs.ExpandedFA.BanachAlgebra.GelfandMazur

open Conventions Filter
open scoped Topology

universe u

/-- All spectral conclusions preceding the division-algebra consequence. -/
def SpectrumAndRadius : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    ∀ a : A,
      (AlgebraSpectrumValue ℂ A a).Nonempty ∧
      IsCompact (AlgebraSpectrumValue ℂ A a) ∧
      (AlgebraSpectrumValue ℂ A a ⊆ {z : ℂ | ‖z‖ ≤ ‖a‖}) ∧
      AnalyticOnNhd ℂ (AlgebraResolventValue ℂ A a) (AlgebraResolventSetValue ℂ A a) ∧
      (∀ (lam mu : ℂ),
        lam ∈ AlgebraResolventSetValue ℂ A a → mu ∈ AlgebraResolventSetValue ℂ A a →
        AlgebraResolventValue ℂ A a lam - AlgebraResolventValue ℂ A a mu =
          (mu - lam) •
            (AlgebraResolventValue ℂ A a lam * AlgebraResolventValue ℂ A a mu)) ∧
      Tendsto (fun n : ℕ => ‖a ^ (n + 1)‖ ^ (1 / ((n + 1 : ℕ) : ℝ))) atTop
        (𝓝 (AlgebraSpectralRadiusValue ℂ A a)) ∧
      sInf (Set.range (fun n : ℕ => ‖a ^ (n + 1)‖ ^ (1 / ((n + 1 : ℕ) : ℝ)))) =
        AlgebraSpectralRadiusValue ℂ A a

/-- Every element in a complex Banach division algebra is a unique scalar. -/
def ScalarRepresentation : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    (∀ a : A, a ≠ 0 → IsUnit a) →
    ∀ a : A, ∃! z : ℂ, z • (1 : A) = a

/-- The scalar inclusion is the unique isometric ℂ-algebra identification. -/
def CanonicalIsometricIdentification : Prop :=
  ∀ (A : Type u) [NormedRing A] [NormedAlgebra ℂ A], IsUnitalBanachAlgebraValue A →
    (∀ a : A, a ≠ 0 → IsUnit a) →
    ∃! e : ℂ ≃ₐ[ℂ] A, (∀ z : ℂ, e z = z • (1 : A)) ∧ Isometry e

end Specs.ExpandedFA.BanachAlgebra.GelfandMazur
