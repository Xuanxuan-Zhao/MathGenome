import MathGenome.Internal.AlgebraCore.Specs.P103.Ch11.TorExactSequences
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-! The finite-length stage of paper.tex 3275–3286. Tor is the upstream
ordinary right-resolution Tor, using the canonical right action on a
commutative left module. A residue model permits modules in arbitrary
universes: it is an actual linear copy of R/m, not an assumed certificate. -/
namespace P103.Ch12.FiniteLengthTorVanishing
open P103.BalancedTensor P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
universe u v w

/-- Vanishing, independently of the ordinary projective resolution used. -/
def TorOneVanishes (R : Type u) [CommRing R]
    (F : Type v) [AddCommGroup F] [Module R F]
    (M : Type w) [AddCommGroup M] [Module R M] : Prop :=
  letI := commRightModule R F
  ∀ P : LeftResolution Rᵐᵒᵖ F, P.IsProjective → Subsingleton (TorWith P M 1)
end P103.Ch12.FiniteLengthTorVanishing

namespace P103.Specs.Ch12.FiniteLengthTorVanishing
open P103.BalancedTensor P103.Specs.Ch10.Comparison
open P103.Specs.Ch11.ExtTorDefinitions
open P103.Ch12.FiniteLengthTorVanishing
universe u v w

def simple_equiv_residueType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (F : Type v) [AddCommGroup F] [Module R F] [IsSimpleModule R F],
    Nonempty (F ≃ₗ[R] R ⧸ IsLocalRing.maximalIdeal R)

/-- One residue resolution suffices; M has no finite generation hypothesis.
The arbitrary residue model k is useful when F and R have different universes. -/
def finite_length_vanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (k F : Type v) [AddCommGroup k] [Module R k]
    [AddCommGroup F] [Module R F]
    (M : Type w) [AddCommGroup M] [Module R M]
    (_ek : k ≃ₗ[R] R ⧸ IsLocalRing.maximalIdeal R),
    letI := commRightModule R k
    ∀ (Pk : LeftResolution Rᵐᵒᵖ k), Pk.IsProjective →
    Subsingleton (TorWith Pk M 1) → IsFiniteLength R F → TorOneVanishes R F M

/-- The direct statement with the actual residue quotient. -/
def residue_finite_length_vanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (F : Type u) [AddCommGroup F] [Module R F]
    (M : Type w) [AddCommGroup M] [Module R M],
    letI := commRightModule R (R ⧸ IsLocalRing.maximalIdeal R)
    ∀ (Pk : LeftResolution Rᵐᵒᵖ (R ⧸ IsLocalRing.maximalIdeal R)), Pk.IsProjective →
    Subsingleton (TorWith Pk M 1) → IsFiniteLength R F → TorOneVanishes R F M

def power_quotient_finite_lengthType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (j : ℕ), 1 ≤ j → IsFiniteLength R (R ⧸ IsLocalRing.maximalIdeal R ^ j)

def quotient_finite_lengthType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (j : ℕ), 1 ≤ j →
    IsFiniteLength R (R ⧸ (I ⊔ IsLocalRing.maximalIdeal R ^ j))

/-- The particular quotients used in the ideal test for flatness. -/
def quotient_vanishingType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M : Type w) [AddCommGroup M] [Module R M],
    letI := commRightModule R (R ⧸ IsLocalRing.maximalIdeal R)
    ∀ (Pk : LeftResolution Rᵐᵒᵖ (R ⧸ IsLocalRing.maximalIdeal R)), Pk.IsProjective →
    Subsingleton (TorWith Pk M 1) → ∀ (I : Ideal R) (j : ℕ), 1 ≤ j →
    TorOneVanishes R (R ⧸ (I ⊔ IsLocalRing.maximalIdeal R ^ j)) M

end P103.Specs.Ch12.FiniteLengthTorVanishing
