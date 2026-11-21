import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
Independent statements for the regular-local step in SN-09
(paper.tex:4273–4276), with the dimension-zero boundary from CM-08.
Regular locality includes the Noetherian and nontrivial local hypotheses.
No domain hypothesis is imposed. The existential in the DVR statement
supplies the domain instance required by Mathlib's DVR predicate.
-/

universe u
namespace AdvCommAlg.Normality.Specs

def regularLocal_isDomainType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R], IsDomain R

def regularLocal_dimension_zero_isFieldType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    ringKrullDim R = 0 → IsField R

def regularLocal_dimension_one_isDVRType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    ringKrullDim R = 1 → ∃ h : IsDomain R, @IsDiscreteValuationRing R _ h

def regularLocal_low_dimension_integrallyClosedType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsRegularLocalRing R],
    ringKrullDim R ≤ 1 → IsDomain R ∧ IsIntegrallyClosed R

end AdvCommAlg.Normality.Specs
