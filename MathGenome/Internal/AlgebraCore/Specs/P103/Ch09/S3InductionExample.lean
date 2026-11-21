import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.MackeyIrreducibility
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.InducedCharacter
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.S3CharacterTable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! The example at paper.tex 2165–2174. The permutation convention and the
standard zero-sum plane are shared with the earlier character table. The root
is arbitrary, so both primitive cube roots are included. -/
noncomputable section
namespace P103.Ch09.S3InductionExampleSpecs
open Ch08.S3CharacterTableSpecs

abbrev H : Subgroup S3 := alternatingGroup (Fin 3)
def c : H := ⟨threeCycle, by simp [H, threeCycle]⟩

def subgroupType : Prop :=
  H = Subgroup.closure ({threeCycle} : Set S3) ∧
  Nat.card H = 3 ∧ H.index = 2 ∧
  transposition ∉ H ∧
  transposition⁻¹ * threeCycle * transposition = threeCycle⁻¹ ∧
  (∀ s : S3, s ∉ H → s⁻¹ * threeCycle * s = threeCycle⁻¹) ∧
  (∀ g : S3, IsConj g transposition → ∀ x : S3, x⁻¹ * g * x ∉ H)

def rootIdentitiesType : Prop :=
  ∀ (ζ : ℂ), IsPrimitiveRoot ζ 3 →
    ζ⁻¹ = ζ ^ 2 ∧ ζ + ζ⁻¹ = -1 ∧ ζ ≠ ζ⁻¹

/-- Values on whole conjugacy classes, in the table's order. -/
def CharacterRow (χ : S3 → ℂ) : Prop :=
  χ 1 = 2 ∧ (∀ g, IsConj g transposition → χ g = 0) ∧
    (∀ g, IsConj g threeCycle → χ g = -1)

/-- A line on which the generator acts as the chosen primitive root, together
with the full conclusion for every realization of the actual tensor induction.
No property of the induced representation is assumed. -/
def realizationType : Prop :=
  ∀ (ζ : ℂ), IsPrimitiveRoot ζ 3 →
    ∃ ρ : Representation ℂ H ℂ,
      (∀ z : ℂ, ρ c z = ζ * z) ∧
      Ch08.Irreducible ℂ H ℂ ρ ∧
      (∀ s : S3, s ∉ H →
        ¬ Nonempty (ρ.Equiv (MackeyIrreducibility.normalTwist H ρ s))) ∧
      ∀ (D : InductionData H ρ) (_E : FunctionModelData H ρ D),
        letI := D.module
        FiniteDimensional ℂ (Induced H ρ) ∧
        Ch08.Irreducible ℂ S3 (Induced H ρ) D.representation ∧
        Module.finrank ℂ (Induced H ρ) = 2 ∧
        CharacterRow (Ch08.CharacterSpecs.characterValue D.representation) ∧
        Ch08.CharacterSpecs.characterValue D.representation threeCycle = ζ + ζ⁻¹ ∧
        Nonempty (standardValue.Equiv D.representation)

end P103.Ch09.S3InductionExampleSpecs
