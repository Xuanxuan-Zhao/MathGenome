import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Smooth.RelativeRank
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! SM-09, additivity in a compatible smooth tower (paper.tex:1242–1244,
1252–1257). The first fiber is extended along the canonical embedding of
residue fields at a prime and its contraction. -/
namespace Specs.AdvCommAlg.Smooth.RelativeRankComposition

universe u v w
noncomputable section
open scoped TensorProduct

/-- The canonical residue-field extension for a prime and its contraction. -/
@[instance_reducible]
def residueExtension (B : Type v) (C : Type w) [CommRing B] [CommRing C]
    [Algebra B C] (r : PrimeSpectrum C) :
    Algebra (r.comap (algebraMap B C)).asIdeal.ResidueField r.asIdeal.ResidueField :=
  (Ideal.ResidueField.map _ _ (algebraMap B C) rfl).toAlgebra

/-- Compatibility of the canonical residue extension with the B-action. -/
theorem residueExtensionTower (B : Type v) (C : Type w) [CommRing B] [CommRing C]
    [Algebra B C] (r : PrimeSpectrum C) :
    letI := residueExtension B C r
    IsScalarTower B (r.comap (algebraMap B C)).asIdeal.ResidueField
      r.asIdeal.ResidueField := by
  let := residueExtension B C r
  apply IsScalarTower.of_algebraMap_eq
  intro b
  exact (Ideal.ResidueField.map_algebraMap _ _ (algebraMap B C) rfl b).symm

/-- An actual linear identification, with its formula on pure tensors.
No smoothness is needed for the residue-field scalar extension itself. -/
def residueFiberIdentification : Prop := ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C] [Algebra A B] [Algebra B C]
    (r : PrimeSpectrum C),
  let q := r.comap (algebraMap B C)
  letI := residueExtension B C r
  ∃ e : (r.asIdeal.ResidueField ⊗[C] (C ⊗[B] KaehlerDifferential A B)) ≃ₗ[
      r.asIdeal.ResidueField]
      (r.asIdeal.ResidueField ⊗[q.asIdeal.ResidueField]
        (q.asIdeal.ResidueField ⊗[B] KaehlerDifferential A B)),
    ∀ (t : r.asIdeal.ResidueField) (c : C) (ω : KaehlerDifferential A B),
      e (t ⊗ₜ[C] (c ⊗ₜ[B] ω)) =
        (algebraMap C r.asIdeal.ResidueField c * t) ⊗ₜ[q.asIdeal.ResidueField]
          (1 ⊗ₜ[B] ω)

/-- Additivity of the residue-field dimensions at every prime of C. -/
def compositionRank : Prop := ∀ (A : Type u) (B : Type v) (C : Type w)
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C],
  smoothValue A B → smoothValue B C → ∀ r : PrimeSpectrum C,
    RelativeRank.relativeRankValue A C r =
      RelativeRank.relativeRankValue A B (r.comap (algebraMap B C)) +
        RelativeRank.relativeRankValue B C r

end
end Specs.AdvCommAlg.Smooth.RelativeRankComposition
