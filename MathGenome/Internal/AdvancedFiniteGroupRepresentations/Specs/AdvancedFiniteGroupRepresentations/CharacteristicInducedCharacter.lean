import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.CharacteristicMultiplication
import Mathlib.RepresentationTheory.Induced

/-! The actual external tensor and coinvariant induction used in FR-C05 and FR-C07. -/

noncomputable section
open scoped TensorProduct BigOperators
open Classical

namespace Specs.AdvancedFiniteGroupRepresentations

universe u v

section
variable {a b : ℕ} {V : Type u} {W : Type v}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The external tensor product on the original tensor product of the carriers. -/
def externalTensorRepresentation
    (ρ : Representation ℂ (SymmetricGroup a) V)
    (τ : Representation ℂ (SymmetricGroup b) W) :
    Representation ℂ (SymmetricGroup a × SymmetricGroup b) (V ⊗[ℂ] W) :=
  Representation.tprod (ρ.comp (MonoidHom.fst _ _)) (τ.comp (MonoidHom.snd _ _))

end

def externalTensorRepresentationType :=
  ∀ {a b : ℕ} {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W],
    Representation ℂ (SymmetricGroup a) V → Representation ℂ (SymmetricGroup b) W →
    Representation ℂ (SymmetricGroup a × SymmetricGroup b) (V ⊗[ℂ] W)

def blockInduced_finiteDimensionalType : Prop :=
  ∀ {a b : ℕ} {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (SymmetricGroup a) V)
    (τ : Representation ℂ (SymmetricGroup b) W),
    FiniteDimensional ℂ (Representation.IndV (blockEmbedding a b)
      (externalTensorRepresentation ρ τ))

def blockInduced_character_applyType : Prop :=
  ∀ {a b : ℕ} {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (SymmetricGroup a) V)
    (τ : Representation ℂ (SymmetricGroup b) W) (σ : SymmetricGroup (a + b)),
    (Representation.ind (blockEmbedding a b) (externalTensorRepresentation ρ τ)).character σ =
      (Fintype.card (SymmetricGroup a × SymmetricGroup b) : ℂ)⁻¹ *
        ∑ x : SymmetricGroup (a + b), ∑ h : SymmetricGroup a × SymmetricGroup b,
          if x * blockEmbedding a b h * x⁻¹ = σ then
            ρ.character h.1 * τ.character h.2 else 0

def blockInduced_characterType : Prop :=
  ∀ {a b : ℕ} {V : Type u} {W : Type v}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ V] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (SymmetricGroup a) V)
    (τ : Representation ℂ (SymmetricGroup b) W),
    representationClassFunction
        (Representation.ind (blockEmbedding a b) (externalTensorRepresentation ρ τ)) =
      inducedExternal (representationClassFunction ρ) (representationClassFunction τ)

end Specs.AdvancedFiniteGroupRepresentations
