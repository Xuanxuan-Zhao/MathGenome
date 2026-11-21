import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorEvaluation
import Mathlib.Algebra.Lie.UniversalEnveloping

/-! FR-D10, construction of the Lie action (source lines 1683–1707), with
FR-D01's zero-degree conventions. The image comparison with B belongs to
FR-D10, separately from this construction. No finite-dimensionality is needed
for the algebraic construction. The bracket is Mathlib's commutator bracket. -/
noncomputable section
open scoped BigOperators
attribute [local instance] LieRing.ofAssociativeRing
universe u
namespace Specs.AdvancedFiniteGroupRepresentations
variable (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- Apply an endomorphism in one position and the identity elsewhere. -/
def tensorSlotInsertion (n : ℕ) (i : Fin n) :
    Module.End ℂ V →ₗ[ℂ] Module.End ℂ (TensorPower V n) :=
  (PiTensorProduct.mapMultilinear ℂ (fun _ : Fin n => V) (fun _ => V)).toLinearMap
    (fun _ => 1) i

/-- The sum of the one-position operators, linear in the endomorphism. -/
def derivedTensorOperator (n : ℕ) :
    Module.End ℂ V →ₗ[ℂ] Module.End ℂ (TensorPower V n) :=
  ∑ i : Fin n, tensorSlotInsertion V n i

def tensorSlotInsertionType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
  (n : ℕ), Fin n → Module.End ℂ V →ₗ[ℂ] Module.End ℂ (TensorPower V n)
def derivedTensorOperatorType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
  (n : ℕ), Module.End ℂ V →ₗ[ℂ] Module.End ℂ (TensorPower V n)

def tensorSlotInsertion_pureType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ) (i : Fin n)
    (T : Module.End ℂ V) (v : Fin n → V),
    tensorSlotInsertion V n i T (pureTensor V n v) =
      pureTensor V n (Function.update v i (T (v i)))

def derivedTensorOperator_pureType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (T : Module.End ℂ V) (v : Fin n → V),
    derivedTensorOperator V n T (pureTensor V n v) =
      ∑ i : Fin n, pureTensor V n (Function.update v i (T (v i)))

def derivedTensorOperator_lieType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ) (T U : Module.End ℂ V),
    derivedTensorOperator V n ⁅T, U⁆ =
      ⁅derivedTensorOperator V n T, derivedTensorOperator V n U⁆

def derivedTensorOperator_commuteType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ)
    (T : Module.End ℂ V) (s : SymmetricGroup n),
    Commute (slotOperator V n s) (derivedTensorOperator V n T)

/-- Bundled Lie and unital enveloping-algebra actions, and the induced action
on each *actual* equivariant Hom space, all with their specified formulas.
The witnesses are maps, not certificates assumed of any input. -/
def derivedTensorAction_existsType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
    ∃ ρ : Module.End ℂ V →ₗ⁅ℂ⁆ Module.End ℂ (TensorPower V n),
      (∀ T, ρ T = derivedTensorOperator V n T) ∧
      ∃ Φ : UniversalEnvelopingAlgebra ℂ (Module.End ℂ V) →ₐ[ℂ]
          Module.End ℂ (TensorPower V n),
        (∀ T, Φ (UniversalEnvelopingAlgebra.ι ℂ T) = derivedTensorOperator V n T) ∧
        (∀ s a, Commute (slotOperator V n s) (Φ a)) ∧
        ∀ p : Partition n,
          ∃ τ : Module.End ℂ V →ₗ⁅ℂ⁆ Module.End ℂ (TensorMultiplicity V p),
          ∃ Ψ : UniversalEnvelopingAlgebra ℂ (Module.End ℂ V) →ₐ[ℂ]
              Module.End ℂ (TensorMultiplicity V p),
            (∀ T, Ψ (UniversalEnvelopingAlgebra.ι ℂ T) = τ T) ∧
            (∀ T (f : TensorMultiplicity V p) v, (τ T f).val v = derivedTensorOperator V n T (f.val v)) ∧
            (∀ a (f : TensorMultiplicity V p) v, (Ψ a f).val v = Φ a (f.val v))

def derivedTensorOperator_zeroType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V], derivedTensorOperator V 0 = 0

/-- At degree zero every unital extension has precisely scalar image,
including when V itself is zero. -/
def derivedTensor_zero_scalar_imageType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
    (Φ : UniversalEnvelopingAlgebra ℂ (Module.End ℂ V) →ₐ[ℂ]
      Module.End ℂ (TensorPower V 0)), Φ.range = ⊥

end Specs.AdvancedFiniteGroupRepresentations
