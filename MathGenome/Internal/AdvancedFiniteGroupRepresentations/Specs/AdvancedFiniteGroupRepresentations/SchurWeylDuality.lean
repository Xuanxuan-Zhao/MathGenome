import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.FirstCentralizer
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.IsotypicMatrixBlocks
import Mathlib.RepresentationTheory.Irreducible

/-! FR-D04, source lines 1391–1466. All spaces and operators are the canonical
ones of the evaluation interface. Nontriviality is required only for
irreducibility and for the assertion that no isomorphism exists. -/
noncomputable section
open scoped TensorProduct DirectSum
universe u
namespace Specs.AdvancedFiniteGroupRepresentations
variable (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- The GL(V) representation by postcomposition on Hom_{S_n}(S^p,V^{⊗n}). -/
def multiplicityRepresentation {n : ℕ} (p : Partition n) :
    Representation ℂ (LinearGroup V) (TensorMultiplicity V p) where
  toFun := tensorMultiplicityOperator V p
  map_one' := by
    ext f v
    change diagonalOperator V n 1 (f.val v) = f.val v
    simp [diagonalOperator]
  map_mul' g h := by
    ext f v
    change diagonalOperator V n (g * h) (f.val v) =
      diagonalOperator V n g (diagonalOperator V n h (f.val v))
    change PiTensorProduct.map (fun _ : Fin n => g.toLinearMap.comp h.toLinearMap) (f.val v) = _
    rw [PiTensorProduct.map_comp]
    rfl

def schurWeylEvaluationType : Prop := tensorEvaluation_isomorphismType.{u}

def tensorMultiplicity_irreducibleType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} (p : Partition n) [Nontrivial (TensorMultiplicity V p)],
    (multiplicityRepresentation V p).IsIrreducible

def tensorMultiplicity_intertwiner_eq_zeroType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} (p q : Partition n), p ≠ q →
    ∀ k : TensorMultiplicity V p →ₗ[ℂ] TensorMultiplicity V q,
      (∀ (g : LinearGroup V) (f : TensorMultiplicity V p),
        k (tensorMultiplicityOperator V p g f) = tensorMultiplicityOperator V q g (k f)) →
      k = 0

def tensorMultiplicity_nonisomorphicType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {n : ℕ} (p q : Partition n) [Nontrivial (TensorMultiplicity V p)]
    [Nontrivial (TensorMultiplicity V q)], p ≠ q →
    ¬ Nonempty (Representation.Equiv (multiplicityRepresentation V p) (multiplicityRepresentation V q))

def secondCentralizerType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    Subalgebra.centralizer ℂ (tensorB V n : Set (Module.End ℂ (TensorPower V n))) =
      tensorA V n

/-- The full theorem, with zero summands retained in the canonical evaluation
and excluded only from the irreducibility and nonisomorphism clauses. -/
def schurWeylDualityType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    (∃ e : TensorEvaluationSum V n ≃ₗ[ℂ] TensorPower V n,
      e.toLinearMap = tensorEvaluationMap V n ∧
      ∀ (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)),
        (∀ p, InheritedSpechtAction p (σ p)) →
        ∀ (s : SymmetricGroup n) (g : LinearGroup V) (x : TensorEvaluationSum V n),
          e (tensorEvaluationOperator V σ s g x) =
            slotOperator V n s (diagonalOperator V n g (e x))) ∧
    (∀ p : Partition n, Nontrivial (TensorMultiplicity V p) →
      (multiplicityRepresentation V p).IsIrreducible) ∧
    (∀ p q : Partition n, Nontrivial (TensorMultiplicity V p) →
      Nontrivial (TensorMultiplicity V q) → p ≠ q →
      ¬ Nonempty (Representation.Equiv (multiplicityRepresentation V p) (multiplicityRepresentation V q))) ∧
    Subalgebra.centralizer ℂ (tensorB V n : Set (Module.End ℂ (TensorPower V n))) = tensorA V n

end Specs.AdvancedFiniteGroupRepresentations
