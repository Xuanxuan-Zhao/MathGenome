import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.IsotypicMatrixBlocks
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.LengthBound
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-! FR-D06, source lines 1512–1539.  Positions are zero-based: the first k
positions are {i | i.val < k}. The block support condition below is the
finite direct sum of precisely the full matrix blocks of length > d.
No positivity assumption is imposed on either n or dim V. -/
noncomputable section
open scoped BigOperators
universe u
namespace Specs.AdvancedFiniteGroupRepresentations

/-- The canonical linear extension of the left slot action. -/
def tensorSlotAction (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ) :
    GroupAlgebra n →ₐ[ℂ] Module.End ℂ (TensorPower V n) :=
  MonoidAlgebra.lift ℂ _ _
    { toFun := slotOperator V n
      map_one' := by
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro v
        exact PiTensorProduct.reindex_tprod (1 : SymmetricGroup n) v
      map_mul' := by
        intro s t
        apply PiTensorProduct.ext
        apply MultilinearMap.ext
        intro v
        change slotOperator V n (s * t) (pureTensor V n v) =
          slotOperator V n s (slotOperator V n t (pureTensor V n v))
        simp only [slotOperator, pureTensor, LinearEquiv.coe_coe,
          PiTensorProduct.reindex_tprod]
        rfl }

/-- All independent matrix coordinates supported on the omitted shapes. -/
def omittedMatrixBlocks (n d : ℕ) :
    Submodule ℂ (∀ p : Partition n, Module.End ℂ (SpechtModule p)) where
  carrier := {F | ∀ p, length p ≤ d → F p = 0}
  zero_mem' := by simp
  add_mem' := by intro F G hF hG p hp; simp [hF p hp, hG p hp]
  smul_mem' := by intro c F hF p hp; simp [hF p hp]

/-- Permutations of the first k positions, fixing every other position. -/
def initialPositionSubgroup (n k : ℕ) : Subgroup (SymmetricGroup n) where
  carrier := {s | ∀ i : Fin n, k ≤ i.val → s i = i}
  one_mem' := by intro i hi; rfl
  mul_mem' := by intro s t hs ht i hi; change s (t i) = i; rw [ht i hi, hs i hi]
  inv_mem' := by intro s hs i hi; exact (s.symm_apply_eq).mpr (hs i hi).symm

instance initialPositionSubgroupFintype (n k : ℕ) :
    Fintype (initialPositionSubgroup n k) := Fintype.ofFinite _

/-- Unnormalized signed sum, so for k=1 the generator is the unit. -/
def initialAlternator (n k : ℕ) : GroupAlgebra n :=
  ∑ s : initialPositionSubgroup n k,
    MonoidAlgebra.single s.val (permutationSign s.val)

def tensorSlotActionType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] (n : ℕ),
  GroupAlgebra n →ₐ[ℂ] Module.End ℂ (TensorPower V n)
def omittedMatrixBlocksType := ∀ n d : ℕ,
  Submodule ℂ (∀ p : Partition n, Module.End ℂ (SpechtModule p))
def initialPositionSubgroupType := ∀ n k : ℕ, Subgroup (SymmetricGroup n)
def initialAlternatorType := (n : ℕ) → ℕ → GroupAlgebra n

/-- The entire kernel, in the actual full-matrix-block decomposition.
The quantification over inherited actions makes this independent of choices. -/
def tensorKernel_blocksType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)),
    (∀ p, InheritedSpechtAction p (σ p)) →
    LinearMap.ker (tensorSlotAction V n).toLinearMap =
      (omittedMatrixBlocks n (Module.finrank ℂ V)).comap
        (spechtFamilyAlgebraMap σ).toLinearMap

def tensorKernel_generatedType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    Module.finrank ℂ V < n →
      TwoSidedIdeal.ker (tensorSlotAction V n).toRingHom =
        TwoSidedIdeal.span {initialAlternator n (Module.finrank ℂ V + 1)}

def tensorSlotAction_injectiveType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    n ≤ Module.finrank ℂ V → Function.Injective (tensorSlotAction V n)

def initialAlternator_oneType : Prop := ∀ n : ℕ, initialAlternator n 1 = 1

def tensorKernel_zero_dimensionType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    0 < n → Module.finrank ℂ V = 0 →
      TwoSidedIdeal.ker (tensorSlotAction V n).toRingHom = ⊤

end Specs.AdvancedFiniteGroupRepresentations
