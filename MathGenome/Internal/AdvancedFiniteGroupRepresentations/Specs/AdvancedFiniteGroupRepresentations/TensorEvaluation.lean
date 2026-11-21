import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.TensorActions
import MathGenome.Internal.AdvancedFiniteGroupRepresentations.Specs.AdvancedFiniteGroupRepresentations.SpechtClassification
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.Algebra.DirectSum.Module

/-! FR-D04 (evaluation portion), source lines 1391–1426, with the chapter's
zero-space conventions. The Hom space consists of actual linear maps on the
original Specht subspace. Equivariance is expressed through its inclusion, so
no choice of a Specht action or unproved stability certificate is assumed.
The operator on the direct sum below uses any inherited Specht action;
the conclusion quantifies over all such actions. -/
noncomputable section
open scoped TensorProduct DirectSum
universe u
namespace Specs.AdvancedFiniteGroupRepresentations
variable (V : Type u) [AddCommGroup V] [Module ℂ V]

/-- The actual space Hom_{S_n}(S^p,V^{⊗n}). -/
def tensorMultiplicitySpace {n : ℕ} (p : Partition n) :
    Submodule ℂ (SpechtModule p →ₗ[ℂ] TensorPower V n) where
  carrier := {f | ∀ (s : SymmetricGroup n) (v w : SpechtModule p),
    w.val = permutationRepresentation p s v.val →
      f w = slotOperator V n s (f v)}
  zero_mem' := by simp
  add_mem' := by
    intro f h hf hh s v w hw
    simpa using congrArg₂ (· + ·) (hf s v w hw) (hh s v w hw)
  smul_mem' := by
    intro a f hf s v w hw
    simpa using congrArg (a • ·) (hf s v w hw)

abbrev TensorMultiplicity {n : ℕ} (p : Partition n) := ↥(tensorMultiplicitySpace V p)

-- Make the additive group instance explicit across the Hom-space subtype.
instance tensorMultiplicityAddCommGroup {n : ℕ} (p : Partition n) :
    AddCommGroup (TensorMultiplicity V p) := (tensorMultiplicitySpace V p).addCommGroup

private theorem slot_diagonal_commute (n : ℕ) (s : SymmetricGroup n)
    (g : LinearGroup V) :
    (slotOperator V n s).comp (diagonalOperator V n g) =
      (diagonalOperator V n g).comp (slotOperator V n s) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change slotOperator V n s (diagonalOperator V n g (pureTensor V n v)) =
    diagonalOperator V n g (slotOperator V n s (pureTensor V n v))
  simp only [slotOperator, diagonalOperator, pureTensor, LinearEquiv.coe_coe,
    PiTensorProduct.map_tprod, PiTensorProduct.reindex_tprod]

/-- Postcomposition by the simultaneous change of vectors. -/
def tensorMultiplicityOperator {n : ℕ} (p : Partition n) (g : LinearGroup V) :
    Module.End ℂ (TensorMultiplicity V p) where
  toFun f := ⟨(diagonalOperator V n g).comp f.val, by
    intro s v w hw
    change diagonalOperator V n g (f.val w) = _
    rw [f.property s v w hw]
    exact congrArg (fun k : Module.End ℂ (TensorPower V n) => k (f.val v))
      (slot_diagonal_commute V n s g).symm⟩
  map_add' f h := by
    apply Subtype.ext; ext v
    change diagonalOperator V n g (f.val v + h.val v) = _
    exact map_add _ _ _
  map_smul' a f := by
    apply Subtype.ext; ext v
    change diagonalOperator V n g (a • f.val v) = _
    exact map_smul _ _ _

abbrev TensorEvaluationSum (n : ℕ) :=
  ⨁ p : Partition n, SpechtModule p ⊗[ℂ] TensorMultiplicity V p

instance tensorEvaluationSumAddCommGroup (n : ℕ) : AddCommGroup (TensorEvaluationSum V n) :=
  @DirectSum.instAddCommGroup _ _ (fun _ => TensorProduct.addCommGroup)

/-- Evaluation on one summand, in the order u ⊗ f ↦ f(u). -/
def tensorEvaluationSummand {n : ℕ} (p : Partition n) :
    SpechtModule p ⊗[ℂ] TensorMultiplicity V p →ₗ[ℂ] TensorPower V n :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun f => f.val v
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      map_add' := by intros; ext f; exact map_add f.val _ _
      map_smul' := by intros; ext f; exact map_smul f.val _ _ }

/-- The canonical evaluation map on the full direct sum, including zero summands. -/
def tensorEvaluationMap (n : ℕ) : TensorEvaluationSum V n →ₗ[ℂ] TensorPower V n :=
  DirectSum.toModule ℂ (Partition n) (TensorPower V n) (tensorEvaluationSummand V)

/-- Product action on the sum: S_n acts on Specht, GL(V) on multiplicities. -/
def tensorEvaluationOperator {n : ℕ}
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (s : SymmetricGroup n) (g : LinearGroup V) :
    Module.End ℂ (TensorEvaluationSum V n) :=
  DirectSum.lmap (fun p => TensorProduct.map (σ p s) (tensorMultiplicityOperator V p g))

def tensorMultiplicitySpaceType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
  {n : ℕ} (p : Partition n), Submodule ℂ (SpechtModule p →ₗ[ℂ] TensorPower V n)
def TensorMultiplicityType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
  {n : ℕ}, Partition n → Type u
-- A tensor with a Type-0 Specht factor lives in the universe of V.
def TensorEvaluationSumType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V], ℕ → Type u

def tensorMultiplicityOperatorType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
  {n : ℕ} (p : Partition n), LinearGroup V → Module.End ℂ (TensorMultiplicity V p)
def tensorEvaluationSummandType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
  {n : ℕ} (p : Partition n),
    SpechtModule p ⊗[ℂ] TensorMultiplicity V p →ₗ[ℂ] TensorPower V n
def tensorEvaluationMapType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
  (n : ℕ), TensorEvaluationSum V n →ₗ[ℂ] TensorPower V n
def tensorEvaluationOperatorType := ∀ (V : Type u) [AddCommGroup V] [Module ℂ V]
  {n : ℕ}, (∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)) →
    SymmetricGroup n → LinearGroup V → Module.End ℂ (TensorEvaluationSum V n)

def tensorMultiplicityOperator_applyType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] {n : ℕ} (p : Partition n)
    (g : LinearGroup V) (f : TensorMultiplicity V p) (v : SpechtModule p),
    (tensorMultiplicityOperator V p g f).val v = diagonalOperator V n g (f.val v)

def tensorMultiplicityOperator_oneType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] {n : ℕ} (p : Partition n),
    tensorMultiplicityOperator V p 1 = 1

def tensorMultiplicityOperator_mulType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] {n : ℕ} (p : Partition n)
    (g h : LinearGroup V), tensorMultiplicityOperator V p (g * h) =
      tensorMultiplicityOperator V p g * tensorMultiplicityOperator V p h

def tensorEvaluationMap_pureType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] {n : ℕ} (p : Partition n)
    (v : SpechtModule p) (f : TensorMultiplicity V p),
    tensorEvaluationMap V n (DirectSum.lof ℂ _ _ p (v ⊗ₜ[ℂ] f)) = f.val v

def tensorEvaluationMap_bijectiveType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    Function.Bijective (tensorEvaluationMap V n)

def tensorEvaluation_equivariantType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)),
    (∀ p, InheritedSpechtAction p (σ p)) →
    ∀ (s : SymmetricGroup n) (g : LinearGroup V) (x : TensorEvaluationSum V n),
    tensorEvaluationMap V n (tensorEvaluationOperator V σ s g x) =
      slotOperator V n s (diagonalOperator V n g (tensorEvaluationMap V n x))

def tensorMultiplicity_zero_dimensionType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    0 < n → Module.finrank ℂ V = 0 →
      ∀ p : Partition n, Subsingleton (TensorMultiplicity V p)

def tensorMultiplicity_empty_lineType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V],
    ∃ e : TensorMultiplicity V emptyPartition ≃ₗ[ℂ] ℂ,
      ∀ (g : LinearGroup V) (f : TensorMultiplicity V emptyPartition),
        e (tensorMultiplicityOperator V emptyPartition g f) = e f

def tensorEvaluationOperator_oneType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)),
    tensorEvaluationOperator V σ 1 1 = 1

def tensorEvaluationOperator_mulType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] {n : ℕ}
    (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p))
    (s t : SymmetricGroup n) (g h : LinearGroup V),
    tensorEvaluationOperator V σ (s * t) (g * h) =
      tensorEvaluationOperator V σ s g * tensorEvaluationOperator V σ t h

/-- An actual linear equivalence, with its canonical forward map and the full
product equivariance. No bijectivity or decomposition hypothesis is supplied. -/
def tensorEvaluation_isomorphismType : Prop :=
  ∀ (V : Type u) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ),
    ∃ e : TensorEvaluationSum V n ≃ₗ[ℂ] TensorPower V n,
      e.toLinearMap = tensorEvaluationMap V n ∧
      ∀ (σ : ∀ p : Partition n, Representation ℂ (SymmetricGroup n) (SpechtModule p)),
        (∀ p, InheritedSpechtAction p (σ p)) →
        ∀ (s : SymmetricGroup n) (g : LinearGroup V) (x : TensorEvaluationSum V n),
          e (tensorEvaluationOperator V σ s g x) =
            slotOperator V n s (diagonalOperator V n g (e x))

end Specs.AdvancedFiniteGroupRepresentations
