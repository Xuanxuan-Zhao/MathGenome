import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.HilbertSerreLength
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch06.LinearGradedNormalization
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.FieldTheory.RatFunc.Basic

namespace P103.HilbertScalarExtension
open P103.Graded
open P103.Specs.Ch06.LinearGradedNormalization
universe u v w x

variable (k : Type u) {C : Type v} {M : Type w}
  [Field k] [CommRing C] [Algebra k C]
  [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]

/-- Homogeneous pieces over the specified structural field. -/
def fieldPiece (G : NonnegativeGrading C) (U : ModuleGrading G M)
    (hzero : Connected k G) (j : ℤ) : Submodule k M where
  __ := U.piece j
  smul_mem' a m hm := by
    have ha : algebraMap k C a ∈ G.piece 0 := (hzero _).mpr ⟨a, rfl⟩
    change a • m ∈ U.piece j
    rw [← IsScalarTower.algebraMap_smul C a m]
    simpa using (SetLike.GradedSMul.smul_mem (A := G.piece) (B := U.piece) ha hm)

def algebraPiece (G : NonnegativeGrading C) (hzero : Connected k G)
    (j : ℤ) : Submodule k C where
  __ := G.piece j
  smul_mem' a c hc := by
    rw [Algebra.smul_def]
    change algebraMap k C a * c ∈ G.piece j
    simpa using SetLike.mul_mem_graded ((hzero _).mpr ⟨a, rfl⟩) hc

variable (K : Type x) [Field K] [Algebra k K]

/-- The representation induced by extension of scalars. -/
noncomputable def tensorRepresentation :
    TensorProduct k K C →ₐ[K] Module.End K (TensorProduct k K M) :=
  Algebra.TensorProduct.lift (Algebra.ofId K _)
    ((Module.End.baseChangeHom k K M).comp (Algebra.lsmul k k M))
    (fun a _c => Algebra.commutes a _)

/-- The canonical tensor action: (a ⊗ c) • (b ⊗ m) = ab ⊗ (c • m). -/
noncomputable instance tensorModule : Module (TensorProduct k K C) (TensorProduct k K M) :=
  Module.compHom _ (tensorRepresentation k K (C := C) (M := M)).toRingHom

section TensorAction
variable (k : Type u) (K : Type x) {C : Type v} {M : Type w}
  [Field k] [Field K] [Algebra k K] [CommRing C] [Algebra k C]
  [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]

@[simp] theorem tensor_smul (a b : K) (c : C) (m : M) :
    (a ⊗ₜ[k] c) • (b ⊗ₜ[k] m) = (a * b) ⊗ₜ[k] (c • m) := by
  change tensorRepresentation k K (a ⊗ₜ[k] c) (b ⊗ₜ[k] m) = _
  change a • ((Algebra.lsmul k k M c).baseChange K (b ⊗ₜ[k] m)) = _
  rw [LinearMap.baseChange_tmul]
  exact TensorProduct.smul_tmul' a b (c • m)

instance tensorScalarTower : IsScalarTower K (TensorProduct k K C) (TensorProduct k K M) :=
  IsScalarTower.of_algebraMap_smul fun a m => by
    change tensorRepresentation k K (algebraMap K (TensorProduct k K C) a) m = a • m
    rw [AlgHom.commutes]
    rfl

end TensorAction
end P103.HilbertScalarExtension

namespace Specs.P103.HilbertScalarExtension
universe u v w x
open _root_.P103.Graded _root_.P103.HilbertScalarExtension
open _root_.P103.Specs.Ch06.LinearGradedNormalization

def dimensionType : Prop :=
  ∀ (k : Type u) (K : Type v) (C : Type x)
    [Field k] [Field K] [Algebra k K] [CommRing C] [Nontrivial C]
    [Algebra k C] [Algebra.FiniteType k C],
    ringKrullDim (TensorProduct k K C) = ringKrullDim C

/-- Full field-extension conclusion, including canonical homogeneous pieces and
comparison with the accepted length-based coefficient convention. -/
def ExtensionResult (k : Type u) (K : Type x) {C : Type v} {M : Type w}
    [Field k] [Field K] [Algebra k K] [CommRing C] [Algebra k C]
    [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]
    (G : NonnegativeGrading C) (U : ModuleGrading G M) (hzero : Connected k G) : Prop :=
  Nontrivial (TensorProduct k K C) ∧ Nontrivial (TensorProduct k K M) ∧
  Module.Finite (TensorProduct k K C) (TensorProduct k K M) ∧
  FaithfulSMul (TensorProduct k K C) (TensorProduct k K M) ∧
  ringKrullDim (TensorProduct k K C) = ringKrullDim C ∧
  ∃ (GK : NonnegativeGrading (TensorProduct k K C))
    (UK : ModuleGrading GK (TensorProduct k K M)) (hK : Connected K GK),
    Specs.P103.Graded.standardValue GK ∧
    (∀ j, GK.piece j = ((algebraPiece k G hzero j).baseChange K).toAddSubgroup) ∧
    (∀ j, UK.piece j = ((fieldPiece k G U hzero j).baseChange K).toAddSubgroup) ∧
    (∀ j, Module.Finite k (fieldPiece k G U hzero j)) ∧
    (∀ j, Module.Finite K (fieldPiece K GK UK hK j)) ∧
    (∀ j, ∃ e : TensorProduct k K (fieldPiece k G U hzero j) ≃ₗ[K]
        fieldPiece K GK UK hK j,
      ∀ (a : K) (m : fieldPiece k G U hzero j),
        (e (TensorProduct.tmul k a m) : TensorProduct k K M) = TensorProduct.tmul k a (m : M)) ∧
    (∀ j, Module.finrank K (fieldPiece K GK UK hK j) =
      Module.finrank k (fieldPiece k G U hzero j)) ∧
    (∀ j, P103.HilbertSerreLength.hilbertFunction G U j =
      (Module.finrank k (fieldPiece k G U hzero j) : ℤ)) ∧
    (∀ j, P103.HilbertSerreLength.hilbertFunction GK UK j =
      (Module.finrank K (fieldPiece K GK UK hK j) : ℤ)) ∧
    P103.HilbertSerreLength.hilbertFunction GK UK = P103.HilbertSerreLength.hilbertFunction G U

def scalarExtensionType : Prop :=
  ∀ (k : Type u) (K : Type x) {C : Type v} {M : Type w}
    [Field k] [Field K] [Algebra k K] [CommRing C] [Nontrivial C] [Algebra k C]
    [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]
    [Nontrivial M] [FaithfulSMul C M] [Module.Finite C M]
    (G : NonnegativeGrading C) (U : ModuleGrading G M) (hzero : Connected k G),
    Specs.P103.Graded.standardValue G → ExtensionResult k K G U hzero

def ratFuncExtensionType : Prop :=
  ∀ (k : Type u) {C : Type v} {M : Type w}
    [Field k] [CommRing C] [Nontrivial C] [Algebra k C]
    [AddCommGroup M] [Module C M] [Module k M] [IsScalarTower k C M]
    [Nontrivial M] [FaithfulSMul C M] [Module.Finite C M]
    (G : NonnegativeGrading C) (U : ModuleGrading G M) (hzero : Connected k G),
    Specs.P103.Graded.standardValue G →
      Infinite (RatFunc k) ∧ ExtensionResult k (RatFunc k) G U hzero
end Specs.P103.HilbertScalarExtension
