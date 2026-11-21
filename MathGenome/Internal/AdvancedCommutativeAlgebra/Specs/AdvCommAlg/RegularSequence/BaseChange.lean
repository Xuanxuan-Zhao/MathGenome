import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.Definitions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.TransferInstance

/-! Independent statements for the scalar extension and localization clauses of RK-02.
The right-factor S-action on M ⊗[R] N is transported through tensor commutation;
its formula on pure tensors is separately verified by the implementation. -/

universe u v w z
open scoped TensorProduct Pointwise
namespace AdvCommAlg.RegularSequence.Specs

/-- The usual S-action on the right tensor factor, on the original tensor product type. -/
@[instance_reducible] noncomputable def rightTensorModule {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] (M : Type w) (N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] :
    Module S (M ⊗[R] N) :=
  (TensorProduct.comm R M N).toAddEquiv.module S

def weaklyRegular_rTensorType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type w) (N : Type z)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
  ∀ [Module.Flat R N] (x : List R), RingTheory.Sequence.IsWeaklyRegular M x →
    RingTheory.Sequence.IsWeaklyRegular (M ⊗[R] N) x

def regular_rTensorType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type w) (N : Type z)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
  ∀ [Module.Flat R N] (x : List R), RingTheory.Sequence.IsWeaklyRegular M x →
    Nontrivial ((M ⊗[R] N) ⧸
      (Ideal.ofList x • ⊤ : Submodule R (M ⊗[R] N))) →
    RingTheory.Sequence.IsRegular (M ⊗[R] N) x

def weaklyRegular_rTensor_iffType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type w) (N : Type z)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
  ∀ [Module.FaithfullyFlat R N] (x : List R),
    RingTheory.Sequence.IsWeaklyRegular (M ⊗[R] N) x ↔
      RingTheory.Sequence.IsWeaklyRegular M x

def regular_rTensor_iffType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type w) (N : Type z)
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N],
  ∀ [Module.FaithfullyFlat R N] (x : List R),
    RingTheory.Sequence.IsRegular (M ⊗[R] N) x ↔ RingTheory.Sequence.IsRegular M x

def rightTensor_smul_tmulType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) (N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
  letI := rightTensorModule (R := R) (S := S) M N
  ∀ (s : S) (m : M) (n : N), s • (m ⊗ₜ[R] n) = m ⊗ₜ[R] (s • n)

def weaklyRegular_rTensor_mapType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) (N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
  letI := rightTensorModule (R := R) (S := S) M N
  ∀ [Module.Flat R N] (x : List R), RingTheory.Sequence.IsWeaklyRegular M x →
    RingTheory.Sequence.IsWeaklyRegular (M ⊗[R] N) (x.map (algebraMap R S))

def regular_rTensor_mapType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) (N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
  letI := rightTensorModule (R := R) (S := S) M N
  ∀ [Module.Flat R N] (x : List R), RingTheory.Sequence.IsWeaklyRegular M x →
    Nontrivial ((M ⊗[R] N) ⧸ (Ideal.ofList (x.map (algebraMap R S)) • ⊤ :
      Submodule S (M ⊗[R] N))) →
    RingTheory.Sequence.IsRegular (M ⊗[R] N) (x.map (algebraMap R S))

def weaklyRegular_rTensor_map_iffType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) (N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
  letI := rightTensorModule (R := R) (S := S) M N
  ∀ [Module.FaithfullyFlat R N] (x : List R),
    RingTheory.Sequence.IsWeaklyRegular (M ⊗[R] N) (x.map (algebraMap R S)) ↔
      RingTheory.Sequence.IsWeaklyRegular M x

def regular_rTensor_map_iffType : Prop :=
  ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type w) (N : Type z) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
  letI := rightTensorModule (R := R) (S := S) M N
  ∀ [Module.FaithfullyFlat R N] (x : List R),
    RingTheory.Sequence.IsRegular (M ⊗[R] N) (x.map (algebraMap R S)) ↔
      RingTheory.Sequence.IsRegular M x

/-- No Noetherian hypothesis; finite means finitely generated as a module. -/
def regular_localizedModuleType : Prop :=
  ∀ {R : Type u} [CommRing R] (M : Type w) [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : Ideal R) [p.IsPrime]
    [Nontrivial (LocalizedModule.AtPrime p M)] (x : List R),
    Ideal.ofList x ≤ p → RingTheory.Sequence.IsRegular M x →
    RingTheory.Sequence.IsRegular (LocalizedModule.AtPrime p M)
      (x.map (algebraMap R (Localization.AtPrime p)))

end AdvCommAlg.RegularSequence.Specs
