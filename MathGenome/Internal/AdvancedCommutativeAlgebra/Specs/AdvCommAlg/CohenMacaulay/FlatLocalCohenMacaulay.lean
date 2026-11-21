import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FlatLocalDepth
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.CohenMacaulay.FlatLocalDimension
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import MathGenome.Internal.AlgebraCore.P103.Ch07.CompletedNoetherian

/-! Independent CM-10 specifications, paper.tex:3504–3521, 3594–3598.
The module N alone is assumed flat over R. Completion means the actual
inverse limit `AdicCompletion`, with its canonical completed-ring action.
Zero modules retain bottom support dimension, infinite depth, and the
separate Cohen–Macaulay convention.
-/
universe u
open scoped TensorProduct
open TensorProduct
noncomputable section
namespace AdvCommAlg.CohenMacaulay.Specs

/-- Finite generation for the standard action on the right tensor factor. -/
theorem rightTensorFinite (R S M N : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Module S N]
    [IsScalarTower R S N] [Module.Finite R M] [Module.Finite S N] :
    letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
    Module.Finite S (M ⊗[R] N) := by
  letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  letI : Module.Finite S (N ⊗[R] M) :=
    Module.Finite.equiv (AlgebraTensorModule.cancelBaseChange R S S N M)
  exact Module.Finite.equiv ((TensorProduct.comm R M N).toAddEquiv.linearEquiv S).symm

noncomputable def flatLocal_tensor_cohenMacaulayType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
  letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  ∀ [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N]
    [Module.Flat R N],
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let F := N ⧸ (J • (⊤ : Submodule S N))
  letI := closedFiberLocalRing R S
  letI : Module.Finite (S ⧸ J) F := Module.Finite.of_restrictScalars_finite S (S ⧸ J) F
  letI := rightTensorFinite R S M N
  (LocalCohenMacaulayValue S (M ⊗[R] N) ↔
    LocalCohenMacaulayValue R M ∧ LocalCohenMacaulayValue (S ⧸ J) F)

noncomputable def flatLocal_tensor_formulasType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N],
  letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := R) (S := S) M N
  ∀ [Module.Finite R M] [Nontrivial M] [Module.Finite S N] [Nontrivial N]
    [Module.Flat R N],
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  let F := N ⧸ (J • (⊤ : Submodule S N))
  letI := closedFiberLocalRing R S
  letI : Module.Finite (S ⧸ J) F := Module.Finite.of_restrictScalars_finite S (S ⧸ J) F
  letI := rightTensorFinite R S M N
  Module.supportDim S (M ⊗[R] N) = Module.supportDim R M + Module.supportDim (S ⧸ J) F ∧
  AdvCommAlg.Depth.Specs.depthValue S (M ⊗[R] N) =
    AdvCommAlg.Depth.Specs.depthValue R M + AdvCommAlg.Depth.Specs.depthValue (S ⧸ J) F ∧
  (LocalCohenMacaulayValue S (M ⊗[R] N) ↔
    LocalCohenMacaulayValue R M ∧ LocalCohenMacaulayValue (S ⧸ J) F)

noncomputable def flatLocal_ring_cohenMacaulayType : Prop :=
  ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S],
  let J := (IsLocalRing.maximalIdeal R).map (algebraMap R S)
  letI := closedFiberLocalRing R S
  LocalCohenMacaulayValue S S ↔
    LocalCohenMacaulayValue R R ∧ LocalCohenMacaulayValue (S ⧸ J) (S ⧸ J)

/-- Library Noetherianness for the actual completed ring, without an extra assumption. -/
theorem completionNoetherian (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] : IsNoetherianRing (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  P103.Ch07.CompletedNoetherian.completed_noetherian R (IsLocalRing.maximalIdeal R)

/-- Finite generation follows from the canonical tensor comparison. -/
theorem completionFinite (R L : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup L] [Module R L] [Module.Finite R L] :
    Module.Finite (AdicCompletion (IsLocalRing.maximalIdeal R) R)
      (AdicCompletion (IsLocalRing.maximalIdeal R) L) :=
  Module.Finite.equiv
    (AdicCompletion.ofTensorProductEquivOfFiniteNoetherian (IsLocalRing.maximalIdeal R) L)

def completion_faithfullyFlatType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R)

def completion_tensor_comparisonType : Prop :=
  ∀ (R L : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup L] [Module R L] [Module.Finite R L],
  let A := AdicCompletion (IsLocalRing.maximalIdeal R) R
  letI := AdvCommAlg.RegularSequence.Specs.rightTensorModule (R := R) (S := A) L A
  ∃ e : (L ⊗[R] A) ≃ₗ[A] AdicCompletion (IsLocalRing.maximalIdeal R) L,
    ∀ (l : L) (a : A), e (l ⊗ₜ a) = a • AdicCompletion.of (IsLocalRing.maximalIdeal R) L l

noncomputable def completion_dimensionType : Prop :=
  ∀ (R L : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup L] [Module R L] [Module.Finite R L],
  Module.supportDim (AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (AdicCompletion (IsLocalRing.maximalIdeal R) L) = Module.supportDim R L

noncomputable def completion_depthType : Prop :=
  ∀ (R L : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup L] [Module R L] [Module.Finite R L],
  AdvCommAlg.Depth.Specs.depthValue (AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (AdicCompletion (IsLocalRing.maximalIdeal R) L) = AdvCommAlg.Depth.Specs.depthValue R L

noncomputable def completion_cohenMacaulayType : Prop :=
  ∀ (R L : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup L] [Module R L] [Module.Finite R L],
  letI := completionNoetherian R
  letI := completionFinite R L
  LocalCohenMacaulayValue (AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (AdicCompletion (IsLocalRing.maximalIdeal R) L) ↔ LocalCohenMacaulayValue R L

end AdvCommAlg.CohenMacaulay.Specs
