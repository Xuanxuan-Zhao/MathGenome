import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.RegularSequence.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.RegularSequence.BaseChange
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Localization.Finiteness

/-! RK-02: flat tensor extension, faithful reflection, and prime localization. -/

universe u v w z
open scoped TensorProduct Pointwise
open RingTheory.Sequence
namespace AdvCommAlg.RegularSequence

section Tensor
variable {R : Type u} [CommRing R]
variable (M : Type w) (N : Type z) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem weaklyRegular_rTensor [Module.Flat R N] (x : List R)
    (hx : WeaklyRegular M x) : WeaklyRegular (M ⊗[R] N) x :=
  hx.isWeaklyRegular_rTensor

theorem regular_rTensor [Module.Flat R N] (x : List R)
    (hx : WeaklyRegular M x)
    (hq : Nontrivial ((M ⊗[R] N) ⧸
      (Ideal.ofList x • ⊤ : Submodule R (M ⊗[R] N)))) : Regular (M ⊗[R] N) x :=
  ⟨weaklyRegular_rTensor M N x hx, (Submodule.Quotient.nontrivial_iff.mp hq).symm⟩

lemma isSMulRegular_lTensor_iff [Module.FaithfullyFlat R N] (r : R) :
    IsSMulRegular (N ⊗[R] M) r ↔ IsSMulRegular M r := by
  change Function.Injective (DistribSMul.toLinearMap R (N ⊗[R] M) r) ↔
    Function.Injective (DistribSMul.toLinearMap R M r)
  rw [← LinearMap.lTensor_smul_action]
  exact Module.FaithfullyFlat.lTensor_injective_iff_injective R N _

lemma weaklyRegular_lTensor_iff [Module.FaithfullyFlat R N] (x : List R) :
    WeaklyRegular (N ⊗[R] M) x ↔ WeaklyRegular M x := by
  induction x generalizing M with
  | nil => exact iff_of_true (.nil R _) (.nil R _)
  | cons r x ih =>
    simp only [WeaklyRegular, isWeaklyRegular_cons_iff]
    exact and_congr (isSMulRegular_lTensor_iff M N r)
      (((QuotSMulTop.tensorQuotSMulTopEquivQuotSMulTop r N M).isWeaklyRegular_congr x).symm.trans
        (ih (QuotSMulTop r M)))

lemma regular_lTensor_iff [Module.FaithfullyFlat R N] (x : List R) :
    Regular (N ⊗[R] M) x ↔ Regular M x := by
  induction x generalizing M with
  | nil =>
    rw [regular_nil_iff, regular_nil_iff]
    exact Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right R N
  | cons r x ih =>
    simp only [Regular, isRegular_cons_iff]
    exact and_congr (isSMulRegular_lTensor_iff M N r)
      (((QuotSMulTop.tensorQuotSMulTopEquivQuotSMulTop r N M).isRegular_congr x).symm.trans
        (ih (QuotSMulTop r M)))

theorem weaklyRegular_rTensor_iff [Module.FaithfullyFlat R N] (x : List R) :
    WeaklyRegular (M ⊗[R] N) x ↔ WeaklyRegular M x :=
  ((TensorProduct.comm R M N).isWeaklyRegular_congr x).trans
    (weaklyRegular_lTensor_iff M N x)

theorem regular_rTensor_iff [Module.FaithfullyFlat R N] (x : List R) :
    Regular (M ⊗[R] N) x ↔ Regular M x :=
  ((TensorProduct.comm R M N).isRegular_congr x).trans (regular_lTensor_iff M N x)
end Tensor

section Scalar
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable (M : Type w) (N : Type z) [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

lemma regular_map_algebraMap_iff (x : List R) :
    Regular (N ⊗[R] M) (x.map (algebraMap R S)) ↔ Regular (N ⊗[R] M) x :=
  (AddEquiv.refl (N ⊗[R] M)).isRegular_congr <| List.forall₂_map_left_iff.mpr <|
    List.forall₂_same.mpr fun r _ => algebraMap_smul S r

/-- Tensor commutation is S-linear for the right-factor action. -/
noncomputable def rightTensorComm :
    letI := Specs.rightTensorModule (R := R) (S := S) M N
    (M ⊗[R] N) ≃ₗ[S] (N ⊗[R] M) :=
  (TensorProduct.comm R M N).toAddEquiv.linearEquiv S

theorem rightTensor_smul_tmul :
    letI := Specs.rightTensorModule (R := R) (S := S) M N
    ∀ (s : S) (m : M) (n : N), s • (m ⊗ₜ[R] n) = m ⊗ₜ[R] (s • n) := by
  letI := Specs.rightTensorModule (R := R) (S := S) M N
  intro s m n
  apply (rightTensorComm (S := S) M N).injective
  simp [rightTensorComm, TensorProduct.smul_tmul']

theorem weaklyRegular_rTensor_map :
    letI := Specs.rightTensorModule (R := R) (S := S) M N
    ∀ [Module.Flat R N] (x : List R), WeaklyRegular M x →
      WeaklyRegular (M ⊗[R] N) (x.map (algebraMap R S)) := by
  letI := Specs.rightTensorModule (R := R) (S := S) M N
  intro _ x hx
  apply ((rightTensorComm (S := S) M N).isWeaklyRegular_congr _).mpr
  exact (isWeaklyRegular_map_algebraMap_iff S _ x).mpr hx.isWeaklyRegular_lTensor

theorem regular_rTensor_map :
    letI := Specs.rightTensorModule (R := R) (S := S) M N
    ∀ [Module.Flat R N] (x : List R), WeaklyRegular M x →
      Nontrivial ((M ⊗[R] N) ⧸ (Ideal.ofList (x.map (algebraMap R S)) • ⊤ :
        Submodule S (M ⊗[R] N))) →
      Regular (M ⊗[R] N) (x.map (algebraMap R S)) := by
  letI := Specs.rightTensorModule (R := R) (S := S) M N
  intro _ x hx hq
  exact ⟨weaklyRegular_rTensor_map M N x hx,
    (Submodule.Quotient.nontrivial_iff.mp hq).symm⟩

theorem weaklyRegular_rTensor_map_iff :
    letI := Specs.rightTensorModule (R := R) (S := S) M N
    ∀ [Module.FaithfullyFlat R N] (x : List R),
      WeaklyRegular (M ⊗[R] N) (x.map (algebraMap R S)) ↔ WeaklyRegular M x := by
  letI := Specs.rightTensorModule (R := R) (S := S) M N
  intro _ x
  exact ((rightTensorComm (S := S) M N).isWeaklyRegular_congr _).trans <|
    (isWeaklyRegular_map_algebraMap_iff S _ x).trans (weaklyRegular_lTensor_iff M N x)

theorem regular_rTensor_map_iff :
    letI := Specs.rightTensorModule (R := R) (S := S) M N
    ∀ [Module.FaithfullyFlat R N] (x : List R),
      Regular (M ⊗[R] N) (x.map (algebraMap R S)) ↔ Regular M x := by
  letI := Specs.rightTensorModule (R := R) (S := S) M N
  intro _ x
  exact ((rightTensorComm (S := S) M N).isRegular_congr _).trans <|
    (regular_map_algebraMap_iff M N x).trans (regular_lTensor_iff M N x)
end Scalar

theorem regular_localizedModule {R : Type u} [CommRing R] (M : Type w)
    [AddCommGroup M] [Module R M] [Module.Finite R M] (p : Ideal R) [p.IsPrime]
    [Nontrivial (LocalizedModule.AtPrime p M)] (x : List R)
    (hp : Ideal.ofList x ≤ p) (hx : Regular M x) :
    Regular (LocalizedModule.AtPrime p M)
      (x.map (algebraMap R (Localization.AtPrime p))) := by
  exact hx.toIsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem
    (Localization.AtPrime p) p (LocalizedModule.mkLinearMap p.primeCompl M)
    (fun r hr => hp (Ideal.subset_span hr))

end AdvCommAlg.RegularSequence
