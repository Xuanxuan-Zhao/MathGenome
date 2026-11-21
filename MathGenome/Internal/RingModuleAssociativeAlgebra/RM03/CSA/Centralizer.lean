import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.CentralizerDimension
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Tensor
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite

/-! The centralizer and double centralizer theorem. -/

namespace RM03.CSA

open scoped TensorProduct

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

private theorem map_center_eq_inf_centralizer (S : Subalgebra k A) :
    (Subalgebra.center k S).map S.val = S ⊓ Subalgebra.centralizer k (S : Set A) := by
  ext x
  rw [Subalgebra.mem_map, Algebra.mem_inf, Subalgebra.mem_centralizer_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.property, fun z hz => ?_⟩
    exact congrArg (fun a : S => (a : A)) (Subalgebra.mem_center_iff.mp hy ⟨z, hz⟩)
  · rintro ⟨hx, hcomm⟩
    exact ⟨⟨x, hx⟩, Subalgebra.mem_center_iff.mpr
      (fun y => Subtype.ext (hcomm y y.property)), rfl⟩

/-- A simple unital subalgebra of a central simple algebra is its own double centralizer. -/
theorem centralizer_and_double_centralizer (hA : IsCentralSimple k A) (B : Subalgebra k A)
    (hB : IsSimpleRing B) :
    let C := Subalgebra.centralizer k (B : Set A)
    IsSimpleRing C ∧
      Module.finrank k B * Module.finrank k C = Module.finrank k A ∧
      Subalgebra.centralizer k (C : Set A) = B ∧
      (Subalgebra.center k C).map C.val = (Subalgebra.center k B).map B.val := by
  let C := Subalgebra.centralizer k (B : Set A)
  let D := Subalgebra.centralizer k (C : Set A)
  let : FiniteDimensional k A := hA.2.2
  obtain ⟨hC, hBC⟩ := centralizer_simple_and_finrank hA B hB
  let : IsSimpleRing C := hC
  obtain ⟨_, hCD⟩ := centralizer_simple_and_finrank hA C hC
  have hdim : Module.finrank k B = Module.finrank k D :=
    Nat.mul_left_cancel (Module.finrank_pos (R := k) (M := C))
      ((Nat.mul_comm _ _).trans (hBC.trans hCD.symm))
  have hDouble : D = B :=
    (Subalgebra.eq_of_le_of_finrank_eq (Subalgebra.le_centralizer_centralizer k) hdim).symm
  refine ⟨hC, hBC, hDouble, ?_⟩
  change (Subalgebra.center k C).map C.val = (Subalgebra.center k B).map B.val
  rw [map_center_eq_inf_centralizer C, map_center_eq_inf_centralizer B]
  change C ⊓ D = B ⊓ C
  rw [hDouble, inf_comm]

/-- For a central simple subalgebra, multiplication gives the tensor product
of the subalgebra and its centralizer as the ambient algebra. -/
theorem centralizer_central_and_tensor_equiv (hA : IsCentralSimple k A) (B : Subalgebra k A)
    (hB : IsSimpleRing B) (hBc : Algebra.IsCentral k B) :
    let C := Subalgebra.centralizer k (B : Set A)
    Algebra.IsCentral k C ∧
      ∃ e : B ⊗[k] C ≃ₐ[k] A, ∀ (b : B) (c : C), e (b ⊗ₜ[k] c) = (b : A) * (c : A) := by
  let C := Subalgebra.centralizer k (B : Set A)
  let : IsSimpleRing A := hA.1
  let : FiniteDimensional k A := hA.2.2
  let : Algebra.IsCentral k B := hBc
  obtain ⟨hC, hdim, _, hZ⟩ := centralizer_and_double_centralizer hA B hB
  have hCenterC : Subalgebra.center k C = ⊥ := by
    apply Subalgebra.map_injective (f := C.val) Subtype.val_injective
    rw [hZ, Algebra.IsCentral.center_eq_bot k B, Algebra.map_bot, Algebra.map_bot]
  refine ⟨⟨hCenterC.le⟩, ?_⟩
  let f : B ⊗[k] C →ₐ[k] A :=
    Algebra.TensorProduct.lift B.val C.val fun b c =>
      (Subalgebra.mem_centralizer_iff k).mp c.property b b.property
  let : IsSimpleRing (B ⊗[k] C) := isSimpleRing_tensor ⟨hB, hBc, inferInstance⟩ hC
  have hf : Function.Injective f := f.toRingHom.injective
  have hTensorDim : Module.finrank k (B ⊗[k] C) = Module.finrank k A :=
    Module.finrank_tensorProduct.trans hdim
  have hSurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hTensorDim (f := f.toLinearMap)).mp hf
  exact ⟨AlgEquiv.ofBijective f ⟨hf, hSurj⟩, fun _ _ => rfl⟩

end RM03.CSA
