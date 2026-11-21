import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.CentralizerDimension
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.Tensor
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.CSA.SimpleArtinianModules
import Mathlib.RingTheory.TensorProduct.Finite

/-! Simplicity and dimension of the centralizer of a simple subalgebra. -/

namespace RM03.CSA

open scoped TensorProduct
open MulOpposite
open _root_.Specs.RM03.CSA (CentralizerEndType centralizerTensorAction centralizerTensorModule
  centralizerTensorScalarTower)

universe u v

variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]

private theorem centralizer_tmul_smul (B : Subalgebra k A) (a : A) (b : Bᵐᵒᵖ) (x : A) :
    letI := centralizerTensorModule B
    (a ⊗ₜ[k] b) • x = a * x * (b.unop : A) := by
  let := centralizerTensorModule B
  change centralizerTensorAction B (a ⊗ₜ[k] b) x = _
  rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.mulLeftRight_apply]
  rfl

/-- The tensor-module endomorphisms are exactly right multiplications by centralizer elements. -/
theorem centralizerEnd : CentralizerEndType.{u, v} := by
  intro k _ A _ _ B
  let := centralizerTensorModule B
  let := centralizerTensorScalarTower B
  let C := Subalgebra.centralizer k (B : Set A)
  let f : Cᵐᵒᵖ →ₐ[k] Module.End (A ⊗[k] Bᵐᵒᵖ) A :=
    { toFun := fun c =>
        { toFun := fun x => x * (c.unop : A)
          map_add' := fun x y => add_mul x y _
          map_smul' := by
            intro z x
            change (z • x) * (c.unop : A) = z • (x * (c.unop : A))
            induction z using TensorProduct.inductionOn with
            | tmul a b =>
              have hc : (b.unop : A) * (c.unop : A) = (c.unop : A) * (b.unop : A) :=
                (Subalgebra.mem_centralizer_iff k).mp c.unop.property _ b.unop.property
              simp only [centralizer_tmul_smul, mul_assoc, hc]
            | add z w hz hw => rw [add_smul, add_smul, add_mul, hz, hw] }
      map_one' := LinearMap.ext fun x => mul_one x
      map_mul' := fun c d => LinearMap.ext fun x => (mul_assoc x (d.unop : A) (c.unop : A)).symm
      map_zero' := LinearMap.ext fun x => mul_zero x
      map_add' := fun c d => LinearMap.ext fun x => mul_add x (c.unop : A) (d.unop : A)
      commutes' := by
        intro r
        apply LinearMap.ext
        intro x
        rw [Module.algebraMap_end_apply]
        change x * algebraMap k A r = r • x
        rw [Algebra.smul_def, Algebra.commutes] }
  have hf (c : Cᵐᵒᵖ) (x : A) : f c x = x * (c.unop : A) := rfl
  have hbij : Function.Bijective f := by
    constructor
    · intro c d h
      apply unop_injective
      apply Subtype.ext
      have h₁ := congrArg (fun g : Module.End (A ⊗[k] Bᵐᵒᵖ) A => g 1) h
      simpa only [hf, one_mul] using h₁
    · intro g
      have hleft (x : A) : g x = x * g 1 := by
        simpa only [centralizer_tmul_smul, unop_op, OneMemClass.coe_one, mul_one] using
          g.map_smul (x ⊗ₜ[k] op (1 : B)) 1
      have hright (b : B) : g (b : A) = g 1 * (b : A) := by
        simpa only [centralizer_tmul_smul, unop_op, one_mul] using
          g.map_smul ((1 : A) ⊗ₜ[k] op b) 1
      have hc : g 1 ∈ C :=
        (Subalgebra.mem_centralizer_iff k).mpr fun b hb => (hleft b).symm.trans (hright ⟨b, hb⟩)
      exact ⟨op ⟨g 1, hc⟩, LinearMap.ext fun x => (hleft x).symm⟩
  exact ⟨AlgEquiv.ofBijective f hbij, fun _ _ => rfl⟩

/-- A simple subalgebra has a simple centralizer with complementary dimension. -/
theorem centralizer_simple_and_finrank (hA : IsCentralSimple k A) (B : Subalgebra k A)
    (hB : IsSimpleRing B) :
    IsSimpleRing (Subalgebra.centralizer k (B : Set A)) ∧
      Module.finrank k B * Module.finrank k (Subalgebra.centralizer k (B : Set A)) =
        Module.finrank k A := by
  let T := A ⊗[k] Bᵐᵒᵖ
  let C := Subalgebra.centralizer k (B : Set A)
  let := centralizerTensorModule B
  let := centralizerTensorScalarTower B
  let : IsSimpleRing A := hA.1
  let : FiniteDimensional k A := hA.2.2
  let : IsSimpleRing B := hB
  let : IsSimpleRing T := isSimpleRing_tensor hA (inferInstance : IsSimpleRing Bᵐᵒᵖ)
  obtain ⟨_, hend, hdim⟩ := SimpleArtinianModules.endSimpleAndDimension k T A
  obtain ⟨e, _⟩ := centralizerEnd B
  have hC_op : IsSimpleRing Cᵐᵒᵖ := IsSimpleRing.of_ringEquiv e.symm.toRingEquiv hend
  refine ⟨IsSimpleRing.of_ringEquiv (RingEquiv.opOp C).symm inferInstance, ?_⟩
  change Module.finrank k (A ⊗[k] Bᵐᵒᵖ) * Module.finrank k (Module.End T A) =
    (Module.finrank k A) ^ 2 at hdim
  rw [Module.finrank_tensorProduct, ← e.toLinearEquiv.finrank_eq,
    ← (opLinearEquiv k : B ≃ₗ[k] Bᵐᵒᵖ).finrank_eq,
    ← (opLinearEquiv k : C ≃ₗ[k] Cᵐᵒᵖ).finrank_eq, mul_assoc, pow_two] at hdim
  exact Nat.mul_left_cancel (Module.finrank_pos (R := k) (M := A)) hdim

end RM03.CSA
