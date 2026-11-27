import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.ArtinSchreierTensor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.ArtinSchreierCoefficients
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! The diagonal tensor module for the Artin–Schreier sequence. -/

namespace GaloisFormalization.GH.ArtinSchreierTensor

noncomputable section

open scoped TensorProduct
open KrullLayers (AbsoluteGaloisGroup)
open Specs.GaloisFormalization.GH.ArtinSchreierTensor
  (diagonalAction_tmul_type tensor_smul_tmul_type tensorInclusion_apply_type tensorWp_tmul_type
    semilinear_type continuous_diagonalAction_type shortExact_type equivariant_type
    continuous_maps_type)

attribute [local instance] ZMod.algebra

abbrev primeFieldModule := @Specs.GaloisFormalization.GH.ArtinSchreierTensor.primeFieldModule
abbrev Tensor := @Specs.GaloisFormalization.GH.ArtinSchreierTensor.Tensor
abbrev tensorInclusion := @Specs.GaloisFormalization.GH.ArtinSchreierTensor.tensorInclusion
abbrev tensorWp := @Specs.GaloisFormalization.GH.ArtinSchreierTensor.tensorWp
abbrev diagonalAction := @Specs.GaloisFormalization.GH.ArtinSchreierTensor.diagonalAction

theorem diagonalAction_tmul : diagonalAction_tmul_type := by
  intro p S _ _ _ M _ _ G _ _ _ g s m
  rfl

theorem tensor_smul_tmul : tensor_smul_tmul_type := by
  intro p S _ _ _ M _ _ a s m
  rfl

theorem tensorInclusion_apply : tensorInclusion_apply_type := by
  intro p S _ _ _ M _ _ m
  rfl

theorem tensorWp_tmul : tensorWp_tmul_type := by
  intro p S _ _ _ M _ _ s m
  rfl

/-- The diagonal Galois action is semilinear over the separable closure. -/
theorem semilinear : semilinear_type := by
  intro p k S _ _ _ _ _ _ M _ _ h
  let _ : CharP S p := charP_of_injective_algebraMap' k p
  let _ : Module (ZMod p) M := primeFieldModule p M h
  let G := AbsoluteGaloisGroup k S
  let action : DistribMulAction G (Tensor p S M) := diagonalAction p S M
  let _ : SMul G (Tensor p S M) := action.toSMul
  change ∀ (g : AbsoluteGaloisGroup k S) (a : S) (z : Tensor p S M),
    g • (a • z) = (g • a) • (g • z)
  intro g a z
  induction z using TensorProduct.inductionOn with
  | tmul s m =>
      rw [tensor_smul_tmul p S M, diagonalAction_tmul p S M,
        diagonalAction_tmul p S M, tensor_smul_tmul p S M]
      exact congrArg (fun x : S => x ⊗ₜ[ZMod p] (g • m)) (map_mul g a s)
  | add z₁ z₂ ih₁ ih₂ => simp only [smul_add, ih₁, ih₂]

/-- Stabilizers of tensors are open for the Krull topology. -/
theorem continuous_diagonalAction : continuous_diagonalAction_type := by
  intro p k S _ _ _ _ _ _ M _ _ _ _ _ h
  let _ : CharP S p := charP_of_injective_algebraMap' k p
  let _ : Module (ZMod p) M := primeFieldModule p M h
  let G := AbsoluteGaloisGroup k S
  let action : DistribMulAction G (Tensor p S M) := diagonalAction p S M
  let _ : SMul G (Tensor p S M) := action.toSMul
  change ∀ [TopologicalSpace (Tensor p S M)] [DiscreteTopology (Tensor p S M)],
    ContinuousSMul G (Tensor p S M)
  intro _ _
  apply continuousSMul_iff_stabilizer_isOpen.mpr
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s m =>
      have hs : IsOpen (MulAction.stabilizer G s : Set G) :=
        stabilizer_isOpen_of_isIntegral (K := k) s
      have hm : IsOpen (MulAction.stabilizer G m : Set G) := stabilizer_isOpen G m
      refine Subgroup.isOpen_mono
        (H₁ := MulAction.stabilizer G s ⊓ MulAction.stabilizer G m) ?_ (hs.inter hm)
      intro g hg
      obtain ⟨hs', hm'⟩ := Subgroup.mem_inf.mp hg
      rw [MulAction.mem_stabilizer_iff, diagonalAction_tmul p S M,
        MulAction.mem_stabilizer_iff.mp hs', MulAction.mem_stabilizer_iff.mp hm']
  | add z₁ z₂ ih₁ ih₂ =>
      refine Subgroup.isOpen_mono
        (H₁ := MulAction.stabilizer G z₁ ⊓ MulAction.stabilizer G z₂) ?_ (ih₁.inter ih₂)
      intro g hg
      obtain ⟨hz₁, hz₂⟩ := Subgroup.mem_inf.mp hg
      rw [MulAction.mem_stabilizer_iff, smul_add, MulAction.mem_stabilizer_iff.mp hz₁,
        MulAction.mem_stabilizer_iff.mp hz₂]

/-- Tensoring Artin–Schreier over the prime field gives the stated short exact sequence. -/
theorem shortExact : shortExact_type := by
  intro p k S _ _ _ _ _ _ M _ h
  let _ : CharP S p := charP_of_injective_algebraMap' k p
  let _ : Module (ZMod p) M := primeFieldModule p M h
  let e := (TensorProduct.lid (ZMod p) M).symm
  let f := (ArtinSchreierCoefficients.primeFieldInclusion p S).rTensor M
  have hinclusion : tensorInclusion p S M = f.comp e.toLinearMap := by
    ext m
    simp [f, e, tensorInclusion_apply p S M]
  obtain ⟨hinj, hexact, hsurj⟩ := ArtinSchreierCoefficients.shortExact_rTensor p k S M
  change Function.Injective (tensorInclusion p S M) ∧
    Function.Exact (tensorInclusion p S M) (tensorWp p S M) ∧
    Function.Surjective (tensorWp p S M)
  rw [hinclusion]
  exact ⟨hinj.comp e.injective, e.surjective.comp_exact_iff_exact.mpr hexact, hsurj⟩

/-- The two maps of the tensor sequence commute with the diagonal action. -/
theorem equivariant : equivariant_type := by
  intro p k S _ _ _ _ _ _ M _ _ h
  let _ : CharP S p := charP_of_injective_algebraMap' k p
  let _ : Module (ZMod p) M := primeFieldModule p M h
  let G := AbsoluteGaloisGroup k S
  let action : DistribMulAction G (Tensor p S M) := diagonalAction p S M
  let _ : SMul G (Tensor p S M) := action.toSMul
  change (∀ (g : G) (m : M), tensorInclusion p S M (g • m) = g • tensorInclusion p S M m) ∧
    (∀ (g : G) (z : Tensor p S M), tensorWp p S M (g • z) = g • tensorWp p S M z)
  constructor
  · intro g m
    have hone : g • (1 : S) = 1 := map_one g
    simp only [tensorInclusion_apply p S M, diagonalAction_tmul p S M, hone]
  · intro g z
    induction z using TensorProduct.inductionOn with
    | tmul s m =>
        rw [diagonalAction_tmul p S M, tensorWp_tmul p S M, tensorWp_tmul p S M,
          diagonalAction_tmul p S M]
        exact congrArg (fun x : S => x ⊗ₜ[ZMod p] (g • m))
          (ArtinSchreierCoefficients.wp_natural p g.toRingEquiv.toRingHom s).symm
    | add z₁ z₂ ih₁ ih₂ => simp only [smul_add, map_add, ih₁, ih₂]

/-- The maps of the exact sequence are continuous for the discrete topologies. -/
theorem continuous_maps : continuous_maps_type := by
  intro p k S _ _ _ _ _ M _ _ _ h
  let _ : CharP S p := charP_of_injective_algebraMap' k p
  let _ : Module (ZMod p) M := primeFieldModule p M h
  change ∀ [TopologicalSpace (Tensor p S M)] [DiscreteTopology (Tensor p S M)],
    Continuous (tensorInclusion p S M) ∧ Continuous (tensorWp p S M)
  intro _ _
  exact ⟨continuous_of_discreteTopology, continuous_of_discreteTopology⟩

end

end GaloisFormalization.GH.ArtinSchreierTensor
