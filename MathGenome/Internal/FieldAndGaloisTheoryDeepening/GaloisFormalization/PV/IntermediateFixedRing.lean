import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.FiniteTypeResiduesAndPoints
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.IntermediateTotalRing
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.PV.RelativePicardVessiotTensor
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.IntermediateFixedRing
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.SimpleModule.Basic

namespace GaloisFormalization.PV

open scoped Matrix TensorProduct nonZeroDivisors
open _root_.GaloisFormalization.PV.Specs
open Algebra.TensorProduct (includeRight lift_tmul map_tmul tmul_mul_tmul)

private theorem constantTensor_eq_zero {C Q D : Type*} [Field C] [IsAlgClosed C]
    [CommRing Q] [CommRing D] [Algebra C Q] [Algebra C D]
    [IsReduced D] [Algebra.FiniteType C D] (z : Q ⊗[C] D)
    (hz : ∀ f : D →ₐ[C] C, evaluateConstantTensor f z = 0) : z = 0 := by
  let basis := Module.Free.chooseBasis C Q
  let coeff := TensorProduct.equivFinsuppOfBasisLeft (N := D) basis
  have hcoord (i : Module.Free.ChooseBasisIndex C Q) (f : D →ₐ[C] C)
      (x : Q ⊗[C] D) :
      f (coeff x i) = basis.coord i (evaluateConstantTensor f x) := by
    induction x using TensorProduct.inductionOn with
    | tmul q d =>
      rw [show coeff (q ⊗ₜ[C] d) i = basis.repr q i • d from
        TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply basis q d i]
      rw [map_smul, evaluateConstantTensor, lift_tmul]
      change basis.repr q i * f d = basis.coord i (q * algebraMap C Q (f d))
      rw [mul_comm q, ← Algebra.smul_def, map_smul, mul_comm]
      rfl
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  apply coeff.injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  by_contra hne
  let : Nontrivial D := nontrivial_of_ne _ _ hne
  obtain ⟨f, hf⟩ := existsAlgHomOfNeZero C D (coeff z i) hne
  exact hf (by rw [hcoord, hz, map_zero])

private theorem intermediateFieldStructure_isSemisimpleRing {kind : OperatorKind}
    {F : Type*} [CommRing F] {op : operator kind F} (h : intermediateFieldStructure op) :
    IsSemisimpleRing F := by
  cases kind with
  | differential =>
    change IsField F at h
    let := h.toField
    infer_instance
  | difference =>
    obtain ⟨ι, L, hL, hfinite, _, e, _⟩ := h
    let := hL
    let := hfinite
    exact e.symm.isSemisimpleRing

private theorem intermediateTotalRing_isSemisimpleRing {kind : OperatorKind} {K R : Type*}
    [Field K] [CommRing R] [Algebra K R] {n : ℕ}
    {δ : operatorField kind K} {A : linearSystem kind K n} {E : operator kind R}
    {T : operator kind (totalQuotientRing R)} {Y : GL (Fin n) R}
    (hbase : isBaseField δ) (hPV : isPicardVessiotTotalExtension δ A E T)
    (hY : isFundamental A E Y) :
    let Q := totalQuotientRing R
    ∀ (F : Subalgebra K Q), isIntermediateTotalRing T F → IsSemisimpleRing F := by
  intro Q F hF
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hstructure, _⟩ :=
    intermediateTotalRing_structure δ A E T Y hbase hPV hY F hF
  exact intermediateFieldStructure_isSemisimpleRing hstructure

/-- A tensor equalizer over a semisimple base can be tested using a linear
retraction of the algebra map. -/
private theorem mem_range_of_tensor_eq {F Q : Type*} [CommRing F] [IsSemisimpleRing F]
    [CommRing Q] [Algebra F Q] (hinj : Function.Injective (algebraMap F Q)) (x : Q)
    (hx : (1 : Q) ⊗ₜ[F] x = x ⊗ₜ[F] (1 : Q)) : x ∈ Set.range (algebraMap F Q) := by
  let i := (Algebra.ofId F Q).toLinearMap
  obtain ⟨l, hl⟩ := IsSemisimpleModule.extension_property i hinj (LinearMap.id : F →ₗ[F] F)
  have h1 : l 1 = 1 := by
    have h : l (algebraMap F Q 1) = 1 := DFunLike.congr_fun hl 1
    simpa only [map_one] using h
  refine ⟨l x, ?_⟩
  have h := congrArg (fun t => TensorProduct.lid F Q (l.rTensor Q t)) hx
  simpa only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, h1, Algebra.smul_def,
    map_one, one_mul, mul_one] using h.symm

private theorem tensor_eq_of_fraction {F B Q : Type*} [CommRing F] [CommRing B]
    [CommRing Q] [Algebra F B] [Algebra F Q] [Algebra B Q] [IsScalarTower F B Q]
    [IsFractionRing B Q] (r : B) (s : B⁰) (x : Q)
    (hfrac : x * algebraMap B Q s = algebraMap B Q r)
    (h : (1 : Q) ⊗ₜ[F] r = x ⊗ₜ[F] (s : B)) :
    (1 : Q) ⊗ₜ[F] x = x ⊗ₜ[F] (1 : Q) := by
  have hunit := (IsLocalization.map_units Q s).map (includeRight : Q →ₐ[F] Q ⊗[F] Q)
  apply hunit.mul_left_inj.mp
  change ((1 : Q) ⊗ₜ[F] x) * ((1 : Q) ⊗ₜ[F] algebraMap B Q s) =
    (x ⊗ₜ[F] (1 : Q)) * ((1 : Q) ⊗ₜ[F] algebraMap B Q s)
  simp only [tmul_mul_tmul, one_mul, mul_one, hfrac]
  have hmap := congrArg (Algebra.TensorProduct.map (AlgHom.id F Q)
    (IsScalarTower.toAlgHom F B Q)) h
  simpa only [map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom'] using hmap

private theorem tensor_eq_of_fixed {kind : OperatorKind} {C F Q B D : Type*} {n : ℕ}
    [Field C] [IsAlgClosed C] [CommRing F] [CommRing Q] [CommRing B] [CommRing D]
    [Algebra F Q] [Algebra F B] [Algebra B Q] [IsScalarTower F B Q] [Algebra C Q] [Algebra C D]
    [IsFractionRing B Q] [IsReduced D] [Algebra.FiniteType C D]
    {T : operator kind Q} {EB : operator kind B} {YQ : GL (Fin n) Q} {YB : GL (Fin n) B}
    {G : Subgroup (GL (Fin n) C)} {S : Set G} {act : G → Q ≃+* Q}
    {e : Q ⊗[C] D ≃ₐ[Q] Q ⊗[F] B} {ZD : GL (Fin n) D}
    (hEval : relativeTensorEvaluations T EB YQ YB G S act e ZD)
    (x : Q) (hfixed : ∀ g ∈ S, act g x = x) :
    (1 : Q) ⊗ₜ[F] x = x ⊗ₜ[F] (1 : Q) := by
  obtain ⟨points, _, hpoints⟩ := hEval
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj B⁰ x
  apply tensor_eq_of_fraction r s x hrs
  apply sub_eq_zero.mp
  apply e.symm.injective
  rw [map_zero]
  apply constantTensor_eq_zero
  intro f
  let g : G := points f
  have hg : g ∈ S := (points f).property
  obtain ⟨σ, _, _, heval, hact, _⟩ := hpoints f
  change ((evaluateConstantTensor f).comp e.symm.toAlgHom)
    ((1 : Q) ⊗ₜ[F] r - x ⊗ₜ[F] (s : B)) = 0
  rw [map_sub, heval, heval, ← hact, ← hact, one_mul, sub_eq_zero]
  have h := congrArg (act g) hrs
  rw [map_mul, hfixed g hg] at h
  exact h.symm

/-- The pointwise stabilizer of an intermediate total ring is algebraic,
and its fixed subalgebra is that intermediate ring. -/
theorem intermediateFixedRing.{u, v} : Specs.intermediateFixedRing.{u, v} := by
  intro kind K R _ _ _ n δ A E T Y hbase hPV hY Q F hF S
  let C := constantSubfield δ
  let : Algebra C Q := Algebra.compHom Q (constantSubfield δ).subtype
  let : IsAlgClosed C := hbase.2
  let YQ := Matrix.GeneralLinearGroup.map (algebraMap R Q) Y
  let B := Specs.relativePicardVessiotSubalgebra F YQ
  obtain ⟨_, _, _, _, _, _, _, _, _, hfrac, _, _, _, hPresentation⟩ :=
    GaloisFormalization.PV.relativePicardVessiotTensor.{u, v} δ A E T Y hbase hPV hY F hF
  obtain ⟨_, _, _, _, hReduced, hFiniteType, _, _, _, _, _, _, hEval, H, hH, _, hClosed⟩ :=
    hPresentation
  refine ⟨⟨H, hH, hClosed⟩, le_antisymm ?_ ?_⟩
  · intro x hx
    have hfixed : ∀ g ∈ S, matrixFractionAutomorphism δ E Y g x = x := hx
    let : IsFractionRing B Q := hfrac
    let := hReduced
    let := hFiniteType
    have ht := tensor_eq_of_fixed hEval x hfixed
    let := intermediateTotalRing_isSemisimpleRing hbase hPV hY F hF
    obtain ⟨a, ha⟩ := mem_range_of_tensor_eq (F := F) Subtype.val_injective x ht
    exact ha ▸ a.property
  · intro x hx g hg
    exact hg ⟨x, hx⟩

end GaloisFormalization.PV
