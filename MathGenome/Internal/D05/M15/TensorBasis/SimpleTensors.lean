import MathGenome.Internal.Specs.D05.M15.TensorBasis.SimpleTensors
import MathGenome.Internal.D05.M15.TensorBasis
import MathGenome.Internal.D05.M02.BasisExtension.Choice
import MathGenome.Internal.D05.M03.BasisExtension
import Mathlib.LinearAlgebra.PiTensorProduct.Generators

/-! Equality of nonzero elementary tensors, with no dimension restriction. -/
namespace D05.M15.TensorBasis.SimpleTensors

open scoped TensorProduct BigOperators

/-- Extend the singleton independent set by the declared classical
basis-extension principle, then prescribe value one on the resulting basis.
This is the only unrestricted basis choice needed in the argument. -/
theorem exists_normalized_functional {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {v : V} (hv : v ≠ 0) :
    ∃ φ : V →ₗ[K] K, φ v = 1 := by
  have hi : LinearIndependent K (fun x : ({v} : Set V) => (x : V)) :=
    (linearIndepOn_singleton_iff (R := K) (v := id)).mpr hv
  obtain ⟨T, hT, b, hb⟩ := D05.M02.BasisExtension.Choice.basis_extension {v} hi
  let j : T := ⟨v, hT (by simp)⟩
  obtain ⟨φ, hφ, _⟩ := D05.M03.BasisExtension.exists_unique_linear_map b (fun _ => (1 : K))
  refine ⟨φ, ?_⟩
  have hj : b j = v := hb j
  simpa only [hj] using hφ j

theorem binary_criterion : Specs.D05.M15.TensorBasis.SimpleTensors.binary_criterion := by
  intro K V W _ _ _ _ _ v v' w w' hn
  have hv : v ≠ 0 := by intro h; simp [h] at hn
  have hw : w ≠ 0 := by intro h; simp [h] at hn
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ := exists_normalized_functional (K := K) hv
    obtain ⟨ψ, hψ⟩ := exists_normalized_functional (K := K) hw
    let L : (V ⊗[K] W) →ₗ[K] W :=
      TensorProduct.lift ((LinearMap.lsmul K W).comp φ)
    have he : w = φ v' • w' := by
      have := congrArg L h
      simpa [L, hφ] using this
    have ha : φ v' ≠ 0 := by
      intro ha
      exact hw (by simpa [ha] using he)
    have hw' : w' = (φ v')⁻¹ • w := by
      rw [he, inv_smul_smul₀ ha]
    let R : (V ⊗[K] W) →ₗ[K] V :=
      TensorProduct.lift (((LinearMap.lsmul K V).comp ψ).flip)
    have he' : v = (φ v')⁻¹ • v' := by
      have := congrArg R h
      simpa [R, hw', hψ] using this
    refine ⟨φ v', ha, ?_, hw'⟩
    rw [he', smul_inv_smul₀ ha]
  · rintro ⟨a, ha, rfl, rfl⟩
    rw [TensorProduct.smul_tmul_smul, mul_inv_cancel₀ ha, one_smul]

theorem finite_criterion : Specs.D05.M15.TensorBasis.SimpleTensors.finite_criterion := by
  intro K I V _ _ _ _ _ v v' hn
  classical
  constructor
  · intro h
    have hi (i : I) : ∃ a : K, a ≠ 0 ∧ v' i = a • v i := by
      let E := PiTensorProduct.equivPiTensorComplSingletonTensor K V i
      have he := congrArg E h
      have hne : E (PiTensorProduct.tprod K v) ≠ 0 :=
        fun hz => hn (E.injective (hz.trans E.map_zero.symm))
      simp only [E, PiTensorProduct.equivPiTensorComplSingletonTensor_tprod] at he hne
      obtain ⟨a, ha, _, hai⟩ := (binary_criterion _ _ _ _ hne).mp he
      exact ⟨a⁻¹, inv_ne_zero ha, hai⟩
    choose a ha hva using hi
    refine ⟨a, ha, ?_, hva⟩
    have hscale : PiTensorProduct.tprod K v' =
        (∏ i, a i) • PiTensorProduct.tprod K v := by
      rw [show v' = fun i => a i • v i from funext hva]
      exact (PiTensorProduct.tprod K).map_smul_univ a v
    exact (smul_left_injective K hn) (hscale.symm.trans (h.symm.trans (one_smul K _).symm))
  · rintro ⟨a, _, hprod, hva⟩
    rw [show v' = fun i => a i • v i from funext hva,
      (PiTensorProduct.tprod K).map_smul_univ, hprod, one_smul]

theorem zero_counterexample : Specs.D05.M15.TensorBasis.SimpleTensors.zero_counterexample := by
  intro K _
  refine ⟨by simp, by simp, ?_⟩
  rintro ⟨a, _, h, _⟩
  simp at h

end D05.M15.TensorBasis.SimpleTensors
