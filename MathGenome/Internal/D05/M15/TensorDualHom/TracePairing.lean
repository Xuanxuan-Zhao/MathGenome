import MathGenome.Internal.Specs.D05.M15.TensorDualHom.TracePairing
import MathGenome.Internal.D05.M03.HomDimension
import MathGenome.Internal.D05.M04.Trace
import MathGenome.Internal.D05.M15.TensorDualHom

/-! The perfect algebraic trace pairing, paper.tex:2816–2823. -/
namespace D05.M15.TensorDualHom.TracePairing

open scoped TensorProduct
open Specs.D05.M03.HomDimension (elementaryMap)

noncomputable abbrev pairing (K V W : Type*) [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] :=
  Specs.D05.M15.TensorDualHom.TracePairing.pairing K V W

theorem pairing_apply : Specs.D05.M15.TensorDualHom.TracePairing.pairing_apply := by
  intro K V W _ _ _ _ _ S T
  rfl

/-- A rank-one test map extracts evaluation of S(v) by a functional. -/
theorem trace_rank_one_comp {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] (S : V →ₗ[K] W) (ψ : Module.Dual K W) (v : V) :
    LinearMap.trace K V ((ψ.smulRight v).comp S) = ψ (S v) := by
  have h : (ψ.smulRight v).comp S = (ψ.comp S).smulRight v := by
    ext x
    rfl
  rw [h, LinearMap.trace_smulRight]
  rfl

theorem matrix_unit_pairing :
    Specs.D05.M15.TensorDualHom.TracePairing.matrix_unit_pairing := by
  intro K V W _ _ _ _ _ n m e f a b i j
  let := e.finiteDimensional_of_finite
  rw [pairing_apply, elementaryMap, trace_rank_one_comp]
  by_cases hij : i = j <;> by_cases hab : a = b <;>
    simp [elementaryMap, Module.Basis.coord_apply,
      hij, hab, eq_comm]

theorem dual_bases : Specs.D05.M15.TensorDualHom.TracePairing.dual_bases := by
  intro K V W _ _ _ _ _ n m e f
  obtain ⟨E, hE⟩ := D05.M03.HomDimension.elementary_maps_basis e f
  obtain ⟨F, hF⟩ := D05.M03.HomDimension.elementary_maps_basis f e
  refine ⟨E, F.reindex (Equiv.prodComm _ _), hE, ?_, ?_⟩
  · intro p
    simpa only [Module.Basis.reindex_apply, Equiv.prodComm_symm,
      Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] using hF p.swap
  · intro p q
    rw [hE, Module.Basis.reindex_apply]
    simp only [Equiv.prodComm_symm, Equiv.prodComm_apply, hF]
    rw [matrix_unit_pairing]
    by_cases h₁ : p.1 = q.1 <;> by_cases h₂ : p.2 = q.2 <;>
      simp [h₁, h₂, Prod.ext_iff]

/-- All rank-one tests vanishing forces each coordinate of every S(v) to vanish.
The argument works without a nonempty-basis assumption. -/
theorem left_separating {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] [FiniteDimensional K W]
    (S : V →ₗ[K] W) (h : ∀ T : W →ₗ[K] V, pairing K V W S T = 0) : S = 0 := by
  let f := Module.finBasis K W
  ext v
  apply f.repr.injective
  ext a
  have ha := h ((f.coord a).smulRight v)
  rw [pairing_apply, trace_rank_one_comp] at ha
  simpa only [Module.Basis.coord_apply, LinearMap.zero_apply, map_zero, Finsupp.zero_apply] using ha

theorem nondegenerate : Specs.D05.M15.TensorDualHom.TracePairing.nondegenerate := by
  intro K V W _ _ _ _ _ _ _
  refine ⟨left_separating, ?_⟩
  intro T h
  apply left_separating T
  intro S
  rw [pairing_apply, LinearMap.trace_comp_comm']
  exact h S

theorem perfect : Specs.D05.M15.TensorDualHom.TracePairing.perfect := by
  intro K V W _ _ _ _ _ _ _
  apply LinearMap.IsPerfPair.of_injective
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro S hS
    apply left_separating S
    intro T
    exact LinearMap.congr_fun hS T
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro T hT
    apply (nondegenerate (K := K) (V := V) (W := W)).2 T
    intro S
    exact LinearMap.congr_fun hT S

theorem rank_one_pairing : Specs.D05.M15.TensorDualHom.TracePairing.rank_one_pairing := by
  intro K V W _ _ _ _ _ _ _ φ ψ v w
  change LinearMap.trace K V ((ψ.smulRight v).comp (φ.smulRight w)) = _
  rw [trace_rank_one_comp]
  simp only [LinearMap.smulRight_apply, map_smul, smul_eq_mul]
  exact mul_comm _ _

end D05.M15.TensorDualHom.TracePairing
