import MathGenome.Internal.Specs.D05.M15.InnerTensor.BilinearMetrics
import MathGenome.Internal.D05.M11.Bilinear
import MathGenome.Internal.D05.M15.TensorUniversal
import MathGenome.Internal.D05.M15.TensorKernel
import MathGenome.Internal.D05.M15.TensorPairing
import Mathlib.RingTheory.Flat.Basic

/-! General bilinear pairings on tensor products, paper.tex:2861–2872.
The construction is algebraic over an arbitrary field. No positivity, symmetry,
or nondegeneracy is imposed until the corresponding theorem explicitly asks for it. -/
namespace D05.M15.InnerTensor.BilinearMetrics

open scoped TensorProduct

abbrev tensorPairing {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K) :
    (V ⊗[K] W) →ₗ[K] (V' ⊗[K] W') →ₗ[K] K :=
  Specs.D05.M15.InnerTensor.BilinearMetrics.tensorPairing b c

@[simp] theorem tensorPairing_apply {K V W V' W' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup V'] [Module K V'] [AddCommGroup W'] [Module K W']
    (b : V →ₗ[K] V' →ₗ[K] K) (c : W →ₗ[K] W' →ₗ[K] K)
    (v : V) (w : W) (v' : V') (w' : W') :
    tensorPairing b c (v ⊗ₜ[K] w) (v' ⊗ₜ[K] w') = b v v' * c w w' := rfl

theorem tensorPairing_unique :
    Specs.D05.M15.InnerTensor.BilinearMetrics.tensorPairing_unique := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ b c P hP
  ext v w v' w'
  exact hP v w v' w'

theorem tensorPairing_exists_unique :
    Specs.D05.M15.InnerTensor.BilinearMetrics.tensorPairing_exists_unique := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ b c
  exact ⟨tensorPairing b c, tensorPairing_apply b c, fun P hP => tensorPairing_unique b c P hP⟩

theorem tensorPairing_flip :
    Specs.D05.M15.InnerTensor.BilinearMetrics.tensorPairing_flip := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ b c
  ext v' w' v w
  rfl

theorem left_radical_membership :
    Specs.D05.M15.InnerTensor.BilinearMetrics.left_radical_membership := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ b c z
  exact LinearMap.ext_iff

theorem right_radical_membership :
    Specs.D05.M15.InnerTensor.BilinearMetrics.right_radical_membership := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ b c z
  exact LinearMap.ext_iff

/-- The canonical dual tensor evaluation is injective in the finite-dimensional
case by the previously established, map-specific equivalence. -/
theorem dualEvaluation_injective {K X Y : Type*} [Field K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    [FiniteDimensional K X] [FiniteDimensional K Y] :
    Function.Injective (TensorProduct.dualDistrib K X Y) := by
  obtain ⟨E, hE⟩ := D05.M15.TensorPairing.perfect_pairing (K := K) (V := X) (W := Y)
  rw [← hE]
  exact E.injective

/-- Factoring through the injective dual tensor map leaves the kernel unchanged;
the upstream tensor-kernel formula then gives precisely the two radical summands. -/
theorem left_radical : Specs.D05.M15.InnerTensor.BilinearMetrics.left_radical := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ b c
  change LinearMap.ker ((TensorProduct.dualDistrib K V' W').comp (TensorProduct.map b c)) = _
  have hD : LinearMap.ker (TensorProduct.dualDistrib K V' W') = ⊥ :=
    LinearMap.ker_eq_bot_of_injective (dualEvaluation_injective (K := K) (X := V') (Y := W'))
  rw [LinearMap.ker_comp_of_ker_eq_bot (TensorProduct.map b c) hD]
  exact D05.M15.TensorKernel.ker_tensorMap b c

theorem right_radical : Specs.D05.M15.InnerTensor.BilinearMetrics.right_radical := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ b c
  rw [tensorPairing_flip]
  exact left_radical b.flip c.flip

theorem left_nondegenerate :
    Specs.D05.M15.InnerTensor.BilinearMetrics.left_nondegenerate := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ b c hb hc
  apply LinearMap.separatingLeft_iff_ker_eq_bot.mpr
  apply LinearMap.ker_eq_bot.mpr
  exact dualEvaluation_injective.comp (TensorProduct.map_injective_of_flat_flat b c
    (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hb))
    (LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp hc)))

theorem right_nondegenerate :
    Specs.D05.M15.InnerTensor.BilinearMetrics.right_nondegenerate := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ b c hb hc
  rw [← LinearMap.flip_separatingLeft, tensorPairing_flip]
  exact left_nondegenerate b.flip c.flip hb hc

/-- An elementary tensor of two nonzero vectors is nonzero: dual functionals
normalized to one evaluate it to one. This argument needs no dimension bound. -/
theorem tmul_ne_zero_of_ne_zero {K X Y : Type*} [Field K]
    [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
    {x : X} {y : Y} (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[K] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hx
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one K hy
  intro h
  have he := congrArg (TensorProduct.dualDistrib K X Y (φ ⊗ₜ[K] ψ)) h
  simp [hφ, hψ] at he

/-- The converse is tested on a nonzero vector in the other left factor. -/
theorem left_nondegenerate_iff :
    Specs.D05.M15.InnerTensor.BilinearMetrics.left_nondegenerate_iff := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b c
  constructor
  · intro h
    constructor
    · intro v hv
      by_contra hv0
      obtain ⟨w, hw⟩ := exists_ne (0 : W)
      apply tmul_ne_zero_of_ne_zero (K := K) hv0 hw
      apply h (v ⊗ₜ[K] w)
      intro z'
      induction z' with
      | tmul v' w' =>
        simp only [tensorPairing_apply, hv, zero_mul]
      | add z t hz ht => simp [hz, ht]
    · intro w hw
      by_contra hw0
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      apply tmul_ne_zero_of_ne_zero (K := K) hv hw0
      apply h (v ⊗ₜ[K] w)
      intro z'
      induction z' with
      | tmul v' w' =>
        simp only [tensorPairing_apply, hw, mul_zero]
      | add z t hz ht => simp [hz, ht]
  · rintro ⟨hb, hc⟩
    exact left_nondegenerate b c hb hc

theorem right_nondegenerate_iff :
    Specs.D05.M15.InnerTensor.BilinearMetrics.right_nondegenerate_iff := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b c
  rw [← LinearMap.flip_separatingLeft, tensorPairing_flip]
  exact left_nondegenerate_iff b.flip c.flip

theorem nondegenerate_tensorPairing :
    Specs.D05.M15.InnerTensor.BilinearMetrics.nondegenerate_tensorPairing := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ b c hb hc
  exact ⟨left_nondegenerate b c hb.1 hc.1, right_nondegenerate b c hb.2 hc.2⟩

/-- In finite dimension injectivity in both slots yields the two isomorphisms
required for perfection; a perfect tensor pairing also includes zero factors. -/
theorem perfect_tensorPairing :
    Specs.D05.M15.InnerTensor.BilinearMetrics.perfect_tensorPairing := by
  intro K V W V' W' _ _ _ _ _ _ _ _ _ _ _ _ _ b c hb hc
  apply LinearMap.IsPerfPair.of_injective
  · exact LinearMap.ker_eq_bot.mp (LinearMap.separatingLeft_iff_ker_eq_bot.mp
      (left_nondegenerate b c hb.separatingLeft hc.separatingLeft))
  · exact LinearMap.ker_eq_bot.mp (LinearMap.separatingRight_iff_flip_ker_eq_bot.mp
      (right_nondegenerate b c hb.separatingRight hc.separatingRight))

theorem symmetric_tensorPairing :
    Specs.D05.M15.InnerTensor.BilinearMetrics.symmetric_tensorPairing := by
  intro K V W _ _ _ _ _ b c hb hc z t
  have hflip : (tensorPairing b c).flip = tensorPairing b c := by
    rw [tensorPairing_flip]
    have hb' : b.flip = b := by ext x y; exact (hb x y).symm
    have hc' : c.flip = c := by ext x y; exact (hc x y).symm
    rw [hb', hc']
  exact (congrArg (fun P : (V ⊗[K] W) →ₗ[K] (V ⊗[K] W) →ₗ[K] K => P z t) hflip).symm

theorem zero_factor_nondegenerate :
    Specs.D05.M15.InnerTensor.BilinearMetrics.zero_factor_nondegenerate := by
  intro K V W _ _ _ _ _ _ b c
  exact ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩

end D05.M15.InnerTensor.BilinearMetrics
