import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.LagrangeMultipliers
import MathGenome.Internal.MultivariableAnalysis.D04.C05.ExistenceFermat
import MathGenome.Internal.MultivariableAnalysis.D04.C04.RegularLevel
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-! Lagrange multipliers, d04:05:lagrange. The proof uses two-sided
feasible velocities, Fermat, and a linear right inverse of Dg(a). -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace D04.LagrangeMultipliers
open Specs.D04.C04.RegularLevel.Model
open Specs.D04.C05.LagrangeMultipliers.Model

def lagrangian : Specs.D04.C05.LagrangeMultipliers.lagrangianType :=
  @Specs.D04.C05.LagrangeMultipliers.lagrangianValue

theorem covector_coordinates : Specs.D04.C05.LagrangeMultipliers.covector_coordinatesType := by
  intro q ℓ y
  have hy : ∑ i : Fin q, y i • standardBasis q i = y := by
    ext j
    simp [standardBasis_apply]
  calc
    ℓ y = ℓ (∑ i : Fin q, y i • standardBasis q i) := congrArg ℓ hy.symm
    _ = ∑ i : Fin q, y i * ℓ (standardBasis q i) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = ∑ i : Fin q, ℓ (standardBasis q i) * y i :=
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- A covector annihilating a surjection's kernel factors uniquely through it. -/
theorem factor_covector {n q : ℕ} (A : E n →L[ℝ] ℝ) (B : E n →L[ℝ] E q)
    (hB : Function.Surjective B) (hker : ∀ v, B v = 0 → A v = 0) :
    ∃! ℓ : E q →L[ℝ] ℝ, A = ℓ.comp B := by
  obtain ⟨R, hR⟩ := B.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hB)
  let R' : E q →L[ℝ] E n := R.toContinuousLinearMap
  have hBR (y : E q) : B (R' y) = y := DFunLike.congr_fun hR y
  refine ⟨A.comp R', ?_, ?_⟩
  · ext v
    have hk : B (v - R' (B v)) = 0 := by simp [hBR]
    have hv := hker (v - R' (B v)) hk
    simpa only [map_sub, sub_eq_zero, ContinuousLinearMap.comp_apply] using hv
  · intro μ hμ
    ext y
    obtain ⟨v, rfl⟩ := hB y
    have hv := DFunLike.congr_fun hμ v
    change A v = μ (B v) at hv
    change μ (B v) = A (R' (B v))
    rw [← hv]
    have hk : B (v - R' (B v)) = 0 := by simp [hBR]
    exact (sub_eq_zero.mp (by simpa only [map_sub] using hker _ hk))

/-- All tangent directions are realized by feasible curves on an open interval. -/
theorem derivative_annihilates_kernel {n q : ℕ} (U : Set (E n))
    (f : E n → ℝ) (g : E n → E q) (c : E q) (a : E n)
    (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (ha : a ∈ level U g c)
    (hm : LocalMinimumOn (level U g c) f a ∨ LocalMaximumOn (level U g c) f a)
    (hs : Function.Surjective (fderiv ℝ g a)) :
    ∀ v, fderiv ℝ g a v = 0 → totalDerivative f a v = 0 := by
  obtain ⟨_, d, had, _⟩ := RegularLevel.regular_level_local 1 U g c a
    (by constructor <;> simp)
    hU hg ha hs
  have hinv := RegularLevel.LevelGraph.inverse_mem d a ⟨ha, had⟩
  have hk := RegularLevel.LevelGraph.kernel_eq d (by rfl) hU hg (d.projection a) hinv.1
  rw [hinv.2] at hk
  have hdf : TotalDifferentiableAt U f a :=
    (totalDifferentiableAt_iff_differentiableAt U f a hU ha.1).mpr
      ((hf.differentiableOn (by norm_num) a ha.1).differentiableAt (hU.mem_nhds ha.1))
  intro v hv
  have hv' : v ∈ LinearMap.range (fderiv ℝ d.θ (d.projection a)).toLinearMap := by
    rw [hk]
    exact hv
  obtain ⟨w, hw⟩ := hv'
  change (fderiv ℝ d.θ (d.projection a)) w = v at hw
  have hvel := RegularLevel.LevelGraph.image_velocity d (by rfl) (d.projection a) hinv.1 w
  rw [hinv.2, hw] at hvel
  obtain ⟨ε, γ, hε, hγ0, hγM, _, hγ⟩ := hvel
  have hfeas : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ level U g c := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-ε) ε by
      constructor <;> linarith)] with t ht
    exact hγM ht
  rcases hm with hm | hm
  · exact feasible_curve_minimum U (level U g c) f a γ v hdf hm hγ0 hγ hfeas
  · exact feasible_curve_maximum U (level U g c) f a γ v hdf hm hγ0 hγ hfeas

/-- The gradient equality is the same covector equation under the Euclidean
inner-product identification, with the actual coordinate functions of g. -/
theorem gradient_of_factor {n q : ℕ} (f : E n → ℝ) (g : E n → E q)
    (a : E n) (ℓ : E q →L[ℝ] ℝ) (hg : DifferentiableAt ℝ g a)
    (he : totalDerivative f a = ℓ.comp (totalDerivative g a)) :
    scalarGradient f a = ∑ i : Fin q,
      ℓ (standardBasis q i) • scalarGradient (fun x => g x i) a := by
  apply ext_inner_right ℝ
  intro v
  rw [← scalarGradient_represents, he, ContinuousLinearMap.comp_apply,
    covector_coordinates, sum_inner]
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left, ← scalarGradient_represents]
  have hgi := (PiLp.hasFDerivAt_apply 2 (g a) i).comp a hg.hasFDerivAt
  have hcomp : totalDerivative (fun x => g x i) a =
      (PiLp.proj 2 (fun _ : Fin q => ℝ) i).comp (totalDerivative g a) := hgi.fderiv
  rw [hcomp]
  rfl

/-- Differentiation uses a fixed ℓ; the sign is f - ℓ g. -/
theorem equations_of_factor {n q : ℕ} (f : E n → ℝ) (g : E n → E q)
    (a : E n) (ℓ : E q →L[ℝ] ℝ) (hf : DifferentiableAt ℝ f a)
    (hg : DifferentiableAt ℝ g a)
    (he : totalDerivative f a = ℓ.comp (totalDerivative g a)) :
    MultiplierEquations f g a ℓ := by
  refine ⟨he, gradient_of_factor f g a ℓ hg he, ?_⟩
  have hfun : Specs.D04.C05.LagrangeMultipliers.Model.lagrangian f g ℓ =
      fun x => f x - ℓ (g x) := by
    funext x
    exact congrArg (f x - ·) (covector_coordinates ℓ (g x)).symm
  apply (hasTotalDerivative_iff_hasFDerivAt univ _ 0 a isOpen_univ (mem_univ a)).mpr
  have hd := hf.hasFDerivAt.sub (ℓ.hasFDerivAt.comp a hg.hasFDerivAt)
  change HasFDerivAt (fun x => f x - ℓ (g x))
    (totalDerivative f a - ℓ.comp (totalDerivative g a)) a at hd
  rw [← he, sub_self] at hd
  simpa only [hfun] using hd

theorem lagrange_multipliers : Specs.D04.C05.LagrangeMultipliers.lagrange_multipliersType := by
  intro n q U f g c a hU hf hg ha hm hs
  have hdf := (hf.differentiableOn (by norm_num) a ha.1).differentiableAt (hU.mem_nhds ha.1)
  have hdg := (hg.differentiableOn (by norm_num) a ha.1).differentiableAt (hU.mem_nhds ha.1)
  obtain ⟨ℓ, hℓ, hu⟩ := factor_covector (totalDerivative f a) (totalDerivative g a) hs
    (derivative_annihilates_kernel U f g c a hU hf hg ha hm hs)
  exact ⟨ℓ, equations_of_factor f g a ℓ hdf hdg hℓ, fun μ hμ => hu μ hμ.1⟩

theorem zero_constraints_fermat : Specs.D04.C05.LagrangeMultipliers.zero_constraints_fermatType := by
  intro n U f g c a hU hf hg ha hm
  have hl : level U g c = U := RegularLevel.zero_constraints U g c
  have hex := lagrange_multipliers U f g c a hU hf hg
    (show a ∈ level U g c by rwa [hl])
    (show LocalMinimumOn (level U g c) f a ∨ LocalMaximumOn (level U g c) f a by
      rwa [hl])
    (show Function.Surjective (totalDerivative g a) from
      fun y => ⟨0, Subsingleton.elim _ _⟩)
  obtain ⟨ℓ, hℓ⟩ := hex.exists
  have hz : totalDerivative f a = 0 := by
    have he : totalDerivative f a = ℓ.comp (totalDerivative g a) := hℓ.1
    rw [he]
    ext v
    change ℓ (totalDerivative g a v) = 0
    rw [show totalDerivative g a v = 0 from Subsingleton.elim _ _, map_zero]
  have hgrad : scalarGradient f a = 0 := by
    have he : scalarGradient f a = ∑ i : Fin 0,
        ℓ (standardBasis 0 i) • scalarGradient (fun x => g x i) a := hℓ.2.1
    simpa using he
  refine ⟨hz, hgrad, ?_, hex⟩
  intro x
  simp [Specs.D04.C05.LagrangeMultipliers.Model.lagrangian]

theorem full_codimension_multipliers :
    Specs.D04.C05.LagrangeMultipliers.full_codimension_multipliersType := by
  intro n U f g c a hU hf hg ha hs
  obtain ⟨hiso, _⟩ := RegularLevel.full_codimension 1 U g c a
    (by constructor <;> simp)
    hU hg ha hs
  obtain ⟨O, hO, haO, he⟩ := hiso
  have hi : IsolatedPoint (level U g c) ⟨a, ha⟩ := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO a haO
    refine ⟨r, hr, fun x hx hxa => ?_⟩
    change ‖x - a‖ < r at hxa
    have hxO := hball (by simpa [dist_eq_norm] using hxa)
    have hx' : x ∈ ({a} : Set (E n)) := he ▸ ⟨hx, hxO⟩
    exact mem_singleton_iff.mp hx'
  obtain ⟨hmin, hmax⟩ := isolated_strict_extrema (level U g c) f ⟨a, ha⟩ hi
  refine ⟨⟨O, hO, haO, he⟩, hmin, hmax, ?_⟩
  exact lagrange_multipliers U f g c a hU hf hg ha
    (Or.inl ((strict_extrema_are_extrema (level U g c) f a).1 hmin)) hs

end D04.LagrangeMultipliers
