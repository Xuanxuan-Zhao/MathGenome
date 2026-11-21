import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.SurjectivePerturbation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C08OpenMapping
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Surjective perturbations by summing nonlinear successive corrections. -/

namespace ExpandedFA.BanachAlgebra

open Filter Topology
open Specs.ExpandedFA.BanachAlgebra.SurjectivePerturbation

universe u v w

section Corrections

variable {𝕜 : Type u} {X : Type v} {Y : Type w} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace 𝕜 X] [NormedSpace 𝕜 Y] [CompleteSpace X]

/-- Lift each residual through T. No additivity or continuity of the chosen
selection is needed. The residual contracts, so the corrections sum in X. -/
theorem successive_correction_lift (T B : X →L[𝕜] Y) (C : ℝ) (hC : 0 < C)
    (hlift : ∀ y : Y, ∃ x : X, T x = y ∧ ‖x‖ ≤ C * ‖y‖)
    (hsmall : C * ‖B‖ < 1) (y : Y) :
    ∃ x : X, (T + B) x = y ∧ ‖x‖ ≤ (C / (1 - C * ‖B‖)) * ‖y‖ := by
  classical
  choose g hg using hlift
  let q := C * ‖B‖
  have hq0 : 0 ≤ q := mul_nonneg hC.le (norm_nonneg B)
  have hq1 : q < 1 := hsmall
  let h : Y → Y := fun z => z - (T + B) (g z)
  have heq (z : Y) : h z = -B (g z) := by
    simp [h, (hg z).1]
  have hle (z : Y) : ‖h z‖ ≤ q * ‖z‖ := by
    rw [heq, norm_neg]
    calc
      ‖B (g z)‖ ≤ ‖B‖ * ‖g z‖ := B.le_opNorm _
      _ ≤ ‖B‖ * (C * ‖z‖) := mul_le_mul_of_nonneg_left (hg z).2 (norm_nonneg B)
      _ = q * ‖z‖ := by dsimp [q]; ring
  have hnle (n : ℕ) : ‖h^[n] y‖ ≤ q ^ n * ‖y‖ := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc
        ‖h (h^[n] y)‖ ≤ q * ‖h^[n] y‖ := hle _
        _ ≤ q * (q ^ n * ‖y‖) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (n + 1) * ‖y‖ := by ring
  let u : ℕ → X := fun n => g (h^[n] y)
  have ule (n : ℕ) : ‖u n‖ ≤ q ^ n * (C * ‖y‖) := by
    calc
      ‖u n‖ ≤ C * ‖h^[n] y‖ := (hg _).2
      _ ≤ C * (q ^ n * ‖y‖) := mul_le_mul_of_nonneg_left (hnle n) hC.le
      _ = q ^ n * (C * ‖y‖) := by ring
  have sgeom : Summable (fun n : ℕ => q ^ n * (C * ‖y‖)) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_right _
  have snorm : Summable (fun n => ‖u n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) ule sgeom
  have su : Summable u := snorm.of_norm
  let x := ∑' n, u n
  have xbound : ‖x‖ ≤ (C / (1 - C * ‖B‖)) * ‖y‖ := by
    calc
      ‖x‖ ≤ ∑' n, ‖u n‖ := norm_tsum_le_tsum_norm snorm
      _ ≤ ∑' n, q ^ n * (C * ‖y‖) := snorm.tsum_le_tsum ule sgeom
      _ = (∑' n : ℕ, q ^ n) * (C * ‖y‖) := tsum_mul_right
      _ = (1 - q)⁻¹ * (C * ‖y‖) := by rw [tsum_geometric_of_lt_one hq0 hq1]
      _ = (C / (1 - C * ‖B‖)) * ‖y‖ := by dsimp [q]; ring
  have telescopes (n : ℕ) :
      (T + B) (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, map_add, ih, Function.iterate_succ_apply']
      dsimp [u, h]
      abel
  have hlim : Tendsto (fun n : ℕ => h^[n] y) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    apply squeeze_zero (fun _ => norm_nonneg _) hnle
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const ‖y‖
  have lim₁ : Tendsto (fun n : ℕ => (T + B) (∑ i ∈ Finset.range n, u i))
      atTop (𝓝 ((T + B) x)) :=
    ((T + B).continuous.tendsto x).comp su.hasSum.tendsto_sum_nat
  have lim₂ : Tendsto (fun n : ℕ => y - h^[n] y) atTop (𝓝 y) := by
    simpa using tendsto_const_nhds.sub hlim
  simp only [telescopes] at lim₁
  exact ⟨x, tendsto_nhds_unique lim₁ lim₂, xbound⟩

end Corrections

theorem controlled_perturbation_lifts : ControlledPerturbationLifts.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ T B C hC hlift hsmall y
  exact successive_correction_lift T B C hC hlift hsmall y

theorem uniform_perturbation_lifts : UniformPerturbationLifts.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ T hT
  obtain ⟨C, hC, hlift⟩ :=
    ExpandedFA.P1.C08OpenMapping.open_mapping_controlled_preimages 𝕜 X Y T hT
  refine ⟨(1 / 2) / C, 2 * C, div_pos (by norm_num) hC, by positivity, ?_⟩
  intro B hB y
  have hq : C * ‖B‖ < 1 / 2 := by
    have := (lt_div_iff₀ hC).mp hB
    nlinarith
  obtain ⟨x, hx, hxn⟩ := successive_correction_lift T B C hC hlift (by linarith) y
  refine ⟨x, hx, hxn.trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg y)
  apply (div_le_iff₀ (by linarith : 0 < 1 - C * ‖B‖)).mpr
  nlinarith

theorem surjectivity_is_open : SurjectivityIsOpen.{u, v, w} := by
  intro 𝕜 X Y _ _ _ _ _ _ _ T hT
  obtain ⟨δ, K, hδ, _, hlift⟩ := uniform_perturbation_lifts 𝕜 X Y T hT
  exact ⟨δ, hδ, fun B hB y => (hlift B hB y).imp (fun _ h => h.1)⟩

/-- Uniformly bounded lifts at a nearby resolvent value bound its inverse.
Applied to a vector in the kernel at lam, this forces that vector to vanish.
Surjectivity would therefore make the spectral boundary value invertible. -/
theorem spectral_boundary_not_surjective : SpectralBoundaryNotSurjective.{v} := by
  intro X _ _ _ A lam hfront hsurj
  change lam ∈ frontier (spectrum ℂ A) at hfront
  let T : X →L[ℂ] X := lam • 1 - A
  obtain ⟨δ, K, hδ, hK, hlift⟩ := uniform_perturbation_lifts ℂ X X T hsurj
  have hcl : lam ∈ closure (spectrum ℂ A)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hfront
    exact hfront.2
  obtain ⟨mu, hmu, hdist⟩ := Metric.mem_closure_iff.mp hcl
    (min δ ((1 / 2) / K)) (lt_min hδ (div_pos (by norm_num) hK))
  have hmunorm : ‖mu - lam‖ < min δ ((1 / 2) / K) := by
    simpa only [dist_eq_norm, norm_sub_rev] using hdist
  let B : X →L[ℂ] X := (mu - lam) • 1
  have hBnorm : ‖B‖ ≤ ‖mu - lam‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simp [B, norm_smul]
  have hBδ : ‖B‖ < δ := hBnorm.trans_lt (lt_of_lt_of_le hmunorm (min_le_left _ _))
  have hBK : K * ‖B‖ < 1 := by
    have h := hBnorm.trans_lt (lt_of_lt_of_le hmunorm (min_le_right _ _))
    have := (lt_div_iff₀ hK).mp h
    nlinarith
  have hTB : T + B = mu • (1 : X →L[ℂ] X) - A := by
    dsimp [T, B]
    rw [sub_smul]
    abel
  have hunit : IsUnit (mu • (1 : X →L[ℂ] X) - A) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (spectrum.notMem_iff.mp hmu)
  have hinj : Function.Injective (T + B) := by
    rw [hTB]
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
  have hker (x : X) (hx : T x = 0) : x = 0 := by
    obtain ⟨z, hz, hnz⟩ := hlift B hBδ ((T + B) x)
    have hzx : z = x := hinj hz
    subst z
    have hbound : ‖x‖ ≤ (K * ‖B‖) * ‖x‖ := by
      calc
        ‖x‖ ≤ K * ‖(T + B) x‖ := hnz
        _ = K * ‖B x‖ := by simp [hx]
        _ ≤ K * (‖B‖ * ‖x‖) := mul_le_mul_of_nonneg_left (B.le_opNorm x) hK.le
        _ = (K * ‖B‖) * ‖x‖ := by ring
    by_contra hxne
    have := mul_lt_mul_of_pos_right hBK (norm_pos_iff.mpr hxne)
    nlinarith
  have hTinj : Function.Injective T := by
    intro x z hxz
    exact sub_eq_zero.mp (hker (x - z) (by rw [map_sub, hxz, sub_self]))
  have hTunit : IsUnit T := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hTinj, hsurj⟩
  have hspec : lam ∈ spectrum ℂ A := (spectrum.isClosed A).frontier_subset hfront
  exact (spectrum.mem_iff.mp hspec) (by
    simpa only [Algebra.algebraMap_eq_smul_one] using hTunit)

end ExpandedFA.BanachAlgebra
