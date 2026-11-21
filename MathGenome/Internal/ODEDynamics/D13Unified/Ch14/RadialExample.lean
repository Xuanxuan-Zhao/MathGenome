import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch14.RadialExample
import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.Annulus
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.Multipliers
import MathGenome.Internal.ODEDynamics.D13Unified.Ch14.OrbitalStability

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology ContDiff
namespace D13Unified.Ch14.RadialExample
open Ch13.Annulus Ch06.StateDerivative
open Specs.D13Unified.Ch14.RadialExample
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch14.ReturnMap Specs.D13Unified.Ch14.Multipliers

theorem period : PeriodExpected := periodic_circle

theorem radial_variation : RadialVariationExpected := by
  refine ⟨?_, ?_, by simp, ?_, Real.exp_pos _, ?_⟩
  · intro r
    convert (hasDerivAt_id r).mul ((hasDerivAt_const r 1).sub ((hasDerivAt_id r).pow 2)) using 1 <;> first | rfl | (dsimp; ring)
  · intro t
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul (-2)).exp
  · congr 1; ring
  · exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])

lemma norm_sq_derivative_one : HasFDerivAt (fun z : ℂ => ‖z‖^2) (2 • Complex.reCLM) 1 := by
  convert ((Complex.reCLM.hasFDerivAt (x := (1:ℂ))).pow 2).add
    ((Complex.imCLM.hasFDerivAt (x := (1:ℂ))).pow 2) using 1
  · ext z
    simpa [Complex.normSq_apply, pow_two] using Complex.sq_norm z
  · ext z
    simp
lemma amp_deriv (t : ℝ) :
  HasFDerivAt (fun z : ℂ => 1 / Real.sqrt (‖z‖^2 + (1-‖z‖^2)*Real.exp (-2*t)))
    ((Real.exp (-2*t)-1) • Complex.reCLM) 1 := by
  have hq := norm_sq_derivative_one
  have hc : HasFDerivAt (fun _ : ℂ => (1:ℝ)) (0 : ℂ →L[ℝ] ℝ) 1 := hasFDerivAt_const 1 1
  have hD := hq.add ((hc.sub hq).mul_const (Real.exp (-2*t)))
  have hs := hD.sqrt (by norm_num)
  have hi := (hasDerivAt_inv (by norm_num : (Real.sqrt (‖(1:ℂ)‖^2 + (1-‖(1:ℂ)‖^2)*Real.exp (-2*t))) ≠ 0)).comp_hasFDerivAt 1 hs
  convert hi using 1
  · ext z; simp [one_div]
  · ext z; simp; ring

/-- Differentiate the explicit formula on an actual neighborhood of the datum.
The positive denominator condition is open even for negative fixed times. -/
lemma flow_eventually_trajectory (t : ℝ) :
    (fun z : ℂ => flow oscillator t z) =ᶠ[𝓝 (1:ℂ)] (fun z => trajectory z t) := by
  have hcont : Continuous (fun z : ℂ => denominator z t) := by
    unfold denominator
    fun_prop
  have hpos : ∀ᶠ z : ℂ in 𝓝 (1:ℂ), 0 < denominator z t :=
    (isOpen_lt continuous_const hcont).mem_nhds (by simp [denominator])
  exact hpos.mono fun z hz => (flow_eq_trajectory z).2 hz

lemma trajectory_fderiv (t : ℝ) (z : ℂ) :
    (fderiv ℝ (fun w => trajectory w t) 1) z =
      circleCurve t * ((Real.exp (-2*t)*z.re:ℝ)+(z.im:ℂ)*Complex.I) := by
  have hA := amp_deriv t
  have hd := ((Complex.ofRealCLM.hasFDerivAt.comp 1 hA).mul_const
    (Complex.exp ((t:ℂ)*Complex.I))).mul (hasFDerivAt_id (𝕜 := ℝ) (1:ℂ))
  change HasFDerivAt (fun w => trajectory w t) _ (1:ℂ) at hd
  rw [hd.fderiv]
  simp only [Function.comp_apply, Complex.ofRealCLM_apply,
    add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Complex.reCLM_apply, id_eq]
  simp only [norm_one, one_pow, sub_self, zero_mul, add_zero,
    Real.sqrt_one, div_self (by norm_num : (1:ℝ) ≠ 0), Complex.ofReal_one,
    one_mul, circleCurve_eq]
  simp only [smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one]
  linear_combination -Complex.exp ((t:ℂ)*Complex.I) * (Complex.re_add_im z)

theorem coordinate_variation : CoordinateVariationExpected := by
  intro t z
  rw [(flow_eventually_trajectory t).fderiv_eq]
  exact trajectory_fderiv t z

lemma circle_flow_periodic : Function.Periodic (fun t => flow oscillator t 1) (2*Real.pi) := by
  simpa only [canonical_circle.2] using circle_periodic

lemma circle_flow_least (R : ℝ) (hR : 0 < R)
    (hper : Function.Periodic (fun t => flow oscillator t 1) R) : 2*Real.pi ≤ R := by
  simp only [canonical_circle.2] at hper
  exact circle_least_period hR hper

lemma circle_flow_nonconstant : ¬ Ch11.Orbits.IsConstant oscillator 1 := by
  intro h
  have he := h Real.pi (by rw [canonical_circle.1]; trivial)
  rw [canonical_circle.2, circleCurve_eq, Complex.exp_pi_mul_I] at he
  norm_num at he

lemma section_transverse : Complex.imCLM (autonomousEvalValue oscillator 1) ≠ 0 := by
  change Complex.im (oscillator.eval 1) ≠ 0
  simp [oscillator_eval, vectorField]

lemma monodromy_apply (z : ℂ) :
    orbitVariation oscillator 1 (2*Real.pi) z =
      (Real.exp (-4*Real.pi)*z.re:ℝ)+(z.im:ℂ)*Complex.I := by
  have hT : circleCurve (2*Real.pi) = 1 := by simpa only [zero_add, circleCurve_eq, Complex.ofReal_zero, zero_mul, Complex.exp_zero] using circle_periodic 0
  simpa only [orbitVariation, hT, one_mul, show -2*(2*Real.pi)=-4*Real.pi by ring]
    using coordinate_variation (2*Real.pi) z

lemma return_derivative (d : FirstReturnData 1 oscillator 1 (2*Real.pi) Complex.imCLM)
    (v : Complex.imCLM.ker) :
    (fderiv ℝ (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0) v =
      Real.exp (-4*Real.pi) • v := by
  apply Subtype.ext
  rw [d.map_derivative]
  have hv : (v:ℂ).im = 0 := v.property
  have hre : ((v:ℂ).re:ℂ) = (v:ℂ) := by
    apply Complex.ext <;> simp [hv]
  change orbitVariation oscillator 1 (2*Real.pi) (v:ℂ) -
    (Complex.imCLM (orbitVariation oscillator 1 (2*Real.pi) (v:ℂ)) /
      Complex.imCLM (autonomousEvalValue oscillator 1)) • autonomousEvalValue oscillator 1 = _
  rw [monodromy_apply]
  simp only [hv, Complex.ofReal_zero, zero_mul, add_zero, Complex.imCLM_apply,
    Complex.ofReal_im, zero_div, zero_smul, sub_zero]
  change ((Real.exp (-4*Real.pi)*(v:ℂ).re:ℝ):ℂ) =
    Real.exp (-4*Real.pi) • (v:ℂ)
  simp only [Complex.ofReal_mul, Complex.real_smul, hre]


lemma section_finrank : Module.finrank ℝ Complex.imCLM.ker = 1 := by
  have h := Multipliers.section_dimension Complex.imCLM
    (autonomousEvalValue oscillator 1) section_transverse
  have hc : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  omega

lemma return_linearMap (d : FirstReturnData 1 oscillator 1 (2*Real.pi) Complex.imCLM) :
    (fderiv ℝ (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0).toLinearMap =
      Real.exp (-4*Real.pi) • LinearMap.id := by
  apply LinearMap.ext
  intro v
  exact return_derivative d v

lemma return_charpoly (d : FirstReturnData 1 oscillator 1 (2*Real.pi) Complex.imCLM) :
    (fderiv ℝ (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0).toLinearMap.charpoly =
      Polynomial.X - Polynomial.C (Real.exp (-4*Real.pi)) := by
  classical
  let b := Module.finBasisOfFinrankEq ℝ Complex.imCLM.ker section_finrank
  rw [← LinearMap.charpoly_toMatrix _ b]
  have hm : LinearMap.toMatrix b b
      (fderiv ℝ (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0).toLinearMap =
        Matrix.diagonal (fun _ => Real.exp (-4*Real.pi)) := by
    rw [return_linearMap]
    rw [map_smul, LinearMap.toMatrix_id, Matrix.smul_one_eq_diagonal]
  rw [hm, Matrix.charpoly_diagonal]
  simp

lemma return_exists : Nonempty (FirstReturnData 1 oscillator 1 (2*Real.pi) Complex.imCLM) := by
  obtain ⟨d,_,_⟩ := ReturnMap.return_map 1 le_rfl oscillator oscillator_c1 1
    (mem_univ _) (2*Real.pi) Real.two_pi_pos canonical_circle.1 circle_flow_periodic
    circle_flow_least circle_flow_nonconstant Complex.imCLM section_transverse
    univ isOpen_univ (mem_univ _) 1 zero_lt_one
  exact ⟨d⟩

theorem return_multipliers : ReturnMultipliersExpected := by
  refine ⟨Multipliers.variation_conclusions oscillator oscillator_c1 1 (mem_univ _)
    (2*Real.pi) canonical_circle.1 circle_flow_periodic, return_exists, ?_⟩
  intro d
  have h := Multipliers.multipliers 1 le_rfl oscillator oscillator_c1 1 (mem_univ _)
    (2*Real.pi) Real.two_pi_pos canonical_circle.1 circle_flow_periodic
    circle_flow_least circle_flow_nonconstant Complex.imCLM section_transverse d
  have hp := h.2.2.2.1
  rw [return_charpoly d] at hp
  refine ⟨return_derivative d, hp, ?_, ?_⟩
  · simp [monodromy_apply]
  · intro hall
    have hroot : Polynomial.IsRoot
        ((orbitVariation oscillator 1 (2*Real.pi)).toLinearMap.charpoly.map
          (algebraMap ℝ ℂ)) (1:ℂ) := by
      rw [hp]
      simp [Polynomial.IsRoot]
    have hn := hall 1 hroot
    norm_num at hn

lemma return_strict_spectrum
    (d : FirstReturnData 1 oscillator 1 (2*Real.pi) Complex.imCLM) :
    Ch08.MatrixPowerCriteria.StrictSpectrum
      (Ch08.MatrixPowerCriteria.complexify (LinearMap.toMatrix
        (Module.finBasis ℝ Complex.imCLM.ker) (Module.finBasis ℝ Complex.imCLM.ker)
          (fderiv ℝ (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0).toLinearMap)) := by
  classical
  let n := Module.finrank ℝ Complex.imCLM.ker
  haveI : Nonempty (Fin n) := ⟨⟨0, by change 0 < Module.finrank ℝ Complex.imCLM.ker; rw [section_finrank]; norm_num⟩⟩
  have hm : Ch08.MatrixPowerCriteria.complexify (LinearMap.toMatrix
        (Module.finBasis ℝ Complex.imCLM.ker) (Module.finBasis ℝ Complex.imCLM.ker)
          (fderiv ℝ (d.P : Complex.imCLM.ker → Complex.imCLM.ker) 0).toLinearMap) =
      algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) (Real.exp (-4*Real.pi) : ℂ) := by
    rw [return_linearMap]
    rw [map_smul, LinearMap.toMatrix_id]
    ext i j
    by_cases hij : i = j <;>
      simp [Ch08.MatrixPowerCriteria.complexify, Matrix.algebraMap_eq_diagonal,
        Matrix.smul_one_eq_diagonal, hij]

  intro μ hμ
  rw [hm, spectrum.scalar_eq] at hμ
  obtain rfl := Set.mem_singleton_iff.mp hμ
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])

lemma circle_orbit : Ch11.Orbits.orbit oscillator 1 = unitCircle := by
  rw [Ch11.Orbits.orbit, canonical_circle.1, image_univ]
  simpa only [canonical_circle.2] using periodic_circle.2.2.1

theorem orbital_attraction : OrbitalAttractionExpected := by
  obtain ⟨d⟩ := return_exists
  have h := OrbitalStability.orbital_stability 1 le_rfl oscillator oscillator_c1 1
    (mem_univ _) (2*Real.pi) Real.two_pi_pos canonical_circle.1 circle_flow_periodic
    circle_flow_least circle_flow_nonconstant Complex.imCLM d (return_strict_spectrum d)
  change Specs.D13Unified.Ch14.OrbitalDefinitions.exponentiallyOrbitallyStableValue
    oscillator unitCircle ∧ Specs.D13Unified.Ch14.OrbitalDefinitions.orbitalAsymptoticallyStableValue
    oscillator unitCircle
  rw [← circle_orbit]
  exact h

end D13Unified.Ch14.RadialExample
