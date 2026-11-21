import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch16.HopfReturnExpansion
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.HopfPolarReduction
import MathGenome.Internal.ODEDynamics.D13Unified.Ch16.HopfAngularScalarEstimates
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section

namespace D13Unified.Ch16.HopfReturnExpansion

open Complex Set
open scoped ComplexConjugate
open Specs.D13Unified.Ch16.CubicHomologicalElimination
open Specs.D13Unified.Ch16.CubicNormalForm
open Specs.D13Unified.Ch16.HopfReturnExpansion

theorem direction_norm (θ : ℝ) : ‖direction θ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I θ

theorem direction_conj_mul (θ : ℝ) : conj (direction θ) * direction θ = 1 := by
  rw [Complex.conj_mul', direction_norm]
  norm_num

theorem polarPoint_norm (r θ : ℝ) : ‖polarPoint r θ‖ = |r| := by
  simp [polarPoint, direction_norm, Complex.norm_real, Real.norm_eq_abs]

/-- Rotation does not change the size of the normal-form error. -/
theorem polarRemainder_norm (F : ℝ × ℂ → ℂ) (μ r θ : ℝ) :
    ‖polarRemainder F θ r μ‖ = ‖remainder F (μ, polarPoint r θ)‖ := by
  simp [polarRemainder, direction_norm]

theorem polarRemainder_bound (F : ℝ × ℂ → ℂ) (ε ρ C μ r θ : ℝ)
    (hR : UniformRemainderBounds F ε ρ C) (hμ : |μ| < ε) (hr : |r| < ρ) :
    ‖polarRemainder F θ r μ‖ ≤ C * |r| ^ 4 := by
  have h := (hR (μ, polarPoint r θ) ⟨hμ, by simpa [polarPoint_norm] using hr⟩).2.2.2.2.2.1
  simpa [polarRemainder_norm, polarPoint_norm] using h

/-- The division in angular velocity loses one order, but is uniformly
controlled in angle and parameter, and has its correct value at zero. -/
theorem angular_remainder_bound (F : ℝ × ℂ → ℂ) (ε ρ C μ r θ : ℝ)
    (hR : UniformRemainderBounds F ε ρ C)
    (hμ : |μ| < ε) (hr : |r| < ρ) :
    |(polarRemainder F θ r μ).im / r| ≤ C * |r| ^ 3 := by
  by_cases hz : r = 0
  · simp [hz]
  have ha : 0 < |r| := abs_pos.mpr hz
  calc
    |(polarRemainder F θ r μ).im / r| = |(polarRemainder F θ r μ).im| / |r| := abs_div _ _
    _ ≤ ‖polarRemainder F θ r μ‖ / |r| :=
      div_le_div_of_nonneg_right (Complex.abs_im_le_norm _) ha.le
    _ ≤ (C * |r| ^ 4) / |r| :=
      div_le_div_of_nonneg_right (polarRemainder_bound F ε ρ C μ r θ hR hμ hr) ha.le
    _ = C * |r| ^ 3 := by field_simp

theorem uniformAngularPositivity : UniformAngularPositivity := by
  intro F ω ε ρ C hω hε hρ hC hR hb hb0 hc
  let M : ℝ := ‖coefficient F 0‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMC : 0 < M + C := add_pos hM hC
  have hbn : ∀ᶠ μ in nhds (0 : ℝ), 3 * ω / 4 < spectralImag F μ :=
    hb.eventually (lt_mem_nhds (show 3 * ω / 4 < spectralImag F 0 by rw [hb0]; linarith))
  have hcn : ∀ᶠ μ in nhds (0 : ℝ), ‖coefficient F μ‖ < M :=
    hc.norm.eventually (gt_mem_nhds (show ‖coefficient F 0‖ < M by dsimp [M]; linarith))
  obtain ⟨η, hη, hl⟩ := Metric.eventually_nhds_iff.mp (hbn.and hcn)
  let ε' := min ε η
  let ρ' := min ρ (min 1 (ω / (4 * (M + C))))
  have hρ' : 0 < ρ' := lt_min hρ (lt_min zero_lt_one (by positivity))
  refine ⟨ε', lt_min hε hη, ρ', hρ', min_le_left _ _, min_le_left _ _, ?_⟩
  intro μ r θ hμ hr
  have hμe : |μ| < ε := hμ.trans_le (min_le_left _ _)
  have hμη : dist μ 0 < η := by
    simpa only [dist_zero_right, Real.norm_eq_abs] using hμ.trans_le (min_le_right ε η)
  obtain ⟨hbμ, hcμ⟩ := hl hμη
  have hrr : |r| < ρ := hr.trans_le (min_le_left _ _)
  have hr1 : |r| ≤ 1 := (hr.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hrt : |r| < ω / (4 * (M + C)) :=
    hr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have ht : (M + C) * |r| < ω / 4 := by
    have h := (lt_div_iff₀ (show 0 < 4 * (M + C) by positivity)).mp hrt
    nlinarith
  have hp2 : |r| ^ 2 ≤ |r| := by nlinarith [abs_nonneg r]
  have hp3 : |r| ^ 3 ≤ |r| := by
    calc
      |r| ^ 3 = |r| ^ 2 * |r| := by ring
      _ ≤ |r| * |r| := mul_le_mul_of_nonneg_right hp2 (abs_nonneg r)
      _ ≤ |r| := by nlinarith [abs_nonneg r]
  have hev := angular_remainder_bound F ε ρ C μ r θ hR hμe hrr
  have hcv : |(coefficient F μ).im * r ^ 2| ≤ M * |r| ^ 2 := by
    rw [abs_mul, abs_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm _).trans hcμ.le) (sq_nonneg r)
  have hlowc : -(M * |r| ^ 2) ≤ (coefficient F μ).im * r ^ 2 :=
    (abs_le.mp hcv).1
  have hlowe : -(C * |r| ^ 3) ≤ (polarRemainder F θ r μ).im / r :=
    (abs_le.mp hev).1
  have hc2 := mul_le_mul_of_nonneg_left hp2 hM.le
  have he3 := mul_le_mul_of_nonneg_left hp3 hC.le
  dsimp [angularVelocity]
  nlinarith

/-- Exact cubic coefficient for an angular equation; no division by a. -/
theorem coefficientAtZero : CoefficientAtZero := by
  intro F ω ha hb
  simp [cubicReturnCoefficient, angularCubic,
    angularLinear, ha, hb, firstLyapunovCoefficient, turnAngle]
  ring

/-- This elementary identity isolates a fourth-order residual without
expanding a reciprocal into an assumed convergent series. -/
theorem angular_quotient_identity (a b u v d e r : ℝ)
    (hb : b ≠ 0) (hr : r ≠ 0) (hD : b + v * r ^ 2 + e / r ≠ 0) :
    (a * r + u * r ^ 3 + d) / (b + v * r ^ 2 + e / r) -
      ((a / b) * r + (u / b - a * v / b ^ 2) * r ^ 3) =
    (d - (a / b) * e - (u / b - a * v / b ^ 2) * v * r ^ 5 -
      (u / b - a * v / b ^ 2) * e * r ^ 2) / (b + v * r ^ 2 + e / r) := by
  apply (eq_div_iff hD).mpr
  rw [sub_mul, div_mul_cancel₀ _ hD]
  field_simp [hb, hr]
  ring

theorem polarVelocityIdentity : PolarVelocityIdentity := by
  intro F μ r θ hr
  rw [CubicNormalForm.transformedField_eq]
  have hu := direction_conj_mul θ
  have hz :
      conj (direction θ) *
        (eigenvalue (spectralReal F μ) (spectralImag F μ) * polarPoint r θ +
          coefficient F μ * polarPoint r θ ^ 2 * conj (polarPoint r θ) +
          remainder F (μ, polarPoint r θ)) =
      eigenvalue (spectralReal F μ) (spectralImag F μ) * (r : ℂ) +
        coefficient F μ * (r : ℂ) ^ 3 + polarRemainder F θ r μ := by
    simp only [polarPoint, map_mul, Complex.conj_ofReal, polarRemainder]
    calc
      _ = eigenvalue (spectralReal F μ) (spectralImag F μ) * r *
            (conj (direction θ) * direction θ) +
          coefficient F μ * (r : ℂ) ^ 3 *
            (conj (direction θ) * direction θ) ^ 2 +
          conj (direction θ) * remainder F (μ, (r : ℂ) * direction θ) := by ring
      _ = _ := by rw [hu]; ring
  rw [hz]
  apply Complex.ext <;>
    simp [radialVelocity, angularVelocity, eigenvalue, Complex.mul_re,
      Complex.mul_im, ← Complex.ofReal_pow] <;> field_simp [hr]

/-- The critical normalization follows from the actual upstream spectral
construction, without transversality or cubic nondegeneracy assumptions. -/
theorem source_coefficient_at_zero (F : ℝ × ℂ → ℂ) (ω : ℝ)
    (hF : ContDiffAt ℝ 5 F (0, 0)) (hω : 0 < ω)
    (heig : Module.End.HasEigenvalue (complexifiedLinearization F 0).toLin' (eigenvalue 0 ω))
    (heq : ∀ᶠ μ in nhds (0 : ℝ), F (μ, 0) = 0) :
    cubicReturnCoefficient F 0 = turnAngle * firstLyapunovCoefficient F / ω := by
  obtain ⟨ha, hb, _⟩ := CubicNormalForm.normalForm F ω hF hω heig heq
  exact coefficientAtZero F ω ha hb

theorem polarNeighborhood : PolarNeighborhood := by
  intro F ω hF hω heig heq
  obtain ⟨_, hb0, ε, hε, ρ, hρ, C, hC, hcoord, hR, hs⟩ :=
    CubicNormalForm.normalForm F ω hF hω heig heq
  have hs0 := hs 0 (by simpa using hε)
  have hb := hs0.2.2.1.continuousAt
  have hc := hs0.2.2.2.1.continuousAt
  obtain ⟨ε', hε', ρ', hρ', he, hr, hp⟩ :=
    uniformAngularPositivity F ω ε ρ C hω hε hρ hC hR hb hb0 hc
  exact ⟨ε', hε', ρ', hρ', CubicNormalForm.coordinateValidity_mono hcoord he hr, hp⟩

theorem angular_field_residual (F : ℝ × ℂ → ℂ) (μ r θ : ℝ)
    (hb : spectralImag F μ ≠ 0) (hr : r ≠ 0)
    (hD : angularVelocity F θ r μ ≠ 0) :
    angularField F θ r μ -
      (angularLinear F μ * r + angularCubic F μ * r ^ 3) =
    ((polarRemainder F θ r μ).re -
      angularLinear F μ * (polarRemainder F θ r μ).im -
      angularCubic F μ * (coefficient F μ).im * r ^ 5 -
      angularCubic F μ * (polarRemainder F θ r μ).im * r ^ 2) /
      angularVelocity F θ r μ := by
  exact angular_quotient_identity _ _ _ _ _ _ _ hb hr hD

theorem polarPoint_zero (r : ℝ) : polarPoint r 0 = (r : ℂ) := by
  simp [polarPoint, direction]

theorem polarPoint_turn (r : ℝ) : polarPoint r turnAngle = (r : ℂ) := by
  simp [polarPoint, direction, turnAngle]

/-- A strictly increasing angle rules out an earlier positive-ray return;
the negative real ray at angle π does not count as an intersection. -/
theorem polarPoint_not_positiveRay (r θ : ℝ) (hr : 0 < r)
    (hθ : θ ∈ Ioo 0 turnAngle) : ¬ positiveRay (polarPoint r θ) := by
  rintro ⟨hi, hre⟩
  have hs : Real.sin θ = 0 := by
    simpa [polarPoint, direction, Complex.mul_im, hr.ne', Complex.exp_ofReal_mul_I_im] using hi
  have hc : 0 < r * Real.cos θ := by
    simpa [polarPoint, direction, Complex.mul_re, Complex.exp_ofReal_mul_I_re] using hre
  rcases Real.sin_eq_zero_iff_cos_eq.mp hs with h | h
  · have hz := (Real.cos_eq_one_iff_of_lt_of_lt
      (by dsimp [turnAngle] at hθ; linarith [hθ.1, Real.pi_pos]) hθ.2).mp h
    exact hθ.1.ne' hz
  · rw [h] at hc
    nlinarith

open Specs.D13Unified.Ch16.HopfPolarReduction
  (SignedPolarData polarBox ReconstructionOnChart)
open _root_.D13Unified.Ch16.HopfAngularScalarEstimates
  (AngularData Hypotheses amplitude endpoint radialSolution dividedDisplacement
    endpointError parameterBox)

/-- Reassociate the polar variables to the scalar IVP interface. -/
def scalarData (F : ℝ × ℂ → ℂ) (ε ρ C : ℝ)
    (G : ℝ × (ℝ × ℝ) → ℝ) : AngularData where
  T := turnAngle
  ρ := ρ
  ε := ε
  M := C
  A := angularLinear F
  B := angularCubic F
  domain := {q | (q.1.1, q.1.2, q.2) ∈ polarBox ε ρ}
  G := fun q => G (q.1.1, q.1.2, q.2)

/-- The polar reduction supplies vector-field hypotheses, without assuming
any solution or return-map certificate. -/
theorem scalarHypotheses (F : ℝ × ℂ → ℂ) (ω ε ρ C : ℝ)
    (G : ℝ × (ℝ × ℝ) → ℝ) (hε : 0 < ε) (hρ : 0 < ρ) (hC : 0 < C)
    (hp : SignedPolarData F ω ε ρ C G) :
    Hypotheses (scalarData F ε ρ C G) := by
  rcases hp with ⟨hcoord, hR, hG, hAB, hpos, hpoint⟩
  have hbox : ∀ q ∈ _root_.D13Unified.Ch16.HopfAngularScalarEstimates.cylinder
      (scalarData F ε ρ C G), (q.1.1,q.1.2,q.2) ∈ polarBox ε ρ := by
    intro q hq
    change q.1.1 ∈ Icc 0 turnAngle ∧ |q.1.2| < ρ ∧ |q.2| < ε at hq
    exact ⟨by linarith [hq.1.1], by dsimp [turnAngle] at hq ⊢; linarith [hq.1.2],
      hq.2.1, hq.2.2⟩
  refine ⟨by dsimp [scalarData, turnAngle]; positivity, hρ, hε, hC.le, ?_,
    hbox, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (HopfPolarReduction.polarBox_isOpen ε ρ).preimage
      ((continuous_fst.fst).prodMk (continuous_fst.snd.prodMk continuous_snd))
  · exact hG.comp
      (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.prodMk contDiffOn_snd))
      (fun _ hq => hq)
  · intro μ hμ
    exact (hAB μ (abs_lt.mpr hμ)).1.contDiffWithinAt
  · intro μ hμ
    exact (hAB μ (abs_lt.mpr hμ)).2.contDiffWithinAt
  · intro θ hθ μ hμ
    have hx := hbox ((θ,0),μ) ⟨hθ, by simpa [scalarData] using hρ, hμ⟩
    exact (hpoint _ hx).1
  · intro q hq
    obtain ⟨_, _, _, hdr, hdμ, _⟩ := hpoint _ (hbox q hq)
    exact ⟨hdr, hdμ⟩
  · intro q hq
    obtain ⟨_, _, _, _, _, hv, hr, hm⟩ := hpoint _ (hbox q hq)
    exact ⟨hv, hr, hm⟩

/-- Keep the angular curve, its clock, and chart confinement together when
passing to physical time. -/
theorem fullAngularTurn_of_curve (F : ℝ × ℂ → ℂ) (ω ε ρ μ r : ℝ)
    (u : ℝ → ℝ) (hrec : ReconstructionOnChart F ε ρ)
    (hpos : ∀ θ s ν, |s| < ρ → |ν| < ε → ω / 2 < angularVelocity F θ s ν)
    (hμ : |μ| < ε) (hr : 0 < r) (hu0 : u 0 = r)
    (hu : ContinuousOn u (Icc 0 turnAngle))
    (hud : ∀ θ ∈ Icc 0 turnAngle,
      HasDerivWithinAt u (angularField F θ (u θ) μ) (Icc 0 turnAngle) θ)
    (hur : ∀ θ ∈ Icc 0 turnAngle, 0 < u θ ∧ u θ < ρ) :
    FullAngularTurn F ω μ r (u turnAngle) ρ := by
  obtain ⟨T, hT, z, hc0, hcT, hcc, hcm, hcb, hcd, hzc, hzd,
    hzclock, hz0, hzT, hfirst⟩ := hrec μ r u hμ hr hu0 hu hud hur
  let clock := Specs.D13Unified.Ch16.HopfPolarReduction.physicalClock F μ u
  change clock turnAngle = T at hcT
  subst T
  refine ⟨u, clock, z, hu0, rfl, hc0, hT, hcm, hcb, ?_, hz0, hzT, ?_, ?_⟩
  · intro θ hθ
    exact ⟨(hur θ hθ).1, (hur θ hθ).2,
      hpos θ (u θ) μ (by rw [abs_of_pos (hur θ hθ).1]; exact (hur θ hθ).2) hμ,
      hud θ hθ, hcd θ hθ, hzclock θ hθ⟩
  · intro t ht
    exact ⟨(hzd t ht).2, (hzd t ht).1⟩
  · intro t ht
    -- The bijective clock transfers exclusion of intermediate ray crossings.
    obtain ⟨θ, hθ, heq⟩ := hcb.surjOn ⟨ht.1.le, ht.2.le⟩
    have hθ0 : 0 < θ := by
      by_contra hn
      have hz : θ = 0 := le_antisymm (le_of_not_gt hn) hθ.1
      have hz' : t = 0 := by simpa only [hz, hc0] using heq.symm
      exact ht.1.ne' hz'
    have hθT : θ < turnAngle := by
      by_contra hn
      have hz : θ = turnAngle := le_antisymm hθ.2 (le_of_not_gt hn)
      have hz' : clock turnAngle = t := by simpa only [hz] using heq
      exact ht.2.ne hz'.symm
    rw [← heq, hzclock θ hθ]
    exact polarPoint_not_positiveRay (u θ) θ (hur θ hθ).1 ⟨hθ0, hθT⟩

/-- Assemble the signed scalar estimates and physical-clock reconstruction
on a common local chart. The C² quotient comes from normalized amplitude. -/
theorem returnExpansion : ReturnExpansion := by
  intro F ω hF hω heig heq
  refine ⟨source_coefficient_at_zero F ω hF hω heig heq, ?_⟩
  obtain ⟨ε, hε, ρ, hρ, C, hC, G, hp, hrec⟩ :=
    HopfPolarReduction.polarReduction F ω hF hω heig heq
  let d := scalarData F ε ρ C G
  have hd : Hypotheses d := scalarHypotheses F ω ε ρ C G hε hρ hC hp
  obtain ⟨δ, η, L, CE, a, b, hCE, he, hE, hEb⟩ :=
    HopfAngularScalarEstimates.angularEstimates d hd
  rcases he with ⟨hδ, hδρ, hη, hηε, hL, ha, hb, hLδ, hdom,
    hY, hsol, hzero, hQ, hfactor⟩
  let P : ℝ × ℝ → ℝ := fun q => endpoint d hd q.1 q.2
  let Q : ℝ × ℝ → ℝ := fun q => dividedDisplacement d hd q.1 q.2
  have hboxes : returnBox δ η = parameterBox δ η := by
    ext q
    exact and_congr abs_lt abs_lt
  have hPf : P = fun q => q.1 * (1 + Q q) := by
    funext q
    exact hfactor q.1 q.2
  have hQ' : ContDiffOn ℝ 2 Q (returnBox δ η) := by
    rw [hboxes]; exact hQ
  have hP : ContDiffOn ℝ 2 P (returnBox δ η) := by
    rw [hPf]
    exact contDiffOn_fst.mul (contDiffOn_const.add hQ')
  have herror : returnError F P = fun q => endpointError d hd q.1 q.2 := by
    rfl
  refine ⟨η, hη, ρ, hρ, δ, hδ, CE + 1, by linarith, P, Q,
    hδρ, CubicNormalForm.coordinateValidity_mono hp.1 hηε.le le_rfl,
    hP, hQ', ?_, ?_, ?_, ?_⟩
  · rw [herror, hboxes]
    exact hE
  · intro μ hμ
    refine ⟨?_, ?_⟩
    · simp [P, endpoint, radialSolution]
    · have hh := hzero μ hμ d.T (right_mem_Icc.mpr hd.T_pos.le)
      change amplitude d hd d.T 0 μ - 1 = _
      rw [hh]
      simp only [d, scalarData, turnAngle, linearReturnFactor, angularLinear, mul_comm]
  · intro q hq
    have hq' : q ∈ parameterBox δ η := by rwa [hboxes] at hq
    obtain ⟨_, hv, hr, hm⟩ := hEb q.1 q.2 hq'
    refine ⟨hfactor q.1 q.2, ?_, ?_, ?_⟩
    · rw [herror]
      exact hv.trans (mul_le_mul_of_nonneg_right (by linarith : CE ≤ CE + 1) (by positivity))
    · rw [herror]
      exact hr.trans (mul_le_mul_of_nonneg_right (by linarith : CE ≤ CE + 1) (by positivity))
    · rw [herror]
      exact hm.trans (mul_le_mul_of_nonneg_right (by linarith : CE ≤ CE + 1) (by positivity))
  · intro μ r hμ hr hrδ
    have hrμ : (r,μ) ∈ parameterBox δ η := ⟨abs_lt.mp (by rwa [abs_of_pos hr]), abs_lt.mp hμ⟩
    let u := fun θ => radialSolution d hd θ r μ
    have hI : Icc 0 turnAngle ⊆ Ioo a b := by
      intro θ hθ
      exact ⟨ha.trans_le hθ.1, hθ.2.trans_lt hb⟩
    obtain ⟨_, hder, hu0, hbounds⟩ := hsol r μ hrμ
    have hu : ContinuousOn u (Icc 0 turnAngle) :=
      (HopfAngularScalarEstimates.radialSolution_c2_on d hd
        (fun θ hθ => hdom ⟨hI hθ,hrμ⟩)).continuousOn
    have hur : ∀ θ ∈ Icc 0 turnAngle, 0 < u θ ∧ u θ < ρ := by
      intro θ hθ
      have hh : |u θ| < ρ := (hbounds θ hθ).2.1
      exact ⟨(hbounds θ hθ).2.2 hr, (le_abs_self _).trans_lt hh⟩
    have hud : ∀ θ ∈ Icc 0 turnAngle,
        HasDerivWithinAt u (angularField F θ (u θ) μ) (Icc 0 turnAngle) θ := by
      intro θ hθ
      have hh := (hder θ (hI hθ)).2.2
      have hx : (θ,u θ,μ) ∈ polarBox ε ρ :=
        ⟨by linarith [hθ.1], by dsimp [turnAngle] at hθ ⊢; linarith [hθ.2],
          by rw [abs_of_pos (hur θ hθ).1]; exact (hur θ hθ).2,
          hμ.trans hηε⟩
      rw [(hp.2.2.2.2.2 _ hx).2.1]
      exact hh.hasDerivWithinAt
    exact fullAngularTurn_of_curve F ω ε ρ μ r u hrec hp.2.2.2.2.1
      (hμ.trans hηε) hr hu0 hu hud hur

end D13Unified.Ch16.HopfReturnExpansion
