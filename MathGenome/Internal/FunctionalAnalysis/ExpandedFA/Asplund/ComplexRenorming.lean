import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Asplund.ComplexRenorming
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Asplund.SimultaneousRenorming

noncomputable section
namespace ExpandedFA.Asplund.ComplexRenorming

open SimultaneousRenorming NormSquareConjugate Iteration OrderLimit
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
local instance : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E

lemma real_norm (p : E → ℝ) (hp : EquivalentComplexNorm p) : EquivalentNorm p := by
  refine ⟨⟨⟨hp.1.1.1, ?_, hp.1.1.2.2⟩, hp.1.2⟩, hp.2⟩
  intro a x
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.norm_real, Real.norm_eq_abs] using hp.1.1.2.1 (a : ℂ) x

theorem real_dual_identification : Spec.RealDualIdentification := by
  intro E _ _
  constructor
  · intro f x
    rfl
  · intro u x
    rfl

lemma realDualEquiv_apply (f : E →L[ℂ] ℂ) (x : E) :
    realDualEquiv f x = (f x).re := rfl

lemma complex_apply_bound (p : E → ℝ) (hp : EquivalentComplexNorm p)
    (f : E →L[ℂ] ℂ) (x : E) :
    ‖f x‖ ≤ dualNorm p (realDualEquiv f) * p x := by
  let u := realDualEquiv f
  let c : NNReal := ⟨dualNorm p u, dualNorm_nonneg p (real_norm p hp) u⟩
  let s := P1.C01Norm.seminormOfAxioms ℂ E p hp.1.1
  have h : ∀ y, |u y| ≤ (c • s) y := by
    intro y
    exact abs_apply_le_dualNorm p (real_norm p hp) u y
  have hb := StrongDual.norm_extendRCLike_le_seminorm (𝕜 := ℂ) u h x
  change ‖(realDualEquiv.symm (realDualEquiv f)) x‖ ≤ _ at hb
  rw [LinearIsometryEquiv.symm_apply_apply] at hb
  change ‖f x‖ ≤ dualNorm p (realDualEquiv f) * p x at hb
  exact hb

lemma complex_dual_isLUB (p : E → ℝ) (hp : EquivalentComplexNorm p)
    (f : E →L[ℂ] ℂ) :
    IsLUB ((fun x => ‖f x‖) '' {x : E | p x ≤ 1}) (dualNorm p (realDualEquiv f)) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (complex_apply_bound p hp f x).trans
      (by simpa using mul_le_mul_of_nonneg_left hx (dualNorm_nonneg p (real_norm p hp) _))
  · intro b hb
    apply (dualNorm_isLUB E p (real_norm p hp) (realDualEquiv f)).2
    rintro _ ⟨x, hx, rfl⟩
    exact (Complex.abs_re_le_norm (f x)).trans (hb ⟨x, hx, rfl⟩)

theorem dual_norm_identification : Spec.DualNormIdentification := by
  intro E _ _ p hp f
  exact (complex_dual_isLUB p hp f).csSup_eq ⟨‖f 0‖, 0,
    by simp [((hp.1.2 0).2 rfl)], rfl⟩

theorem common_dual_topology : Spec.CommonDualTopology := by
  intro E _ _ p hp
  refine ⟨continuous_iff_norm_bound p (real_norm p hp), ?_⟩
  intro f
  constructor
  · intro hf
    obtain ⟨a, b, ha, hb, hab⟩ := hp.2
    let g : E →L[ℂ] ℂ := ⟨f, hf⟩
    refine ⟨‖g‖ / a, div_nonneg (norm_nonneg g) ha.le, ?_⟩
    intro x
    have hx : ‖x‖ ≤ p x / a := (le_div_iff₀ ha).mpr (by simpa [mul_comm] using (hab x).1)
    exact (g.le_opNorm x).trans (by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hx (norm_nonneg g))
  · rintro ⟨M, hM, hbound⟩
    obtain ⟨a, b, ha, hb, hab⟩ := hp.2
    exact (f.mkContinuous (M * b) (fun x => (hbound x).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hab x).2 hM))).continuous

lemma infimal_phase (φ ψ : E → ℝ) (hφ : PhaseInvariant φ) (hψ : PhaseInvariant ψ) :
    PhaseInvariant (infimalMean E φ ψ) := by
  intro z hz x
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hsurj : Function.Surjective (fun y : E => z • y) := by
    intro y
    exact ⟨z⁻¹ • y, by simp [smul_smul, hz0]⟩
  have heq : (fun y => φ (z • x + y) + ψ (z • x - y)) ∘ (fun y : E => z • y) =
      (fun y => φ (x + y) + ψ (x - y)) := by
    funext y
    dsimp only [Function.comp_apply]
    rw [← smul_add, ← smul_sub, hφ z hz, hψ z hz]
  have hr := congrArg Set.range heq
  rw [hsurj.range_comp] at hr
  exact congrArg (fun S : Set ℝ => sInf S / 2) hr

lemma iterates_phase (φ ψ : E → ℝ) (hφ : PhaseInvariant φ) (hψ : PhaseInvariant ψ) :
    ∀ n, PhaseInvariant (phi E φ ψ n) ∧ PhaseInvariant (psi E φ ψ n) := by
  intro n
  induction n with
  | zero => exact ⟨hφ, hψ⟩
  | succ n ih =>
    constructor
    · intro z hz x
      rw [phi_succ, phi_succ, ih.1 z hz, ih.2 z hz]
    · exact infimal_phase _ _ ih.1 ih.2

lemma theta_phase (φ ψ : E → ℝ) (hφ : PhaseInvariant φ) (hψ : PhaseInvariant ψ) :
    PhaseInvariant (theta E φ ψ) := by
  intro z hz x
  change sInf (range fun n => phi E φ ψ n (z • x)) = sInf (range fun n => phi E φ ψ n x)
  congr 2
  funext n
  exact (iterates_phase φ ψ hφ hψ n).1 z hz x

theorem iteration_phase_invariance : Spec.IterationPhaseInvariance := by
  intro E _ _ φ ψ hφ hψ
  exact ⟨iterates_phase φ ψ hφ hψ, theta_phase φ ψ hφ hψ⟩

lemma phase_of_norm (p : E → ℝ) (hp : P1.C01Norm.NormAxioms ℂ p) : PhaseInvariant p := by
  intro z hz x
  rw [hp.1.2.1, hz, one_mul]

lemma complex_norm_of_phase (p : E → ℝ) (hp : P1.C01Norm.NormAxioms ℝ p)
    (hphase : PhaseInvariant p) : P1.C01Norm.NormAxioms ℂ p := by
  refine ⟨⟨hp.1.1, ?_, hp.1.2.2⟩, hp.2⟩
  intro z x
  by_cases hz : z = 0
  · simp [hz, (hp.2 0).mpr rfl]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hu : ‖(‖z‖⁻¹ : ℂ) * z‖ = 1 := by
    simp [Complex.norm_real, hn]
  have heq : z • x = ‖z‖ • (((‖z‖⁻¹ : ℂ) * z) • x) := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
    congr 1
    simp [hn]
  rw [heq, hp.1.2.1, Real.norm_eq_abs, abs_norm, hphase _ hu]

theorem limit_complex_norm : Spec.LimitComplexNorm := by
  intro E _ _ φ ψ p hφ hψ hp heq
  apply complex_norm_of_phase p hp
  intro z hz x
  have ht := theta_phase φ ψ hφ hψ z hz x
  change ∀ x, p x ^ 2 / 2 = theta E φ ψ x at heq
  rw [← heq, ← heq] at ht
  nlinarith [hp.1.1 x, hp.1.1 (z • x)]

lemma dual_strict_to_real (p : E → ℝ) (hp : EquivalentComplexNorm p)
    (h : SphereStrictConvex (complexDualNorm p)) : SphereStrictConvex (dualNorm p) := by
  intro u v hu hv huv
  let e := realDualEquiv (E := E)
  have hid (w : E →L[ℝ] ℝ) : complexDualNorm p (e.symm w) = dualNorm p w := by
    rw [dual_norm_identification E p hp]
    exact congrArg (dualNorm p) (e.apply_symm_apply w)
  have hh := h (e.symm u) (e.symm v) (by rw [hid]; exact hu)
    (by rw [hid]; exact hv) (fun he => huv (e.symm.injective he))
  have hm : (1 / 2 : ℝ) • (e.symm u + e.symm v) = e.symm ((1 / 2 : ℝ) • (u + v)) := by
    simp
  rw [hm, hid] at hh
  exact hh

lemma dual_strict_to_complex (p : E → ℝ) (hp : EquivalentComplexNorm p)
    (h : SphereStrictConvex (dualNorm p)) : SphereStrictConvex (complexDualNorm p) := by
  intro f g hf hg hfg
  let e := realDualEquiv (E := E)
  have hid (w : E →L[ℂ] ℂ) : dualNorm p (e w) = complexDualNorm p w :=
    (dual_norm_identification E p hp w).symm
  have hh := h (e f) (e g) (by rw [hid]; exact hf) (by rw [hid]; exact hg)
    (fun he => hfg (e.injective he))
  have hm : (1 / 2 : ℝ) • (e f + e g) = e ((1 / 2 : ℝ) • (f + g)) := by simp
  rw [hm, hid] at hh
  exact hh

/-- Use the real construction with its actual quadratic-limit identity.
This identity is what makes the output retain the complex phase symmetry. -/
lemma combine_ordered_complex (p r : E → ℝ)
    (hp : EquivalentComplexNorm p) (hr : EquivalentComplexNorm r)
    (horder : ∀ x, r x ≤ p x)
    (C : ℝ) (hC : 0 ≤ C)
    (hcomp : ∀ x, p x ^ 2 / 2 ≤ (1 + C) * (r x ^ 2 / 2))
    (hsp : SphereStrictConvex p)
    (hsr : StrictConvexOn ℝ univ (fun f => dualNorm r f ^ 2 / 2)) :
    ∃ s : E → ℝ, EquivalentComplexNorm s ∧ SphereStrictConvex s ∧
      SphereStrictConvex (complexDualNorm s) := by
  let φ : E → ℝ := fun x => p x ^ 2 / 2
  let ψ : E → ℝ := fun x => r x ^ 2 / 2
  have hpR := real_norm p hp
  have hrR := real_norm r hr
  have h : InitialData E φ ψ := by
    refine ⟨(half_square_properties p hpR.1).2.1, (half_square_properties r hrR.1).2.1,
      (half_square_properties r hrR.1).1, ?_, ?_, ?_⟩
    · intro x
      change r x ^ 2 / 2 ≤ p x ^ 2 / 2
      nlinarith [horder x, hr.1.1.1 x, hp.1.1.1 x]
    · change p 0 ^ 2 / 2 = 0
      rw [(hp.1.2 0).mpr rfl]
      norm_num
    · change r 0 ^ 2 / 2 = 0
      rw [(hr.1.2 0).mpr rfl]
      norm_num
  obtain ⟨s, hs, heq⟩ := limit_norm p r hpR hrR h
  have hφ : PhaseInvariant φ := by
    intro z hz x
    dsimp [φ]
    rw [phase_of_norm p hp.1 z hz x]
  have hψ : PhaseInvariant ψ := by
    intro z hz x
    dsimp [ψ]
    rw [phase_of_norm r hr.1 z hz x]
  have hsC : EquivalentComplexNorm s :=
    ⟨limit_complex_norm E φ ψ s hφ hψ hs.1 heq, hs.2⟩
  have hEq : (fun x => s x ^ 2 / 2) = theta E φ ψ := funext heq
  have hφh := (half_square_properties p hpR.1).2.2
  have hψh := (half_square_properties r hrR.1).2.2
  have hprimal := StrictnessPersistence.strictness_persistence E φ ψ h hφh hψh C hC hcomp
    (Or.inl (strict_half_square p hpR.1 hsp))
  have hdual := SimultaneousRenorming.dual_strictness φ ψ h hφh hψh C hC hcomp
    (half_square_conjugate_finite r hrR) (by
      change StrictConvexOn ℝ univ (realConjugate (fun x => r x ^ 2 / 2))
      rw [realConjugate_half_square r hrR]
      exact hsr)
  refine ⟨s, hsC, ?_, dual_strict_to_complex s hsC ?_⟩
  · apply sphereStrict_of_halfSquare s hs.1
    rw [hEq]
    exact hprimal
  · apply sphereStrict_of_halfSquare (dualNorm s) (dualNorm_normAxioms s hs)
    rw [← hEq, realConjugate_half_square s hs] at hdual
    exact hdual

/-- Any two equivalent norms have a uniform positive comparison constant. -/
lemma norm_comparison (p q : E → ℝ) (hp : EquivalentNorm p) (hq : EquivalentNorm q) :
    ∃ A : ℝ, 0 < A ∧ ∀ x, p x ≤ A * q x := by
  obtain ⟨_, b, _, hb, hpb⟩ := hp.2
  obtain ⟨a, _, ha, _, hqa⟩ := hq.2
  refine ⟨b / a, div_pos hb ha, ?_⟩
  intro x
  have hx : ‖x‖ ≤ q x / a :=
    (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using (hqa x).1)
  calc
    p x ≤ b * ‖x‖ := (hpb x).2
    _ ≤ b * (q x / a) := mul_le_mul_of_nonneg_left hx hb.le
    _ = (b / a) * q x := by ring

theorem simultaneous_complex_renorming : Spec.SimultaneousComplexRenorming := by
  intro E _ _ p₁ p₂ hp₁ hp₂ hs₁ hs₂
  obtain ⟨A, hA, hdom⟩ := norm_comparison p₂ p₁ (real_norm p₂ hp₂) (real_norm p₁ hp₁)
  let r : E → ℝ := fun x => A⁻¹ * p₂ x
  have hrR : EquivalentNorm r := scale_equivalentNorm p₂ (real_norm p₂ hp₂) A⁻¹ (inv_pos.mpr hA)
  have hr : EquivalentComplexNorm r := by
    refine ⟨complex_norm_of_phase r hrR.1 ?_, hrR.2⟩
    intro z hz x
    change A⁻¹ * p₂ (z • x) = A⁻¹ * p₂ x
    rw [phase_of_norm p₂ hp₂.1 z hz x]
  have horder (x : E) : r x ≤ p₁ x := by
    have hh := mul_le_mul_of_nonneg_left (hdom x) (inv_nonneg.mpr hA.le)
    simpa only [r, ← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul] using hh
  obtain ⟨B, hB, hratio⟩ := norm_comparison p₁ r (real_norm p₁ hp₁) hrR
  have hcomp (x : E) : p₁ x ^ 2 / 2 ≤ (1 + B ^ 2) * (r x ^ 2 / 2) := by
    have hsq : p₁ x ^ 2 ≤ (B * r x) ^ 2 := by
      nlinarith [hratio x, hp₁.1.1.1 x, hr.1.1.1 x]
    nlinarith [sq_nonneg (r x)]
  apply combine_ordered_complex p₁ r hp₁ hr horder (B ^ 2) (sq_nonneg B) hcomp hs₁
  have hs₂R := strict_half_square (dualNorm p₂) (dualNorm_normAxioms p₂ (real_norm p₂ hp₂))
    (dual_strict_to_real p₂ hp₂ hs₂)
  have hscaled := strictConvex_positive_multiple _ hs₂R (A ^ 2) (sq_pos_of_pos hA)
  convert hscaled using 1
  ext f
  dsimp [r]
  rw [dualNorm_scale p₂ (real_norm p₂ hp₂) A⁻¹ (inv_pos.mpr hA)]
  field_simp

end ExpandedFA.Asplund.ComplexRenorming
