import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.PerronIntegralODE
import Mathlib.Tactic.Abel

noncomputable section
open Set MeasureTheory Filter
open scoped Topology

namespace D13Unified.Ch20.PerronIntegralODE
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma evolution_add (A : E →L[ℝ] E) (s t : ℝ) :
    evolution A (s+t) = evolution A s * evolution A t := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
  simpa only [evolution, add_smul] using
    NormedSpace.exp_add_of_commute (((Commute.refl A).smul_left s).smul_right t)

omit [CompleteSpace E] in
@[simp] lemma evolution_zero (A : E →L[ℝ] E) : evolution A 0 = 1 := by
  simp [evolution]

lemma evolution_cancel (A : E →L[ℝ] E) (t : ℝ) (x : E) :
    evolution A t (evolution A (-t) x) = x := by
  change (evolution A t * evolution A (-t)) x = x
  rw [← evolution_add, add_neg_cancel, evolution_zero]
  rfl

lemma evolution_continuous (A : E →L[ℝ] E) : Continuous (evolution A) := by
  exact continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_exp_smul_const' A t).continuousAt

lemma forcing_continuousOn (A P : E →L[ℝ] E) {g : ℝ → E}
    (hg : ContinuousOn g (Ici 0)) :
    ContinuousOn (fun s => evolution A (-s) (P (g s))) (Ici 0) := by
  exact ((evolution_continuous A).comp continuous_neg).continuousOn.clm_apply
    (P.continuous.comp_continuousOn hg)

lemma primitive_hasDerivWithinAt {f : ℝ → E} (hf : ContinuousOn f (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, f s) (f t) (Ici 0) t := by
  have hJ : OrdConnected (Ici (0 : ℝ)) := ordConnected_Ici
  have : (𝓝[Ici 0] t).IsMeasurablyGenerated :=
    measurableSet_Ici.nhdsWithin_isMeasurablyGenerated t
  have : TendstoIxxClass Icc (𝓝[Ici 0] t) (𝓝[Ici 0] t) := tendstoIxxClass_inf
  have : TendstoIxxClass Ioc (𝓝[Ici 0] t) (𝓝[Ici 0] t) :=
    tendstoIxxClass_of_subset (fun _ _ => Ioc_subset_Icc_self)
  have : intervalIntegral.FTCFilter t (𝓝[Ici 0] t) (𝓝[Ici 0] t) :=
    { pure_le := pure_le_nhdsWithin ht, le_nhds := nhdsWithin_le_nhds }
  exact intervalIntegral.integral_hasDerivWithinAt_right
    ((hf.mono (hJ.uIcc_subset (by simp) ht)).intervalIntegrable)
    (hf.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ici t) (hf t ht)

lemma kernel_factor (A P : E →L[ℝ] E) (g : ℝ → E) (t s : ℝ) :
    evolution A (t-s) (P (g s)) =
      evolution A t (evolution A (-s) (P (g s))) := by
  rw [sub_eq_add_neg, evolution_add]
  rfl

lemma finite_integrable (A P : E →L[ℝ] E) {g : ℝ → E}
    (hg : ContinuousOn g (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => evolution A (t-s) (P (g s))) volume 0 t := by
  have hk : ContinuousOn (fun s => evolution A (t-s) (P (g s))) (Ici 0) :=
    ((evolution_continuous A).comp (continuous_const.sub continuous_id)).continuousOn.clm_apply
      (P.continuous.comp_continuousOn hg)
  exact (hk.mono (ordConnected_Ici.uIcc_subset (by simp) ht)).intervalIntegrable

lemma transformed_finite_integrable (A P : E →L[ℝ] E) {g : ℝ → E}
    (hg : ContinuousOn g (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun s => evolution A (-s) (P (g s))) volume 0 t := by
  exact ((forcing_continuousOn A P hg).mono (ordConnected_Ici.uIcc_subset (by simp) ht)).intervalIntegrable

lemma stableIntegral_factor (A P : E →L[ℝ] E) {g : ℝ → E}
    (hg : ContinuousOn g (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    stableIntegral A P g t =
      evolution A t (∫ s in (0 : ℝ)..t, evolution A (-s) (P (g s))) := by
  unfold stableIntegral
  simp_rw [kernel_factor]
  exact (evolution A t).intervalIntegral_comp_comm (transformed_finite_integrable A P hg ht)

lemma tail_integrable (A P : E →L[ℝ] E) {g : ℝ → E}
    (hu : IntegrableOn (fun s => evolution A (-s) (P (g s))) (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun s => evolution A (t-s) (P (g s))) (Ici t) := by
  simp_rw [kernel_factor]
  exact (evolution A t).integrable_comp (hu.mono_set (Ici_subset_Ici.mpr ht))

lemma unstableIntegral_factor (A P : E →L[ℝ] E) {g : ℝ → E}
    (hu : IntegrableOn (fun s => evolution A (-s) (P (g s))) (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    unstableIntegral A P g t = evolution A t
      ((∫ s in Ici (0 : ℝ), evolution A (-s) (P (g s))) -
        ∫ s in (0 : ℝ)..t, evolution A (-s) (P (g s))) := by
  unfold unstableIntegral
  simp_rw [kernel_factor]
  rw [(evolution A t).integral_comp_comm (hu.mono_set (Ici_subset_Ici.mpr ht))]
  congr 1
  rw [← intervalIntegral.integral_Ici_sub_Ici' hu (hu.mono_set (Ici_subset_Ici.mpr ht))]
  abel

lemma stableIntegral_hasDerivWithinAt (A P : E →L[ℝ] E) {g : ℝ → E}
    (hg : ContinuousOn g (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (stableIntegral A P g)
      (A (stableIntegral A P g t) + P (g t)) (Ici 0) t := by
  have hp := primitive_hasDerivWithinAt (forcing_continuousOn A P hg) ht
  have he : HasDerivWithinAt (evolution A) (A * evolution A t) (Ici 0) t :=
    (hasDerivAt_exp_smul_const' A t).hasDerivWithinAt
  have hd := he.clm_apply hp
  have hd' : HasDerivWithinAt
      (fun u => evolution A u (∫ s in (0 : ℝ)..u, evolution A (-s) (P (g s))))
      (A (stableIntegral A P g t) + P (g t)) (Ici 0) t := by
    rw [stableIntegral_factor A P hg ht]
    simpa only [mul_apply_eq_comp, evolution_cancel] using hd
  exact hd'.congr_of_mem (fun u hu => stableIntegral_factor A P hg hu) ht

lemma unstableIntegral_hasDerivWithinAt (A P : E →L[ℝ] E) {g : ℝ → E}
    (hg : ContinuousOn g (Ici 0))
    (hu : IntegrableOn (fun s => evolution A (-s) (P (g s))) (Ici 0))
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (unstableIntegral A P g)
      (A (unstableIntegral A P g t) - P (g t)) (Ici 0) t := by
  have hp := (primitive_hasDerivWithinAt (forcing_continuousOn A P hg) ht).const_sub
    (∫ s in Ici (0 : ℝ), evolution A (-s) (P (g s)))
  have he : HasDerivWithinAt (evolution A) (A * evolution A t) (Ici 0) t :=
    (hasDerivAt_exp_smul_const' A t).hasDerivWithinAt
  have hd := he.clm_apply hp
  have hd' : HasDerivWithinAt
      (fun u => evolution A u ((∫ s in Ici (0 : ℝ), evolution A (-s) (P (g s))) -
        ∫ s in (0 : ℝ)..u, evolution A (-s) (P (g s))))
      (A (unstableIntegral A P g t) - P (g t)) (Ici 0) t := by
    rw [unstableIntegral_factor A P hu ht]
    simpa only [mul_apply_eq_comp, map_neg, evolution_cancel, sub_eq_add_neg] using hd
  exact hd'.congr_of_mem (fun u hut => unstableIntegral_factor A P hu hut) ht

/-- The derivative identity needs only the complementary sum; the commutation
and cross-projection laws enter the initial stable projection below. -/
lemma perronPath_hasDerivWithinAt (A Ps Pu : E →L[ℝ] E)
    (hSum : Ps + Pu = 1) {g : ℝ → E} (hg : ContinuousOn g (Ici 0))
    (hu : IntegrableOn (fun s => evolution A (-s) (Pu (g s))) (Ici 0))
    (ξ : E) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (perronPath A Ps Pu g ξ)
      (A (perronPath A Ps Pu g ξ t) + g t) (Ici 0) t := by
  have he : HasDerivWithinAt (evolution A) (A * evolution A t) (Ici 0) t :=
    (hasDerivAt_exp_smul_const' A t).hasDerivWithinAt
  have hlin : HasDerivWithinAt (fun u => evolution A u ξ)
      (A (evolution A t ξ)) (Ici 0) t := by
    simpa only [mul_apply_eq_comp, map_zero, add_zero] using
      he.clm_apply (hasDerivWithinAt_const t (Ici 0) ξ)
  have hd := (hlin.add (stableIntegral_hasDerivWithinAt A Ps hg ht)).sub
    (unstableIntegral_hasDerivWithinAt A Pu hg hu ht)
  have hSumg : Ps (g t) + Pu (g t) = g t := by
    simpa only [add_apply, one_apply_eq_self] using
      congrArg (fun P : E →L[ℝ] E => P (g t)) hSum
  have heq : A (evolution A t ξ) + (A (stableIntegral A Ps g t) + Ps (g t)) -
        (A (unstableIntegral A Pu g t) - Pu (g t)) =
      A (perronPath A Ps Pu g ξ t) + g t := by
    conv_rhs => rw [perronPath, map_sub, map_add, ← hSumg]
    abel
  rw [heq] at hd
  exact hd

omit [CompleteSpace E] in
lemma commute_evolution (A P : E →L[ℝ] E) (hP : Commute P A) (t : ℝ) :
    Commute P (evolution A t) := by
  let : NormedAlgebra ℚ (E →L[ℝ] E) := .restrictScalars ℚ ℝ _
  exact (hP.smul_right t).exp_right

lemma perronPath_initial_projection (A Ps Pu : E →L[ℝ] E)
    (hCross : Ps * Pu = 0) (hComm : Commute Ps A) {g : ℝ → E}
    (hu : IntegrableOn (fun s => evolution A (-s) (Pu (g s))) (Ici 0))
    (ξ : E) (hξ : Ps ξ = ξ) : Ps (perronPath A Ps Pu g ξ 0) = ξ := by
  have hz : Ps (unstableIntegral A Pu g 0) = 0 := by
    simp only [unstableIntegral, zero_sub]
    rw [← Ps.integral_comp_comm hu]
    have hpoint : ∀ s : ℝ, Ps (evolution A (-s) (Pu (g s))) = 0 := by
      intro s
      have hc := congrArg (fun P : E →L[ℝ] E => P (Pu (g s)))
        (commute_evolution A Ps hComm (-s)).eq
      change Ps (evolution A (-s) (Pu (g s))) =
        evolution A (-s) ((Ps * Pu) (g s)) at hc
      rw [hc, hCross]
      simp
    simp_rw [hpoint]
    simp
  simpa only [perronPath, stableIntegral, intervalIntegral.integral_same,
    evolution_zero, one_apply_eq_self, add_zero, map_sub, hz, sub_zero] using hξ

/-- The full linear-forcing bridge, including convergence and the right
endpoint derivative. No fixed point or ODE identity is an input. -/
theorem perron_integral_ode :
    Specs.D13Unified.Ch20.PerronIntegralODE.perronIntegralODEType := by
  intro E _ _ _ A Ps Pu hSum hCross hComm _ g hg hu ξ hξ
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (perronPath A Ps Pu g ξ)
      (A (perronPath A Ps Pu g ξ t) + g t) (Ici 0) t :=
    fun t ht => perronPath_hasDerivWithinAt A Ps Pu hSum hg hu ξ ht
  refine ⟨?_, ?_, hd, perronPath_initial_projection A Ps Pu hCross hComm hu ξ hξ⟩
  · intro t ht
    exact ⟨finite_integrable A Ps hg ht, tail_integrable A Pu hu ht⟩
  · intro t ht
    exact (hd t ht).continuousWithinAt

end D13Unified.Ch20.PerronIntegralODE
