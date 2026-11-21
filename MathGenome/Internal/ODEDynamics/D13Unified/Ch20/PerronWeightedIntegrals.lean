import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.PerronWeightedIntegrals
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Weighted half-line Green estimates in a real Banach space. Only the two
operator decay bounds are used; no projection identities are needed.
The stable majorant is enlarged from [0,t] to (-∞,t], while the unstable
majorant is integrated on [t,∞). Continuity follows from exponential
factorization and an ordinary continuous primitive, after extending g
constantly to negative times. No condition on the supplied g at negative
times enters any conclusion.
-/

noncomputable section
open MeasureTheory Set
namespace D13Unified.Ch20.PerronWeightedIntegrals
open Specs.D13Unified.Ch20.PerronWeightedIntegrals
universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma evolution_continuous (A : E →L[ℝ] E) : Continuous (evolution A) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have h : Continuous (fun s : ℝ => s • A) := continuous_id.smul continuous_const
  change ContinuousAt (NormedSpace.exp ∘ (fun s : ℝ => s • A)) t
  exact ContinuousAt.comp (g := NormedSpace.exp) (f := fun s : ℝ => s • A)
    (NormedSpace.exp_analytic (𝕂 := ℝ) (t • A)).continuousAt h.continuousAt

lemma kernel_continuousOn (A P : E →L[ℝ] E) {g : ℝ → E}
    (hg : ContinuousOn g (Ici 0)) (t : ℝ) :
    ContinuousOn (kernel A P g t) (Ici 0) := by
  exact ((evolution_continuous A).comp (continuous_const.sub continuous_id)).continuousOn.clm_apply
    (P.continuous.comp_continuousOn hg)

lemma weighted_unweighted {β M : ℝ} {g : ℝ → E} (hg : WeightedBound β M g)
    {s : ℝ} (hs : 0 ≤ s) : ‖g s‖ ≤ M * Real.exp (-β * s) := by
  have h := hg.2.2 s hs
  rw [mul_comm] at h
  have h := (le_div_iff₀ (Real.exp_pos (β * s))).mpr h
  simpa [Real.exp_neg, div_eq_mul_inv, neg_mul] using h

lemma stable_kernel_bound (A P : E →L[ℝ] E) {K α β M : ℝ}
    (hK : 0 ≤ K) (hd : StableDecay A P K α) {g : ℝ → E}
    (hg : WeightedBound β M g) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ‖kernel A P g t s‖ ≤ (K * M * Real.exp (-α * t)) * Real.exp ((α - β) * s) := by
  have hd' := hd (t - s) (sub_nonneg.mpr hst)
  calc
    ‖kernel A P g t s‖ ≤ ‖(evolution A (t-s)).comp P‖ * ‖g s‖ :=
      ((evolution A (t-s)).comp P).le_opNorm (g s)
    _ ≤ (K * Real.exp (-α * (t-s))) * (M * Real.exp (-β * s)) :=
      mul_le_mul hd' (weighted_unweighted hg hs) (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_mul_mul_comm, ← Real.exp_add];
                rw [show -α * (t-s) + -β * s = -α*t + (α-β)*s by ring, Real.exp_add]; ring

lemma unstable_kernel_bound (A P : E →L[ℝ] E) {K α β M : ℝ}
    (hK : 0 ≤ K) (hd : UnstableDecay A P K α) {g : ℝ → E}
    (hg : WeightedBound β M g) {t s : ℝ} (ht : 0 ≤ t) (hst : t ≤ s) :
    ‖kernel A P g t s‖ ≤ (K * M * Real.exp (α * t)) * Real.exp ((-(α + β)) * s) := by
  have hd' := hd (s - t) (sub_nonneg.mpr hst)
  rw [show -(s-t) = t-s by ring] at hd'
  calc
    ‖kernel A P g t s‖ ≤ ‖(evolution A (t-s)).comp P‖ * ‖g s‖ :=
      ((evolution A (t-s)).comp P).le_opNorm (g s)
    _ ≤ (K * Real.exp (-α * (s-t))) * (M * Real.exp (-β * s)) :=
      mul_le_mul hd' (weighted_unweighted hg (ht.trans hst)) (norm_nonneg _) (by positivity)
    _ = _ := by rw [mul_mul_mul_comm, ← Real.exp_add];
                rw [show -α * (s-t) + -β * s = α*t + (-(α+β))*s by ring, Real.exp_add]; ring

theorem stable_estimate : stableEstimateType := by
  intro E _ _ _ A P K α β M hK hβ hβα hd g hg t ht
  have hrate : 0 < α - β := sub_pos.mpr hβα
  have hC : 0 ≤ K * M * Real.exp (-α*t) := by have := hg.2.1; positivity
  have hcont := (kernel_continuousOn A P hg.1 t).mono
    (show Icc 0 t ⊆ Ici 0 from fun s hs => hs.1)
  have hi : IntegrableOn (kernel A P g t) (Icc 0 t) := hcont.integrableOn_Icc
  refine ⟨hi, ?_⟩
  have hmajor : IntegrableOn (fun s => (K*M*Real.exp (-α*t))*Real.exp ((α-β)*s)) (Iic t) :=
    (integrableOn_exp_mul_Iic hrate t).const_mul _
  have hbound : ‖stableIntegral A P g t‖ ≤
      (K*M*Real.exp (-α*t)) * (Real.exp ((α-β)*t) / (α-β)) := by
    calc
      ‖stableIntegral A P g t‖ ≤
          ∫ s in Icc 0 t, (K*M*Real.exp (-α*t))*Real.exp ((α-β)*s) := by
        apply norm_integral_le_of_norm_le
          (hmajor.mono_set (fun _ hs => hs.2))
        exact (ae_restrict_iff' measurableSet_Icc).mpr
          (Filter.Eventually.of_forall (fun s hs => stable_kernel_bound A P (by linarith) hd hg hs.1 hs.2))
      _ ≤ ∫ s in Iic t, (K*M*Real.exp (-α*t))*Real.exp ((α-β)*s) := by
        apply setIntegral_mono_set hmajor
        · exact Filter.Eventually.of_forall (fun s => mul_nonneg hC (Real.exp_pos _).le)
        · exact Filter.Eventually.of_forall (fun s hs => hs.2)
      _ = _ := by rw [integral_const_mul, integral_exp_mul_Iic hrate]
  calc
    Real.exp (β*t)*‖stableIntegral A P g t‖ ≤
        Real.exp (β*t)*((K*M*Real.exp (-α*t))*(Real.exp ((α-β)*t)/(α-β))) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = (K*M/(α-β))*(Real.exp (β*t)*Real.exp (-α*t)*Real.exp ((α-β)*t)) := by ring
    _ = K*M/(α-β) := by
      rw [← Real.exp_add, ← Real.exp_add, show β*t + -α*t + (α-β)*t = 0 by ring]
      simp

theorem unstable_estimate : unstableEstimateType := by
  intro E _ _ _ A P K α β M hK hβ hβα hd g hg t ht
  have hrate : -(α+β) < 0 := by linarith
  have hC : 0 ≤ K*M*Real.exp (α*t) := by have := hg.2.1; positivity
  have hmajor : IntegrableOn (fun s => (K*M*Real.exp (α*t))*Real.exp ((-(α+β))*s)) (Ici t) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi).mpr (integrableOn_exp_mul_Ioi hrate t)).const_mul _
  have hbound : ∀ᵐ s ∂volume.restrict (Ici t), ‖kernel A P g t s‖ ≤
      (K*M*Real.exp (α*t))*Real.exp ((-(α+β))*s) :=
    (ae_restrict_iff' measurableSet_Ici).mpr
      (Filter.Eventually.of_forall (fun s hs => unstable_kernel_bound A P (by linarith) hd hg ht hs))
  have hmeas : AEStronglyMeasurable (kernel A P g t) (volume.restrict (Ici t)) := ((kernel_continuousOn A P hg.1 t).mono
    (show Ici t ⊆ Ici 0 from fun s hs => ht.trans hs)).aestronglyMeasurable measurableSet_Ici
  have hi : IntegrableOn (kernel A P g t) (Ici t) := hmajor.mono' hmeas hbound
  refine ⟨hi, ?_⟩
  have hn : ‖unstableIntegral A P g t‖ ≤
      (K*M*Real.exp (α*t)) * (Real.exp ((-(α+β))*t) / (α+β)) := by
    calc
      ‖unstableIntegral A P g t‖ ≤
          ∫ s in Ici t, (K*M*Real.exp (α*t))*Real.exp ((-(α+β))*s) :=
        norm_integral_le_of_norm_le hmajor hbound
      _ = _ := by
        rw [integral_const_mul, integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi hrate]
        simp only [neg_div_neg_eq]
  calc
    Real.exp (β*t)*‖unstableIntegral A P g t‖ ≤
        Real.exp (β*t)*((K*M*Real.exp (α*t))*(Real.exp ((-(α+β))*t)/(α+β))) :=
      mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
    _ = (K*M/(α+β))*(Real.exp (β*t)*Real.exp (α*t)*Real.exp ((-(α+β))*t)) := by ring
    _ = K*M/(α+β) := by
      rw [← Real.exp_add, ← Real.exp_add, show β*t + α*t + (-(α+β))*t = 0 by ring]
      simp

lemma evolution_sub (A : E →L[ℝ] E) (t s : ℝ) :
    evolution A (t-s) = (evolution A t).comp (evolution A (-s)) := by
  change NormedSpace.exp ((t-s) • A) =
    NormedSpace.exp (t • A) * NormedSpace.exp ((-s) • A)
  rw [sub_eq_add_neg, add_smul]
  apply NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
    (((Commute.refl A).smul_left t).smul_right (-s)) <;>
    simp [NormedSpace.expSeries_radius_eq_top]

private def extended (g : ℝ → E) (s : ℝ) : E := g (max s 0)

private lemma extended_eq (g : ℝ → E) {s : ℝ} (hs : 0 ≤ s) : extended g s = g s := by
  simp [extended, max_eq_left hs]

private lemma extended_continuous {g : ℝ → E} (hg : ContinuousOn g (Ici 0)) :
    Continuous (extended g) :=
  hg.comp_continuous (continuous_id.max continuous_const) (fun s => (show 0 ≤ max s 0 from le_max_right s 0))

private def forcing (A P : E →L[ℝ] E) (g : ℝ → E) (s : ℝ) : E :=
  evolution A (-s) (P (extended g s))

private lemma forcing_continuous (A P : E →L[ℝ] E) {g : ℝ → E}
    (hg : ContinuousOn g (Ici 0)) : Continuous (forcing A P g) := by
  exact ((evolution_continuous A).comp continuous_neg).clm_apply
    (P.continuous.comp (extended_continuous hg))

private lemma kernel_factor (A P : E →L[ℝ] E) (g : ℝ → E) (t : ℝ)
    {s : ℝ} (hs : 0 ≤ s) : kernel A P g t s = evolution A t (forcing A P g s) := by
  rw [kernel, evolution_sub]
  simp [forcing, extended_eq g hs]

private lemma stable_factor (A P : E →L[ℝ] E) {g : ℝ → E}
    (hg : ContinuousOn g (Ici 0)) {t : ℝ} (ht : 0 ≤ t) :
    stableIntegral A P g t =
      evolution A t (∫ s in 0..t, forcing A P g s) := by
  calc
    stableIntegral A P g t = ∫ s in Icc 0 t, evolution A t (forcing A P g s) :=
      setIntegral_congr_fun measurableSet_Icc (fun s hs => kernel_factor A P g t hs.1)
    _ = evolution A t (∫ s in Icc 0 t, forcing A P g s) :=
      (evolution A t).integral_comp_comm (forcing_continuous A P hg).continuousOn.integrableOn_Icc
    _ = _ := by rw [intervalIntegral.integral_of_le ht, integral_Icc_eq_integral_Ioc]

lemma stable_continuous (A P : E →L[ℝ] E) {g : ℝ → E}
    (hg : ContinuousOn g (Ici 0)) : ContinuousOn (stableIntegral A P g) (Ici 0) := by
  have hprim : Continuous (fun t => ∫ s in 0..t, forcing A P g s) :=
    intervalIntegral.continuous_primitive
      (fun _ _ => (forcing_continuous A P hg).intervalIntegrable _ _) 0
  exact ((evolution_continuous A).clm_apply hprim).continuousOn.congr
    (fun t ht => stable_factor A P hg ht)

lemma unstable_continuous_of_integrable (A P : E →L[ℝ] E) {g : ℝ → E}
    (hg : ContinuousOn g (Ici 0)) (hi : IntegrableOn (kernel A P g 0) (Ici 0)) :
    ContinuousOn (unstableIntegral A P g) (Ici 0) := by
  have hF : IntegrableOn (forcing A P g) (Ici 0) := hi.congr_fun (by
    intro s hs
    simp [kernel, forcing, extended_eq g hs]) measurableSet_Ici
  have hformula (t : ℝ) (ht : 0 ≤ t) : unstableIntegral A P g t =
      evolution A t ((∫ s in Ici 0, forcing A P g s) - ∫ s in 0..t, forcing A P g s) := by
    have htail := hF.mono_set (show Ici t ⊆ Ici 0 from fun _ hs => ht.trans hs)
    have hsplit := intervalIntegral.integral_Ici_sub_Ici' hF htail
    calc
      unstableIntegral A P g t = ∫ s in Ici t, evolution A t (forcing A P g s) :=
        setIntegral_congr_fun measurableSet_Ici (fun s hs => kernel_factor A P g t (ht.trans hs))
      _ = evolution A t (∫ s in Ici t, forcing A P g s) :=
        (evolution A t).integral_comp_comm htail
      _ = _ := by congr 1; exact eq_sub_iff_add_eq.mpr (by rw [← hsplit]; abel)
  have hprim : Continuous (fun t => ∫ s in 0..t, forcing A P g s) :=
    intervalIntegral.continuous_primitive
      (fun _ _ => (forcing_continuous A P hg).intervalIntegrable _ _) 0
  have hc : Continuous (fun t : ℝ => (∫ s in Ici 0, forcing A P g s) -
      ∫ s in 0..t, forcing A P g s) := continuous_const.sub hprim
  exact ((evolution_continuous A).clm_apply hc).continuousOn.congr hformula

theorem integral_continuity : continuityType := by
  intro E _ _ _ A Ps Pu K α β M hK hβ hβα hs hu g hg
  exact ⟨stable_continuous A Ps hg.1, unstable_continuous_of_integrable A Pu hg.1
    (unstable_estimate A Pu K α β M hK hβ hβα hu g hg 0 le_rfl).1⟩

theorem stable_interval_eq : stableIntervalType := by
  intro E _ _ _ A P g t ht
  rw [stableIntegral, intervalIntegral.integral_of_le ht, integral_Icc_eq_integral_Ioc]

lemma kernel_linear (A P : E →L[ℝ] E) (g h : ℝ → E) (c d t s : ℝ) :
    kernel A P (fun s => c • g s + d • h s) t s =
      c • kernel A P g t s + d • kernel A P h t s := by
  simp [kernel]

theorem integral_linearity : linearityType := by
  intro E _ _ _ A Ps Pu K α β hK hβ hβα hs hu g h M N hg hh c d t ht
  have hsg := (stable_estimate A Ps K α β M hK hβ hβα hs g hg t ht).1
  have hsh := (stable_estimate A Ps K α β N hK hβ hβα hs h hh t ht).1
  have hug := (unstable_estimate A Pu K α β M hK hβ hβα hu g hg t ht).1
  have huh := (unstable_estimate A Pu K α β N hK hβ hβα hu h hh t ht).1
  dsimp only [greenIntegral, stableIntegral, unstableIntegral]
  simp_rw [kernel_linear]
  rw [integral_add (f := fun s => c • kernel A Ps g t s)
      (g := fun s => d • kernel A Ps h t s) (hsg.smul c) (hsh.smul d),
    integral_add (f := fun s => c • kernel A Pu g t s)
      (g := fun s => d • kernel A Pu h t s) (hug.smul c) (huh.smul d)]
  simp only [integral_smul, smul_sub]
  abel

theorem green_estimate : greenEstimateType := by
  intro E _ _ _ A Ps Pu K α β M hK hβ hβα hs hu g hg t ht
  have hsg := (stable_estimate A Ps K α β M hK hβ hβα hs g hg t ht).2
  have hug := (unstable_estimate A Pu K α β M hK hβ hβα hu g hg t ht).2
  calc
    Real.exp (β*t)*‖greenIntegral A Ps Pu g t‖ ≤
        Real.exp (β*t)*(‖stableIntegral A Ps g t‖ + ‖unstableIntegral A Pu g t‖) :=
      mul_le_mul_of_nonneg_left (norm_sub_le _ _) (Real.exp_pos _).le
    _ = Real.exp (β*t)*‖stableIntegral A Ps g t‖ +
        Real.exp (β*t)*‖unstableIntegral A Pu g t‖ := mul_add _ _ _
    _ ≤ K*M/(α-β) + K*M/(α+β) := add_le_add hsg hug
    _ = _ := by simp only [div_eq_mul_inv]; ring

end D13Unified.Ch20.PerronWeightedIntegrals




