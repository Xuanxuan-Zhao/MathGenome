import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.HyperbolicWeakEnergyExistence
import Mathlib.Tactic.Abel

/-!
Weak-energy uniqueness and strong state continuity for symmetric scalar-C¹
hyperbolic forms. The integrated V-valued test and a short-interval maximum
argument prove uniqueness with weak endpoint traces. Forward/backward
restarting then recovers strong continuity in the original V and H norms.
No strong wave-energy identity is assumed.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
universe u v

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyUniquenessSpec HyperbolicWeakEnergyExistence

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Scalarize first, so no common null set indexed by a nonseparable dual
is needed. Positive time gives full support on the entire closed interval. -/
theorem weaklyContinuousOn_eq_of_ae {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (hT : 0 < T) (x y : ℝ → E)
    (hx : WeaklyContinuousOn x (Set.Icc 0 T))
    (hy : WeaklyContinuousOn y (Set.Icc 0 T))
    (heq : x =ᵐ[timeMeasureValue T] y) :
    ∀ t ∈ Set.Icc 0 T, x t = y t := by
  intro t ht
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  have hz : ∀ r ∈ Set.Icc 0 T, L (x r) - L (y r) ∈ ({0} : Set ℝ) :=
    continuousOn_mem_closed_of_ae T hT _ ((hx L).sub (hy L)) _ isClosed_singleton
      (heq.mono fun r hr => by simp [hr])
  exact sub_eq_zero.mp (hz t ht)

theorem state_equality_of_ae : StateEqualityOfAE (V := V) (H := H) := by
  intro j T hT a u₀ v₀ f z w hu hv t ht
  exact ⟨weaklyContinuousOn_eq_of_ae T hT _ _ z.displacement_weak
    w.displacement_weak hu t ht,
    weaklyContinuousOn_eq_of_ae T hT _ _ z.velocity_weak w.velocity_weak hv t ht⟩

theorem zero_time_uniqueness : ZeroTimeUniqueness (V := V) (H := H) := by
  intro j a u₀ v₀ f z w
  constructor
  · intro t ht
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst t
    exact ⟨z.initial_displacement.trans w.initial_displacement.symm,
      z.initial_velocity.trans w.initial_velocity.symm⟩
  · simp only [timeMeasureValue, Set.Ioo_self, Measure.restrict_empty, ae_zero]
    exact Filter.eventually_bot

/-- The primitive supplied by the distributional fundamental theorem is
the given weak representative after scalarization. -/
theorem primitive_of_weaklyContinuousOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (T : ℝ) (hT : 0 < T) (x g : ℝ → E)
    (hx : Integrable x (timeMeasureValue T))
    (hg : Integrable g (timeMeasureValue T))
    (hd : derivativeValue T x g)
    (hweak : WeaklyContinuousOn x (Set.Icc 0 T)) :
    ContinuousOn x (Set.Icc 0 T) ∧
    ∀ s t : Set.Icc 0 T, x t - x s = ∫ r in s.val..t.val, g r := by
  obtain ⟨P, hPc, hPae, hPinc⟩ :=
    hasTimeDerivative_continuous_primitive T x g hx hg hd
  have hxeq : ∀ t ∈ Set.Icc 0 T, x t = P t :=
    weaklyContinuousOn_eq_of_ae T hT x P hweak
      (fun L => (L.continuous.comp hPc).continuousOn) hPae
  refine ⟨hPc.continuousOn.congr (fun t ht => hxeq t ht), ?_⟩
  intro s t
  rw [hxeq t t.property, hxeq s s.property]
  exact hPinc s t

/-- Applying a fixed bounded linear map preserves weak continuity. -/
theorem weaklyContinuousOn_map {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E →L[ℝ] F) (x : ℝ → E) (S : Set ℝ)
    (hx : WeaklyContinuousOn x S) :
    WeaklyContinuousOn (fun t => A (x t)) S := by
  intro L
  exact hx (L.comp A)

theorem primitive_representatives : PrimitiveRepresentatives (V := V) (H := H) := by
  intro j T hT a u₀ v₀ f z
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  obtain ⟨hu, hui⟩ := primitive_of_weaklyContinuousOn T hT
    (fun t => j.embedding (z.displacement t)) z.velocity
    (z.pivot_displacement_mem.integrable (by simp))
    (z.velocity_mem.integrable (by simp)) z.displacement_derivative
    (weaklyContinuousOn_map j.embedding _ _ z.displacement_weak)
  obtain ⟨hv, hvi⟩ := primitive_of_weaklyContinuousOn T hT
    (fun t => pivotValue j (z.velocity t)) z.acceleration
    (z.dual_velocity_mem.integrable (by norm_num))
    (z.acceleration_mem.integrable (by norm_num)) z.velocity_derivative
    (weaklyContinuousOn_map (pivotValue j) _ _ z.velocity_weak)
  exact ⟨hu, hv, hui, hvi⟩

/-- Once the displacement class is determined, the two vector weak
derivative graphs determine the velocity and acceleration classes. -/
theorem derivatives_eq_of_displacement_ae (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z w : WeakEnergySolution j T a u₀ v₀ f)
    (hu : z.displacement =ᵐ[timeMeasureValue T] w.displacement) :
    z.velocity =ᵐ[timeMeasureValue T] w.velocity ∧
    z.acceleration =ᵐ[timeMeasureValue T] w.acceleration := by
  have hd := (hasTimeDerivative_congr T
    (fun t => j.embedding (z.displacement t))
    (fun t => j.embedding (w.displacement t)) z.velocity z.velocity
    (hu.mono fun t ht => congrArg j.embedding ht) Filter.EventuallyEq.rfl).mp
      z.displacement_derivative
  have hv := hasTimeDerivative_unique T _ _ _ hd w.displacement_derivative
  have hdd := (hasTimeDerivative_congr T
    (fun t => pivotValue j (z.velocity t))
    (fun t => pivotValue j (w.velocity t)) z.acceleration z.acceleration
    (hv.mono fun t ht => congrArg (pivotValue j) ht) Filter.EventuallyEq.rfl).mp
      z.velocity_derivative
  exact ⟨hv, hasTimeDerivative_unique T _ _ _ hdd w.velocity_derivative⟩

theorem uniqueness_of_displacement_ae (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z w : WeakEnergySolution j T a u₀ v₀ f)
    (hu : z.displacement =ᵐ[timeMeasureValue T] w.displacement) :
    (∀ t ∈ Set.Icc 0 T,
      z.displacement t = w.displacement t ∧ z.velocity t = w.velocity t) ∧
    z.acceleration =ᵐ[timeMeasureValue T] w.acceleration := by
  obtain ⟨hv, hg⟩ := derivatives_eq_of_displacement_ae j T a u₀ v₀ f z w hu
  exact ⟨state_equality_of_ae j T hT a u₀ v₀ f z w hu hv, hg⟩

/-- The open-interval Bochner integral controls any subinterval including
its endpoints. No extension of the trajectory outside [0,T] is required. -/
theorem intervalIntegrable_of_timeIntegrable {E : Type*} [NormedAddCommGroup E]
    (T : ℝ) {g : ℝ → E} (hg : Integrable g (timeMeasureValue T))
    (s t : Set.Icc 0 T) : IntervalIntegrable g volume s.val t.val := by
  have hg' : IntegrableOn g (Set.Icc 0 T) := by
    change Integrable g (volume.restrict (Set.Icc 0 T))
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact hg
  exact (hg'.mono_set (Set.uIcc_subset_Icc s.property t.property)).intervalIntegrable

/-- Both primitive curves are absolutely continuous in precisely the
Banach spaces needed to pair the velocity with a V-valued test. -/
theorem weak_solution_pivot_ac (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) :
    AbsolutelyContinuousOnInterval (fun t => j.embedding (z.displacement t)) 0 T ∧
    AbsolutelyContinuousOnInterval (fun t => pivotValue j (z.velocity t)) 0 T := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  obtain ⟨_, _, hui, hvi⟩ := primitive_representatives j T hT a u₀ v₀ f z
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have h1 : T ∈ Set.Icc 0 T := ⟨hT.le, le_rfl⟩
  constructor
  · apply FiniteEnergy.primitive_increment_ac
      (intervalIntegrable_of_timeIntegrable T (z.velocity_mem.integrable (by simp))
        ⟨0, h0⟩ ⟨T, h1⟩)
    intro t ht
    exact hui ⟨0, h0⟩ ⟨t, by simpa [Set.uIcc_of_le hT.le] using ht⟩
  · apply FiniteEnergy.primitive_increment_ac
      (intervalIntegrable_of_timeIntegrable T
        (z.acceleration_mem.integrable (by norm_num)) ⟨0, h0⟩ ⟨T, h1⟩)
    intro t ht
    exact hvi ⟨0, h0⟩ ⟨t, by simpa [Set.uIcc_of_le hT.le] using ht⟩

/-- The a.e. L∞ bound extends to all values of the weak representatives.
The argument uses the accepted bounded-lifting theorem, not continuity of
the V norm in the weak topology. -/
theorem weak_solution_uniform_bounds (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) :
    ∃ R S : ℝ, 0 ≤ R ∧ 0 ≤ S ∧
      ∀ t ∈ Set.Icc 0 T, ‖z.displacement t‖ ≤ R ∧ ‖z.velocity t‖ ≤ S := by
  obtain ⟨R, hR⟩ := (eLpNormEssSup_lt_top_iff_isBoundedUnder (f := z.displacement)
    (μ := timeMeasureValue T)).mp
    (by simpa only [MemLp, eLpNorm_exponent_top z.displacement_mem.aestronglyMeasurable] using
      z.displacement_mem)
  obtain ⟨S, hS⟩ := (eLpNormEssSup_lt_top_iff_isBoundedUnder (f := z.velocity)
    (μ := timeMeasureValue T)).mp
    (by simpa only [MemLp, eLpNorm_exponent_top z.velocity_mem.aestronglyMeasurable] using
      z.velocity_mem)
  have hu : ∀ᵐ t ∂timeMeasureValue T, ‖z.displacement t‖ ≤ (R : ℝ) :=
    hR.mono fun t ht => ht
  have hv : ∀ᵐ t ∂timeMeasureValue T, ‖z.velocity t‖ ≤ (S : ℝ) :=
    hS.mono fun t ht => ht
  obtain ⟨x, y, hxae, hyae, hb, hxw, hyw, _⟩ := weak_representatives j T hT
    z.displacement z.velocity z.acceleration R S R.coe_nonneg S.coe_nonneg
    z.displacement_mem z.velocity_mem z.acceleration_mem hu hv
    z.displacement_derivative z.velocity_derivative
  have hx := weaklyContinuousOn_eq_of_ae T hT _ _ z.displacement_weak hxw hxae.symm
  have hy := weaklyContinuousOn_eq_of_ae T hT _ _ z.velocity_weak hyw hyae.symm
  refine ⟨R, S, R.coe_nonneg, S.coe_nonneg, ?_⟩
  intro t ht
  rw [hx t ht, hy t ht]
  exact hb t ht

/-- Bounded bilinear pairings preserve absolute continuity. This applies
to the dual pairing V′ × V even when the first curve is not V-valued. -/
theorem bilinear_absolutelyContinuousOnInterval {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {a b : ℝ} {x : ℝ → E} {y : ℝ → F}
    (hx : AbsolutelyContinuousOnInterval x a b)
    (hy : AbsolutelyContinuousOnInterval y a b) :
    AbsolutelyContinuousOnInterval (fun t => B (x t) (y t)) a b := by
  obtain ⟨R, hR⟩ := hx.exists_bound
  obtain ⟨S, hS⟩ := hy.exists_bound
  have hdist (s t : ℝ) (hs : s ∈ Set.uIcc a b) (ht : t ∈ Set.uIcc a b) :
      dist (B (x s) (y s)) (B (x t) (y t)) ≤
        (‖B‖ * R) * dist (y s) (y t) + (‖B‖ * S) * dist (x s) (x t) := by
    have heq : B (x s) (y s) - B (x t) (y t) =
        B (x s) (y s - y t) + B (x s - x t) (y t) := by
      simp only [map_sub, sub_apply]
      abel
    rw [dist_eq_norm, heq]
    calc
      _ ≤ ‖B (x s) (y s - y t)‖ + ‖B (x s - x t) (y t)‖ := norm_add_le _ _
      _ ≤ ‖B‖ * ‖x s‖ * ‖y s - y t‖ + ‖B‖ * ‖x s - x t‖ * ‖y t‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
      _ ≤ ‖B‖ * R * ‖y s - y t‖ + ‖B‖ * ‖x s - x t‖ * S := by
        gcongr
        · exact hR s hs
        · exact hS t ht
      _ = _ := by simp only [dist_eq_norm]; ring
  unfold AbsolutelyContinuousOnInterval at hx hy ⊢
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ =>
    Finset.sum_nonneg fun _ _ => dist_nonneg) ?_
    (by simpa using (hy.const_mul (‖B‖ * R)).add (hx.const_mul (‖B‖ * S)))
  rw [eventually_inf_principal]
  filter_upwards with q hq
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  exact hdist _ _ (hq.1 i hi).1 (hq.1 i hi).2

/-- The scalar fundamental theorem for a Banach dual pairing. Both curves
are AC in their actual Banach norms; neither is assumed differentiable at
every time. This is the integration-by-parts step for the integrated test. -/
theorem bilinear_integral_derivative {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : E →L[ℝ] F →L[ℝ] ℝ) {a b : ℝ} (hab : a ≤ b)
    {x dx : ℝ → E} {y dy : ℝ → F}
    (hx : AbsolutelyContinuousOnInterval x a b)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hdx : ∀ᵐ t ∂volume, t ∈ Set.Icc a b → HasDerivAt x (dx t) t)
    (hdy : ∀ᵐ t ∂volume, t ∈ Set.Icc a b → HasDerivAt y (dy t) t) :
    IntervalIntegrable (fun t => B (x t) (dy t) + B (dx t) (y t)) volume a b ∧
    (∫ t in a..b, B (x t) (dy t) + B (dx t) (y t)) =
      B (x b) (y b) - B (x a) (y a) := by
  have hp := bilinear_absolutelyContinuousOnInterval B hx hy
  have heq : deriv (fun t => B (x t) (y t)) =ᵐ[volume.restrict (Set.uIcc a b)]
      fun t => B (x t) (dy t) + B (dx t) (y t) := by
    filter_upwards [ae_restrict_of_ae hdx, ae_restrict_of_ae hdy,
      ae_restrict_mem measurableSet_uIcc] with t ht₁ ht₂ ht
    have ht' : t ∈ Set.Icc a b := by simpa only [Set.uIcc_of_le hab] using ht
    exact (ContinuousLinearMap.hasDerivAt_of_bilinear
      (B := B) (fun _ => ht₁ ht') (fun _ => ht₂ ht')).deriv
  refine ⟨hp.intervalIntegrable_deriv.congr_ae
    (ae_restrict_of_ae_restrict_of_subset Set.uIoc_subset_uIcc heq), ?_⟩
  rw [← intervalIntegral.integral_congr_ae_restrict
    (ae_restrict_of_ae_restrict_of_subset Set.uIoc_subset_uIcc heq)]
  exact hp.integral_deriv_eq_sub

/-- The integrated V-valued test can be paired with the actual weak
acceleration. This proves its integration-by-parts identity, including
both endpoint terms, without testing the wave equation with velocity. -/
theorem weak_solution_integrated_pairing (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) :
    let U : ℝ → V := fun t => ∫ r in 0..t, z.displacement r
    let w : ℝ → V := fun t => U T - U t
    IntervalIntegrable (fun t => z.acceleration t (w t) -
      inner ℝ (z.velocity t) (j.embedding (z.displacement t))) volume 0 T ∧
    (∫ t in 0..T, z.acceleration t (w t) -
      inner ℝ (z.velocity t) (j.embedding (z.displacement t))) =
      -(pivotValue j v₀ (U T)) := by
  let U : ℝ → V := fun t => ∫ r in 0..t, z.displacement r
  let w : ℝ → V := fun t => U T - U t
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have h1 : T ∈ Set.Icc 0 T := ⟨hT.le, le_rfl⟩
  have hUi := intervalIntegrable_of_timeIntegrable T
    (z.displacement_mem.integrable (by simp)) ⟨0, h0⟩ ⟨T, h1⟩
  have hUac : AbsolutelyContinuousOnInterval U 0 T := FiniteEnergy.vector_primitive_ac hUi
  have hwac : AbsolutelyContinuousOnInterval w 0 T :=
    (show AbsolutelyContinuousOnInterval (fun _ : ℝ => U T) 0 T from
      contDiff_const.contDiffOn.absolutelyContinuousOnInterval).sub hUac
  have hUd : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 T → HasDerivAt U (z.displacement t) t :=
    FiniteEnergy.primitive_increment_ae_deriv hT.le hUi (by intro t ht; simp [U])
  have hwd : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 T → HasDerivAt w (-z.displacement t) t := by
    filter_upwards [hUd] with t ht hti
    change HasDerivAt ((fun _ : ℝ => U T) - U) (-z.displacement t) t
    convert (hasDerivAt_const t (U T)).sub (ht hti) using 1
    simp
  have hgi := intervalIntegrable_of_timeIntegrable T
    (z.acceleration_mem.integrable (by norm_num)) ⟨0, h0⟩ ⟨T, h1⟩
  obtain ⟨_, _, _, hvi⟩ := primitive_representatives j T hT a u₀ v₀ f z
  have hvd : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 T →
      HasDerivAt (fun r => pivotValue j (z.velocity r)) (z.acceleration t) t :=
    FiniteEnergy.primitive_increment_ae_deriv hT.le hgi
      (fun t ht => hvi ⟨0, h0⟩ ⟨t, ht⟩)
  have hp := bilinear_integral_derivative (ContinuousLinearMap.id ℝ (StrongDual ℝ V))
    hT.le (weak_solution_pivot_ac j T hT a u₀ v₀ f z).2 hwac hvd hwd
  have hpivot (t : ℝ) : pivotValue j (z.velocity t) (z.displacement t) =
      inner ℝ (z.velocity t) (j.embedding (z.displacement t)) :=
    pivotInjection_apply j _ _
  simpa only [ContinuousLinearMap.id_apply, map_neg, hpivot,
    neg_add_eq_sub, w, U, sub_self, map_zero, intervalIntegral.integral_same,
    sub_zero, z.initial_velocity, zero_sub] using hp

/-- Only the H-valued Sobolev product rule is used here; this is not the
wave energy identity involving a(t;u(t),u(t)). -/
theorem weak_solution_displacement_norm (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) :
    IntervalIntegrable (fun t => inner ℝ (z.velocity t)
      (j.embedding (z.displacement t))) volume 0 T ∧
    ‖j.embedding (z.displacement T)‖ ^ 2 - ‖j.embedding u₀‖ ^ 2 =
      2 * ∫ t in 0..T, inner ℝ (z.velocity t) (j.embedding (z.displacement t)) := by
  let : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, hT.le⟩
  have h1 : T ∈ Set.Icc 0 T := ⟨hT.le, le_rfl⟩
  have hvi := intervalIntegrable_of_timeIntegrable T
    (z.velocity_mem.integrable (by simp)) ⟨0, h0⟩ ⟨T, h1⟩
  obtain ⟨_, _, hui, _⟩ := primitive_representatives j T hT a u₀ v₀ f z
  have hud : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 T →
      HasDerivAt (fun r => j.embedding (z.displacement r)) (z.velocity t) t :=
    FiniteEnergy.primitive_increment_ae_deriv hT.le hvi
      (fun t ht => hui ⟨0, h0⟩ ⟨t, ht⟩)
  have huac := (weak_solution_pivot_ac j T hT a u₀ v₀ f z).1
  have hp := bilinear_integral_derivative (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ)
    hT.le huac huac hud hud
  have heq (t : ℝ) : inner ℝ (j.embedding (z.displacement t)) (z.velocity t) +
      inner ℝ (z.velocity t) (j.embedding (z.displacement t)) =
      2 * inner ℝ (z.velocity t) (j.embedding (z.displacement t)) := by
    rw [real_inner_comm (j.embedding (z.displacement t))]
    ring
  have hB (x y : H) :
      (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ) x y = inner ℝ x y := rfl
  simp only [hB, heq, real_inner_self_eq_norm_sq,
    z.initial_displacement, intervalIntegral.integral_const_mul] at hp
  constructor
  · convert hp.1.const_mul (2⁻¹ : ℝ) using 1
    ext t
    ring
  · exact hp.2.symm

/-- The acceleration tested against ∫_t^T u determines the H displacement
norm, with all initial terms explicit. The later form product rule may
now be applied to a homogeneous difference. -/
theorem weak_solution_integrated_acceleration (j : HilbertTriple V H)
    (T : ℝ) (hT : 0 < T) (a : ℝ → Form V) (u₀ : V) (v₀ : H)
    (f : timeLpValue H 2 T) (z : WeakEnergySolution j T a u₀ v₀ f) :
    let U : ℝ → V := fun t => ∫ r in 0..t, z.displacement r
    let w : ℝ → V := fun t => U T - U t
    IntervalIntegrable (fun t => z.acceleration t (w t)) volume 0 T ∧
    ‖j.embedding (z.displacement T)‖ ^ 2 - ‖j.embedding u₀‖ ^ 2 =
      2 * (∫ t in 0..T, z.acceleration t (w t)) + 2 * pivotValue j v₀ (U T) := by
  let U : ℝ → V := fun t => ∫ r in 0..t, z.displacement r
  let w : ℝ → V := fun t => U T - U t
  obtain ⟨hpi, hp⟩ := weak_solution_integrated_pairing j T hT a u₀ v₀ f z
  obtain ⟨hki, hk⟩ := weak_solution_displacement_norm j T hT a u₀ v₀ f z
  have hgi : IntervalIntegrable (fun t => z.acceleration t (w t)) volume 0 T := by
    convert hpi.add hki using 1
    ext t
    exact (sub_add_cancel _ _).symm
  refine ⟨hgi, ?_⟩
  change (∫ t in 0..T, z.acceleration t (w t) -
    inner ℝ (z.velocity t) (j.embedding (z.displacement t))) = _ at hp
  rw [intervalIntegral.integral_sub hgi hki] at hp
  linarith

/-- Integral Gronwall with zero initial value, in the form used after the
short-interval coercivity absorption. -/
theorem eq_zero_of_le_integral {T k : ℝ} (hT : 0 ≤ T) (hk : 0 ≤ k)
    {E : ℝ → ℝ} (hE : ContinuousOn E (Set.Icc 0 T))
    (hn : ∀ t ∈ Set.Icc 0 T, 0 ≤ E t)
    (hle : ∀ t ∈ Set.Icc 0 T, E t ≤ k * ∫ r in 0..t, E r) :
    ∀ t ∈ Set.Icc 0 T, E t = 0 := by
  have hEi : IntervalIntegrable E volume 0 T := hE.intervalIntegrable_of_Icc hT
  let P : ℝ → ℝ := fun t => ∫ r in 0..t, E r
  have hPac : AbsolutelyContinuousOnInterval P 0 T := FiniteEnergy.vector_primitive_ac hEi
  have hPd : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 T → HasDerivAt P (E t) t :=
    FiniteEnergy.primitive_increment_ae_deriv hT hEi (by intro t ht; simp [P])
  have hPg := FiniteEnergy.ac_gronwall hT hk hPac
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 T)
    (Filter.Eventually.of_forall fun _ _ => le_rfl)
    (hPd.mono fun t ht hti => ⟨ht hti, by simpa [P] using hle t hti⟩)
  intro t ht
  have hP : P t ≤ 0 := by simpa [P] using hPg t ht
  have hmul := mul_nonpos_of_nonneg_of_nonpos hk hP
  exact le_antisymm ((hle t ht).trans hmul) (hn t ht)

/-- Evaluation of a convergent family of bounded linear maps at convergent
vectors. The operator family need only be continuous, not differentiable. -/
theorem tendsto_linearMap_apply {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter ι} {A : ι → E →L[ℝ] F} {x : ι → E}
    {A₀ : E →L[ℝ] F} {x₀ : E}
    (hA : Tendsto A l (𝓝 A₀)) (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun i => A i (x i)) l (𝓝 (A₀ x₀)) :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := F)).continuous.tendsto
    (A₀, x₀) |>.comp (hA.prodMk_nhds hx)

/-- Product rule for a scalar differentiable evaluation of a continuous
bilinear family. No derivative in the operator norm is assumed. -/
theorem varying_bilinear_hasDerivAt {a : ℝ → Form V} {x y : ℝ → V}
    {t d : ℝ} {dx dy : V}
    (ha : ContinuousAt a t)
    (hfixed : HasDerivAt (fun r => a r (x t) (y t)) d t)
    (hx : HasDerivAt x dx t) (hy : HasDerivAt y dy t) :
    HasDerivAt (fun r => a r (x r) (y r))
      (d + a t dx (y t) + a t (x t) dy) t := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hA : Tendsto a (𝓝[≠] t) (𝓝 (a t)) := ha.tendsto.mono_left nhdsWithin_le_nhds
  have hyc : Tendsto y (𝓝[≠] t) (𝓝 (y t)) :=
    hy.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h₁ := tendsto_linearMap_apply
    (tendsto_linearMap_apply hA hx.tendsto_slope) hyc
  have h₂ := tendsto_linearMap_apply
    (tendsto_linearMap_apply (x₀ := x t) hA tendsto_const_nhds) hy.tendsto_slope
  have hsum := (hfixed.tendsto_slope.add h₁).add h₂
  convert hsum using 1
  ext r
  simp only [slope_def_module, map_smul, ContinuousLinearMap.smul_apply,
    smul_eq_mul, map_sub, ContinuousLinearMap.sub_apply]
  ring

/-- Scalar C¹ regularity gives norm absolute continuity of the forms via
the accepted uniform secant bound. -/
theorem scalarC1_form_ac (T : ℝ) (hT : 0 ≤ T) (a : ℝ → Form V)
    (ha : ScalarC1 T a) : AbsolutelyContinuousOnInterval a 0 T := by
  obtain ⟨M, hM, hb⟩ := HyperbolicFormBoundsAndCarrier.form_secants_bounded T a ha
  have hLip : LipschitzOnWith ⟨M, hM⟩ a (Set.uIcc 0 T) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    rw [dist_eq_norm, dist_eq_norm]
    change ‖a s - a t‖ ≤ M * ‖s - t‖
    exact
      hb t (by simpa [Set.uIcc_of_le hT] using ht)
        s (by simpa [Set.uIcc_of_le hT] using hs)
  exact hLip.absolutelyContinuousOnInterval

set_option maxHeartbeats 400000

/-- Absolute continuity of the quadratic form along an AC V-valued curve. -/
theorem varying_form_ac (T : ℝ) (hT : 0 ≤ T) (a : ℝ → Form V)
    (ha : ScalarC1 T a) {w : ℝ → V}
    (hw : AbsolutelyContinuousOnInterval w 0 T) :
    AbsolutelyContinuousOnInterval (fun t => a t (w t) (w t)) 0 T := by
  have haac : AbsolutelyContinuousOnInterval a 0 T := scalarC1_form_ac (V := V) T hT a ha
  have hav : AbsolutelyContinuousOnInterval (fun t => a t (w t)) 0 T :=
    @bilinear_absolutelyContinuousOnInterval (Form V) V (StrongDual ℝ V)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (ContinuousLinearMap.id ℝ (Form V)) 0 T a w haac hw
  exact @bilinear_absolutelyContinuousOnInterval (StrongDual ℝ V) V ℝ
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (ContinuousLinearMap.id ℝ (StrongDual ℝ V)) 0 T (fun t => a t (w t)) w hav hw

/-- The varying-form chain rule on the closed time interval. The scalar
C¹ derivative is paired only after fixing the current vector. -/
theorem varying_form_ae_hasDerivAt (T : ℝ) (hT : 0 ≤ T) (a : ℝ → Form V)
    (ha : ScalarC1 T a)
    (hsym : ∀ t ∈ Set.Icc 0 T, ∀ x y, a t x y = a t y x)
    {w dw : ℝ → V}
    (hwd : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 T → HasDerivAt w (dw t) t) :
    ∀ᵐ t ∂volume, t ∈ Set.Icc 0 T →
      HasDerivAt (fun r => a r (w r) (w r))
        (derivWithin (fun r => a r (w t) (w t)) (Set.Icc 0 T) t +
          2 * a t (dw t) (w t)) t := by
  have haac : AbsolutelyContinuousOnInterval a 0 T := scalarC1_form_ac (V := V) T hT a ha
  have hac : ContinuousOn a (Set.Icc 0 T) := by
    have h : ContinuousOn a (Set.uIcc 0 T) :=
      @AbsolutelyContinuousOnInterval.continuousOn (Form V) inferInstance 0 T a haac
    simpa only [Set.uIcc_of_le hT] using h
  have hn₁ : ∀ᵐ t : ℝ ∂volume, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hn₂ : ∀ᵐ t : ℝ ∂volume, t ≠ T := by simp [ae_iff, measure_singleton]
  filter_upwards [hwd, hn₁, hn₂] with t hd ht0 htT ht
  have hti : t ∈ Set.Ioo 0 T :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htT⟩
  have hI : Set.Icc (0 : ℝ) T ∈ 𝓝 t := Icc_mem_nhds hti.1 hti.2
  have hf := ((ha (w t) (w t)).differentiableOn (by simp) t ht).hasDerivWithinAt
  have hd := varying_bilinear_hasDerivAt
    ((hac t ht).continuousAt hI)
    (hf.hasDerivAt hI) (hd ht) (hd ht)
  convert hd using 1
  rw [hsym t ht (w t) (dw t)]
  ring

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyExistence
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- FTC for the varying form on any subinterval of its scalar-C¹ interval. -/
theorem varying_form_integral_derivative (T : ℝ) (hT : 0 ≤ T) (a : ℝ → Form V)
    (ha : ScalarC1 T a)
    (hsym : ∀ t ∈ Set.Icc 0 T, ∀ x y, a t x y = a t y x)
    {w dw : ℝ → V} (hw : AbsolutelyContinuousOnInterval w 0 T)
    (hwd : ∀ᵐ t ∂volume, t ∈ Set.Icc 0 T → HasDerivAt w (dw t) t)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T) :
    IntervalIntegrable (fun r =>
      derivWithin (fun q => a q (w r) (w r)) (Set.Icc 0 T) r +
      2 * a r (dw r) (w r)) volume s t ∧
    (∫ r in s..t,
      derivWithin (fun q => a q (w r) (w r)) (Set.Icc 0 T) r +
      2 * a r (dw r) (w r)) = a t (w t) (w t) - a s (w s) (w s) := by
  have hsub : Set.uIcc s t ⊆ Set.Icc 0 T := Set.uIcc_subset_Icc hs ht
  have hp : AbsolutelyContinuousOnInterval (fun r => a r (w r) (w r)) s t :=
    (varying_form_ac T hT a ha hw).mono (by simpa [Set.uIcc_of_le hT] using hsub)
  have hd := varying_form_ae_hasDerivAt T hT a ha hsym hwd
  have heq : deriv (fun r => a r (w r) (w r)) =ᵐ[volume.restrict (Set.uIcc s t)]
      (fun r => derivWithin (fun q => a q (w r) (w r)) (Set.Icc 0 T) r +
        2 * a r (dw r) (w r)) := by
    filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_uIcc] with r hr hri
    exact (hr (hsub hri)).deriv
  refine ⟨hp.intervalIntegrable_deriv.congr_ae
    (ae_restrict_of_ae_restrict_of_subset Set.uIoc_subset_uIcc heq), ?_⟩
  rw [← intervalIntegral.integral_congr_ae_restrict
    (ae_restrict_of_ae_restrict_of_subset Set.uIoc_subset_uIcc heq)]
  exact hp.integral_deriv_eq_sub

/-- A continuous family of duals on a compact interval pairs integrably
with a Bochner-integrable vector curve. -/
theorem intervalIntegrable_dual_pairing {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}
    {L : ℝ → StrongDual ℝ E} {u : ℝ → E}
    (hL : ContinuousOn L (Set.uIcc a b)) (hu : IntervalIntegrable u volume a b) :
    IntervalIntegrable (fun r => L r (u r)) volume a b := by
  obtain ⟨R, hR⟩ := isCompact_uIcc.exists_bound_of_continuousOn hL
  have hLi : IntervalIntegrable L volume a b := hL.intervalIntegrable (μ := volume)
  rw [intervalIntegrable_iff] at hu hLi ⊢
  apply (ContinuousLinearMap.id ℝ (StrongDual ℝ E)).integrable_of_bilin_of_bdd_left R
    hLi.aestronglyMeasurable ?_ hu
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact hR r (Set.Ioc_subset_Icc_self hr)

/-- The source's integrated scalar-form product rule for its primitive test.
Only scalar-C¹ regularity of the forms is used. -/
theorem varying_form_primitive_identity (T : ℝ) (hT : 0 ≤ T) (a : ℝ → Form V)
    (ha : ScalarC1 T a)
    (hsym : ∀ t ∈ Set.Icc 0 T, ∀ x y, a t x y = a t y x)
    {u : ℝ → V} (hu : IntervalIntegrable u volume 0 T)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 T) (ht : t ∈ Set.Icc 0 T) :
    let U : ℝ → V := fun r => ∫ q in 0..r, u q
    let w : ℝ → V := fun r => U t - U r
    IntervalIntegrable (fun r => a r (u r) (w r)) volume s t ∧
    IntervalIntegrable (fun r =>
      derivWithin (fun q => a q (w r) (w r)) (Set.Icc 0 T) r) volume s t ∧
    2 * (∫ r in s..t, a r (u r) (w r)) =
      a s (w s) (w s) +
      ∫ r in s..t, derivWithin (fun q => a q (w r) (w r)) (Set.Icc 0 T) r := by
  dsimp only
  let U : ℝ → V := fun r => ∫ q in 0..r, u q
  let w : ℝ → V := fun r => U t - U r
  have hUac : AbsolutelyContinuousOnInterval U 0 T := FiniteEnergy.vector_primitive_ac hu
  have hwac : AbsolutelyContinuousOnInterval w 0 T :=
    (show AbsolutelyContinuousOnInterval (fun _ : ℝ => U t) 0 T from
      contDiff_const.contDiffOn.absolutelyContinuousOnInterval).sub hUac
  have hUd : ∀ᵐ r ∂volume, r ∈ Set.Icc 0 T → HasDerivAt U (u r) r :=
    FiniteEnergy.primitive_increment_ae_deriv hT hu (by intro r hr; simp [U])
  have hwd : ∀ᵐ r ∂volume, r ∈ Set.Icc 0 T → HasDerivAt w (-u r) r := by
    filter_upwards [hUd] with r hr hri
    convert (hasDerivAt_const r (U t)).sub (hr hri) using 1 <;> simp [w]
  have hsub : Set.uIcc s t ⊆ Set.Icc 0 T := Set.uIcc_subset_Icc hs ht
  have hav : AbsolutelyContinuousOnInterval (fun r => a r (w r)) 0 T :=
    @bilinear_absolutelyContinuousOnInterval (Form V) V (StrongDual ℝ V)
      inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      (ContinuousLinearMap.id ℝ (Form V)) 0 T a w
      (scalarC1_form_ac (V := V) T hT a ha) hwac
  have havc : ContinuousOn (fun r => a r (w r)) (Set.uIcc 0 T) :=
    @AbsolutelyContinuousOnInterval.continuousOn (StrongDual ℝ V) inferInstance
      0 T (fun r => a r (w r)) hav
  have hvi : IntervalIntegrable (fun r => a r (w r) (u r)) volume s t :=
    intervalIntegrable_dual_pairing
      (havc.mono (by simpa [Set.uIcc_of_le hT] using hsub))
      (hu.mono_set (by simpa [Set.uIcc_of_le hT] using hsub))
  have hui : IntervalIntegrable (fun r => a r (u r) (w r)) volume s t := by
    apply hvi.congr
    intro r hr
    exact hsym r (hsub (Set.uIoc_subset_uIcc hr)) _ _
  have hp := varying_form_integral_derivative T hT a ha hsym hwac hwd hs ht
  have hsum : IntervalIntegrable (fun r =>
      derivWithin (fun q => a q (w r) (w r)) (Set.Icc 0 T) r -
      2 * a r (u r) (w r)) volume s t := by
    simpa only [map_neg, neg_apply, mul_neg, ← sub_eq_add_neg] using hp.1
  have hdi : IntervalIntegrable (fun r =>
      derivWithin (fun q => a q (w r) (w r)) (Set.Icc 0 T) r) volume s t := by
    convert hsum.add (hui.const_mul 2) using 1
    ext r
    ring
  refine ⟨hui, hdi, ?_⟩
  have hpe := hp.2
  simp only [map_neg, neg_apply, mul_neg, ← sub_eq_add_neg, w, sub_self, map_zero] at hpe
  rw [intervalIntegral.integral_sub hdi (hui.const_mul 2),
    intervalIntegral.integral_const_mul] at hpe
  change 2 * (∫ r in s..t, a r (u r) (w r)) = _
  change (∫ r in s..t, derivWithin (fun q => a q (w r) (w r))
    (Set.Icc 0 T) r) - 2 * (∫ r in s..t, a r (u r) (w r)) =
    0 - a s (w s) (w s) at hpe
  linarith

/-- One uniform constant controls partial-time integrals along every bounded
vector curve, without any operator-norm differentiability hypothesis. -/
theorem exists_form_partial_integral_bound (T : ℝ) (a : ℝ → Form V)
    (ha : ScalarC1 T a) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (w : ℝ → V) (B s t : ℝ),
      s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      (∀ r ∈ Set.uIcc s t, ‖w r‖ ^ 2 ≤ B) →
      |∫ r in s..t,
        derivWithin (fun q => a q (w r) (w r)) (Set.Icc 0 T) r| ≤
          M * B * |t - s| := by
  obtain ⟨M, hM, hb, _⟩ := HyperbolicFormBoundsAndCarrier.uniform_bounds T a ha
  refine ⟨M, hM, ?_⟩
  intro w B s t hs ht hw
  have hsub : Set.uIcc s t ⊆ Set.Icc 0 T := Set.uIcc_subset_Icc hs ht
  apply (show ‖∫ r in s..t,
      derivWithin (fun q => a q (w r) (w r)) (Set.Icc 0 T) r‖ ≤
        M * B * |t - s| from ?_)
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro r hr
  have hri := Set.uIoc_subset_uIcc hr
  have hd : |derivWithin (fun q => a q (w r) (w r)) (Set.Icc 0 T) r| ≤
      M * ‖w r‖ * ‖w r‖ :=
    le_trans (le_add_of_nonneg_left (abs_nonneg _)) (hb r (hsub hri) (w r) (w r))
  calc
    ‖derivWithin (fun q => a q (w r) (w r)) (Set.Icc 0 T) r‖ ≤
        M * ‖w r‖ ^ 2 := by simpa only [Real.norm_eq_abs, pow_two, mul_assoc] using hd
    _ ≤ M * B := mul_le_mul_of_nonneg_left (hw r hri) hM

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyExistence
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem derivativeValue_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) (u v g h : ℝ → E) (hu : derivativeValue T u g)
    (hv : derivativeValue T v h) :
    derivativeValue T (fun t => u t - v t) (fun t => g t - h t) := by
  refine ⟨hu.1.sub hv.1, hu.2.1.sub hv.2.1, ?_⟩
  intro φ hφ
  have hiu : Integrable (fun t => deriv φ t • u t) (timeMeasureValue T) ∧
      Integrable (fun t => φ t • g t) (timeMeasureValue T) :=
    hasTimeDerivative_test_integrable T u g hu φ hφ
  have hiv : Integrable (fun t => deriv φ t • v t) (timeMeasureValue T) ∧
      Integrable (fun t => φ t • h t) (timeMeasureValue T) :=
    hasTimeDerivative_test_integrable T v h hv φ hφ
  simp_rw [smul_sub]
  rw [integral_sub hiu.1 hiv.1, integral_sub hiu.2 hiv.2, hu.2.2 φ hφ, hv.2.2 φ hφ]
  abel

def weakEnergySolution_sub (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z w : WeakEnergySolution j T a u₀ v₀ f) :
    WeakEnergySolution j T a 0 0 (0 : timeLpValue H 2 T) where
  displacement := fun t => z.displacement t - w.displacement t
  velocity := fun t => z.velocity t - w.velocity t
  acceleration := fun t => z.acceleration t - w.acceleration t
  displacement_mem := z.displacement_mem.sub w.displacement_mem
  pivot_displacement_mem := by
    convert z.pivot_displacement_mem.sub w.pivot_displacement_mem using 1
    ext t
    simp only [Pi.sub_apply, map_sub]
  velocity_mem := z.velocity_mem.sub w.velocity_mem
  dual_velocity_mem := by
    convert z.dual_velocity_mem.sub w.dual_velocity_mem using 1
    ext t
    simp only [Pi.sub_apply, map_sub]
  acceleration_mem := z.acceleration_mem.sub w.acceleration_mem
  displacement_derivative := by
    simpa only [map_sub, Pi.sub_apply] using
      derivativeValue_sub T _ _ _ _ z.displacement_derivative w.displacement_derivative
  velocity_derivative := by
    simpa only [map_sub, Pi.sub_apply] using
      derivativeValue_sub T _ _ _ _ z.velocity_derivative w.velocity_derivative
  equation := by
    filter_upwards [z.equation, w.equation, Lp.coeFn_zero (E := H) (p := 2)
      (μ := timeMeasureValue T)] with t hz hw hf
    simp only [map_sub, hf, Pi.zero_apply, map_zero]
    calc
      z.acceleration t - w.acceleration t + (a t (z.displacement t) - a t (w.displacement t)) =
          (z.acceleration t + a t (z.displacement t)) -
            (w.acceleration t + a t (w.displacement t)) := by abel
      _ = 0 := by rw [hz, hw, sub_self]
  displacement_weak := by
    intro L
    convert (z.displacement_weak L).sub (w.displacement_weak L) using 1
    ext t
    simp only [Pi.sub_apply, map_sub]
  velocity_weak := by
    intro L
    convert (z.velocity_weak L).sub (w.velocity_weak L) using 1
    ext t
    simp only [Pi.sub_apply, map_sub]
  initial_displacement := by simp only [z.initial_displacement, w.initial_displacement, sub_self]
  initial_velocity := by simp only [z.initial_velocity, w.initial_velocity, sub_self]

theorem derivativeValue_restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T s : ℝ} (hsT : s ≤ T) (u g : ℝ → E) (hu : derivativeValue T u g) :
    derivativeValue s u g := by
  have hsub : Set.Ioo 0 s ⊆ Set.Ioo 0 T := Set.Ioo_subset_Ioo_right hsT
  refine ⟨hu.1.mono_set hsub, hu.2.1.mono_set hsub, ?_⟩
  intro φ hφ
  have heq (ψ : ℝ → ℝ) (v : ℝ → E) (hψ : tsupport ψ ⊆ Set.Ioo 0 s) :
      (∫ t, ψ t • v t ∂timeMeasureValue T) =
        ∫ t, ψ t • v t ∂timeMeasureValue s := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo hsub
    intro t ht
    have hz : ψ t = 0 := by
      by_contra hn
      exact ht.2 (hψ (subset_tsupport ψ hn))
    simp only [hz, zero_smul]
  rw [← heq (deriv φ) u (tsupport_deriv_subset.trans hφ.2.2), ← heq φ g hφ.2.2]
  exact hu.2.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hsub⟩

theorem timeMeasureValue_mono {s T : ℝ} (hsT : s ≤ T) :
    timeMeasureValue s ≤ timeMeasureValue T :=
  Measure.restrict_mono (Set.Ioo_subset_Ioo_right hsT) (le_refl _)

def timeLp_restrict {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {T s : ℝ} (hsT : s ≤ T)
    (f : timeLpValue E p T) : timeLpValue E p s :=
  ((Lp.memLp f).mono_measure (timeMeasureValue_mono hsT)).toLp f

theorem timeLp_restrict_ae {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {T s : ℝ} (hsT : s ≤ T)
    (f : timeLpValue E p T) :
    timeLp_restrict hsT f =ᵐ[timeMeasureValue s] f :=
  MemLp.coeFn_toLp _

@[simp] theorem timeLp_restrict_zero {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {T s : ℝ} (hsT : s ≤ T) :
    timeLp_restrict hsT (0 : timeLpValue E p T) = 0 := by
  apply Lp.ext
  have hf : (0 : timeLpValue E p T) =ᵐ[timeMeasureValue s] (0 : ℝ → E) :=
    (ae_mono (timeMeasureValue_mono hsT)) (Lp.coeFn_zero E p (timeMeasureValue T))
  filter_upwards [timeLp_restrict_ae hsT (0 : timeLpValue E p T), hf,
    Lp.coeFn_zero E p (timeMeasureValue s)] with t ht hf hz
  exact ht.trans (hf.trans hz.symm)


def weakEnergySolution_restrict (j : HilbertTriple V H) {T s : ℝ} (hsT : s ≤ T)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) :
    WeakEnergySolution j s a u₀ v₀ (timeLp_restrict hsT f) where
  displacement := z.displacement
  velocity := z.velocity
  acceleration := z.acceleration
  displacement_mem := z.displacement_mem.mono_measure (timeMeasureValue_mono hsT)
  pivot_displacement_mem := z.pivot_displacement_mem.mono_measure (timeMeasureValue_mono hsT)
  velocity_mem := z.velocity_mem.mono_measure (timeMeasureValue_mono hsT)
  dual_velocity_mem := z.dual_velocity_mem.mono_measure (timeMeasureValue_mono hsT)
  acceleration_mem := z.acceleration_mem.mono_measure (timeMeasureValue_mono hsT)
  displacement_derivative := derivativeValue_restrict hsT _ _ z.displacement_derivative
  velocity_derivative := derivativeValue_restrict hsT _ _ z.velocity_derivative
  equation := by
    have hq := (ae_mono (timeMeasureValue_mono hsT)) z.equation
    filter_upwards [hq, timeLp_restrict_ae hsT f] with t ht hf
    rw [hf]
    exact ht
  displacement_weak := fun L => (z.displacement_weak L).mono (Set.Icc_subset_Icc_right hsT)
  velocity_weak := fun L => (z.velocity_weak L).mono (Set.Icc_subset_Icc_right hsT)
  initial_displacement := z.initial_displacement
  initial_velocity := z.initial_velocity

def weakEnergySolution_restrict_homogeneous (j : HilbertTriple V H) {T s : ℝ}
    (hsT : s ≤ T) (a : ℝ → Form V)
    (z : WeakEnergySolution j T a 0 0 (0 : timeLpValue H 2 T)) :
    WeakEnergySolution j s a 0 0 (0 : timeLpValue H 2 s) where
  displacement := z.displacement
  velocity := z.velocity
  acceleration := z.acceleration
  displacement_mem := z.displacement_mem.mono_measure (timeMeasureValue_mono hsT)
  pivot_displacement_mem := z.pivot_displacement_mem.mono_measure (timeMeasureValue_mono hsT)
  velocity_mem := z.velocity_mem.mono_measure (timeMeasureValue_mono hsT)
  dual_velocity_mem := z.dual_velocity_mem.mono_measure (timeMeasureValue_mono hsT)
  acceleration_mem := z.acceleration_mem.mono_measure (timeMeasureValue_mono hsT)
  displacement_derivative := derivativeValue_restrict hsT _ _ z.displacement_derivative
  velocity_derivative := derivativeValue_restrict hsT _ _ z.velocity_derivative
  equation := by
    have hq := (ae_mono (timeMeasureValue_mono hsT)) z.equation
    have hf : (0 : timeLpValue H 2 T) =ᵐ[timeMeasureValue s] (0 : ℝ → H) :=
      (ae_mono (timeMeasureValue_mono hsT)) (Lp.coeFn_zero H 2 (timeMeasureValue T))
    filter_upwards [hq,hf,Lp.coeFn_zero H 2 (timeMeasureValue s)] with t ht hf hz
    simp only [hf,Pi.zero_apply] at ht
    simpa only [hz,Pi.zero_apply] using ht
  displacement_weak := fun L => (z.displacement_weak L).mono (Set.Icc_subset_Icc_right hsT)
  velocity_weak := fun L => (z.velocity_weak L).mono (Set.Icc_subset_Icc_right hsT)
  initial_displacement := z.initial_displacement
  initial_velocity := z.initial_velocity

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

theorem global_zero_of_local_zero {E : Type*} [Zero E]
    (T δ : ℝ) (_hT : 0 ≤ T) (hδ : 0 < δ) (z : ℝ → E) (hz0 : z 0 = 0)
    (hlocal : ∀ τ ∈ Set.Icc 0 T, z τ = 0 →
      ∀ t ∈ Set.Icc τ T, t ≤ τ + δ → z t = 0) :
    ∀ t ∈ Set.Icc 0 T, z t = 0 := by
  have hind : ∀ n : ℕ, ∀ t ∈ Set.Icc 0 T, t ≤ (n : ℝ) * δ → z t = 0 := by
    intro n
    induction n with
    | zero =>
        intro t ht hb
        simp only [Nat.cast_zero, zero_mul] at hb
        have ht0 : t = 0 := le_antisymm hb ht.1
        simpa only [ht0] using hz0
    | succ n ih =>
        intro t ht hb
        by_cases htn : t ≤ (n : ℝ) * δ
        · exact ih t ht htn
        · have hn0 : 0 ≤ (n : ℝ) * δ := mul_nonneg (Nat.cast_nonneg n) hδ.le
          have hnT : (n : ℝ) * δ ≤ T := (le_of_not_ge htn).trans ht.2
          apply hlocal ((n : ℝ) * δ) ⟨hn0, hnT⟩ (ih _ ⟨hn0, hnT⟩ le_rfl)
            t ⟨(le_of_not_ge htn), ht.2⟩
          simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hb
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ)
  have hn : T < (n : ℝ) * δ := (div_lt_iff₀ hδ).mp hn
  intro t ht
  exact hind n t ht (ht.2.trans hn.le)

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyExistence

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem derivativeValue_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ) : derivativeValue T (0 : ℝ → E) 0 := by
  refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
  intro φ hφ
  simp only [Pi.zero_apply, smul_zero, integral_zero, neg_zero]

theorem derivativeValue_eq_zero_of_ae_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (T : ℝ) (u g : ℝ → E)
    (hd : derivativeValue T u g) (hu : u =ᵐ[timeMeasureValue T] 0) :
    g =ᵐ[timeMeasureValue T] 0 := by
  have hd' := (hasTimeDerivative_congr T u 0 g g hu Filter.EventuallyEq.rfl).mp hd
  exact hasTimeDerivative_unique T _ _ _ hd' (derivativeValue_zero T)

theorem weak_solution_velocity_zero_of_displacement_zero (j : HilbertTriple V H)
    (T : ℝ) (hT : 0 < T) (a : ℝ → Form V) (u₀ : V) (v₀ : H)
    (f : timeLpValue H 2 T) (z : WeakEnergySolution j T a u₀ v₀ f)
    (hu : ∀ t ∈ Set.Icc 0 T, z.displacement t = 0) :
    (∀ t ∈ Set.Icc 0 T, z.velocity t = 0) ∧
    z.acceleration =ᵐ[timeMeasureValue T] 0 := by
  have hua : z.displacement =ᵐ[timeMeasureValue T] 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact hu t (Set.Ioo_subset_Icc_self ht)
  have hv : z.velocity =ᵐ[timeMeasureValue T] 0 :=
    derivativeValue_eq_zero_of_ae_zero T _ _ z.displacement_derivative
      (hua.mono fun t ht => by simp only [ht, Pi.zero_apply, map_zero])
  have hgv : (fun t => pivotValue j (z.velocity t)) =ᵐ[timeMeasureValue T] 0 :=
    hv.mono fun t ht => by simp only [ht, Pi.zero_apply, map_zero]
  refine ⟨?_, derivativeValue_eq_zero_of_ae_zero T _ _ z.velocity_derivative hgv⟩
  apply weaklyContinuousOn_eq_of_ae T hT _ _ z.velocity_weak ?_ hv
  intro L
  simpa only [Pi.zero_apply, map_zero] using
    (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ))).continuousOn

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyExistence
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem FormHypotheses.forward (j : HilbertTriple V H) (T s : ℝ)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (hs : s ∈ Set.Icc 0 T) :
    FormHypotheses j (T-s) (fun r => a (s+r)) α C := by
  have hmaps : Set.MapsTo (fun r : ℝ => s+r) (Set.Icc 0 (T-s)) (Set.Icc 0 T) := by
    intro r hr
    exact ⟨by linarith [hr.1, hs.1], by linarith [hr.2]⟩
  exact ⟨fun x y => (ha.scalarC1 x y).comp
    ((contDiff_const.add contDiff_id).contDiffOn) hmaps,
    fun r hr => ha.symmetric _ (hmaps hr), ha.alpha_pos, ha.shift_nonneg,
    fun r hr => ha.garding _ (hmaps hr)⟩

theorem FormHypotheses.backward (j : HilbertTriple V H) (T s : ℝ)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j T a α C)
    (hs : s ∈ Set.Icc 0 T) :
    FormHypotheses j s (fun r => a (s-r)) α C := by
  have hmaps : Set.MapsTo (fun r : ℝ => s-r) (Set.Icc 0 s) (Set.Icc 0 T) := by
    intro r hr
    exact ⟨by linarith [hr.2], by linarith [hr.1, hs.2]⟩
  exact ⟨fun x y => (ha.scalarC1 x y).comp
    ((contDiff_const.sub contDiff_id).contDiffOn) hmaps,
    fun r hr => ha.symmetric _ (hmaps hr), ha.alpha_pos, ha.shift_nonneg,
    fun r hr => ha.garding _ (hmaps hr)⟩

theorem forwardTime_measurePreserving (T s : ℝ) :
    MeasurePreserving (fun r : ℝ => s+r) (timeMeasureValue (T-s))
      (volume.restrict (Set.Ioo s T)) := by
  have h := (measurePreserving_add_left volume s).restrict_preimage
    (measurableSet_Ioo : MeasurableSet (Set.Ioo s T))
  have hpre : (fun r : ℝ => s+r) ⁻¹' Set.Ioo s T = Set.Ioo 0 (T-s) := by
    ext r
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro hr <;> constructor <;> linarith [hr.1,hr.2]
  simpa only [hpre, timeMeasureValue] using h

theorem backwardTime_measurePreserving (s : ℝ) :
    MeasurePreserving (fun r : ℝ => s-r) (timeMeasureValue s) (timeMeasureValue s) := by
  have h := (volume.measurePreserving_sub_left s).restrict_preimage
    (measurableSet_Ioo : MeasurableSet (Set.Ioo 0 s))
  have hpre : (fun r : ℝ => s-r) ⁻¹' Set.Ioo 0 s = Set.Ioo 0 s := by
    ext r
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro hr <;> constructor <;> linarith [hr.1,hr.2]
  simpa only [hpre, timeMeasureValue] using h

theorem MemLp.forwardTime {E : Type*} [NormedAddCommGroup E]
    {T s : ℝ} {p : ℝ≥0∞} {g : ℝ → E}
    (hg : MemLp g p (timeMeasureValue T)) (hs : 0 ≤ s) :
    MemLp (fun r => g (s+r)) p (timeMeasureValue (T-s)) := by
  have hsub : Set.Ioo s T ⊆ Set.Ioo 0 T := fun r hr => ⟨lt_of_le_of_lt hs hr.1, hr.2⟩
  exact (hg.mono_measure (Measure.restrict_mono hsub le_rfl)).comp_measurePreserving
    (forwardTime_measurePreserving T s)

theorem MemLp.backwardTime {E : Type*} [NormedAddCommGroup E]
    {T s : ℝ} {p : ℝ≥0∞} {g : ℝ → E}
    (hg : MemLp g p (timeMeasureValue T)) (hs : s ≤ T) :
    MemLp (fun r => g (s-r)) p (timeMeasureValue s) := by
  have hsub : Set.Ioo 0 s ⊆ Set.Ioo 0 T := fun r hr => ⟨hr.1, lt_of_lt_of_le hr.2 hs⟩
  exact (hg.mono_measure (Measure.restrict_mono hsub le_rfl)).comp_measurePreserving
    (backwardTime_measurePreserving s)

theorem Integrable.forwardTime {E : Type*} [NormedAddCommGroup E]
    {T s : ℝ} {g : ℝ → E}
    (hg : Integrable g (timeMeasureValue T)) (hs : 0 ≤ s) :
    Integrable (fun r => g (s+r)) (timeMeasureValue (T-s)) := by
  have hsub : Set.Ioo s T ⊆ Set.Ioo 0 T := fun r hr => ⟨lt_of_le_of_lt hs hr.1, hr.2⟩
  exact (forwardTime_measurePreserving T s).integrable_comp_of_integrable
    (hg.mono_measure (Measure.restrict_mono hsub le_rfl))

theorem Integrable.backwardTime {E : Type*} [NormedAddCommGroup E]
    {T s : ℝ} {g : ℝ → E}
    (hg : Integrable g (timeMeasureValue T)) (hs : s ≤ T) :
    Integrable (fun r => g (s-r)) (timeMeasureValue s) := by
  have hsub : Set.Ioo 0 s ⊆ Set.Ioo 0 T := fun r hr => ⟨hr.1, lt_of_lt_of_le hr.2 hs⟩
  exact (backwardTime_measurePreserving s).integrable_comp_of_integrable
    (hg.mono_measure (Measure.restrict_mono hsub le_rfl))

theorem derivativeValue_forwardTime {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T s : ℝ} (hs : s ∈ Set.Icc 0 T) (U g : ℝ → E)
    (hU : Integrable U (timeMeasureValue T)) (hg : Integrable g (timeMeasureValue T))
    (hinc : ∀ r t : Set.Icc 0 T, U t - U r = ∫ x in r.val..t.val, g x) :
    derivativeValue (T-s) (fun r => U (s+r)) (fun r => g (s+r)) := by
  apply GalerkinNet.derivativeValue_of_integral_increments (T-s) (sub_nonneg.mpr hs.2)
    _ _ (Integrable.forwardTime hU hs.1) (Integrable.forwardTime hg hs.1)
  intro r t
  have hmaps : ∀ r ∈ Set.Icc 0 (T-s), s+r ∈ Set.Icc 0 T := by
    intro r hr
    constructor <;> linarith [hr.1,hr.2,hs.1]
  rw [intervalIntegral.integral_comp_add_left]
  exact hinc ⟨s+r,hmaps r r.property⟩ ⟨s+t,hmaps t t.property⟩

theorem derivativeValue_backwardTime {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T s : ℝ} (hs : s ∈ Set.Icc 0 T) (U g : ℝ → E)
    (hU : Integrable U (timeMeasureValue T)) (hg : Integrable g (timeMeasureValue T))
    (hinc : ∀ r t : Set.Icc 0 T, U t - U r = ∫ x in r.val..t.val, g x) :
    derivativeValue s (fun r => U (s-r)) (fun r => -g (s-r)) := by
  apply GalerkinNet.derivativeValue_of_integral_increments s hs.1
    _ _ (Integrable.backwardTime hU hs.2) (Integrable.backwardTime hg hs.2).neg
  intro r t
  have hmaps : ∀ r ∈ Set.Icc 0 s, s-r ∈ Set.Icc 0 T := by
    intro r hr
    constructor <;> linarith [hr.1,hr.2,hs.2]
  simp only [Pi.neg_apply]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left,
    ← intervalIntegral.integral_symm]
  exact hinc ⟨s-r,hmaps r r.property⟩ ⟨s-t,hmaps t t.property⟩

def forwardForcing {T s : ℝ} (f : timeLpValue H 2 T) (hs : 0 ≤ s) :
    timeLpValue H 2 (T-s) :=
  (MemLp.forwardTime (Lp.memLp f) hs).toLp (fun r => f (s+r))

theorem forwardForcing_coe {T s : ℝ} (f : timeLpValue H 2 T) (hs : 0 ≤ s) :
    forwardForcing f hs =ᵐ[timeMeasureValue (T-s)] (fun r => f (s+r)) :=
  MemLp.coeFn_toLp _

def backwardForcing {T s : ℝ} (f : timeLpValue H 2 T) (hs : s ≤ T) :
    timeLpValue H 2 s :=
  (MemLp.backwardTime (Lp.memLp f) hs).toLp (fun r => f (s-r))

theorem backwardForcing_coe {T s : ℝ} (f : timeLpValue H 2 T) (hs : s ≤ T) :
    backwardForcing f hs =ᵐ[timeMeasureValue s] (fun r => f (s-r)) :=
  MemLp.coeFn_toLp _

/-- Restrict a weak solution to an arbitrary later starting time. -/
def WeakEnergySolution.forwardTime (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) (s : ℝ) (hs : s ∈ Set.Icc 0 T) :
    WeakEnergySolution j (T-s) (fun r => a (s+r))
      (z.displacement s) (z.velocity s) (forwardForcing f hs.1) := by
  letI : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  obtain ⟨_,_,huinc,hvinc⟩ := primitive_representatives j T hT a u₀ v₀ f z
  have hmaps : Set.MapsTo (fun r : ℝ => s+r) (Set.Icc 0 (T-s)) (Set.Icc 0 T) := by
    intro r hr
    constructor <;> linarith [hr.1,hr.2,hs.1]
  refine {
    displacement := fun r => z.displacement (s+r)
    velocity := fun r => z.velocity (s+r)
    acceleration := fun r => z.acceleration (s+r)
    displacement_mem := MemLp.forwardTime z.displacement_mem hs.1
    pivot_displacement_mem := MemLp.forwardTime z.pivot_displacement_mem hs.1
    velocity_mem := MemLp.forwardTime z.velocity_mem hs.1
    dual_velocity_mem := MemLp.forwardTime z.dual_velocity_mem hs.1
    acceleration_mem := MemLp.forwardTime z.acceleration_mem hs.1
    displacement_derivative := derivativeValue_forwardTime hs _ _
      (z.pivot_displacement_mem.integrable (by simp))
      (z.velocity_mem.integrable (by simp)) huinc
    velocity_derivative := derivativeValue_forwardTime hs _ _
      (z.dual_velocity_mem.integrable (by norm_num))
      (z.acceleration_mem.integrable (by norm_num)) hvinc
    equation := ?_
    displacement_weak := fun L => (z.displacement_weak L).comp
      (continuous_const.add continuous_id).continuousOn hmaps
    velocity_weak := fun L => (z.velocity_weak L).comp
      (continuous_const.add continuous_id).continuousOn hmaps
    initial_displacement := by simp
    initial_velocity := by simp }
  have hsub : Set.Ioo s T ⊆ Set.Ioo 0 T := fun r hr => ⟨lt_of_le_of_lt hs.1 hr.1, hr.2⟩
  have heq := (forwardTime_measurePreserving T s).quasiMeasurePreserving.ae
    (ae_restrict_of_ae_restrict_of_subset hsub z.equation)
  filter_upwards [heq, forwardForcing_coe f hs.1] with r hr hf
  simpa only [hf] using hr

/-- Reverse time from arbitrary weak state data. The velocity changes sign,
while acceleration and forcing retain their signs. -/
def WeakEnergySolution.backwardTime (j : HilbertTriple V H) (T : ℝ) (hT : 0 < T)
    (a : ℝ → Form V) (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) (s : ℝ) (hs : s ∈ Set.Icc 0 T) :
    WeakEnergySolution j s (fun r => a (s-r))
      (z.displacement s) (-z.velocity s) (backwardForcing f hs.2) := by
  letI : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 T)))
  obtain ⟨_,_,huinc,hvinc⟩ := primitive_representatives j T hT a u₀ v₀ f z
  have hmaps : Set.MapsTo (fun r : ℝ => s-r) (Set.Icc 0 s) (Set.Icc 0 T) := by
    intro r hr
    constructor <;> linarith [hr.1,hr.2,hs.2]
  have hback := derivativeValue_backwardTime hs _ _
      (z.dual_velocity_mem.integrable (by norm_num))
      (z.acceleration_mem.integrable (by norm_num)) hvinc
  have hneg := hasTimeDerivative_map (-ContinuousLinearMap.id ℝ (StrongDual ℝ V))
    s _ _ hback
  refine {
    displacement := fun r => z.displacement (s-r)
    velocity := fun r => -z.velocity (s-r)
    acceleration := fun r => z.acceleration (s-r)
    displacement_mem := MemLp.backwardTime z.displacement_mem hs.2
    pivot_displacement_mem := MemLp.backwardTime z.pivot_displacement_mem hs.2
    velocity_mem := (MemLp.backwardTime z.velocity_mem hs.2).neg
    dual_velocity_mem := ?_
    acceleration_mem := MemLp.backwardTime z.acceleration_mem hs.2
    displacement_derivative := derivativeValue_backwardTime hs _ _
      (z.pivot_displacement_mem.integrable (by simp))
      (z.velocity_mem.integrable (by simp)) huinc
    velocity_derivative := ?_
    equation := ?_
    displacement_weak := fun L => (z.displacement_weak L).comp
      (continuous_const.sub continuous_id).continuousOn hmaps
    velocity_weak := ?_
    initial_displacement := by simp
    initial_velocity := by simp }
  · have hdu := MemLp.backwardTime z.dual_velocity_mem hs.2
    apply hdu.congr_enorm
    · have hnegcont : Continuous (fun l : StrongDual ℝ V => -l) := continuous_neg
      simpa only [Function.comp_def, map_neg, Pi.neg_apply] using
        hnegcont.comp_aestronglyMeasurable hdu.aestronglyMeasurable
    · exact Filter.Eventually.of_forall (fun r => by simp only [map_neg, enorm_neg])
  · simpa only [HasTimeDerivative, ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply,
      neg_neg, map_neg] using hneg
  · have hsub : Set.Ioo 0 s ⊆ Set.Ioo 0 T := fun r hr => ⟨hr.1, lt_of_lt_of_le hr.2 hs.2⟩
    have heq := (backwardTime_measurePreserving s).quasiMeasurePreserving.ae
      (ae_restrict_of_ae_restrict_of_subset hsub z.equation)
    filter_upwards [heq, backwardForcing_coe f hs.2] with r hr hf
    simpa only [hf] using hr
  · intro L
    simpa only [Function.comp_def, Pi.sub_apply, id_eq, map_neg, ContinuousLinearMap.neg_apply] using (z.velocity_weak (-L)).comp
      (continuous_const.sub continuous_id).continuousOn hmaps

/-- Two one-sided translated strong traces give continuity at the original time. -/
theorem continuousWithinAt_of_forward_backward {E : Type*} [TopologicalSpace E]
    {T s : ℝ} (x : ℝ → E)
    (hf : Tendsto (fun r => x (s+r)) (𝓝[Set.Icc 0 (T-s)] 0) (𝓝 (x s)))
    (hb : Tendsto (fun r => x (s-r)) (𝓝[Set.Icc 0 s] 0) (𝓝 (x s))) :
    ContinuousWithinAt x (Set.Icc 0 T) s := by
  have hfmaps : Set.MapsTo (fun t : ℝ => t-s) (Set.Icc s T) (Set.Icc 0 (T-s)) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hbmaps : Set.MapsTo (fun t : ℝ => s-t) (Set.Icc 0 s) (Set.Icc 0 s) := by
    intro t ht
    constructor <;> linarith [ht.1,ht.2]
  have hfc : ContinuousWithinAt (fun r => x (s+r)) (Set.Icc 0 (T-s)) 0 := by
    simpa only [ContinuousWithinAt,add_zero] using hf
  have hbc : ContinuousWithinAt (fun r => x (s-r)) (Set.Icc 0 s) 0 := by
    simpa only [ContinuousWithinAt,sub_zero] using hb
  have hright : ContinuousWithinAt x (Set.Icc s T) s := by
    have h := hfc.comp_of_eq (continuousWithinAt_id.sub_const s) hfmaps (sub_self s)
    simpa only [Function.comp_def, Pi.sub_apply, id_eq, add_sub_cancel] using h
  have hleft : ContinuousWithinAt x (Set.Icc 0 s) s := by
    have h := hbc.comp_of_eq (continuousWithinAt_const.sub continuousWithinAt_id)
      hbmaps (sub_self s)
    simpa only [Function.comp_def, Pi.sub_apply, id_eq, sub_sub_cancel] using h
  apply (hleft.union hright).mono
  intro t ht
  by_cases hts : t ≤ s
  · exact Or.inl ⟨ht.1,hts⟩
  · exact Or.inr ⟨le_of_not_ge hts,ht.2⟩

/-- The restarting deduction, parameterized by the independent general weak
uniqueness theorem. The final strong-continuity theorem instantiates this
helper with the proved uniqueness result. -/
theorem strong_state_continuity_of_uniqueness
    (huniq : HyperbolicWeakEnergyUniquenessSpec.WeakUniqueness (V := V) (H := H)) :
    HyperbolicWeakEnergyUniquenessSpec.StrongStateContinuity (V := V) (H := H) := by
  intro j T hT a α C ha u₀ v₀ f z
  by_cases hzero : T = 0
  · subst T
    simpa only [Set.Icc_self] using
      (show ContinuousOn z.displacement {0} ∧ ContinuousOn z.velocity {0} from
        ⟨continuousOn_singleton _ _,continuousOn_singleton _ _⟩)
  have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
  have hc : ∀ s ∈ Set.Icc 0 T,
      ContinuousWithinAt z.displacement (Set.Icc 0 T) s ∧
      ContinuousWithinAt z.velocity (Set.Icc 0 T) s := by
    intro s hs
    let ff := forwardForcing f hs.1
    let fb := backwardForcing f hs.2
    let zf := WeakEnergySolution.forwardTime j T hpos a u₀ v₀ f z s hs
    let zb := WeakEnergySolution.backwardTime j T hpos a u₀ v₀ f z s hs
    obtain ⟨cf,Kf,hcf,hKf,hexF⟩ := weak_existence j (T-s) (sub_nonneg.mpr hs.2)
      (fun r => a (s+r)) α C (FormHypotheses.forward j T s a α C ha hs)
    obtain ⟨wf,_,_,huf,hvf⟩ := hexF (z.displacement s) (z.velocity s) ff
    have heqF := (huniq j (T-s) (sub_nonneg.mpr hs.2) (fun r => a (s+r)) α C
      (FormHypotheses.forward j T s a α C ha hs) _ _ ff zf wf).1
    obtain ⟨cb,Kb,hcb,hKb,hexB⟩ := weak_existence j s hs.1
      (fun r => a (s-r)) α C (FormHypotheses.backward j T s a α C ha hs)
    obtain ⟨wb,_,_,hub,hvb⟩ := hexB (z.displacement s) (-z.velocity s) fb
    have heqB := (huniq j s hs.1 (fun r => a (s-r)) α C
      (FormHypotheses.backward j T s a α C ha hs) _ _ fb zb wb).1
    have huf' : Tendsto (fun r => z.displacement (s+r))
        (𝓝[Set.Icc 0 (T-s)] 0) (𝓝 (z.displacement s)) := by
      apply huf.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (heqF r hr).1.symm
    have hvf' : Tendsto (fun r => z.velocity (s+r))
        (𝓝[Set.Icc 0 (T-s)] 0) (𝓝 (z.velocity s)) := by
      apply hvf.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (heqF r hr).2.symm
    have hub' : Tendsto (fun r => z.displacement (s-r))
        (𝓝[Set.Icc 0 s] 0) (𝓝 (z.displacement s)) := by
      apply hub.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (heqB r hr).1.symm
    have hvb' : Tendsto (fun r => -z.velocity (s-r))
        (𝓝[Set.Icc 0 s] 0) (𝓝 (-z.velocity s)) := by
      apply hvb.congr'
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact (heqB r hr).2.symm
    have hvb'' : Tendsto (fun r => z.velocity (s-r))
        (𝓝[Set.Icc 0 s] 0) (𝓝 (z.velocity s)) := by
      simpa only [neg_neg] using hvb'.neg
    exact ⟨continuousWithinAt_of_forward_backward _ huf' hub',
      continuousWithinAt_of_forward_backward _ hvf' hvb''⟩
  exact ⟨fun s hs => (hc s hs).1,fun s hs => (hc s hs).2⟩

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

/-- A maximum argument for the integrated-test inequality on a short interval. -/
theorem integrated_test_short_interval {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [CompleteSpace E]
    {D α C M : ℝ} (hD : 0 ≤ D) (hα : 0 < α) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hsmall : C * D ^ 2 + 4 * M * D < min 1 α)
    {x : ℝ → E} {U : ℝ → F} {q : ℝ → ℝ → ℝ}
    (hx : ContinuousOn x (Set.Icc 0 D)) (hU : ContinuousOn U (Set.Icc 0 D))
    (hq : ∀ s ∈ Set.Icc 0 D, ∀ t ∈ Set.Icc 0 s,
      |q s t| ≤ M * ‖U s - U t‖ ^ 2)
    (he : ∀ s ∈ Set.Icc 0 D,
      ‖x s‖ ^ 2 + α * ‖U s‖ ^ 2 ≤
        C * ‖∫ t in 0..s, x t‖ ^ 2 + |∫ t in 0..s, q s t|) :
    ∀ t ∈ Set.Icc 0 D, x t = 0 ∧ U t = 0 := by
  let e : ℝ → ℝ := fun t => ‖x t‖ ^ 2 + ‖U t‖ ^ 2
  have hec : ContinuousOn e (Set.Icc 0 D) := (hx.norm.pow 2).add (hU.norm.pow 2)
  obtain ⟨s, hs, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr hD) hec
  let P : ℝ := e s
  have hP : 0 ≤ P := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hxt (t : ℝ) (ht : t ∈ Set.Icc 0 D) : ‖x t‖ ≤ Real.sqrt P := by
    apply (Real.le_sqrt (norm_nonneg _) hP).mpr
    have hm : e t ≤ P := hmax ht
    dsimp [e] at hm
    nlinarith [sq_nonneg ‖U t‖]
  have hUt (t : ℝ) (ht : t ∈ Set.Icc 0 D) : ‖U t‖ ≤ Real.sqrt P := by
    apply (Real.le_sqrt (norm_nonneg _) hP).mpr
    have hm : e t ≤ P := hmax ht
    dsimp [e] at hm
    nlinarith [sq_nonneg ‖x t‖]
  have hint : ‖∫ t in 0..s, x t‖ ^ 2 ≤ P * s ^ 2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s) (f := x) (fun t ht => by
      have ht' : t ∈ Set.Ioc 0 s := by simpa [Set.uIoc_of_le hs.1] using ht
      exact hxt t ⟨ht'.1.le, ht'.2.trans hs.2⟩)
    have hb' : ‖∫ t in 0..s, x t‖ ≤ Real.sqrt P * s := by
      simpa [abs_of_nonneg hs.1] using hb
    have hroot : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP
    calc
      _ ≤ (Real.sqrt P * s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb' 2
      _ = _ := by rw [mul_pow, hroot]
  have hqint : |∫ t in 0..s, q s t| ≤ 4 * M * P * s := by
    have hb : ∀ t ∈ Set.uIoc 0 s, ‖q s t‖ ≤ 4 * M * P := by
      intro t ht
      have ht' : t ∈ Set.Icc 0 s := by
        have ht'' : t ∈ Set.Ioc 0 s := by simpa [Set.uIoc_of_le hs.1] using ht
        exact ⟨ht''.1.le, ht''.2⟩
      have htD : t ∈ Set.Icc 0 D := ⟨ht'.1, ht'.2.trans hs.2⟩
      have hu : ‖U s - U t‖ ≤ 2 * Real.sqrt P := by
        calc
          _ ≤ ‖U s‖ + ‖U t‖ := norm_sub_le _ _
          _ ≤ 2 * Real.sqrt P := by linarith [hUt s hs, hUt t htD]
      have hu2 : ‖U s - U t‖ ^ 2 ≤ 4 * P := by
        nlinarith [Real.sq_sqrt hP, norm_nonneg (U s - U t), Real.sqrt_nonneg P]
      rw [Real.norm_eq_abs]
      calc
        _ ≤ M * ‖U s - U t‖ ^ 2 := hq s hs t ht'
        _ ≤ 4 * M * P := by nlinarith
    simpa [Real.norm_eq_abs, abs_of_nonneg hs.1] using
      intervalIntegral.norm_integral_le_of_norm_le_const hb
  have hmin : min 1 α * P ≤ ‖x s‖ ^ 2 + α * ‖U s‖ ^ 2 := by
    dsimp [P, e]
    nlinarith [mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) α) (sq_nonneg ‖x s‖),
      mul_le_mul_of_nonneg_right (min_le_right (1 : ℝ) α) (sq_nonneg ‖U s‖)]
  have hDs : s ^ 2 ≤ D ^ 2 := by nlinarith [hs.1, hs.2]
  have hbound : min 1 α * P ≤ (C * D ^ 2 + 4 * M * D) * P := by
    calc
      _ ≤ ‖x s‖ ^ 2 + α * ‖U s‖ ^ 2 := hmin
      _ ≤ C * ‖∫ t in 0..s, x t‖ ^ 2 + |∫ t in 0..s, q s t| := he s hs
      _ ≤ C * (P * s ^ 2) + 4 * M * P * s := by gcongr
      _ ≤ (C * D ^ 2 + 4 * M * D) * P := by
        nlinarith [mul_nonneg (mul_nonneg hC hP) (sub_nonneg.mpr hDs),
          mul_nonneg (mul_nonneg hM hP) (sub_nonneg.mpr hs.2)]
  have hP0 : P = 0 := by nlinarith
  intro t ht
  have hm : e t ≤ P := hmax ht
  dsimp [e] at hm
  constructor
  · apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖U t‖, norm_nonneg (x t)]
  · apply norm_eq_zero.mp
    nlinarith [sq_nonneg ‖x t‖, norm_nonneg (U t)]

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

theorem exists_integrated_test_radius (α C M : ℝ) (hα : 0 < α) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ D ∈ Set.Icc 0 δ,
      C * D ^ 2 + 4 * M * D < min 1 α := by
  have hm : 0 < min (1 : ℝ) α := lt_min zero_lt_one hα
  have hc : ContinuousAt (fun D : ℝ => C * D ^ 2 + 4 * M * D) 0 := by fun_prop
  have he : ∀ᶠ D in 𝓝 (0 : ℝ), C * D ^ 2 + 4 * M * D < min 1 α :=
    hc.eventually (gt_mem_nhds (by simpa using hm))
  obtain ⟨ε, hε, hb⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨ε / 2, by positivity, ?_⟩
  intro D hD
  apply hb
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hD.1] using
    (show D < ε by linarith [hD.2])

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyExistence
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem form_deriv_bound_of_secants (D M : ℝ) (hM : 0 ≤ M) (a : ℝ → Form V)
    (hsec : ∀ s ∈ Set.Icc 0 D, ∀ t ∈ Set.Icc 0 D,
      ‖a t - a s‖ ≤ M * ‖t - s‖)
    (t : ℝ) (ht : t ∈ Set.Icc 0 D) (x : V) :
    |derivWithin (fun r => a r x x) (Set.Icc 0 D) t| ≤ M * ‖x‖ ^ 2 := by
  have hlip : LipschitzOnWith ⟨M * ‖x‖ * ‖x‖, by positivity⟩
      (fun r => a r x x) (Set.Icc 0 D) := by
    apply lipschitzOnWith_iff_norm_sub_le.mpr
    intro s hs r hr
    have hb := (a s - a r).le_of_opNorm₂_le_of_le
      (hsec r hr s hs) (le_refl ‖x‖) (le_refl ‖x‖)
    change ‖a s x x - a r x x‖ ≤ _ at hb
    change ‖a s x x - a r x x‖ ≤ (M * ‖x‖ * ‖x‖) * ‖s-r‖
    convert hb using 1 <;> ring
  have hd := HyperbolicFormBoundsAndCarrier.norm_derivWithin_le_of_lipschitzOn ht hlip
  change ‖derivWithin (fun r => a r x x) (Set.Icc 0 D) t‖ ≤ M * ‖x‖ * ‖x‖ at hd
  simpa only [Real.norm_eq_abs, sq, mul_assoc] using hd

/-- The integrated test yields its endpoint identity for each prefix. -/
theorem homogeneous_primitive_energy (j : HilbertTriple V H) (D : ℝ) (hD : 0 < D)
    (a : ℝ → Form V) (α C : ℝ) (ha : FormHypotheses j D a α C)
    (z : WeakEnergySolution j D a 0 0 (0 : timeLpValue H 2 D)) :
    let U : ℝ → V := fun t => ∫ r in 0..t, z.displacement r
    ∀ s ∈ Set.Icc 0 D,
      ‖j.embedding (z.displacement s)‖ ^ 2 + a 0 (U s) (U s) =
        -(∫ r in 0..s, derivWithin (fun t =>
          a t (U s - U r) (U s - U r)) (Set.Icc 0 D) r) := by
  dsimp only
  let U : ℝ → V := fun t => ∫ r in 0..t, z.displacement r
  let : IsFiniteMeasure (timeMeasureValue D) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 D)))
  have h0 : (0 : ℝ) ∈ Set.Icc 0 D := ⟨le_rfl, hD.le⟩
  have h1 : D ∈ Set.Icc 0 D := ⟨hD.le, le_rfl⟩
  have hui := intervalIntegrable_of_timeIntegrable D
    (z.displacement_mem.integrable (by simp)) ⟨0,h0⟩ ⟨D,h1⟩
  intro s hs
  by_cases hs0 : s = 0
  · simp [hs0, z.initial_displacement, U]
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  let zs := weakEnergySolution_restrict j hs.2 a 0 0 (0 : timeLpValue H 2 D) z
  obtain ⟨hgi, hge⟩ := weak_solution_integrated_acceleration j s hspos a 0 0
    (timeLp_restrict hs.2 (0 : timeLpValue H 2 D)) zs
  have hge' : ‖j.embedding (z.displacement s)‖ ^ 2 =
      2 * ∫ r in 0..s, z.acceleration r (U s - U r) := by
    simpa only [zs, weakEnergySolution_restrict, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0),
      sub_zero, zero_add, zero_mul, mul_zero, add_zero, zero_apply] using hge
  obtain ⟨hai, hdi, hae⟩ := varying_form_primitive_identity D hD.le a ha.scalarC1
    ha.symmetric hui 0 s h0 hs
  have hgi' : IntervalIntegrable (fun r => z.acceleration r (U s - U r)) volume 0 s := hgi
  have hneg : (∫ r in 0..s, z.acceleration r (U s - U r)) =
      -(∫ r in 0..s, a r (z.displacement r) (U s - U r)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae_restrict
    have hq := (ae_mono (timeMeasureValue_mono hs.2)) z.equation
    have hf := (ae_mono (timeMeasureValue_mono hs.2))
      (Lp.coeFn_zero (E := H) (p := 2) (μ := timeMeasureValue D))
    have hq' : ∀ᵐ r ∂volume.restrict (Set.Ioo 0 s),
        z.acceleration r + a r (z.displacement r) = 0 := by
      filter_upwards [hq,hf] with r hr hfr
      simpa only [hfr, Pi.zero_apply, map_zero] using hr
    rw [restrict_Ioo_eq_restrict_Ioc] at hq'
    have he : ∀ᵐ r ∂volume.restrict (Set.uIoc 0 s),
        z.acceleration r + a r (z.displacement r) = 0 := by
      simpa only [Set.uIoc_of_le hs.1] using hq'
    filter_upwards [he] with r hr
    have hr' := congrArg (fun L : StrongDual ℝ V => L (U s - U r)) hr
    simp only [add_apply, zero_apply] at hr'
    linarith
  have hae' : 2 * (∫ r in 0..s, a r (z.displacement r) (U s - U r)) =
      a 0 (U s) (U s) + ∫ r in 0..s,
        derivWithin (fun t => a t (U s - U r) (U s - U r)) (Set.Icc 0 D) r := by
    simpa only [U, intervalIntegral.integral_same, sub_zero] using hae
  change ‖j.embedding (z.displacement s)‖ ^ 2 + a 0 (U s) (U s) = _
  rw [hneg] at hge'
  linarith

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyExistence
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem short_homogeneous_zero (j : HilbertTriple V H) (D : ℝ) (hD : 0 < D)
    (a : ℝ → Form V) (α C M : ℝ) (ha : FormHypotheses j D a α C) (hM : 0 ≤ M)
    (hsec : ∀ s ∈ Set.Icc 0 D, ∀ t ∈ Set.Icc 0 D,
      ‖a t - a s‖ ≤ M * ‖t - s‖)
    (hsmall : C * D ^ 2 + 4 * M * D < min 1 α)
    (z : WeakEnergySolution j D a 0 0 (0 : timeLpValue H 2 D)) :
    ∀ t ∈ Set.Icc 0 D, z.displacement t = 0 ∧ z.velocity t = 0 := by
  let U : ℝ → V := fun t => ∫ r in 0..t, z.displacement r
  let q : ℝ → ℝ → ℝ := fun s r => derivWithin
    (fun t => a t (U s - U r) (U s - U r)) (Set.Icc 0 D) r
  let : IsFiniteMeasure (timeMeasureValue D) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Set.Ioo 0 D)))
  have h0 : (0 : ℝ) ∈ Set.Icc 0 D := ⟨le_rfl,hD.le⟩
  have h1 : D ∈ Set.Icc 0 D := ⟨hD.le,le_rfl⟩
  have hui := intervalIntegrable_of_timeIntegrable D
    (z.displacement_mem.integrable (by simp)) ⟨0,h0⟩ ⟨D,h1⟩
  have hUc : ContinuousOn U (Set.Icc 0 D) := by
    simpa only [Set.uIcc_of_le hD.le] using
      (FiniteEnergy.vector_primitive_ac hui).continuousOn
  have hxc := (primitive_representatives j D hD a 0 0 0 z).1
  have hid := homogeneous_primitive_energy j D hD a α C ha z
  have he : ∀ s ∈ Set.Icc 0 D,
      ‖j.embedding (z.displacement s)‖ ^ 2 + α * ‖U s‖ ^ 2 ≤
        C * ‖∫ t in 0..s, j.embedding (z.displacement t)‖ ^ 2 + |∫ t in 0..s, q s t| := by
    intro s hs
    have hg := ha.garding 0 h0 (U s)
    have hi := hid s hs
    have hcomm : (∫ t in 0..s, j.embedding (z.displacement t)) = j.embedding (U s) :=
      j.embedding.intervalIntegral_comp_comm
        (hui.mono_set (Set.uIcc_subset_Icc h0 hs |>.trans (by simp [Set.uIcc_of_le hD.le])))
    rw [hcomm]
    change ‖j.embedding (z.displacement s)‖ ^ 2 + a 0 (U s) (U s) =
      -(∫ r in 0..s, q s r) at hi
    linarith [neg_le_abs (∫ r in 0..s, q s r)]
  have hz := integrated_test_short_interval hD.le ha.alpha_pos ha.shift_nonneg hM
    hsmall hxc hUc (q := q) (fun s hs t ht =>
      form_deriv_bound_of_secants D M hM a hsec t ⟨ht.1, ht.2.trans hs.2⟩ (U s-U t)) he
  have huz : ∀ t ∈ Set.Icc 0 D, z.displacement t = 0 := by
    intro t ht
    apply j.injective
    simpa only [map_zero] using (hz t ht).1
  have hvz := (weak_solution_velocity_zero_of_displacement_zero j D hD a 0 0 0 z huz).1
  exact fun t ht => ⟨huz t ht,hvz t ht⟩

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyUniquenessSpec HyperbolicWeakEnergyExistence
variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def WeakEnergySolution.change_initial (j : HilbertTriple V H) (T : ℝ)
    (a : ℝ → Form V) (u₀ u₁ : V) (v₀ v₁ : H) (f : timeLpValue H 2 T)
    (z : WeakEnergySolution j T a u₀ v₀ f) (hu : u₀ = u₁) (hv : v₀ = v₁) :
    WeakEnergySolution j T a u₁ v₁ f where
  displacement := z.displacement
  velocity := z.velocity
  acceleration := z.acceleration
  displacement_mem := z.displacement_mem
  pivot_displacement_mem := z.pivot_displacement_mem
  velocity_mem := z.velocity_mem
  dual_velocity_mem := z.dual_velocity_mem
  acceleration_mem := z.acceleration_mem
  displacement_derivative := z.displacement_derivative
  velocity_derivative := z.velocity_derivative
  equation := z.equation
  displacement_weak := z.displacement_weak
  velocity_weak := z.velocity_weak
  initial_displacement := z.initial_displacement.trans hu
  initial_velocity := z.initial_velocity.trans hv

theorem state_uniqueness_from_short_intervals (j : HilbertTriple V H)
    (T : ℝ) (hT : 0 ≤ T) (a : ℝ → Form V) (α C M δ : ℝ)
    (ha : FormHypotheses j T a α C) (hδ : 0 < δ)
    (hsec : ∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, ‖a t - a s‖ ≤ M * ‖t-s‖)
    (hshort : ∀ D : ℝ, 0 < D → D ≤ δ → ∀ aD : ℝ → Form V,
      FormHypotheses j D aD α C →
      (∀ s ∈ Set.Icc 0 D, ∀ t ∈ Set.Icc 0 D, ‖aD t - aD s‖ ≤ M * ‖t-s‖) →
      ∀ q : WeakEnergySolution j D aD 0 0 (0 : timeLpValue H 2 D),
      ∀ t ∈ Set.Icc 0 D, q.displacement t = 0 ∧ q.velocity t = 0)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z w : WeakEnergySolution j T a u₀ v₀ f) :
    ∀ t ∈ Set.Icc 0 T,
      z.displacement t = w.displacement t ∧ z.velocity t = w.velocity t := by
  by_cases hzero : T = 0
  · subst T
    exact (zero_time_uniqueness j a u₀ v₀ f z w).1
  have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
  let x : ℝ → V × H := fun t =>
    (z.displacement t - w.displacement t, z.velocity t - w.velocity t)
  have hx0 : x 0 = 0 := by simp [x,z.initial_displacement,w.initial_displacement,
    z.initial_velocity,w.initial_velocity]
  have hx : ∀ t ∈ Set.Icc 0 T, x t = 0 := by
    apply global_zero_of_local_zero T δ hT hδ x hx0
    intro τ hτ hτ0 t ht htδ
    by_cases heq : t = τ
    · simpa only [heq] using hτ0
    have hD : 0 < t-τ := sub_pos.mpr (lt_of_le_of_ne ht.1 (Ne.symm heq))
    have hDδ : t-τ ≤ δ := by linarith
    have hDmax : t-τ ≤ T-τ := sub_le_sub_right ht.2 τ
    have hzu : w.displacement τ = z.displacement τ := by
      have h := congrArg Prod.fst hτ0
      exact (sub_eq_zero.mp h).symm
    have hzv : w.velocity τ = z.velocity τ := by
      have h := congrArg Prod.snd hτ0
      exact (sub_eq_zero.mp h).symm
    let zf := WeakEnergySolution.forwardTime j T hpos a u₀ v₀ f z τ hτ
    let wf₀ := WeakEnergySolution.forwardTime j T hpos a u₀ v₀ f w τ hτ
    let wf := WeakEnergySolution.change_initial j (T-τ) (fun r => a (τ+r))
      (w.displacement τ) (z.displacement τ) (w.velocity τ) (z.velocity τ)
      (forwardForcing f hτ.1) wf₀ hzu hzv
    let q := weakEnergySolution_sub j (T-τ) (fun r => a (τ+r))
      (z.displacement τ) (z.velocity τ) (forwardForcing f hτ.1) zf wf
    let qD := weakEnergySolution_restrict_homogeneous j hDmax (fun r => a (τ+r)) q
    have haF := FormHypotheses.forward j T τ a α C ha hτ
    have hsub : Set.Icc 0 (t-τ) ⊆ Set.Icc 0 (T-τ) := Set.Icc_subset_Icc_right hDmax
    have haD : FormHypotheses j (t-τ) (fun r => a (τ+r)) α C :=
      ⟨fun u v => (haF.scalarC1 u v).mono hsub,
        fun r hr => haF.symmetric r (hsub hr), ha.alpha_pos, ha.shift_nonneg,
        fun r hr => haF.garding r (hsub hr)⟩
    have hsecD : ∀ r ∈ Set.Icc 0 (t-τ), ∀ s ∈ Set.Icc 0 (t-τ),
        ‖a (τ+s) - a (τ+r)‖ ≤ M * ‖s-r‖ := by
      intro r hr s hs
      have hrT : τ+r ∈ Set.Icc 0 T := by
        constructor <;> linarith [hτ.1,hr.1,hr.2,ht.2]
      have hsT : τ+s ∈ Set.Icc 0 T := by
        constructor <;> linarith [hτ.1,hs.1,hs.2,ht.2]
      simpa only [add_sub_add_left_eq_sub] using hsec _ hrT _ hsT
    obtain ⟨hu,hv⟩ := hshort (t-τ) hD hDδ (fun r => a (τ+r)) haD hsecD
      qD (t-τ) ⟨hD.le,le_rfl⟩
    have heval : τ+(t-τ) = t := by ring
    change z.displacement (τ+(t-τ)) - w.displacement (τ+(t-τ)) = 0 at hu
    change z.velocity (τ+(t-τ)) - w.velocity (τ+(t-τ)) = 0 at hv
    simp only [heval] at hu hv
    exact Prod.ext hu hv
  intro t ht
  have h := hx t ht
  exact ⟨sub_eq_zero.mp (congrArg Prod.fst h),sub_eq_zero.mp (congrArg Prod.snd h)⟩

theorem weak_uniqueness_from_short_intervals (j : HilbertTriple V H)
    (T : ℝ) (hT : 0 ≤ T) (a : ℝ → Form V) (α C M δ : ℝ)
    (ha : FormHypotheses j T a α C) (hδ : 0 < δ)
    (hsec : ∀ s ∈ Set.Icc 0 T, ∀ t ∈ Set.Icc 0 T, ‖a t - a s‖ ≤ M * ‖t-s‖)
    (hshort : ∀ D : ℝ, 0 < D → D ≤ δ → ∀ aD : ℝ → Form V,
      FormHypotheses j D aD α C →
      (∀ s ∈ Set.Icc 0 D, ∀ t ∈ Set.Icc 0 D, ‖aD t - aD s‖ ≤ M * ‖t-s‖) →
      ∀ q : WeakEnergySolution j D aD 0 0 (0 : timeLpValue H 2 D),
      ∀ t ∈ Set.Icc 0 D, q.displacement t = 0 ∧ q.velocity t = 0)
    (u₀ : V) (v₀ : H) (f : timeLpValue H 2 T)
    (z w : WeakEnergySolution j T a u₀ v₀ f) :
    (∀ t ∈ Set.Icc 0 T,
      z.displacement t = w.displacement t ∧ z.velocity t = w.velocity t) ∧
    z.acceleration =ᵐ[timeMeasureValue T] w.acceleration := by
  have hstate := state_uniqueness_from_short_intervals j T hT a α C M δ ha hδ hsec
    hshort u₀ v₀ f z w
  have hu : z.displacement =ᵐ[timeMeasureValue T] w.displacement := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hstate t (Set.Ioo_subset_Icc_self ht)).1
  exact ⟨hstate,(derivatives_eq_of_displacement_ae j T a u₀ v₀ f z w hu).2⟩

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness

namespace ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyUniquenessSpec HyperbolicWeakEnergyExistence

variable {V : Type u} {H : Type v}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Uniqueness in the original weak energy class, with equality of both
weak representatives at every time and acceleration equality almost everywhere. -/
theorem weak_uniqueness : WeakUniqueness (V := V) (H := H) := by
  intro j T hT a α C ha u₀ v₀ f z w
  obtain ⟨M,hM,hsec⟩ := HyperbolicFormBoundsAndCarrier.form_secants_bounded T a ha.scalarC1
  obtain ⟨δ,hδ,hsmall⟩ := exists_integrated_test_radius α C M ha.alpha_pos
  apply weak_uniqueness_from_short_intervals j T hT a α C M δ ha hδ hsec ?_ u₀ v₀ f z w
  intro D hD hDδ aD haD hsecD q
  exact short_homogeneous_zero j D hD aD α C M haD hM hsecD
    (hsmall D ⟨hD.le,hDδ⟩) q

/-- The strong initial traces of the accepted existence construction,
restarted in both time directions and identified by weak uniqueness, give
strong state continuity at every point, including both endpoints. -/
theorem strong_state_continuity : StrongStateContinuity (V := V) (H := H) :=
  strong_state_continuity_of_uniqueness weak_uniqueness

end ExpandedFA.Evolution.HyperbolicWeakEnergyUniqueness
