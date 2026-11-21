import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.Counterexamples
import MathGenome.Internal.MultivariableAnalysis.D04.C06.MeasureBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C06.ExceptionalSets
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Topology MeasureTheory
namespace D04.Counterexamples
open Specs.D04.C08.Counterexamples.Model
open Specs.D04.C06.DarbouxIntegral.Model

/-- The coordinate identification preserves the Euclidean norm, and hence volume. -/
def scalarEquiv : E 1 ≃ₗᵢ[ℝ] ℝ where
  toFun x := x 0
  invFun := scalarPoint
  left_inv x := by ext i; fin_cases i; rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' x := by
    change ‖x 0‖ = ‖x‖
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs]

lemma interval_carrier {a b : ℝ} (hab : a ≤ b) :
    carrier (interval a b) = scalarEquiv ⁻¹' Icc a b := by
  ext x
  simp only [interval, min_eq_left hab, max_eq_right hab, carrier, intervalBox,
    scalarPoint, mem_preimage, mem_Icc]
  exact ⟨fun h => h 0, fun h i => by fin_cases i; exact h⟩

theorem closedIntegral_bridge : Specs.D04.C08.Counterexamples.closedIntegral_bridgeType := by
  intro f a b hab hf
  have hc := interval_carrier hab
  have hfun : (carrier (interval a b)).indicator (fun x : E 1 => f (x 0)) =
      ((Icc a b).indicator f) ∘ scalarEquiv := by
    ext x
    rw [hc]
    change ((scalarEquiv ⁻¹' Icc a b).indicator (f ∘ scalarEquiv)) x = _
    simp only [indicator, mem_preimage, Function.comp_apply]
    split_ifs <;> rfl
  obtain ⟨_, hi, he⟩ := MeasureBridge.box_bridge _ _ hf
  have hm := scalarEquiv.measurePreserving
  have hem := scalarEquiv.toMeasurableEquiv.measurableEmbedding
  have hfi := (hm.integrable_comp_emb hem).mp (hfun ▸ hi)
  refine ⟨(integrable_indicator_iff measurableSet_Icc).mp hfi, ?_⟩
  change Darboux.integral _ _ hf = _
  rw [he, ← integral_indicator (NullCovers.isClosed_carrier _).measurableSet, hfun]
  simp only [Function.comp_apply]
  rw [hm.integral_comp hem, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

lemma riemannOn_continuous {f : ℝ → ℝ} (hf : Continuous f) (a b : ℝ) :
    RiemannOn f a b :=
  ExceptionalSets.integrable_continuous (by norm_num) _ _
    (hf.comp (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0)).continuousOn

lemma closedIntegral_zero (a b : ℝ) : closedIntegral (fun _ => 0) a b = 0 := by
  exact (Darboux.integral_const (interval a b) 0 (Darboux.integrable_const _ _)).trans (by simp)

lemma closedIntegral_const (c a b : ℝ) (hab : a ≤ b) :
    closedIntegral (fun _ => c) a b = (b - a) * c := by
  rw [(closedIntegral_bridge _ _ _ hab (riemannOn_continuous continuous_const _ _)).2]
  simp [mul_comm]

lemma spike_eventually_zero (x : ℝ) : ∀ᶠ t in 𝓝[>] (0 : ℝ), spike x t = 0 := by
  by_cases hx : 0 < x
  · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hx)] with t ht
    simp [spike, not_lt.mpr ht.le]
  · exact Eventually.of_forall (fun t => by simp [spike, hx])

theorem spike_pointwise : Specs.D04.C08.Counterexamples.spike_pointwiseType := by
  intro x
  exact tendsto_const_nhds.congr' ((spike_eventually_zero x).mono (fun _ h => h.symm))

theorem spike_zero : Specs.D04.C08.Counterexamples.spike_zeroType := by
  have hz : (fun x => spike x 0) = (fun _ => 0) := by
    funext x; simp [spike]
  exact ⟨congrFun hz, by rw [hz]; exact closedIntegral_zero _ _⟩

lemma spike_continuousAt {t x : ℝ} (hx : x ≠ 0) (ht : x ≠ t) :
    ContinuousAt (fun y => spike y t) x := by
  have h₀ : ∀ᶠ y in 𝓝 x, (0 < y ↔ 0 < x) := by
    rcases lt_or_gt_of_ne hx with h | h
    · filter_upwards [eventually_lt_nhds h] with y hy
      simp [not_lt.mpr h.le, not_lt.mpr hy.le]
    · filter_upwards [eventually_gt_nhds h] with y hy
      simp [h, hy]
  have h₁ : ∀ᶠ y in 𝓝 x, (y < t ↔ x < t) := by
    rcases lt_or_gt_of_ne ht with h | h
    · filter_upwards [eventually_lt_nhds h] with y hy
      simp [h, hy]
    · filter_upwards [eventually_gt_nhds h] with y hy
      simp [not_lt.mpr h.le, not_lt.mpr hy.le]
  have hc : ContinuousAt (fun _ : ℝ => spike x t) x := continuousAt_const
  apply hc.congr_of_eventuallyEq
  filter_upwards [h₀, h₁] with y hy hy'
  simp only [spike, hy, hy']

theorem spike_integrable : Specs.D04.C08.Counterexamples.spike_integrableType := by
  intro t ht
  apply (DiscontinuityCriterion.integrable_iff_null_discontinuitySet
    (by norm_num) _ _ (Darboux.bounded_of_abs_le (M := |t⁻¹|) ?_)).mpr
  · apply NullCovers.null_mono (T := {scalarPoint 0, scalarPoint t}) ?_
      (NullCovers.countable_null (by norm_num) (Set.to_countable _))
    rintro x ⟨hx, hdisc⟩
    by_contra hx'
    have hzero : x 0 ≠ 0 := by
      intro h
      apply hx'
      left
      ext i; fin_cases i; exact h
    have ht' : x 0 ≠ t := by
      intro h
      apply hx'
      right
      ext i; fin_cases i; exact h
    exact hdisc ((ContinuousAt.comp (f := fun y : E 1 => y 0) (spike_continuousAt hzero ht')
      (scalarEquiv.continuous.continuousAt)).continuousWithinAt)
  · intro x _
    dsimp [spike]
    split_ifs <;> simp

lemma spike_indicator (t : ℝ) : (fun x => spike x t) = (Ioo 0 t).indicator (fun _ => t⁻¹) := by
  funext x
  simp only [spike, indicator, mem_Ioo]

theorem spike_mass : Specs.D04.C08.Counterexamples.spike_massType := by
  intro t ht
  rw [(closedIntegral_bridge _ 0 1 (by norm_num)
    (spike_integrable t ⟨ht.1.le, ht.2.le⟩)).2,
    spike_indicator, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_indicator measurableSet_Ioc, Set.indicator_indicator]
  have hi : Ioc (0 : ℝ) 1 ∩ Ioo 0 t = Ioo 0 t :=
    inter_eq_right.mpr (fun x hx => ⟨hx.1, hx.2.le.trans ht.2.le⟩)
  rw [hi, integral_indicator measurableSet_Ioo]
  simp [ht.1.le, ht.1.ne']

private def poly (u : ℝ) : ℝ := 30 * (u - 1)^2 * (2 - u)^2
private def polyD (u : ℝ) : ℝ := 60 * (u - 1) * (2 - u)^2 - 60 * (u - 1)^2 * (2 - u)
private def psiD (u : ℝ) : ℝ := if u ∈ Icc 1 2 then polyD u else 0

private lemma poly_deriv (u : ℝ) : HasDerivAt poly (polyD u) u := by
  convert (((((hasDerivAt_id u).sub_const 1).pow 2).const_mul 30).mul
    (((hasDerivAt_id u).const_sub 2).pow 2)) using 1 <;> (try funext z) <;> dsimp [poly, polyD] <;> ring

private lemma psi_eq_poly {u : ℝ} (hu : u ∈ Icc 1 2) : psi u = poly u := by
  simp [psi, hu, poly]

lemma psi_zero_of_le {u : ℝ} (hu : u ≤ 1) : psi u = 0 := by
  by_cases h : u = 1
  · subst u; norm_num [psi]
  · simp [psi, not_le.mpr (lt_of_le_of_ne hu h)]

lemma psi_zero_of_ge {u : ℝ} (hu : 2 ≤ u) : psi u = 0 := by
  by_cases h : u = 2
  · subst u; norm_num [psi]
  · simp [psi, not_le.mpr (lt_of_le_of_ne hu (Ne.symm h))]

private lemma psi_deriv_one : HasDerivAt psi 0 1 := by
  have hleft : HasDerivWithinAt psi 0 (Iic 1) 1 :=
    (hasDerivAt_const (1 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
      (fun u hu => psi_zero_of_le hu) (psi_zero_of_le le_rfl)
  have hright : HasDerivWithinAt psi 0 (Icc 1 2) 1 := by
    have hp : HasDerivAt poly 0 1 := by simpa [polyD] using poly_deriv 1
    exact hp.hasDerivWithinAt.congr (fun _ hu => psi_eq_poly hu)
      (psi_eq_poly (by norm_num))
  apply (hleft.union hright).hasDerivAt
  exact Filter.mem_of_superset (Iic_mem_nhds (by norm_num : (1 : ℝ) < 2))
    (fun u hu => by by_cases h : u ≤ 1; exact Or.inl h; exact Or.inr ⟨(le_of_not_ge h), hu⟩)

private lemma psi_deriv_two : HasDerivAt psi 0 2 := by
  have hright : HasDerivWithinAt psi 0 (Ici 2) 2 :=
    (hasDerivAt_const (2 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
      (fun u hu => psi_zero_of_ge hu) (psi_zero_of_ge le_rfl)
  have hleft : HasDerivWithinAt psi 0 (Icc 1 2) 2 := by
    have hp : HasDerivAt poly 0 2 := by simpa [polyD] using poly_deriv 2
    exact hp.hasDerivWithinAt.congr (fun _ hu => psi_eq_poly hu)
      (psi_eq_poly (by norm_num))
  apply (hleft.union hright).hasDerivAt
  exact Filter.mem_of_superset (Ici_mem_nhds (by norm_num : (1 : ℝ) < 2))
    (fun u hu => by by_cases h : 2 ≤ u; exact Or.inr h; exact Or.inl ⟨hu, le_of_not_ge h⟩)

private lemma psi_deriv (u : ℝ) : HasDerivAt psi (psiD u) u := by
  by_cases h₁ : u = 1
  · subst u; simpa [psiD, polyD] using psi_deriv_one
  by_cases h₂ : u = 2
  · subst u; simpa [psiD, polyD] using psi_deriv_two
  by_cases hu : u ∈ Icc 1 2
  · have hmem : Ioo (1 : ℝ) 2 ∈ 𝓝 u := Ioo_mem_nhds
        (lt_of_le_of_ne hu.1 (Ne.symm h₁)) (lt_of_le_of_ne hu.2 h₂)
    rw [psiD, ite_eq_left hu]
    exact (poly_deriv u).congr_of_eventuallyEq
      (Filter.mem_of_superset hmem (fun _ hv => psi_eq_poly ⟨hv.1.le, hv.2.le⟩))
  · rw [psiD, ite_eq_right hu]
    apply (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
    have hor : u < 1 ∨ 2 < u := by simpa only [mem_Icc, not_and_or, not_le] using hu
    rcases hor with h | h
    · exact (eventually_lt_nhds h).mono (fun _ hv => psi_zero_of_le hv.le)
    · exact (eventually_gt_nhds h).mono (fun _ hv => psi_zero_of_ge hv.le)

lemma psi_contDiff : ContDiff ℝ 1 psi := by
  have hd : Continuous psiD := by
    apply Continuous.if ?_ (show Continuous polyD by unfold polyD; fun_prop) continuous_const
    intro u hu
    change u ∈ frontier (Icc (1 : ℝ) 2) at hu
    have hh : u = 1 ∨ u = 2 := by
      simpa only [frontier_Icc (by norm_num : (1 : ℝ) ≤ 2), mem_insert_iff, mem_singleton_iff] using hu
    rcases hh with rfl | rfl <;> norm_num [polyD]
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun u => (psi_deriv u).differentiableAt, ?_⟩
  have he : deriv psi = psiD := funext (fun u => (psi_deriv u).deriv)
  rw [he]
  exact hd

lemma psi_nonneg (u : ℝ) : 0 ≤ psi u := by
  dsimp [psi]
  split_ifs <;> positivity

lemma psi_support : Function.support psi ⊆ Icc 1 2 := by
  intro u hu
  by_contra h
  exact hu (by simp [psi, h])

lemma psi_integrable : MeasureTheory.Integrable psi := by
  have hs : HasCompactSupport psi := HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (1 : ℝ) 2))
      (fun u hu => by simp [psi, hu])
  exact psi_contDiff.continuous.integrable_of_hasCompactSupport hs

lemma psi_integral : (∫ u, psi u) = 1 := by
  have he : psi = (Icc 1 2).indicator poly := by
    funext u; simp only [psi, indicator, poly]; split_ifs <;> rfl
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (1 : ℝ) ≤ 2)]
  let P (u : ℝ) := 6*u^5 - 45*u^4 + 130*u^3 - 180*u^2 + 120*u
  have hp (u : ℝ) : HasDerivAt P (poly u) u := by
    convert ((((((hasDerivAt_id u).pow 5).const_mul 6).sub
      (((hasDerivAt_id u).pow 4).const_mul 45)).add
      (((hasDerivAt_id u).pow 3).const_mul 130)).sub
      (((hasDerivAt_id u).pow 2).const_mul 180)).add
      ((hasDerivAt_id u).const_mul 120) using 1 <;> (try funext z) <;> dsimp [P, poly] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hp u)
    (show IntervalIntegrable poly volume 1 2 from (by unfold poly; fun_prop : Continuous poly).intervalIntegrable _ _)]
  norm_num [P]

theorem psi_properties : Specs.D04.C08.Counterexamples.psi_propertiesType :=
  ⟨psi_contDiff, psi_nonneg, psi_support, psi_integrable, psi_integral⟩

theorem escape_regular : Specs.D04.C08.Counterexamples.escape_regularType := by
  have hc (t : ℝ) : Continuous (fun x => escape x t) :=
    continuous_const.mul (psi_contDiff.continuous.comp (continuous_const.mul continuous_id))
  exact ⟨hc, fun t => riemannOn_continuous (hc t)⟩

theorem escape_local_zero : Specs.D04.C08.Counterexamples.escape_local_zeroType := by
  intro A hA
  refine ⟨1 / (A + 1), by positivity, ?_⟩
  intro t ht x hx
  have h : t * (A + 1) < 1 := (lt_div_iff₀ (by positivity : 0 < A + 1)).mp ht.2
  have hx' : t * x ≤ 1 := by nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr hx.2)]
  simp [escape, psi_zero_of_le hx']

theorem escape_uniform : Specs.D04.C08.Counterexamples.escape_uniformType := by
  intro A hA
  obtain ⟨δ, hδ, hz⟩ := escape_local_zero A hA
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds hδ)] with t ht htδ x hx
  simpa [hz t ⟨ht, htδ⟩ x hx] using hε

lemma escape_zero_of_nonpos {x t : ℝ} (ht : 0 ≤ t) (hx : x ≤ 0) : escape x t = 0 := by
  have h : t * x ≤ 1 := (mul_nonpos_of_nonneg_of_nonpos ht hx).trans (by norm_num)
  simp [escape, psi_zero_of_le h]

theorem escape_deriv : Specs.D04.C08.Counterexamples.escape_derivType := by
  intro x hx
  obtain ⟨δ, hδ, hz⟩ := escape_local_zero x hx
  apply HasDerivAt.hasDerivWithinAt
  apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [eventually_lt_nhds hδ] with t ht
  by_cases ht₀ : 0 < t
  · exact hz t ⟨ht₀, ht⟩ x ⟨hx, le_rfl⟩
  · have h : t * x ≤ 1 := (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt ht₀) hx).trans (by norm_num)
    simp [escape, psi_zero_of_le h]

lemma escape_integrable {t : ℝ} (ht : 0 < t) : MeasureTheory.Integrable (fun x => escape x t) :=
  (psi_integrable.comp_mul_left' ht.ne').const_mul t

lemma escape_integral {t : ℝ} (ht : 0 < t) : (∫ x, escape x t) = 1 := by
  simp only [escape, integral_const_mul, Measure.integral_comp_mul_left, psi_integral,
    smul_eq_mul, mul_one]
  rw [abs_of_pos (inv_pos.mpr ht)]
  exact mul_inv_cancel₀ ht.ne'

theorem escape_mass : Specs.D04.C08.Counterexamples.escape_massType := by
  intro t ht
  refine ⟨(escape_integrable ht).integrableOn, ?_⟩
  change (∫ x in Ioi 0, escape x t) = 1
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioi (0 : ℝ))
    (f := fun x : ℝ => escape x t)
    (fun x hx => escape_zero_of_nonpos ht.le (le_of_not_gt hx))]
  exact escape_integral ht

theorem escape_improper : Specs.D04.C08.Counterexamples.escape_improperType := by
  intro t ht
  have hl := intervalIntegral_tendsto_integral_Ioi 0 (escape_mass t ht).1
    tendsto_natCast_atTop_atTop
  change Tendsto _ _ (𝓝 (halflineMass t)) at hl
  rw [(escape_mass t ht).2] at hl
  apply hl.congr
  intro n
  exact (closedIntegral_bridge _ _ _ (Nat.cast_nonneg n) (escape_regular.2 t 0 n)).2.symm

theorem escape_zero_mass : Specs.D04.C08.Counterexamples.escape_zero_massType := by
  have hz (x : ℝ) : escape x 0 = 0 := by simp [escape]
  refine ⟨hz, ?_, ?_⟩
  · simp [halflineMass, hz]
  · intro n
    simp only [hz]
    exact closedIntegral_zero _ _

theorem escape_discontinuous : Specs.D04.C08.Counterexamples.escape_discontinuousType := by
  intro hc
  have hl : Tendsto halflineMass (𝓝[>] 0) (𝓝 0) := by
    have hh := hc.mono Ioi_subset_Ici_self
    change Tendsto halflineMass (𝓝[>] 0) (𝓝 (halflineMass 0)) at hh
    simpa only [escape_zero_mass.2.1] using hh
  have he : halflineMass =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 1) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (escape_mass t ht).2
  have hl' : Tendsto halflineMass (𝓝[>] 0) (𝓝 1) := tendsto_const_nhds.congr' he.symm
  have h : (0 : ℝ) = 1 := tendsto_nhds_unique hl hl'
  norm_num at h

theorem escape_no_uniform_tails : Specs.D04.C08.Counterexamples.escape_no_uniform_tailsType := by
  intro δ hδ R hR
  obtain ⟨η, hη, hz⟩ := escape_local_zero R hR
  let t := min δ η / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have htδ : t < δ := by dsimp [t]; linarith [min_le_left δ η]
  have htη : t < η := by dsimp [t]; linarith [min_le_right δ η]
  refine ⟨t, ⟨ht, htδ⟩, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero ?_]
  · exact escape_integral ht
  · intro x hx
    have hxR : x ≤ R := le_of_not_gt hx
    by_cases hx₀ : 0 ≤ x
    · exact hz t ⟨ht, htη⟩ x ⟨hx₀, hxR⟩
    · exact escape_zero_of_nonpos ht.le (le_of_not_ge hx₀)

theorem cauchy_regular : Specs.D04.C08.Counterexamples.cauchy_regularType := by
  intro p
  have hc : Continuous (fun x => cauchy x p) := by
    apply Continuous.inv₀ (by fun_prop)
    intro x
    exact ne_of_gt (by positivity : (0 : ℝ) < 1 + (x - p)^2)
  exact ⟨hc, fun x => by dsimp [cauchy]; positivity,
    riemannOn_continuous hc⟩

theorem cauchy_mass : Specs.D04.C08.Counterexamples.cauchy_massType := by
  intro p
  exact ⟨integrable_inv_one_add_sq.comp_sub_right p,
    (integral_sub_right_eq_self (fun x : ℝ => (1 + x^2)⁻¹) p).trans
      integral_univ_inv_one_add_sq⟩

theorem cauchy_improper : Specs.D04.C08.Counterexamples.cauchy_improperType := by
  intro p
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hl := intervalIntegral_tendsto_integral (cauchy_mass p).1
    (tendsto_neg_atTop_atBot.comp hn) hn
  rw [(cauchy_mass p).2] at hl
  apply hl.congr
  intro n
  exact (closedIntegral_bridge (fun x => cauchy x p) (-(n : ℝ)) (n : ℝ)
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) ((cauchy_regular p).2.2 _ _)).2.symm

theorem cauchy_compact_bound : Specs.D04.C08.Counterexamples.cauchy_compact_boundType := by
  intro K hK
  obtain ⟨M, hM⟩ := (hK.image continuous_abs).bddAbove
  let B := max M 0
  have hB : 0 ≤ B := le_max_right _ _
  refine ⟨2 + 2 * B^2, by positivity, ?_⟩
  intro p hp x
  have hpB : |p| ≤ B := (hM ⟨p, hp, rfl⟩).trans (le_max_left _ _)
  have hpsq : p^2 ≤ B^2 := by nlinarith [sq_abs p, mul_nonneg (sub_nonneg.mpr hpB) (add_nonneg hB (abs_nonneg p))]
  have hd : (0 : ℝ) < 1 + (x - p)^2 := by positivity
  have hx : (0 : ℝ) < 1 + x^2 := by positivity
  rw [cauchy, inv_eq_one_div]
  apply (div_le_div_iff₀ hd hx).mpr
  nlinarith [sq_nonneg (x - 2*p), mul_nonneg (sq_nonneg B) (sq_nonneg (x - p))]

lemma cauchy_exterior_identity (R p : ℝ) :
    exteriorMass R p = Real.pi - ∫ x in Icc (-R) R, cauchy x p := by
  have h := integral_add_compl (s := Icc (-R) R) measurableSet_Icc (cauchy_mass p).1
  rw [(cauchy_mass p).2] at h
  dsimp [exteriorMass]
  linarith

lemma cauchy_exterior_limit : Tendsto (fun R => exteriorMass R 0) atTop (𝓝 0) := by
  have hl := intervalIntegral_tendsto_integral (cauchy_mass 0).1
    tendsto_neg_atTop_atBot tendsto_id
  rw [(cauchy_mass 0).2] at hl
  have hs : Tendsto (fun R : ℝ => Real.pi - ∫ x in -R..R, cauchy x 0) atTop
      (𝓝 (Real.pi - Real.pi)) := tendsto_const_nhds.sub hl
  rw [sub_self] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with R hR
  rw [cauchy_exterior_identity, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -R ≤ R)]

theorem cauchy_compact_tails : Specs.D04.C08.Counterexamples.cauchy_compact_tailsType := by
  intro K hK ε hε
  obtain ⟨C, hC, hb⟩ := cauchy_compact_bound K hK
  have hl : Tendsto (fun R => C * exteriorMass R 0) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul cauchy_exterior_limit
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hl.eventually (eventually_lt_nhds hε))
  refine ⟨max N 0, le_max_right _ _, ?_⟩
  intro R hR p hp
  have hi : exteriorMass R p ≤ C * exteriorMass R 0 := by
    rw [exteriorMass, exteriorMass, ← integral_const_mul]
    apply integral_mono (cauchy_mass p).1.integrableOn ((cauchy_mass 0).1.const_mul C).integrableOn
    intro x
    simpa only [cauchy, sub_zero, div_eq_mul_inv] using hb p hp x
  exact hi.trans_lt (hN R ((le_max_left _ _).trans hR))

lemma cauchy_exterior_nonneg (R p : ℝ) : 0 ≤ exteriorMass R p :=
  integral_nonneg (fun x => ((cauchy_regular p).2.1 x).le)

lemma cauchy_exterior_nat (n : ℕ) (p : ℝ) :
    exteriorMass n p = Real.pi - closedIntegral (fun x => cauchy x p) (-(n : ℝ)) n := by
  rw [cauchy_exterior_identity, (closedIntegral_bridge (fun x => cauchy x p) (-(n : ℝ)) n
    (by linarith [Nat.cast_nonneg (α := ℝ) n]) ((cauchy_regular p).2.2 _ _)).2,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [Nat.cast_nonneg (α := ℝ) n] : -(n : ℝ) ≤ n)]

theorem cauchy_compact_riemann_tails :
    Specs.D04.C08.Counterexamples.cauchy_compact_riemann_tailsType := by
  intro K hK ε hε
  obtain ⟨R, hR, hb⟩ := cauchy_compact_tails K hK (ε/2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_ge R
  refine ⟨N, ?_⟩
  intro n hn m hm p hp
  have hn' : R ≤ (n : ℝ) := hN.trans (by exact_mod_cast hn)
  have hm' : R ≤ (m : ℝ) := hn'.trans (by exact_mod_cast hm)
  have hb₁ := hb n hn' p hp
  have hb₂ := hb m hm' p hp
  have he : closedIntegral (fun x => cauchy x p) (-↑m) m - closedIntegral (fun x => cauchy x p) (-↑n) n =
      exteriorMass n p - exteriorMass m p := by
    rw [cauchy_exterior_nat, cauchy_exterior_nat]
    ring
  rw [he]
  have h := abs_sub_le (exteriorMass n p) 0 (exteriorMass m p)
  rw [sub_zero, zero_sub, abs_neg,
    abs_of_nonneg (cauchy_exterior_nonneg n p), abs_of_nonneg (cauchy_exterior_nonneg m p)] at h
  linarith

lemma cauchy_center_limit (x : ℝ) :
    Tendsto (fun p => cauchy x p) atTop (𝓝 0) := by
  have hlin : Tendsto (fun p : ℝ => p - x) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b + x)] with p hp
    linarith
  have hsq := (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hlin
  have hd : Tendsto (fun p : ℝ => 1 + (p - x)^2) atTop atTop :=
    tendsto_const_nhds.add_atTop hsq
  apply (tendsto_inv_atTop_zero.comp hd).congr
  intro p
  change (1 + (p - x)^2)⁻¹ = (1 + (x - p)^2)⁻¹
  rw [sub_sq_comm p x]

lemma cauchy_le_one (x p : ℝ) : cauchy x p ≤ 1 := by
  dsimp [cauchy]
  exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg (x - p)])

lemma cauchy_proper_center_limit (R : ℝ) :
    Tendsto (fun p => ∫ x in Icc (-R) R, cauchy x p) atTop (𝓝 0) := by
  have hlim : Tendsto (fun p => ∫ x in Icc (-R) R, cauchy x p) atTop
      (𝓝 (∫ _ : ℝ in Icc (-R) R, (0 : ℝ))) := by
    apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
    · exact Eventually.of_forall (fun p => (cauchy_regular p).1.aestronglyMeasurable.restrict)
    · exact Eventually.of_forall (fun p => ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg ((cauchy_regular p).2.1 x).le]
        exact cauchy_le_one x p))
    · exact integrableOn_const (by simp only [Real.volume_Icc]; finiteness)
    · exact ae_of_all _ cauchy_center_limit
  simpa only [integral_zero] using hlim

theorem cauchy_escape_mass : Specs.D04.C08.Counterexamples.cauchy_escape_massType := by
  intro R hR ε hε A
  have hs : ∀ᶠ p : ℝ in atTop, (∫ x in Icc (-R) R, cauchy x p) < ε :=
    (cauchy_proper_center_limit R).eventually (eventually_lt_nhds hε)
  obtain ⟨p, hp, hs⟩ := ((eventually_gt_atTop A).and hs).exists
  refine ⟨p, hp, ?_⟩
  rw [cauchy_exterior_identity]
  linarith

theorem cauchy_no_uniform_tails : Specs.D04.C08.Counterexamples.cauchy_no_uniform_tailsType := by
  intro h
  obtain ⟨N, hN, hb⟩ := h (Real.pi / 2) (by positivity)
  obtain ⟨p, _, hp⟩ := cauchy_escape_mass N hN (Real.pi / 2) (by positivity) 0
  have hsmall := hb N le_rfl p
  linarith

theorem escape_no_uniform_riemann_tails :
    Specs.D04.C08.Counterexamples.escape_no_uniform_riemann_tailsType := by
  intro δ hδ h
  obtain ⟨N, hN⟩ := h (1/2) (by norm_num)
  obtain ⟨t, ht, htail⟩ := escape_no_uniform_tails δ hδ N (Nat.cast_nonneg N)
  have he := intervalIntegral.integral_interval_add_Ioi (a := (0 : ℝ)) (b := (N : ℝ))
    (escape_mass t ht.1).1 (escape_integrable ht.1).integrableOn
  rw [htail, ← (closedIntegral_bridge _ _ _ (Nat.cast_nonneg N) (escape_regular.2 t 0 N)).2] at he
  change closedIntegral (fun x => escape x t) 0 N + 1 = halflineMass t at he
  rw [(escape_mass t ht.1).2] at he
  have hz : closedIntegral (fun x => escape x t) 0 N = 0 := by linarith
  have hs : ∀ᶠ m : ℕ in atTop, (1 : ℝ)/2 < closedIntegral (fun x => escape x t) 0 m :=
    (escape_improper t ht.1).eventually (eventually_gt_nhds (by norm_num : (1 : ℝ)/2 < 1))
  obtain ⟨m, hm, hs⟩ := ((eventually_ge_atTop N).and hs).exists
  have hc := hN N le_rfl m hm t ⟨ht.1.le, ht.2.le⟩
  rw [hz, sub_zero] at hc
  exact (not_lt_of_ge ((le_abs_self _).trans hc.le)) hs

theorem cauchy_no_uniform_riemann_tails :
    Specs.D04.C08.Counterexamples.cauchy_no_uniform_riemann_tailsType := by
  intro h
  obtain ⟨N, hN⟩ := h (Real.pi / 2) (by positivity)
  obtain ⟨p, _, hp⟩ := cauchy_escape_mass N (Nat.cast_nonneg N)
    (Real.pi / 4) (by positivity) 0
  have he := cauchy_exterior_nat N p
  have hl := (cauchy_improper p).sub_const (closedIntegral (fun x => cauchy x p) (-↑N) N)
  rw [← he] at hl
  have hs : ∀ᶠ m : ℕ in atTop, Real.pi / 2 <
      closedIntegral (fun x => cauchy x p) (-↑m) m - closedIntegral (fun x => cauchy x p) (-↑N) N :=
    hl.eventually (eventually_gt_nhds (by linarith [Real.pi_pos] : Real.pi/2 < exteriorMass N p))
  obtain ⟨m, hm, hs⟩ := ((eventually_ge_atTop N).and hs).exists
  have hc := hN N le_rfl m hm p
  exact (not_lt_of_ge ((le_abs_self _).trans hc.le)) hs

theorem dominated_convergence : Specs.D04.C08.Counterexamples.dominated_convergenceType := by
  intro F f M hF hM hb hl
  exact tendsto_integral_of_dominated_convergence M hF hM hb hl

theorem riemann_applicability : Specs.D04.C08.Counterexamples.riemann_applicabilityType :=
  ⟨MeasureBridge.box_bridge, MeasureBridge.region_bridge, MeasureBridge.improper_bridge⟩

/- Names for the canonical objects in the independent specification. -/
abbrev interval := Specs.D04.C08.Counterexamples.Model.interval
abbrev RiemannOn := Specs.D04.C08.Counterexamples.Model.RiemannOn
abbrev closedIntegral := Specs.D04.C08.Counterexamples.Model.closedIntegral
abbrev spike := Specs.D04.C08.Counterexamples.Model.spike
abbrev psi := Specs.D04.C08.Counterexamples.Model.psi
abbrev escape := Specs.D04.C08.Counterexamples.Model.escape
abbrev cauchy := Specs.D04.C08.Counterexamples.Model.cauchy
abbrev halflineMass := Specs.D04.C08.Counterexamples.Model.halflineMass
abbrev exteriorMass := Specs.D04.C08.Counterexamples.Model.exteriorMass

end D04.Counterexamples
