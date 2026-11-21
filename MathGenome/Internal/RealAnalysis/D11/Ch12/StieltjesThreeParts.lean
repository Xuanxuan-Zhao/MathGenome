import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.StieltjesThreeParts
import MathGenome.Internal.RealAnalysis.D11.Ch12.AcStieltjesEquivalence
import MathGenome.Internal.RealAnalysis.D11.Ch15.LebesgueDecompositionFiniteTarget
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

noncomputable section
open scoped Classical
open Set Filter MeasureTheory Metric
open scoped Topology ENNReal
namespace D11.Ch12.StieltjesThreeParts
open Specs.D11.Ch12.StieltjesThreeParts
open ScalarStieltjesCorrespondence
open Ch14.ScalarInterfaces Ch14.TotalVariation Ch15.AbsoluteContinuity

variable {K : Type*} [RCLike K]

lemma atoms_countable (ν : VectorMeasure ℝ K) [IsFiniteMeasure ν.variation] :
    (atoms ν).Countable := by
  have hc := Measure.countable_meas_pos_of_disjoint_iUnion
    (μ := ν.variation) (fun x : ℝ => measurableSet_singleton x)
    (fun x y hxy => disjoint_singleton.mpr hxy)
  simpa only [VectorMeasure.variation_apply_singleton, enorm_pos, atoms] using hc

lemma measurableSet_atoms (ν : VectorMeasure ℝ K) [IsFiniteMeasure ν.variation] :
    MeasurableSet (atoms ν) := (atoms_countable ν).measurableSet

lemma atoms_summable (ν : VectorMeasure ℝ K) [IsFiniteMeasure ν.variation] :
    Summable (fun p : atoms ν => ‖ν {p.val}‖) := by
  have hle : (∑' p : atoms ν, ν.variation {p.val}) ≤ ν.variation univ :=
    tsum_measure_le_measure_univ
      (fun _ => (measurableSet_singleton _).nullMeasurableSet)
      (fun p q hpq => (disjoint_singleton.mpr (Subtype.coe_injective.ne hpq)).aedisjoint)
  have hfin := ne_top_of_le_ne_top (measure_ne_top ν.variation univ) hle
  simpa only [VectorMeasure.variation_apply_singleton, ← ofReal_norm,
    ENNReal.toReal_ofReal (norm_nonneg _)] using ENNReal.summable_toReal hfin

lemma restrict_singleton (ν : VectorMeasure ℝ K) (D : Set ℝ)
    (hD : MeasurableSet D) (x : ℝ) :
    ν.restrict D {x} = if x ∈ D then ν {x} else 0 := by
  rw [VectorMeasure.restrict_apply ν hD (measurableSet_singleton x)]
  by_cases hx : x ∈ D <;> simp [hx]

lemma atomless_complement (ν : VectorMeasure ℝ K) [IsFiniteMeasure ν.variation] :
    IsAtomless (ν.restrict (atoms ν)ᶜ) := by
  intro x
  rw [restrict_singleton ν _ (measurableSet_atoms ν).compl]
  by_cases hx : x ∈ atoms ν
  · simp [hx]
  · simpa [hx] using (not_not.mp hx : ν {x} = 0)

lemma supported_restrict (ν : VectorMeasure ℝ K) (D : Set ℝ) (hD : MeasurableSet D) :
    (ν.restrict D).variation Dᶜ = 0 := by
  rw [VectorMeasure.variation_restrict hD, Measure.restrict_apply hD.compl,
    compl_inter_self, measure_empty]

lemma atomless_countable_null (ν : VectorMeasure ℝ K) (hν : IsAtomless ν)
    {D : Set ℝ} (hD : D.Countable) : ν.variation D = 0 := by
  letI : NullSingletonClass ν.variation := ⟨fun x => by
    simp [VectorMeasure.variation_apply_singleton, hν x]⟩
  exact hD.measure_zero ν.variation

lemma ac_atomless (ν : VectorMeasure ℝ K) (hν : ν.variation ≪ volume) : IsAtomless ν := by
  intro x
  have hz : ν.variation {x} = 0 := hν (measure_singleton x)
  simpa only [VectorMeasure.variation_apply_singleton, enorm_eq_zero] using hz

lemma native_scalar_singular (ν η : VectorMeasure ℝ K)
    (h : ν.variation ⟂ₘ η.variation) : scalarSingular ν η := by
  obtain ⟨D, hD, hν, hη⟩ := h
  refine ⟨Dᶜ, hD.compl, ?_, ?_⟩
  · rw [compl_compl, ← totalVariation_apply ν D hD]; exact hν
  · rw [← totalVariation_apply η Dᶜ hD.compl]; exact hη

lemma native_positive_singular (ν : VectorMeasure ℝ K)
    (h : scalarPositiveSingular ν volume) : ν.variation ⟂ₘ volume := by
  obtain ⟨D, hD, hν, hvol⟩ := h
  refine ⟨Dᶜ, hD.compl, ?_, ?_⟩
  · rw [← totalVariation_apply ν Dᶜ hD.compl] at hν
    exact hν
  · simpa using hvol

/-- Restriction to countably many points is the unconditional Dirac series. -/
lemma restrict_hasSum (ν : VectorMeasure ℝ K) {D : Set ℝ} (hD : D.Countable)
    (E : Set ℝ) (hE : MeasurableSet E) :
    HasSum (fun p : D => if p.val ∈ E then ν {p.val} else 0) (ν.restrict D E) := by
  classical
  letI := hD.toEncodable
  let A : D → Set ℝ := fun p => E ∩ {p.val}
  have hA : ∀ p, MeasurableSet (A p) := fun p => hE.inter (measurableSet_singleton _)
  have hd : Pairwise (fun p q => Disjoint (A p) (A q)) := by
    intro p q hpq
    exact (disjoint_singleton.mpr (Subtype.coe_injective.ne hpq)).mono
      inter_subset_right inter_subset_right
  have hu : (⋃ p : D, A p) = E ∩ D := by
    ext x
    simp only [A, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    constructor
    · rintro ⟨p, hx, rfl⟩; exact ⟨hx, p.property⟩
    · rintro ⟨hx, hD⟩; exact ⟨⟨x, hD⟩, hx, rfl⟩
  have hv : ∀ p : D, ν (A p) = if p.val ∈ E then ν {p.val} else 0 := by
    intro p
    by_cases hp : p.val ∈ E
    · change ν (E ∩ {p.val}) = _
      rw [if_pos hp, inter_eq_right.mpr (singleton_subset_iff.mpr hp)]
    · change ν (E ∩ {p.val}) = _
      rw [if_neg hp, inter_singleton_eq_empty.mpr hp, ν.empty]
  simpa only [hv, hu, VectorMeasure.restrict_apply ν hD.measurableSet hE] using
    (VectorMeasure.hasSum_of_disjoint_iUnion (v := ν) hA hd)

lemma supported_restrict_eq (ν : VectorMeasure ℝ K) {D : Set ℝ}
    (hD : MeasurableSet D) (hz : ν.variation Dᶜ = 0) : ν.restrict D = ν := by
  have hc : ν.restrict Dᶜ = 0 := by
    apply VectorMeasure.ext
    intro E hE
    rw [VectorMeasure.restrict_apply ν hD.compl hE]
    have hzero := (totalVariation_null_iff ν Dᶜ hD.compl).mp hz
    exact hzero _ (hE.inter hD.compl) inter_subset_right
  have hsum := VectorMeasure.restrict_add_restrict_compl (v := ν) hD
  simpa only [hc, add_zero] using hsum

/-- Countably supported scalar measures are determined by singleton values. -/
lemma discrete_ext (ν η : VectorMeasure ℝ K) (hν : IsDiscrete ν) (hη : IsDiscrete η)
    (heq : ∀ x : ℝ, ν {x} = η {x}) : ν = η := by
  obtain ⟨D, hD, hzD⟩ := hν
  obtain ⟨A, hA, hzA⟩ := hη
  have hU := hD.union hA
  have hv : ν.restrict (D ∪ A) = ν := supported_restrict_eq ν hU.measurableSet
    (measure_mono_null (compl_subset_compl.mpr subset_union_left) hzD)
  have hw : η.restrict (D ∪ A) = η := supported_restrict_eq η hU.measurableSet
    (measure_mono_null (compl_subset_compl.mpr subset_union_right) hzA)
  apply VectorMeasure.ext
  intro E hE
  have hsumν := restrict_hasSum ν hU E hE
  have hsumη := restrict_hasSum η hU E hE
  have hvsum : HasSum (fun p : ↥(D ∪ A) => if p.val ∈ E then η {p.val} else 0)
      (ν.restrict (D ∪ A) E) := by
    simpa only [heq] using hsumν
  simpa only [hv, hw] using hvsum.unique hsumη

/-- The measure-level decomposition, before any differentiability arguments. -/
lemma measure_decomposition (ν : VectorMeasure ℝ K) [IsFiniteMeasure ν.variation] :
    ∃ a s, IsDecomposition ν (ν.restrict (atoms ν)) a s := by
  letI : IsFiniteMeasure (totalVariation ν) := ‹IsFiniteMeasure ν.variation›
  let D := atoms ν
  have hD : MeasurableSet D := measurableSet_atoms ν
  let r := ν.restrict Dᶜ
  have hrfin : IsFiniteMeasure r.variation :=
    Ch15.LebesgueDecompositionFiniteTarget.restrict_finite_variation ν Dᶜ hD.compl
  letI : IsFiniteMeasure (Specs.D11.Ch14.TotalVariation.totalVariation_value r) := hrfin
  obtain ⟨B, hB, haFin, hsFin, hsum, ha, hs, _⟩ :=
    Ch15.LebesgueDecompositionFiniteTarget.finite_variation_decomposition r volume
  let a := r.restrict Bᶜ
  let s := r.restrict B
  have hr : IsAtomless r := atomless_complement ν
  have hsatom : IsAtomless s := by
    intro x
    rw [restrict_singleton r B hB.1]
    split_ifs
    · exact hr x
    · rfl
  have hatom := ac_atomless a ha
  have hdFin : IsFiniteMeasure (ν.restrict D).variation :=
    Ch15.LebesgueDecompositionFiniteTarget.restrict_finite_variation ν D hD
  have hd : IsDiscrete (ν.restrict D) := ⟨D, atoms_countable ν, supported_restrict ν D hD⟩
  have hsumν : ν = ν.restrict D + a + s := by
    rw [add_assoc, ← hsum]
    exact (VectorMeasure.restrict_add_restrict_compl hD).symm
  have hda : scalarSingular (ν.restrict D) a := by
    apply native_scalar_singular
    refine ⟨Dᶜ, hD.compl, supported_restrict ν D hD, ?_⟩
    simpa using atomless_countable_null a hatom (atoms_countable ν)
  have hds : scalarSingular (ν.restrict D) s := by
    apply native_scalar_singular
    refine ⟨Dᶜ, hD.compl, supported_restrict ν D hD, ?_⟩
    simpa using atomless_countable_null s hsatom (atoms_countable ν)
  have has : scalarSingular a s := by
    apply native_scalar_singular
    exact ⟨B, hB.1, ha hB.2.1, supported_restrict r B hB.1⟩
  exact ⟨a, s, hdFin, haFin, hsFin, hsumν, hd, ha, hs, hsatom, hda, hds, has⟩

lemma decomposition_unique (ν d a s d' a' s' : VectorMeasure ℝ K)
    (h : IsDecomposition ν d a s) (h' : IsDecomposition ν d' a' s') :
    d' = d ∧ a' = a ∧ s' = s := by
  rcases h with ⟨_, _, _, hsum, hd, ha, hs, hatom, _⟩
  rcases h' with ⟨_, _, _, hsum', hd', ha', hs', hatom', _⟩
  have hd_eq : d' = d := by
    apply discrete_ext d' d hd' hd
    intro x
    have he := congrArg (fun v : VectorMeasure ℝ K => v {x}) (hsum'.symm.trans hsum)
    simpa only [add_apply, ac_atomless a ha x, ac_atomless a' ha' x,
      hatom x, hatom' x, add_zero] using he
  refine ⟨hd_eq, ?_⟩
  have hr : a + s = a' + s' := by
    rw [hd_eq] at hsum'
    have he := hsum.symm.trans hsum'
    exact add_left_cancel (a := d) (by simpa only [add_assoc] using he)
  exact Ch15.ACSingularZero.decomposition_unique (a + s) volume a' s' a s
    hr rfl ha' hs' ha hs

lemma atomic_data (ν : VectorMeasure ℝ K) [IsFiniteMeasure ν.variation] :
    AtomicData ν (ν.restrict (atoms ν)) := by
  have hsum := restrict_hasSum ν (atoms_countable ν)
  have hcum (x : ℝ) : cumulative (ν.restrict (atoms ν)) x =
      ∑' p : atoms ν, if p.val ≤ x then ν {p.val} else 0 :=
    (hsum (Iic x) measurableSet_Iic).tsum_eq.symm
  have hdirac (E : Set ℝ) (hE : MeasurableSet E) :
      HasSum (fun p : atoms ν => VectorMeasure.dirac p.val (ν {p.val}) E)
        (ν.restrict (atoms ν) E) := by
    have heq : (fun p : atoms ν => VectorMeasure.dirac p.val (ν {p.val}) E) =
        (fun p : atoms ν => if p.val ∈ E then ν {p.val} else 0) := by
      funext p
      by_cases hp : p.val ∈ E
      · simp [VectorMeasure.dirac_apply_of_mem hE hp, hp]
      · simp [hp]
    rw [heq]
    exact hsum E hE
  refine ⟨atoms_countable ν, atoms_summable ν, hdirac, hcum, ?_⟩
  have hb (p : atoms ν) (x : ℝ) :
      ‖if p.val ≤ x then ν {p.val} else 0‖ ≤ ‖ν {p.val}‖ := by
    split_ifs <;> simp
  have hu := tendstoUniformly_tsum (atoms_summable ν) hb
  have heq : cumulative (ν.restrict (atoms ν)) =
      (fun x => ∑' p : atoms ν, if p.val ≤ x then ν {p.val} else 0) := funext hcum
  change TendstoUniformly _ (cumulative (ν.restrict (atoms ν))) atTop
  rw [heq]
  exact hu

lemma cumulative_continuous_of_atomless (ν : VectorMeasure ℝ K)
    [IsFiniteMeasure ν.variation] (ha : IsAtomless ν) : Continuous (cumulative ν) := by
  have hF := cumulative_properties ν ‹IsFiniteMeasure ν.variation›
  apply continuous_iff_continuousAt.mpr
  intro x
  have hat := measure_atom (cumulative ν) hF x
  rw [measure_cumulative ν ‹IsFiniteMeasure ν.variation›] at hat
  have hleft : (cumulative ν).leftLim x = cumulative ν x :=
    (sub_eq_zero.mp (hat.symm.trans (ha x))).symm
  apply continuousAt_iff_continuous_left'_right'.mpr
  constructor
  · have ht := hF.boundedVariationOn.tendsto_leftLim x
    rwa [hleft] at ht
  · exact (hF.2.1 x).mono Ioi_subset_Ici_self

lemma discrete_singular (d : VectorMeasure ℝ K) (hd : IsDiscrete d) :
    d.variation ⟂ₘ volume := by
  obtain ⟨D, hD, hz⟩ := hd
  exact ⟨Dᶜ, hD.measurableSet.compl, hz, by simpa using hD.measure_zero volume⟩


lemma singular_closed_density (σ : Measure ℝ) [IsFiniteMeasure σ]
    (hs : σ ⟂ₘ volume) : ∀ᵐ x ∂volume,
    Tendsto (fun r : ℝ => (σ (closedBall x r)).toReal / (2 * r))
      (𝓝[>] 0) (𝓝 0) := by
  let v := IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure ℝ) 0
  filter_upwards [v.ae_eventually_measure_zero_of_singular hs] with x hx
  have hc := hx.comp (IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt
    (volume : Measure ℝ) (K := 0) (fun _ : ℝ => x) id tendsto_id
    (Eventually.of_forall (fun r => by simp)))
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hc
  simp only [ENNReal.toReal_zero] at hreal
  apply hreal.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  change (σ (closedBall x r) / volume (closedBall x r)).toReal = _
  rw [ENNReal.toReal_div, Real.volume_closedBall,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num) hr.le)]

lemma increment_bound (ν : VectorMeasure ℝ K) [IsFiniteMeasure ν.variation]
    (x y : ℝ) : ‖cumulative ν y - cumulative ν x‖ ≤
      (ν.variation (closedBall x |y - x|)).toReal := by
  have hI {a b : ℝ} (ha : x - |y-x| ≤ a) (hb : b ≤ x + |y-x|) :
      Ioc a b ⊆ closedBall x |y-x| := by
    rw [Real.closedBall_eq_Icc]
    exact fun z hz => ⟨ha.trans hz.1.le, hz.2.trans hb⟩
  rcases le_total x y with hxy | hyx
  · rw [cumulative_sub ν hxy]
    exact (VectorMeasure.norm_measure_le_variation (μ := ν)).trans
      (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono
        (hI (by linarith [abs_nonneg (y-x)]) (by linarith [le_abs_self (y-x)]))))
  · rw [← norm_neg, neg_sub, cumulative_sub ν hyx]
    exact (VectorMeasure.norm_measure_le_variation (μ := ν)).trans
      (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono
        (hI (by linarith [neg_abs_le (y-x)]) (by linarith [abs_nonneg (y-x)]))))

lemma singular_derivative (ν : VectorMeasure ℝ K) [IsFiniteMeasure ν.variation]
    (hs : ν.variation ⟂ₘ volume) :
    ∀ᵐ x ∂volume, HasDerivAt (cumulative ν) 0 x := by
  filter_upwards [singular_closed_density ν.variation hs] with x hx
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht := (hx.comp tendsto_abs_nhdsNE_zero).const_mul 2
  simp only [mul_zero] at ht
  apply squeeze_zero (fun h => norm_nonneg _) ?_ ht
  intro h
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  have hb := increment_bound ν x (x+h)
  simp only [add_sub_cancel_left] at hb
  calc
    |h|⁻¹ * ‖cumulative ν (x+h) - cumulative ν x‖ ≤
        |h|⁻¹ * (ν.variation (closedBall x |h|)).toReal :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (abs_nonneg _))
    _ = 2 * ((ν.variation (closedBall x |h|)).toReal / (2 * |h|)) := by
      by_cases hh : h = 0
      · simp [hh]
      · field_simp

/-- Transfer the source measure classes to their normalized BV functions. -/
lemma function_data (ν d a s : VectorMeasure ℝ K) (h : IsDecomposition ν d a s)
    (hac : AbsolutelyContinuous (cumulative a)) : FunctionData ν d a s := by
  rcases h with ⟨hdFin, haFin, hsFin, hsum, hd, _, hs, hsc, _⟩
  letI : IsFiniteMeasure d.variation := hdFin
  letI : IsFiniteMeasure a.variation := haFin
  letI : IsFiniteMeasure s.variation := hsFin
  refine ⟨cumulative_properties d hdFin, cumulative_properties a haFin,
    cumulative_properties s hsFin, ?_, hac, cumulative_continuous_of_atomless s hsc,
    singular_derivative d (discrete_singular d hd),
    singular_derivative s (native_positive_singular s hs)⟩
  intro x
  exact congrArg (fun v : VectorMeasure ℝ K => v (Iic x)) hsum

lemma complete_of_ac (ν : VectorMeasure ℝ K) [IsFiniteMeasure ν.variation]
    (hac : ∀ a : VectorMeasure ℝ K, IsFiniteMeasure a.variation →
      a.variation ≪ volume → AbsolutelyContinuous (cumulative a)) : CompleteResult ν := by
  obtain ⟨a, s, h⟩ := measure_decomposition ν
  refine ⟨ν.restrict (atoms ν), a, s, h, atomic_data ν,
    function_data ν _ a s h (hac a h.2.1 h.2.2.2.2.2.1), ?_⟩
  intro d' a' s' h'
  exact decomposition_unique ν _ a s d' a' s' h h'

theorem real_three_parts : Specs.D11.Ch12.StieltjesThreeParts.real_three_parts := by
  intro ν
  letI : IsFiniteMeasure ν.variation := signed_finite ν
  apply complete_of_ac ν
  intro a ha hac
  have hF := cumulative_properties a ha
  apply (AcStieltjesEquivalence.measure_ac_real (cumulative a) hF ?_).1
  change (stieltjesMeasure (cumulative a)).variation ≪ volume
  rwa [measure_cumulative a ha]

theorem complex_three_parts : Specs.D11.Ch12.StieltjesThreeParts.complex_three_parts := by
  intro ν
  letI : IsFiniteMeasure ν.variation := complex_finite ν
  apply complete_of_ac ν
  intro a ha hac
  have hF := cumulative_properties a ha
  apply (AcStieltjesEquivalence.measure_ac_complex (cumulative a) hF ?_).1
  change (stieltjesMeasure (cumulative a)).variation ≪ volume
  rwa [measure_cumulative a ha]

theorem nbv_real_three_parts : Specs.D11.Ch12.StieltjesThreeParts.nbv_real_three_parts := by
  intro F hF
  exact ⟨real_three_parts (stieltjesMeasure F), cumulative_measure F hF⟩

theorem nbv_complex_three_parts : Specs.D11.Ch12.StieltjesThreeParts.nbv_complex_three_parts := by
  intro F hF
  exact ⟨complex_three_parts (stieltjesMeasure F), cumulative_measure F hF⟩

end D11.Ch12.StieltjesThreeParts
