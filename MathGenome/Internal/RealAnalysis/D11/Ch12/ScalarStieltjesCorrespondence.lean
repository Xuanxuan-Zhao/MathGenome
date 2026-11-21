import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.ScalarStieltjesCorrespondence
import MathGenome.Internal.RealAnalysis.D11.Ch12.PositiveStieltjes
import MathGenome.Internal.RealAnalysis.D11.Ch14.TotalVariation
import Mathlib.Tactic.Linarith

/-! Normalized scalar Stieltjes correspondence, paper.tex:3915–3980.
The forward construction uses the library's extension of the interval content
of a BV function. We separately verify the regularity of the classical initial
variation, including legitimacy of the normalized real Jordan generators.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace D11.Ch12.ScalarStieltjesCorrespondence

variable {E : Type*} [NormedAddCommGroup E]

def NBV (F : ℝ → E) : Prop :=
  GloballyBV F ∧ (∀ x, ContinuousWithinAt F (Ici x) x) ∧ Tendsto F atBot (𝓝 0)

def cumulative (ν : VectorMeasure ℝ E) (x : ℝ) : E := ν (Iic x)

noncomputable def initialVariation (F : ℝ → E) (x : ℝ) : ℝ≥0∞ :=
  ⨆ a : ℝ, variation F a x

open scoped Classical in
noncomputable def stieltjesMeasure [CompleteSpace E] (F : ℝ → E) : VectorMeasure ℝ E :=
  if h : BoundedVariationOn F univ then h.vectorMeasure else 0

noncomputable def positiveComponent (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((initialVariation F x).toReal + F x) / 2

noncomputable def negativeComponent (F : ℝ → ℝ) (x : ℝ) : ℝ :=
  ((initialVariation F x).toReal - F x) / 2

lemma NBV.boundedVariationOn {F : ℝ → E} (hF : NBV F) : BoundedVariationOn F univ :=
  (globallyBV_iff_boundedVariationOn F).mp hF.1

lemma NBV.rightLim_eq {F : ℝ → E} (hF : NBV F) : F.rightLim = F :=
  funext fun x => (hF.2.1 x).rightLim_eq

lemma initialVariation_bridge (F : ℝ → E) (x : ℝ) :
    initialVariation F x = eVariationOn F (Iic x) := by
  simp only [initialVariation, variation_eq_eVariationOn]
  apply le_antisymm
  · exact iSup_le fun a => eVariationOn.mono F Icc_subset_Iic_self
  · rw [eVariationOn]
    apply iSup_le
    rintro ⟨n, u, hu, hm⟩
    apply (eVariationOn.sum_le_of_monotoneOn_Iic (hu.monotoneOn _) ?_).trans
    · exact le_iSup_of_le (u 0) le_rfl
    · intro i hi
      exact ⟨hu (Nat.zero_le i), hm i⟩

lemma initialVariation_finite {F : ℝ → E} (hF : GloballyBV F) (x : ℝ) :
    initialVariation F x < ⊤ := by
  rw [initialVariation_bridge]
  exact ((globallyBV_iff_boundedVariationOn F).mp hF).mono (subset_univ _) |>.lt_top

lemma initialVariation_add {F : ℝ → E} {x y : ℝ} (hxy : x ≤ y) :
    initialVariation F y = initialVariation F x + eVariationOn F (Icc x y) := by
  simp only [initialVariation_bridge]
  have hu : Iic x ∪ Icc x y = Iic y := by ext z; simp; grind
  rw [← hu]
  exact eVariationOn.union F isGreatest_Iic ⟨⟨le_rfl, hxy⟩, Icc_subset_Ici_self⟩

lemma initialVariation_tendsto_atBot {F : ℝ → E} (hF : GloballyBV F) :
    Tendsto (fun x => (initialVariation F x).toReal) atBot (𝓝 0) := by
  have ht : Tendsto (fun x => eVariationOn F (Iic x)) atBot (𝓝 0) := by
    simpa using ((globallyBV_iff_boundedVariationOn F).mp hF).tendsto_eVariationOn_Iic_zero
  simpa only [initialVariation_bridge, Function.comp_def, ENNReal.toReal_zero] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht

lemma initialVariation_right_continuous {F : ℝ → E} (hF : NBV F) (x : ℝ) :
    ContinuousWithinAt (fun y => (initialVariation F y).toReal) (Ici x) x := by
  have ht : Tendsto (fun y => eVariationOn F (Icc x y)) (𝓝 (x : ℝ)) (𝓝 0) := by
    simpa using hF.boundedVariationOn.tendsto_eVariationOn_Icc_zero_right
      ((hF.2.1 x).mono inter_subset_right)
  have hr := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp ht
  have ha := (tendsto_const_nhds (x := (initialVariation F x).toReal)).add hr
  simp only [Function.comp_def, ENNReal.toReal_zero, add_zero] at ha
  refine Tendsto.congr' ?_ (ha.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [initialVariation_add hy,
    ENNReal.toReal_add (initialVariation_finite hF.1 x).ne
      (hF.boundedVariationOn.mono (subset_univ _))]

lemma initialVariation_regular (F : ℝ → E) (hF : NBV F) :
    (∀ x, initialVariation F x < ⊤) ∧
    (∀ x, ContinuousWithinAt (fun y => (initialVariation F y).toReal) (Ici x) x) ∧
    Tendsto (fun x => (initialVariation F x).toReal) atBot (𝓝 0) :=
  ⟨initialVariation_finite hF.1, initialVariation_right_continuous hF,
    initialVariation_tendsto_atBot hF.1⟩

/-- Initial variation has increments dominating those of the function. -/
lemma initialVariation_increment_bound {F : ℝ → E} (hF : GloballyBV F)
    {x y : ℝ} (hxy : x ≤ y) :
    ‖F y - F x‖ ≤ (initialVariation F y).toReal - (initialVariation F x).toReal := by
  have hb := (globallyBV_iff_boundedVariationOn F).mp hF
  have hsub : BV F x y := (bv_iff_boundedVariationOn F x y).mpr (hb.mono (subset_univ _))
  have heq := congrArg ENNReal.toReal (initialVariation_add (F := F) hxy)
  rw [ENNReal.toReal_add (initialVariation_finite hF x).ne
    (hb.mono (subset_univ _))] at heq
  have hn := norm_sub_le_variation F hxy hsub
  rw [variation_eq_eVariationOn] at hn
  linarith

/-- Normalization at minus infinity bounds the value itself by initial variation. -/
lemma norm_le_initialVariation {F : ℝ → E} (hF : NBV F) (x : ℝ) :
    ‖F x‖ ≤ (initialVariation F x).toReal := by
  have ht : Tendsto (fun a => ‖F x - F a‖) atBot (𝓝 ‖F x‖) := by
    simpa using (tendsto_const_nhds.sub hF.2.2).norm
  apply le_of_tendsto ht
  filter_upwards [eventually_le_atBot x] with a ha
  have hav : variation F a x ≤ initialVariation F x := le_iSup (fun a => variation F a x) a
  exact (norm_sub_le_variation F ha (hav.trans_lt (initialVariation_finite hF.1 x))).trans
    (ENNReal.toReal_mono (initialVariation_finite hF.1 x).ne hav)

lemma initialVariation_le_global (F : ℝ → E) (x : ℝ) :
    initialVariation F x ≤ globalVariation F :=
  iSup_le fun a => le_iSup_of_le a (le_iSup (fun b => variation F a b) x)

lemma components_generators (F : ℝ → ℝ) (hF : NBV F) :
    PositiveStieltjes.PositiveGenerator (positiveComponent F) ∧
    PositiveStieltjes.PositiveGenerator (negativeComponent F) ∧
    ∀ x, F x = positiveComponent F x - negativeComponent F x := by
  have hp : Monotone (positiveComponent F) := by
    intro x y hxy
    have hi := initialVariation_increment_bound hF.1 hxy
    have hn := neg_abs_le (F y - F x)
    rw [Real.norm_eq_abs] at hi
    dsimp [positiveComponent]
    linarith
  have hn : Monotone (negativeComponent F) := by
    intro x y hxy
    have hi := initialVariation_increment_bound hF.1 hxy
    have hn := le_abs_self (F y - F x)
    rw [Real.norm_eq_abs] at hi
    dsimp [negativeComponent]
    linarith
  have hpc (x : ℝ) : ContinuousWithinAt (positiveComponent F) (Ici x) x :=
    ((initialVariation_right_continuous hF x).add (hF.2.1 x)).div_const 2
  have hnc (x : ℝ) : ContinuousWithinAt (negativeComponent F) (Ici x) x :=
    ((initialVariation_right_continuous hF x).sub (hF.2.1 x)).div_const 2
  have hpt : Tendsto (positiveComponent F) atBot (𝓝 0) := by
    change Tendsto (fun x => ((initialVariation F x).toReal + F x) / 2) atBot (𝓝 0)
    simpa only [positiveComponent, zero_add, zero_div] using
      ((initialVariation_tendsto_atBot hF.1).add hF.2.2).div_const 2
  have hnt : Tendsto (negativeComponent F) atBot (𝓝 0) := by
    change Tendsto (fun x => ((initialVariation F x).toReal - F x) / 2) atBot (𝓝 0)
    simpa only [negativeComponent, sub_zero, zero_div] using
      ((initialVariation_tendsto_atBot hF.1).sub hF.2.2).div_const 2
  have hb (x : ℝ) :
      |positiveComponent F x| ≤ (globalVariation F).toReal ∧
      |negativeComponent F x| ≤ (globalVariation F).toReal := by
    have hfx := norm_le_initialVariation hF x
    rw [Real.norm_eq_abs, abs_le] at hfx
    have hvg : (initialVariation F x).toReal ≤ (globalVariation F).toReal :=
      ENNReal.toReal_mono hF.1.ne (initialVariation_le_global F x)
    dsimp [positiveComponent, negativeComponent]
    constructor <;> rw [abs_le] <;> constructor <;> linarith
  refine ⟨⟨hp, hpc, hpt, (globalVariation F).toReal, fun x => (hb x).1⟩,
    ⟨hn, hnc, hnt, (globalVariation F).toReal, fun x => (hb x).2⟩, ?_⟩
  intro x
  dsimp [positiveComponent, negativeComponent]
  ring

lemma stieltjesMeasure_eq [CompleteSpace E] {F : ℝ → E} (hF : NBV F) :
    stieltjesMeasure F = hF.boundedVariationOn.vectorMeasure := by
  simp only [stieltjesMeasure, dite_eq_left hF.boundedVariationOn]

lemma measure_finite [CompleteSpace E] (F : ℝ → E) (hF : NBV F) :
    IsFiniteMeasure (stieltjesMeasure F).variation := by
  rw [stieltjesMeasure_eq hF]
  infer_instance

lemma cumulative_measure [CompleteSpace E] (F : ℝ → E) (hF : NBV F) :
    cumulative (stieltjesMeasure F) = F := by
  ext x
  rw [cumulative, stieltjesMeasure_eq hF, BoundedVariationOn.vectorMeasure_Iic,
    hF.rightLim_eq]
  have hlim : limUnder atBot F = 0 :=
    tendsto_nhds_unique hF.boundedVariationOn.tendsto_atBot_limUnder hF.2.2
  rw [hlim, sub_zero]

lemma measure_interval [CompleteSpace E] (F : ℝ → E) (hF : NBV F)
    (a b : ℝ) (hab : a < b) : stieltjesMeasure F (Ioc a b) = F b - F a := by
  rw [stieltjesMeasure_eq hF, BoundedVariationOn.vectorMeasure_Ioc _ hab.le, hF.rightLim_eq]

lemma measure_atom [CompleteSpace E] (F : ℝ → E) (hF : NBV F) (x : ℝ) :
    stieltjesMeasure F {x} = F x - Function.leftLim F x := by
  rw [stieltjesMeasure_eq hF, BoundedVariationOn.vectorMeasure_singleton, hF.rightLim_eq]

/-- Finite scalar additivity on initial intervals, before any BV assumption. -/
lemma cumulative_sub (ν : VectorMeasure ℝ E) {a b : ℝ} (hab : a ≤ b) :
    cumulative ν b - cumulative ν a = ν (Ioc a b) := by
  rw [cumulative, cumulative, ← VectorMeasure.of_sdiff measurableSet_Iic measurableSet_Iic
    (Iic_subset_Iic.mpr hab)]
  congr 1
  ext x
  simp only [Set.mem_sdiff, mem_Iic, not_le, mem_Ioc]
  tauto

/-- Every partition sum of the cumulative function is bounded by total mass
of the positive variation measure. No exact variation identity is used. -/
lemma cumulative_variation_le (ν : VectorMeasure ℝ E) :
    eVariationOn (cumulative ν) univ ≤ ν.variation univ := by
  simp only [eVariationOn, iSup_le_iff, Prod.forall, Subtype.forall,
    mem_univ, forall_const, edist_eq_enorm_sub]
  intro n u ⟨hu, _⟩
  calc
    ∑ i ∈ Finset.range n, ‖cumulative ν (u (i + 1)) - cumulative ν (u i)‖ₑ
      ≤ ∑ i ∈ Finset.range n, ν.variation (Ioc (u i) (u (i + 1))) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [cumulative_sub ν (hu (Nat.le_succ i))]
        exact ν.enorm_measure_le_variation _
    _ = ν.variation (⋃ i ∈ Finset.range n, Ioc (u i) (u (i + 1))) := by
        rw [measure_biUnion_finset ?_ (fun _ _ => measurableSet_Ioc)]
        rintro i _ j _ hij
        simp only [Function.onFun]
        rcases lt_or_gt_of_ne hij with hij | hij
        · exact Set.disjoint_left.mpr fun x hx hy =>
            (not_lt_of_ge (hx.2.trans (hu (Nat.succ_le_of_lt hij)))) hy.1
        · exact Set.disjoint_left.mpr fun x hx hy =>
            (not_lt_of_ge (hy.2.trans (hu (Nat.succ_le_of_lt hij)))) hx.1
    _ ≤ ν.variation univ := measure_mono (subset_univ _)

lemma cumulative_globallyBV (ν : VectorMeasure ℝ E) [IsFiniteMeasure ν.variation] :
    GloballyBV (cumulative ν) := by
  rw [GloballyBV, globalVariation_eq_eVariationOn]
  exact (cumulative_variation_le ν).trans_lt (measure_lt_top _ _)

lemma cumulative_tendsto_atBot (ν : VectorMeasure ℝ E) [IsFiniteMeasure ν.variation] :
    Tendsto (cumulative ν) atBot (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) (fun _ => VectorMeasure.norm_measure_le_variation)
    (PositiveStieltjes.cumulative_tendsto_atBot ν.variation)

lemma cumulative_right_continuous (ν : VectorMeasure ℝ E) [IsFiniteMeasure ν.variation]
    (x : ℝ) : ContinuousWithinAt (cumulative ν) (Ici x) x := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := ((PositiveStieltjes.cumulative_right_continuous ν.variation x).sub
    (continuousWithinAt_const (b := ν.variation.real (Iic x))))
  have ht' : Tendsto (fun y => ν.variation.real (Iic y) - ν.variation.real (Iic x))
      (𝓝[Ici x] x) (𝓝 0) := by
    simpa only [ContinuousWithinAt, Pi.sub_def, PositiveStieltjes.cumulative, sub_self] using ht
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_ ht'
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [cumulative_sub ν hy]
  have hb := VectorMeasure.norm_measure_le_variation (μ := ν) (E := Ioc x y)
  have heq : ν.variation.real (Ioc x y) =
      ν.variation.real (Iic y) - ν.variation.real (Iic x) := by
    rw [← measureReal_sdiff (Iic_subset_Iic.mpr hy) measurableSet_Iic]
    congr 1
    ext z
    simp only [Set.mem_sdiff, mem_Iic, not_le, mem_Ioc]
    tauto
  exact heq ▸ hb

lemma cumulative_properties (ν : VectorMeasure ℝ E) (hν : IsFiniteMeasure ν.variation) :
    NBV (cumulative ν) := by
  letI := hν
  exact ⟨cumulative_globallyBV ν, cumulative_right_continuous ν, cumulative_tendsto_atBot ν⟩

/-- Initial rays determine a scalar measure; the total mass is recovered by
continuity along an increasing exhaustion, rather than assumed separately. -/
lemma vectorMeasure_ext_of_Iic (μ ν : VectorMeasure ℝ E)
    (h : ∀ x : ℝ, μ (Iic x) = ν (Iic x)) : μ = ν := by
  apply VectorMeasure.ext_of_generateFrom (range Iic)
    (by rintro _ ⟨x, rfl⟩; exact h x)
    (borel_eq_generateFrom_Iic ℝ) isPiSystem_Iic
  have hs : (⋃ n : ℕ, Iic (n : ℝ)) = univ := by
    ext x
    simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]
    exact exists_nat_ge x
  have hm : Monotone (fun n : ℕ => Iic (n : ℝ)) :=
    fun _ _ hmn => Iic_subset_Iic.mpr (Nat.cast_le.mpr hmn)
  have hμ := μ.tendsto_vectorMeasure_iUnion_atTop_nat hm (fun _ => measurableSet_Iic)
  have hν := ν.tendsto_vectorMeasure_iUnion_atTop_nat hm (fun _ => measurableSet_Iic)
  rw [hs] at hμ hν
  simp only [h] at hμ
  exact tendsto_nhds_unique hμ hν

lemma measure_cumulative [CompleteSpace E] (ν : VectorMeasure ℝ E)
    (hν : IsFiniteMeasure ν.variation) : stieltjesMeasure (cumulative ν) = ν := by
  apply vectorMeasure_ext_of_Iic
  exact fun x => congrFun (cumulative_measure (cumulative ν) (cumulative_properties ν hν)) x

lemma signed_cumulative_properties (ν : SignedMeasure ℝ) : NBV (cumulative ν) :=
  cumulative_properties ν (D11.Ch14.TotalVariation.signed_finite ν)

lemma complex_cumulative_properties (ν : ComplexMeasure ℝ) : NBV (cumulative ν) :=
  cumulative_properties ν (D11.Ch14.TotalVariation.complex_finite ν)

lemma signed_measure_cumulative (ν : SignedMeasure ℝ) : stieltjesMeasure (cumulative ν) = ν :=
  measure_cumulative ν (D11.Ch14.TotalVariation.signed_finite ν)

lemma complex_measure_cumulative (ν : ComplexMeasure ℝ) : stieltjesMeasure (cumulative ν) = ν :=
  measure_cumulative ν (D11.Ch14.TotalVariation.complex_finite ν)

lemma measure_unique [CompleteSpace E] (F : ℝ → E) (hF : NBV F)
    (ν : VectorMeasure ℝ E)
    (hν : ∀ a b : ℝ, a < b → ν (Ioc a b) = F b - F a) : ν = stieltjesMeasure F := by
  apply vectorMeasure_ext_of_Iic
  intro x
  obtain ⟨u, hu, hlim⟩ := Filter.exists_seq_antitone_tendsto_atTop_atBot ℝ
  have hs : (⋃ n, Ioc (u n) x) = Iic x := by
    ext y
    simp only [mem_iUnion, mem_Ioc, mem_Iic]
    constructor
    · rintro ⟨n, _, hy⟩
      exact hy
    · intro hy
      obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_atBot y)).exists
      exact ⟨n, hn, hy⟩
  have ht := ν.tendsto_vectorMeasure_iUnion_atTop_nat
    (s := fun n => Ioc (u n) x)
    (fun _ _ hmn => Ioc_subset_Ioc_left (hu hmn)) (fun _ => measurableSet_Ioc)
  rw [hs] at ht
  have hft : Tendsto (fun n => F x - F (u n)) atTop (𝓝 (F x)) := by
    simpa using tendsto_const_nhds.sub (hF.2.2.comp hlim)
  have heq : (fun n => F x - F (u n)) =ᶠ[atTop] (fun n => ν (Ioc (u n) x)) := by
    filter_upwards [hlim.eventually (eventually_lt_atBot x)] with n hn
    exact (hν _ _ hn).symm
  have hc : ν (Iic x) = F x := tendsto_nhds_unique ht (hft.congr' heq)
  exact hc.trans (congrFun (cumulative_measure F hF) x).symm

lemma signed_bijection :
    ∃ e : {F : ℝ → ℝ // NBV F} ≃ SignedMeasure ℝ,
      (∀ F x, e F (Iic x) = F.val x) ∧
      (∀ ν x, (e.symm ν).val x = ν (Iic x)) := by
  let e : {F : ℝ → ℝ // NBV F} ≃ SignedMeasure ℝ :=
    { toFun := fun F => stieltjesMeasure F.val
      invFun := fun ν => ⟨cumulative ν, signed_cumulative_properties ν⟩
      left_inv := fun F => Subtype.ext (cumulative_measure F.val F.property)
      right_inv := signed_measure_cumulative }
  exact ⟨e, fun F x => congrFun (cumulative_measure F.val F.property) x, fun _ _ => rfl⟩

lemma complex_bijection :
    ∃ e : {F : ℝ → ℂ // NBV F} ≃ ComplexMeasure ℝ,
      (∀ F x, e F (Iic x) = F.val x) ∧
      (∀ ν x, (e.symm ν).val x = ν (Iic x)) := by
  let e : {F : ℝ → ℂ // NBV F} ≃ ComplexMeasure ℝ :=
    { toFun := fun F => stieltjesMeasure F.val
      invFun := fun ν => ⟨cumulative ν, complex_cumulative_properties ν⟩
      left_inv := fun F => Subtype.ext (cumulative_measure F.val F.property)
      right_inv := complex_measure_cumulative }
  exact ⟨e, fun F x => congrFun (cumulative_measure F.val F.property) x, fun _ _ => rfl⟩

end D11.Ch12.ScalarStieltjesCorrespondence
