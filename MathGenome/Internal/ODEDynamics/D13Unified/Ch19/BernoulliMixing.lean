import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.BernoulliMixing
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.BernoulliMeasure
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.ErgodicCriterion
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.Birkhoff
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.FullShiftChaos
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.Tactic.Tauto

namespace D13Unified.Ch19.BernoulliMixing
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators symmDiff ENNReal Classical
open D13Unified.Ch17
open D13Unified.Ch17.ShiftSpaces D13Unified.Ch19.BernoulliMeasure

lemma reindex_preserves {I : Type} (f : I → I) (hf : Function.Injective f) :
    MeasurePreserving (fun s : I → Binary => fun i => s (f i))
      (bernoulliMeasure I) (bernoulliMeasure I) := by
  refine ⟨measurable_pi_iff.mpr (fun i => measurable_pi_apply (f i)), ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj hf

theorem preservesPlus : Specs.D13Unified.Ch19.BernoulliMixing.preservesPlusStatement :=
  reindex_preserves (fun i : ℕ => i + 1) (by intro i j h; dsimp at h; omega)

theorem preservesTwoSided : Specs.D13Unified.Ch19.BernoulliMixing.preservesTwoSidedStatement :=
  reindex_preserves (fun i : ℤ => i + 1) (by intro i j h; dsimp at h; omega)

/-- Events determined by finitely many coordinates, including arbitrary unions
of assignments on those coordinates. -/
def FiniteCoordinateEvent {I : Type} (A : Set (I → Binary)) : Prop :=
  ∃ F : Finset I, ∀ x y : I → Binary,
    (∀ i ∈ F, x i = y i) → (x ∈ A ↔ y ∈ A)

lemma finiteCoordinateEvent_representation {I : Type} {A : Set (I → Binary)}
    (hA : FiniteCoordinateEvent A) :
    ∃ (F : Finset I) (E : Set (F → Binary)), A = F.restrict ⁻¹' E := by
  classical
  obtain ⟨F, hF⟩ := hA
  let extend : (F → Binary) → I → Binary :=
    fun x i => if hi : i ∈ F then x ⟨i, hi⟩ else 0
  refine ⟨F, extend ⁻¹' A, ?_⟩
  ext x
  exact hF x (extend (F.restrict x)) (by intro i hi; simp [extend, hi])

lemma finiteCoordinateEvent_measurable {I : Type} {A : Set (I → Binary)}
    (hA : FiniteCoordinateEvent A) : MeasurableSet A := by
  obtain ⟨F, E, rfl⟩ := finiteCoordinateEvent_representation hA
  exact (MeasurableSet.of_discrete : MeasurableSet E).preimage
    (measurable_pi_iff.mpr (fun i => measurable_pi_apply (i : I)))

lemma finiteCoordinateEvent_ring (I : Type) :
    IsSetRing {A : Set (I → Binary) | FiniteCoordinateEvent A} := by
  classical
  refine ⟨⟨∅, by simp⟩, ?_, ?_⟩
  · rintro A B ⟨F, hF⟩ ⟨G, hG⟩
    refine ⟨F ∪ G, ?_⟩
    intro x y h
    exact or_congr (hF x y (fun i hi => h i (Finset.mem_union_left _ hi)))
      (hG x y (fun i hi => h i (Finset.mem_union_right _ hi)))
  · rintro A B ⟨F, hF⟩ ⟨G, hG⟩
    refine ⟨F ∪ G, ?_⟩
    intro x y h
    exact and_congr (hF x y (fun i hi => h i (Finset.mem_union_left _ hi)))
      (not_congr (hG x y (fun i hi => h i (Finset.mem_union_right _ hi))))

lemma finiteCoordinateEvent_generate (I : Type) :
    (inferInstance : MeasurableSpace (I → Binary)) =
      MeasurableSpace.generateFrom {A | FiniteCoordinateEvent A} := by
  apply le_antisymm
  · rw [MeasurableSpace.pi_eq_generateFrom_projections]
    apply MeasurableSpace.generateFrom_mono
    rintro A ⟨i, E, _, rfl⟩
    refine ⟨{i}, ?_⟩
    intro x y h
    change x i ∈ E ↔ y i ∈ E
    rw [h i (Finset.mem_singleton_self i)]
  · exact MeasurableSpace.generateFrom_le (fun A hA => finiteCoordinateEvent_measurable hA)

lemma approximate_finiteCoordinates {I : Type} {A : Set (I → Binary)}
    (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C, FiniteCoordinateEvent C ∧ bernoulliMeasure I (C ∆ A) < ε := by
  let := probability I
  apply exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    (finiteCoordinateEvent_ring I) ?_ (finiteCoordinateEvent_generate I) hA hε
  refine ⟨{univ}, Set.countable_singleton _, ?_, by simp⟩
  intro A hA
  have : A = univ := Set.mem_singleton_iff.mp hA
  subst A
  exact ⟨∅, by simp⟩

lemma finite_event_independent {I : Type} (T : (I → Binary) → I → Binary)
    (k : I → I) (hk : ∀ s i, T s i = s (k i))
    (F G : Finset I) (C : Set (F → Binary)) (D : Set (G → Binary))
    (hsep : ∀ i ∈ F, ∀ j ∈ G, k j ≠ i) :
    bernoulliMeasure I ((F.restrict ⁻¹' C) ∩ T ⁻¹' (G.restrict ⁻¹' D)) =
      bernoulliMeasure I (F.restrict ⁻¹' C) *
        bernoulliMeasure I (T ⁻¹' (G.restrict ⁻¹' D)) := by
  classical
  let J := G.image k
  let r : (J → Binary) → G → Binary := fun x i =>
    x ⟨k i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩
  have hd : Disjoint F J := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hj
    exact hsep i hi j hj hji
  have hi := (independent_blocks I F J hd).comp
    measurable_id (show Measurable r from .of_discrete)
  have he := hi.measure_inter_preimage_eq_mul C D (.of_discrete) (.of_discrete)
  have hr : (r ∘ J.restrict) = G.restrict ∘ T := by
    funext s j
    exact (hk s j).symm
  change bernoulliMeasure I ((id ∘ F.restrict) ⁻¹' C ∩ (r ∘ J.restrict) ⁻¹' D) =
    bernoulliMeasure I ((id ∘ F.restrict) ⁻¹' C) *
      bernoulliMeasure I ((r ∘ J.restrict) ⁻¹' D) at he
  simpa only [Function.id_comp, hr, preimage_comp] using he

lemma finite_events_eventually_independent {I : Type}
    (T : (I → Binary) → I → Binary) (k : ℕ → I → I)
    (hk : ∀ n s i, T^[n] s i = s (k n i))
    (hsep : ∀ F G : Finset I, ∀ᶠ n in atTop, ∀ i ∈ F, ∀ j ∈ G, k n j ≠ i)
    (hp : MeasurePreserving T (bernoulliMeasure I) (bernoulliMeasure I))
    {A B : Set (I → Binary)} (hA : FiniteCoordinateEvent A)
    (hB : FiniteCoordinateEvent B) :
    ∀ᶠ n in atTop, bernoulliMeasure I (A ∩ (T^[n] ⁻¹' B)) =
      bernoulliMeasure I A * bernoulliMeasure I B := by
  obtain ⟨F, C, rfl⟩ := finiteCoordinateEvent_representation hA
  obtain ⟨G, D, rfl⟩ := finiteCoordinateEvent_representation hB
  filter_upwards [hsep F G] with n hn
  rw [finite_event_independent _ _ (hk n) F G C D hn,
    (hp.iterate n).measure_preimage (finiteCoordinateEvent_measurable hB).nullMeasurableSet]

lemma measureReal_distance {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {A C : Set X} (hA : MeasurableSet A) (hC : MeasurableSet C) :
    |μ.real A - μ.real C| ≤ μ.real (A ∆ C) := by
  have h1 := MeasuredSets.real_sub_real_le_dist (μ := μ)
    (⟨A, hA⟩ : MeasuredSets μ) (⟨C, hC⟩ : MeasuredSets μ)
  have h2 := MeasuredSets.real_sub_real_le_dist (μ := μ)
    (⟨C, hC⟩ : MeasuredSets μ) (⟨A, hA⟩ : MeasuredSets μ)
  change μ.real A - μ.real C ≤ μ.real (A ∆ C) at h1
  change μ.real C - μ.real A ≤ μ.real (C ∆ A) at h2
  rw [symmDiff_comm C A] at h2
  exact abs_le.mpr ⟨by linarith, h1⟩

lemma correlation_distance {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (T : X → X) (hp : MeasurePreserving T μ μ)
    {A B C D : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    |μ.real (A ∩ T ⁻¹' B) - μ.real (C ∩ T ⁻¹' D)| ≤
      μ.real (A ∆ C) + μ.real (B ∆ D) := by
  apply (measureReal_distance μ (hA.inter (hp.measurable hB))
    (hC.inter (hp.measurable hD))).trans
  have hsub : (A ∩ T ⁻¹' B) ∆ (C ∩ T ⁻¹' D) ⊆
      (A ∆ C) ∪ T ⁻¹' (B ∆ D) := by
    intro x
    simp only [mem_symmDiff, mem_inter_iff, mem_union, mem_preimage]
    tauto
  apply (measureReal_mono hsub).trans
  rw [show μ.real (B ∆ D) = μ.real (T ⁻¹' (B ∆ D)) from
    (congrArg ENNReal.toReal (hp.measure_preimage (hB.symmDiff hD).nullMeasurableSet)).symm]
  exact measureReal_union_le _ _

lemma product_distance {a b c d : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hbu : b ≤ 1) (hcu : c ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ ≤ |a - c| + |b - d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb, abs_of_nonneg hc]
      exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) hbu)
        (mul_le_of_le_one_left (abs_nonneg _) hcu)

/-- The finite-coordinate approximation argument extends exact eventual
independence to correlation limits for every measurable pair. -/
lemma mixing_of_finite_events {I : Type}
    (T : (I → Binary) → I → Binary)
    (hp : MeasurePreserving T (bernoulliMeasure I) (bernoulliMeasure I))
    (hf : ∀ A B : Set (I → Binary), FiniteCoordinateEvent A → FiniteCoordinateEvent B →
      ∀ᶠ n in atTop, bernoulliMeasure I (A ∩ (T^[n] ⁻¹' B)) =
        bernoulliMeasure I A * bernoulliMeasure I B) :
    Specs.D13Unified.Ch19.MeasureDefinitions.IsMixing T (bernoulliMeasure I) := by
  let := probability I
  intro A B hA hB
  change Tendsto (fun n => bernoulliMeasure I (A ∩ (T^[n] ⁻¹' B))) atTop
    (𝓝 (bernoulliMeasure I A * bernoulliMeasure I B))
  apply (ENNReal.tendsto_toReal_iff (fun _ => measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))).mp
  simp only [ENNReal.toReal_mul]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ENNReal.ofReal (ε / 8) := ENNReal.ofReal_pos.mpr (by positivity)
  obtain ⟨C, hCf, hCA⟩ := approximate_finiteCoordinates hA he
  obtain ⟨D, hDf, hDB⟩ := approximate_finiteCoordinates hB he
  have hC := finiteCoordinateEvent_measurable hCf
  have hD := finiteCoordinateEvent_measurable hDf
  have hAC : (bernoulliMeasure I).real (A ∆ C) < ε / 8 := by
    rw [symmDiff_comm]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (by simp)).mpr hCA |>.trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  have hBD : (bernoulliMeasure I).real (B ∆ D) < ε / 8 := by
    rw [symmDiff_comm]
    exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) (by simp)).mpr hDB |>.trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  filter_upwards [hf C D hCf hDf] with n hn
  have hi := correlation_distance (bernoulliMeasure I) (T^[n]) (hp.iterate n) hA hB hC hD
  have hprod := product_distance
    (a := (bernoulliMeasure I).real C) (b := (bernoulliMeasure I).real D)
    (c := (bernoulliMeasure I).real A) (d := (bernoulliMeasure I).real B)
    (measureReal_nonneg (μ := bernoulliMeasure I) (s := D))
    (measureReal_nonneg (μ := bernoulliMeasure I) (s := A))
    (measureReal_le_one (μ := bernoulliMeasure I) (s := D))
    (measureReal_le_one (μ := bernoulliMeasure I) (s := A))
  have h1 := measureReal_distance (bernoulliMeasure I) hA hC
  have h2 := measureReal_distance (bernoulliMeasure I) hB hD
  have hn' := congrArg ENNReal.toReal hn
  simp only [ENNReal.toReal_mul] at hn'
  change (bernoulliMeasure I).real (C ∩ (T^[n] ⁻¹' D)) =
    (bernoulliMeasure I).real C * (bernoulliMeasure I).real D at hn'
  rw [hn'] at hi
  rw [abs_sub_comm ((bernoulliMeasure I).real C),
    abs_sub_comm ((bernoulliMeasure I).real D)] at hprod
  have htri := abs_sub_le ((bernoulliMeasure I).real (A ∩ (T^[n] ⁻¹' B)))
    ((bernoulliMeasure I).real C * (bernoulliMeasure I).real D)
    ((bernoulliMeasure I).real A * (bernoulliMeasure I).real B)
  simp only [Real.dist_eq]
  dsimp [Measure.real] at hi htri hprod h1 h2 hAC hBD
  linarith

theorem mixingPlus : Specs.D13Unified.Ch19.BernoulliMixing.mixingPlusStatement := by
  classical
  apply mixing_of_finite_events shiftPlus preservesPlus
  intro A B hA hB
  apply finite_events_eventually_independent shiftPlus (fun n j => j + n)
    FullShiftChaos.shiftPlus_iterate ?_ preservesPlus hA hB
  intro F G
  obtain ⟨N, hN⟩ := FullShiftChaos.nat_bound F
  filter_upwards [eventually_ge_atTop N] with n hn
  intro i hi j hj hji
  have := hN i hi
  omega

theorem mixingTwoSided : Specs.D13Unified.Ch19.BernoulliMixing.mixingTwoSidedStatement := by
  classical
  apply mixing_of_finite_events shift preservesTwoSided
  intro A B hA hB
  apply finite_events_eventually_independent shift (fun n j => j + (n : ℤ))
    FullShiftChaos.shift_iterate ?_ preservesTwoSided hA hB
  intro F G
  obtain ⟨N, hN⟩ := FullShiftChaos.int_bound (F ∪ G)
  filter_upwards [eventually_ge_atTop (2 * N)] with n hn
  intro i hi j hj hji
  have hi' := (hN i (Finset.mem_union_left G hi)).2
  have hj' := (hN j (Finset.mem_union_right F hj)).1
  omega

theorem ergodicPlus : Specs.D13Unified.Ch19.BernoulliMixing.ergodicPlusStatement := by
  let : IsProbabilityMeasure bernoulliPlus := probability ℕ
  exact ErgodicCriterion.mixing_implies_ergodic shiftPlus bernoulliPlus preservesPlus mixingPlus

theorem ergodicTwoSided : Specs.D13Unified.Ch19.BernoulliMixing.ergodicTwoSidedStatement := by
  let : IsProbabilityMeasure bernoulliTwoSided := probability ℤ
  exact ErgodicCriterion.mixing_implies_ergodic shift bernoulliTwoSided preservesTwoSided mixingTwoSided

lemma coordinate_integrable {I : Type} (i : I) :
    Integrable (fun s : I → Binary => ((s i).val : ℝ)) (bernoulliMeasure I) := by
  let := probability I
  apply Integrable.of_bound
    ((Measurable.of_discrete : Measurable (fun b : Binary => (b.val : ℝ))).comp
      (measurable_pi_apply i)).aestronglyMeasurable 1
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  change ((s i).val : ℝ) ≤ 1
  exact_mod_cast (show (s i).val ≤ 1 from by have := (s i).isLt; omega)

lemma coordinate_integral {I : Type} (i : I) :
    (∫ s : I → Binary, ((s i).val : ℝ) ∂bernoulliMeasure I) = 1 / 2 := by
  have hm : Measure.map (fun s : I → Binary => s i) (bernoulliMeasure I) = fair :=
    Measure.infinitePi_map_eval (fun _ : I => fair) i
  calc
    _ = ∫ b : Binary, (b.val : ℝ) ∂fair := by
      rw [← hm]
      exact (integral_map (μ := bernoulliMeasure I)
        (φ := fun s : I → Binary => s i) (f := fun b : Binary => (b.val : ℝ))
        (measurable_pi_apply i).aemeasurable
        (Measurable.of_discrete.aestronglyMeasurable)).symm
    _ = 1 / 2 := by
      rw [fair, Specs.D13Unified.Ch19.BernoulliMeasure.fair, integral_smul_measure,
        integral_add_measure (integrable_dirac (by finiteness)) (integrable_dirac (by finiteness))]
      norm_num

theorem frequencyPlus : Specs.D13Unified.Ch19.BernoulliMixing.frequencyPlusStatement := by
  let : IsProbabilityMeasure bernoulliPlus := probability ℕ
  have h := (ErgodicCriterion.real_ergodic_criterion shiftPlus bernoulliPlus preservesPlus).mp
    ergodicPlus (fun s => ((s 0).val : ℝ)) (coordinate_integrable 0)
  have hi : (∫ s : OneSided, ((s 0).val : ℝ) ∂bernoulliPlus) = 1 / 2 :=
    coordinate_integral (0 : ℕ)
  rw [hi] at h
  filter_upwards [h] with s hs
  convert hs using 1
  funext n
  rw [Specs.D13Unified.Ch19.MeasureDefinitions.ergodicAverage,
    birkhoffAverage, birkhoffSum]
  simp only [FullShiftChaos.shiftPlus_iterate, zero_add, smul_eq_mul, div_eq_mul_inv]
  ring

theorem frequencyTwoSided : Specs.D13Unified.Ch19.BernoulliMixing.frequencyTwoSidedStatement := by
  let : IsProbabilityMeasure bernoulliTwoSided := probability ℤ
  have h := (ErgodicCriterion.real_ergodic_criterion shift bernoulliTwoSided preservesTwoSided).mp
    ergodicTwoSided (fun s => ((s 0).val : ℝ)) (coordinate_integrable (0 : ℤ))
  have hi : (∫ s : TwoSided, ((s 0).val : ℝ) ∂bernoulliTwoSided) = 1 / 2 :=
    coordinate_integral (0 : ℤ)
  rw [hi] at h
  filter_upwards [h] with s hs
  convert hs using 1
  funext n
  rw [Specs.D13Unified.Ch19.MeasureDefinitions.ergodicAverage,
    birkhoffAverage, birkhoffSum]
  simp only [FullShiftChaos.shift_iterate, zero_add, smul_eq_mul, div_eq_mul_inv]
  ring

/-- A single sequence is contained in cylinders with arbitrarily many
specified coordinates, whose probabilities tend geometrically to zero. -/
instance bernoulli_nullSingleton (I : Type) [Infinite I] :
    NullSingletonClass (bernoulliMeasure I) := by
  classical
  constructor
  intro s
  let e : ℕ ↪ I := Infinite.natEmbedding I
  have hb : ∀ n : ℕ, bernoulliMeasure I {s} ≤ ((2 : ℝ≥0∞)⁻¹) ^ n := by
    intro n
    let F := (Finset.range n).image e
    have hc : F.card = n := by
      simp [F, Finset.card_image_of_injective _ e.injective]
    calc
      bernoulliMeasure I {s} ≤ bernoulliMeasure I (cylinder s F) := by
        apply measure_mono
        intro x hx
        have : x = s := Set.mem_singleton_iff.mp hx
        subst x
        intro j hj
        rfl
      _ = ((2 : ℝ≥0∞)⁻¹) ^ n := by
        rw [cylinder_mass I s F, hc]
        simp [ENNReal.zpow_neg, zpow_natCast, ENNReal.inv_pow]
  exact le_antisymm
    (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)) hb)
    bot_le

theorem fixedNullPlus : Specs.D13Unified.Ch19.BernoulliMixing.fixedNullPlusStatement := by
  intro n hn
  let : Finite {s : OneSided // shiftPlus^[n] s = s} :=
    Finite.of_equiv (Fin n → Binary) (FullShiftChaos.fixedPlusEquiv n hn).symm
  have hfin : {s : OneSided | shiftPlus^[n] s = s}.Finite :=
    Set.finite_coe_iff.mp (inferInstance : Finite {s : OneSided // shiftPlus^[n] s = s})
  exact hfin.measure_zero (bernoulliMeasure ℕ)

theorem fixedNullTwoSided : Specs.D13Unified.Ch19.BernoulliMixing.fixedNullTwoSidedStatement := by
  intro n hn
  let : Finite {s : TwoSided // shift^[n] s = s} :=
    Finite.of_equiv (Fin n → Binary) (FullShiftChaos.fixedEquiv n hn).symm
  have hfin : {s : TwoSided | shift^[n] s = s}.Finite :=
    Set.finite_coe_iff.mp (inferInstance : Finite {s : TwoSided // shift^[n] s = s})
  exact hfin.measure_zero (bernoulliMeasure ℤ)

lemma periodicPoints_union {X : Type*} (T : X → X) :
    ChaosDefinitions.periodicPoints T = ⋃ n : ℕ, ⋃ (_ : 0 < n), {s | T^[n] s = s} := by
  ext s
  simp [ChaosDefinitions.periodicPoints, Specs.D13Unified.Ch17.ChaosDefinitions.periodicPoints, Function.mem_periodicPts,
    Function.IsPeriodicPt, Function.IsFixedPt]

theorem periodicNullPlus : Specs.D13Unified.Ch19.BernoulliMixing.periodicNullPlusStatement := by
  change bernoulliPlus (ChaosDefinitions.periodicPoints shiftPlus) = 0
  rw [periodicPoints_union]
  exact measure_iUnion_null (fun n => measure_iUnion_null (fun hn => fixedNullPlus n hn))

theorem periodicNullTwoSided : Specs.D13Unified.Ch19.BernoulliMixing.periodicNullTwoSidedStatement := by
  change bernoulliTwoSided (ChaosDefinitions.periodicPoints shift) = 0
  rw [periodicPoints_union]
  exact measure_iUnion_null (fun n => measure_iUnion_null (fun hn => fixedNullTwoSided n hn))

theorem periodicDensePlus : Specs.D13Unified.Ch19.BernoulliMixing.periodicDensePlusStatement :=
  FullShiftChaos.shiftPlus_dense_periodic

theorem periodicDenseTwoSided : Specs.D13Unified.Ch19.BernoulliMixing.periodicDenseTwoSidedStatement :=
  FullShiftChaos.shift_dense_periodic

end
end D13Unified.Ch19.BernoulliMixing
