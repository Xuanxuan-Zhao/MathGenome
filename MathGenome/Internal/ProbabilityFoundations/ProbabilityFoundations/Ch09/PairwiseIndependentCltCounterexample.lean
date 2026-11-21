import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch09.PairwiseIndependentCltCounterexample
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch05.IndependentProduct
import MathGenome.Internal.ProbabilityFoundations.ProbabilityFoundations.Ch02.ConvergenceComparisons
import Mathlib.Probability.Independence.Integration
import Mathlib.Data.Finset.SymmDiff
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! Explicit binary-character counterexample, paper.tex:3100–3111.
The natural binary encoding provides the requested increasing coordinate blocks.
The powerset product identity gives their exact sums. Orthogonality and the
fact that every function on two signs is affine give pairwise independence.
A nonzero coordinate occurs almost surely; beyond it the selected sums equal -1.
Their normalized laws therefore tend to δ₀, precluding a standard Gaussian limit.
All objects are the canonical definitions in the independent specification. -/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology symmDiff

namespace ProbabilityFoundations.Ch09.PairwiseIndependentCltCounterexample

open Specs.ProbabilityFoundations.Ch09.PairwiseIndependentCltCounterexample

noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false

/-- The source's independent fair bits, on their uncompleted product space. -/
theorem bit_construction : bitConstructionType := by
  refine ⟨fun j => measurable_pi_apply j, ?_, ?_⟩
  · exact (Ch02.independentRandomElements_iff_iIndepFun _ _).mp
      (Ch05.IndependentProduct.infinitePi_independent_coordinates
        (fun _ : ℕ => Bool) (fun _ => fairBitMeasure))
  · exact Measure.infinitePi_map_eval (fun _ : ℕ => fairBitMeasure)

private theorem coefficients_ne_empty (k : ℕ) : coefficients k ≠ ∅ := by
  intro h
  have h' := congrArg Finset.equivBitIndices.symm h
  simp [coefficients, Finset.equivBitIndices] at h'

private theorem coefficients_injective : Function.Injective coefficients := by
  intro k l h
  have := Finset.equivBitIndices.injective h
  exact Nat.add_right_cancel this

private theorem code_lt_iff (s : Finset ℕ) (m : ℕ) :
    Finset.equivBitIndices.symm s < 2 ^ m ↔ s ⊆ Finset.range m := by
  constructor
  · intro h j hj
    apply Finset.mem_range.mpr
    have hle : 2 ^ j ≤ Finset.equivBitIndices.symm s :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj
    have hp : 2 ^ j < 2 ^ m := lt_of_le_of_lt hle h
    exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hp
  · intro h
    exact Nat.geomSum_lt (by decide : 2 ≤ 2) (fun j hj => Finset.mem_range.mp (h hj))

/-- Binary numeral order enumerates supports by increasing largest occupied coordinate. -/
theorem coefficient_enumeration : enumerationType := by
  refine ⟨coefficients_injective, coefficients_ne_empty, ?_, ?_⟩
  · intro s hs
    have hp : 0 < Finset.equivBitIndices.symm s := by
      by_contra h
      have hz : Finset.equivBitIndices.symm s = 0 := by omega
      have h' := congrArg Finset.equivBitIndices hz
      exact hs (by simpa [Finset.equivBitIndices] using h')
    refine ⟨Finset.equivBitIndices.symm s - 1, ?_⟩
    simp only [coefficients, Nat.sub_add_cancel hp, Equiv.apply_symm_apply]
  · intro m
    ext s
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_erase, Finset.mem_powerset]
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨coefficients_ne_empty k, (code_lt_iff _ m).mp ?_⟩
      simp only [coefficients, Equiv.symm_apply_apply]
      have hp := Nat.two_pow_pos m
      dsimp [blockSize] at hk
      omega
    · rintro ⟨hs, hsub⟩
      have hp : 0 < Finset.equivBitIndices.symm s := by
        by_contra h
        have hz : Finset.equivBitIndices.symm s = 0 := by omega
        have h' := congrArg Finset.equivBitIndices hz
        exact hs (by simpa [Finset.equivBitIndices] using h')
      refine ⟨Finset.equivBitIndices.symm s - 1, ?_, ?_⟩
      · have hlt := (code_lt_iff s m).mpr hsub
        dsimp [blockSize]
        omega
      · simp only [coefficients, Nat.sub_add_cancel hp, Equiv.apply_symm_apply]

/-- The product is the sign of the indicated binary linear form. -/
theorem character_formula : characterFormulaType := by
  intro s ω
  simp only [character, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro j _
  cases ω j <;> norm_num

private theorem complete_character_sum (s : Finset ℕ) (ω : BitSpace) :
    ∑ t ∈ s.powerset, character t ω = ∏ j ∈ s, (1 + if ω j then (-1 : ℝ) else 1) := by
  exact (Finset.prod_one_add s).symm

/-- Exact finite-block character sum, with the zero coefficient removed. -/
theorem block_sum : blockSumType := by
  intro m ω
  have hsum : partialSum (blockSize m) ω =
      ∑ s ∈ (Finset.range m).powerset.erase ∅, character s ω := by
    rw [← coefficient_enumeration.2.2.2 m, Finset.sum_image]
    · rfl
    · intro k _ l _ h
      exact coefficients_injective h
  rw [hsum]
  have hempty : (∅ : Finset ℕ) ∈ (Finset.range m).powerset := by simp
  have hadd := Finset.sum_erase_add (s := (Finset.range m).powerset)
    (fun s => character s ω) hempty
  rw [complete_character_sum] at hadd
  have hchar : character ∅ ω = 1 := by simp [character]
  rw [hchar] at hadd
  split_ifs with hzero
  · have hprod : (∏ j ∈ Finset.range m, (1 + if ω j then (-1 : ℝ) else 1)) =
        (2 : ℝ) ^ m := by
      calc
        _ = ∏ _j ∈ Finset.range m, (2 : ℝ) := by
          apply Finset.prod_congr rfl
          intro j hj
          rw [show ω j = false from hzero j (Finset.mem_range.mp hj)]
          norm_num
        _ = _ := by simp
    linarith
  · have hex : ∃ j < m, ω j = true := by
      by_contra hn
      apply hzero
      intro j hj
      cases hb : ω j
      · rfl
      · exact False.elim (hn ⟨j, hj, hb⟩)
    obtain ⟨j, hj, hbit⟩ := hex
    have hprod : (∏ i ∈ Finset.range m, (1 + if ω i then (-1 : ℝ) else 1)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_range.mpr hj)
      simp [hbit]
    linarith

/-- Every character is an actual measurable finite product of coordinate signs. -/
theorem character_measurable (s : Finset ℕ) : Measurable (character s) := by
  apply Finset.measurable_prod
  intro j _
  exact (measurable_of_finite (fun b : Bool => if b then (-1 : ℝ) else 1)).comp
    (measurable_pi_apply j)

/-- Characters take precisely sign values; this includes the constant empty character. -/
theorem character_sq (s : Finset ℕ) (ω : BitSpace) : character s ω ^ 2 = 1 := by
  rw [character, ← Finset.prod_pow]
  trans ∏ _j ∈ s, (1 : ℝ)
  · apply Finset.prod_congr rfl
    intro j _
    cases ω j <;> norm_num
  · simp

theorem character_values (s : Finset ℕ) (ω : BitSpace) :
    character s ω = 1 ∨ character s ω = -1 := by
  have h := character_sq s ω
  have : (character s ω - 1) * (character s ω + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h | h
  · left; linarith
  · right; linarith

theorem character_integrable (s : Finset ℕ) : Integrable (character s) bitProbability := by
  apply Integrable.of_bound (character_measurable s).aestronglyMeasurable 1
  filter_upwards [] with ω
  rcases character_values s ω with h | h <;> simp [h]

private theorem bit_sign_mean (j : ℕ) :
    (∫ ω : BitSpace, (if ω j then (-1 : ℝ) else 1) ∂bitProbability) = 0 := by
  have hmap := bit_construction.2.2 j
  have hmeas := measurable_of_finite (fun b : Bool => if b then (-1 : ℝ) else 1)
  have heq := integral_map (μ := bitProbability)
    (φ := fun ω : BitSpace => ω j) (f := fun b : Bool => if b then (-1 : ℝ) else 1)
    (measurable_pi_apply j).aemeasurable hmeas.aestronglyMeasurable
  rw [← heq, hmap, fairBitMeasure, integral_bernoulliMeasure]
  norm_num

/-- Orthogonality to constants for each nonzero binary coefficient vector. -/
theorem character_mean_zero (s : Finset ℕ) (hs : s ≠ ∅) :
    (∫ ω, character s ω ∂bitProbability) = 0 := by
  have hind := bit_construction.2.1.restrict s
  have heq := hind.integral_fun_prod_comp
    (fun j : s => (measurable_pi_apply (j : ℕ)).aemeasurable)
    (fun _ => (measurable_of_finite
      (fun b : Bool => if b then (-1 : ℝ) else 1)).aestronglyMeasurable)
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hs
  calc
    _ = ∫ ω, ∏ i : s, (if ω (i : ℕ) then (-1 : ℝ) else 1) ∂bitProbability := by
      congr 1
      funext ω
      exact (Finset.prod_coe_sort s (fun i => if ω i then (-1 : ℝ) else 1)).symm
    _ = ∏ i : s, ∫ ω, (if ω (i : ℕ) then (-1 : ℝ) else 1) ∂bitProbability := heq
    _ = 0 := Finset.prod_eq_zero (by simp : (⟨j, hj⟩ : s) ∈ Finset.univ) (bit_sign_mean j)

/-- Multiplication of real binary characters is symmetric difference of supports. -/
theorem character_mul (s t : Finset ℕ) (ω : BitSpace) :
    character s ω * character t ω = character (s ∆ t) ω := by
  have hsplit (s t : Finset ℕ) :
      character (s \ t) ω * character (s ∩ t) ω = character s ω := by
    simpa only [character, Finset.sdiff_inter_self_left] using
      (Finset.prod_sdiff (s₁ := s ∩ t) (s₂ := s)
        (f := fun j => if ω j then (-1 : ℝ) else 1) Finset.inter_subset_left)
  have hd : Disjoint (s \ t) (t \ s) := by
    simp only [Finset.disjoint_left, Finset.mem_sdiff]
    tauto
  rw [← hsplit s t, ← hsplit t s, Finset.inter_comm t s]
  calc
    _ = (character (s \ t) ω * character (t \ s) ω) * character (s ∩ t) ω ^ 2 := by ring
    _ = character (s \ t) ω * character (t \ s) ω := by rw [character_sq, mul_one]
    _ = character (s ∆ t) ω := by
      simp only [Finset.symmDiff_def, character, Finset.prod_union hd]

private theorem affine_on_signs (φ : ℝ → ℝ) {x : ℝ} (hx : x = 1 ∨ x = -1) :
    φ x = (φ 1 + φ (-1)) / 2 + ((φ 1 - φ (-1)) / 2) * x := by
  rcases hx with rfl | rfl <;> ring

/-- Every test function of a sign is affine in that sign, pointwise. -/
theorem integral_character_comp (s : Finset ℕ) (hs : s ≠ ∅) (φ : ℝ → ℝ) :
    (∫ ω, φ (character s ω) ∂bitProbability) = (φ 1 + φ (-1)) / 2 := by
  have heq : (fun ω => φ (character s ω)) =
      (fun ω => (φ 1 + φ (-1)) / 2 + ((φ 1 - φ (-1)) / 2) * character s ω) :=
    funext (fun ω => affine_on_signs φ (character_values s ω))
  rw [heq, integral_add (integrable_const _) ((character_integrable s).const_mul _),
    integral_const, integral_const_mul, character_mean_zero s hs]
  simp

/-- All nonzero characters have exactly the same fair two-point law. -/
theorem character_law (s : Finset ℕ) (hs : s ≠ ∅) :
    Measure.map (character s) bitProbability = fairSignMeasure := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  rw [integral_map (character_measurable s).aemeasurable
    φ.continuous.measurable.aestronglyMeasurable, integral_character_comp s hs,
    fairSignMeasure, integral_bernoulliMeasure]
  simp only [smul_eq_mul]
  norm_num
  ring

/-- Both mean and variance are the actual integrals, not assumed moment certificates. -/
theorem signs_moments : signsMomentsType := by
  intro k
  have hs := coefficients_ne_empty k
  refine ⟨character_integrable _, ?_, character_mean_zero _ hs, ?_⟩
  · have h : (fun ω => signs k ω ^ 2) = (fun _ : BitSpace => (1 : ℝ)) :=
      funext (character_sq (coefficients k))
    rw [h]
    exact integrable_const _
  · change variance (character (coefficients k)) bitProbability = 1
    rw [variance_eq_integral (character_measurable _).aemeasurable,
      character_mean_zero _ hs]
    simp only [sub_zero, character_sq, integral_const, probReal_univ, smul_eq_mul,
      one_mul]

/-- Measurability includes n=0, where the normalized sum is defined as zero. -/
theorem normalized_sum_measurable : measurabilityType := by
  intro n
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro k _
  exact character_measurable _

/-- Distinct nonzero characters are independent, even when their supports overlap. -/
theorem characters_independent (s t : Finset ℕ) (hs : s ≠ ∅) (ht : t ≠ ∅)
    (hst : s ≠ t) : IndepFun (character s) (character t) bitProbability := by
  have hst' : s ∆ t ≠ ∅ := by simpa using hst
  have hmix : (∫ ω, character s ω * character t ω ∂bitProbability) = 0 := by
    simp_rw [character_mul]
    exact character_mean_zero _ hst'
  have hint : Integrable (fun ω => character s ω * character t ω) bitProbability := by
    simpa only [character_mul] using character_integrable (s ∆ t)
  apply (indepFun_iff_integral_comp_mul
    (hfm := character_measurable s) (hgm := character_measurable t)).mpr
  intro φ ψ _hφ _hψ _hintφ _hintψ
  change (∫ ω, φ (character s ω) * ψ (character t ω) ∂bitProbability) =
    (∫ ω, φ (character s ω) ∂bitProbability) *
      (∫ ω, ψ (character t ω) ∂bitProbability)
  rw [integral_character_comp s hs, integral_character_comp t ht]
  let a := (φ 1 + φ (-1)) / 2
  let b := (φ 1 - φ (-1)) / 2
  let c := (ψ 1 + ψ (-1)) / 2
  let d := (ψ 1 - ψ (-1)) / 2
  have heq : (fun ω => φ (character s ω) * ψ (character t ω)) =
      (fun ω => a * c + (a * d) * character t ω + (b * c) * character s ω +
        (b * d) * (character s ω * character t ω)) := by
    funext ω
    rw [affine_on_signs φ (character_values s ω), affine_on_signs ψ (character_values t ω)]
    dsimp [a, b, c, d]
    ring
  have hi₁ := integrable_const (μ := bitProbability) (a * c)
  have hi₂ := (character_integrable t).const_mul (a * d)
  have hi₃ := (character_integrable s).const_mul (b * c)
  have hi₄ := hint.const_mul (b * d)
  have hi₁₂ : Integrable (fun ω => a * c + (a * d) * character t ω) bitProbability :=
    hi₁.add hi₂
  have hi₁₂₃ : Integrable
      (fun ω => a * c + (a * d) * character t ω + (b * c) * character s ω)
      bitProbability := hi₁₂.add hi₃
  rw [heq, integral_add hi₁₂₃ hi₄, integral_add hi₁₂ hi₃, integral_add hi₁ hi₂]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul,
    character_mean_zero s hs, character_mean_zero t ht, hmix, mul_zero, add_zero]
  rfl

theorem signs_distribution : signsDistributionType := by
  refine ⟨fun k => character_measurable _, fun k => character_law _ (coefficients_ne_empty k), ?_⟩
  intro k l hkl
  exact characters_independent _ _ (coefficients_ne_empty k) (coefficients_ne_empty l)
    (fun h => hkl (coefficients_injective h))

private theorem prefix_measurable (m : ℕ) : MeasurableSet (zeroPrefix m) := by
  have heq : zeroPrefix m = ⋂ j ∈ Finset.range m, {ω : BitSpace | ω j = false} := by
    ext ω
    simp [zeroPrefix]
  rw [heq]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    (show Measurable (fun ω : BitSpace => ω j) from measurable_pi_apply j)
      (measurableSet_singleton false)

private theorem prefix_probability (m : ℕ) :
    bitProbability (zeroPrefix m) = (1 / 2 : ℝ≥0∞) ^ m := by
  have heq : zeroPrefix m = ⋂ j ∈ Finset.range m, {ω : BitSpace | ω j = false} := by
    ext ω
    simp [zeroPrefix]
  rw [heq, bit_construction.2.1.meas_biInter]
  · have hcoord (j : ℕ) : bitProbability {ω : BitSpace | ω j = false} = (1 / 2 : ℝ≥0∞) := by
      change bitProbability ((fun ω : BitSpace => ω j) ⁻¹' {false}) = (1 / 2 : ℝ≥0∞)
      rw [← Measure.map_apply (show Measurable (fun ω : BitSpace => ω j) from measurable_pi_apply j)
      (measurableSet_singleton false),
        bit_construction.2.2 j, fairBitMeasure,
        bernoulliMeasure_apply _ (measurableSet_singleton false)]
      simp only [Set.mem_singleton_iff, Bool.true_eq_false, ite_true, ite_false]
      change ((1 / 2 : ℝ≥0) : ℝ≥0∞) = (1 / 2 : ℝ≥0∞)
      norm_num
    simp only [hcoord, Finset.prod_const, Finset.card_range]
  · intro j _
    exact ⟨{false}, measurableSet_singleton false, rfl⟩

/-- The rare exceptional value has mass exactly 2^{-m}. -/
theorem block_probability : blockProbabilityType := by
  refine ⟨fun m => ⟨prefix_measurable m, prefix_probability m⟩, ?_⟩
  intro m _hm
  have heq : {ω : BitSpace | partialSum (blockSize m) ω = (2 : ℝ) ^ m - 1} =
      zeroPrefix m := by
    ext ω
    rw [Set.mem_ofPred_eq, block_sum]
    by_cases h : ω ∈ zeroPrefix m
    · simp [h]
    · simp only [h, ite_false, iff_false]
      have hp : (0 : ℝ) < 2 ^ m := pow_pos (by norm_num) _
      linarith
  rw [heq, prefix_probability]

/-- The selected indices form a genuine subsequence, including the initial index zero. -/
theorem blockSize_strictMono : StrictMono blockSize := by
  intro m n hmn
  have hp : 2 ^ m < 2 ^ n := Nat.pow_lt_pow_right (by decide : 1 < 2) hmn
  have hm : 0 < 2 ^ m := Nat.two_pow_pos m
  dsimp [blockSize]
  omega

private theorem regular_value_tendsto :
    Tendsto (fun m => (-1 : ℝ) / Real.sqrt (blockSize m)) atTop (𝓝 0) := by
  apply Filter.Tendsto.const_div_atTop _ (-1 : ℝ)
  exact Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.comp blockSize_strictMono.tendsto_atTop)

/-- The single infinite all-zero path is null, proved from the finite-prefix probabilities. -/
theorem almost_everywhere_nonzero_prefix :
    ∀ᵐ ω ∂bitProbability, ∃ m, ω ∉ zeroPrefix m := by
  have hpow : Tendsto (fun m => (1 / 2 : ℝ≥0∞) ^ m) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  have hnull : bitProbability (⋂ m, zeroPrefix m) = 0 := by
    apply le_antisymm _ bot_le
    apply ge_of_tendsto' hpow
    intro m
    rw [← prefix_probability m]
    exact measure_mono (Set.iInter_subset (fun m => zeroPrefix m) m)
  rw [ae_iff]
  convert hnull using 1
  congr 1
  ext ω
  simp

/-- A stronger convergence conclusion than the required convergence in probability. -/
theorem blocks_almost_sure :
    ∀ᵐ ω ∂bitProbability, Tendsto (fun m => normalizedSum (blockSize m) ω) atTop (𝓝 0) := by
  filter_upwards [almost_everywhere_nonzero_prefix] with ω hω
  obtain ⟨m₀, hm₀⟩ := hω
  apply regular_value_tendsto.congr'
  filter_upwards [eventually_ge_atTop m₀] with m hm
  have hnot : ω ∉ zeroPrefix m := by
    intro h
    apply hm₀
    intro j hj
    exact h j (lt_of_lt_of_le hj hm)
  dsimp only [normalizedSum]
  rw [block_sum m ω, ite_eq_right hnot]

theorem block_convergence : blockConvergenceType := by
  exact Ch02.almostSure_implies_probability bitProbability
    (fun m => normalizedSum (blockSize m)) (fun _ => 0)
    (fun m => normalized_sum_measurable _) measurable_const blocks_almost_sure

/-- The full normalized sums cannot have the standard Gaussian law as weak limit. -/
theorem no_gaussian_limit : noGaussianLimitType := by
  intro hfull
  have hprob : TendstoInMeasure bitProbability (fun m => normalizedSum (blockSize m)) atTop
      (fun _ => (0 : ℝ)) :=
    (Ch01.convergesInProbability_iff_tendstoInMeasure _ _ _).mp block_convergence
  have hdist := hprob.tendstoInDistribution
    (fun m => (normalized_sum_measurable (blockSize m)).aemeasurable)
  have hzero : Tendsto
      (fun m => (Measure.map (normalizedSum (blockSize m)) bitProbability).toProbabilityMeasure)
      atTop (𝓝 (Measure.dirac (0 : ℝ)).toProbabilityMeasure) := by
    simpa only [Measure.toProbabilityMeasure, Measure.map_const, measure_univ, one_smul]
      using hdist.tendsto
  have hsub := hfull.comp blockSize_strictMono.tendsto_atTop
  have heq := tendsto_nhds_unique hsub hzero
  have hmeq : gaussianReal 0 1 = Measure.dirac (0 : ℝ) := congrArg Subtype.val heq
  have : NullSingletonClass (gaussianReal 0 1) :=
    nullSingletonClass_gaussianReal (by norm_num)
  have hmass := congrArg (fun μ : Measure ℝ => μ {(0 : ℝ)}) hmeq
  simp at hmass

end
end ProbabilityFoundations.Ch09.PairwiseIndependentCltCounterexample
