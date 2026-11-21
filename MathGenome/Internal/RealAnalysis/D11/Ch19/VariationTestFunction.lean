import MathGenome.Internal.RealAnalysis.D11.Ch19.ComplexRadonVariation
import MathGenome.Internal.RealAnalysis.D11.Ch18.CompactCutoff
import MathGenome.Internal.RealAnalysis.D11.Ch14.IntegralVariationBound
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch19.VariationTestFunction
import Mathlib.Order.Filter.Bases.Finite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency.types false
/-! Continuous compact-support tests for partition total variation
(paper.tex:5593–5600). A finite near-maximizing Borel partition supplies scalar
phases. Compact inner approximation and disjoint open neighborhoods produce a
unit-ball Cc function agreeing with that phase step function except on a set of
arbitrarily small variation. The sharp integral bound transfers the partition
sum to the continuous test. No normality of the whole space, countability,
Radon–Nikodym theorem, or measure representation theorem is assumed. -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
universe u
namespace D11.Ch19.VariationTestFunction
open D11.Ch14.TotalVariation D11.Ch14.ScalarIntegration D11.Ch14.Jordan
open D11.Ch18
local instance {X : Type u} [TopologicalSpace X] : MeasurableSpace X := borel X
local instance {X : Type u} [TopologicalSpace X] : BorelSpace X := ⟨rfl⟩
variable {X : Type u} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
variable {𝕜 : Type} [RCLike 𝕜]

/-- Prescribed values in the unit ball on finitely many disjoint compact sets
extend to a compactly supported continuous function in the unit ball. -/
theorem interpolate_disjoint_compacts {ι : Type u} [Fintype ι]
    (K : ι → Set X) (hK : ∀ i, IsCompact (K i))
    (hd : Pairwise fun i j => Disjoint (K i) (K j))
    (z : ι → 𝕜) (hz : ∀ i, ‖z i‖ ≤ 1) :
    ∃ f : CompactlySupportedContinuousMap X 𝕜,
      (∀ x, ‖f x‖ ≤ 1) ∧ ∀ i, EqOn f (fun _ => z i) (K i) := by
  classical
  have hn : Pairwise fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j)) := by
    intro i j hij
    exact SeparatedNhds.disjoint_nhdsSet
      (SeparatedNhds.of_isCompact_isCompact_isClosed (hK i) (hK j) (hK j).isClosed (hd hij))
  obtain ⟨U, hU, hdU⟩ := hn.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (K i))
  choose φ hφK hφcomp hφU hφbound using fun i =>
    exists_continuousMap_one_of_isCompact_subset_isOpen (hK i) (hU i).1 (hU i).2
  let f : X → 𝕜 := fun x => ∑ i, (φ i x : ℝ) • z i
  have hfc : Continuous f := by fun_prop
  have hfcomp : HasCompactSupport f := by
    apply HasCompactSupport.intro (isCompact_iUnion hφcomp)
    intro x hx
    dsimp [f]
    apply Finset.sum_eq_zero
    intro i _
    have hx' : x ∉ tsupport (φ i) := fun h => hx (mem_iUnion.mpr ⟨i, h⟩)
    simp [image_eq_zero_of_notMem_tsupport hx']
  have hzero (i : ι) (x : X) (hx : x ∉ U i) : φ i x = 0 := by
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hφU i h))
  have hsingle (i : ι) (x : X) (hx : x ∈ U i) : f x = (φ i x : ℝ) • z i := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      have hnot : x ∉ U j := fun hxj => Set.disjoint_left.mp (hdU hji) hxj hx
      simp [hzero j x hnot]
    · simp
  refine ⟨⟨⟨f, hfc⟩, hfcomp⟩, ?_, ?_⟩
  · intro x
    change ‖f x‖ ≤ 1
    by_cases hx : ∃ i, x ∈ U i
    · obtain ⟨i, hi⟩ := hx
      rw [hsingle i x hi, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφbound i x).1]
      exact (mul_le_mul_of_nonneg_left (hz i) (hφbound i x).1).trans (by simpa using (hφbound i x).2)
    · have hf0 : f x = 0 := Finset.sum_eq_zero fun i _ => by
        simp [hzero i x (fun hi => hx ⟨i, hi⟩)]
      simp [hf0]
  · intro i x hx
    change f x = z i
    rw [hsingle i x ((hU i).2 hx), hφK i hx, Pi.one_apply, one_smul]

/-- The phase multiplying a scalar mass into its absolute value. -/
theorem exists_phase (a : 𝕜) : ∃ z : 𝕜, ‖z‖ ≤ 1 ∧ z * a = (‖a‖ : 𝕜) := by
  by_cases ha : a = 0
  · exact ⟨1, by simp, by simp [ha]⟩
  refine ⟨(starRingEnd 𝕜) a / (‖a‖ : 𝕜), ?_, ?_⟩
  · simp [norm_div, div_self (norm_ne_zero_iff.mpr ha)]
  · rw [div_mul_eq_mul_div, RCLike.conj_mul, sq, mul_div_cancel_right₀]
    exact_mod_cast norm_ne_zero_iff.mpr ha

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- A phase step function on a finite Borel partition has a unit-ball Cc
approximation in L1 for every finite Radon measure, without normality of X. -/
theorem approximate_partition (μ : @Measure X (borel X)) [IsFiniteMeasure μ]
    (hμ : isRadon μ) {ι : Type u} [Fintype ι]
    (A : ι → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hd : Pairwise fun i j => Disjoint (A i) (A j)) (hcover : ⋃ i, A i = univ)
    (z : ι → 𝕜) (hz : ∀ i, ‖z i‖ ≤ 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : CompactlySupportedContinuousMap X 𝕜,
      (∀ x, ‖f x‖ ≤ 1) ∧
      (∫ x, ‖f x - ∑ i, (A i).indicator (fun _ => z i) x‖ ∂μ) < ε := by
  classical
  let : Measure.Regular μ := (isRadon_iff_regular μ).mp hμ
  let δ : ℝ := ε / (4 * (Fintype.card ι + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hKA, hK, herr⟩ : ∃ K : ι → Set X,
      (∀ i, K i ⊆ A i) ∧ (∀ i, IsCompact (K i)) ∧
      ∀ i, μ (A i \ K i) < ENNReal.ofReal δ := by
    have H (i : ι) := (hA i).exists_isCompact_sdiff_lt (μ := μ)
      (measure_ne_top μ (A i)) (ENNReal.ofReal_pos.mpr hδ).ne'
    choose K hKA hK herr using H
    exact ⟨K, hKA, hK, herr⟩
  have hdK : Pairwise fun i j => Disjoint (K i) (K j) :=
    fun i j hij => (hd hij).mono (hKA i) (hKA j)
  obtain ⟨f, hf, hfK⟩ := interpolate_disjoint_compacts K hK hdK z hz
  let s : X → 𝕜 := fun x => ∑ i, (A i).indicator (fun _ => z i) x
  have hs_eq (i : ι) (x : X) (hx : x ∈ A i) : s x = z i := by
    dsimp [s]
    rw [Finset.sum_eq_single i]
    · simp [hx]
    · intro j _ hji
      have hxj : x ∉ A j := fun hj => Set.disjoint_left.mp (hd hji) hj hx
      simp [hxj]
    · simp
  have hs_bound (x : X) : ‖s x‖ ≤ 1 := by
    have hx : x ∈ ⋃ i, A i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    rw [hs_eq i x hi]
    exact hz i
  have hsm : Measurable s := Finset.measurable_sum _ fun i _ => measurable_const.indicator (hA i)
  have hsi : Integrable s μ := Integrable.of_bound hsm.aestronglyMeasurable 1
    (Eventually.of_forall hs_bound)
  have hfi : Integrable (f : X → 𝕜) μ := Integrable.of_bound f.continuous.aestronglyMeasurable 1
    (Eventually.of_forall hf)
  let C : Set X := ⋃ i, K i
  have hC : IsCompact C := isCompact_iUnion hK
  have hsub : Cᶜ ⊆ ⋃ i, A i \ K i := by
    intro x hx
    have hxA : x ∈ ⋃ i, A i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxA
    exact mem_iUnion.mpr ⟨i, hi, fun hxK => hx (mem_iUnion.mpr ⟨i, hxK⟩)⟩
  have hmass : μ.real Cᶜ < ε / 2 := calc
    μ.real Cᶜ ≤ μ.real (⋃ i, A i \ K i) := measureReal_mono hsub
    _ ≤ ∑ i, μ.real (A i \ K i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : ι, δ := Finset.sum_le_sum fun i _ => by
      exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
        ENNReal.ofReal_ne_top).mpr (herr i) |>.le |>.trans (by rw [ENNReal.toReal_ofReal hδ.le])
    _ < ε / 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [δ]
      have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
      apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      rw [mul_div_assoc', div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
  have hdiff (x : X) : ‖f x - s x‖ ≤ Cᶜ.indicator (fun _ => (2 : ℝ)) x := by
    by_cases hx : x ∈ C
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      rw [hfK i hi, hs_eq i x (hKA i hi)]
      dsimp only
      rw [sub_self, norm_zero]
      exact indicator_nonneg (fun _ _ => by norm_num) x
    · simp only [mem_compl_iff, hx, not_false_eq_true, indicator_of_mem]
      exact (norm_sub_le _ _).trans (by linarith [hf x, hs_bound x])
  refine ⟨f, hf, lt_of_le_of_lt (integral_mono ((hfi.sub hsi).norm)
    ((integrable_const (2 : ℝ)).indicator hC.measurableSet.compl) hdiff) ?_⟩
  rw [integral_indicator_const _ hC.measurableSet.compl, smul_eq_mul]
  nlinarith

/-- Common argument for signed and complex Jordan integration. Only proved
integral algebra, the indicator formula and the sharp variation bound enter. -/
private theorem variation_test_of_integral
    (ν : VectorMeasure X 𝕜) [IsFiniteMeasure (totalVariation ν)]
    (hν : isRadon (totalVariation ν)) (T : (X → 𝕜) → 𝕜)
    (hT0 : T (fun _ => 0) = 0)
    (hTadd : ∀ f g, Measurable f → Integrable f (totalVariation ν) →
      Measurable g → Integrable g (totalVariation ν) →
      T (fun x => f x + g x) = T f + T g)
    (hTsub : ∀ f g, Measurable f → Integrable f (totalVariation ν) →
      Measurable g → Integrable g (totalVariation ν) →
      T (fun x => f x - g x) = T f - T g)
    (hTind : ∀ A, MeasurableSet A → ∀ z : 𝕜,
      T (A.indicator (fun _ => z)) = z * ν A)
    (hTbound : ∀ f, Measurable f → Integrable f (totalVariation ν) →
      ‖T f‖ ≤ ∫ x, ‖f x‖ ∂(totalVariation ν))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : CompactlySupportedContinuousMap X 𝕜,
      (∀ x, ‖f x‖ ≤ 1) ∧ (totalVariation ν univ).toReal - ε ≤ ‖T f‖ := by
  classical
  let μ := totalVariation ν
  by_cases hm : μ.real univ ≤ ε
  · refine ⟨0, fun x => by simp, ?_⟩
    change μ.real univ - ε ≤ ‖T (fun _ => 0)‖
    rw [hT0, norm_zero]
    linarith
  have hpos : 0 < μ.real univ - ε / 2 := by dsimp [μ] at *; linarith
  have hlt : ENNReal.ofReal (μ.real univ - ε / 2) < μ univ := by
    conv_rhs => rw [← ENNReal.ofReal_toReal (measure_ne_top μ univ)]
    exact (ENNReal.ofReal_lt_ofReal_iff (by change 0 < μ.real univ; linarith)).mpr (by change _ < μ.real univ; linarith)
  rw [show μ = totalVariation ν from rfl, totalVariation_partition_formula ν univ MeasurableSet.univ,
    lt_iSup_iff] at hlt
  obtain ⟨P, hP⟩ := hlt
  let ι := {A // A ∈ P.parts}
  let A : ι → Set X := fun i => i.val.val
  have hA (i : ι) : MeasurableSet (A i) := i.val.property
  have hd : Pairwise fun i j : ι => Disjoint (A i) (A j) := by
    intro i j hij
    exact P.pairwiseDisjoint_apply (f := fun S : Subtype MeasurableSet => S.val) (fun _ _ => rfl) rfl i.property j.property
      (fun he => hij (Subtype.ext he))
  have hcover : (⋃ i, A i) = univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x ∈ P.parts.sup (fun S : Subtype MeasurableSet => S.val) := by
      rw [P.sup_parts_apply (f := fun S : Subtype MeasurableSet => S.val) (fun _ _ => rfl) rfl]
      trivial
    simp only [Finset.sup_set_eq_biUnion, mem_iUnion] at hx
    obtain ⟨B, hB, hx⟩ := hx
    exact mem_iUnion.mpr ⟨⟨B, hB⟩, hx⟩
  have hpart : μ.real univ - ε / 2 < ∑ i : ι, ‖ν (A i)‖ := by
    have hP' := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top
      (by simp : (∑ p ∈ P.parts, ENNReal.ofReal ‖ν p.val‖) ≠ ∞)).mpr hP
    rw [ENNReal.toReal_ofReal hpos.le, ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)] at hP'
    simp only [ENNReal.toReal_ofReal (norm_nonneg _)] at hP'
    change μ.real univ - ε / 2 < ∑ i : P.parts, ‖ν i.val.val‖
    rw [show (∑ i : P.parts, ‖ν i.val.val‖) = ∑ p ∈ P.parts, ‖ν p.val‖ from
      Finset.sum_coe_sort P.parts (fun p : Subtype MeasurableSet => ‖ν p.val‖)]
    exact hP' 
  choose z hz hza using fun i : ι => exists_phase (ν (A i))
  obtain ⟨f, hf, herr⟩ := approximate_partition μ hν A hA hd hcover z hz (ε / 2) (by positivity)
  let s : X → 𝕜 := fun x => ∑ i, (A i).indicator (fun _ => z i) x
  have hsm : Measurable s := Finset.measurable_sum _ fun i _ => measurable_const.indicator (hA i)
  have hsi : Integrable s μ := integrable_finsetSum _ fun i _ =>
    (integrable_const (z i)).indicator (hA i)
  have hfm : Measurable (f : X → 𝕜) := f.continuous.measurable
  have hfi : Integrable (f : X → 𝕜) μ := Integrable.of_bound hfm.aestronglyMeasurable 1
    (Eventually.of_forall hf)
  have hsum (q : Finset ι) :
      T (fun x => ∑ i ∈ q, (A i).indicator (fun _ => z i) x) =
        ∑ i ∈ q, z i * ν (A i) := by
    induction q using Finset.induction_on with
    | empty => simpa using hT0
    | insert i q hi ih =>
      simp only [Finset.sum_insert hi]
      rw [hTadd _ _ (measurable_const.indicator (hA i))
        ((integrable_const _).indicator (hA i))
        (Finset.measurable_sum _ fun j _ => measurable_const.indicator (hA j))
        (integrable_finsetSum _ fun j _ => (integrable_const _).indicator (hA j)),
        hTind _ (hA i), ih]
  have hsval : T s = ((∑ i : ι, ‖ν (A i)‖ : ℝ) : 𝕜) := by
    rw [hsum Finset.univ]
    simp_rw [hza]
    exact (map_sum (algebraMap ℝ 𝕜) _ _).symm
  have hsnorm : ‖T s‖ = ∑ i : ι, ‖ν (A i)‖ := by
    rw [hsval, RCLike.norm_ofReal, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
  have herror : ‖T f - T s‖ < ε / 2 := by
    rw [← hTsub f s hfm hfi hsm hsi]
    exact (hTbound _ (hfm.sub hsm) (hfi.sub hsi)).trans_lt herr
  refine ⟨f, hf, ?_⟩
  have hn := norm_sub_norm_le (T s) (T f)
  rw [norm_sub_rev, hsnorm] at hn
  change μ.real univ - ε ≤ ‖T f‖
  linarith

/-- Real compact-support tests detect the full variation of a signed Radon measure. -/
theorem signed_variation_test_function :
    Specs.D11.Ch19.VariationTestFunction.signed_variation_test_function := by
  intro X _ _ _ ν hν ε hε
  let : IsFiniteMeasure (totalVariation ν) := signed_finite ν
  have hreg : isRadon (totalVariation ν) := (signedRadon_iff_variation ν).mp hν
  let T : (X → ℝ) → ℝ := fun f =>
    (∫ x, f x ∂(positivePart ν)) - (∫ x, f x ∂(negativePart ν))
  have hparts (f : X → ℝ) (hm : Measurable f) (hi : Integrable f (totalVariation ν)) :=
    signed_parts_integrable ν f ((signedIntegrable_iff _ _).mpr ⟨hm, hi⟩)
  have hTadd (f g : X → ℝ) (hfm : Measurable f) (hfi : Integrable f (totalVariation ν))
      (hgm : Measurable g) (hgi : Integrable g (totalVariation ν)) :
      T (fun x => f x + g x) = T f + T g := by
    dsimp [T]
    rw [integral_add (hparts f hfm hfi).1 (hparts g hgm hgi).1,
      integral_add (hparts f hfm hfi).2 (hparts g hgm hgi).2]
    ring
  have hTsub (f g : X → ℝ) (hfm : Measurable f) (hfi : Integrable f (totalVariation ν))
      (hgm : Measurable g) (hgi : Integrable g (totalVariation ν)) :
      T (fun x => f x - g x) = T f - T g := by
    dsimp [T]
    rw [integral_sub (hparts f hfm hfi).1 (hparts g hgm hgi).1,
      integral_sub (hparts f hfm hfi).2 (hparts g hgm hgi).2]
    ring
  have hTind (A : Set X) (hA : MeasurableSet A) (z : ℝ) :
      T (A.indicator (fun _ => z)) = z * ν A := by
    simpa only [T, signedIntegral, smul_eq_mul, mul_comm] using
      signedIntegral_indicator_const ν A hA z (signedIntegrable_indicator ν A hA z)
  have hTbound (f : X → ℝ) (hm : Measurable f) (hi : Integrable f (totalVariation ν)) :
      ‖T f‖ ≤ ∫ x, ‖f x‖ ∂(totalVariation ν) :=
    Ch14.IntegralVariationBound.norm_signedIntegral_le ν f ((signedIntegrable_iff _ _).mpr ⟨hm, hi⟩)
  obtain ⟨f, hf, hval⟩ := variation_test_of_integral ν hreg T (by simp [T])
    hTadd hTsub hTind hTbound ε hε
  refine ⟨f, (BoundedContinuousFunction.norm_le (by norm_num)).mpr hf, ?_⟩
  have hfi : signedIntegrable ν (f : X → ℝ) := (signedIntegrable_iff _ _).mpr
    ⟨f.continuous.measurable, Integrable.of_bound f.continuous.aestronglyMeasurable 1
      (Eventually.of_forall hf)⟩
  exact ⟨hfi, hval⟩

/-- Complex compact-support tests use the bilinear Jordan integral; there is
no conjugation in the integral pairing. -/
theorem complex_variation_test_function :
    Specs.D11.Ch19.VariationTestFunction.complex_variation_test_function := by
  intro X _ _ _ ν hν ε hε
  let : IsFiniteMeasure (totalVariation ν) := complex_finite ν
  have hreg : isRadon (totalVariation ν) := (complexRadon_iff_variation ν).mp hν
  let T : (X → ℂ) → ℂ := fun f =>
    ((∫ x, f x ∂(positivePart ν.re)) - (∫ x, f x ∂(negativePart ν.re))) +
      Complex.I * ((∫ x, f x ∂(positivePart ν.im)) - (∫ x, f x ∂(negativePart ν.im)))
  have hparts (f : X → ℂ) (hm : Measurable f) (hi : Integrable f (totalVariation ν)) :
      Integrable f (positivePart ν.re) ∧ Integrable f (negativePart ν.re) ∧
      Integrable f (positivePart ν.im) ∧ Integrable f (negativePart ν.im) := by
    obtain ⟨hr, hi⟩ := complex_parts_integrable ν f ((complexIntegrable_iff _ _).mpr ⟨hm, hi⟩)
    exact ⟨(signed_parts_integrable ν.re f hr).1, (signed_parts_integrable ν.re f hr).2,
      signed_parts_integrable ν.im f hi⟩
  have hTadd (f g : X → ℂ) (hfm : Measurable f) (hfi : Integrable f (totalVariation ν))
      (hgm : Measurable g) (hgi : Integrable g (totalVariation ν)) :
      T (fun x => f x + g x) = T f + T g := by
    dsimp [T]
    rw [integral_add (hparts f hfm hfi).1 (hparts g hgm hgi).1,
      integral_add (hparts f hfm hfi).2.1 (hparts g hgm hgi).2.1,
      integral_add (hparts f hfm hfi).2.2.1 (hparts g hgm hgi).2.2.1,
      integral_add (hparts f hfm hfi).2.2.2 (hparts g hgm hgi).2.2.2]
    ring
  have hTsub (f g : X → ℂ) (hfm : Measurable f) (hfi : Integrable f (totalVariation ν))
      (hgm : Measurable g) (hgi : Integrable g (totalVariation ν)) :
      T (fun x => f x - g x) = T f - T g := by
    dsimp [T]
    rw [integral_sub (hparts f hfm hfi).1 (hparts g hgm hgi).1,
      integral_sub (hparts f hfm hfi).2.1 (hparts g hgm hgi).2.1,
      integral_sub (hparts f hfm hfi).2.2.1 (hparts g hgm hgi).2.2.1,
      integral_sub (hparts f hfm hfi).2.2.2 (hparts g hgm hgi).2.2.2]
    ring
  have hTind (A : Set X) (hA : MeasurableSet A) (z : ℂ) :
      T (A.indicator (fun _ => z)) = z * ν A := by
    exact complexIntegral_indicator_const ν A hA z (complexIntegrable_indicator ν A hA z)
  have hTbound (f : X → ℂ) (hm : Measurable f) (hi : Integrable f (totalVariation ν)) :
      ‖T f‖ ≤ ∫ x, ‖f x‖ ∂(totalVariation ν) :=
    Ch14.IntegralVariationBound.norm_complexIntegral_le ν f ((complexIntegrable_iff _ _).mpr ⟨hm, hi⟩)
  obtain ⟨f, hf, hval⟩ := variation_test_of_integral ν hreg T (by simp [T])
    hTadd hTsub hTind hTbound ε hε
  refine ⟨f, (BoundedContinuousFunction.norm_le (by norm_num)).mpr hf, ?_⟩
  have hfi : complexIntegrable ν (f : X → ℂ) := (complexIntegrable_iff _ _).mpr
    ⟨f.continuous.measurable, Integrable.of_bound f.continuous.aestronglyMeasurable 1
      (Eventually.of_forall hf)⟩
  exact ⟨hfi, hval⟩

end D11.Ch19.VariationTestFunction
