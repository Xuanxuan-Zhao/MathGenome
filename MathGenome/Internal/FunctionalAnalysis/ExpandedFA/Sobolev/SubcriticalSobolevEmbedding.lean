import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.EndpointSobolevInequality
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.WeakDerivativeSpaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.C1DomainExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.OneDimensionalSobolev
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

set_option maxHeartbeats 1000000

noncomputable section
open MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.Sobolev.Subcritical
open ExpandedFA.Distributions

/-- The NNReal formula is the ordinary real Sobolev exponent on its range. -/
theorem criticalExponent_coe {d : ℕ} {p : ℝ≥0} (hpd : p < d) :
    (criticalExponent d p : ℝ) = (d : ℝ) * p / ((d : ℝ) - p) := by
  simp only [criticalExponent, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast,
    NNReal.coe_sub hpd.le]

/-- The inverse-exponent identity required by the library inequality. -/
theorem criticalExponent_inv {d : ℕ} {p : ℝ≥0} (hp : 1 ≤ p) (hpd : p < d) :
    (criticalExponent d p : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹ := by
  have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp))
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one
    (by exact_mod_cast hp.trans hpd.le))
  have hdp : (d : ℝ) - p ≠ 0 := ne_of_gt (sub_pos.mpr (by exact_mod_cast hpd))
  rw [criticalExponent_coe hpd]
  field_simp

/-- A coordinate bound connects the accepted sup-norm coordinate domain with
exactly the Euclidean gradient norm used by the source. -/
theorem norm_le_dimension_mul_gradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (A : Domain d →L[ℝ] 𝕜) :
    ‖A‖ ≤ d * ‖(WithLp.toLp 2 (fun j => A (coordinateVector j)) : EuclideanSpace 𝕜 (Fin d))‖ := by
  classical
  refine (norm_le_sum_coordinate_norm A).trans ?_
  calc
    (∑ j : Fin d, ‖A (coordinateVector j)‖) ≤
        ∑ _j : Fin d, ‖(WithLp.toLp 2 (fun j => A (coordinateVector j)) :
          EuclideanSpace 𝕜 (Fin d))‖ := by
      exact Finset.sum_le_sum fun j _ => PiLp.norm_apply_le (WithLp.toLp 2 (fun j => A (coordinateVector j)) : EuclideanSpace 𝕜 (Fin d)) j
    _ = _ := by simp

theorem classicalGradient_continuous {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u : Domain d → 𝕜} (hu : ContDiff ℝ 1 u) : Continuous (classicalGradient u) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin d => 𝕜)).comp
  exact continuous_pi fun j => (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem classicalGradient_hasCompactSupport {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {u : Domain d → 𝕜} (hu : HasCompactSupport u) : HasCompactSupport (classicalGradient u) := by
  apply HasCompactSupport.of_support_subset_isCompact hu
  intro x hx
  by_contra hn
  apply hx
  simp [classicalGradient, fderiv_of_notMem_tsupport ℝ hn, Pi.zero_def]

/-- Gagliardo–Nirenberg–Sobolev for C¹ compactly supported functions. The
library hypothesis is checked against the actual formula dp/(d-p), and the
operator norm on the right is bounded by the Euclidean gradient. -/
theorem compact_smooth_inequality :
    Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding.CompactSmoothInequality := by
  intro d p hp hpd
  have hd : 0 < Module.finrank ℝ (Domain d) := by
    simpa [Domain] using (show 0 < d from
      Nat.cast_pos.mp (lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp.trans hpd.le : (1 : ℝ) ≤ d)))
  refine ⟨eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Domain d)) p * d, ?_⟩
  intro 𝕜 _ u hu hs
  let : InnerProductSpace ℝ 𝕜 := RCLike.toInnerProductSpaceReal
  refine ⟨hu.continuous.memLp_of_hasCompactSupport hs,
    (classicalGradient_continuous hu).memLp_of_hasCompactSupport
      (classicalGradient_hasCompactSupport hs), ?_⟩
  have hexp : (criticalExponent d p : ℝ)⁻¹ = (p : ℝ)⁻¹ -
      (Module.finrank ℝ (Domain d) : ℝ)⁻¹ := by
    simpa [Domain] using criticalExponent_inv hp hpd
  have h := eLpNorm_le_eLpNorm_fderiv_of_eq_inner volume hu hs hp hd hexp
  have hg : eLpNorm (fderiv ℝ u) p volume ≤
      (d : ℝ≥0) * eLpNorm (classicalGradient u) p volume :=
    eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
      (hu.continuous_fderiv one_ne_zero).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => norm_le_dimension_mul_gradient (fderiv ℝ u x)) p
  calc
    eLpNorm u (criticalExponent d p) volume ≤ _ := h
    _ ≤ _ := mul_le_mul_right hg _
    _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc]

/-- Reassemble a Euclidean coordinate tuple as a finite sum. -/
theorem euclideanTuple_eq_sum {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (g : Fin d → 𝕜) :
    (WithLp.toLp 2 g : EuclideanSpace 𝕜 (Fin d)) =
      ∑ j, EuclideanSpace.single j (g j) := by
  classical
  ext i
  simp

theorem euclideanSingle_continuous {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (j : Fin d) :
    Continuous (fun z : 𝕜 => EuclideanSpace.single j z) := by
  have hi : Isometry (fun z : 𝕜 => EuclideanSpace.single j z) := by
    intro x y
    exact PiLp.edist_single_same 2 (fun _ : Fin d => 𝕜) j x y
  exact hi.continuous

/-- Finite Euclidean tuples of Lp functions are Lp. -/
theorem euclideanTuple_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞}
    (g : Fin d → X → 𝕜) (hg : ∀ j, MemLp (g j) p μ) :
    MemLp (fun x => (WithLp.toLp 2 (fun j => g j x) : EuclideanSpace 𝕜 (Fin d))) p μ := by
  classical
  simp_rw [euclideanTuple_eq_sum]
  apply memLp_finsetSum
  intro j _
  have hc := euclideanSingle_continuous (𝕜 := 𝕜) j
  apply (hg j).congr_norm (hc.comp_aestronglyMeasurable (hg j).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => (PiLp.norm_single 2 (fun _ : Fin d => 𝕜) j (g j x)).symm

/-- The Euclidean gradient is genuinely Lp for every element of the accepted
first-order derivative graph, including p=infinity and dimension zero. -/
theorem weakGradient_memLp {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d Ω 1 p) :
    MemLp (weakGradient u) p (volume.restrict (Ω : Set (Domain d))) :=
  euclideanTuple_memLp _ (fun j => Lp.memLp (u.val (firstIndex j)))

/-- The sum of coordinate Lp norms is bounded by d times the Euclidean
Lp gradient norm. This also allows coordinate-sum inequalities to be used
without changing the gradient in the theorem's conclusion. -/
theorem sum_coordinate_eLpNorm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d Ω 1 p) :
    ∑ j : Fin d, eLpNorm (u.val (firstIndex j)) p (volume.restrict (Ω : Set (Domain d))) ≤
      d * eLpNorm (weakGradient u) p (volume.restrict (Ω : Set (Domain d))) := by
  classical
  calc
    _ ≤ ∑ _j : Fin d, eLpNorm (weakGradient u) p (volume.restrict (Ω : Set (Domain d))) := by
      apply Finset.sum_le_sum
      intro j _
      exact eLpNorm_mono (Lp.memLp (u.val (firstIndex j))).aestronglyMeasurable
        (fun x => PiLp.norm_apply_le (weakGradient u x) j)
    _ = _ := by simp

/-- A full Sobolev norm bound for the Euclidean gradient. The harmless dimension
factor avoids a change to the canonical sum-component Sobolev norm. -/
theorem weakGradient_eLpNorm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.SpaceValue 𝕜 d Ω 1 p) :
    eLpNorm (weakGradient u) p (volume.restrict (Ω : Set (Domain d))) ≤
      d * ENNReal.ofReal ‖u‖ := by
  classical
  have heq : weakGradient u = ∑ j : Fin d,
      (fun x => EuclideanSpace.single j (u.val (firstIndex j) x)) := by
    ext x i
    simp [weakGradient]
  rw [heq]
  apply (eLpNorm_sum_le Fact.out).trans
  calc
    _ = ∑ j : Fin d, eLpNorm (u.val (firstIndex j)) p
        (volume.restrict (Ω : Set (Domain d))) := by
      apply Finset.sum_congr rfl
      intro j _
      apply eLpNorm_congr_norm_ae
        ((euclideanSingle_continuous j).comp_aestronglyMeasurable
          (Lp.memLp (u.val (firstIndex j))).aestronglyMeasurable)
        (Lp.memLp (u.val (firstIndex j))).aestronglyMeasurable
      exact Filter.Eventually.of_forall fun x => PiLp.norm_single 2 (fun _ : Fin d => 𝕜) j _
    _ ≤ ∑ _j : Fin d, ENNReal.ofReal ‖u‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [← Lp.enorm_def, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (PiLp.norm_apply_le u.val (firstIndex j))
    _ = _ := by simp

/-- Fatou with varying upper bounds: the norm of an a.e. limit is controlled
by the limit of the bounds. This does not assert any unproved density result. -/
theorem eLpNorm_le_of_ae_tendsto_bounds {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {F : Type*} [NormedAddCommGroup F] {q : ℝ≥0∞}
    {f : ℕ → X → F} {g : X → F} {b : ℕ → ℝ≥0∞} {B : ℝ≥0∞}
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : AEStronglyMeasurable g μ)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x)))
    (hb : Filter.Tendsto b Filter.atTop (nhds B))
    (hbound : ∀ n, eLpNorm (f n) q μ ≤ b n) : eLpNorm g q μ ≤ B := by
  apply (Lp.eLpNorm_lim_le_liminf_eLpNorm hf g hg hlim).trans
  exact (Filter.liminf_le_liminf (Filter.Eventually.of_forall hbound)).trans_eq hb.liminf_eq

/-- Identify the independently stated derivative index with the accepted
coordinate weak derivative interface. -/
theorem firstIndex_eq_coordinateIndex {d : ℕ} (j : Fin d) :
    firstIndex j = HalfSpace.coordinateIndex j := by
  classical
  apply HalfSpace.derivativeIndex_ext
  ext i
  simp [firstIndex, natIndex, HalfSpace.coordinateIndex, boundedIndex, Pi.single_apply, eq_comm]

/-- The coordinate weak-derivative estimate implies the exact Euclidean-gradient
statement. The analytic estimate in the premise remains a separate obligation. -/
theorem whole_space_of_coordinate_inequality
    (H : Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding.CoordinateWholeSpaceInequality) :
    Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding.WholeSpaceInequality := by
  intro d p hp hpd
  obtain ⟨C, hC⟩ := H d p hp hpd
  refine ⟨C * d, ?_⟩
  intro 𝕜 _ _ u
  have hw : Lines.HasWeakCoordinateDerivatives (u.val (zeroIndex d 1))
      (fun j => u.val (firstIndex j)) := by
    simpa only [firstIndex_eq_coordinateIndex] using HalfSpace.coordinate_weak_derivatives_on u
  obtain ⟨hm, hb⟩ := hC 𝕜 _ _ hw
  refine ⟨hm, ?_⟩
  calc
    _ ≤ (C : ℝ≥0∞) * ∑ j : Fin d, eLpNorm (u.val (firstIndex j)) p volume := hb
    _ ≤ (C : ℝ≥0∞) * (d * eLpNorm (weakGradient u) p volume) := by
      apply mul_le_mul_right
      simpa using sum_coordinate_eLpNorm_le u
    _ = _ := by simp only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc]

/-- A direct reduction of the subcritical bounded-domain assertion to the
whole-space inequality using the accepted extension theorem. -/
theorem bounded_domain_of_whole_space
    (H : Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding.WholeSpaceInequality) :
    Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding.BoundedDomainInequality := by
  intro 𝕜 _ d Ω hC1 hΩ p hp hpd
  let : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  have hfront : IsCompact (frontier (Ω : Set (Domain d))) :=
    hΩ.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨T, E, hE, _hcompat, _hsupport⟩ := C1Extension.extension_exists 𝕜 d Ω hC1 hfront
  obtain ⟨C, hC⟩ := H d p hp hpd
  refine ⟨C * d * (‖E p‖).toNNReal, ?_⟩
  intro _ u
  obtain ⟨hm, hb⟩ := hC 𝕜 (E p u)
  have hmΩ : MemLp (u.val (zeroIndex d 1)) (criticalExponent d p)
      (volume.restrict (Ω : Set (Domain d))) :=
    (hm.restrict (Ω : Set (Domain d))).ae_eq (hE p u)
  refine ⟨hmΩ, ?_⟩
  calc
    _ = eLpNorm ((E p u).val (zeroIndex d 1)) (criticalExponent d p)
        (volume.restrict (Ω : Set (Domain d))) := eLpNorm_congr_ae (hE p u).symm
    _ ≤ eLpNorm ((E p u).val (zeroIndex d 1)) (criticalExponent d p) volume :=
      eLpNorm_restrict_le _ _ _ _
    _ ≤ (C : ℝ≥0∞) * eLpNorm (weakGradient (E p u)) p volume := hb
    _ ≤ (C : ℝ≥0∞) * (d * ENNReal.ofReal ‖E p u‖) := by
      apply mul_le_mul_right
      simpa using weakGradient_eLpNorm_le (E p u)
    _ ≤ (C : ℝ≥0∞) * (d * (ENNReal.ofReal ‖E p‖ * ENNReal.ofReal ‖u‖)) := by
      apply mul_le_mul_right
      apply mul_le_mul_right
      simpa only [ENNReal.ofReal_mul (norm_nonneg (E p))] using
        ENNReal.ofReal_le_ofReal ((E p).le_opNorm u)
    _ = _ := by
      simp only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc]
      rfl

/-- Removing the compact support hypothesis for smooth Lp functions by scaled
cutoffs. The derivative norm is the operator norm on the accepted domain. -/
theorem smooth_whole_space_inequality {d : ℕ} {p : ℝ≥0}
    (hp : 1 ≤ p) (hpd : p < d) {𝕜 : Type} [RCLike 𝕜]
    {u : Domain d → 𝕜} (hu : ContDiff ℝ 1 u)
    (huLp : MemLp u p volume) (hDu : MemLp (fderiv ℝ u) p volume) :
    eLpNorm u (criticalExponent d p) volume ≤
      (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Domain d)) p : ℝ≥0∞) *
        eLpNorm (fderiv ℝ u) p volume := by
  let : InnerProductSpace ℝ 𝕜 := RCLike.toInnerProductSpaceReal
  let b : ContDiffBump (0 : Domain d) := ⟨1, 2, by norm_num, by norm_num⟩
  have hb : ContDiff ℝ 1 (b : Domain d → ℝ) := b.contDiff
  obtain ⟨M, hM⟩ := ((hb.continuous_fderiv one_ne_zero).norm.bddAbove_range_of_hasCompactSupport
    (b.hasCompactSupport.fderiv ℝ).norm)
  have hM0 : 0 ≤ M := (norm_nonneg (fderiv ℝ (b : Domain d → ℝ) 0)).trans (hM ⟨0, rfl⟩)
  let a : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a, inv_eq_one_div] using tendsto_one_div_add_atTop_nhds_zero_nat
  let v : ℕ → Domain d → 𝕜 := fun n x => b (a n • x) • u x
  have hv (n : ℕ) : ContDiff ℝ 1 (v n) :=
    (hb.comp (contDiff_id.const_smul (a n))).smul hu
  have hvs (n : ℕ) : HasCompactSupport (v n) := by
    change HasCompactSupport ((fun x => b (a n • x)) • u)
    apply HasCompactSupport.smul_right
    exact b.hasCompactSupport.comp_homeomorph
      (Homeomorph.smul (Units.mk0 (a n) (ha n).ne'))
  have hder (n : ℕ) (x : Domain d) :
      ‖fderiv ℝ (v n) x‖ ≤ ‖fderiv ℝ u x‖ + (a n * M) * ‖u x‖ := by
    have hc : DifferentiableAt ℝ (fun y : Domain d => b (a n • y)) x :=
      (hb.comp (contDiff_id.const_smul (a n))).differentiable (by simp) x
    have he : fderiv ℝ (fun y : Domain d => b (a n • y)) x =
        (fderiv ℝ (b : Domain d → ℝ) (a n • x)).comp
          (a n • ContinuousLinearMap.id ℝ (Domain d)) := by
      exact (hb.differentiable (by simp) _).hasFDerivAt.comp x
        ((a n • ContinuousLinearMap.id ℝ (Domain d)).hasFDerivAt) |>.fderiv
    have hbabs : ‖b (a n • x)‖ ≤ 1 := by
      rw [Real.norm_of_nonneg b.nonneg]
      exact b.le_one
    have hbc : ‖fderiv ℝ (fun y : Domain d => b (a n • y)) x‖ ≤ a n * M := by
      rw [he]
      calc
        _ ≤ ‖fderiv ℝ (b : Domain d → ℝ) (a n • x)‖ *
            ‖a n • ContinuousLinearMap.id ℝ (Domain d)‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ M * (a n * 1) := by
          gcongr
          · exact hM ⟨_, rfl⟩
          · rw [norm_smul, Real.norm_of_nonneg (ha n).le]
            gcongr
            exact ContinuousLinearMap.norm_id_le
        _ = _ := by ring
    change ‖fderiv ℝ (fun y => b (a n • y) • u y) x‖ ≤ _
    rw [fderiv_fun_smul hc (hu.differentiable (by simp) x)]
    calc
      _ ≤ ‖b (a n • x) • fderiv ℝ u x‖ +
          ‖(fderiv ℝ (fun y => b (a n • y)) x).smulRight (u x)‖ := norm_add_le _ _
      _ ≤ ‖fderiv ℝ u x‖ + (a n * M) * ‖u x‖ := by
        apply add_le_add
        · simpa only [norm_smul, one_mul] using mul_le_mul_of_nonneg_right hbabs (norm_nonneg _)
        · exact (le_of_eq (ContinuousLinearMap.norm_smulRight_apply _ _)).trans
            (mul_le_mul_of_nonneg_right hbc (norm_nonneg _))
  have hnorm (n : ℕ) : eLpNorm (fderiv ℝ (v n)) p volume ≤
      eLpNorm (fderiv ℝ u) p volume +
        ENNReal.ofReal (a n * M) * eLpNorm u p volume := by
    calc
      _ ≤ eLpNorm (fun x => ‖fderiv ℝ u x‖ + (a n * M) * ‖u x‖) p volume :=
        eLpNorm_mono (hv n |>.continuous_fderiv one_ne_zero |>.aestronglyMeasurable)
          (fun x => (hder n x).trans_eq (Real.norm_of_nonneg (by positivity)).symm)
      _ ≤ eLpNorm (fun x => ‖fderiv ℝ u x‖) p volume +
          eLpNorm (fun x => (a n * M) * ‖u x‖) p volume :=
        eLpNorm_add_le (by exact_mod_cast hp)
      _ = _ := by
        rw [show (fun x => (a n * M) * ‖u x‖) = (a n * M) • (fun x => ‖u x‖) from rfl,
          eLpNorm_const_smul, eLpNorm_norm, eLpNorm_norm,
          Real.enorm_eq_ofReal (mul_nonneg (ha n).le hM0)]
        · exact huLp.aestronglyMeasurable
        · exact hDu.aestronglyMeasurable
  have hd : 0 < Module.finrank ℝ (Domain d) := by
    simp only [Domain, Module.finrank_pi, Fintype.card_fin]
    exact_mod_cast (lt_of_lt_of_le zero_lt_one (hp.trans hpd.le))
  have hexp : (criticalExponent d p : ℝ)⁻¹ = (p : ℝ)⁻¹ -
      (Module.finrank ℝ (Domain d) : ℝ)⁻¹ := by
    simpa [Domain] using criticalExponent_inv hp hpd
  refine eLpNorm_le_of_ae_tendsto_bounds
    (fun n => (hv n).continuous.aestronglyMeasurable) hu.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
    (show Tendsto (fun n =>
        (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Domain d)) p : ℝ≥0∞) *
        (eLpNorm (fderiv ℝ u) p volume + ENNReal.ofReal (a n * M) * eLpNorm u p volume))
      atTop (𝓝 _) from ?_)
    (fun n => (eLpNorm_le_eLpNorm_fderiv_of_eq_inner volume (hv n) (hvs n) hp hd hexp).trans
      (mul_le_mul_right (hnorm n) _))
  · rename_i x
    have hbx : Tendsto (fun n => b (a n • x)) atTop (𝓝 1) := by
      have h := b.continuous.continuousAt.tendsto.comp (hat.smul_const x)
      have hb0 : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
      simpa only [Function.comp_def, zero_smul, hb0] using h
    simpa only [one_smul] using hbx.smul_const (u x)
  · have hzero : Tendsto (fun n => ENNReal.ofReal (a n * M) * eLpNorm u p volume)
        atTop (𝓝 0) := by
      convert ENNReal.Tendsto.mul_const (b := eLpNorm u p volume)
        (ENNReal.tendsto_ofReal (hat.mul_const M)) (Or.inr huLp.eLpNorm_lt_top.ne) using 1 <;> simp
    simpa using ENNReal.Tendsto.const_mul
      (a := (eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Domain d)) p : ℝ≥0∞))
      (tendsto_const_nhds.add hzero) (Or.inr ENNReal.coe_ne_top)

open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
open SmoothApproximateIdentitiesSpec

/-- On the whole space, convolution commutes with every weak derivative at
all positive scales. There is no boundary support condition to check. -/
theorem regularize_derivative_top {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d ⊤ 1 p)
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε)
    (j : Fin d) :
    (fun x => fderiv ℝ (Smoothing.regularize ρ ε (u.val (zeroIndex d 1))) x
      (coordinateVector j)) = Smoothing.regularize ρ ε (u.val (firstIndex j)) := by
  rw [Smoothing.regularize_eq_kernelTest ρ hρ hε,
    Smoothing.regularize_eq_kernelTest ρ hρ hε]
  funext x
  have h := Smoothing.interior_convolution_identity u (firstIndex j)
    (Smoothing.scaledKernelTest ρ hρ ε hε) x (Set.subset_univ _)
  simpa only [Smoothing.classicalDerivative, firstIndex_eq_coordinateIndex,
    HalfSpace.coordinateIndex, natIndex_boundedIndex, Lines.multiIndexWord_single,
    List.reverse_singleton, partialFunction] using h

/-- Mollification is an Lp contraction, including both endpoints. -/
theorem regularize_eLpNorm_le {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p)
    (ρ : Domain d → ℝ) (hρ : IsMollifier ρ) {ε : ℝ} (hε : 0 < ε) :
    eLpNorm (Smoothing.regularize ρ ε u) p volume ≤ eLpNorm u p volume := by
  have hk := scaledKernel_properties ρ hρ ε hε
  have hki : MemLp (ScaledKernelValue ρ ε) 1 volume :=
    memLp_one_iff_integrable.mpr (hk.1.continuous.integrable_of_hasCompactSupport hk.2.1)
  have hb := (young_l1_lp_endpoint p Fact.out (fun x => (ScaledKernelValue ρ ε x : 𝕜))
    (Smoothing.zeroExtend u) hki.ofReal (Smoothing.zeroExtend_memLp u)).2.2.2
  have he : eLpNorm (fun x => (ScaledKernelValue ρ ε x : 𝕜)) 1 volume = 1 := by
    calc
      _ = eLpNorm (ScaledKernelValue ρ ε) 1 volume :=
        eLpNorm_congr_norm_ae hki.ofReal.aestronglyMeasurable hki.aestronglyMeasurable
          (Filter.Eventually.of_forall fun x => RCLike.norm_ofReal _)
      _ = 1 := Smoothing.scaledKernel_eLpNorm_one ρ hρ hε
  have huNorm : ENNReal.ofReal ‖u‖ = eLpNorm u p volume := by
    simpa [ofReal_norm] using (Lp.enorm_def u)
  rw [he, one_mul, Smoothing.zeroExtend_eLpNorm, huNorm] at hb
  convert hb using 1
  congr 1
  funext x
  change (∫ y, ScaledKernelValue ρ ε y • Smoothing.zeroExtend u (x-y)) =
    ∫ y, (ScaledKernelValue ρ ε y : 𝕜) * Smoothing.zeroExtend u (x-y)
  simp only [RCLike.real_smul_eq_coe_mul]


/-- The operator derivative is Lp if all its coordinate evaluations are Lp. -/
theorem fderiv_memLp_of_coordinates {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} {f : Domain d → 𝕜} (hf : ContDiff ℝ 1 f)
    (hg : ∀ j, MemLp (fun x => fderiv ℝ f x (coordinateVector j)) p volume) :
    MemLp (fderiv ℝ f) p volume := by
  classical
  have hs := memLp_finsetSum (μ := volume) Finset.univ (fun j _ => (hg j).norm)
  apply hs.mono' (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => norm_le_sum_coordinate_norm (fderiv ℝ f x)

/-- The operator derivative norm is bounded by the sum of coordinate norms. -/
theorem eLpNorm_fderiv_le_sum {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {f : Domain d → 𝕜} (hf : ContDiff ℝ 1 f) :
    eLpNorm (fderiv ℝ f) p volume ≤
      ∑ j : Fin d, eLpNorm (fun x => fderiv ℝ f x (coordinateVector j)) p volume := by
  classical
  calc
    _ ≤ eLpNorm (fun x => ∑ j : Fin d, ‖fderiv ℝ f x (coordinateVector j)‖) p volume := by
      apply eLpNorm_mono (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable
      intro x
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
      exact norm_le_sum_coordinate_norm _
    _ ≤ ∑ j : Fin d, eLpNorm (fun x => ‖fderiv ℝ f x (coordinateVector j)‖) p volume :=
      by simpa only [Finset.sum_apply, Finset.sum_fn] using
        (eLpNorm_sum_le (f := fun j x => ‖fderiv ℝ f x (coordinateVector j)‖) (s := Finset.univ) (μ := volume) hp)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact eLpNorm_norm _ ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable

/-- The homogeneous inequality on the full distributional Sobolev space.
Mollification is used at every positive scale, then an a.e. convergent
subsequence and Fatou pass the uniform estimate to the original class. -/
theorem whole_space_inequality :
    Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding.WholeSpaceInequality := by
  intro d p hp hpd
  let C := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Domain d)) p
  refine ⟨C * d, ?_⟩
  intro 𝕜 _ _ u
  obtain ⟨ρ, hρ⟩ := Smoothing.exists_mollifier d
  let a : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hat : Tendsto a atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [a, inv_eq_one_div] using tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall ha⟩
  let f : ℕ → Domain d → 𝕜 := fun n =>
    Smoothing.regularize ρ (a n) (u.val (zeroIndex d 1))
  have hf (n : ℕ) : ContDiff ℝ 1 (f n) :=
    (Smoothing.regularize_contDiff ρ hρ (ha n) _).of_le (by simp)
  have hcoord (n : ℕ) (j : Fin d) :
      (fun x => fderiv ℝ (f n) x (coordinateVector j)) =
        Smoothing.regularize ρ (a n) (u.val (firstIndex j)) :=
    regularize_derivative_top u ρ hρ (ha n) j
  have hg (n : ℕ) (j : Fin d) : MemLp
      (fun x => fderiv ℝ (f n) x (coordinateVector j)) p volume := by
    rw [hcoord]
    exact Smoothing.regularize_memLp ρ hρ (ha n) _
  have hb (n : ℕ) : eLpNorm (f n) (criticalExponent d p) volume ≤
      (C : ℝ≥0∞) * (d * eLpNorm (weakGradient u) p volume) := by
    calc
      _ ≤ (C : ℝ≥0∞) * eLpNorm (fderiv ℝ (f n)) p volume :=
        smooth_whole_space_inequality hp hpd (hf n)
          (Smoothing.regularize_memLp ρ hρ (ha n) _) (fderiv_memLp_of_coordinates (hf n) (hg n))
      _ ≤ (C : ℝ≥0∞) * ∑ j : Fin d,
          eLpNorm (fun x => fderiv ℝ (f n) x (coordinateVector j)) p volume :=
        mul_le_mul_right (eLpNorm_fderiv_le_sum (by exact_mod_cast hp) (hf n)) _
      _ ≤ (C : ℝ≥0∞) * ∑ j : Fin d, eLpNorm (u.val (firstIndex j)) p volume := by
        apply mul_le_mul_right
        apply Finset.sum_le_sum
        intro j _
        rw [hcoord]
        exact regularize_eLpNorm_le _ ρ hρ (ha n)
      _ ≤ _ := by
        apply mul_le_mul_right
        simpa using sum_coordinate_eLpNorm_le u
  have ht : Tendsto (fun n => eLpNorm (f n - (u.val (zeroIndex d 1) : Domain d → 𝕜)) p volume)
      atTop (𝓝 0) := by
    have h := (Smoothing.regularize_zeroExtend_tendsto (p := (p : ℝ≥0∞))
      ENNReal.coe_ne_top ρ hρ (u.val (zeroIndex d 1))).comp hat
    simpa only [Function.comp_def, f, Smoothing.zeroExtend, TopologicalSpace.Opens.coe_top, Set.indicator_univ] using h
  obtain ⟨ns, _hns, hns⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hp).ne') ht).exists_seq_tendsto_ae
  have hbound : eLpNorm (u.val (zeroIndex d 1)) (criticalExponent d p) volume ≤
      (C : ℝ≥0∞) * (d * eLpNorm (weakGradient u) p volume) :=
    eLpNorm_le_of_ae_tendsto_bounds
      (fun n => (hf (ns n)).continuous.aestronglyMeasurable)
      (by simpa using (Lp.memLp (u.val (zeroIndex d 1))).aestronglyMeasurable)
      hns tendsto_const_nhds (fun n => hb (ns n))
  have hgrad : eLpNorm (weakGradient u) p volume < ∞ := by
    simpa using (weakGradient_memLp u).eLpNorm_lt_top
  refine ⟨hbound.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (ENNReal.mul_lt_top (by simp) hgrad)), ?_⟩
  simpa only [ENNReal.coe_mul, ENNReal.coe_natCast, mul_assoc] using hbound


/-- The subcritical embedding on bounded C¹ domains, with the full Sobolev norm. -/
theorem bounded_domain_inequality :
    Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding.BoundedDomainInequality :=
  bounded_domain_of_whole_space whole_space_inequality


/-- Choose a subcritical source exponent whose Sobolev conjugate exceeds
any prescribed finite target exponent in dimensions at least two. -/
theorem choose_subcritical_exponent {d : ℕ} (hd : 2 ≤ d) (q : ℝ≥0) (hq : 1 ≤ q) :
    ∃ p : ℝ≥0, 1 ≤ p ∧ p < d ∧ q ≤ criticalExponent d p := by
  let p : ℝ≥0 := d * (q + 1) / (d + q + 1)
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hden : (0 : ℝ≥0) < d + q + 1 := by positivity
  have hp : 1 ≤ p := by
    dsimp [p]
    rw [le_div_iff₀ hden]
    have : (1 : ℝ) * (d + q + 1) ≤ d * (q + 1) := by nlinarith
    exact_mod_cast this
  have hpd : p < d := by
    dsimp [p]
    rw [div_lt_iff₀ hden]
    have : (d : ℝ) * (q + 1) < d * (d + q + 1) := by nlinarith
    exact_mod_cast this
  refine ⟨p, hp, hpd, ?_⟩
  have heq : (criticalExponent d p : ℝ) = q + 1 := by
    rw [criticalExponent_coe hpd]
    have hpR : (p : ℝ) = d * ((q : ℝ) + 1) / (d + q + 1) := by simp [p]
    apply (div_eq_iff (sub_pos.mpr (by exact_mod_cast hpd : (p : ℝ) < d)).ne').mpr
    rw [hpR]
    field_simp
    <;> ring
  exact_mod_cast (show (q : ℝ) ≤ criticalExponent d p by rw [heq]; linarith)

/-- Finite-measure exponent lowering preserves the derivative graph and
controls its sum norm by the usual Hölder measure factor. -/
theorem lowerExponent_eNorm_le {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {m : ℕ} {p r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ r)]
    [IsFiniteMeasure (volume.restrict (Ω : Set (Domain d)))] (h : r ≤ p)
    (u : SpaceValue 𝕜 d Ω m p) :
    ENNReal.ofReal ‖C1Extension.Transport.lowerExponent h u‖ ≤ ENNReal.ofReal ‖u‖ *
      (volume.restrict (Ω : Set (Domain d))) Set.univ ^ (1/r.toReal - 1/p.toReal) := by
  classical
  have hnorm (v : SpaceValue 𝕜 d Ω m p) :
      ENNReal.ofReal ‖v‖ = ∑ α, eLpNorm (v.val α) p (volume.restrict (Ω : Set (Domain d))) := by
    rw [sobolev_norm_formula]
    simp only [NormValue]
    rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => norm_nonneg (v.val α))]
    simp only [ofReal_norm, Lp.enorm_def]
  have hnormr (v : SpaceValue 𝕜 d Ω m r) :
      ENNReal.ofReal ‖v‖ = ∑ α, eLpNorm (v.val α) r (volume.restrict (Ω : Set (Domain d))) := by
    rw [sobolev_norm_formula]
    simp only [NormValue]
    rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => norm_nonneg (v.val α))]
    simp only [ofReal_norm, Lp.enorm_def]
  rw [hnorm, hnormr]
  calc
    _ ≤ ∑ α, eLpNorm (u.val α) p (volume.restrict (Ω : Set (Domain d))) *
        (volume.restrict (Ω : Set (Domain d))) Set.univ ^ (1/r.toReal - 1/p.toReal) := by
      apply Finset.sum_le_sum
      intro α _
      rw [eLpNorm_congr_ae (C1Extension.Transport.lowerExponent_coe h u α)]
      exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ h (Lp.memLp (u.val α)).aestronglyMeasurable
    _ = _ := (Finset.sum_mul _ _ _).symm


/-- The critical embedding in dimensions at least two follows by lowering
the Sobolev exponent and then the target exponent on the finite-measure domain. -/
theorem critical_bounded_domain_inequality_of_two_le
    (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (hd : 2 ≤ d) (Ω : Opens (Domain d))
    (hC1 : C1Extension.IsC1Domain Ω) (hΩ : Bornology.IsBounded (Ω : Set (Domain d)))
    (q : ℝ≥0) (hq : 1 ≤ q) :
    ∃ C : ℝ≥0, ∀ [Fact (1 ≤ (d : ℝ≥0∞))] (u : SpaceValue 𝕜 d Ω 1 d),
      MemLp (u.val (zeroIndex d 1)) q (volume.restrict (Ω : Set (Domain d))) ∧
      eLpNorm (u.val (zeroIndex d 1)) q (volume.restrict (Ω : Set (Domain d))) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
  let μ := volume.restrict (Ω : Set (Domain d))
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hΩ.measure_lt_top.ne
  obtain ⟨p, hp, hpd, hqp⟩ := choose_subcritical_exponent hd q hq
  letI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
  obtain ⟨C, hC⟩ := bounded_domain_inequality 𝕜 d Ω hC1 hΩ p hp hpd
  let A : ℝ≥0∞ := μ Set.univ ^ (1/(p : ℝ) - 1/(d : ℝ))
  let B : ℝ≥0∞ := μ Set.univ ^ (1/(q : ℝ) - 1/(criticalExponent d p : ℝ))
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hp)
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hq)
  have hA : A ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg
    (sub_nonneg.mpr (one_div_le_one_div_of_le hp0 (by exact_mod_cast hpd.le)))
      (measure_lt_top μ Set.univ).ne).ne
  have hB : B ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg
    (sub_nonneg.mpr (one_div_le_one_div_of_le hq0 (by exact_mod_cast hqp)))
      (measure_lt_top μ Set.univ).ne).ne
  refine ⟨B.toNNReal * C * A.toNNReal, ?_⟩
  intro _ u
  have hpd' : (p : ℝ≥0∞) ≤ d := by exact_mod_cast hpd.le
  let v := C1Extension.Transport.lowerExponent hpd' u
  obtain ⟨hmem, hbound⟩ := hC v
  have heq : v.val (zeroIndex d 1) =ᵐ[μ] u.val (zeroIndex d 1) :=
    C1Extension.Transport.lowerExponent_coe hpd' u (zeroIndex d 1)
  have hmemu : MemLp (u.val (zeroIndex d 1)) (criticalExponent d p) μ := hmem.ae_eq heq
  refine ⟨hmemu.mono_exponent (by exact_mod_cast hqp), ?_⟩
  have hnorm : ENNReal.ofReal ‖v‖ ≤ ENNReal.ofReal ‖u‖ * A := by
    simpa only [ENNReal.coe_toReal, ENNReal.toReal_natCast] using lowerExponent_eNorm_le hpd' u
  calc
    _ ≤ eLpNorm (u.val (zeroIndex d 1)) (criticalExponent d p) μ * B :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by exact_mod_cast hqp)
        hmemu.aestronglyMeasurable
    _ = eLpNorm (v.val (zeroIndex d 1)) (criticalExponent d p) μ * B := by
      rw [eLpNorm_congr_ae heq]
    _ ≤ ((C : ℝ≥0∞) * ENNReal.ofReal ‖v‖) * B := by gcongr
    _ ≤ ((C : ℝ≥0∞) * (ENNReal.ofReal ‖u‖ * A)) * B := by
      gcongr
    _ = _ := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_toNNReal hA,
        ENNReal.coe_toNNReal hB]
      ring

/-- The one-dimensional critical embedding on an arbitrary bounded C¹ open set. -/
theorem critical_one_bounded_domain
    (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Domain 1))
    (hC1 : C1Extension.IsC1Domain Ω) (hΩ : Bornology.IsBounded (Ω : Set (Domain 1)))
    (q : ℝ≥0) (_hq : 1 ≤ q) :
    ∃ C : ℝ≥0, ∀ [Fact (1 ≤ (1 : ℝ≥0∞))] (u : SpaceValue 𝕜 1 Ω 1 1),
      MemLp (u.val (zeroIndex 1 1)) q (volume.restrict (Ω : Set (Domain 1))) ∧
      eLpNorm (u.val (zeroIndex 1 1)) q (volume.restrict (Ω : Set (Domain 1))) ≤
        (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
  letI : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  have hfront : IsCompact (frontier (Ω : Set (Domain 1))) :=
    hΩ.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨T, E, hE, _, _⟩ := C1Extension.extension_exists 𝕜 1 Ω hC1 hfront
  obtain ⟨r, hr, hball⟩ := hΩ.subset_ball_lt 1 (0 : Domain 1)
  let I : Opens ℝ := ⟨Set.Ioo (-r) r, isOpen_Ioo⟩
  have hΩI : Ω ≤ OneDimensional.lineDomain I := by
    intro x hx
    have hxnorm : ‖x‖ < r := by simpa using hball hx
    have hxcoord : |x 0| < r := by simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm x 0).trans_lt hxnorm
    exact abs_lt.mp hxcoord
  have hrr : -r < r := by linarith
  have hμ : volume (Ω : Set (Domain 1)) ≠ ∞ :=
    (measure_mono (s := (Ω : Set (Domain 1))) subset_closure).trans_lt
      hΩ.isCompact_closure.measure_lt_top |>.ne
  let A : ℝ≥0∞ := volume (Ω : Set (Domain 1)) ^ (1 / (q : ℝ))
  have hA : A ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hμ
  refine ⟨2 * ‖E 1‖₊ * A.toNNReal, ?_⟩
  intro _ u
  let v : OneDimensional.W1p 𝕜 I 1 := C1Extension.restrictSobolev le_top (E 1 u)
  obtain ⟨f, hf⟩ := OneDimensional.representative_existence 𝕜 I Set.ordConnected_Ioo 1 v
  have hvinfty := OneDimensional.finite_interval_essential_supremum 𝕜 (-r) r hrr 1 v f hf
  have hbase : ‖OneDimensional.baseLp v‖ ≤ ‖v‖ := PiLp.norm_apply_le v.val _
  have hder : ‖OneDimensional.derivativeLp v‖ ≤ ‖v‖ := PiLp.norm_apply_le v.val _
  have hlen : (r - -r)⁻¹ ≤ 1 := (inv_le_one₀ (by linarith)).mpr (by linarith)
  have hvreal : (r - -r) ^ (-OneDimensional.reciprocalExponent 1) *
        ‖OneDimensional.baseLp v‖ + (r - -r) ^
        (1 - OneDimensional.reciprocalExponent 1) * ‖OneDimensional.derivativeLp v‖ ≤
        2 * ‖E 1‖ * ‖u‖ := by
    simp only [OneDimensional.reciprocalExponent, ENNReal.toReal_one, div_one,
      Real.rpow_neg_one, sub_self, Real.rpow_zero, one_mul]
    calc
      (r - -r)⁻¹ * ‖OneDimensional.baseLp v‖ + ‖OneDimensional.derivativeLp v‖ ≤
          ‖v‖ + ‖v‖ := by
        apply add_le_add _ hder
        exact (mul_le_mul_of_nonneg_right hlen (norm_nonneg _)).trans (by simpa using hbase)
      _ ≤ 2 * ‖E 1‖ * ‖u‖ := by
        have hvnorm := C1Extension.restrictSobolev_norm_le (le_top : OneDimensional.lineDomain I ≤ ⊤) (E 1 u)
        have hEnorm := (E 1).le_opNorm u
        dsimp [v] at *
        nlinarith
  have hrestr : (OneDimensional.baseLp v : Domain 1 → 𝕜) =ᵐ[volume.restrict (Ω : Set (Domain 1))]
      (E 1 u).val (zeroIndex 1 1) :=
    (C1Extension.restrictSobolev_coe le_top (E 1 u) (zeroIndex 1 1)).filter_mono
      (ae_mono (Measure.restrict_mono hΩI le_rfl))
  have huinfty : eLpNorm (u.val (zeroIndex 1 1)) ∞ (volume.restrict (Ω : Set (Domain 1))) ≤
      ENNReal.ofReal (2 * ‖E 1‖ * ‖u‖) := by
    calc
      _ = eLpNorm (OneDimensional.baseLp v) ∞ (volume.restrict (Ω : Set (Domain 1))) :=
        eLpNorm_congr_ae ((hE 1 u).symm.trans hrestr.symm)
      _ ≤ eLpNorm (OneDimensional.baseLp v) ∞
          (volume.restrict (OneDimensional.lineDomain I : Set (Domain 1))) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono hΩI le_rfl)
      _ ≤ _ := hvinfty.trans (ENNReal.ofReal_le_ofReal hvreal)
  have hubound : eLpNorm (u.val (zeroIndex 1 1)) q (volume.restrict (Ω : Set (Domain 1))) ≤
      ((2 * ‖E 1‖₊ * A.toNNReal : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
    calc
      _ ≤ eLpNorm (u.val (zeroIndex 1 1)) ∞ (volume.restrict (Ω : Set (Domain 1))) * A := by
        simpa [A] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ (le_top : (q : ℝ≥0∞) ≤ ∞)
          (Lp.memLp (u.val (zeroIndex 1 1))).aestronglyMeasurable
      _ ≤ ENNReal.ofReal (2 * ‖E 1‖ * ‖u‖) * A := mul_le_mul_left huinfty A
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        simp only [ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_toNNReal hA, ENNReal.ofReal_ofNat]
        rw [show ENNReal.ofReal ‖E 1‖ = (‖E 1‖₊ : ℝ≥0∞) from ENNReal.ofReal_eq_coe_nnreal _]
        change (2 * (‖E 1‖₊ : ℝ≥0∞) * ENNReal.ofReal ‖u‖) * A =
          (2 * (‖E 1‖₊ : ℝ≥0∞) * A) * ENNReal.ofReal ‖u‖
        ac_rfl
  exact ⟨hubound.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top ENNReal.ofReal_lt_top), hubound⟩


/-- Every finite target exponent is admitted at p=d on bounded C¹ domains.
Dimension one uses the interval estimate after extension; higher dimensions
use finite-measure exponent lowering. -/
theorem critical_bounded_domain_inequality :
    Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding.CriticalBoundedDomainInequality := by
  intro 𝕜 _ d hd Ω hC1 hΩ q hq
  by_cases hd1 : d = 1
  · subst d
    let P (p : ℝ≥0∞) : Prop :=
      ∃ C : ℝ≥0, ∀ [Fact (1 ≤ p)] (u : SpaceValue 𝕜 1 Ω 1 p),
        MemLp (u.val (zeroIndex 1 1)) q (volume.restrict (Ω : Set (Domain 1))) ∧
        eLpNorm (u.val (zeroIndex 1 1)) q (volume.restrict (Ω : Set (Domain 1))) ≤
          (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖
    change P ((1 : ℕ) : ℝ≥0∞)
    have h : P 1 := critical_one_bounded_domain 𝕜 Ω hC1 hΩ q hq
    exact (Nat.cast_one : ((1 : ℕ) : ℝ≥0∞) = 1) ▸ h
  · exact critical_bounded_domain_inequality_of_two_le 𝕜 d (by omega) Ω hC1 hΩ q hq

end ExpandedFA.Sobolev.Subcritical
