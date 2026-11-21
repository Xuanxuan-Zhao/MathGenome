import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.LocalW2p
import MathGenome.Internal.LinearPDE.P201.Elliptic.NewtonLp
import MathGenome.Internal.LinearPDE.P201.Elliptic.WholeSpaceW2p
import MathGenome.Internal.LinearPDE.P201.Potential.Weyl
import MathGenome.Internal.LinearPDE.P201.Potential.DerivativesLiouville
import MathGenome.Internal.FourierSobolev.P102.U4.DifferenceQuotientConverse
import MathGenome.Internal.FourierSobolev.P102.U4.WholeSpaceDensity

/-! Local distributional regularity and estimates for `pde:elliptic-poisson-w2p`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal ContDiff

namespace P201.Elliptic.LocalW2p
open P201Specs
open P201Specs.Elliptic.LocalW2p

/-- Almost-everywhere identification with the original function identifies
all weak derivatives with the original distribution as well. -/
theorem representsOn_of_ae {n : ℕ} {V : Domain n} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] {u : Space n → ℝ} (hu : LocallyIntegrableOn u V volume)
    (w : W ℝ V 2 p)
    (hw : (P102.U4.sobolevUnderlying w : Space n → ℝ) =ᵐ[domainMeasure V] u) :
    RepresentsOn u w := by
  have he := (P102.U4.regular_injectivity n ℝ V _ _
    (P102.U4.domainLp_locallyIntegrable V p _) hu).mpr hw
  refine ⟨hw, he, ?_⟩
  intro α
  change P102.U4.distributionPartial α.val (P102.U4.regularDistribution V u) = _
  rw [← he]
  exact P102.U4.sobolev_derivative_distribution V 2 p w α

/-- Build the canonical Sobolev element from actual Lᵖ weak derivative
functions. The equality records the full sum norm, including order zero. -/
theorem exists_sobolev_of_weak_derivatives {n : ℕ} (V : Domain n) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : Space n → ℝ) (hu : MemLp u p (domainMeasure V))
    (D : P102.U4.SobolevIndex n 2 → Space n → ℝ)
    (hD : ∀ α, MemLp (D α) p (domainMeasure V))
    (hweak : ∀ α, distributionDerivative α.val (regularDistribution V u) =
      regularDistribution V (D α)) :
    ∃ w : W ℝ V 2 p, RepresentsOn u w ∧
      ‖w‖ = ∑ α : P102.U4.SobolevIndex n 2,
        (eLpNorm (D α) p (domainMeasure V)).toReal := by
  have huloc : LocallyIntegrableOn u V volume :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (hu.locallyIntegrable Fact.out)
  have hreg : regularDistribution V (hu.toLp u) = regularDistribution V u :=
    (P102.U4.regular_injectivity n ℝ V _ _
      (P102.U4.domainLp_locallyIntegrable V p _) huloc).mpr hu.coeFn_toLp
  have hmem : P102.U4.HasSobolevDerivatives V 2 p (hu.toLp u) := by
    intro α hα
    let β : P102.U4.SobolevIndex n 2 := ⟨α, hα⟩
    refine ⟨(hD β).toLp (D β), ?_⟩
    change distributionDerivative β.val (regularDistribution V (hu.toLp u)) =
      regularDistribution V ((hD β).toLp (D β))
    rw [hreg, hweak β]
    exact (P102.U4.regular_injectivity n ℝ V _ _
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((hD β).locallyIntegrable Fact.out))
      (P102.U4.domainLp_locallyIntegrable V p _)).mpr (hD β).coeFn_toLp.symm
  obtain ⟨w, hw⟩ := (Set.ext_iff.mp (P102.U4.sobolev_range V 2 p) (hu.toLp u)).mpr hmem
  have hae : (P102.U4.sobolevUnderlying w : Space n → ℝ) =ᵐ[domainMeasure V] u :=
    hw ▸ hu.coeFn_toLp
  have hrep := representsOn_of_ae huloc w hae
  refine ⟨w, hrep, ?_⟩
  rw [P102.U4.sobolev_norm V 2 p]
  apply Finset.sum_congr rfl
  intro α _
  have he : (hD α).toLp (D α) = P102.U4.sobolevDerivative w α := by
    apply P102.U4.sobolev_derivative_unique V 2 p w α
    change distributionDerivative α.val (regularDistribution V (P102.U4.sobolevUnderlying w)) =
      regularDistribution V ((hD α).toLp (D α))
    rw [hw, hreg, hweak α]
    exact (P102.U4.regular_injectivity n ℝ V _ _
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((hD α).locallyIntegrable Fact.out))
      (P102.U4.domainLp_locallyIntegrable V p _)).mpr (hD α).coeFn_toLp.symm
  rw [← he, Lp.norm_toLp]

/-- Distribution derivatives commute with restriction to an open subset. -/
theorem restrict_derivative {n : ℕ} {V Ω : Domain n} (h : V ≤ Ω)
    (T : Distribution ℝ Ω) (α : MultiIndex n) :
    P102.U4.restrictDistribution h (distributionDerivative α T) =
      distributionDerivative α (P102.U4.restrictDistribution h T) := by
  ext φ
  change (-1 : ℝ) ^ α.card * T (P102.U4.testPartialWord Ω (α.sort (· ≤ ·))
    (P102.U4.zeroExtension ℝ h φ)) =
      (-1 : ℝ) ^ α.card * T (P102.U4.zeroExtension ℝ h
        (P102.U4.testPartialWord V (α.sort (· ≤ ·)) φ))
  congr 2
  ext x
  have hφ : (P102.U4.zeroExtension ℝ h φ : Space n → ℝ) = φ :=
    funext (P102.U4.zeroExtensionProperties n ℝ V Ω h φ).1
  rw [P102.U4.testPartialWord_coe, hφ,
    (P102.U4.zeroExtensionProperties n ℝ V Ω h
      (P102.U4.testPartialWord V (α.sort (· ≤ ·)) φ)).1,
    P102.U4.testPartialWord_coe]

/-- The shared sign and Laplacian survive restriction unchanged. -/
theorem restrict_laplacian {n : ℕ} {V Ω : Domain n} (h : V ≤ Ω)
    (T : Distribution ℝ Ω) :
    P102.U4.restrictDistribution h (distributionLaplacian T) =
      distributionLaplacian (P102.U4.restrictDistribution h T) := by
  change P102.U4.distributionRestriction h (∑ i : Fin n, distributionDerivative {i,i} T) = _
  rw [map_sum]
  exact Finset.sum_congr rfl (fun i _ => restrict_derivative h T {i,i})

/-- Restrict the Poisson equation for locally integrable representatives. -/
theorem poisson_restrict {n : ℕ} {V Ω : Domain n} (h : V ≤ Ω)
    {u f : Space n → ℝ} (hu : LocallyIntegrableOn u Ω volume)
    (hf : LocallyIntegrableOn f Ω volume)
    (he : -distributionLaplacian (regularDistribution Ω u) = regularDistribution Ω f) :
    -distributionLaplacian (regularDistribution V u) = regularDistribution V f := by
  have hh := congrArg (P102.U4.distributionRestriction h) he
  change P102.U4.restrictDistribution h (-distributionLaplacian (regularDistribution Ω u)) =
    P102.U4.restrictDistribution h (regularDistribution Ω f) at hh
  rw [show P102.U4.restrictDistribution h (-distributionLaplacian (regularDistribution Ω u)) =
    -P102.U4.restrictDistribution h (distributionLaplacian (regularDistribution Ω u)) from
      map_neg (P102.U4.distributionRestriction h) _, restrict_laplacian,
    P201.Weyl.regular_restriction h u hu, P201.Weyl.regular_restriction h f hf] at hh
  exact hh

private theorem regular_sub {n : ℕ} (Ω : Domain n) {u v : Space n → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) (hv : LocallyIntegrableOn v Ω volume) :
    regularDistribution Ω (u-v) = regularDistribution Ω u - regularDistribution Ω v := by
  ext φ
  rw [P201.Weyl.regular_apply Ω (u-v) (hu.sub hv),
    sub_apply, P201.Weyl.regular_apply Ω u hu,
    P201.Weyl.regular_apply Ω v hv]
  simp_rw [Pi.sub_apply, sub_mul]
  apply integral_sub
  · simpa [mul_comm] using φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hu
  · simpa [mul_comm] using φ.integrable_bilin (ContinuousLinearMap.mul ℝ ℝ) hv

private theorem laplacian_sub {n : ℕ} {Ω : Domain n} (U V : Distribution ℝ Ω) :
    distributionLaplacian (U-V) = distributionLaplacian U - distributionLaplacian V := by
  ext φ
  simp [distributionLaplacian, P201Specs.distributionLaplacian,
    distributionDerivative, P201Specs.distributionDerivative, P102.U4.distributionPartial,
    Finset.sum_sub_distrib, mul_sub]

/-- Weyl's lemma applied to the difference of two solutions of the same
Poisson equation gives an actual smooth harmonic remainder and a.e. equality. -/
theorem harmonic_remainder {n : ℕ} (hn : 1 ≤ n) (Ω : Domain n)
    (u v f : Space n → ℝ) (hu : LocallyIntegrableOn u Ω volume)
    (hv : LocallyIntegrableOn v Ω volume)
    (huEq : -distributionLaplacian (regularDistribution Ω u) = regularDistribution Ω f)
    (hvEq : -distributionLaplacian (regularDistribution Ω v) = regularDistribution Ω f) :
    ∃ h : Space n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) h Ω ∧
      P201Specs.MeanValues.IsHarmonic Ω h ∧
      regularDistribution Ω h = regularDistribution Ω (u-v) ∧
      h =ᵐ[domainMeasure Ω] (u-v) := by
  have heq : distributionLaplacian (regularDistribution Ω (u-v)) = 0 := by
    rw [regular_sub Ω hu hv, laplacian_sub, sub_eq_zero]
    exact neg_injective (huEq.trans hvEq.symm)
  obtain ⟨h, hs, hh, hreg, _⟩ := P201.Weyl.weyl hn Ω
    (regularDistribution Ω (u-v)) heq
  refine ⟨h, hs, hh, hreg, ?_⟩
  exact (P102.U4.regular_injectivity n ℝ Ω h (u-v)
    (hs.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) (hu.sub hv)).mp hreg

/-- A continuous function on a neighborhood of the compact closure has
finite Lᵖ norm on the interior domain, for every exponent. -/
theorem memLp_on_interior {n : ℕ} {U V : Domain n} (hV : RelativelyCompactIn V U)
    {u : Space n → ℝ} (hu : ContinuousOn u U) (p : ℝ≥0∞) :
    MemLp u p (domainMeasure V) := by
  letI : IsFiniteMeasure (domainMeasure V) := isFiniteMeasure_restrict.mpr
    ((hV.1.isBounded.subset subset_closure).measure_lt_top.ne)
  obtain ⟨B, hB⟩ := hV.1.exists_bound_of_continuousOn (hu.mono hV.2)
  apply MemLp.of_bound ((hu.mono (subset_closure.trans hV.2)).aestronglyMeasurable
    V.isOpen.measurableSet) B
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
  exact hB x (subset_closure hx)

/-- Every derivative of a smooth local representative is retained in the
canonical Sobolev tuple. No ambient smoothness outside U is required. -/
theorem smooth_sobolev_on_interior {n : ℕ} {U V : Domain n}
    (hV : RelativelyCompactIn V U) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ w : W ℝ V 2 p, RepresentsOn u w ∧
      ‖w‖ = ∑ α : P102.U4.SobolevIndex n 2,
        (eLpNorm (multiPartial u α.val) p (domainMeasure V)).toReal := by
  have hcont (α : P102.U4.SobolevIndex n 2) : ContinuousOn (multiPartial u α.val) U := by
    exact (P102.U4.partialWord_contDiffOn U (N := α.val.card)
      (hu.of_le (by simp))
      (α.val.sort (· ≤ ·)) 0 (by simp)).continuousOn
  apply exists_sobolev_of_weak_derivatives V p u (memLp_on_interior hV hu.continuousOn p)
    (fun α => multiPartial u α.val) (fun α => memLp_on_interior hV (hcont α) p)
  intro α
  exact P102.U4.derivative_classicalCompatibility n ℝ V α.val u
    ((hu.of_le (by simp)).mono (subset_closure.trans hV.2))

/-- A finite measure turns a pointwise bound into a bound on the real Lᵖ
norm, with the exact constant-function norm. -/
theorem lpNorm_le_constant {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] {u : X → ℝ} {p : ℝ≥0∞} (hu : AEStronglyMeasurable u μ)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ x ∂μ, ‖u x‖ ≤ B) :
    (eLpNorm u p μ).toReal ≤ B * (eLpNorm (fun _ : X => (1 : ℝ)) p μ).toReal := by
  have hconst : MemLp (fun _ : X => B) p μ := memLp_const B
  have he : (fun _ : X => B) = B • (fun _ : X => (1 : ℝ)) := by ext x; simp
  calc
    _ ≤ (eLpNorm (fun _ : X => B) p μ).toReal :=
      ENNReal.toReal_mono hconst.eLpNorm_ne_top (eLpNorm_mono_ae_real hu hb)
    _ = _ := by rw [he, eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm,
      Real.norm_eq_abs, abs_of_nonneg hB]

/-- Uniform interior W²ᵖ control of a smooth harmonic remainder by its L¹
norm on the larger open set. The constant precedes the harmonic function. -/
theorem harmonic_sobolev_estimate {n : ℕ} (hn : 1 ≤ n) (U V : Domain n)
    (hV : RelativelyCompactIn V U) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Space n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) h U → P201Specs.MeanValues.IsHarmonic U h →
      IntegrableOn h U volume → ∃ w : W ℝ V 2 p, RepresentsOn h w ∧
        ‖w‖ ≤ C * ∫ x in U, ‖h x‖ := by
  classical
  obtain ⟨r, hr, hball⟩ := hV.1.exists_cthickening_subset_open U.isOpen hV.2
  choose A hA hest using fun α : P102.U4.SobolevIndex n 2 =>
    P201.DerivativesLiouville.interior_derivative_estimate hn α.val
  let c (α : P102.U4.SobolevIndex n 2) := A α / r ^ (n + α.val.card)
  have hc (α : P102.U4.SobolevIndex n 2) : 0 ≤ c α :=
    div_nonneg (hA α).le (pow_pos hr _).le
  let m := (eLpNorm (fun _ : Space n => (1 : ℝ)) p (domainMeasure V)).toReal
  refine ⟨(∑ α, c α) * m, mul_nonneg (Finset.sum_nonneg (fun α _ => hc α))
    ENNReal.toReal_nonneg, ?_⟩
  intro h hs hh hi
  obtain ⟨w, hw, hnorm⟩ := smooth_sobolev_on_interior hV hs p
  refine ⟨w, hw, ?_⟩
  have hI : 0 ≤ ∫ x in U, ‖h x‖ := integral_nonneg (fun _ => norm_nonneg _)
  letI : IsFiniteMeasure (domainMeasure V) := isFiniteMeasure_restrict.mpr
    ((hV.1.isBounded.subset subset_closure).measure_lt_top.ne)
  have hb (α : P102.U4.SobolevIndex n 2) (x : Space n) (hx : x ∈ V) :
      ‖multiPartial h α.val x‖ ≤ c α * ∫ y in U, ‖h y‖ := by
    have hsub : Metric.closedBall x r ⊆ (U : Set (Space n)) :=
      (Metric.closedBall_subset_cthickening (subset_closure hx) r).trans hball
    apply (hest α U h hh x r hr hsub).trans
    exact mul_le_mul_of_nonneg_left
      (integral_mono_measure (Measure.restrict_mono (Metric.ball_subset_closedBall.trans hsub) le_rfl)
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hi.norm) (hc α)
  rw [hnorm]
  calc
    _ ≤ ∑ α : P102.U4.SobolevIndex n 2, (c α * ∫ x in U, ‖h x‖) * m := by
      apply Finset.sum_le_sum
      intro α _
      have hcont : ContinuousOn (multiPartial h α.val) U :=
        (P102.U4.partialWord_contDiffOn U (N := α.val.card) (hs.of_le (by simp))
          (α.val.sort (· ≤ ·)) 0 (by simp)).continuousOn
      apply lpNorm_le_constant (μ := domainMeasure V) (p := p)
        ((memLp_on_interior hV hcont p).aestronglyMeasurable)
        (mul_nonneg (hc α) hI)
      filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
      exact hb α x hx
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

/-- Hölder's inequality on a finite-measure domain, without changing
representatives or assuming pointwise regularity. -/
theorem integral_norm_le_lp {n : ℕ} (U : Domain n) [IsFiniteMeasure (domainMeasure U)]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] {h : Space n → ℝ} (hh : MemLp h p (domainMeasure U)) :
    ∫ x in U, ‖h x‖ ≤
      (eLpNorm (fun _ : Space n => (1 : ℝ)) (ENNReal.conjExponent p) (domainMeasure U)).toReal *
        (eLpNorm h p (domainMeasure U)).toReal := by
  letI : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨by simp only [ENNReal.conjExponent]; exact le_self_add⟩
  have hb := P102.U4.DifferenceQuotient.integral_mul_bound hh.norm
    (memLp_const (1 : ℝ) : MemLp (fun _ : Space n => (1 : ℝ))
      (ENNReal.conjExponent p) (domainMeasure U))
  have hnonneg : 0 ≤ ∫ x : Space n, ‖h x‖ ∂domainMeasure U :=
    integral_nonneg (fun x : Space n => norm_nonneg (h x))
  have he : eLpNorm (fun x => ‖h x‖) p (domainMeasure U) = eLpNorm h p (domainMeasure U) :=
    eLpNorm_norm h hh.aestronglyMeasurable
  simpa only [mul_one, he, Real.norm_of_nonneg hnonneg] using hb

/-- The quantitative harmonic contribution in the source's finite Lᵖ norms.
All constants depend only on the fixed domains, dimension, and exponent. -/
theorem harmonic_sobolev_lp_estimate {n : ℕ} (hn : 1 ≤ n) (U V : Domain n)
    (hU : Bornology.IsBounded (U : Set (Space n))) (hV : RelativelyCompactIn V U)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Space n → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞) h U → P201Specs.MeanValues.IsHarmonic U h →
      MemLp h p (domainMeasure U) → ∃ w : W ℝ V 2 p, RepresentsOn h w ∧
        ‖w‖ ≤ C * (eLpNorm h p (domainMeasure U)).toReal := by
  letI : IsFiniteMeasure (domainMeasure U) := isFiniteMeasure_restrict.mpr hU.measure_lt_top.ne
  obtain ⟨C, hC, hest⟩ := harmonic_sobolev_estimate hn U V hV p
  let B := (eLpNorm (fun _ : Space n => (1 : ℝ))
    (ENNReal.conjExponent p) (domainMeasure U)).toReal
  refine ⟨C * B, mul_nonneg hC ENNReal.toReal_nonneg, ?_⟩
  intro h hs hh hp
  obtain ⟨w, hw, hb⟩ := hest h hs hh (hp.integrable Fact.out)
  refine ⟨w, hw, hb.trans ?_⟩
  calc
    _ ≤ C * (B * (eLpNorm h p (domainMeasure U)).toReal) :=
      mul_le_mul_of_nonneg_left (integral_norm_le_lp U p hp) hC
    _ = _ := (mul_assoc _ _ _).symm

/-- Zero extension of the source on an interior open set. This is a
function cutoff; no derivative of the original datum is taken. -/
def localizedSource {n : ℕ} (U : Domain n) (f : Space n → ℝ) : Space n → ℝ :=
  (U : Set (Space n)).indicator f

theorem localizedSource_memLp {n : ℕ} (U : Domain n) (p : ℝ≥0∞)
    (f : Space n → ℝ) (hf : MemLp f p (domainMeasure U)) :
    MemLp (localizedSource U f) p volume :=
  (memLp_indicator_iff_restrict U.isOpen.measurableSet.nullMeasurableSet).mpr hf

theorem localizedSource_norm {n : ℕ} (U : Domain n) (p : ℝ≥0∞)
    (f : Space n → ℝ) :
    eLpNorm (localizedSource U f) p volume = eLpNorm f p (domainMeasure U) :=
  eLpNorm_indicator_eq_eLpNorm_restrict U.isOpen.measurableSet.nullMeasurableSet

theorem localizedSource_support {n : ℕ} (U : Domain n) (f : Space n → ℝ)
    (hU : IsCompact (closure (U : Set (Space n)))) :
    ∀ᵐ x ∂volume, x ∉ (⟨closure (U : Set (Space n)), hU⟩ : Compacts (Space n)) →
      localizedSource U f x = 0 := by
  apply Filter.Eventually.of_forall
  intro x hx
  exact indicator_of_notMem (fun h => hx (subset_closure h)) f

/-- A compact-source Newton potential and a smooth harmonic remainder
represent the original distributional solution on any interior open set.
This uses only the exact potential-equation premise, with no initial
Sobolev regularity or continuity of the input solution. -/
theorem local_potential_decomposition
    (potentialEquation : P201Specs.Elliptic.NewtonLp.PotentialEquationStatement)
    {n : ℕ} (hn : 1 ≤ n) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (Ω U : Domain n) (hU : RelativelyCompactIn U Ω) (u f : Space n → ℝ)
    (hu : LocallyMemLp Ω p u) (hf : LocallyMemLp Ω p f)
    (he : -distributionLaplacian (regularDistribution Ω u) = regularDistribution Ω f) :
    let v := P201Specs.Elliptic.NewtonHessian.holderPotential (localizedSource U f)
    LocallyIntegrable v volume ∧
    -distributionLaplacian (regularDistribution (⊤ : Domain n) v) =
      regularDistribution (⊤ : Domain n) (localizedSource U f) ∧
    ∃ h : Space n → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) h U ∧
      P201Specs.MeanValues.IsHarmonic U h ∧
      regularDistribution U h = regularDistribution U (u-v) ∧
      u =ᵐ[domainMeasure U] (fun x => v x + h x) := by
  let F := localizedSource U f
  have hFp : MemLp F p volume := localizedSource_memLp U p f (hf U hU)
  have hFc : P102.U4.HasCompactEssentialSupport F :=
    ⟨⟨closure (U : Set (Space n)), hU.1⟩, localizedSource_support U f hU.1⟩
  obtain ⟨_, hvloc, hvEq⟩ := potentialEquation n hn p hp F hFp hFc
  refine ⟨hvloc, hvEq, ?_⟩
  have hUΩ : U ≤ Ω := fun x hx => hU.2 (subset_closure hx)
  have huloc := hu.locallyIntegrableOn hp
  have hfloc := hf.locallyIntegrableOn hp
  have hFtop : LocallyIntegrableOn F (⊤ : Domain n) volume :=
    (hFp.locallyIntegrable hp).locallyIntegrableOn _
  have hvtop : LocallyIntegrableOn
      (P201Specs.Elliptic.NewtonHessian.holderPotential F) (⊤ : Domain n) volume :=
    hvloc.locallyIntegrableOn _
  have hregF : regularDistribution U F = regularDistribution U f := by
    apply (P102.U4.regular_injectivity n ℝ U F f
      (hFtop.mono_set (show U ≤ (⊤ : Domain n) from le_top))
      (hfloc.mono_set hUΩ)).mpr
    filter_upwards [ae_restrict_mem U.isOpen.measurableSet] with x hx
    exact indicator_of_mem hx f
  have hvUEq := poisson_restrict (show U ≤ (⊤ : Domain n) from le_top)
    hvtop hFtop hvEq
  rw [hregF] at hvUEq
  obtain ⟨h, hs, hh, hr, hae⟩ := harmonic_remainder hn U u
    (P201Specs.Elliptic.NewtonHessian.holderPotential F) f (huloc.mono_set hUΩ)
    (hvtop.mono_set (show U ≤ (⊤ : Domain n) from le_top))
    (poisson_restrict hUΩ huloc hfloc he) hvUEq
  refine ⟨h, hs, hh, hr, ?_⟩
  filter_upwards [hae] with x hx
  change h x = u x - _ at hx
  linarith

/-- Both the source and observation compact sets are fixed before the
constant. The lower-order functions remain ordinary convolution integrals. -/
theorem localized_potential_lowerOrder
    (lowerOrderEstimate : P201Specs.Elliptic.NewtonLp.LowerOrderEstimateStatement)
    {n : ℕ} (hn : 1 ≤ n) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (U : Domain n) (hU : IsCompact (closure (U : Set (Space n))))
    (B : Compacts (Space n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Space n → ℝ, MemLp f p (domainMeasure U) →
      MemLp (P201Specs.Elliptic.NewtonHessian.holderPotential (localizedSource U f))
        p (volume.restrict B) ∧
      (∀ i : Fin n, MemLp (P102.U4.functionConvolution
        (P201Specs.Elliptic.NewtonHessian.gradientKernel i) (localizedSource U f))
          p (volume.restrict B)) ∧
      (eLpNorm (P201Specs.Elliptic.NewtonHessian.holderPotential (localizedSource U f))
        p (volume.restrict B)).toReal +
        (∑ i : Fin n, (eLpNorm (P102.U4.functionConvolution
          (P201Specs.Elliptic.NewtonHessian.gradientKernel i) (localizedSource U f))
            p (volume.restrict B)).toReal) ≤
        C * (eLpNorm f p (domainMeasure U)).toReal := by
  obtain ⟨C, hC, hb⟩ := lowerOrderEstimate n hn p hp
    ⟨closure (U : Set (Space n)), hU⟩ B
  refine ⟨C, hC, ?_⟩
  intro f hf
  have hh := hb (localizedSource U f) (localizedSource_memLp U p f hf)
    (localizedSource_support U f hU)
  rw [localizedSource_norm] at hh
  exact hh

/-- A fixed nonnegative test of mass one, for the compact-solution
mollification argument. -/
def smoothingKernel (n : ℕ) : Test ℝ (⊤ : Domain n) :=
  let b : ContDiffBump (0 : Space n) := ⟨1, 2, by norm_num, by norm_num⟩
  ⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed, subset_univ _⟩

theorem smoothingKernel_mass (n : ℕ) : (∫ x, smoothingKernel n x) = 1 :=
  ContDiffBump.integral_normed _

theorem smoothingKernel_norm_mass (n : ℕ) : (∫ x, ‖smoothingKernel n x‖) = 1 := by
  have hn (x : Space n) : 0 ≤ smoothingKernel n x := ContDiffBump.nonneg_normed _ _
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (hn _)]
  exact smoothingKernel_mass n

/-- The Poisson equation commutes with whole-space smoothing, pointwise. -/
theorem smoothed_poisson_equation {n : ℕ} (w G : Space n → ℝ)
    (he : -distributionLaplacian (regularDistribution (⊤ : Domain n) w) =
      regularDistribution (⊤ : Domain n) G) (ρ : Test ℝ (⊤ : Domain n)) :
    -laplacian (P102.U4.localConvolution (regularDistribution (⊤ : Domain n) w) ρ) =
      P102.U4.localConvolution (regularDistribution (⊤ : Domain n) G) ρ := by
  funext x
  have hx : x ∈ P102.U4.convolutionDomain (⊤ : Domain n) ρ :=
    P102.U4.Mollification.mem_convolutionDomain_top ρ x
  change -(∑ i : Fin n, multiPartial
    (P102.U4.localConvolution (regularDistribution (⊤ : Domain n) w) ρ) {i,i} x) = _
  simp_rw [P201.Weyl.convolution_distribution_derivative (⊤ : Domain n) _ ρ _ x hx]
  simp_rw [P102.U4.localConvolution_pairing n ℝ (⊤ : Domain n) _ ρ x hx]
  have hh := congrArg (fun T : Distribution ℝ (⊤ : Domain n) =>
    T (P102.U4.convolutionTest ρ x hx)) he
  simpa only [distributionLaplacian, P201Specs.distributionLaplacian,
    neg_apply, sum_apply] using hh

/-- Whole-space estimates and Lᵖ duality recover the Hessian of a compactly
supported distributional solution. The solution initially has only Lᵖ
regularity; the mollified Hessians are never assumed to converge in Lᵖ. -/
theorem compact_poisson_hessian (n : ℕ) (hn : 1 ≤ n) (p : ℝ) (hp : 1 < p) :
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      simpa using ENNReal.ofReal_le_ofReal hp.le⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w G : Space n → ℝ,
      MemLp w (ENNReal.ofReal p) volume → P102.U4.HasCompactEssentialSupport w →
      MemLp G (ENNReal.ofReal p) volume →
      -distributionLaplacian (regularDistribution (⊤ : Domain n) w) =
        regularDistribution (⊤ : Domain n) G →
      ∀ i j : Fin n, ∃ g : Lp ℝ (⊤ : Domain n) (ENNReal.ofReal p),
        distributionDerivative {i,j} (regularDistribution (⊤ : Domain n) w) =
          regularDistribution (⊤ : Domain n) g ∧
        ‖g‖ ≤ C * (eLpNorm G (ENNReal.ofReal p) volume).toReal := by
  let P := ENNReal.ofReal p
  letI : Fact (1 ≤ P) := ⟨by simpa [P] using ENNReal.ofReal_le_ofReal hp.le⟩
  let q := ENNReal.conjExponent P
  letI : Fact (1 ≤ q) := ⟨by simp only [q, ENNReal.conjExponent]; exact le_self_add⟩
  have hqtop : q ≠ ⊤ := by
    dsimp [q, ENNReal.conjExponent]
    apply ENNReal.add_ne_top.mpr
    refine ⟨by simp, ENNReal.inv_ne_top.mpr ?_⟩
    exact ne_of_gt (tsub_pos_iff_lt.mpr (by
      simpa [P] using (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < p)).mpr hp))
  obtain ⟨C, hC, hest⟩ := P201.Elliptic.WholeSpaceW2p.realEstimate n hn p hp
  refine ⟨C, hC, ?_⟩
  intro w G hw hwc hG he i j
  let T := distributionDerivative ({i,j} : MultiIndex n)
    (regularDistribution (⊤ : Domain n) w)
  let M : ℝ≥0 := ⟨C * (eLpNorm G P volume).toReal, mul_nonneg hC ENNReal.toReal_nonneg⟩
  have htest : ∀ φ : Test ℝ (⊤ : Domain n),
      ‖T φ‖ ≤ M * (eLpNorm φ q (domainMeasure (⊤ : Domain n))).toReal := by
    intro φ
    let ρ := smoothingKernel n
    let κε (ε : ℝ) := P102.U4.Mollification.scaledKernel ρ ε
    let S (ε : ℝ) := P102.U4.localConvolution
      (regularDistribution (⊤ : Domain n) w) (κε ε)
    have hlim := P102.U4.Mollification.distributionLimit n ℝ (⊤ : Domain n) T ρ
      (smoothingKernel_mass n) φ
    have hlim' : Filter.Tendsto (fun ε => ∫ x, multiPartial (S ε) {i,j} x * φ x)
        (nhdsWithin 0 (Ioi 0)) (nhds (T φ)) := by
      convert hlim using 1
      funext ε
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      exact congrArg (fun z : ℝ => z * φ x)
        (P201.Weyl.convolution_distribution_derivative (⊤ : Domain n) _ (κε ε)
          _ x (P102.U4.Mollification.mem_convolutionDomain_top (κε ε) x))
    apply le_of_tendsto hlim'.norm
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hs := P102.U4.localConvolution_contDiff (regularDistribution (⊤ : Domain n) w) (κε ε)
    have hsc := P102.U4.localConvolution_hasCompactSupport (hw.locallyIntegrable Fact.out) hwc (κε ε)
    obtain ⟨hH, _, hbound⟩ := hest (S ε) hs hsc
    have hκ : MemLp (κε ε) 1 volume :=
      (κε ε).continuous.memLp_of_hasCompactSupport (κε ε).hasCompactSupport
    have hκnorm : (eLpNorm (κε ε) 1 volume).toReal = 1 := by
      rw [toReal_eLpNorm, lpNorm_one_eq_integral_norm hκ.aestronglyMeasurable]
      exact (P102.U4.Mollification.scalingIntegrals n ℝ ρ ε hε).2.trans
        (smoothingKernel_norm_mass n)
    obtain ⟨_, hconv, hconvbound, _⟩ := P102.U2.Young.euclidean_young n hn ℝ 1 P P
      le_rfl Fact.out Fact.out (by simp) (κε ε) G hκ hG
    have hconv' : P102.U2.Young.integralConvolution volume (κε ε) G =
        -laplacian (S ε) := by
      rw [← P102.U4.localConvolution_regular_whole (hG.locallyIntegrable Fact.out)]
      exact (smoothed_poisson_equation w G he (κε ε)).symm
    have hΔ : (eLpNorm (laplacian (S ε)) P volume).toReal ≤
        (eLpNorm G P volume).toReal := by
      calc
        _ = (eLpNorm (P102.U2.Young.integralConvolution volume (κε ε) G) P volume).toReal := by
          rw [hconv', eLpNorm_neg]
        _ ≤ (eLpNorm (κε ε) 1 volume * eLpNorm G P volume).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top hκ.eLpNorm_ne_top hG.eLpNorm_ne_top) hconvbound
        _ = _ := by rw [ENNReal.toReal_mul, hκnorm, one_mul]
    have hentry : (eLpNorm (P201Specs.Elliptic.WholeSpaceW2p.HessianEntry (S ε) i j)
        P volume).toReal ≤ C * (eLpNorm G P volume).toReal := by
      apply le_trans _ (hbound.trans (mul_le_mul_of_nonneg_left hΔ hC))
      change _ ≤ ∑ a : Fin n, ∑ b : Fin n,
        (eLpNorm (P201Specs.Elliptic.WholeSpaceW2p.HessianEntry (S ε) a b) P volume).toReal
      calc
        _ ≤ ∑ b : Fin n, (eLpNorm
            (P201Specs.Elliptic.WholeSpaceW2p.HessianEntry (S ε) i b) P volume).toReal :=
          Finset.single_le_sum (fun b _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
        _ ≤ _ := Finset.single_le_sum
          (f := fun a : Fin n => ∑ b : Fin n,
            (eLpNorm (P201Specs.Elliptic.WholeSpaceW2p.HessianEntry (S ε) a b) P volume).toReal)
          (fun a _ => Finset.sum_nonneg (fun b _ => ENNReal.toReal_nonneg)) (Finset.mem_univ i)
    have hφ : MemLp φ q volume := φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
    have hi := P102.U4.DifferenceQuotient.integral_mul_bound (hH i j) hφ
    change ‖∫ x, multiPartial (S ε) {i,j} x * φ x‖ ≤ _ at hi
    change ‖∫ x, multiPartial (S ε) {i,j} x * φ x‖ ≤ _
    have hb := hi.trans (mul_le_mul_of_nonneg_left hentry ENNReal.toReal_nonneg)
    change ‖∫ x, multiPartial (S ε) {i,j} x * φ x‖ ≤
      (C * (eLpNorm G P volume).toReal) * (eLpNorm φ q (volume.restrict Set.univ)).toReal
    simpa only [Measure.restrict_univ, mul_comm] using hb
  obtain ⟨g, hg, hreg⟩ := P102.U4.DifferenceQuotient.exists_density_of_test_bound
    (⊤ : Domain n) P q hqtop T M htest
  refine ⟨g, hreg, ?_⟩
  rw [Lp.norm_def]
  exact (ENNReal.toReal_mono ENNReal.coe_ne_top hg).trans_eq (by
    rw [ENNReal.coe_toReal]; rfl)

/-- The zeroth component is one of the terms of the full Sobolev norm. -/
theorem underlying_norm_le {n : ℕ} {V : Domain n} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (w : W ℝ V 2 p) :
    ‖P102.U4.sobolevUnderlying w‖ ≤ ‖w‖ := by
  rw [P102.U4.sobolev_norm V 2 p]
  exact Finset.single_le_sum (fun α _ => norm_nonneg
    (P102.U4.sobolevDerivative w α)) (Finset.mem_univ (P102.U4.zeroSobolevIndex n 2))

/-- A quantitative interior estimate starting from the original Lᵖ data.
The indicator source has compact essential support; the solution itself
is never differentiated before its Sobolev representative is constructed. -/
theorem interiorEstimate : P201Specs.Elliptic.LocalW2p.InteriorEstimateStatement := by
  intro n hn p hp
  let q := ENNReal.ofReal p
  have hq : 1 ≤ q := by simpa [q] using ENNReal.ofReal_le_ofReal hp.le
  letI : Fact (1 ≤ q) := ⟨hq⟩
  let P : P102.U2.CZLpData.Exponent :=
    ⟨q, by simpa [q] using (ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : ℝ) < p)).mpr hp,
      ENNReal.ofReal_lt_top⟩
  intro Ω V U hVU hUΩ
  have hUb : Bornology.IsBounded (U : Set (Space n)) :=
    hUΩ.1.isBounded.subset subset_closure
  have hVb : Bornology.IsBounded (V : Set (Space n)) :=
    hVU.1.isBounded.subset subset_closure
  let K : Compacts (Space n) := ⟨closure (U : Set (Space n)), hUΩ.1⟩
  obtain ⟨A, hA, hpotU⟩ := P201.Elliptic.NewtonLp.potentialEstimate n hn P K U hUb
  obtain ⟨B, hB, hpotV⟩ := P201.Elliptic.NewtonLp.potentialEstimate n hn P K V hVb
  obtain ⟨H, hH, hharm⟩ := harmonic_sobolev_lp_estimate hn U V hUb hVU q
  refine ⟨B + H * (1 + A), by positivity, ?_⟩
  intro u f hu hf he
  let F := localizedSource U f
  let v := P201Specs.Elliptic.NewtonHessian.holderPotential F
  have hFp : MemLp F q volume := localizedSource_memLp U q f (hf U hUΩ)
  have hFK : ∀ᵐ x ∂volume, x ∉ K → F x = 0 := localizedSource_support U f hUΩ.1
  obtain ⟨_, _, _, a, ha, hanorm⟩ := hpotU F hFp hFK
  obtain ⟨_, _, _, b, hb, hbnorm⟩ := hpotV F hFp hFK
  have hvp : MemLp v q (domainMeasure U) := MemLp.ae_eq ha (Lp.memLp (P102.U4.sobolevUnderlying a))
  have hvnorm : (eLpNorm v q (domainMeasure U)).toReal ≤
      A * (eLpNorm f q (domainMeasure U)).toReal := by
    calc
      _ = ‖P102.U4.sobolevUnderlying a‖ := by
        rw [Lp.norm_def, eLpNorm_congr_ae ha]
      _ ≤ ‖a‖ := underlying_norm_le a
      _ ≤ _ := by simpa [P, F, localizedSource_norm] using hanorm
  have hbnd : ‖b‖ ≤ B * (eLpNorm f q (domainMeasure U)).toReal := by
    simpa [P, F, localizedSource_norm] using hbnorm
  obtain ⟨_, _, h, hs, hh, _, huvh⟩ := local_potential_decomposition
    P201.Elliptic.NewtonLp.potentialEquation hn q hq Ω U hUΩ u f hu hf he
  have hup := hu U hUΩ
  have hhp : MemLp h q (domainMeasure U) := by
    have hae : u - v =ᵐ[domainMeasure U] h := by
      filter_upwards [huvh] with x hx
      change u x = v x + h x at hx
      change u x - v x = h x
      linarith
    exact MemLp.ae_eq hae (hup.sub hvp)
  have hhnorm : (eLpNorm h q (domainMeasure U)).toReal ≤
      (eLpNorm u q (domainMeasure U)).toReal +
        A * (eLpNorm f q (domainMeasure U)).toReal := by
    have hae : h =ᵐ[domainMeasure U] u - v := by
      filter_upwards [huvh] with x hx
      change u x = v x + h x at hx
      change h x = u x - v x
      linarith
    rw [eLpNorm_congr_ae hae]
    have htri := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hup.eLpNorm_ne_top, hvp.eLpNorm_ne_top⟩)
      (eLpNorm_sub_le (f := u) (g := v) hq)
    rw [ENNReal.toReal_add hup.eLpNorm_ne_top hvp.eLpNorm_ne_top] at htri
    exact htri.trans (add_le_add le_rfl hvnorm)
  obtain ⟨c, hc, hcnorm⟩ := hharm h hs hh hhp
  have hVleU : V ≤ U := fun x hx => hVU.2 (subset_closure hx)
  have huvhV : u =ᵐ[domainMeasure V] (fun x => v x + h x) :=
    ae_mono (Measure.restrict_mono hVleU le_rfl) huvh
  have hsum : (P102.U4.sobolevUnderlying (b+c) : Space n → ℝ) =ᵐ[domainMeasure V] u := by
    have headd : P102.U4.sobolevUnderlying (b+c) =
        P102.U4.sobolevUnderlying b + P102.U4.sobolevUnderlying c :=
      (P102.U4.sobolevUnderlyingCLM V 2 q).map_add b c
    rw [headd]
    exact ((Lp.coeFn_add _ _).trans (hb.add hc.1)).trans huvhV.symm
  refine ⟨b+c, representsOn_of_ae
    ((hu.locallyIntegrableOn hq).mono_set (hVleU.trans
      (show U ≤ Ω from fun x hx => hUΩ.2 (subset_closure hx)))) (b+c) hsum, ?_⟩
  let Nf := (eLpNorm f q (domainMeasure U)).toReal
  let Nu := (eLpNorm u q (domainMeasure U)).toReal
  have hNf : 0 ≤ Nf := ENNReal.toReal_nonneg
  have hNu : 0 ≤ Nu := ENNReal.toReal_nonneg
  calc
    ‖b+c‖ ≤ ‖b‖ + ‖c‖ := norm_add_le _ _
    _ ≤ B * Nf + H * (Nu + A * Nf) :=
      add_le_add hbnd (hcnorm.trans (mul_le_mul_of_nonneg_left hhnorm hH))
    _ ≤ (B + H * (1+A)) * (Nf+Nu) := by
      nlinarith [mul_nonneg hB hNu, mul_nonneg (mul_nonneg hH hA) hNu,
        mul_nonneg hH hNf]

/-- Local membership follows by inserting an intermediate relatively compact
open set between the requested closure and the original domain. -/
theorem localRegularity : P201Specs.Elliptic.LocalW2p.LocalRegularityStatement := by
  intro n hn p hp Ω u f hu hf he V hVΩ
  obtain ⟨U, hUΩ, hVU⟩ := P102.U4.DifferenceQuotient.exists_relativelyCompact_open hVΩ.1 hVΩ.2
  obtain ⟨_, _, hest⟩ := interiorEstimate n hn p hp Ω V U ⟨hVΩ.1, hVU⟩ hUΩ
  obtain ⟨w, hw, _⟩ := hest u f hu hf he
  exact ⟨w, hw⟩

/-- The whole-space clause of the same source theorem. -/
theorem wholeSpaceEstimate : P201Specs.Elliptic.LocalW2p.WholeSpaceEstimateStatement :=
  P201.Elliptic.WholeSpaceW2p.frobeniusEstimate

end P201.Elliptic.LocalW2p
