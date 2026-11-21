import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.CircleMoments
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ExpandedFA.PartIV.CircleMoments

open MeasureTheory Set
open scoped ComplexConjugate

def character (n : ℤ) : C(Circle, ℂ) where
  toFun z := (z : ℂ) ^ n
  continuous_toFun := (continuous_subtype_val : Continuous fun z : Circle => (z : ℂ)).zpow₀ n
    (fun z => Or.inl (Circle.coe_ne_zero z))

@[simp] theorem character_apply (n : ℤ) (z : Circle) :
    character n z = (z : ℂ) ^ n := rfl

theorem character_integrable (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℤ) :
    Integrable (fun z : Circle => (z : ℂ) ^ n) μ :=
  (character n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) 

theorem conj_zpow (z : Circle) (n : ℤ) :
    conj ((z : ℂ) ^ n) = (z : ℂ) ^ (-n) := by
  rw [← Circle.coe_zpow, ← Circle.coe_inv_eq_conj, Circle.coe_inv, Circle.coe_zpow,
    zpow_neg]

theorem moment_neg (μ : Measure Circle) [IsFiniteMeasure μ] (n : ℤ) :
    moment μ (-n) = conj (moment μ n) := by
  simp only [moment, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => (conj_zpow z n).symm

theorem toeplitzForm_moment (μ : Measure Circle) [IsFiniteMeasure μ]
    (s : Finset ℤ) (a : ℤ → ℂ) :
    toeplitzForm (moment μ) s a =
      ∫ z : Circle, conj (∑ j ∈ s, a j * (z : ℂ) ^ j) *
        (∑ k ∈ s, a k * (z : ℂ) ^ k) ∂μ := by
  unfold toeplitzForm moment
  simp_rw [← integral_const_mul]
  have hi (j : ℤ) :
      (∑ k ∈ s, ∫ z : Circle, conj (a j) * a k * (z : ℂ) ^ (k-j) ∂μ) =
      ∫ z : Circle, ∑ k ∈ s, conj (a j) * a k * (z : ℂ) ^ (k-j) ∂μ :=
    (integral_finsetSum s (fun k _ => (character_integrable μ (k-j)).const_mul _)).symm
  simp_rw [hi]
  rw [← integral_finsetSum s (fun j _ => integrable_finsetSum s
    (fun k _ => (character_integrable μ (k-j)).const_mul _))]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [map_sum, map_mul, conj_zpow]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [zpow_sub₀ z.coe_ne_zero]
  rw [zpow_neg]
  ring

theorem necessity : Spec.Necessity := by
  intro c μ h
  have := h.1
  have hc : c = moment μ := funext h.2
  subst c
  refine ⟨moment_neg μ, ?_⟩
  intro s a
  rw [toeplitzForm_moment]
  have heq : (fun z : Circle => conj (∑ j ∈ s, a j * (z : ℂ) ^ j) *
      (∑ k ∈ s, a k * (z : ℂ) ^ k)) =
      (fun z : Circle => (Complex.normSq (∑ j ∈ s, a j * (z : ℂ) ^ j) : ℂ)) := by
    funext z
    simpa only [Complex.normSq_eq_norm_sq, Complex.ofReal_pow] using Complex.conj_mul' _
  rw [heq, integral_complex_ofReal]
  exact ⟨by simp, by simpa using integral_nonneg (fun _ => Complex.normSq_nonneg _)⟩

theorem mass : Spec.Mass := by
  intro c μ h
  have := h.1
  have hzero : c 0 = (μ.real univ : ℂ) := by simpa [moment] using h.2 0
  refine ⟨hzero, ?_⟩
  rw [hzero, Complex.ofReal_re, Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ univ)]

theorem zero_measure : Spec.ZeroMeasure := by
  intro c μ h hc
  apply Measure.measure_univ_eq_zero.mp
  rw [(mass c μ h).2, hc]
  simp

/-- Vanishing mass forces every entry to vanish, already on two indices. -/
theorem zero_sequence : Spec.ZeroSequence := by
  classical
  intro c hsym hpos hzero
  funext n
  by_cases hn : n = 0
  · simpa [hn] using hzero
  have h := (hpos {0, n} (fun j => if j = 0 then 1 else -conj (c n))).2
  have hn' : (0 : ℤ) ≠ n := Ne.symm hn
  simp [toeplitzForm, hn, hn', hzero, hsym n, Complex.mul_re,
    Complex.conj_re, Complex.conj_im] at h
  apply Complex.ext <;> simp only [Pi.zero_apply, Complex.zero_re, Complex.zero_im]
  · nlinarith [sq_nonneg (c n).re, sq_nonneg (c n).im]
  · nlinarith [sq_nonneg (c n).re, sq_nonneg (c n).im]

/-- The Laurent characters form a uniformly dense subspace. -/
theorem span_character_dense :
    Dense (Submodule.span ℂ (range character) : Set C(Circle, ℂ)) := by
  let A : StarSubalgebra ℂ C(Circle, ℂ) :=
    { toSubalgebra := Algebra.adjoin ℂ (range character)
      star_mem' := by
        change Algebra.adjoin ℂ (range character) ≤ star (Algebra.adjoin ℂ (range character))
        apply Algebra.adjoin_le
        rintro _ ⟨n, rfl⟩
        exact Algebra.subset_adjoin ⟨-n, ContinuousMap.ext (fun z => (conj_zpow z n).symm)⟩ }
  have hspan : A.toSubalgebra.toSubmodule = Submodule.span ℂ (range character) := by
    apply Algebra.adjoin_eq_span_of_subset
    refine Subset.trans ?_ Submodule.subset_span
    intro f hf
    refine Submonoid.closure_induction (fun _ => id) ?_ ?_ hf
    · exact ⟨0, ContinuousMap.ext fun z => by simp⟩
    · rintro _ _ _ _ ⟨m, rfl⟩ ⟨n, rfl⟩
      exact ⟨m+n, ContinuousMap.ext fun z => zpow_add₀ z.coe_ne_zero _ _⟩
  have hsep : A.SeparatesPoints := by
    intro x y hxy
    refine ⟨_, ⟨character 1, Algebra.subset_adjoin ⟨1, rfl⟩, rfl⟩, ?_⟩
    simpa using (fun heq => hxy (Circle.ext heq) : (x : ℂ) ≠ (y : ℂ))
  have hA := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hsep
  have htop : (Submodule.span ℂ (range character)).topologicalClosure = ⊤ := by
    rw [← hspan]
    exact congrArg (fun B : StarSubalgebra ℂ C(Circle, ℂ) => B.toSubalgebra.toSubmodule) hA
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr htop

/-- Integration on the actual continuous functions, with the uniform norm. -/
def integralFunctional (μ : Measure Circle) [IsFiniteMeasure μ] : C(Circle, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun f := ∫ z, f z ∂μ
      map_add' f g := integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' a f := integral_smul a f }
    (μ.real univ) (fun f => by
      change ‖∫ z, f z ∂μ‖ ≤ μ.real univ * ‖f‖
      simpa only [BoundedContinuousFunction.norm_mkOfCompact, BoundedContinuousFunction.mkOfCompact_apply] using (BoundedContinuousFunction.mkOfCompact f).norm_integral_le_mul_norm μ)

theorem uniqueness : Spec.Uniqueness := by
  intro c μ ν hμ hν
  have := hμ.1
  have := hν.1
  have hfun : integralFunctional μ = integralFunctional ν := by
    apply ContinuousLinearMap.ext_on span_character_dense
    rintro _ ⟨n, rfl⟩
    exact (hμ.2 n).symm.trans (hν.2 n)
  suffices heq : (⟨μ, hμ.1⟩ : FiniteMeasure Circle) = ⟨ν, hν.1⟩ from
    congrArg FiniteMeasure.toMeasure heq
  apply FiniteMeasure.ext_of_forall_integral_eq
  intro f
  change (∫ z, f z ∂μ) = ∫ z, f z ∂ν
  have heq := congrArg (fun L : C(Circle, ℂ) →L[ℂ] ℂ =>
    L ⟨fun z => (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩) hfun
  change (∫ z, (f z : ℂ) ∂μ) = ∫ z, (f z : ℂ) ∂ν at heq
  simpa only [integral_complex_ofReal, Complex.ofReal_inj] using heq

/-- Normalized arc measure, transported from the additive circle. -/
def circleHaar : Measure Circle :=
  Measure.map (AddCircle.toCircle (T := 1)) (AddCircle.haarAddCircle (T := 1))

instance circleHaar_probability : IsProbabilityMeasure circleHaar := by
  unfold circleHaar
  infer_instance

theorem moment_circleHaar (n : ℤ) : moment circleHaar n = if n = 0 then 1 else 0 := by
  unfold moment circleHaar
  change (∫ z, character n z ∂Measure.map (AddCircle.toCircle (T := 1)) _) = _
  rw [integral_map AddCircle.continuous_toCircle.measurable.aemeasurable
    (character n).continuous.aestronglyMeasurable]
  have h := congrFun (fourierCoeff_fourier (T := 1) n) 0
  simp only [fourierCoeff, neg_zero, fourier_zero, one_smul] at h
  simpa only [fourier_apply, AddCircle.toCircle_zsmul, Circle.coe_zpow,
    Pi.single_apply, eq_comm, character_apply] using h

/-- The Fejér polynomial in double-sum form; this avoids a sign choice for
Fourier coefficients: its nth positive moment will approximate `c n`. -/
def fejerPolynomial (c : ℤ → ℂ) (N : ℕ) : C(Circle, ℂ) :=
  ((N : ℂ) + 1)⁻¹ •
    ∑ j ∈ Finset.Icc (0 : ℤ) N, ∑ k ∈ Finset.Icc (0 : ℤ) N,
      c (k-j) • character (j-k)

theorem fejerPolynomial_eq_form (c : ℤ → ℂ) (N : ℕ) (z : Circle) :
    fejerPolynomial c N z = ((N : ℂ) + 1)⁻¹ *
      toeplitzForm c (Finset.Icc 0 N) (fun j => (z : ℂ) ^ (-j)) := by
  simp only [fejerPolynomial, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    smul_eq_mul, toeplitzForm]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [conj_zpow, neg_neg, character_apply]
  rw [zpow_sub₀ z.coe_ne_zero, zpow_neg]
  ring

theorem fejerPolynomial_nonnegative (c : ℤ → ℂ) (hpos : ToeplitzNonnegative c)
    (N : ℕ) (z : Circle) :
    (fejerPolynomial c N z).im = 0 ∧ 0 ≤ (fejerPolynomial c N z).re := by
  rw [fejerPolynomial_eq_form]
  have h := hpos (Finset.Icc 0 N) (fun j => (z : ℂ) ^ (-j))
  have hcast : ((N : ℂ) + 1)⁻¹ = (((N : ℝ) + 1)⁻¹ : ℝ) := by simp
  rw [hcast]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, h.1, mul_zero]
  exact ⟨trivial, mul_nonneg (by positivity) h.2⟩

def fejerDensity (c : ℤ → ℂ) (N : ℕ) : C(Circle, ℝ) :=
  ⟨fun z => (fejerPolynomial c N z).re, Complex.continuous_re.comp (fejerPolynomial c N).continuous⟩

theorem fejerDensity_cast (c : ℤ → ℂ) (hpos : ToeplitzNonnegative c)
    (N : ℕ) (z : Circle) : (fejerDensity c N z : ℂ) = fejerPolynomial c N z := by
  apply Complex.ext
  · rfl
  · exact (fejerPolynomial_nonnegative c hpos N z).1.symm

def fejerMeasure (c : ℤ → ℂ) (N : ℕ) : Measure Circle :=
  circleHaar.withDensity (fun z => ENNReal.ofReal (fejerDensity c N z))

instance fejerMeasure_finite (c : ℤ → ℂ) (N : ℕ) : IsFiniteMeasure (fejerMeasure c N) :=
  isFiniteMeasure_withDensity_ofReal
    ((fejerDensity c N).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).hasFiniteIntegral

theorem moment_fejerMeasure_integral (c : ℤ → ℂ) (hpos : ToeplitzNonnegative c)
    (N : ℕ) (n : ℤ) :
    moment (fejerMeasure c N) n =
      ∫ z : Circle, fejerPolynomial c N z * (z : ℂ) ^ n ∂circleHaar := by
  unfold moment fejerMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    ((fejerDensity c N).continuous.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with z
  have hz : 0 ≤ fejerDensity c N z := (fejerPolynomial_nonnegative c hpos N z).2
  rw [ENNReal.toReal_ofReal hz]
  simp only [Complex.real_smul, fejerDensity_cast c hpos]

/-- Integrating the double sum leaves only its nth diagonal. -/
theorem moment_fejerMeasure_diagonal (c : ℤ → ℂ) (hpos : ToeplitzNonnegative c)
    (N : ℕ) (n : ℤ) :
    moment (fejerMeasure c N) n = ((N : ℂ) + 1)⁻¹ *
      ∑ j ∈ Finset.Icc (0 : ℤ) N,
        if j+n ∈ Finset.Icc (0 : ℤ) N then c n else 0 := by
  classical
  rw [moment_fejerMeasure_integral c hpos]
  change integralFunctional circleHaar (fejerPolynomial c N * character n) = _
  have heq : fejerPolynomial c N * character n = ((N : ℂ) + 1)⁻¹ •
      ∑ j ∈ Finset.Icc (0 : ℤ) N, ∑ k ∈ Finset.Icc (0 : ℤ) N,
        c (k-j) • character (j-k+n) := by
    ext z
    simp only [fejerPolynomial, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
      ContinuousMap.mul_apply, smul_eq_mul, character_apply]
    rw [mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [zpow_add₀ z.coe_ne_zero]
    ring
  rw [heq, map_smul]
  simp only [map_sum, map_smul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hint (k : ℤ) : integralFunctional circleHaar (character (j-k+n)) =
      if j-k+n = 0 then (1 : ℂ) else 0 := moment_circleHaar _
  simp only [hint]
  have hterm (k : ℤ) : c (k-j) * (if j-k+n = 0 then (1 : ℂ) else 0) =
      if k = j+n then c n else 0 := by
    by_cases hk : k = j+n
    · subst k
      simp
    · have hh : j-k+n ≠ 0 := by omega
      simp [hh, hk]
  simp only [hterm]
  simp

/-- The exact Fejér weight for a fixed nonnegative index. -/
theorem moment_fejerMeasure_nat (c : ℤ → ℂ) (hpos : ToeplitzNonnegative c)
    (N n : ℕ) (hn : n ≤ N) :
    moment (fejerMeasure c N) n = (1 - (n : ℂ) / ((N : ℂ) + 1)) * c n := by
  classical
  rw [moment_fejerMeasure_diagonal c hpos]
  have hfilter : (Finset.Icc (0 : ℤ) N).filter
      (fun j => j + (n : ℤ) ∈ Finset.Icc (0 : ℤ) N) =
      Finset.Icc (0 : ℤ) ((N : ℤ) - n) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (Finset.Icc (0 : ℤ) ((N : ℤ) - n)).card = N+1-n := by
    rw [Int.card_Icc]
    omega
  rw [hcard, Nat.cast_sub (by omega : n ≤ N+1)]
  push_cast
  have hden : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : (N : ℤ) + 1 ≠ 0)
  field_simp

theorem moment_fejerMeasure_zero (c : ℤ → ℂ) (hpos : ToeplitzNonnegative c)
    (N : ℕ) : moment (fejerMeasure c N) 0 = c 0 := by
  simpa using moment_fejerMeasure_nat c hpos N 0 (Nat.zero_le _)

open Filter Topology in
theorem tendsto_moment_fejerMeasure (c : ℤ → ℂ) (hsym : Hermitian c)
    (hpos : ToeplitzNonnegative c) (n : ℤ) :
    Tendsto (fun N : ℕ => moment (fejerMeasure c N) n) atTop (𝓝 (c n)) := by
  have hnat (k : ℕ) : Tendsto (fun N : ℕ => moment (fejerMeasure c N) k)
      atTop (𝓝 (c k)) := by
    have hinv : Tendsto (fun N : ℕ => (1 : ℂ) / ((N : ℂ)+1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hw := ((tendsto_const_nhds (x := (1 : ℂ))).sub
      ((tendsto_const_nhds (x := (k : ℂ))).mul hinv)).mul
      (tendsto_const_nhds (x := c k))
    simp only [mul_zero, sub_zero, one_mul] at hw
    apply hw.congr'
    filter_upwards [eventually_ge_atTop k] with N hN
    rw [moment_fejerMeasure_nat c hpos N k hN]
    simp [div_eq_mul_inv]
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact hnat k
  · have h := Complex.continuous_conj.continuousAt.tendsto.comp (hnat k)
    change Tendsto (fun N : ℕ => conj (moment (fejerMeasure c N) k)) atTop
      (𝓝 (conj (c k))) at h
    rw [hsym k]
    simpa only [moment_neg] using h

open Filter Topology in
theorem continuous_moment (n : ℤ) :
    Continuous (fun μ : FiniteMeasure Circle => moment (μ : Measure Circle) n) := by
  let fr : C(Circle, ℝ) :=
    ⟨fun z => ((z : ℂ) ^ n).re, Complex.continuous_re.comp (character n).continuous⟩
  let fi : C(Circle, ℝ) :=
    ⟨fun z => ((z : ℂ) ^ n).im, Complex.continuous_im.comp (character n).continuous⟩
  have hr := FiniteMeasure.continuous_integral_continuousMap fr
  have hi := FiniteMeasure.continuous_integral_continuousMap fi
  have hc := (Complex.continuous_ofReal.comp hr).add
    ((Complex.continuous_ofReal.comp hi).mul (continuous_const (y := Complex.I)))
  convert hc using 1
  funext μ
  exact (integral_re_add_im (character_integrable (μ : Measure Circle) n)).symm

/-- Compactness of bounded-mass measures produces a representing measure
from the positive Fejér approximants, without assuming positive total mass. -/
theorem sufficiency (c : ℤ → ℂ) (hsym : Hermitian c) (hpos : ToeplitzNonnegative c) :
    ∃ μ : Measure Circle, Represents c μ := by
  classical
  let ν : ℕ → FiniteMeasure Circle := fun N => ⟨fejerMeasure c N, inferInstance⟩
  have hm (N : ℕ) : ((ν N).mass : ℝ) = (c 0).re := by
    have h := congrArg Complex.re (moment_fejerMeasure_zero c hpos N)
    change (fejerMeasure c N).real univ = (c 0).re
    simpa only [moment, zpow_zero, integral_const, Complex.real_smul, mul_one,
      Complex.ofReal_re] using h
  have hmass (N : ℕ) : (ν N).mass ≤ (ν 0).mass := by
    exact_mod_cast (le_of_eq ((hm N).trans (hm 0).symm))
  obtain ⟨μ, _, hcluster⟩ :=
    (isCompact_setOfPred_finiteMeasure_le_of_compactSpace Circle (ν 0).mass).exists_mapClusterPt
      (f := Filter.atTop) (u := ν)
      (Filter.tendsto_principal.2 (Filter.Eventually.of_forall hmass))
  refine ⟨(μ : Measure Circle), inferInstance, ?_⟩
  intro n
  have hcl := hcluster.continuousAt_comp (continuous_moment n).continuousAt
  have ht := tendsto_moment_fejerMeasure c hsym hpos n
  exact (eq_of_nhds_neBot (hcl.clusterPt.mono ht)).symm

theorem circle_moment_theorem : Spec.CircleMomentTheorem := by
  intro c hsym
  constructor
  · intro hpos
    obtain ⟨μ, hμ⟩ := sufficiency c hsym hpos
    exact ⟨μ, hμ, fun ν hν => uniqueness c ν μ hν hμ⟩
  · rintro ⟨μ, hμ, _⟩
    exact (necessity c μ hμ).2

end ExpandedFA.PartIV.CircleMoments
