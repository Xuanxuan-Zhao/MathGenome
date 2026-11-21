import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.WeakDerivativeSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.OneDimensionalSobolev
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Convex.Measure
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal Topology

namespace ExpandedFA.Sobolev.OneDimensional
open ExpandedFA.Distributions

@[simp] theorem linePoint_apply (t : ℝ) (i : Fin 1) : linePoint t i = t := rfl

@[simp] theorem linePoint_coordinate (z : Domain 1) : linePoint (z 0) = z := by
  ext i
  exact congrArg z (Subsingleton.elim (0 : Fin 1) i)

/-- The domain change is measure preserving, including the restriction to an
arbitrary open interval. No normalization constant is lost in dimension one. -/
theorem coordinate_measurePreserving (I : Opens ℝ) :
    MeasurePreserving (fun z : Domain 1 => z 0)
      (volume.restrict (lineDomain I : Set (Domain 1)))
      (volume.restrict (I : Set ℝ)) :=
  (volume_preserving_funUnique (Fin 1) ℝ).restrict_preimage I.isOpen.measurableSet

theorem linePoint_measurePreserving (I : Opens ℝ) :
    MeasurePreserving linePoint (volume.restrict (I : Set ℝ))
      (volume.restrict (lineDomain I : Set (Domain 1))) :=
  MeasurePreserving.symm (MeasurableEquiv.funUnique (Fin 1) ℝ)
    (coordinate_measurePreserving I)

variable {𝕜 : Type} [RCLike 𝕜] {I : Opens ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem lineFunction_memLp (v : DomainLp 𝕜 (lineDomain I) p) :
    MemLp (lineFunction v) p (volume.restrict (I : Set ℝ)) :=
  (Lp.memLp v).comp_measurePreserving (linePoint_measurePreserving I)

theorem lineFunction_eLpNorm (v : DomainLp 𝕜 (lineDomain I) p) :
    eLpNorm (lineFunction v) p (volume.restrict (I : Set ℝ)) =
      eLpNorm v p (volume.restrict (lineDomain I : Set (Domain 1))) :=
  eLpNorm_comp_measurePreserving (Lp.memLp v).aestronglyMeasurable (linePoint_measurePreserving I)

/-- A version of the quotient representative on the real line has exactly the
same p-norm as the original accepted Lp element. -/
theorem lineFunction_norm (v : DomainLp 𝕜 (lineDomain I) p) :
    (eLpNorm (lineFunction v) p (volume.restrict (I : Set ℝ))).toReal = ‖v‖ := by
  rw [lineFunction_eLpNorm, Lp.norm_def]

/-- Extending the density by zero gives an actual global Lp function. This
operation is on representatives, and imposes no boundary condition on u. -/
def extendedLineFunction (v : DomainLp 𝕜 (lineDomain I) p) : ℝ → 𝕜 :=
  (I : Set ℝ).indicator (lineFunction v)

theorem extendedLineFunction_memLp (v : DomainLp 𝕜 (lineDomain I) p) :
    MemLp (extendedLineFunction v) p volume :=
  (memLp_indicator_iff_restrict I.isOpen.measurableSet.nullMeasurableSet).mpr
    (lineFunction_memLp v)

theorem extendedLineFunction_locallyIntegrable (v : DomainLp 𝕜 (lineDomain I) p) :
    LocallyIntegrable (extendedLineFunction v) volume :=
  (extendedLineFunction_memLp v).locallyIntegrable Fact.out

/-- The finite boundary of any open interval has zero volume, also for rays,
the whole line and the empty interval. -/
theorem interval_closure_ae_eq (hI : OrdConnected (I : Set ℝ)) :
    closure (I : Set ℝ) =ᵐ[volume] (I : Set ℝ) := by
  have hn := (hI.convex : Convex ℝ (I : Set ℝ)).addHaar_frontier volume
  have ha : ∀ᵐ t ∂volume, t ∉ frontier (I : Set ℝ) := by
    exact (ae_iff.mpr (by simpa using hn))
  filter_upwards [ha] with t ht
  apply propext
  constructor
  · intro hc
    by_contra hi
    exact ht (by simpa [frontier, I.isOpen.interior_eq] using And.intro hc hi)
  · intro hi
    exact subset_closure hi

/-- Lp densities are integrable on every finite segment of the closed
interval. Endpoint values are irrelevant to integrability. -/
theorem lineFunction_intervalIntegrable_closure (hI : OrdConnected (I : Set ℝ))
    (v : DomainLp 𝕜 (lineDomain I) p) {x y : ℝ}
    (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) :
    IntervalIntegrable (lineFunction v) volume y x := by
  have hc : MemLp (lineFunction v) p (volume.restrict (closure (I : Set ℝ))) := by
    rw [Measure.restrict_congr_set (interval_closure_ae_eq hI)]
    exact lineFunction_memLp v
  have hs : uIoc y x ⊆ closure (I : Set ℝ) :=
    (hI.convex.closure.ordConnected).uIoc_subset hy hx
  let : IsFiniteMeasure (volume.restrict (uIoc y x)) := ⟨by simp⟩
  exact intervalIntegrable_iff.mpr
    ((hc.mono_measure (Measure.restrict_mono_set volume hs)).integrable Fact.out)

theorem extendedLineFunction_ae_on_segment (hI : OrdConnected (I : Set ℝ))
    (v : DomainLp 𝕜 (lineDomain I) p) {x y : ℝ}
    (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) :
    extendedLineFunction v =ᵐ[volume.restrict (uIoc y x)] lineFunction v := by
  have hs : uIoc y x ⊆ closure (I : Set ℝ) :=
    (hI.convex.closure.ordConnected).uIoc_subset hy hx
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae (interval_closure_ae_eq hI)] with t ht he
  exact indicator_of_mem (show t ∈ (I : Set ℝ) from he ▸ hs ht) _

/-- A Banach-valued primitive is absolutely continuous. The real primitive of
the norm controls its total increments, so no scalar restriction or loss in
the complex norm is needed. -/
theorem integral_primitive_absolutelyContinuous {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg : ∀ a b, IntervalIntegrable g volume a b) (a b c : ℝ) :
    AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, g t) a b := by
  have hn := (hg a b).norm.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  change Filter.Tendsto _ _ _ at hn ⊢
  apply squeeze_zero (fun q => Finset.sum_nonneg (fun _ _ => dist_nonneg))
    (fun q => Finset.sum_le_sum (fun i _ => ?_)) hn
  rw [dist_eq_norm,
    intervalIntegral.integral_interval_sub_left (hg c _) (hg c _),
    Real.dist_eq,
    intervalIntegral.integral_interval_sub_left (hg a _).norm (hg a _).norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- The fundamental theorem for a Banach-valued AC function with a specified
locally integrable a.e. derivative. This form retains the full complex norm. -/
theorem integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f g : ℝ → E} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : LocallyIntegrable g volume)
    (hd : ∀ᵐ x ∂volume, x ∈ uIcc a b → HasDerivAt f (g x) x) :
    (∫ t in a..b, g t) = f b - f a := by
  have hi (x y : ℝ) : IntervalIntegrable g volume x y :=
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  have hp := integral_primitive_absolutelyContinuous hi a b a
  have hz : ∀ᵐ x ∂volume, x ∈ uIcc a b →
      HasDerivAt (fun x => f x - ∫ t in a..x, g t) 0 x := by
    filter_upwards [hd, _root_.LocallyIntegrable.ae_hasDerivAt_integral hg] with x hx hpx hxi
    convert! (hx hxi).sub (hpx a) using 1 <;> simp
  obtain ⟨C, hC⟩ := (hf.sub hp).const_of_ae_hasDerivAt_zero hz
  have he := (hC b right_mem_uIcc).trans (hC a left_mem_uIcc).symm
  simp only [Pi.sub_apply, intervalIntegral.integral_same, sub_zero] at he
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (sub_eq_iff_eq_add.mp he).symm)

theorem integral_test_mul_density {𝕜 : Type*} [RCLike 𝕜] {f g ψ : ℝ → 𝕜}
    (hf : Continuous f) (hfac : ∀ a b, AbsolutelyContinuousOnInterval f a b)
    (hg : LocallyIntegrable g volume)
    (hd : ∀ᵐ t ∂volume, HasDerivAt f (g t) t) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hcψ : HasCompactSupport ψ) :
    (∫ t, ψ t * g t) = -(∫ t, deriv ψ t * f t) := by
  have h₁ : Integrable (fun t => deriv ψ t * f t) volume :=
    ((hψ.continuous_deriv (by simp)).mul hf).integrable_of_hasCompactSupport
      hcψ.deriv.mul_right
  have h₂ : Integrable (fun t => ψ t * g t) volume := by
    simpa only [smul_eq_mul] using
      hg.integrable_smul_left_of_hasCompactSupport hψ.continuous hcψ
  obtain ⟨l, hl⟩ := hcψ.bddBelow
  obtain ⟨r, hr⟩ := hcψ.bddAbove
  let a := min l r - 1
  let b := max l r + 1
  have hab : a < b := by dsimp [a, b]; linarith [show min l r ≤ max l r from min_le_max]
  have hs : tsupport ψ ⊆ Ioo a b := by
    intro t ht
    have hlt := hl ht
    have htr := hr ht
    constructor <;> dsimp [a, b] <;> linarith [min_le_left l r, le_max_right l r]
  have hψa : ψ a = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hs ht).1.false)
  have hψb : ψ b = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hs ht).2.false)
  have hqac : AbsolutelyContinuousOnInterval (fun t => ψ t * f t) a b := by
    have hpac : AbsolutelyContinuousOnInterval ψ a b :=
      (hψ.of_le (by simp) : ContDiff ℝ 1 ψ).contDiffOn.absolutelyContinuousOnInterval
    convert! hpac.smul (hfac a b) using 1
  have hqint : LocallyIntegrable
      (fun t => deriv ψ t * f t + ψ t * g t) volume := (h₁.add h₂).locallyIntegrable
  have hqd : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun t => ψ t * f t) (deriv ψ t * f t + ψ t * g t) t := by
    filter_upwards [hd] with t ht _
    convert! (hψ.differentiable (by simp) t).hasDerivAt.mul ht using 1
  have he := integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt hqac hqint hqd
  have hs₁ : Function.support (fun t => deriv ψ t * f t) ⊆ Ioc a b := by
    intro t ht
    exact Ioo_subset_Ioc_self (hs (support_deriv_subset ((mul_ne_zero_iff.mp ht).1)))
  have hs₂ : Function.support (fun t => ψ t * g t) ⊆ Ioc a b := by
    intro t ht
    exact Ioo_subset_Ioc_self (hs (subset_tsupport ψ ((mul_ne_zero_iff.mp ht).1)))
  rw [intervalIntegral.integral_add h₁.intervalIntegrable h₂.intervalIntegrable,
    intervalIntegral.integral_eq_integral_of_support_subset hs₁,
    intervalIntegral.integral_eq_integral_of_support_subset hs₂, hψa, hψb] at he
  simpa using (eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using he))


theorem integral_test_mul_primitive {𝕜 : Type*} [RCLike 𝕜] {g ψ : ℝ → 𝕜}
    (hg : LocallyIntegrable g volume) (c : ℝ)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hcψ : HasCompactSupport ψ) :
    (∫ t, ψ t * g t) = -(∫ t, deriv ψ t * (∫ s in c..t, g s)) := by
  have hi (a b : ℝ) : IntervalIntegrable g volume a b :=
    (hg.integrableOn_isCompact isCompact_uIcc).intervalIntegrable
  refine integral_test_mul_density (intervalIntegral.continuous_primitive hi c)
    (fun a b => integral_primitive_absolutelyContinuous hi a b c) hg ?_ hψ hcψ
  filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hg] with t ht
  exact ht c




/-- Integration by parts for a real- or complex-valued Lipschitz function
against a smooth compactly supported scalar test on the line. -/
theorem integral_test_mul_deriv_lipschitz {f ψ : ℝ → 𝕜} {K : ℝ≥0}
    (hf : LipschitzWith K f) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hcψ : HasCompactSupport ψ) :
    (∫ t, ψ t * deriv f t) = -(∫ t, deriv ψ t * f t) := by
  have hdf : MemLp (deriv f) ∞ volume :=
    memLp_top_of_bound (aestronglyMeasurable_deriv f volume) K
      (.of_forall fun _ => norm_deriv_le_of_lipschitz hf)
  have hdloc : LocallyIntegrable (deriv f) volume := hdf.locallyIntegrable le_top
  have h₁ : Integrable (fun t => deriv ψ t * f t) volume :=
    ((hψ.continuous_deriv (by simp)).mul hf.continuous).integrable_of_hasCompactSupport
      hcψ.deriv.mul_right
  have h₂ : Integrable (fun t => ψ t * deriv f t) volume := by
    simpa only [smul_eq_mul] using
      hdloc.integrable_smul_left_of_hasCompactSupport hψ.continuous hcψ
  obtain ⟨l, hl⟩ := hcψ.bddBelow
  obtain ⟨r, hr⟩ := hcψ.bddAbove
  let a := min l r - 1
  let b := max l r + 1
  have hab : a < b := by dsimp [a, b]; linarith [show min l r ≤ max l r from min_le_max]
  have hs : tsupport ψ ⊆ Ioo a b := by
    intro t ht
    have hlt := hl ht
    have htr := hr ht
    constructor <;> dsimp [a, b] <;> linarith [min_le_left l r, le_max_right l r]
  have hψa : ψ a = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hs ht).1.false)
  have hψb : ψ b = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hs ht).2.false)
  have hqac : AbsolutelyContinuousOnInterval (fun t => ψ t * f t) a b := by
    have hpac : AbsolutelyContinuousOnInterval ψ a b :=
      (hψ.of_le (by simp) : ContDiff ℝ 1 ψ).contDiffOn.absolutelyContinuousOnInterval
    convert! hpac.smul hf.lipschitzOnWith.absolutelyContinuousOnInterval using 1
  have hqint : LocallyIntegrable
      (fun t => deriv ψ t * f t + ψ t * deriv f t) volume := (h₁.add h₂).locallyIntegrable
  have hqd : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun t => ψ t * f t) (deriv ψ t * f t + ψ t * deriv f t) t := by
    filter_upwards [hf.ae_differentiableAt (μ := volume)] with t ht _
    convert! (hψ.differentiable (by simp) t).hasDerivAt.mul ht.hasDerivAt using 1
  have he := integral_eq_sub_of_absolutelyContinuous_of_ae_hasDerivAt hqac hqint hqd
  have hs₁ : Function.support (fun t => deriv ψ t * f t) ⊆ Ioc a b := by
    intro t ht
    exact Ioo_subset_Ioc_self (hs (support_deriv_subset ((mul_ne_zero_iff.mp ht).1)))
  have hs₂ : Function.support (fun t => ψ t * deriv f t) ⊆ Ioc a b := by
    intro t ht
    exact Ioo_subset_Ioc_self (hs (subset_tsupport ψ ((mul_ne_zero_iff.mp ht).1)))
  rw [intervalIntegral.integral_add h₁.intervalIntegrable h₂.intervalIntegrable,
    intervalIntegral.integral_eq_integral_of_support_subset hs₁,
    intervalIntegral.integral_eq_integral_of_support_subset hs₂, hψa, hψb] at he
  simpa using (eq_neg_iff_add_eq_zero.mpr (by simpa [add_comm] using he))

theorem extendedLineFunction_intervalIntegrable (v : DomainLp 𝕜 (lineDomain I) p)
    (a b : ℝ) : IntervalIntegrable (extendedLineFunction v) volume a b :=
  ((extendedLineFunction_locallyIntegrable v).integrableOn_isCompact
    isCompact_uIcc).intervalIntegrable

/-- An everywhere continuous primitive of the zero extension of a density.
The choice of base point zero does not require zero to belong to I. -/
def canonicalPrimitive (v : DomainLp 𝕜 (lineDomain I) p) (x : ℝ) : 𝕜 :=
  ∫ t in 0..x, extendedLineFunction v t

theorem canonicalPrimitive_continuous (v : DomainLp 𝕜 (lineDomain I) p) :
    Continuous (canonicalPrimitive v) :=
  intervalIntegral.continuous_primitive (extendedLineFunction_intervalIntegrable v) 0

theorem canonicalPrimitive_absolutelyContinuous (v : DomainLp 𝕜 (lineDomain I) p)
    (a b : ℝ) : AbsolutelyContinuousOnInterval (canonicalPrimitive v) a b :=
  integral_primitive_absolutelyContinuous (extendedLineFunction_intervalIntegrable v) a b 0

theorem canonicalPrimitive_sub_eq (hI : OrdConnected (I : Set ℝ))
    (v : DomainLp 𝕜 (lineDomain I) p) {x y : ℝ}
    (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) :
    canonicalPrimitive v x - canonicalPrimitive v y = ∫ t in y..x, lineFunction v t := by
  rw [canonicalPrimitive, canonicalPrimitive,
    intervalIntegral.integral_interval_sub_left (extendedLineFunction_intervalIntegrable v 0 x)
      (extendedLineFunction_intervalIntegrable v 0 y)]
  exact intervalIntegral.integral_congr_ae_restrict
    (extendedLineFunction_ae_on_segment hI v hx hy)

/-- Almost everywhere the canonical primitive has the original density as
its classical derivative in the interior of the interval. -/
theorem canonicalPrimitive_ae_hasDerivAt (v : DomainLp 𝕜 (lineDomain I) p) :
    ∀ᵐ t ∂volume.restrict (I : Set ℝ),
      HasDerivAt (canonicalPrimitive v) (lineFunction v t) t := by
  filter_upwards [ae_restrict_of_ae
    (_root_.LocallyIntegrable.ae_hasDerivAt_integral
      (extendedLineFunction_locallyIntegrable v)),
    ae_restrict_mem I.isOpen.measurableSet] with t ht hti
  convert! ht 0 using 1
  exact (indicator_of_mem hti _).symm

/-- Pulling a test back by the one-dimensional coordinate chart preserves its
smoothness, compact support and its actual coordinate derivative. -/
theorem test_line_deriv (φ : Tests 𝕜 (lineDomain I)) (t : ℝ) :
    deriv (fun s => φ (linePoint s)) t = testPartialCLM [0] φ (linePoint t) := by
  have hp : HasDerivAt linePoint (coordinateVector (0 : Fin 1)) t := by
    let e := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
    convert e.toContinuousLinearMap.hasDerivAt using 1
    · rfl
    · ext i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simp [e, coordinateVector]
  have hφ := (φ.contDiff.differentiable (by simp) (linePoint t)).hasFDerivAt
  have hd := hφ.comp_hasDerivAt t hp
  convert! hd.deriv using 1

theorem integral_test_mul_coordinate_deriv_lipschitz {f : ℝ → 𝕜} {K : ℝ≥0}
    (hf : LipschitzWith K f) (φ : Tests 𝕜 (lineDomain I)) :
    (∫ z : Domain 1, φ z * deriv f (z 0)) =
      -(∫ z : Domain 1, testPartialCLM [0] φ z * f (z 0)) := by
  let e := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => φ (linePoint t)) :=
    φ.contDiff.comp e.contDiff
  have hcψ : HasCompactSupport (fun t => φ (linePoint t)) :=
    φ.hasCompactSupport.comp_homeomorph e.toHomeomorph
  have hi := integral_test_mul_deriv_lipschitz hf hψ hcψ
  simp_rw [test_line_deriv] at hi
  have hp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      (volume : Measure ℝ) (volume : Measure (Domain 1)) :=
    MeasurePreserving.symm (MeasurableEquiv.funUnique (Fin 1) ℝ)
      (volume_preserving_funUnique (Fin 1) ℝ)
  rw [← hp.integral_comp' (fun z : Domain 1 => φ z * deriv f (z 0)),
    ← hp.integral_comp' (fun z : Domain 1 => testPartialCLM [0] φ z * f (z 0))]
  exact hi

theorem integral_test_mul_canonicalPrimitive (v : DomainLp 𝕜 (lineDomain I) p)
    (φ : Tests 𝕜 (lineDomain I)) :
    (∫ z : Domain 1, φ z * extendedLineFunction v (z 0)) =
      -(∫ z : Domain 1, testPartialCLM [0] φ z * canonicalPrimitive v (z 0)) := by
  let e := (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm
  have hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun t => φ (linePoint t)) :=
    φ.contDiff.comp e.contDiff
  have hcψ : HasCompactSupport (fun t => φ (linePoint t)) :=
    φ.hasCompactSupport.comp_homeomorph e.toHomeomorph
  have hi := integral_test_mul_primitive (extendedLineFunction_locallyIntegrable v) 0 hψ hcψ
  change (∫ t, φ (linePoint t) * extendedLineFunction v t) =
    -(∫ t, deriv (fun s => φ (linePoint s)) t * canonicalPrimitive v t) at hi
  simp_rw [test_line_deriv] at hi
  have hp : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      (volume : Measure ℝ) (volume : Measure (Domain 1)) :=
    MeasurePreserving.symm (MeasurableEquiv.funUnique (Fin 1) ℝ)
      (volume_preserving_funUnique (Fin 1) ℝ)
  rw [← hp.integral_comp' (fun z : Domain 1 => φ z * extendedLineFunction v (z 0)),
    ← hp.integral_comp' (fun z : Domain 1 => testPartialCLM [0] φ z * canonicalPrimitive v (z 0))]
  exact hi

theorem integral_test_mul_lineFunction_canonicalPrimitive
    (v : DomainLp 𝕜 (lineDomain I) p) (φ : Tests 𝕜 (lineDomain I)) :
    (∫ z : Domain 1, φ z * lineFunction v (z 0)) =
      -(∫ z : Domain 1, testPartialCLM [0] φ z * canonicalPrimitive v (z 0)) := by
  rw [← integral_test_mul_canonicalPrimitive v φ]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : z ∈ lineDomain I
    · dsimp only [extendedLineFunction]
      rw [indicator_of_mem (show z 0 ∈ (I : Set ℝ) from hz)]
    · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport
        (fun ht => hz (φ.tsupport_subset ht))
      simp [hφ]

theorem derivativeIndex_one_cases (α : DerivativeIndex 1 1) :
    α = zeroIndex 1 1 ∨ α = firstIndex := by
  have h' : (α.val 0).val = 0 ∨ (α.val 0).val = 1 := by omega
  have h : α.val 0 = 0 ∨ α.val 0 = 1 := by
    rcases h' with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases h with h | h
  · left
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact h
  · right
    apply Subtype.ext
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact h

@[simp] theorem multiIndexWord_firstIndex : multiIndexWord (natIndex firstIndex) = [0] := by
  simp [multiIndexWord, natIndex, firstIndex, List.ofFn_succ]

/-- Assemble the accepted derivative graph from an actual scalar-linear
weak first derivative. No additional certificate is stored in this graph. -/
def ofWeakDerivative (v g : DomainLp 𝕜 (lineDomain I) p)
    (h : lpDistribution g = -(lpDistribution v).comp (testPartialCLM [0])) :
    W1p 𝕜 I p :=
  ⟨WithLp.toLp 1 (fun α => if α = zeroIndex 1 1 then v else g), by
    intro α
    have hz : (firstIndex : DerivativeIndex 1 1) ≠ zeroIndex 1 1 := by
      intro he
      have he' := congrArg (fun β : DerivativeIndex 1 1 => β.val 0) he
      simp [firstIndex, zeroIndex] at he'
    rcases derivativeIndex_one_cases α with rfl | rfl
    · change lpDistribution (if zeroIndex 1 1 = zeroIndex 1 1 then v else g) =
        Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
          𝕜 1 (lineDomain I) (natIndex (zeroIndex 1 1))
          (lpDistribution (if zeroIndex 1 1 = zeroIndex 1 1 then v else g))
      exact (derivative_zero (lpDistribution v)).symm
    · change lpDistribution (if firstIndex = zeroIndex 1 1 then v else g) =
        Specs.ExpandedFA.Distributions.DistributionCalculus.multiIndexDerivativeValue
          𝕜 1 (lineDomain I) (natIndex firstIndex)
          (lpDistribution (if zeroIndex 1 1 = zeroIndex 1 1 then v else g))
      simp only [if_neg hz]
      change lpDistribution g = distributionDerivative 𝕜 1 (lineDomain I)
        (multiIndexWord (natIndex firstIndex)) (lpDistribution v)
      rw [multiIndexWord_firstIndex, distributionDerivative_cons, distributionDerivative_nil]
      exact h⟩

@[simp] theorem ofWeakDerivative_base (v g : DomainLp 𝕜 (lineDomain I) p)
    (h : lpDistribution g = -(lpDistribution v).comp (testPartialCLM [0])) :
    baseLp (ofWeakDerivative v g h) = v := by
  change (if zeroIndex 1 1 = zeroIndex 1 1 then v else g) = v
  simp

@[simp] theorem ofWeakDerivative_derivative (v g : DomainLp 𝕜 (lineDomain I) p)
    (h : lpDistribution g = -(lpDistribution v).comp (testPartialCLM [0])) :
    derivativeLp (ofWeakDerivative v g h) = g := by
  change (if firstIndex = zeroIndex 1 1 then v else g) = g
  have hz : firstIndex ≠ zeroIndex 1 1 := by
    intro he
    have he' := congrArg (fun β : DerivativeIndex 1 1 => β.val 0) he
    simp [firstIndex, zeroIndex] at he'
  simp [hz]

theorem lipschitzOn_deriv_memLp {f : ℝ → 𝕜} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (I : Set ℝ)) :
    MemLp (fun z : Domain 1 => deriv f (z 0)) ∞
      (volume.restrict (lineDomain I : Set (Domain 1))) := by
  have hm : AEStronglyMeasurable (fun z : Domain 1 => deriv f (z 0))
      (volume.restrict (lineDomain I : Set (Domain 1))) := by
    apply (aestronglyMeasurable_deriv f (volume.restrict (I : Set ℝ))).comp_measurePreserving
    exact (volume_preserving_funUnique (Fin 1) ℝ).restrict_preimage I.isOpen.measurableSet
  apply memLp_top_of_bound hm K
  filter_upwards [ae_restrict_mem (lineDomain I).isOpen.measurableSet] with z hz
  exact norm_deriv_le_of_lipschitzOn (I.isOpen.mem_nhds hz) hf

-- A global extension is used only for integration by parts. Its possibly larger
-- global constant does not affect the sharp derivative estimate inside I.
theorem lipschitzOn_exists_global_extension {f : ℝ → 𝕜} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (I : Set ℝ)) :
    ∃ F : ℝ → 𝕜, (∃ L, LipschitzWith L F) ∧ EqOn f F (I : Set ℝ) ∧
      EqOn (deriv f) (deriv F) (I : Set ℝ) := by
  obtain ⟨F, hF, he⟩ := hf.extend_finite_dimension
  exact ⟨F, ⟨_, hF⟩, he, he.deriv I.isOpen⟩


/-- Sharp local integration by parts needs only a Lipschitz representative on I.
The extension is auxiliary; both integrands vanish off the test support. -/
theorem integral_test_mul_deriv_lipschitzOn {f : ℝ → 𝕜} {K : ℝ≥0}
    (hf : LipschitzOnWith K f (I : Set ℝ)) (φ : Tests 𝕜 (lineDomain I)) :
    (∫ z : Domain 1, φ z * deriv f (z 0)
      ∂volume.restrict (lineDomain I : Set (Domain 1))) =
      -(∫ z : Domain 1, testPartialCLM [0] φ z * f (z 0)
        ∂volume.restrict (lineDomain I : Set (Domain 1))) := by
  obtain ⟨F, ⟨L, hF⟩, he, hde⟩ := lipschitzOn_exists_global_extension hf
  have hleft : (∫ z : Domain 1, φ z * deriv f (z 0)
      ∂volume.restrict (lineDomain I : Set (Domain 1))) =
      ∫ z : Domain 1, φ z * deriv F (z 0) := by
    calc
      _ = ∫ z : Domain 1, φ z * deriv F (z 0)
          ∂volume.restrict (lineDomain I : Set (Domain 1)) := by
        apply setIntegral_congr_fun (lineDomain I).isOpen.measurableSet
        intro z hz
        exact congrArg (fun v => φ z * v) (hde hz)
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport (fun ht => hz (φ.tsupport_subset ht)), zero_mul]
  have hright : (∫ z : Domain 1, testPartialCLM [0] φ z * f (z 0)
      ∂volume.restrict (lineDomain I : Set (Domain 1))) =
      ∫ z : Domain 1, testPartialCLM [0] φ z * F (z 0) := by
    calc
      _ = ∫ z : Domain 1, testPartialCLM [0] φ z * F (z 0)
          ∂volume.restrict (lineDomain I : Set (Domain 1)) := by
        apply setIntegral_congr_fun (lineDomain I).isOpen.measurableSet
        intro z hz
        exact congrArg (fun v => testPartialCLM [0] φ z * v) (he hz)
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
        rw [image_eq_zero_of_notMem_tsupport
          (fun ht => hz ((testPartialCLM [0] φ).tsupport_subset ht)), zero_mul]
  rw [hleft, hright]
  exact integral_test_mul_coordinate_deriv_lipschitz hF φ


theorem lipschitzOn_exists_weakDerivative (v : DomainLp 𝕜 (lineDomain I) ∞)
    {f : ℝ → 𝕜} {K : ℝ≥0} (hv : Represents v f)
    (hf : LipschitzOnWith K f (I : Set ℝ)) :
    ∃ g : DomainLp 𝕜 (lineDomain I) ∞, ‖g‖ ≤ (K : ℝ) ∧
      lpDistribution g =
        Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue
          𝕜 1 (lineDomain I) [0] (lpDistribution v) := by
  let hmem := lipschitzOn_deriv_memLp hf
  let g : DomainLp 𝕜 (lineDomain I) ∞ := hmem.toLp _
  have hg : g =ᵐ[volume.restrict (lineDomain I : Set (Domain 1))]
      (fun z : Domain 1 => deriv f (z 0)) := hmem.coeFn_toLp
  have hbd : ∀ᵐ z ∂volume.restrict (lineDomain I : Set (Domain 1)), ‖g z‖ ≤ (K : ℝ) := by
    filter_upwards [hg, ae_restrict_mem (lineDomain I).isOpen.measurableSet] with z hz hzi
    rw [hz]
    exact norm_deriv_le_of_lipschitzOn (I.isOpen.mem_nhds hzi) hf
  refine ⟨g, ?_, ?_⟩
  · rw [Lp.norm_def, eLpNorm_exponent_top (Lp.memLp g).aestronglyMeasurable]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (eLpNormEssSup_le_of_ae_bound hbd)).trans_eq (ENNReal.toReal_ofReal K.coe_nonneg)
  · ext φ
    simp only [lpDistribution_apply,
      Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue,
      List.length_cons, List.length_nil, zero_add, pow_one,
      smul_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, neg_smul, one_smul]
    have hl : (∫ z : Domain 1, φ z * g z
        ∂volume.restrict (lineDomain I : Set (Domain 1))) =
        ∫ z : Domain 1, φ z * deriv f (z 0)
          ∂volume.restrict (lineDomain I : Set (Domain 1)) := by
      apply integral_congr_ae
      filter_upwards [hg] with z hz
      rw [hz]
    have hr : (∫ z : Domain 1, testPartialCLM [0] φ z * v z
        ∂volume.restrict (lineDomain I : Set (Domain 1))) =
        ∫ z : Domain 1, testPartialCLM [0] φ z * f (z 0)
          ∂volume.restrict (lineDomain I : Set (Domain 1)) := by
      apply integral_congr_ae
      filter_upwards [hv] with z hz
      rw [hz]
    rw [hl, hr]
    exact integral_test_mul_deriv_lipschitzOn hf φ


theorem lipschitz_lift (v : DomainLp 𝕜 (lineDomain I) ∞)
    {f : ℝ → 𝕜} {K : ℝ≥0} (hv : Represents v f)
    (hf : LipschitzOnWith K f (I : Set ℝ)) :
    ∃ u : W1p 𝕜 I ∞, baseLp u = v ∧ ‖derivativeLp u‖ ≤ (K : ℝ) := by
  obtain ⟨g, hg, hd⟩ := lipschitzOn_exists_weakDerivative v hv hf
  have hd' : lpDistribution g = -(lpDistribution v).comp (testPartialCLM [0]) := by
    ext φ
    have he := congrArg (fun T : ScalarDistribution 𝕜 (lineDomain I) => T φ) hd
    simpa [Specs.ExpandedFA.Distributions.DistributionCalculus.derivativeValue] using he
  exact ⟨ofWeakDerivative v g hd', ofWeakDerivative_base v g hd', by
    simpa using hg⟩

theorem optimal_lipschitz_constant :
    Specs.ExpandedFA.Sobolev.OneDimensionalSobolev.OptimalLipschitzConstant := by
  intro 𝕜 _ I _hI u f K hv hf
  obtain ⟨w, hw, hbd⟩ := lipschitz_lift (baseLp u) hv hf
  have he : w = u := sobolev_underlying_injective 𝕜 1 (lineDomain I) 1 ∞ hw
  simpa [he] using hbd

theorem weakDerivative_test_identity (u : W1p 𝕜 I p) (φ : Tests 𝕜 (lineDomain I)) :
    (∫ z : Domain 1, φ z * lineFunction (derivativeLp u) (z 0)) =
      -(∫ z : Domain 1, testPartialCLM [0] φ z * lineFunction (baseLp u) (z 0)) := by
  have he := u.property firstIndex
  change lpDistribution (derivativeLp u) =
    distributionDerivative 𝕜 1 (lineDomain I)
      (multiIndexWord (natIndex firstIndex)) (lpDistribution (baseLp u)) at he
  rw [multiIndexWord_firstIndex, distributionDerivative_cons, distributionDerivative_nil] at he
  have ht := congrArg (fun T : ScalarDistribution 𝕜 (lineDomain I) => T φ) he
  simp only [lpDistribution_apply, neg_apply, ContinuousLinearMap.comp_apply] at ht
  have hzero (v : DomainLp 𝕜 (lineDomain I) p) (ψ : Tests 𝕜 (lineDomain I)) :
      (∫ z : Domain 1 in (lineDomain I : Set (Domain 1)), ψ z * v z) =
        ∫ z : Domain 1, ψ z * lineFunction v (z 0) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [ψ.zero_on_compl hz])]
    simp only [lineFunction, linePoint_coordinate]
  rw [hzero, hzero] at ht
  exact ht


def realLineTest (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ (I : Set ℝ)) :
    Tests 𝕜 (lineDomain I) := by
  let e := ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ
  refine ⟨fun z => (ψ (z 0) : 𝕜),
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp (hψ.comp e.contDiff), ?_, ?_⟩
  · exact (hcψ.comp_homeomorph e.toHomeomorph).comp_left (by simp)
  · intro z hz
    have hzc : z ∈ tsupport (fun z : Domain 1 => ψ (z 0)) :=
      tsupport_comp_subset (g := fun r : ℝ => (r : 𝕜)) (by simp) _ hz
    have hzψ : z 0 ∈ tsupport ψ := by
      change z ∈ e.toHomeomorph ⁻¹' tsupport ψ
      rw [← tsupport_comp_eq_preimage]
      exact hzc
    exact hsψ hzψ

@[simp] theorem realLineTest_apply (ψ : ℝ → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ (I : Set ℝ)) (z : Domain 1) :
    realLineTest (𝕜 := 𝕜) ψ hψ hcψ hsψ z = (ψ (z 0) : 𝕜) := rfl

@[simp] theorem testPartial_realLineTest (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (I : Set ℝ)) (t : ℝ) :
    testPartialCLM [0] (realLineTest (𝕜 := 𝕜) ψ hψ hcψ hsψ) (linePoint t) =
      ((deriv ψ t : ℝ) : 𝕜) := by
  rw [← test_line_deriv]
  have hd := ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt t
    (hψ.differentiable (by simp) t).hasDerivAt).deriv
  exact hd


theorem weakPrimitive_real_test_identity (u : W1p 𝕜 I p) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hcψ : HasCompactSupport ψ)
    (hsψ : tsupport ψ ⊆ (I : Set ℝ)) :
    (∫ t, deriv ψ t • (extendedLineFunction (baseLp u) t -
      canonicalPrimitive (derivativeLp u) t)) = 0 := by
  let φ := realLineTest (𝕜 := 𝕜) ψ hψ hcψ hsψ
  have hw := weakDerivative_test_identity u φ
  have hp := integral_test_mul_lineFunction_canonicalPrimitive (derivativeLp u) φ
  have he : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ).symm
      (volume : Measure ℝ) (volume : Measure (Domain 1)) :=
    MeasurePreserving.symm (MeasurableEquiv.funUnique (Fin 1) ℝ)
      (volume_preserving_funUnique (Fin 1) ℝ)
  rw [← he.integral_comp' (fun z : Domain 1 => φ z * lineFunction (derivativeLp u) (z 0)),
    ← he.integral_comp' (fun z : Domain 1 => testPartialCLM [0] φ z * lineFunction (baseLp u) (z 0))] at hw
  rw [← he.integral_comp' (fun z : Domain 1 => φ z * lineFunction (derivativeLp u) (z 0)),
    ← he.integral_comp' (fun z : Domain 1 => testPartialCLM [0] φ z * canonicalPrimitive (derivativeLp u) (z 0))] at hp
  change (∫ t, (ψ t : 𝕜) * lineFunction (derivativeLp u) t) =
    -(∫ t, testPartialCLM [0] (realLineTest (𝕜 := 𝕜) ψ hψ hcψ hsψ) (linePoint t) *
      lineFunction (baseLp u) t) at hw
  change (∫ t, (ψ t : 𝕜) * lineFunction (derivativeLp u) t) =
    -(∫ t, testPartialCLM [0] (realLineTest (𝕜 := 𝕜) ψ hψ hcψ hsψ) (linePoint t) *
      canonicalPrimitive (derivativeLp u) t) at hp
  simp only [testPartial_realLineTest] at hw hp
  have hi : (∫ t, ((deriv ψ t : ℝ) : 𝕜) * lineFunction (baseLp u) t) =
      ∫ t, ((deriv ψ t : ℝ) : 𝕜) * canonicalPrimitive (derivativeLp u) t := by
    exact neg_injective (hw.symm.trans hp)
  have hid : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
  have hcd : HasCompactSupport (deriv ψ) := hcψ.deriv
  have hi₁ : Integrable (fun t => deriv ψ t • extendedLineFunction (baseLp u) t) volume :=
    (extendedLineFunction_locallyIntegrable (baseLp u)).integrable_smul_left_of_hasCompactSupport hid hcd
  have hi₂ : Integrable (fun t => deriv ψ t • canonicalPrimitive (derivativeLp u) t) volume :=
    (canonicalPrimitive_continuous (derivativeLp u)).locallyIntegrable.integrable_smul_left_of_hasCompactSupport hid hcd
  have hie : (fun t => deriv ψ t • extendedLineFunction (baseLp u) t) =
      (fun t => deriv ψ t • lineFunction (baseLp u) t) := by
    funext t
    by_cases ht : t ∈ (I : Set ℝ)
    · rw [extendedLineFunction, indicator_of_mem ht]
    · have hd : deriv ψ t = 0 := by
        by_contra hne
        exact ht (hsψ (support_deriv_subset hne))
      simp [hd]
  simp_rw [smul_sub]
  rw [integral_sub hi₁ hi₂, hie]
  simp only [RCLike.real_smul_eq_coe_mul]
  rw [hi, sub_self]


section SmoothPrimitives
open scoped ContDiff

/-- A smooth density has a smooth indefinite integral. -/
theorem primitive_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (a : ℝ) :
    ContDiff ℝ ∞ (fun x => ∫ t in a..x, g t) := by
  have hd (x : ℝ) : HasDerivAt (fun x => ∫ t in a..x, g t) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable a x)
      (hg.continuous.stronglyMeasurableAtFilter volume (𝓝 x)) hg.continuous.continuousAt
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (hd x).differentiableAt, ?_⟩
  simpa only [funext fun x => (hd x).deriv] using hg

/-- A zero integral smooth test admits a smooth test antiderivative. -/
theorem exists_compact_antiderivative {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ Ioo a b)
    (hz : (∫ t, g t) = 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
      tsupport G ⊆ Icc a b ∧ ∀ x, deriv G x = g x := by
  let G : ℝ → ℝ := fun x => ∫ t in a..x, g t
  have hd (x : ℝ) : HasDerivAt G (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.continuous.intervalIntegrable a x)
      (hg.continuous.stronglyMeasurableAtFilter volume (𝓝 x)) hg.continuous.continuousAt
  have hsupport : Function.support G ⊆ Icc a b := by
    intro x hx
    by_contra hxout
    rcases not_and_or.mp hxout with hxa | hxb
    · have hxa : x < a := lt_of_not_ge hxa
      apply hx
      apply intervalIntegral.integral_zero_ae
      filter_upwards with t ht
      have hta : t ≤ a := (uIoc_subset_uIcc ht).2.trans_eq (max_eq_left hxa.le)
      exact image_eq_zero_of_notMem_tsupport (fun htg => (hs htg).1.not_ge hta)
    · have hxb : b < x := lt_of_not_ge hxb
      apply hx
      change (∫ t in a..x, g t) = 0
      rw [intervalIntegral.integral_eq_integral_of_support_subset ?_, hz]
      intro t ht
      have ht' := hs (subset_tsupport _ ht)
      exact ⟨ht'.1, ht'.2.le.trans hxb.le⟩
  have hts : tsupport G ⊆ Icc a b := closure_minimal hsupport isClosed_Icc
  exact ⟨G, primitive_contDiff hg a,
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupport,
    hts, fun x => (hd x).deriv⟩

/-- Enclose a compact subset of an open interval by an interior closed interval. -/
theorem compact_interval_enclosure {I K : Set ℝ} (hI : IsOpen I)
    (_hIc : OrdConnected I) (hIn : I.Nonempty) (hK : IsCompact K) (hKI : K ⊆ I) :
    ∃ a ∈ I, ∃ b ∈ I, K ⊆ Ioo a b := by
  by_cases hKn : K.Nonempty
  · obtain ⟨l, hl, hmin⟩ := hK.exists_isMinOn hKn continuousOn_id
    obtain ⟨r, hr, hmax⟩ := hK.exists_isMaxOn hKn continuousOn_id
    obtain ⟨a', b', hlab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (hI.mem_nhds (hKI hl))
    obtain ⟨c', d', hrcd, hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (hI.mem_nhds (hKI hr))
    obtain ⟨a, haa', hal⟩ := exists_between hlab.1
    obtain ⟨b, hrb, hbd'⟩ := exists_between hrcd.2
    refine ⟨a, hsub ⟨haa', hal.trans hlab.2⟩,
      b, hsub' ⟨hrcd.1.trans hrb, hbd'⟩, ?_⟩
    intro t ht
    exact ⟨hal.trans_le (hmin ht), (hmax ht).trans_lt hrb⟩
  · obtain ⟨x, hx⟩ := hIn
    exact ⟨x, hx, x, hx, by simpa [Set.not_nonempty_iff_eq_empty.mp hKn]⟩

/-- Every nonempty open set contains an integral-one real smooth test. -/
theorem exists_integral_one_test {I : Set ℝ} (hI : IsOpen I) (hIn : I.Nonempty) :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ I ∧ (∫ t, η t) = 1 := by
  obtain ⟨x, hx⟩ := hIn
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hI.mem_nhds hx)
  let f : ContDiffBump x := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed,
    ?_, f.integral_normed⟩
  rw [f.tsupport_normed_eq]
  exact (Metric.closedBall_subset_ball (by dsimp [f]; linarith)).trans hsub

/-- The one-dimensional fundamental lemma for zero distribution derivative. -/
theorem ae_eq_const_of_integral_deriv_eq_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {I : Set ℝ} (hI : IsOpen I) (hIc : OrdConnected I) {h : ℝ → E}
    (hf : LocallyIntegrable h volume)
    (hzero : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ I → (∫ t, deriv ψ t • h t) = 0) :
    ∃ c : E, h =ᵐ[volume.restrict I] fun _ => c := by
  by_cases hIn : I.Nonempty
  swap
  · refine ⟨0, ?_⟩
    simpa only [Set.not_nonempty_iff_eq_empty.mp hIn, Measure.restrict_empty, ae_zero] using (show h =ᶠ[⊥] (fun _ => (0:E)) from Filter.eventually_bot)
  obtain ⟨η, hηdiff, hηc, hηI, hηone⟩ := exists_integral_one_test hI hIn
  let c : E := ∫ t, η t • h t
  have hηint : Integrable (fun t => η t • h t) :=
    hf.integrable_smul_left_of_hasCompactSupport hηdiff.continuous hηc
  have hpair : ∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ I → (∫ t, φ t • h t) = (∫ t, φ t) • c := by
    intro φ hφdiff hφc hφI
    let A : ℝ := ∫ t, φ t
    let g : ℝ → ℝ := fun t => φ t - A * η t
    have hgdiff : ContDiff ℝ ∞ g := hφdiff.sub (contDiff_const.mul hηdiff)
    have hgc : HasCompactSupport g := hφc.sub (hηc.mul_left (f := fun _ => A))
    have hgI : tsupport g ⊆ I :=
      (tsupport_sub _ _).trans (union_subset hφI
        ((tsupport_mul_subset_right).trans hηI))
    obtain ⟨a, ha, b, hb, hgab⟩ := compact_interval_enclosure hI hIc hIn hgc hgI
    have hgzero : (∫ t, g t) = 0 := by
      rw [integral_sub (hφdiff.continuous.integrable_of_hasCompactSupport hφc)
        ((hηdiff.continuous.integrable_of_hasCompactSupport hηc).const_mul A),
        integral_const_mul, hηone, mul_one, sub_self]
    obtain ⟨G, hGdiff, hGc, hGab, hGderiv⟩ :=
      exists_compact_antiderivative hgdiff hgab hgzero
    have hGzero := hzero G hGdiff hGc (hGab.trans (hIc.out ha hb))
    simp_rw [hGderiv] at hGzero
    have hφint : Integrable (fun t => φ t • h t) :=
      hf.integrable_smul_left_of_hasCompactSupport hφdiff.continuous hφc
    have hgeq : (fun t => g t • h t) =
        (fun t => φ t • h t - A • (η t • h t)) := by
      funext t
      simp [g, sub_smul, mul_smul]
    rw [hgeq, integral_sub hφint (hηint.fun_smul A), integral_smul] at hGzero
    exact sub_eq_zero.mp hGzero
  have hz : ∀ᵐ t ∂volume, t ∈ I → h t - c = 0 := by
    apply hI.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hf.sub (locallyIntegrable_const c)).locallyIntegrableOn I)
    intro φ hφdiff hφc hφI
    have hφint : Integrable (fun t => φ t • h t) :=
      hf.integrable_smul_left_of_hasCompactSupport hφdiff.continuous hφc
    have hφcint : Integrable (fun t => φ t • c) :=
      (hφdiff.continuous.integrable_of_hasCompactSupport hφc).smul_const c
    change (∫ t, φ t • (h t - c)) = 0
    simp_rw [smul_sub]
    rw [integral_sub hφint hφcint, integral_smul_const, hpair φ hφdiff hφc hφI, sub_self]
  refine ⟨c, ?_⟩
  apply (ae_restrict_iff' hI.measurableSet).mpr
  filter_upwards [hz] with t ht hti
  exact sub_eq_zero.mp (ht hti)


end SmoothPrimitives

theorem represents_of_lineFunction_ae (v : DomainLp 𝕜 (lineDomain I) p)
    {f : ℝ → 𝕜} (hf : lineFunction v =ᵐ[volume.restrict (I : Set ℝ)] f) :
    Represents v f := by
  filter_upwards [(coordinate_measurePreserving I).quasiMeasurePreserving.ae hf] with z hz
  simpa only [lineFunction, linePoint_coordinate] using hz

set_option maxHeartbeats 800000 in
theorem primitiveRepresentative_of_ae_eq_const (hI : OrdConnected (I : Set ℝ))
    (u : W1p 𝕜 I p) (c : 𝕜)
    (hc : (fun t => extendedLineFunction (baseLp u) t -
        canonicalPrimitive (derivativeLp u) t) =ᵐ[volume.restrict (I : Set ℝ)]
      (fun _ => c)) :
    PrimitiveRepresentative u (fun t => canonicalPrimitive (derivativeLp u) t + c) := by
  refine ⟨((canonicalPrimitive_continuous _).add continuous_const).continuousOn, ?_, ?_, ?_⟩
  · apply represents_of_lineFunction_ae
    filter_upwards [hc, ae_restrict_mem I.isOpen.measurableSet] with t ht hti
    rw [extendedLineFunction, indicator_of_mem hti] at ht
    exact (sub_eq_iff_eq_add.mp ht).trans (add_comm _ _)
  · intro a ha b hb
    have h₁ := canonicalPrimitive_absolutelyContinuous (derivativeLp u) a b
    have h₂ : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
      (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
    exact h₁.add h₂
  · intro x hx y hy
    refine ⟨lineFunction_intervalIntegrable_closure hI _ hx hy, ?_⟩
    simpa only [add_sub_add_right_eq_sub] using
      canonicalPrimitive_sub_eq hI (derivativeLp u) hx hy
theorem representative_existence :
    Specs.ExpandedFA.Sobolev.OneDimensionalSobolev.RepresentativeExistence := by
  intro 𝕜 _ I hI p _ u
  have hl : LocallyIntegrable (fun t => extendedLineFunction (baseLp u) t -
      canonicalPrimitive (derivativeLp u) t) volume :=
    (extendedLineFunction_locallyIntegrable (baseLp u)).sub
      (canonicalPrimitive_continuous (derivativeLp u)).locallyIntegrable
  obtain ⟨c, hc⟩ := ae_eq_const_of_integral_deriv_eq_zero I.isOpen hI hl
    (fun ψ hψ hcψ hsψ => weakPrimitive_real_test_identity u ψ hψ hcψ hsψ)
  exact ⟨_, primitiveRepresentative_of_ae_eq_const hI u c hc⟩



/-- Equality of continuous representatives already holds on the open domain. -/
theorem represents_unique_on_open (v : DomainLp 𝕜 (lineDomain I) p)
    {f g : ℝ → 𝕜} (hf : ContinuousOn f (I : Set ℝ))
    (hg : ContinuousOn g (I : Set ℝ)) (hvf : Represents v f) (hvg : Represents v g) :
    EqOn f g (I : Set ℝ) := by
  have heq : (fun z : Domain 1 => f (z 0)) =ᵐ[
      volume.restrict (lineDomain I : Set (Domain 1))] (fun z => g (z 0)) :=
    hvf.symm.trans hvg
  have hfg := Measure.eqOn_open_of_ae_eq heq (lineDomain I).isOpen
    (hf.comp (continuous_apply 0).continuousOn (fun _ hx => hx))
    (hg.comp (continuous_apply 0).continuousOn (fun _ hx => hx))
  intro t ht
  exact hfg (by exact ht : linePoint t ∈ lineDomain I)

/-- The continuous finite endpoint values are unique as well. -/
theorem representative_uniqueness :
    Specs.ExpandedFA.Sobolev.OneDimensionalSobolev.RepresentativeUniqueness := by
  intro 𝕜 _ I p _ v f g hf hg hvf hvg
  exact (represents_unique_on_open v (hf.mono subset_closure)
    (hg.mono subset_closure) hvf hvg).of_subset_closure hf hg subset_closure (Subset.refl _)

/-- Pull an equality of quotient representatives back to the real coordinate. -/
theorem represents_lineFunction_ae (v : DomainLp 𝕜 (lineDomain I) p)
    {f : ℝ → 𝕜} (hf : Represents v f) :
    lineFunction v =ᵐ[volume.restrict (I : Set ℝ)] f :=
  (linePoint_measurePreserving I).quasiMeasurePreserving.ae hf

theorem reciprocalExponent_le_one : reciprocalExponent p ≤ 1 := by
  by_cases hp : p = ∞
  · simp [reciprocalExponent, hp]
  · have h : (1 : ℝ) ≤ p.toReal := by
      simpa using ENNReal.toReal_mono hp (show (1 : ℝ≥0∞) ≤ p from Fact.out)
    exact (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h).trans_eq (by norm_num)

/-- Hölder on a subinterval, measured using the original global Lp norm.
This includes p=1 and p=∞. -/
theorem norm_intervalIntegral_le_lp (hI : OrdConnected (I : Set ℝ))
    (v : DomainLp 𝕜 (lineDomain I) p) {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    ‖∫ t in y..x, lineFunction v t‖ ≤
      ‖v‖ * |x - y| ^ (1 - reciprocalExponent p) := by
  let ν : Measure ℝ := volume.restrict (uIoc y x)
  have hsub : ν ≤ volume.restrict (I : Set ℝ) :=
    Measure.restrict_mono_set volume (hI.uIoc_subset hy hx)
  have hm : MemLp (lineFunction v) p ν := (lineFunction_memLp v).mono_measure hsub
  have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1 : ℝ≥0∞) ≤ p from Fact.out) hm.aestronglyMeasurable
  simp only [ENNReal.toReal_one, div_one] at he
  have hep : eLpNorm (lineFunction v) p ν ≤
      eLpNorm v p (volume.restrict (lineDomain I : Set (Domain 1))) :=
    (eLpNorm_mono_measure _ hsub).trans_eq (lineFunction_eLpNorm v)
  have hr : 0 ≤ 1 - reciprocalExponent p := sub_nonneg.mpr reciprocalExponent_le_one
  have hn : ν univ ≠ ∞ := by simp [ν]
  have hprod : eLpNorm v p (volume.restrict (lineDomain I : Set (Domain 1))) *
      ν univ ^ (1 - reciprocalExponent p) ≠ ∞ :=
    ENNReal.mul_ne_top (Lp.eLpNorm_ne_top v) (ENNReal.rpow_ne_top_of_nonneg hr hn)
  have he' : eLpNorm (lineFunction v) 1 ν ≤
      eLpNorm v p (volume.restrict (lineDomain I : Set (Domain 1))) *
        ν univ ^ (1 - reciprocalExponent p) :=
    he.trans (mul_le_mul' hep le_rfl)
  have hνreal : (ν univ).toReal = |x - y| := by
    simp [ν, Real.volume_uIoc]
  calc
    ‖∫ t in y..x, lineFunction v t‖ ≤ ∫ t in uIoc y x, ‖lineFunction v t‖ :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ = (eLpNorm (lineFunction v) 1 ν).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable,
        integral_norm_eq_lintegral_enorm hm.aestronglyMeasurable]
    _ ≤ (eLpNorm v p (volume.restrict (lineDomain I : Set (Domain 1))) *
        ν univ ^ (1 - reciprocalExponent p)).toReal := ENNReal.toReal_mono hprod he'
    _ = ‖v‖ * |x - y| ^ (1 - reciprocalExponent p) := by
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, hνreal, Lp.norm_def]

/-- Once the weak primitive is constructed, all interior increment estimates
follow directly from Hölder, without an additional smoothness assumption. -/
theorem primitive_increment_bound (hI : OrdConnected (I : Set ℝ))
    (u : W1p 𝕜 I p) {f : ℝ → 𝕜} (hf : PrimitiveRepresentative u f)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) :
    ‖f x - f y‖ ≤ ‖derivativeLp u‖ * |x - y| ^ (1 - reciprocalExponent p) := by
  rw [(hf.2.2.2 x (subset_closure hx) y (subset_closure hy)).2]
  exact norm_intervalIntegral_le_lp hI (derivativeLp u) hx hy

/-- Continuity extends the quantitative increment bound to every finite
endpoint. This argument even retains the p=1 oscillation bound. -/
theorem primitive_increment_bound_closure (hI : OrdConnected (I : Set ℝ))
    (u : W1p 𝕜 I p) {f : ℝ → 𝕜} (hf : PrimitiveRepresentative u f)
    {x y : ℝ} (hx : x ∈ closure (I : Set ℝ)) (hy : y ∈ closure (I : Set ℝ)) :
    ‖f x - f y‖ ≤ ‖derivativeLp u‖ * |x - y| ^ (1 - reciprocalExponent p) := by
  have hr : 0 ≤ 1 - reciprocalExponent p := sub_nonneg.mpr reciprocalExponent_le_one
  have hb : ∀ x ∈ I, ∀ y ∈ closure (I : Set ℝ),
      ‖f x - f y‖ ≤ ‖derivativeLp u‖ * |x - y| ^ (1 - reciprocalExponent p) := by
    intro x hx y hy
    apply le_on_closure (fun y hy => primitive_increment_bound hI u hf hx hy)
      (continuousOn_const.sub hf.1).norm ?_ hy
    exact (((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ => Or.inr hr)).const_mul _).continuousOn
  apply le_on_closure (fun x hx => hb x hx y hy)
    (hf.1.sub continuousOn_const).norm ?_ hx
  exact (((continuous_id.sub continuous_const).abs.rpow_const
    (fun _ => Or.inr hr)).const_mul _).continuousOn

theorem holder_estimate : Specs.ExpandedFA.Sobolev.OneDimensionalSobolev.HolderEstimate := by
  intro 𝕜 _ I hI p _ _hp u f hf x hx y hy
  exact primitive_increment_bound_closure hI u hf hx hy

/-- The infinity endpoint gives the exact forward Lipschitz constant on the
closed interval, using the continuity of the same primitive at finite endpoints. -/
theorem lipschitz_bound : Specs.ExpandedFA.Sobolev.OneDimensionalSobolev.LipschitzBound := by
  intro 𝕜 _ I hI u f hf
  apply LipschitzOnWith.closure hf.1
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  simpa [dist_eq_norm, Real.norm_eq_abs, reciprocalExponent] using
    primitive_increment_bound hI u hf hx hy

/-- The finite-measure Lp-to-L1 estimate in real-valued norm form. -/
theorem integral_norm_le_lp {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {g : α → 𝕜} (hg : MemLp g p μ) :
    (∫ t, ‖g t‖ ∂μ) ≤ (eLpNorm g p μ).toReal *
      (μ univ).toReal ^ (1 - reciprocalExponent p) := by
  have hr : 0 ≤ 1 - reciprocalExponent p := sub_nonneg.mpr reciprocalExponent_le_one
  have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (1 : ℝ≥0∞) ≤ p from Fact.out) hg.aestronglyMeasurable
  simp only [ENNReal.toReal_one, div_one] at he
  have hprod : eLpNorm g p μ * μ univ ^ (1 - reciprocalExponent p) ≠ ∞ :=
    ENNReal.mul_ne_top hg.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hr (measure_ne_top μ univ))
  calc
    (∫ t, ‖g t‖ ∂μ) = (eLpNorm g 1 μ).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm hg.aestronglyMeasurable,
        integral_norm_eq_lintegral_enorm hg.aestronglyMeasurable]
    _ ≤ (eLpNorm g p μ * μ univ ^ (1 - reciprocalExponent p)).toReal :=
      ENNReal.toReal_mono hprod he
    _ = _ := by rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]

/-- Averaging the increment bound gives the sharp two coefficients in the
finite-interval inequality. It needs no point realizing an essential infimum. -/
theorem finite_interval_estimate :
    Specs.ExpandedFA.Sobolev.OneDimensionalSobolev.FiniteIntervalEstimate := by
  intro 𝕜 _ a b hab p _ u f hf x hx
  let I : Opens ℝ := ⟨Ioo a b, isOpen_Ioo⟩
  let ν : Measure ℝ := volume.restrict (Ioo a b)
  let L : ℝ := b - a
  let r : ℝ := 1 - reciprocalExponent p
  let C : ℝ := ‖derivativeLp u‖ * L ^ r
  have hL : 0 < L := sub_pos.mpr hab
  have hr : 0 ≤ r := sub_nonneg.mpr reciprocalExponent_le_one
  have hcl : closure (I : Set ℝ) = Icc a b := closure_Ioo hab.ne
  have hν : (ν univ).toReal = L := by
    simp [ν, L, Real.volume_Ioo, sub_nonneg.mpr hab.le]
  let : IsFiniteMeasure ν := inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo a b)))
  have hm : MemLp (lineFunction (baseLp u)) p ν := lineFunction_memLp (baseLp u)
  have hu : Integrable (lineFunction (baseLp u)) ν := hm.integrable (show 1 ≤ p from Fact.out)
  have havg : (∫ t, ‖lineFunction (baseLp u) t‖ ∂ν) ≤ ‖baseLp u‖ * L ^ r := by
    have hi := integral_norm_le_lp hm
    have hn : (eLpNorm (lineFunction (baseLp u)) p ν).toReal = ‖baseLp u‖ :=
      lineFunction_norm (baseLp u)
    rw [hn, hν] at hi
    exact hi
  have hosc : ∀ y ∈ Ioo a b, ‖f x - f y‖ ≤ C := by
    intro y hy
    have hxy : |x - y| ≤ L := by
      apply abs_le.mpr
      constructor <;> dsimp [L] <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have hi := primitive_increment_bound_closure
      (I := I) ordConnected_Ioo u hf (by rw [hcl]; exact hx)
      (subset_closure hy)
    exact hi.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) hxy hr) (norm_nonneg _))
  have hpoint : ∀ᵐ t ∂ν, ‖f x‖ ≤ ‖lineFunction (baseLp u) t‖ + C := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      represents_lineFunction_ae (baseLp u) hf.2.1] with t ht hft
    rw [hft]
    calc
      ‖f x‖ = ‖(f x - f t) + f t‖ := by congr 1; abel
      _ ≤ ‖f x - f t‖ + ‖f t‖ := norm_add_le _ _
      _ ≤ ‖f t‖ + C := by linarith [hosc t ht]
  have hi := integral_mono_ae (integrable_const ‖f x‖)
    (hu.norm.add (integrable_const C)) hpoint
  have hmain : L * ‖f x‖ ≤ ‖baseLp u‖ * L ^ r + L * C := by
    calc
      L * ‖f x‖ = ∫ _t : ℝ, ‖f x‖ ∂ν := by
        simp [integral_const, measureReal_def, hν]
      _ ≤ ∫ t, ‖lineFunction (baseLp u) t‖ + C ∂ν := hi
      _ = (∫ t, ‖lineFunction (baseLp u) t‖ ∂ν) + L * C := by
        rw [integral_add hu.norm (integrable_const C), integral_const]
        simp [measureReal_def, hν]
      _ ≤ _ := by gcongr
  have hpow : L * L ^ (-reciprocalExponent p) = L ^ r := by
    calc
      L * L ^ (-reciprocalExponent p) = L ^ (1 : ℝ) * L ^ (-reciprocalExponent p) := by
        rw [Real.rpow_one]
      _ = L ^ (1 + -reciprocalExponent p) := (Real.rpow_add hL _ _).symm
      _ = L ^ r := by congr 1
  apply (mul_le_mul_iff_right₀ hL).mp
  calc
    L * ‖f x‖ ≤ ‖baseLp u‖ * L ^ r + L * C := hmain
    _ = L * ((b - a) ^ (-reciprocalExponent p) * ‖baseLp u‖ +
        (b - a) ^ (1 - reciprocalExponent p) * ‖derivativeLp u‖) := by
      change _ = L * (L ^ (-reciprocalExponent p) * ‖baseLp u‖ + L ^ r * ‖derivativeLp u‖)
      rw [mul_add, ← mul_assoc L (L ^ (-reciprocalExponent p)), hpow]
      dsimp only [C]
      ring

/-- In particular the original p-class has finite essential supremum, with
the source bound. ENNReal retains finiteness instead of mapping infinity to zero. -/
theorem finite_interval_essential_supremum :
    Specs.ExpandedFA.Sobolev.OneDimensionalSobolev.FiniteIntervalEssentialSupremum := by
  intro 𝕜 _ a b hab p _ u f hf
  rw [eLpNorm_exponent_top (Lp.memLp (baseLp u)).aestronglyMeasurable]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [ae_restrict_mem (lineDomain ⟨Ioo a b, isOpen_Ioo⟩).isOpen.measurableSet,
    hf.2.1] with z hz hzf
  rw [hzf]
  exact finite_interval_estimate 𝕜 a b hab p u f hf (z 0) ⟨hz.1.le, hz.2.le⟩

theorem lipschitz_characterization :
    Specs.ExpandedFA.Sobolev.OneDimensionalSobolev.LipschitzCharacterization := by
  intro 𝕜 _ I hI v
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨f, hf⟩ := representative_existence 𝕜 I hI ∞ u
    exact ⟨f, ‖derivativeLp u‖₊, hf.2.1,
      (lipschitz_bound 𝕜 I hI u f hf).mono subset_closure⟩
  · rintro ⟨f, K, hv, hf⟩
    obtain ⟨u, hu, _⟩ := lipschitz_lift v hv hf
    exact ⟨u, hu⟩

end ExpandedFA.Sobolev.OneDimensional
