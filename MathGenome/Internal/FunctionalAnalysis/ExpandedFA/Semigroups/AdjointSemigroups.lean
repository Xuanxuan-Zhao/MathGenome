import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.AdjointSemigroups
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.LaplaceResolvent
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.Integral
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.BanachAdjoint
import Mathlib.Analysis.Normed.Module.HahnBanach

noncomputable section
open Filter Topology Set
open scoped NNReal

namespace ExpandedFA.Semigroups.AdjointSemigroups
open AdjointSemigroupsSpec

section General
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

omit [CompleteSpace X] in
@[simp] theorem transpose_apply (U : X →L[𝕜] X) (q : X →L[𝕜] 𝕜) (x : X) :
    transpose U q x = q (U x) := rfl

@[simp] theorem adjointOperators_apply (T : C0Semigroup 𝕜 X)
    (t : ℝ≥0) (q : X →L[𝕜] 𝕜) (x : X) :
    adjointOperators T t q x = q (T.operators t x) := rfl

omit [CompleteSpace X] in
theorem norm_transpose_le (U : X →L[𝕜] X) : ‖transpose U‖ ≤ ‖U‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro q
  change ‖q.comp U‖ ≤ ‖U‖ * ‖q‖
  simpa only [mul_comm] using q.opNorm_comp_le U

theorem adjoint_semigroup_laws : SemigroupLaws (𝕜 := 𝕜) (X := X) := by
  intro T
  constructor
  · ext q x
    simp
  · intro t s
    ext q x
    change q (T.operators (t + s) x) = q (T.operators s (T.operators t x))
    rw [add_comm t s, T.add_apply]

theorem adjoint_weakStar_continuity : WeakStarContinuity (𝕜 := 𝕜) (X := X) := by
  intro T
  constructor
  · intro t
    apply WeakDual.continuous_of_continuous_eval
    intro x
    exact WeakDual.eval_continuous (T.operators t x)
  · intro q
    apply WeakDual.continuous_of_continuous_eval
    intro x
    exact q.continuous.comp (T.continuous_orbit x)

local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X

/-- A uniform bound on T bounds its orbit primitives, including time zero. -/
theorem integratedOperator_norm_le (T : C0Semigroup 𝕜 X) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ s : ℝ≥0, s ≤ 1 → ‖T.operators s‖ ≤ C)
    (t : ℝ≥0) (ht : t ≤ 1) : ‖T.integratedOperator t‖ ≤ C * (t : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC t.coe_nonneg)
  intro x
  rw [C0Semigroup.integratedOperator_apply]
  calc
    _ ≤ (C * ‖x‖) * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
        rw [uIoc_of_le t.coe_nonneg] at hs
        have hst : s.toNNReal ≤ t := by
          simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2
        exact ((T.operators s.toNNReal).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hbound _ (hst.trans ht)) (norm_nonneg _)))
    _ = C * (t : ℝ) * ‖x‖ := by rw [sub_zero, abs_of_nonneg t.coe_nonneg]; ring

/-- The defining adjoint pairing applied to an orbit primitive. -/
theorem adjoint_integrated_identity (T : C0Semigroup 𝕜 X)
    (q : (Unbounded.banachAdjoint (generator T)).domain) (t : ℝ≥0) :
    adjointOperators T t q - (q : X →L[𝕜] 𝕜) =
      transpose (T.integratedOperator t) (Unbounded.banachAdjoint (generator T) q) := by
  ext x
  have hi := T.integratedOperator_hasGeneratorLimit t x
  have hg : generator T ⟨T.integratedOperator t x, T.integratedOperator_mem_domain t x⟩ =
      T.operators t x - x :=
    generator_limit_unique T _ _ _ (generator_has_limit T _) hi
  have ha := Unbounded.banachAdjoint_apply (generator T) T.generator_domain_dense q
    ⟨T.integratedOperator t x, T.integratedOperator_mem_domain t x⟩
  change (q : X →L[𝕜] 𝕜) (T.operators t x) - (q : X →L[𝕜] 𝕜) x = _
  rw [transpose_apply, ha, hg, map_sub]

/-- The adjoint orbit is norm continuous on the entire adjoint domain, without
assuming reflexivity or any norm continuity of T itself. -/
theorem adjoint_domain_strong_zero (T : C0Semigroup 𝕜 X)
    (q : (Unbounded.banachAdjoint (generator T)).domain) :
    Tendsto (fun h : ℝ => adjointOperators T h.toNNReal q) (𝓝[>] 0) (𝓝 (q : X →L[𝕜] 𝕜)) := by
  obtain ⟨C, hC, hbound⟩ := T.bounded_on_interval 1
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm' (a := fun h : ℝ =>
    C * h * ‖Unbounded.banachAdjoint (generator T) q‖)
  · filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with h hh hh1
    rw [adjoint_integrated_identity]
    apply (transpose (T.integratedOperator h.toNNReal)).le_opNorm _ |>.trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (norm_transpose_le _).trans
    simpa only [Real.coe_toNNReal _ hh.le] using
      integratedOperator_norm_le T (by linarith) hbound h.toNNReal
        (by simpa using (Real.toNNReal_le_toNNReal hh1.le))
  · have hc : Continuous (fun h : ℝ => C * h * ‖Unbounded.banachAdjoint (generator T) q‖) :=
      (continuous_const.mul continuous_id).mul continuous_const
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- Reflexivity turns weak-star density of the adjoint domain into norm density.
The proof uses a genuine resolvent to avoid assuming density as a certificate. -/
theorem adjoint_domain_dense (href : Reflexive (𝕜 := 𝕜) (X := X))
    (T : C0Semigroup 𝕜 X) :
    Dense ((Unbounded.banachAdjoint (generator T)).domain : Set (X →L[𝕜] 𝕜)) := by
  intro q
  by_contra hq
  obtain ⟨f, hf, hfq⟩ := Unbounded.exists_dual_vanishing_of_not_mem_closure
    (Unbounded.banachAdjoint (generator T)).domain q hq
  obtain ⟨x, hx⟩ := href f
  have hx_eval : ∀ r : X →L[𝕜] 𝕜, f r = r x := by
    intro r
    exact (congrArg (fun g : (X →L[𝕜] 𝕜) →L[𝕜] 𝕜 => g r) hx).symm
  obtain ⟨M, ω, hT⟩ := SemigroupGrowthAndGenerator.exponential_growth T
  let ζ : 𝕜 := algebraMap ℝ 𝕜 (ω + 1)
  have hζ : ω < RCLike.re ζ := by simp [ζ]
  obtain ⟨R, _⟩ := LaplaceResolvent.laplace_inverse T M ω ζ hT hζ
  have hxR : R.inverse x = 0 := by
    apply (SeparatingDual.eq_zero_iff_forall_dual_eq_zero (R := 𝕜) _).mpr
    intro r
    let u := r.comp R.inverse
    have hu : u ∈ (Unbounded.banachAdjoint (generator T)).domain := by
      apply (Unbounded.mem_banachAdjoint_domain_iff _ _).mpr
      refine ⟨ζ • u - r, fun z => ?_⟩
      have hz := congrArg r (R.left_inverse z)
      simp only [map_sub, map_smul] at hz
      change ζ • u (z : X) - r (z : X) = u (generator T z)
      change ζ • u (z : X) - u (generator T z) = r (z : X) at hz
      exact sub_eq_iff_eq_add.mpr (by
        rw [sub_eq_iff_eq_add] at hz
        simpa only [add_comm] using hz)
    change u x = 0
    rw [← hx_eval u]
    exact hf u hu
  have hx0 : x = 0 := by
    have hr := R.right_inverse x
    have hd : (⟨R.inverse x, R.mem_domain x⟩ : (generator T).domain) = 0 :=
      Subtype.ext hxR
    change ζ • R.inverse x - generator T ⟨R.inverse x, R.mem_domain x⟩ = x at hr
    rw [hd, (generator T).map_zero, hxR, smul_zero, sub_zero] at hr
    exact hr.symm
  apply hfq
  rw [hx_eval, hx0, map_zero]

/-- A locally bounded equicontinuous family extends the dense-domain limit. -/
theorem adjoint_reflexive_strong_zero : ReflexiveStrongContinuity (𝕜 := 𝕜) (X := X) := by
  intro href T q
  obtain ⟨C, hC, hbound⟩ := T.bounded_on_interval 1
  let F : ℝ → (X →L[𝕜] 𝕜) →L[𝕜] (X →L[𝕜] 𝕜) :=
    fun h => adjointOperators T (min h.toNNReal 1)
  have hnorm : ∀ h : ℝ, ‖F h‖ ≤ C := fun h =>
    (norm_transpose_le _).trans (hbound _ (min_le_right _ _))
  have heqct : Equicontinuous (fun h => (F h : (X →L[𝕜] 𝕜) → (X →L[𝕜] 𝕜))) := by
    exact (LipschitzWith.uniformEquicontinuous _ ⟨C, by linarith⟩
      (fun h => (F h).lipschitzWith_of_opNorm_le (hnorm h))).equicontinuous
  have heq (r : X →L[𝕜] 𝕜) : (fun h => F h r) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun h => adjointOperators T h.toNNReal r) := by
    filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with h hh
    change adjointOperators T (min h.toNNReal 1) r = _
    rw [min_eq_left (by simpa using Real.toNNReal_le_toNNReal hh.le)]
  have hclosed := heqct.isClosed_setOfPred_tendsto
    (l := 𝓝[>] (0 : ℝ)) (f := fun r : X →L[𝕜] 𝕜 => r) continuous_id
  have hin : ((Unbounded.banachAdjoint (generator T)).domain : Set (X →L[𝕜] 𝕜)) ⊆
      {r | Tendsto (fun h => F h r) (𝓝[>] (0 : ℝ)) (𝓝 r)} := by
    intro r hr
    exact (tendsto_congr' (heq r)).mpr (adjoint_domain_strong_zero T ⟨r, hr⟩)
  have hlim := (hclosed.closure_subset_iff.mpr hin) (adjoint_domain_dense href T q)
  exact (tendsto_congr' (heq q)).mp hlim

/-- The adjoints on a reflexive Banach space, now with the proved C₀ axiom. -/
def reflexiveAdjoint (href : Reflexive (𝕜 := 𝕜) (X := X))
    (T : C0Semigroup 𝕜 X) : C0Semigroup 𝕜 (X →L[𝕜] 𝕜) where
  operators := adjointOperators T
  at_zero := (adjoint_semigroup_laws T).1
  add_time := (adjoint_semigroup_laws T).2
  strong_zero := adjoint_reflexive_strong_zero href T

/-- Dual orbit primitives are the transposes of the primal primitives. -/
theorem adjoint_integratedOperator (T : C0Semigroup 𝕜 X)
    (S : C0Semigroup 𝕜 (X →L[𝕜] 𝕜)) (hS : S.operators = adjointOperators T)
    (t : ℝ≥0) : S.integratedOperator t = transpose (T.integratedOperator t) := by
  ext q x
  rw [C0Semigroup.integratedOperator_apply, transpose_apply,
    C0Semigroup.integratedOperator_apply]
  calc
    _ = ∫ s in (0 : ℝ)..(t : ℝ), S.operators s.toNNReal q x :=
      ((ContinuousLinearMap.apply 𝕜 𝕜 x).intervalIntegral_comp_comm
        ((S.continuous_real_orbit q).intervalIntegrable _ _)).symm
    _ = ∫ s in (0 : ℝ)..(t : ℝ), q (T.operators s.toNNReal x) := by
      simp only [hS, adjointOperators_apply]
    _ = _ := q.intervalIntegral_comp_comm ((T.continuous_real_orbit x).intervalIntegrable _ _)

/-- Pairing the norm difference quotients identifies the generator graph.
The reverse implication uses the integrated identity on its full domain. -/
theorem adjoint_generator (T : C0Semigroup 𝕜 X)
    (S : C0Semigroup 𝕜 (X →L[𝕜] 𝕜)) (hS : S.operators = adjointOperators T) :
    generator S = Unbounded.banachAdjoint (generator T) := by
  apply LinearPMap.eq_of_eq_graph
  rw [Unbounded.banachAdjoint_graph (generator T) T.generator_domain_dense]
  ext ⟨q, y⟩
  change (q, y) ∈ (C0SemigroupSpec.generatorValue S).graph ↔ _
  rw [mem_generator_graph_iff]
  change HasGeneratorLimit S q y ↔ ∀ x : (generator T).domain, y (x : X) = q (generator T x)
  constructor
  · intro h x
    have hq : Tendsto (fun h : ℝ => differenceQuotient S h q (x : X))
        (𝓝[>] 0) (𝓝 (y (x : X))) :=
      (ContinuousLinearMap.apply 𝕜 𝕜 (x : X)).continuous.continuousAt.tendsto.comp h
    have hx : Tendsto (fun h : ℝ => q (differenceQuotient T h (x : X)))
        (𝓝[>] 0) (𝓝 (q (generator T x))) :=
      q.continuous.continuousAt.tendsto.comp (generator_has_limit T x)
    apply tendsto_nhds_unique hq
    convert hx using 1
    ext h
    simp only [differenceQuotient, C0SemigroupSpec.differenceQuotientValue,
      smul_apply, sub_apply,
      ContinuousLinearMap.id_apply, map_smul, map_sub, hS, adjointOperators_apply]
  · intro hy
    have hq : q ∈ (Unbounded.banachAdjoint (generator T)).domain :=
      (Unbounded.mem_banachAdjoint_domain_iff _ _).mpr ⟨y, hy⟩
    have hval : y = Unbounded.banachAdjoint (generator T) ⟨q, hq⟩ :=
      Unbounded.banachAdjoint_unique_extension _ T.generator_domain_dense ⟨q, hq⟩ y hy
    rw [S.hasGeneratorLimit_iff_integrated]
    intro t
    rw [hS, adjoint_integratedOperator T S hS, hval]
    exact adjoint_integrated_identity T ⟨q, hq⟩ t

theorem reflexive_adjoint_generator : ReflexiveGenerator (𝕜 := 𝕜) (X := X) := by
  intro href T
  refine ⟨reflexiveAdjoint href T, rfl, ?_⟩
  exact adjoint_generator T (reflexiveAdjoint href T) rfl

end General

section Translations
variable {𝕜 : Type*} [RCLike 𝕜]
open MeasureTheory
open scoped ENNReal

@[simp] theorem lpTranslate_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℝ)
    (f : Lp 𝕜 p (volume : Measure ℝ)) :
    lpTranslate p h f = Lp.compMeasurePreserving (fun x : ℝ => x - h)
      (measurePreserving_sub_right volume h) f := rfl

@[simp] theorem lpTranslate_zero (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    lpTranslate (𝕜 := 𝕜) p 0 = ContinuousLinearMap.id 𝕜 (Lp 𝕜 p (volume : Measure ℝ)) := by
  ext f : 1
  have heq : (fun x : ℝ => x - (0 : ℝ)) = id := by ext x; simp
  simp only [lpTranslate_apply, heq, ContinuousLinearMap.id_apply,
    Lp.compMeasurePreserving_id_apply]

theorem lpTranslate_add (p : ℝ≥0∞) [Fact (1 ≤ p)] (h k : ℝ) :
    lpTranslate (𝕜 := 𝕜) p (h + k) = (lpTranslate p h).comp (lpTranslate p k) := by
  ext f : 1
  have hh := Lp.compMeasurePreserving_comp_apply f
    (measurePreserving_sub_right volume k) (measurePreserving_sub_right volume h)
  have heq : (fun x : ℝ => x - k) ∘ (fun x : ℝ => x - h) =
      (fun x : ℝ => x - (h + k)) := by ext x; dsimp; ring
  simpa only [heq, lpTranslate_apply, ContinuousLinearMap.comp_apply] using hh

theorem lpTranslate_representative (p : ℝ≥0∞) [Fact (1 ≤ p)] (h : ℝ)
    (f : Lp 𝕜 p (volume : Measure ℝ)) :
    lpTranslate p h f =ᵐ[volume] fun x => f (x - h) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_sub_right volume h)

theorem translation_primal : TranslationPrimal (𝕜 := 𝕜) := by
  have hc (f : Lp 𝕜 1 (volume : Measure ℝ)) : Continuous (fun h : ℝ => lpTranslate 1 h f) := by
    let g : ℝ → C(ℝ, ℝ) := fun h => ⟨fun x => x - h, continuous_id.sub continuous_const⟩
    have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
      (continuous_snd.sub continuous_fst)
    exact continuous_const.compMeasurePreservingLp hg
      (fun h => measurePreserving_sub_right volume h) (by norm_num)
  refine ⟨⟨fun t => lpTranslate 1 (t : ℝ), lpTranslate_zero 1,
    fun t s => lpTranslate_add 1 (t : ℝ) (s : ℝ), ?_⟩, rfl⟩
  intro f
  have hlim := ((hc f).comp (NNReal.continuous_coe.comp continuous_real_toNNReal)).tendsto 0
  have hlim' : Tendsto (fun h : ℝ => lpTranslate 1 (h.toNNReal : ℝ) f)
      (𝓝 (0 : ℝ)) (𝓝 f) := by
    simpa only [Function.comp_def, Real.toNNReal_zero, NNReal.coe_zero,
      lpTranslate_zero, ContinuousLinearMap.id_apply] using hlim
  exact hlim'.mono_left nhdsWithin_le_nhds

theorem linftyToDual_apply (g : Lp 𝕜 ∞ (volume : Measure ℝ))
    (f : Lp 𝕜 1 (volume : Measure ℝ)) :
    linftyToDual g f = ∫ x : ℝ, g x * f x :=
  by simpa only [linftyToDual, ContinuousLinearMap.mul_apply'] using
    (ContinuousLinearMap.mul 𝕜 𝕜).lpPairing_eq_integral g f

theorem translation_adjoint : TranslationAdjoint (𝕜 := 𝕜) := by
  intro h g
  ext f
  change linftyToDual g (lpTranslate 1 h f) = linftyToDual (lpTranslate ∞ (-h) g) f
  rw [linftyToDual_apply, linftyToDual_apply]
  calc
    _ = ∫ x : ℝ, g x * f (x - h) := by
      apply integral_congr_ae
      filter_upwards [lpTranslate_representative 1 h f] with x hx
      rw [hx]
    _ = ∫ x : ℝ, g (x + h) * f x := by
      have heq := integral_add_right_eq_self (μ := (volume : Measure ℝ))
        (fun x : ℝ => g x * f (x - h)) h
      simpa only [add_sub_cancel_right] using heq.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [lpTranslate_representative ∞ (-h) g] with x hx
      simp only [sub_neg_eq_add] at hx
      rw [hx]

/-- The integral realization is contractive into the genuine normed dual. -/
theorem norm_linftyToDual_le (g : Lp 𝕜 ∞ (volume : Measure ℝ)) :
    ‖linftyToDual g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  let v : Lp 𝕜 1 (volume : Measure ℝ) := (ContinuousLinearMap.mul 𝕜 𝕜).holder 1 g f
  calc
    ‖linftyToDual g f‖ = ‖L1.integral v‖ := by
      rw [linftyToDual_apply, L1.integral_eq_integral]
      apply congrArg norm
      apply integral_congr_ae
      exact ((ContinuousLinearMap.mul 𝕜 𝕜).coeFn_holder g f).symm
    _ ≤ ‖v‖ := L1.norm_integral_le v
    _ ≤ ‖ContinuousLinearMap.mul 𝕜 𝕜‖ * ‖g‖ * ‖f‖ :=
      (ContinuousLinearMap.mul 𝕜 𝕜).norm_holder_apply_apply_le g f
    _ ≤ ‖g‖ * ‖f‖ := by
      calc
        _ ≤ 1 * ‖g‖ * ‖f‖ := by
          gcongr
          exact ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
        _ = _ := by rw [one_mul]

private def intervalLp (p : ℝ≥0∞) (a b : ℝ) (c : 𝕜) :
    Lp 𝕜 p (volume : Measure ℝ) :=
  indicatorConstLp (s := Ico a b) p measurableSet_Ico (by simp [Real.volume_Ico]) c

private theorem intervalLp_representative (p : ℝ≥0∞) (a b : ℝ) (c : 𝕜) :
    intervalLp p a b c =ᵐ[volume] (Ico a b).indicator (fun _ => c) :=
  by unfold intervalLp; exact indicatorConstLp_coeFn

private theorem intervalLp_norm_top (a b : ℝ) (hab : a < b) (c : 𝕜) :
    ‖intervalLp ∞ a b c‖ = ‖c‖ := by
  unfold intervalLp
  apply norm_indicatorConstLp_top
  simp only [Real.volume_Ico, ne_eq, ENNReal.ofReal_eq_zero]
  exact not_le.mpr (sub_pos.mpr hab)

private theorem intervalLp_norm_one (a b : ℝ) (hab : a < b) (c : 𝕜) :
    ‖intervalLp 1 a b c‖ = ‖c‖ * (b - a) := by
  rw [intervalLp, norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_one, div_one, Real.rpow_one,
    Real.volume_real_Ico_of_le hab.le]

private theorem intervalLp_pairing (a b : ℝ) (c : 𝕜) :
    linftyToDual (intervalLp ∞ a b c) (intervalLp 1 a b (1 : 𝕜)) =
      (volume.real (Ico a b)) • c := by
  rw [linftyToDual_apply]
  calc
    _ = ∫ x : ℝ, (Ico a b).indicator (fun _ => c) x := by
      apply integral_congr_ae
      filter_upwards [intervalLp_representative ∞ a b c,
        intervalLp_representative 1 a b (1 : 𝕜)] with x hx hy
      rw [hx, hy]
      by_cases h : x ∈ Ico a b <;> simp [Set.indicator, h]
    _ = _ := integral_indicator_const c measurableSet_Ico

private theorem intervalLp_dual_norm (a b : ℝ) (hab : a < b) (c : 𝕜) :
    ‖linftyToDual (intervalLp ∞ a b c)‖ = ‖c‖ := by
  apply le_antisymm
  · exact (norm_linftyToDual_le _).trans_eq (intervalLp_norm_top a b hab c)
  · have h := (linftyToDual (intervalLp ∞ a b c)).le_opNorm (intervalLp 1 a b (1 : 𝕜))
    rw [intervalLp_pairing, norm_smul, Real.norm_eq_abs,
      Real.volume_real_Ico_of_le hab.le, abs_of_pos (sub_pos.mpr hab),
      intervalLp_norm_one a b hab, norm_one, one_mul] at h
    exact (mul_le_mul_iff_right₀ (sub_pos.mpr hab)).mp (by simpa only [mul_comm] using h)

private theorem halfLine_representative :
    halfLine (𝕜 := 𝕜) =ᵐ[volume] halfLineFunction :=
  halfLine_memLp.coeFn_toLp

private theorem halfLine_difference_pos (h : ℝ) (hh : 0 < h) :
    lpTranslate ∞ h (halfLine (𝕜 := 𝕜)) - halfLine = intervalLp ∞ 0 h (-1 : 𝕜) := by
  apply Lp.ext
  have hshift := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae_eq_comp
    (halfLine_representative (𝕜 := 𝕜))
  filter_upwards [Lp.coeFn_sub (lpTranslate ∞ h (halfLine (𝕜 := 𝕜))) halfLine,
    lpTranslate_representative ∞ h (halfLine (𝕜 := 𝕜)), hshift,
    halfLine_representative (𝕜 := 𝕜), intervalLp_representative ∞ 0 h (-1 : 𝕜)]
    with x hsub ht hs hg hi
  dsimp only [Function.comp_apply] at hs
  rw [hsub, Pi.sub_apply, ht, hs, hg, hi]
  dsimp only [Function.comp_apply, halfLineFunction]
  by_cases hx : 0 ≤ x
  · by_cases hxh : x < h
    · have hxmh : ¬ 0 ≤ x - h := by linarith
      simp [Set.indicator, hx, hxh, hxmh]
    · have hxmh : 0 ≤ x - h := by linarith
      simp [Set.indicator, hx, hxh, hxmh]
  · have hxmh : ¬ 0 ≤ x - h := by linarith
    simp [Set.indicator, hx, hxmh]

private theorem halfLine_difference_neg (h : ℝ) (hh : h < 0) :
    lpTranslate ∞ h (halfLine (𝕜 := 𝕜)) - halfLine = intervalLp ∞ h 0 (1 : 𝕜) := by
  apply Lp.ext
  have hshift := (measurePreserving_sub_right volume h).quasiMeasurePreserving.ae_eq_comp
    (halfLine_representative (𝕜 := 𝕜))
  filter_upwards [Lp.coeFn_sub (lpTranslate ∞ h (halfLine (𝕜 := 𝕜))) halfLine,
    lpTranslate_representative ∞ h (halfLine (𝕜 := 𝕜)), hshift,
    halfLine_representative (𝕜 := 𝕜), intervalLp_representative ∞ h 0 (1 : 𝕜)]
    with x hsub ht hs hg hi
  dsimp only [Function.comp_apply] at hs
  rw [hsub, Pi.sub_apply, ht, hs, hg, hi]
  dsimp only [Function.comp_apply, halfLineFunction]
  by_cases hx : 0 ≤ x
  · have hxmh : 0 ≤ x - h := by linarith
    simp [Set.indicator, hx, hxmh, not_lt.mpr hx]
  · by_cases hxh : h ≤ x
    · have hxmh : 0 ≤ x - h := sub_nonneg.mpr hxh
      simp [Set.indicator, hx, hxh, hxmh, lt_of_not_ge hx]
    · have hxmh : ¬ 0 ≤ x - h := by linarith
      simp [Set.indicator, hx, hxh, hxmh]

theorem translation_step_distance : TranslationStepDistance (𝕜 := 𝕜) := by
  intro h hh
  rw [← map_sub linftyToDual]
  rcases lt_or_gt_of_ne hh with hneg | hpos
  · rw [halfLine_difference_neg h hneg, intervalLp_norm_top h 0 hneg,
      intervalLp_dual_norm h 0 hneg, norm_one]
    exact ⟨rfl, rfl⟩
  · rw [halfLine_difference_pos h hpos, intervalLp_norm_top 0 h hpos,
      intervalLp_dual_norm 0 h hpos, norm_neg, norm_one]
    exact ⟨rfl, rfl⟩

theorem translation_not_strong : TranslationNotStrong (𝕜 := 𝕜) := by
  intro hlim
  have hnorm : Tendsto (fun h : ℝ =>
      ‖(linftyToDual (halfLine (𝕜 := 𝕜))).comp (lpTranslate 1 h) - linftyToDual halfLine‖)
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Tendsto (fun _ : ℝ => linftyToDual (halfLine (𝕜 := 𝕜)))
        (𝓝[>] 0) (𝓝 (linftyToDual (halfLine (𝕜 := 𝕜)))) := tendsto_const_nhds
    simpa only [sub_self, norm_zero] using (hlim.sub hc).norm
  have heq : (fun h : ℝ =>
      ‖(linftyToDual (halfLine (𝕜 := 𝕜))).comp (lpTranslate 1 h) - linftyToDual halfLine‖)
      =ᶠ[𝓝[>] 0] (fun _ => (1 : ℝ)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    rw [translation_adjoint]
    exact (translation_step_distance (-h) (neg_ne_zero.mpr (ne_of_gt hh))).2
  have hbad : (0 : ℝ) = 1 :=
    tendsto_nhds_unique (hnorm.congr' heq) tendsto_const_nhds
  exact zero_ne_one hbad

/-- Assemble the explicit counterexample in the canonical C₀ semigroup interface. -/
theorem translation_counterexample : TranslationCounterexample (𝕜 := 𝕜) := by
  obtain ⟨T, hT⟩ := translation_primal (𝕜 := 𝕜)
  refine ⟨T, hT, ?_, ?_⟩
  · intro t g
    change (linftyToDual g).comp (T.operators t) = _
    rw [hT]
    exact translation_adjoint (t : ℝ) g
  · intro hlim
    apply translation_not_strong (𝕜 := 𝕜)
    have heq : (fun h : ℝ => adjointOperators T h.toNNReal
        (linftyToDual (halfLine (𝕜 := 𝕜)))) =ᶠ[𝓝[>] 0]
        (fun h : ℝ => (linftyToDual (halfLine (𝕜 := 𝕜))).comp (lpTranslate 1 h)) := by
      filter_upwards [self_mem_nhdsWithin] with h hh
      change (linftyToDual (halfLine (𝕜 := 𝕜))).comp (T.operators h.toNNReal) = _
      simp only [hT, Real.coe_toNNReal h hh.le]
    exact hlim.congr' heq

end Translations
end ExpandedFA.Semigroups.AdjointSemigroups
