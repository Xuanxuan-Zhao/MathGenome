import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.BlaschkeInterpolation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.Herglotz
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.BlaschkeProducts
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.CanonicalDecomposition

noncomputable section
open Set MeasureTheory

namespace ExpandedFA.PartV.BlaschkeInterpolation
open ExpandedFA.PartIV.PositiveHarmonic
open ExpandedFA.PartIV.BlaschkeProducts


variable {E X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (g : X → E)

lemma short_combination {x : E} (hx : x ∈ convexHull ℝ (range g)) :
    ∃ k ≤ Module.finrank ℝ E + 1, ∃ (w : Fin k → ℝ) (v : Fin k → X),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • g (v i) = x := by
  classical
  let t := Caratheodory.minCardFinsetOfMemConvexHull hx
  have ht : (t : Set E) ⊆ range g := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
  have hi : AffineIndependent ℝ ((↑) : t → E) :=
    Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have hc : Fintype.card t ≤ Module.finrank ℝ E + 1 := by
    have h := hi.card_le_finrank_succ
    exact h.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  have hm := Caratheodory.mem_minCardFinsetOfMemConvexHull hx
  change x ∈ convexHull ℝ (t : Set E) at hm
  rw [Finset.mem_convexHull'] at hm
  obtain ⟨w, hw, hs, hsum⟩ := hm
  let e := Fintype.equivFin t
  have hpre : ∀ i : Fin (Fintype.card t), ∃ y, g y = (e.symm i).val := fun i => ht (e.symm i).property
  choose v hv using hpre
  refine ⟨Fintype.card t, hc, (fun i => w (e.symm i)), v, ?_, ?_, ?_⟩
  · intro i
    exact hw _ (e.symm i).property
  · change ∑ i, (fun a : t => w a.val) (e.symm i) = 1
    rw [e.symm.sum_comp (fun a : t => w a.val)]
    simpa only [Finset.sum_coe_sort] using hs
  · simp_rw [hv]
    change ∑ i, (fun a : t => w a.val • a.val) (e.symm i) = x
    rw [e.symm.sum_comp (fun a : t => w a.val • a.val)]
    exact (Finset.sum_subtype t (by simp) (fun a => w a • a)).symm.trans hsum

variable [TopologicalSpace X] [CompactSpace X]

/-- Compactness of finite-dimensional convex hulls via bounded-length combinations. -/
lemma compact_convexHull_range (hg : Continuous g) : IsCompact (convexHull ℝ (range g)) := by
  classical
  let d := Module.finrank ℝ E + 1
  let B (k : Fin (d + 1)) := stdSimplex ℝ (Fin k.val) × (Fin k.val → X)
  let eval (k : Fin (d + 1)) (p : B k) : E := ∑ i, p.1.val i • g (p.2 i)
  have hB (k : Fin (d + 1)) : CompactSpace (B k) := by
    have : CompactSpace (stdSimplex ℝ (Fin k.val)) :=
      isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin k.val))
    exact inferInstance
  have heval (k : Fin (d + 1)) : Continuous (eval k) := by
    apply continuous_finsetSum
    intro i _
    exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).smul
      (hg.comp ((continuous_apply i).comp continuous_snd))
  have heq : convexHull ℝ (range g) = ⋃ k, range (eval k) := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk, w, v, hw, hs, hv⟩ := short_combination g hx
      refine mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_of_le hk⟩, ?_⟩
      exact ⟨(⟨w, hw, hs⟩, v), hv⟩
    · intro hx
      obtain ⟨k, p, rfl⟩ := mem_iUnion.mp hx
      exact mem_convexHull_of_exists_fintype p.1.val (fun i => g (p.2 i))
        p.1.property.1 p.1.property.2 (fun i => mem_range_self _) rfl
  rw [heq]
  exact isCompact_iUnion (fun k => @isCompact_range _ _ _ _ (hB k) _ (heval k))

variable [MeasurableSpace X] [BorelSpace X]

lemma atomic_barycenter (hg : Continuous g) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∃ k ≤ Module.finrank ℝ E + 1, ∃ (w : Fin k → ℝ) (v : Fin k → X),
      (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧ ∑ i, w i • g (v i) = ∫ x, g x ∂μ := by
  apply short_combination
  exact (convex_convexHull ℝ (range g)).integral_mem
    (compact_convexHull_range g hg).isClosed
    (Filter.Eventually.of_forall (fun x => subset_convexHull ℝ _ (mem_range_self x)))
    (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

theorem atomic_herglotz_samples : Spec.AtomicHerglotzSamples := by
  intro n z hz μ hμ
  let : IsProbabilityMeasure μ := hμ
  let g (ζ : Circle) : Fin n → ℂ := fun j => circleHerglotzKernel (z j) ζ
  have hg : Continuous g := continuous_pi (fun j => continuous_circleHerglotzKernel (hz j))
  obtain ⟨k, hk, w, v, hw, hs, hv⟩ := atomic_barycenter g hg μ
  have hdim : Module.finrank ℝ (Fin n → ℂ) = 2 * n := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, Nat.mul_comm]
  refine ⟨k, by simpa only [hdim] using hk, v, w, hw, hs, ?_⟩
  intro j
  have he := congrFun hv j
  have hi : Integrable g μ :=
    hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hproj := (ContinuousLinearMap.proj (R := ℝ) j).integral_comp_comm hi
  change (∫ ξ, g ξ j ∂μ) = (∫ ξ, g ξ ∂μ) j at hproj
  rw [← hproj] at he
  simpa [g, circleHerglotzKernel, herglotzRieszKernel,
    Finset.sum_apply, Complex.real_smul, mul_div_assoc] using he

/-- Explicit degree-zero products, with no nonempty-node assumption. -/
def constantProduct (c : ℂ) (hc : ‖c‖ = 1) : FiniteBlaschke where
  degree := 0
  phase := c
  phase_norm := hc
  zeros := Fin.elim0
  zeros_mem := fun i => Fin.elim0 i

@[simp] theorem constantProduct_eval (c : ℂ) (hc : ‖c‖ = 1) (z : ℂ) :
    (constantProduct c hc).eval z = c := by
  change c * (∏ i : Fin 0, factor (Fin.elim0 i) z) = c
  rw [Fin.prod_univ_zero, mul_one]

theorem empty_data : Spec.EmptyData := by
  exact ⟨constantProduct 1 (by simp), rfl, fun z => by simp⟩

theorem repeated_consistency : Spec.RepeatedConsistency := by
  rintro n z w ⟨f, hf, hfw⟩ i j hij
  rw [← hfw i, ← hfw j, hij]

theorem boundary_constant : Spec.BoundaryConstant := by
  intro f hf a ha hfa z hz
  apply Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    ExpandedFA.PartIV.Herglotz.unitDisk_connected.isPreconnected
    isOpen_unitDisk hf.1 ha (fun y hy => ?_) hz
  change ‖f y‖ ≤ ‖f a‖
  rw [hfa]
  exact hf.2 y hy

theorem boundary_interpolation : Spec.BoundaryInterpolation := by
  rintro n z w hz ⟨f, hf, hfw⟩ ⟨j, hj⟩
  refine ⟨constantProduct (w j) hj, rfl, ?_⟩
  intro i
  rw [constantProduct_eval, ← hfw i, ← hfw j]
  exact (boundary_constant f hf (z j) (hz j) (by rwa [hfw j]) (z i) (hz i)).symm

theorem product_geometry : Spec.ProductGeometry := by
  intro B
  have hzeros (i : Fin B.degree) : B.zeros i ∈ ExpandedFA.PartIV.HardyDiskSpec.disk := by
    simpa [unitDisk, ExpandedFA.PartIV.HardyDiskSpec.disk] using B.zeros_mem i
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact (differentiableOn_const (c := B.phase)).mul (DifferentiableOn.fun_finsetProd
      (fun i _ => by
        simpa [unitDisk, ExpandedFA.PartIV.HardyDiskSpec.disk, Metric.ball, dist_zero_right] using
          (factor_analytic (B.zeros i) (hzeros i)).differentiableOn))
  · intro z hz
    simp only [FiniteBlaschke.eval, norm_mul, B.phase_norm, one_mul, norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
      (fun i _ => factor_bound (B.zeros i) (hzeros i) z
        (by simpa [unitDisk, ExpandedFA.PartIV.HardyDiskSpec.disk] using hz))
  · intro z hz
    simp only [FiniteBlaschke.eval, norm_mul, B.phase_norm, one_mul, norm_prod]
    exact Finset.prod_eq_one (fun i _ => factor_boundary (B.zeros i) (hzeros i) z hz)


theorem finite_measure_samples : Spec.FiniteMeasureSamples := by
  intro n z hz μ hμ
  let : IsFiniteMeasure μ := hμ
  by_cases hzero : μ = 0
  · subst μ
    refine ⟨0, by omega, Fin.elim0, Fin.elim0, (fun i => Fin.elim0 i), ?_, ?_⟩
    · simp [Finset.univ_eq_empty]
    · intro j
      simp [Finset.univ_eq_empty]
  have hmass : μ univ ≠ 0 := by simpa using hzero
  have htop : μ univ ≠ ⊤ := measure_ne_top _ _
  let ν : Measure Circle := (μ univ)⁻¹ • μ
  have hprob : IsProbabilityMeasure ν := ⟨by
    simp [ν, Measure.smul_apply, ENNReal.inv_mul_cancel hmass htop]⟩
  obtain ⟨k, hk, v, w, hw, hs, hv⟩ := atomic_herglotz_samples n z hz ν hprob
  have hμν : μ = μ univ • ν := by
    simp [ν, smul_smul, ENNReal.mul_inv_cancel hmass htop]
  refine ⟨k, hk, v, (fun i => μ.real univ * w i),
    (fun i => mul_nonneg ENNReal.toReal_nonneg (hw i)), ?_, ?_⟩
  · rw [← Finset.mul_sum, hs, mul_one]
  · intro j
    calc
      _ = (μ.real univ : ℂ) *
          (∑ i, (w i : ℂ) * ((v i : ℂ) + z j) / ((v i : ℂ) - z j)) := by
        simp only [Complex.ofReal_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (μ.real univ : ℂ) *
          (∫ ξ : Circle, ((ξ : ℂ) + z j) / ((ξ : ℂ) - z j) ∂ν) := by rw [hv j]
      _ = _ := by
        conv_rhs => rw [hμν]
        rw [show (∫ ξ : Circle, ((ξ : ℂ) + z j) / ((ξ : ℂ) - z j) ∂(μ univ • ν)) =
          (μ univ).toReal • (∫ ξ : Circle, ((ξ : ℂ) + z j) / ((ξ : ℂ) - z j) ∂ν) from
          integral_smul_measure _ _]
        rw [Complex.real_smul]
        rfl

lemma one_sub_ne_zero_of_norm_lt_one {t : ℂ} (ht : ‖t‖ < 1) : 1 - t ≠ 0 := by
  intro h
  have : t = 1 := (sub_eq_zero.mp h).symm
  simp [this] at ht

lemma cayley_re_pos {t : ℂ} (ht : ‖t‖ < 1) : 0 < ((1 + t) / (1 - t)).re := by
  have hnorm : Complex.normSq t < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg t]
  have hden : 0 < Complex.normSq (1 - t) :=
    Complex.normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one ht)
  rw [Complex.div_re, ← add_div]
  apply div_pos _ hden
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im,
    Complex.one_im, Complex.sub_im]
  dsimp [Complex.normSq] at hnorm
  nlinarith

lemma cayley_inverse {t : ℂ} (ht : ‖t‖ < 1) :
    (((1 + t) / (1 - t)) - 1) / (((1 + t) / (1 - t)) + 1) = t := by
  have hd := one_sub_ne_zero_of_norm_lt_one ht
  have hplus : (1 + t) / (1 - t) + 1 ≠ 0 := by
    intro h
    have := cayley_re_pos ht
    have he := congrArg Complex.re h
    simp at he
    linarith
  field_simp
  ring

/-- Assembly theorem with the two remaining analytic bridges made explicit.
This is not a proof of `Spec.Interpolation` until both bridges are supplied. -/
theorem interpolation_of_bridges
    (extend : Spec.AtomicCayleyExtension) (factorize : Spec.ClosedDiskFactorization) :
    Spec.Interpolation := by
  rintro n z w hz ⟨f, hf, hfw⟩
  by_cases hboundary : ∃ a ∈ unitDisk, ‖f a‖ = 1
  · obtain ⟨a, ha, hfa⟩ := hboundary
    refine ⟨constantProduct (f a) hfa, ?_⟩
    intro j
    rw [constantProduct_eval, ← hfw j]
    exact (boundary_constant f hf a ha hfa (z j) (hz j)).symm
  have hstrict : ∀ a ∈ unitDisk, ‖f a‖ < 1 := by
    intro a ha
    exact lt_of_le_of_ne (hf.2 a ha) (fun h => hboundary ⟨a, ha, h⟩)
  let H : ℂ → ℂ := fun a => (1 + f a) / (1 - f a)
  have hH : ExpandedFA.PartIV.Herglotz.NonnegativeHolomorphic H := by
    refine ⟨((differentiableOn_const (c := (1 : ℂ))).add hf.1).div
      ((differentiableOn_const (c := (1 : ℂ))).sub hf.1)
      (fun a ha => one_sub_ne_zero_of_norm_lt_one (hstrict a ha)), ?_⟩
    exact fun a ha => (cayley_re_pos (hstrict a ha)).le
  obtain ⟨⟨μ, c⟩, hrep, _⟩ := ExpandedFA.PartIV.Herglotz.representation H hH
  have hmass : 0 < μ.real univ := by
    rw [(ExpandedFA.PartIV.Herglotz.center_normalization H μ c hrep).2]
    exact cayley_re_pos (hstrict 0 (by simp [unitDisk]))
  obtain ⟨k, hk, v, u, hu, hs, hv⟩ := finite_measure_samples n z hz μ hrep.1
  obtain ⟨G, hGa, hGb, hGe⟩ := extend k v u c hu (by rwa [hs])
  obtain ⟨B, hB⟩ := factorize G hGa hGb
  refine ⟨B, ?_⟩
  intro j
  rw [hB (hz j), hGe (z j) (hz j), hv j]
  have hj := hrep.2.2 (z j) (hz j)
  unfold ExpandedFA.PartIV.Herglotz.herglotzTransform at hj
  rw [← hj]
  exact (cayley_inverse (hstrict (z j) (hz j))).trans (hfw j)

/-! The remaining bridges: removal of the boundary singularities and finite
factorization of functions analytic near the closed disk. -/
open Filter Metric Complex MeromorphicOn
open scoped Topology ComplexConjugate

lemma closedBall_eq_of_codiscrete {f g : ℂ → ℂ}
    (hf : ContinuousOn f (closedBall 0 1)) (hg : ContinuousOn g (closedBall 0 1))
    (h : f =ᶠ[codiscreteWithin (closedBall 0 1)] g) : EqOn f g (closedBall 0 1) := by
  have hi : EqOn f g (ball 0 1) := by
    intro z hz
    have he : f =ᶠ[𝓝[≠] z] g := by
      have hh := mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp h z (ball_subset_closedBall hz)
      filter_upwards [hh, nhdsWithin_le_nhds (isOpen_ball.mem_nhds hz)] with x hx hxball
      exact hx.resolve_right (not_not.mpr (ball_subset_closedBall hxball))
    have hfc : ContinuousAt f z := (hf.mono ball_subset_closedBall).continuousAt (isOpen_ball.mem_nhds hz)
    have hgc : ContinuousAt g z := (hg.mono ball_subset_closedBall).continuousAt (isOpen_ball.mem_nhds hz)
    exact tendsto_nhds_unique (hfc.tendsto.mono_left nhdsWithin_le_nhds)
      ((hgc.tendsto.mono_left nhdsWithin_le_nhds).congr' he.symm)
  apply hi.of_subset_closure hf hg ball_subset_closedBall
  rw [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)]

lemma unimodular_constant {q : ℂ → ℂ} (hq : AnalyticOnNhd ℂ q (closedBall 0 1))
    (hn : ∀ z ∈ closedBall 0 1, q z ≠ 0)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → ‖q z‖ = 1) :
    ‖q 0‖ = 1 ∧ EqOn q (fun _ => q 0) (ball 0 1) := by
  have hbound {v : ℂ → ℂ} (hv : AnalyticOnNhd ℂ v (closedBall 0 1))
      (hbv : ∀ z : ℂ, ‖z‖ = 1 → ‖v z‖ ≤ 1) : ∀ z ∈ closedBall 0 1, ‖v z‖ ≤ 1 := by
    intro z hz
    apply Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hv.differentiableOn.diffContOnCl_ball (by rfl)) _
      (by simpa only [closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] using hz)
    intro a ha
    rw [frontier_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at ha
    exact hbv a (by simpa using ha)
  have hle := hbound hq (fun z hz => (hb z hz).le)
  have hinv : AnalyticOnNhd ℂ (fun z => (q z)⁻¹) (closedBall 0 1) :=
    fun z hz => (hq z hz).inv (hn z hz)
  have hleinv := hbound hinv (by intro z hz; simp [hb z hz])
  have hnorm : ∀ z ∈ closedBall 0 1, ‖q z‖ = 1 := by
    intro z hz
    apply le_antisymm (hle z hz)
    have hh := hleinv z hz
    rw [norm_inv, inv_le_one₀ (norm_pos_iff.mpr (hn z hz))] at hh
    exact hh
  refine ⟨hnorm 0 (by simp), ?_⟩
  intro z hz
  exact Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball (0 : ℂ) 1).isPreconnected isOpen_ball
    (hq.differentiableOn.mono ball_subset_closedBall) (by simp : (0 : ℂ) ∈ ball 0 1)
    (fun a ha => by simp [hnorm a (ball_subset_closedBall ha), hnorm 0 (by simp)]) hz

lemma inverse_canonical_eq (a z : ℂ) (ha : a ∈ ball 0 1) (hz : z ∈ closedBall 0 1) :
    (canonicalFactor 1 a z)⁻¹ =
      (if a = 0 then 1 else -a / (‖a‖ : ℂ)) * factor a z := by
  have had : a ∈ ExpandedFA.PartIV.HardyDiskSpec.disk := by
    simpa [ExpandedFA.PartIV.HardyDiskSpec.disk] using ha
  have hd := denominator_ne_zero had (by simpa using hz)
  by_cases h : a = 0
  · subst a
    simp [canonicalFactor_apply, factor]
  · have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.mpr h)
    simp only [canonicalFactor_apply, one_pow, Complex.ofReal_one, one_mul,
      inv_div, ite_eq_right h, factor]
    field_simp
    ring

lemma norm_canonical_phase (a : ℂ) : ‖(if a = 0 then 1 else -a / (‖a‖ : ℂ))‖ = 1 := by
  split_ifs with h
  · simp
  · simp [norm_ne_zero_iff.mpr h]


/-- Reindex an arbitrary finite zero family by `Fin degree`. -/
def productOfFamily {ι : Type} [Fintype ι] (a : ι → ℂ)
    (ha : ∀ i, a i ∈ unitDisk) (c : ℂ) (hc : ‖c‖ = 1) : FiniteBlaschke where
  degree := Fintype.card ι
  phase := c
  phase_norm := hc
  zeros := fun j => a ((Fintype.equivFin ι).symm j)
  zeros_mem := fun _ => ha _

lemma productOfFamily_eval {ι : Type} [Fintype ι] (a : ι → ℂ)
    (ha : ∀ i, a i ∈ unitDisk) (c : ℂ) (hc : ‖c‖ = 1) (z : ℂ) :
    (productOfFamily a ha c hc).eval z = c * ∏ i, factor (a i) z := by
  change c * (∏ j, factor (a ((Fintype.equivFin ι).symm j)) z) = _
  rw [(Fintype.equivFin ι).symm.prod_comp (fun i => factor (a i) z)]

theorem closed_disk_factorization : Spec.ClosedDiskFactorization := by
  intro G hG hb
  classical
  have hm := hG.meromorphicOn
  have horder : ∀ u : closedBall (0 : ℂ) 1, meromorphicOrderAt G u ≠ ⊤ := by
    apply (hm.exists_meromorphicOrderAt_ne_top_iff_forall (isConnected_closedBall (by norm_num))).mp
    refine ⟨⟨1, by simp⟩, ?_⟩
    rw [((hG 1 (by simp)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr ?_)]
    · simp
    · have hh := hb 1 (by simp)
      exact norm_ne_zero_iff.mp (by rw [hh]; norm_num)
  obtain ⟨h, hh⟩ := hm.exists_ecanonicalDecomp horder
  let D := divisor G (ball 0 1)
  have hDfin : D.support.Finite := hm.divisor_ball_support_finite
  let s := hDfin.toFinset
  have hs (a : s) : (a : ℂ) ∈ ball 0 1 :=
    D.supportWithinDomain (hDfin.mem_toFinset.mp a.property)
  have hDnonneg : ∀ a, 0 ≤ D a := hG.mono ball_subset_closedBall |>.divisor_nonneg
  let ι := (a : s) × Fin (D a).toNat
  let a : ι → ℂ := fun j => j.1.val
  have ha : ∀ j, a j ∈ unitDisk := by
    intro j
    simpa [unitDisk, a] using hs j.1
  let P (z : ℂ) := ∏ i : ι, factor (a i) z
  let k : ℂ := ∏ i : ι, if a i = 0 then 1 else -a i / (‖a i‖ : ℂ)
  have hk : ‖k‖ = 1 := by
    dsimp [k]
    rw [norm_prod]
    exact Finset.prod_eq_one (fun i _ => norm_canonical_phase (a i))
  have hP : AnalyticOnNhd ℂ P (closedBall 0 1) := by
    intro z hz
    have ht : ∀ i : ι, AnalyticAt ℂ (factor (a i)) z := by
      intro i
      apply analyticAt_factor_closed
      · simpa [ExpandedFA.PartIV.HardyDiskSpec.disk, unitDisk] using ha i
      · simpa using hz
    convert Finset.analyticAt_prod Finset.univ (fun i _ => ht i) using 1
    ext x
    simp [P]
  have hprod (z : ℂ) (hz : z ∈ closedBall 0 1) :
      (∏ᶠ u, (canonicalFactor 1 u) ^ (-D u)) z = k * P z := by
    have hsupport : Function.mulSupport (fun u => (canonicalFactor 1 u) ^ (-D u)) ⊆ D.support := by
      intro u hu
      by_contra h
      have hz : D u = 0 := by simpa only [Function.mem_support, not_not] using h
      simp [hz] at hu
    rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hsupport hDfin]
    change (∏ u ∈ s, canonicalFactor 1 u ^ (-D u)) z = k * P z
    simp only [Finset.prod_apply, Pi.pow_apply]
    have hexp (u : s) : canonicalFactor 1 u z ^ (-D u) =
        ((if (u : ℂ) = 0 then 1 else -(u : ℂ) / (‖(u : ℂ)‖ : ℂ)) * factor u z) ^ (D u).toNat := by
      conv_lhs => rw [← Int.toNat_of_nonneg (hDnonneg u)]
      rw [zpow_neg, zpow_natCast, ← inv_pow, inverse_canonical_eq u z (hs u) hz]
    rw [← Finset.prod_attach]
    change (∏ u : s, canonicalFactor 1 u z ^ (-D u)) = k * P z
    simp_rw [hexp, mul_pow]
    rw [Finset.prod_mul_distrib]
    dsimp [k, P, a, ι]
    simp only [Fintype.prod_sigma, Fin.prod_const, Finset.attach_eq_univ]
  have hboundarydiv : divisor G (sphere 0 1) = 0 := by
    ext z
    by_cases hz : z ∈ sphere (0 : ℂ) 1
    · have hn : G z ≠ 0 := norm_ne_zero_iff.mp (by rw [hb z (by simpa using hz)]; norm_num)
      rw [divisor_apply (hG.mono sphere_subset_closedBall).meromorphicOn hz,
        ((hG z (sphere_subset_closedBall hz)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hn)]
      rfl
    · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hz
  have he : EqOn G (fun z => (k * P z) * h z) (closedBall 0 1) := by
    apply closedBall_eq_of_codiscrete hG.continuousOn
      ((continuousOn_const.mul hP.continuousOn).mul hh.analyticOnNhd.continuousOn)
    filter_upwards [hh.eventuallyEq, self_mem_codiscreteWithin (closedBall (0 : ℂ) 1)] with z hz hzball
    rw [hboundarydiv] at hz
    simp only [Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, zpow_zero, finprod_one, mul_one, smul_eq_mul] at hz
    change G z = (∏ᶠ u, (canonicalFactor 1 u) ^ (-D u)) z * h z at hz
    rwa [hprod z hzball] at hz
  let q : ℂ → ℂ := fun z => k * h z
  have hq : AnalyticOnNhd ℂ q (closedBall 0 1) := analyticOnNhd_const.mul hh.analyticOnNhd
  have hqn : ∀ z ∈ closedBall (0 : ℂ) 1, q z ≠ 0 := by
    intro z hz
    exact mul_ne_zero (norm_ne_zero_iff.mp (by rw [hk]; norm_num)) (hh.ne_zero z hz)
  have hqb : ∀ z : ℂ, ‖z‖ = 1 → ‖q z‖ = 1 := by
    intro z hz
    have hPnorm : ‖P z‖ = 1 := by
      dsimp [P]
      rw [norm_prod]
      apply Finset.prod_eq_one
      intro i _
      exact factor_boundary (a i) (by simpa [unitDisk, ExpandedFA.PartIV.HardyDiskSpec.disk] using ha i) z hz
    have hez := congrArg norm (he (show z ∈ closedBall 0 1 by simpa using hz.le))
    rw [hb z hz, norm_mul, norm_mul, hk, hPnorm] at hez
    simpa [q, norm_mul, hk] using hez.symm
  obtain ⟨hq0, hconst⟩ := unimodular_constant hq hqn hqb
  refine ⟨productOfFamily a ha (q 0) hq0, ?_⟩
  intro z hz
  have hzb : z ∈ ball (0 : ℂ) 1 := by simpa [unitDisk] using hz
  rw [productOfFamily_eval, he (ball_subset_closedBall hzb)]
  change q 0 * P z = k * P z * h z
  rw [← show q z = q 0 from hconst hzb]
  dsimp [q]
  ring


lemma kernel_re_formula (ξ z : ℂ) :
    (((ξ + z) / (ξ - z))).re = (Complex.normSq ξ - Complex.normSq z) / Complex.normSq (ξ - z) := by
  rw [Complex.div_re]
  simp only [Complex.add_re, Complex.sub_re, Complex.add_im, Complex.sub_im, Complex.normSq_apply]
  ring

lemma cayley_den_ne_zero {x : ℂ} (hx : 0 ≤ x.re) : x + 1 ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp at he
  linarith

lemma cayley_norm_one {x : ℂ} (hx : x.re = 0) : ‖(x - 1) / (x + 1)‖ = 1 := by
  have hd := cayley_den_ne_zero (le_of_eq hx.symm)
  have hn : ‖x - 1‖ = ‖x + 1‖ := by
    have he : Complex.normSq (x - 1) = Complex.normSq (x + 1) := by
      simp [Complex.normSq_apply, hx]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at he
    nlinarith [norm_nonneg (x - 1), norm_nonneg (x + 1)]
  rw [norm_div, hn, div_self (norm_ne_zero_iff.mpr hd)]

lemma normalForm_local_extension {f r : ℂ → ℂ} {U : Set ℂ} {a : ℂ}
    (hf : MeromorphicOn f U) (ha : a ∈ U) (hr : AnalyticAt ℂ r a)
    (he : f =ᶠ[𝓝[≠] a] r) :
    AnalyticAt ℂ (toMeromorphicNFOn f U) a ∧ toMeromorphicNFOn f U a = r a := by
  have h := (toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds hf ha).trans
    (toMeromorphicNFAt_eventuallyEq_nhds_congr he)
  rw [toMeromorphicNFAt_eq_self.mpr hr.meromorphicNFAt] at h
  exact ⟨(analyticAt_congr h).mpr hr, h.eq_of_nhds⟩

/-- Finite atomic Herglotz transform with unnormalized nonnegative weights. -/
def atomicTransform {m : ℕ} (ξ : Fin m → Circle) (w : Fin m → ℝ) (c : ℝ) (z : ℂ) : ℂ :=
  Complex.I * (c : ℂ) + ∑ i, (w i : ℂ) * ((ξ i : ℂ) + z) / ((ξ i : ℂ) - z)

lemma atomicTransform_re_nonneg {m : ℕ} (ξ : Fin m → Circle) (w : Fin m → ℝ) (c : ℝ)
    (hw : ∀ i, 0 ≤ w i) {z : ℂ} (hz : ‖z‖ ≤ 1) : 0 ≤ (atomicTransform ξ w c z).re := by
  simp only [atomicTransform, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_self, zero_add]
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [mul_div_assoc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply mul_nonneg (hw i)
  rw [kernel_re_formula]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow]
  nlinarith [norm_nonneg z]

lemma atomicTransform_re_boundary {m : ℕ} (ξ : Fin m → Circle) (w : Fin m → ℝ) (c : ℝ)
    {z : ℂ} (hz : ‖z‖ = 1) : (atomicTransform ξ w c z).re = 0 := by
  unfold atomicTransform
  simp only [Complex.add_re]
  have he (i : Fin m) : (((w i : ℂ) * ((ξ i : ℂ) + z) / ((ξ i : ℂ) - z))).re = 0 := by
    rw [mul_div_assoc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [kernel_re_formula, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      Circle.norm_coe, hz, sub_self, zero_div, mul_zero]
  simp [he]

lemma atomicTransform_analytic_interior {m : ℕ} (ξ : Fin m → Circle) (w : Fin m → ℝ) (c : ℝ)
    {z : ℂ} (hz : ‖z‖ < 1) : AnalyticAt ℂ (atomicTransform ξ w c) z := by
  have ht (i : Fin m) : AnalyticAt ℂ
      (fun u => (w i : ℂ) * ((ξ i : ℂ) + u) / ((ξ i : ℂ) - u)) z := by
    refine (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
      (analyticAt_const.sub analyticAt_id) ?_
    intro h
    have he := congrArg norm (sub_eq_zero.mp h)
    rw [Circle.norm_coe] at he
    linarith
  convert (analyticAt_const (v := Complex.I * (c : ℂ))).add (Finset.analyticAt_sum Finset.univ (fun i _ => ht i)) using 1
  ext u
  simp [atomicTransform]


/-- Local cancellation at a boundary point, grouping every coincident atom. -/
lemma atomic_cayley_boundary_extension {m : ℕ} (ξ : Fin m → Circle) (w : Fin m → ℝ)
    (c : ℝ) (a : ℂ) (ha : ‖a‖ = 1) :
    ∃ r : ℂ → ℂ, AnalyticAt ℂ r a ∧
      (fun z => (atomicTransform ξ w c z - 1) / (atomicTransform ξ w c z + 1)) =ᶠ[𝓝[≠] a] r ∧
      ‖r a‖ = 1 := by
  classical
  let W : ℝ := ∑ i, if (ξ i : ℂ) = a then w i else 0
  let S (z : ℂ) := Complex.I * (c : ℂ) +
    ∑ i, if (ξ i : ℂ) = a then 0 else (w i : ℂ) * ((ξ i : ℂ) + z) / ((ξ i : ℂ) - z)
  have hS : AnalyticAt ℂ S a := by
    have ht (i : Fin m) : AnalyticAt ℂ (fun z =>
        if (ξ i : ℂ) = a then 0 else (w i : ℂ) * ((ξ i : ℂ) + z) / ((ξ i : ℂ) - z)) a := by
      by_cases hi : (ξ i : ℂ) = a
      · simp only [hi, ↓reduceIte]
        exact analyticAt_const
      · simp only [hi, ↓reduceIte]
        exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
          (analyticAt_const.sub analyticAt_id) (sub_ne_zero.mpr hi)
    convert (analyticAt_const (v := Complex.I * (c : ℂ))).add
      (Finset.analyticAt_sum Finset.univ (fun i _ => ht i)) using 1
    ext z
    simp [S]
  have hgroup (z : ℂ) : atomicTransform ξ w c z = S z + (W : ℂ) * (a + z) / (a - z) := by
    have ht (i : Fin m) : (w i : ℂ) * ((ξ i : ℂ) + z) / ((ξ i : ℂ) - z) =
        (if (ξ i : ℂ) = a then 0 else (w i : ℂ) * ((ξ i : ℂ) + z) / ((ξ i : ℂ) - z)) +
        ((if (ξ i : ℂ) = a then w i else 0 : ℝ) : ℂ) * (a + z) / (a - z) := by
      by_cases hi : (ξ i : ℂ) = a <;> simp [hi]
    unfold atomicTransform
    rw [Finset.sum_congr rfl (fun i _ => ht i)]
    rw [Finset.sum_add_distrib]
    simp only [S, W, Complex.ofReal_sum, Finset.sum_mul, Finset.sum_div]
    ring
  by_cases hzero : W = 0
  · have he : atomicTransform ξ w c = S := by
      funext z
      simp [hgroup z, hzero]
    refine ⟨(fun z => (atomicTransform ξ w c z - 1) / (atomicTransform ξ w c z + 1)), ?_,
      Filter.EventuallyEq.rfl, cayley_norm_one (atomicTransform_re_boundary ξ w c ha)⟩
    have hH : AnalyticAt ℂ (atomicTransform ξ w c) a := he ▸ hS
    exact (hH.sub analyticAt_const).div (hH.add analyticAt_const)
      (cayley_den_ne_zero (by rw [atomicTransform_re_boundary ξ w c ha]))
  let N (z : ℂ) := (a - z) * (S z - 1) + (W : ℂ) * (a + z)
  let D (z : ℂ) := (a - z) * (S z + 1) + (W : ℂ) * (a + z)
  have hN : AnalyticAt ℂ N a :=
    ((analyticAt_const.sub analyticAt_id).mul (hS.sub analyticAt_const)).add
      (analyticAt_const.mul (analyticAt_const.add analyticAt_id))
  have hD : AnalyticAt ℂ D a :=
    ((analyticAt_const.sub analyticAt_id).mul (hS.add analyticAt_const)).add
      (analyticAt_const.mul (analyticAt_const.add analyticAt_id))
  have han : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
  have hWn : (W : ℂ) ≠ 0 := by exact_mod_cast hzero
  have hDn : D a ≠ 0 := by
    dsimp [D]
    simpa only [sub_self, zero_mul, zero_add, ← two_mul] using
      mul_ne_zero hWn (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) han)
  refine ⟨(fun z => N z / D z), hN.div hD hDn, ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hza : a - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    have hNe : N z = (a - z) * (atomicTransform ξ w c z - 1) := by
      rw [hgroup]
      dsimp [N]
      field_simp
      ring
    have hDe : D z = (a - z) * (atomicTransform ξ w c z + 1) := by
      rw [hgroup]
      dsimp [D]
      field_simp
      ring
    rw [hNe, hDe, mul_div_mul_left _ _ hza]
  · have he : N a = D a := by simp [N, D]
    change ‖N a / D a‖ = 1
    rw [he, div_self hDn, norm_one]


theorem atomic_cayley_extension : Spec.AtomicCayleyExtension := by
  intro m ξ w c hw _hmass
  let raw (z : ℂ) := (atomicTransform ξ w c z - 1) / (atomicTransform ξ w c z + 1)
  have hm : MeromorphicOn raw (closedBall 0 1) := by
    intro z _
    dsimp [raw, atomicTransform]
    fun_prop
  have hi (z : ℂ) (hz : ‖z‖ < 1) : AnalyticAt ℂ raw z :=
    ((atomicTransform_analytic_interior ξ w c hz).sub analyticAt_const).div
      ((atomicTransform_analytic_interior ξ w c hz).add analyticAt_const)
      (cayley_den_ne_zero (atomicTransform_re_nonneg ξ w c hw hz.le))
  let G := toMeromorphicNFOn raw (closedBall 0 1)
  have hG : AnalyticOnNhd ℂ G (closedBall 0 1) := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := by simpa using hz
    rcases lt_or_eq_of_le hzn with hzlt | hzeq
    · exact (normalForm_local_extension hm hz (hi z hzlt) Filter.EventuallyEq.rfl).1
    · obtain ⟨r, hr, he, _⟩ := atomic_cayley_boundary_extension ξ w c z hzeq
      exact (normalForm_local_extension hm hz hr he).1
  refine ⟨G, hG, ?_, ?_⟩
  · intro z hz
    obtain ⟨r, hr, he, hnorm⟩ := atomic_cayley_boundary_extension ξ w c z hz
    change ‖toMeromorphicNFOn raw (closedBall 0 1) z‖ = 1
    rw [(normalForm_local_extension hm (by simpa using hz.le) hr he).2]
    exact hnorm
  · intro z hz
    have hzn : ‖z‖ < 1 := hz
    exact (normalForm_local_extension hm (by simpa using hzn.le) (hi z hzn) Filter.EventuallyEq.rfl).2

theorem interpolation : Spec.Interpolation :=
  interpolation_of_bridges atomic_cayley_extension closed_disk_factorization

end ExpandedFA.PartV.BlaschkeInterpolation
