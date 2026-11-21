import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.HaarAveraging
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
The averaging part of `fa2:p5:haar`, paper.tex:23292–23321. We reuse the
library Haar measure constructed from compact covering numbers, integrate the
norm-continuous translation orbit, and use the closed-convex integral theorem.
This supplies the unique common hull constant without an action on measures.
The last theorem also gives the source's successive-averaging additivity
argument for a scalar function with the proved hull properties; it assumes
neither additivity nor continuity of that scalar function.
-/

noncomputable section
universe u v
open Set MeasureTheory MeasureTheory.Measure TopologicalSpace
open scoped Topology ENNReal
namespace ExpandedFA.PartV.HaarAveraging

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] {𝕜 : Type v} [RCLike 𝕜]

lemma continuous_translate (side : Side) (f : C(G, 𝕜)) :
    Continuous (fun s => translate side s f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  cases side
  · exact f.continuous.comp (continuous_fst.mul continuous_snd)
  · exact f.continuous.comp (continuous_snd.mul continuous_fst)

theorem compact_translate_hulls : Spec.CompactTranslateHulls.{u,v} := by
  intro G _ _ _ _ _ 𝕜 _ side f
  have hc := continuous_translate side f
  have ho : IsCompact (orbit side f) := isCompact_range hc
  exact ⟨hc, ho, ho.totallyBounded.convexHull.closure.isCompact_of_isClosed isClosed_closure⟩

-- Mathlib's Haar measure is constructed from compact covering numbers, not
-- from the averaging theorem being proved here. Normalize on the whole group.
private def probabilityHaar [MeasurableSpace G] [BorelSpace G] : Measure G :=
  Measure.haarMeasure (⟨⟨univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts G)

private instance [MeasurableSpace G] [BorelSpace G] :
    IsProbabilityMeasure (probabilityHaar (G := G)) :=
  ⟨Measure.haarMeasure_self⟩

private instance [MeasurableSpace G] [BorelSpace G] :
    (probabilityHaar (G := G)).IsHaarMeasure :=
  inferInstanceAs (Measure.IsHaarMeasure (Measure.haarMeasure _))

private instance [MeasurableSpace G] [BorelSpace G] :
    IsMulRightInvariant (probabilityHaar (G := G)) := by
  constructor
  intro g
  let μ := probabilityHaar (G := G)
  have heq := Measure.isMulInvariant_eq_smul_of_compactSpace (μ.map (· * g)) μ
  have hc : (Measure.haarScalarFactor (μ.map (· * g)) μ : ℝ≥0∞) = 1 := by
    have h := congrArg (fun ν : Measure G => ν univ) heq
    simpa using h.symm
  simpa [hc, ENNReal.smul_def] using heq

private def integralMean [MeasurableSpace G] [BorelSpace G] : C(G, 𝕜) →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂probabilityHaar (G := G)
      map_add' := fun f g => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c f }
    1 (fun f => by
      simpa using norm_integral_le_of_norm_le_const (μ := probabilityHaar (G := G))
        (Filter.Eventually.of_forall f.norm_coe_le_norm))

private lemma integralMean_const [MeasurableSpace G] [BorelSpace G] (c : 𝕜) :
    integralMean (ContinuousMap.const G c) = c := by
  change (∫ _ : G, c ∂probabilityHaar (G := G)) = c
  simp

private lemma integralMean_translate [MeasurableSpace G] [BorelSpace G]
    (side : Side) (s : G) (f : C(G, 𝕜)) :
    integralMean (translate side s f) = integralMean f := by
  cases side
  · exact integral_mul_left_eq_self f s
  · exact integral_mul_right_eq_self f s

private lemma integralMean_hull [MeasurableSpace G] [BorelSpace G]
    (side : Side) (f h : C(G, 𝕜)) (hh : h ∈ translateHull side f) :
    integralMean h = integralMean f := by
  let M : C(G, 𝕜) →L[𝕜] 𝕜 := integralMean
  have hc : Convex ℝ {h | M h = M f} := by
    exact (convex_singleton (M f)).linear_preimage (M.restrictScalars ℝ).toLinearMap
  apply closure_minimal (convexHull_min ?_ hc) (isClosed_eq M.continuous continuous_const) hh
  rintro _ ⟨s, rfl⟩
  exact integralMean_translate side s f

private lemma integralMean_const_mem_hull [MeasurableSpace G] [BorelSpace G]
    (side : Side) (f : C(G, 𝕜)) :
    ContinuousMap.const G (integralMean f) ∈ translateHull side f := by
  let μ := probabilityHaar (G := G)
  have hi : Integrable (fun s => translate side s f) μ :=
    (continuous_translate side f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have heq : (∫ s, translate side s f ∂μ) = ContinuousMap.const G (integralMean f) := by
    ext x
    rw [ContinuousMap.integral_apply hi]
    cases side
    · exact integral_mul_right_eq_self f x
    · exact integral_mul_left_eq_self f x
  rw [← heq]
  exact (convex_convexHull ℝ (orbit side f)).closure.integral_mem isClosed_closure
    (Filter.Eventually.of_forall fun s => subset_closure
      (subset_convexHull ℝ (orbit side f) (mem_range_self s))) hi

theorem exists_averaging_mean : Spec.ExistsAveragingMean.{u,v} := by
  intro G _ _ _ _ _ 𝕜 _
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let M : C(G, 𝕜) →L[𝕜] 𝕜 := integralMean
  have hconst : ∀ c, M (ContinuousMap.const G c) = c := integralMean_const
  have hnorm : ‖M‖ ≤ 1 := by
    apply M.opNorm_le_bound zero_le_one
    intro f
    simpa [M, integralMean] using
      norm_integral_le_of_norm_le_const (μ := probabilityHaar (G := G))
        (Filter.Eventually.of_forall f.norm_coe_le_norm)
  refine ⟨M, hconst, ?_, integralMean_translate, ?_, integralMean_hull, ?_⟩
  · intro f hf
    let r : G → ℝ := fun x => RCLike.re (f x)
    have hr (x : G) : 0 ≤ r x ∧ f x = (r x : 𝕜) := by
      obtain ⟨t, ht, hft⟩ := hf x
      simpa [r, hft] using And.intro ht hft
    refine ⟨∫ x, r x ∂probabilityHaar (G := G),
      integral_nonneg (fun x => (hr x).1), ?_⟩
    change (∫ x, f x ∂probabilityHaar (G := G)) = _
    simp_rw [(hr _).2]
    exact integral_ofReal
  · intro side f c
    constructor
    · intro hc
      have h := integralMean_hull side f (ContinuousMap.const G c) hc
      simpa only [integralMean_const] using h
    · rintro rfl
      exact integralMean_const_mem_hull side f
  · apply le_antisymm hnorm
    have h := M.le_opNorm (ContinuousMap.const G (1 : 𝕜))
    rw [hconst] at h
    simpa using h

/-- Evaluating finite convex combinations of operators gives exactly the
finite convex combinations of translates, with the same weights. -/
lemma finiteAverage_image (side : Side) (f : C(G, 𝕜)) :
    (fun P : C(G, 𝕜) →L[𝕜] C(G, 𝕜) => P f) '' {P | IsFiniteAverage side P} =
      convexHull ℝ (orbit side f) := by
  let ev := ((ContinuousLinearMap.apply 𝕜 C(G, 𝕜) f).restrictScalars ℝ).toLinearMap
  change ev '' convexHull ℝ (range (translateOperator side)) = _
  rw [ev.image_convexHull, ← range_comp]
  rfl

lemma finiteAverage_norm_le (side : Side) {P : C(G, 𝕜) →L[𝕜] C(G, 𝕜)}
    (hP : IsFiniteAverage side P) : ‖P‖ ≤ 1 := by
  have hc : Convex ℝ {P : C(G, 𝕜) →L[𝕜] C(G, 𝕜) | ‖P‖ ≤ 1} := by
    simpa only [Metric.closedBall, dist_zero_right] using
      (convex_closedBall (0 : C(G, 𝕜) →L[𝕜] C(G, 𝕜)) (1 : ℝ))
  apply convexHull_min ?_ hc hP
  rintro _ ⟨s, rfl⟩
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul]
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).2
  intro x
  cases side <;> exact f.norm_coe_le_norm _

lemma finiteAverage_const (side : Side) {P : C(G, 𝕜) →L[𝕜] C(G, 𝕜)}
    (hP : IsFiniteAverage side P) (c : 𝕜) :
    P (ContinuousMap.const G c) = ContinuousMap.const G c := by
  let ev := ((ContinuousLinearMap.apply 𝕜 C(G, 𝕜)
    (ContinuousMap.const G c)).restrictScalars ℝ).toLinearMap
  have hc : Convex ℝ {P : C(G, 𝕜) →L[𝕜] C(G, 𝕜) |
      P (ContinuousMap.const G c) = ContinuousMap.const G c} :=
    (convex_singleton (ContinuousMap.const G c)).linear_preimage ev
  apply convexHull_min ?_ hc hP
  rintro _ ⟨s, rfl⟩
  ext x
  rfl

lemma finiteAverage_preserves_mean (M : C(G, 𝕜) →L[𝕜] 𝕜)
    (hM : Spec.MeanProperties M) (side : Side)
    {P : C(G, 𝕜) →L[𝕜] C(G, 𝕜)} (hP : IsFiniteAverage side P) (f : C(G, 𝕜)) :
    M (P f) = M f := by
  apply hM.2.2.2.2.1 side f (P f)
  apply subset_closure
  rw [← finiteAverage_image side f]
  exact mem_image_of_mem (fun P : C(G, 𝕜) →L[𝕜] C(G, 𝕜) => P f) hP

lemma exists_finiteAverage_approx_of_mem (side : Side) (f : C(G, 𝕜)) (c : 𝕜)
    (hc : ContinuousMap.const G c ∈ translateHull side f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : C(G, 𝕜) →L[𝕜] C(G, 𝕜), IsFiniteAverage side P ∧
      ‖P f - ContinuousMap.const G c‖ < ε := by
  obtain ⟨h, hh, hd⟩ := Metric.mem_closure_iff.mp hc ε hε
  rw [← finiteAverage_image side f] at hh
  obtain ⟨P, hP, rfl⟩ := hh
  exact ⟨P, hP, by simpa only [dist_eq_norm, norm_sub_rev] using hd⟩

lemma exists_finiteAverage_approx (M : C(G, 𝕜) →L[𝕜] 𝕜)
    (hM : Spec.MeanProperties M) (side : Side) (f : C(G, 𝕜))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : C(G, 𝕜) →L[𝕜] C(G, 𝕜), IsFiniteAverage side P ∧
      ‖P f - ContinuousMap.const G (M f)‖ < ε :=
  exists_finiteAverage_approx_of_mem side f (M f)
    ((hM.2.2.2.1 side f (M f)).2 rfl) hε

lemma successive_averaging_of_hulls (m : C(G, 𝕜) → 𝕜)
    (hc : ∀ f, ContinuousMap.const G (m f) ∈ translateHull .left f)
    (hi : ∀ f h, h ∈ translateHull .left f → m h = m f)
    (f g : C(G, 𝕜)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P Q : C(G, 𝕜) →L[𝕜] C(G, 𝕜),
      IsFiniteAverage .left P ∧ IsFiniteAverage .left Q ∧
      ‖P f - ContinuousMap.const G (m f)‖ < ε ∧
      ‖Q (P f) - ContinuousMap.const G (m f)‖ < ε ∧
      ‖Q (P g) - ContinuousMap.const G (m g)‖ < ε ∧
      ‖Q (P (f + g)) - ContinuousMap.const G (m f + m g)‖ < 2 * ε := by
  obtain ⟨P, hP, hf⟩ := exists_finiteAverage_approx_of_mem .left f (m f) (hc f) hε
  obtain ⟨Q, hQ, hg⟩ := exists_finiteAverage_approx_of_mem .left (P g) (m (P g)) (hc (P g)) hε
  have hPg : P g ∈ translateHull .left g := by
    apply subset_closure
    rw [← finiteAverage_image .left g]
    exact mem_image_of_mem (fun R : C(G, 𝕜) →L[𝕜] C(G, 𝕜) => R g) hP
  rw [hi g (P g) hPg] at hg
  have hqf : ‖Q (P f) - ContinuousMap.const G (m f)‖ < ε := by
    calc
      ‖Q (P f) - ContinuousMap.const G (m f)‖ =
          ‖Q (P f - ContinuousMap.const G (m f))‖ := by
        rw [map_sub, finiteAverage_const .left hQ]
      _ ≤ ‖P f - ContinuousMap.const G (m f)‖ :=
        Q.le_of_opNorm_le (finiteAverage_norm_le .left hQ) _ |>.trans_eq (one_mul _)
      _ < ε := hf
  refine ⟨P, Q, hP, hQ, hf, hqf, hg, ?_⟩
  have heq : Q (P (f + g)) - ContinuousMap.const G (m f + m g) =
      (Q (P f) - ContinuousMap.const G (m f)) +
      (Q (P g) - ContinuousMap.const G (m g)) := by
    rw [map_add, map_add]
    change Q (P f) + Q (P g) -
      (ContinuousMap.const G (m f) + ContinuousMap.const G (m g)) = _
    abel
  rw [heq]
  exact (norm_add_le _ _).trans_lt (by linarith)

theorem successive_averaging : Spec.SuccessiveAveraging.{u,v} := by
  intro G _ _ _ _ _ 𝕜 _ M hM f g ε hε
  exact successive_averaging_of_hulls M
    (fun f => (hM.2.2.2.1 .left f (M f)).2 rfl) (hM.2.2.2.2.1 .left) f g hε

/-- Composition preserves finite averages; the order t*s here reflects the
source's convention Lₛf(x)=f(sx). -/
lemma finiteAverage_comp {P Q : C(G, 𝕜) →L[𝕜] C(G, 𝕜)}
    (hP : IsFiniteAverage .left P) (hQ : IsFiniteAverage .left Q) :
    IsFiniteAverage .left (Q.comp P) := by
  let T := translateOperator (G := G) (𝕜 := 𝕜) Side.left
  let A := convexHull ℝ (range T)
  have hc : Convex ℝ A := convex_convexHull ℝ _
  have hleft (s : G) : (T s).comp P ∈ A := by
    let F := ((ContinuousLinearMap.compL 𝕜 C(G, 𝕜) C(G, 𝕜) C(G, 𝕜)
      (T s)).restrictScalars ℝ).toLinearMap
    apply convexHull_min ?_ (hc.linear_preimage F) hP
    rintro _ ⟨t, rfl⟩
    apply subset_convexHull ℝ (range T)
    refine ⟨t * s, ?_⟩
    ext f x
    simp [T, F, translateOperator, mul_assoc]
  let F := (((ContinuousLinearMap.compL 𝕜 C(G, 𝕜) C(G, 𝕜) C(G, 𝕜)).flip
    P).restrictScalars ℝ).toLinearMap
  exact convexHull_min (by rintro _ ⟨s, rfl⟩; exact hleft s)
    (hc.linear_preimage F) hQ

theorem additivity_of_hull_averaging : Spec.AdditivityOfHullAveraging.{u,v} := by
  intro G _ _ _ _ _ 𝕜 _ m hc hi f g
  apply Eq.symm
  apply (hc (f + g) (m f + m g)).1
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨P, Q, hP, hQ, _, _, _, hsum⟩ := successive_averaging_of_hulls m
    (fun f => (hc f (m f)).2 rfl) hi f g (half_pos hε)
  refine ⟨Q (P (f + g)), ?_, ?_⟩
  · rw [← finiteAverage_image .left (f + g)]
    exact ⟨Q.comp P, finiteAverage_comp hP hQ, rfl⟩
  · simpa only [dist_eq_norm, norm_sub_rev, mul_div_cancel₀ _ (by norm_num : (2:ℝ) ≠ 0)]
      using hsum

end ExpandedFA.PartV.HaarAveraging
