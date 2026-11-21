import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.EmbeddingsCompactness
import MathGenome.Internal.FourierSobolev.P102.Fractional.Space
import MathGenome.Internal.FourierSobolev.P102.U2.Young
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

import MathGenome.Internal.FourierSobolev.P102.Fractional.Extension
import MathGenome.Internal.FourierSobolev.P102.Fractional.Morrey
import MathGenome.Internal.FourierSobolev.P102.Fractional.Subcritical
noncomputable section
open MeasureTheory MeasureTheory.Measure Filter BoundedContinuousFunction Set Metric
open scoped ENNReal NNReal Topology

namespace P102.Fractional.Embedding
universe u

/-- Conditional extraction of the source's fixed-support extension clause. -/
theorem extension_clause_conditional
    (hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (_hClosure : Specs.P102.Fractional.Morrey.onClosure.{u})
    (_hMorrey : Specs.P102.Fractional.Morrey.wholeSpace.{u})
    (_hDomain : Specs.P102.Fractional.Subcritical.boundedDomain.{u})
    (_hWhole : Specs.P102.Fractional.Subcritical.wholeSpace.{u}) :
    Specs.P102.Fractional.EmbeddingsCompactness.extensionClause.{u} := hExtension

/-- Both original subcritical quantitative estimates, without altered scope. -/
theorem subcritical_estimates_conditional
    (_hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (_hClosure : Specs.P102.Fractional.Morrey.onClosure.{u})
    (_hMorrey : Specs.P102.Fractional.Morrey.wholeSpace.{u})
    (hDomain : Specs.P102.Fractional.Subcritical.boundedDomain.{u})
    (hWhole : Specs.P102.Fractional.Subcritical.wholeSpace.{u}) :
    Specs.P102.Fractional.EmbeddingsCompactness.subcriticalEstimates.{u} := ⟨hWhole, hDomain⟩

/-- The endpoint domain Hölder norm estimate and unique representative. -/
theorem supercritical_embedding_conditional
    (_hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (hClosure : Specs.P102.Fractional.Morrey.onClosure.{u})
    (_hMorrey : Specs.P102.Fractional.Morrey.wholeSpace.{u})
    (_hDomain : Specs.P102.Fractional.Subcritical.boundedDomain.{u})
    (_hWhole : Specs.P102.Fractional.Subcritical.wholeSpace.{u}) :
    Specs.P102.Fractional.EmbeddingsCompactness.supercriticalEmbedding.{u} := hClosure

/-- The geometry condition transports boundedness through the fixed isometry. -/
theorem bounded_of_lipschitz {n : ℕ} {G : Set (Domain (n + 1))}
    (hG : IsBoundedLipschitzOpen G) : Bornology.IsBounded G := by
  have h := (geometryCoordinates n).isometry.lipschitzWith.isBounded_image hG.2.1
  rwa [Set.image_preimage_eq G (geometryCoordinates n).surjective] at h

/-- Real-distance form of the Hölder condition. -/
theorem holderWith_of_dist_le {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {H α : ℝ≥0} {f : X → Y}
    (h : ∀ x y, dist (f x) (f y) ≤ (H : ℝ) * dist x y ^ (α : ℝ)) :
    HolderWith H α f := by
  intro x y
  rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg,
    ← ENNReal.coe_mul, ENNReal.coe_le_coe]
  exact_mod_cast h x y

/-- Uniform limits retain a common Hölder constant. -/
theorem holderWith_of_tendsto {X 𝕜 : Type*} [MetricSpace X] [RCLike 𝕜]
    {H α : ℝ≥0} {f : ℕ → X →ᵇ 𝕜} {g : X →ᵇ 𝕜}
    (hf : ∀ j, HolderWith H α (f j : X → 𝕜)) (hg : Tendsto f atTop (𝓝 g)) :
    HolderWith H α (g : X → 𝕜) := by
  apply holderWith_of_dist_le
  intro x y
  apply le_of_tendsto
    (((continuous_eval_const x).tendsto g |>.comp hg).dist
      ((continuous_eval_const y).tendsto g |>.comp hg))
  exact Eventually.of_forall fun j => (hf j).dist_le x y

/-- A uniform limit with uniformly controlled α-Hölder constants converges
in each strictly smaller Hölder exponent. -/
theorem holderConverges_of_tendsto {X 𝕜 : Type*} [MetricSpace X] [RCLike 𝕜]
    {H α β : ℝ≥0} (hα : 0 < α) (hβ : β < α)
    {f : ℕ → X →ᵇ 𝕜} {g : X →ᵇ 𝕜}
    (hf : ∀ j, HolderWith H α (f j : X → 𝕜)) (hg : Tendsto f atTop (𝓝 g)) :
    HolderConverges β f g := by
  have hlim := holderWith_of_tendsto hf hg
  have hsub (j : ℕ) : HolderWith (H + H) α (fun x => f j x - g x) := by
    apply holderWith_of_dist_le
    intro x y
    calc
      dist (f j x - g x) (f j y - g y) ≤ dist (f j x) (f j y) + dist (g x) (g y) :=
        dist_sub_sub_le _ _ _ _
      _ ≤ H * dist x y ^ (α : ℝ) + H * dist x y ^ (α : ℝ) :=
        add_le_add ((hf j).dist_le x y) (hlim.dist_le x y)
      _ = _ := by push_cast; ring
  let θ : ℝ≥0 := β / α
  have hθ : θ < 1 := (div_lt_one hα).mpr hβ
  have hsum : (1 - θ) + θ = 1 := tsub_add_cancel_of_le hθ.le
  have hexp : (0 : ℝ≥0) * (1 - θ) + α * θ = β := by
    dsimp [θ]
    simp only [zero_mul, zero_add]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ (ne_of_gt hα)]
  have hzero (j : ℕ) : HolderWith (2 * ‖f j - g‖₊) 0 (fun x => f j x - g x) := by
    apply holderWith_of_dist_le
    intro x y
    have hx := (f j - g).norm_coe_le_norm x
    have hy := (f j - g).norm_coe_le_norm y
    have ht := norm_sub_le (f j x - g x) (f j y - g y)
    rw [dist_eq_norm]
    simp only [NNReal.coe_mul, NNReal.coe_ofNat, coe_nnnorm, NNReal.coe_zero,
      Real.rpow_zero, mul_one]
    change ‖f j x - g x‖ ≤ ‖f j - g‖ at hx
    change ‖f j y - g y‖ ≤ ‖f j - g‖ at hy
    linarith
  have hnorm : Tendsto (fun j => (2 : ℝ≥0) * ‖f j - g‖₊) atTop (𝓝 0) := by
    have hh : Tendsto (fun j => f j - g) atTop (𝓝 (0 : X →ᵇ 𝕜)) := by
      simpa using hg.sub (tendsto_const_nhds (x := g))
    simpa using (tendsto_const_nhds (x := (2 : ℝ≥0))).mul hh.nnnorm
  have hp : 0 < ((1 - θ : ℝ≥0) : ℝ) := by exact_mod_cast tsub_pos_of_lt hθ
  have hc : Tendsto (fun j => (2 * ‖f j - g‖₊) ^ ((1 - θ : ℝ≥0) : ℝ) *
      (H + H) ^ (θ : ℝ)) atTop (𝓝 0) := by
    simpa [NNReal.zero_rpow (ne_of_gt hp)] using
      (hnorm.nnrpow tendsto_const_nhds (Or.inr hp)).mul_const ((H + H) ^ (θ : ℝ))
  refine ⟨hg, Or.inr (fun ε hε => ?_)⟩
  filter_upwards [hc.eventually (gt_mem_nhds hε)] with j hj
  have hi := (hzero j).interpolate (hsub j) hsum
  rw [hexp] at hi
  exact hi.mono hj.le

/-- Arzelà–Ascoli for a sequence with a common Hölder and supremum bound. -/
theorem holder_subsequence {X 𝕜 : Type*} [MetricSpace X] [CompactSpace X] [RCLike 𝕜]
    {H α β : ℝ≥0} (hα : 0 < α) (hβ : β < α)
    (f : ℕ → X →ᵇ 𝕜) (hf : ∀ j, HolderWith H α (f j : X → 𝕜))
    (M : ℝ) (hM : ∀ j, ‖f j‖ ≤ M) :
    ∃ g : X →ᵇ 𝕜, MemHolder β (g : X → 𝕜) ∧
      ∃ σ : ℕ → ℕ, StrictMono σ ∧ HolderConverges β (fun j => f (σ j)) g := by
  have hequi : Equicontinuous ((↑) : Set.range f → X → 𝕜) := by
    intro x
    let b : X → ℝ := fun y => H * dist x y ^ (α : ℝ)
    have hb : Continuous b := continuous_const.mul
      ((continuous_const.dist continuous_id).rpow_const (fun _ => Or.inr α.coe_nonneg))
    have hb0 : Tendsto b (𝓝 x) (𝓝 0) := by
      simpa [b, ne_of_gt (show (0 : ℝ) < α by exact_mod_cast hα)] using hb.tendsto x
    apply Metric.equicontinuousAt_of_continuity_modulus b hb0
    apply Eventually.of_forall
    rintro y ⟨_, j, rfl⟩
    exact (hf j).dist_le x y
  have hrange : ∀ (g : X →ᵇ 𝕜) (x : X), g ∈ Set.range f →
      g x ∈ Metric.closedBall (0 : 𝕜) M := by
    rintro _ x ⟨j, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      ((f j).norm_coe_le_norm x).trans (hM j)
  have hc := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : 𝕜) M) (isCompact_closedBall _ _) (Set.range f) hrange hequi
  obtain ⟨g, _, σ, hσ, hg⟩ := hc.tendsto_subseq
    (fun j => subset_closure (Set.mem_range_self j))
  have hhold := holderWith_of_tendsto (fun j => hf (σ j)) hg
  have hmem : MemHolder β (g : X → 𝕜) := hhold.memHolder.of_le hβ.le
  exact ⟨g, hmem, σ, hσ, holderConverges_of_tendsto hα hβ (fun j => hf (σ j)) hg⟩

/-- Compactness in every strict Hölder exponent, derived from the exact
ordered conditional premises. No compactness certificate is assumed. -/
theorem supercritical_compactness_conditional
    (_hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (hClosure : Specs.P102.Fractional.Morrey.onClosure.{u})
    (_hMorrey : Specs.P102.Fractional.Morrey.wholeSpace.{u})
    (_hDomain : Specs.P102.Fractional.Subcritical.boundedDomain.{u})
    (_hWhole : Specs.P102.Fractional.Subcritical.wholeSpace.{u}) :
    Specs.P102.Fractional.EmbeddingsCompactness.supercriticalCompactness.{u} := by
  intro n G hG s hs0 hs1 p _ hp hsp 𝕜 _
  let : CompactSpace (closure G) := isCompact_iff_compactSpace.mp (bounded_of_lipschitz hG).isCompact_closure
  obtain ⟨C, _hC, h⟩ := hClosure n G hG s hs0 hs1 p hp hsp 𝕜
  choose F hF using fun u => (h u).exists
  choose H hHN hHH using fun u => (hF u).2
  refine ⟨F, fun u => (hF u).1, ?_⟩
  intro β hβ v hv
  obtain ⟨M, hM⟩ := hv
  have hM0 : 0 ≤ M := (norm_nonneg (v 0)).trans (hM 0)
  let B : ℝ≥0 := ⟨(C : ℝ) * M, mul_nonneg C.coe_nonneg hM0⟩
  have hnorm (j : ℕ) : ‖F (v j)‖ ≤ (B : ℝ) := by
    calc
      ‖F (v j)‖ ≤ (C : ℝ) * Morrey.fullNorm (v j) :=
        (le_add_of_nonneg_right (H (v j)).coe_nonneg).trans (hHN (v j))
      _ = (C : ℝ) * ‖v j‖ := by rw [Morrey.fullNorm, ← space_norm hp]
      _ ≤ (B : ℝ) := mul_le_mul_of_nonneg_left (hM j) C.coe_nonneg
  have hH (j : ℕ) : (H (v j) : ℝ) ≤ (B : ℝ) := by
    calc
      (H (v j) : ℝ) ≤ ‖F (v j)‖ + (H (v j) : ℝ) := le_add_of_nonneg_left (norm_nonneg _)
      _ ≤ (C : ℝ) * Morrey.fullNorm (v j) := hHN (v j)
      _ = (C : ℝ) * ‖v j‖ := by rw [Morrey.fullNorm, ← space_norm hp]
      _ ≤ (B : ℝ) := mul_le_mul_of_nonneg_left (hM j) C.coe_nonneg
  have hp0 : 0 < p.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ p))) hp
  have ha : 0 < Morrey.exponent (n + 1) s p := by
    dsimp [Morrey.exponent]
    exact sub_pos.mpr ((div_lt_iff₀ hp0).mpr (by simpa only [mul_comm] using hsp))
  let α : ℝ≥0 := ⟨Morrey.exponent (n + 1) s p, ha.le⟩
  have hhold (j : ℕ) : HolderWith B α (F (v j) : closure G → 𝕜) := by
    apply holderWith_of_dist_le
    intro x y
    rw [dist_eq_norm]
    exact (hHH (v j) x y).trans
      (mul_le_mul_of_nonneg_right (hH j) (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist x.val y.val) _))
  exact holder_subsequence (show 0 < α from ha) (show β < α from hβ)
    (fun j => F (v j)) hhold (B : ℝ) hnorm

/-- Comparison of the Gagliardo kernels on a set of bounded diameter. -/
theorem kernel_lower_le {d : ℕ} {t s : ℝ} {p : ℝ≥0∞}
    (hts : t ≤ s) {R : ℝ} {z : Domain d × Domain d} (hz : ‖z.1 - z.2‖ ≤ R) :
    kernel d t p z ≤ ENNReal.ofReal R ^ ((s - t) * p.toReal) * kernel d s p z := by
  by_cases heq : z.1 = z.2
  · simp [kernel, heq]
  have hn : 0 < ‖z.1 - z.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
  have hn0 : ENNReal.ofReal ‖z.1 - z.2‖ ≠ 0 := (ENNReal.ofReal_pos.mpr hn).ne'
  have hnT : ENNReal.ofReal ‖z.1 - z.2‖ ≠ ∞ := ENNReal.ofReal_ne_top
  have hexp : -((d : ℝ) + t * p.toReal) =
      (s - t) * p.toReal + -((d : ℝ) + s * p.toReal) := by ring
  simp only [kernel, ite_eq_right heq]
  rw [← ENNReal.rpow_neg, hexp, ENNReal.rpow_add _ _ hn0 hnT, ENNReal.rpow_neg]
  exact mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hz)
    (mul_nonneg (sub_nonneg.mpr hts) ENNReal.toReal_nonneg)) le_rfl

/-- A bounded set admits a finite scalar comparison of its pair measures. -/
theorem pairMeasure_lower_le {d : ℕ} {G : Set (Domain d)}
    (hG : Bornology.IsBounded G) {t s : ℝ} (hts : t ≤ s) (p : ℝ≥0∞) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ pairMeasure G t p ≤ c • pairMeasure G s p := by
  obtain ⟨R, hR, hb⟩ := hG.closure.exists_pos_norm_le
  let c : ℝ≥0∞ := ENNReal.ofReal (2 * R) ^ ((s - t) * p.toReal)
  refine ⟨c, ENNReal.rpow_ne_top_of_nonneg
    (mul_nonneg (sub_nonneg.mpr hts) ENNReal.toReal_nonneg) ENNReal.ofReal_ne_top, ?_⟩
  have hx : ∀ᵐ x ∂domainMeasure G, x ∈ closure G :=
    ae_restrict_of_ae_restrict_of_subset subset_closure
      (ae_restrict_mem isClosed_closure.measurableSet)
  have hk : kernel d t p ≤ᵐ[(domainMeasure G).prod (domainMeasure G)] c • kernel d s p := by
    filter_upwards [quasiMeasurePreserving_fst.ae hx, quasiMeasurePreserving_snd.ae hx]
      with z hz1 hz2
    apply kernel_lower_le hts
    exact (norm_sub_le _ _).trans (by linarith [hb z.1 hz1, hb z.2 hz2])
  exact (withDensity_mono hk).trans_eq (withDensity_smul c kernel_measurable)

/-- Lower-smoothness seminorm comparison from the weighted-measure bound. -/
theorem seminorm_lower_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s t : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {c : ℝ≥0∞} (_hc : c ≠ ∞) (hmeasure : pairMeasure G t p ≤ c • pairMeasure G s p)
    (u : Space 𝕜 G s p) :
    seminorm G t p (firstProjection u) ≤ c ^ (1 / p).toReal * seminorm G s p (firstProjection u) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have he := eLpNorm_le_of_measure_le_smul (f := increment (firstProjection u)) (p := p) hmeasure
  change eLpNorm (increment (firstProjection u)) p (pairMeasure G t p) ≤
    c ^ (1 / p).toReal * eLpNorm (increment (firstProjection u)) p (pairMeasure G s p) at he
  rwa [eLpNorm_increment_eq_seminorm (s := t) hp0 hp (Lp.aestronglyMeasurable _),
    eLpNorm_increment_eq_seminorm (s := s) hp0 hp (Lp.aestronglyMeasurable _)] at he

/-- Existence in the target graph, using the proved graph characterization. -/
theorem exists_lower_element {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s t : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hmeasure : pairMeasure G t p ≤ c • pairMeasure G s p)
    (u : Space 𝕜 G s p) :
    ∃ v : Space 𝕜 G t p, firstProjection v = firstProjection u := by
  apply (firstProjection_range_seminorm (s := t) hp (firstProjection u)).mpr
  have hs : seminorm G s p (firstProjection u) < ∞ :=
    (firstProjection_range_seminorm (s := s) hp (firstProjection u)).mp ⟨u, rfl⟩
  exact (seminorm_lower_le hp hc hmeasure u).trans_lt
    (ENNReal.mul_lt_top ((ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hc).lt_top) hs)

/-- Norm comparison for the unique graph element with the same first projection. -/
theorem norm_lower_element {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s t : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {c : ℝ≥0∞} (hc : c ≠ ∞) (hmeasure : pairMeasure G t p ≤ c • pairMeasure G s p)
    (u : Space 𝕜 G s p) (v : Space 𝕜 G t p) (hv : firstProjection v = firstProjection u) :
    ‖v‖ ≤ (1 + (c ^ (1 / p).toReal).toReal) * ‖u‖ := by
  let D := c ^ (1 / p).toReal
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg hc
  have hs : seminorm G s p (firstProjection u) < ∞ :=
    (firstProjection_range_seminorm (s := s) hp (firstProjection u)).mp ⟨u, rfl⟩
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hD hs.ne) (seminorm_lower_le hp hc hmeasure u)
  rw [ENNReal.toReal_mul] at hr
  rw [space_norm hp v, hv, space_norm hp u]
  have hn1 := norm_nonneg (firstProjection u)
  have hn2 := ENNReal.toReal_nonneg (a := seminorm G s p (firstProjection u))
  have hnD := ENNReal.toReal_nonneg (a := D)
  change ‖firstProjection u‖ + (seminorm G t p (firstProjection u)).toReal ≤
    (1 + D.toReal) * (‖firstProjection u‖ + (seminorm G s p (firstProjection u)).toReal)
  calc
    _ ≤ ‖firstProjection u‖ + D.toReal * (seminorm G s p (firstProjection u)).toReal := add_le_add le_rfl hr
    _ ≤ _ := by nlinarith [mul_nonneg hnD hn1]

theorem lower_smoothness_conditional
    (_hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (_hClosure : Specs.P102.Fractional.Morrey.onClosure.{u})
    (_hMorrey : Specs.P102.Fractional.Morrey.wholeSpace.{u})
    (_hDomain : Specs.P102.Fractional.Subcritical.boundedDomain.{u})
    (_hWhole : Specs.P102.Fractional.Subcritical.wholeSpace.{u}) :
    Specs.P102.Fractional.EmbeddingsCompactness.lowerSmoothness.{u} := by
  classical
  intro d G hG t s _ht hts _hs p _ hp 𝕜 _
  obtain ⟨c, hc, hmeasure⟩ := pairMeasure_lower_le hG hts.le p
  choose F hF using exists_lower_element (𝕜 := 𝕜) hp hc hmeasure
  let L : Space 𝕜 G s p →ₗ[𝕜] Space 𝕜 G t p :=
    { toFun := F
      map_add' := by
        intro u v
        apply firstProjection_injective (s := t)
        rw [map_add, hF, hF, hF, map_add]
      map_smul' := by
        intro a u
        apply firstProjection_injective (s := t)
        rw [map_smul, hF, hF, map_smul]
        rfl }
  let B : ℝ≥0 := ⟨1 + (c ^ (1 / p).toReal).toReal, by positivity⟩
  have hbound : ∀ u, ‖L u‖ ≤ (B : ℝ) * ‖u‖ := fun u => norm_lower_element hp hc hmeasure u (F u) (hF u)
  exact ⟨B, L.mkContinuous B hbound, hF, hbound⟩
/-- The extended full norm agrees with the canonical graph norm. -/
theorem fullNorm_eq_ofReal_norm {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : Space 𝕜 G s p) :
    eLpNorm (firstProjection u) p (domainMeasure G) + seminorm G s p (firstProjection u) =
      ENNReal.ofReal ‖u‖ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hsemi : seminorm G s p (firstProjection u) ≠ ∞ := by
    rw [← eLpNorm_increment_eq_seminorm hp0 hp (Lp.aestronglyMeasurable _)]
    exact ((Lp.memLp u.val.snd).ae_eq u.property).ne
  rw [space_norm hp, ENNReal.ofReal_add (norm_nonneg _) ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hsemi, Lp.norm_def, ENNReal.ofReal_toReal (Lp.memLp _).ne]

/-- A quantitative Lq estimate of a.e. classes constructs the canonical
bounded linear inclusion, preserving scalar linearity over both fields. -/
theorem lpInclusion_of_bound {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (H : ∀ u : Space 𝕜 G s p, MemLp (firstProjection u) q (domainMeasure G) ∧
      eLpNorm (firstProjection u) q (domainMeasure G) ≤ C * ENNReal.ofReal ‖u‖) :
    ∃ J : Space 𝕜 G s p →L[𝕜] Lp 𝕜 q (domainMeasure G),
      ∀ u, (J u : Domain d → 𝕜) =ᵐ[domainMeasure G] firstProjection u := by
  let F (u : Space 𝕜 G s p) : Lp 𝕜 q (domainMeasure G) := (H u).1.toLp _
  have hF (u) : (F u : Domain d → 𝕜) =ᵐ[domainMeasure G] firstProjection u := MemLp.coeFn_toLp _
  let L : Space 𝕜 G s p →ₗ[𝕜] Lp 𝕜 q (domainMeasure G) :=
    { toFun := F
      map_add' := by
        intro u v
        apply Lp.ext
        have hs := Lp.coeFn_add (firstProjection u) (firstProjection v)
        rw [← map_add] at hs
        filter_upwards [hF (u + v), hF u, hF v, Lp.coeFn_add (F u) (F v), hs]
          with x huv hu hv hadd hsrc
        change F (u + v) x = (F u + F v) x
        rw [huv, hadd, hsrc]
        simp only [Pi.add_apply, hu, hv]
      map_smul' := by
        intro a u
        apply Lp.ext
        have hs := Lp.coeFn_smul a (firstProjection u)
        rw [← map_smul] at hs
        filter_upwards [hF (a • u), hF u, Lp.coeFn_smul a (F u), hs]
          with x hau hu hsm hsrc
        change F (a • u) x = (a • F u) x
        rw [hau, hsm, hsrc]
        simp only [Pi.smul_apply, hu] }
  refine ⟨L.mkContinuous C.toReal (fun u => ?_), hF⟩
  change ‖(H u).1.toLp _‖ ≤ _
  rw [Lp.norm_toLp]
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) (H u).2
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg u)] at hh
/-- Each finite critical target lies strictly below a lower-smoothness
subcritical Sobolev exponent. -/
theorem exists_lower_sobolevExponent {d : ℕ} (hd : 0 < d) {s : ℝ} (hs : 0 < s)
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ∞) (hq : q ≠ ∞)
    (hsp : s * p.toReal = (d : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ t < s ∧ t * p.toReal < (d : ℝ) ∧ q < sobolevExponent d t p := by
  have hp1 : (1 : ℝ) ≤ p.toReal := by exact_mod_cast ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hq1 : (1 : ℝ) ≤ q.toReal := by exact_mod_cast ENNReal.toReal_mono hq (Fact.out : 1 ≤ q)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  let a : ℝ := 1 / (2 * q.toReal)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by dsimp [a]; apply (div_lt_one (by positivity)).mpr; linarith
  have hqa : q.toReal * a = 1 / 2 := by dsimp [a]; field_simp
  let t : ℝ := s * (1 - a)
  have ht0 : 0 < t := mul_pos hs (sub_pos.mpr ha1)
  have hts : t < s := by dsimp [t]; nlinarith
  have hden : (d : ℝ) - t * p.toReal = (d : ℝ) * a := by dsimp [t]; nlinarith [hsp]
  have hden0 : 0 < (d : ℝ) - t * p.toReal := by rw [hden]; positivity
  have hexp0 : 0 < (d : ℝ) * p.toReal / ((d : ℝ) - t * p.toReal) := by positivity
  refine ⟨t, ht0, hts, by linarith, ?_⟩
  rw [sobolevExponent, ← ENNReal.ofReal_toReal hq, ENNReal.ofReal_lt_ofReal_iff hexp0]
  apply (lt_div_iff₀ hden0).mpr
  rw [hden]
  have hhalf : q.toReal * ((d : ℝ) * a) = (d : ℝ) / 2 := by nlinarith [hqa]
  rw [hhalf]
  nlinarith
/-- Reduction of critical compactness to strict subcritical compactness,
using a genuine bounded lower-smoothness map. -/
theorem critical_of_subcritical
    (hlower : Specs.P102.Fractional.EmbeddingsCompactness.lowerSmoothness.{u})
    (hsub : Specs.P102.Fractional.EmbeddingsCompactness.subcriticalCompactness.{u}) :
    Specs.P102.Fractional.EmbeddingsCompactness.criticalInclusions.{u} := by
  intro n G hG s hs0 hs1 p _ hp hsp q _ hq 𝕜 _
  obtain ⟨t, ht0, hts, htp, hqt⟩ := exists_lower_sobolevExponent (Nat.succ_pos n) hs0 hp hq hsp
  obtain ⟨_, J, hJ, _⟩ := hlower (n + 1) G (bounded_of_lipschitz hG)
    t s ht0 hts hs1 p hp 𝕜
  obtain ⟨I, hI, hcompact⟩ := hsub n G hG t ht0 (hts.trans hs1) p hp htp q hq hqt 𝕜
  refine ⟨I.comp J, fun u => ?_, fun A hA => ?_⟩
  · change (I (J u) : Domain (n + 1) → 𝕜) =ᵐ[domainMeasure G] firstProjection u
    exact (hI (J u)).trans (by rw [hJ u])
  · have hc := hcompact (J '' A) (J.lipschitzWith.isBounded_image hA)
    simpa only [Set.image_image, ContinuousLinearMap.coe_comp, Function.comp_def] using hc

/-- Continuous inclusion at every finite exponent in the critical case.
The comparison and exponent selection are proved, rather than assumed. -/
theorem critical_embedding_conditional
    (hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (hClosure : Specs.P102.Fractional.Morrey.onClosure.{u})
    (hMorrey : Specs.P102.Fractional.Morrey.wholeSpace.{u})
    (hDomain : Specs.P102.Fractional.Subcritical.boundedDomain.{u})
    (hWhole : Specs.P102.Fractional.Subcritical.wholeSpace.{u}) :
    Specs.P102.Fractional.EmbeddingsCompactness.criticalEmbedding.{u} := by
  intro n G hG s hs0 hs1 p _ hp hsp q _ hq 𝕜 _
  have hGb := bounded_of_lipschitz hG
  let : IsFiniteMeasure (domainMeasure G) := ⟨by
    simpa only [domainMeasure, Measure.restrict_apply_univ] using hGb.measure_lt_top (μ := volume)⟩
  obtain ⟨t, ht0, hts, htp, hqt⟩ := exists_lower_sobolevExponent (Nat.succ_pos n) hs0 hp hq hsp
  obtain ⟨B, J, hJ, hJbound⟩ := lower_smoothness_conditional
    hExtension hClosure hMorrey hDomain hWhole (n + 1) G hGb t s ht0 hts hs1 p hp 𝕜
  obtain ⟨C, H⟩ := hDomain n G hG t ht0 (hts.trans hs1) p hp htp 𝕜
  let r := sobolevExponent (n + 1) t p
  have hr : r ≠ ∞ := ENNReal.ofReal_ne_top
  have hq1 : (1 : ℝ) ≤ q.toReal := by exact_mod_cast ENNReal.toReal_mono hq (Fact.out : 1 ≤ q)
  have hqr : q.toReal ≤ r.toReal := ENNReal.toReal_mono hr hqt.le
  let a : ℝ := 1 / q.toReal - 1 / r.toReal
  have ha : 0 ≤ a := sub_nonneg.mpr (one_div_le_one_div_of_le (by linarith : 0 < q.toReal) hqr)
  let D : ℝ≥0∞ := (domainMeasure G Set.univ) ^ a
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ha (measure_ne_top _ _)
  apply lpInclusion_of_bound (C := (C : ℝ≥0∞) * B * D)
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top) hD)
  intro u
  have hu := H (J u)
  have hur : eLpNorm (firstProjection (J u)) r (domainMeasure G) ≤
      (C : ℝ≥0∞) * ENNReal.ofReal ‖J u‖ := by
    simpa only [fullNorm_eq_ofReal_norm hp] using hu.2
  have hJn : ENNReal.ofReal ‖J u‖ ≤ (B : ℝ≥0∞) * ENNReal.ofReal ‖u‖ := by
    have hh := ENNReal.ofReal_le_ofReal (hJbound u)
    rwa [ENNReal.ofReal_mul B.coe_nonneg, ← ENNReal.coe_nnreal_eq] at hh
  rw [hJ u] at hu hur
  refine ⟨hu.1.mono_exponent hqt.le, ?_⟩
  calc
    _ ≤ eLpNorm (firstProjection u) r (domainMeasure G) * D :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqt.le hu.1.aestronglyMeasurable
    _ ≤ ((C : ℝ≥0∞) * ENNReal.ofReal ‖J u‖) * D := mul_le_mul' hur le_rfl
    _ ≤ ((C : ℝ≥0∞) * ((B : ℝ≥0∞) * ENNReal.ofReal ‖u‖)) * D := by gcongr
    _ = _ := by ac_rfl



/-- A common compact essential support gives a uniform L1 bound from Lp. -/
theorem integrable_bound_of_support {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (K : Set (Domain d)) (hK : IsCompact K)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ f : Domain d → E, MemLp f p volume →
      (∀ᵐ x ∂volume, x ∉ K → f x = 0) →
      Integrable f volume ∧ (∫ x, ‖f x‖) ≤ D * (eLpNorm f p volume).toReal := by
  classical
  let a : ℝ := 1 - 1 / p.toReal
  have hpR : (1 : ℝ) ≤ p.toReal := by
    exact_mod_cast ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have ha : 0 ≤ a := by
    dsimp [a]
    apply sub_nonneg.mpr
    simpa only [div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpR
  let c : ℝ≥0∞ := (volume K) ^ a
  have hc : c ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ha hK.measure_ne_top
  refine ⟨c.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro f hf hsupp
  have heq : K.indicator f =ᵐ[volume] f := by
    filter_upwards [hsupp] with x hx
    by_cases h : x ∈ K
    · simp [h]
    · simp [h, hx h]
  let : IsFiniteMeasure (volume.restrict K) := ⟨by
    simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top⟩
  have h1res : MemLp f 1 (volume.restrict K) := (hf.restrict K).mono_exponent (Fact.out : 1 ≤ p)
  have h1 : MemLp f 1 volume :=
    ((memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet).mpr h1res).ae_eq heq
  have hb : eLpNorm f 1 volume ≤ eLpNorm f p volume * c := by
    rw [← eLpNorm_congr_ae heq,
      eLpNorm_indicator_eq_eLpNorm_restrict hK.measurableSet.nullMeasurableSet]
    calc
      _ ≤ eLpNorm f p (volume.restrict K) * c := by
        simpa only [ENNReal.toReal_one, div_one, Measure.restrict_apply_univ] using
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (Fact.out : 1 ≤ p) (hf.restrict K).aestronglyMeasurable
      _ ≤ _ := mul_le_mul' (eLpNorm_mono_measure _ Measure.restrict_le_self) le_rfl
  refine ⟨memLp_one_iff_integrable.mp h1, ?_⟩
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.ne hc) hb
  rw [ENNReal.toReal_mul, mul_comm] at hreal
  simpa only [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    ← integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable] using hreal


/-- A bounded family in a strictly larger finite exponent is uniformly integrable. -/
theorem uniformIntegrable_of_eLpNorm_bound
    {α E ι : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} [IsFiniteMeasure μ]
    {f : ι → α → E} {q r C : ℝ≥0∞}
    (hq : 1 ≤ q) (hr : r ≠ ∞) (hqr : q < r)
    (hC : C ≠ ∞) (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hbound : ∀ i, eLpNorm (f i) r μ ≤ C) :
    UniformIntegrable f q μ := by
  have hqT : q ≠ ∞ := (hqr.trans_le le_top).ne
  have hq0 : q ≠ 0 := (zero_lt_one.trans_le hq).ne'
  have hr0 : r ≠ 0 := (zero_lt_one.trans_le (hq.trans hqr.le)).ne'
  have hqR : 0 < q.toReal := ENNReal.toReal_pos hq0 hqT
  have hrR : q.toReal < r.toReal := ENNReal.toReal_lt_toReal hqT hr |>.mpr hqr
  let a : ℝ := 1 / q.toReal - 1 / r.toReal
  have ha : 0 < a := by
    dsimp [a]
    exact sub_pos.mpr (one_div_lt_one_div_of_lt hqR hrR)
  have hrestrict (i : ι) (S : Set α) :
      eLpNorm (f i) q (μ.restrict S) ≤ C * (μ S) ^ a := by
    calc
      _ ≤ eLpNorm (f i) r (μ.restrict S) * (μ.restrict S Set.univ) ^ a :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqr.le (hf i).restrict
      _ ≤ C * (μ S) ^ a := by
        rw [Measure.restrict_apply_univ]
        exact mul_le_mul' ((eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hbound i)) le_rfl
  refine ⟨unifIntegrable_iff.mpr ?_, ?_⟩
  · intro ε hε
    have ht := ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC ha
    obtain ⟨δ, hδ, hδε⟩ :=
      ENNReal.nhds_zero_basis_Iic.eventually_iff.mp (ENNReal.tendsto_nhds_zero.mp ht ε hε)
    refine ⟨δ, hδ, fun i S hS => ?_⟩
    exact (hrestrict i S).trans (hδε hS)
  · let D := C * (μ Set.univ) ^ a
    have hD : D ≠ ∞ := ENNReal.mul_ne_top hC
      (ENNReal.rpow_ne_top_of_nonneg ha.le (measure_ne_top _ _))
    refine ⟨D.toNNReal, fun i => ?_⟩
    rw [ENNReal.coe_toNNReal hD]
    simpa only [Measure.restrict_univ] using hrestrict i Set.univ


/-- Relative sequential compactness is enough for compact closure in a metric space. -/
theorem isCompact_closure_of_subsequence {X : Type*} [MetricSpace X] {A : Set X}
    (h : ∀ v : ℕ → X, (∀ j, v j ∈ A) →
      ∃ g : X, ∃ σ : ℕ → ℕ, StrictMono σ ∧ Tendsto (v ∘ σ) atTop (𝓝 g)) :
    IsCompact (closure A) := by
  classical
  apply IsSeqCompact.isCompact
  intro v hv
  have happ (j : ℕ) : ∃ x ∈ A, dist (v j) x < 1 / ((j : ℝ) + 1) :=
    Metric.mem_closure_iff.mp (hv j) _ (by positivity)
  choose w hw hdist using happ
  obtain ⟨g, σ, hσ, hg⟩ := h w hw
  have he : Tendsto (fun j => dist (v j) (w j)) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => (hdist j).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hvσ : Tendsto (v ∘ σ) atTop (𝓝 g) :=
    (tendsto_iff_of_dist (he.comp hσ.tendsto_atTop)).mpr hg
  exact ⟨g, isClosed_closure.mem_of_tendsto hg (Eventually.of_forall fun j => subset_closure (hw (σ j))),
    σ, hσ, hvσ⟩

/-- Compactness of the underlying Lp classes and uniform integrability in q
imply compactness of the canonical Lq inclusion. -/
theorem compactLpInclusion_of_uniformIntegrable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s : ℝ} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [IsFiniteMeasure (domainMeasure G)] (hq : q ≠ ∞)
    (J : Space 𝕜 G s p →L[𝕜] Lp 𝕜 q (domainMeasure G))
    (hJ : ∀ u, (J u : Domain d → 𝕜) =ᵐ[domainMeasure G] firstProjection u)
    (hcompact : ∀ A : Set (Space 𝕜 G s p), Bornology.IsBounded A →
      IsCompact (closure (firstProjection '' A)))
    (hui : ∀ (v : ℕ → Space 𝕜 G s p), (∃ M : ℝ, ∀ j, ‖v j‖ ≤ M) →
      UniformIntegrable (fun j => (firstProjection (v j) : Domain d → 𝕜)) q (domainMeasure G)) :
    CompactLpInclusion 𝕜 G s p q := by
  refine ⟨J, hJ, ?_⟩
  intro A hA
  apply isCompact_closure_of_subsequence
  intro w hw
  choose v hv heq using hw
  obtain ⟨M, hM⟩ := hA.exists_norm_le
  obtain ⟨g, _, σ, hσ, hg⟩ := (hcompact A hA).tendsto_subseq
    (fun j => subset_closure (Set.mem_image_of_mem firstProjection (hv j)))
  have huiσ := hui (v ∘ σ) ⟨M, fun j => hM (v (σ j)) (hv (σ j))⟩
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hg
  have hgm := huiσ.memLp_of_tendstoInMeasure hmeasure
  have hconv := tendsto_Lp_finite_of_tendstoInMeasure (Fact.out : 1 ≤ q) hq
    (fun j => Lp.aestronglyMeasurable (firstProjection (v (σ j)))) hgm huiσ.1 hmeasure
  have hconv' : Tendsto (fun j => eLpNorm
      ((J (v (σ j)) : Domain d → 𝕜) - (g : Domain d → 𝕜)) q (domainMeasure G)) atTop (𝓝 0) := by
    apply hconv.congr
    intro j
    exact (eLpNorm_congr_ae ((hJ (v (σ j))).sub EventuallyEq.rfl)).symm
  refine ⟨hgm.toLp g, σ, hσ, ?_⟩
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ g hgm).mpr hconv'
  change Tendsto (fun j => w (σ j)) atTop (𝓝 (hgm.toLp g))
  simpa only [heq] using ht

/-- A quantitative bound at a larger exponent yields a bounded canonical
inclusion and uniform integrability of every bounded sequence. -/
theorem compactLpInclusion_of_larger_bound {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {s : ℝ} {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [IsFiniteMeasure (domainMeasure G)] (hr : r ≠ ∞) (hqr : q < r)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (H : ∀ u : Space 𝕜 G s p, MemLp (firstProjection u) r (domainMeasure G) ∧
      eLpNorm (firstProjection u) r (domainMeasure G) ≤ C * ENNReal.ofReal ‖u‖)
    (hcompact : ∀ A : Set (Space 𝕜 G s p), Bornology.IsBounded A →
      IsCompact (closure (firstProjection '' A))) :
    CompactLpInclusion 𝕜 G s p q := by
  have hq : q ≠ ∞ := (hqr.trans_le le_top).ne
  have hq0 : 0 < q.toReal := ENNReal.toReal_pos
    (ne_of_gt (zero_lt_one.trans_le (Fact.out : 1 ≤ q))) hq
  have hqrR : q.toReal ≤ r.toReal := ENNReal.toReal_mono hr hqr.le
  let a : ℝ := 1 / q.toReal - 1 / r.toReal
  have ha : 0 ≤ a := sub_nonneg.mpr (one_div_le_one_div_of_le hq0 hqrR)
  let D : ℝ≥0∞ := (domainMeasure G Set.univ) ^ a
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ha (measure_ne_top _ _)
  obtain ⟨J, hJ⟩ := lpInclusion_of_bound (C := C * D) (ENNReal.mul_ne_top hC hD) (fun u => by
    refine ⟨(H u).1.mono_exponent hqr.le, ?_⟩
    calc
      _ ≤ eLpNorm (firstProjection u) r (domainMeasure G) * D :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hqr.le (H u).1.aestronglyMeasurable
      _ ≤ (C * ENNReal.ofReal ‖u‖) * D := mul_le_mul' (H u).2 le_rfl
      _ = _ := by ac_rfl)
  apply compactLpInclusion_of_uniformIntegrable hq J hJ hcompact
  intro v hv
  obtain ⟨M, hM⟩ := hv
  apply uniformIntegrable_of_eLpNorm_bound (Fact.out : 1 ≤ q) hr hqr
    (C := C * ENNReal.ofReal M) (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top)
    (fun j => (H (v j)).1.aestronglyMeasurable)
  intro j
  exact (H (v j)).2.trans (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hM j)))

/-- Endpoint control and precompactness of underlying Lp classes cover
all strictly subcritical target exponents by Vitali's theorem. -/
theorem subcriticalCompactness_of_projection_compact
    (hDomain : Specs.P102.Fractional.Subcritical.boundedDomain.{u})
    (hbase : ∀ (n : ℕ) (G : Set (Domain (n + 1))), IsBoundedLipschitzOpen G →
      ∀ s : ℝ, 0 < s → s < 1 → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
      ∀ (𝕜 : Type u) [RCLike 𝕜],
      ∀ A : Set (Space 𝕜 G s p), Bornology.IsBounded A →
        IsCompact (closure (firstProjection '' A))) :
    Specs.P102.Fractional.EmbeddingsCompactness.subcriticalCompactness.{u} := by
  intro n G hG s hs0 hs1 p _ hp hsp q _ _hq hqr 𝕜 _
  let : IsFiniteMeasure (domainMeasure G) := ⟨by
    simpa only [domainMeasure, Measure.restrict_apply_univ] using
      (bounded_of_lipschitz hG).measure_lt_top (μ := volume)⟩
  obtain ⟨C, H⟩ := hDomain n G hG s hs0 hs1 p hp hsp 𝕜
  apply compactLpInclusion_of_larger_bound (r := sobolevExponent (n + 1) s p)
    ENNReal.ofReal_ne_top hqr (C := C) ENNReal.coe_ne_top
    (fun u => ⟨(H u).1, by simpa only [fullNorm_eq_ofReal_norm hp] using (H u).2⟩)
    (hbase n G hG s hs0 hs1 p hp 𝕜)


/-- Uniform approximation by totally bounded families preserves total boundedness. -/
theorem totallyBounded_of_approximations {X : Type*} [PseudoMetricSpace X] {S : Set X}
    (h : ∀ ε : ℝ, 0 < ε → ∃ T : Set X, TotallyBounded T ∧
      ∀ x ∈ S, ∃ y ∈ T, dist x y < ε) : TotallyBounded S := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨T, hT, hST⟩ := h (ε / 2) (half_pos hε)
  obtain ⟨F, hF, hTF⟩ := Metric.totallyBounded_iff.mp hT (ε / 2) (half_pos hε)
  refine ⟨F, hF, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hST x hx
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (hTF hy)
  apply Set.mem_iUnion₂.mpr
  refine ⟨z, hz, ?_⟩
  change dist x z < ε
  exact (dist_triangle x y z).trans_lt (by linarith [show dist y z < ε / 2 from hyz])

/-- Total boundedness transfers along a uniformly Lipschitz comparison of distances. -/
theorem totallyBounded_range_of_dist_le {I X Y : Type*} [PseudoMetricSpace X]
    [MetricSpace Y] (f : I → X) (g : I → Y) (D : ℝ) (hD : 0 ≤ D)
    (hf : TotallyBounded (Set.range f))
    (h : ∀ i j, dist (g i) (g j) ≤ D * dist (f i) (f j)) :
    TotallyBounded (Set.range g) := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  have hD1 : 0 < D + 1 := by linarith
  obtain ⟨F, hFs, hF, hcover⟩ := Metric.finite_approx_of_totallyBounded hf
    (ε / (D + 1)) (div_pos hε hD1)
  let T : Set Y := g '' (f ⁻¹' F)
  have hTF : T.Finite := by
    classical
    choose j hj using fun x : F => hFs x.property
    have hsub : T ⊆ Set.range (fun x : F => g (j x)) := by
      rintro _ ⟨i, hi, rfl⟩
      refine ⟨⟨f i, hi⟩, ?_⟩
      have heq : f (j ⟨f i, hi⟩) = f i := hj ⟨f i, hi⟩
      exact dist_le_zero.mp (by simpa [heq] using h (j ⟨f i, hi⟩) i)
    let : Finite F := hF
    exact (Set.finite_range _).subset hsub
  refine ⟨T, hTF, ?_⟩
  rintro _ ⟨i, rfl⟩
  obtain ⟨x, hx, hix⟩ := Set.mem_iUnion₂.mp (hcover (Set.mem_range_self i))
  obtain ⟨j, hj⟩ := hFs hx
  apply Set.mem_iUnion₂.mpr
  refine ⟨g j, ⟨j, by simpa [hj] using hx, rfl⟩, ?_⟩
  change dist (g i) (g j) < ε
  calc
    _ ≤ D * dist (f i) (f j) := h i j
    _ ≤ (D + 1) * dist (f i) x := by rw [hj]; gcongr; linarith
    _ < (D + 1) * (ε / (D + 1)) :=
      mul_lt_mul_of_pos_left hix hD1
    _ = ε := mul_div_cancel₀ ε (ne_of_gt hD1)


/-- Convolution written with the translated scalar kernel. -/
def regularizedValue {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (k : Domain d → ℝ) (f : Domain d → 𝕜) (x : Domain d) : 𝕜 :=
  ∫ y, k (x - y) • f y

theorem regularized_integrable {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {k : Domain d → ℝ} {f : Domain d → 𝕜} (hf : Integrable f)
    (hk : Continuous k) {B : ℝ} (hB : ∀ x, ‖k x‖ ≤ B) (x : Domain d) :
    Integrable (fun y => k (x - y) • f y) := by
  exact hf.bdd_smul B (hk.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun y => hB (x - y))

theorem continuous_regularizedValue {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {k : Domain d → ℝ} {f : Domain d → 𝕜} (hf : Integrable f)
    (hk : Continuous k) {B : ℝ} (hB : ∀ x, ‖k x‖ ≤ B) :
    Continuous (regularizedValue k f) := by
  have hb : BddAbove (Set.range fun x => ‖k x‖) := ⟨B, by rintro _ ⟨x,rfl⟩; exact hB x⟩
  exact hb.continuous_convolution_right_of_integrable
    (ContinuousLinearMap.lsmul ℝ ℝ).flip hf hk

theorem norm_regularizedValue_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {k : Domain d → ℝ} {f : Domain d → 𝕜} (hf : Integrable f)
    {B : ℝ} (hB : ∀ x, ‖k x‖ ≤ B) (x : Domain d) :
    ‖regularizedValue k f x‖ ≤ B * ∫ y, ‖f y‖ := by
  rw [← integral_const_mul]
  apply norm_integral_le_of_norm_le (hf.norm.const_mul B)
  filter_upwards with y
  exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _))

theorem dist_regularizedValue_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {k : Domain d → ℝ} {f : Domain d → 𝕜} (hf : Integrable f)
    (hk : Continuous k) {B : ℝ} (hB : ∀ x, ‖k x‖ ≤ B)
    {δ : ℝ} {x z : Domain d} (hδ : ∀ y, ‖k (x - y) - k (z - y)‖ ≤ δ) :
    dist (regularizedValue k f x) (regularizedValue k f z) ≤ δ * ∫ y, ‖f y‖ := by
  rw [dist_eq_norm]
  unfold regularizedValue
  rw [← integral_sub (regularized_integrable hf hk hB _) (regularized_integrable hf hk hB _),
    ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hf.norm.const_mul δ)
  filter_upwards with y
  rw [← sub_smul]
  exact (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_right (hδ _) (norm_nonneg _))


/-- Smooth averages on a compact spatial set. -/
def regularizedOn {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} [CompactSpace G] {k : Domain d → ℝ}
    {f : Domain d → 𝕜} (hf : Integrable f) (hk : Continuous k)
    {B : ℝ} (hB : ∀ x, ‖k x‖ ≤ B) : G →ᵇ 𝕜 :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => regularizedValue k f x,
    (continuous_regularizedValue hf hk hB).comp continuous_subtype_val⟩

/-- A uniformly bounded L¹ family convolved with a bounded uniformly continuous
kernel is precompact on any fixed compact spatial set. -/
theorem compact_regularized_family {d : ℕ} {𝕜 I : Type*} [RCLike 𝕜]
    (G : Set (Domain d)) [CompactSpace G]
    (f : I → Domain d → 𝕜) (hf : ∀ i, Integrable (f i))
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ i, (∫ y, ‖f i y‖) ≤ M)
    (k : Domain d → ℝ) (hk : Continuous k) (hku : UniformContinuous k)
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x, ‖k x‖ ≤ B) :
    IsCompact (closure (Set.range (fun i => regularizedOn (G := G) (hf i) hk hB))) := by
  let F : I → G →ᵇ 𝕜 := fun i => regularizedOn (hf i) hk hB
  have hequi : Equicontinuous ((↑) : Set.range F → G → 𝕜) := by
    intro x
    apply Metric.equicontinuousAt_iff.mpr
    intro η hη
    have hM1 : 0 < M + 1 := by linarith
    obtain ⟨δ, hδ, hδk⟩ := Metric.uniformContinuous_iff.mp hku
      (η / (M + 1)) (div_pos hη hM1)
    refine ⟨δ, hδ, ?_⟩
    rintro z hxz ⟨_, i, rfl⟩
    change dist (regularizedValue k (f i) x) (regularizedValue k (f i) z) < η
    have hbound : ∀ y, ‖k (x - y) - k (z - y)‖ ≤ η / (M + 1) := by
      intro y
      rw [← dist_eq_norm]
      exact (hδk (by simpa only [dist_sub_right, Subtype.dist_eq, dist_comm] using hxz)).le
    calc
      _ ≤ (η / (M + 1)) * ∫ y, ‖f i y‖ := dist_regularizedValue_le (hf i) hk hB hbound
      _ ≤ (η / (M + 1)) * M :=
        mul_le_mul_of_nonneg_left (hM i) (div_nonneg hη.le hM1.le)
      _ < η := by rw [div_mul_eq_mul_div]; apply (div_lt_iff₀ hM1).mpr; nlinarith
  apply BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : 𝕜) (B * M))
    (isCompact_closedBall _ _) (Set.range F) _ hequi
  rintro _ x ⟨i, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (norm_regularizedValue_le (hf i) hB x).trans
    (mul_le_mul_of_nonneg_left (hM i) hB0)


/-- Compactness in the supremum norm on the closure transfers to total
boundedness of the corresponding Lp classes on a finite-measure domain. -/
theorem totallyBounded_toLp_of_compact_restrictions {d : ℕ} {𝕜 I : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} [IsFiniteMeasure (domainMeasure G)]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : I → Domain d → 𝕜)
    (hf : ∀ i, MemLp (f i) p (domainMeasure G))
    (F : I → closure G →ᵇ 𝕜)
    (hF : ∀ i (x : closure G), F i x = f i x)
    (hcomp : IsCompact (closure (Set.range F))) :
    TotallyBounded (Set.range (fun i => (hf i).toLp (f i))) := by
  let W : ℝ≥0∞ := (domainMeasure G Set.univ) ^ p.toReal⁻¹
  have hW : W ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _)
  apply totallyBounded_range_of_dist_le F (fun i => (hf i).toLp (f i)) W.toReal
    ENNReal.toReal_nonneg (hcomp.totallyBounded.subset subset_closure)
  intro i j
  rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
  have ha : ∀ᵐ x ∂domainMeasure G, x ∈ closure G :=
    ae_restrict_of_ae_restrict_of_subset subset_closure
      (ae_restrict_mem isClosed_closure.measurableSet)
  have hb : ∀ᵐ x ∂domainMeasure G, ‖(f i - f j) x‖ ≤ dist (F i) (F j) := by
    filter_upwards [ha] with x hx
    have hh := BoundedContinuousFunction.dist_coe_le_dist (f := F i) (g := F j) ⟨x,hx⟩
    simpa only [Pi.sub_apply, hF, dist_eq_norm] using hh
  have he := eLpNorm_le_of_ae_bound (p := p) ((hf i).aestronglyMeasurable.sub (hf j).aestronglyMeasurable) hb
  have hne : W * ENNReal.ofReal (dist (F i) (F j)) ≠ ∞ :=
    ENNReal.mul_ne_top hW ENNReal.ofReal_ne_top
  have hh := ENNReal.toReal_mono hne he
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal dist_nonneg] using hh


/-- The conventional convolution formula agrees with its translated-kernel form. -/
theorem regularizedValue_scaled_eq_smoothValue {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (ρ : Domain d → ℝ) (ε : ℝ) (f : Domain d → 𝕜) :
    regularizedValue (fun y => ε⁻¹ ^ d * ρ (ε⁻¹ • y)) f = smoothValue ρ ε f := by
  funext x
  have h := integral_sub_left_eq_self
    (fun y => (ε⁻¹ ^ d * ρ (ε⁻¹ • y)) • f (x - y)) volume x
  simpa only [sub_sub_cancel, regularizedValue, smoothValue] using h

/-- The scaled smooth kernel is bounded and uniformly continuous. -/
theorem scaled_kernel_properties {d : ℕ} {ρ : Domain d → ℝ}
    (hρ : Continuous ρ) (hc : HasCompactSupport ρ) (ε : ℝ) :
    Continuous (fun y => ε⁻¹ ^ d * ρ (ε⁻¹ • y)) ∧
    UniformContinuous (fun y => ε⁻¹ ^ d * ρ (ε⁻¹ • y)) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖ε⁻¹ ^ d * ρ (ε⁻¹ • y)‖ ≤ B := by
  obtain ⟨R, hR⟩ := hc.exists_bound_of_continuous hρ
  have hR0 : 0 ≤ R := (norm_nonneg (ρ 0)).trans (hR 0)
  refine ⟨by fun_prop, ?_, ‖ε⁻¹ ^ d‖ * R, mul_nonneg (norm_nonneg _) hR0, ?_⟩
  · exact Real.uniformContinuous_const_mul.comp
      ((hρ.uniformContinuous_of_tendsto_cocompact hc.is_zero_at_infty).comp
        (uniformContinuous_const_smul ε⁻¹))
  · intro y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hR _) (norm_nonneg _)

theorem exists_smoothing_scale {s : ℝ} (hs : 0 < s) (D : ℝ)
    {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ D * ε ^ s < η := by
  have hc : ContinuousAt (fun ε : ℝ => D * ε ^ s) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 s (Or.inr hs.le))
  obtain ⟨δ, hδ, hδb⟩ := Metric.continuousAt_iff.mp hc η hη
  let ε := min 1 (δ / 2)
  have hε : 0 < ε := lt_min zero_lt_one (half_pos hδ)
  refine ⟨ε, hε, min_le_left _ _, ?_⟩
  have hdist : dist ε 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε]
    exact (min_le_right _ _).trans_lt (by linarith)
  have hh := hδb hdist
  simpa only [Real.zero_rpow hs.ne', mul_zero, Real.dist_eq, sub_zero] using
    (le_abs_self (D * ε ^ s)).trans_lt (by simpa only [Real.zero_rpow hs.ne', mul_zero,
      Real.dist_eq, sub_zero] using hh)


/-- A whole-space approximation estimate controls the distance of the restricted classes. -/
theorem lp_restrict_dist_le {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    {G : Set (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp 𝕜 p (domainMeasure G)) (v w : Domain d → 𝕜)
    (hv : v =ᵐ[domainMeasure G] f) (hw : MemLp w p volume)
    {R : ℝ} (hR : 0 ≤ R)
    (herror : eLpNorm (fun x => w x - v x) p volume ≤ ENNReal.ofReal R) :
    dist (((hw.restrict G).toLp w) : Lp 𝕜 p (domainMeasure G)) f ≤ R := by
  have hwG : MemLp w p (domainMeasure G) := hw.restrict G
  let a : Lp 𝕜 p (domainMeasure G) := hwG.toLp w
  have hdiff : ((a - f : Lp 𝕜 p (domainMeasure G)) : Domain d → 𝕜) =ᵐ[domainMeasure G] (fun x => w x - v x) := by
    filter_upwards [Lp.coeFn_sub a f, hwG.coeFn_toLp, hv] with x hsub ha hx
    rw [hsub, Pi.sub_apply, ha, hx]
  change dist a f ≤ R
  rw [dist_eq_norm, Lp.norm_def, eLpNorm_congr_ae hdiff]
  have hlocal : eLpNorm (fun x => w x - v x) p (domainMeasure G) ≤ ENNReal.ofReal R :=
    (eLpNorm_mono_measure _ Measure.restrict_le_self).trans herror
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlocal).trans_eq (ENNReal.toReal_ofReal hR)


/-- The extension and quantitative smoothing estimates imply compactness in
exactly the original source exponent, with no restriction on sp. -/
theorem compact_firstProjection_of_smoothing
    (hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (hSmooth : Specs.P102.Fractional.EmbeddingsCompactness.uniformSmoothing.{u}) :
    ∀ (n : ℕ) (G : Set (Domain (n + 1))), IsBoundedLipschitzOpen G →
    ∀ s : ℝ, 0 < s → s < 1 →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
    ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∀ A : Set (Space 𝕜 G s p), Bornology.IsBounded A →
      IsCompact (closure (firstProjection '' A)) := by
  intro n G hG s hs0 hs1 p _ hp 𝕜 _ A hA
  have hGb := bounded_of_lipschitz hG
  let : CompactSpace (closure G) := isCompact_iff_compactSpace.mp hGb.isCompact_closure
  let : IsFiniteMeasure (domainMeasure G) := ⟨by
    simpa only [domainMeasure, Measure.restrict_apply_univ] using hGb.measure_lt_top (μ := volume)⟩
  obtain ⟨K, hK, Cext, E, hrestrict, hsupp, _hEbound⟩ :=
    hExtension n G hG s hs0 hs1 p hp 𝕜
  obtain ⟨D, hD0, hD⟩ := integrable_bound_of_support (E := 𝕜) K hK p hp
  obtain ⟨R, hR, hAR⟩ := hA.exists_pos_norm_le
  let N : ℝ := ‖E‖ * R
  have hN0 : 0 ≤ N := mul_nonneg (norm_nonneg E) hR.le
  have hEnorm (i : A) : ‖E i.val‖ ≤ N := by
    exact (E.le_opNorm i.val).trans (mul_le_mul_of_nonneg_left (hAR _ i.property) (norm_nonneg E))
  let f : A → Domain (n + 1) → 𝕜 := fun i => firstProjection (E i.val)
  have hf (i : A) : MemLp (f i) p volume := by
    simpa only [f, domainMeasure, Measure.restrict_univ] using Lp.memLp (firstProjection (E i.val))
  have hfi (i : A) : Integrable (f i) := (hD (f i) (hf i) (hsupp i.val)).1
  have hfL1 (i : A) : (∫ x, ‖f i x‖) ≤ D * N := by
    have h := (hD (f i) (hf i) (hsupp i.val)).2
    have hn : (eLpNorm (f i) p volume).toReal ≤ N := by
      have hn1 : ‖firstProjection (E i.val)‖ ≤ ‖E i.val‖ := by
        rw [space_norm hp]
        exact le_add_of_nonneg_right ENNReal.toReal_nonneg
      have heq : (eLpNorm (f i) p volume).toReal = ‖firstProjection (E i.val)‖ := by
        rw [Lp.norm_def]
        simp only [f, domainMeasure, Measure.restrict_univ]
      exact heq ▸ (hn1.trans (hEnorm i))
    exact h.trans (mul_le_mul_of_nonneg_left hn hD0)
  have hfsemi (i : A) : seminorm Set.univ s p (f i) ≤ ENNReal.ofReal N := by
    calc
      _ ≤ eLpNorm (firstProjection (E i.val)) p (domainMeasure Set.univ) +
          seminorm Set.univ s p (firstProjection (E i.val)) := le_add_left le_rfl
      _ = ENNReal.ofReal ‖E i.val‖ := fullNorm_eq_ofReal_norm hp _
      _ ≤ ENNReal.ofReal N := ENNReal.ofReal_le_ofReal (hEnorm i)
  obtain ⟨ρ, C, hρdiff, hρsupp, _hρpos, _hρmass, _hρball, hsmooth⟩ :=
    hSmooth (n + 1) (Nat.succ_pos n) s hs0 hs1 p hp 𝕜
  apply TotallyBounded.isCompact_of_isClosed _ isClosed_closure
  apply TotallyBounded.closure
  apply totallyBounded_of_approximations
  intro η hη
  obtain ⟨ε, hε, hε1, hεerr⟩ := exists_smoothing_scale hs0 ((C : ℝ) * N) hη
  let w : A → Domain (n + 1) → 𝕜 := fun i => smoothValue ρ ε (f i)
  have hw (i : A) : MemLp (w i) p volume := (hsmooth ε hε hε1 (E i.val)).1
  let W : A → Lp 𝕜 p (domainMeasure G) := fun i => ((hw i).restrict G).toLp (w i)
  obtain ⟨hk, hku, B, hB0, hB⟩ := scaled_kernel_properties hρdiff.continuous hρsupp ε
  let F : A → closure G →ᵇ 𝕜 := fun i => regularizedOn (hfi i) hk hB
  have hF (i : A) (x : closure G) : F i x = w i x := by
    change regularizedValue (fun y => ε⁻¹ ^ (n + 1) * ρ (ε⁻¹ • y)) (f i) x = _
    rw [regularizedValue_scaled_eq_smoothValue]
  have hcomp : IsCompact (closure (Set.range F)) :=
    compact_regularized_family (closure G) f hfi (D * N) (mul_nonneg hD0 hN0) hfL1
      _ hk hku B hB0 hB
  have hTB : TotallyBounded (Set.range W) :=
    totallyBounded_toLp_of_compact_restrictions w (fun i => (hw i).restrict G) F hF hcomp
  refine ⟨Set.range W, hTB, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  let i : A := ⟨v, hv⟩
  refine ⟨W i, Set.mem_range_self i, ?_⟩
  have herr : eLpNorm (fun x => w i x - f i x) p volume ≤
      ENNReal.ofReal ((C : ℝ) * ε ^ s * N) := by
    calc
      _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (ε ^ s) * seminorm Set.univ s p (f i) :=
        (hsmooth ε hε hε1 (E i.val)).2
      _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (ε ^ s) * ENNReal.ofReal N :=
        mul_le_mul' le_rfl (hfsemi i)
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg C.coe_nonneg (Real.rpow_nonneg hε.le _)),
          ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  have herrR : 0 ≤ (C : ℝ) * ε ^ s * N := by positivity
  have hdist : dist (W i) (firstProjection v) ≤ (C : ℝ) * ε ^ s * N := by
    exact lp_restrict_dist_le (firstProjection v) (f i) (w i)
      (hrestrict v) (hw i) herrR herr
  have hh : (C : ℝ) * ε ^ s * N < η := by nlinarith [hεerr]
  rw [dist_comm]
  exact hdist.trans_lt hh


/-- Once underlying Lp compactness is known, all compactness clauses follow
from the endpoint estimates and the proved lower-smoothness map. -/
theorem compactness_clauses_of_projection_compact
    (hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (hClosure : Specs.P102.Fractional.Morrey.onClosure.{u})
    (hMorrey : Specs.P102.Fractional.Morrey.wholeSpace.{u})
    (hDomain : Specs.P102.Fractional.Subcritical.boundedDomain.{u})
    (hWhole : Specs.P102.Fractional.Subcritical.wholeSpace.{u})
    (hbase : ∀ (n : ℕ) (G : Set (Domain (n + 1))), IsBoundedLipschitzOpen G →
      ∀ s : ℝ, 0 < s → s < 1 → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ →
      ∀ (𝕜 : Type u) [RCLike 𝕜],
      ∀ A : Set (Space 𝕜 G s p), Bornology.IsBounded A →
        IsCompact (closure (firstProjection '' A))) :
    Specs.P102.Fractional.EmbeddingsCompactness.subcriticalCompactness.{u} ∧
      Specs.P102.Fractional.EmbeddingsCompactness.criticalInclusions.{u} ∧
      Specs.P102.Fractional.EmbeddingsCompactness.supercriticalCompactness.{u} := by
  have hsub := subcriticalCompactness_of_projection_compact hDomain hbase
  exact ⟨hsub, critical_of_subcritical
    (lower_smoothness_conditional hExtension hClosure hMorrey hDomain hWhole) hsub,
    supercritical_compactness_conditional hExtension hClosure hMorrey hDomain hWhole⟩


namespace Smoothing

theorem exists_kernel (d : ℕ) :
    ∃ (ρ : Domain d → ℝ) (B : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      (∀ x, 0 ≤ ρ x) ∧ (∫ x, ρ x) = 1 ∧
      Function.support ρ ⊆ Metric.closedBall 0 1 ∧ ∀ x, ρ x ≤ B := by
  let b : ContDiffBump (0 : Domain d) := ⟨1/2, 1, by norm_num, by norm_num⟩
  refine ⟨b.normed volume, 1 / (volume : Measure (Domain d)).real (Metric.closedBall 0 b.rIn),
    b.contDiff_normed, b.hasCompactSupport_normed, b.nonneg_normed,
    b.integral_normed, ?_, b.normed_le_div_measure_closedBall_rIn volume⟩
  rw [b.support_normed_eq]
  exact Metric.ball_subset_closedBall

/-- Weighted Jensen written as an ENNReal estimate, valid also at p = 1. -/
theorem weighted_integral_le {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure α} (w : α → ℝ) (hw : Measurable w)
    (hwn : ∀ x, 0 ≤ w x) (hwm : ∫⁻ x, ENNReal.ofReal (w x) ∂μ = 1)
    (f : α → E) (hf : AEStronglyMeasurable f μ)
    (p : ℝ) (hp : 1 ≤ p) :
    ‖∫ x, w x • f x ∂μ‖ₑ ≤
      (∫⁻ x, ENNReal.ofReal (w x) * ‖f x‖ₑ ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpi : 0 ≤ 1 / p := by positivity
  have hpic : 0 ≤ 1 - 1 / p := by apply sub_nonneg.mpr; exact (div_le_one hp0).mpr hp
  have hh := P102.U2.Young.lintegral_three_rpow_le
    (hw.ennreal_ofReal.aemeasurable.mul (hf.enorm.pow_const p))
    hw.ennreal_ofReal.aemeasurable (aemeasurable_const (b := (1 : ℝ≥0∞)))
    hpi hpic (le_refl (0 : ℝ)) (by ring : 1 / p + (1 - 1 / p) + 0 = 1)
  simp only [ENNReal.rpow_zero, mul_one, hwm, ENNReal.one_rpow] at hh
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  apply le_trans (lintegral_mono (fun x => ?_)) hh
  simp only [Pi.mul_apply] at *
  rw [enorm_smul, Real.enorm_of_nonneg (hwn x)]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hpi, ← ENNReal.rpow_mul,
    (by field_simp : p * (1 / p) = 1), ENNReal.rpow_one]
  rw [mul_assoc, mul_comm (‖f x‖ₑ), ← mul_assoc,
    ← ENNReal.rpow_add_of_nonneg _ _ hpi hpic]
  simp

/-- A probability convolution is controlled by its singular-kernel domination. -/
theorem convolution_error_le {d : ℕ} {𝕜 : Type u} [RCLike 𝕜]
    (w : Domain d → ℝ) (hwc : Continuous w) (hwcs : HasCompactSupport w)
    (hwn : ∀ x, 0 ≤ w x) (hwint : ∫ x, w x = 1)
    (f : Domain d → 𝕜) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hf : MemLp f p volume) (D : ℝ≥0∞) (hD : D ≠ ∞)
    (hdom : ∀ z : Domain d, z ≠ 0 →
      ENNReal.ofReal (w z) ≤ D / ENNReal.ofReal ‖z‖ ^ ((d : ℝ) + s * p.toReal)) :
    eLpNorm (convolution w f (ContinuousLinearMap.lsmul ℝ ℝ) volume - f) p volume ≤
      D ^ (1 / p.toReal) * seminorm Set.univ s p f := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hpR1 : 1 ≤ p.toReal := by
    exact_mod_cast ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hwi : Integrable w volume := hwc.integrable_of_hasCompactSupport hwcs
  have hwm : ∫⁻ x, ENNReal.ofReal (w x) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all _ hwn), hwint, ENNReal.ofReal_one]
  have hfli : LocallyIntegrable f volume := hf.locallyIntegrable (Fact.out : 1 ≤ p)
  have hci (x : Domain d) : Integrable (fun y => w y • f (x - y)) volume :=
    hwcs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hwc hfli x
  have herr (x : Domain d) :
      convolution w f (ContinuousLinearMap.lsmul ℝ ℝ) volume x - f x =
        ∫ y, w y • (f (x-y) - f x) := by
    simp_rw [smul_sub]
    rw [integral_sub (hci x) (hwi.smul_const (f x)), integral_smul_const, hwint, one_smul]
    rfl
  have hb (x : Domain d) :
      ‖(convolution w f (ContinuousLinearMap.lsmul ℝ ℝ) volume - f) x‖ₑ ^ p.toReal ≤
        D * ∫⁻ y, if x = y then 0 else
          ‖f x - f y‖ₑ ^ p.toReal / ENNReal.ofReal ‖x-y‖ ^ ((d : ℝ) + s*p.toReal) := by
    have hfm : AEStronglyMeasurable (fun y => f (x-y) - f x) volume :=
      (hf.aestronglyMeasurable.comp_measurePreserving
        (measurePreserving_sub_left (volume : Measure (Domain d)) x )).sub aestronglyMeasurable_const
    have hj := weighted_integral_le w hwc.measurable hwn hwm
      (fun y => f (x-y) - f x) hfm p.toReal hpR1
    rw [← herr] at hj
    have hjp := ENNReal.rpow_le_rpow hj hpR.le
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hpR.ne', ENNReal.rpow_one] at hjp
    apply hjp.trans
    rw [← lintegral_const_mul' D _ hD]
    have hsub := (measurePreserving_sub_left (volume : Measure (Domain d)) x).lintegral_comp_emb
      (Homeomorph.subLeft x).isClosedEmbedding.measurableEmbedding
      (fun y => D * if x = y then 0 else
        ‖f x - f y‖ₑ ^ p.toReal / ENNReal.ofReal ‖x-y‖ ^ ((d : ℝ) + s*p.toReal))
    rw [← hsub]
    apply lintegral_mono
    intro y
    by_cases hy : y = 0
    · subst y
      simp [hpR]
    · have hxy : x ≠ x-y := by
        intro hh
        apply hy
        have he := congrArg (fun z : Domain d => x-z) hh
        simpa using he.symm
      simp only [hxy, ite_false, sub_sub_cancel]
      rw [enorm_sub_rev, div_eq_mul_inv, ← mul_assoc]
      convert mul_le_mul' (hdom y hy) (le_refl (‖f x - f (x-y)‖ₑ ^ p.toReal)) using 1
      simp only [div_eq_mul_inv]
      ac_rfl
  have hmeas : AEStronglyMeasurable
      (convolution w f (ContinuousLinearMap.lsmul ℝ ℝ) volume - f) volume :=
    (hwcs.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hwc hfli).aestronglyMeasurable.sub hf.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hmeas, seminorm]
  have hi := lintegral_mono (μ := (volume : Measure (Domain d))) hb
  rw [lintegral_const_mul' D _ hD] at hi
  have hr := ENNReal.rpow_le_rpow hi (by positivity : 0 ≤ 1 / p.toReal)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p.toReal)] at hr
  simpa only [energy, domainMeasure, Measure.restrict_univ] using hr

/-- Dilation preserves the probability normalization of a compact convolution kernel. -/
theorem scaled_kernel_properties {d : ℕ} {ρ : Domain d → ℝ}
    (hcont : Continuous ρ) (hcompact : HasCompactSupport ρ)
    (hnonneg : ∀ x, 0 ≤ ρ x) (hmass : (∫ x, ρ x) = 1)
    {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun x => ε⁻¹ ^ d * ρ (ε⁻¹ • x)) ∧
    HasCompactSupport (fun x => ε⁻¹ ^ d * ρ (ε⁻¹ • x)) ∧
    (∀ x, 0 ≤ ε⁻¹ ^ d * ρ (ε⁻¹ • x)) ∧
    (∫ x, ε⁻¹ ^ d * ρ (ε⁻¹ • x)) = 1 := by
  have hc : Continuous (fun x : Domain d => ρ (ε⁻¹ • x)) :=
    hcont.comp (by fun_prop)
  have hk : HasCompactSupport (fun x : Domain d => ρ (ε⁻¹ • x)) :=
    hcompact.comp_smul (inv_ne_zero hε.ne')
  refine ⟨continuous_const.mul hc, hk.mul_left, fun x => mul_nonneg (by positivity) (hnonneg _), ?_⟩
  rw [integral_const_mul, integral_comp_inv_smul_of_nonneg volume ρ hε.le,
    finrank_euclideanSpace_fin, hmass, smul_eq_mul, mul_one, ← mul_pow,
    inv_mul_cancel₀ hε.ne', one_pow]

theorem scaled_kernel_domination {d : ℕ} (ρ : Domain d → ℝ) (B : ℝ)
    (_hB : 0 ≤ B) (hρB : ∀ x, ρ x ≤ B)
    (hsupp : Function.support ρ ⊆ Metric.closedBall 0 1)
    {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s)
    (p : ℝ≥0∞) :
    ∀ z : Domain d, z ≠ 0 →
      ENNReal.ofReal (ε⁻¹ ^ d * ρ (ε⁻¹ • z)) ≤
        (ENNReal.ofReal B * ENNReal.ofReal ε ^ (s * p.toReal)) /
          ENNReal.ofReal ‖z‖ ^ ((d : ℝ) + s * p.toReal) := by
  intro z hz
  by_cases hρz : ρ (ε⁻¹ • z) = 0
  · simp [hρz]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hn0 : ENNReal.ofReal ‖z‖ ^ ((d : ℝ) + s * p.toReal) ≠ 0 :=
    (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hn) ENNReal.ofReal_ne_top).ne'
  have hnT : ENNReal.ofReal ‖z‖ ^ ((d : ℝ) + s * p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  have hnε : ‖z‖ ≤ ε := by
    have hh := hsupp hρz
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hε.le)] at hh
    simpa using (inv_mul_le_iff₀ hε).mp hh
  apply (ENNReal.le_div_iff_mul_le (Or.inl hn0) (Or.inl hnT)).mpr
  calc
    _ ≤ (ENNReal.ofReal (ε⁻¹ ^ d) * ENNReal.ofReal B) *
        ENNReal.ofReal ε ^ ((d : ℝ) + s * p.toReal) := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ε⁻¹ ^ d)]
      exact mul_le_mul' (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (hρB _)))
        (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hnε) (by positivity))
    _ = _ := by
      rw [ENNReal.ofReal_pow, ENNReal.ofReal_inv_of_pos hε]
      rw [← ENNReal.rpow_natCast, ENNReal.inv_rpow, ← ENNReal.rpow_neg, mul_assoc, mul_comm (ENNReal.ofReal B),
        ← mul_assoc, ← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.mpr hε).ne' ENNReal.ofReal_ne_top]
      ring_nf
      positivity

theorem uniform_smoothing_conditional
    (_hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (_hClosure : Specs.P102.Fractional.Morrey.onClosure.{u})
    (_hMorrey : Specs.P102.Fractional.Morrey.wholeSpace.{u})
    (_hDomain : Specs.P102.Fractional.Subcritical.boundedDomain.{u})
    (_hWhole : Specs.P102.Fractional.Subcritical.wholeSpace.{u}) :
    Specs.P102.Fractional.EmbeddingsCompactness.uniformSmoothing.{u} := by
  intro d _hd s hs0 _hs1 p _ hp 𝕜 _
  obtain ⟨ρ, B, hρdiff, hρcomp, hρnn, hρint, hρsupp, hρB⟩ := exists_kernel d
  have hB0 : 0 ≤ B := (hρnn 0).trans (hρB 0)
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  let C : ℝ≥0 := ⟨B ^ (1 / p.toReal), Real.rpow_nonneg hB0 _⟩
  refine ⟨ρ, C, hρdiff, hρcomp, hρnn, hρint, hρsupp, ?_⟩
  intro ε hε _hε1 v
  let w : Domain d → ℝ := fun z => ε⁻¹ ^ d * ρ (ε⁻¹ • z)
  obtain ⟨hwc, hwcs, hwn, hwmass⟩ := scaled_kernel_properties
    hρdiff.continuous hρcomp hρnn hρint hε
  have hf : MemLp (firstProjection v) p volume := by
    simpa only [domainMeasure, Measure.restrict_univ] using Lp.memLp (firstProjection v)
  let D : ℝ≥0∞ := ENNReal.ofReal B * ENNReal.ofReal ε ^ (s * p.toReal)
  have hD : D ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top)
  have herr := convolution_error_le w hwc hwcs hwn hwmass
    (firstProjection v) s p hp hf D hD
    (scaled_kernel_domination ρ B hB0 hρB hρsupp hε hs0.le p)
  have hsemi : seminorm Set.univ s p (firstProjection v) < ∞ :=
    (firstProjection_range_seminorm hp (firstProjection v)).mp ⟨v, rfl⟩
  have hmemErr : MemLp
      (convolution w (firstProjection v) (ContinuousLinearMap.lsmul ℝ ℝ) volume - (firstProjection v : Domain d → 𝕜))
      p volume := herr.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) hD).lt_top hsemi)
  have hmem : MemLp
      (convolution w (firstProjection v) (ContinuousLinearMap.lsmul ℝ ℝ) volume) p volume := by
    convert hmemErr.add hf using 1
    ext x
    simp
  have hconv : convolution w (firstProjection v) (ContinuousLinearMap.lsmul ℝ ℝ) volume =
      smoothValue ρ ε (firstProjection v) := rfl
  refine ⟨by simpa only [hconv] using hmem, ?_⟩
  rw [← hconv]
  convert herr using 1
  dsimp only [D]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p.toReal),
    ← ENNReal.rpow_mul]
  have he : s * p.toReal * (1 / p.toReal) = s := by field_simp
  rw [he, ENNReal.ofReal_rpow_of_nonneg hε.le (by positivity : 0 ≤ s)]
  congr 2
  rw [ENNReal.ofReal_rpow_of_nonneg hB0 (by positivity : 0 ≤ 1 / p.toReal)]
  exact ENNReal.coe_nnreal_eq C

end Smoothing


/-- The full original theorem, conditionally derived from the five frozen
upstream proposition types in their specified order. The independent expected
type retains the original unconditional statement; no closed wrapper is defined here. -/
theorem full_theorem_conditional
    (hExtension : Specs.P102.Fractional.Extension.extension.{u})
    (hClosure : Specs.P102.Fractional.Morrey.onClosure.{u})
    (hMorrey : Specs.P102.Fractional.Morrey.wholeSpace.{u})
    (hDomain : Specs.P102.Fractional.Subcritical.boundedDomain.{u})
    (hWhole : Specs.P102.Fractional.Subcritical.wholeSpace.{u}) :
    Specs.P102.Fractional.EmbeddingsCompactness.fullTheorem.{u} := by
  have hsmooth := Smoothing.uniform_smoothing_conditional
    hExtension hClosure hMorrey hDomain hWhole
  have hbase := compact_firstProjection_of_smoothing hExtension hsmooth
  obtain ⟨hsub, hcrit, hsuper⟩ := compactness_clauses_of_projection_compact
    hExtension hClosure hMorrey hDomain hWhole hbase
  exact ⟨extension_clause_conditional hExtension hClosure hMorrey hDomain hWhole,
    subcritical_estimates_conditional hExtension hClosure hMorrey hDomain hWhole,
    supercritical_embedding_conditional hExtension hClosure hMorrey hDomain hWhole,
    hsub, critical_embedding_conditional hExtension hClosure hMorrey hDomain hWhole,
    hcrit, hsuper, lower_smoothness_conditional hExtension hClosure hMorrey hDomain hWhole,
    hsmooth⟩

end P102.Fractional.Embedding

universe v8_closure_729bdd24a2b04483_u0
theorem _root_.«P102».«Fractional».«Embedding».«full_theorem» : _root_.«Specs».«P102».«Fractional».«EmbeddingsCompactness».«fullTheorem».{v8_closure_729bdd24a2b04483_u0} :=
  @_root_.«P102».«Fractional».«Embedding».«full_theorem_conditional».{v8_closure_729bdd24a2b04483_u0} (@_root_.«P102».«Fractional».«bounded_linear_extension».{v8_closure_729bdd24a2b04483_u0}) (@_root_.«P102».«Fractional».«Morrey».«on_closure».{v8_closure_729bdd24a2b04483_u0}) (@_root_.«P102».«Fractional».«Morrey».«whole_space».{v8_closure_729bdd24a2b04483_u0}) (@_root_.«P102».«Fractional».«subcritical_bounded_domain».{v8_closure_729bdd24a2b04483_u0}) (@_root_.«P102».«Fractional».«subcritical_whole_space».{v8_closure_729bdd24a2b04483_u0})
