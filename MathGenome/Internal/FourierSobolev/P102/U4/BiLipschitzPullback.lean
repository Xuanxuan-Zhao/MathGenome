import MathGenome.Internal.FourierSobolev.Specs.P102.U4.BiLipschitzPullback
import MathGenome.Internal.FourierSobolev.P102.U4.Rademacher
import MathGenome.Internal.FourierSobolev.P102.U4.ChainProduct
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ContDiff.RCLike

import MathGenome.Internal.FourierSobolev.P102.U4.MeyersSerrin
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace P102.U4

/-- Euclidean outer volume satisfies the sharp Lipschitz image estimate.
Use Hausdorff measure in the ambient dimension and cancel its Haar
normalization, so no measurability of the set is needed. -/
theorem volume_image_le_of_lipschitzOnWith {d : ℕ} {K : ℝ≥0}
    {f : Space d → Space d} {s : Set (Space d)} (hf : LipschitzOnWith K f s) :
    volume (f '' s) ≤ (K : ℝ≥0∞) ^ d * volume s := by
  let μ : Measure (Space d) :=
    Measure.hausdorffMeasure (Module.finrank ℝ (Space d))
  let c : ℝ≥0 := Measure.addHaarScalarFactor μ volume
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume
  have hμ : μ = c • volume := Measure.isAddLeftInvariant_eq_smul μ volume
  have h := hf.hausdorffMeasure_image_le (d := (Module.finrank ℝ (Space d) : ℝ))
    (by positivity)
  have hdim : Module.finrank ℝ (Space d) = d := by simp [Space]
  change μ (f '' s) ≤ _ * μ s at h
  rw [hμ] at h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul,
    ENNReal.rpow_natCast, hdim] at h
  rw [mul_left_comm] at h
  exact (ENNReal.mul_le_mul_iff_right (by exact_mod_cast hc.ne') ENNReal.coe_ne_top).mp h

namespace BiLipschitzChart
variable {d : ℕ} {U V : Opens (Space d)} {L M : ℝ≥0}

def symm (g : BiLipschitzChart U V L M) : BiLipschitzChart V U M L where
  toFun := g.invFun
  invFun := g.toFun
  mapsTo := g.inv_mapsTo
  inv_mapsTo := g.mapsTo
  left_inv := g.right_inv
  right_inv := g.left_inv
  lipschitz := g.inv_lipschitz
  inv_lipschitz := g.lipschitz

theorem preimage_eq_inverse_image (g : BiLipschitzChart U V L M) (E : Set (Space d)) :
    (V : Set (Space d)) ∩ g.toFun ⁻¹' E = g.invFun '' ((U : Set (Space d)) ∩ E) := by
  ext x
  constructor
  · rintro ⟨hx, hE⟩
    exact ⟨g.toFun x, ⟨g.mapsTo hx, hE⟩, g.left_inv x hx⟩
  · rintro ⟨y, ⟨hy, hE⟩, rfl⟩
    exact ⟨g.inv_mapsTo hy, by change g.toFun (g.invFun y) ∈ E; rwa [g.right_inv y hy]⟩

theorem preimage_volume_le (g : BiLipschitzChart U V L M) (E : Set (Space d)) :
    volume ((V : Set (Space d)) ∩ g.toFun ⁻¹' E) ≤
      (M : ℝ≥0∞) ^ d * volume ((U : Set (Space d)) ∩ E) := by
  rw [g.preimage_eq_inverse_image]
  exact volume_image_le_of_lipschitzOnWith (g.inv_lipschitz.mono inter_subset_left)

theorem image_volume_le (g : BiLipschitzChart U V L M) {E : Set (Space d)}
    (hE : E ⊆ V) : volume (g.toFun '' E) ≤ (L : ℝ≥0∞) ^ d * volume E :=
  volume_image_le_of_lipschitzOnWith (g.lipschitz.mono hE)

theorem image_null (g : BiLipschitzChart U V L M) {E : Set (Space d)}
    (hE : E ⊆ V) (hnull : volume E = 0) : volume (g.toFun '' E) = 0 := by
  simpa only [hnull, mul_zero, nonpos_iff_eq_zero] using g.image_volume_le hE

theorem aemeasurable (g : BiLipschitzChart U V L M) :
    AEMeasurable g.toFun (volume.restrict (V : Set (Space d))) :=
  g.lipschitz.continuousOn.aemeasurable V.isOpen.measurableSet

/-- Domination of the pushforward of the restricted measure. -/
theorem map_volume_le (g : BiLipschitzChart U V L M) :
    Measure.map g.toFun (volume.restrict (V : Set (Space d))) ≤
      (M : ℝ≥0∞) ^ d • volume.restrict (U : Set (Space d)) := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.map_apply_of_aemeasurable g.aemeasurable hE, Measure.smul_apply,
    Measure.restrict_apply hE, Measure.restrict_apply' V.isOpen.measurableSet]
  simpa only [smul_eq_mul, inter_comm] using g.preimage_volume_le E

theorem map_volume_absolutelyContinuous (g : BiLipschitzChart U V L M) :
    Measure.map g.toFun (volume.restrict (V : Set (Space d))) ≪
      volume.restrict (U : Set (Space d)) :=
  Measure.absolutelyContinuous_of_le_smul g.map_volume_le

/-- A.e. assertions can be transported even though values off V are arbitrary. -/
theorem ae_comp (g : BiLipschitzChart U V L M) {P : Space d → Prop}
    (hP : ∀ᵐ x ∂volume.restrict (U : Set (Space d)), P x) :
    ∀ᵐ x ∂volume.restrict (V : Set (Space d)), P (g.toFun x) :=
  ae_of_ae_map g.aemeasurable (g.map_volume_absolutelyContinuous.ae_le hP)

theorem memLp_comp {E : Type*} [NormedAddCommGroup E]
    (g : BiLipschitzChart U V L M) {p : ℝ≥0∞} {f : Space d → E}
    (hf : MemLp f p (volume.restrict (U : Set (Space d)))) :
    MemLp (f ∘ g.toFun) p (volume.restrict (V : Set (Space d))) :=
  (hf.of_measure_le_smul (by simp) g.map_volume_le).comp_of_map g.aemeasurable

theorem eLpNorm_comp_le {E : Type*} [NormedAddCommGroup E]
    (g : BiLipschitzChart U V L M) {p : ℝ≥0∞} {f : Space d → E}
    (hf : MemLp f p (volume.restrict (U : Set (Space d)))) :
    eLpNorm (f ∘ g.toFun) p (volume.restrict (V : Set (Space d))) ≤
      ((M : ℝ≥0∞) ^ d) ^ (1 / p).toReal *
        eLpNorm f p (volume.restrict (U : Set (Space d))) := by
  have hm := hf.of_measure_le_smul (by simp) g.map_volume_le
  rw [← eLpNorm_map_measure hm.aestronglyMeasurable g.aemeasurable]
  exact eLpNorm_le_of_measure_le_smul g.map_volume_le

variable (g : BiLipschitzChart U V L M) (𝕜 : Type) [RCLike 𝕜]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- Pullback on Lp classes before its continuity proof. -/
def lpPullbackLinear : DomainLp 𝕜 U p →ₗ[𝕜] DomainLp 𝕜 V p where
  toFun u := (g.memLp_comp (Lp.memLp u)).toLp (u ∘ g.toFun)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(g.memLp_comp (Lp.memLp (u + v))).coeFn_toLp,
      (g.memLp_comp (Lp.memLp u)).coeFn_toLp,
      (g.memLp_comp (Lp.memLp v)).coeFn_toLp,
      Lp.coeFn_add ((g.memLp_comp (Lp.memLp u)).toLp (u ∘ g.toFun))
        ((g.memLp_comp (Lp.memLp v)).toLp (v ∘ g.toFun)),
      g.ae_comp (Lp.coeFn_add u v)] with x huv hu hv hadd hsource
    simpa only [Function.comp_apply, huv, hadd, Pi.add_apply, hu, hv] using hsource
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(g.memLp_comp (Lp.memLp (c • u))).coeFn_toLp,
      (g.memLp_comp (Lp.memLp u)).coeFn_toLp,
      Lp.coeFn_smul c ((g.memLp_comp (Lp.memLp u)).toLp (u ∘ g.toFun)),
      g.ae_comp (Lp.coeFn_smul c u)] with x hcu hu hsmul hsource
    simpa only [Function.comp_apply, hcu, RingHom.id_apply, hsmul, Pi.smul_apply,
      hu] using hsource

omit [Fact (1 ≤ p)] in
theorem lpPullbackLinear_norm_le (u : DomainLp 𝕜 U p) :
    ‖g.lpPullbackLinear 𝕜 p u‖ ≤ pullbackLpBound d p M * ‖u‖ := by
  change ‖(g.memLp_comp (Lp.memLp u)).toLp (u ∘ g.toFun)‖ ≤ _
  rw [Lp.norm_toLp]
  calc
    _ ≤ (((M : ℝ≥0∞) ^ d) ^ (1 / p).toReal *
        eLpNorm u p (volume.restrict (U : Set (Space d)))).toReal :=
      ENNReal.toReal_mono (by finiteness) (g.eLpNorm_comp_le (Lp.memLp u))
    _ = pullbackLpBound d p M * ‖u‖ := by
      rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow]
      simp only [ENNReal.toReal_pow, ENNReal.coe_toReal, pullbackLpBound, Lp.norm_def]

/-- The bounded linear pullback on Lp, also for complex scalars. -/
def lpPullback : DomainLp 𝕜 U p →L[𝕜] DomainLp 𝕜 V p :=
  (g.lpPullbackLinear 𝕜 p).mkContinuous (pullbackLpBound d p M)
    (g.lpPullbackLinear_norm_le 𝕜 p)

theorem lpPullback_ae (u : DomainLp 𝕜 U p) :
    g.lpPullback 𝕜 p u =ᵐ[volume.restrict (V : Set (Space d))] (u ∘ g.toFun) :=
  (g.memLp_comp (Lp.memLp u)).coeFn_toLp

theorem lpPullback_norm_le : ‖g.lpPullback 𝕜 p‖ ≤ pullbackLpBound d p M :=
  LinearMap.mkContinuous_norm_le _ (Real.rpow_nonneg (by positivity) _) _

end BiLipschitzChart

section Multiplier
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (V : Opens (Space d))
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Space d → ℝ) (C : ℝ≥0)
  (ha : AEStronglyMeasurable a (volume.restrict (V : Set (Space d))))
  (hbound : ∀ᵐ x ∂volume.restrict (V : Set (Space d)), ‖a x‖ ≤ C)
include ha hbound

omit [Fact (1 ≤ p)] in
private theorem realMultiplier_memLp (u : DomainLp 𝕜 V p) :
    MemLp (fun x => a x • u x) p (volume.restrict (V : Set (Space d))) := by
  apply (Lp.memLp u).of_le_mul (c := (C : ℝ)) (ha.smul (Lp.aestronglyMeasurable u))
  filter_upwards [hbound] with x hx
  change ‖a x • u x‖ ≤ (C : ℝ) * ‖u x‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg (u x))

private def realMultiplierLinear : DomainLp 𝕜 V p →ₗ[𝕜] DomainLp 𝕜 V p where
  toFun u := (realMultiplier_memLp V p a C ha hbound u).toLp (fun x => a x • u x)
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(realMultiplier_memLp V p a C ha hbound (u + v)).coeFn_toLp,
      (realMultiplier_memLp V p a C ha hbound u).coeFn_toLp,
      (realMultiplier_memLp V p a C ha hbound v).coeFn_toLp,
      Lp.coeFn_add u v,
      Lp.coeFn_add ((realMultiplier_memLp V p a C ha hbound u).toLp _)
        ((realMultiplier_memLp V p a C ha hbound v).toLp _)] with x huv hu hv hsource htgt
    simp only [huv, htgt, Pi.add_apply, hu, hv, hsource, smul_add]
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [(realMultiplier_memLp V p a C ha hbound (c • u)).coeFn_toLp,
      (realMultiplier_memLp V p a C ha hbound u).coeFn_toLp,
      Lp.coeFn_smul c u,
      Lp.coeFn_smul c ((realMultiplier_memLp V p a C ha hbound u).toLp _)]
      with x hcu hu hsource htgt
    simp only [hcu, RingHom.id_apply, htgt, Pi.smul_apply, hu, hsource]
    exact smul_comm (a x) c (u x)

private theorem realMultiplierLinear_norm_le (u : DomainLp 𝕜 V p) :
    ‖realMultiplierLinear V p a C ha hbound u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(realMultiplier_memLp V p a C ha hbound u).coeFn_toLp, hbound] with x hx hb
  simpa only [realMultiplierLinear, LinearMap.coe_mk, AddHom.coe_mk, hx, norm_smul]
    using mul_le_mul_of_nonneg_right hb (norm_nonneg (u x))

/-- Multiplication by a bounded measurable real coefficient, scalar-linear
also on complex Lp spaces. -/
def realMultiplier : DomainLp 𝕜 V p →L[𝕜] DomainLp 𝕜 V p :=
  (realMultiplierLinear V p a C ha hbound).mkContinuous C
    (realMultiplierLinear_norm_le V p a C ha hbound)

theorem realMultiplier_ae (u : DomainLp 𝕜 V p) :
    realMultiplier V p a C ha hbound u =ᵐ[volume.restrict (V : Set (Space d))]
      (fun x => a x • u x) := (realMultiplier_memLp V p a C ha hbound u).coeFn_toLp

theorem realMultiplier_norm_le : ‖realMultiplier (𝕜 := 𝕜) V p a C ha hbound‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ C.coe_nonneg _
end Multiplier

/-- A locally Lipschitz scalar function is locally AC on the coordinate fibers. -/
theorem scalar_locallyAC_on_fiber {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {V : Opens (Space d)} {f : Space d → 𝕜}
    (hf : LocallyLipschitzOn (V : Set (Space d)) f) (j : Fin d) (z : ACL.Transverse j) :
    ACL.LocallyAC (fun t => f (ACL.line j z t)) (ACL.fiber V j z) := by
  intro a b hab
  have hc := (isCompact_uIcc (a := a) (b := b)).image (acl_line_lipschitz j z).continuous
  have hs : ACL.line j z '' uIcc a b ⊆ (V : Set (Space d)) := by
    rintro _ ⟨t, ht, rfl⟩
    exact hab ht
  obtain ⟨C, hC⟩ := (hf.mono hs).exists_lipschitzOnWith_of_compact hc
  exact (hC.comp (acl_line_lipschitz j z).lipschitzOnWith
    (mapsTo_image (ACL.line j z) (uIcc a b))).absolutelyContinuousOnInterval

/-- Classical derivatives of a locally Lipschitz scalar function identify its
weak derivatives whenever the proposed entries are locally integrable. -/
theorem weakDerivative_of_locallyLipschitzOn {d : ℕ} (hd : 0 < d)
    {𝕜 : Type} [RCLike 𝕜] (V : Opens (Space d)) (f : Space d → 𝕜)
    (D : Space d → Space d →L[ℝ] 𝕜)
    (hf : LocallyLipschitzOn (V : Set (Space d)) f)
    (hD : ∀ᵐ x ∂volume.restrict (V : Set (Space d)), HasFDerivAt f (D x) x)
    (j : Fin d)
    (hLI : LocallyIntegrableOn (fun x => D x (coordinateVector d j)) V volume) :
    distributionPartial {j} (regularDistribution V f) =
      regularDistribution V (fun x => D x (coordinateVector d j)) := by
  apply acl_converse d hd 𝕜 V j f _
    (hf.continuousOn.locallyIntegrableOn V.isOpen.measurableSet) hLI
  refine ⟨f, Filter.EventuallyEq.rfl, ?_⟩
  filter_upwards [ae_on_acl_fibers V j hD] with z hz
  refine ⟨scalar_locallyAC_on_fiber hf j z, ?_⟩
  filter_upwards [hz] with t ht
  exact ht.comp_hasDerivAt t (acl_line_hasDerivAt j z t)

namespace BiLipschitzChart
variable {d : ℕ} {U V : Opens (Space d)} {L M : ℝ≥0}
  (g : BiLipschitzChart U V L M)

theorem locallyLipschitzOn : LocallyLipschitzOn (V : Set (Space d)) g.toFun :=
  fun _x _hx => ⟨L, V, self_mem_nhdsWithin, g.lipschitz⟩

theorem smooth_comp_locallyLipschitz {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiffOn ℝ 1 f U) :
    LocallyLipschitzOn (V : Set (Space d)) (f ∘ g.toFun) := by
  intro x hx
  obtain ⟨K, s, hs, hK⟩ := (hf.contDiffAt (U.isOpen.mem_nhds (g.mapsTo hx))).exists_lipschitzOnWith
  refine ⟨K * L, (V : Set (Space d)) ∩ g.toFun ⁻¹' s,
    inter_mem self_mem_nhdsWithin ((g.lipschitz.continuousOn x hx).preimage_mem_nhdsWithin hs), ?_⟩
  exact hK.comp (g.lipschitz.mono inter_subset_left) (fun y hy => hy.2)

/-- Smooth scalar functions obey the weak coordinate chain rule through a
Lipschitz chart. The local L¹ assumption is exactly what is needed to regard
the displayed classical expression as a regular distribution. -/
theorem smooth_comp_weak_chain (hd : 0 < d) {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiffOn ℝ 1 f U) (j : Fin d)
    (hLI : LocallyIntegrableOn
      (fun x => fderiv ℝ f (g.toFun x) (chartDerivative g x (coordinateVector d j))) V volume) :
    distributionPartial {j} (regularDistribution V (f ∘ g.toFun)) =
      regularDistribution V
        (fun x => fderiv ℝ f (g.toFun x) (chartDerivative g x (coordinateVector d j))) := by
  apply weakDerivative_of_locallyLipschitzOn hd V (f ∘ g.toFun)
    (fun x => (fderiv ℝ f (g.toFun x)).comp (chartDerivative g x))
    (g.smooth_comp_locallyLipschitz hf) _ j hLI
  filter_upwards [ae_differentiableAt_of_locallyLipschitzOn g.locallyLipschitzOn,
    ae_restrict_mem V.isOpen.measurableSet] with x hx hxV
  exact ((hf.contDiffAt (U.isOpen.mem_nhds (g.mapsTo hxV))).differentiableAt
    (by decide)).hasFDerivAt.comp x hx.hasFDerivAt

theorem derivative_entry_measurable (i j : Fin d) :
    Measurable (fun x => (chartDerivative g x (coordinateVector d j)) i) := by
  let e : (Space d →L[ℝ] Space d) →L[ℝ] ℝ :=
    (EuclideanSpace.proj i).comp (ContinuousLinearMap.apply ℝ (Space d) (coordinateVector d j))
  exact e.continuous.measurable.comp (measurable_fderiv ℝ g.toFun)

theorem derivative_entry_bound (i j : Fin d) :
    ∀ᵐ x ∂volume.restrict (V : Set (Space d)),
      ‖(chartDerivative g x (coordinateVector d j)) i‖ ≤ L := by
  filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
  calc
    _ ≤ ‖chartDerivative g x (coordinateVector d j)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖chartDerivative g x‖ * ‖coordinateVector d j‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖chartDerivative g x‖ := by
      simp [coordinateVector, EuclideanSpace.basisFun_apply, EuclideanSpace.single,
        PiLp.norm_single]
    _ ≤ L := norm_fderiv_le_of_lipschitzOn ℝ (V.isOpen.mem_nhds hx) g.lipschitz

variable (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]

/-- The bounded coefficient map used in the candidate weak derivative. -/
def derivativeEntryMultiplier (i j : Fin d) : DomainLp 𝕜 V p →L[𝕜] DomainLp 𝕜 V p :=
  realMultiplier V p (fun x => (chartDerivative g x (coordinateVector d j)) i) L
    (g.derivative_entry_measurable i j).aestronglyMeasurable
    (g.derivative_entry_bound i j)

def coordinateDerivativeCLM (i : Fin d) : Sobolev 𝕜 U 1 p →L[𝕜] DomainLp 𝕜 U p :=
  (PiLp.proj 1 _ (firstSobolevIndex i)).comp (sobolevSubmodule 𝕜 U 1 p).subtypeL

/-- The formal expression Du(g(x)) Dg(x), constructed as a bounded linear
map of the input Sobolev class before imposing any weak derivative identity. -/
def derivativePullback (j : Fin d) : Sobolev 𝕜 U 1 p →L[𝕜] DomainLp 𝕜 V p :=
  ∑ i : Fin d, (g.derivativeEntryMultiplier 𝕜 p i j).comp
    ((g.lpPullback 𝕜 p).comp (coordinateDerivativeCLM (U := U) 𝕜 p i))

theorem derivativePullback_ae (u : Sobolev 𝕜 U 1 p) (j : Fin d) :
    g.derivativePullback 𝕜 p j u =ᵐ[volume.restrict (V : Set (Space d))]
      (fun x => ∑ i : Fin d, (chartDerivative g x (coordinateVector d j) i) •
        firstWeakDerivative u i (g.toFun x)) := by
  have he (i : Fin d) :
      g.derivativeEntryMultiplier 𝕜 p i j (g.lpPullback 𝕜 p (firstWeakDerivative u i)) =ᵐ[
        volume.restrict (V : Set (Space d))]
        (fun x => (chartDerivative g x (coordinateVector d j) i) •
          firstWeakDerivative u i (g.toFun x)) := by
    filter_upwards [realMultiplier_ae V p _ L
      (g.derivative_entry_measurable i j).aestronglyMeasurable
      (g.derivative_entry_bound i j) (g.lpPullback 𝕜 p (firstWeakDerivative u i)),
      g.lpPullback_ae 𝕜 p (firstWeakDerivative u i)] with x hm hc
    simp only [derivativeEntryMultiplier, hm, hc, Function.comp_apply]
  simp only [derivativePullback, sum_apply, ContinuousLinearMap.comp_apply]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun i =>
    g.derivativeEntryMultiplier 𝕜 p i j (g.lpPullback 𝕜 p (firstWeakDerivative u i))),
    ae_all_iff.mpr he] with x hs hx
  change (∑ i, g.derivativeEntryMultiplier 𝕜 p i j
    (g.lpPullback 𝕜 p (firstWeakDerivative u i))) x = _
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => hx i)

theorem derivativePullback_norm_le (u : Sobolev 𝕜 U 1 p) (j : Fin d) :
    ‖g.derivativePullback 𝕜 p j u‖ ≤
      (L : ℝ) * pullbackLpBound d p M * ∑ i : Fin d, ‖firstWeakDerivative u i‖ := by
  simp only [derivativePullback, sum_apply, ContinuousLinearMap.comp_apply]
  calc
    _ ≤ ∑ i : Fin d, ‖g.derivativeEntryMultiplier 𝕜 p i j
        (g.lpPullback 𝕜 p (firstWeakDerivative u i))‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin d, (L : ℝ) *
        (pullbackLpBound d p M * ‖firstWeakDerivative u i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      exact ((g.derivativeEntryMultiplier 𝕜 p i j).le_opNorm _).trans
        ((mul_le_mul_of_nonneg_right (realMultiplier_norm_le V p _ L _ _) (norm_nonneg _)).trans
          (mul_le_mul_of_nonneg_left
            ((g.lpPullback 𝕜 p).le_opNorm _ |>.trans
              (mul_le_mul_of_nonneg_right (g.lpPullback_norm_le 𝕜 p) (norm_nonneg _)))
            L.coe_nonneg))
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi; ring

/-- Expansion of a real differential in the shared Euclidean coordinate basis. -/
theorem differential_coordinates (D : Space d →L[ℝ] 𝕜) (v : Space d) :
    D v = ∑ i : Fin d, v i • D (coordinateVector d i) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_repr, coordinateVector]

/-- Smooth Sobolev representatives satisfy the coordinate equations after
pullback, for every p including infinity. -/
theorem smooth_sobolev_weak_chain (hd : 0 < d) (u : Sobolev 𝕜 U 1 p)
    (f : Space d → 𝕜) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hfu : RepresentsSobolevOn f u) (j : Fin d) :
    distributionPartial {j} (regularDistribution V
      (g.lpPullback 𝕜 p (sobolevUnderlying u))) =
      regularDistribution V (g.derivativePullback 𝕜 p j u) := by
  have hf1 : ContDiffOn ℝ 1 f U := hf.of_le (by simp)
  have hzero : (sobolevUnderlying u : Space d → 𝕜) =ᵐ[
      volume.restrict (U : Set (Space d))] f := by
    simpa only [sobolevUnderlying, zeroSobolevIndex, multiPartial, Multiset.sort_zero, partialWord]
      using hfu (zeroSobolevIndex d 1)
  have hcoord (i : Fin d) : (firstWeakDerivative u i : Space d → 𝕜) =ᵐ[
      volume.restrict (U : Set (Space d))]
        (fun x => fderiv ℝ f x (coordinateVector d i)) := by
    simpa only [firstWeakDerivative, firstSobolevIndex, multiPartial, Multiset.sort_singleton, partialWord]
      using hfu (firstSobolevIndex i)
  have hsource := g.ae_comp (ae_all_iff.mpr hcoord)
  have he : (fun x => fderiv ℝ f (g.toFun x)
      (chartDerivative g x (coordinateVector d j))) =ᵐ[
        volume.restrict (V : Set (Space d))] (g.derivativePullback 𝕜 p j u) := by
    filter_upwards [g.derivativePullback_ae 𝕜 p u j, hsource] with x hk hx
    rw [hk, differential_coordinates 𝕜]
    exact Finset.sum_congr rfl (fun i _ => congrArg
      (fun t : 𝕜 => chartDerivative g x (coordinateVector d j) i • t) (hx i).symm)
  have hLI := LocallyIntegrableOn.congr he.symm
    (domainLp_locallyIntegrable V p (g.derivativePullback 𝕜 p j u))
  have hfunLI : LocallyIntegrableOn (f ∘ g.toFun) V volume :=
    (g.smooth_comp_locallyLipschitz hf1).continuousOn.locallyIntegrableOn V.isOpen.measurableSet
  have hzero' := (g.lpPullback_ae 𝕜 p (sobolevUnderlying u)).trans (g.ae_comp hzero)
  calc
    _ = distributionPartial {j} (regularDistribution V (f ∘ g.toFun)) :=
      congrArg (distributionPartial {j})
        ((regular_injectivity d 𝕜 V _ _
          (domainLp_locallyIntegrable V p _) hfunLI).mpr hzero')
    _ = _ := (g.smooth_comp_weak_chain hd hf1 j hLI).trans
      ((regular_injectivity d 𝕜 V _ _ hLI
        (domainLp_locallyIntegrable V p _)).mpr he)

end BiLipschitzChart

/-- The weak derivative graph is closed under simultaneous Lp convergence,
including at both endpoints. Each test gives a continuous scalar equation. -/
theorem weakDerivative_closed {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (V : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : Fin d)
    (u v : ℕ → DomainLp 𝕜 V p) (u₀ v₀ : DomainLp 𝕜 V p)
    (hu : Tendsto u atTop (𝓝 u₀)) (hv : Tendsto v atTop (𝓝 v₀))
    (h : ∀ n, distributionPartial {j} (regularDistribution V (u n)) =
      regularDistribution V (v n)) :
    distributionPartial {j} (regularDistribution V u₀) = regularDistribution V v₀ := by
  apply (distributionPartial_eq_regularLp_iff V p {j} u₀ v₀).mpr
  intro φ
  have hleft := ((lpTestPairing V p φ).continuous.tendsto v₀).comp hv
  have hright := (tendsto_const_nhds (x := (-1 : 𝕜) ^ ({j} : MultiIndex d).card)).mul
    (((lpTestPairing V p (testPartialWord V (({j} : MultiIndex d).sort (· ≤ ·)) φ)).continuous.tendsto u₀).comp hu)
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Eventually.of_forall fun n =>
    ((distributionPartial_eq_regularLp_iff V p {j} (u n) (v n)).mp (h n) φ).symm)

/-- Finite-exponent passage from smooth approximation to the full weak
coordinate identity. This uses the exact arbitrary-open density premise. -/
theorem bilipschitz_weak_chain_finite
    (hSmooth : MeyersSerrinExpected.SmoothDensity)
    {d : ℕ} (hd : 0 < d) {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (L M : ℝ≥0) (g : BiLipschitzChart U V L M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) (u : Sobolev 𝕜 U 1 p) (j : Fin d) :
    distributionPartial {j} (regularDistribution V
      (g.lpPullback 𝕜 p (sobolevUnderlying u))) =
      regularDistribution V (g.derivativePullback 𝕜 p j u) := by
  obtain ⟨f, v, hfv, hv, herr⟩ := hSmooth U 1 p hp u
  let C : Sobolev 𝕜 U 1 p →L[𝕜] DomainLp 𝕜 V p :=
    (g.lpPullback 𝕜 p).comp (sobolevUnderlyingCLM U 1 p)
  exact weakDerivative_closed V p j (fun n => C (v n))
    (fun n => g.derivativePullback 𝕜 p j (v n)) (C u) _
    ((C.continuous.tendsto u).comp hv)
    (((g.derivativePullback 𝕜 p j).continuous.tendsto u).comp hv)
    (fun n => g.smooth_sobolev_weak_chain 𝕜 p hd (v n) (f n) (hfv n).1 (hfv n).2 j)

/-- Changing the ambient open does not change a regular pairing with the
same compactly supported test. Local integrability is required on both opens. -/
theorem regular_test_change {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U W : Opens (Space d)) (f : Space d → 𝕜)
    (hU : LocallyIntegrableOn f U volume) (hW : LocallyIntegrableOn f W volume)
    (φ : TestSpace 𝕜 U) (ψ : TestSpace 𝕜 W)
    (he : (φ : Space d → 𝕜) = ψ) :
    regularDistribution U f φ = regularDistribution W f ψ := by
  unfold regularDistribution
  rw [TestFunction.integralAgainstBilinCLM_eq_integral hU,
    TestFunction.integralAgainstBilinCLM_eq_integral hW, he]

theorem partial_regular_test_change {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U W : Opens (Space d)) (f : Space d → 𝕜)
    (hU : LocallyIntegrableOn f U volume) (hW : LocallyIntegrableOn f W volume)
    (j : Fin d) (φ : TestSpace 𝕜 U) (ψ : TestSpace 𝕜 W)
    (he : (φ : Space d → 𝕜) = ψ) :
    distributionPartial {j} (regularDistribution U f) φ =
      distributionPartial {j} (regularDistribution W f) ψ := by
  simp only [distributionPartial, Multiset.card_singleton, pow_one,
    Multiset.sort_singleton, ContinuousLinearMap.comp_apply, smul_apply, neg_smul, one_smul]
  congr 1
  apply regular_test_change U W f hU hW
  ext x
  simp only [testPartialWord_coe, partialWord, he]

/-- Restriction of a weak coordinate equation, using the same ambient
representatives. -/
theorem weakDerivative_restrict {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U W : Opens (Space d)} (hWU : W ≤ U) (f k : Space d → 𝕜)
    (hf : LocallyIntegrableOn f U volume) (hk : LocallyIntegrableOn k U volume)
    (j : Fin d)
    (h : distributionPartial {j} (regularDistribution U f) = regularDistribution U k) :
    distributionPartial {j} (regularDistribution W f) = regularDistribution W k := by
  ext φ
  let ψ : TestSpace 𝕜 U :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hWU⟩
  calc
    _ = distributionPartial {j} (regularDistribution U f) ψ :=
      (partial_regular_test_change U W f hf (hf.mono_set hWU) j ψ φ rfl).symm
    _ = regularDistribution U k ψ := congrArg (fun T : DistributionSpace 𝕜 U => T ψ) h
    _ = _ := regular_test_change U W k hk (hk.mono_set hWU) ψ φ rfl

/-- On a relatively compact open subset, every global W^{1,p} class,
including p = infinity, defines a W^{1,1} class with the same weak derivatives. -/
theorem exists_localL1Sobolev {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {U : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 U 1 p) (W : Opens (Space d))
    (hWc : IsCompact (closure (W : Set (Space d))))
    (hWU : closure (W : Set (Space d)) ⊆ U) :
    ∃ v : Sobolev 𝕜 W 1 1,
      sobolevUnderlying v =ᵐ[volume.restrict (W : Set (Space d))] sobolevUnderlying u ∧
      ∀ j : Fin d, firstWeakDerivative v j =ᵐ[
        volume.restrict (W : Set (Space d))] firstWeakDerivative u j := by
  have hsub : W ≤ U := subset_closure.trans hWU
  have hm (z : DomainLp 𝕜 U p) : MemLp z 1 (volume.restrict (W : Set (Space d))) :=
    memLp_one_iff_integrable.mpr
      (((domainLp_locallyIntegrable U p z).integrableOn_compact_subset hWU hWc).mono_set
        subset_closure)
  let z : DomainLp 𝕜 W 1 := (hm (sobolevUnderlying u)).toLp _
  let k : Fin d → DomainLp 𝕜 W 1 := fun j => (hm (firstWeakDerivative u j)).toLp _
  have hz : z =ᵐ[volume.restrict (W : Set (Space d))] sobolevUnderlying u :=
    (hm (sobolevUnderlying u)).coeFn_toLp
  have hk (j : Fin d) : k j =ᵐ[volume.restrict (W : Set (Space d))] firstWeakDerivative u j :=
    (hm (firstWeakDerivative u j)).coeFn_toLp
  have he (j : Fin d) : distributionPartial {j} (regularDistribution W z) =
      regularDistribution W (k j) := by
    have hL0 := (domainLp_locallyIntegrable U p (sobolevUnderlying u)).mono_set hsub
    have hLj := (domainLp_locallyIntegrable U p (firstWeakDerivative u j)).mono_set hsub
    calc
      _ = distributionPartial {j} (regularDistribution W (sobolevUnderlying u)) :=
        congrArg (distributionPartial {j})
          ((regular_injectivity d 𝕜 W _ _ (domainLp_locallyIntegrable W 1 _) hL0).mpr hz)
      _ = regularDistribution W (firstWeakDerivative u j) :=
        weakDerivative_restrict hsub _ _ (domainLp_locallyIntegrable U p _)
          (domainLp_locallyIntegrable U p _) j
          (sobolev_derivative_distribution U 1 p u (firstSobolevIndex j))
      _ = _ := ((regular_injectivity d 𝕜 W _ _ (domainLp_locallyIntegrable W 1 _) hLj).mpr (hk j)).symm
  obtain ⟨v, hv, hvj⟩ := firstOrder_graph W 1 z k he
  exact ⟨v, hv ▸ hz, fun j => hvj j ▸ hk j⟩

namespace BiLipschitzChart
variable {d : ℕ} {U V : Opens (Space d)} {L M : ℝ≥0}
  (g : BiLipschitzChart U V L M)

def preimageOpen (W : Opens (Space d)) : Opens (Space d) :=
  ⟨(V : Set (Space d)) ∩ g.toFun ⁻¹' (W : Set (Space d)),
    g.lipschitz.continuousOn.isOpen_inter_preimage V.isOpen W.isOpen⟩

def restrict (W : Opens (Space d)) (hWU : W ≤ U) :
    BiLipschitzChart W (g.preimageOpen W) L M where
  toFun := g.toFun
  invFun := g.invFun
  mapsTo := fun x hx => hx.2
  inv_mapsTo := fun y hy => ⟨g.inv_mapsTo (hWU hy), by
    change g.toFun (g.invFun y) ∈ W
    rwa [g.right_inv y (hWU hy)]⟩
  left_inv := fun x hx => g.left_inv x hx.1
  right_inv := fun y hy => g.right_inv y (hWU hy)
  lipschitz := g.lipschitz.mono inter_subset_left
  inv_lipschitz := g.inv_lipschitz.mono hWU
end BiLipschitzChart

/-- The weak coordinate identity for all exponents. Each test is contained in
the preimage of a relatively compact target open. Restriction there gives a
W^{1,1} class, to which finite-exponent approximation applies. -/
theorem bilipschitz_weak_chain
    (hSmooth : MeyersSerrinExpected.SmoothDensity)
    {d : ℕ} (hd : 0 < d) {𝕜 : Type} [RCLike 𝕜]
    (U V : Opens (Space d)) (L M : ℝ≥0) (g : BiLipschitzChart U V L M)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 U 1 p) (j : Fin d) :
    distributionPartial {j} (regularDistribution V
      (g.lpPullback 𝕜 p (sobolevUnderlying u))) =
      regularDistribution V (g.derivativePullback 𝕜 p j u) := by
  ext φ
  have hKc : IsCompact (g.toFun '' tsupport φ) :=
    φ.hasCompactSupport.image_of_continuousOn
      (g.lipschitz.continuousOn.mono φ.tsupport_subset)
  have hKU : g.toFun '' tsupport φ ⊆ (U : Set (Space d)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact g.mapsTo (φ.tsupport_subset hx)
  obtain ⟨Wset, hWo, hKW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hKc U.isOpen hKU
  let W : Opens (Space d) := ⟨Wset, hWo⟩
  have hsub : W ≤ U := subset_closure.trans hWU
  let Z := g.preimageOpen W
  let g' : BiLipschitzChart W Z L M := g.restrict W hsub
  have hZV : Z ≤ V := inter_subset_left
  let ψ : TestSpace 𝕜 Z := ⟨φ, φ.contDiff, φ.hasCompactSupport, by
    intro x hx
    exact ⟨φ.tsupport_subset hx, hKW ⟨x, hx, rfl⟩⟩⟩
  obtain ⟨v, hv0, hvj⟩ := exists_localL1Sobolev u W hWc hWU
  let z₁ := g'.lpPullback 𝕜 1 (sobolevUnderlying v)
  let k₁ := g'.derivativePullback 𝕜 1 j v
  let z := g.lpPullback 𝕜 p (sobolevUnderlying u)
  let k := g.derivativePullback 𝕜 p j u
  have hzae : (z₁ : Space d → 𝕜) =ᵐ[volume.restrict (Z : Set (Space d))] z :=
    ((g'.lpPullback_ae 𝕜 1 (sobolevUnderlying v)).trans (g'.ae_comp hv0)).trans
      ((g.lpPullback_ae 𝕜 p (sobolevUnderlying u)).filter_mono
        (ae_mono (volume.restrict_mono_set hZV))).symm
  have hkae : (k₁ : Space d → 𝕜) =ᵐ[volume.restrict (Z : Set (Space d))] k := by
    filter_upwards [g'.derivativePullback_ae 𝕜 1 v j,
      g'.ae_comp (ae_all_iff.mpr hvj),
      (g.derivativePullback_ae 𝕜 p u j).filter_mono
        (ae_mono (volume.restrict_mono_set hZV))] with x hnew hsource hold
    rw [hnew, hold]
    exact Finset.sum_congr rfl (fun i _ => congrArg
      (fun t : 𝕜 => chartDerivative g x (coordinateVector d j) i • t) (hsource i))
  have hzLI : LocallyIntegrableOn z V volume := domainLp_locallyIntegrable V p z
  have hkLI : LocallyIntegrableOn k V volume := domainLp_locallyIntegrable V p k
  have he : distributionPartial {j} (regularDistribution Z z) = regularDistribution Z k := by
    calc
      _ = distributionPartial {j} (regularDistribution Z z₁) :=
        congrArg (distributionPartial {j})
          ((regular_injectivity d 𝕜 Z _ _ (domainLp_locallyIntegrable Z 1 z₁)
            (hzLI.mono_set hZV)).mpr hzae).symm
      _ = regularDistribution Z k₁ :=
        bilipschitz_weak_chain_finite hSmooth hd W Z L M g' 1 (by simp) v j
      _ = _ := (regular_injectivity d 𝕜 Z _ _
        (domainLp_locallyIntegrable Z 1 k₁) (hkLI.mono_set hZV)).mpr hkae
  calc
    _ = distributionPartial {j} (regularDistribution Z z) ψ :=
      partial_regular_test_change V Z z hzLI (hzLI.mono_set hZV) j φ ψ rfl
    _ = regularDistribution Z k ψ := congrArg (fun T : DistributionSpace 𝕜 Z => T ψ) he
    _ = _ := (regular_test_change V Z k hkLI (hkLI.mono_set hZV) φ ψ rfl).symm

namespace BiLipschitzPullback

/-- Order-one multi-indices consist of zero and the single coordinate indices. -/
def firstOrderIndexEquiv (d : ℕ) : Option (Fin d) ≃ SobolevIndex d 1 :=
  Equiv.ofBijective (fun o => match o with
    | none => zeroSobolevIndex d 1
    | some i => firstSobolevIndex i) (by
      constructor
      · intro a b h
        cases a with
        | none =>
          cases b with
          | none => rfl
          | some j =>
            have hh : (0 : MultiIndex d) = {j} := congrArg Subtype.val h
            have hc := congrArg Multiset.card hh
            simp at hc
        | some i =>
          cases b with
          | none =>
            have hh : ({i} : MultiIndex d) = 0 := congrArg Subtype.val h
            have hc := congrArg Multiset.card hh
            simp at hc
          | some j =>
            have hh : ({i} : MultiIndex d) = {j} := congrArg Subtype.val h
            exact congrArg some (Multiset.singleton_inj.mp hh)
      · intro α
        by_cases hzero : α.val = 0
        · exact ⟨none, Subtype.ext hzero.symm⟩
        · have hcard : α.val.card = 1 := by
            have hne := Multiset.card_eq_zero.not.mpr hzero
            have := α.property
            omega
          obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp hcard
          exact ⟨some j, Subtype.ext hj.symm⟩)

theorem sobolev_firstOrder_norm {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (U : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 U 1 p) :
    ‖u‖ = ‖sobolevUnderlying u‖ + ∑ j : Fin d, ‖firstWeakDerivative u j‖ := by
  rw [sobolev_norm U 1 p u, ← (firstOrderIndexEquiv d).sum_comp,
    Fintype.sum_option]
  rfl

end BiLipschitzPullback

namespace BiLipschitzChart
variable (hSmooth : MeyersSerrinExpected.SmoothDensity)
  {d : ℕ} (hd : 0 < d) {U V : Opens (Space d)} {L M : ℝ≥0}
  (g : BiLipschitzChart U V L M) (𝕜 : Type) [RCLike 𝕜]
  (p : ℝ≥0∞) [Fact (1 ≤ p)]
include hSmooth hd

private theorem exists_sobolevPullback (u : Sobolev 𝕜 U 1 p) :
    ∃ w : Sobolev 𝕜 V 1 p,
      sobolevUnderlying w = g.lpPullback 𝕜 p (sobolevUnderlying u) ∧
      ∀ j, firstWeakDerivative w j = g.derivativePullback 𝕜 p j u :=
  firstOrder_graph V p (g.lpPullback 𝕜 p (sobolevUnderlying u))
    (fun j => g.derivativePullback 𝕜 p j u)
    (fun j => bilipschitz_weak_chain hSmooth hd U V L M g p u j)

private def sobolevPullbackValue (u : Sobolev 𝕜 U 1 p) : Sobolev 𝕜 V 1 p :=
  Classical.choose (g.exists_sobolevPullback hSmooth hd 𝕜 p u)

private theorem sobolevPullbackValue_underlying (u : Sobolev 𝕜 U 1 p) :
    sobolevUnderlying (g.sobolevPullbackValue hSmooth hd 𝕜 p u) =
      g.lpPullback 𝕜 p (sobolevUnderlying u) :=
  (Classical.choose_spec (g.exists_sobolevPullback hSmooth hd 𝕜 p u)).1

private theorem sobolevPullbackValue_derivative (u : Sobolev 𝕜 U 1 p) (j : Fin d) :
    firstWeakDerivative (g.sobolevPullbackValue hSmooth hd 𝕜 p u) j =
      g.derivativePullback 𝕜 p j u :=
  (Classical.choose_spec (g.exists_sobolevPullback hSmooth hd 𝕜 p u)).2 j

private def sobolevPullbackLinear : Sobolev 𝕜 U 1 p →ₗ[𝕜] Sobolev 𝕜 V 1 p where
  toFun := g.sobolevPullbackValue hSmooth hd 𝕜 p
  map_add' u v := by
    apply sobolevUnderlying_injective V 1 p
    rw [g.sobolevPullbackValue_underlying hSmooth hd 𝕜 p]
    calc
      _ = g.lpPullback 𝕜 p (sobolevUnderlying u + sobolevUnderlying v) := rfl
      _ = g.lpPullback 𝕜 p (sobolevUnderlying u) + g.lpPullback 𝕜 p (sobolevUnderlying v) := map_add _ _ _
      _ = sobolevUnderlying (g.sobolevPullbackValue hSmooth hd 𝕜 p u) +
          sobolevUnderlying (g.sobolevPullbackValue hSmooth hd 𝕜 p v) := by
        rw [g.sobolevPullbackValue_underlying hSmooth hd 𝕜 p,
          g.sobolevPullbackValue_underlying hSmooth hd 𝕜 p]
      _ = _ := rfl
  map_smul' c u := by
    apply sobolevUnderlying_injective V 1 p
    rw [g.sobolevPullbackValue_underlying hSmooth hd 𝕜 p]
    calc
      _ = g.lpPullback 𝕜 p (c • sobolevUnderlying u) := rfl
      _ = c • g.lpPullback 𝕜 p (sobolevUnderlying u) := map_smul _ _ _
      _ = c • sobolevUnderlying (g.sobolevPullbackValue hSmooth hd 𝕜 p u) := by
        rw [g.sobolevPullbackValue_underlying hSmooth hd 𝕜 p]
      _ = _ := rfl

private theorem sobolevPullbackLinear_norm_le (u : Sobolev 𝕜 U 1 p) :
    ‖g.sobolevPullbackLinear hSmooth hd 𝕜 p u‖ ≤ pullbackSobolevBound d p L M * ‖u‖ := by
  have hB : 0 ≤ pullbackLpBound d p M := Real.rpow_nonneg (by positivity) _
  have hn : 0 ≤ ∑ i : Fin d, ‖firstWeakDerivative u i‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have h₀ : ‖sobolevUnderlying u‖ ≤ ‖u‖ := by
    rw [BiLipschitzPullback.sobolev_firstOrder_norm U p u]
    exact le_add_of_nonneg_right hn
  have h₁ : (∑ i : Fin d, ‖firstWeakDerivative u i‖) ≤ ‖u‖ := by
    rw [BiLipschitzPullback.sobolev_firstOrder_norm U p u]
    exact le_add_of_nonneg_left (norm_nonneg _)
  change ‖g.sobolevPullbackValue hSmooth hd 𝕜 p u‖ ≤ _
  rw [BiLipschitzPullback.sobolev_firstOrder_norm V p,
    g.sobolevPullbackValue_underlying hSmooth hd 𝕜 p]
  simp only [g.sobolevPullbackValue_derivative hSmooth hd 𝕜 p]
  calc
    _ ≤ pullbackLpBound d p M * ‖sobolevUnderlying u‖ +
        ∑ j : Fin d, ((L : ℝ) * pullbackLpBound d p M *
          ∑ i : Fin d, ‖firstWeakDerivative u i‖) :=
      add_le_add
        (((g.lpPullback 𝕜 p).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (g.lpPullback_norm_le 𝕜 p) (norm_nonneg _)))
        (Finset.sum_le_sum fun j _ => g.derivativePullback_norm_le 𝕜 p u j)
    _ = pullbackLpBound d p M * ‖sobolevUnderlying u‖ +
        (d : ℝ) * ((L : ℝ) * pullbackLpBound d p M *
          ∑ i : Fin d, ‖firstWeakDerivative u i‖) := by simp
    _ ≤ pullbackLpBound d p M * ‖u‖ +
        (d : ℝ) * ((L : ℝ) * pullbackLpBound d p M * ‖u‖) :=
      add_le_add (mul_le_mul_of_nonneg_left h₀ hB)
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₁ (mul_nonneg L.coe_nonneg hB))
          (Nat.cast_nonneg d))
    _ = _ := by unfold pullbackSobolevBound; ring

/-- The bounded linear Sobolev pullback constructed using the density premise. -/
def sobolevPullback : Sobolev 𝕜 U 1 p →L[𝕜] Sobolev 𝕜 V 1 p :=
  (g.sobolevPullbackLinear hSmooth hd 𝕜 p).mkContinuous (pullbackSobolevBound d p L M)
    (g.sobolevPullbackLinear_norm_le hSmooth hd 𝕜 p)

theorem sobolevPullback_underlying (u : Sobolev 𝕜 U 1 p) :
    sobolevUnderlying (g.sobolevPullback hSmooth hd 𝕜 p u) =
      g.lpPullback 𝕜 p (sobolevUnderlying u) :=
  g.sobolevPullbackValue_underlying hSmooth hd 𝕜 p u

theorem sobolevPullback_derivative (u : Sobolev 𝕜 U 1 p) (j : Fin d) :
    firstWeakDerivative (g.sobolevPullback hSmooth hd 𝕜 p u) j =
      g.derivativePullback 𝕜 p j u :=
  g.sobolevPullbackValue_derivative hSmooth hd 𝕜 p u j

theorem sobolevPullback_norm_le :
    ‖g.sobolevPullback hSmooth hd 𝕜 p‖ ≤ pullbackSobolevBound d p L M :=
  LinearMap.mkContinuous_norm_le _
    (mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)) _

end BiLipschitzChart

theorem bilipschitz_sobolevPullback_conditional
    (hSmooth : MeyersSerrinExpected.SmoothDensity)
    (_hWhole : MeyersSerrinExpected.WholeSpaceDensity)
    (_hZero : MeyersSerrinExpected.ZeroExtension) : BiLipschitzPullbackExpected.SobolevPullback := by
  intro d hd 𝕜 _ U V L M g p _
  refine ⟨g.sobolevPullback hSmooth hd 𝕜 p, ?_, ?_, g.sobolevPullback_norm_le hSmooth hd 𝕜 p⟩
  · intro u
    rw [g.sobolevPullback_underlying hSmooth hd 𝕜 p]
    exact g.lpPullback_ae 𝕜 p (sobolevUnderlying u)
  · intro u j
    rw [g.sobolevPullback_derivative hSmooth hd 𝕜 p]
    exact g.derivativePullback_ae 𝕜 p u j

/-- Conditional draft; the full ordered density premises are retained even
for this clause, whose proof does not need approximation. -/
theorem bilipschitz_distortion_conditional
    (_hSmooth : MeyersSerrinExpected.SmoothDensity)
    (_hWhole : MeyersSerrinExpected.WholeSpaceDensity)
    (_hZero : MeyersSerrinExpected.ZeroExtension) : BiLipschitzPullbackExpected.Distortion := by
  intro d hd U V L M g
  exact ⟨g.preimage_volume_le, g.symm.preimage_volume_le,
    fun _ hE hnull => g.image_null hE hnull,
    fun _ hE hnull => g.symm.image_null hE hnull⟩

theorem bilipschitz_lpPullback_conditional
    (_hSmooth : MeyersSerrinExpected.SmoothDensity)
    (_hWhole : MeyersSerrinExpected.WholeSpaceDensity)
    (_hZero : MeyersSerrinExpected.ZeroExtension) : BiLipschitzPullbackExpected.LpPullback := by
  intro d hd 𝕜 _ U V L M g p _
  exact ⟨fun f hf => ⟨g.memLp_comp hf, g.eLpNorm_comp_le hf⟩,
    g.lpPullback 𝕜 p, g.lpPullback_ae 𝕜 p, g.lpPullback_norm_le 𝕜 p⟩

/-- The canonical Fréchet derivative is the same a.e. matrix as in the
authorized Rademacher interface. -/
theorem bilipschitz_derivative_conditional
    (_hSmooth : MeyersSerrinExpected.SmoothDensity)
    (_hWhole : MeyersSerrinExpected.WholeSpaceDensity)
    (_hZero : MeyersSerrinExpected.ZeroExtension) : BiLipschitzPullbackExpected.Derivative := by
  intro d hd U V L M g
  have hlocal : LocallyLipschitzOn (V : Set (Space d)) g.toFun :=
    fun _x _hx => ⟨L, V, self_mem_nhdsWithin, g.lipschitz⟩
  obtain ⟨A, hAm, hAd, hAw, hAl, hAb⟩ := rademacher d hd d V g.toFun hlocal
  have hAe : chartDerivative g =ᵐ[volume.restrict (V : Set (Space d))] A := by
    filter_upwards [hAd] with x hx
    exact hx.fderiv
  refine ⟨measurable_fderiv ℝ g.toFun, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hAd, hAe] with x hx he
    simpa only [he] using hx
  · intro i j
    have he : (fun x => (A x (coordinateVector d j)) i) =ᵐ[
        volume.restrict (V : Set (Space d))]
        (fun x => (chartDerivative g x (coordinateVector d j)) i) := by
      filter_upwards [hAe] with x hx using congrArg (fun B => B (coordinateVector d j) i) hx.symm
    have hLI := LocallyIntegrableOn.congr he (hAw i j).1
    refine ⟨hLI, (hAw i j).2.trans ?_⟩
    exact (regular_injectivity d ℝ V _ _ (hAw i j).1 hLI).mpr he
  · exact fderiv_memLp_top_on_open V g.lipschitz
  · filter_upwards [ae_restrict_mem V.isOpen.measurableSet] with x hx
    exact norm_fderiv_le_of_lipschitzOn ℝ (V.isOpen.mem_nhds hx) g.lipschitz

end P102.U4

theorem _root_.«P102».«U4».«bilipschitz_derivative» : _root_.«P102».«U4».«BiLipschitzPullbackExpected».«Derivative» :=
  @_root_.«P102».«U4».«bilipschitz_derivative_conditional» (@_root_.«P102».«U4».«meyersSerrin_smoothDensity») (@_root_.«P102».«U4».«meyersSerrin_wholeSpaceDensity») (@_root_.«P102».«U4».«meyersSerrin_zeroExtension»)
theorem _root_.«P102».«U4».«bilipschitz_distortion» : _root_.«P102».«U4».«BiLipschitzPullbackExpected».«Distortion» :=
  @_root_.«P102».«U4».«bilipschitz_distortion_conditional» (@_root_.«P102».«U4».«meyersSerrin_smoothDensity») (@_root_.«P102».«U4».«meyersSerrin_wholeSpaceDensity») (@_root_.«P102».«U4».«meyersSerrin_zeroExtension»)
theorem _root_.«P102».«U4».«bilipschitz_lpPullback» : _root_.«P102».«U4».«BiLipschitzPullbackExpected».«LpPullback» :=
  @_root_.«P102».«U4».«bilipschitz_lpPullback_conditional» (@_root_.«P102».«U4».«meyersSerrin_smoothDensity») (@_root_.«P102».«U4».«meyersSerrin_wholeSpaceDensity») (@_root_.«P102».«U4».«meyersSerrin_zeroExtension»)
theorem _root_.«P102».«U4».«bilipschitz_sobolevPullback» : _root_.«P102».«U4».«BiLipschitzPullbackExpected».«SobolevPullback» :=
  @_root_.«P102».«U4».«bilipschitz_sobolevPullback_conditional» (@_root_.«P102».«U4».«meyersSerrin_smoothDensity») (@_root_.«P102».«U4».«meyersSerrin_wholeSpaceDensity») (@_root_.«P102».«U4».«meyersSerrin_zeroExtension»)
