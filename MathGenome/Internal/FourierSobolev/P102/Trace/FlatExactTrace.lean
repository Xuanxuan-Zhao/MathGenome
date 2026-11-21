import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.FlatExactTrace
import MathGenome.Internal.FourierSobolev.P102.Trace.FlatTrace
import MathGenome.Internal.FourierSobolev.P102.U4.SobolevSpace
import MathGenome.Internal.FourierSobolev.P102.Fractional.Space
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SharpTraceBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SharpTraceExtension

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal Topology

namespace P102.Trace
namespace CoordinateBridge
open P102.U4
open ExpandedFA.Sobolev.HalfSpace

/-- The finite derivative indices agree by their multiplicities. -/
def indexEquiv (d k : ℕ) : SobolevIndex d k ≃ ExpandedFA.Sobolev.DerivativeIndex d k where
  toFun α := ExpandedFA.Sobolev.boundedIndex (multiIndexCountsEquiv d α.val)
    (by rw [← (multiIndexCoordinates d α.val).2]; exact α.property)
  invFun α := ⟨(multiIndexCountsEquiv d).symm (ExpandedFA.Sobolev.natIndex α), by
    rw [(multiIndexCoordinates d _).2, Equiv.apply_symm_apply]
    exact α.property⟩
  left_inv α := Subtype.ext ((multiIndexCountsEquiv d).symm_apply_apply α.val)
  right_inv α := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrFun ((multiIndexCountsEquiv d).apply_symm_apply
      (ExpandedFA.Sobolev.natIndex α)) i

@[simp] theorem indexEquiv_zero (d k : ℕ) :
    indexEquiv d k (zeroSobolevIndex d k) = ExpandedFA.Sobolev.zeroIndex d k := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change Multiset.count i 0 = 0
  simp

@[simp] theorem indexEquiv_single {d : ℕ} (j : Fin d) :
    indexEquiv d 1 ⟨{j}, by simp⟩ = coordinateIndex j := by
  apply derivativeIndex_ext
  funext i
  change Multiset.count i {j} = (Pi.single j 1 : Fin d → ℕ) i
  simp only [Multiset.count_singleton, Pi.single_apply, eq_comm]

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

theorem coordinates_measurePreserving :
    MeasurePreserving (ACL.coordinates d) volume volume :=
  (PiLp.volume_preserving_toLp (Fin d)).symm (MeasurableEquiv.toLp 2 (Fin d → ℝ))

def lpCoordinates (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    DomainLp 𝕜 Ω p →ₗᵢ[𝕜]
      ExpandedFA.Sobolev.DomainLp 𝕜 (ACL.coordinateDomain Ω) p :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (ACL.coordinates d).symm
    ((PiLp.volume_preserving_toLp (Fin d)).restrict_preimage Ω.isOpen.measurableSet)

theorem coordinates_restrict_measurePreserving (Ω : Opens (Space d)) :
    MeasurePreserving (ACL.coordinates d) (volume.restrict (Ω : Set (Space d)))
      (volume.restrict (ACL.coordinateDomain Ω : Set (Fin d → ℝ))) := by
  convert (coordinates_measurePreserving (d := d)).restrict_preimage
    (ACL.coordinateDomain Ω).isOpen.measurableSet using 1
  congr 1

def lpEuclidean (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ExpandedFA.Sobolev.DomainLp 𝕜 (ACL.coordinateDomain Ω) p →ₗᵢ[𝕜] DomainLp 𝕜 Ω p :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (ACL.coordinates d)
    (coordinates_restrict_measurePreserving Ω)

@[simp] theorem lpEuclidean_coordinates (Ω : Opens (Space d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : DomainLp 𝕜 Ω p) :
    lpEuclidean Ω p (lpCoordinates Ω p u) = u := by
  apply Lp.ext
  have h := coordinates_restrict_measurePreserving Ω
  have he := h.quasiMeasurePreserving.ae
    (Lp.coeFn_compMeasurePreserving u
      ((PiLp.volume_preserving_toLp (Fin d)).restrict_preimage Ω.isOpen.measurableSet))
  filter_upwards [Lp.coeFn_compMeasurePreserving (lpCoordinates Ω p u)
    h, he] with x hx hy
  change lpCoordinates Ω p u (ACL.coordinates d x) =
    u ((ACL.coordinates d).symm (ACL.coordinates d x)) at hy
  rw [ContinuousLinearEquiv.symm_apply_apply] at hy
  exact hx.trans hy

@[simp] theorem lpCoordinates_euclidean (Ω : Opens (Space d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : ExpandedFA.Sobolev.DomainLp 𝕜 (ACL.coordinateDomain Ω) p) :
    lpCoordinates Ω p (lpEuclidean Ω p u) = u := by
  apply Lp.ext
  have h := coordinates_restrict_measurePreserving Ω
  have he := ((PiLp.volume_preserving_toLp (Fin d)).restrict_preimage
    Ω.isOpen.measurableSet).quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving u h)
  filter_upwards [Lp.coeFn_compMeasurePreserving (lpEuclidean Ω p u)
    ((PiLp.volume_preserving_toLp (Fin d)).restrict_preimage Ω.isOpen.measurableSet), he]
      with x hx hy
  change lpEuclidean Ω p u ((ACL.coordinates d).symm x) =
    u (ACL.coordinates d ((ACL.coordinates d).symm x)) at hy
  rw [ContinuousLinearEquiv.apply_symm_apply] at hy
  exact hx.trans hy

def lpEquiv (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    DomainLp 𝕜 Ω p ≃ₗᵢ[𝕜] ExpandedFA.Sobolev.DomainLp 𝕜 (ACL.coordinateDomain Ω) p where
  toLinearEquiv :=
    { toLinearMap := (lpCoordinates Ω p).toLinearMap
      invFun := lpEuclidean Ω p
      left_inv := lpEuclidean_coordinates Ω p
      right_inv := lpCoordinates_euclidean Ω p }
  norm_map' := (lpCoordinates Ω p).norm_map

@[simp] theorem lpEquiv_apply (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) : lpEquiv Ω p u = lpCoordinates Ω p u := rfl

/-- Reindexing derivative tuples and changing coordinates preserves their sum norm. -/
def tupleEquiv (Ω : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    SobolevTuple 𝕜 Ω k p ≃ₗᵢ[𝕜]
      ExpandedFA.Sobolev.DerivativeTuple 𝕜 (ACL.coordinateDomain Ω) k p :=
  (LinearIsometryEquiv.piLpCongrLeft 1 𝕜 (DomainLp 𝕜 Ω p) (indexEquiv d k)).trans
    (LinearIsometryEquiv.piLpCongrRight 1 (fun _ => lpEquiv Ω p))

@[simp] theorem tupleEquiv_apply (Ω : Opens (Space d)) (k : ℕ) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : SobolevTuple 𝕜 Ω k p) (α : SobolevIndex d k) :
    tupleEquiv Ω k p u (indexEquiv d k α) = lpCoordinates Ω p (u α) := by
  simp [tupleEquiv, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem lpCoordinates_coe (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) :
    lpCoordinates Ω p u =ᵐ[volume.restrict (ACL.coordinateDomain Ω : Set (Fin d → ℝ))]
      u ∘ (ACL.coordinates d).symm :=
  Lp.coeFn_compMeasurePreserving u
    ((PiLp.volume_preserving_toLp (Fin d)).restrict_preimage Ω.isOpen.measurableSet)

theorem lpCoordinates_coe_reverse (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : DomainLp 𝕜 Ω p) :
    (fun x => lpCoordinates Ω p u (ACL.coordinates d x)) =ᵐ[
      volume.restrict (Ω : Set (Space d))] u := by
  have h := (coordinates_restrict_measurePreserving Ω).quasiMeasurePreserving.ae_eq_comp
    (lpCoordinates_coe Ω p u)
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using h

theorem lpCoordinates_distribution_apply (Ω : Opens (Space d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : DomainLp 𝕜 Ω p)
    (φ : ExpandedFA.Distributions.Tests 𝕜 (ACL.coordinateDomain Ω)) :
    ExpandedFA.Sobolev.lpDistribution (lpCoordinates Ω p u) φ =
      ∫ x, φ x * u ((ACL.coordinates d).symm x) := by
  rw [ExpandedFA.Sobolev.lpDistribution_apply]
  calc
    _ = ∫ x in ACL.coordinateDomain Ω, φ x * u ((ACL.coordinates d).symm x) := by
      apply integral_congr_ae
      filter_upwards [lpCoordinates_coe Ω p u] with x hx
      exact congrArg (φ x * ·) hx
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      simp only [φ.zero_on_compl hx, Pi.zero_apply, zero_mul]

theorem weak_coordinates (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (j : Fin d) (u v : DomainLp 𝕜 Ω p)
    (h : distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v) :
    ExpandedFA.Sobolev.lpDistribution (lpCoordinates Ω p v) =
      -(ExpandedFA.Sobolev.lpDistribution (lpCoordinates Ω p u)).comp
        (ExpandedFA.Distributions.testPartialCLM [j]) := by
  ext φ
  simp only [neg_apply, ContinuousLinearMap.comp_apply, lpCoordinates_distribution_apply]
  exact ACL.weak_identity_coordinates j (domainLp_locallyIntegrable Ω p u)
    (domainLp_locallyIntegrable Ω p v) h φ

theorem tupleEquiv_mem (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω 1 p) :
    tupleEquiv Ω 1 p u.val ∈ ExpandedFA.Sobolev.derivativeGraph 𝕜 (ACL.coordinateDomain Ω) 1 p := by
  apply firstJet_mem_of_coordinateWeak
  intro j
  have hz := tupleEquiv_apply Ω 1 p u.val (zeroSobolevIndex d 1)
  have hj := tupleEquiv_apply Ω 1 p u.val ⟨{j}, by simp⟩
  rw [indexEquiv_zero] at hz
  rw [indexEquiv_single] at hj
  dsimp only
  rw [hz, hj]
  exact weak_coordinates Ω p j _ _
    (sobolev_derivative_distribution Ω 1 p u ⟨{j}, by simp⟩)

/-- Transport back uses the actual ACL derivative representatives, so the
inverse is a weak-derivative map as well as an isometry of ambient tuples. -/
theorem tupleEquiv_mem_reverse (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (v : SobolevTuple 𝕜 Ω 1 p)
    (hv : tupleEquiv Ω 1 p v ∈ ExpandedFA.Sobolev.derivativeGraph 𝕜 (ACL.coordinateDomain Ω) 1 p) :
    v ∈ sobolevSubmodule 𝕜 Ω 1 p := by
  let w : ExpandedFA.Sobolev.SobolevSpace 𝕜 d (ACL.coordinateDomain Ω) 1 p :=
    ⟨tupleEquiv Ω 1 p v, hv⟩
  have hz : w.val (ExpandedFA.Sobolev.zeroIndex d 1) =
      lpCoordinates Ω p (v (zeroSobolevIndex d 1)) := by
    simpa only [indexEquiv_zero] using tupleEquiv_apply Ω 1 p v (zeroSobolevIndex d 1)
  have hj (j : Fin d) : w.val (coordinateIndex j) =
      lpCoordinates Ω p (v ⟨{j}, by simp⟩) := by
    simpa only [indexEquiv_single] using tupleEquiv_apply Ω 1 p v ⟨{j}, by simp⟩
  obtain ⟨f, hf, hacl⟩ := ExpandedFA.Sobolev.Lines.weak_to_acl
    (w.val (ExpandedFA.Sobolev.zeroIndex d 1)) (fun j => w.val (coordinateIndex j))
    (coordinate_weak_derivatives_on w)
  have hrep : (v (zeroSobolevIndex d 1) : Space d → 𝕜) =ᵐ[
      volume.restrict (Ω : Set (Space d))] fun x => f (ACL.coordinates d x) := by
    rw [hz] at hf
    exact (lpCoordinates_coe_reverse Ω p _).symm.trans
      ((coordinates_restrict_measurePreserving Ω).quasiMeasurePreserving.ae_eq_comp hf)
  have hw (j : Fin d) : distributionPartial {j}
      (regularDistribution Ω (v (zeroSobolevIndex d 1))) =
        regularDistribution Ω (v ⟨{j}, by simp⟩) := by
    apply ACL.representative_to_weak j (domainLp_locallyIntegrable Ω p _)
      (domainLp_locallyIntegrable Ω p _)
    refine ⟨fun x => f (ACL.coordinates d x), hrep, ?_⟩
    have hder := lpCoordinates_coe_reverse Ω p (v ⟨{j}, by simp⟩)
    filter_upwards [hacl j, ACL.ae_on_fibers j hder] with z hza hzd
    refine ⟨hza.1, ?_⟩
    rw [hj] at hza
    filter_upwards [hza.2, hzd] with t ht hdt
    exact hdt ▸ ht
  apply (mem_sobolevSubmodule_iff Ω 1 p v).mpr
  intro α φ
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp α.property with h0 | h1
  · have he : α = zeroSobolevIndex d 1 := Subtype.ext (Multiset.card_eq_zero.mp h0)
    subst α
    simp [zeroSobolevIndex, testPartialWord]
  · obtain ⟨j, hj⟩ := Multiset.card_eq_one.mp h1
    have he : α = ⟨{j}, by simp⟩ := Subtype.ext hj
    subst α
    exact (distributionPartial_eq_regularLp_iff Ω p {j} _ _).mp (hw j) φ

/-- The two first-order Sobolev graphs represent precisely the same functions
and derivatives. Both directions preserve the full derivative sum norm. -/
def sobolevEquiv (Ω : Opens (Space d)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Sobolev 𝕜 Ω 1 p ≃ₗᵢ[𝕜]
      ExpandedFA.Sobolev.SobolevSpace 𝕜 d (ACL.coordinateDomain Ω) 1 p where
  toLinearEquiv :=
    { toFun := fun u => ⟨tupleEquiv Ω 1 p u.val, tupleEquiv_mem Ω p u⟩
      invFun := fun v => ⟨(tupleEquiv Ω 1 p).symm v.val,
        tupleEquiv_mem_reverse Ω p _ (by simpa only [LinearIsometryEquiv.apply_symm_apply] using v.property)⟩
      left_inv := fun u => Subtype.ext ((tupleEquiv Ω 1 p).symm_apply_apply u.val)
      right_inv := fun v => Subtype.ext ((tupleEquiv Ω 1 p).apply_symm_apply v.val)
      map_add' := fun u v => Subtype.ext ((tupleEquiv Ω 1 p).map_add u.val v.val)
      map_smul' := fun c u => Subtype.ext ((tupleEquiv Ω 1 p).map_smul c u.val) }
  norm_map' u := (tupleEquiv Ω 1 p).norm_map u.val

@[simp] theorem sobolevEquiv_underlying (Ω : Opens (Space d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω 1 p) :
    (sobolevEquiv Ω p u).val (ExpandedFA.Sobolev.zeroIndex d 1) =
      lpCoordinates Ω p (sobolevUnderlying u) := by
  change tupleEquiv Ω 1 p u.val (ExpandedFA.Sobolev.zeroIndex d 1) =
    lpCoordinates Ω p (u.val (zeroSobolevIndex d 1))
  rw [← indexEquiv_zero d 1]
  exact tupleEquiv_apply Ω 1 p u.val (zeroSobolevIndex d 1)

theorem sobolevEquiv_underlying_reverse (Ω : Opens (Space d)) (p : ℝ≥0∞)
    [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω 1 p) :
    (fun x => (sobolevEquiv Ω p u).val (ExpandedFA.Sobolev.zeroIndex d 1)
      (ACL.coordinates d x)) =ᵐ[volume.restrict (Ω : Set (Space d))] sobolevUnderlying u := by
  rw [sobolevEquiv_underlying]
  exact lpCoordinates_coe_reverse Ω p _

@[simp] theorem coordinate_halfSpace (m : ℕ) :
    ACL.coordinateDomain (halfSpace m) = upper (Fin.last m) := rfl

def halfEquiv (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    HalfSobolev m 𝕜 p ≃ₗᵢ[𝕜]
      ExpandedFA.Sobolev.SobolevSpace 𝕜 (m + 1) (upper (Fin.last m)) 1 p :=
  sobolevEquiv (halfSpace m) p

theorem halfEquiv_underlying_reverse {m : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : HalfSobolev m 𝕜 p) :
    (fun x => (halfEquiv m p u).val (ExpandedFA.Sobolev.zeroIndex (m + 1) 1)
      (ACL.coordinates (m + 1) x)) =ᵐ[
        volume.restrict (halfSpace m : Set (Space (m + 1)))] sobolevUnderlying u :=
  sobolevEquiv_underlying_reverse (halfSpace m) p u

/-- The boundary energy used below is exactly the canonical Gagliardo double
integral of U5, after the volume-preserving Euclidean coordinate change. This
also checks the diagonal convention and the orientation of the increments. -/
theorem fractional_energy_coordinates (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : Lp 𝕜 p (volume : Measure (Fin d → ℝ))) :
    ExpandedFA.PartIV.FractionalSobolev.differenceEnergy s p g =
      P102.Fractional.energy (Set.univ : Set (Space d)) s p
        (fun x => g (ACL.coordinates d x)) := by
  rw [ExpandedFA.PartIV.FractionalSobolev.difference_energy_double_integral]
  let K : Space d × Space d → ℝ≥0∞ := fun z =>
    if z.1 = z.2 then 0 else
      ‖g (ACL.coordinates d z.1) - g (ACL.coordinates d z.2)‖ₑ ^ p.toReal /
        ENNReal.ofReal ‖z.1 - z.2‖ ^ ((d : ℝ) + s * p.toReal)
  have hg : Measurable (fun x : Space d => g (ACL.coordinates d x)) :=
    (Lp.stronglyMeasurable g).measurable.comp (ACL.coordinates d).continuous.measurable
  have hK : Measurable K := by
    apply Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const
    exact (((hg.comp measurable_fst).sub (hg.comp measurable_snd)).enorm.pow_const _).div
      (((measurable_fst.sub measurable_snd).norm.ennreal_ofReal).pow_const _)
  have hmp := PiLp.volume_preserving_toLp (Fin d)
  symm
  change (∫⁻ x, ∫⁻ y, K (x, y) ∂P102.Fractional.domainMeasure Set.univ
    ∂P102.Fractional.domainMeasure Set.univ) = _
  simp only [P102.Fractional.domainMeasure, Measure.restrict_univ]
  rw [← hmp.lintegral_comp hK.lintegral_prod_right']
  apply lintegral_congr
  intro x
  have hmK : Measurable (fun y : Space d => K (WithLp.toLp 2 x, y)) :=
    hK.comp (measurable_const.prodMk measurable_id)
  rw [← hmp.lintegral_comp hmK]
  apply lintegral_congr
  intro y
  dsimp only [K]
  change (if WithLp.toLp 2 x = WithLp.toLp 2 y then 0 else
    ‖g x - g y‖ₑ ^ p.toReal /
      ENNReal.ofReal ‖WithLp.toLp 2 x - WithLp.toLp 2 y‖ ^ ((d : ℝ) + s * p.toReal)) = _
  by_cases hxy : x = y
  · subst y
    simp [ExpandedFA.PartIV.FractionalSobolev.differenceKernel]
  · have hne : WithLp.toLp 2 x ≠ WithLp.toLp 2 y :=
      fun h => hxy (WithLp.toLp_injective 2 h)
    rw [ite_eq_right hne, ExpandedFA.PartIV.FractionalSobolev.differenceKernel,
      ite_eq_right (sub_ne_zero.mpr (Ne.symm hxy))]
    simp only [ExpandedFA.PartIV.FractionalSobolev.euclideanLength, WithLp.toLp_sub,
      norm_sub_rev, enorm_sub_rev, ENNReal.rpow_neg, div_eq_mul_inv, mul_comm]

theorem fractional_full_norm_coordinates (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (g : ExpandedFA.PartIV.FractionalSobolev.FractionalSpace 𝕜 d s p) :
    ExpandedFA.PartIV.FractionalSobolev.fractionalNorm s p g =
      ‖g.val‖ + (P102.Fractional.seminorm (Set.univ : Set (Space d)) s p
        (fun x => g.val (ACL.coordinates d x))).toReal := by
  rw [ExpandedFA.PartIV.FractionalSobolev.fractionalNorm,
    fractional_energy_coordinates, P102.Fractional.seminorm, ENNReal.toReal_rpow]

end CoordinateBridge

open P102.U4 CoordinateBridge

theorem flatTrace_unique (hunique : FlatTraceExpected.SliceUniqueness)
    {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T S : HalfSobolev m 𝕜 p →L[𝕜] BoundaryLp m 𝕜 p)
    (hT : IsFlatTrace T) (hS : IsFlatTrace S) : T = S := by
  apply ContinuousLinearMap.ext
  intro u
  obtain ⟨F, hF, hF0⟩ := hT u
  obtain ⟨G, hG, hG0⟩ := hS u
  exact hF0.symm.trans ((hunique m 𝕜 p u F G hF hG (by simp)).trans hG0)

/-- Every slice trace inherits compatibility with continuous representatives
from the ordinary trace, by uniqueness at height zero. -/
theorem flatTrace_compatibility
    (hexists : FlatTraceExpected.TraceExists)
    (hunique : FlatTraceExpected.SliceUniqueness)
    {m : ℕ} (hm : 1 ≤ m) {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (T : HalfSobolev m 𝕜 p →L[𝕜] BoundaryLp m 𝕜 p)
    (hT : IsFlatTrace T) (u : HalfSobolev m 𝕜 p) (f : Space (m + 1) → 𝕜)
    (hf : ContinuousOn f {x | 0 ≤ x (Fin.last m)})
    (hu : sobolevUnderlying u =ᵐ[volume.restrict
      (halfSpace m : Set (Space (m + 1)))] f) :
    (fun z : Boundary m => T u z) =ᵐ[volume] fun z => f (point m z 0) := by
  obtain ⟨_, _, S, _, hS, hcompat⟩ := hexists m hm 𝕜 p hp
  have hflat : IsFlatTrace S := fun u => by
    obtain ⟨F, hF, h0, _⟩ := hS u
    exact ⟨F, hF, h0⟩
  rw [flatTrace_unique hunique T S hT hflat]
  exact hcompat u f hf hu

/-- The transported map satisfies the library's actual smooth agreement
predicate; hence its sharp estimate applies to the original flat trace. -/
theorem transportedTrace_condition
    (hexists : FlatTraceExpected.TraceExists)
    (hunique : FlatTraceExpected.SliceUniqueness)
    {m : ℕ} (hm : 1 ≤ m) {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (T : HalfSobolev m 𝕜 p →L[𝕜] BoundaryLp m 𝕜 p)
    (hT : IsFlatTrace T) :
    ExpandedFA.PartIV.SharpTraceBound.CoordinateTraceCondition (Fin.last m)
      (T.comp (halfEquiv m p).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  intro v f hf hv
  let u := (halfEquiv m p).symm v
  have he : halfEquiv m p u = v := (halfEquiv m p).apply_symm_apply v
  have hrep : sobolevUnderlying u =ᵐ[volume.restrict
      (halfSpace m : Set (Space (m + 1)))] fun x => f (ACL.coordinates (m + 1) x) := by
    have hr := halfEquiv_underlying_reverse p u
    rw [he] at hr
    exact hr.symm.trans ((coordinates_restrict_measurePreserving (halfSpace m)).quasiMeasurePreserving.ae_eq_comp hv)
  exact flatTrace_compatibility hexists hunique hm hp T hT u
    (fun x => f (ACL.coordinates (m + 1) x))
    ((hf.continuous.comp (ACL.coordinates (m + 1)).continuous).continuousOn) hrep

/-- Assemble the sharp estimate and the scalar-linear lift for the same slice
trace, using ordinary trace existence and uniqueness. -/
theorem exact_flat_trace_conditional
    (hexists : FlatTraceExpected.TraceExists)
    (hunique : FlatTraceExpected.SliceUniqueness)
    :
    FlatExactTraceExpected.ExactFlatTrace := by
  intro m hm p _ hp1 hp
  have : Fact (p ≠ ∞) := ⟨hp⟩
  obtain ⟨Ct, hCt, hbound⟩ := ExpandedFA.PartIV.SharpTraceBound.sharp_trace_bound m p hp1 hp
  obtain ⟨Cl, hCl, hlift⟩ := ExpandedFA.PartIV.SharpTraceExtension.bounded_right_inverse m p hp1 hp
  refine ⟨max Ct Cl, hCt.trans (le_max_left _ _), ?_⟩
  intro 𝕜 _
  constructor
  · obtain ⟨_, _, T, _, hT, _⟩ := hexists m hm 𝕜 p hp
    refine ⟨T, fun u => ?_⟩
    obtain ⟨F, hF, h0, _⟩ := hT u
    exact ⟨F, hF, h0⟩
  · intro T hT
    let e := halfEquiv (𝕜 := 𝕜) m p
    let S := T.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hS : ExpandedFA.PartIV.SharpTraceBound.CoordinateTraceCondition (Fin.last m) S :=
      transportedTrace_condition hexists hunique hm hp T hT
    have htrace (u : HalfSobolev m 𝕜 p) :
        ExpandedFA.PartIV.SharpTraceBound.reindexedTrace (Fin.last m) S (e u) =
          ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p (T u) := by
      change ExpandedFA.PartIV.SharpTraceBound.boundaryPullback (Fin.last m) p
        (T (e.symm (e u))) = _
      rw [e.symm_apply_apply]
    constructor
    · intro u
      have hbnd := (hbound 𝕜 (Fin.last m)).2 S hS (e u)
      simp only [htrace, e.norm_map] at hbnd
      obtain ⟨h, hb⟩ := hbnd
      refine ⟨h, hb.trans ?_⟩
      exact mul_le_mul_of_nonneg_right (le_max_left Ct Cl) (norm_nonneg u)
    · obtain ⟨E, hAdd, hSmul, hNorm, hTrace⟩ := hlift 𝕜 (Fin.last m)
      let Elinear : ExpandedFA.PartIV.FractionalSobolev.FractionalSpace
          𝕜 m (1 - 1 / p.toReal) p →ₗ[𝕜]
          ExpandedFA.Sobolev.SobolevSpace 𝕜 (m + 1)
            (ExpandedFA.Sobolev.HalfSpace.upper (Fin.last m)) 1 p :=
        { toFun := E
          map_add' := fun u v => hAdd u v (u + v) rfl
          map_smul' := fun c u => hSmul c u (c • u) rfl }
      let Econtinuous := Elinear.mkContinuous Cl hNorm
      let L := e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp Econtinuous
      refine ⟨L, ?_, ?_⟩
      · intro g
        change ‖e.symm (E g)‖ ≤ _
        rw [e.symm.norm_map]
        exact (hNorm g).trans (mul_le_mul_of_nonneg_right (le_max_right Ct Cl)
          (ExpandedFA.PartIV.FractionalSobolev.fractionalNorm_nonneg _ _ g))
      · intro g
        exact hTrace S hS g

/-- For finite 1 < p and positive boundary dimension, the existing flat trace
has the full Gagliardo norm bound and a bounded linear right inverse. -/
theorem exact_flat_trace : FlatExactTraceExpected.ExactFlatTrace :=
  exact_flat_trace_conditional flat_trace_exists slice_unique

end P102.Trace
