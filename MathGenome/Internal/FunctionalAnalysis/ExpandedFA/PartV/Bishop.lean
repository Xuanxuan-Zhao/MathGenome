import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.Bishop
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.AntisymmetricSets
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C24KreinMilman
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C05NormExtension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

set_option maxHeartbeats 400000

noncomputable section
namespace ExpandedFA.PartV.Bishop
open Set MeasureTheory Filter
open scoped ENNReal Topology ZeroAtInfty
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
open ExpandedFA.FunctionSpaces.ScalarRieszMarkov
open AntisymmetricSetsSpec AntisymmetricSets
universe u
variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]

private abbrev lift (f : C(K, ℂ)) : C₀(K, ℂ) :=
  ZeroAtInftyContinuousMap.ContinuousMap.liftZeroAtInfty f

private def dualBall (A : NonUnitalSubalgebra ℂ C(K, ℂ)) :
    Set (WeakDual ℂ C₀(K, ℂ)) :=
  {L | ‖L.toStrongDual‖ ≤ 1 ∧ ∀ f ∈ A, L (lift f) = 0}

private lemma zero_mem_dualBall (A : NonUnitalSubalgebra ℂ C(K, ℂ)) :
    0 ∈ dualBall A := by
  constructor
  · change ‖(0 : C₀(K, ℂ) →L[ℂ] ℂ)‖ ≤ 1
    rw [ContinuousLinearMap.opNorm_zero]
    norm_num
  · intro f hf; rfl

private lemma dualBall_compact (A : NonUnitalSubalgebra ℂ C(K, ℂ)) :
    IsCompact (dualBall A) := by
  have hc : IsClosed {L : WeakDual ℂ C₀(K, ℂ) | ∀ f ∈ A, L (lift f) = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter (fun f => isClosed_iInter (fun _ =>
      isClosed_eq (WeakDual.eval_continuous (lift f)) continuous_const))
  have heq : dualBall A =
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : C₀(K, ℂ) →L[ℂ] ℂ) 1 ∩
        {L : WeakDual ℂ C₀(K, ℂ) | ∀ f ∈ A, L (lift f) = 0} := by
    ext L
    simp only [dualBall, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Metric.mem_closedBall]
    rw [@dist_zero_right (C₀(K, ℂ) →L[ℂ] ℂ) inferInstance L.toStrongDual]
  rw [heq]
  exact (WeakDual.isCompact_closedBall (0 : C₀(K, ℂ) →L[ℂ] ℂ) 1).inter_right hc

private lemma dualBall_convex (A : NonUnitalSubalgebra ℂ C(K, ℂ)) :
    Convex ℝ (dualBall A) := by
  intro L hL M hM a b ha hb hab
  constructor
  · change ‖a • L.toStrongDual + b • M.toStrongDual‖ ≤ 1
    calc
      _ ≤ ‖a • L.toStrongDual‖ + ‖b • M.toStrongDual‖ := ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ a * ‖L.toStrongDual‖ + b * ‖M.toStrongDual‖ := by
        simpa only [Real.norm_of_nonneg ha, Real.norm_of_nonneg hb] using
          add_le_add (ContinuousLinearMap.opNorm_smul_le a L.toStrongDual)
            (ContinuousLinearMap.opNorm_smul_le b M.toStrongDual)
      _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hL.1 ha)
        (mul_le_mul_of_nonneg_left hM.1 hb)
      _ = 1 := by linarith
  · intro f hf
    change a • L (lift f) + b • M (lift f) = 0
    rw [hL.2 f hf, hM.2 f hf, smul_zero, smul_zero, add_zero]

/-- A nonzero extreme annihilator functional has norm one. The singleton
zero ball is allowed: no nontriviality of the annihilator is assumed. -/
private lemma extreme_norm (A : NonUnitalSubalgebra ℂ C(K, ℂ))
    (L : WeakDual ℂ C₀(K, ℂ)) (hL : L ∈ (dualBall A).extremePoints ℝ)
    (hne : L ≠ 0) : ‖L.toStrongDual‖ = 1 := by
  by_contra hn
  have hnlt : ‖L.toStrongDual‖ < 1 := lt_of_le_of_ne hL.1.1 hn
  let t := (1 + ‖L.toStrongDual‖) / 2
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by dsimp [t]; linarith
  have hnt : ‖L.toStrongDual‖ ≤ t := by dsimp [t]; linarith
  have hscaled : t⁻¹ • L ∈ dualBall A := by
    constructor
    · change ‖t⁻¹ • L.toStrongDual‖ ≤ 1
      apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
      rw [Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]
      exact (inv_mul_le_one₀ ht).mpr hnt
    · intro f hf
      change t⁻¹ • L (lift f) = 0
      rw [hL.1.2 f hf, smul_zero]
  have heq : (0 : WeakDual ℂ C₀(K, ℂ)) = L :=
    hL.2 (zero_mem_dualBall A) hscaled ⟨1 - t, t, by linarith, ht, by ring, by
      rw [smul_zero, zero_add, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]⟩
  exact hne heq.symm

section Measures
variable [MeasurableSpace K] [BorelSpace K]

private lemma functional_mem (A : NonUnitalSubalgebra ℂ C(K, ℂ))
    (ν : VectorMeasure K ℂ) (hν : ν ∈ annihilatorBall A) :
    ∃ L : WeakDual ℂ C₀(K, ℂ), L ∈ dualBall A ∧
      ∀ f : C₀(K, ℂ), L f = scalarIntegral ν f := by
  have := ExtremeScalarMeasures.finite_variation ν hν.1.1
  refine ⟨StrongDual.toWeakDual (scalarMeasureFunctional ν), ⟨?_, ?_⟩, fun _ => rfl⟩
  · apply (scalarMeasureFunctional_norm_le ν).trans
    exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using hν.1.2)
  · intro f hf
    exact hν.2 f hf

private lemma representation_extreme (A : NonUnitalSubalgebra ℂ C(K, ℂ))
    (L : WeakDual ℂ C₀(K, ℂ)) (hL : L ∈ (dualBall A).extremePoints ℝ)
    (ν : VectorMeasure K ℂ) (hrad : FiniteScalarRadon ν)
    (hrep : ∀ f : C₀(K, ℂ), L f = scalarIntegral ν f)
    (hm : ‖L.toStrongDual‖ = ν.variation.real univ) :
    ν ∈ (annihilatorBall A).extremePoints ℝ := by
  have hν : ν ∈ annihilatorBall A := by
    refine ⟨⟨hrad, ?_⟩, ?_⟩
    · rw [← ENNReal.ofReal_toReal hrad.1.ne]
      apply ENNReal.ofReal_le_one.mpr
      change ν.variation.real univ ≤ 1
      rw [← hm]
      exact hL.1.1
    · intro f hf
      exact (hrep (lift f)).symm.trans (hL.1.2 f hf)
  refine ⟨hν, ?_⟩
  intro μ hμ η hη hseg
  obtain ⟨F, hF, hFrep⟩ := functional_mem A μ hμ
  obtain ⟨G, hG, hGrep⟩ := functional_mem A η hη
  obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
  have := ExtremeScalarMeasures.finite_variation μ hμ.1.1
  have := ExtremeScalarMeasures.finite_variation η hη.1.1
  have hFG : a • F + b • G = L := by
    apply WeakDual.toStrongDual.injective
    ext f
    change a • F f + b • G f = L f
    rw [hFrep, hGrep, hrep, ← heq]
    change _ = VectorMeasure.integral _ _ _
    rw [VectorMeasure.integral_add_vectorMeasure
      (VectorMeasure.Integrable.smul_vectorMeasure
        (show μ.Integrable (f : K → ℂ) from (scalarIntegral_bound μ f).1) a)
      (VectorMeasure.Integrable.smul_vectorMeasure
        (show η.Integrable (f : K → ℂ) from (scalarIntegral_bound η f).1) b),
      VectorMeasure.integral_smul_vectorMeasure, VectorMeasure.integral_smul_vectorMeasure]
    rfl
  have hFL : F = L := hL.2 hF hG ⟨a, b, ha, hb, hab, hFG⟩
  apply scalarIntegral_injective μ ν hμ.1.1 hrad
  intro f
  exact (hFrep f).symm.trans ((congrArg (fun T : WeakDual ℂ C₀(K, ℂ) => T f) hFL).trans (hrep f))

private lemma extreme_vanishes (A : NonUnitalSubalgebra ℂ C(K, ℂ))
    (hclosed : IsClosed (A : Set C(K, ℂ))) (g : C(K, ℂ))
    (hg : ∀ S : Set K, IsMaximalClosedAntisymmetric A S →
      ∃ f ∈ A, ∀ x ∈ S, g x = f x)
    (L : WeakDual ℂ C₀(K, ℂ)) (hL : L ∈ (dualBall A).extremePoints ℝ) :
    L (lift g) = 0 := by
  by_cases hzero : L = 0
  · subst L
    rfl
  have hn := extreme_norm A L hL hzero
  obtain ⟨ν, hrad, hrep, hm, _⟩ := complex_representation K L.toStrongDual
  have hν := representation_extreme A L hL ν hrad (fun f => (hrep f).2) hm
  have hmass : ν.variation univ = 1 := by
    rw [← ENNReal.ofReal_toReal hrad.1.ne]
    change ENNReal.ofReal (ν.variation.real univ) = 1
    rw [← hm, hn, ENNReal.ofReal_one]
  obtain ⟨S, hS, hmax⟩ := maximal_closed_extension K A ν.variation.support
    (extreme_annihilator_support K A hclosed ν hν hmass)
  obtain ⟨f, hf, heq⟩ := hg S hmax
  have := ExtremeScalarMeasures.finite_variation ν hrad
  have : ν.variation.Regular :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mp hrad.2
  have hae : (g : K → ℂ) =ᵐ[ν.variation] f := by
    filter_upwards [ν.variation.support_mem_ae_of_regular] with x hx
    exact heq x (hS hx)
  calc
    L (lift g) = scalarIntegral ν g := (hrep (lift g)).2
    _ = scalarIntegral ν f := VectorMeasure.integral_congr_ae hae
    _ = 0 := hν.1.2 f hf

private lemma dualBall_vanishes (A : NonUnitalSubalgebra ℂ C(K, ℂ))
    (hclosed : IsClosed (A : Set C(K, ℂ))) (g : C(K, ℂ))
    (hg : ∀ S : Set K, IsMaximalClosedAntisymmetric A S →
      ∃ f ∈ A, ∀ x ∈ S, g x = f x) :
    ∀ L ∈ dualBall A, L (lift g) = 0 := by
  letI : LocallyConvexSpace ℝ (WeakDual ℂ C₀(K, ℂ)) :=
    @WeakBilin.locallyConvexSpace ℂ (C₀(K, ℂ) →L[ℂ] ℂ) C₀(K, ℂ)
      inferInstance inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance (topDualPairing ℂ C₀(K, ℂ))
  have hzeroClosed : IsClosed {L : WeakDual ℂ C₀(K, ℂ) | L (lift g) = 0} :=
    isClosed_eq (WeakDual.eval_continuous (lift g)) continuous_const
  have hzeroConvex : Convex ℝ {L : WeakDual ℂ C₀(K, ℂ) | L (lift g) = 0} := by
    intro L hL M hM a b ha hb hab
    change a • L (lift g) + b • M (lift g) = 0
    rw [hL, hM, smul_zero, smul_zero, add_zero]
  have hext : (dualBall A).extremePoints ℝ ⊆ {L | L (lift g) = 0} :=
    fun L hL => extreme_vanishes A hclosed g hg L hL
  have hKM := @closure_convexHull_extremePoints (WeakDual ℂ C₀(K, ℂ))
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (dualBall A) (dualBall_compact A) (dualBall_convex A)
  have hsub : closure (convexHull ℝ ((dualBall A).extremePoints ℝ)) ⊆
      {L : WeakDual ℂ C₀(K, ℂ) | L (lift g) = 0} := by
    apply closure_minimal _ hzeroClosed
    exact convexHull_min hext hzeroConvex
  rw [hKM] at hsub
  exact hsub

end Measures

/-- Bishop's antisymmetric-set theorem for a closed, possibly nonunital,
complex function algebra on an arbitrary compact Hausdorff space. -/
theorem bishop : BishopSpec.BishopTheorem.{u} := by
  intro K _ _ _ A hclosed g hg
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  have hall : ∀ L : C₀(K, ℂ) →L[ℂ] ℂ,
      (∀ f ∈ A, L (lift f) = 0) → L (lift g) = 0 := by
    intro L hL
    let c : ℝ := (1 + ‖L‖)⁻¹
    have hc : 0 < c := by dsimp [c]; positivity
    have hmem : (c • (StrongDual.toWeakDual L)) ∈ dualBall A := by
      constructor
      · change ‖c • L‖ ≤ 1
        apply (ContinuousLinearMap.opNorm_smul_le _ _).trans
        rw [Real.norm_of_nonneg hc.le]
        dsimp [c]
        apply (inv_mul_le_one₀ (by positivity : 0 < 1 + ‖L‖)).mpr
        linarith
      · intro f hf
        change c • L (lift f) = 0
        rw [hL f hf, smul_zero]
    have hz := dualBall_vanishes A hclosed g hg _ hmem
    change c • L (lift g) = 0 at hz
    exact (smul_eq_zero.mp hz).resolve_left hc.ne'
  obtain ⟨e, he, he'⟩ := compact_identification K ℂ
  have hinv (f : C(K, ℂ)) : e.symm (lift f) = f := by
    ext x
    exact he' _ x
  have hall' : ∀ L : C(K, ℂ) →L[ℂ] ℂ,
      (∀ f ∈ A, L f = 0) → L g = 0 := by
    intro L hL
    have hz := hall (L.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
      (fun f hf => by simpa [hinv] using hL f hf)
    simpa [hinv] using hz
  let M : Submodule ℂ C(K, ℂ) := A.toSubmodule
  letI : IsClosed (M : Set C(K, ℂ)) := hclosed
  by_contra hnot
  have hq : (M.mkQ g : C(K, ℂ) ⧸ M) ≠ 0 := by
    change (Submodule.Quotient.mk g : C(K, ℂ) ⧸ M) ≠ 0
    exact fun h => hnot ((Submodule.Quotient.mk_eq_zero M).mp h)
  obtain ⟨F, hF, hv⟩ := exists_dual_vector ℂ (M.mkQ g) (norm_ne_zero_iff.mpr hq)
  let L : C(K, ℂ) →L[ℂ] ℂ := F.comp M.mkQL
  have hzero : L g = 0 := hall' L (fun f hf => by
    change F (M.mkQ f) = 0
    rw [show M.mkQ f = 0 from (Submodule.Quotient.mk_eq_zero M).mpr hf, map_zero])
  have hz : (‖M.mkQ g‖ : ℂ) = 0 := hv.symm.trans hzero
  exact hq (norm_eq_zero.mp (by exact_mod_cast hz))

end ExpandedFA.PartV.Bishop
