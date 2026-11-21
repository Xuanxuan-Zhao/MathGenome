import MathGenome.Internal.LinearPDE.P201Specs.Potential.GreenCollarLocalization
import MathGenome.Internal.LinearPDE.P201.Potential.GreenConstruction
import Mathlib.Tactic.Linarith
import Mathlib.Topology.TietzeExtension

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set TopologicalSpace MeasureTheory Metric Filter
open scoped ContDiff Topology

namespace P201.GreenCollarLocalization
open P201Specs
open P201Specs.GreenConstruction
open P201Specs.GreenCollarLocalization
open P201Specs.NormalTrace

/-- Finite Taylor data near each point of a compact closure bound the actual
interior derivatives. No regularity of the total function outside the closure
and no uniqueness of derivatives at the boundary is required. -/
lemma interior_iteratedFDeriv_bound {n : ℕ} (Ω : Domain n)
    (hK : IsCompact (closure (Ω : Set (Space n)))) (f : Space n → ℝ)
    {k j : ℕ} (hf : ContDiffOn ℝ k f (closure (Ω : Set _))) (hj : j ≤ k) :
    ∃ C : ℝ, ∀ y ∈ Ω, ‖iteratedFDeriv ℝ j f y‖ ≤ C := by
  classical
  have hlocal (x : Space n) (hx : x ∈ closure (Ω : Set _)) :
      ∃ U ∈ 𝓝 x, ∃ C : ℝ, ∀ y ∈ U ∩ (Ω : Set _),
        ‖iteratedFDeriv ℝ j f y‖ ≤ C := by
    obtain ⟨u, hu, p, hp⟩ := contDiffWithinAt_nat.mp (hf x hx)
    rw [insert_eq_of_mem hx] at hu
    have hxu : x ∈ u := mem_of_mem_nhdsWithin hx hu
    obtain ⟨O, hO, hxO, hOu⟩ := mem_nhdsWithin.mp hu
    have hpn := (hp.cont j (by exact_mod_cast hj) x hxu).norm
    have hb : ∀ᶠ y in 𝓝[closure (Ω : Set _)] x, ‖p y j‖ < ‖p x j‖ + 1 := by
      apply Filter.Eventually.filter_mono (nhdsWithin_le_of_mem hu)
      exact hpn (gt_mem_nhds (lt_add_one _))
    obtain ⟨V, hV, hxV, hVb⟩ := mem_nhdsWithin.mp hb
    refine ⟨O ∩ V, (hO.inter hV).mem_nhds ⟨hxO, hxV⟩, ‖p x j‖ + 1, ?_⟩
    intro y hy
    have hyO : y ∈ (Ω : Set _) ∩ O := ⟨hy.2, hy.1.1⟩
    have hsub : (Ω : Set (Space n)) ∩ O ⊆ u :=
      fun z hz => hOu ⟨hz.2, subset_closure hz.1⟩
    have he := (hp.mono hsub).eq_iteratedFDerivWithin_of_uniqueDiffOn
      (by exact_mod_cast hj) (Ω.isOpen.inter hO).uniqueDiffOn hyO
    have hfc : ContDiffAt ℝ j f y :=
      ((hf.mono subset_closure) y hy.2).contDiffAt (Ω.isOpen.mem_nhds hy.2) |>.of_le
        (by exact_mod_cast hj)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (Ω.isOpen.inter hO).uniqueDiffOn hfc hyO] at he
    rw [← he]
    exact (hVb ⟨hy.1.2, subset_closure hy.2⟩).le
  choose U hU C hC using hlocal
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' U hU
  refine ⟨∑ x ∈ t, max (C x x.2) 0, ?_⟩
  intro y hy
  obtain ⟨x, hxt, hyU⟩ := mem_iUnion₂.mp (ht (subset_closure hy))
  have hs : max (C x x.property) 0 ≤ ∑ z ∈ t, max (C z z.property) 0 :=
    Finset.single_le_sum (s := t) (a := x)
      (f := fun z : ↥(closure (Ω : Set (Space n))) => max (C z z.property) 0) (fun z _ => le_max_right _ _) hxt
  exact (hC x x.2 y ⟨hyU, hy⟩).trans ((le_max_left _ 0).trans hs)


/-- Coordinate words are evaluations of the actual interior Fréchet derivative
at finite regularity; global smoothness is unnecessary. -/
lemma partialWord_ofFn_on {n k : ℕ} (Ω : Domain n) (f : Space n → ℝ)
    (hf : ContDiffOn ℝ k f Ω) {j : ℕ} (hj : j ≤ k)
    (a : Fin j → Fin n) (x : Space n) (hx : x ∈ Ω) :
    P102.U4.partialWord f (List.ofFn a) x =
      iteratedFDeriv ℝ j f x (fun i => coordinate n (a i)) := by
  induction j generalizing x with
  | zero => simp [P102.U4.partialWord, iteratedFDeriv_zero_apply]
  | succ j ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (P102.U4.partialWord f (List.ofFn (Fin.tail a))) x
      (coordinate n (a 0)) = _
    have he : P102.U4.partialWord f (List.ofFn (Fin.tail a)) =ᶠ[𝓝 x]
        fun y => iteratedFDeriv ℝ j f y (fun i => coordinate n (a i.succ)) := by
      filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
      exact ih (Nat.le_of_succ_le hj) (Fin.tail a) y hy
    rw [he.fderiv_eq]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
      (((hf x hx).contDiffAt (Ω.isOpen.mem_nhds hx)).iteratedFDeriv_right
        (m := 1) (by rw [add_comm]; exact_mod_cast hj)).differentiableAt one_ne_zero
    rw [fderiv_continuousMultilinear_apply_const hd]
    rfl

/-- Every finite classical coordinate derivative is in L² on a bounded open
set when the function is C^k on its closure. -/
lemma closure_partial_memLp {n k : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) (f : Space n → ℝ)
    (hf : ContDiffOn ℝ k f (closure (Ω : Set _)))
    (α : MultiIndex n) (hα : α.card ≤ k) :
    MemLp (multiPartial f α) 2 (domainMeasure Ω) := by
  have hK : IsCompact (closure (Ω : Set (Space n))) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hb.closure⟩
  have : IsFiniteMeasure (domainMeasure Ω) := ⟨by
    change (volume.restrict (Ω : Set (Space n))) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hK.measure_lt_top⟩
  have hfo : ContDiffOn ℝ k f Ω := hf.mono subset_closure
  have hcont : ContinuousOn (multiPartial f α) Ω := by
    have h := P102.U4.partialWord_contDiffOn Ω hfo (α.sort (· ≤ ·)) 0 (by simpa using hα)
    exact h.continuousOn
  obtain ⟨C, hC⟩ := interior_iteratedFDeriv_bound Ω hK f hf hα
  apply MemLp.of_bound (hcont.aestronglyMeasurable Ω.isOpen.measurableSet) C
  filter_upwards [ae_restrict_mem Ω.isOpen.measurableSet] with x hx
  let l := α.sort (· ≤ ·)
  have hl : l.length = α.card := Multiset.length_sort _
  have he : multiPartial f α x = iteratedFDeriv ℝ l.length f x
      (fun i => coordinate n (l.get i)) := by
    simpa only [List.ofFn_get, P201Specs.multiPartial, P102.U4.multiPartial, l] using partialWord_ofFn_on Ω f hfo (hl ▸ hα) l.get x hx
  rw [he]
  calc
    _ ≤ ‖iteratedFDeriv ℝ l.length f x‖ *
        ∏ i, ‖coordinate n (l.get i)‖ := (iteratedFDeriv ℝ l.length f x).le_opNorm _
    _ = ‖iteratedFDeriv ℝ α.card f x‖ := by
      have hn (i : Fin n) : ‖coordinate n i‖ = 1 := by
        simp [P102.U4.coordinateVector,
          EuclideanSpace.basisFun_apply, EuclideanSpace.single]
      simp_rw [hn]
      rw [Finset.prod_const_one, mul_one]
      exact congrArg (fun j => ‖iteratedFDeriv ℝ j f x‖) hl
    _ ≤ C := hC x hx


/-- C^k on a bounded closure gives a genuine H^k class, with all its weak
coordinate derivatives represented by the actual classical derivatives. -/
lemma closure_hilbert_realization {n k : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) (f : Space n → ℝ)
    (hf : ContDiffOn ℝ k f (closure (Ω : Set _))) :
    ∃ z : H ℝ Ω k,
      ∀ α : P102.U4.SobolevIndex n k,
        (P102.U4.sobolevDerivative (hToW ℝ Ω k z) α : Space n → ℝ)
          =ᵐ[domainMeasure Ω] multiPartial f α.val := by
  classical
  have hm (α : MultiIndex n) (hα : α.card ≤ k) := closure_partial_memLp Ω hb f hf α hα
  have hf0 : MemLp f 2 (domainMeasure Ω) := by
    simpa [P201Specs.multiPartial, P102.U4.multiPartial, P102.U4.partialWord] using hm 0 (Nat.zero_le _)
  let u := hf0.toLp f
  have hu : (u : Space n → ℝ) =ᵐ[domainMeasure Ω] f := hf0.coeFn_toLp
  have hreg : P102.U4.regularDistribution Ω u = P102.U4.regularDistribution Ω f :=
    (P102.U4.regular_injectivity n ℝ Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω 2 u)
      ((hf.continuousOn.mono subset_closure).locallyIntegrableOn Ω.isOpen.measurableSet)).mpr hu
  have hs : P102.U4.HasSobolevDerivatives Ω k 2 u := by
    intro α hα
    let v := (hm α hα).toLp (multiPartial f α)
    refine ⟨v, ?_⟩
    rw [hreg, P102.U4.derivative_classicalCompatibility n ℝ Ω α f
      ((hf.mono subset_closure).of_le (by exact_mod_cast hα))]
    exact (P102.U4.regular_injectivity n ℝ Ω _ _
      ((P102.U4.partialWord_contDiffOn Ω (hf.mono subset_closure)
        (α.sort (· ≤ ·)) 0 (by simpa using hα)).continuousOn.locallyIntegrableOn
          Ω.isOpen.measurableSet)
      (P102.U4.domainLp_locallyIntegrable Ω 2 v)).mpr (hm α hα).coeFn_toLp.symm
  obtain ⟨w, hw⟩ := (Set.ext_iff.mp (P102.U4.sobolev_range Ω k 2) u).mpr hs
  refine ⟨(hToW ℝ Ω k).symm w, ?_⟩
  intro α
  let v := (hm α.val α.property).toLp (multiPartial f α.val)
  have hv : v = P102.U4.sobolevDerivative w α := by
    apply P102.U4.sobolev_derivative_unique Ω k 2 w α v
    rw [hw, hreg, P102.U4.derivative_classicalCompatibility n ℝ Ω α.val f
      ((hf.mono subset_closure).of_le (by exact_mod_cast α.property))]
    exact (P102.U4.regular_injectivity n ℝ Ω _ _
      ((P102.U4.partialWord_contDiffOn Ω (hf.mono subset_closure)
        (α.val.sort (· ≤ ·)) 0 (by simpa using α.property)).continuousOn.locallyIntegrableOn
          Ω.isOpen.measurableSet)
      (P102.U4.domainLp_locallyIntegrable Ω 2 v)).mpr (hm α.val α.property).coeFn_toLp.symm
  simpa only [ContinuousLinearEquiv.apply_symm_apply, ← hv] using (hm α.val α.property).coeFn_toLp

lemma closure_laplacian_memLp {n : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) (f : Space n → ℝ)
    (hf : ContDiffOn ℝ 2 f (closure (Ω : Set _))) :
    MemLp (laplacian f) 2 (domainMeasure Ω) := by
  exact memLp_finsetSum _ fun i _ => closure_partial_memLp Ω hb f hf {i, i} (by simp)


/-- The remainder's classical Laplacian is the actual L² distributional
Laplacian of its Sobolev realization, under C² on the closure alone. -/
lemma closure_laplacian_realization {n : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) (f : Space n → ℝ)
    (hf : ContDiffOn ℝ 2 f (closure (Ω : Set _))) :
    ∃ (z : H ℝ Ω 1) (q : Lp ℝ Ω 2),
      (hUnderlying Ω 1 z : Space n → ℝ) =ᵐ[domainMeasure Ω] f ∧
      (q : Space n → ℝ) =ᵐ[domainMeasure Ω] laplacian f ∧
      P201Specs.NormalTrace.HasLaplacian Ω z q := by
  obtain ⟨z, hzall⟩ := closure_hilbert_realization Ω hb f (hf.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))
  have hz : (hUnderlying Ω 1 z : Space n → ℝ) =ᵐ[domainMeasure Ω] f := by
    change (P102.U4.sobolevDerivative (hToW ℝ Ω 1 z) (P102.U4.zeroSobolevIndex n 1) :
      Space n → ℝ) =ᵐ[domainMeasure Ω] f
    simpa only [P102.U4.zeroSobolevIndex, P201Specs.multiPartial, P102.U4.multiPartial,
      Multiset.sort_zero, P102.U4.partialWord] using hzall (P102.U4.zeroSobolevIndex n 1)
  have hm := closure_laplacian_memLp Ω hb f hf
  let q := hm.toLp (laplacian f)
  have hq : (q : Space n → ℝ) =ᵐ[domainMeasure Ω] laplacian f := hm.coeFn_toLp
  refine ⟨z, q, hz, hq, ?_⟩
  have hreg : P201Specs.regularDistribution Ω (hUnderlying Ω 1 z) =
      P201Specs.regularDistribution Ω f :=
    (P102.U4.regular_injectivity n ℝ Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω 2 _)
      ((hf.continuousOn.mono subset_closure).locallyIntegrableOn Ω.isOpen.measurableSet)).mpr hz
  have hregq : P201Specs.regularDistribution Ω q =
      P201Specs.regularDistribution Ω (laplacian f) :=
    (P102.U4.regular_injectivity n ℝ Ω _ _
      (P102.U4.domainLp_locallyIntegrable Ω 2 _)
      ((P201.MeanValues.laplacian_continuousOn Ω f (hf.mono subset_closure)).locallyIntegrableOn
        Ω.isOpen.measurableSet)).mpr hq
  unfold P201Specs.NormalTrace.HasLaplacian
  rw [hreg, hregq]
  exact P201.GreenConstruction.classical_laplacian_distribution Ω f (hf.mono subset_closure)

end P201.GreenCollarLocalization

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
/- Physical trace compatibility for continuous representatives. -/
namespace GreenCollarTraceContinuity
open scoped ENNReal NNReal
open P102.U4 P102.U4.GraphPieces P102.Sobolev.Geometry P102.Sobolev.Extension
open P102.Trace P102.Trace.Ordinary P102.Trace.Exact

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

lemma continuous_trace_higher {m : ℕ} (hm : 1 ≤ m)
    (Ω : Opens (Space (m + 1)))
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (T : Sobolev ℝ Ω 1 2 →L[ℝ] P102.Trace.Ordinary.BoundaryLp ℝ Ω 2)
    (hT : IsTrace T) (u : Sobolev ℝ Ω 1 2)
    (f : Space (m + 1) → ℝ) (hf : Continuous f)
    (hu : sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f) :
    (T u : Space (m + 1) → ℝ) =ᵐ[P102.Trace.Ordinary.boundaryMeasure Ω] f := by
  classical
  obtain ⟨A⟩ := BoundaryFractional.atlas_exists m (geometricOpen e Ω : Set (Ambient m)) hΩ
  obtain ⟨_, _, S, _, hSlices, _⟩ := flat_trace_exists m hm ℝ 2 (by norm_num)
  have hS : IsFlatTrace S := by
    intro v
    obtain ⟨F, hF, hF0, _⟩ := hSlices v
    exact ⟨F, hF, hF0⟩
  let q := boundaryPullback e 2 (T u)
  let r : Ambient m → ℝ := f ∘ e
  have hlocal (i : Fin A.count) :
      (fun x => A.cutoff i x • q x) =ᵐ[BoundaryFractional.surfaceMeasure
          (geometricOpen e Ω : Set (Ambient m))] (fun x => A.cutoff i x • r x) := by
    let D := atlasFlattenCollar e A i
    have hcomm := D.flattenOperator_commutes e (A.chart i) hm hΩ (by norm_num) S hS T hT u
    have hflat := D.flattenOperator_smooth_trace e (A.chart i) hm (by norm_num) S hS u f hf hu
    have hflatbase := (faceCoordinates_measurePreserving m).quasiMeasurePreserving.ae_eq_comp hflat
    have hQ := flatBoundaryPullback_reverse (S (D.flattenOperator e (A.chart i) ℝ 2 u))
    rw [hcomm] at hQ
    have hbase := (hQ.symm.trans (baseCoordinates_reverse
      (GraphInput.lp e (A.chart i) D.cutoff D.smooth D.compact (T u)))).symm
    have hloc := GraphInput.lp_ae e (A.chart i) D.cutoff D.smooth D.compact (T u)
    apply supported_pullback_injective (A.chart i) (K := tsupport (A.cutoff i))
      D.support_subset
    · exact ae_of_all _ (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_smul])
    · exact ae_of_all _ (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, zero_smul])
    · filter_upwards [hbase, hloc, hflatbase] with x hx hl hfl
      change GraphInput.lp e (A.chart i) D.cutoff D.smooth D.compact (T u) x =
        BoundaryChartLocalization.localizedPullback (A.chart i) D.cutoff (q : Ambient m → ℝ) x at hl
      change S (D.flattenOperator e (A.chart i) ℝ 2 u) (faceCoordinates m x) = _ at hfl
      have hface := flatten_at_face e (A.chart i) D.graphExtension (ACL.coordinates m x)
      change flattenEquiv e (A.chart i).frame D.graphExtension (point m (faceCoordinates m x) 0) =
        e ((A.chart i).frame (graph D.graphExtension x)) at hface
      simp only [Function.comp_apply] at hfl
      rw [hface, LinearIsometryEquiv.symm_apply_apply] at hfl
      have hform := D.localized_boundary_formula e (A.chart i) f x
      change BoundaryChartLocalization.localizedPullback (A.chart i) D.cutoff r x = _ at hform
      have heq := hl.symm.trans (hx.trans (hfl.trans hform.symm))
      change (if x ∈ ball (A.chart i).center (A.chart i).radius then _ else 0) =
        (if x ∈ ball (A.chart i).center (A.chart i).radius then _ else 0)
      simpa only [BoundaryChartLocalization.localizedPullback, Function.comp_apply,
        BoundaryChartLocalization.chartGraph, D, atlasFlattenCollar] using heq
  have hqr : (q : Ambient m → ℝ) =ᵐ[BoundaryFractional.surfaceMeasure
      (geometricOpen e Ω : Set (Ambient m))] r := by
    filter_upwards [ae_all_iff.mpr hlocal, ae_restrict_mem isClosed_frontier.measurableSet]
      with x hx hxfront
    rw [← BoundaryFractional.partition_reconstruction A q hxfront,
      ← BoundaryFractional.partition_reconstruction A r hxfront]
    exact Finset.sum_congr rfl (fun i _ => hx i)
  have hqae := boundaryPullback_ae e (T u)
  have ht : (fun x => T u (e x)) =ᵐ[BoundaryFractional.surfaceMeasure
      (geometricOpen e Ω : Set (Ambient m))] (fun x => f (e x)) := hqae.symm.trans hqr
  have ht' : ∀ᵐ y ∂(BoundaryFractional.surfaceMeasure
      (geometricOpen e Ω : Set (Ambient m))).map e, T u y = f y :=
    e.toHomeomorph.measurableEmbedding.ae_map_iff.mpr ht
  change ∀ᵐ y ∂P102.Trace.Ordinary.boundaryMeasure Ω, (T u : Space (m + 1) → ℝ) y = f y
  simpa only [(boundary_measurePreserving e).map_eq] using ht'

lemma continuous_trace_one
    (Ω : Opens (Space 1)) (e : Ambient 0 ≃ₗᵢ[ℝ] Space 1)
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient 0)))
    (T : Sobolev ℝ Ω 1 2 →L[ℝ] P102.Trace.Ordinary.BoundaryLp ℝ Ω 2)
    (hT : IsTrace T) (u : Sobolev ℝ Ω 1 2)
    (f : Space 1 → ℝ) (hf : Continuous f)
    (hu : sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space 1))] f) :
    (T u : Space 1 → ℝ) =ᵐ[P102.Trace.Ordinary.boundaryMeasure Ω] f := by
  obtain ⟨_, n, a, b, hab, hinj, hdis, hcover, hfront, hbound, hrep, hval⟩ :=
    endpoint_identification e Ω hΩ ℝ 2 (by norm_num) T hT
  obtain ⟨F, hF⟩ := hrep u
  have hsub (i : Fin n) : Ioo (a i) (b i) ⊆ linePoint ⁻¹' (Ω : Set (Space 1)) := by
    intro t ht
    change linePoint t ∈ (Ω : Set (Space 1))
    rw [hcover]
    exact mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩
  have heq (i : Fin n) : EqOn F (fun t => f (linePoint t)) (Icc (a i) (b i)) :=
    line_representative_eqOn (hab i) (hsub i)
      (by simpa only [uIcc_of_le (hab i).le] using (hF.2.1 i).continuousOn)
      (hf.comp lineIsometry.continuous).continuousOn hF.1 (linePoint_ae_restrict hu)
  filter_upwards [boundaryMeasure_ae_frontier Ω] with y hy
  rw [hfront] at hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  rcases (by simpa using hi : y = linePoint (a i) ∨ y = linePoint (b i)) with rfl | rfl
  · exact (hval u F hF i).1.trans (heq i ⟨le_rfl, (hab i).le⟩)
  · exact (hval u F hF i).2.trans (heq i ⟨(hab i).le, le_rfl⟩)

lemma continuous_trace_ambient {m : ℕ}
    (Ω : Opens (Space (m + 1)))
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (T : Sobolev ℝ Ω 1 2 →L[ℝ] P102.Trace.Ordinary.BoundaryLp ℝ Ω 2)
    (hT : IsTrace T) (u : Sobolev ℝ Ω 1 2)
    (f : Space (m + 1) → ℝ) (hf : Continuous f)
    (hu : sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f) :
    (T u : Space (m + 1) → ℝ) =ᵐ[P102.Trace.Ordinary.boundaryMeasure Ω] f := by
  cases m with
  | zero => exact continuous_trace_one Ω e hΩ T hT u f hf hu
  | succ m => exact continuous_trace_higher (by omega) Ω e hΩ T hT u f hf hu

lemma continuous_trace_closure {m : ℕ}
    (Ω : Opens (Space (m + 1)))
    (e : Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (hΩ : IsLipschitzOpen (geometricOpen e Ω : Set (Ambient m)))
    (T : Sobolev ℝ Ω 1 2 →L[ℝ] P102.Trace.Ordinary.BoundaryLp ℝ Ω 2)
    (hT : IsTrace T) (u : Sobolev ℝ Ω 1 2)
    (f : Space (m + 1) → ℝ) (hf : ContinuousOn f (closure (Ω : Set (Space (m + 1)))))
    (hu : sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] f) :
    (T u : Space (m + 1) → ℝ) =ᵐ[P102.Trace.Ordinary.boundaryMeasure Ω] f := by
  let Fc : C(closure (Ω : Set (Space (m + 1))), ℝ) := ⟨_, hf.domRestrict⟩
  obtain ⟨F, hF⟩ := ContinuousMap.exists_restrict_eq isClosed_closure Fc
  have hFeq : EqOn F f (closure (Ω : Set (Space (m + 1)))) := by
    intro y hy
    exact congrArg (fun g : C(closure (Ω : Set (Space (m + 1))), ℝ) => g ⟨y, hy⟩) hF
  have huF : sobolevUnderlying u =ᵐ[volume.restrict (Ω : Set (Space (m + 1)))] F := by
    filter_upwards [hu, ae_restrict_mem Ω.isOpen.measurableSet] with y hy hyΩ
    exact hy.trans (hFeq (subset_closure hyΩ)).symm
  refine (continuous_trace_ambient Ω e hΩ T hT u F F.continuous huF).trans ?_
  filter_upwards [boundaryMeasure_ae_frontier Ω] with y hy
  exact hFeq (frontier_subset_closure hy)

end GreenCollarTraceContinuity
end

namespace P201.GreenCollarLocalization
open P201Specs P201Specs.GreenConstruction P201Specs.GreenCollarLocalization
open P201Specs.NormalTrace

lemma continuous_trace {m : ℕ} (Ω : Domain (m + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) (D : TraceData Ω hΩ)
    (z : H ℝ Ω 1) (f : Space (m + 1) → ℝ)
    (hf : ContinuousOn f (closure (Ω : Set (Space (m + 1)))))
    (hz : (hUnderlying Ω 1 z : Space (m + 1) → ℝ) =ᵐ[domainMeasure Ω] f) :
    (P201Specs.Trace.inclusion Ω hΩ (D.trace z) : Space (m + 1) → ℝ)
      =ᵐ[boundaryMeasure Ω] f := by
  let e := P201Specs.hToW ℝ Ω 1
  let T := (P201Specs.Trace.inclusion Ω hΩ).comp (D.trace.comp e.symm.toContinuousLinearMap)
  have hT : P102.Trace.Ordinary.IsTrace T := by
    intro u g hg hu
    apply D.smooth (e.symm u) g hg
    change P102.U4.sobolevUnderlying (e (e.symm u)) =ᵐ[domainMeasure Ω] g
    simpa only [e.apply_symm_apply] using hu
  exact GreenCollarTraceContinuity.continuous_trace_closure Ω (graphFrame m) hΩ T hT (e z) f hf hz

lemma gradient_zero_off_compact {n : ℕ} (Ω : Domain n) (a : H ℝ Ω 1)
    (K : TopologicalSpace.Compacts (Space n))
    (ha : ∀ᵐ y ∂domainMeasure Ω, y ∉ K → hUnderlying Ω 1 a y = 0) :
    ∀ᵐ y ∂domainMeasure Ω, y ∉ K → hGradient a y = 0 := by
  have hi (i : Fin n) : ∀ᵐ y ∂domainMeasure Ω,
      y ∉ K → hFirstDerivative a i y = 0 :=
    P102.U4.sobolevDerivative_zero_off_compact Ω 1 2
      (hToW ℝ Ω 1 a) K ha ⟨{i}, by simp⟩
  have hg : (hGradient a : Space n → Space n) =ᵐ[domainMeasure Ω]
      (fun y => WithLp.toLp 2 (fun i => hFirstDerivative a i y)) :=
    MemLp.coeFn_toLp _
  filter_upwards [hg, ae_all_iff.mpr hi] with y hy hiy hyK
  rw [hy]
  apply PiLp.ext
  intro i
  exact hiy i hyK

lemma gradient_zero_on_ball {n : ℕ} (Ω : Domain n)
    (hb : Bornology.IsBounded (Ω : Set (Space n))) (z : H ℝ Ω 1)
    (x : Space n) (s : ℝ)
    (hz : ∀ᵐ y ∂domainMeasure Ω, y ∈ ball x s → hUnderlying Ω 1 z y = 0) :
    ∀ᵐ y ∂domainMeasure Ω, y ∈ ball x s → hGradient z y = 0 := by
  let K : TopologicalSpace.Compacts (Space n) :=
    ⟨closure (Ω : Set (Space n)) \ ball x s, hb.isCompact_closure.diff isOpen_ball⟩
  have hs : ∀ᵐ y ∂domainMeasure Ω, y ∉ K → hUnderlying Ω 1 z y = 0 := by
    filter_upwards [hz, ae_restrict_mem Ω.isOpen.measurableSet] with y hy hyΩ hyK
    apply hy
    by_contra hyB
    exact hyK ⟨subset_closure hyΩ, hyB⟩
  filter_upwards [gradient_zero_off_compact Ω z K hs] with y hy hyB
  exact hy (fun hyK => hyK.2 hyB)

lemma pairing_zero_of_inner_support {m : ℕ} (Ω : Domain (m+1))
    (hΩ : IsBoundedLipschitzOpen Ω) (D : TraceData Ω hΩ)
    (z a : H ℝ Ω 1) (q : Lp ℝ Ω 2) (τ : HminusHalf Ω hΩ)
    (hτ : Pairing D (hGradient z) q τ)
    (K : TopologicalSpace.Compacts (Space (m+1)))
    (ha : ∀ᵐ y ∂domainMeasure Ω, y ∉ K → hUnderlying Ω 1 a y = 0)
    (hz : ∀ᵐ y ∂domainMeasure Ω, y ∈ K → hGradient z y = 0)
    (hq : ∀ᵐ y ∂domainMeasure Ω, y ∈ K → q y = 0) :
    τ (D.trace a) = 0 := by
  rw [hτ]
  apply integral_eq_zero_of_ae
  filter_upwards [gradient_zero_off_compact Ω a K ha, ha, hz, hq]
    with y hga ha hz hq
  by_cases hyK : y ∈ K
  · simp only [hz hyK, hq hyK, inner_zero_left, zero_mul, add_zero, Pi.zero_apply]
  · simp only [hga hyK, ha hyK, inner_zero_right, mul_zero, add_zero, Pi.zero_apply]

lemma exists_cutoff_class {n : ℕ} (Ω : Domain n) (w : H ℝ Ω 1)
    (χ : Test ℝ (⊤ : Domain n)) :
    ∃ a : H ℝ Ω 1,
      (hUnderlying Ω 1 a : Space n → ℝ) =ᵐ[domainMeasure Ω]
        (fun y => χ y * hUnderlying Ω 1 w y) ∧
      ∀ᵐ y ∂domainMeasure Ω, y ∉ tsupport χ → hUnderlying Ω 1 a y = 0 := by
  let a := (hToW ℝ Ω 1).symm
    (P102.Sobolev.Extension.domainTestMulSobolev Ω 2 χ (hToW ℝ Ω 1 w))
  have hae : (hUnderlying Ω 1 a : Space n → ℝ) =ᵐ[domainMeasure Ω]
      (fun y => χ y * hUnderlying Ω 1 w y) := by
    change (P102.U4.sobolevUnderlying ((hToW ℝ Ω 1) a) : Space n → ℝ) =ᵐ[_] _
    simp only [a, ContinuousLinearEquiv.apply_symm_apply,
      P102.Sobolev.Extension.domainTestMulSobolev_underlying]
    exact P102.Sobolev.Extension.domainTestMul_ae Ω 2 χ _
  refine ⟨a, hae, ?_⟩
  filter_upwards [hae] with y hy hyS
  rw [hy, image_eq_zero_of_notMem_tsupport hyS, zero_mul]



/-- The opposing Green trace vanishes because the Green row is zero on the
outer boundary and the remainder has a zero germ near the inner sphere. -/
lemma opposing_trace_zero {m : ℕ} (Ω : Domain (m+1))
    (hb : Bornology.IsBounded (Ω : Set (Space (m+1))))
    (x : Space (m+1)) (r : ℝ) (hr : 0 < r)
    (hC : IsBoundedLipschitzOpen (GreenConstruction.collar Ω x r))
    (D : NormalTrace.TraceData (GreenConstruction.collar Ω x r) hC)
    (g : Space (m+1) → ℝ) (hg : GreenConstruction.IsGreenFunction Ω x g)
    (w : H ℝ (GreenConstruction.collar Ω x r) 1)
    (hw : (hUnderlying _ 1 w : Space (m+1) → ℝ)
      =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)] g)
    (u : Space (m+1) → ℝ) (β : ContDiffBump x) (hri : r < β.rIn)
    (z : H ℝ (GreenConstruction.collar Ω x r) 1)
    (q : Lp ℝ (GreenConstruction.collar Ω x r) 2)
    (hz : (hUnderlying _ 1 z : Space (m+1) → ℝ)
      =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)]
        P201Specs.GreenCollarLocalization.remainder β u)
    (hq : (q : Space (m+1) → ℝ)
      =ᵐ[domainMeasure (GreenConstruction.collar Ω x r)]
        laplacian (P201Specs.GreenCollarLocalization.remainder β u))
    (τ : HminusHalf (GreenConstruction.collar Ω x r) hC)
    (hτ : NormalTrace.Pairing D (hGradient z) q τ) :
    τ (D.trace w) = 0 := by
  let C := GreenConstruction.collar Ω x r
  let χ : ContDiffBump x :=
    ⟨(2*r+β.rIn)/3, (r+2*β.rIn)/3, by linarith, by linarith⟩
  have hχri : r < χ.rIn := by dsimp [χ]; linarith
  have hχro : χ.rOut < β.rIn := by dsimp [χ]; linarith
  let φ : Test ℝ (⊤ : Domain (m+1)) :=
    ⟨χ, χ.contDiff, χ.hasCompactSupport, subset_univ _⟩
  obtain ⟨a, hae, has⟩ := exists_cutoff_class C w φ
  let K : TopologicalSpace.Compacts (Space (m+1)) :=
    ⟨closedBall x χ.rOut, isCompact_closedBall x χ.rOut⟩
  have ha : ∀ᵐ y ∂domainMeasure C, y ∉ K → hUnderlying C 1 a y = 0 := by
    filter_upwards [has] with y hy hyK
    apply hy
    change y ∉ tsupport χ
    rwa [χ.tsupport_eq]
  have hCΩ : C ≤ Ω := fun _ hy => hy.1
  have hCcl : closure (C : Set (Space (m+1))) ⊆
      closure (Ω : Set (Space (m+1))) \ {x} := by
    have hd : closure (C : Set (Space (m+1))) ⊆ {y | r ≤ dist y x} :=
      closure_minimal (by
        intro y hy
        change r ≤ dist y x
        exact (lt_of_not_ge hy.2).le)
        (isClosed_le continuous_const (continuous_id.dist continuous_const))
    intro y hy
    refine ⟨closure_mono hCΩ hy, ?_⟩
    simp only [mem_singleton_iff]
    intro he
    have hh : r ≤ dist y x := hd hy
    rw [he, dist_self] at hh
    linarith
  let f : Space (m+1) → ℝ := fun y => (1-χ y)*g y
  have hfc : ContinuousOn f (closure (C : Set (Space (m+1)))) :=
    (continuous_const.sub χ.continuous).continuousOn.mul (hg.2.2.2.2.1.mono hCcl)
  have hrep : (hUnderlying C 1 (w-a) : Space (m+1) → ℝ)
      =ᵐ[domainMeasure C] f := by
    rw [map_sub]
    filter_upwards [Lp.coeFn_sub (hUnderlying C 1 w) (hUnderlying C 1 a), hw, hae]
      with y hys hyw hya
    rw [hys]
    change hUnderlying C 1 w y - hUnderlying C 1 a y = f y
    rw [hyw, hya, hyw]
    change g y - χ y * g y = (1-χ y)*g y
    ring
  have hfb : ∀ y ∈ frontier (C : Set (Space (m+1))), f y = 0 := by
    intro y hy
    rcases P201.GreenConstruction.frontier_collar_subset Ω x r hy with hyΩ | hys
    · change (1-χ y)*g y = 0
      rw [hg.2.2.2.2.2 y hyΩ, mul_zero]
    · have hyχ : y ∈ closedBall x χ.rIn := by
        change dist y x ≤ χ.rIn
        rw [mem_sphere.mp hys]
        exact hχri.le
      change (1-χ y)*g y = 0
      rw [χ.one_of_mem_closedBall hyχ, sub_self, zero_mul]
  have ht : D.trace (w-a) = 0 := by
    apply P201.Trace.inclusion_injective C hC
    rw [map_zero]
    apply Lp.ext
    filter_upwards [continuous_trace C hC D (w-a) f hfc hrep,
      P102.Trace.Ordinary.boundaryMeasure_ae_frontier C,
      Lp.coeFn_zero ℝ 2 (boundaryMeasure C)] with y hy hyC hy0
    exact hy.trans ((hfb y hyC).trans (hy0).symm)
  rw [map_sub, sub_eq_zero] at ht
  rw [ht]
  have hz0 : ∀ᵐ y ∂domainMeasure C,
      y ∈ ball x β.rIn → hUnderlying C 1 z y = 0 := by
    filter_upwards [hz] with y hy hyB
    rw [hy]
    change (1-β y)*u y = 0
    rw [β.one_of_mem_closedBall (mem_closedBall.mpr (mem_ball.mp hyB).le),
      sub_self, zero_mul]
  have hg0 := gradient_zero_on_ball C (hb.subset hCΩ) z x β.rIn hz0
  have hgz : ∀ᵐ y ∂domainMeasure C, y ∈ K → hGradient z y = 0 := by
    filter_upwards [hg0] with y hy hyK
    exact hy (lt_of_le_of_lt (show dist y x ≤ χ.rOut from hyK) hχro)
  have hq0 : ∀ᵐ y ∂domainMeasure C, y ∈ K → q y = 0 := by
    filter_upwards [hq] with y hy hyK
    rw [hy]
    have hyB : y ∈ ball x β.rIn :=
      lt_of_le_of_lt (show dist y x ≤ χ.rOut from hyK) hχro
    have he : P201Specs.GreenCollarLocalization.remainder β u =ᶠ[𝓝 y] (0 : Space (m+1) → ℝ) := by
      filter_upwards [β.eventuallyEq_one_of_mem_ball hyB] with t ht
      simp [P201Specs.GreenCollarLocalization.remainder, ht]
    rw [P201.Weyl.laplacian_eq_of_eventuallyEq he]
    exact ((P201.MeanValues.harmonic_bridge (⊤ : Domain (m+1))
      (0 : Space (m+1) → ℝ)).mpr
      (InnerProductSpace.harmonicOnNhd_const 0)).2 y (mem_univ y)
  exact pairing_zero_of_inner_support C hC D z a q τ hτ K ha hgz hq0

/-- Local multiplication by the bump removes all ambient irregularity outside Ω. -/
theorem compactPart_contDiff {n : ℕ} (Ω : Domain n) (x : Space n)
    (β : ContDiffBump x) (hβ : tsupport β ⊆ (Ω : Set _))
    (u : Space n → ℝ) (hu : ContDiffOn ℝ 2 u (closure (Ω : Set _))) :
    ContDiff ℝ 2 (compactPart β u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ tsupport β
  · exact β.contDiffAt.mul (hu.contDiffAt
      (mem_of_superset (Ω.isOpen.mem_nhds (hβ hy)) subset_closure))
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hy] with z hz
    simp [compactPart, hz]

/-- A cutoff can be chosen strictly between the collar sphere and twice its radius. -/
theorem cutoff : CutoffStatement := by
  intro n Ω x r hr hball u hu
  let β : ContDiffBump x := ⟨4 * r / 3, 5 * r / 3, by linarith, by linarith⟩
  have hri : r < β.rIn := by dsimp [β]; linarith
  have hro : β.rOut < 2 * r := by dsimp [β]; linarith
  have hβ : tsupport β ⊆ (Ω : Set _) := by
    rw [β.tsupport_eq]
    exact (closedBall_subset_closedBall hro.le).trans hball
  have hinner (y : Space n) (hy : y ∈ closedBall x r) :
      remainder β u =ᶠ[𝓝 y] (0 : Space n → ℝ) := by
    have hyb : y ∈ ball x β.rIn := lt_of_le_of_lt hy hri
    filter_upwards [β.eventuallyEq_one_of_mem_ball hyb] with z hz
    simp [remainder, hz]
  have houter (y : Space n) (hy : y ∈ frontier (Ω : Set _)) :
      remainder β u =ᶠ[𝓝 y] u := by
    have hdist := (P201.GreenConstruction.collar_outer_boundary_germ Ω hr hball hy).1
    have hysupp : y ∉ tsupport β := by
      rw [β.tsupport_eq]
      exact not_le_of_gt (hro.trans hdist)
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hysupp] with z hz
    simp [remainder, hz]
  refine ⟨β, hri, hro, compactPart_contDiff Ω x β hβ u hu,
    β.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans hβ, ?_,
    (contDiffOn_const.sub β.contDiff.contDiffOn).mul hu, hinner, houter, ?_⟩
  · simp [compactPart, β.one_of_mem_closedBall (mem_closedBall_self β.rIn_pos.le)]
  · intro y hy
    classical
    by_cases hyo : y ∈ frontier (Ω : Set _)
    · simpa [outerValues, hyo] using (houter y hyo).eq_of_nhds
    · have hys : y ∈ sphere x r :=
        (P201.GreenConstruction.frontier_collar_subset Ω x r hy).resolve_left hyo
      have hyb : y ∈ closedBall x r := sphere_subset_closedBall hys
      simpa [outerValues, hyo] using (hinner y hyb).eq_of_nhds

/-- Select a genuine trace map; the upstream collar theorem applies to every such map. -/
theorem collar_data : CollarDataStatement := by
  intro m Ω x g hg
  obtain ⟨r, hr, hball, hC, w, w₂, hw, _, hΔ, htrace⟩ := hg
  obtain ⟨T, L, hsmooth, _, hright, hkernel⟩ :=
    P201.Trace.exact_trace m (collar Ω x r) hC
  let D : P201Specs.NormalTrace.TraceData (collar Ω x r) hC :=
    ⟨T, L, hsmooth, hright, hkernel⟩
  obtain ⟨τ, hτ, _, hflux⟩ := htrace D
  exact ⟨r, hr, hball, hC, w, D, τ, hw, hΔ, hτ, hflux⟩

/-- The outer boundary is a literal part of the collar boundary. -/
theorem outer_frontier_subset {n : ℕ} (Ω : Domain n) (x : Space n) (r : ℝ)
    (hr : 0 < r) (hball : closedBall x (2 * r) ⊆ (Ω : Set _)) :
    frontier (Ω : Set _) ⊆ frontier (collar Ω x r : Set (Space n)) := by
  intro y hy
  have hd := (P201.GreenConstruction.collar_outer_boundary_germ Ω hr hball hy).1
  have hyE : y ∈ (closedBall x r)ᶜ := by
    change ¬dist y x ≤ r
    linarith
  have he := frontier_inter_open_inter (s := (Ω : Set (Space n)))
    (t := (closedBall x r)ᶜ) isClosed_closedBall.isOpen_compl
  have hym : y ∈ frontier (Ω : Set _) ∩ (closedBall x r)ᶜ := ⟨hy, hyE⟩
  rw [← he] at hym
  change y ∈ frontier ((Ω : Set (Space n)) ∩ (closedBall x r)ᶜ)
  exact hym.1

/-- No boundary is lost when the interior ball is removed. -/
theorem collar_frontier : FrontierStatement := by
  intro m Ω x r hr hball
  apply subset_antisymm (P201.GreenConstruction.frontier_collar_subset Ω x r)
  intro y hy
  rcases hy with hy | hy
  · exact outer_frontier_subset Ω x r hr hball hy
  · have hyΩ := (P201.GreenConstruction.collar_inner_boundary_germ Ω hr hball hy).1
    have hyE : y ∈ frontier ((closedBall x r)ᶜ) := by
      rwa [frontier_compl, frontier_closedBall x hr.ne']
    have he := frontier_inter_open_inter (s := (closedBall x r)ᶜ) Ω.isOpen
    have hym : y ∈ frontier ((closedBall x r)ᶜ) ∩ (Ω : Set _) := ⟨hyE, hyΩ⟩
    rw [← he] at hym
    change y ∈ frontier ((Ω : Set (Space (m+1))) ∩ (closedBall x r)ᶜ)
    simpa only [inter_comm] using hym.1

/-- Restriction to the outer boundary preserves the physical Hausdorff measure,
including H⁰, which is the endpoint counting convention. -/
theorem outer_measure : OuterMeasureStatement := by
  intro m Ω x r hr hball
  simp only [P201Specs.boundaryMeasure, P102.Trace.Ordinary.boundaryMeasure]
  rw [Measure.restrict_restrict measurableSet_frontier]
  congr 1
  exact inter_eq_left.mpr (outer_frontier_subset Ω x r hr hball)

lemma geometric_normal_congr {m : ℕ} (A B : Domain (m+1)) (p v : Space (m+1))
    (hA : (A : Set _) =ᶠ[𝓝 p] (B : Set _))
    (hS : frontier (A : Set _) =ᶠ[𝓝 p] frontier (B : Set _))
    (hn : P201Specs.SmoothFlux.GeometricNormalAt A p v) :
    P201Specs.SmoothFlux.GeometricNormalAt B p v := by
  let e := graphFrame m
  have ht : Tendsto e (𝓝 (e.symm p)) (𝓝 p) := by
    simpa using e.continuous.tendsto (e.symm p)
  have hg : (P102.Sobolev.Extension.geometricOpen e A : Set _) =ᶠ[𝓝 (e.symm p)]
      (P102.Sobolev.Extension.geometricOpen e B : Set _) := ht.eventually hA
  have hs : frontier (P102.Sobolev.Extension.geometricOpen e A : Set _) =ᶠ[𝓝 (e.symm p)]
      frontier (P102.Sobolev.Extension.geometricOpen e B : Set _) := by
    change frontier (e ⁻¹' (A : Set _)) =ᶠ[𝓝 (e.symm p)] frontier (e ⁻¹' (B : Set _))
    have heA : e ⁻¹' frontier (A : Set _) = frontier (e ⁻¹' (A : Set _)) :=
      e.toHomeomorph.preimage_frontier _
    have heB : e ⁻¹' frontier (B : Set _) = frontier (e ⁻¹' (B : Set _)) :=
      e.toHomeomorph.preimage_frontier _
    rw [← heA, ← heB]
    exact ht.eventually hS
  exact P102.U4.GraphArea.outward_congr hg hs hn

/-- The outward normal on the collar is already an outward normal on Ω.
The assertion uses germ geometry and the physical measure restriction. -/
theorem outer_normal : OuterNormalStatement := by
  intro m Ω x r hr hball ν hν
  have hle : P201Specs.boundaryMeasure Ω ≤ P201Specs.boundaryMeasure (collar Ω x r) := by
    rw [← outer_measure Ω x r hr hball]
    exact Measure.restrict_le_self
  refine ⟨hν.1.mono_measure hle, ?_⟩
  filter_upwards [ae_mono hle hν.2,
    P102.Trace.Ordinary.boundaryMeasure_ae_frontier Ω] with p hp hpf
  have hd := (P201.GreenConstruction.collar_outer_boundary_germ Ω hr hball hpf).1
  have hpE : p ∈ (closedBall x r)ᶜ := by
    change ¬dist p x ≤ r
    linarith
  have hS : frontier (collar Ω x r : Set (Space (m+1))) =ᶠ[𝓝 p]
      frontier (Ω : Set (Space (m+1))) := by
    have he := frontier_inter_open_inter (s := (Ω : Set (Space (m+1))))
      (t := (closedBall x r)ᶜ) isClosed_closedBall.isOpen_compl
    filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hpE] with y hy
    have he' := congrArg (fun A : Set (Space (m+1)) => y ∈ A) he
    change (y ∈ frontier ((Ω : Set (Space (m+1))) ∩ (closedBall x r)ᶜ)) =
      (y ∈ frontier (Ω : Set (Space (m+1))))
    simpa only [mem_inter_iff, hy, and_true] using he'
  apply geometric_normal_congr (collar Ω x r) Ω p (ν p) _ hS hp
  filter_upwards [(P201.GreenConstruction.collar_outer_boundary_germ Ω hr hball hpf).2]
    with y hy
  exact propext hy

/-- An outer-supported collar integral is exactly the original boundary integral.
This uses no continuity or regularity of the chosen integrand. -/
theorem outer_integral : OuterIntegralStatement := by
  intro m Ω x r hr hball u f
  classical
  have he : (fun y => outerValues Ω u y * f y) =
      (frontier (Ω : Set (Space (m+1)))).indicator (fun y => u y * f y) := by
    funext y
    by_cases hy : y ∈ frontier (Ω : Set (Space (m+1))) <;> simp [outerValues, hy]
  rw [he]
  constructor
  · rw [integrable_indicator_iff measurableSet_frontier]
    change Integrable _ ((boundaryMeasure (collar Ω x r)).restrict
      (frontier (Ω : Set (Space (m+1))))) ↔ _
    rw [outer_measure Ω x r hr hball]
  · rw [integral_indicator measurableSet_frontier]
    change (∫ y, u y * f y ∂((boundaryMeasure (collar Ω x r)).restrict
      (frontier (Ω : Set (Space (m+1)))))) = _
    rw [outer_measure Ω x r hr hball]

/-- Vanishing near the inner sphere is germ vanishing of the actual function,
so its coordinate Laplacian vanishes there without any Sobolev assumption. -/
theorem remainder_volume : RemainderVolumeStatement := by
  intro n Ω x r u β hβ
  have hz (y : Space n) (hy : y ∈ closedBall x r) :
      laplacian (remainder β u) y = 0 := by
    have hlocal := hβ.2.2.2.2.2.2.2.1 y hy
    rw [P201.Weyl.laplacian_eq_of_eventuallyEq hlocal]
    exact ((P201.MeanValues.harmonic_bridge (⊤ : Domain n) (0 : Space n → ℝ)).mpr
      (InnerProductSpace.harmonicOnNhd_const 0)).2 y (mem_univ y)
  refine ⟨hz, ?_⟩
  intro g
  have he : (Ω : Set (Space n)).indicator (fun y => g y * laplacian (remainder β u) y) =
      (collar Ω x r : Set (Space n)).indicator
        (fun y => g y * laplacian (remainder β u) y) := by
    funext y
    classical
    by_cases hyΩ : y ∈ Ω
    · by_cases hyB : y ∈ closedBall x r
      · have hyC : y ∉ collar Ω x r := fun h => h.2 hyB
        simp [indicator_of_mem hyΩ, indicator_of_notMem hyC, hz y hyB]
      · have hyC : y ∈ collar Ω x r := ⟨hyΩ, hyB⟩
        rw [indicator_of_mem hyΩ, indicator_of_mem hyC]
    · have hyC : y ∉ collar Ω x r := fun h => hyΩ h.1
      rw [indicator_of_notMem hyΩ, indicator_of_notMem hyC]
  constructor
  · rw [← integrable_indicator_iff Ω.isOpen.measurableSet,
      ← integrable_indicator_iff (collar Ω x r).isOpen.measurableSet, he]
  · rw [← integral_indicator Ω.isOpen.measurableSet,
      ← integral_indicator (collar Ω x r).isOpen.measurableSet, he]

/-- Realize the remainder on the collar using only C² on the original
closure; arbitrary ambient behavior of u is immaterial. -/
theorem remainder_data : RemainderDataStatement := by
  intro n Ω hb x r u β hβ
  have hsub : (collar Ω x r : Set (Space n)) ⊆ (Ω : Set _) := fun _ h => h.1
  have hf : ContDiffOn ℝ 2 (remainder β u) (closure (collar Ω x r : Set _)) :=
    hβ.2.2.2.2.2.2.1.mono (closure_mono hsub)
  exact closure_laplacian_realization (collar Ω x r) (hb.subset hsub) (remainder β u) hf

/-- The L² collar data give integrability; the zero inner germ extends that
integrability to Ω without estimating g at its singular pole. -/
theorem remainder_integrable : RemainderIntegrabilityStatement := by
  intro n Ω hb x r u β hβ g w hw
  obtain ⟨z, q, hz, hq, hΔ⟩ := remainder_data Ω hb x r u β hβ
  apply ((remainder_volume Ω x r u β hβ).2 g).1.mpr
  have hg : MemLp g 2 (domainMeasure (collar Ω x r)) := (Lp.memLp (hUnderlying _ 1 w)).ae_eq hw
  have hd : MemLp (laplacian (remainder β u)) 2 (domainMeasure (collar Ω x r)) :=
    (Lp.memLp q).ae_eq hq
  exact hg.integrable_mul hd

/-- The removed positive ball separates the collar closure from the singular
pole, so the original continuous Green representative is continuous there. -/
lemma green_continuousOn_collar {n : ℕ} (Ω : Domain n) (x : Space n)
    (r : ℝ) (hr : 0 < r) (g : Space n → ℝ) (hg : IsGreenFunction Ω x g) :
    ContinuousOn g (closure (collar Ω x r : Set (Space n))) := by
  apply hg.2.2.2.2.1.mono
  have hsub : (collar Ω x r : Set (Space n)) ⊆ (Ω : Set _) := fun _ h => h.1
  have hsep : closure (collar Ω x r : Set (Space n)) ⊆ (ball x r)ᶜ :=
    closure_minimal (fun _ h hy => h.2 (ball_subset_closedBall hy)) isOpen_ball.isClosed_compl
  intro y hy
  refine ⟨closure_mono hsub hy, ?_⟩
  simp only [mem_singleton_iff]
  intro hyx
  subst y
  exact hsep hy (mem_ball_self hr)

/-- Physical trace agreement follows from continuity on the collar closure;
the cutoff's pointwise boundary separation then identifies the datum. -/
theorem remainder_trace : RemainderTraceStatement := by
  intro m Ω x r u β hβ hC D z hz
  have hsub : (collar Ω x r : Set (Space (m + 1))) ⊆ (Ω : Set _) := fun _ h => h.1
  have hf : ContinuousOn (remainder β u) (closure (collar Ω x r : Set _)) :=
    hβ.2.2.2.2.2.2.1.continuousOn.mono (closure_mono hsub)
  have ht := continuous_trace (collar Ω x r) hC D z (remainder β u) hf hz
  filter_upwards [ht, P102.Trace.Ordinary.boundaryMeasure_ae_frontier (collar Ω x r)]
    with y hy hyf
  exact hy.trans (hβ.2.2.2.2.2.2.2.2.2 hyf)

/-- Apply the actual weak second Green identity, with the original collar
normal trace. The opposing term is retained explicitly until boundary
localization proves that it vanishes. -/
theorem remainder_green : RemainderGreenStatement := by
  intro m Ω x r u β hβ hC D w τ g hw hΔw hτ z q hq hΔz
  have hg : MemLp g 2 (domainMeasure (collar Ω x r)) :=
    (Lp.memLp (hUnderlying _ 1 w)).ae_eq hw
  have hd : MemLp (laplacian (remainder β u)) 2 (domainMeasure (collar Ω x r)) :=
    (Lp.memLp q).ae_eq hq
  have hvol := (remainder_volume Ω x r u β hβ).2 g
  refine ⟨hvol.1.mpr (hg.integrable_mul hd), ?_⟩
  obtain ⟨τw, σ, hτw, hσ, hgreen⟩ :=
    P201.NormalTrace.green (collar Ω x r) hC D w z 0 q hΔw hΔz
  have heτ : τw = τ := P201.NormalTrace.pairing_unique D (hGradient w) 0 τw τ hτw hτ
  rw [heτ] at hgreen
  have hevol : (∫ y in collar Ω x r,
      hUnderlying (collar Ω x r) 1 w y * q y -
        hUnderlying (collar Ω x r) 1 z y * (0 : Lp ℝ (collar Ω x r) 2) y) =
      ∫ y in Ω, g y * laplacian (remainder β u) y := by
    rw [hvol.2]
    apply integral_congr_ae
    filter_upwards [hw, hq, Lp.coeFn_zero ℝ 2 (domainMeasure (collar Ω x r))]
      with y hyw hyq hy0
    simp only [Pi.zero_apply] at hy0
    rw [hyw, hyq, hy0, mul_zero, sub_zero]
  rw [hevol] at hgreen
  refine ⟨σ, hσ, ?_⟩
  linarith only [hgreen]

/-- All geometric transport in the physical outer boundary flux follows from
the previously proved measure and normal transport. -/
theorem outer_flux : OuterFluxStatement := by
  intro m Ω x r hr hball hC D τ vi ν u b hν hb hi hτ
  let f := fun y => ∑ i,
    Trace.inclusion (collar Ω x r) hC (D.trace (vi i)) y * ν y i
  have hae : (fun y => Trace.inclusion (collar Ω x r) hC b y * f y)
      =ᵐ[boundaryMeasure (collar Ω x r)] fun y => outerValues Ω u y * f y := by
    filter_upwards [hb] with y hy
    rw [hy]
  have htransport := outer_integral Ω x r hr hball u f
  exact ⟨outer_normal Ω x r hr hball ν hν, htransport.1.mp (hi.congr hae),
    hτ.trans ((integral_congr_ae hae).trans htransport.2)⟩

/-- Nonsingular collar localization, with the inner and outer boundary terms
identified using the physical trace rather than an evaluation premise. -/
theorem localization : FullStatement := by
  intro m Ω hb hboundary x hx g hg hcollar u hu
  obtain ⟨r, hr, hball, hC, w, D, τ, hw, hΔw, hτ, ν, vi, hν, hvi, hflux⟩ :=
    collar_data Ω x g hcollar
  obtain ⟨β, hβ⟩ := cutoff Ω x r hr hball u hu
  obtain ⟨z, q, hz, hq, hΔz⟩ := remainder_data Ω hb x r u β hβ
  have hbphys := remainder_trace Ω x r u β hβ hC D z hz
  obtain ⟨hInt, σ, hσ, hsecond⟩ :=
    remainder_green Ω x r u β hβ hC D w τ g hw hΔw hτ z q hq hΔz
  have hzero : σ (D.trace w) = 0 :=
    opposing_trace_zero Ω hb x r hr hC D g hg w hw u β hβ.1 z q hz hq σ hσ
  have hvolume : τ (D.trace z) = -(∫ y in Ω, g y * laplacian (remainder β u) y) := by
    rw [hzero, zero_sub] at hsecond
    exact hsecond
  obtain ⟨houterν, houterInt, houterFlux⟩ := outer_flux Ω x r hr hball hC D τ vi ν u
    (D.trace z) hν hbphys (hflux (D.trace z)).1 (hflux (D.trace z)).2
  exact ⟨r, hr, hball, hC, β, w, D, τ, D.trace z, hβ, hw, hΔw, hτ, hbphys,
    hInt, hvolume, ν, vi, houterν, hvi, houterInt, houterFlux⟩

end P201.GreenCollarLocalization
