import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinHilbertSchmidtBridge
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.L2HilbertSchmidt
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinSymmetricOperator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinKernelPatching
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Separation.Hausdorff

import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace ExpandedFA.PartIV.KreinHilbertSchmidtBridge
open KreinSpectralKernel

/-- Equality is simultaneous once continuity in a separable test space has
actually been established. -/
theorem common_null_set : Spec.CommonNullSet := by
  intro Ω E Y _ μ _ _ _ _ L R hcont heq
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense E
  have hall : ∀ᵐ ω ∂μ, ∀ x ∈ D, L ω x = R ω x :=
    (ae_ball_iff hD).2 (fun x _ => heq x)
  filter_upwards [hcont, hall] with ω hω hDω
  exact fun x => congrFun (Continuous.ext_on hdense hω.1 hω.2 hDω) x

theorem spectral_test_identity : Spec.SpectralTestIdentity := by
  intro H _ _ _ p F G S M haction f
  exact (M.graph_iff _ _).mp (haction f)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [InnerProductSpace ℂ H] [CompleteSpace H] in
lemma continuous_memLp_interval (v : ℝ → H) (hv : Continuous v) (R : ℝ) :
    MemLp v 2 (intervalMeasure R) := by
  apply (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mpr
  exact (hv.norm.pow 2).integrableOn_Icc

omit [CompleteSpace H] in
/-- The local integral is genuine Bochner integration, obtained using the
L²–L² Hölder product. -/
lemma synthesis_integrable {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) (f : Lp ℂ 2 μ) :
    Integrable (fun t => f t • v t) μ := by
  exact memLp_one_iff_integrable.mp ((Lp.memLp f).smul hv)

/-- The canonical synthesis operator, built from the continuous Hölder pairing.
Its value is identified with the actual integral below. -/
def synthesisOperator {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) : Lp ℂ 2 μ →L[ℂ] H :=
  ((ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).lpPairing μ 2 2).flip
    (hv.toLp v)

lemma synthesisOperator_apply {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) (f : Lp ℂ 2 μ) :
    synthesisOperator μ v hv f = ∫ t, f t • v t ∂μ := by
  rw [synthesisOperator, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp] with t ht
  simp [ht]

theorem local_synthesis : Spec.LocalSynthesis := by
  intro H _ _ _ v hv R
  have hmem := continuous_memLp_interval v hv R
  exact ⟨synthesisOperator (intervalMeasure R) v hmem,
    synthesis_integrable _ v hmem, synthesisOperator_apply _ v hmem⟩

/-- The adjoint has the concrete scalar coefficient representative. -/
lemma synthesisOperator_adjoint {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) (w : H) :
    ContinuousLinearMap.adjoint (synthesisOperator μ v hv) w =
      (hv.inner_const (𝕜 := ℂ) w).toLp (fun t => ⟪v t, w⟫_ℂ) := by
  apply ext_inner_right ℂ
  intro f
  rw [ContinuousLinearMap.adjoint_inner_left, synthesisOperator_apply,
    ← integral_inner (synthesis_integrable μ v hv f), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hv.inner_const (𝕜 := ℂ) w).coeFn_toLp] with t ht
  simp [ht, inner_smul_right, inner_conj_symm, mul_comm]

omit [CompleteSpace H] in
lemma integral_sq_norm {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) :
    (∫ t, ‖v t‖ ^ 2 ∂μ) = ‖hv.toLp v‖ ^ 2 := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hv.toLp v))
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) (hv.toLp v) (hv.toLp v))] at h
  simp only [inner_self_eq_norm_sq_to_K, RCLike.re_ofReal_pow] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [hv.coeFn_toLp] with t ht
  rw [ht]

omit [CompleteSpace H] in
/-- Separability makes every orthonormal family countable, also in the zero
space. The proof uses coefficient supports on an actual countable dense set. -/
lemma countable_orthonormal [TopologicalSpace.SeparableSpace H]
    {ι : Type} (e : ι → H) (he : Orthonormal ℂ e) : Countable ι := by
  classical
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense H
  have hcover : (⋃ d ∈ D, {i | ⟪e i, d⟫_ℂ ≠ 0}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro i
    by_contra hi
    have hz : ∀ d ∈ D, ⟪e i, d⟫_ℂ = 0 := by
      intro d hd
      by_contra h
      exact hi (Set.mem_iUnion.mpr ⟨d, Set.mem_iUnion.mpr ⟨hd, h⟩⟩)
    have hfun : (fun x : H => ⟪e i, x⟫_ℂ) = fun _ => 0 :=
      Continuous.ext_on hdense (continuous_const.inner continuous_id) continuous_const hz
    have hei : e i = 0 := inner_self_eq_zero.mp (congrFun hfun (e i))
    have hnorm := he.norm_eq_one i
    simp [hei] at hnorm
  have hc : (⋃ d ∈ D, {i | ⟪e i, d⟫_ℂ ≠ 0}).Countable :=
    hD.biUnion fun d _ => ExpandedFA.Hilbert.OrthonormalExpansion.countable_coefficient_support
      ℂ H ι e he d
  rw [hcover] at hc
  exact Set.countable_univ_iff.mp hc

omit [CompleteSpace H] in
lemma lintegral_sq_norm {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) :
    (∫⁻ t, ENNReal.ofReal (‖v t‖ ^ 2) ∂μ) =
      ENNReal.ofReal (‖hv.toLp v‖ ^ 2) := by
  rw [← integral_sq_norm μ v hv]
  exact (ofReal_integral_eq_lintegral_ofReal
    ((memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv)
    (ae_of_all _ fun t => sq_nonneg _)).symm

set_option maxHeartbeats 1000000 in
/-- Parseval in the target followed by Tonelli gives the exact square, with
no positivity-of-radius or nonzero-space assumption. -/
lemma synthesisOperator_square [TopologicalSpace.SeparableSpace H]
    {X : Type} [MeasurableSpace X] (μ : Measure X)
    (v : X → H) (hv : MemLp v 2 μ) :
    TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue
      (synthesisOperator μ v hv) = ENNReal.ofReal (∫ t, ‖v t‖ ^ 2 ∂μ) := by
  classical
  let J := synthesisOperator μ v hv
  obtain ⟨E, hE⟩ := Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset
    ℂ (Lp ℂ 2 μ)
  obtain ⟨D, hD⟩ := Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset ℂ H
  let : Countable D := countable_orthonormal (Subtype.val : D → H) hD.1
  rw [TraceIdeals.HilbertSchmidtDefinitions.squareSum_in_basis J _ hE,
    TraceIdeals.HilbertSchmidtDefinitions.adjoint_basis_identity J _ _ hE hD]
  change (∑' d : D, ENNReal.ofReal (‖ContinuousLinearMap.adjoint J d.val‖ ^ 2)) = _
  have hj (d : D) : ENNReal.ofReal (‖ContinuousLinearMap.adjoint J d.val‖ ^ 2) =
      ∫⁻ t : X, ENNReal.ofReal (‖⟪v t, d.val⟫_ℂ‖ ^ 2) ∂μ := by
    rw [show J = synthesisOperator μ v hv from rfl, synthesisOperator_adjoint]
    exact (lintegral_sq_norm (H := ℂ) μ _ (hv.inner_const (𝕜 := ℂ) d.val)).symm
  have hton := lintegral_tsum (μ := μ)
    (f := fun (d : D) (t : X) => ENNReal.ofReal (‖⟪v t, d.val⟫_ℂ‖ ^ 2))
    (fun d => ((hv.inner_const (𝕜 := ℂ) d.val).aestronglyMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal)
  calc
    _ = ∑' d : D, ∫⁻ t : X, ENNReal.ofReal (‖⟪v t, d.val⟫_ℂ‖ ^ 2) ∂μ :=
      tsum_congr hj
    _ = ∫⁻ t : X, ∑' d : D, ENNReal.ofReal (‖⟪v t, d.val⟫_ℂ‖ ^ 2) ∂μ := hton.symm
    _ = ∫⁻ t : X, ENNReal.ofReal (‖v t‖ ^ 2) ∂μ := by
      apply lintegral_congr
      intro t
      simp_rw [norm_inner_symm (𝕜 := ℂ) (v t)]
      exact (TraceIdeals.HilbertSchmidtDefinitions.parseval_ennreal _ hD (v t)).symm
    _ = _ := (lintegral_sq_norm μ v hv).trans
      (congrArg ENNReal.ofReal (integral_sq_norm μ v hv).symm)

theorem local_synthesis_energy : Spec.LocalSynthesisEnergy := by
  intro H _ _ _ _ v hv R
  have hmem := continuous_memLp_interval v hv R
  exact ⟨synthesisOperator (intervalMeasure R) v hmem,
    synthesisOperator_apply _ v hmem, synthesisOperator_square _ v hmem⟩

set_option maxHeartbeats 1000000 in
/-- Reconstruct the product-L² kernel from all matrix coefficients in the
product basis. No compactness, nonzero-measure or countability is assumed. -/
theorem reverse_scalar_kernel : Spec.ReverseScalarKernel := by
  intro X Y _ _ μ ν _ _ T hT
  classical
  obtain ⟨E, hE⟩ := Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset ℂ (Lp ℂ 2 ν)
  obtain ⟨D, hD⟩ := Hilbert.OrthonormalExpansion.exists_maximal_orthonormal_subset ℂ (Lp ℂ 2 μ)
  let e : E → Lp ℂ 2 ν := Subtype.val
  let d : D → Lp ℂ 2 μ := Subtype.val
  have hprod := PartV.L2HilbertSchmidt.product_basis μ ν e d hE hD
  let b : HilbertBasis (E × D) ℂ (Lp ℂ 2 (μ.prod ν)) :=
    HilbertBasis.mk hprod.1
      ((Hilbert.OrthonormalExpansion.maximal_iff_total ℂ _ _ _ hprod.1).mp hprod).ge
  have hb : ⇑b = fun p : E × D => PartV.L2HilbertSchmidt.productVector μ ν (d p.2) (e p.1) :=
    HilbertBasis.coe_mk _ _
  have hmatrix : (∑' p : E × D, ENNReal.ofReal (‖⟪d p.2, T (e p.1)⟫_ℂ‖ ^ 2)) < ∞ := by
    rw [ENNReal.tsum_prod (f := fun (i : E) (j : D) => ENNReal.ofReal (‖⟪d j, T (e i)⟫_ℂ‖ ^ 2))]
    change TraceIdeals.HilbertSchmidtDefinitions.Spec.MatrixSquareSumValue T e d < ∞
    have heq := (TraceIdeals.HilbertSchmidtDefinitions.squareSum_in_basis T e hE).trans
      (TraceIdeals.HilbertSchmidtDefinitions.matrix_identity T e d hD)
    change TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue T < ∞ at hT
    exact heq ▸ hT
  have hs : Summable (fun p : E × D => ‖⟪d p.2, T (e p.1)⟫_ℂ‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using ENNReal.summable_toReal hmatrix.ne
  have hc : Memℓp (fun p : E × D => ⟪d p.2, T (e p.1)⟫_ℂ) 2 := by
    apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mpr
    simpa using hs
  let c : lp (fun _ : E × D => ℂ) 2 := ⟨_, hc⟩
  let k : Lp ℂ 2 (μ.prod ν) := b.repr.symm c
  have hcoeff (p : E × D) :
      ⟪PartV.L2HilbertSchmidt.productVector μ ν (d p.2) (e p.1), k⟫_ℂ =
        ⟪d p.2, T (e p.1)⟫_ℂ := by
    rw [← congrFun hb p, ← b.repr_apply_apply]
    change b.repr (b.repr.symm c) p = _
    rw [b.repr.apply_symm_apply]
  have hTe (i : E) : PartV.L2Kernel.kernelOperator μ ν k (e i) = T (e i) := by
    apply sub_eq_zero.mp
    apply PartV.L2HilbertSchmidt.eq_zero_of_basis_coefficients d hD
    intro j
    rw [inner_sub_right, ← PartV.L2HilbertSchmidt.productVector_coefficient]
    exact sub_eq_zero.mpr (hcoeff (i, j))
  have hk : PartV.L2Kernel.kernelOperator μ ν k = T := by
    ext1 u
    have hu := (Hilbert.OrthonormalExpansion.expansion ℂ _ E e hE u).1
    have ht := (PartV.L2Kernel.kernelOperator μ ν k).hasSum hu
    have ht' := T.hasSum hu
    simp only [map_smul, hTe] at ht
    simp only [map_smul] at ht'
    exact ht.unique ht'
  refine ⟨k, hk, ?_⟩
  intro k' hk'
  change PartV.L2Kernel.kernelOperator μ ν k' = T at hk'
  apply sub_eq_zero.mp
  apply PartV.L2HilbertSchmidt.eq_zero_of_basis_coefficients _ hprod
  intro p
  rw [inner_sub_right, PartV.L2HilbertSchmidt.productVector_coefficient,
    PartV.L2HilbertSchmidt.productVector_coefficient]
  change ⟪d p.2, PartV.L2Kernel.kernelOperator μ ν k' (e p.1)⟫_ℂ -
    ⟪d p.2, PartV.L2Kernel.kernelOperator μ ν k (e p.1)⟫_ℂ = 0
  rw [hk', hk, sub_self]

/-- The degenerate Gram realization requires no division or basis choice. -/
theorem zero_kernel : Spec.ZeroKernel := by
  intro H _ _ _ p F G S M hv
  refine ⟨{
    h := fun _ _ => 0
    measurable := aestronglyMeasurable_zero
    local_square := fun _ _ => MemLp.zero
    fiber_properties := ?_
    represents := ?_
    energy := ?_ }⟩
  · exact ae_of_all _ fun ξ => ⟨fun _ => MemLp.zero,
      ae_of_all _ fun _ => (coordinateFiber (M.multiplicity ξ)).zero_mem,
      ae_of_all _ fun _ => by simp, fun φ => by simp⟩
  · intro R hR f
    have hzero : (∫ t, f t • G.vectors t ∂intervalMeasure R) = 0 := by simp [hv]
    rw [hzero, map_zero]
    filter_upwards [Lp.coeFn_zero FiberSpace 2 M.μ] with ξ hξ
    simpa only [smul_zero, integral_zero, Pi.zero_apply] using hξ
  · intro R hR
    simp [hv]

private def SupportedTest (n : ℕ) :=
  {φ : LineTest // tsupport (φ : ℝ → ℂ) ⊆ Icc (-(n + 1 : ℝ)) (n + 1)}

private def testJet (n : ℕ) (φ : SupportedTest n) :
    C(ℝ, ℂ) × C(ℝ, ℂ) × C(ℝ, ℂ) :=
  (⟨φ.val, φ.val.continuous⟩,
    ⟨deriv (φ.val : ℝ → ℂ), (contDiff_infty_iff_deriv.mp φ.val.contDiff).2.continuous⟩,
    ⟨deriv (deriv (φ.val : ℝ → ℂ)),
      (contDiff_infty_iff_deriv.mp
        (contDiff_infty_iff_deriv.mp φ.val.contDiff).2).2.continuous⟩)

private instance supportedTestTopology (n : ℕ) : TopologicalSpace (SupportedTest n) :=
  TopologicalSpace.induced (testJet n) inferInstance

private instance supportedTestSecondCountable (n : ℕ) :
    SecondCountableTopology (SupportedTest n) :=
  (Topology.IsInducing.induced (testJet n)).secondCountableTopology

private lemma continuous_supported_pairing {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (n : ℕ) (h : ℝ → H)
    (hh : IntegrableOn h (Icc (-(n + 1 : ℝ)) (n + 1)))
    (j : SupportedTest n → C(ℝ, ℂ)) (hj : Continuous j)
    (hs : ∀ φ : SupportedTest n,
      tsupport (j φ : ℝ → ℂ) ⊆ Icc (-(n + 1 : ℝ)) (n + 1)) :
    Continuous (fun φ : SupportedTest n => ∫ t : ℝ, j φ t • h t) := by
  have hc : Continuous (fun x : SupportedTest n × ℝ => j x.1 x.2) :=
    continuous_eval.comp (hj.prodMap continuous_id)
  have ht := continuousOn_integral_bilinear_of_locally_integrable_of_compact_support
    (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] H →L[ℂ] H).flip
    isCompact_Icc (s := univ) hc.continuousOn
    (fun φ t _ ht => image_eq_zero_of_notMem_tsupport (fun hx => ht (hs φ hx))) hh
  simpa only [continuousOn_univ, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply] using ht

private lemma supported_pairings_continuous {H : Type} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (n : ℕ) (h : ℝ → H)
    (hh : IntegrableOn h (Icc (-(n + 1 : ℝ)) (n + 1))) :
    Continuous (fun φ : SupportedTest n => ∫ t : ℝ, (φ.val : ℝ → ℂ) t • h t) ∧
    Continuous (fun φ : SupportedTest n =>
      ∫ t : ℝ, deriv (deriv (φ.val : ℝ → ℂ)) t • h t) := by
  have hj : Continuous (testJet n) := continuous_induced_dom
  exact ⟨continuous_supported_pairing n h hh (fun φ => (testJet n φ).1) hj.fst
      (fun φ => φ.property),
    continuous_supported_pairing n h hh (fun φ => (testJet n φ).2.2) hj.snd.snd
      (fun φ => tsupport_deriv_subset.trans (tsupport_deriv_subset.trans φ.property))⟩

private lemma test_supported (φ : LineTest) :
    ∃ n : ℕ, tsupport (φ : ℝ → ℂ) ⊆ Icc (-(n + 1 : ℝ)) (n + 1) := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt R
  refine ⟨n, fun t ht => ?_⟩
  have hnorm := hR t ht
  have habs : |t| ≤ (n + 1 : ℝ) := by simpa only [Real.norm_eq_abs] using hnorm.trans (by linarith)
  exact abs_le.mp habs

/-- Fixed-support tests carry the topology induced by their first two
continuous derivatives. It is second countable; the integral pairings are
continuous by local integrability. Countable exhaustion then gives ONE null
set for ALL native compact smooth tests. -/
theorem native_common_null_set {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (parameter : Ω → ℝ) (h : Ω → ℝ → FiberSpace)
    (hlocal : ∀ᵐ ξ ∂μ, ∀ n : ℕ, MemLp (h ξ) 2 (intervalMeasure (n + 1)))
    (heq : ∀ φ : LineTest, ∀ᵐ ξ ∂μ,
      (∫ t : ℝ, deriv (deriv (φ : ℝ → ℂ)) t • h ξ t) =
        (parameter ξ : ℂ) • ∫ t : ℝ, φ t • h ξ t) :
    ∀ᵐ ξ ∂μ, WeakEquation (parameter ξ) (h ξ) := by
  have hfixed (n : ℕ) : ∀ᵐ ξ ∂μ, ∀ φ : SupportedTest n,
      (∫ t : ℝ, deriv (deriv (φ.val : ℝ → ℂ)) t • h ξ t) =
        (parameter ξ : ℂ) • ∫ t : ℝ, φ.val t • h ξ t := by
    apply common_null_set μ
    · filter_upwards [hlocal] with ξ hξ
      have : IsFiniteMeasure (intervalMeasure (n + 1)) := by
        dsimp [intervalMeasure]
        infer_instance
      have hh : IntegrableOn (h ξ) (Icc (-(n + 1 : ℝ)) (n + 1)) :=
        (hξ n).integrable (by norm_num)
      obtain ⟨hc₀, hc₂⟩ := supported_pairings_continuous n (h ξ) hh
      exact ⟨hc₂, hc₀.const_smul (parameter ξ : ℂ)⟩
    · intro φ
      exact heq φ.val
  filter_upwards [ae_all_iff.mpr hfixed] with ξ hξ
  intro φ
  obtain ⟨n, hn⟩ := test_supported φ
  exact hξ n ⟨φ, hn⟩


open KreinSymmetricOperator
open scoped ContDiff

lemma second_deriv_projectTest (p : Bool) (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hs : HasCompactSupport f) :
    deriv (deriv (projectTest p f hf hs).val) =
      (projectTest p (deriv (deriv f))
        (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hf).2).2
        hs.deriv.deriv).val := by
  have hg : ContDiff ℝ ∞ (fun t => Spec.paritySign p * f (-t)) :=
    contDiff_const.mul (hf.comp contDiff_neg)
  have h₁ : deriv (projectTest p f hf hs).val =
      fun t => deriv f t + deriv (fun t => Spec.paritySign p * f (-t)) t := by
    funext t
    exact deriv_fun_add (hf.differentiable (by simp) t) (hg.differentiable (by simp) t)
  rw [h₁]
  have h₂ : deriv (fun t => deriv f t +
      deriv (fun t => Spec.paritySign p * f (-t)) t) =
        fun t => deriv (deriv f) t +
          deriv (deriv (fun t => Spec.paritySign p * f (-t))) t := by
    funext t
    exact deriv_fun_add
      ((contDiff_infty_iff_deriv.mp hf).2.differentiable (by simp) t)
      ((contDiff_infty_iff_deriv.mp hg).2.differentiable (by simp) t)
  rw [h₂, second_deriv_const_mul, second_deriv_comp_neg]
  rfl


/-- Extend the graph identity from the matching-parity representation to every
native compact smooth test by the actual upstream parity projection. -/
theorem native_spectral_test_identity
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} (G : KreinSymmetricOperator.Spec.GramData p F H)
    (S : Unbounded.Operator ℂ H H) (M : RealSpectralModel S)
    (haction : ∀ f : KreinSymmetricOperator.Spec.SmoothTest p,
      ∃ hf : KreinSymmetricOperator.Spec.testIntegral G.vectors f.val ∈ S.domain,
        S ⟨KreinSymmetricOperator.Spec.testIntegral G.vectors f.val, hf⟩ =
          KreinSymmetricOperator.Spec.testIntegral G.vectors (deriv (deriv f.val)))
    (φ : LineTest) :
    (M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors (deriv (deriv (φ : ℝ → ℂ)))) :
      ℝ → FiberSpace) =ᵐ[M.μ]
      fun ξ => (ξ : ℂ) • M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors φ) ξ := by
  have ht := spectral_test_identity G S M haction (projectTest p φ φ.contDiff φ.hasCompactSupport)
  rw [second_deriv_projectTest,
    integral_projectTest _ G.continuous_vectors G.parity,
    integral_projectTest _ G.continuous_vectors G.parity, map_add, map_add] at ht
  filter_upwards [ht, Lp.coeFn_add (M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors
    (deriv (deriv (φ : ℝ → ℂ)))) ) (M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors
    (deriv (deriv (φ : ℝ → ℂ)))) ),
    Lp.coeFn_add (M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors φ))
      (M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors φ))] with ξ hξ h₂ h₀
  rw [h₂, h₀, Pi.add_apply, Pi.add_apply, smul_add] at hξ
  exact smul_right_injective (R := ℂ) FiberSpace (by norm_num : (2 : ℂ) ≠ 0)
    (by simpa only [two_smul] using hξ)


lemma integral_toLp_compact {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℝ → ℂ) (R : ℝ) (hf : MemLp f 2 (intervalMeasure R))
    (hs : tsupport f ⊆ Icc (-R) R) (w : ℝ → E) :
    (∫ t, hf.toLp f t • w t ∂intervalMeasure R) = ∫ t : ℝ, f t • w t := by
  calc
    _ = ∫ t, f t • w t ∂intervalMeasure R := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with t ht
      rw [ht]
    _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => by
      rw [image_eq_zero_of_notMem_tsupport (fun hx => ht (hs hx)), zero_smul]

lemma represents_native_test
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} (G : KreinSymmetricOperator.Spec.GramData p F H)
    {S : Unbounded.Operator ℂ H H} (M : RealSpectralModel S)
    (h : ℝ → ℝ → FiberSpace)
    (hrep : ∀ R : ℝ, 0 < R → ∀ f : Lp ℂ 2 (intervalMeasure R),
      (M.U (∫ t, f t • G.vectors t ∂intervalMeasure R) : ℝ → FiberSpace) =ᵐ[M.μ]
        fun ξ => ∫ t, f t • h ξ t ∂intervalMeasure R)
    (φ : LineTest) :
    (M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors φ) : ℝ → FiberSpace) =ᵐ[M.μ]
      fun ξ => ∫ t : ℝ, φ t • h ξ t := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hs : tsupport (φ : ℝ → ℂ) ⊆ Icc (-(n + 1 : ℝ)) (n + 1) := by
    intro t ht
    have hnorm := hR t ht
    exact abs_le.mp (show |t| ≤ (n + 1 : ℝ) by
      simpa only [Real.norm_eq_abs] using hnorm.trans (by linarith))
  have hf := continuous_memLp_interval (H := ℂ) φ φ.continuous (n + 1)
  have heq := hrep (n + 1) (by positivity) (hf.toLp φ)
  rw [integral_toLp_compact _ _ hf hs] at heq
  apply heq.trans
  exact ae_of_all _ fun ξ => integral_toLp_compact _ _ hf hs (h ξ)

/-- A genuine local representation plus the supplied operator action yields
all native distribution equations on one scalar conull set. -/
theorem weakEquation_of_representation
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} (G : KreinSymmetricOperator.Spec.GramData p F H)
    (S : Unbounded.Operator ℂ H H) (M : RealSpectralModel S)
    (haction : ∀ f : KreinSymmetricOperator.Spec.SmoothTest p,
      ∃ hf : KreinSymmetricOperator.Spec.testIntegral G.vectors f.val ∈ S.domain,
        S ⟨KreinSymmetricOperator.Spec.testIntegral G.vectors f.val, hf⟩ =
          KreinSymmetricOperator.Spec.testIntegral G.vectors (deriv (deriv f.val)))
    (h : ℝ → ℝ → FiberSpace)
    (hlocal : ∀ᵐ ξ ∂M.μ, ∀ n : ℕ, MemLp (h ξ) 2 (intervalMeasure (n + 1)))
    (hrep : ∀ R : ℝ, 0 < R → ∀ f : Lp ℂ 2 (intervalMeasure R),
      (M.U (∫ t, f t • G.vectors t ∂intervalMeasure R) : ℝ → FiberSpace) =ᵐ[M.μ]
        fun ξ => ∫ t, f t • h ξ t ∂intervalMeasure R) :
    ∀ᵐ ξ ∂M.μ, WeakEquation ξ (h ξ) := by
  apply native_common_null_set M.μ id h hlocal
  intro φ
  let ψ : LineTest := ⟨deriv (deriv (φ : ℝ → ℂ)),
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp φ.contDiff).2).2,
    φ.hasCompactSupport.deriv.deriv, by simp⟩
  have h₀ := represents_native_test G M h hrep φ
  have h₂ := represents_native_test G M h hrep ψ
  have hs := native_spectral_test_identity G S M haction φ
  filter_upwards [h₀, h₂, hs] with ξ h₀ h₂ hs
  exact h₂.symm.trans (hs.trans (congrArg ((ξ : ℂ) • ·) h₀))

/-- The patched local Hilbert–Schmidt kernels satisfy the distributional
equation on the same scalar conull set as all their fiber properties. -/
theorem exists_kernel : KreinSpectralKernel.Spec.KernelExistence := by
  intro H _ _ _ _ p F G S M haction
  obtain ⟨K⟩ := KreinKernelPatching.exists_kernel G S M
  have hlocal : ∀ᵐ ξ ∂M.μ, ∀ n : ℕ, MemLp (K.h ξ) 2 (intervalMeasure (n + 1)) :=
    K.fiber_properties.mono fun _ hξ => hξ.1
  have hequation := weakEquation_of_representation G S M haction K.h hlocal K.represents
  refine ⟨{
    h := K.h
    measurable := K.measurable
    local_square := K.local_square
    fiber_properties := ?_
    represents := K.represents
    energy := K.energy
  }⟩
  filter_upwards [K.fiber_properties, hequation] with ξ hξ heq
  exact ⟨hξ.1, hξ.2.1, hξ.2.2, heq⟩


end ExpandedFA.PartIV.KreinHilbertSchmidtBridge
