import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.VectorLpReflexive
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.VectorLpDual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C14Reflexive
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Normed.Module.HahnBanach
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.SequenceDuals
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C01ExamplesComplete
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
universe u v w
namespace ExpandedFA.PartIV.VectorLpReflexive
open VectorLpRepresentationSpec
open P1.C04CanonicalMap.Spec

/-- This uses the literal integral pairing and the ordinary a.e. quotient. -/
theorem canonical_embedding_identity : VectorLpReflexiveSpec.CanonicalIdentity.{u,v} := by
  intro 𝕜 _ X E _ _ _ μ p q _ _ _ f g
  rw [(VectorLpRepresentation.pairing_formula 𝕜 μ q p _ g).2]
  change _ = PairingValue 𝕜 μ p q g f
  rw [(VectorLpRepresentation.pairing_formula 𝕜 μ p q g f).2]
  apply integral_congr_ae
  have hJ : (ContinuousLinearMap.compLp (𝕜 := 𝕜) (𝕜' := 𝕜) (F := ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)) (CanonicalEvaluationValue 𝕜 E) f) =ᵐ[μ]
      (fun t => CanonicalEvaluationValue 𝕜 E (f t)) :=
    ContinuousLinearMap.coeFn_compLp (𝕜 := 𝕜) (𝕜' := 𝕜) (F := ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜)) _ _
  filter_upwards [hJ] with t ht
  rw [ht]
  rfl

/-- The inverse canonical isometry acts on strongly measurable representatives. -/
theorem lp_reflexive : VectorLpReflexiveSpec.Reflexivity.{u,v} := by
  intro 𝕜 _ X E _ _ _ _ hE μ _ p _ hp hpfin
  letI : NormedAddCommGroup (E →L[𝕜] 𝕜) := inferInstance
  letI : NormedSpace 𝕜 (E →L[𝕜] 𝕜) := inferInstance
  letI : NormedAddCommGroup ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) := inferInstance
  letI : NormedSpace 𝕜 ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) := inferInstance
  let q := ENNReal.conjExponent p
  haveI : ENNReal.HolderConjugate p q := inferInstance
  haveI : Fact (1 ≤ q) := ⟨ENNReal.HolderConjugate.one_le q p⟩
  have hqfin : q ≠ ∞ := by
    intro hq
    have h := ENNReal.HolderConjugate.inv_add_inv_eq_one p q
    rw [hq] at h
    have hi : p⁻¹ = 1 := by simpa using h
    have heq : p = 1 := by simpa using congrArg Inv.inv hi
    exact hp.ne' heq
  have hD := VectorLpRepresentation.dual_reflexive 𝕜 E hE
  let J : E ≃ₗᵢ[𝕜] ((E →L[𝕜] 𝕜) →L[𝕜] 𝕜) :=
    LinearIsometryEquiv.ofSurjective
      ((CanonicalEvaluationValue 𝕜 E).toLinearMap.toLinearIsometry
        (P1.C05BidualIsometry.canonicalEvaluation_linear_isometry 𝕜 E).2.2) hE
  obtain ⟨T, hT⟩ := VectorLpDual.isometric_equivalence 𝕜 hE μ p q hpfin
  intro Φ
  obtain ⟨h, hh, _⟩ := VectorLpDual.representation 𝕜 hD μ q p hqfin
    (Φ.comp T.toContinuousLinearEquiv.toContinuousLinearMap)
  let f := J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp h
  refine ⟨f, ?_⟩
  ext ℓ
  obtain ⟨g, rfl⟩ := T.surjective ℓ
  change T g f = Φ (T g)
  have hhg : Φ (T g) = ∫ t, h t (g t) ∂μ := (hh.1 g).2
  rw [(hT g f).2, hhg]
  apply integral_congr_ae
  filter_upwards [J.symm.toContinuousLinearEquiv.toContinuousLinearMap.coeFn_compLp h] with t ht
  change g t (f t) = h t (g t)
  change g t (J.symm.toContinuousLinearEquiv.toContinuousLinearMap.compLp h t) = _
  rw [ht]
  have heq : CanonicalEvaluationValue 𝕜 E (J.symm (h t)) = h t := J.apply_symm_apply _
  exact congrArg (fun z => z (g t)) heq

/-- Pulling a bidual element back along the transpose of an equivalence
preserves the actual canonical embedding. -/
theorem reflexive_of_equiv {𝕜 : Type*} [RCLike 𝕜] {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (T : E ≃L[𝕜] F) (hE : IsReflexiveValue 𝕜 E) : IsReflexiveValue 𝕜 F := by
  intro ξ
  let S := (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip T.toContinuousLinearMap
  let R := (ContinuousLinearMap.compL 𝕜 F E 𝕜).flip T.symm.toContinuousLinearMap
  obtain ⟨x, hx⟩ := hE (ξ.comp R)
  refine ⟨T x, ?_⟩
  ext f
  have hh := congrArg (fun η => η (S f)) hx
  change f (T x) = ξ ((f.comp T.toContinuousLinearMap).comp T.symm.toContinuousLinearMap) at hh
  have hid : (f.comp T.toContinuousLinearMap).comp T.symm.toContinuousLinearMap = f := by
    ext y
    simp
  exact hh.trans (congrArg ξ hid)

/-- Hahn–Banach proves that a closed subspace of a reflexive space is reflexive. -/
theorem closed_subspace_reflexive {𝕜 : Type*} [RCLike 𝕜] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (M : Submodule 𝕜 F) (hM : IsClosed (M : Set F))
    (hF : IsReflexiveValue 𝕜 F) : IsReflexiveValue 𝕜 M := by
  letI : IsClosed (M : Set F) := hM
  let R : (F →L[𝕜] 𝕜) →L[𝕜] (M →L[𝕜] 𝕜) :=
    (ContinuousLinearMap.compL 𝕜 M F 𝕜).flip M.subtypeL
  intro ξ
  obtain ⟨x, hx⟩ := hF (ξ.comp R)
  have hxM : x ∈ M := by
    by_contra hnot
    have hqx : M.mkQL x ≠ 0 := fun hz => hnot ((Submodule.Quotient.mk_eq_zero M).mp hz)
    obtain ⟨g, _, hg⟩ := exists_dual_vector 𝕜 (M.mkQL x) (norm_ne_zero_iff.mpr hqx)
    let f := g.comp M.mkQL
    have hf : R f = 0 := by
      ext y
      change g (M.mkQL y.val) = 0
      have hy : M.mkQL y.val = 0 := (Submodule.Quotient.mk_eq_zero M).mpr y.property
      simp [hy]
    have he := congrArg (fun η => η f) hx
    change g (M.mkQL x) = ξ (R f) at he
    rw [hf, map_zero, hg] at he
    exact (norm_ne_zero_iff.mpr hqx) (RCLike.ofReal_eq_zero.mp he)
  refine ⟨⟨x, hxM⟩, ?_⟩
  ext f
  obtain ⟨g, hg, _⟩ := exists_extension_norm_eq M f
  have hRg : R g = f := by
    ext y
    exact hg y
  have he := congrArg (fun η => η g) hx
  change g x = ξ (R g) at he
  change f ⟨x, hxM⟩ = ξ f
  rw [← hRg, ← he]
  rfl

/-- A complete isometric copy has closed range, so reflexivity descends to it. -/
theorem reflexive_of_isometry {𝕜 : Type*} [RCLike 𝕜] {E : Type*} {F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (I : E →ₗᵢ[𝕜] F) (hF : IsReflexiveValue 𝕜 F) : IsReflexiveValue 𝕜 E := by
  have hclosed : IsClosed (I.toLinearMap.range : Set F) := I.isometry.isClosedEmbedding.isClosed_range
  exact reflexive_of_equiv I.equivRange.symm.toContinuousLinearEquiv
    (closed_subspace_reflexive I.toLinearMap.range hclosed hF)

theorem normalized_indicator_copy : VectorLpReflexiveSpec.IndicatorCopy.{u,v} := by
  intro 𝕜 _ X E _ _ _ _ μ p _ A hA hpos hfin
  let c : ℝ := μ.real A ^ (1 / p.toReal)
  have hc : 0 < c := Real.rpow_pos_of_pos (ENNReal.toReal_pos hpos hfin) _
  let T : E →ₗ[𝕜] Lp E p μ :=
    { toFun := fun x => (RCLike.ofReal c⁻¹ : 𝕜) • indicatorConstLp p hA hfin x
      map_add' := by
        intro x y
        rw [← indicatorConstLp_add, smul_add]
      map_smul' := by
        intro a x
        have hsm : indicatorConstLp (μ := μ) p hA hfin (a • x) =
            a • indicatorConstLp p hA hfin x := by
          apply Lp.ext
          filter_upwards [indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hA) (hμs := hfin) (c := a • x),
            indicatorConstLp_coeFn (μ := μ) (p := p) (hs := hA) (hμs := hfin) (c := x),
            Lp.coeFn_smul a (indicatorConstLp p hA hfin x)] with t h₁ h₂ h₃
          simp only [h₁, h₃, Pi.smul_apply, h₂]
          by_cases ht : t ∈ A <;> simp [ht]
        simp only [hsm, RingHom.id_apply, smul_comm a (RCLike.ofReal c⁻¹ : 𝕜)] }
  have hn : ∀ x, ‖T x‖ = ‖x‖ := by
    intro x
    change ‖(RCLike.ofReal c⁻¹ : 𝕜) • indicatorConstLp p hA hfin x‖ = ‖x‖
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hc),
      norm_indicatorConstLp' (ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))) hpos]
    change c⁻¹ * (‖x‖ * c) = ‖x‖
    rw [mul_left_comm, inv_mul_cancel₀ hc.ne', mul_one]
  let I : E →ₗᵢ[𝕜] Lp E p μ := ⟨T, hn⟩
  exact ⟨I, fun _ => rfl, I.isometry.isClosedEmbedding.isClosed_range⟩

theorem range_reflexive : VectorLpReflexiveSpec.Converse.{u,v} := by
  intro 𝕜 _ X E _ _ _ _ μ p _ ⟨A, hA, hpos, hfin⟩ hLp
  obtain ⟨I, _, _⟩ := normalized_indicator_copy 𝕜 (E := E) μ p A hA hpos hfin
  exact reflexive_of_isometry I hLp

open P1.C01SequenceSpaces FunctionSpaces.SequenceDuals

-- Cache the inherited structures before iterating the continuous-dual constructor.
local instance (𝕜 : Type) [RCLike 𝕜] : NormedAddCommGroup (SequenceC0 𝕜) := inferInstance
local instance (𝕜 : Type) [RCLike 𝕜] : NormedSpace 𝕜 (SequenceC0 𝕜) := inferInstance

/-- Restriction by an isometric domain equivalence, on scalar-linear duals. -/
def dualPrecomposeIsometry {𝕜 : Type*} [RCLike 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (U : E ≃ₗᵢ[𝕜] F) :
    (F →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] (E →L[𝕜] 𝕜) where
  toLinearEquiv :=
    { toFun := fun f => f.comp U.toContinuousLinearEquiv.toContinuousLinearMap
      invFun := fun g => g.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap
      map_add' := by intros; rfl
      map_smul' := by intros; rfl
      left_inv := by intro f; ext x; simp
      right_inv := by intro g; ext x; simp }
  norm_map' f := ContinuousLinearMap.opNorm_comp_linearIsometryEquiv f U

/-- The concrete c₀ bidual identification obtained from the bilinear series dualities. -/
def c0BidualEquiv (𝕜 : Type) [RCLike 𝕜] :
    ((SequenceC0 𝕜 →L[𝕜] 𝕜) →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] SequenceLInfinity 𝕜 :=
  (dualPrecomposeIsometry (c0DualityEquiv (𝕜 := 𝕜))).trans (l1Duality (𝕜 := 𝕜)).symm

@[simp] theorem c0BidualEquiv_evaluation (𝕜 : Type) [RCLike 𝕜]
    (x : SequenceC0 𝕜) :
    c0BidualEquiv 𝕜 (CanonicalEvaluationValue 𝕜 _ x) = x.val := by
  apply (l1Duality (𝕜 := 𝕜)).injective
  simp only [c0BidualEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  change (CanonicalEvaluationValue 𝕜 (SequenceC0 𝕜) x).comp
    (c0DualityEquiv (𝕜 := 𝕜)).toContinuousLinearEquiv.toContinuousLinearMap =
      (l1Duality (𝕜 := 𝕜)) x.val
  ext a
  change (∑' j, a j * x.val j) = ∑' j, x.val j * a j
  simp_rw [mul_comm]

theorem c0_not_reflexive (𝕜 : Type) [RCLike 𝕜] :
    ¬ IsReflexiveValue 𝕜 (SequenceC0 𝕜) := by
  intro h
  obtain ⟨x, hx⟩ := h ((c0BidualEquiv 𝕜).symm 1)
  have hxone : x.val = 1 := by
    simpa only [c0BidualEquiv_evaluation, LinearIsometryEquiv.apply_symm_apply] using
      congrArg (c0BidualEquiv 𝕜) hx
  have ht := x.property
  change Tendsto (fun n => x.val n) atTop (𝓝 0) at ht
  rw [hxone] at ht
  have ht' : Tendsto (fun _ : ℕ => (1 : 𝕜)) atTop (𝓝 0) := by simpa using ht
  exact one_ne_zero (tendsto_nhds_unique ht' tendsto_const_nhds).symm

theorem linfty_not_reflexive (𝕜 : Type) [RCLike 𝕜] :
    ¬ IsReflexiveValue 𝕜 (SequenceLInfinity 𝕜) := by
  intro h
  exact c0_not_reflexive 𝕜 (closed_subspace_reflexive (sequenceC0Submodule 𝕜)
    (P1.C01ExamplesComplete.sequence_c0_closed 𝕜) h)

theorem l1_not_reflexive (𝕜 : Type) [RCLike 𝕜] :
    ¬ IsReflexiveValue 𝕜 (SequenceLp 𝕜 1) := by
  intro h
  exact linfty_not_reflexive 𝕜 (reflexive_of_equiv
    (l1Duality (𝕜 := 𝕜)).symm.toContinuousLinearEquiv
    (VectorLpRepresentation.dual_reflexive 𝕜 _ h))

/-- Passing from scalar sequences to the native counting-measure quotient. -/
def countLpLinearMap (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (h : ∀ x : SequenceLp 𝕜 p, MemLp (fun n => x n) p (Measure.count : Measure ℕ)) :
    SequenceLp 𝕜 p →ₗ[𝕜] Lp 𝕜 p (Measure.count : Measure ℕ) where
  toFun x := (h x).toLp (fun n => x n)
  map_add' x y := by
    apply Lp.ext
    filter_upwards [(h (x + y)).coeFn_toLp, (h x).coeFn_toLp,
      (h y).coeFn_toLp, Lp.coeFn_add ((h x).toLp _) ((h y).toLp _)] with n hn hx hy ha
    refine hn.trans ?_
    simp only [ha, Pi.add_apply, hx, hy, lp.coeFn_add]
  map_smul' a x := by
    apply Lp.ext
    filter_upwards [(h (a • x)).coeFn_toLp, (h x).coeFn_toLp,
      Lp.coeFn_smul a ((h x).toLp _)] with n hn hx ha
    refine hn.trans ?_
    simp only [RingHom.id_apply, ha, Pi.smul_apply, hx, lp.coeFn_smul]

theorem sequence_memL1_count (𝕜 : Type) [RCLike 𝕜] (x : SequenceLp 𝕜 1) :
    MemLp (fun n => x n) 1 (Measure.count : Measure ℕ) := by
  rw [memLp_one_iff_integrable, integrable_count_iff]
  simpa using (lp.memℓp x).summable (by simp : 0 < (1 : ℝ≥0∞).toReal)

def l1CountIsometry (𝕜 : Type) [RCLike 𝕜] :
    SequenceLp 𝕜 1 →ₗᵢ[𝕜] Lp 𝕜 1 (Measure.count : Measure ℕ) where
  toLinearMap := countLpLinearMap 𝕜 1 (sequence_memL1_count 𝕜)
  norm_map' x := by
    rw [L1.norm_eq_integral_norm]
    have heq := (sequence_memL1_count 𝕜 x).coeFn_toLp
    change (∫ n, ‖((sequence_memL1_count 𝕜 x).toLp (fun n => x n)) n‖ ∂Measure.count) = _
    rw [integral_congr_ae (heq.mono (fun n hn => congrArg norm hn))]
    have hi : Integrable (fun n => ‖x n‖) (Measure.count : Measure ℕ) :=
      (memLp_one_iff_integrable.mp (sequence_memL1_count 𝕜 x)).norm
    rw [integral_countable hi]
    simpa [Measure.real, lp.norm_eq_tsum_rpow (by simp : 0 < (1 : ℝ≥0∞).toReal)]

theorem sequence_memLInfinity_count (𝕜 : Type) [RCLike 𝕜] (x : SequenceLInfinity 𝕜) :
    MemLp (fun n => x n) ∞ (Measure.count : Measure ℕ) :=
  memLp_top_of_bound StronglyMeasurable.of_discrete.aestronglyMeasurable ‖x‖
    (ae_of_all _ (lp.norm_apply_le_norm ENNReal.top_ne_zero x))

def linftyCountIsometry (𝕜 : Type) [RCLike 𝕜] :
    SequenceLInfinity 𝕜 →ₗᵢ[𝕜] Lp 𝕜 ∞ (Measure.count : Measure ℕ) where
  toLinearMap := countLpLinearMap 𝕜 ∞ (sequence_memLInfinity_count 𝕜)
  norm_map' x := by
    change ‖(sequence_memLInfinity_count 𝕜 x).toLp (fun n => x n)‖ = ‖x‖
    rw [Lp.norm_toLp, eLpNorm_exponent_top StronglyMeasurable.of_discrete.aestronglyMeasurable,
      eLpNormEssSup_count, ENNReal.toReal_iSup (fun _ => enorm_ne_top)]
    simp only [enorm, ENNReal.coe_toReal, coe_nnnorm, lp.norm_eq_ciSup]

theorem endpoint_counterexamples : VectorLpReflexiveSpec.Endpoints := by
  intro 𝕜 _
  refine ⟨?_, ?_, ?_⟩
  · intro Φ
    let f : 𝕜 →L[𝕜] 𝕜 := ContinuousLinearMap.id 𝕜 𝕜
    refine ⟨Φ f, ?_⟩
    ext g
    have hg : g = g 1 • f := by
      ext z
      simpa [f, mul_comm] using g.map_smul z (1 : 𝕜)
    change g (Φ f) = Φ g
    rw [hg, map_smul]
    simp [f]
  · intro h
    exact l1_not_reflexive 𝕜 (reflexive_of_isometry (l1CountIsometry 𝕜) h)
  · intro h
    exact linfty_not_reflexive 𝕜 (reflexive_of_isometry (linftyCountIsometry 𝕜) h)

end ExpandedFA.PartIV.VectorLpReflexive
