import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.ApproximationPropertyOperatorForm
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.ApproximationPropertyDefinitions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Compactness.CompactDiskEmbedding
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.ScalarRieszMarkov
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerIntegral
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section
namespace ExpandedFA.Compactness
universe u v w
open Set MeasureTheory
open scoped Topology ZeroAtInfty

/-- Approximate the identity on the compact closure of the unit-ball image.
The supremum error is strictly below ε, so it bounds the operator norm too. -/
theorem ap_implies_compact_operator_approximation :
    ApproximationPropertyOperatorFormSpec.Forward.{u,v,w} := by
  intro 𝕜 _ X Y _ _ _ _ _ _ hAP T hT ε hε
  let K := closure (T '' Metric.closedBall (0 : Y) 1)
  have hK : IsCompact K := hT.isCompact_closure_image_closedBall 1
  obtain ⟨F, hF, herr⟩ := hAP K hK ε hε
  let S := F.comp T
  refine ⟨S, ?_, ?_⟩
  · let := hF
    exact FiniteDimensional.of_injective
      (Submodule.inclusion (show LinearMap.range S.toLinearMap ≤
        LinearMap.range F.toLinearMap from by
          rintro _ ⟨y, rfl⟩; exact ⟨T y, rfl⟩)) (Submodule.inclusion_injective _)
  · let r := sSup ((fun x : X => ‖F x - x‖) '' K)
    have h0 : (0 : X) ∈ K := subset_closure ⟨0, by simp, by simp⟩
    have hb : BddAbove ((fun x : X => ‖F x - x‖) '' K) :=
      (hK.image ((F.continuous.sub continuous_id).norm)).bddAbove
    have hr : 0 ≤ r := by
      exact le_csSup hb ⟨0, h0, by simp⟩
    have hn : ‖S - T‖ ≤ r := by
      apply ContinuousLinearMap.opNorm_le_of_unit_norm hr
      intro y hy
      have hyK : T y ∈ K := subset_closure ⟨y,
        by simp [Metric.mem_closedBall, dist_zero_right, hy], rfl⟩
      simpa [S, r, mul_one] using le_csSup hb ⟨T y, hyK, rfl⟩
    exact hn.trans_lt herr

/-- The annihilator criterion for membership in a closed linear span. -/
theorem mem_closure_of_dual_annihilator {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (p : Submodule ℝ E) (x : E)
    (h : ∀ L : E →L[ℝ] ℝ, (∀ y ∈ p, L y = 0) → L x = 0) :
    x ∈ closure (p : Set E) := by
  by_contra hx
  let N := p.topologicalClosure
  let : IsClosed (N : Set E) := p.isClosed_topologicalClosure
  have hq : N.mkQL x ≠ 0 := by
    intro hq
    exact hx (((Submodule.Quotient.mk_eq_zero N).mp hq) : x ∈ N)
  obtain ⟨l, hl⟩ := SeparatingDual.exists_ne_zero (R := ℝ) hq
  apply hl
  exact h (l.comp N.mkQL) (by
    intro y hy
    change l (N.mkQ y) = 0
    have hyN : y ∈ N := p.le_topologicalClosure hy
    have hzero : N.mkQ y = 0 := (Submodule.Quotient.mk_eq_zero N).mpr hyN
    rw [hzero, map_zero])

/-- An injective bounded inclusion has a transpose with dense restrictions
on every compact subset of its Banach domain. Here the real case is proved
by separation in C(K), positive Riesz representation, and an actual barycenter. -/
theorem approximate_real_functional_on_compact
    {G E : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : G →L[ℝ] E) (hi : Function.Injective i)
    (K : Set G) (hK : IsCompact K) (f : G →L[ℝ] ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : E →L[ℝ] ℝ, ∀ x ∈ K, ‖g (i x) - f x‖ < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasurableSpace K := borel K
  let : BorelSpace K := ⟨rfl⟩
  let j : C(K, G) := ⟨Subtype.val, continuous_subtype_val⟩
  let R : (E →L[ℝ] ℝ) →ₗ[ℝ] C(K, ℝ) :=
    { toFun := fun g => ⟨fun x => g (i x),
        g.continuous.comp (i.continuous.comp continuous_subtype_val)⟩
      map_add' := fun _ _ => by ext x; rfl
      map_smul' := fun _ _ => by ext x; rfl }
  let fK : C(K, ℝ) := ⟨fun x => f x, f.continuous.comp continuous_subtype_val⟩
  have hd : fK ∈ closure (LinearMap.range R : Set C(K, ℝ)) := by
    apply mem_closure_of_dual_annihilator
    intro L hLzero
    obtain ⟨e, he, _⟩ := FunctionSpaces.ScalarRieszMarkov.compact_identification K ℝ
    let L0 : C₀(K, ℝ) →L[ℝ] ℝ := L.comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap
    obtain ⟨P, Q, hP, hQ, hL⟩ :=
      FunctionSpaces.ScalarRieszMarkov.exists_positive_decomposition L0
    obtain ⟨μ, _, hμfin, hμrep, _⟩ :=
      FunctionSpaces.ScalarRieszMarkov.positive_representation K P hP
    obtain ⟨ν, _, hνfin, hνrep, _⟩ :=
      FunctionSpaces.ScalarRieszMarkov.positive_representation K Q hQ
    let : IsFiniteMeasure μ := ⟨hμfin⟩
    let : IsFiniteMeasure ν := ⟨hνfin⟩
    have hrep (h : C(K, ℝ)) :
        L h = (∫ x, h x ∂μ) - ∫ x, h x ∂ν := by
      calc
        L h = L0 (e h) := by simp [L0]
        _ = P (e h) - Q (e h) := by rw [hL]; rfl
        _ = _ := by
          rw [(hμrep (e h)).2, (hνrep (e h)).2]
          simp only [he]
    have hj (ρ : Measure K) [IsFiniteMeasure ρ] : Integrable j ρ := by
      have ht := j.continuous.continuousOn.integrableOn_of_subset_isCompact
        isCompact_univ MeasurableSet.univ (Subset.rfl) (measure_ne_top ρ univ)
      simpa using ht
    let z : G := (∫ x, j x ∂μ) - ∫ x, j x ∂ν
    have hz (g : G →L[ℝ] ℝ) :
        g z = (∫ x, g (j x) ∂μ) - ∫ x, g (j x) ∂ν := by
      simp only [z, map_sub]
      rw [← g.integral_comp_comm (hj μ), ← g.integral_comp_comm (hj ν)]
    have hiz : i z = 0 := by
      apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
      intro g
      rw [← ContinuousLinearMap.comp_apply, hz]
      exact (hrep (R g)).symm.trans (hLzero _ ⟨g, rfl⟩)
    have hz0 : z = 0 := hi (by simpa using hiz)
    calc
      L fK = f z := (hrep fK).trans (hz f).symm
      _ = 0 := by rw [hz0, map_zero]
  obtain ⟨h, ⟨g, rfl⟩, hdist⟩ := Metric.mem_closure_iff.mp hd ε hε
  refine ⟨g, fun x hx => ?_⟩
  have hb := ContinuousMap.norm_coe_le_norm (R g - fK) (⟨x, hx⟩ : K)
  have hn : ‖R g - fK‖ < ε := by simpa [dist_eq_norm, norm_sub_rev] using hdist
  exact hb.trans_lt hn

/-- Real and complex versions of restriction density. The compact set is
also tested after multiplication by I before extending the real functional. -/
theorem approximate_functional_on_compact
    {𝕜 : Type*} [RCLike 𝕜] {G E : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (i : G →L[𝕜] E) (hi : Function.Injective i)
    (K : Set G) (hK : IsCompact K) (f : G →L[𝕜] 𝕜)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : E →L[𝕜] 𝕜, ∀ x ∈ K, ‖g (i x) - f x‖ < ε := by
  let : NormedSpace ℝ G := NormedSpace.restrictScalars ℝ 𝕜 G
  let : IsScalarTower ℝ 𝕜 G := IsScalarTower.restrictScalars ℝ 𝕜 G
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := IsScalarTower.restrictScalars ℝ 𝕜 E
  let fr : G →L[ℝ] ℝ := RCLike.reCLM.comp (f.restrictScalars ℝ)
  let K' := K ∪ (fun x : G => (RCLike.I : 𝕜) • x) '' K
  have hK' : IsCompact K' := hK.union (hK.image (continuous_const.smul continuous_id))
  obtain ⟨g, hg⟩ := approximate_real_functional_on_compact
    (i.restrictScalars ℝ) hi K' hK' fr (ε / 2) (half_pos hε)
  have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
    rw [RCLike.norm_I]; split_ifs <;> norm_num
  have hfr : (StrongDual.extendRCLike fr : G →L[𝕜] 𝕜) = f :=
    (StrongDual.extendRCLikeₗ (𝕜 := 𝕜) (F := G)).right_inv f
  refine ⟨StrongDual.extendRCLike g, fun x hx => ?_⟩
  have h1 := hg x (Or.inl hx)
  have h2 := hg ((RCLike.I : 𝕜) • x) (Or.inr ⟨x, hx, rfl⟩)
  calc
    ‖(StrongDual.extendRCLike g : E →L[𝕜] 𝕜) (i x) - f x‖ =
        ‖((g (i x) - fr x : ℝ) : 𝕜) -
          (RCLike.I : 𝕜) * ((g (i ((RCLike.I : 𝕜) • x)) -
            fr ((RCLike.I : 𝕜) • x) : ℝ) : 𝕜)‖ := by
      rw [← hfr, StrongDual.extendRCLike_apply, StrongDual.extendRCLike_apply]
      simp only [map_smul, map_sub]
      congr 1
      ring
    _ ≤ ‖((g (i x) - fr x : ℝ) : 𝕜)‖ +
        ‖(RCLike.I : 𝕜) * ((g (i ((RCLike.I : 𝕜) • x)) -
          fr ((RCLike.I : 𝕜) • x) : ℝ) : 𝕜)‖ := norm_sub_le _ _
    _ ≤ ‖g (i x) - fr x‖ +
        ‖g (i ((RCLike.I : 𝕜) • x)) - fr ((RCLike.I : 𝕜) • x)‖ := by
      simp only [norm_mul, RCLike.norm_ofReal, Real.norm_eq_abs]
      nlinarith [hI,
        abs_nonneg (g (i ((RCLike.I : 𝕜) • x)) - fr ((RCLike.I : 𝕜) • x))]
    _ < ε := by change ‖g (i x) - fr x‖ < _ at h1; change ‖g (i _) - fr _‖ < _ at h2; linarith

/-- Transfer a finite-rank map across an injective inclusion on a compact
set, without claiming that its coordinate functionals extend exactly. -/
theorem approximate_finite_rank_on_compact
    {𝕜 : Type*} [RCLike 𝕜] {G E X : Type*}
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (i : G →L[𝕜] E) (hi : Function.Injective i)
    (K : Set G) (hK : IsCompact K) (S : G →L[𝕜] X)
    (hS : FiniteDimensional 𝕜 (LinearMap.range S.toLinearMap))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : E →L[𝕜] X, FiniteDimensional 𝕜 (LinearMap.range F.toLinearMap) ∧
      ∀ x ∈ K, ‖F (i x) - S x‖ < ε := by
  classical
  let := hS
  let b := Module.finBasis 𝕜 (LinearMap.range S.toLinearMap)
  let J := Fin (Module.finrank 𝕜 (LinearMap.range S.toLinearMap))
  let y : J → X := fun j => b j
  let f : J → G →L[𝕜] 𝕜 := fun j =>
    (b.coord j).toContinuousLinearMap.comp S.rangeRestrict
  have hsum (x : G) : S x = ∑ j : J, f j x • y j := by
    have ht := congrArg (fun z : LinearMap.range S.toLinearMap => (z : X))
      (b.sum_repr (S.rangeRestrict x))
    simpa [f, y, Module.Basis.coord, Function.comp_def, Finsupp.lapply_apply] using ht.symm
  let M := ∑ j : J, ‖y j‖
  have hM : 0 ≤ M := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let δ := ε / (M + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  choose g hg using fun j => approximate_functional_on_compact i hi K hK (f j) δ hδ
  let F : E →L[𝕜] X := ∑ j : J, (g j).smulRight (y j)
  refine ⟨F, ?_, ?_⟩
  · let V := Submodule.span 𝕜 (range y)
    have hV : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 (finite_range y)
    let := hV
    apply FiniteDimensional.of_injective
      (Submodule.inclusion (show LinearMap.range F.toLinearMap ≤ V from ?_))
      (Submodule.inclusion_injective _)
    rintro _ ⟨x, rfl⟩
    simp only [F, FunLike.coe_sum, Finset.sum_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_coe]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem V _ (Submodule.subset_span ⟨j, rfl⟩)
  · intro x hx
    calc
      ‖F (i x) - S x‖ = ‖∑ j : J, (g j (i x) - f j x) • y j‖ := by
        rw [hsum]
        congr 1
        simp [F, Finset.sum_sub_distrib, sub_smul]
      _ ≤ ∑ j : J, ‖(g j (i x) - f j x) • y j‖ := norm_sum_le _ _
      _ ≤ ∑ j : J, δ * ‖y j‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hg j x hx).le (norm_nonneg _)
      _ = δ * M := by rw [Finset.mul_sum]
      _ < δ * (M + 1) := by nlinarith
      _ = ε := by dsimp [δ]; field_simp

/-- Compact disk inclusions suffice for the converse. The original compact
set has a compact lift contained in the disk-space unit ball. -/
theorem compact_operator_approximation_implies_ap :
    ApproximationPropertyOperatorFormSpec.Converse.{u,v} := by
  intro 𝕜 _ X _ _ _ hOp
  apply (hasApproximationProperty_iff_pointwise 𝕜 X).mpr
  intro K hK ε hε
  obtain ⟨z, hz, hKz, hC, G, nG, sG, cG, i, hi, hic, hball,
      hrange, hgauge, hspan, hpre⟩ := compactDiskEmbedding (𝕜 := 𝕜) K hK
  let := nG
  let := sG
  let := cG
  obtain ⟨S, hS, hSi⟩ := hOp G i hic (ε / 2) (half_pos hε)
  obtain ⟨F, hF, hFS⟩ := approximate_finite_rank_on_compact i hi
    (i ⁻¹' K) hpre S hS (ε / 2) (half_pos hε)
  refine ⟨F, hF, fun x hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := hball.symm ▸ hKz hx
  have hynorm : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hy
  have hyK : y ∈ i ⁻¹' K := by simpa [hyx] using hx
  have hSy : ‖S y - i y‖ < ε / 2 :=
    (ContinuousLinearMap.unit_le_opNorm (S - i) y hynorm).trans_lt hSi
  calc
    ‖F x - x‖ = ‖(F (i y) - S y) + (S y - i y)‖ := by rw [hyx]; congr 1; abel
    _ ≤ ‖F (i y) - S y‖ + ‖S y - i y‖ := norm_add_le _ _
    _ < ε := by linarith [hFS y hyK]

/-- The operator characterization of AP over ℝ or ℂ. -/
theorem hasApproximationProperty_iff_compact_operator_approximation :
    ApproximationPropertyOperatorFormSpec.Equivalence.{u,v} := by
  intro 𝕜 _ X _ _ _
  constructor
  · intro h Y _ _ _
    exact ap_implies_compact_operator_approximation h
  · exact compact_operator_approximation_implies_ap

end ExpandedFA.Compactness
