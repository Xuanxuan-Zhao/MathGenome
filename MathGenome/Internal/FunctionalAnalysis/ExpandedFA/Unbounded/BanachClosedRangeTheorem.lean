import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.BanachClosedRangeTheorem
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.BanachClosedRangeDistance
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.BanachAdjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.KreinSmulian
import Mathlib.Analysis.Normed.Module.HahnBanach

/-! Banach's closed range theorem, `paper.tex`, fa2:p3:banach-closed-range.

The difficult reverse direction first obtains bounded preimages from open
mapping on the adjoint graph. Alaoglu and the weak-star extension relation
make the unit slice of its range closed; Krein–Šmulian closes the whole range.
Graph separation identifies its preannihilator with the original kernel.
A norming functional on the ambient quotient then yields the distance bound.
All pairings are scalar-linear and no reflexivity assumption is used. -/

noncomputable section
open Set Metric Topology
namespace ExpandedFA.Unbounded.BanachClosedRangeTheorem

variable {𝕜 X Y : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

theorem annihilator_isClosed (S : Submodule 𝕜 X) :
    _root_.IsClosed {f : X →L[𝕜] 𝕜 | ∀ x ∈ S, f x = 0} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_eq (ContinuousLinearMap.apply 𝕜 𝕜 x).continuous continuous_const

theorem range_subset_annihilator (A : Operator 𝕜 X Y)
    (hd : Dense (A.domain : Set X)) :
    ((banachAdjoint A).toFun.range : Set (X →L[𝕜] 𝕜)) ⊆
      {f | ∀ x ∈ A.ker, f x = 0} := by
  rintro f ⟨q, rfl⟩ x hx
  let z : A.domain := ⟨x, A.ker_le_domain hx⟩
  have hz : A z = 0 := A.coe_mem_ker_iff.mp hx
  change banachAdjoint A q (z : X) = 0
  rw [banachAdjoint_apply A hd q z, hz, map_zero]

/-- The adjoint range separates every vector outside the kernel. This uses
closedness of the original graph, rather than any bidual reflexivity claim. -/
theorem preannihilator_range (A : Operator 𝕜 X Y)
    (hd : Dense (A.domain : Set X)) (hc : A.IsClosed) (x : X) :
    (∀ f ∈ (banachAdjoint A).toFun.range, f x = 0) ↔ x ∈ A.ker := by
  constructor
  · intro hx
    have hgraph : (x, (0 : Y)) ∈ A.graph := by
      by_contra hn
      have hn' : (x, (0 : Y)) ∉ _root_.closure (A.graph : Set (X × Y)) := by
        rwa [hc.closure_eq]
      obtain ⟨L, hL, hLn⟩ :=
        exists_dual_vanishing_of_not_mem_closure A.graph (x, 0) hn'
      let f : X →L[𝕜] 𝕜 := L.comp (ContinuousLinearMap.inl 𝕜 X Y)
      let q : Y →L[𝕜] 𝕜 := L.comp (ContinuousLinearMap.inr 𝕜 X Y)
      have hext (z : A.domain) : (-f) (z : X) = q (A z) := by
        have hz := hL ((z : X), A z) (A.mem_graph z)
        have heq : f (z : X) + q (A z) = 0 := by
          simpa only [f, q, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
            ContinuousLinearMap.inr_apply, ← map_add, Prod.mk_add_mk, add_zero, zero_add] using hz
        exact neg_eq_iff_add_eq_zero.mpr heq
      have hq := (mem_banachAdjoint_domain_iff A q).mpr ⟨-f, hext⟩
      let z : (banachAdjoint A).domain := ⟨q, hq⟩
      have hz : banachAdjoint A z = -f :=
        (banachAdjoint_unique_extension A hd z (-f) hext).symm
      have hfx := hx (-f) ⟨z, hz⟩
      apply hLn
      change f x = 0
      simpa only [neg_apply, neg_eq_zero] using hfx
    obtain ⟨z, hz, hzero⟩ := A.mem_graph_iff.mp hgraph
    exact (LinearPMap.mem_ker_iff).mpr ⟨z, hz.symm, hzero⟩
  · intro hx f hf
    exact range_subset_annihilator A hd hf x hx

/-- The fourth condition is exactly removal of the closure in the general
range-annihilator identity. -/
theorem range_eq_preannihilator_iff (A : Operator 𝕜 X Y)
    (hd : Dense (A.domain : Set X)) :
    _root_.IsClosed (A.toFun.range : Set Y) ↔
      (A.toFun.range : Set Y) = {y | ∀ q ∈ (banachAdjoint A).ker, q y = 0} := by
  have heq := banachAdjoint_range_closure A hd
  constructor
  · intro hc
    exact hc.closure_eq.symm.trans heq
  · intro h
    rw [← h] at heq
    exact closure_eq_iff_isClosed.mp heq

/-- A continuous functional vanishing on S is bounded by distance to S. -/
theorem dual_vanish_bound (S : Submodule 𝕜 X) (f : X →L[𝕜] 𝕜)
    (hf : ∀ z ∈ S, f z = 0) (x : X) :
    ‖f x‖ ≤ ‖f‖ * infDist x (S : Set X) := by
  by_cases hn : ‖f‖ = 0
  · have : f = 0 := norm_eq_zero.mp hn
    simp [this]
  · have hn' : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hn)
    have h : ‖f x‖ / ‖f‖ ≤ infDist x (S : Set X) := by
      apply (le_infDist S.nonempty).mpr
      intro z hz
      apply (div_le_iff₀ hn').mpr
      have heq : f x = f (x - z) := by rw [map_sub, hf z hz, sub_zero]
      rw [heq, dist_eq_norm, mul_comm]
      exact f.le_opNorm _
    exact (div_le_iff₀ hn').mp h |>.trans_eq (mul_comm _ _)

/-- Hahn–Banach on the range, with the ambient distance estimate. -/
theorem adjoint_range_eq_of_closed_range [CompleteSpace X] [CompleteSpace Y]
    (A : Operator 𝕜 X Y) (hd : Dense (A.domain : Set X)) (hc : A.IsClosed)
    (hr : _root_.IsClosed (A.toFun.range : Set Y)) :
    ((banachAdjoint A).toFun.range : Set (X →L[𝕜] 𝕜)) =
      {f | ∀ x ∈ A.ker, f x = 0} := by
  apply Set.Subset.antisymm (range_subset_annihilator A hd)
  intro f hf
  obtain ⟨C, hC, hdist⟩ :=
    BanachClosedRangeDistance.distance_bound_of_closed_range A hc hr
  let F : A.domain →ₗ[𝕜] 𝕜 := f.toLinearMap.comp A.domain.subtype
  have hker : A.toFun.rangeRestrict.ker ≤ F.ker := by
    intro x hx
    apply hf
    exact LinearPMap.mem_ker_iff.mpr ⟨x, rfl, by
      exact congrArg Subtype.val (LinearMap.mem_ker.mp hx)⟩
  let g : A.toFun.range →ₗ[𝕜] 𝕜 :=
    A.toFun.rangeRestrict.liftOfSurjective A.toFun.surjective_rangeRestrict ⟨F, hker⟩
  have hg (x : A.domain) : g (A.toFun.rangeRestrict x) = f (x : X) :=
    LinearMap.equivOfSurjective_apply _ _
  have hbound (y : A.toFun.range) : ‖g y‖ ≤ (‖f‖ * C) * ‖y‖ := by
    obtain ⟨x, hx⟩ := A.toFun.surjective_rangeRestrict y
    rw [← hx, hg]
    calc
      ‖f (x : X)‖ ≤ ‖f‖ * infDist (x : X) (A.ker : Set X) :=
        dual_vanish_bound A.ker f hf _
      _ ≤ ‖f‖ * (C * ‖A x‖) := mul_le_mul_of_nonneg_left (hdist x) (norm_nonneg _)
      _ = (‖f‖ * C) * ‖A.toFun.rangeRestrict x‖ := (mul_assoc _ _ _).symm
  obtain ⟨q, hq, _⟩ := exists_extension_norm_eq A.toFun.range
    (g.mkContinuous (‖f‖ * C) hbound)
  have hext (x : A.domain) : f (x : X) = q (A x) :=
    (hg x).symm.trans (hq (A.toFun.rangeRestrict x)).symm
  have hqmem := (mem_banachAdjoint_domain_iff A q).mpr ⟨f, hext⟩
  exact ⟨⟨q, hqmem⟩, (banachAdjoint_unique_extension A hd ⟨q, hqmem⟩ f hext).symm⟩

/-- Open mapping on a closed graph gives uniformly bounded preimages in the
original ambient norm; no boundedness of the operator is asserted. -/
theorem bounded_preimages [CompleteSpace X] [CompleteSpace Y]
    (A : Operator 𝕜 X Y) (hc : A.IsClosed)
    (hr : _root_.IsClosed (A.toFun.range : Set Y)) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ A.toFun.range,
      ∃ q : A.domain, A q = f ∧ ‖(q : X)‖ ≤ C * ‖f‖ := by
  let : CompleteSpace A.graph := hc.completeSpace_coe
  let T := BanachClosedRangeDistance.graphOutput A
  have hTr : _root_.IsClosed (T.range : Set Y) := by
    simpa only [T, BanachClosedRangeDistance.graphOutput_range] using hr
  let : CompleteSpace T.range := hTr.completeSpace_coe
  obtain ⟨C, hC, hpre⟩ := T.rangeRestrict.exists_preimage_norm_le (by
    rintro ⟨y, z, rfl⟩
    exact ⟨z, rfl⟩)
  refine ⟨C, hC, fun f hf => ?_⟩
  have hfT : f ∈ T.range := by
    simpa only [T, BanachClosedRangeDistance.graphOutput_range] using hf
  obtain ⟨z, hz, hn⟩ := hpre ⟨f, hfT⟩
  obtain ⟨q, hq, hAq⟩ := A.mem_graph_iff.mp z.property
  refine ⟨q, hAq.trans (congrArg Subtype.val hz), ?_⟩
  calc
    ‖(q : X)‖ = ‖z.val.1‖ := congrArg norm hq
    _ ≤ ‖z‖ := norm_fst_le z.val
    _ ≤ C * ‖f‖ := hn

/-- Bounded preimages make the closed unit slice of the adjoint range the
projection of a compact part of the weak-star closed extension relation. -/
theorem adjoint_range_weakStar_closed [CompleteSpace X] [CompleteSpace Y]
    (A : Operator 𝕜 X Y) (hd : Dense (A.domain : Set X))
    (hr : _root_.IsClosed ((banachAdjoint A).toFun.range : Set (X →L[𝕜] 𝕜))) :
    @_root_.IsClosed (X →L[𝕜] 𝕜) (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 X)
      ((banachAdjoint A).toFun.range : Set _) := by
  obtain ⟨C, hC, hpre⟩ := bounded_preimages (banachAdjoint A) (banachAdjoint_closed A hd) hr
  let R : Set (WeakDual 𝕜 Y × WeakDual 𝕜 X) :=
    {p | ∀ x : A.domain, p.2 (x : X) = p.1 (A x)}
  have hR : _root_.IsClosed R := by
    simp only [R, Set.ofPred_forall]
    exact isClosed_iInter fun x => isClosed_eq
      ((WeakDual.eval_continuous (𝕜 := 𝕜) (x : X)).comp continuous_snd)
      ((WeakDual.eval_continuous (𝕜 := 𝕜) (A x)).comp continuous_fst)
  let BY : Set (WeakDual 𝕜 Y) := {q | ‖q.toStrongDual‖ ≤ C}
  let BX : Set (WeakDual 𝕜 X) := {f | ‖f.toStrongDual‖ ≤ 1}
  have hBY : IsCompact BY := by
    simpa only [BY, Set.preimage, Metric.closedBall, dist_zero_right, Set.mem_ofPred_eq] using
      (WeakDual.isCompact_closedBall (𝕜 := 𝕜) (E := Y) 0 C)
  have hBX : IsCompact BX := by
    simpa only [BX, Set.preimage, Metric.closedBall, dist_zero_right, Set.mem_ofPred_eq] using
      (WeakDual.isCompact_closedBall (𝕜 := 𝕜) (E := X) 0 1)
  have hproj : _root_.IsClosed (Prod.snd '' ((BY ×ˢ BX) ∩ R)) :=
    (((hBY.prod hBX).inter_right hR).image continuous_snd).isClosed
  have heq : (StrongDual.toWeakDual : (X →L[𝕜] 𝕜) → WeakDual 𝕜 X) ⁻¹'
      (Prod.snd '' ((BY ×ˢ BX) ∩ R)) =
      ((banachAdjoint A).toFun.range : Set _) ∩ {f | ‖f‖ ≤ 1} := by
    ext f
    constructor
    · rintro ⟨⟨q, g⟩, ⟨⟨hq, hg⟩, hrel⟩, hgf⟩
      have hgf' : g.toStrongDual = f := congrArg WeakDual.toStrongDual hgf
      have hext : ∀ x : A.domain, f (x : X) = q.toStrongDual (A x) := by
        intro x
        rw [← hgf']
        exact hrel x
      have hmem := (mem_banachAdjoint_domain_iff A q.toStrongDual).mpr ⟨f, hext⟩
      exact ⟨⟨⟨q.toStrongDual, hmem⟩,
        (banachAdjoint_unique_extension A hd ⟨q.toStrongDual, hmem⟩ f hext).symm⟩,
        hgf' ▸ hg⟩
    · rintro ⟨hf, hfn⟩
      obtain ⟨q, hq, hqn⟩ := hpre f hf
      refine ⟨(StrongDual.toWeakDual (q : Y →L[𝕜] 𝕜), StrongDual.toWeakDual f), ⟨⟨?_, hfn⟩, ?_⟩, rfl⟩
      · exact hqn.trans (mul_le_of_le_one_right hC.le hfn)
      · intro x
        change f (x : X) = (q : Y →L[𝕜] 𝕜) (A x)
        rw [← hq]
        exact banachAdjoint_apply A hd q x
  apply (ExpandedFA.P1.KreinSmulian.subspace_closed_criterion 𝕜 X
    (banachAdjoint A).toFun.range).mpr
  rw [← heq]
  let : TopologicalSpace (X →L[𝕜] 𝕜) := ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 X
  have he : IsInducing (StrongDual.toWeakDual : (X →L[𝕜] 𝕜) → WeakDual 𝕜 X) :=
    ⟨ExpandedFA.P1.C12WeakStar.weakStarTopology_native 𝕜 X⟩
  exact hproj.preimage he.continuous

/-- Weak-star closed subspaces are determined by their preannihilator.
The weak representation theorem turns a separating functional into evaluation. -/
theorem mem_of_weakStar_closed (M : Submodule 𝕜 (X →L[𝕜] 𝕜))
    (hM : @_root_.IsClosed (X →L[𝕜] 𝕜)
      (ExpandedFA.P1.C12WeakStar.Spec.WeakStarTopologyValue 𝕜 X) (M : Set _))
    (f : X →L[𝕜] 𝕜)
    (hf : ∀ x : X, (∀ g ∈ M, g x = 0) → f x = 0) : f ∈ M := by
  let N : Submodule 𝕜 (WeakDual 𝕜 X) := M
  have hN : _root_.IsClosed (N : Set (WeakDual 𝕜 X)) := by
    rw [ExpandedFA.P1.C12WeakStar.weakStarTopology_native] at hM
    change @_root_.IsClosed (WeakDual 𝕜 X) (TopologicalSpace.induced id inferInstance) (N : Set _) at hM
    rwa [induced_id] at hM
  let : LocallyConvexSpace ℝ (WeakDual 𝕜 X) :=
    WeakBilin.locallyConvexSpace (B := topDualPairing 𝕜 X)
  by_contra hn
  have hn' : StrongDual.toWeakDual f ∉ N := hn
  obtain ⟨L, a, hL, ha⟩ := RCLike.geometric_hahn_banach_closed_point
    (𝕜 := 𝕜) (N.restrictScalars ℝ).convex hN hn'
  obtain ⟨x, hx⟩ := (topDualPairing 𝕜 X).dualEmbedding_surjective L
  have hx' (g : WeakDual 𝕜 X) : L g = g x :=
    (congrArg (fun u : (WeakDual 𝕜 X) →L[𝕜] 𝕜 => u g) hx).symm
  have hvan (g : X →L[𝕜] 𝕜) (hg : g ∈ M) : g x = 0 := by
    by_contra hne
    let c : 𝕜 := ((a + 1 : ℝ) : 𝕜) / g x
    have hb := hL (c • StrongDual.toWeakDual g) (N.smul_mem c hg)
    rw [hx'] at hb
    have heq : (c • StrongDual.toWeakDual g) x = ((a + 1 : ℝ) : 𝕜) := by
      change (((a + 1 : ℝ) : 𝕜) / g x) * g x = _
      exact div_mul_cancel₀ _ hne
    rw [heq, RCLike.ofReal_re] at hb
    linarith
  have hfzero := hf x hvan
  have ha' : a < 0 := by
    simpa only [hx', StrongDual.toWeakDual_apply, hfzero, RCLike.zero_re] using ha
  have ha0 : 0 < a := by
    simpa only [map_zero, RCLike.zero_re] using hL 0 N.zero_mem
  exact (ha0.trans ha').false

/-- Norm-closed adjoint range equals the annihilator of the primal kernel. -/
theorem adjoint_range_eq_of_norm_closed [CompleteSpace X] [CompleteSpace Y]
    (A : Operator 𝕜 X Y) (hd : Dense (A.domain : Set X)) (hc : A.IsClosed)
    (hr : _root_.IsClosed ((banachAdjoint A).toFun.range : Set (X →L[𝕜] 𝕜))) :
    ((banachAdjoint A).toFun.range : Set (X →L[𝕜] 𝕜)) =
      {f | ∀ x ∈ A.ker, f x = 0} := by
  apply Set.Subset.antisymm (range_subset_annihilator A hd)
  intro f hf
  apply mem_of_weakStar_closed _ (adjoint_range_weakStar_closed A hd hr) f
  intro x hx
  exact hf x ((preannihilator_range A hd hc x).mp hx)

/-- A norming functional on the ambient quotient gives the distance formula,
including zero quotient and zero-distance cases. -/
theorem exists_norming_annihilator (S : Submodule 𝕜 X) (x : X) :
    ∃ f : X →L[𝕜] 𝕜, (∀ z ∈ S, f z = 0) ∧ ‖f‖ ≤ 1 ∧
      ‖f x‖ = infDist x (S : Set X) := by
  obtain ⟨g, hgn, hgx⟩ := exists_dual_vector'' 𝕜 (S.mkQ x)
  let f : X →L[𝕜] 𝕜 := g.comp S.mkQL
  refine ⟨f, ?_, ?_, ?_⟩
  · intro z hz
    change g (S.mkQ z) = 0
    have hzq : S.mkQ z = 0 := (Submodule.Quotient.mk_eq_zero S).mpr hz
    rw [hzq, map_zero]
  · apply f.opNorm_le_bound zero_le_one
    intro z
    calc
      ‖f z‖ ≤ ‖g‖ * ‖S.mkQ z‖ := g.le_opNorm _
      _ ≤ 1 * ‖z‖ := mul_le_mul hgn (Submodule.Quotient.norm_mk_le S z)
        (norm_nonneg _) zero_le_one
  · change ‖g (S.mkQ x)‖ = _
    rw [hgx, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    exact QuotientAddGroup.norm_mk (S := S.toAddSubgroup) x

/-- The annihilator identity, with open mapping on the adjoint graph, yields
the ambient distance estimate for A. -/
theorem closed_range_of_adjoint_norm_closed [CompleteSpace X] [CompleteSpace Y]
    (A : Operator 𝕜 X Y) (hd : Dense (A.domain : Set X)) (hc : A.IsClosed)
    (hr : _root_.IsClosed ((banachAdjoint A).toFun.range : Set (X →L[𝕜] 𝕜))) :
    _root_.IsClosed (A.toFun.range : Set Y) := by
  obtain ⟨C, hC, hpre⟩ := bounded_preimages (banachAdjoint A) (banachAdjoint_closed A hd) hr
  have heq := adjoint_range_eq_of_norm_closed A hd hc hr
  apply BanachClosedRangeDistance.closed_range_of_distance_bound A hc C hC
  intro x
  obtain ⟨f, hf, hfn, hfx⟩ := exists_norming_annihilator A.ker (x : X)
  have hfr : f ∈ (banachAdjoint A).toFun.range := by
    change f ∈ ((banachAdjoint A).toFun.range : Set _)
    rw [heq]
    exact hf
  obtain ⟨q, hq, hqn⟩ := hpre f hfr
  calc
    infDist (x : X) (A.ker : Set X) = ‖f (x : X)‖ := hfx.symm
    _ = ‖(q : Y →L[𝕜] 𝕜) (A x)‖ := by rw [← hq, banachAdjoint_apply A hd q x]
    _ ≤ ‖(q : Y →L[𝕜] 𝕜)‖ * ‖A x‖ := (q : Y →L[𝕜] 𝕜).le_opNorm _
    _ ≤ C * ‖A x‖ := mul_le_mul_of_nonneg_right
      (hqn.trans (mul_le_of_le_one_right hC.le hfn)) (norm_nonneg _)

end ExpandedFA.Unbounded.BanachClosedRangeTheorem

namespace ExpandedFA.Unbounded

/-- Banach's closed range theorem for closed densely defined operators. -/
theorem banach_closed_range_equivalences :
    BanachClosedRangeTheoremSpec.ClosedRangeEquivalences := by
  intro 𝕜 X Y _ _ _ _ _ _ _ A hd hc
  dsimp only
  have hforward := BanachClosedRangeTheorem.adjoint_range_eq_of_closed_range A hd hc
  have hclosed := BanachClosedRangeTheorem.annihilator_isClosed A.ker
  have hiff : _root_.IsClosed (A.toFun.range : Set Y) ↔
      _root_.IsClosed ((banachAdjoint A).toFun.range : Set (X →L[𝕜] 𝕜)) :=
    ⟨fun hr => by rw [hforward hr]; exact hclosed,
      BanachClosedRangeTheorem.closed_range_of_adjoint_norm_closed A hd hc⟩
  refine ⟨hiff, ⟨hforward, ?_⟩,
    BanachClosedRangeTheorem.range_eq_preannihilator_iff A hd⟩
  intro heq
  apply hiff.mpr
  rw [heq]
  exact hclosed

end ExpandedFA.Unbounded

