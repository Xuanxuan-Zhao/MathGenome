import MathGenome.Internal.LinearPDE.P201Specs.Common.ExactTrace
import MathGenome.Internal.LinearPDE.P201.Common.SpatialInterfaces
import MathGenome.Internal.FourierSobolev.P102.Trace.ExactTrace
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section
set_option maxHeartbeats 3200000
set_option maxRecDepth 8000
open Set TopologicalSpace MeasureTheory
open scoped ENNReal ContDiff
namespace P201
namespace Trace
open P102.Trace.MeasuredFractional
open P201Specs.Trace

variable {m : ℕ} (Ω : Domain (m + 1)) (hΩ : IsBoundedLipschitzOpen Ω)

/-- A physical fractional graph point is uniquely determined by its surface class. -/
theorem graph_fst_injective : Function.Injective
    (fun u : P201Specs.Trace.fractionalGraph Ω hΩ => u.val.ofLp.1) := by
  intro u v huv
  apply Subtype.ext
  apply WithLp.ofLp_injective 1
  apply Prod.ext huv
  apply Lp.ext
  change u.val.ofLp.1 = v.val.ofLp.1 at huv
  have hu : (u.val.ofLp.2 : _ → ℝ) =ᵐ[_] metricIncrement (u.val.ofLp.1 : _ → ℝ) := u.property
  have hv : (v.val.ofLp.2 : _ → ℝ) =ᵐ[_] metricIncrement (v.val.ofLp.1 : _ → ℝ) := v.property
  exact hu.trans (by rw [huv]; exact hv.symm)

/-- The graph has exactly the prescribed intrinsic norm. -/
theorem graph_norm (u : P201Specs.Trace.fractionalGraph Ω hΩ) :
    ‖u‖ = ‖u.val.ofLp.1‖ +
      (metricSeminorm m (boundaryMeasure Ω) halfOrder 2
        (u.val.ofLp.1 : P201.Space (m + 1) → ℝ)).toReal := by
  haveI := P201Specs.Trace.boundaryFinite Ω hΩ
  change ‖u.val‖ = _
  rw [WithLp.prod_norm_eq_of_L1]
  change ‖u.val.ofLp.1‖ + ‖u.val.ofLp.2‖ = _
  rw [Lp.norm_def u.val.ofLp.2,
    eLpNorm_congr_ae u.property,
    eLpNorm_metricIncrement_eq_seminorm (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable _)]

/-- Every finite-energy surface class has its canonical graph point. -/
def dataToGraph (g : P102.Trace.Exact.BoundaryData ℝ Ω halfOrder 2) :
    P201Specs.Trace.fractionalGraph Ω hΩ := by
  haveI := P201Specs.Trace.boundaryFinite Ω hΩ
  have hg : MemLp (metricIncrement (g.val : P201.Space (m + 1) → ℝ)) 2
      (metricPairMeasure m (boundaryMeasure Ω) halfOrder 2) := by
    change eLpNorm _ _ _ < ⊤
    rw [eLpNorm_metricIncrement_eq_seminorm (by norm_num) (by norm_num)
      (Lp.aestronglyMeasurable g.val)]
    exact g.property
  exact ⟨WithLp.toLp 1 (g.val, hg.toLp _), hg.coeFn_toLp⟩

@[simp] theorem dataToGraph_fst (g : P102.Trace.Exact.BoundaryData ℝ Ω halfOrder 2) :
    (dataToGraph Ω hΩ g).val.ofLp.1 = g.val := rfl

@[simp] theorem dataToGraph_norm (g : P102.Trace.Exact.BoundaryData ℝ Ω halfOrder 2) :
    ‖dataToGraph Ω hΩ g‖ = P102.Trace.Exact.dataNorm g := graph_norm Ω hΩ _

/-- The converse uses finiteness of the L² increment, not a trace certificate. -/
def graphToData (u : P201Specs.Trace.fractionalGraph Ω hΩ) :
    P102.Trace.Exact.BoundaryData ℝ Ω halfOrder 2 := by
  haveI := P201Specs.Trace.boundaryFinite Ω hΩ
  refine ⟨u.val.ofLp.1, ?_⟩
  rw [← eLpNorm_metricIncrement_eq_seminorm (by norm_num) (by norm_num)
    (Lp.aestronglyMeasurable u.val.ofLp.1), ← eLpNorm_congr_ae u.property]
  exact Lp.eLpNorm_lt_top _

@[simp] theorem graphToData_norm (u : P201Specs.Trace.fractionalGraph Ω hΩ) :
    P102.Trace.Exact.dataNorm (graphToData Ω hΩ u) = ‖u‖ :=
  (graph_norm Ω hΩ u).symm

/-- The graph realizes exactly the library's physical data, with the same norm. -/
def graphDataEquiv : P201Specs.Trace.fractionalGraph Ω hΩ ≃
    P102.Trace.Exact.BoundaryData ℝ Ω halfOrder 2 where
  toFun := graphToData Ω hΩ
  invFun := dataToGraph Ω hΩ
  left_inv u := graph_fst_injective Ω hΩ rfl
  right_inv g := Subtype.ext rfl

include hΩ in
/-- Transfer an ordinary trace to the full H¹ norm, retaining its canonical
smooth boundary values and its actual closure kernel. -/
theorem ordinary_trace : ∃ T : H ℝ Ω 1 →L[ℝ] P201Specs.Trace.BoundaryL2 Ω,
    (∀ (u : H ℝ Ω 1) (f : P201.Space (m + 1) → ℝ), ContDiff ℝ ∞ f →
      hUnderlying Ω 1 u =ᵐ[domainMeasure Ω] f →
      (T u : P201.Space (m + 1) → ℝ) =ᵐ[boundaryMeasure Ω] f) ∧
    T.ker = P201Specs.hZeroSubmodule ℝ Ω := by
  obtain ⟨_, _, S, hS, _, _⟩ :=
    P102.Trace.Ordinary.ordinary_trace.1 m (graphFrame m) Ω hΩ ℝ 2 (by norm_num)
  refine ⟨S.comp (hToW ℝ Ω 1).toContinuousLinearMap, ?_, ?_⟩
  · intro u f hf hu
    exact hS _ f hf hu
  · change (S.toLinearMap.comp (hToW ℝ Ω 1).toLinearMap).ker = _
    rw [LinearMap.ker_comp]
    rw [P102.Trace.Ordinary.ordinary_trace.2.1 m (graphFrame m) Ω hΩ ℝ 2
      (by norm_num) S hS]
    exact (hZeroClosureBridge ℝ Ω).symm

/-- Inclusion into the physical L² space is injective in every dimension. -/
theorem inclusion_injective : Function.Injective (P201Specs.Trace.inclusion Ω hΩ) := by
  cases m with
  | zero => exact Function.injective_id
  | succ m => exact graph_fst_injective Ω hΩ

end Trace
end P201

namespace P201.Trace
open P102.Trace.MeasuredFractional
open P201Specs.Trace

/-- The higher-dimensional exact theorem, with the m ≥ 1 premise discharged
at the actual library application. -/
theorem higher_exact_trace (m : ℕ) (Ω : Domain ((m + 1) + 1))
    (hΩ : IsBoundedLipschitzOpen Ω) :
    ∃ (T : H ℝ Ω 1 →L[ℝ] P201Specs.Hhalf Ω hΩ)
      (L : P201Specs.Hhalf Ω hΩ →L[ℝ] H ℝ Ω 1),
      AgreesWithSmooth T ∧ Function.Surjective T ∧
      (∀ g, T (L g) = g) ∧ T.ker = P201Specs.hZeroSubmodule ℝ Ω := by
  obtain ⟨_, _, S, hS, _, _⟩ :=
    P102.Trace.Ordinary.ordinary_trace.1 (m + 1) (graphFrame (m + 1)) Ω hΩ ℝ 2
      (by norm_num)
  obtain ⟨C, hC, hb⟩ := P102.Trace.Exact.exact_trace.2.1 (m + 1) (by omega)
    (graphFrame (m + 1)) Ω hΩ ℝ 2 (by norm_num) (by norm_num)

  let E := hToW ℝ Ω 1
  let d (u : H ℝ Ω 1) : P102.Trace.Exact.BoundaryData ℝ Ω halfOrder 2 :=
    ⟨S (E u), (hb S hS (E u)).choose⟩
  let t : H ℝ Ω 1 →ₗ[ℝ] P201Specs.Hhalf Ω hΩ :=
    { toFun := fun u => dataToGraph Ω hΩ (d u)
      map_add' := by
        intro u v
        apply graph_fst_injective Ω hΩ
        exact (S.comp E.toContinuousLinearMap).map_add u v
      map_smul' := by
        intro c u
        apply graph_fst_injective Ω hΩ
        exact (S.comp E.toContinuousLinearMap).map_smul c u }
  have ht (u : H ℝ Ω 1) : ‖t u‖ ≤ (C * ‖E.toContinuousLinearMap‖) * ‖u‖ := by
    change ‖dataToGraph Ω hΩ (d u)‖ ≤ _
    rw [dataToGraph_norm Ω hΩ (d u)]
    have he : ‖E u‖ ≤ ‖E.toContinuousLinearMap‖ * ‖u‖ :=
      E.toContinuousLinearMap.le_opNorm u
    exact (hb S hS (E u)).choose_spec.trans
      ((mul_le_mul_of_nonneg_left he hC).trans_eq (mul_assoc _ _ _).symm)
  let T := t.mkContinuous (C * ‖E.toContinuousLinearMap‖) ht
  have hTf (u : H ℝ Ω 1) : P201Specs.Trace.inclusion Ω hΩ (T u) = S (E u) := rfl
  obtain ⟨D, l, hD, hladd, hlsmul, hlbound, hlright⟩ :=
    P102.Trace.Exact.right_inverse (m + 1) (by omega) (graphFrame (m + 1)) Ω hΩ
      ℝ 2 (by norm_num) (by norm_num)

  let l' : P201Specs.Hhalf Ω hΩ →ₗ[ℝ] H ℝ Ω 1 :=
    { toFun := fun g => E.symm (l (graphToData Ω hΩ g))
      map_add' := by
        intro g h
        rw [hladd (graphToData Ω hΩ g) (graphToData Ω hΩ h)
          (graphToData Ω hΩ (g + h)) rfl, map_add]
      map_smul' := by
        intro c g
        rw [hlsmul c (graphToData Ω hΩ g) (graphToData Ω hΩ (c • g)) rfl, map_smul]
        rfl }
  have hl' (g : P201Specs.Hhalf Ω hΩ) :
      ‖l' g‖ ≤ (‖E.symm.toContinuousLinearMap‖ * D) * ‖g‖ := by
    change ‖E.symm (l (graphToData Ω hΩ g))‖ ≤ _
    calc
      _ ≤ ‖E.symm.toContinuousLinearMap‖ * ‖l (graphToData Ω hΩ g)‖ :=
        E.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖E.symm.toContinuousLinearMap‖ * (D * ‖g‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg E.symm.toContinuousLinearMap)
        simpa only [graphToData_norm] using hlbound (graphToData Ω hΩ g)
      _ = _ := (mul_assoc _ _ _).symm
  let L := l'.mkContinuous (‖E.symm.toContinuousLinearMap‖ * D) hl'
  have hright (g : P201Specs.Hhalf Ω hΩ) : T (L g) = g := by
    apply inclusion_injective Ω hΩ
    rw [hTf]
    change S (E (E.symm (l (graphToData Ω hΩ g)))) = g.val.ofLp.1
    rw [E.apply_symm_apply]
    exact hlright S hS (graphToData Ω hΩ g)
  refine ⟨T, L, ?_, ?_, hright, ?_⟩
  · intro u f hf hu
    rw [hTf]
    exact hS _ f hf hu
  · exact fun g => ⟨L g, hright g⟩
  · have hker := P102.Trace.Ordinary.ordinary_trace.2.1
      (m + 1) (graphFrame (m + 1)) Ω hΩ ℝ 2 (by norm_num) S hS
    rw [P201.hZeroClosureBridge ℝ Ω, ← hker]
    ext u
    change T u = 0 ↔ S (E u) = 0
    rw [← hTf u]
    exact ⟨fun h => by rw [h, map_zero], fun h =>
      inclusion_injective Ω hΩ (by rw [h, map_zero])⟩

end P201.Trace

namespace P201.Trace
open P201Specs.Trace

/-- Endpoint counting L² is finite dimensional: evaluation embeds it into
the finite family of actual boundary atoms. -/
theorem boundaryL2_finiteDimensional (Ω : Domain 1)
    (hfinite : (frontier (Ω : Set (P201.Space 1))).Finite) :
    FiniteDimensional ℝ (P201Specs.Trace.BoundaryL2 Ω) := by
  classical
  letI : Fintype (frontier (Ω : Set (P201.Space 1))) := hfinite.fintype
  let ev : P201Specs.Trace.BoundaryL2 Ω →ₗ[ℝ]
      ((frontier (Ω : Set (P201.Space 1))) → ℝ) :=
    { toFun := fun g x => g x
      map_add' := by
        intro g h
        funext x
        exact P102.Trace.Ordinary.boundary_ae_eq_at_one_dimension Ω
          (Lp.coeFn_add g h) x.property
      map_smul' := by
        intro c g
        funext x
        exact P102.Trace.Ordinary.boundary_ae_eq_at_one_dimension Ω
          (Lp.coeFn_smul c g) x.property }
  apply FiniteDimensional.of_injective ev
  intro g h he
  apply Lp.ext
  filter_upwards [P102.Trace.Ordinary.boundaryMeasure_ae_frontier Ω] with x hx
  exact congrFun he ⟨x, hx⟩

/-- The endpoint case of the exact theorem. The section in this lemma is a
finite-dimensional linear section; the explicit affine section is separate. -/
theorem endpoint_exact_trace (Ω : Domain 1) (hΩ : IsBoundedLipschitzOpen Ω) :
    ∃ (T : H ℝ Ω 1 →L[ℝ] P201Specs.Hhalf Ω hΩ)
      (L : P201Specs.Hhalf Ω hΩ →L[ℝ] H ℝ Ω 1),
      AgreesWithSmooth T ∧ Function.Surjective T ∧
      (∀ g, T (L g) = g) ∧ T.ker = P201Specs.hZeroSubmodule ℝ Ω := by
  obtain ⟨S, hS, hker⟩ := ordinary_trace Ω hΩ
  obtain ⟨n, a, b, hab, hinj, hdis, hcover, hfront⟩ :=
    P102.Trace.Ordinary.physical_interval_decomposition (graphFrame 0) Ω hΩ
  have hfinite : (frontier (Ω : Set (P201.Space 1))).Finite := by
    rw [hfront]
    exact Set.finite_iUnion fun _ => by simp
  haveI := boundaryL2_finiteDimensional Ω hfinite
  let E := hToW ℝ Ω 1
  let S' := S.comp E.symm.toContinuousLinearMap
  have hS' : P102.Trace.Ordinary.IsTrace S' := by
    intro u f hf hu
    exact hS (E.symm u) f hf hu
  have hs' := P102.Trace.Ordinary.trace_surjective_of_finite_frontier hfinite S' hS'
  have hs : Function.Surjective S := by
    intro g
    obtain ⟨u, hu⟩ := hs' g
    exact ⟨E.symm u, hu⟩
  obtain ⟨l, hl⟩ := S.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hs)
  let L : P201Specs.Hhalf Ω hΩ →L[ℝ] H ℝ Ω 1 :=
    ⟨l, l.continuous_of_finiteDimensional⟩
  refine ⟨S, L, ?_, hs, ?_, hker⟩
  · exact hS
  · intro g
    exact congrArg (fun f : P201Specs.Trace.BoundaryL2 Ω →ₗ[ℝ]
      P201Specs.Trace.BoundaryL2 Ω => f g) hl

/-- Bounded exact trace on every bounded Lipschitz open set in every n ≥ 1. -/
theorem exact_trace : P201Specs.Trace.ExactStatement := by
  intro m Ω hΩ
  cases m with
  | zero => exact endpoint_exact_trace Ω hΩ
  | succ m => exact higher_exact_trace m Ω hΩ

end P201.Trace

namespace P201.Trace
open P102.Trace.Ordinary
open P102.U4

/-- Distinct endpoints prevent two disjoint open components from touching. -/
theorem closed_components_disjoint {n : ℕ} (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i) (hinj : Function.Injective (Sum.elim a b))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) :
    Pairwise (fun i j => Disjoint (Icc (a i) (b i)) (Icc (a j) (b j))) := by
  intro i j hij
  have hne : b i ≠ a j := by
    intro h
    have he := hinj (show Sum.elim a b (Sum.inr i) = Sum.elim a b (Sum.inl j) from h)
    cases he
  have hne' : b j ≠ a i := by
    intro h
    have he := hinj (show Sum.elim a b (Sum.inr j) = Sum.elim a b (Sum.inl i) from h)
    cases he
  have hd := Set.Ioo_disjoint_Ioo.mp (hdis hij)
  simp only [min_le_iff, le_max_iff] at hd
  apply Set.disjoint_left.mpr
  intro t ht ht'
  rcases hd with (hd | hd) | (hd | hd)
  · linarith [hab i]
  · have := lt_of_le_of_ne hd hne'
    linarith [ht'.2, ht.1]
  · have := lt_of_le_of_ne hd hne
    linarith [ht.2, ht'.1]
  · linarith [hab j]

/-- Fixed smooth compact cutoffs separate all the closed component intervals. -/
theorem interval_cutoffs {n : ℕ} (a b : Fin n → ℝ)
    (hab : ∀ i, a i < b i) (hinj : Function.Injective (Sum.elim a b))
    (hdis : Pairwise (fun i j => Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) :
    ∃ ζ : Fin n → WholeTests 1 ℝ,
      ∀ i j t, t ∈ Icc (a j) (b j) → ζ i (linePoint t) = if i = j then 1 else 0 := by
  classical
  let K : Fin n → Set (P201.Space 1) := fun i => linePoint '' Icc (a i) (b i)
  have hK (i) : IsCompact (K i) := isCompact_Icc.image lineIsometry.continuous
  have hdK : Pairwise (fun i j => Disjoint (K i) (K j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨t, ht, he⟩ ⟨t', ht', he'⟩
    have htt : t = t' := lineIsometry.injective (he.trans he'.symm)
    subst t'
    exact Set.disjoint_left.mp (closed_components_disjoint a b hab hinj hdis hij) ht ht'
  obtain ⟨R, hR⟩ := (isCompact_iUnion hK).isBounded.subset_ball 0
  have hz (i : Fin n) : ∃ ζ : WholeTests 1 ℝ,
      ∀ j t, t ∈ Icc (a j) (b j) → ζ (linePoint t) = if i = j then 1 else 0 := by
    let A := ⋃ j : {j : Fin n // j ≠ i}, K j.val
    have hA : IsClosed A := (isCompact_iUnion (fun j : {j : Fin n // j ≠ i} => hK j.val)).isClosed
    let U := Metric.ball (0 : P201.Space 1) R ∩ Aᶜ
    have hKU : K i ⊆ U := by
      intro x hx
      refine ⟨hR (mem_iUnion.mpr ⟨i, hx⟩), ?_⟩
      intro hxA
      obtain ⟨j, hj⟩ := mem_iUnion.mp hxA
      exact Set.disjoint_left.mp (hdK (Ne.symm j.property)) hx hj
    obtain ⟨f, hf, _, hsupp, hone⟩ :=
      exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
        (Metric.isOpen_ball.inter hA.isOpen_compl) (hK i).isClosed hKU
    have hfc : HasCompactSupport f := by
      apply (isCompact_closedBall (0 : P201.Space 1) R).of_isClosed_subset isClosed_closure
      change closure (Function.support f) ⊆ Metric.closedBall (0 : P201.Space 1) R
      rw [hsupp]
      exact closure_minimal (fun x hx => Metric.ball_subset_closedBall hx.1) Metric.isClosed_closedBall
    refine ⟨⟨f, hf, hfc, subset_univ _⟩, ?_⟩
    intro j t ht
    change f (linePoint t) = if i = j then 1 else 0
    by_cases hij : i = j
    · subst j
      simpa using (hone (linePoint t)).mp ⟨t, ht, rfl⟩
    · rw [ite_eq_right hij]
      apply Function.notMem_support.mp
      rw [hsupp]
      intro hx
      exact hx.2 (mem_iUnion.mpr ⟨⟨j, Ne.symm hij⟩, ⟨t, ht, rfl⟩⟩)
  choose ζ hζ using hz
  exact ⟨ζ, hζ⟩

/-- Restrict the unique Sobolev class of a whole-space compact smooth test. -/
def wholeTestToH (Ω : Domain 1) (φ : WholeTests 1 ℝ) : H ℝ Ω 1 :=
  (hToW ℝ Ω 1).symm
    (P102.U4.sobolevRestrict Ω (Classical.choose (P102.U4.wholeSpace_smoothTests 1 2 φ)))

theorem wholeTestToH_ae (Ω : Domain 1) (φ : WholeTests 1 ℝ) :
    hUnderlying Ω 1 (wholeTestToH Ω φ) =ᵐ[domainMeasure Ω] φ := by
  have hw := Classical.choose_spec (P102.U4.wholeSpace_smoothTests 1 2 φ)
  have hw0 := hw (zeroSobolevIndex 1 1)
  simp only [zeroSobolevIndex, P102.U4.multiPartial, Multiset.sort_zero, P102.U4.partialWord] at hw0
  exact (P102.U4.domainLpRestrict_ae Ω _).trans (ae_restrict_of_ae hw0)

def wholeTestToHLinear (Ω : Domain 1) : WholeTests 1 ℝ →ₗ[ℝ] H ℝ Ω 1 where
  toFun := wholeTestToH Ω
  map_add' φ ψ := by
    apply P201.hilbertUnderlyingInjective Ω 1
    apply Lp.ext
    rw [map_add]
    filter_upwards [wholeTestToH_ae Ω (φ + ψ), wholeTestToH_ae Ω φ,
      wholeTestToH_ae Ω ψ,
      Lp.coeFn_add (hUnderlying Ω 1 (wholeTestToH Ω φ))
        (hUnderlying Ω 1 (wholeTestToH Ω ψ))] with x hx hφ hψ hsum
    simp only [Pi.add_apply] at hsum
    exact hx.trans (by rw [hsum, hφ, hψ]; rfl)
  map_smul' c φ := by
    apply P201.hilbertUnderlyingInjective Ω 1
    apply Lp.ext
    rw [map_smul]
    change (hUnderlying Ω 1 (wholeTestToH Ω (c • φ)) : _ → ℝ) =ᵐ[_]
      ((c • hUnderlying Ω 1 (wholeTestToH Ω φ) : Lp ℝ Ω 2) : _ → ℝ)
    filter_upwards [wholeTestToH_ae Ω (c • φ), wholeTestToH_ae Ω φ,
      Lp.coeFn_smul c (hUnderlying Ω 1 (wholeTestToH Ω φ))] with x hx hφ hsmul
    simp only [Pi.smul_apply] at hsmul
    exact hx.trans (by rw [hsmul, hφ]; rfl)

end P201.Trace

namespace P201.Trace
open P102.Trace.Ordinary
open P102.U4

/-- Intervalwise affine interpolation gives a bounded linear section of the
same endpoint trace, including empty and disconnected bounded Lipschitz opens. -/
theorem endpoint_affine : P201Specs.Trace.EndpointAffineStatement := by
  classical
  intro Ω hΩ
  obtain ⟨T, hT, hker⟩ := ordinary_trace Ω hΩ
  obtain ⟨n, a, b, hab, hinj, hdis, hcover, hfront⟩ :=
    physical_interval_decomposition (graphFrame 0) Ω hΩ
  have hfinite : (frontier (Ω : Set (P201.Space 1))).Finite := by
    rw [hfront]
    exact Set.finite_iUnion fun _ => by simp
  haveI := boundaryL2_finiteDimensional Ω hfinite
  have hfa (i : Fin n) : linePoint (a i) ∈ frontier (Ω : Set (P201.Space 1)) := by
    rw [hfront]; exact mem_iUnion.mpr ⟨i, by simp⟩
  have hfb (i : Fin n) : linePoint (b i) ∈ frontier (Ω : Set (P201.Space 1)) := by
    rw [hfront]; exact mem_iUnion.mpr ⟨i, by simp⟩
  obtain ⟨ζ, hζ⟩ := interval_cutoffs a b hab hinj hdis
  let φa : Fin n → WholeTests 1 ℝ := fun i =>
    ⟨fun x => ζ i x * ((b i - lineIsometry.symm x) / (b i - a i)),
      (ζ i).contDiff.mul ((contDiff_const.sub lineIsometry.symm.contDiff).div_const _),
      (ζ i).hasCompactSupport.mul_right, subset_univ _⟩
  let φb : Fin n → WholeTests 1 ℝ := fun i =>
    ⟨fun x => ζ i x * ((lineIsometry.symm x - a i) / (b i - a i)),
      (ζ i).contDiff.mul ((lineIsometry.symm.contDiff.sub contDiff_const).div_const _),
      (ζ i).hasCompactSupport.mul_right, subset_univ _⟩
  let ea (i : Fin n) := boundaryEvaluation (𝕜 := ℝ) (p := 2) (by norm_num) (linePoint (a i)) (hfa i)
  let eb (i : Fin n) := boundaryEvaluation (𝕜 := ℝ) (p := 2) (by norm_num) (linePoint (b i)) (hfb i)
  let F : P201Specs.Trace.BoundaryL2 Ω →ₗ[ℝ] WholeTests 1 ℝ :=
    ∑ i, ((ea i).toLinearMap.smulRight (φa i) + (eb i).toLinearMap.smulRight (φb i))
  have hF (g : P201Specs.Trace.BoundaryL2 Ω) (j : Fin n) (t : ℝ)
      (ht : t ∈ Icc (a j) (b j)) :
      F g (linePoint t) = ((b j - t) / (b j - a j)) * g (linePoint (a j)) +
        ((t - a j) / (b j - a j)) * g (linePoint (b j)) := by
    have hcoord : lineIsometry.symm (linePoint t) = t := lineIsometry.symm_apply_apply t
    have he : F g (linePoint t) = ∑ i,
        ζ i (linePoint t) * (((b i - t) / (b i - a i)) * g (linePoint (a i)) +
          ((t - a i) / (b i - a i)) * g (linePoint (b i))) := by
      simp only [F, LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smulRight_apply,
        FunLike.coe_sum, Finset.sum_apply, FunLike.coe_add, FunLike.coe_smul,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro i _
      change g (linePoint (a i)) * (ζ i (linePoint t) * ((b i - lineIsometry.symm (linePoint t)) / (b i - a i))) +
        g (linePoint (b i)) * (ζ i (linePoint t) * ((lineIsometry.symm (linePoint t) - a i) / (b i - a i))) = _
      rw [hcoord]
      ring
    rw [he, Finset.sum_eq_single j]
    · rw [hζ j j t ht, ite_eq_left rfl, one_mul]
    · intro i _ hij
      rw [hζ i j t ht, ite_eq_right hij, zero_mul]
    · simp
  let l := (wholeTestToHLinear Ω).comp F
  let L : P201Specs.Hhalf Ω hΩ →L[ℝ] H ℝ Ω 1 :=
    ⟨l, l.continuous_of_finiteDimensional⟩
  have hL (g : P201Specs.Hhalf Ω hΩ) :
      hUnderlying Ω 1 (L g) =ᵐ[domainMeasure Ω] F g := wholeTestToH_ae Ω (F g)
  have hend (g : P201Specs.Hhalf Ω hΩ) (i : Fin n) :
      F g (linePoint (a i)) = g (linePoint (a i)) ∧
      F g (linePoint (b i)) = g (linePoint (b i)) := by
    have hi : b i - a i ≠ 0 := (sub_pos.mpr (hab i)).ne'
    constructor
    · rw [hF g i (a i) ⟨le_rfl, (hab i).le⟩]
      simp [hi]
    · rw [hF g i (b i) ⟨(hab i).le, le_rfl⟩]
      simp [hi]
  have hright (g : P201Specs.Hhalf Ω hΩ) : T (L g) = g := by
    apply Lp.ext
    have ht := hT (L g) (F g) (F g).contDiff (hL g)
    filter_upwards [ht, boundaryMeasure_ae_frontier Ω] with x hx hxf
    rw [hx]
    rw [hfront] at hxf
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxf
    rcases (by simpa only [mem_insert_iff, mem_singleton_iff] using hi) with hi | hi
    · subst x; exact (hend g i).1
    · subst x; exact (hend g i).2
  refine ⟨n, a, b, T, L, hab, hinj, hdis, hcover, hfront, hT, hright, hker, ?_⟩
  intro g i
  have hsub : Ioo (a i) (b i) ⊆ linePoint ⁻¹' (Ω : Set (P201.Space 1)) := by
    intro t ht
    rw [hcover]
    exact mem_iUnion.mpr ⟨i, ⟨t, ht, rfl⟩⟩
  have hline := linePoint_ae_restrict (hL g)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hline,
    ae_restrict_mem measurableSet_Ioo] with t ht hti
  exact ht.trans (hF g i t ⟨hti.1.le, hti.2.le⟩)

end P201.Trace

namespace P201
abbrev Hhalf : P201Specs.HhalfExportType := @P201Specs.Hhalf
abbrev HminusHalf : P201Specs.HminusHalfExportType := @P201Specs.HminusHalf

namespace Trace
open P102.Trace.MeasuredFractional
open P201Specs.Trace

/-- The graph realization has exactly the physical Gagliardo classes and
norm at p=2, s=1/2; this is stronger than an abstract trace-space equivalence. -/
theorem physical_space : P201Specs.Trace.PhysicalSpaceStatement := by
  intro m Ω hΩ
  refine ⟨?_, ?_⟩
  · intro u
    have hs := congrArg (fun s : ℝ =>
      (metricSeminorm (m + 1) (boundaryMeasure Ω) s 2
        (P201Specs.Trace.inclusion Ω hΩ u : P201.Space ((m + 1) + 1) → ℝ)).toReal) halfOrder_eq
    exact (graph_norm Ω hΩ u).trans
      (congrArg (fun t : ℝ => ‖P201Specs.Trace.inclusion Ω hΩ u‖ + t) hs)
  · intro g
    rw [← halfOrder_eq]
    constructor
    · rintro ⟨u, rfl⟩
      exact (graphToData Ω hΩ u).property
    · intro hg
      exact ⟨dataToGraph Ω hΩ ⟨g, hg⟩, rfl⟩

/-- The one-dimensional branch is the specified counting-measure L². -/
theorem endpoint_space : P201Specs.Trace.EndpointSpaceStatement := by
  intro Ω hΩ
  exact ⟨P201.boundaryCountingMeasure Ω, fun _ => rfl, Function.bijective_id⟩

/-- The complete C02 obligation, including both physical norm identifications
and the affine endpoint lifting, without an assumed lifting certificate. -/
theorem full_exact_trace : P201Specs.Trace.FullStatement :=
  ⟨physical_space, endpoint_space, exact_trace, endpoint_affine⟩

end Trace
end P201
