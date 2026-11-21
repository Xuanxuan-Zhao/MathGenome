import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceGeometry
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SharpTrace

/-! C² boundary geometry. No use is made of the pending SecondTrace theorem. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension ExpandedFA.PartIV.FractionalSobolev
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Forget only the second derivative, keeping precisely the given flattenings. -/
theorem c2Charts_to_c1 {d : ℕ} (Ω : Opens (Domain d))
    (hΩ : ∀ x ∈ frontier (Ω : Set (Domain d)),
      ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
        x ∈ Φ.source ∧ Φ x i = 0 ∧
        ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
        ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) : IsC1Domain Ω := by
  intro x hx
  obtain ⟨i, Φ, hxΦ, hz, hΦ, hInv, hside⟩ := hΩ x hx
  exact ⟨i, Φ, hxΦ, hz, hΦ.of_le (by norm_num), hInv.of_le (by norm_num), hside⟩

/-- Shrinking a C² chart by the existing geometric C¹ shrinking lemma does
not lose C² regularity: that lemma preserves both ambient functions exactly. -/
theorem local_c2_bilipschitz_chart {d : ℕ} (Ω : Opens (Domain d))
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (x : Domain d) (hx : x ∈ Φ.source)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) :
    ∃ (Ψ : OpenPartialHomeomorph (Domain d) (Domain d)) (K L : ℝ≥0),
      x ∈ Ψ.source ∧ ContDiffOn ℝ 2 Ψ Ψ.source ∧
      ContDiffOn ℝ 2 Ψ.symm Ψ.target ∧
      Bornology.IsBounded Ψ.source ∧ Bornology.IsBounded Ψ.target ∧
      (∀ y ∈ Ψ.source, y ∈ Ω ↔ 0 < Ψ y i) ∧
      LipschitzOnWith K Ψ Ψ.source ∧ LipschitzOnWith L Ψ.symm Ψ.target := by
  obtain ⟨K, U, hU, hLip⟩ :=
    ((hΦ.of_le (by norm_num) x hx).contDiffAt (Φ.open_source.mem_nhds hx)).exists_lipschitzOnWith
  obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp hU
  let Θ := Φ.restrOpen V hV
  have hΘ : ContDiffOn ℝ 2 Θ Θ.source := hΦ.mono inter_subset_left
  have hΘinv : ContDiffOn ℝ 2 Θ.symm Θ.target := hInv.mono inter_subset_left
  obtain ⟨Ψ, r, hr, hxΨ, ht, hs, hst, _, _, hb, hbt, he, hei, _, _, C, hC, _, hD⟩ :=
    shrink_c1_chart Θ x ⟨hx, hxV⟩ (hΘ.of_le (by norm_num)) (hΘinv.of_le (by norm_num))
  have hΨ : ContDiffOn ℝ 2 Ψ Ψ.source := by
    rw [he]
    exact hΘ.mono (fun _ hy => hs (subset_closure hy))
  have hΨinv : ContDiffOn ℝ 2 Ψ.symm Ψ.target := by
    rw [hei]
    exact hΘinv.mono (fun _ hy => hst (subset_closure hy))
  refine ⟨Ψ, K, ⟨C, hC⟩, hxΨ, hΨ, hΨinv, hb, hbt, ?_, ?_, ?_⟩
  · intro y hy
    rw [he]
    exact hside y (hs (subset_closure hy)).1
  · rw [he]
    exact hLip.mono (fun _ hy => hVU (hs (subset_closure hy)).2)
  · apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
      (fun y hy => ((hΨinv.of_le (by norm_num)).differentiableOn_one y hy).differentiableAt
        (Ψ.open_target.mem_nhds hy)) (fun y hy => ?_)
    · rw [ht]
      exact convex_ball _ _
    · exact_mod_cast hD y hy

/-- The finite extraction keeps the actual C² regularity and genuine
Lipschitz bounds in both directions, also for the empty frontier. -/
theorem finite_c2_charts : Specs.ExpandedFA.PartIV.SecondTraceGeometry.FiniteC2Charts := by
  classical
  intro d Ω hΩ hc
  have localCharts (x : frontier (Ω : Set (Domain d))) :
      ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (K L : ℝ≥0),
        x.val ∈ Φ.source ∧ ContDiffOn ℝ 2 Φ Φ.source ∧
        ContDiffOn ℝ 2 Φ.symm Φ.target ∧
        Bornology.IsBounded Φ.source ∧ Bornology.IsBounded Φ.target ∧
        (∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) ∧
        LipschitzOnWith K Φ Φ.source ∧ LipschitzOnWith L Φ.symm Φ.target := by
    obtain ⟨i, Φ, hx, _, hΦ, hInv, hside⟩ := hΩ x.val x.property
    obtain ⟨Ψ, K, L, hΨ⟩ := local_c2_bilipschitz_chart Ω Φ i x.val hx hΦ hInv hside
    exact ⟨i, Ψ, K, L, hΨ⟩
  choose i Φ K L hx hreg hinv hbound hboundinv hside hLip hLipinv using localCharts
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover (fun x => (Φ x).source)
    (fun x => (Φ x).open_source)
    (fun x hx' => mem_iUnion.mpr ⟨⟨x, hx'⟩, hx ⟨x, hx'⟩⟩)
  let q := s.equivFin.symm
  refine ⟨s.card, fun j => i (q j).val, fun j => Φ (q j).val,
    fun j => K (q j).val, fun j => L (q j).val, ?_, ?_⟩
  · intro j
    exact ⟨hreg _, hinv _, hbound _, hboundinv _, hside _, hLip _, hLipinv _⟩
  · intro y hy
    obtain ⟨z, hz⟩ := mem_iUnion.mp (hs hy)
    obtain ⟨hzs, hyz⟩ := mem_iUnion.mp hz
    refine mem_iUnion.mpr ⟨s.equivFin ⟨z, hzs⟩, ?_⟩
    simpa [q] using hyz

/-- Construct the full surface model while retaining the ambient C² charts.
The measure comparison is the accepted surface/atlas theorem, applied to this
particular atlas; it does not replace surfaceMeasure by a new measure. -/
theorem c2_boundary_model_nonempty {n : ℕ} (Ω : Opens (Domain (n + 1)))
    (hΩ : ∀ x ∈ frontier (Ω : Set (Domain (n + 1))),
      ∃ (i : Fin (n + 1)) (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))),
        x ∈ Φ.source ∧ Φ x i = 0 ∧
        ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
        ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (hc : IsCompact (frontier (Ω : Set (Domain (n + 1)))))
    (x₀ : frontier (Ω : Set (Domain (n + 1))))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Nonempty (C2BoundaryModel 𝕜 Ω p) := by
  classical
  obtain ⟨N, i, Φ, K, L, hreg, hcover⟩ := finite_c2_charts (n + 1) Ω hΩ hc
  let U : Opens (Domain (n + 1)) :=
    ⟨⋃ j, (Φ j).source, isOpen_iUnion fun j => (Φ j).open_source⟩
  obtain ⟨κ, hκ, φ, hφLip, hφnonneg, hφsum, hφsub⟩ :=
    Boundary.finite_lipschitz_cutoffs U (frontier (Ω : Set (Domain (n + 1)))) hc hcover
      (Fin N) (fun j => (Φ j).source) (fun j => (Φ j).open_source) Subset.rfl
  let : Finite κ := hκ
  let : Fintype κ := Fintype.ofFinite κ
  choose P hP using hφLip
  choose ind hind using hφsub
  let q : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let Ψ := fun j => Φ (ind (q j))
  let normal := fun j => i (ind (q j))
  have hside : ∀ j y, y ∈ (Ψ j).source → (y ∈ Ω ↔ 0 < Ψ j y (normal j)) :=
    fun j => (hreg (ind (q j))).2.2.2.2.1
  let e := fun j => SharpTrace.frontierChart Ω x₀ (Ψ j) (normal j) (hside j)
  let θ : Fin (Fintype.card κ) → Tests ℝ (⊤ : Opens (Domain (n + 1))) :=
    fun j => ⟨φ (q j), (φ (q j)).contDiff, (φ (q j)).hasCompactSupport, by simp⟩
  let η : Fin (Fintype.card κ) → frontier (Ω : Set (Domain (n + 1))) → ℝ :=
    fun j x => θ j x.val
  have hηsub : ∀ j, tsupport (η j) ⊆ (e j).source := by
    intro j
    exact (C1Geometry.tsupport_restrict_subset _ (θ j)).trans (preimage_mono (hind (q j)))
  have hηsum : ∀ x, ∑ j, η j x = 1 := by
    intro x
    change ∑ j, φ (q j) x.val = 1
    rw [q.sum_comp (fun k => φ k x.val)]
    simpa only [finsum_eq_sum_of_fintype] using hφsum x.val x.property
  let A : Boundary.FiniteAtlas (frontier (Ω : Set (Domain (n + 1)))) n (Fin (Fintype.card κ)) := {
    chart := e
    cover := by
      intro x
      have hn : ∃ j, η j x ≠ 0 := by
        by_contra hn
        push Not at hn
        have hz := hηsum x
        simp only [hn, Finset.sum_const_zero] at hz
        exact zero_ne_one hz
      obtain ⟨j, hj⟩ := hn
      exact ⟨j, hηsub j (subset_tsupport (η j) hj)⟩
    chartLip := fun j => K (ind (q j))
    chartSymmLip := fun j => L (ind (q j))
    chart_lipschitz := fun j => SharpTrace.frontierChart_lipschitz Ω x₀ _ _ _
      (hreg (ind (q j))).2.2.2.2.2.1
    chartSymm_lipschitz := fun j => SharpTrace.frontierChart_symm_lipschitz Ω x₀ _ _ _
      (hreg (ind (q j))).2.2.2.2.2.2
    bounded_target := fun j => SharpTrace.frontierChart_target_bounded Ω x₀ _ _ _
      (hreg (ind (q j))).2.2.2.1
    cutoff := η
    cutoffLip := fun j => P (q j)
    cutoff_lipschitz := fun j => by
      have heq : η j = fun x => φ (q j) x.val := by funext x; rfl
      rw [heq]
      simpa only [Function.comp_def, mul_one] using
        (hP (q j)).comp (LipschitzWith.subtype_val (frontier (Ω : Set (Domain (n + 1)))))
    cutoff_nonneg := fun j x => hφnonneg (q j) x.val
    cutoff_sum := hηsum
    cutoff_subordinate := hηsub }
  exact ⟨{
    toBoundaryModel := SharpTrace.boundaryModelFromAtlas Ω p A
    normal := normal
    ambient := Ψ
    regular := fun j => ⟨(hreg (ind (q j))).1, (hreg (ind (q j))).2.1⟩
    side := hside
    chart_source := fun _ => rfl
    chart_apply := fun _ _ _ => rfl
    test := θ
    cutoff_eq := fun _ _ => rfl
    test_subordinate := fun j => hind (q j) }⟩

/-- An empty frontier admits an empty C² atlas, including ambient dimension
zero. Its surface and atlas Lp spaces are both the original zero quotient. -/
theorem c2_boundary_model_of_empty_frontier {d : ℕ} (Ω : Opens (Domain d))
    (hf : frontier (Ω : Set (Domain d)) = ∅)
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Nonempty (C2BoundaryModel 𝕜 Ω p) := by
  classical
  let : IsEmpty (frontier (Ω : Set (Domain d))) :=
    ⟨fun x => (eq_empty_iff_forall_notMem.mp hf) x.val x.property⟩
  let A : Boundary.FiniteAtlas (frontier (Ω : Set (Domain d))) (d - 1) (Fin 0) := {
    chart := fun j => Fin.elim0 j
    cover := isEmptyElim
    chartLip := fun j => Fin.elim0 j
    chartSymmLip := fun j => Fin.elim0 j
    chart_lipschitz := fun j => Fin.elim0 j
    chartSymm_lipschitz := fun j => Fin.elim0 j
    bounded_target := fun j => Fin.elim0 j
    cutoff := fun j => Fin.elim0 j
    cutoffLip := fun j => Fin.elim0 j
    cutoff_lipschitz := fun j => Fin.elim0 j
    cutoff_nonneg := fun j => Fin.elim0 j
    cutoff_sum := isEmptyElim
    cutoff_subordinate := fun j => Fin.elim0 j }
  have hμ : surfaceMeasure Ω = 0 := by simp [surfaceMeasure, hf]
  have hA : A.atlasMeasure = 0 := Subsingleton.elim _ _
  let : Subsingleton (BoundaryLp 𝕜 Ω p) :=
    ⟨fun _ _ => Lp.ext (by simp [Filter.EventuallyEq, hμ])⟩
  let : Subsingleton (Lp 𝕜 p A.atlasMeasure) :=
    ⟨fun _ _ => Lp.ext (by simp [Filter.EventuallyEq, hA])⟩
  exact ⟨{
    chartCount := 0
    atlas := A
    identify := LinearEquiv.ofSubsingleton _ _
    representative := fun _ _ _ => by simp [Filter.EventuallyEq, hA]
    forwardConstant := 0
    backwardConstant := 0
    forward_nonneg := le_rfl
    backward_nonneg := le_rfl
    forward_bound := fun _ => by simp [Subsingleton.elim _ (0 : Lp 𝕜 p A.atlasMeasure)]
    backward_bound := fun _ => by simp [Subsingleton.elim _ (0 : BoundaryLp 𝕜 Ω p)]
    normal := fun j => Fin.elim0 j
    ambient := fun j => Fin.elim0 j
    regular := fun j => Fin.elim0 j
    side := fun j => Fin.elim0 j
    chart_source := fun j => Fin.elim0 j
    chart_apply := fun j => Fin.elim0 j
    test := fun j => Fin.elim0 j
    cutoff_eq := fun j => Fin.elim0 j
    test_subordinate := fun j => Fin.elim0 j }⟩

/-- Existence of the genuine C² model needs only compactness of the frontier;
no analytic trace or higher-order chart transport is assumed. -/
theorem c2_boundary_models_exist {d : ℕ} (Ω : Opens (Domain d))
    (hΩ : ∀ x ∈ frontier (Ω : Set (Domain d)),
      ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
        x ∈ Φ.source ∧ Φ x i = 0 ∧
        ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
        ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (hc : IsCompact (frontier (Ω : Set (Domain d))))
    (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Nonempty (C2BoundaryModel 𝕜 Ω p) := by
  by_cases h : (frontier (Ω : Set (Domain d))).Nonempty
  · obtain ⟨x, hx⟩ := h
    cases d with
    | zero => obtain ⟨i, _⟩ := hΩ x hx; exact Fin.elim0 i
    | succ n => exact c2_boundary_model_nonempty Ω hΩ hc ⟨x, hx⟩ 𝕜 p
  · exact c2_boundary_model_of_empty_frontier Ω (Set.not_nonempty_iff_eq_empty.mp h) 𝕜 p

namespace C2BoundaryModel
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : C2BoundaryModel 𝕜 Ω p)

/-- The graph witness is uniquely fixed by its zero-order localized Lp class. -/
theorem higherPiece_unique (σ : ℝ) (g : BoundaryLp 𝕜 Ω p)
    (j : Fin B.chartCount) (u v : HigherFractionalSpace 𝕜 (d - 1) σ p)
    (hu : wholeLp (u.val.val (zeroIndex (d - 1) 1)) = B.atlas.localizedLp p j (B.identify g))
    (hv : wholeLp (v.val.val (zeroIndex (d - 1) 1)) = B.atlas.localizedLp p j (B.identify g)) :
    u = v := by
  apply Subtype.ext
  apply sobolev_underlying_injective 𝕜 (d - 1) ⊤ 1 p
  exact wholeLpLI.injective (hu.trans hv.symm)

theorem higherPiece_spec (σ : ℝ) (g : B.HigherData σ) (j : Fin B.chartCount) :
    wholeLp ((B.higherPiece σ g j).val.val (zeroIndex (d - 1) 1)) =
      B.atlas.localizedLp p j (B.identify g.val) := Classical.choose_spec (g.property j)
end C2BoundaryModel
/-- A nonzero scalar differential has a nonzero Euclidean coordinate gradient. -/
lemma sum_coordinate_squares_ne_zero {d : ℕ}
    (A : Domain d →L[ℝ] ℝ) (hA : A ≠ 0) :
    (∑ j : Fin d, (A (coordinateVector j)) ^ 2) ≠ 0 := by
  intro hz
  have hc (j : Fin d) : A (coordinateVector j) = 0 := by
    have hj : (A (coordinateVector j)) ^ 2 ≤ ∑ k : Fin d, (A (coordinateVector k)) ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg (A (coordinateVector k))) (Finset.mem_univ j)
    rw [hz] at hj
    nlinarith [sq_nonneg (A (coordinateVector j))]
  apply hA
  apply ContinuousLinearMap.ext
  intro v
  rw [pi_eq_sum_univ' v, map_sum]
  have hc' (j : Fin d) : A (Pi.single j (1 : ℝ)) = 0 := hc j
  simp only [map_smul, hc', smul_zero, Finset.sum_const_zero, zero_apply]

lemma normalized_component_le_one {d : ℕ} (v : Domain d) (j : Fin d) :
    |v j / Real.sqrt (∑ k : Fin d, (v k) ^ 2)| ≤ 1 := by
  have hv : (v j) ^ 2 ≤ ∑ k : Fin d, (v k) ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (v k)) (Finset.mem_univ j)
  have hbound : |v j| ≤ Real.sqrt (∑ k : Fin d, (v k) ^ 2) := by
    apply Real.le_sqrt_of_sq_le
    simpa only [sq_abs] using hv
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  by_cases hz : Real.sqrt (∑ k : Fin d, (v k) ^ 2) = 0
  · simp [hz]
  · exact (div_le_one (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz))).mpr hbound

/-- The outward defining function of an inward flattening is minus its
normal coordinate. In particular its differential cannot vanish. -/
lemma chart_defining_function {d : ℕ} (Ω : Opens (Domain d))
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d)) (i : Fin d)
    (hΦ : ContDiffOn ℝ 2 Φ Φ.source) (hInv : ContDiffOn ℝ 2 Φ.symm Φ.target)
    (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (x : Domain d) (hx : x ∈ Φ.source) :
    ContDiffOn ℝ 2 (fun y => -Φ y i) Φ.source ∧
    (∀ y ∈ Φ.source, y ∈ Ω ↔ (-Φ y i) < 0) ∧
    (∑ j : Fin d, (fderiv ℝ (fun y => -Φ y i) x (coordinateVector j)) ^ 2) ≠ 0 := by
  have hr : ContDiffOn ℝ 2 (fun y => -Φ y i) Φ.source := ((contDiffOn_pi.mp hΦ) i).neg
  refine ⟨hr, fun y hy => by simpa using hside y hy, ?_⟩
  apply sum_coordinate_squares_ne_zero
  intro hz
  have he : (fun y => -Φ (Φ.symm y) i) =ᶠ[𝓝 (Φ x)] fun y => -y i := by
    filter_upwards [Φ.open_target.mem_nhds (Φ.map_source hx)] with y hy
    rw [Φ.right_inv hy]
  have hcomp := he.fderiv_eq (𝕜 := ℝ)
  have hrd : DifferentiableAt ℝ (fun y => -Φ y i) x :=
    ((hr.of_le (by norm_num)).differentiableOn_one x hx).differentiableAt (Φ.open_source.mem_nhds hx)
  have hid : DifferentiableAt ℝ Φ.symm (Φ x) :=
    (((hInv.of_le (by norm_num)).differentiableOn_one _ (Φ.map_source hx))).differentiableAt
      (Φ.open_target.mem_nhds (Φ.map_source hx))
  rw [show (fun y => -Φ (Φ.symm y) i) = (fun y => -Φ y i) ∘ Φ.symm from rfl,
    fderiv_comp _ (by simpa only [Φ.left_inv hx] using hrd) hid,
    Φ.left_inv hx, hz, ContinuousLinearMap.zero_comp] at hcomp
  have hneg : fderiv ℝ (fun y : Domain d => -y i) (Φ x) =
      -(ContinuousLinearMap.proj i : Domain d →L[ℝ] ℝ) := by
    exact (((ContinuousLinearMap.proj i : Domain d →L[ℝ] ℝ).hasFDerivAt).neg).fderiv
  rw [hneg] at hcomp
  have := congrArg (fun A : Domain d →L[ℝ] ℝ => A (coordinateVector i)) hcomp
  simp [coordinateVector] at this
/-- A finite measurable family can be patched by taking the first active
member, with zero assigned off the union. No overlap identities are needed. -/
lemma finite_measurable_patching {X E : Type} [MeasurableSpace X]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (N : ℕ)
    (U : Fin N → Set X) (hU : ∀ j, MeasurableSet (U j))
    (f : Fin N → X → E)
    (hf : ∀ j, Measurable ((U j).indicator (f j))) :
    ∃ v : X → E, Measurable v ∧
      (∀ x, (∃ j, x ∈ U j) → ∃ j, x ∈ U j ∧ v x = f j x) ∧
      (∀ x, (∀ j, x ∉ U j) → v x = 0) := by
  classical
  induction N with
  | zero =>
    refine ⟨0, measurable_const, ?_, ?_⟩
    · rintro x ⟨j, _⟩; exact Fin.elim0 j
    · intro x _; rfl
  | succ N ih =>
    obtain ⟨v, hv, hactive, hoff⟩ := ih (fun j => U j.succ) (fun j => hU j.succ)
      (fun j => f j.succ) (fun j => hf j.succ)
    let w := (U 0).indicator (f 0) + (U 0)ᶜ.indicator v
    have hw : Measurable w := (hf 0).add (hv.indicator (hU 0).compl)
    refine ⟨w, hw, ?_, ?_⟩
    · intro x hx
      by_cases hx0 : x ∈ U 0
      · exact ⟨0, hx0, by simp [w, hx0]⟩
      · have htail : ∃ j : Fin N, x ∈ U j.succ := by
          obtain ⟨j, hj⟩ := hx
          refine Fin.cases (fun h => (hx0 h).elim) (fun k hk => ⟨k, hk⟩) j hj
        obtain ⟨j, hj, heq⟩ := hactive x htail
        exact ⟨j.succ, hj, by simpa [w, hx0] using heq⟩
    · intro x hx
      simp [w, hx 0, hoff x (fun j => hx j.succ)]

/-- A measurable outward normal is obtained from finitely many genuine
local defining functions, choosing the first chart on each measurable patch. -/
theorem outward_normal_exists {d : ℕ} (Ω : Opens (Domain d))
    (hΩ : ∀ x ∈ frontier (Ω : Set (Domain d)),
      ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
        x ∈ Φ.source ∧ Φ x i = 0 ∧
        ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
        ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (hc : IsCompact (frontier (Ω : Set (Domain d)))) :
    ∃ ν : Domain d → Domain d,
      (∀ j : Fin d, Measurable (fun x => ν x j)) ∧
  (∀ j : Fin d, ∀ᵐ x ∂surfaceMeasure Ω, |ν x j| ≤ 1) ∧
  ∀ x ∈ frontier (Ω : Set (Domain d)),
    ∃ (U : Set (Domain d)) (r : Domain d → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 2 r U ∧ r x = 0 ∧
      (∀ y ∈ U, y ∈ Ω ↔ r y < 0) ∧
      (∑ j : Fin d, (fderiv ℝ r x (coordinateVector j)) ^ 2) ≠ 0 ∧
      ∀ j : Fin d, ν x j = fderiv ℝ r x (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2) := by
  classical
  obtain ⟨N, i, Φ, K, L, hreg, hcover⟩ := finite_c2_charts d Ω hΩ hc
  let r := fun j y => -Φ j y (i j)
  let grad := fun j x k => fderiv ℝ (r j) x (coordinateVector k)
  let v := fun j x k => grad j x k / Real.sqrt (∑ l : Fin d, (grad j x l) ^ 2)
  have hr (j : Fin N) : ContDiffOn ℝ 2 (r j) (Φ j).source :=
    ((contDiffOn_pi.mp (hreg j).1) (i j)).neg
  have hn (j : Fin N) (x : Domain d) (hx : x ∈ (Φ j).source) :
      (∑ k : Fin d, (grad j x k) ^ 2) ≠ 0 :=
    (chart_defining_function Ω (Φ j) (i j) (hreg j).1 (hreg j).2.1
      (hreg j).2.2.2.2.1 x hx).2.2
  have hv (j : Fin N) : ContinuousOn (v j) (Φ j).source := by
    have hg (k : Fin d) : ContinuousOn (fun x => grad j x k) (Φ j).source :=
      ((hr j).continuousOn_fderiv_of_isOpen (Φ j).open_source (by norm_num)).clm_apply
        continuousOn_const
    apply continuousOn_pi.mpr
    intro k
    apply (hg k).div ((continuousOn_finsetSum _ (fun l _ => (hg l).pow 2)).sqrt)
    intro x hx
    exact (Real.sqrt_pos.mpr (lt_of_le_of_ne
      (Finset.sum_nonneg (fun l _ => sq_nonneg (grad j x l))) (Ne.symm (hn j x hx)))).ne'
  obtain ⟨ν, hν, hνactive, hνoff⟩ := finite_measurable_patching N
    (fun j => (Φ j).source) (fun j => (Φ j).open_source.measurableSet) v
    (fun j => (hv j).measurable_piecewise continuousOn_const (Φ j).open_source.measurableSet)
  refine ⟨ν, ?_, ?_, ?_⟩
  · intro j
    exact (measurable_pi_apply j).comp hν
  · intro k
    apply Filter.Eventually.of_forall
    intro x
    by_cases hx : ∃ j, x ∈ (Φ j).source
    · obtain ⟨j, _, heq⟩ := hνactive x hx
      rw [heq]
      exact normalized_component_le_one (grad j x) k
    · have heq := hνoff x (by simpa only [not_exists] using hx)
      simp [heq]
  · intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp (hcover hx)
    obtain ⟨k, hxk, hνk⟩ := hνactive x ⟨j, hxj⟩
    refine ⟨(Φ k).source, r k, (Φ k).open_source, hxk, hr k, ?_, ?_, hn k x hxk, ?_⟩
    · have hz := (chart_boundary_iff Ω (Φ k) (i k) (hreg k).2.2.2.2.1 x hxk).mp hx
      simp only [r, hz, neg_zero]
    · intro y hy
      simpa only [r, neg_lt_zero] using (hreg k).2.2.2.2.1 y hy
    · intro l
      rw [hνk]

/-- The entire geometric existence obligation, without any analytic
certificate assumptions. -/
theorem geometry_exists : Specs.ExpandedFA.PartIV.SecondTraceGeometry.GeometryExists := by
  intro 𝕜 _ d Ω hb hΩ p _ _ _
  have hc : IsCompact (frontier (Ω : Set (Domain d))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  exact ⟨c2_boundary_models_exist Ω hΩ hc 𝕜 p, outward_normal_exists Ω hΩ hc⟩

namespace C2BoundaryModel
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : C2BoundaryModel 𝕜 Ω p)

lemma higherEnergy_of_empty_frontier (hf : frontier (Ω : Set (Domain d)) = ∅)
    (σ : ℝ) (hp : p ≠ ∞) (g : BoundaryLp 𝕜 Ω p) : B.HasHigherEnergy σ g := by
  have hμ : surfaceMeasure Ω = 0 := by simp [surfaceMeasure, hf]
  have hg : g = 0 := Lp.ext (by simp [Filter.EventuallyEq, hμ])
  intro j
  refine ⟨⟨0, higher_finite_energy_zero σ p hp⟩, ?_⟩
  rw [hg, map_zero]
  change wholeLpLI 0 = B.atlas.localizer p j 0
  rw [map_zero, map_zero]

lemma higherDataNorm_of_empty_frontier (hf : frontier (Ω : Set (Domain d)) = ∅)
    (σ : ℝ) (hp : p ≠ ∞) (g : B.HigherData σ) : B.higherDataNorm σ g = 0 := by
  have hμ : surfaceMeasure Ω = 0 := by simp [surfaceMeasure, hf]
  have hg : g.val = 0 := Lp.ext (by simp [Filter.EventuallyEq, hμ])
  unfold higherDataNorm
  apply Finset.sum_eq_zero
  intro j _
  let z : HigherFractionalSpace 𝕜 (d - 1) σ p := ⟨0, higher_finite_energy_zero σ p hp⟩
  have hz : B.higherPiece σ g j = z := by
    apply B.higherPiece_unique σ g.val j _ z (B.higherPiece_spec σ g j)
    rw [hg, map_zero]
    change wholeLpLI 0 = B.atlas.localizer p j 0
    rw [map_zero, map_zero]
  rw [hz]
  exact (higherFractionalNorm_eq_zero_iff σ p hp z).mpr rfl
end C2BoundaryModel

/-- Complete higher-order atlas independence in the empty-boundary cases. -/
theorem higher_atlas_independence_empty_frontier {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (hf : frontier (Ω : Set (Domain d)) = ∅)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞) (B D : C2BoundaryModel 𝕜 Ω p) :
    (∀ g, B.HasHigherEnergy (2 - 1 / p.toReal) g ↔ D.HasHigherEnergy (2 - 1 / p.toReal) g) ∧
    ∃ C E : ℝ, 0 < C ∧ 0 < E ∧
      ∀ (g : B.HigherData (2 - 1 / p.toReal)) (h : D.HigherData (2 - 1 / p.toReal)),
        g.val = h.val →
        D.higherDataNorm (2 - 1 / p.toReal) h ≤ C * B.higherDataNorm (2 - 1 / p.toReal) g ∧
        B.higherDataNorm (2 - 1 / p.toReal) g ≤ E * D.higherDataNorm (2 - 1 / p.toReal) h := by
  refine ⟨fun g => ⟨fun _ => D.higherEnergy_of_empty_frontier hf _ hp g,
    fun _ => B.higherEnergy_of_empty_frontier hf _ hp g⟩, 1, 1, zero_lt_one, zero_lt_one, ?_⟩
  intro g h _
  rw [B.higherDataNorm_of_empty_frontier hf _ hp g, D.higherDataNorm_of_empty_frontier hf _ hp h]
  simp

namespace C2BoundaryModel
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B D : C2BoundaryModel 𝕜 Ω p)

lemma identify_change_atlas [CompactSpace (frontier (Ω : Set (Domain d)))]
    (g : BoundaryLp 𝕜 Ω p) :
    D.identify g = D.atlas.lpEquiv B.atlas p (B.identify g) := by
  apply Lp.ext
  have hB := B.representative g g Filter.EventuallyEq.rfl
  have hD := D.representative g g Filter.EventuallyEq.rfl
  have hBD : D.atlas.atlasMeasure ≪ B.atlas.atlasMeasure :=
    Measure.absolutelyContinuous_of_le_smul (D.atlas.atlasMeasure_le_smul_atlasMeasure B.atlas)
  exact hD.trans ((hBD.ae_eq hB).symm.trans
    (D.atlas.lpEquiv_representative B.atlas p (B.identify g)).symm)

/-- The zero-order inclusion of the actual higher graph into the original Lp
space is scalar linear. This does not assign derivatives by fiat. -/
def higherUnderlyingLM (σ : ℝ) [Fact (p ≠ ∞)] :
    HigherFractionalSpace 𝕜 (d - 1) σ p →ₗ[𝕜] Lp 𝕜 p (volume : Measure (Domain (d - 1))) := by
  exact {
    toFun := fun u => wholeLp (u.val.val (zeroIndex (d - 1) 1))
    map_add' := fun u v => by
      change wholeLpLI (u.val.val _ + v.val.val _) = _
      exact map_add wholeLpLI _ _
    map_smul' := fun c u => by
      change wholeLpLI (c • u.val.val _) = _
      exact map_smul wholeLpLI _ _ }

lemma higherDataNorm_nonneg (σ : ℝ) (g : B.HigherData σ) :
    0 ≤ B.higherDataNorm σ g :=
  Finset.sum_nonneg (fun j _ => higherFractionalNorm_nonneg σ p (B.higherPiece σ g j))

/-- All global membership and norm estimates follow once the genuine higher
Sobolev overlap estimates have been established. These hypotheses are only
an assembly interface, not assumptions of HigherAtlasIndependence. -/
lemma higher_atlas_domination [CompactSpace (frontier (Ω : Set (Domain d)))]
    (σ : ℝ) (hp : p ≠ ∞)
    (hoverlap : ∀ i : Fin D.chartCount, ∀ j : Fin B.chartCount,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : B.HigherData σ,
        ∃ v : HigherFractionalSpace 𝕜 (d - 1) σ p,
          wholeLp (v.val.val (zeroIndex (d - 1) 1)) =ᵐ[volume]
            D.atlas.overlapRepresentative B.atlas i j (B.identify g.val) ∧
          higherFractionalNorm σ p v ≤ C * higherFractionalNorm σ p (B.higherPiece σ g j)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : B.HigherData σ,
      ∃ hg : D.HasHigherEnergy σ g.val,
        D.higherDataNorm σ ⟨g.val, hg⟩ ≤ C * B.higherDataNorm σ g := by
  classical
  let : Fact (p ≠ ∞) := ⟨hp⟩
  choose C hC hv using hoverlap
  let Ctotal := ∑ i, ∑ j, C i j
  refine ⟨Ctotal, Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC i j)), ?_⟩
  intro g
  choose v hrep hnorm using fun i j => hv i j g
  let w := fun i => ∑ j, v i j
  have hw (i : Fin D.chartCount) :
      wholeLp ((w i).val.val (zeroIndex (d - 1) 1)) = D.atlas.localizedLp p i (D.identify g.val) := by
    have hsum : wholeLp ((w i).val.val (zeroIndex (d - 1) 1)) =
        ∑ j, wholeLp ((v i j).val.val (zeroIndex (d - 1) 1)) :=
      map_sum (higherUnderlyingLM (d := d) σ) (fun j => v i j) Finset.univ
    rw [hsum]
    apply Lp.ext
    have hident : D.identify g.val =ᵐ[D.atlas.atlasMeasure] B.identify g.val := by
      rw [B.identify_change_atlas D g.val]
      exact D.atlas.lpEquiv_representative B.atlas p (B.identify g.val)
    have hloc := (D.atlas.localizedLp_representative p i (D.identify g.val)).trans
      (D.atlas.localizedRepresentative_congr_ae i hident)
    filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun j => wholeLp ((v i j).val.val (zeroIndex (d - 1) 1))),
      ae_all_iff.mpr (hrep i), hloc] with x hsum hx hloc
    rw [hsum, hloc, D.atlas.localizedRepresentative_reconstruction B.atlas i (B.identify g.val)]
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => hx j)
  have hg : D.HasHigherEnergy σ g.val := fun i => ⟨w i, hw i⟩
  refine ⟨hg, ?_⟩
  have hpiece (i) : D.higherPiece σ ⟨g.val, hg⟩ i = w i :=
    D.higherPiece_unique σ g.val i _ _ (D.higherPiece_spec σ ⟨g.val, hg⟩ i) (hw i)
  simp only [higherDataNorm, hpiece]
  calc
    _ ≤ ∑ i, ∑ j, C i j * higherFractionalNorm σ p (B.higherPiece σ g j) := by
      apply Finset.sum_le_sum
      intro i _
      change ‖∑ j, v i j‖ ≤ _
      exact (norm_sum_le Finset.univ (fun j => v i j)).trans
        (Finset.sum_le_sum (fun j _ => hnorm i j))
    _ ≤ ∑ i, ∑ j, C i j * B.higherDataNorm σ g := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hC i j)
      exact Finset.single_le_sum (fun k _ => higherFractionalNorm_nonneg σ p _)
        (Finset.mem_univ j)
    _ = _ := by simp only [Ctotal, Finset.sum_mul]; rfl
end C2BoundaryModel

open ExpandedFA.Sobolev.Lines

set_option maxHeartbeats 1200000

namespace Analytic
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev
open ExpandedFA.PartIV.SharpTraceBound.AnalyticEstimates
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma whole_smooth_partial_energy_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (j : Fin d) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : SobolevSpace 𝕜 d ⊤ 1 p) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ 1 f)
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d))] f) :
    (∫⁻ z, ‖fderiv ℝ f z (coordinateVector j)‖ₑ ^ p.toReal) ≤
      ENNReal.ofReal ‖u‖ ^ p.toReal := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hd := C1Extension.Classical.c1_representative_derivative u f hf.contDiffOn hu j
  simp only [Opens.coe_top, Measure.restrict_univ] at hd
  have he : (∫⁻ z, ‖fderiv ℝ f z (coordinateVector j)‖ₑ ^ p.toReal) =
      ∫⁻ z, ‖wholeLp (u.val (coordinateIndex j)) z‖ₑ ^ p.toReal := by
    apply lintegral_congr_ae
    filter_upwards [hd, wholeLp_representative (u.val (coordinateIndex j))] with z hz hw
    rw [hw, hz]
  rw [he, lintegral_rpow_enorm_eq_rpow_eLpNorm' hpR,
    ← eLpNorm_eq_eLpNorm' hp0 hp (Lp.memLp _).aestronglyMeasurable,
    ← Lp.enorm_def, ← ofReal_norm]
  apply ENNReal.rpow_le_rpow _ hpR.le
  apply ENNReal.ofReal_le_ofReal
  change ‖wholeLpLI (u.val (coordinateIndex j))‖ ≤ ‖u‖
  rw [wholeLpLI.norm_map]
  exact PiLp.norm_apply_le u.val (coordinateIndex j)

lemma whole_smooth_fderiv_energy_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : SobolevSpace 𝕜 d ⊤ 1 p) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ 1 f)
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d))] f) :
    (∫⁻ z, ‖fderiv ℝ f z‖ₑ ^ p.toReal) ≤
      ((d : ℝ≥0∞) ^ (p.toReal-1) * d) * ENNReal.ofReal ‖u‖ ^ p.toReal := by
  have hpR : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  have hD := hf.continuous_fderiv (by norm_num)
  calc
    _ ≤ ∫⁻ z, (d : ℝ≥0∞) ^ (p.toReal-1) * ∑ j : Fin d,
          ‖fderiv ℝ f z (coordinateVector j)‖ₑ ^ p.toReal :=
      lintegral_mono (fun z => enorm_opNorm_rpow_le_sum_coordinate _ hpR)
    _ = (d : ℝ≥0∞) ^ (p.toReal-1) * ∑ j : Fin d,
        ∫⁻ z, ‖fderiv ℝ f z (coordinateVector j)‖ₑ ^ p.toReal := by
      rw [lintegral_const_mul _ (by fun_prop), lintegral_finsetSum _ (by intro j hj; fun_prop)]
    _ ≤ _ := by
      calc
        _ ≤ (d : ℝ≥0∞) ^ (p.toReal-1) * ∑ j : Fin d, ENNReal.ofReal ‖u‖ ^ p.toReal := by
          gcongr with j
          exact whole_smooth_partial_energy_bound j hp u f hf hu
        _ = _ := by simp [mul_assoc]

def wholeFirstIncrementConstant (d : ℕ) (p : ℝ≥0∞) : ℝ :=
  (((d : ℝ≥0∞) ^ (p.toReal - 1) * d).toReal) ^ (1 / p.toReal)

lemma wholeFirstIncrementConstant_nonneg (d : ℕ) (p : ℝ≥0∞) :
    0 ≤ wholeFirstIncrementConstant d p := Real.rpow_nonneg ENNReal.toReal_nonneg _

lemma smooth_whole_first_increment_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : SobolevSpace 𝕜 d ⊤ 1 p) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ 1 f)
    (hu : u.val (zeroIndex d 1) =ᵐ[volume.restrict ((⊤ : Opens (Domain d)) : Set (Domain d))] f)
    (h : Domain d) :
    ‖lpIncrement p h (wholeLp (u.val (zeroIndex d 1)))‖ ≤
      wholeFirstIncrementConstant d p * ‖h‖ * ‖u‖ := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out)
  have hpR : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hpR1 : 1 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp (Fact.out : 1 ≤ p)
  let A : ℝ≥0∞ := (d : ℝ≥0∞) ^ (p.toReal - 1) * d
  have hA : A ≠ ∞ := by
    dsimp [A]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by simp)) (by simp)
  let w := wholeLp (u.val (zeroIndex d 1))
  have hwf : w =ᵐ[volume] f := by
    apply (wholeLp_representative _).trans
    simpa only [Opens.coe_top, Measure.restrict_univ] using hu
  have hwfshift := (measurePreserving_add_right (volume : Measure (Domain d)) h).quasiMeasurePreserving.ae_eq_comp hwf
  have hraw : (∫⁻ x, ‖lpIncrement p h w x‖ₑ ^ p.toReal) ≤
      A * ENNReal.ofReal (‖h‖ * ‖u‖) ^ p.toReal := by
    calc
      _ = ∫⁻ x, ‖f (x+h)-f x‖ₑ ^ p.toReal := by
        apply lintegral_congr_ae
        filter_upwards [lpIncrement_representative p w h, hwf, hwfshift] with x hx hf0 hf1
        dsimp only [Function.comp_apply] at hf1
        rw [hx, hf0, hf1]
      _ ≤ ‖h‖ₑ ^ p.toReal * ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ p.toReal := by
        simpa using translation_affine_rpow f hf (ContinuousLinearMap.id ℝ (Domain d)) 0 h hpR1
      _ ≤ ‖h‖ₑ ^ p.toReal * (A * ENNReal.ofReal ‖u‖ ^ p.toReal) :=
        mul_le_mul_right (whole_smooth_fderiv_energy_bound hp u f hf hu) _
      _ = _ := by
        simp only [ENNReal.ofReal_mul (norm_nonneg h), ENNReal.mul_rpow_of_nonneg _ _ hpR.le, ofReal_norm]
        ring
  have hroot := energy_root_bound hA hpR (mul_nonneg (norm_nonneg h) (norm_nonneg u)) hraw
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hpR,
      ← eLpNorm_eq_eLpNorm' hp0 hp (Lp.memLp _).aestronglyMeasurable,
      ← Lp.enorm_def, ← ENNReal.rpow_mul, mul_one_div_cancel hpR.ne', ENNReal.rpow_one,
      ← ofReal_norm] at hroot
  have hbound := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (Real.rpow_nonneg ENNReal.toReal_nonneg _) (mul_nonneg (norm_nonneg h) (norm_nonneg u)))).mp hroot
  simpa only [wholeFirstIncrementConstant, mul_assoc, w, A] using hbound

lemma whole_first_increment_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : SobolevSpace 𝕜 d ⊤ 1 p) (h : Domain d) :
    ‖lpIncrement p h (wholeLp (u.val (zeroIndex d 1)))‖ ≤
      wholeFirstIncrementConstant d p * ‖h‖ * ‖u‖ := by
  obtain ⟨v, hv, hlim⟩ := mem_closure_iff_seq_limit.mp
    (Smoothing.smooth_density 𝕜 d ⊤ 1 p hp u)
  have hzero : Continuous (fun u : SobolevSpace 𝕜 d ⊤ 1 p =>
      wholeLp (u.val (zeroIndex d 1))) :=
    wholeLpLI.continuous.comp ((PiLp.continuous_apply 1 _ _).comp continuous_subtype_val)
  apply le_of_tendsto_of_tendsto
    ((((SharpTraceBound.lpIncrement_continuous_input p h).comp hzero).norm.tendsto u).comp hlim)
    (((continuous_const.mul continuous_norm).tendsto u).comp hlim)
  apply Eventually.of_forall
  intro k
  obtain ⟨f, hf, hvf⟩ := hv k
  have hf' : ContDiff ℝ 1 f := by
    apply contDiffOn_univ.mp
    exact hf.of_le (by simp)
  exact smooth_whole_first_increment_bound hp (v k) f hf' hvf h

lemma lpIncrement_norm_le_twice {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Lp 𝕜 p (volume : Measure (Domain d))) (h : Domain d) :
    ‖lpIncrement p h u‖ ≤ 2 * ‖u‖ := by
  let T := Lp.compMeasurePreservingₗᵢ 𝕜 (fun x : Domain d => x - (-h))
    (measurePreserving_sub_right volume (-h)) (p := p) (E := 𝕜)
  change ‖T u - u‖ ≤ _
  exact (norm_sub_le _ _).trans (by rw [T.norm_map]; ring_nf; exact le_rfl)

lemma whole_first_increment_cutoff_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (u : SobolevSpace 𝕜 d ⊤ 1 p) (h : Domain d) :
    ‖lpIncrement p h (wholeLp (u.val (zeroIndex d 1)))‖ ≤
      (max (wholeFirstIncrementConstant d p) 2 * ‖u‖) * incrementCutoff h := by
  have hbase : ‖wholeLp (u.val (zeroIndex d 1))‖ ≤ ‖u‖ := by
    change ‖wholeLpLI (u.val (zeroIndex d 1))‖ ≤ ‖u‖
    rw [wholeLpLI.norm_map]
    exact PiLp.norm_apply_le u.val _
  by_cases hnear : euclideanLength h ≤ 1
  · rw [incrementCutoff, min_eq_left hnear]
    calc
      _ ≤ wholeFirstIncrementConstant d p * ‖h‖ * ‖u‖ := whole_first_increment_bound hp u h
      _ ≤ wholeFirstIncrementConstant d p * euclideanLength h * ‖u‖ := by
        gcongr
        exact wholeFirstIncrementConstant_nonneg d p
        exact norm_le_euclideanLength h
      _ ≤ _ := by
        calc
          _ = wholeFirstIncrementConstant d p * (‖u‖ * euclideanLength h) := by ring
          _ ≤ max (wholeFirstIncrementConstant d p) 2 * (‖u‖ * euclideanLength h) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _)
              (mul_nonneg (norm_nonneg u) (norm_nonneg (WithLp.toLp 2 h)))
          _ = _ := by ring
  · rw [incrementCutoff, min_eq_right (le_of_not_ge hnear), mul_one]
    calc
      _ ≤ 2 * ‖wholeLp (u.val (zeroIndex d 1))‖ := lpIncrement_norm_le_twice p _ h
      _ ≤ 2 * ‖u‖ := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg u)

def wholeFirstFractionalConstant (d : ℕ) (s : ℝ) (p : ℝ≥0∞) : ℝ :=
  1 + max (wholeFirstIncrementConstant d p) 2 *
    (eLpNorm (@incrementCutoff d) p (differenceMeasure s p)).toReal

lemma wholeFirstFractionalConstant_nonneg (d : ℕ) (s : ℝ) (p : ℝ≥0∞) :
    0 ≤ wholeFirstFractionalConstant d s p := by
  unfold wholeFirstFractionalConstant
  positivity

lemma whole_first_fractional_norm_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hs0 : 0 < s) (hs1 : s < 1)
    (hp : p ≠ ∞) (u : SobolevSpace 𝕜 d ⊤ 1 p) :
    ∃ hfin : differenceEnergy s p (wholeLp (u.val (zeroIndex d 1))) < ∞,
      fractionalNorm s p ⟨wholeLp (u.val (zeroIndex d 1)), hfin⟩ ≤
        wholeFirstFractionalConstant d s p * ‖u‖ := by
  let K := max (wholeFirstIncrementConstant d p) 2
  have hK : 0 ≤ K := le_trans (by norm_num : (0:ℝ) ≤ 2) (le_max_right _ _)
  let w := wholeLp (u.val (zeroIndex d 1))
  let F := fun h : Domain d => (K * ‖u‖) * incrementCutoff h
  have hF : MemLp F p (differenceMeasure s p) :=
    (incrementCutoff_memLp (d := d) s p hs0 hs1 hp).const_mul (K * ‖u‖)
  have hbound : ∀ h, ‖lpIncrement p h w‖ ≤ ‖F h‖ := by
    intro h
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hK (norm_nonneg u)) (incrementCutoff_nonneg h))]
    exact whole_first_increment_cutoff_bound hp u h
  have hinc : MemLp (fun h => lpIncrement p h w) p (differenceMeasure s p) :=
    hF.of_le (lpIncrement_continuous p hp w).stronglyMeasurable.aestronglyMeasurable
      (Eventually.of_forall hbound)
  have hfin := (finite_energy_iff_memLp s p hp w).mpr hinc
  refine ⟨hfin, ?_⟩
  have hsemi : (eLpNorm (fun h => lpIncrement p h w) p (differenceMeasure s p)).toReal ≤
      (K * ‖u‖) * (eLpNorm (@incrementCutoff d) p (differenceMeasure s p)).toReal := by
    have hle : eLpNorm (fun h => lpIncrement p h w) p (differenceMeasure s p) ≤
        eLpNorm F p (differenceMeasure s p) :=
      eLpNorm_mono_ae (lpIncrement_continuous p hp w).stronglyMeasurable.aestronglyMeasurable
        (Eventually.of_forall hbound)
    have hle' := ENNReal.toReal_mono hF.ne hle
    have he : eLpNorm F p (differenceMeasure s p) =
        ‖K * ‖u‖‖ₑ * eLpNorm (@incrementCutoff d) p (differenceMeasure s p) :=
      eLpNorm_const_smul (K * ‖u‖) (@incrementCutoff d) p (differenceMeasure s p)
    rw [he, ENNReal.toReal_mul, toReal_enorm, Real.norm_of_nonneg (mul_nonneg hK (norm_nonneg u))] at hle'
    exact hle'
  have hw : ‖w‖ ≤ ‖u‖ := by
    change ‖wholeLpLI (u.val (zeroIndex d 1))‖ ≤ ‖u‖
    rw [wholeLpLI.norm_map]
    exact PiLp.norm_apply_le u.val _
  rw [fractionalNorm_eq_weightedLp s p hp]
  dsimp only
  unfold wholeFirstFractionalConstant
  dsimp only [w] at hw hsemi ⊢
  dsimp only [K] at hsemi
  nlinarith

lemma sobolev_norm_le_card_higher_fractional_norm {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : HigherFractionalSpace 𝕜 d s p) :
    ‖u.val‖ ≤ Fintype.card (DerivativeIndex d 1) * higherFractionalNorm s p u := by
  have hbase : ‖u.val.val (zeroIndex d 1)‖ ≤ higherFractionalNorm s p u := by
    have hn := Finset.sum_nonneg (s := Finset.univ) (fun i _ => fractionalNorm_nonneg (s-1) p
      (⟨wholeLp (u.val.val (firstIndex i)), u.property i⟩ : FractionalSpace 𝕜 d (s-1) p))
    have he : ‖wholeLp (u.val.val (zeroIndex d 1))‖ = ‖u.val.val (zeroIndex d 1)‖ :=
      wholeLpLI.norm_map _
    unfold higherFractionalNorm
    rw [he]
    linarith
  have hcomponent (α : DerivativeIndex d 1) :
      ‖u.val.val α‖ ≤ higherFractionalNorm s p u := by
    rcases multiIndex_order_one_cases (natIndex α) α.property with hz | ⟨j, hj⟩
    · have he : α = zeroIndex d 1 := derivativeIndex_ext hz
      simpa only [he] using hbase
    · have he : α = firstIndex j := derivativeIndex_ext (by simpa using hj)
      rw [he]
      calc
        _ = ‖wholeLp (u.val.val (firstIndex j))‖ := (wholeLpLI.norm_map _).symm
        _ ≤ fractionalNorm (s-1) p ⟨wholeLp (u.val.val (firstIndex j)), u.property j⟩ :=
          norm_le_fractionalNorm (s-1) p
            (⟨wholeLp (u.val.val (firstIndex j)), u.property j⟩ : FractionalSpace 𝕜 d (s-1) p)
        _ ≤ ∑ i : Fin d, fractionalNorm (s-1) p
            ⟨wholeLp (u.val.val (firstIndex i)), u.property i⟩ :=
          Finset.single_le_sum (fun i _ => fractionalNorm_nonneg (s-1) p
            (⟨wholeLp (u.val.val (firstIndex i)), u.property i⟩ : FractionalSpace 𝕜 d (s-1) p))
            (Finset.mem_univ j)
        _ ≤ higherFractionalNorm s p u := by
          unfold higherFractionalNorm
          exact le_add_of_nonneg_left (norm_nonneg _)
  rw [sobolev_norm_formula]
  unfold Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.NormValue
  calc
    _ ≤ ∑ _α : DerivativeIndex d 1, higherFractionalNorm s p u :=
      Finset.sum_le_sum (fun α _ => hcomponent α)
    _ = _ := by simp

lemma higher_base_fractional_norm_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (s t : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (ht0 : 0 < t) (ht1 : t < 1)
    (hp : p ≠ ∞) (u : HigherFractionalSpace 𝕜 d s p) :
    ∃ hfin : differenceEnergy t p (wholeLp (u.val.val (zeroIndex d 1))) < ∞,
      fractionalNorm t p ⟨wholeLp (u.val.val (zeroIndex d 1)), hfin⟩ ≤
        (wholeFirstFractionalConstant d t p * Fintype.card (DerivativeIndex d 1)) *
          higherFractionalNorm s p u := by
  obtain ⟨hfin, hbound⟩ := whole_first_fractional_norm_bound t p ht0 ht1 hp u.val
  refine ⟨hfin, hbound.trans ?_⟩
  calc
    _ ≤ wholeFirstFractionalConstant d t p *
        (Fintype.card (DerivativeIndex d 1) * higherFractionalNorm s p u) :=
      mul_le_mul_of_nonneg_left (sobolev_norm_le_card_higher_fractional_norm s p u)
        (wholeFirstFractionalConstant_nonneg d t p)
    _ = _ := by ring

end Analytic

/-- The weak product rule with a bounded C¹ coefficient does not require the
Sobolev factor to be bounded or the coefficient to belong to Lp. -/
lemma c1_coefficient_weak_product {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (a : Domain d → 𝕜) (ha : ContDiff ℝ 1 a) (C : ℝ)
    (hC : ∀ x, ‖a x‖ ≤ C)
    (hD : ∀ i x, ‖fderiv ℝ a x (coordinateVector i)‖ ≤ C)
    (u : DomainLp 𝕜 Ω p) (g : Fin d → DomainLp 𝕜 Ω p)
    (hu : HasWeakCoordinateDerivatives u g) :
    ∃ (w : DomainLp 𝕜 Ω p) (k : Fin d → DomainLp 𝕜 Ω p),
      HasWeakCoordinateDerivatives w k ∧
      w =ᵐ[volume.restrict (Ω : Set (Domain d))] (fun x => a x * u x) ∧
      (∀ i, k i =ᵐ[volume.restrict (Ω : Set (Domain d))]
        (fun x => a x * g i x + fderiv ℝ a x (coordinateVector i) * u x)) ∧
      ‖w‖ ≤ C * ‖u‖ ∧ ∀ i, ‖k i‖ ≤ C * (‖g i‖ + ‖u‖) := by
  have hd (i : Fin d) : Continuous (fun x => fderiv ℝ a x (coordinateVector i)) :=
    (ha.continuous_fderiv (by norm_num)).clm_apply continuous_const
  let w := boundedMulLp a ha.continuous C hC u
  let k := fun i => boundedMulLp a ha.continuous C hC (g i) +
    boundedMulLp (fun x => fderiv ℝ a x (coordinateVector i)) (hd i) C (hD i) u
  have hw : w =ᵐ[volume.restrict (Ω : Set (Domain d))] (fun x => a x * u x) :=
    boundedMulLp_coe _ _ _ _ _
  have hk (i) : k i =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => a x * g i x + fderiv ℝ a x (coordinateVector i) * u x) := by
    filter_upwards [Lp.coeFn_add (boundedMulLp a ha.continuous C hC (g i))
      (boundedMulLp (fun x => fderiv ℝ a x (coordinateVector i)) (hd i) C (hD i) u),
      boundedMulLp_coe a ha.continuous C hC (g i),
      boundedMulLp_coe (fun x => fderiv ℝ a x (coordinateVector i)) (hd i) C (hD i) u]
      with x he h₁ h₂
    exact he.trans (congrArg₂ (· + ·) h₁ h₂)
  refine ⟨w, k, ?_, hw, hk, boundedMulLp_norm_le _ _ _ _ _, ?_⟩
  · obtain ⟨f, huf, hf⟩ := weak_to_acl u g hu
    apply acl_to_weak w k (fun x => a x * f x)
    · filter_upwards [hw, huf] with x hwx hux
      rw [hwx, hux]
    intro i
    filter_upwards [hf i, ae_on_fibers i huf, ae_on_fibers i (hk i)] with y hfy huy hky
    refine ⟨?_, ?_⟩
    · intro b c hbc
      have hac : ContDiff ℝ 1 (fun t => a (coordinateLine i y t)) :=
        ha.comp ((coordinateLine_contDiff i y).of_le (by simp))
      exact hac.contDiffOn.absolutelyContinuousOnInterval.smul (hfy.1 b c hbc)
    · filter_upwards [hfy.2, huy, hky] with t hft hut hkt
      have had : HasDerivAt (fun s => a (coordinateLine i y s))
          (fderiv ℝ a (coordinateLine i y t) (coordinateVector i)) t :=
        (ha.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt t
          (coordinateLine_hasDerivAt i y t)
      convert! had.mul hft using 1
      rw [hkt, hut]
      ring
  · intro i
    exact (norm_add_le _ _).trans ((add_le_add
      (boundedMulLp_norm_le _ _ _ _ _) (boundedMulLp_norm_le _ _ _ _ _)).trans_eq
        (mul_add C ‖g i‖ ‖u‖).symm)

lemma compact_c1_coefficient_bounds {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Domain d → 𝕜) (ha : ContDiff ℝ 1 a) (hc : HasCompactSupport a) :
    ∃ M L : ℝ≥0, (∀ x, ‖a x‖ ≤ M) ∧
      ∀ x y, ‖a x - a y‖ ≤ L * euclideanLength (x - y) := by
  obtain ⟨M, hM⟩ := ha.continuous.bounded_above_of_compact_support hc
  obtain ⟨L, hL⟩ := (ha.continuous_fderiv (by norm_num)).bounded_above_of_compact_support (hc.fderiv ℝ)
  have hM0 : 0 ≤ M := (norm_nonneg (a 0)).trans (hM 0)
  have hL0 : 0 ≤ L := (norm_nonneg (fderiv ℝ a 0)).trans (hL 0)
  refine ⟨⟨M, hM0⟩, ⟨L, hL0⟩, hM, ?_⟩
  apply bounded_fderiv_euclideanLipschitz a ⟨L, hL0⟩ (ha.differentiable (by norm_num))
  intro x
  exact_mod_cast hL x

/-- Compact C² coefficients have uniform bounds and Lipschitz constants for
both the coefficient and all its first partials. No global chart bounds are
inferred from mere C² regularity on an open set. -/
lemma compact_c2_coefficient_bounds {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : Domain d → 𝕜) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a) :
    ∃ M L : ℝ≥0, (∀ x, ‖a x‖ ≤ M) ∧
      (∀ x y, ‖a x - a y‖ ≤ L * euclideanLength (x - y)) ∧
      (∀ i x, ‖fderiv ℝ a x (coordinateVector i)‖ ≤ M) ∧
      ∀ i x y, ‖fderiv ℝ a x (coordinateVector i) -
        fderiv ℝ a y (coordinateVector i)‖ ≤ L * euclideanLength (x - y) := by
  classical
  obtain ⟨M, L, hM, hL⟩ := compact_c1_coefficient_bounds a (ha.of_le (by norm_num)) hc
  have hpart (i : Fin d) : ContDiff ℝ 1 (fun x => fderiv ℝ a x (coordinateVector i)) := by
    exact (ha.fderiv_right (by norm_num)).clm_apply contDiff_const
  choose N P hN hP using fun i : Fin d =>
    compact_c1_coefficient_bounds _ (hpart i) (hc.fderiv_apply ℝ (coordinateVector i))
  refine ⟨M + ∑ i, N i, L + ∑ i, P i, ?_, ?_, ?_, ?_⟩
  · intro x
    exact (hM x).trans (by exact_mod_cast le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (N i).coe_nonneg))
  · intro x y
    apply (hL x y).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg (WithLp.toLp 2 (x-y)))
    exact_mod_cast le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => (P i).coe_nonneg)
  · intro i x
    apply (hN i x).trans
    have hi : N i ≤ ∑ k, N k := Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
    exact_mod_cast hi.trans (le_add_of_nonneg_left (show (0 : ℝ≥0) ≤ M from bot_le))
  · intro i x y
    apply (hP i x y).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg (WithLp.toLp 2 (x-y)))
    have hi : P i ≤ ∑ k, P k := Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)
    exact_mod_cast hi.trans (le_add_of_nonneg_left (show (0 : ℝ≥0) ≤ L from bot_le))

lemma higher_coefficient_multiplier {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (σ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hσ0 : 1 < σ) (hσ1 : σ < 2) (hp : p ≠ ∞)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ 1 a) (M L : ℝ≥0)
    (hM : ∀ x, ‖a x‖ ≤ M)
    (hL : ∀ x y, ‖a x - a y‖ ≤ L * euclideanLength (x-y))
    (hDM : ∀ i x, ‖fderiv ℝ a x (coordinateVector i)‖ ≤ M)
    (hDL : ∀ i x y, ‖fderiv ℝ a x (coordinateVector i) -
      fderiv ℝ a y (coordinateVector i)‖ ≤ L * euclideanLength (x-y)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : HigherFractionalSpace 𝕜 d σ p)
      (u0 : FractionalSpace 𝕜 d (σ-1) p),
      u0.val = wholeLp (u.val.val (zeroIndex d 1)) →
      ∃ v : HigherFractionalSpace 𝕜 d σ p,
        wholeLp (v.val.val (zeroIndex d 1)) =ᵐ[volume]
          (fun x => a x * wholeLp (u.val.val (zeroIndex d 1)) x) ∧
        higherFractionalNorm σ p v ≤ C *
          (higherFractionalNorm σ p u + fractionalNorm (σ-1) p u0) := by
  classical
  let : Fact (p ≠ ∞) := ⟨hp⟩
  let s := σ-1
  have hs0 : 0 < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  let K := multiplierBound (d:=d) s p M L
  have hK : 0 ≤ K := multiplierBound_nonneg s p M L
  let C := (M:ℝ) + K + d*K
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u u0 hu0
  let f := u.val.val (zeroIndex d 1)
  let g := fun i => u.val.val (firstIndex i)
  have hu : HasWeakCoordinateDerivatives f g := fun i => first_derivative_formula u.val i
  obtain ⟨w, k, hwk, hw, hk, hwnorm, hknorm⟩ :=
    c1_coefficient_weak_product a ha M hM hDM f g hu
  have hw' : w =ᵐ[volume] (fun x => a x * f x) := by simpa using hw
  have hk' (i) : k i =ᵐ[volume] (fun x => a x * g i x +
      fderiv ℝ a x (coordinateVector i) * f x) := by simpa using hk i
  let uD : Fin d → FractionalSpace 𝕜 d s p :=
    fun i => ⟨wholeLp (g i), u.property i⟩
  let A := fun i => fractionalMultiply s p hs0 hs1 hp a M L hM hL (uD i)
  let B := fun i => fractionalMultiply s p hs0 hs1 hp
    (fun x => fderiv ℝ a x (coordinateVector i)) M L (hDM i) (hDL i) u0
  let z := fun i => A i + B i
  have hu0rep : u0.val =ᵐ[volume] f := by
    rw [hu0]
    exact wholeLp_representative f
  have hzi (i : Fin d) : wholeLp (k i) = (z i).val := by
    apply Lp.ext
    have hA := fractionalMultiply_representative s p hs0 hs1 hp a M L hM hL (uD i)
    have hB := fractionalMultiply_representative s p hs0 hs1 hp
      (fun x => fderiv ℝ a x (coordinateVector i)) M L (hDM i) (hDL i) u0
    filter_upwards [wholeLp_representative (k i), hk' i, hA, hB,
      Lp.coeFn_add (A i).val (B i).val, wholeLp_representative (g i), hu0rep]
      with x hx hki hAi hBi hadd hgi hfi
    change _ = ((A i).val + (B i).val) x
    rw [hx, hki, hadd]
    change _ = (A i).val x + (B i).val x
    rw [hAi, hBi]
    change _ = a x * wholeLp (g i) x + _
    rw [hgi, hfi]
  have hkenergy (i : Fin d) : differenceEnergy (σ-1) p (wholeLp (k i)) < ∞ := by
    rw [hzi i]
    exact (z i).property
  obtain ⟨v, hv⟩ := (higher_fractional_membership 𝕜 d σ p w).mpr ⟨k, hwk, hkenergy⟩
  have hvk (i : Fin d) : v.val.val (firstIndex i) = k i := by
    apply lpDistribution_injective
    rw [first_derivative_formula v.val i, hv]
    exact (hwk i).symm
  have hvzi (i : Fin d) :
      (⟨wholeLp (v.val.val (firstIndex i)), v.property i⟩ : FractionalSpace 𝕜 d s p) = z i := by
    apply Subtype.ext
    change wholeLp (v.val.val (firstIndex i)) = (z i).val
    rw [hvk i, hzi i]
  have hvnorm : higherFractionalNorm σ p v = ‖w‖ + ∑ i, fractionalNorm s p (z i) := by
    unfold higherFractionalNorm
    rw [hv, norm_wholeLp]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => congrArg (fractionalNorm s p) (hvzi i))
  have hzinorm (i : Fin d) : fractionalNorm s p (z i) ≤
      K * fractionalNorm s p (uD i) + K * fractionalNorm s p u0 := by
    apply (fractionalNorm_add_le s p hp (A i) (B i)).trans
    exact add_le_add (fractionalMultiply_norm_le s p hs0 hs1 hp a M L hM hL (uD i))
      (fractionalMultiply_norm_le s p hs0 hs1 hp
        (fun x => fderiv ℝ a x (coordinateVector i)) M L (hDM i) (hDL i) u0)
  have hzsum : (∑ i, fractionalNorm s p (z i)) ≤
      K * (∑ i, fractionalNorm s p (uD i)) + d*K*fractionalNorm s p u0 := by
    calc
      _ ≤ ∑ i, (K * fractionalNorm s p (uD i) + K * fractionalNorm s p u0) :=
        Finset.sum_le_sum (fun i _ => hzinorm i)
      _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  have hunorm : higherFractionalNorm σ p u =
      ‖f‖ + ∑ i, fractionalNorm s p (uD i) := by
    simp only [higherFractionalNorm, norm_wholeLp]
    rfl
  refine ⟨v, ?_, ?_⟩
  · rw [hv]
    filter_upwards [wholeLp_representative w, hw', wholeLp_representative f]
      with x hx hwx hfx
    rw [hx, hwx, hfx]
  · rw [hvnorm, hunorm]
    have hS : 0 ≤ ∑ i, fractionalNorm s p (uD i) :=
      Finset.sum_nonneg (fun i _ => fractionalNorm_nonneg _ _ _)
    have hF : 0 ≤ fractionalNorm s p u0 := fractionalNorm_nonneg _ _ _
    have hU : 0 ≤ ‖f‖ := norm_nonneg _
    have hM0 : 0 ≤ (M:ℝ) := M.coe_nonneg
    have hd0 : 0 ≤ (d:ℝ) := Nat.cast_nonneg d
    have hCU : (M:ℝ)*‖f‖ + K*(∑ i, fractionalNorm s p (uD i)) ≤
        ((M:ℝ)+K)*(‖f‖+∑ i, fractionalNorm s p (uD i)) := by
      nlinarith [mul_nonneg hM0 hS, mul_nonneg hK hU]
    have hCF : ((M:ℝ)+K)*(‖f‖+∑ i, fractionalNorm s p (uD i)) +
        d*K*fractionalNorm s p u0 ≤ C*(‖f‖+∑ i, fractionalNorm s p (uD i)+fractionalNorm s p u0) := by
      dsimp [C]
      nlinarith [mul_nonneg (mul_nonneg hd0 hK) (add_nonneg hU hS),
        mul_nonneg (add_nonneg hM0 hK) hF]
    exact (add_le_add hwnorm hzsum).trans (by linarith)


lemma compact_c2_higher_multiplier {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (σ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hσ0 : 1 < σ) (hσ1 : σ < 2) (hp : p ≠ ∞)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ 2 a) (hc : HasCompactSupport a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : HigherFractionalSpace 𝕜 d σ p,
      ∃ v : HigherFractionalSpace 𝕜 d σ p,
        wholeLp (v.val.val (zeroIndex d 1)) =ᵐ[volume]
          (fun x => a x * wholeLp (u.val.val (zeroIndex d 1)) x) ∧
        higherFractionalNorm σ p v ≤ C * higherFractionalNorm σ p u := by
  obtain ⟨M, L, hM, hL, hDM, hDL⟩ := compact_c2_coefficient_bounds a ha hc
  obtain ⟨C, hC, hmult⟩ := higher_coefficient_multiplier σ p hσ0 hσ1 hp
    a (ha.of_le (by norm_num)) M L hM hL hDM hDL
  let Q := Analytic.wholeFirstFractionalConstant d (σ-1) p *
    Fintype.card (DerivativeIndex d 1)
  have hQ : 0 ≤ Q := mul_nonneg
    (Analytic.wholeFirstFractionalConstant_nonneg d (σ-1) p) (Nat.cast_nonneg _)
  refine ⟨C * (1+Q), mul_nonneg hC (by positivity), ?_⟩
  intro u
  obtain ⟨hfin, hbound⟩ := Analytic.higher_base_fractional_norm_bound σ (σ-1) p
    (by linarith) (by linarith) hp u
  let u0 : FractionalSpace 𝕜 d (σ-1) p :=
    ⟨wholeLp (u.val.val (zeroIndex d 1)), hfin⟩
  obtain ⟨v, hv, hnorm⟩ := hmult u u0 rfl
  refine ⟨v, hv, hnorm.trans ?_⟩
  calc
    _ ≤ C * (higherFractionalNorm σ p u + Q * higherFractionalNorm σ p u) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hbound) hC
    _ = _ := by ring


/-- A C² coefficient on an open neighborhood of a compact set has a compactly
supported global C² extension which agrees on a neighborhood of that set. -/
lemma exists_compact_c2_extension {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (U : Set (Domain n)) (hU : IsOpen U)
    (K : Set (Domain n)) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Domain n → 𝕜) (ha : ContDiffOn ℝ 2 a U) :
    ∃ b : Domain n → 𝕜, ContDiff ℝ 2 b ∧ HasCompactSupport b ∧
      tsupport b ⊆ U ∧ ∃ V : Set (Domain n), IsOpen V ∧ K ⊆ V ∧ EqOn b a V := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨χ, hχU, hχone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (closure V) hVc ⟨U, hU⟩ hVU
  let b : Domain n → 𝕜 := fun x => χ x * a x
  have hb : ContDiff ℝ 2 b := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact ((χ.contDiff.of_le (by norm_num)).contDiffAt).mul
        ((ha x hx).contDiffAt (hU.mem_nhds hx))
    · have hxχ : x ∉ tsupport χ := fun h => hx (hχU h)
      have hzero : b =ᶠ[𝓝 x] fun _ => (0 : 𝕜) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
        simp only [b, hy, Pi.zero_apply, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  refine ⟨b, hb, χ.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans hχU,
    V, hV, hKV, ?_⟩
  intro x hx
  dsimp only [b]
  rw [hχone x (subset_closure hx), one_mul]


namespace C2BoundaryModel
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.Sobolev.C1Extension ExpandedFA.PartIV.FractionalSobolev

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n+1))}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B D : C2BoundaryModel 𝕜 Ω p)

lemma ambient_normal_zero (j : Fin B.chartCount)
    (x : frontier (Ω : Set (Domain (n+1)))) (hx : x ∈ (B.atlas.chart j).source) :
    B.ambient j x.val (B.normal j) = 0 := by
  apply (chart_boundary_iff Ω (B.ambient j) (B.normal j) (B.side j) x.val _).mp x.property
  simpa only [B.chart_source j, mem_preimage] using hx

lemma insert_chart (j : Fin B.chartCount)
    (x : frontier (Ω : Set (Domain (n+1)))) (hx : x ∈ (B.atlas.chart j).source) :
    (B.normal j).insertNth 0 (B.atlas.chart j x) = B.ambient j x.val := by
  rw [B.chart_apply j x hx]
  change (B.normal j).insertNth 0 ((B.normal j).removeNth (B.ambient j x.val)) = _
  rw [← B.ambient_normal_zero j x hx, Fin.insertNth_self_removeNth]

lemma chart_symm_val (j : Fin B.chartCount)
    (z : Domain n) (hz : z ∈ (B.atlas.chart j).target) :
    ((B.atlas.chart j).symm z).val =
      (B.ambient j).symm ((B.normal j).insertNth 0 z) := by
  have hx := (B.atlas.chart j).map_target hz
  have hxa : ((B.atlas.chart j).symm z).val ∈ (B.ambient j).source := by
    simpa only [B.chart_source j, mem_preimage] using hx
  have heq := B.insert_chart j ((B.atlas.chart j).symm z) hx
  rw [(B.atlas.chart j).right_inv hz] at heq
  rw [heq, (B.ambient j).left_inv hxa]

lemma insert_chart_mem (j : Fin B.chartCount)
    (z : Domain n) (hz : z ∈ (B.atlas.chart j).target) :
    (B.normal j).insertNth 0 z ∈ (B.ambient j).target := by
  have hx := (B.atlas.chart j).map_target hz
  have hxa : ((B.atlas.chart j).symm z).val ∈ (B.ambient j).source := by
    simpa only [B.chart_source j, mem_preimage] using hx
  have heq := B.insert_chart j ((B.atlas.chart j).symm z) hx
  rw [(B.atlas.chart j).right_inv hz] at heq
  rw [heq]
  exact (B.ambient j).map_source hxa

lemma contDiff_insertNth_zero (i : Fin (n+1)) :
    ContDiff ℝ 2 (fun z : Domain n => i.insertNth (α := fun _ => ℝ) 0 z) := by
  apply contDiff_pi.mpr
  intro k
  by_cases hk : k = i
  · subst k
    simpa using (contDiff_const : ContDiff ℝ 2 (fun _ : Domain n => (0:ℝ)))
  · obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hk
    rw [← hl]
    simpa using (contDiff_apply ℝ (fun _ : Fin n => ℝ) l : ContDiff ℝ 2 (fun z : Domain n => z l))

lemma contDiff_removeNth (i : Fin (n+1)) :
    ContDiff ℝ 2 (fun z : Domain (n+1) => i.removeNth z) := by
  apply contDiff_pi.mpr
  intro k
  exact contDiff_apply ℝ (fun _ : Fin (n+1) => ℝ) (i.succAbove k)

lemma chart_symm_contDiff (j : Fin B.chartCount) :
    ContDiffOn ℝ 2 (fun z => ((B.atlas.chart j).symm z).val) (B.atlas.chart j).target := by
  apply ContDiffOn.congr _ (fun z hz => B.chart_symm_val j z hz)
  exact (B.regular j).2.comp (contDiff_insertNth_zero (B.normal j)).contDiffOn
    (fun z hz => B.insert_chart_mem j z hz)

lemma overlap_contDiff (i : Fin D.chartCount) (j : Fin B.chartCount) :
    ContDiffOn ℝ 2 (D.atlas.overlapChart B.atlas i j) (D.atlas.overlapChart B.atlas i j).source := by
  have hDS : (D.atlas.overlapChart B.atlas i j).source ⊆ (D.atlas.chart i).target :=
    fun _ hx => hx.1
  have hBA : MapsTo (fun z => ((D.atlas.chart i).symm z).val)
      (D.atlas.overlapChart B.atlas i j).source (B.ambient j).source := by
    intro z hz
    simpa only [B.chart_source j, mem_preimage, OpenPartialHomeomorph.symm_symm] using hz.2
  have hcomp := (contDiff_removeNth (B.normal j)).contDiffOn.comp
    ((B.regular j).1.comp ((D.chart_symm_contDiff i).mono hDS) hBA)
    (fun _ _ => Set.mem_univ _)
  apply hcomp.congr
  intro z hz
  exact B.chart_apply j ((D.atlas.chart i).symm z) hz.2

lemma cutoff_coordinate_contDiff (i : Fin D.chartCount) (j : Fin B.chartCount) :
    ContDiffOn ℝ 2 (fun z => D.atlas.cutoff i ((B.atlas.chart j).symm z))
      (B.atlas.chart j).target := by
  have htest : ContDiff ℝ 2 (D.test i) := (D.test i).contDiff.of_le (by norm_num)
  have hcomp := htest.contDiffOn.comp (B.chart_symm_contDiff j)
    (fun _ _ => Set.mem_univ _)
  apply hcomp.congr
  intro z _
  exact D.cutoff_eq i ((B.atlas.chart j).symm z)

end C2BoundaryModel

namespace C2BoundaryModel
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B D : C2BoundaryModel 𝕜 Ω p)

lemma overlap_regular (i : Fin D.chartCount) (j : Fin B.chartCount) :
    ContDiffOn ℝ 2 (D.atlas.overlapChart B.atlas i j)
      (D.atlas.overlapChart B.atlas i j).source ∧
    ContDiffOn ℝ 2 (D.atlas.overlapChart B.atlas i j).symm
      (D.atlas.overlapChart B.atlas i j).target := by
  cases d with
  | zero => exact Fin.elim0 (D.normal i)
  | succ n =>
    exact ⟨B.overlap_contDiff D i j, D.overlap_contDiff B j i⟩

end C2BoundaryModel

/-- A coefficient of any finite or smooth order near a compact set admits a
compactly supported global extension agreeing on a neighborhood of that set. -/
lemma exists_compact_contDiff_extension {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (m : ℕ∞) (U : Set (Domain n)) (hU : IsOpen U)
    (K : Set (Domain n)) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Domain n → 𝕜) (ha : ContDiffOn ℝ m a U) :
    ∃ b : Domain n → 𝕜, ContDiff ℝ m b ∧ HasCompactSupport b ∧
      tsupport b ⊆ U ∧ ∃ V : Set (Domain n), IsOpen V ∧ K ⊆ V ∧ EqOn b a V := by
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨χ, hχU, hχone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (closure V) hVc ⟨U, hU⟩ hVU
  let b : Domain n → 𝕜 := fun x => χ x * a x
  have hb : ContDiff ℝ m b := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact ((χ.contDiff.of_le (by simp)).contDiffAt).mul
        ((ha x hx).contDiffAt (hU.mem_nhds hx))
    · have hxχ : x ∉ tsupport χ := fun h => hx (hχU h)
      have hzero : b =ᶠ[𝓝 x] fun _ => (0 : 𝕜) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
        simp only [b, hy, Pi.zero_apply, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  refine ⟨b, hb, χ.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans hχU,
    V, hV, hKV, ?_⟩
  intro x hx
  dsimp only [b]
  rw [hχone x (subset_closure hx), one_mul]

/-- Extending by zero introduces no edge derivative when the local nonzero
set lies in a fixed compact subset of the open coordinate domain. -/
lemma compact_zero_extension_contDiff {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (m : ℕ∞) (U : Set (Domain n)) (hU : IsOpen U)
    (K : Set (Domain n)) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Domain n → 𝕜) (ha : ContDiffOn ℝ m a U)
    (hsupp : ∀ x ∈ U, a x ≠ 0 → x ∈ K) :
    ContDiff ℝ m (U.indicator a) ∧ HasCompactSupport (U.indicator a) ∧
      tsupport (U.indicator a) ⊆ K ∧ EqOn (U.indicator a) a U := by
  classical
  let b := U.indicator a
  have hs : Function.support b ⊆ K := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact hsupp x hxU (by simpa only [Function.mem_support, b, indicator_of_mem hxU] using hx)
    · simp only [b, indicator_of_notMem hxU, Function.mem_support, ne_eq, not_true_eq_false] at hx
  have hts : tsupport b ⊆ K := closure_minimal hs hK.isClosed
  refine ⟨?_, hK.of_isClosed_subset (isClosed_tsupport b) hts, hts, ?_⟩
  · apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · apply ((ha x hx).contDiffAt (hU.mem_nhds hx)).congr_of_eventuallyEq
      filter_upwards [hU.mem_nhds hx] with y hy
      exact indicator_of_mem hy a
    · have hxK : x ∉ K := fun h => hx (hKU h)
      have hzero : b =ᶠ[𝓝 x] fun _ => (0 : 𝕜) := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hxK] with y hy
        exact not_not.mp (fun hn => hy (hs hn))
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  · intro x hx
    exact indicator_of_mem hx a

/-- Transport a global compact coefficient into the inverse coordinates and
extend by zero; its support remains compact inside the chart target. -/
lemma compact_chart_coefficient_contDiff {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (m : ℕ∞) (e : OpenPartialHomeomorph (Domain n) (Domain n))
    (he : ContDiffOn ℝ m e.symm e.target)
    (a : Domain n → 𝕜) (ha : ContDiff ℝ m a)
    (haK : HasCompactSupport a) (haS : tsupport a ⊆ e.source) :
    ContDiff ℝ m (e.target.indicator (a ∘ e.symm)) ∧
      HasCompactSupport (e.target.indicator (a ∘ e.symm)) ∧
      tsupport (e.target.indicator (a ∘ e.symm)) ⊆ e '' tsupport a ∧
      EqOn (e.target.indicator (a ∘ e.symm)) (a ∘ e.symm) e.target := by
  have hK : IsCompact (e '' tsupport a) :=
    haK.isCompact.image_of_continuousOn (e.continuousOn.mono haS)
  have hKU : e '' tsupport a ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (haS hx)
  apply compact_zero_extension_contDiff m e.target e.open_target (e '' tsupport a) hK hKU
    (a ∘ e.symm) (ha.contDiffOn.comp he (fun _ _ => Set.mem_univ _))
  intro y hy hay
  exact ⟨e.symm y, subset_tsupport a hay, e.right_inv hy⟩

/-- An inverse-Lipschitz local coordinate map preserves ambient almost-
everywhere agreement when restricted to its actual source. -/
lemma ae_comp_of_chart_ae {α : Type*} {n : ℕ}
    (e : OpenPartialHomeomorph (Domain n) (Domain n)) {L : ℝ≥0}
    (he : LipschitzOnWith L e.symm e.target) {f g : Domain n → α}
    (hfg : f =ᵐ[volume] g) :
    (f ∘ e) =ᵐ[volume.restrict e.source] (g ∘ e) := by
  have hmap := ExpandedFA.PartIV.FractionalSobolev.Transport.map_restrict_volume_le
    e.open_source.measurableSet e.open_target.measurableSet e.continuousOn he
    (fun x hx => ⟨e.map_source hx, e.left_inv hx⟩)
    (fun y hy => ⟨e.map_target hy, e.right_inv hy⟩)
  have hac : (volume.restrict e.source).map e ≪ volume :=
    (Measure.absolutelyContinuous_of_le_smul hmap).trans
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  exact ae_of_ae_map (e.continuousOn.aemeasurable e.open_source.measurableSet) (hac.ae_eq hfg)


namespace Analytic
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.Sobolev.C1Extension ExpandedFA.Sobolev.C1Extension.Transport
open ExpandedFA.PartIV.FractionalSobolev
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The accepted C¹ chart-chain proof already works at finite p without a
bounded-target hypothesis; this wrapper exposes exactly that fact. -/
def finiteChartSobolevPull {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (e : OpenPartialHomeomorph (Domain d) (Domain d))
    (he : ContDiffOn ℝ 1 e e.source) (he' : ContDiffOn ℝ 1 e.symm e.target)
    (B : ℝ) (hB : ∀ x ∈ e.source, ‖fderiv ℝ e x‖ ≤ B) (hB0 : 0 ≤ B)
    (J : ℝ) (hJ : ∀ y ∈ e.target, |(fderiv ℝ e.symm y).det| ≤ J) (hJ1 : 1 ≤ J)
    (Ω : Opens (Domain d)) :
    SobolevSpace 𝕜 d (chartTarget e Ω) 1 p →L[𝕜]
      SobolevSpace 𝕜 d (chartPreimage e Ω) 1 p :=
  (chartChainJetCLM e he he' B hB J hJ Ω hB0 hJ1).restrict
    (fun u hu => chartChainJet_mem_finite_of_continuous e he he' B hB hB0 J hJ hJ1 Ω hp
      (chartChainJetCLM e he he' B hB J hJ Ω hB0 hJ1).continuous ⟨u, hu⟩)

lemma localizedZeroExtension_coordinate_representative
    {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Ω : Opens (Domain d)) (η : Tests 𝕜 (⊤ : Opens (Domain d)))
    (hη : tsupport η ⊆ Ω)
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, ‖η x‖ ≤ C)
    (hD : ∀ j x, ‖partialFunction [j] η x‖ ≤ C)
    (u : SobolevSpace 𝕜 d Ω 1 p) (f : Domain d → 𝕜)
    (g : Fin d → Domain d → 𝕜)
    (hf : u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f)
    (hg : ∀ i, u.val (coordinateIndex i) =ᵐ[volume.restrict (Ω : Set (Domain d))] g i)
    (i : Fin d) :
    wholeLp ((localizedZeroExtension (le_top : Ω ≤ ⊤) (tsupport η)
        (by simpa using η.hasCompactSupport.isClosed) hη η η.contDiff C hC0 hC hD
        inter_subset_right u).val (coordinateIndex i)) =ᵐ[volume]
      (Ω : Set (Domain d)).indicator
        (fun x => η x * g i x + partialFunction [i] η x * f x) := by
  let a := ambientMultiply η η.contDiff C hC0 hC hD u
  have ha : a.val (coordinateIndex i) =ᵐ[volume.restrict (Ω : Set (Domain d))]
      (fun x => η x * g i x + partialFunction [i] η x * f x) := by
    change ambientMultiplyJet η η.contDiff C hC hD u.val (coordinateIndex i) =ᵐ[_] _
    rw [ambientMultiplyJet_coordinate]
    filter_upwards [Lp.coeFn_add
      (boundedMulLp η η.contDiff.continuous C hC (u.val (coordinateIndex i)))
      (boundedMulLp (partialFunction [i] η) (Smoothing.partialFunction_contDiff _ η η.contDiff).continuous C
        (hD i) (u.val (zeroIndex d 1))),
      boundedMulLp_coe η η.contDiff.continuous C hC (u.val (coordinateIndex i)),
      boundedMulLp_coe (partialFunction [i] η)
        (Smoothing.partialFunction_contDiff _ η η.contDiff).continuous C (hD i) (u.val (zeroIndex d 1)),
      hf, hg i] with x hx h₁ h₂ hfx hgx
    rw [hx]
    simp only [Pi.add_apply]
    rw [h₁, h₂, hfx, hgx]
  have ha' := (ae_eq_restrict_iff_indicator_ae_eq Ω.isOpen.measurableSet).mp ha
  have hz := zeroLp_coe (Λ := (⊤ : Opens (Domain d))) (a.val (coordinateIndex i))
  simp only [Opens.coe_top, Measure.restrict_univ] at hz
  apply (wholeLp_representative _).trans
  change zeroLp ⊤ (a.val (coordinateIndex i)) =ᵐ[volume] _
  exact hz.trans ha'

lemma localized_c1_whole_pullback
    {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (e : OpenPartialHomeomorph (Domain d) (Domain d))
    (he : ContDiffOn ℝ 1 e e.source) (he' : ContDiffOn ℝ 1 e.symm e.target)
    (K K' : ℝ≥0) (hK : LipschitzOnWith K e e.source)
    (hK' : LipschitzOnWith K' e.symm e.target)
    (η : Tests 𝕜 (⊤ : Opens (Domain d))) (hη : tsupport η ⊆ e.source) :
    ∃ T : SobolevSpace 𝕜 d ⊤ 1 p →L[𝕜] SobolevSpace 𝕜 d ⊤ 1 p,
      (∀ u, wholeLp ((T u).val (zeroIndex d 1)) =ᵐ[volume]
        e.source.indicator (fun x => η x * wholeLp (u.val (zeroIndex d 1)) (e x))) ∧
      (∀ u i, wholeLp ((T u).val (coordinateIndex i)) =ᵐ[volume]
        e.source.indicator (fun x =>
          η x * ∑ k : Fin d, (chartCoefficient e i k x : 𝕜) *
            wholeLp (u.val (coordinateIndex k)) (e x) +
          partialFunction [i] η x * wholeLp (u.val (zeroIndex d 1)) (e x))) := by
  have hB : ∀ x ∈ e.source, ‖fderiv ℝ e x‖ ≤ (K : ℝ) :=
    fun x hx => norm_fderiv_le_of_lipschitzOn ℝ (e.open_source.mem_nhds hx) hK
  have hBi : ∀ y ∈ e.target, ‖fderiv ℝ e.symm y‖ ≤ (K' : ℝ) :=
    fun y hy => norm_fderiv_le_of_lipschitzOn ℝ (e.open_target.mem_nhds hy) hK'
  obtain ⟨J, hJ1, hJ⟩ := exists_det_bound_of_norm_bound (E := Domain d) (K' : ℝ)
  have hdet : ∀ y ∈ e.target, |(fderiv ℝ e.symm y).det| ≤ J :=
    fun y hy => hJ _ (hBi y hy)
  let U := chartPreimage e (⊤ : Opens (Domain d))
  let V := chartTarget e (⊤ : Opens (Domain d))
  have hU : (U : Set (Domain d)) = e.source := by ext x; simp [U]
  have hV : (V : Set (Domain d)) = e.target := by ext x; simp [V]
  let R : SobolevSpace 𝕜 d ⊤ 1 p →L[𝕜] SobolevSpace 𝕜 d V 1 p := restrictSobolev le_top
  let P : SobolevSpace 𝕜 d V 1 p →L[𝕜] SobolevSpace 𝕜 d U 1 p :=
    finiteChartSobolevPull hp e he he' K hB K.coe_nonneg J hdet hJ1 ⊤
  obtain ⟨C, hC0, hC, hD⟩ := ambient_test_bounds η
  have hηU : tsupport η ⊆ U := by simpa only [hU] using hη
  let L : SobolevSpace 𝕜 d U 1 p →L[𝕜] SobolevSpace 𝕜 d ⊤ 1 p :=
    localizedZeroExtension le_top (tsupport η) (by simpa using η.hasCompactSupport.isClosed)
      hηU η η.contDiff C hC0 hC hD inter_subset_right
  let T := L.comp (P.comp R)
  have hR (u : SobolevSpace 𝕜 d ⊤ 1 p) (α : DerivativeIndex d 1) :
      (R u).val α =ᵐ[volume.restrict (V : Set (Domain d))] wholeLp (u.val α) :=
    (restrictSobolev_coe le_top u α).trans
      (ae_restrict_of_ae (wholeLp_representative (u.val α)).symm)
  have hP0 (u : SobolevSpace 𝕜 d ⊤ 1 p) :
      (P (R u)).val (zeroIndex d 1) =ᵐ[volume.restrict (U : Set (Domain d))]
        fun x => wholeLp (u.val (zeroIndex d 1)) (e x) := by
    change chartChainJet e he he' K hB J hdet ⊤ (R u).val (zeroIndex d 1) =ᵐ[_] _
    rw [chartChainJet_zero]
    exact pullLp_coe_of_ae_eq (chart_aemeasurable e ⊤) ENNReal.ofReal_ne_top
      (chart_map_measure_le e he' J hdet ⊤) _ _ (hR u _).symm
  have hPi (u : SobolevSpace 𝕜 d ⊤ 1 p) (i : Fin d) :
      (P (R u)).val (coordinateIndex i) =ᵐ[volume.restrict (U : Set (Domain d))]
        fun x => ∑ k : Fin d, (chartCoefficient e i k x : 𝕜) *
          wholeLp (u.val (coordinateIndex k)) (e x) := by
    have h := chartChainJet_coordinate_coe e he he' K hB J hdet ⊤ (R u).val i
    have hcomp (k : Fin d) :
        (fun x => (R u).val (coordinateIndex k) (e x)) =ᵐ[volume.restrict (U : Set (Domain d))]
        (fun x => wholeLp (u.val (coordinateIndex k)) (e x)) := by
      have h₁ := chartLpPull_coe e he' J hdet ⊤ ((R u).val (coordinateIndex k))
      have h₂ := pullLp_coe_of_ae_eq (chart_aemeasurable e ⊤) ENNReal.ofReal_ne_top
        (chart_map_measure_le e he' J hdet ⊤) ((R u).val (coordinateIndex k)) _ (hR u _).symm
      exact h₁.symm.trans h₂
    apply h.trans
    filter_upwards [ae_all_iff.mpr hcomp] with x hx
    exact Finset.sum_congr rfl (fun k _ => by rw [RCLike.real_smul_eq_coe_mul, hx k])
  refine ⟨T, ?_, ?_⟩
  · intro u
    apply (wholeLp_representative _).trans
    have h := localizedZeroExtension_representative (le_top : U ≤ ⊤) (tsupport η)
      (by simpa using η.hasCompactSupport.isClosed) hηU η η.contDiff C hC0 hC hD
      inter_subset_right (P (R u)) _ (hP0 u).symm
    simpa only [T, L, ContinuousLinearMap.comp_apply, Opens.coe_top, Measure.restrict_univ,
      localizedRaw, LinearMap.coe_mk, AddHom.coe_mk, hU] using h
  · intro u i
    simpa only [T, L, ContinuousLinearMap.comp_apply, hU] using localizedZeroExtension_coordinate_representative U η hηU C hC0 hC hD
      (P (R u)) _ _ (hP0 u) (hPi u) i

lemma localized_pullback_representation_of_support
    {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (e : OpenPartialHomeomorph (Domain d) (Domain d)) (S : Set (Domain d))
    (hSe : S ⊆ e.source) (η f F : Domain d → 𝕜)
    (hηone : ∀ x ∈ S, η x = 1)
    (hFS : Function.support F ⊆ S)
    (heq : F =ᵐ[volume.restrict e.source] f ∘ e) :
    e.source.indicator (fun x => η x * f (e x)) =ᵐ[volume] F := by
  have hlocal := (ae_eq_restrict_iff_indicator_ae_eq e.open_source.measurableSet).mp heq
  filter_upwards [hlocal] with x hx
  by_cases hxS : x ∈ e.source
  · simp only [indicator_of_mem hxS, Function.comp_apply] at hx ⊢
    by_cases hFx : F x = 0
    · rw [← hx, hFx, mul_zero]
    · rw [hηone x (hFS hFx), one_mul, ← hx]
  · have hFx : F x = 0 := by
      by_contra hF
      exact hxS (hSe (hFS hF))
    simp only [indicator_of_notMem hxS, hFx]

/-- Compactly supported local pullback data are genuine global W¹,p data.
The bound is uniform in the graph and in its measurable representative. -/
lemma compact_c1_weak_pullback
    {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (e : OpenPartialHomeomorph (Domain d) (Domain d))
    (he : ContDiffOn ℝ 1 e e.source) (he' : ContDiffOn ℝ 1 e.symm e.target)
    (K K' : ℝ≥0) (hK : LipschitzOnWith K e e.source)
    (hK' : LipschitzOnWith K' e.symm e.target)
    (S : Set (Domain d)) (hS : IsCompact S) (hSe : S ⊆ e.source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : SobolevSpace 𝕜 d ⊤ 1 p) (F : Domain d → 𝕜),
      Function.support F ⊆ S →
      F =ᵐ[volume.restrict e.source] (wholeLp (u.val (zeroIndex d 1))) ∘ e →
      ∃ v : SobolevSpace 𝕜 d ⊤ 1 p,
        wholeLp (v.val (zeroIndex d 1)) =ᵐ[volume] F ∧ ‖v‖ ≤ C * ‖u‖ := by
  obtain ⟨η, hη, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜) S hS
    ⟨e.source, e.open_source⟩ hSe
  obtain ⟨T, hT, _⟩ := localized_c1_whole_pullback hp e he he' K K' hK hK' η hη
  refine ⟨max ‖T‖ 0, le_max_right _ _, ?_⟩
  intro u F hFS hF
  refine ⟨T u, (hT u).trans ?_, (T.le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg u))⟩
  exact localized_pullback_representation_of_support e S hSe η _ F hηone hFS hF

lemma firstIndex_eq_coordinateIndex {d : ℕ} (i : Fin d) :
    firstIndex i = coordinateIndex i := by
  apply derivativeIndex_ext
  simp [coordinateIndex]

/-- The localized C² transition coefficient is genuinely C¹ everywhere,
with compact support strictly inside the transition source. -/
lemma compact_chart_derivative_coefficient
    {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (e : OpenPartialHomeomorph (Domain d) (Domain d))
    (he : ContDiffOn ℝ 2 e e.source)
    (η : Tests 𝕜 (⊤ : Opens (Domain d))) (hη : tsupport η ⊆ e.source)
    (i k : Fin d) :
    ContDiff ℝ 1 (fun x => η x * (chartCoefficient e i k x : 𝕜)) ∧
      HasCompactSupport (fun x => η x * (chartCoefficient e i k x : 𝕜)) ∧
      tsupport (fun x => η x * (chartCoefficient e i k x : 𝕜)) ⊆ e.source := by
  have hdf : ContDiffOn ℝ 1 (fun x => fderiv ℝ e x (coordinateVector i)) e.source :=
    (he.fderiv_of_isOpen e.open_source (by norm_num)).clm_apply contDiffOn_const
  have hcoord : ContDiffOn ℝ 1 (chartCoefficient e i k) e.source :=
    (contDiffOn_pi.mp hdf) k
  have hscalar : ContDiffOn ℝ 1 (fun x => (chartCoefficient e i k x : 𝕜)) e.source :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp_contDiffOn hcoord
  refine ⟨?_, η.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans hη⟩
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ e.source
  · exact ((η.contDiff.of_le (by norm_num)).contDiffAt).mul
      ((hscalar x hx).contDiffAt (e.open_source.mem_nhds hx))
  · have hxη : x ∉ tsupport η := fun h => hx (hη h)
    have hzero : (fun x => η x * (chartCoefficient e i k x : 𝕜)) =ᶠ[𝓝 x]
        fun _ => (0 : 𝕜) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxη] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

lemma compact_cutoff_derivative_coefficient
    {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (e : OpenPartialHomeomorph (Domain d) (Domain d))
    (η : Tests 𝕜 (⊤ : Opens (Domain d))) (hη : tsupport η ⊆ e.source)
    (i : Fin d) :
    ContDiff ℝ 1 (partialFunction [i] η) ∧ HasCompactSupport (partialFunction [i] η) ∧
      tsupport (partialFunction [i] η) ⊆ e.source := by
  refine ⟨(Smoothing.partialFunction_contDiff [i] η η.contDiff).of_le (by simp), ?_, ?_⟩
  · exact η.hasCompactSupport.fderiv_apply ℝ (coordinateVector i)
  · exact (tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans hη

end Analytic


namespace C2BoundaryModel
/-- The overlap cutoff has a genuine compact C² extension in source-chart
coordinates. Agreement is needed only where the source localized piece lives. -/
lemma exists_compact_overlap_multiplier {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    {Ω : Opens (Domain (n+1))} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    [CompactSpace (frontier (Ω : Set (Domain (n+1))))]
    (B D : C2BoundaryModel 𝕜 Ω p) (i : Fin D.chartCount) (j : Fin B.chartCount) :
    ∃ a : Domain n → 𝕜, ContDiff ℝ 2 a ∧ HasCompactSupport a ∧
      tsupport a ⊆ (B.atlas.chart j).target ∧
      ∀ f : frontier (Ω : Set (Domain (n+1))) → 𝕜,
        EqOn (D.atlas.overlapRepresentative B.atlas i j f)
          ((fun y => a y * B.atlas.localizedRepresentative j f y) ∘
            D.atlas.overlapChart B.atlas i j)
          (D.atlas.overlapChart B.atlas i j).source := by
  let a0 : Domain n → 𝕜 := fun y => (D.atlas.cutoff i ((B.atlas.chart j).symm y) : 𝕜)
  have ha0 : ContDiffOn ℝ 2 a0 (B.atlas.chart j).target :=
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp_contDiffOn
      (B.cutoff_coordinate_contDiff D i j)
  let K := (B.atlas.chart j) '' tsupport (B.atlas.cutoff j)
  obtain ⟨a, ha, hac, hasub, V, hV, hKV, hVa⟩ :=
    ExpandedFA.PartIV.SecondTrace.exists_compact_c2_extension
      (B.atlas.chart j).target (B.atlas.chart j).open_target
      K (B.atlas.cutoffImage_isCompact j) (B.atlas.cutoffImage_subset_target j) a0 ha0
  refine ⟨a, ha, hac, hasub, ?_⟩
  intro f x hx
  have hbase := D.atlas.overlapRepresentative_eqOn B.atlas i j f
    (fun y => D.atlas.cutoff i ((B.atlas.chart j).symm y)) (fun _ _ => rfl) hx
  dsimp only [Function.comp_apply] at hbase ⊢
  change _ = a (D.atlas.overlapChart B.atlas i j x) *
    B.atlas.localizedRepresentative j f (D.atlas.overlapChart B.atlas i j x)
  change _ = a0 (D.atlas.overlapChart B.atlas i j x) *
    B.atlas.localizedRepresentative j f (D.atlas.overlapChart B.atlas i j x) at hbase
  rw [hbase]
  by_cases hz : B.atlas.localizedRepresentative j f (D.atlas.overlapChart B.atlas i j x) = 0
  · simp only [hz, mul_zero]
  · have hK : D.atlas.overlapChart B.atlas i j x ∈ K :=
      B.atlas.localizedRepresentative_support_subset j f hz
    rw [hVa (hKV hK)]


end C2BoundaryModel

open ExpandedFA.PartIV.FractionalSobolev.Transport
open ExpandedFA.PartIV.FractionalSobolev.Boundary.FiniteAtlas

lemma fractional_of_raw_norm_bound {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (G : Domain n → 𝕜) (hG : Measurable G)
    (C : ℝ≥0∞) (hC : C ≠ ∞) (u : FractionalSpace 𝕜 n s p)
    (hb : rawFullNorm s p G ≤ C * ENNReal.ofReal (fractionalNorm s p u)) :
    ∃ v : FractionalSpace 𝕜 n s p, v.val =ᵐ[volume] G ∧
      fractionalNorm s p v ≤ C.toReal * fractionalNorm s p u := by
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (Fact.out : 1 ≤ p))
  have hq : 0 < 1 / p.toReal := one_div_pos.mpr (ENNReal.toReal_pos hp0 hp)
  have hraw : rawFullNorm s p G < ∞ := hb.trans_lt
    (ENNReal.mul_lt_top hC.lt_top ENNReal.ofReal_lt_top)
  have hm : (∫⁻ x, ‖G x‖ₑ ^ p.toReal) ^ (1/p.toReal) < ∞ :=
    lt_of_le_of_lt le_self_add hraw
  have he : rawDoubleEnergy s p G < ∞ :=
    (ENNReal.rpow_lt_top_iff_of_pos hq).mp (lt_of_le_of_lt le_add_self hraw)
  have hmem : MemLp G p volume := by
    change eLpNorm G p volume < ∞
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hG.aestronglyMeasurable]
    exact hm
  let w := hmem.toLp G
  have hw : w =ᵐ[volume] G := hmem.coeFn_toLp
  have hwenergy : differenceEnergy s p w < ∞ := by
    rw [difference_energy_double_integral]
    change rawDoubleEnergy s p w < ∞
    rw [rawDoubleEnergy_congr s p hw]
    exact he
  let v : FractionalSpace 𝕜 n s p := ⟨w, hwenergy⟩
  refine ⟨v, hw, ?_⟩
  have hb' : ENNReal.ofReal (fractionalNorm s p v) ≤
      C * ENNReal.ofReal (fractionalNorm s p u) := by
    rw [← rawFullNorm_eq_ofReal_fractionalNorm s p hp,
      rawFullNorm_congr_ae s p hw]
    exact hb
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top hC ENNReal.ofReal_ne_top) hb'
  simpa only [ENNReal.toReal_ofReal (fractionalNorm_nonneg s p v),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (fractionalNorm_nonneg s p u)] using hr

lemma compact_c1_weighted_pullback {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (e : OpenPartialHomeomorph (Domain n) (Domain n))
    (heInv1 : ContDiffOn ℝ 1 e.symm e.target)
    (K K' : ℝ≥0) (hK : LipschitzOnWith K e e.source)
    (hK' : LipschitzOnWith K' e.symm e.target)
    (a : Domain n → 𝕜) (haC1 : ContDiff ℝ 1 a)
    (haCompact : HasCompactSupport a) (haSource : tsupport a ⊆ e.source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : FractionalSpace 𝕜 n s p,
      ∃ v : FractionalSpace 𝕜 n s p,
        v.val =ᵐ[volume] e.source.indicator (fun x => a x * u.val (e x)) ∧
        fractionalNorm s p v ≤ C * fractionalNorm s p u := by
  classical
  let b : Domain n → 𝕜 := e.target.indicator (a ∘ e.symm)
  obtain ⟨hb, hbCompact, hbSupport, hbEq⟩ :=
    compact_chart_coefficient_contDiff 1 e heInv1 a haC1 haCompact haSource
  obtain ⟨M, L, hM, hL⟩ := compact_c1_coefficient_bounds b hb hbCompact
  obtain ⟨CT, hCT, htrans⟩ := compact_overlap_pullback_rawNorm_bound (𝕜:=𝕜)
    s p hs0 hs1 hp e K K' hK hK' (tsupport a) haCompact.isCompact haSource
  let CP := ENNReal.ofReal (multiplierBound (d:=n) s p M L)
  have hCP : CP ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨(CT*CP).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro u
  let w := fractionalMultiply s p hs0 hs1 hp b M L hM hL u
  let F := fun x => b x * u.val x
  let G := e.source.indicator (fun x => a x * u.val (e x))
  have hF : Measurable F := hb.continuous.measurable.mul (Lp.stronglyMeasurable u.val).measurable
  have hG : Measurable G := by
    have hcomp : Measurable (e.source.indicator (u.val ∘ e)) :=
      chart_indicator_comp_measurable e.symm u.val (Lp.stronglyMeasurable u.val).measurable
    have heq : G = fun x => a x * (e.source.indicator (u.val ∘ e)) x := by
      funext x
      by_cases hx : x ∈ e.source <;> simp [G, hx]
    rw [heq]
    exact haC1.continuous.measurable.mul hcomp
  have hGF : EqOn G (F ∘ e) e.source := by
    intro x hx
    change e.source.indicator (fun x => a x * u.val (e x)) x = b (e x) * u.val (e x)
    rw [indicator_of_mem hx]
    dsimp only [b]
    rw [indicator_of_mem (e.map_source hx)]
    simp only [Function.comp_apply, e.left_inv hx]
  have hGS : Function.support G ⊆ tsupport a := by
    intro x hx
    have hxS : x ∈ e.source := by
      by_contra hxS
      simp [G, hxS] at hx
    apply subset_tsupport a
    intro hax
    simp [G, hxS, hax] at hx
  have hrep : w.val =ᵐ[volume] F :=
    fractionalMultiply_representative s p hs0 hs1 hp b M L hM hL u
  have hmul : rawFullNorm s p F ≤ CP * ENNReal.ofReal (fractionalNorm s p u) := by
    rw [← rawFullNorm_congr_ae s p hrep, rawFullNorm_eq_ofReal_fractionalNorm s p hp]
    dsimp only [CP]
    rw [← ENNReal.ofReal_mul (multiplierBound_nonneg s p M L)]
    exact ENNReal.ofReal_le_ofReal (fractionalMultiply_norm_le s p hs0 hs1 hp b M L hM hL u)
  apply fractional_of_raw_norm_bound s p hp G hG (CT*CP) (ENNReal.mul_ne_top hCT hCP) u
  exact (htrans F G hF hG hGF hGS).trans
    (by simpa only [mul_assoc] using mul_le_mul' (le_refl CT) hmul)


open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.C1Extension.Transport

lemma firstIndex_eq_coordinateIndex {d : ℕ} (i : Fin d) : firstIndex i = coordinateIndex i := by
  apply derivativeIndex_ext
  simp [coordinateIndex]

/-- Compactly supported C² coordinate pullback preserves the actual higher
weak-derivative graph, with a uniform full-norm estimate. -/
lemma compact_c2_higher_pullback {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (σ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hσ0 : 1 < σ) (hσ1 : σ < 2) (hp : p ≠ ∞)
    (e : OpenPartialHomeomorph (Domain d) (Domain d))
    (he : ContDiffOn ℝ 2 e e.source) (he' : ContDiffOn ℝ 2 e.symm e.target)
    (K K' : ℝ≥0) (hK : LipschitzOnWith K e e.source)
    (hK' : LipschitzOnWith K' e.symm e.target)
    (S : Set (Domain d)) (hS : IsCompact S) (hSe : S ⊆ e.source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : HigherFractionalSpace 𝕜 d σ p) (F : Domain d → 𝕜),
      Function.support F ⊆ S →
      F =ᵐ[volume.restrict e.source] (fun x => wholeLp (u.val.val (zeroIndex d 1)) (e x)) →
      ∃ v : HigherFractionalSpace 𝕜 d σ p,
        wholeLp (v.val.val (zeroIndex d 1)) =ᵐ[volume] F ∧
        higherFractionalNorm σ p v ≤ C * higherFractionalNorm σ p u := by
  classical
  let : Fact (p ≠ ∞) := ⟨hp⟩
  let s := σ-1
  have hs0 : 0 < s := by dsimp [s]; linarith
  have hs1 : s < 1 := by dsimp [s]; linarith
  obtain ⟨η, hη, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜) S hS ⟨e.source, e.open_source⟩ hSe
  obtain ⟨T, hT0, hTD⟩ := Analytic.localized_c1_whole_pullback hp e
    (he.of_le (by norm_num)) (he'.of_le (by norm_num)) K K' hK hK' η hη
  let A : Fin d → Fin d → Domain d → 𝕜 := fun i k x => η x * (chartCoefficient e i k x : 𝕜)
  let B : Fin d → Domain d → 𝕜 := fun i => partialFunction [i] η
  have hA (i k : Fin d) : ContDiff ℝ 1 (A i k) ∧ HasCompactSupport (A i k) ∧ tsupport (A i k) ⊆ e.source := by
    exact Analytic.compact_chart_derivative_coefficient e he η hη i k
  have hB (i : Fin d) : ContDiff ℝ 1 (B i) ∧ HasCompactSupport (B i) ∧ tsupport (B i) ⊆ e.source := by
    exact Analytic.compact_cutoff_derivative_coefficient e η hη i
  choose C hC hCA using fun i k : Fin d => compact_c1_weighted_pullback s p hs0 hs1 hp e
    (he'.of_le (by norm_num)) K K' hK hK' (A i k) (hA i k).1 (hA i k).2.1 (hA i k).2.2
  choose D hD hDB using fun i : Fin d => compact_c1_weighted_pullback s p hs0 hs1 hp e
    (he'.of_le (by norm_num)) K K' hK hK' (B i) (hB i).1 (hB i).2.1 (hB i).2.2
  let N : ℝ := Fintype.card (DerivativeIndex d 1)
  let Q := Analytic.wholeFirstFractionalConstant d s p * N
  have hQ : 0 ≤ Q := mul_nonneg (Analytic.wholeFirstFractionalConstant_nonneg d s p) (Nat.cast_nonneg _)
  let Ctotal := ‖T‖*N + (∑ i, ∑ k, C i k) + (∑ i, D i)*Q
  have hCT : 0 ≤ ‖T‖*N := mul_nonneg T.opNorm_nonneg (Nat.cast_nonneg _)
  have hCC : 0 ≤ ∑ i, ∑ k, C i k := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun k _ => hC i k))
  have hDD : 0 ≤ ∑ i, D i := Finset.sum_nonneg (fun i _ => hD i)
  refine ⟨Ctotal, add_nonneg (add_nonneg hCT hCC) (mul_nonneg hDD hQ), ?_⟩
  intro u F hFS hFlocal
  obtain ⟨hf0, hf0bound⟩ := Analytic.higher_base_fractional_norm_bound σ s p hs0 hs1 hp u
  let u0 : FractionalSpace 𝕜 d s p := ⟨wholeLp (u.val.val (zeroIndex d 1)), hf0⟩
  let uD : Fin d → FractionalSpace 𝕜 d s p := fun k => ⟨wholeLp (u.val.val (firstIndex k)), u.property k⟩
  choose W hW hWnorm using fun i k : Fin d => hCA i k (uD k)
  choose Z hZ hZnorm using fun i : Fin d => hDB i u0
  let z : Fin d → FractionalSpace 𝕜 d s p := fun i => (∑ k, W i k) + Z i
  have hz (i : Fin d) : wholeLp ((T u.val).val (firstIndex i)) = (z i).val := by
    have hsum : (z i).val = (∑ k, (W i k).val) + (Z i).val := by
      exact (SharpTraceExtension.fractionalInclusion s p).map_add (∑ k, W i k) (Z i) |>.trans
        (congrArg (fun w => w + (Z i).val) (map_sum (SharpTraceExtension.fractionalInclusion s p) (W i) Finset.univ))
    apply Lp.ext
    rw [hsum]
    have hder := hTD u.val i
    simp only [← firstIndex_eq_coordinateIndex] at hder
    filter_upwards [hder, ae_all_iff.mpr (hW i), hZ i,
      Lp.coeFn_add (∑ k, (W i k).val) (Z i).val,
      Lp.coeFn_finsetSum Finset.univ (fun k => (W i k).val)] with x hdx hWx hZx hAdd hSum
    rw [hdx, hAdd]
    simp only [Pi.add_apply]
    rw [hSum]
    simp only [Finset.sum_apply]
    rw [hZx]
    simp_rw [hWx]
    by_cases hx : x ∈ e.source
    · simp only [indicator_of_mem hx, A, B, uD, u0]
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun k _ => (mul_assoc _ _ _).symm)
    · simp [indicator_of_notMem hx]
  let v : HigherFractionalSpace 𝕜 d σ p := ⟨T u.val, fun i => by rw [hz i]; exact (z i).property⟩
  have hvF : wholeLp (v.val.val (zeroIndex d 1)) =ᵐ[volume] F := by
    have hloc : (fun x => η x * wholeLp (u.val.val (zeroIndex d 1)) (e x)) =ᵐ[volume.restrict e.source]
        (fun x => η x * F x) := by
      filter_upwards [hFlocal] with x hx
      rw [hx]
    have hind := (ae_eq_restrict_iff_indicator_ae_eq e.open_source.measurableSet).mp hloc
    apply (hT0 u.val).trans (hind.trans _)
    exact Eventually.of_forall fun x => by
      by_cases hFx : F x = 0
      · simp [hFx, indicator_apply]
      · have hxS := hFS hFx
        rw [indicator_of_mem (hSe hxS), hηone x hxS, one_mul]
  have hvnorm : higherFractionalNorm σ p v = ‖wholeLp ((T u.val).val (zeroIndex d 1))‖ +
      ∑ i, fractionalNorm s p (z i) := by
    unfold higherFractionalNorm
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    apply Subtype.ext
    exact hz i
  have huD (k : Fin d) : fractionalNorm s p (uD k) ≤ higherFractionalNorm σ p u := by
    apply (Finset.single_le_sum (fun i _ => fractionalNorm_nonneg s p (uD i)) (Finset.mem_univ k)).trans
    exact le_add_of_nonneg_left (norm_nonneg _)
  have hzbound (i : Fin d) : fractionalNorm s p (z i) ≤
      ((∑ k, C i k) + D i*Q) * higherFractionalNorm σ p u := by
    calc
      _ ≤ (∑ k, fractionalNorm s p (W i k)) + fractionalNorm s p (Z i) := by
        change ‖(∑ k, W i k) + Z i‖ ≤ (∑ k, ‖W i k‖) + ‖Z i‖
        exact (norm_add_le (∑ k, W i k) (Z i)).trans
          (add_le_add (norm_sum_le Finset.univ (W i)) (le_refl ‖Z i‖))
      _ ≤ (∑ k, C i k * fractionalNorm s p (uD k)) + D i * fractionalNorm s p u0 :=
        add_le_add (Finset.sum_le_sum (fun k _ => hWnorm i k)) (hZnorm i)
      _ ≤ (∑ k, C i k * higherFractionalNorm σ p u) + D i * (Q * higherFractionalNorm σ p u) := by
        apply add_le_add
        · exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (huD k) (hC i k))
        · exact mul_le_mul_of_nonneg_left hf0bound (hD i)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hbase : ‖wholeLp ((T u.val).val (zeroIndex d 1))‖ ≤
      (‖T‖*N) * higherFractionalNorm σ p u := by
    calc
      _ = ‖(T u.val).val (zeroIndex d 1)‖ := norm_wholeLp _
      _ ≤ ‖T u.val‖ := PiLp.norm_apply_le (T u.val).val _
      _ ≤ ‖T‖ * ‖u.val‖ := T.le_opNorm _
      _ ≤ ‖T‖ * (N * higherFractionalNorm σ p u) := mul_le_mul_of_nonneg_left
        (Analytic.sobolev_norm_le_card_higher_fractional_norm σ p u) T.opNorm_nonneg
      _ = _ := by ring
  refine ⟨v, hvF, ?_⟩
  rw [hvnorm]
  calc
    _ ≤ (‖T‖*N) * higherFractionalNorm σ p u +
        ∑ i, ((∑ k, C i k) + D i*Q) * higherFractionalNorm σ p u :=
      add_le_add hbase (Finset.sum_le_sum (fun i _ => hzbound i))
    _ = _ := by dsimp [Ctotal]; simp only [add_mul, Finset.sum_add_distrib, ← Finset.sum_mul]; ring

/-- In tangential dimension zero the original distributional graph has no
first derivatives; every Lp class gives a genuine higher graph. -/
lemma higher_zero_dim_of_lp {𝕜 : Type} [RCLike 𝕜] (σ : ℝ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (f : Lp 𝕜 p (volume : Measure (Domain 0))) :
    ∃ v : HigherFractionalSpace 𝕜 0 σ p,
      wholeLp (v.val.val (zeroIndex 0 1)) = f := by
  have hf : MemLp f p (volume.restrict ((⊤ : Opens (Domain 0)) : Set (Domain 0))) := by
    simpa using Lp.memLp f
  let u : DomainLp 𝕜 (⊤ : Opens (Domain 0)) p := hf.toLp f
  have hu : wholeLp u = f := by
    apply Lp.ext
    have huf : u =ᵐ[volume] f := by simpa [u] using hf.coeFn_toLp
    exact (wholeLp_representative u).trans huf
  obtain ⟨v, hv⟩ := (higher_fractional_membership 𝕜 0 σ p u).mpr
    ⟨fun i => Fin.elim0 i, (fun i => Fin.elim0 i), fun i => Fin.elim0 i⟩
  exact ⟨v, by rw [hv, hu]⟩

namespace C2BoundaryModel
lemma hasHigherEnergy_dimension_one {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Domain 1)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (B : C2BoundaryModel 𝕜 Ω p) (σ : ℝ) (g : BoundaryLp 𝕜 Ω p) :
    B.HasHigherEnergy σ g := by
  intro j
  exact higher_zero_dim_of_lp σ p (B.atlas.localizedLp p j (B.identify g))
end C2BoundaryModel

lemma higher_overlap_estimate_dimension_one {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Domain 1)) (hb : Bornology.IsBounded (Ω : Set (Domain 1)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (B D : C2BoundaryModel 𝕜 Ω p) (i : Fin D.chartCount) (j : Fin B.chartCount)
    (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : B.HigherData σ,
      ∃ v : HigherFractionalSpace 𝕜 0 σ p,
        wholeLp (v.val.val (zeroIndex 0 1)) =ᵐ[volume]
          D.atlas.overlapRepresentative B.atlas i j (B.identify g.val) ∧
        higherFractionalNorm σ p v ≤ C * higherFractionalNorm σ p (B.higherPiece σ g j) := by
  have hc : IsCompact (frontier (Ω : Set (Domain 1))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  let : CompactSpace (frontier (Ω : Set (Domain 1))) := isCompact_iff_compactSpace.mp hc
  let s : ℝ := 1 / 2
  have hs0 : 0 < s := by norm_num [s]
  have hs1 : s < 1 := by norm_num [s]
  obtain ⟨C, hC, hbound⟩ := D.atlas.overlapFractional_norm_bound (𝕜 := 𝕜) B.atlas s p hs0 hs1 hp i j
  refine ⟨C, hC, ?_⟩
  intro g
  let u : B.atlas.FractionalSpace 𝕜 s p :=
    ⟨B.identify g.val, fun k => (difference_zero_dimension 𝕜 s p _).2⟩
  let w := D.atlas.overlapFractional B.atlas s p hs0 hs1 hp i j u
  obtain ⟨v, hv⟩ := higher_zero_dim_of_lp σ p w.val
  refine ⟨v, ?_, ?_⟩
  · rw [hv]
    exact D.atlas.overlapLp_representative B.atlas s p i j u
  · have hbnd := hbound u
    have hpiece : wholeLp ((B.higherPiece σ g j).val.val (zeroIndex 0 1)) =
        B.atlas.localizedLp p j (B.identify g.val) := Classical.choose_spec (g.property j)
    have hvnorm : higherFractionalNorm σ p v = ‖w.val‖ := by
      simpa [higherFractionalNorm] using congrArg norm hv
    have hgnorm : higherFractionalNorm σ p (B.higherPiece σ g j) =
        ‖B.atlas.localizedLp p j (B.identify g.val)‖ := by
      simpa [higherFractionalNorm] using congrArg norm hpiece
    rw [hvnorm, hgnorm]
    simpa only [fractionalNorm_zero_dimension 𝕜 s p hp] using hbnd


/-- Full higher-order atlas independence in ambient dimension one. -/
theorem higher_atlas_independence_dimension_one {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Domain 1)) (hb : Bornology.IsBounded (Ω : Set (Domain 1)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (B D : C2BoundaryModel 𝕜 Ω p) (σ : ℝ) :
    (∀ g, B.HasHigherEnergy σ g ↔ D.HasHigherEnergy σ g) ∧
    ∃ C E : ℝ, 0 < C ∧ 0 < E ∧
      ∀ (g : B.HigherData σ) (h : D.HigherData σ), g.val = h.val →
        D.higherDataNorm σ h ≤ C * B.higherDataNorm σ g ∧
        B.higherDataNorm σ g ≤ E * D.higherDataNorm σ h := by
  have hc : IsCompact (frontier (Ω : Set (Domain 1))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  let : CompactSpace (frontier (Ω : Set (Domain 1))) := isCompact_iff_compactSpace.mp hc
  obtain ⟨C, hC, hCD⟩ := B.higher_atlas_domination D σ hp
    (fun i j => higher_overlap_estimate_dimension_one Ω hb p hp B D i j σ)
  obtain ⟨E, hE, hDC⟩ := D.higher_atlas_domination B σ hp
    (fun i j => higher_overlap_estimate_dimension_one Ω hb p hp D B i j σ)
  refine ⟨?_, C + 1, E + 1, by linarith, by linarith, ?_⟩
  · intro g
    exact ⟨fun _ => D.hasHigherEnergy_dimension_one σ g,
      fun _ => B.hasHigherEnergy_dimension_one σ g⟩
  · intro g h heq
    obtain ⟨hg, hbound⟩ := hCD g
    obtain ⟨hh, hback⟩ := hDC h
    have heqD : (⟨g.val, hg⟩ : D.HigherData σ) = h := Subtype.ext heq
    have heqB : (⟨h.val, hh⟩ : B.HigherData σ) = g := Subtype.ext heq.symm
    rw [heqD] at hbound
    rw [heqB] at hback
    exact ⟨hbound.trans (mul_le_mul_of_nonneg_right (by linarith)
        (B.higherDataNorm_nonneg _ g)),
      hback.trans (mul_le_mul_of_nonneg_right (by linarith) (D.higherDataNorm_nonneg _ h))⟩


lemma higher_overlap_estimate_of_order {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    {Ω : Opens (Domain (n+1))} [CompactSpace (frontier (Ω : Set (Domain (n+1))))]
    (σ : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hσ0 : 1 < σ) (hσ1 : σ < 2) (hp : p ≠ ∞)
    (B D : C2BoundaryModel 𝕜 Ω p) (i : Fin D.chartCount) (j : Fin B.chartCount) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : B.HigherData σ,
      ∃ v : HigherFractionalSpace 𝕜 n σ p,
        wholeLp (v.val.val (zeroIndex n 1)) =ᵐ[volume]
          D.atlas.overlapRepresentative B.atlas i j (B.identify g.val) ∧
        higherFractionalNorm σ p v ≤ C * higherFractionalNorm σ p (B.higherPiece σ g j) := by
  obtain ⟨a, ha, haCompact, haSource, haEq⟩ := B.exists_compact_overlap_multiplier D i j
  obtain ⟨CM, hCM, hmult⟩ := compact_c2_higher_multiplier σ p hσ0 hσ1 hp a ha haCompact
  let e := D.atlas.overlapChart B.atlas i j
  have he := B.overlap_regular D i j
  obtain ⟨CT, hCT, htrans⟩ := compact_c2_higher_pullback (𝕜 := 𝕜) σ p hσ0 hσ1 hp e he.1 he.2
    _ _ (D.atlas.overlapChart_lipschitz B.atlas i j) (D.atlas.overlapChart_symm_lipschitz B.atlas i j)
    _ (D.atlas.overlapCutoffImage_isCompact B.atlas i j)
    (D.atlas.overlapCutoffImage_subset_source B.atlas i j)
  refine ⟨CT*CM, mul_nonneg hCT hCM, ?_⟩
  intro g
  obtain ⟨w, hw, hwnorm⟩ := hmult (B.higherPiece σ g j)
  have hlocal : wholeLp ((B.higherPiece σ g j).val.val (zeroIndex n 1)) =ᵐ[volume]
      B.atlas.localizedRepresentative j (B.identify g.val) := by
    have hpiece : wholeLp ((B.higherPiece σ g j).val.val (zeroIndex n 1)) =
        B.atlas.localizedLp p j (B.identify g.val) := by
      exact Classical.choose_spec (g.property j)
    rw [hpiece]
    exact B.atlas.localizedLp_representative p j (B.identify g.val)
  have hwlocal : wholeLp (w.val.val (zeroIndex n 1)) =ᵐ[volume]
      (fun y => a y * B.atlas.localizedRepresentative j (B.identify g.val) y) := by
    filter_upwards [hw, hlocal] with y hwy hlocy
    rw [hwy, hlocy]
  have hcomp := ae_comp_of_chart_ae e (D.atlas.overlapChart_symm_lipschitz B.atlas i j) hwlocal
  have hFlocal : D.atlas.overlapRepresentative B.atlas i j (B.identify g.val) =ᵐ[volume.restrict e.source]
      (fun x => wholeLp (w.val.val (zeroIndex n 1)) (e x)) := by
    filter_upwards [hcomp, ae_restrict_mem e.open_source.measurableSet] with x hx hxS
    exact (haEq (B.identify g.val) hxS).trans hx.symm
  obtain ⟨v, hv, hvnorm⟩ := htrans w
    (D.atlas.overlapRepresentative B.atlas i j (B.identify g.val))
    (D.atlas.overlapRepresentative_support_subset B.atlas i j (B.identify g.val)) hFlocal
  refine ⟨v, hv, hvnorm.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hwnorm hCT

/-- Higher-order compact overlap transport, including the differentiated
cutoff term and genuine weak coordinate derivatives. -/
theorem higher_overlap_estimate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (hb : Bornology.IsBounded (Ω : Set (Domain d)))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (B D : C2BoundaryModel 𝕜 Ω p) (i : Fin D.chartCount) (j : Fin B.chartCount) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : B.HigherData (2 - 1 / p.toReal),
      ∃ v : HigherFractionalSpace 𝕜 (d - 1) (2 - 1 / p.toReal) p,
        wholeLp (v.val.val (zeroIndex (d - 1) 1)) =ᵐ[volume]
          D.atlas.overlapRepresentative B.atlas i j (B.identify g.val) ∧
        higherFractionalNorm (2 - 1 / p.toReal) p v ≤
          C * higherFractionalNorm (2 - 1 / p.toReal) p
            (B.higherPiece (2 - 1 / p.toReal) g j) := by

  have hc : IsCompact (frontier (Ω : Set (Domain d))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  let : CompactSpace (frontier (Ω : Set (Domain d))) := isCompact_iff_compactSpace.mp hc
  obtain ⟨hs0, hs1⟩ := SharpTraceBound.endpoint_exponent hp1 hp
  cases d with
  | zero => exact Fin.elim0 (D.normal i)
  | succ n =>
    exact higher_overlap_estimate_of_order (2 - 1 / p.toReal) p (by linarith) (by linarith) hp B D i j


/-- Finite reconstruction gives membership and two-sided full-norm bounds
on the original surface-measure quotient. -/
theorem higher_atlas_independence :
    Specs.ExpandedFA.PartIV.SecondTraceGeometry.HigherAtlasIndependence := by
  intro 𝕜 _ d Ω hb p _ hp1 hp B D
  have hc : IsCompact (frontier (Ω : Set (Domain d))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  let : CompactSpace (frontier (Ω : Set (Domain d))) := isCompact_iff_compactSpace.mp hc
  by_cases hf : frontier (Ω : Set (Domain d)) = ∅
  · exact higher_atlas_independence_empty_frontier Ω hf p hp B D
  obtain ⟨C, hC, hCD⟩ := B.higher_atlas_domination D (2 - 1 / p.toReal) hp
    (higher_overlap_estimate Ω hb p hp1 hp B D)
  obtain ⟨E, hE, hDC⟩ := D.higher_atlas_domination B (2 - 1 / p.toReal) hp
    (higher_overlap_estimate Ω hb p hp1 hp D B)
  refine ⟨?_, C + 1, E + 1, by linarith, by linarith, ?_⟩
  · intro g
    exact ⟨fun hg => (hCD ⟨g, hg⟩).choose, fun hg => (hDC ⟨g, hg⟩).choose⟩
  · intro g h heq
    obtain ⟨hg, hbound⟩ := hCD g
    obtain ⟨hh, hback⟩ := hDC h
    have heqD : (⟨g.val, hg⟩ : D.HigherData (2 - 1 / p.toReal)) = h := Subtype.ext heq
    have heqB : (⟨h.val, hh⟩ : B.HigherData (2 - 1 / p.toReal)) = g := Subtype.ext heq.symm
    rw [heqD] at hbound
    rw [heqB] at hback
    exact ⟨hbound.trans (mul_le_mul_of_nonneg_right (by linarith)
        (B.higherDataNorm_nonneg _ g)),
      hback.trans (mul_le_mul_of_nonneg_right (by linarith) (D.higherDataNorm_nonneg _ h))⟩

end ExpandedFA.PartIV.SecondTrace
