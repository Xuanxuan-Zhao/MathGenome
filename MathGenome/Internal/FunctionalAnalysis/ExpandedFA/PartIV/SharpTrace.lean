import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SharpTrace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.SharpTraceExtension
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.TraceEndpointOne

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma boundedMulLp_tendsto_const (hp : p ≠ ∞)
    (a : ℕ → Domain d → 𝕜) (ha : ∀ n, Continuous (a n))
    (C : ℝ) (hC : ∀ n x, ‖a n x‖ ≤ C) (c : 𝕜)
    (hlim : ∀ x, Tendsto (fun n => a n x) atTop (𝓝 c)) (u : DomainLp 𝕜 Ω p) :
    Tendsto (fun n => boundedMulLp (a n) (ha n) C (hC n) u) atTop (𝓝 (c • u)) := by
  have hd := SharpTraceExtension.eLpNorm_tendsto_zero_of_dominated
    (volume.restrict (Ω : Set (Domain d))) p hp
    (fun n x => (a n x - c) * u x) (fun x => (C + ‖c‖) * ‖u x‖)
    (fun n => ((ha n).aestronglyMeasurable.sub aestronglyMeasurable_const).mul
      (Lp.aestronglyMeasurable u)) ((Lp.memLp u).norm.const_mul (C + ‖c‖))
    (fun n => Filter.Eventually.of_forall fun x => by
      rw [norm_mul]
      apply (mul_le_mul_of_nonneg_right ((norm_sub_le (a n x) c).trans
        (add_le_add (hC n x) le_rfl)) (norm_nonneg _)).trans
      exact le_abs_self _)
    (Filter.Eventually.of_forall fun x => by
      simpa only [sub_self, zero_mul] using ((hlim x).sub (tendsto_const_nhds (x := c))).mul
        (tendsto_const_nhds (x := u x)))
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mpr
  convert hd using 1
  funext n
  apply eLpNorm_congr_ae
  filter_upwards [boundedMulLp_coe (a n) (ha n) C (hC n) u, Lp.coeFn_smul c u] with x hx hy
  simp only [Pi.sub_apply, hx, hy, Pi.smul_apply, smul_eq_mul]
  ring

lemma partial_scaled (i : Fin d) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (x : Domain d) :
    partialFunction [i] (fun y => f (t • y)) x = t • partialFunction [i] f (t • x) := by
  change (fderiv ℝ (f ∘ (t • id)) x) (coordinateVector i) = _
  rw [fderiv_comp x (hf.differentiable (by simp) _) (differentiable_id.const_smul t _)]
  simp [fderiv_const_smul differentiableAt_id t, partialFunction]

/-- Compact smooth multipliers tending to one with derivatives tending to
zero converge on the actual first-jet graph at every finite exponent. -/
lemma ambientMultiply_tendsto (hp : p ≠ ∞)
    (a : ℕ → Domain d → 𝕜) (ha : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (a n))
    (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ n x, ‖a n x‖ ≤ C)
    (hD : ∀ n j x, ‖partialFunction [j] (a n) x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => a n x) atTop (𝓝 1))
    (hdlim : ∀ j x, Tendsto (fun n => partialFunction [j] (a n) x) atTop (𝓝 0))
    (u : SpaceValue 𝕜 d Ω 1 p) :
    Tendsto (fun n => ambientMultiply (a n) (ha n) C hC0 (hC n) (hD n) u)
      atTop (𝓝 u) := by
  apply tendsto_subtype_rng.mpr
  have h (α : DerivativeIndex d 1) :
      Tendsto (fun n => ambientMultiplyJet (a n) (ha n) C (hC n) (hD n) u.val α)
        atTop (𝓝 (u.val α)) := by
    rcases multiIndex_order_one_cases (natIndex α) α.property with hz | ⟨j, hj⟩
    · have hα : α = zeroIndex d 1 := derivativeIndex_ext hz
      subst α
      simp only [ambientMultiplyJet_zero]
      simpa only [one_smul] using boundedMulLp_tendsto_const hp a
        (fun n => (ha n).continuous) C hC 1 hlim (u.val (zeroIndex d 1))
    · have hα : α = coordinateIndex j := derivativeIndex_ext (by simpa [coordinateIndex] using hj)
      subst α
      simp only [ambientMultiplyJet_coordinate]
      have h₁ := boundedMulLp_tendsto_const hp a (fun n => (ha n).continuous) C hC
        1 hlim (u.val (coordinateIndex j))
      have h₂ := boundedMulLp_tendsto_const hp (fun n => partialFunction [j] (a n))
        (fun n => (Smoothing.partialFunction_contDiff _ _ (ha n)).continuous)
        C (fun n => hD n j) 0 (hdlim j) (u.val (zeroIndex d 1))
      simpa only [one_smul, zero_smul, add_zero] using h₁.add h₂
  exact (PiLp.continuous_toLp 1 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr h)

lemma exists_compact_multiplier_approximation (hp : p ≠ ∞)
    (u : SpaceValue 𝕜 d Ω 1 p) :
    ∃ (a : ℕ → Tests 𝕜 (⊤ : Opens (Domain d))) (C : ℝ)
      (hC0 : 0 ≤ C) (hC : ∀ n x, ‖a n x‖ ≤ C)
      (hD : ∀ n j x, ‖partialFunction [j] (a n) x‖ ≤ C),
      Tendsto (fun n => ambientMultiply (a n) (a n).contDiff C hC0 (hC n) (hD n) u)
        atTop (𝓝 u) := by
  obtain ⟨η, _, hη⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    ({0} : Set (Domain d)) (isCompact_singleton) ⊤ (by simp)
  obtain ⟨C, hC0, hC, hD⟩ := ambient_test_bounds η
  let q : ℕ → ℝ := fun n => 1 / (n + 1)
  have hqpos (n) : 0 < q n := by dsimp [q]; positivity
  have hqle (n) : q n ≤ 1 := by
    dsimp [q]
    exact (div_le_one (by positivity)).mpr (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
  have hq : Tendsto q atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let a : ℕ → Tests 𝕜 (⊤ : Opens (Domain d)) := fun n =>
    ⟨fun x => η (q n • x), η.contDiff.comp (contDiff_const_smul _),
      η.hasCompactSupport.comp_homeomorph (Homeomorph.smul (Units.mk0 (q n) (hqpos n).ne')), by simp⟩
  have ha (n x) : ‖a n x‖ ≤ C := hC _
  have hd (n j x) : ‖partialFunction [j] (a n) x‖ ≤ C := by
    change ‖partialFunction [j] (fun y => η (q n • y)) x‖ ≤ C
    rw [partial_scaled j η η.contDiff, norm_smul, Real.norm_eq_abs, abs_of_pos (hqpos n)]
    exact (mul_le_mul_of_nonneg_left (hD j _) (hqpos n).le).trans
      (mul_le_of_le_one_left hC0 (hqle n))
  refine ⟨a, C, hC0, ha, hd, ambientMultiply_tendsto hp _ (fun n => (a n).contDiff)
    C hC0 ha hd ?_ ?_ u⟩
  · intro x
    change Tendsto (fun n => η (q n • x)) atTop (𝓝 1)
    have hx := η.continuous.continuousAt.tendsto.comp (hq.smul_const x)
    simpa only [Function.comp_def, a, zero_smul, hη 0 (by simp)] using hx
  · intro j x
    change Tendsto (fun n => partialFunction [j] (fun y => η (q n • y)) x) atTop (𝓝 0)
    have hx := ((Smoothing.partialFunction_contDiff [j] η η.contDiff).continuous.tendsto 0).comp
      (by simpa only [zero_smul] using hq.smul_const x)
    have ht := hq.smul hx
    simpa only [zero_smul] using ht.congr (fun n => (partial_scaled j η η.contDiff (q n) x).symm)

/-- Exhaustion removes the compact-support restriction from the accepted
flat zero-trace argument. -/
lemma coordinate_trace_zero_mem_zeroSpace (i : Fin d) (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Transverse i)))
    (hT : IsCoordinateTrace i T) (u : SpaceValue 𝕜 d (upper i) 1 p) (hu : T u = 0) :
    u ∈ ZeroSpaceValue 𝕜 d (upper i) 1 p hp := by
  obtain ⟨a, C, hC0, hC, hD, hlim⟩ := exists_compact_multiplier_approximation hp u
  apply (smoothSubmodule 𝕜 d (upper i) 1 p).isClosed_topologicalClosure.mem_of_tendsto hlim
  apply Filter.Eventually.of_forall
  intro n
  let v := ambientMultiply (a n) (a n).contDiff C hC0 (hC n) (hD n) u
  apply coordinate_zero_trace_mem_zeroSpace_of_compact_support hp i T hT v
    (coordinate_trace_zero_ambientMultiply i hp T hT _ (a n).contDiff C hC0 (hC n) (hD n) u hu)
    (tsupport (a n)) (a n).hasCompactSupport
  filter_upwards [ambientMultiply_coe (a n) (a n).contDiff C hC0 (hC n) (hD n) u] with x hx hxK
  rw [hx, image_eq_zero_of_notMem_tsupport hxK, zero_mul]

lemma coordinate_kernel_contains_zeroSpace (i : Fin d) (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Transverse i)))
    (hT : IsCoordinateTrace i T) : ZeroSpaceValue 𝕜 d (upper i) 1 p hp ≤ T.ker := by
  apply (smoothSubmodule 𝕜 d (upper i) 1 p).topologicalClosure_minimal _ T.isClosed_ker
  rintro u ⟨φ, hφ⟩
  change T u = 0
  apply Lp.ext
  filter_upwards [hT u φ (φ.contDiff.of_le (by simp)) hφ,
    Lp.coeFn_zero 𝕜 p (volume : Measure (Transverse i))] with y hy hz
  rw [hy, hz]
  apply φ.zero_on_compl
  change ¬ 0 < coordinateLine i y 0 i
  simp [coordinateLine]

/-- Smooth restriction determines the C1 trace as well, by the already
proved density. This also ties the endpoint trace to the kernel theorem. -/
lemma coordinate_trace_of_smooth_agreement (i : Fin d) (hp : p ≠ ∞)
    (T : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] Lp 𝕜 p (volume : Measure (Transverse i)))
    (hT : ∀ (u : SpaceValue 𝕜 d (upper i) 1 p) (f : Domain d → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f →
      T u =ᵐ[volume] fun y : Transverse i => f (coordinateLine i y 0)) :
    IsCoordinateTrace i T := by
  obtain ⟨S, hS, _⟩ := coordinate_upper_trace_exists (𝕜 := 𝕜) i hp
  have heq : EqOn T S (SmoothUpToBoundary (𝕜 := 𝕜) (upper i) p) := by
    rintro u ⟨f, hf, hu⟩
    exact Lp.ext ((hT u f hf hu).trans (hS u f (hf.of_le (by simp)) hu).symm)
  have hTS : T = S := by
    apply ContinuousLinearMap.ext
    intro u
    exact heq.closure T.continuous S.continuous (coordinate_upper_smooth_density i hp u)
  rw [hTS]
  exact hS

/-- The genuine trace has the original closure-defined kernel in every
half-space and at every finite exponent, including the endpoint. -/
theorem halfSpace_kernel : Specs.ExpandedFA.PartIV.SharpTrace.HalfSpaceKernel := by
  intro 𝕜 _ d i p _ hp T hT
  have hc := coordinate_trace_of_smooth_agreement i hp T hT
  apply le_antisymm
  · intro u hu
    exact coordinate_trace_zero_mem_zeroSpace i hp T hc u hu
  · exact coordinate_kernel_contains_zeroSpace i hp T hc

theorem halfSpace_bound_and_lift :
    Specs.ExpandedFA.PartIV.SharpTrace.HalfSpaceBoundAndLift :=
  ⟨sharp_trace_bound, SharpTraceExtension.bounded_right_inverse⟩

theorem halfSpace_onto : Specs.ExpandedFA.PartIV.SharpTrace.HalfSpaceOnto := by
  intro 𝕜 _ n p _ hp1 hp i T hT g
  obtain ⟨C, hC, hE⟩ := SharpTraceExtension.bounded_right_inverse n p hp1 hp
  obtain ⟨E, _, _, _, hTrace⟩ := hE 𝕜 i
  exact ⟨E g, hTrace T hT g⟩

theorem halfSpace_endpoint : Specs.ExpandedFA.PartIV.SharpTrace.HalfSpaceEndpoint :=
  TraceEndpointOne.halfSpace_onto_trace_exists

theorem domain_kernel : Specs.ExpandedFA.PartIV.SharpTrace.DomainKernel := trace_kernel

/-- In particular this handles the empty boundary and dimension zero when
assembling the endpoint theorem. -/
theorem domain_endpoint_of_surfaceMeasure_zero
    (hμ : surfaceMeasure Ω = 0)
    (T : SpaceValue 𝕜 d Ω 1 1 →L[𝕜] BoundaryLp 𝕜 Ω 1) :
    Function.Surjective T := by
  intro g
  refine ⟨0, ?_⟩
  rw [map_zero]
  apply Lp.ext
  simp [Filter.EventuallyEq, hμ]

/-- Restrict a genuine ambient flattening chart to the actual frontier and
remove its normal coordinate. Values outside the chart target are irrelevant. -/
def frontierChart {n : ℕ} (Ω : Opens (Domain (n + 1)))
    (x₀ : frontier (Ω : Set (Domain (n + 1))))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1)))
    (i : Fin (n + 1)) (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i) :
    OpenPartialHomeomorph (frontier (Ω : Set (Domain (n + 1)))) (Domain n) := by
  classical
  let v : Domain n → frontier (Ω : Set (Domain (n + 1))) := fun z =>
    if hz : z ∈ boundaryParameters Φ i then
      ⟨boundaryParam Φ i z, ((boundaryParam_image Ω Φ i hside).subset ⟨z, hz, rfl⟩).2⟩
    else x₀
  have hv (z) (hz : z ∈ boundaryParameters Φ i) :
      (v z).val = boundaryParam Φ i z := by simp only [v, dite_eq_left hz]
  refine {
    toFun := fun x => i.removeNth (Φ x.val)
    invFun := v
    source := Subtype.val ⁻¹' Φ.source
    target := boundaryParameters Φ i
    map_source' := ?_
    map_target' := ?_
    left_inv' := ?_
    right_inv' := ?_
    open_source := Φ.open_source.preimage continuous_subtype_val
    open_target := boundaryParameters_isOpen Φ i
    continuousOn_toFun := ?_
    continuousOn_invFun := ?_
  }
  · intro x hx
    change i.insertNth (α := fun _ => ℝ) 0 (i.removeNth (Φ x.val)) ∈ Φ.target
    rw [← (chart_boundary_iff Ω Φ i hside x.val hx).mp x.property,
      Fin.insertNth_self_removeNth]
    exact Φ.map_source hx
  · intro z hz
    change (v z).val ∈ Φ.source
    rw [hv z hz]
    exact Φ.map_target hz
  · intro x hx
    apply Subtype.ext
    have hz : i.removeNth (Φ x.val) ∈ boundaryParameters Φ i := by
      change i.insertNth (α := fun _ => ℝ) 0 (i.removeNth (Φ x.val)) ∈ Φ.target
      rw [← (chart_boundary_iff Ω Φ i hside x.val hx).mp x.property,
        Fin.insertNth_self_removeNth]
      exact Φ.map_source hx
    rw [hv _ hz]
    dsimp [boundaryParam]
    rw [← (chart_boundary_iff Ω Φ i hside x.val hx).mp x.property,
      Fin.insertNth_self_removeNth, Φ.left_inv hx]
  · intro z hz
    change i.removeNth (Φ (v z).val) = z
    rw [hv z hz]
    dsimp [boundaryParam]
    rw [Φ.right_inv hz, Fin.removeNth_insertNth]
  · have hrem : Continuous (fun y : Domain (n + 1) => i.removeNth y) :=
      continuous_pi fun j => continuous_apply (i.succAbove j)
    exact hrem.continuousOn.comp
      (Φ.continuousOn.comp continuous_subtype_val.continuousOn (fun _ hx => hx))
      (fun _ _ => mem_univ _)
  · apply Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    apply ContinuousOn.congr _ (fun z hz => hv z hz)
    exact Φ.continuousOn_symm.comp (continuous_insertNth_zero i).continuousOn (fun _ hz => hz)

lemma frontierChart_apply {n : ℕ} (Ω : Opens (Domain (n + 1)))
    (x₀ : frontier (Ω : Set (Domain (n + 1))))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1)))
    (i : Fin (n + 1)) (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (x : frontier (Ω : Set (Domain (n + 1)))) :
    frontierChart Ω x₀ Φ i hside x = i.removeNth (Φ x.val) := rfl

lemma frontierChart_symm_apply {n : ℕ} (Ω : Opens (Domain (n + 1)))
    (x₀ : frontier (Ω : Set (Domain (n + 1))))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1)))
    (i : Fin (n + 1)) (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (z : Domain n) (hz : z ∈ boundaryParameters Φ i) :
    ((frontierChart Ω x₀ Φ i hside).symm z).val = boundaryParam Φ i z := by
  classical
  change (if h : z ∈ boundaryParameters Φ i then
    (⟨boundaryParam Φ i z, _⟩ : frontier (Ω : Set (Domain (n + 1)))) else x₀).val = _
  rw [dite_eq_left hz]

lemma frontierChart_lipschitz {n : ℕ} (Ω : Opens (Domain (n + 1)))
    (x₀ : frontier (Ω : Set (Domain (n + 1))))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1)))
    (i : Fin (n + 1)) (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K : ℝ≥0} (hK : LipschitzOnWith K Φ Φ.source) :
    LipschitzOnWith K (frontierChart Ω x₀ Φ i hside)
      (frontierChart Ω x₀ Φ i hside).source := by
  intro x hx y hy
  change edist (i.removeNth (Φ x.val)) (i.removeNth (Φ y.val)) ≤ _
  have hr : LipschitzWith 1 (fun z : Domain (n + 1) => i.removeNth z) :=
    by
      intro a b
      apply edist_pi_le_iff.mpr
      intro j
      simpa only [Fin.removeNth, Function.comp_def, ENNReal.coe_one, one_mul] using
        (LipschitzWith.eval (i.succAbove j) a b)
  exact (hr _ _).trans (by simpa only [Subtype.edist_eq, ENNReal.coe_one, one_mul] using hK hx hy)

lemma frontierChart_symm_lipschitz {n : ℕ} (Ω : Opens (Domain (n + 1)))
    (x₀ : frontier (Ω : Set (Domain (n + 1))))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1)))
    (i : Fin (n + 1)) (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K : ℝ≥0} (hK : LipschitzOnWith K Φ.symm Φ.target) :
    LipschitzOnWith K (frontierChart Ω x₀ Φ i hside).symm
      (frontierChart Ω x₀ Φ i hside).target := by
  intro x hx y hy
  change edist ((frontierChart Ω x₀ Φ i hside).symm x).val
    ((frontierChart Ω x₀ Φ i hside).symm y).val ≤ _
  rw [frontierChart_symm_apply Ω x₀ Φ i hside x hx,
    frontierChart_symm_apply Ω x₀ Φ i hside y hy]
  exact boundaryParam_lipschitz Φ i hK hx hy

/-- The actual C1 flattening definition, rather than a stronger graph-boundary
hypothesis, yields the intrinsic finite atlas needed for the sharp theorem. -/
theorem finite_boundary_atlas (Ω : Opens (Domain d)) (hΩ : IsC1Domain Ω)
    (hc : IsCompact (frontier (Ω : Set (Domain d)))) :
    ∃ N : ℕ, Nonempty (Boundary.FiniteAtlas (frontier (Ω : Set (Domain d)))
      (d - 1) (Fin N)) := by
  classical
  by_cases hne : (frontier (Ω : Set (Domain d))).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    cases d with
    | zero =>
      obtain ⟨i, _⟩ := hΩ x₀ hx₀
      exact Fin.elim0 i
    | succ n =>
      obtain ⟨N, i, Φ, B, K, L, hB, hcharts, hLip, hcover⟩ :=
        finite_bounded_bilipschitz_boundary_charts (n + 1) Ω hΩ hc
      let x : frontier (Ω : Set (Domain (n + 1))) := ⟨x₀, hx₀⟩
      let e := fun j => frontierChart Ω x (Φ j) (i j) (hcharts j).2.2.2.2.1
      apply C1Geometry.exists_finiteAtlas_of_compact_charts _ hc e K L
      · intro y
        obtain ⟨j, hj⟩ := mem_iUnion.mp (hcover y.property)
        exact ⟨j, hj⟩
      · intro j
        have hr : LipschitzWith 1 (fun z : Domain (n + 1) => (i j).removeNth z) :=
          by
            intro a b
            apply edist_pi_le_iff.mpr
            intro k
            simpa only [Fin.removeNth, Function.comp_def, ENNReal.coe_one, one_mul] using
              (LipschitzWith.eval ((i j).succAbove k) a b)
        apply (hr.isBounded_image (hcharts j).2.2.2.1).subset
        intro z hz
        refine ⟨(i j).insertNth 0 z, hz, ?_⟩
        exact Fin.removeNth_insertNth _ _ _
      · intro j
        exact frontierChart_lipschitz Ω x (Φ j) (i j) _ (hLip j).1
      · intro j
        exact frontierChart_symm_lipschitz Ω x (Φ j) (i j) _ (hLip j).2
  · have hempty : IsEmpty (frontier (Ω : Set (Domain d))) := ⟨fun x => hne ⟨x.val, x.property⟩⟩
    let _ := hempty
    refine ⟨0, ⟨{
      chart := Fin.elim0
      cover := fun x => isEmptyElim x
      chartLip := Fin.elim0
      chartSymmLip := Fin.elim0
      chart_lipschitz := fun j => Fin.elim0 j
      chartSymm_lipschitz := fun j => Fin.elim0 j
      bounded_target := fun j => Fin.elim0 j
      cutoff := Fin.elim0
      cutoffLip := Fin.elim0
      cutoff_lipschitz := fun j => Fin.elim0 j
      cutoff_nonneg := fun j => Fin.elim0 j
      cutoff_sum := fun x => isEmptyElim x
      cutoff_subordinate := fun j => Fin.elim0 j
    }⟩⟩

/-- Passing between a measure on a closed subset and its pushforward does
not change the Lp norm or identify any additional functions. -/
def subtypeLpEquiv {X : Type} [MeasurableSpace X] (s : Set X)
    (hs : MeasurableSet s) (μ : Measure s) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p (μ.map Subtype.val) ≃ₗᵢ[𝕜] Lp 𝕜 p μ := by
  let hpres : MeasurePreserving (Subtype.val : s → X) μ (μ.map Subtype.val) :=
    ⟨measurable_subtype_coe, rfl⟩
  apply LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ 𝕜 Subtype.val hpres)
  intro u
  let f : X → 𝕜 := Function.extend Subtype.val u (fun _ => 0)
  have hf : f ∘ (Subtype.val : s → X) = u := by
    funext x
    exact Subtype.coe_injective.extend_apply (u : s → 𝕜) (fun _ => 0) x
  have hmem : MemLp f p (μ.map Subtype.val) :=
    (MeasurableEmbedding.subtype_coe hs).memLp_map_measure_iff.mpr (hf ▸ Lp.memLp u)
  refine ⟨hmem.toLp f, ?_⟩
  apply Lp.ext
  exact (Lp.coeFn_compMeasurePreserving _ hpres).trans
    (((hpres.quasiMeasurePreserving.ae_eq_comp hmem.coeFn_toLp)).trans (Filter.EventuallyEq.of_eq hf))

/-- Every finite atlas on the actual frontier has pushforward measure
comparable in both directions to the original surface measure. -/
lemma atlas_surface_comparison {n N : ℕ} (Ω : Opens (Domain (n + 1)))
    (A : Boundary.FiniteAtlas (frontier (Ω : Set (Domain (n + 1)))) n (Fin N)) :
    ∃ C D : ℝ≥0∞, C ≠ ∞ ∧ D ≠ ∞ ∧
      A.atlasMeasure.map Subtype.val ≤ C • surfaceMeasure Ω ∧
      surfaceMeasure Ω ≤ D • A.atlasMeasure.map Subtype.val := by
  obtain ⟨C, hC, hμH⟩ := surfaceMeasure_le_hausdorff Ω
  obtain ⟨D, hD, hHμ⟩ := hausdorff_restrict_le_surfaceMeasure Ω
  let P : ℝ≥0∞ := ∑ j, (A.chartLip j : ℝ≥0∞) ^ n
  let Q : ℝ≥0∞ := ∑ j, (A.chartSymmLip j : ℝ≥0∞) ^ n
  have hP : P ≠ ∞ := by simp [P]
  have hQ : Q ≠ ∞ := by simp [Q]
  have hmapH : (Measure.hausdorffMeasure (n : ℝ) :
      Measure (frontier (Ω : Set (Domain (n + 1))))).map Subtype.val =
      (Measure.hausdorffMeasure (n : ℝ)).restrict (frontier (Ω : Set (Domain (n + 1)))) := by
    simpa only [Subtype.range_coe] using
      (isometry_subtype_coe (s := frontier (Ω : Set (Domain (n + 1))))).map_hausdorffMeasure
        (Or.inl (Nat.cast_nonneg n))
  have hAH : A.atlasMeasure.map Subtype.val ≤ P •
      (Measure.hausdorffMeasure (n : ℝ)).restrict (frontier (Ω : Set (Domain (n + 1)))) := by
    have h := Measure.map_mono A.atlasMeasure_le_smul_hausdorff measurable_subtype_coe
    rwa [Measure.map_smul _ measurable_subtype_coe.aemeasurable, hmapH] at h
  have hHA : (Measure.hausdorffMeasure (n : ℝ)).restrict (frontier (Ω : Set (Domain (n + 1)))) ≤
      Q • A.atlasMeasure.map Subtype.val := by
    have h := Measure.map_mono A.hausdorff_le_smul_atlasMeasure measurable_subtype_coe
    rwa [Measure.map_smul _ measurable_subtype_coe.aemeasurable, hmapH] at h
  refine ⟨P * D, C * Q, ENNReal.mul_ne_top hP hD.ne,
    ENNReal.mul_ne_top hC.ne hQ, ?_, ?_⟩
  · calc
      _ ≤ P • ((Measure.hausdorffMeasure (n : ℝ)).restrict
          (frontier (Ω : Set (Domain (n + 1))))) := hAH
      _ ≤ P • (D • surfaceMeasure Ω) := by gcongr
      _ = _ := by rw [smul_smul]
  · calc
      _ ≤ C • ((Measure.hausdorffMeasure (n : ℝ)).restrict
          (frontier (Ω : Set (Domain (n + 1))))) := hμH
      _ ≤ C • (Q • A.atlasMeasure.map Subtype.val) := by gcongr
      _ = _ := by rw [smul_smul]

/-- The atlas and surface-measure models agree on every representative;
no trace theorem is assumed in this change of quotient. -/
theorem boundaryModelOfAtlas {𝕜 : Type} [RCLike 𝕜] {n N : ℕ}
    (Ω : Opens (Domain (n + 1))) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : Boundary.FiniteAtlas (frontier (Ω : Set (Domain (n + 1)))) n (Fin N)) :
    Nonempty (BoundaryModel 𝕜 Ω p) := by
  obtain ⟨C, D, hC, hD, hμν, hνμ⟩ := atlas_surface_comparison Ω A
  let J := subtypeLpEquiv (frontier (Ω : Set (Domain (n + 1))))
    isClosed_frontier.measurableSet A.atlasMeasure 𝕜 p
  let E := Boundary.changeMeasureLpLinearEquiv (𝕜 := 𝕜) p hC hμν hD hνμ
  refine ⟨{
    chartCount := N
    atlas := A
    identify := E.trans J.toLinearEquiv
    forwardConstant := C.toReal ^ (1 / p).toReal
    backwardConstant := D.toReal ^ (1 / p).toReal
    forward_nonneg := Real.rpow_nonneg ENNReal.toReal_nonneg _
    backward_nonneg := Real.rpow_nonneg ENNReal.toReal_nonneg _
    representative := ?_
    forward_bound := ?_
    backward_bound := ?_
  }⟩
  · intro g f hgf
    let hpres : MeasurePreserving (Subtype.val : frontier (Ω : Set (Domain (n + 1))) → _)
        A.atlasMeasure (A.atlasMeasure.map Subtype.val) := ⟨measurable_subtype_coe, rfl⟩
    have hJ : J (E g) =ᵐ[A.atlasMeasure] (E g) ∘ Subtype.val :=
      Lp.coeFn_compMeasurePreserving (E g) hpres
    have hE : E g =ᵐ[A.atlasMeasure.map Subtype.val] f :=
      (Boundary.changeMeasureLpLinear_representative p hC hμν g).trans
        ((Measure.absolutelyContinuous_of_le_smul hμν).ae_eq hgf)
    exact hJ.trans (hpres.quasiMeasurePreserving.ae_eq_comp hE)
  · intro g
    change ‖J (E g)‖ ≤ _
    rw [J.norm_map]
    exact Boundary.changeMeasureLpLinear_norm_le p hC hμν g
  · intro g
    change ‖g‖ ≤ _ * ‖J (E g)‖
    rw [J.norm_map]
    have h := Boundary.changeMeasureLpLinear_norm_le p hD hνμ (E g)
    change ‖Boundary.changeMeasureLpLinear p hD hνμ
      (Boundary.changeMeasureLpLinear p hC hμν g)‖ ≤ _ at h
    rw [Boundary.changeMeasureLpLinear_inverse] at h
    exact h

/-- A domain with empty frontier has the zero boundary space, with its empty
atlas. This includes ambient dimension zero without a positive-dimension assumption. -/
theorem boundaryModelOfEmptyFrontier (Ω : Opens (Domain d))
    (hf : frontier (Ω : Set (Domain d)) = ∅) (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)] : Nonempty (BoundaryModel 𝕜 Ω p) := by
  classical
  have : IsEmpty (frontier (Ω : Set (Domain d))) := ⟨fun x => by simpa [hf] using x.property⟩
  let A : Boundary.FiniteAtlas (frontier (Ω : Set (Domain d))) (d - 1) (Fin 0) := {
    chart := Fin.elim0
    cover := fun x => isEmptyElim x
    chartLip := Fin.elim0
    chartSymmLip := Fin.elim0
    chart_lipschitz := fun j => Fin.elim0 j
    chartSymm_lipschitz := fun j => Fin.elim0 j
    bounded_target := fun j => Fin.elim0 j
    cutoff := Fin.elim0
    cutoffLip := Fin.elim0
    cutoff_lipschitz := fun j => Fin.elim0 j
    cutoff_nonneg := fun j => Fin.elim0 j
    cutoff_sum := fun x => isEmptyElim x
    cutoff_subordinate := fun j => Fin.elim0 j
  }
  have hμ : surfaceMeasure Ω = 0 := by simp [surfaceMeasure, hf]
  have hA : A.atlasMeasure = 0 := Subsingleton.elim _ _
  have : Subsingleton (BoundaryLp 𝕜 Ω p) := ⟨fun u v => Lp.ext (by simp [Filter.EventuallyEq, hμ])⟩
  have : Subsingleton (Lp 𝕜 p A.atlasMeasure) := ⟨fun u v => Lp.ext (by simp [Filter.EventuallyEq, hA])⟩
  refine ⟨{
    chartCount := 0
    atlas := A
    identify := LinearEquiv.ofSubsingleton _ _
    representative := fun _ _ _ => by simp [Filter.EventuallyEq, hA]
    forwardConstant := 0
    backwardConstant := 0
    forward_nonneg := le_rfl
    backward_nonneg := le_rfl
    forward_bound := ?_
    backward_bound := ?_
  }⟩
  · intro g
    rw [Subsingleton.elim (LinearEquiv.ofSubsingleton (BoundaryLp 𝕜 Ω p)
      (Lp 𝕜 p A.atlasMeasure) g) 0, norm_zero, zero_mul]
  · intro g
    rw [Subsingleton.elim g 0, norm_zero, zero_mul]

/-- Faithful surface-measure boundary models exist under exactly the
original bounded C1-domain hypothesis, at every finite exponent. -/
theorem boundary_models_exist : Specs.ExpandedFA.PartIV.SharpTrace.BoundaryModelsExist := by
  intro 𝕜 _ d Ω hb hΩ p _ hp
  have hc : IsCompact (frontier (Ω : Set (Domain d))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  cases d with
  | zero =>
    have hf : frontier (Ω : Set (Domain 0)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨i, _⟩ := hΩ x hx
      exact Fin.elim0 i
    exact boundaryModelOfEmptyFrontier Ω hf 𝕜 p
  | succ n =>
    obtain ⟨N, ⟨A⟩⟩ := finite_boundary_atlas Ω hΩ hc
    exact boundaryModelOfAtlas Ω p A


lemma localizedLp_norm_le {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    {n : ℕ} {ι : Type*} [Fintype ι] (A : Boundary.FiniteAtlas M n ι)
    {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (j : ι) (u : Lp 𝕜 p A.atlasMeasure) : ‖A.localizedLp p j u‖ ≤ ‖u‖ := by
  have hu : AEStronglyMeasurable (u : M → 𝕜) (A.chartMeasure j) :=
    (Lp.aestronglyMeasurable u).mono_measure (A.chartMeasure_le j)
  have h : eLpNorm (A.localizedLp p j u) p volume ≤ eLpNorm u p A.atlasMeasure := by
    rw [eLpNorm_congr_ae (A.localizedLp_representative p j u)]
    unfold Boundary.FiniteAtlas.localizedRepresentative
    rw [eLpNorm_indicator_eq_eLpNorm_restrict (A.chart j).open_target.measurableSet.nullMeasurableSet]
    calc
      _ ≤ eLpNorm ((u : M → 𝕜) ∘ (A.chart j).symm) p
          (volume.restrict (A.chart j).target) := by
        apply eLpNorm_mono_ae
        · exact ((RCLike.continuous_ofReal.comp (A.cutoff_lipschitz j).continuous).comp_continuousOn
            (A.chart j).continuousOn_symm).aestronglyMeasurable
            (A.chart j).open_target.measurableSet |>.mul (hu.comp_aemeasurable
              ((A.chart j).continuousOn_symm.aemeasurable (A.chart j).open_target.measurableSet))
        filter_upwards with x
        simp only [Function.comp_apply, norm_mul, RCLike.norm_ofReal,
          abs_of_nonneg (A.cutoff_nonneg j _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (A.cutoff_le_one j _)
      _ = eLpNorm u p (A.chartMeasure j) := by
        exact (eLpNorm_map_measure hu
          ((A.chart j).continuousOn_symm.aemeasurable (A.chart j).open_target.measurableSet)).symm
      _ ≤ _ := eLpNorm_mono_measure u (A.chartMeasure_le j)
  simpa only [← Lp.norm_def] using ENNReal.toReal_mono (Lp.eLpNorm_ne_top u) h

def atlasLocalizerCLM {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    {n : ℕ} {ι : Type*} [Fintype ι] (A : Boundary.FiniteAtlas M n ι)
    {𝕜 : Type} [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : ι) :
    Lp 𝕜 p A.atlasMeasure →L[𝕜] Lp 𝕜 p (volume : Measure (Domain n)) :=
  (A.localizer p j).mkContinuous 1 (fun u => by simpa only [one_mul, Boundary.FiniteAtlas.localizer, LinearMap.coe_mk, AddHom.coe_mk] using localizedLp_norm_le A p j u)


/-- Exact localized trace transport follows from smooth agreement and the
actual Lp bounds on the atlas localizer and surface identification. -/
lemma localized_trace_eq_of_smooth
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n + 1))}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : BoundaryModel 𝕜 Ω p)
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (j : Fin B.chartCount) (i : Fin (n + 1))
    (E : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜]
      SpaceValue 𝕜 (n + 1) (upper i) 1 p)
    (S : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)))
    (T : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (hT : IsTrace T)
    (hSmooth : ∀ (u : SpaceValue 𝕜 (n + 1) Ω 1 p) (f : Domain (n + 1) → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))] f →
      reindexedTrace i S (E u) =ᵐ[volume]
        B.atlas.localizedRepresentative j (fun x => f x.val)) :
    ∀ u, B.atlas.localizedLp p j (B.identify (T u)) = reindexedTrace i S (E u) := by
  let I : BoundaryLp 𝕜 Ω p →L[𝕜] Lp 𝕜 p B.atlas.atlasMeasure :=
    B.identify.toLinearMap.mkContinuous B.forwardConstant B.forward_bound
  let F := (atlasLocalizerCLM B.atlas p j).comp (I.comp T)
  let G := (reindexedTrace i S).comp E
  have heq : EqOn F G (SmoothUpToBoundary (𝕜 := 𝕜) Ω p) := by
    rintro u ⟨f, hf, hu⟩
    apply Lp.ext
    exact (B.atlas.localizedLp_representative p j (B.identify (T u))).trans
      ((B.atlas.localizedRepresentative_congr_ae j (B.representative (T u) f
        (hT u f hf hu))).trans (hSmooth u f hf hu).symm)
  intro u
  exact heq.closure F.continuous G.continuous (hdense u)

lemma flattened_trace_smooth_eq_localized
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n + 1))}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : BoundaryModel 𝕜 Ω p)
    (j : Fin B.chartCount) (i : Fin (n + 1))
    (x₀ : frontier (Ω : Set (Domain (n + 1))))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1)))
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (θ χ : Tests 𝕜 (⊤ : Opens (Domain (n + 1))))
    (hχ : tsupport χ ⊆ Φ.target)
    (hχone : ∀ x ∈ tsupport θ, χ (Φ x) = 1)
    (hchart : B.atlas.chart j = frontierChart Ω x₀ Φ i hside)
    (hcutoff : ∀ x : frontier (Ω : Set (Domain (n + 1))),
      (B.atlas.cutoff j x : 𝕜) = θ x.val)
    (E : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜]
      SpaceValue 𝕜 (n + 1) (upper i) 1 p)
    (hE : ∀ (u : SpaceValue 𝕜 (n + 1) Ω 1 p) (f : Domain (n + 1) → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))] f →
      ContDiff ℝ 1 (fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))) ∧
      (E u).val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)))
    (S : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S)
    (u : SpaceValue 𝕜 (n + 1) Ω 1 p) (f : Domain (n + 1) → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hu : u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))] f) :
    reindexedTrace i S (E u) =ᵐ[volume]
      B.atlas.localizedRepresentative j (fun x => f x.val) := by
  obtain ⟨hg, hEu⟩ := hE u f hf hu
  apply (reindexedTrace_smooth i S hS (E u) _ hg hEu).trans
  apply Filter.Eventually.of_forall
  intro z
  unfold Boundary.FiniteAtlas.localizedRepresentative
  rw [hchart]
  change χ (i.insertNth 0 z) * (θ (Φ.symm (i.insertNth 0 z)) *
    f (Φ.symm (i.insertNth 0 z))) =
      (boundaryParameters Φ i).indicator (fun x =>
        (B.atlas.cutoff j ((frontierChart Ω x₀ Φ i hside).symm x) : 𝕜) *
          f ((frontierChart Ω x₀ Φ i hside).symm x).val) z
  by_cases hz : z ∈ boundaryParameters Φ i
  · rw [indicator_of_mem hz, hcutoff,
      frontierChart_symm_apply Ω x₀ Φ i hside z hz]
    change χ (i.insertNth 0 z) * (θ (Φ.symm (i.insertNth 0 z)) *
      f (Φ.symm (i.insertNth 0 z))) =
        θ (Φ.symm (i.insertNth 0 z)) * f (Φ.symm (i.insertNth 0 z))
    by_cases hθz : θ (Φ.symm (i.insertNth 0 z)) = 0
    · simp only [hθz, zero_mul, mul_zero]
    · have hχz := hχone _ (subset_tsupport θ hθz)
      rw [Φ.right_inv hz] at hχz
      rw [hχz, one_mul]
  · rw [indicator_of_notMem hz]
    have hχz : i.insertNth (α := fun _ => ℝ) 0 z ∉ tsupport χ := fun h => hz (hχ h)
    rw [image_eq_zero_of_notMem_tsupport hχz, zero_mul]



structure SmoothBoundaryAtlas {n : ℕ} (Ω : Opens (Domain (n+1)))
    (x₀ : frontier (Ω : Set (Domain (n+1)))) where
  chartCount : ℕ
  normal : Fin chartCount → Fin (n+1)
  ambient : Fin chartCount → OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1))
  side : ∀ j y, y ∈ (ambient j).source → (y ∈ Ω ↔ 0 < ambient j y (normal j))
  derivativeBound : ℝ
  derivativeBound_nonneg : 0 ≤ derivativeBound
  regular : ∀ j,
    ContDiffOn ℝ 1 (ambient j) (ambient j).source ∧
    ContDiffOn ℝ 1 (ambient j).symm (ambient j).target ∧
    Bornology.IsBounded (ambient j).source ∧ Bornology.IsBounded (ambient j).target ∧
    (∀ y ∈ (ambient j).source, ‖fderiv ℝ (ambient j) y‖ ≤ derivativeBound) ∧
    (∀ y ∈ (ambient j).target, ‖fderiv ℝ (ambient j).symm y‖ ≤ derivativeBound)
  ambientLip : Fin chartCount → ℝ≥0
  ambientSymmLip : Fin chartCount → ℝ≥0
  ambient_lipschitz : ∀ j, LipschitzOnWith (ambientLip j) (ambient j) (ambient j).source
  ambientSymm_lipschitz : ∀ j,
    LipschitzOnWith (ambientSymmLip j) (ambient j).symm (ambient j).target
  test : Fin chartCount → Tests ℝ (⊤ : Opens (Domain (n+1)))
  test_nonneg : ∀ j y, 0 ≤ test j y
  test_sum : ∀ y ∈ frontier (Ω : Set (Domain (n+1))), ∑ j, test j y = 1
  test_subordinate : ∀ j, tsupport (test j) ⊆ (ambient j).source
  atlas : Boundary.FiniteAtlas (frontier (Ω : Set (Domain (n+1)))) n (Fin chartCount)
  chart_eq : ∀ j, atlas.chart j = frontierChart Ω x₀ (ambient j) (normal j) (side j)
  cutoff_eq : ∀ j x, atlas.cutoff j x = test j x.val

lemma frontierChart_target_bounded {n : ℕ} (Ω : Opens (Domain (n+1)))
    (x₀ : frontier (Ω : Set (Domain (n+1))))
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (i : Fin (n+1)) (hside : ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i)
    (hb : Bornology.IsBounded Φ.target) :
    Bornology.IsBounded (frontierChart Ω x₀ Φ i hside).target := by
  have hr : LipschitzWith 1 (fun z : Domain (n+1) => i.removeNth z) := by
    intro a b
    apply edist_pi_le_iff.mpr
    intro k
    simpa only [Fin.removeNth, Function.comp_def, ENNReal.coe_one, one_mul] using
      (LipschitzWith.eval (i.succAbove k) a b)
  apply (hr.isBounded_image hb).subset
  intro z hz
  refine ⟨i.insertNth 0 z, hz, ?_⟩
  exact Fin.removeNth_insertNth _ _ _

theorem exists_smoothBoundaryAtlas {n : ℕ} (Ω : Opens (Domain (n+1)))
    (hΩ : IsC1Domain Ω) (hc : IsCompact (frontier (Ω : Set (Domain (n+1)))))
    (x₀ : frontier (Ω : Set (Domain (n+1)))) : Nonempty (SmoothBoundaryAtlas Ω x₀) := by
  classical
  obtain ⟨N, i, Φ, B, K, L, hB, hcharts, hLip, hcover⟩ :=
    finite_bounded_bilipschitz_boundary_charts (n+1) Ω hΩ hc
  let U : Opens (Domain (n+1)) := ⟨⋃ j, (Φ j).source, isOpen_iUnion fun j => (Φ j).open_source⟩
  obtain ⟨κ, hκ, φ, hφLip, hφnonneg, hφsum, hφsub⟩ :=
    Boundary.finite_lipschitz_cutoffs U (frontier (Ω : Set (Domain (n+1)))) hc hcover
      (Fin N) (fun j => (Φ j).source) (fun j => (Φ j).open_source) (by exact Subset.rfl)
  let : Finite κ := hκ
  let : Fintype κ := Fintype.ofFinite κ
  choose P hP using hφLip
  choose ind hind using hφsub
  let q : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let normal := fun j => i (ind (q j))
  let ambient := fun j => Φ (ind (q j))
  have side : ∀ j y, y ∈ (ambient j).source → (y ∈ Ω ↔ 0 < ambient j y (normal j)) :=
    fun j => (hcharts (ind (q j))).2.2.2.2.1
  let ψ : Fin (Fintype.card κ) → Tests ℝ (⊤ : Opens (Domain (n+1))) := fun j =>
    ⟨φ (q j), (φ (q j)).contDiff, (φ (q j)).hasCompactSupport, by simp⟩
  have hψnonneg : ∀ j y, 0 ≤ ψ j y := fun j y => hφnonneg (q j) y
  have hψsum : ∀ y ∈ frontier (Ω : Set (Domain (n+1))), ∑ j, ψ j y = 1 := by
    intro y hy
    change ∑ j, φ (q j) y = 1
    rw [q.sum_comp (fun k => φ k y)]
    simpa only [finsum_eq_sum_of_fintype] using hφsum y hy
  have hψsub : ∀ j, tsupport (ψ j) ⊆ (ambient j).source := fun j => hind (q j)
  let e := fun j => frontierChart Ω x₀ (ambient j) (normal j) (side j)
  let cutoff : Fin (Fintype.card κ) → frontier (Ω : Set (Domain (n+1))) → ℝ :=
    fun j x => ψ j x.val
  have hcutLip (j) : LipschitzWith (P (q j)) (cutoff j) := by
    have heq : cutoff j = fun x => φ (q j) x.val := by funext x; rfl
    rw [heq]
    simpa only [Function.comp_def, mul_one] using
      (hP (q j)).comp (LipschitzWith.subtype_val (frontier (Ω : Set (Domain (n+1)))))
  have hcutsub (j) : tsupport (cutoff j) ⊆ (e j).source :=
    (C1Geometry.tsupport_restrict_subset _ (ψ j)).trans (preimage_mono (hψsub j))
  have hcutsum (x : frontier (Ω : Set (Domain (n+1)))) : ∑ j, cutoff j x = 1 :=
    hψsum x.val x.property
  let A : Boundary.FiniteAtlas (frontier (Ω : Set (Domain (n+1)))) n (Fin (Fintype.card κ)) := {
    chart := e
    cover := by
      intro x
      have hne : ∃ j, cutoff j x ≠ 0 := by
        by_contra hn
        push Not at hn
        have h := hcutsum x
        simp only [hn, Finset.sum_const_zero] at h
        exact zero_ne_one h
      obtain ⟨j, hj⟩ := hne
      exact ⟨j, hcutsub j (subset_tsupport (cutoff j) hj)⟩
    chartLip := fun j => K (ind (q j))
    chartSymmLip := fun j => L (ind (q j))
    chart_lipschitz := fun j => frontierChart_lipschitz Ω x₀ _ _ _ (hLip _).1
    chartSymm_lipschitz := fun j => frontierChart_symm_lipschitz Ω x₀ _ _ _ (hLip _).2
    bounded_target := fun j => frontierChart_target_bounded Ω x₀ _ _ _ (hcharts _).2.2.2.1
    cutoff := cutoff
    cutoffLip := fun j => P (q j)
    cutoff_lipschitz := hcutLip
    cutoff_nonneg := fun j x => hψnonneg j x.val
    cutoff_sum := hcutsum
    cutoff_subordinate := hcutsub
  }
  exact ⟨{
    chartCount := Fintype.card κ
    normal := normal
    ambient := ambient
    side := side
    derivativeBound := B
    derivativeBound_nonneg := hB
    regular := fun j => ⟨(hcharts _).1, (hcharts _).2.1, (hcharts _).2.2.1,
      (hcharts _).2.2.2.1, (hcharts _).2.2.2.2.2.1, (hcharts _).2.2.2.2.2.2⟩
    ambientLip := fun j => K (ind (q j))
    ambientSymmLip := fun j => L (ind (q j))
    ambient_lipschitz := fun j => (hLip _).1
    ambientSymm_lipschitz := fun j => (hLip _).2
    test := ψ
    test_nonneg := hψnonneg
    test_sum := hψsum
    test_subordinate := hψsub
    atlas := A
    chart_eq := fun _ => rfl
    cutoff_eq := fun _ _ => rfl
  }⟩

def boundaryModelFromAtlas {𝕜 : Type} [RCLike 𝕜] {n N : ℕ}
    (Ω : Opens (Domain (n + 1))) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : Boundary.FiniteAtlas (frontier (Ω : Set (Domain (n + 1)))) n (Fin N)) :
    BoundaryModel 𝕜 Ω p := by
  let comparison := atlas_surface_comparison Ω A
  let C : ℝ≥0∞ := Classical.choose comparison
  let D : ℝ≥0∞ := Classical.choose (Classical.choose_spec comparison)
  have hcomparison : C ≠ ∞ ∧ D ≠ ∞ ∧
      A.atlasMeasure.map Subtype.val ≤ C • surfaceMeasure Ω ∧
      surfaceMeasure Ω ≤ D • A.atlasMeasure.map Subtype.val :=
    Classical.choose_spec (Classical.choose_spec comparison)
  rcases hcomparison with ⟨hC, hD, hμν, hνμ⟩
  let J := subtypeLpEquiv (frontier (Ω : Set (Domain (n + 1))))
    isClosed_frontier.measurableSet A.atlasMeasure 𝕜 p
  let E := Boundary.changeMeasureLpLinearEquiv (𝕜 := 𝕜) p hC hμν hD hνμ
  exact {
    chartCount := N
    atlas := A
    identify := E.trans J.toLinearEquiv
    forwardConstant := C.toReal ^ (1 / p).toReal
    backwardConstant := D.toReal ^ (1 / p).toReal
    forward_nonneg := Real.rpow_nonneg ENNReal.toReal_nonneg _
    backward_nonneg := Real.rpow_nonneg ENNReal.toReal_nonneg _
    representative := by
      intro g f hgf
      let hpres : MeasurePreserving
          (Subtype.val : frontier (Ω : Set (Domain (n + 1))) → _)
          A.atlasMeasure (A.atlasMeasure.map Subtype.val) := ⟨measurable_subtype_coe, rfl⟩
      have hJ : J (E g) =ᵐ[A.atlasMeasure] (E g) ∘ Subtype.val :=
        Lp.coeFn_compMeasurePreserving (E g) hpres
      have hE : E g =ᵐ[A.atlasMeasure.map Subtype.val] f :=
        (Boundary.changeMeasureLpLinear_representative p hC hμν g).trans
          ((Measure.absolutelyContinuous_of_le_smul hμν).ae_eq hgf)
      exact hJ.trans (hpres.quasiMeasurePreserving.ae_eq_comp hE)
    forward_bound := by
      intro g
      change ‖J (E g)‖ ≤ _
      rw [J.norm_map]
      exact Boundary.changeMeasureLpLinear_norm_le p hC hμν g
    backward_bound := by
      intro g
      change ‖g‖ ≤ _ * ‖J (E g)‖
      rw [J.norm_map]
      have h := Boundary.changeMeasureLpLinear_norm_le p hD hνμ (E g)
      change ‖Boundary.changeMeasureLpLinear p hD hνμ
        (Boundary.changeMeasureLpLinear p hC hμν g)‖ ≤ _ at h
      rw [Boundary.changeMeasureLpLinear_inverse] at h
      exact h
  }

@[simp] lemma boundaryModelFromAtlas_chartCount {𝕜 : Type} [RCLike 𝕜] {n N : ℕ}
    (Ω : Opens (Domain (n+1))) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : Boundary.FiniteAtlas (frontier (Ω : Set (Domain (n+1)))) n (Fin N)) :
    (boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A).chartCount = N := rfl

@[simp] lemma boundaryModelFromAtlas_atlas {𝕜 : Type} [RCLike 𝕜] {n N : ℕ}
    (Ω : Opens (Domain (n+1))) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (A : Boundary.FiniteAtlas (frontier (Ω : Set (Domain (n+1)))) n (Fin N)) :
    (boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A).atlas = A := rfl


end ExpandedFA.PartIV.SharpTrace
namespace ExpandedFA.PartIV.SharpTrace.BoundaryModel
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (A B : BoundaryModel 𝕜 Ω p)

lemma identify_lpEquiv (g : BoundaryLp 𝕜 Ω p) :
    A.atlas.lpEquiv B.atlas p (B.identify g) = A.identify g := by
  apply Lp.ext
  exact (A.atlas.lpEquiv_representative B.atlas p (B.identify g)).trans
    (((A.atlas.atlasMeasure_absolutelyContinuous B.atlas).ae_eq
      (B.representative g g Filter.EventuallyEq.rfl)).trans
      (A.representative g g Filter.EventuallyEq.rfl).symm)

variable [CompactSpace (frontier (Ω : Set (Domain d)))]

lemma finiteEnergy_iff (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (g : BoundaryLp 𝕜 Ω p) : A.FiniteEnergy s g ↔ B.FiniteEnergy s g := by
  unfold FiniteEnergy
  rw [← A.identify_lpEquiv B g]
  exact A.atlas.finite_energy_lpEquiv_iff B.atlas p s hs0 hs1 hp (B.identify g)

def transferData (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (u : B.Data s) : A.Data s :=
  ⟨u.val, (A.finiteEnergy_iff B s hs0 hs1 hp u.val).mpr u.property⟩

@[simp] lemma transferData_val (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (u : B.Data s) : (A.transferData B s hs0 hs1 hp u).val = u.val := rfl

lemma transferData_norm_bound (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : B.Data s,
      A.dataNorm s (A.transferData B s hs0 hs1 hp u) ≤ C * B.dataNorm s u := by
  let : Fact (p ≠ ∞) := ⟨hp⟩
  obtain ⟨C, hC, hb⟩ := A.atlas.fractionalLinearEquiv_norm_bound
    (𝕜 := 𝕜) B.atlas s p hs0 hs1
  refine ⟨C, hC, ?_⟩
  intro u
  have h := hb ⟨B.identify u.val, u.property⟩
  change A.atlas.fractionalNorm s p
    ⟨A.atlas.lpEquiv B.atlas p (B.identify u.val), _⟩ ≤
      C * B.atlas.fractionalNorm s p ⟨B.identify u.val, u.property⟩ at h
  change A.atlas.fractionalNorm s p ⟨A.identify u.val, _⟩ ≤
    C * B.atlas.fractionalNorm s p ⟨B.identify u.val, u.property⟩
  simpa only [A.identify_lpEquiv B] using h

lemma transferData_norm_equivalence (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ u : B.Data s,
      A.dataNorm s (A.transferData B s hs0 hs1 hp u) ≤ C * B.dataNorm s u ∧
      B.dataNorm s u ≤ D * A.dataNorm s (A.transferData B s hs0 hs1 hp u) := by
  obtain ⟨C, hC, hb⟩ := A.transferData_norm_bound B s hs0 hs1 hp
  obtain ⟨D, hD, hd⟩ := B.transferData_norm_bound A s hs0 hs1 hp
  refine ⟨C, D, hC, hD, fun u => ⟨hb u, ?_⟩⟩
  simpa only [transferData] using hd (A.transferData B s hs0 hs1 hp u)

/-- A lift proved using one faithful boundary model applies to every model.
The transported datum is the identical original surface Lp class. -/
lemma bounded_right_inverse_of_model (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (hp : p ≠ ∞)
    (hA : ∃ (C : ℝ) (E : A.Data s → SpaceValue 𝕜 d Ω 1 p),
      0 ≤ C ∧
      (∀ u v w, w.val = u.val + v.val → E w = E u + E v) ∧
      (∀ (c : 𝕜) u v, v.val = c • u.val → E v = c • E u) ∧
      (∀ u, ‖E u‖ ≤ C * A.dataNorm s u) ∧
      (∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
        ∀ u, T (E u) = u.val)) :
    ∃ (C : ℝ) (E : B.Data s → SpaceValue 𝕜 d Ω 1 p),
      0 ≤ C ∧
      (∀ u v w, w.val = u.val + v.val → E w = E u + E v) ∧
      (∀ (c : 𝕜) u v, v.val = c • u.val → E v = c • E u) ∧
      (∀ u, ‖E u‖ ≤ C * B.dataNorm s u) ∧
      (∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
        ∀ u, T (E u) = u.val) := by
  obtain ⟨C, E, hC, hadd, hsmul, hbound, htrace⟩ := hA
  obtain ⟨D, hD, hnorm⟩ := A.transferData_norm_bound B s hs0 hs1 hp
  let F : B.Data s → SpaceValue 𝕜 d Ω 1 p :=
    fun u => E (A.transferData B s hs0 hs1 hp u)
  refine ⟨C * D, F, mul_nonneg hC hD, ?_, ?_, ?_, ?_⟩
  · intro u v w hw
    exact hadd _ _ _ hw
  · intro c u v hv
    exact hsmul c _ _ hv
  · intro u
    exact (hbound _).trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hnorm u) hC)
  · intro T hT u
    exact htrace T hT (A.transferData B s hs0 hs1 hp u)

/-- A sharp trace bound in a convenient model transfers to every model. -/
lemma sharp_bound_of_model (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (hp : p ≠ ∞)
    (hA : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u, ∃ h : A.FiniteEnergy s (T u),
        A.dataNorm s ⟨T u, h⟩ ≤ C * ‖u‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u, ∃ h : B.FiniteEnergy s (T u),
        B.dataNorm s ⟨T u, h⟩ ≤ C * ‖u‖ := by
  obtain ⟨C, hC, hb⟩ := hA
  obtain ⟨D, hD, hnorm⟩ := B.transferData_norm_bound A s hs0 hs1 hp
  refine ⟨D * C, mul_nonneg hD hC, ?_⟩
  intro T hT u
  obtain ⟨hu, hbu⟩ := hb T hT u
  refine ⟨(B.finiteEnergy_iff A s hs0 hs1 hp (T u)).mpr hu, ?_⟩
  exact (hnorm ⟨T u, hu⟩).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbu hD)

/-- The full fractional class of one boundary partition piece. -/
def localizedFractional (s : ℝ) (u : A.Data s) (j : Fin A.chartCount) :
    FractionalSpace 𝕜 (d - 1) s p :=
  ⟨A.atlas.localizedLp p j (A.identify u.val), u.property j⟩

omit [CompactSpace (frontier (Ω : Set (Domain d)))] in
/-- Finite gluing of local bounded linear lifts. The trace identity is the
partition reconstruction, so its proof can be supplied by chart naturality. -/
lemma bounded_right_inverse_of_local_maps (s : ℝ) [Fact (p ≠ ∞)]
    (Q : Fin A.chartCount →
      FractionalSpace 𝕜 (d - 1) s p →L[𝕜] SpaceValue 𝕜 d Ω 1 p)
    (hQ : ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u : A.Data s, ∑ j, T (Q j (A.localizedFractional s u j)) = u.val) :
    ∃ (C : ℝ) (E : A.Data s → SpaceValue 𝕜 d Ω 1 p),
      0 ≤ C ∧
      (∀ u v w, w.val = u.val + v.val → E w = E u + E v) ∧
      (∀ (c : 𝕜) u v, v.val = c • u.val → E v = c • E u) ∧
      (∀ u, ‖E u‖ ≤ C * A.dataNorm s u) ∧
      (∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
        ∀ u, T (E u) = u.val) := by
  classical
  let E : A.Data s → SpaceValue 𝕜 d Ω 1 p :=
    fun u => ∑ j, Q j (A.localizedFractional s u j)
  let C : ℝ := ∑ j, ‖Q j‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun j _ => (Q j).opNorm_nonneg
  refine ⟨C, E, hC, ?_, ?_, ?_, ?_⟩
  · intro u v w hw
    have hj (j : Fin A.chartCount) :
        A.localizedFractional s w j = A.localizedFractional s u j +
          A.localizedFractional s v j := by
      apply Subtype.ext
      change A.atlas.localizedLp p j (A.identify w.val) =
        A.atlas.localizedLp p j (A.identify u.val) + A.atlas.localizedLp p j (A.identify v.val)
      rw [hw, map_add, A.atlas.localizedLp_add]
    simp only [E, hj, map_add, Finset.sum_add_distrib]
  · intro c u v hv
    have hj (j : Fin A.chartCount) :
        A.localizedFractional s v j = c • A.localizedFractional s u j := by
      apply Subtype.ext
      change A.atlas.localizedLp p j (A.identify v.val) =
        c • A.atlas.localizedLp p j (A.identify u.val)
      rw [hv, map_smul, A.atlas.localizedLp_smul]
    simp only [E, hj, map_smul, Finset.smul_sum]
  · intro u
    calc
      ‖E u‖ ≤ ∑ j, ‖Q j (A.localizedFractional s u j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, C * ‖A.localizedFractional s u j‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (Q j).le_opNorm _ |>.trans
          (mul_le_mul_of_nonneg_right
            (Finset.single_le_sum (fun k _ => (Q k).opNorm_nonneg) (Finset.mem_univ j))
            (norm_nonneg _))
      _ = C * A.dataNorm s u := by
        rw [← Finset.mul_sum]
        rfl
  · intro T hT u
    change T (∑ j, Q j (A.localizedFractional s u j)) = u.val
    rw [map_sum]
    exact hQ T hT u


end ExpandedFA.PartIV.SharpTrace.BoundaryModel
namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma boundaryLp_eq_zero_of_surfaceMeasure_zero (hμ : surfaceMeasure Ω = 0)
    (g : BoundaryLp 𝕜 Ω p) : g = 0 := by
  apply Lp.ext
  simp [Filter.EventuallyEq, hμ]

lemma boundaryModel_finiteEnergy_of_surfaceMeasure_zero
    (hμ : surfaceMeasure Ω = 0) (hp : p ≠ ∞) (B : BoundaryModel 𝕜 Ω p)
    (s : ℝ) (g : BoundaryLp 𝕜 Ω p) : B.FiniteEnergy s g := by
  rw [boundaryLp_eq_zero_of_surfaceMeasure_zero hμ g]
  intro j
  rw [map_zero]
  change differenceEnergy s p ((B.atlas.localizer p j) 0) < ∞
  rw [map_zero]
  exact finite_energy_zero s p hp

lemma boundaryModel_dataNorm_of_surfaceMeasure_zero
    (hμ : surfaceMeasure Ω = 0) (hp : p ≠ ∞) (B : BoundaryModel 𝕜 Ω p)
    (s : ℝ) (g : B.Data s) : B.dataNorm s g = 0 := by
  let : Fact (p ≠ ∞) := ⟨hp⟩
  have hz : B.identify g.val = 0 := by
    rw [boundaryLp_eq_zero_of_surfaceMeasure_zero hμ g.val, map_zero]
  have heq : (⟨B.identify g.val, g.property⟩ : B.atlas.FractionalSpace 𝕜 s p) = 0 :=
    Subtype.ext hz
  change ‖(⟨B.identify g.val, g.property⟩ : B.atlas.FractionalSpace 𝕜 s p)‖ = 0
  rw [heq, norm_zero]

theorem domain_sharp_bound_of_empty_frontier
    (hf : frontier (Ω : Set (Domain d)) = ∅) (hp : p ≠ ∞)
    (B : BoundaryModel 𝕜 Ω p) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u, ∃ h : B.FiniteEnergy s (T u), B.dataNorm s ⟨T u, h⟩ ≤ C * ‖u‖ := by
  have hμ : surfaceMeasure Ω = 0 := by simp [surfaceMeasure, hf]
  refine ⟨0, le_rfl, ?_⟩
  intro T _ u
  refine ⟨boundaryModel_finiteEnergy_of_surfaceMeasure_zero hμ hp B s (T u), ?_⟩
  rw [boundaryModel_dataNorm_of_surfaceMeasure_zero hμ hp B, zero_mul]

theorem domain_right_inverse_of_empty_frontier
    (hf : frontier (Ω : Set (Domain d)) = ∅) (hp : p ≠ ∞)
    (B : BoundaryModel 𝕜 Ω p) (s : ℝ) :
    ∃ (C : ℝ) (E : B.Data s → SpaceValue 𝕜 d Ω 1 p),
      0 ≤ C ∧
      (∀ u v w, w.val = u.val + v.val → E w = E u + E v) ∧
      (∀ (c : 𝕜) u v, v.val = c • u.val → E v = c • E u) ∧
      (∀ u, ‖E u‖ ≤ C * B.dataNorm s u) ∧
      (∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
        ∀ u, T (E u) = u.val) := by
  have hμ : surfaceMeasure Ω = 0 := by simp [surfaceMeasure, hf]
  refine ⟨0, fun _ => 0, le_rfl, ?_, ?_, ?_, ?_⟩
  · intro u v w _
    simp
  · intro c u v _
    simp
  · intro u
    simp
  · intro T _ u
    rw [map_zero, boundaryLp_eq_zero_of_surfaceMeasure_zero hμ u.val]



lemma localized_sharp_bound_of_chart
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n + 1))}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (B : BoundaryModel 𝕜 Ω p)
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (j : Fin B.chartCount) (i : Fin (n + 1))
    (x₀ : frontier (Ω : Set (Domain (n + 1))))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1)))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ D)
    (hDinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ D)
    (hSource : Bornology.IsBounded Φ.source)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (θ : Tests 𝕜 (⊤ : Opens (Domain (n + 1)))) (hθ : tsupport θ ⊆ Φ.source)
    (hchart : B.atlas.chart j = frontierChart Ω x₀ Φ i hside)
    (hcutoff : ∀ x : frontier (Ω : Set (Domain (n + 1))),
      (B.atlas.cutoff j x : 𝕜) = θ x.val) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u, ∃ h : differenceEnergy (1 - 1 / p.toReal) p
          (B.atlas.localizedLp p j (B.identify (T u))) < ∞,
        fractionalNorm (1 - 1 / p.toReal) p
          ⟨B.atlas.localizedLp p j (B.identify (T u)), h⟩ ≤ C * ‖u‖ := by
  obtain ⟨χ, hχ, hχone, E, hE⟩ := exists_flattened_localization (p := p)
    i Φ hΦ hInv D hD0 hD hDinv hSource hside θ hθ
  obtain ⟨S, hS, _⟩ := coordinate_upper_trace_exists (𝕜 := 𝕜) i hp
  obtain ⟨C, hC, hb⟩ := sharp_trace_bound n p hp1 hp
  refine ⟨C * ‖E‖, mul_nonneg hC E.opNorm_nonneg, ?_⟩
  intro T hT u
  have heq := localized_trace_eq_of_smooth B hdense j i E S T hT
    (flattened_trace_smooth_eq_localized B j i x₀ Φ hside θ χ hχ hχone hchart hcutoff E hE S hS) u
  obtain ⟨hu, hbu⟩ := (hb 𝕜 i).2 S hS (E u)
  have hmem : differenceEnergy (1 - 1 / p.toReal) p
      (B.atlas.localizedLp p j (B.identify (T u))) < ∞ := heq.symm ▸ hu
  refine ⟨hmem, ?_⟩
  have hnorm : fractionalNorm (1 - 1 / p.toReal) p
      ⟨B.atlas.localizedLp p j (B.identify (T u)), hmem⟩ =
        fractionalNorm (1 - 1 / p.toReal) p ⟨reindexedTrace i S (E u), hu⟩ :=
    congrArg (fractionalNorm (1 - 1 / p.toReal) p) (Subtype.ext heq)
  rw [hnorm]
  apply hbu.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (E.le_opNorm u) hC

lemma boundary_sharp_bound_of_chart_estimates
    {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : BoundaryModel 𝕜 Ω p)
    (s : ℝ)
    (hlocal : ∀ j : Fin B.chartCount, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u, ∃ h : differenceEnergy s p (B.atlas.localizedLp p j (B.identify (T u))) < ∞,
        fractionalNorm s p ⟨B.atlas.localizedLp p j (B.identify (T u)), h⟩ ≤ C * ‖u‖) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u, ∃ h : B.FiniteEnergy s (T u), B.dataNorm s ⟨T u, h⟩ ≤ C * ‖u‖ := by
  choose C hC hb using hlocal
  refine ⟨∑ j, C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro T hT u
  choose hmem hbound using fun j => hb j T hT u
  refine ⟨hmem, ?_⟩
  change (∑ j, fractionalNorm s p ⟨B.atlas.localizedLp p j (B.identify (T u)), hmem j⟩) ≤ _
  calc
    _ ≤ ∑ j, C j * ‖u‖ := Finset.sum_le_sum (fun j _ => hbound j)
    _ = _ := by rw [Finset.sum_mul]


abbrev scalarTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (θ : Tests ℝ (⊤ : Opens (Domain d))) : Tests 𝕜 (⊤ : Opens (Domain d)) :=
  Smoothing.liftRealTest θ

lemma tsupport_scalarTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (θ : Tests ℝ (⊤ : Opens (Domain d))) :
    tsupport (scalarTest (𝕜 := 𝕜) θ) ⊆ tsupport θ := by
  apply closure_mono
  intro x hx
  change (θ x : 𝕜) ≠ 0 at hx
  exact fun hz => hx (by rw [hz]; simp)

lemma domain_sharp_bound_of_smoothAtlas
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n + 1))}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (x₀ : frontier (Ω : Set (Domain (n + 1)))) (A : SmoothBoundaryAtlas Ω x₀) :
    let B := boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u, ∃ h : B.FiniteEnergy (1 - 1 / p.toReal) (T u),
        B.dataNorm (1 - 1 / p.toReal) ⟨T u, h⟩ ≤ C * ‖u‖ := by
  let B := boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas
  apply boundary_sharp_bound_of_chart_estimates B
  intro j
  rcases A.regular j with ⟨hΦ, hInv, hSource, _, hD, hDinv⟩
  apply localized_sharp_bound_of_chart hp1 hp B hdense j (A.normal j) x₀
    (A.ambient j) hΦ hInv A.derivativeBound A.derivativeBound_nonneg hD hDinv hSource
    (A.side j) (scalarTest (A.test j))
    ((tsupport_scalarTest (A.test j)).trans (A.test_subordinate j))
  · exact A.chart_eq j
  · intro x
    change (A.atlas.cutoff j x : 𝕜) = (A.test j x.val : 𝕜)
    exact congrArg (fun r : ℝ => (r : 𝕜)) (A.cutoff_eq j x)



/-- Expressed linearity of a fractional lift gives an actual bounded linear map
for the full fractional norm, rather than the topology inherited from Lp. -/
def fractionalLiftCLM {𝕜 : Type} [RCLike 𝕜] {n d : ℕ}
    {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    {Ω : Opens (Domain d)}
    (E : FractionalSpace 𝕜 n s p → SpaceValue 𝕜 d Ω 1 p)
    (hadd : ∀ u v w, w.val = u.val + v.val → E w = E u + E v)
    (hsmul : ∀ (c : 𝕜) u v, v.val = c • u.val → E v = c • E u)
    (C : ℝ) (hbound : ∀ u, ‖E u‖ ≤ C * fractionalNorm s p u) :
    FractionalSpace 𝕜 n s p →L[𝕜] SpaceValue 𝕜 d Ω 1 p :=
  LinearMap.mkContinuous
    { toFun := E
      map_add' u v := hadd u v (u + v) rfl
      map_smul' c u := hsmul c u (c • u) rfl }
    C hbound

@[simp] lemma fractionalLiftCLM_apply {𝕜 : Type} [RCLike 𝕜] {n d : ℕ}
    {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    {Ω : Opens (Domain d)}
    (E : FractionalSpace 𝕜 n s p → SpaceValue 𝕜 d Ω 1 p)
    (hadd : ∀ u v w, w.val = u.val + v.val → E w = E u + E v)
    (hsmul : ∀ (c : 𝕜) u v, v.val = c • u.val → E v = c • E u)
    (C : ℝ) (hbound : ∀ u, ‖E u‖ ≤ C * fractionalNorm s p u)
    (u : FractionalSpace 𝕜 n s p) :
    fractionalLiftCLM E hadd hsmul C hbound u = E u := rfl

/-- The accepted flat inverse, as a genuine continuous linear map for every
normal coordinate, with its original full-norm bound and trace identity. -/
theorem flat_lift_clm (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (p ≠ ∞)]
    (hp1 : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1)),
      ∃ E : FractionalSpace 𝕜 n (1 - 1 / p.toReal) p →L[𝕜]
          SpaceValue 𝕜 (n + 1) (upper i) 1 p,
        (∀ u, ‖E u‖ ≤ C * fractionalNorm (1 - 1 / p.toReal) p u) ∧
        (∀ (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
            Lp 𝕜 p (volume : Measure (Transverse i))), CoordinateTraceCondition i T →
          ∀ u, reindexedTrace i T (E u) = u.val) := by
  obtain ⟨C, hC, hE⟩ := SharpTraceExtension.bounded_right_inverse n p hp1 Fact.out
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ i
  obtain ⟨E, hadd, hsmul, hbound, htrace⟩ := hE 𝕜 i
  exact ⟨fractionalLiftCLM E hadd hsmul C hbound, hbound, htrace⟩



theorem domain_sharp_bound : Specs.ExpandedFA.PartIV.SharpTrace.DomainSharpBound := by
  intro 𝕜 _ d Ω hb hΩ p _ hp1 hp B
  have hc : IsCompact (frontier (Ω : Set (Domain d))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  let : CompactSpace (frontier (Ω : Set (Domain d))) := isCompact_iff_compactSpace.mp hc
  by_cases hf : frontier (Ω : Set (Domain d)) = ∅
  · exact domain_sharp_bound_of_empty_frontier hf hp B _
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hf
  cases d with
  | zero =>
    obtain ⟨i, _⟩ := hΩ x hx
    exact Fin.elim0 i
  | succ n =>
    let x₀ : frontier (Ω : Set (Domain (n + 1))) := ⟨x, hx⟩
    obtain ⟨A⟩ := exists_smoothBoundaryAtlas Ω hΩ hc x₀
    have hdense := C1Extension.smooth_density 𝕜 (n + 1) Ω hΩ hc p hp
    obtain ⟨hs0, hs1⟩ := endpoint_exponent hp1 hp
    exact (boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas).sharp_bound_of_model B
      (1 - 1 / p.toReal) hs0 hs1 hp (domain_sharp_bound_of_smoothAtlas hp1 hp hdense x₀ A)


open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.PartIV.FractionalSobolev
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Finite localized boundary classes reconstruct the original surface class
whenever their representatives form a partition on the actual frontier. -/
lemma boundary_model_partition_reconstruction {ι : Type*} [Fintype ι]
    (a : ι → Domain d → 𝕜)
    (hsum : ∀ x ∈ frontier (Ω : Set (Domain d)), ∑ j, a j x = 1)
    (g : BoundaryLp 𝕜 Ω p) (piece : ι → BoundaryLp 𝕜 Ω p)
    (hpiece : ∀ j, piece j =ᵐ[surfaceMeasure Ω] fun x => a j x * g x) :
    ∑ j, piece j = g := by
  classical
  apply Lp.ext
  have hall := ae_all_iff.mpr hpiece
  filter_upwards [Lp.coeFn_finsetSum Finset.univ piece, hall,
    surfaceMeasure_ae_frontier Ω] with x hsumlp hpieces hx
  simp only [Finset.sum_apply] at hsumlp
  rw [hsumlp]
  calc
    ∑ j, piece j x = ∑ j, a j x * g x :=
      Finset.sum_congr rfl (fun j _ => hpieces j)
    _ = (∑ j, a j x) * g x := (Finset.sum_mul _ _ _).symm
    _ = g x := by rw [hsum x hx, one_mul]

lemma boundary_model_partition_reconstruction_real {ι : Type*} [Fintype ι]
    (a : ι → Domain d → ℝ)
    (hsum : ∀ x ∈ frontier (Ω : Set (Domain d)), ∑ j, a j x = 1)
    (g : BoundaryLp 𝕜 Ω p) (piece : ι → BoundaryLp 𝕜 Ω p)
    (hpiece : ∀ j, piece j =ᵐ[surfaceMeasure Ω] fun x => (a j x : 𝕜) * g x) :
    ∑ j, piece j = g := by
  apply boundary_model_partition_reconstruction (fun j x => (a j x : 𝕜)) _ g piece hpiece
  intro x hx
  rw [← RCLike.ofReal_sum, hsum x hx, RCLike.ofReal_one]

lemma boundedLpMultiplyCLM_partition_sum {ι : Type*} [Fintype ι]
    (a : ι → Domain d → 𝕜)
    (ha : ∀ j, AEStronglyMeasurable (a j) (surfaceMeasure Ω))
    (C : ι → ℝ) (hC : ∀ j x, ‖a j x‖ ≤ C j)
    (hsum : ∀ x ∈ frontier (Ω : Set (Domain d)), ∑ j, a j x = 1)
    (g : BoundaryLp 𝕜 Ω p) :
    ∑ j, boundedLpMultiplyCLM (surfaceMeasure Ω) (a j) (ha j) (C j) (hC j) g = g := by
  apply boundary_model_partition_reconstruction a hsum g
  intro j
  exact boundedLpMultiplyCLM_coe (surfaceMeasure Ω) (a j) (ha j) (C j) (hC j) g

lemma boundedLpMultiplyCLM_partition_sum_real {ι : Type*} [Fintype ι]
    (a : ι → Domain d → ℝ)
    (ha : ∀ j, AEStronglyMeasurable (fun x => (a j x : 𝕜)) (surfaceMeasure Ω))
    (C : ι → ℝ) (hC : ∀ j x, ‖(a j x : 𝕜)‖ ≤ C j)
    (hsum : ∀ x ∈ frontier (Ω : Set (Domain d)), ∑ j, a j x = 1)
    (g : BoundaryLp 𝕜 Ω p) :
    ∑ j, boundedLpMultiplyCLM (surfaceMeasure Ω) (fun x => (a j x : 𝕜))
      (ha j) (C j) (hC j) g = g := by
  apply boundary_model_partition_reconstruction_real a hsum g
  intro j
  exact boundedLpMultiplyCLM_coe (surfaceMeasure Ω) (fun x => (a j x : 𝕜))
    (ha j) (C j) (hC j) g


namespace SmoothBoundaryAtlas
variable {n : ℕ} {Ω : Opens (Domain (n+1))}
  {x₀ : frontier (Ω : Set (Domain (n+1)))} (A : SmoothBoundaryAtlas Ω x₀)

/-- A global bound comes from the actual compactly supported ambient test.
The partition is normalized only on the boundary. -/
def boundaryPieceBound (j : Fin A.chartCount) : ℝ :=
  Classical.choose (ambient_test_bounds (A.test j))

lemma boundaryPieceBound_nonneg (j : Fin A.chartCount) : 0 ≤ A.boundaryPieceBound j :=
  (Classical.choose_spec (ambient_test_bounds (A.test j))).1

lemma boundaryPieceBound_bound (j : Fin A.chartCount) (x : Domain (n+1)) :
    ‖(A.test j x : 𝕜)‖ ≤ A.boundaryPieceBound j := by
  simpa only [boundaryPieceBound, RCLike.norm_ofReal, Real.norm_eq_abs] using
    (Classical.choose_spec (ambient_test_bounds (A.test j))).2.1 x

/-- The actual surface boundary partition piece, as a bounded scalar-linear map. -/
def boundaryPiece (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (j : Fin A.chartCount) : BoundaryLp 𝕜 Ω p →L[𝕜] BoundaryLp 𝕜 Ω p :=
  boundedLpMultiplyCLM (surfaceMeasure Ω) (fun x => (A.test j x : 𝕜))
    (RCLike.continuous_ofReal.comp (A.test j).continuous).aestronglyMeasurable
    (A.boundaryPieceBound j) (A.boundaryPieceBound_bound j)

lemma boundaryPiece_coe (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : Fin A.chartCount)
    (g : BoundaryLp 𝕜 Ω p) :
    A.boundaryPiece 𝕜 p j g =ᵐ[surfaceMeasure Ω] fun x => (A.test j x : 𝕜) * g x :=
  boundedLpMultiplyCLM_coe (surfaceMeasure Ω) (fun x => (A.test j x : 𝕜))
    (RCLike.continuous_ofReal.comp (A.test j).continuous).aestronglyMeasurable
    (A.boundaryPieceBound j) (A.boundaryPieceBound_bound j) g

lemma sum_boundaryPiece (p : ℝ≥0∞) [Fact (1 ≤ p)] (g : BoundaryLp 𝕜 Ω p) :
    ∑ j, A.boundaryPiece 𝕜 p j g = g :=
  boundary_model_partition_reconstruction_real (fun j => A.test j) A.test_sum g
    (fun j => A.boundaryPiece 𝕜 p j g) (fun j => A.boundaryPiece_coe p j g)

lemma boundaryPiece_supported (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : Fin A.chartCount)
    (g : BoundaryLp 𝕜 Ω p) :
    ∀ᵐ x ∂surfaceMeasure Ω, x ∉ tsupport (A.test j) → A.boundaryPiece 𝕜 p j g x = 0 := by
  filter_upwards [A.boundaryPiece_coe p j g] with x hx hxs
  rw [hx, image_eq_zero_of_notMem_tsupport hxs, RCLike.ofReal_zero, zero_mul]

lemma boundaryPiece_mul_eq (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : Fin A.chartCount)
    (g : BoundaryLp 𝕜 Ω p) (η : Domain (n+1) → 𝕜)
    (hη : ∀ x ∈ tsupport (A.test j), η x = 1) :
    (fun x => η x * A.boundaryPiece 𝕜 p j g x) =ᵐ[surfaceMeasure Ω]
      A.boundaryPiece 𝕜 p j g := by
  filter_upwards [A.boundaryPiece_coe p j g] with x hx
  by_cases hxs : x ∈ tsupport (A.test j)
  · rw [hη x hxs, one_mul]
  · rw [hx, image_eq_zero_of_notMem_tsupport hxs, RCLike.ofReal_zero, zero_mul, mul_zero]

lemma boundaryPiece_multiplier_eq (p : ℝ≥0∞) [Fact (1 ≤ p)] (j : Fin A.chartCount)
    (g : BoundaryLp 𝕜 Ω p) (η : Domain (n+1) → 𝕜)
    (hηmeas : AEStronglyMeasurable η (surfaceMeasure Ω))
    (C : ℝ) (hC : ∀ x, ‖η x‖ ≤ C)
    (hη : ∀ x ∈ tsupport (A.test j), η x = 1) :
    boundedLpMultiplyCLM (surfaceMeasure Ω) η hηmeas C hC
      (A.boundaryPiece 𝕜 p j g) = A.boundaryPiece 𝕜 p j g := by
  apply Lp.ext
  exact (boundedLpMultiplyCLM_coe (surfaceMeasure Ω) η hηmeas C hC
    (A.boundaryPiece 𝕜 p j g)).trans (A.boundaryPiece_mul_eq p j g η hη)

end SmoothBoundaryAtlas


open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n+1))}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma BoundaryModel.localizedLp_representative (B : BoundaryModel 𝕜 Ω p)
    (j : Fin B.chartCount) (g : BoundaryLp 𝕜 Ω p) :
    B.atlas.localizedLp p j (B.identify g) =ᵐ[volume]
      B.atlas.localizedRepresentative j (fun x => g x.val) :=
  (B.atlas.localizedLp_representative p j (B.identify g)).trans
    (B.atlas.localizedRepresentative_congr_ae j (B.representative g g EventuallyEq.rfl))

lemma frontierChart_symm_val
    (x₀ : frontier (Ω : Set (Domain (n+1))))
    (Φ : OpenPartialHomeomorph (Domain (n+1)) (Domain (n+1)))
    (i : Fin (n+1)) (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (z : Domain n) (hz : z ∈ boundaryParameters Φ i) :
    ((frontierChart Ω x₀ Φ i hside).symm z).val = boundaryParam Φ i z := by
  classical
  change Subtype.val (dite (z ∈ boundaryParameters Φ i) _ _) = _
  rw [dite_eq_left hz]

lemma SmoothBoundaryAtlas.localizedLp_representative
    {x₀ : frontier (Ω : Set (Domain (n+1)))} (A : SmoothBoundaryAtlas Ω x₀)
    (j : Fin A.chartCount) (g : BoundaryLp 𝕜 Ω p) :
    (boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas).atlas.localizedLp p j
      ((boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas).identify g) =ᵐ[
        volume.restrict (boundaryParameters (A.ambient j) (A.normal j))]
      fun z => (A.test j (boundaryParam (A.ambient j) (A.normal j) z) : 𝕜) *
        g (boundaryParam (A.ambient j) (A.normal j) z) := by
  let B := boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas
  have hr := (B.localizedLp_representative j g).restrict (s := boundaryParameters (A.ambient j) (A.normal j))
  filter_upwards [hr,
    ae_restrict_mem (boundaryParameters_isOpen (A.ambient j) (A.normal j)).measurableSet]
      with z hz hzV
  rw [hz]
  change A.atlas.localizedRepresentative j (fun x => g x.val) z = _
  unfold Boundary.FiniteAtlas.localizedRepresentative
  have hzT : z ∈ (A.atlas.chart j).target := by
    rw [A.chart_eq j]
    exact hzV
  rw [indicator_of_mem hzT, A.cutoff_eq, A.chart_eq j,
    frontierChart_symm_val x₀ (A.ambient j) (A.normal j) (A.side j) z hzV]
  dsimp only
  rw [frontierChart_symm_val x₀ (A.ambient j) (A.normal j) (A.side j) z hzV]

lemma SmoothBoundaryAtlas.localizedRepresentative_eq
    {x₀ : frontier (Ω : Set (Domain (n+1)))} (A : SmoothBoundaryAtlas Ω x₀)
    (j : Fin A.chartCount) (f : Domain (n+1) → 𝕜) :
    A.atlas.localizedRepresentative j (fun x => f x.val) =
      (boundaryParameters (A.ambient j) (A.normal j)).indicator
        (fun z => (A.test j (boundaryParam (A.ambient j) (A.normal j) z) : 𝕜) *
          f (boundaryParam (A.ambient j) (A.normal j) z)) := by
  classical
  funext z
  unfold Boundary.FiniteAtlas.localizedRepresentative
  have ht : (A.atlas.chart j).target = boundaryParameters (A.ambient j) (A.normal j) := by
    rw [A.chart_eq j]
    rfl
  rw [ht]
  by_cases hz : z ∈ boundaryParameters (A.ambient j) (A.normal j)
  · rw [indicator_of_mem hz, indicator_of_mem hz, A.cutoff_eq, A.chart_eq j,
      frontierChart_symm_val x₀ (A.ambient j) (A.normal j) (A.side j) z hz]
    dsimp only
    rw [frontierChart_symm_val x₀ (A.ambient j) (A.normal j) (A.side j) z hz]
  · rw [indicator_of_notMem hz, indicator_of_notMem hz]

lemma SmoothBoundaryAtlas.localizedLp_representative_global
    {x₀ : frontier (Ω : Set (Domain (n+1)))} (A : SmoothBoundaryAtlas Ω x₀)
    (j : Fin A.chartCount) (g : BoundaryLp 𝕜 Ω p) :
    (boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas).atlas.localizedLp p j
      ((boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas).identify g) =ᵐ[volume]
      (boundaryParameters (A.ambient j) (A.normal j)).indicator
        (fun z => (A.test j (boundaryParam (A.ambient j) (A.normal j) z) : 𝕜) *
          g (boundaryParam (A.ambient j) (A.normal j) z)) := by
  exact ((boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas).localizedLp_representative j g).trans
    (EventuallyEq.of_eq (A.localizedRepresentative_eq j g))

lemma SmoothBoundaryAtlas.localizedLp_eq_surfacePiece
    {x₀ : frontier (Ω : Set (Domain (n+1)))} (A : SmoothBoundaryAtlas Ω x₀)
    (j : Fin A.chartCount) (g : BoundaryLp 𝕜 Ω p)
    (C : ℝ) (hC : ∀ x, ‖(A.test j x : 𝕜)‖ ≤ C) :
    let θ := scalarTest (𝕜 := 𝕜) (A.test j)
    let b := boundedLpMultiplyCLM (surfaceMeasure Ω) θ
      θ.contDiff.continuous.aestronglyMeasurable C hC g
    (boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas).atlas.localizedLp p j
      ((boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas).identify g) =ᵐ[
        volume.restrict (boundaryParameters (A.ambient j) (A.normal j))]
      fun z => b (boundaryParam (A.ambient j) (A.normal j) z) := by
  dsimp only
  let Φ := A.ambient j
  let i := A.normal j
  obtain ⟨D, hD, hmap⟩ := boundaryParam_map_le_surfaceMeasure Ω Φ i (A.side j)
    (A.ambient_lipschitz j)
  have hac : (volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i) ≪
      surfaceMeasure Ω :=
    (Measure.absolutelyContinuous_of_le_smul hmap).trans Measure.restrict_le_self.absolutelyContinuous
  have hb := boundedLpMultiplyCLM_coe (surfaceMeasure Ω) (scalarTest (𝕜 := 𝕜) (A.test j))
    (scalarTest (𝕜 := 𝕜) (A.test j)).contDiff.continuous.aestronglyMeasurable C hC g
  have hpull := ae_of_ae_map (boundaryParam_aemeasurable Φ i) (hac.ae_eq hb)
  exact (A.localizedLp_representative j g).trans (Filter.EventuallyEq.symm hpull)


open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma boundaryPullback_surjective {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Function.Surjective (boundaryPullback (𝕜 := 𝕜) i p) := by
  intro g
  let e := boundaryCoordinates i
  have hpres := (boundaryCoordinates_measurePreserving i).symm e
  let h := Lp.compMeasurePreserving e.symm hpres g
  refine ⟨h, ?_⟩
  apply Lp.ext
  have hback := (boundaryCoordinates_measurePreserving i).quasiMeasurePreserving.ae_eq_comp
    (Lp.coeFn_compMeasurePreserving g hpres)
  filter_upwards [Lp.coeFn_compMeasurePreserving h (boundaryCoordinates_measurePreserving i), hback]
    with z hz hb
  change h (e z) = g (e.symm (e z)) at hb
  exact hz.trans (hb.trans (by rw [e.symm_apply_apply]))

lemma reindexedTrace_surjective_endpoint {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1))
    (S : SpaceValue 𝕜 (n + 1) (upper i) 1 1 →L[𝕜]
      Lp 𝕜 1 (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S) :
    Function.Surjective (reindexedTrace i S) := by
  intro g
  obtain ⟨h, hh⟩ := boundaryPullback_surjective i 1 g
  obtain ⟨u, hu⟩ := TraceEndpointOne.halfSpace_trace_surjective 𝕜 (n + 1) i S
    (fun u f hf hu => hS u f (hf.of_le (by simp)) hu) h
  refine ⟨u, ?_⟩
  change boundaryPullback i 1 (S u) = g
  rw [hu, hh]


end ExpandedFA.PartIV.SharpTrace
namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A continuous graph operator with a C1 multiplier representative has the
expected flat boundary multiplier. The coefficient need not be smooth. -/
lemma coordinate_trace_of_continuous_multiplier (i : Fin d) (hp : p ≠ ∞)
    (S : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)))
    (hS : IsCoordinateTrace i S)
    (a : Domain d → 𝕜) (ha : ContDiff ℝ 1 a)
    (C : ℝ) (hC : ∀ x, ‖a x‖ ≤ C)
    (M : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] SpaceValue 𝕜 d (upper i) 1 p)
    (hM : ∀ u, (M u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
      fun x => a x * u.val (zeroIndex d 1) x)
    (u : SpaceValue 𝕜 d (upper i) 1 p) :
    S (M u) =ᵐ[volume] fun y => a (coordinateLine i y 0) * S u y := by
  have hc : Continuous (fun y : Transverse i => coordinateLine i y 0) := by
    apply continuous_pi
    intro j
    dsimp [coordinateLine]
    split_ifs
    · exact continuous_const
    · exact continuous_apply _
  let B := boundedLpMultiplyCLM (p := p) (volume : Measure (Transverse i))
    (fun y => a (coordinateLine i y 0)) (ha.continuous.comp hc).aestronglyMeasurable C
    (fun y => hC _)
  have heq : EqOn (S.comp M) (B.comp S) (SmoothUpToBoundary (𝕜 := 𝕜) (upper i) p) := by
    rintro v ⟨f, hf, hv⟩
    have hMv : (M v).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun x => a x * f x := by
      filter_upwards [hM v, hv] with x hx hfx
      exact hx.trans (congrArg (a x * ·) hfx)
    apply Lp.ext
    filter_upwards [hS (M v) (a * f) (ha.mul (hf.of_le (by simp))) hMv,
      boundedLpMultiplyCLM_coe (volume : Measure (Transverse i))
        (fun y => a (coordinateLine i y 0)) (ha.continuous.comp hc).aestronglyMeasurable C
        (fun y => hC _) (S v),
      hS v f (hf.of_le (by simp)) hv] with y h₁ h₂ h₃
    change S (M v) y = B (S v) y
    rw [h₁, h₂, h₃]
    rfl
  have h := heq.closure (S.comp M).continuous (B.comp S).continuous
    (coordinate_upper_smooth_density (𝕜 := 𝕜) i hp u)
  change S (M u) = B (S u) at h
  rw [h]
  exact boundedLpMultiplyCLM_coe (volume : Measure (Transverse i))
    (fun y => a (coordinateLine i y 0)) (ha.continuous.comp hc).aestronglyMeasurable C
    (fun y => hC _) (S u)

/-- If the underlying Sobolev function is unchanged by an ambient cutoff,
the same cutoff fixes its boundary trace. -/
lemma trace_fixed_by_cutoff
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (η : Tests 𝕜 (⊤ : Opens (Domain d)))
    (u : SpaceValue 𝕜 d Ω 1 p)
    (hu : ∀ᵐ x ∂(volume.restrict (Ω : Set (Domain d))),
      η x * u.val (zeroIndex d 1) x = u.val (zeroIndex d 1) x) :
    T u =ᵐ[surfaceMeasure Ω] fun x => η x * T u x := by
  obtain ⟨C, hC0, hC, hD⟩ := ambient_test_bounds η
  let M := ambientMultiply (Ω := Ω) (p := p) η η.contDiff C hC0 hC hD
  have hMu : M u = u := by
    apply sobolev_underlying_injective 𝕜 d Ω 1 p
    apply Lp.ext
    exact (ambientMultiply_coe η η.contDiff C hC0 hC hD u).trans hu
  have htrace := trace_ambientMultiply Ω hdense T hT η η.contDiff C hC0 hC hD u
  change T (M u) =ᵐ[surfaceMeasure Ω] _ at htrace
  simpa only [hMu] using htrace

end ExpandedFA.PartIV.SharpTrace

namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Localized chart pushback has boundary support in the same chart source.
This uses only actual graph representatives and smooth trace density. -/
lemma localized_chart_pullback_trace_supported
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (Λ : Opens (Domain d))
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (θ : Tests 𝕜 (⊤ : Opens (Domain d))) (hθ : tsupport θ ⊆ Φ.source)
    (F : SpaceValue 𝕜 d Λ 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p)
    (hF : ∀ (u : SpaceValue 𝕜 d Λ 1 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Λ : Set (Domain d))] f →
      (F u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => θ x * f (Φ x))
    (u : SpaceValue 𝕜 d Λ 1 p) :
    ∀ᵐ x ∂(surfaceMeasure Ω), x ∉ Φ.source → T (F u) x = 0 := by
  obtain ⟨η, hη, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (tsupport θ) θ.hasCompactSupport ⟨Φ.source, Φ.open_source⟩ hθ
  have hfix := trace_fixed_by_cutoff hdense T hT η (F u) (by
    filter_upwards [hF u (u.val (zeroIndex d 1)) Filter.EventuallyEq.rfl] with x hx
    rw [hx]
    by_cases hxθ : x ∈ tsupport θ
    · rw [hηone x hxθ, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxθ, zero_mul, mul_zero])
  filter_upwards [hfix] with x hx hxs
  have hxη : x ∉ tsupport η := fun hh => hxs (hη hh)
  simpa only [image_eq_zero_of_notMem_tsupport hxη, zero_mul] using hx

end ExpandedFA.PartIV.SharpTrace

namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pulling back and then flattening is an actual C1 multiplier; the flat
trace formula follows without requiring a C1 agreement axiom for domain traces. -/
lemma coordinate_trace_flattening_pushback (i : Fin d) (hp : p ≠ ∞)
    (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (θ η χ : Tests 𝕜 (⊤ : Opens (Domain d))) (hχ : tsupport χ ⊆ Φ.target)
    (E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d (upper i) 1 p)
    (hE : ∀ (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      (E u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)))
    (F : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜] SpaceValue 𝕜 d Ω 1 p)
    (hF : ∀ (u : SpaceValue 𝕜 d (upper i) 1 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))] f →
      (F u).val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))]
        fun x => η x * f (Φ x))
    (S : SpaceValue 𝕜 d (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S)
    (u : SpaceValue 𝕜 d (upper i) 1 p) :
    S (E (F u)) =ᵐ[volume] fun y =>
      (χ (coordinateLine i y 0) *
        (θ (Φ.symm (coordinateLine i y 0)) * η (Φ.symm (coordinateLine i y 0)))) * S u y := by
  let a : Domain d → 𝕜 := fun y => χ y * (θ (Φ.symm y) * η (Φ.symm y))
  have ha : ContDiff ℝ 1 a :=
    contDiff_chart_cutoff_comp Φ hInv χ hχ (fun x => θ x * η x)
      ((θ.contDiff.mul η.contDiff).of_le (by simp))
  obtain ⟨Cχ, hCχ0, hCχ, _⟩ := ambient_test_bounds χ
  obtain ⟨Cθ, hCθ0, hCθ, _⟩ := ambient_test_bounds θ
  obtain ⟨Cη, hCη0, hCη, _⟩ := ambient_test_bounds η
  have hbound : ∀ y, ‖a y‖ ≤ Cχ * (Cθ * Cη) := by
    intro y
    dsimp [a]
    rw [norm_mul, norm_mul]
    exact mul_le_mul (hCχ _) (mul_le_mul (hCθ _) (hCη _) (norm_nonneg _) hCθ0)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCχ0
  have hEF : ∀ v, (E (F v)).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
      fun y => a y * v.val (zeroIndex d 1) y := by
    intro v
    have hFv := hF v (v.val (zeroIndex d 1)) Filter.EventuallyEq.rfl
    filter_upwards [hE (F v) (fun x => η x * v.val (zeroIndex d 1) (Φ x)) hFv] with y hy
    rw [hy]
    by_cases hyt : y ∈ Φ.target
    · rw [Φ.right_inv hyt]
      simp only [a]
      ring
    · have hyχ : y ∉ tsupport χ := fun hh => hyt (hχ hh)
      simp only [a, image_eq_zero_of_notMem_tsupport hyχ, zero_mul]
  exact coordinate_trace_of_continuous_multiplier i hp S hS a ha _ hbound (E.comp F) hEF u

end ExpandedFA.PartIV.SharpTrace

namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Flattening as a composition of the accepted arbitrary-representative
chart pullback and the actual domain multiplier. This exposes its formula for
all Sobolev elements, not only globally smooth input representatives. -/
lemma exists_flattened_localization_all_representatives
    (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    (θ χ : Tests 𝕜 (⊤ : Opens (Domain d))) (hχ : tsupport χ ⊆ Φ.target) :
    ∃ E : SpaceValue 𝕜 d Ω 1 p →L[𝕜] SpaceValue 𝕜 d (upper i) 1 p,
      ∀ (u : SpaceValue 𝕜 d Ω 1 p) (f : Domain d → 𝕜),
      u.val (zeroIndex d 1) =ᵐ[volume.restrict (Ω : Set (Domain d))] f →
      (E u).val (zeroIndex d 1) =ᵐ[volume.restrict (upper i : Set (Domain d))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)) := by
  obtain ⟨J, hJ1, hJbound⟩ := Transport.exists_det_bound_of_norm_bound (E := Domain d) B
  have hJ : ∀ x ∈ Φ.source, |(fderiv ℝ Φ x).det| ≤ J :=
    fun x hx => hJbound _ (hB x hx)
  have hsideInv : ∀ y ∈ Φ.symm.source, y ∈ upper i ↔ Φ.symm y ∈ Ω := by
    intro y hy
    have heq := hside (Φ.symm y) (Φ.map_target hy)
    change 0 < y i ↔ Φ.symm y ∈ Ω
    simpa only [Φ.right_inv hy] using heq.symm
  obtain ⟨G, hG⟩ := exists_localized_chart_pullback (Ω := upper i) (p := p)
    Ω Φ.symm hInv hΦ B hB0 hBinv J hJ1 hJ hSource hsideInv χ hχ
  obtain ⟨Cθ, hCθ0, hCθ, hDθ⟩ := ambient_test_bounds θ
  let Mθ := ambientMultiply (Ω := Ω) (p := p) θ θ.contDiff Cθ hCθ0 hCθ hDθ
  refine ⟨G.comp Mθ, ?_⟩
  intro u f hu
  apply hG (Mθ u) (fun x => θ x * f x)
  filter_upwards [ambientMultiply_coe θ θ.contDiff Cθ hCθ0 hCθ hDθ u, hu] with x hx hux
  exact hx.trans (congrArg (θ x * ·) hux)

end ExpandedFA.PartIV.SharpTrace

namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The original surface quotient is determined on one chart by its raw
parameter pullback and by its values outside the chart source. Both measure
domination directions are essential because Lp representatives need not be
pointwise measurable. -/
lemma boundary_eq_of_chart_pullback_eq
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (Ω : Opens (Domain (n + 1)))
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K L : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (hInvLip : LipschitzOnWith L Φ.symm Φ.target)
    (g h : BoundaryLp 𝕜 Ω p)
    (heq : (fun z => g (boundaryParam Φ i z)) =ᵐ[volume.restrict (boundaryParameters Φ i)]
      fun z => h (boundaryParam Φ i z))
    (houtside : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ Φ.source → g x = h x) :
    g = h := by
  let μ := volume.restrict (boundaryParameters Φ i)
  have hf : AEMeasurable (boundaryParam Φ i) μ := boundaryParam_aemeasurable Φ i
  obtain ⟨C, hC, hmap⟩ := boundaryParam_map_le_surfaceMeasure Ω Φ i hside hLip
  have hac : μ.map (boundaryParam Φ i) ≪ surfaceMeasure Ω :=
    Measure.absolutelyContinuous_of_le_smul
      (hmap.trans (smul_le_smul_left C Measure.restrict_le_self))
  have hg := Lp.aestronglyMeasurable g
  have hh := Lp.aestronglyMeasurable h
  have hgm := ae_of_ae_map hf (hac.ae_eq hg.ae_eq_mk)
  have hhm := ae_of_ae_map hf (hac.ae_eq hh.ae_eq_mk)
  have hmkcomp : (fun z => hg.mk g (boundaryParam Φ i z)) =ᵐ[μ]
      fun z => hh.mk h (boundaryParam Φ i z) := by
    filter_upwards [hgm, hhm, heq] with z hz₁ hz₂ hz₃
    exact hz₁.symm.trans (hz₃.trans hz₂)
  have hmkeq : hg.mk g =ᵐ[μ.map (boundaryParam Φ i)] hh.mk h :=
    (ae_map_iff hf (hg.stronglyMeasurable_mk.measurableSet_eq_fun
      hh.stronglyMeasurable_mk)).mpr hmkcomp
  obtain ⟨D, hD, hreverse⟩ := surfaceMeasure_chart_le_map Ω Φ i hside hInvLip
  have hacrev : (surfaceMeasure Ω).restrict Φ.source ≪ μ.map (boundaryParam Φ i) :=
    Measure.absolutelyContinuous_of_le_smul hreverse
  have hlocal : g =ᵐ[(surfaceMeasure Ω).restrict Φ.source] h :=
    (hg.ae_eq_mk.filter_mono (ae_mono Measure.restrict_le_self)).trans
      ((hacrev.ae_eq hmkeq).trans
        (hh.ae_eq_mk.filter_mono (ae_mono Measure.restrict_le_self)).symm)
  apply Lp.ext
  filter_upwards [(ae_restrict_iff' Φ.open_source.measurableSet).mp hlocal, houtside] with x hxin hxout
  by_cases hx : x ∈ Φ.source
  · exact hxin hx
  · exact hxout hx

end ExpandedFA.PartIV.SharpTrace

namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma flattened_trace_raw_boundary_formula
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (Ω : Opens (Domain (n + 1)))
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (θ χ : Tests 𝕜 (⊤ : Opens (Domain (n + 1))))
    (E : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] SpaceValue 𝕜 (n + 1) (upper i) 1 p)
    (hE : ∀ (u : SpaceValue 𝕜 (n + 1) Ω 1 p) (f : Domain (n + 1) → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))] f →
      ContDiff ℝ 1 (fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))) ∧
      (E u).val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)))
    (T : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (S : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S)
    (u : SpaceValue 𝕜 (n + 1) Ω 1 p) :
    reindexedTrace i S (E u) =ᵐ[volume.restrict (boundaryParameters Φ i)]
      fun z => (χ (i.insertNth 0 z) * θ (boundaryParam Φ i z)) * T u (boundaryParam Φ i z) := by
  let μ := volume.restrict (boundaryParameters Φ i)
  have hparam : AEMeasurable (boundaryParam Φ i) μ := boundaryParam_aemeasurable Φ i
  obtain ⟨D, hD, hmap⟩ := boundaryParam_map_le_surfaceMeasure Ω Φ i hside hLip
  have hdom : μ.map (boundaryParam Φ i) ≤ D • surfaceMeasure Ω :=
    hmap.trans (smul_le_smul_left D Measure.restrict_le_self)
  let P : BoundaryLp 𝕜 Ω p →L[𝕜] Lp 𝕜 p μ := Transport.pullLpCLM hparam hD.ne hdom
  have hid : AEMeasurable (id : Domain n → Domain n) μ := measurable_id.aemeasurable
  have hrestrict : μ.map (id : Domain n → Domain n) ≤ (1 : ℝ≥0∞) • volume := by
    simpa only [Measure.map_id, one_smul] using (Measure.restrict_le_self : μ ≤ volume)
  let R : Lp 𝕜 p (volume : Measure (Domain n)) →L[𝕜] Lp 𝕜 p μ :=
    Transport.pullLpCLM hid (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hrestrict
  let a : Domain n → 𝕜 := fun z => χ (i.insertNth 0 z) * θ (boundaryParam Φ i z)
  have ha : AEStronglyMeasurable a μ :=
    (χ.contDiff.continuous.comp (continuous_insertNth_zero i)).aestronglyMeasurable.mul
      (θ.contDiff.continuous.aestronglyMeasurable.comp_aemeasurable hparam)
  obtain ⟨Cχ, hCχ0, hCχ, _⟩ := ambient_test_bounds χ
  obtain ⟨Cθ, hCθ0, hCθ, _⟩ := ambient_test_bounds θ
  have hbound : ∀ z, ‖a z‖ ≤ Cχ * Cθ := by
    intro z
    exact (norm_mul _ _).le.trans (mul_le_mul (hCχ _) (hCθ _) (norm_nonneg _) hCχ0)
  let M : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ := boundedLpMultiplyCLM μ a ha (Cχ * Cθ) hbound
  let F := R.comp ((reindexedTrace i S).comp E)
  let G := M.comp (P.comp T)
  have heq : EqOn F G (SmoothUpToBoundary (𝕜 := 𝕜) Ω p) := by
    rintro v ⟨f, hf, hv⟩
    obtain ⟨hg, hEv⟩ := hE v f hf hv
    have hflat := (reindexedTrace_smooth i S hS (E v) _ hg hEv).filter_mono
      (ae_mono (show μ ≤ volume from Measure.restrict_le_self))
    have hpull := Transport.pullLp_coe_of_ae_eq hparam hD.ne hdom (T v) f (hT v f hf hv).symm
    change P (T v) =ᵐ[μ] f ∘ boundaryParam Φ i at hpull
    apply Lp.ext
    filter_upwards [Transport.pullLp_coe hid (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hrestrict
        (reindexedTrace i S (E v)), hflat,
      boundedLpMultiplyCLM_coe μ a ha (Cχ * Cθ) hbound (P (T v)), hpull] with z h₁ h₂ h₃ h₄
    change R (reindexedTrace i S (E v)) z = M (P (T v)) z
    change R (reindexedTrace i S (E v)) z = reindexedTrace i S (E v) z at h₁
    change M (P (T v)) z = _ at h₃
    rw [h₁, h₂, h₃, h₄]
    simp only [a, Function.comp_apply, boundaryParam]
    ring
  have h := heq.closure F.continuous G.continuous (hdense u)
  change R (reindexedTrace i S (E u)) = M (P (T u)) at h
  have hleft := Transport.pullLp_coe hid (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hrestrict
    (reindexedTrace i S (E u))
  have hright := boundedLpMultiplyCLM_coe μ a ha (Cχ * Cθ) hbound (P (T u))
  have hpull := Transport.pullLp_coe hparam hD.ne hdom (T u)
  change P (T u) =ᵐ[μ] (T u) ∘ boundaryParam Φ i at hpull
  filter_upwards [hleft, hright, hpull] with z h₁ h₂ h₃
  change R (reindexedTrace i S (E u)) z = reindexedTrace i S (E u) z at h₁
  change M (P (T u)) z = _ at h₂
  exact h₁.symm.trans (by rw [h, h₂, h₃]; rfl)

end ExpandedFA.PartIV.SharpTrace

namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma reindexed_trace_multiplier_of_ae
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (i : Fin (n + 1))
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (S : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i)))
    (a : Domain (n + 1) → 𝕜)
    (u v : SpaceValue 𝕜 (n + 1) (upper i) 1 p)
    (h : S v =ᵐ[volume] fun y => a (coordinateLine i y 0) * S u y) :
    reindexedTrace i S v =ᵐ[volume] fun z => a (i.insertNth 0 z) * reindexedTrace i S u z := by
  have hcomp := (boundaryCoordinates_measurePreserving i).quasiMeasurePreserving.ae_eq_comp h
  have hv := Lp.coeFn_compMeasurePreserving (S v) (boundaryCoordinates_measurePreserving i)
  have hu := Lp.coeFn_compMeasurePreserving (S u) (boundaryCoordinates_measurePreserving i)
  filter_upwards [hcomp, hv, hu] with z hz hzv hzu
  change reindexedTrace i S v z = S v (transverseFinEquiv i z) at hzv
  change reindexedTrace i S u z = S u (transverseFinEquiv i z) at hzu
  change S v (transverseFinEquiv i z) =
    a (coordinateLine i (transverseFinEquiv i z) 0) * S u (transverseFinEquiv i z) at hz
  rw [coordinateLine_transverseFinEquiv] at hz
  rw [hzv, hzu]
  exact hz

/-- Full inverse chart naturality for the genuine surface trace. The
auxiliary cutoff removes the need to assert C1 agreement for IsTrace. -/
lemma localized_chart_pullback_trace_formula
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (Ω : Opens (Domain (n + 1)))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (η : Tests 𝕜 (⊤ : Opens (Domain (n + 1)))) (hη : tsupport η ⊆ Φ.source)
    (F : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜] SpaceValue 𝕜 (n + 1) Ω 1 p)
    (hF : ∀ (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) (f : Domain (n + 1) → 𝕜),
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))] f →
      (F u).val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))]
        fun x => η x * f (Φ x))
    (T : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (S : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S)
    (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) :
    (fun z => T (F u) (boundaryParam Φ i z)) =ᵐ[volume.restrict (boundaryParameters Φ i)]
      fun z => η (boundaryParam Φ i z) * reindexedTrace i S u z := by
  obtain ⟨θ, hθ, hθone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
    (tsupport η) η.hasCompactSupport ⟨Φ.source, Φ.open_source⟩ hη
  obtain ⟨χ, hχ, hχone⟩ := exists_chart_cutoff Φ θ hθ
  obtain ⟨E, hE⟩ := exists_flattened_localization_all_representatives (Ω := Ω) (p := p) i Φ hΦ hInv B hB0
    hB hBinv hSource hside θ χ hχ
  have hEsmooth : ∀ (v : SpaceValue 𝕜 (n + 1) Ω 1 p) (f : Domain (n + 1) → 𝕜),
      ContDiff ℝ (⊤ : ℕ∞) f →
      v.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))] f →
      ContDiff ℝ 1 (fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y))) ∧
      (E v).val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))]
        fun y => χ y * (θ (Φ.symm y) * f (Φ.symm y)) := by
    intro v f hf hv
    exact ⟨contDiff_chart_cutoff_comp Φ hInv χ hχ (fun x => θ x * f x)
      ((θ.contDiff.mul hf).of_le (by simp)), hE v f hv⟩
  have hraw := flattened_trace_raw_boundary_formula Ω hdense Φ i hside hLip θ χ E hEsmooth T hT S hS (F u)
  have hcomp := reindexed_trace_multiplier_of_ae i S
    (fun y => χ y * (θ (Φ.symm y) * η (Φ.symm y))) u (E (F u))
    (coordinate_trace_flattening_pushback i hp Φ hInv θ η χ hχ E hE F hF S hS u)
  have hcomp' := hcomp.filter_mono
    (ae_mono (show volume.restrict (boundaryParameters Φ i) ≤ volume from Measure.restrict_le_self))
  have hfix := trace_fixed_by_cutoff hdense T hT θ (F u) (by
    filter_upwards [hF u (u.val (zeroIndex (n + 1) 1)) Filter.EventuallyEq.rfl] with x hx
    rw [hx]
    by_cases hxη : x ∈ tsupport η
    · rw [hθone x hxη, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxη, zero_mul, mul_zero])
  obtain ⟨D, hD, hmap⟩ := boundaryParam_map_le_surfaceMeasure Ω Φ i hside hLip
  have hac : (volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i) ≪ surfaceMeasure Ω :=
    Measure.absolutelyContinuous_of_le_smul
      (hmap.trans (smul_le_smul_left D Measure.restrict_le_self))
  have hfixparam := ae_of_ae_map (boundaryParam_aemeasurable Φ i) (hac.ae_eq hfix)
  filter_upwards [hraw, hcomp', hfixparam,
    ae_restrict_mem (boundaryParameters_isOpen Φ i).measurableSet] with z hzraw hzcomp hzfix hz
  have hχθ : χ (i.insertNth 0 z) * θ (boundaryParam Φ i z) * T (F u) (boundaryParam Φ i z) =
      T (F u) (boundaryParam Φ i z) := by
    by_cases hzθ : θ (boundaryParam Φ i z) = 0
    · simpa only [hzθ, zero_mul, mul_zero] using hzfix.symm
    · have hχz := hχone _ (subset_tsupport θ hzθ)
      change χ (Φ (Φ.symm (i.insertNth 0 z))) = 1 at hχz
      rw [Φ.right_inv hz] at hχz
      rw [mul_assoc, ← hzfix, hχz, one_mul]
  have hχη : χ (i.insertNth 0 z) * (θ (boundaryParam Φ i z) * η (boundaryParam Φ i z)) =
      η (boundaryParam Φ i z) := by
    by_cases hzη : η (boundaryParam Φ i z) = 0
    · simp only [hzη, mul_zero]
    · have hθz := hθone _ (subset_tsupport η hzη)
      have hχz := hχone (boundaryParam Φ i z) (subset_tsupport θ
        (show θ (boundaryParam Φ i z) ≠ 0 by rw [hθz]; exact one_ne_zero))
      change χ (Φ (Φ.symm (i.insertNth 0 z))) = 1 at hχz
      rw [Φ.right_inv hz] at hχz
      rw [hθz, hχz, one_mul, one_mul]
  rw [hχθ] at hzraw
  change reindexedTrace i S (E (F u)) z =
    (χ (i.insertNth 0 z) * (θ (boundaryParam Φ i z) * η (boundaryParam Φ i z))) *
      reindexedTrace i S u z at hzcomp
  rw [hχη] at hzcomp
  exact hzraw.symm.trans hzcomp

end ExpandedFA.PartIV.SharpTrace

namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma localized_chart_pullback_trace_eq
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (Ω : Opens (Domain (n + 1)))
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (Φ : OpenPartialHomeomorph (Domain (n + 1)) (Domain (n + 1))) (i : Fin (n + 1))
    (hΦ : ContDiffOn ℝ 1 Φ Φ.source) (hInv : ContDiffOn ℝ 1 Φ.symm Φ.target)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ x ∈ Φ.source, ‖fderiv ℝ Φ x‖ ≤ B)
    (hBinv : ∀ x ∈ Φ.target, ‖fderiv ℝ Φ.symm x‖ ≤ B)
    (hSource : Bornology.IsBounded Φ.source)
    (hside : ∀ x ∈ Φ.source, x ∈ Ω ↔ 0 < Φ x i)
    {K L : ℝ≥0} (hLip : LipschitzOnWith K Φ Φ.source)
    (hInvLip : LipschitzOnWith L Φ.symm Φ.target)
    (η : Tests 𝕜 (⊤ : Opens (Domain (n + 1)))) (hη : tsupport η ⊆ Φ.source)
    (F : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜] SpaceValue 𝕜 (n + 1) Ω 1 p)
    (hF : ∀ (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) (f : Domain (n + 1) → 𝕜),
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))] f →
      (F u).val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n + 1)))]
        fun x => η x * f (Φ x))
    (T : SpaceValue 𝕜 (n + 1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p) (hT : IsTrace T)
    (S : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) (hS : IsCoordinateTrace i S)
    (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) (g : BoundaryLp 𝕜 Ω p)
    (hfix : ∀ᵐ x ∂surfaceMeasure Ω, η x * g x = g x)
    (houtside : ∀ᵐ x ∂surfaceMeasure Ω, x ∉ Φ.source → g x = 0)
    (hflat : reindexedTrace i S u =ᵐ[volume.restrict (boundaryParameters Φ i)]
      fun z => g (boundaryParam Φ i z)) :
    T (F u) = g := by
  have hraw := localized_chart_pullback_trace_formula Ω hp hdense Φ i hΦ hInv B hB0 hB hBinv
    hSource hside hLip η hη F hF T hT S hS u
  obtain ⟨D, hD, hmap⟩ := boundaryParam_map_le_surfaceMeasure Ω Φ i hside hLip
  have hac : (volume.restrict (boundaryParameters Φ i)).map (boundaryParam Φ i) ≪ surfaceMeasure Ω :=
    Measure.absolutelyContinuous_of_le_smul
      (hmap.trans (smul_le_smul_left D Measure.restrict_le_self))
  have hfixparam := ae_of_ae_map (boundaryParam_aemeasurable Φ i) (hac.ae_eq hfix)
  apply boundary_eq_of_chart_pullback_eq Ω Φ i hside hLip hInvLip (T (F u)) g
  · filter_upwards [hraw, hflat, hfixparam] with z hz₁ hz₂ hz₃
    exact hz₁.trans ((congrArg (η (boundaryParam Φ i z) * ·) hz₂).trans hz₃)
  · have hsupport := localized_chart_pullback_trace_supported hdense T hT (upper i) Φ η hη F hF u
    filter_upwards [hsupport, houtside] with x hx₁ hx₂ hxout
    exact (hx₁ hxout).trans (hx₂ hxout).symm

end ExpandedFA.PartIV.SharpTrace

namespace ExpandedFA.PartIV.SharpTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.Trace ExpandedFA.Sobolev.C1Extension
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

lemma SmoothBoundaryAtlas.localizedLp_eq_boundaryPiece
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n+1))}
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {x₀ : frontier (Ω : Set (Domain (n+1)))} (A : SmoothBoundaryAtlas Ω x₀)
    (j : Fin A.chartCount) (g : BoundaryLp 𝕜 Ω p) :
    (boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas).atlas.localizedLp p j
      ((boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas).identify g) =ᵐ[
        volume.restrict (boundaryParameters (A.ambient j) (A.normal j))]
      fun z => A.boundaryPiece 𝕜 p j g (boundaryParam (A.ambient j) (A.normal j) z) := by
  obtain ⟨D, hD, hmap⟩ := boundaryParam_map_le_surfaceMeasure Ω (A.ambient j) (A.normal j)
    (A.side j) (A.ambient_lipschitz j)
  have hac : (volume.restrict (boundaryParameters (A.ambient j) (A.normal j))).map
      (boundaryParam (A.ambient j) (A.normal j)) ≪ surfaceMeasure Ω :=
    (Measure.absolutelyContinuous_of_le_smul hmap).trans Measure.restrict_le_self.absolutelyContinuous
  have hpull := ae_of_ae_map (boundaryParam_aemeasurable (A.ambient j) (A.normal j))
    (hac.ae_eq (A.boundaryPiece_coe p j g))
  exact (A.localizedLp_representative j g).trans (Filter.EventuallyEq.symm hpull)

lemma domain_right_inverse_of_smoothAtlas
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n + 1))}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ∞)
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω p))
    (x₀ : frontier (Ω : Set (Domain (n + 1)))) (A : SmoothBoundaryAtlas Ω x₀) :
    let B := boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas
    ∃ (C : ℝ) (E : B.Data (1 - 1 / p.toReal) → SpaceValue 𝕜 (n+1) Ω 1 p),
      0 ≤ C ∧
      (∀ u v w, w.val = u.val + v.val → E w = E u + E v) ∧
      (∀ (c : 𝕜) u v, v.val = c • u.val → E v = c • E u) ∧
      (∀ u, ‖E u‖ ≤ C * B.dataNorm (1 - 1 / p.toReal) u) ∧
      (∀ (T : SpaceValue 𝕜 (n+1) Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
        ∀ u, T (E u) = u.val) := by
  classical
  let : Fact (p ≠ ∞) := ⟨hp⟩
  let s := 1 - 1 / p.toReal
  let B := boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas
  obtain ⟨C, hC, hall⟩ := flat_lift_clm n p hp1
  choose E hEbound hEtrace using fun j : Fin A.chartCount => hall 𝕜 (A.normal j)
  choose η hη hηone using fun j : Fin A.chartCount =>
    exists_compact_ambient_cutoff (𝕜 := 𝕜) (tsupport (A.test j))
      (A.test j).hasCompactSupport ⟨(A.ambient j).source, (A.ambient j).open_source⟩
      (A.test_subordinate j)
  obtain ⟨J, hJ1, hJ⟩ := Transport.exists_det_bound_of_norm_bound (E := Domain (n+1))
    A.derivativeBound
  have hFall (j : Fin A.chartCount) :
      ∃ F : SpaceValue 𝕜 (n+1) (upper (A.normal j)) 1 p →L[𝕜] SpaceValue 𝕜 (n+1) Ω 1 p,
        ∀ (u : SpaceValue 𝕜 (n+1) (upper (A.normal j)) 1 p) (f : Domain (n+1) → 𝕜),
          u.val (zeroIndex (n+1) 1) =ᵐ[volume.restrict (upper (A.normal j) : Set (Domain (n+1)))] f →
          (F u).val (zeroIndex (n+1) 1) =ᵐ[volume.restrict (Ω : Set (Domain (n+1)))]
            fun x => η j x * f (A.ambient j x) := by
    rcases A.regular j with ⟨hΦ, hInv, _, hTarget, hD, hDinv⟩
    exact exists_localized_chart_pullback (Ω := Ω) (upper (A.normal j)) (A.ambient j)
      hΦ hInv A.derivativeBound A.derivativeBound_nonneg hD J hJ1
      (fun y hy => hJ _ (hDinv y hy)) hTarget (A.side j) (η j) (hη j)
  choose F hF using hFall
  let Q : Fin B.chartCount → FractionalSpace 𝕜 n s p →L[𝕜] SpaceValue 𝕜 (n+1) Ω 1 p :=
    fun j => (F j).comp (E j)
  apply B.bounded_right_inverse_of_local_maps s Q
  intro T hT u
  have hj (j : Fin A.chartCount) :
      T (Q j (B.localizedFractional s u j)) = A.boundaryPiece 𝕜 p j u.val := by
    obtain ⟨S, hS, _⟩ := coordinate_upper_trace_exists (𝕜 := 𝕜) (i := A.normal j) hp
    rcases A.regular j with ⟨hΦ, hInv, hSource, _, hD, hDinv⟩
    apply localized_chart_pullback_trace_eq Ω hp hdense (A.ambient j) (A.normal j)
      hΦ hInv A.derivativeBound A.derivativeBound_nonneg hD hDinv hSource
      (A.side j) (A.ambient_lipschitz j) (A.ambientSymm_lipschitz j)
      (η j) (hη j) (F j) (hF j) T hT S hS (E j (B.localizedFractional s u j))
      (A.boundaryPiece 𝕜 p j u.val)
    · exact A.boundaryPiece_mul_eq p j u.val (η j) (hηone j)
    · filter_upwards [A.boundaryPiece_supported p j u.val] with x hx hxout
      exact hx (fun hxs => hxout (A.test_subordinate j hxs))
    · have h := hEtrace j S hS (B.localizedFractional s u j)
      rw [h]
      exact A.localizedLp_eq_boundaryPiece j u.val
  calc
    (∑ j, T (Q j (B.localizedFractional s u j))) = ∑ j, A.boundaryPiece 𝕜 p j u.val :=
      Finset.sum_congr rfl (fun j _ => hj j)
    _ = u.val := A.sum_boundaryPiece p u.val

theorem domain_right_inverse : Specs.ExpandedFA.PartIV.SharpTrace.DomainRightInverse := by
  intro 𝕜 _ d Ω hb hΩ p _ hp1 hp B
  have hc : IsCompact (frontier (Ω : Set (Domain d))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  let : CompactSpace (frontier (Ω : Set (Domain d))) := isCompact_iff_compactSpace.mp hc
  by_cases hf : frontier (Ω : Set (Domain d)) = ∅
  · exact domain_right_inverse_of_empty_frontier hf hp B _
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hf
  cases d with
  | zero =>
    obtain ⟨i, _⟩ := hΩ x hx
    exact Fin.elim0 i
  | succ n =>
    let x₀ : frontier (Ω : Set (Domain (n + 1))) := ⟨x, hx⟩
    obtain ⟨A⟩ := exists_smoothBoundaryAtlas Ω hΩ hc x₀
    have hdense := C1Extension.smooth_density 𝕜 (n + 1) Ω hΩ hc p hp
    obtain ⟨hs0, hs1⟩ := endpoint_exponent hp1 hp
    exact (boundaryModelFromAtlas (𝕜 := 𝕜) Ω p A.atlas).bounded_right_inverse_of_model B
      (1 - 1 / p.toReal) hs0 hs1 hp (domain_right_inverse_of_smoothAtlas hp1 hp hdense x₀ A)



lemma domain_endpoint_of_smoothAtlas
    {𝕜 : Type} [RCLike 𝕜] {n : ℕ} {Ω : Opens (Domain (n + 1))}
    (hdense : Dense (SmoothUpToBoundary (𝕜 := 𝕜) Ω 1))
    (x₀ : frontier (Ω : Set (Domain (n + 1)))) (A : SmoothBoundaryAtlas Ω x₀)
    (T : SpaceValue 𝕜 (n + 1) Ω 1 1 →L[𝕜] BoundaryLp 𝕜 Ω 1) (hT : IsTrace T) :
    Function.Surjective T := by
  classical
  intro g
  have hlocal (j : Fin A.chartCount) :
      ∃ u : SpaceValue 𝕜 (n + 1) Ω 1 1, T u = A.boundaryPiece 𝕜 1 j g := by
    rcases A.regular j with ⟨hΦ, hInv, hSource, hTarget, hD, hDinv⟩
    obtain ⟨η, hη, hηone⟩ := exists_compact_ambient_cutoff (𝕜 := 𝕜)
      (tsupport (A.test j)) (A.test j).hasCompactSupport
      ⟨(A.ambient j).source, (A.ambient j).open_source⟩ (A.test_subordinate j)
    obtain ⟨J, hJ1, hJbound⟩ := Transport.exists_det_bound_of_norm_bound
      (E := Domain (n + 1)) A.derivativeBound
    obtain ⟨F, hF⟩ := exists_localized_chart_pullback (Ω := Ω) (p := (1 : ℝ≥0∞))
      (upper (A.normal j)) (A.ambient j) hΦ hInv A.derivativeBound
      A.derivativeBound_nonneg hD J hJ1 (fun x hx => hJbound _ (hDinv x hx))
      hTarget (A.side j) η hη
    obtain ⟨S, hS, _⟩ := coordinate_upper_trace_exists (𝕜 := 𝕜) (A.normal j) (by simp : (1 : ℝ≥0∞) ≠ ∞)
    let B := boundaryModelFromAtlas (𝕜 := 𝕜) Ω 1 A.atlas
    let datum := B.atlas.localizedLp 1 j (B.identify g)
    obtain ⟨v, hv⟩ := reindexedTrace_surjective_endpoint (A.normal j) S hS datum
    refine ⟨F v, localized_chart_pullback_trace_eq Ω (by simp) hdense (A.ambient j)
      (A.normal j) hΦ hInv A.derivativeBound A.derivativeBound_nonneg hD hDinv
      hSource (A.side j) (A.ambient_lipschitz j) (A.ambientSymm_lipschitz j)
      η hη F hF T hT S hS v (A.boundaryPiece 𝕜 1 j g)
      (A.boundaryPiece_mul_eq 1 j g η hηone) ?_ ?_⟩
    · filter_upwards [A.boundaryPiece_supported 1 j g] with x hx hxout
      exact hx (fun h => hxout (A.test_subordinate j h))
    · rw [hv]
      exact A.localizedLp_eq_surfacePiece j g (A.boundaryPieceBound j)
        (A.boundaryPieceBound_bound j)
  choose u hu using hlocal
  refine ⟨∑ j, u j, ?_⟩
  rw [map_sum]
  simp_rw [hu]
  exact A.sum_boundaryPiece 1 g

theorem domain_endpoint : Specs.ExpandedFA.PartIV.SharpTrace.DomainEndpoint := by
  intro 𝕜 _ d Ω hb hΩ T hT
  have hc : IsCompact (frontier (Ω : Set (Domain d))) :=
    hb.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  by_cases hf : frontier (Ω : Set (Domain d)) = ∅
  · apply domain_endpoint_of_surfaceMeasure_zero (Ω := Ω) _ T
    simp [surfaceMeasure, hf]
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hf
  cases d with
  | zero =>
    obtain ⟨i, _⟩ := hΩ x hx
    exact Fin.elim0 i
  | succ n =>
    let x₀ : frontier (Ω : Set (Domain (n + 1))) := ⟨x, hx⟩
    obtain ⟨A⟩ := exists_smoothBoundaryAtlas Ω hΩ hc x₀
    have hdense := C1Extension.smooth_density 𝕜 (n + 1) Ω hΩ hc 1 (by simp)
    exact domain_endpoint_of_smoothAtlas hdense x₀ A T hT


/-- Once the explicitly named domain transport obligations are proved,
the other parts come from the genuine traces and the kernel proof above. -/
theorem sharp_trace_assembly : Specs.ExpandedFA.PartIV.SharpTrace.Assembly := by
  intro hModels hBound hLift hEndpoint
  exact ⟨halfSpace_bound_and_lift, halfSpace_onto, halfSpace_endpoint,
    halfSpace_kernel, trace_exists, hModels, hBound, hLift, hEndpoint, domain_kernel⟩

/-- Complete sharp first trace theorem on half-spaces and bounded C1 domains,
with the endpoint range and the original compact-test closure kernels. -/
theorem sharp_trace : Specs.ExpandedFA.PartIV.SharpTrace.SharpTrace :=
  sharp_trace_assembly boundary_models_exist domain_sharp_bound domain_right_inverse domain_endpoint

end ExpandedFA.PartIV.SharpTrace
