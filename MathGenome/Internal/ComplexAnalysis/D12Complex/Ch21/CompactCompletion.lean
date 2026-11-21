import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.CompactCompletion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.CyclicParameters
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.FiniteEndGluing
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.AnalyticEndPasting
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.MonodromyTransitive
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.MapsMultiplicity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.AlgebraicGrowth
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.LocalQuotientsArithmetic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace

/-! The finite-branch completion (paper.tex:3689–3718).
The literal algebraic covering is completed by its actual cyclic ends. We
construct the attachment data, extend the old complex structure and both
coordinate functions, and exhibit a finite compact cover by the old core
and closed parameter disks.
-/

noncomputable section
open Set Polynomial
open scoped Topology

namespace D12Complex.CompactCompletion
open D12Complex.AlgebraicCovering

/-- The defining bivariate polynomial is continuous in its literal two coordinates. -/
theorem continuous_fiber_eval (P : Polynomial (Polynomial ℂ)) :
    Continuous (fun x : ℂ × ℂ => (fiber P x.1).eval x.2) := by
  have h (x : ℂ × ℂ) : (fiber P x.1).eval x.2 =
      ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j).eval x.1 * x.2 ^ j := by
    simp only [fiber, Specs.D12Complex.Ch21.FiniteExceptionalSet.fiber_value,
      Polynomial.eval_map, Polynomial.eval₂_eq_sum_range, Polynomial.coe_evalRingHom]
  simp_rw [h]
  apply continuous_finsetSum
  intro j hj
  exact ((P.coeff j).continuous.comp continuous_fst).mul (continuous_snd.pow j)

/-- A uniform root bound on any compact set where the leading coefficient does not vanish. -/
theorem exists_uniform_root_bound (P : Polynomial (Polynomial ℂ)) {K : Set ℂ}
    (hK : IsCompact K) (hlead : ∀ z ∈ K, P.leadingCoeff.eval z ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ w : ℂ, (fiber P z).eval w = 0 → ‖w‖ ≤ R := by
  let B : ℂ → ℝ := fun z =>
    ∑ j ∈ Finset.range P.natDegree, ‖(P.coeff j).eval z / P.leadingCoeff.eval z‖
  have hBc : ContinuousOn B K := by
    apply continuousOn_finsetSum
    intro j hj
    exact ((P.coeff j).continuous.continuousOn.div
      P.leadingCoeff.continuous.continuousOn hlead).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hBc
  refine ⟨1 + max C 0, by positivity, fun z hz w hw => ?_⟩
  apply D12Complex.AlgebraicGrowth.fiber_root_norm_le (hlead z hz) hw (le_max_right C 0)
  intro j hj
  have hterm : ‖(P.coeff j).eval z / P.leadingCoeff.eval z‖ ≤ B z :=
    Finset.single_le_sum (f := fun i => ‖(P.coeff i).eval z / P.leadingCoeff.eval z‖)
      (fun i _ => norm_nonneg _) (Finset.mem_range.mpr hj)
  exact hterm.trans ((le_abs_self (B z)).trans ((hC z hz).trans (le_max_left C 0)))

/-- Roots above a compact set form a compact subset of the original affine plane. -/
theorem isCompact_affine_preimage (P : Polynomial (Polynomial ℂ)) {K : Set ℂ}
    (hK : IsCompact K) (hlead : ∀ z ∈ K, P.leadingCoeff.eval z ≠ 0) :
    IsCompact {x : ℂ × ℂ | x.1 ∈ K ∧ (fiber P x.1).eval x.2 = 0} := by
  obtain ⟨R, hR, hbound⟩ := exists_uniform_root_bound P hK hlead
  have hclosed : IsClosed {x : ℂ × ℂ | x.1 ∈ K ∧ (fiber P x.1).eval x.2 = 0} :=
    (hK.isClosed.preimage continuous_fst).inter
      (isClosed_eq (continuous_fiber_eval P) continuous_const)
  apply (hK.prod (isCompact_closedBall (0 : ℂ) R)).of_isClosed_subset hclosed
  intro x hx
  exact ⟨hx.1, by simpa [Metric.mem_closedBall, dist_zero_right] using hbound x.1 hx.1 x.2 hx.2⟩

/-- The old covering over any compact subset of its good base is compact. -/
theorem isCompact_curve_preimage (P : Polynomial (Polynomial ℂ)) {K : Set ℂ}
    (hK : IsCompact K) (hgood : K ⊆ baseSet P) :
    IsCompact {x : Curve P | x.val.1 ∈ K} := by
  have hlead : ∀ z ∈ K, P.leadingCoeff.eval z ≠ 0 := by
    intro z hz
    have h := hgood hz
    change (P.leadingCoeff *
      Specs.D12Complex.Ch21.FiniteExceptionalSet.resultantPolynomial_value P).eval z ≠ 0 at h
    rw [Polynomial.eval_mul] at h
    exact (mul_ne_zero_iff.mp h).1
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  convert isCompact_affine_preimage P hK hlead using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property.2⟩
  · intro hx
    exact ⟨⟨x, hgood hx.1, hx.2⟩, hx.1, rfl⟩

/-- The same compactness statement expressed using the literal covering projection. -/
theorem isCompact_projection_preimage (P : Polynomial (Polynomial ℂ))
    {K : Set (Base P)} (hK : IsCompact K) :
    IsCompact (projection P ⁻¹' K) := by
  have hbase : IsCompact ((↑) '' K : Set ℂ) := hK.image continuous_subtype_val
  have hgood : ((↑) '' K : Set ℂ) ⊆ baseSet P := by
    rintro z ⟨a, ha, rfl⟩
    exact a.property
  convert isCompact_curve_preimage P hbase hgood using 1
  ext x
  change projection P x ∈ K ↔ x.val.1 ∈ ((↑) '' K : Set ℂ)
  constructor
  · intro hx
    exact ⟨projection P x, hx, rfl⟩
  · rintro ⟨a, ha, hax⟩
    have heq : a = projection P x := Subtype.ext hax
    exact heq ▸ ha

/-- Every finite base value with nonzero leading coefficient has finitely many roots. -/
theorem finite_fiber_roots (P : Polynomial (Polynomial ℂ)) {a : ℂ}
    (hlead : P.leadingCoeff.eval a ≠ 0) :
    Set.Finite {w : ℂ | (fiber P a).eval w = 0} := by
  apply Polynomial.finite_setOfPred_isRoot
  apply Polynomial.leadingCoeff_ne_zero.mp
  change (P.map (Polynomial.evalRingHom a)).leadingCoeff ≠ 0
  rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hlead]
  exact hlead

/-- Fill the center of a meromorphic punctured-disk parameter, preserving every
original value away from the center. Poles acquire the sphere's infinite value;
removable singularities acquire their holomorphic extension value. -/
theorem exists_scalarMeromorphic_disk_extension {r : ℝ} (_hr : 0 < r)
    {W : ℂ → ℂ} (hW : HolomorphicOn (puncturedDisk 0 r) W)
    (hW0 : MeromorphicAt W 0) :
    ∃ F : ℂ → RiemannSphere,
      ScalarMeromorphicOn (Metric.ball 0 r) F ∧
      ∀ t ∈ puncturedDisk 0 r, F t = sphereFinite (W t) := by
  have han (t : ℂ) (ht : t ∈ puncturedDisk 0 r) : AnalyticAt ℂ W t :=
    (D12Complex.LocalZeroFactorization.holomorphicNear_iff_analyticAt W t).mp
      ⟨puncturedDisk 0 r, ht, hW⟩
  have hM : MeromorphicOn W (Metric.ball 0 r) := by
    intro t ht
    by_cases ht0 : t = 0
    · simpa only [ht0] using hW0
    · apply (han t ?_).meromorphicAt
      exact ⟨by simpa only [sub_zero] using norm_pos_iff.mpr ht0,
        by simpa only [sub_zero, Metric.mem_ball, dist_zero_right] using ht⟩
  refine ⟨D12Complex.LocalQuotientsArithmetic.fill W,
    D12Complex.LocalQuotientsArithmetic.scalarMeromorphicOn_fill
      (Metric.ball 0 r) Metric.isOpen_ball W hM, ?_⟩
  intro t ht
  exact D12Complex.LocalQuotientsArithmetic.fill_of_analyticAt (han t ht)

open D12Complex.CyclicParameters
open D12Complex.Ch20.PuncturedDiskLoops D12Complex.Ch20.PunctureCompletion

/-- Choose punctured base neighborhoods at every exceptional value and infinity. -/
theorem exists_admissible_radii (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d) :
    Nonempty (Radii P) := by
  classical
  obtain ⟨hf, rinf, hrinf, hinf⟩ := admissible_radii P d hP hdeg hd
  choose rf hrf hfadm using hf
  refine ⟨{
    radius := Sum.elim (fun c => rf (c : ℂ)) (fun _ => rinf)
    positive := ?_
    admissible := ?_
  }⟩
  · intro a
    cases a with
    | inl c => exact hrf c
    | inr _ => exact hrinf
  · intro a u
    cases a with
    | inl c =>
      apply hfadm c ((c : ℂ) + (u : ℂ))
      · simpa only [add_sub_cancel_left] using u.property.1
      · simpa using u.property.2
    | inr _ => exact hinf u

/-- Both local base-coordinate expressions are holomorphic away from their center. -/
theorem holomorphic_baseMap (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (a : Puncture P) :
    HolomorphicOn {u : ℂ | 0 < ‖u‖ ∧ ‖u‖ < R.radius a} (baseMap P a) := by
  refine ⟨(isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const), ?_⟩
  intro u hu
  cases a with
  | inl c => exact (differentiableAt_const (c : ℂ)).add differentiableAt_id
  | inr _ => exact differentiableAt_id.inv (norm_pos_iff.mp hu.1)

/-- There are only finitely many actual local connected components to fill. -/
theorem finite_ends (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d) (R : Radii P) :
    Finite (End P R) := by
  classical
  have hE := (D12Complex.Ch21.FiniteExceptionalSet.finite_exceptional_set
    P d hP hdeg hd).2.1
  letI : Finite (exceptionalSet P) := Set.Finite.to_subtype hE
  letI (a : Puncture P) : Finite (ConnectedComponents (LocalCover P R a)) := by
    obtain ⟨cov, hfinite, _, _⟩ := cyclic_parameters P d hP hdeg hd
      (baseMap P a) (R.radius a) (R.positive a) (holomorphic_baseMap P R a) (R.admissible a)
    exact hfinite
  exact inferInstance

/-- Each actual punctured local component has the accepted cyclic power model. -/
theorem exists_local_model (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (R : Radii P) (j : End P R) : Nonempty (LocalModel P R j) := by
  classical
  let b : Disk (R.radius j.1) := Classical.choice (disk_isDomain (R.positive j.1)).1.to_subtype
  obtain ⟨cov, hfinite, hgerms, hcycles⟩ := cyclic_parameters P d hP hdeg hd
    (baseMap P j.1) (R.radius j.1) (R.positive j.1)
    (holomorphic_baseMap P R j.1) (R.admissible j.1)
  obtain ⟨horbit, hpos, hperm, hmodels⟩ :=
    hcycles b (circleLoop b 1) (circleLoop_winding b 1)
  obtain ⟨hn, S, T, Φ, W, hS, hwS, hT, hΦ, hΦi, hW, hident⟩ := hmodels j.2
  refine ⟨{
    anchor := b
    degree := Nat.card {x : diskProjection P (baseMap P j.1) (R.radius j.1) ⁻¹' {b} //
      ConnectedComponents.mk (x : LocalCover P R j.1) = j.2}
    positive := hn
    degree_eq_card := rfl
    parameter := Φ
    componentSurface := S
    parameterSurface := T
    component_coordinates := hS
    parameter_coordinates := hT
    parameter_holomorphic := hΦ
    inverse_holomorphic := hΦi
    projection_eq := fun t => (hident t).1
    root := W
    holomorphic := by simpa only [puncturedDisk, sub_zero] using hW
    root_eq := fun t => (hident t).2.2.1
  }⟩

/-- Simultaneously choose all local power parameters and their finitely many centers. -/
theorem exists_local_models (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d) :
    ∃ (R : Radii P) (M : ∀ j : End P R, LocalModel P R j), Finite (End P R) := by
  classical
  obtain ⟨R⟩ := exists_admissible_radii P d hP hdeg hd
  exact ⟨R, (fun j => Classical.choice (exists_local_model P d hP hdeg hd R j)),
    finite_ends P d hP hdeg hd R⟩

/-- The local parameter still satisfies the original polynomial in the original base value. -/
theorem local_model_equation (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (j : End P R) (M : LocalModel P R j)
    (t : Disk (rootRadius (R.radius j.1) M.degree)) :
    (fiber P (baseMap P j.1 ((t : ℂ) ^ M.degree))).eval (M.root t) = 0 := by
  have hproj : (diskProjection P (baseMap P j.1) (R.radius j.1) (M.parameter t) : ℂ) =
      (t : ℂ) ^ M.degree :=
    congrArg (fun u : Disk (R.radius j.1) => (u : ℂ)) (M.projection_eq t)
  have hbase : baseMap P j.1 ((t : ℂ) ^ M.degree) =
      (localPoint P R j (M.parameter t)).val.1 := by
    rw [← hproj]
    exact (M.parameter t).val.property
  rw [hbase, M.root_eq t]
  exact (localPoint P R j (M.parameter t)).property.2

/-- The source's root-growth theorem excludes an essential singularity at every new center. -/
theorem local_model_meromorphic (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0)
    (R : Radii P) (j : End P R) (M : LocalModel P R j) :
    MeromorphicAt M.root 0 := by
  have hr := rootRadius_pos (R.positive j.1) M.degree
  have hroot : ∀ t ∈ puncturedDisk 0 (rootRadius (R.radius j.1) M.degree),
      (fiber P (baseMap P j.1 (t ^ M.degree))).eval (M.root t) = 0 := by
    intro t ht
    let tt : Disk (rootRadius (R.radius j.1) M.degree) :=
      ⟨t, by simpa only [puncturedDisk, Set.mem_ofPred_eq, sub_zero] using ht⟩
    exact local_model_equation P R j M tt
  cases ha : j.1 with
  | inl c =>
    obtain ⟨k, hk, hbound, htail⟩ := D12Complex.AlgebraicGrowth.finite_parameter
      P hP (c : ℂ) M.degree M.positive (rootRadius (R.radius j.1) M.degree)
      hr M.root M.holomorphic (by simpa only [ha, baseMap] using hroot)
    exact htail.1
  | inr _ =>
    obtain ⟨L, hcoeff, hparameters⟩ := D12Complex.AlgebraicGrowth.infinity_parameter P hP
    exact (hparameters M.degree M.positive (rootRadius (R.radius j.1) M.degree)
      hr M.root M.holomorphic (by simpa only [ha, baseMap] using hroot)).2.1

/-- Every chosen local model extends meromorphically across its parameter center. -/
theorem local_model_extension (P : Polynomial (Polynomial ℂ)) (hP : P ≠ 0)
    (R : Radii P) (j : End P R) (M : LocalModel P R j) :
    ∃ F : ℂ → RiemannSphere,
      ScalarMeromorphicOn (Metric.ball 0 (rootRadius (R.radius j.1) M.degree)) F ∧
      ∀ t ∈ puncturedDisk 0 (rootRadius (R.radius j.1) M.degree),
        F t = sphereFinite (M.root t) :=
  exists_scalarMeromorphic_disk_extension (rootRadius_pos (R.positive j.1) M.degree)
    M.holomorphic (local_model_meromorphic P hP R j M)

open D12Complex.Surfaces Filter


/-- Scalar meromorphy may be checked on a compatible chart neighborhood
of each point. No separate exclusion of infinite germs is required. -/
theorem scalarMeromorphic_of_local_charts
    {X : Type*} [TopologicalSpace X] (S : RiemannSurface X)
    (F : X → RiemannSphere)
    (hlocal : ∀ x : X, ∃ e ∈ maximalAtlas S.atlas,
      x ∈ e.val.source ∧ ScalarMeromorphicOn e.val.target (F ∘ e.val.symm)) :
    ScalarMeromorphic S F := by
  have hno : ∀ x : X, ¬ ∀ᶠ y in 𝓝 x, F y = sphereInfty := by
    intro x hinf
    obtain ⟨e, he, hx, hM⟩ := hlocal x
    have hP := D12Complex.scalarMeromorphic_planeSphereHolomorphic hM
    have hnot : ¬ EqOn (F ∘ e.val.symm) (fun _ => sphereInfty) e.val.target := by
      intro hall
      obtain ⟨b, hb, hbfin⟩ := hM.2.2.2.2.2 (e.val x) (e.val.map_source hx)
      exact hbfin (hall (connectedComponentIn_subset _ _ hb))
    exact D12Complex.plane_no_infty_germ e.property hP hnot
      (e.val x) (e.val.map_source hx) ((e.val.tendsto_symm hx) hinf)
  intro d hd
  have hP : PlaneSphereHolomorphicOn d.val.target (F ∘ d.val.symm) := by
    refine ⟨d.val.open_target, ?_⟩
    intro a ha
    obtain ⟨e, he, hx, hM⟩ := hlocal (d.val.symm a)
    have hg := compatibleCharts_germ (compatibleCharts_symm (he d hd))
      (d.val.map_target ha) hx
    rw [d.val.right_inv ha] at hg
    have hF := (D12Complex.scalarMeromorphic_planeSphereHolomorphic hM).2
      (e.val (d.val.symm a)) (e.val.map_source hx)
    have hh := planeSphereHolomorphicAt_comp hF hg
    apply hh.congr
    filter_upwards [(d.val.continuousAt_symm ha) (e.val.open_source.mem_nhds hx)] with z hz
    simp only [Function.comp_def, e.val.left_inv hz]
  apply D12Complex.plane_scalarMeromorphic_of_no_infty_germ hP
  intro a ha hinf
  apply hno (d.val.symm a)
  have ht := (d.val.continuousAt (d.val.map_target ha)).tendsto
  rw [d.val.right_inv ha] at ht
  filter_upwards [ht hinf, d.val.open_source.mem_nhds (d.val.map_target ha)] with x hx hxd
  change F (d.val.symm (d.val x)) = sphereInfty at hx
  simpa only [d.val.left_inv hxd] using hx

end D12Complex.CompactCompletion


noncomputable section
open Set Polynomial Topology
open D12Complex D12Complex.AlgebraicCovering D12Complex.CyclicParameters
open D12Complex.Ch20.PuncturedDiskLoops D12Complex.Ch20.PunctureCompletion
open D12Complex.Surfaces

namespace D12Complex.CompactCompletion

theorem localCover_locallyConnected (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (R : Radii P) (a : Puncture P) : LocallyConnectedSpace (LocalCover P R a) := by
  have hg := holomorphic_baseMap P R a
  have hc : Continuous (fun u : Disk (R.radius a) => baseMap P a (u : ℂ)) := by
    apply continuousOn_iff_continuous_domRestrict.mp
    exact fun z hz => (hg.2 z hz).continuousAt.continuousWithinAt
  have cov := curveOver_covering P d hP hdeg hd (baseMap P a) (R.radius a)
    (R.admissible a) hc
  have hq := hg.1.isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp cov.isLocalHomeomorph
  obtain ⟨A, hA, _⟩ := localHomeomorph_complex_atlas
    (fun x : LocalCover P R a => (diskProjection P (baseMap P a) (R.radius a) x : ℂ)) hq
  letI := atlas_locallyPathConnected A hA
  infer_instance

theorem localPoint_openEmbedding (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (R : Radii P) (j : End P R) : IsOpenEmbedding (localPoint P R j) := by
  letI := localCover_locallyConnected P d hP hdeg hd R j.1
  have hcomp : IsOpenEmbedding (Subtype.val : LocalComponent P R j → LocalCover P R j.1) :=
    (componentSet_clopen j.2).isOpen.isOpenEmbedding_subtypeVal
  have hlocal : IsOpenEmbedding (fun x : LocalCover P R j.1 => x.val.2) := by
    cases ha : j.1 with
    | inl c =>
      have hopen : IsOpen {x : Curve P | 0 < ‖x.val.1 - (c : ℂ)‖ ∧
          ‖x.val.1 - (c : ℂ)‖ < R.radius (Sum.inl c)} :=
        (isOpen_lt continuous_const ((continuous_subtype_val.fst).sub continuous_const).norm).inter
          (isOpen_lt ((continuous_subtype_val.fst).sub continuous_const).norm continuous_const)
      exact hopen.isOpenEmbedding_subtypeVal.comp
        (finiteRestrictionHomeomorph P (c : ℂ) (R.radius (Sum.inl c))).isOpenEmbedding
    | inr u =>
      have hopen : IsOpen {x : Curve P | 0 < ‖x.val.1⁻¹‖ ∧
          ‖x.val.1⁻¹‖ < R.radius (Sum.inr u)} := by
        have heq : {x : Curve P | 0 < ‖x.val.1⁻¹‖ ∧
            ‖x.val.1⁻¹‖ < R.radius (Sum.inr u)} =
            {x : Curve P | (R.radius (Sum.inr u))⁻¹ < ‖x.val.1‖} := by
          ext x
          simp only [mem_setOf_eq, norm_inv]
          constructor
          · intro h
            exact (inv_lt_comm₀ (inv_pos.mp h.1)
              (R.positive (Sum.inr u))).mp h.2
          · intro h
            have hx : 0 < ‖x.val.1‖ := (inv_pos.mpr (R.positive _)).trans h
            exact ⟨inv_pos.mpr hx, (inv_lt_comm₀ hx (R.positive _)).mpr h⟩
        rw [heq]
        exact isOpen_lt continuous_const continuous_subtype_val.fst.norm
      exact hopen.isOpenEmbedding_subtypeVal.comp
        (infinityRestrictionHomeomorph P (R.radius (Sum.inr u))).isOpenEmbedding
  exact hlocal.comp hcomp


def punctureValue (P : Polynomial (Polynomial ℂ)) : Puncture P → RiemannSphere
  | Sum.inl c => sphereFinite c
  | Sum.inr _ => sphereInfty

theorem punctureValue_injective (P : Polynomial (Polynomial ℂ)) :
    Function.Injective (punctureValue P) := by
  intro a b h
  cases a with
  | inl c =>
    cases b with
    | inl c' =>
      have h' : (c : ℂ) = (c' : ℂ) := congrArg finiteCoordinate h
      exact congrArg Sum.inl (Subtype.ext h')
    | inr u => exact ((OnePoint.coe_ne_infty (c : ℂ)) h).elim
  | inr u =>
    cases b with
    | inl c => exact ((OnePoint.coe_ne_infty (c : ℂ)) h.symm).elim
    | inr v => exact congrArg Sum.inr (Subsingleton.elim u v)

def modelDiskProjection (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (M : ∀ j : End P R, LocalModel P R j) (j : End P R)
    (t : FiniteEndGluing.FullDisk (rootRadius (R.radius j.1) (M j).degree)) :
    RiemannSphere :=
  match j.1 with
  | Sum.inl c => sphereFinite ((c : ℂ) + (t : ℂ) ^ (M j).degree)
  | Sum.inr _ => infinityParametrization ((t : ℂ) ^ (M j).degree)

theorem modelDiskProjection_continuous (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (M : ∀ j : End P R, LocalModel P R j) (j : End P R) :
    Continuous (modelDiskProjection P R M j) := by
  unfold modelDiskProjection
  split
  · exact continuous_sphereFinite.comp
      (continuous_const.add (continuous_subtype_val.pow (M j).degree))
  · exact continuous_infinityParametrization.comp (continuous_subtype_val.pow (M j).degree)

theorem modelDiskProjection_center (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (M : ∀ j : End P R, LocalModel P R j) (j : End P R) :
    modelDiskProjection P R M j ⟨0, by
      simpa using rootRadius_pos (R.positive j.1) (M j).degree⟩ =
      punctureValue P j.1 := by
  unfold modelDiskProjection punctureValue
  split <;> simp [zero_pow (Nat.ne_of_gt (M j).positive), infinityParametrization_zero]

theorem modelDiskProjection_agrees (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (M : ∀ j : End P R, LocalModel P R j) (j : End P R)
    (t : Disk (rootRadius (R.radius j.1) (M j).degree)) :
    modelDiskProjection P R M j (FiniteEndGluing.punctureInclusion t) =
      sphereFinite (localPoint P R j ((M j).parameter t)).val.1 := by
  have hproj : (diskProjection P (baseMap P j.1) (R.radius j.1)
      ((M j).parameter t) : ℂ) = (t : ℂ) ^ (M j).degree :=
    congrArg (fun u : Disk (R.radius j.1) => (u : ℂ)) ((M j).projection_eq t)
  have hp : (localPoint P R j ((M j).parameter t)).val.1 =
      baseMap P j.1 ((t : ℂ) ^ (M j).degree) := by
    rw [← hproj]
    exact ((M j).parameter t).val.property.symm
  rw [hp]
  unfold modelDiskProjection
  split
  · rename_i c ha
    simp only [ha, baseMap, FiniteEndGluing.punctureInclusion]
  · rename_i u ha
    simpa only [ha, baseMap, FiniteEndGluing.punctureInclusion] using
      infinityParametrization_ne_zero ((t : ℂ) ^ (M j).degree)
        (pow_ne_zero _ (norm_pos_iff.mp t.property.1))

theorem localCover_point_injective (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (a : Puncture P) : Function.Injective (fun x : LocalCover P R a => x.val.2) := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    have hp : baseMap P a (x.val.1 : ℂ) = baseMap P a (y.val.1 : ℂ) :=
      x.property.trans ((congrArg (fun z : Curve P => z.val.1) h).trans y.property.symm)
    cases a with
    | inl c => exact add_left_cancel hp
    | inr u => exact inv_injective hp
  · exact h

def attachmentData (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (R : Radii P) (M : ∀ j : End P R, LocalModel P R j) :
    FiniteEndGluing.Data (Curve P) (End P R) RiemannSphere where
  radius j := rootRadius (R.radius j.1) (M j).degree
  radius_pos j := rootRadius_pos (R.positive j.1) (M j).degree
  theta j := localPoint P R j ∘ (M j).parameter
  theta_openEmbedding j := (localPoint_openEmbedding P d hP hdeg hd R j).comp
    (M j).parameter.isOpenEmbedding
  projection x := sphereFinite x.val.1
  projection_continuous := continuous_sphereFinite.comp continuous_subtype_val.fst
  diskProjection := modelDiskProjection P R M
  diskProjection_continuous := modelDiskProjection_continuous P R M
  agrees := modelDiskProjection_agrees P R M
  avoids := by
    intro x j
    rw [modelDiskProjection_center]
    cases ha : j.1 with
    | inl c =>
      intro h
      have hx : x.val.1 = (c : ℂ) := congrArg finiteCoordinate h
      have hg := x.property.1
      rw [hx] at hg
      exact hg c.property
    | inr u => exact OnePoint.coe_ne_infty x.val.1
  disjoint := by
    intro j k hjk hcenter
    rw [modelDiskProjection_center, modelDiskProjection_center] at hcenter
    have ha := punctureValue_injective P hcenter
    rcases j with ⟨a,j⟩
    rcases k with ⟨b,k⟩
    dsimp only at ha
    subst b
    apply Set.disjoint_left.mpr
    rintro x ⟨s, hs⟩ ⟨t, ht⟩
    have hp : ((M ⟨a,j⟩).parameter s).val = ((M ⟨a,k⟩).parameter t).val :=
      localCover_point_injective P R a (hs.trans ht.symm)
    have heq : j = k :=
      ((M ⟨a,j⟩).parameter s).property.symm.trans
        ((congrArg ConnectedComponents.mk hp).trans ((M ⟨a,k⟩).parameter t).property)
    exact hjk (congrArg (Sigma.mk a) heq)

end D12Complex.CompactCompletion


noncomputable section
open Set Filter Topology
namespace D12Complex.CompactCompletion
open Surfaces CyclicParameters
open D12Complex.Ch20.PuncturedDiskLoops D12Complex.Ch20.PunctureCompletion
open FiniteEndGluing AnalyticEndPasting

/-- The inverse of an open punctured parameter embedding is a literal plane chart. -/
def puncturedParameterChart {E : Type*} [TopologicalSpace E]
    {r : ℝ} (hr : 0 < r) (θ : Disk r → E) (hθ : IsOpenEmbedding θ) :
    ComplexChart E := by
  letI : Nonempty (Disk r) := (disk_isDomain hr).1.to_subtype
  exact embeddedChart θ hθ (planeChart _ (disk_isDomain hr)) (planeChart_source _ _)

@[simp] theorem puncturedParameterChart_source {E : Type*} [TopologicalSpace E]
    {r : ℝ} (hr : 0 < r) (θ : Disk r → E) (hθ : IsOpenEmbedding θ) :
    (puncturedParameterChart hr θ hθ).val.source = range θ := by
  letI : Nonempty (Disk r) := (disk_isDomain hr).1.to_subtype
  exact embeddedChart_source θ hθ (planeChart _ (disk_isDomain hr)) (planeChart_source _ _)

@[simp] theorem puncturedParameterChart_target {E : Type*} [TopologicalSpace E]
    {r : ℝ} (hr : 0 < r) (θ : Disk r → E) (hθ : IsOpenEmbedding θ) :
    (puncturedParameterChart hr θ hθ).val.target = {t : ℂ | 0 < ‖t‖ ∧ ‖t‖ < r} := by
  letI : Nonempty (Disk r) := (disk_isDomain hr).1.to_subtype
  rw [puncturedParameterChart, embeddedChart_target]
  exact planeChart_target _ _

@[simp] theorem puncturedParameterChart_apply {E : Type*} [TopologicalSpace E]
    {r : ℝ} (hr : 0 < r) (θ : Disk r → E) (hθ : IsOpenEmbedding θ) (t : Disk r) :
    (puncturedParameterChart hr θ hθ).val (θ t) = (t : ℂ) := by
  letI : Nonempty (Disk r) := (disk_isDomain hr).1.to_subtype
  rw [puncturedParameterChart, embeddedChart_apply]
  exact planeChart_apply _ _ t

@[simp] theorem puncturedParameterChart_symm {E : Type*} [TopologicalSpace E]
    {r : ℝ} (hr : 0 < r) (θ : Disk r → E) (hθ : IsOpenEmbedding θ) (t : Disk r) :
    (puncturedParameterChart hr θ hθ).val.symm (t : ℂ) = θ t := by
  apply (puncturedParameterChart hr θ hθ).val.injOn
  · exact (puncturedParameterChart hr θ hθ).val.map_target (by
      rw [puncturedParameterChart_target]; exact t.property)
  · rw [puncturedParameterChart_source]; exact mem_range_self t
  · rw [(puncturedParameterChart hr θ hθ).val.right_inv (by
      rw [puncturedParameterChart_target]; exact t.property), puncturedParameterChart_apply]

/-- The first coordinate in every cyclic model is the prescribed power expression. -/
lemma local_model_base (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (j : End P R) (M : LocalModel P R j)
    (t : Disk (rootRadius (R.radius j.1) M.degree)) :
    (localPoint P R j (M.parameter t)).val.1 =
      baseMap P j.1 ((t : ℂ) ^ M.degree) := by
  have hproj : (diskProjection P (baseMap P j.1) (R.radius j.1) (M.parameter t) : ℂ) = (t : ℂ) ^ M.degree :=
    congrArg (fun u : Disk (R.radius j.1) => (u : ℂ)) (M.projection_eq t)
  change ((M.parameter t).val.val.2).val.1 = _
  rw [← hproj]
  exact (M.parameter t).val.property.symm

/-- The punctured parameter inverse charts fit the original base-coordinate atlas. -/
def analyticParameters_of_models
    (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (M : ∀ j : End P R, LocalModel P R j)
    (d : Data (AlgebraicCovering.Curve P) (End P R) RiemannSphere)
    (hr : ∀ j, d.radius j = rootRadius (R.radius j.1) (M j).degree)
    (hθ : ∀ j (t : Parameter (d.radius j)), d.theta j t =
      localPoint P R j ((M j).parameter (hr j ▸ t)))
    (S : RiemannSurface (AlgebraicCovering.Curve P))
    (hS : ∀ e ∈ S.atlas, ∀ x ∈ e.val.source, e.val x = x.val.1) :
    AnalyticParameters d S := by
  let c (j : End P R) := puncturedParameterChart (d.radius_pos j) (d.theta j) (d.theta_openEmbedding j)
  refine ⟨c, fun j => puncturedParameterChart_source _ _ _,
    fun j => puncturedParameterChart_target _ _ _,
    fun j => puncturedParameterChart_apply _ _ _,
    fun j => puncturedParameterChart_symm _ _ _, ?_⟩
  intro j e he
  let t := (c j).val.symm.trans e.val
  have ht : HolomorphicOn t.source t := by
    refine ⟨t.open_source, fun z hz => ?_⟩
    have hzmem : 0 < ‖z‖ ∧ ‖z‖ < d.radius j := by
      have hz1 : z ∈ (c j).val.target := hz.1
      simpa only [c, puncturedParameterChart_target, mem_setOf_eq] using hz1
    have hz0 : z ≠ 0 := norm_pos_iff.mp hzmem.1
    have hd : DifferentiableAt ℂ (fun z => baseMap P j.1 (z ^ (M j).degree)) z := by
      cases h : j.1 with
      | inl a => exact (differentiableAt_const (a : ℂ)).add (differentiableAt_id.pow _)
      | inr a => exact (differentiableAt_id.pow _).inv (pow_ne_zero _ hz0)
    apply hd.congr_of_eventuallyEq
    filter_upwards [t.open_source.mem_nhds hz] with w hw
    have hw' : 0 < ‖w‖ ∧ ‖w‖ < d.radius j := by
      have hw1 : w ∈ (c j).val.target := hw.1
      simpa only [c, puncturedParameterChart_target, mem_setOf_eq] using hw1
    let u : Parameter (d.radius j) := ⟨w, hw'⟩
    have hcs : (c j).val.symm w = d.theta j u := puncturedParameterChart_symm _ _ _ u
    change e.val ((c j).val.symm w) = baseMap P j.1 (w ^ (M j).degree)
    rw [hS e he ((c j).val.symm w) (show (c j).val.symm w ∈ e.val.source from hw.2), hcs, hθ j u]
    have hcoe {r s : ℝ} (h : r = s) (u : Disk r) :
        ((h ▸ u : Disk s) : ℂ) = (u : ℂ) := by cases h; rfl
    simpa only [hcoe] using local_model_base P R j (M j) (hr j ▸ u)
  exact ⟨ht, holomorphicOn_symm t ht, t.mapsTo, t.symm.mapsTo, t.leftInvOn, t.rightInvOn⟩

/-- Original algebraic-curve surface, using its literal base-coordinate charts. -/
theorem exists_old_surface (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d) :
    ∃ S : RiemannSurface (AlgebraicCovering.Curve P),
      (∀ e ∈ S.atlas, ∀ x ∈ e.val.source, e.val x = x.val.1) ∧
      ScalarHolomorphic S (fun x => x.val.1) ∧
      ScalarHolomorphic S (fun x => x.val.2) := by
  obtain ⟨hT, hC, A, hA, hc⟩ := AlgebraicCovering.complex_atlas P d hP hdeg hd
  let S : RiemannSurface (AlgebraicCovering.Curve P) := {
    connected := (MonodromyTransitive.connected P d hP hdeg hd).2
    hausdorff := hT
    secondCountable := hC
    atlas := A
    isAtlas := hA }
  refine ⟨S, fun e he => (hc e he).1, ?_, ?_⟩
  · refine ⟨continuous_subtype_val.fst, fun e he => ⟨e.val.open_target, fun z hz => ?_⟩⟩
    apply differentiableAt_id.congr_of_eventuallyEq
    filter_upwards [e.val.open_target.mem_nhds hz] with w hw
    exact ((hc e he).1 _ (e.val.map_target hw)).symm.trans (e.val.right_inv hw)
  · exact ⟨continuous_subtype_val.snd, fun e he => (hc e he).2⟩

end D12Complex.CompactCompletion


noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.CompactCompletion
open D12Complex.Surfaces

/-- Every plane holomorphic function defines a finite-valued scalar meromorphic map. -/
theorem scalarMeromorphicOn_of_holomorphic {U : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn U f) :
    ScalarMeromorphicOn U (fun t => sphereFinite (f t)) := by
  apply D12Complex.LocalQuotientsArithmetic.scalar_congr
    (D12Complex.LocalQuotientsArithmetic.scalarMeromorphicOn_fill U hf.1 f ?_)
  · intro t ht
    have h := (D12Complex.LocalZeroFactorization.holomorphicNear_iff_analyticAt f t).mp
      ⟨U, ht, hf⟩
    exact D12Complex.LocalQuotientsArithmetic.fill_of_analyticAt h
  · intro t ht
    exact ((D12Complex.LocalZeroFactorization.holomorphicNear_iff_analyticAt f t).mp
      ⟨U, ht, hf⟩).meromorphicAt

/-- The reciprocal power is a scalar meromorphic sphere expression, including
its prescribed infinite value at the origin. -/
theorem scalarMeromorphicOn_infinity_power (r : ℝ) (n : ℕ) (hn : 0 < n) :
    ScalarMeromorphicOn (Metric.ball 0 r)
      (fun t : ℂ => infinityParametrization (t ^ n)) := by
  have hp : PlaneSphereHolomorphicOn (Metric.ball 0 r)
      (fun t : ℂ => infinityParametrization (t ^ n)) := by
    refine ⟨Metric.isOpen_ball, ?_⟩
    intro t ht
    by_cases ht0 : t = 0
    · apply D12Complex.planeSphereHolomorphicAt_of_reciprocal_lift
        (g := fun z : ℂ => z ^ n)
      · exact ⟨univ, mem_univ _, isOpen_univ, fun z _ => differentiableAt_id.pow n⟩
      · simp [ht0, hn.ne']
      · exact Filter.EventuallyEq.rfl
    · apply D12Complex.planeSphereHolomorphicAt_of_finite_germ
      · have he : scalarFinitePart (fun z : ℂ => infinityParametrization (z ^ n)) =
            fun z : ℂ => (z ^ n)⁻¹ := by
          funext z
          by_cases hz : z ^ n = 0
          · simp [scalarFinitePart, infinityParametrization, hz, finiteCoordinate, sphereInfty]
          · rw [scalarFinitePart, infinityParametrization_ne_zero _ hz,
              finiteCoordinate_sphereFinite]
        rw [he]
        exact ⟨{z : ℂ | z ≠ 0}, ht0, isOpen_compl_singleton,
          fun z hz => (differentiableAt_id.pow n).inv (pow_ne_zero n hz)⟩
      · filter_upwards [isOpen_compl_singleton.mem_nhds ht0] with z hz
        rw [infinityParametrization_ne_zero _ (pow_ne_zero n hz)]
        exact OnePoint.coe_ne_infty _
  apply D12Complex.plane_scalarMeromorphic_of_no_infty_germ hp
  intro t ht hinf
  have hfinite : ∀ᶠ z in 𝓝[≠] t,
      infinityParametrization (z ^ n) ≠ sphereInfty := by
    by_cases ht0 : t = 0
    · subst t
      filter_upwards [self_mem_nhdsWithin] with z hz
      rw [infinityParametrization_ne_zero _ (pow_ne_zero n hz)]
      exact OnePoint.coe_ne_infty _
    · filter_upwards [nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds ht0)] with z hz
      rw [infinityParametrization_ne_zero _ (pow_ne_zero n hz)]
      exact OnePoint.coe_ne_infty _
  exact (hinf.filter_mono nhdsWithin_le_nhds).and hfinite |>.exists.elim fun z hz => hz.2 hz.1

/-- The finite embedding sends a holomorphic scalar on a surface to a scalar
meromorphic function with the same values. -/
theorem scalarMeromorphic_of_scalarHolomorphic
    {X : Type*} [TopologicalSpace X] (S : RiemannSurface X) (f : X → ℂ)
    (hf : ScalarHolomorphic S f) :
    ScalarMeromorphic S (fun x => sphereFinite (f x)) := by
  intro e he
  exact scalarMeromorphicOn_of_holomorphic (hf.2 e he)

open D12Complex.AlgebraicCovering D12Complex.CyclicParameters
open D12Complex.Ch20.PunctureCompletion

/-- The full-disk first-coordinate expression for every actual cyclic end. -/
def modelBaseExpression (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (M : ∀ j : End P R, LocalModel P R j) (j : End P R) (t : ℂ) : RiemannSphere :=
  match j.1 with
  | Sum.inl c => sphereFinite ((c : ℂ) + t ^ (M j).degree)
  | Sum.inr _ => infinityParametrization (t ^ (M j).degree)

/-- These literal first-coordinate expressions are meromorphic on their full disks. -/
theorem scalarMeromorphicOn_modelBaseExpression
    (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (M : ∀ j : End P R, LocalModel P R j) (j : End P R) :
    ScalarMeromorphicOn (Metric.ball 0 (rootRadius (R.radius j.1) (M j).degree))
      (modelBaseExpression P R M j) := by
  unfold modelBaseExpression
  cases ha : j.1 with
  | inl c =>
    have h : HolomorphicOn
        (Metric.ball 0 (rootRadius (R.radius j.1) (M j).degree))
        (fun t : ℂ => (c : ℂ) + t ^ (M j).degree) :=
      ⟨Metric.isOpen_ball, fun t _ =>
        (differentiableAt_const (c : ℂ)).add (differentiableAt_id.pow _)⟩
    simpa only [modelBaseExpression, ha] using scalarMeromorphicOn_of_holomorphic h
  | inr u =>
    simpa only [modelBaseExpression, ha] using
      scalarMeromorphicOn_infinity_power (rootRadius (R.radius j.1) (M j).degree)
        (M j).degree (M j).positive

end D12Complex.CompactCompletion


noncomputable section
open Set
open scoped Topology
namespace D12Complex.CompactCompletion
lemma exists_uniform_positive_lt {I : Type*} [Finite I] (a : I → ℝ)
    (ha : ∀ i, 0 < a i) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ i, δ < a i := by
  classical
  let := Fintype.ofFinite I
  have aux (s : Finset I) : ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ i ∈ s, δ < a i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1 / 2, by norm_num, by norm_num, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε, hε, hε1, hεall⟩ := ih
      refine ⟨min ε (a i / 2), lt_min hε (half_pos (ha i)),
        (min_le_left _ _).trans_lt hε1, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        exact (min_le_right _ _).trans_lt (half_lt_self (ha i))
      · exact (min_le_left _ _).trans_lt (hεall j hj)
  obtain ⟨δ, hδ, hδ1, hall⟩ := aux Finset.univ
  exact ⟨δ, hδ, hδ1, fun i => hall i (Finset.mem_univ i)⟩

lemma isCompact_base_core {C : Type*} (c : C → ℂ) {δ : ℝ} (_hδ : 0 < δ) :
    IsCompact {z : ℂ | ‖z‖ ≤ δ⁻¹ ∧ ∀ a, δ ≤ ‖z - c a‖} := by
  have hleft : IsClosed {z : ℂ | ‖z‖ ≤ δ⁻¹} :=
    isClosed_le continuous_norm continuous_const
  have hright : IsClosed (⋂ a : C, {z : ℂ | δ ≤ ‖z - c a‖}) :=
    isClosed_iInter fun a =>
      isClosed_le continuous_const ((continuous_id.sub continuous_const).norm)
  have hclosed : IsClosed {z : ℂ | ‖z‖ ≤ δ⁻¹ ∧ ∀ a, δ ≤ ‖z - c a‖} := by
    convert hleft.inter hright using 1
    ext z
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter]
  exact (isCompact_closedBall (0 : ℂ) δ⁻¹).of_isClosed_subset hclosed
    (fun z hz => by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1)

open D12Complex.AlgebraicCovering D12Complex.CyclicParameters
open D12Complex.Ch20.PuncturedDiskLoops D12Complex.Ch20.PunctureCompletion

lemma exists_local_parameter_of_small_base
    (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    (M : ∀ j : End P R, LocalModel P R j) (s : End P R → ℝ)
    (hs : ∀ j, 0 < s j) {δ : ℝ}
    (hδR : ∀ a, δ < R.radius a)
    (hδs : ∀ j, δ < s j ^ (M j).degree)
    (a : Puncture P) (x : Curve P) (u : ℂ)
    (hu : 0 < ‖u‖ ∧ ‖u‖ < δ) (hbase : baseMap P a u = x.val.1) :
    ∃ (j : End P R) (t : Disk (rootRadius (R.radius j.1) (M j).degree)),
      ‖(t : ℂ)‖ ≤ s j ∧ localPoint P R j ((M j).parameter t) = x := by
  let uu : Disk (R.radius a) := ⟨u, hu.1, hu.2.trans (hδR a)⟩
  let y : LocalCover P R a := ⟨(uu, x), hbase⟩
  let j : End P R := ⟨a, ConnectedComponents.mk y⟩
  let yy : LocalComponent P R j := ⟨y, rfl⟩
  let t := (M j).parameter.symm yy
  refine ⟨j, t, ?_, ?_⟩
  · have hpow := (M j).projection_eq t
    have ht : (M j).parameter t = yy := (M j).parameter.apply_symm_apply yy
    rw [ht] at hpow
    have huPow : u = (t : ℂ) ^ (M j).degree :=
      congrArg (fun v : Disk (R.radius a) => (v : ℂ)) hpow
    have hnorm : ‖(t : ℂ)‖ ^ (M j).degree < s j ^ (M j).degree := by
      rw [← norm_pow, ← huPow]
      exact hu.2.trans (hδs j)
    exact ((pow_lt_pow_iff_left₀ (norm_nonneg _) (hs j).le (M j).positive.ne').mp hnorm).le
  · rw [(M j).parameter.apply_symm_apply yy]
    rfl

lemma exists_compact_core_parameters
    (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    [Finite (exceptionalSet P)] [Finite (End P R)]
    (M : ∀ j : End P R, LocalModel P R j) :
    ∃ (K : Set ℂ) (s : End P R → ℝ),
      IsCompact K ∧ K ⊆ baseSet P ∧
      (∀ j, 0 < s j ∧ s j < rootRadius (R.radius j.1) (M j).degree) ∧
      ∀ x : Curve P, x.val.1 ∈ K ∨
        ∃ (j : End P R) (t : Disk (rootRadius (R.radius j.1) (M j).degree)),
          ‖(t : ℂ)‖ ≤ s j ∧ localPoint P R j ((M j).parameter t) = x := by
  classical
  let s : End P R → ℝ := fun j => rootRadius (R.radius j.1) (M j).degree / 2
  have hs : ∀ j, 0 < s j ∧ s j < rootRadius (R.radius j.1) (M j).degree := by
    intro j
    exact ⟨half_pos (rootRadius_pos (R.positive j.1) _),
      half_lt_self (rootRadius_pos (R.positive j.1) _)⟩
  obtain ⟨δ, hδ, _, hδall⟩ := exists_uniform_positive_lt
    (Sum.elim (R.radius) (fun j => s j ^ (M j).degree)) (by
      rintro (a | j)
      · exact R.positive a
      · exact pow_pos (hs j).1 _)
  have hδR (a : Puncture P) : δ < R.radius a := hδall (Sum.inl a)
  have hδs (j : End P R) : δ < s j ^ (M j).degree := hδall (Sum.inr j)
  let K : Set ℂ := {z | ‖z‖ ≤ δ⁻¹ ∧ ∀ a : exceptionalSet P, δ ≤ ‖z - a.val‖}
  refine ⟨K, s, isCompact_base_core Subtype.val hδ, ?_, hs, ?_⟩
  · intro z hz
    change z ∉ exceptionalSet P
    intro he
    have h := hz.2 ⟨z, he⟩
    simp only [sub_self, norm_zero] at h
    exact (not_le.mpr hδ) h
  · intro x
    by_cases hx : x.val.1 ∈ K
    · exact Or.inl hx
    · right
      by_cases hnorm : ‖x.val.1‖ ≤ δ⁻¹
      · have hnear : ¬ ∀ a : exceptionalSet P, δ ≤ ‖x.val.1 - a.val‖ := by
          intro hh
          exact hx ⟨hnorm, hh⟩
        obtain ⟨c, hc⟩ := not_forall.mp hnear
        have hz : x.val.1 ≠ c.val := by
          intro he
          exact x.property.1 (he.symm ▸ c.property)
        exact exists_local_parameter_of_small_base P R M s (fun j => (hs j).1)
          hδR hδs (Sum.inl c) x (x.val.1 - c.val)
          ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hz), lt_of_not_ge hc⟩
          (by simp [baseMap])
      · have hzpos : 0 < ‖x.val.1‖ := (inv_pos.mpr hδ).trans (lt_of_not_ge hnorm)
        have hinv : ‖x.val.1⁻¹‖ < δ := by
          rw [norm_inv]
          exact (inv_lt_comm₀ hzpos hδ).mpr (lt_of_not_ge hnorm)
        exact exists_local_parameter_of_small_base P R M s (fun j => (hs j).1)
          hδR hδs (Sum.inr ()) x (x.val.1⁻¹)
          ⟨by simpa only [norm_inv] using inv_pos.mpr hzpos, hinv⟩
          (by simp [baseMap])

open D12Complex.Surfaces

lemma exists_compact_core_cover
    (P : Polynomial (Polynomial ℂ)) (R : Radii P)
    [Finite (exceptionalSet P)] [Finite (End P R)]
    (M : ∀ j : End P R, LocalModel P R j)
    [TopologicalSpace (Carrier P R)]
    (hi : Topology.IsOpenEmbedding (Sum.inl : Curve P → Carrier P R))
    (chart : End P R → ComplexChart (Carrier P R))
    (htarget : ∀ j, (chart j).val.target =
      Metric.ball 0 (rootRadius (R.radius j.1) (M j).degree))
    (hsymm : ∀ j (t : Disk (rootRadius (R.radius j.1) (M j).degree)),
      (chart j).val.symm t = Sum.inl (localPoint P R j ((M j).parameter t)))
    (hcenter : ∀ j, (chart j).val.symm 0 = Sum.inr j) :
    ∃ (K : Set ℂ) (s : End P R → ℝ),
      IsCompact K ∧ K ⊆ baseSet P ∧
      (∀ j, 0 < s j ∧ s j < rootRadius (R.radius j.1) (M j).degree) ∧
      IsCompact (Sum.inl '' {x : Curve P | x.val.1 ∈ K} : Set (Carrier P R)) ∧
      (∀ j, IsCompact ((chart j).val.symm '' Metric.closedBall 0 (s j))) ∧
      (Set.univ : Set (Carrier P R)) =
        (Sum.inl '' {x : Curve P | x.val.1 ∈ K}) ∪
          ⋃ j, (chart j).val.symm '' Metric.closedBall 0 (s j) := by
  obtain ⟨K, s, hK, hgood, hs, hcov⟩ := exists_compact_core_parameters P R M
  refine ⟨K, s, hK, hgood, hs,
    (isCompact_curve_preimage P hK hgood).image hi.continuous, ?_, ?_⟩
  · intro j
    apply (isCompact_closedBall (0 : ℂ) (s j)).image_of_continuousOn
    apply (chart j).val.continuousOn_symm.mono
    rw [htarget j]
    intro t ht
    exact lt_of_le_of_lt ht (hs j).2
  · ext y
    constructor
    · intro _
      cases y with
      | inl x =>
        rcases hcov x with hx | ⟨j, t, ht, he⟩
        · exact Or.inl ⟨x, hx, rfl⟩
        · right
          refine mem_iUnion.mpr ⟨j, ?_⟩
          refine ⟨(t : ℂ), ?_, ?_⟩
          · simpa only [Metric.mem_closedBall, dist_zero_right] using ht
          · rw [hsymm j t, he]
      | inr j =>
        right
        refine mem_iUnion.mpr ⟨j, ?_⟩
        exact ⟨0, Metric.mem_closedBall_self (hs j).1.le, hcenter j⟩
    · intro _
      exact mem_univ y

lemma compactSpace_of_compact_core_cover {X : Type*} [TopologicalSpace X]
    {J : Type*} [Finite J] (K : Set X) (D : J → Set X)
    (hK : IsCompact K) (hD : ∀ j, IsCompact (D j))
    (hcover : (Set.univ : Set X) = K ∪ ⋃ j, D j) : CompactSpace X := by
  apply isCompact_univ_iff.mp
  rw [hcover]
  exact hK.union (isCompact_iUnion hD)

end D12Complex.CompactCompletion


noncomputable section
open Set Filter Topology Polynomial
open scoped Topology
namespace D12Complex.CompactCompletion
open Surfaces CyclicParameters AlgebraicCovering FiniteEndGluing AnalyticEndPasting
open D12Complex.Ch20.PuncturedDiskLoops D12Complex.Ch20.PunctureCompletion

/-- The glued projection is the original first coordinate, with the forced
finite exceptional and infinite values at the added centers. -/
lemma attachment_projection_eq (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (R : Radii P) (M : ∀ j : End P R, LocalModel P R j) :
    (attachmentData P d hP hdeg hd R M).extendedProjection = baseCoordinate P R := by
  funext x
  cases x with
  | inl x => rfl
  | inr j =>
    change modelDiskProjection P R M j
      ⟨0, by simpa using rootRadius_pos (R.positive j.1) (M j).degree⟩ = _
    rw [modelDiskProjection_center]
    rcases j with ⟨a, j⟩
    cases a <;> rfl

lemma attachment_chart_source (P : Polynomial (Polynomial ℂ)) (d : ℕ)
    (hP : Irreducible P) (hdeg : P.natDegree = d) (hd : 0 < d)
    (R : Radii P) (M : ∀ j : End P R, LocalModel P R j) (j : End P R) :
    range ((attachmentData P d hP hdeg hd R M).psi j) = endChartSource P R j := by
  rw [Data.range_psi]
  have h : range ((attachmentData P d hP hdeg hd R M).theta j) =
      range (localPoint P R j) := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨(M j).parameter.symm y, by simp only [attachmentData, Function.comp_apply,
        Homeomorph.apply_symm_apply]⟩
  rw [h]
  rfl

/-- The finite cyclic completion of the original irreducible algebraic covering. -/
theorem compact_completion :
    Specs.D12Complex.Ch21.CompactCompletion.compact_completion_type := by
  intro P d hP hdeg hd
  classical
  obtain ⟨R, M, hfin⟩ := exists_local_models P d hP hdeg hd
  letI := hfin
  have hE := (D12Complex.Ch21.FiniteExceptionalSet.finite_exceptional_set
    P d hP hdeg hd).2.1
  letI : Finite (exceptionalSet P) := hE.to_subtype
  let D := attachmentData P d hP hdeg hd R M
  obtain ⟨S₀, hcoords, hz, hw⟩ := exists_old_surface P d hP hdeg hd
  let a : AnalyticParameters D S₀ := analyticParameters_of_models P R M D
    (fun _ => rfl) (fun _ _ => rfl) S₀ hcoords
  letI := D.topology
  obtain ⟨C⟩ := analytic_end_pasting D S₀ a
  have hsymm (j : End P R) (t : Disk (rootRadius (R.radius j.1) (M j).degree)) :
      (C.parameterChart j).val.symm t = Sum.inl (localPoint P R j ((M j).parameter t)) := by
    exact (C.parameter_symm j (punctureInclusion t)).trans (D.psi_puncture j t)
  have hcenter (j : End P R) : (C.parameterChart j).val.symm 0 = Sum.inr j := by
    exact (C.parameter_symm j (D.center j)).trans (D.psi_center j)
  obtain ⟨K, s, hK, hgood, hs, hKX, hdisks, hcover⟩ :=
    exists_compact_core_cover P R M C.oldEmbedding C.parameterChart
      C.parameter_target hsymm hcenter
  have hcompact := compactSpace_of_compact_core_cover
    (Sum.inl '' {x : Curve P | x.val.1 ∈ K} : Set (Carrier P R))
    (fun j => (C.parameterChart j).val.symm '' Metric.closedBall 0 (s j))
    hKX hdisks hcover
  have hbase : ScalarMeromorphic C.surface (baseCoordinate P R) := by
    have hmatch (j : End P R) (t : Parameter (D.radius j)) :
        modelBaseExpression P R M j t = sphereFinite (D.theta j t).val.1 :=
      modelDiskProjection_agrees P R M j t
    have hm := C.meromorphic_paste (fun x : Curve P => sphereFinite x.val.1)
      (modelBaseExpression P R M) (scalarMeromorphic_of_scalarHolomorphic S₀ _ hz)
      (scalarMeromorphicOn_modelBaseExpression P R M) hmatch
    have heq : paste (fun x : Curve P => sphereFinite x.val.1)
        (modelBaseExpression P R M) = baseCoordinate P R := by
      funext x
      cases x with
      | inl x => rfl
      | inr j =>
        change modelBaseExpression P R M j 0 = _
        have he : modelBaseExpression P R M j 0 = punctureValue P j.1 :=
          modelDiskProjection_center P R M j
        rw [he]
        rcases j with ⟨a, j⟩
        cases a <;> rfl
    rwa [heq] at hm
  have hext (j : End P R) := local_model_extension P hP.ne_zero R j (M j)
  choose G hG hGmatch using hext
  let W := paste (fun x : Curve P => sphereFinite x.val.2) G
  have hW : ScalarMeromorphic C.surface W := by
    apply C.meromorphic_paste _ G (scalarMeromorphic_of_scalarHolomorphic S₀ _ hw) hG
    intro j t
    have ht : (t : ℂ) ∈ puncturedDisk 0 (rootRadius (R.radius j.1) (M j).degree) := by
      simpa only [puncturedDisk, Set.mem_ofPred_eq, sub_zero, D, attachmentData] using t.property
    exact (hGmatch j t ht).trans (congrArg sphereFinite ((M j).root_eq t))
  refine ⟨R, M, hfin, D.topology, C.surface, S₀, W, C.parameterChart,
    hcompact, C.oldEmbedding, D.dense_old, hcoords, C.old_holomorphic,
    C.old_locallyBiholomorphic, hbase, hW, (fun x => rfl), ?_,
    K, s, hK, hgood, hs, hKX, hdisks, hcover⟩
  intro j
  refine ⟨?_, ?_, C.parameter_target j, C.parameter_center j, hsymm j, ?_⟩
  · rw [C.atlas_eq]
    exact Or.inr ⟨j, rfl⟩
  · rw [C.parameter_source j]
    exact attachment_chart_source P d hP hdeg hd R M j
  · intro t ht
    rw [C.parameter_target j] at ht
    rw [C.parameter_symm j ⟨t, ht⟩]
    rw [← attachment_projection_eq P d hP hdeg hd R M]
    exact congrFun (D.extendedProjection_psi j) ⟨t, ht⟩

end D12Complex.CompactCompletion
