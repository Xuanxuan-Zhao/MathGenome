import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch12.SchwarzChristoffel
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch12.PolygonVertex
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch10.HalfplaneAutomorphisms
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PrimitivePeriodCriterion
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Topology.ExtendFrom
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Analysis.Complex.RealDeriv
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Complex Filter Metric
open scoped Topology BigOperators

namespace D12Complex.SchwarzChristoffel
open PolygonVertex

namespace Definitions
abbrev integrand := @D12Complex.SchwarzChristoffel.integrand
abbrev poleSum := @D12Complex.SchwarzChristoffel.poleSum
abbrev correctedLogDeriv := @D12Complex.SchwarzChristoffel.correctedLogDeriv
end Definitions

lemma isOpen_halfPlane : IsOpen halfPlane :=
  isOpen_lt continuous_const continuous_im

lemma isDomain_halfPlane : IsDomain halfPlane :=
  ⟨⟨I, by simp [halfPlane]⟩, isOpen_halfPlane,
    (convex_halfSpace_im_gt 0).isPreconnected⟩

/-- The chosen branch is an exponential, so no factor ever vanishes. -/
theorem integrand_ne_zero :
    Specs.D12Complex.Ch12.SchwarzChristoffel.integrand_ne_zero_type := by
  intro n a α z
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  exact Exponential.E_ne_zero _

/-- Product differentiation in logarithmic-derivative form, including the
empty product. All powers use one fixed upper-half-plane branch. -/
lemma hasDerivAt_upperPower_product {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) (b : ι → ℂ) {z : ℂ} (hz : z ∈ halfPlane) :
    HasDerivAt (fun w => ∏ j ∈ s, upperPower (b j) (a j) w)
      ((∏ j ∈ s, upperPower (b j) (a j) z) *
        ∑ j ∈ s, b j / (z - (a j : ℂ))) z := by
  induction s using Finset.induction_on with
  | empty => simpa using hasDerivAt_const z (1 : ℂ)
  | @insert j s hj ih =>
    have hd := (PolygonVertex.hasDerivAt_upperPower (b j) (a j) hz).mul ih
    convert hd using 1
    · funext w
      simp only [Finset.prod_insert hj]
      rfl
    · simp only [Finset.prod_insert hj, Finset.sum_insert hj]
      ring

theorem hasDerivAt_integrand :
    Specs.D12Complex.Ch12.SchwarzChristoffel.hasDerivAt_integrand_type := by
  intro n a α z hz
  exact hasDerivAt_upperPower_product Finset.univ a (fun j => (α j : ℂ) - 1) hz

theorem holomorphic_integrand :
    Specs.D12Complex.Ch12.SchwarzChristoffel.holomorphic_integrand_type := by
  intro n a α
  exact ⟨isOpen_halfPlane, fun z hz => (hasDerivAt_integrand n a α z hz).differentiableAt⟩

/-- Once F′ = CQ is known, the normalized primitive is (F-F(z₀))/C.
The endpoint theorem supplies the integral along every admissible path. -/
theorem primitive_formula :
    Specs.D12Complex.Ch12.SchwarzChristoffel.primitive_formula_type := by
  intro n a α F C hC hF hd
  have hQc : ContinuousOn (integrand a α) halfPlane :=
    fun z hz => ((holomorphic_integrand n a α).2 z hz).continuousAt.continuousWithinAt
  have hB (z₀ : ℂ) : Primitives.IsPrimitive halfPlane (integrand a α)
      (fun z => (F z - F z₀) / C) := by
    refine ⟨⟨isOpen_halfPlane, fun z hz => ((hF.2 z hz).sub_const _).div_const _⟩, ?_⟩
    intro z hz
    rw [((hF.2 z hz).hasDerivAt.sub_const (F z₀) |>.div_const C).deriv, hd z hz]
    exact mul_div_cancel_left₀ _ hC
  refine ⟨Primitives.primitive_endpointIndependent halfPlane (integrand a α)
    (fun z => (F z - F I) / C) hQc (hB I), ?_⟩
  intro z₀ hz₀
  refine ⟨(fun z => (F z - F z₀) / C), hB z₀, by simp, ?_, ?_⟩
  · intro z _
    field_simp
    ring
  · intro γ hγ hs
    have he := Primitives.piecewise_endpoint halfPlane (integrand a α)
      (fun z => (F z - F z₀) / C) hQc (hB z₀) γ hγ
    rw [hs] at he
    simp only [sub_self, zero_div, sub_zero] at he
    rw [he]
    field_simp
    ring

private lemma holomorphic_deriv {U : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn U f) : HolomorphicOn U (deriv f) := by
  refine ⟨hf.1, fun z hz => ?_⟩
  have ha : AnalyticAt ℂ f z :=
    (show DifferentiableOn ℂ f U from fun w hw =>
      (hf.2 w hw).differentiableWithinAt).analyticAt (hf.1.mem_nhds hz)
  exact ha.deriv.differentiableAt

/-- Constancy of F′/Q follows from the proved logarithmic-derivative identity.
In particular neither that identity nor a global factorization is hidden in
holomorphy or the boundary data. -/
theorem formula_of_logDeriv :
    Specs.D12Complex.Ch12.SchwarzChristoffel.formula_of_logDeriv_type := by
  intro n a α F hF hn he
  have hdF := holomorphic_deriv hF
  let R : ℂ → ℂ := fun z => deriv F z / integrand a α z
  have hdR : ∀ z ∈ halfPlane, HasDerivAt R 0 z := by
    intro z hz
    have hQn := integrand_ne_zero n a α z
    have hF2 : deriv (deriv F) z = poleSum a α z * deriv F z :=
      (div_eq_iff (hn z hz)).mp (he z hz)
    have hh := (hdF.2 z hz).hasDerivAt.div (hasDerivAt_integrand n a α z hz) hQn
    have hzero : (deriv (deriv F) z * integrand a α z -
        deriv F z * (integrand a α z * poleSum a α z)) / integrand a α z ^ 2 = 0 := by
      rw [hF2]
      ring
    convert hh using 1
    exact hzero.symm
  obtain ⟨C, hC⟩ := isOpen_halfPlane.exists_is_const_of_deriv_eq_zero
    (convex_halfSpace_im_gt 0).isPreconnected
    (fun z hz => (hdR z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hdR z hz).deriv)
  have hderiv : ∀ z ∈ halfPlane, deriv F z = C * integrand a α z := by
    intro z hz
    exact (div_eq_iff (integrand_ne_zero n a α z)).mp (hC z hz)
  have hCn : C ≠ 0 := by
    intro hzero
    have hI : I ∈ halfPlane := by simp [halfPlane]
    have h := hderiv I hI
    rw [hzero, zero_mul] at h
    exact hn I hI h
  exact ⟨C, hCn, hderiv, primitive_formula n a α F C hCn hF hderiv⟩

/-- Liouville is used only after an entire correction and its genuine global
limit have been proved. -/
theorem formula_of_entire_correction :
    Specs.D12Complex.Ch12.SchwarzChristoffel.formula_of_entire_correction_type := by
  intro n a α F hF hn h hh he ht
  have hzero : ∀ z : ℂ, h z = 0 :=
    fun z => (show Differentiable ℂ h from fun w => hh.2 w (mem_univ w)).apply_eq_of_tendsto_cocompact z ht
  apply formula_of_logDeriv n a α F hF hn
  intro z hz
  have hz' := (he hz).symm.trans (hzero z)
  exact sub_eq_zero.mp hz'

/-- The local finite-vertex conclusion is retained for both infinity cases. -/
theorem finite_vertex_factors :
    Specs.D12Complex.Ch12.SchwarzChristoffel.finite_vertex_factors_type := by
  intro n a α β P F G h j
  exact PolygonVertex.polygon_vertex P F G h.domain h.bounded h.biholomorphic
    ⟨h.extension, h.agrees⟩ (a j) (α j) (h.angle_pos j) (h.angle_lt_two j) (h.vertex j)

/-- The boundary extension takes infinity to the boundary: an interior
image would already have a finite preimage under the interior inverse. -/
lemma extension_infinity_frontier {P : Set ℂ} {F G : ℂ → ℂ}
    (hp : BiholomorphicPair halfPlane P F G)
    (e : compactifiedClosedHalfPlane ≃ₜ closure P)
    (he : ∀ (z : ℂ) (hz : z ∈ closedHalfPlane),
      (e ⟨sphereFinite z, Or.inr ⟨z, hz, rfl⟩⟩ : ℂ) = F z) :
    (e ⟨sphereInfty, Or.inl rfl⟩ : ℂ) ∈ frontier P := by
  let w : ℂ := e ⟨sphereInfty, Or.inl rfl⟩
  rw [hp.2.1.1.frontier_eq]
  refine ⟨(e ⟨sphereInfty, Or.inl rfl⟩).property, ?_⟩
  intro hw
  have hg : G w ∈ closedHalfPlane :=
    le_of_lt (show 0 < (G w).im from hp.2.2.2.1 hw)
  have heq : e ⟨sphereFinite (G w), Or.inr ⟨G w, hg, rfl⟩⟩ =
      e ⟨sphereInfty, Or.inl rfl⟩ := by
    apply Subtype.ext
    exact (he (G w) hg).trans (hp.2.2.2.2.2 hw)
  have heq' := congrArg Subtype.val (e.injective heq)
  exact (OnePoint.coe_ne_infty (G w)) heq'

lemma extension_real_ne_infinity {P : Set ℂ} {F : ℂ → ℂ}
    (e : compactifiedClosedHalfPlane ≃ₜ closure P)
    (he : ∀ (z : ℂ) (hz : z ∈ closedHalfPlane),
      (e ⟨sphereFinite z, Or.inr ⟨z, hz, rfl⟩⟩ : ℂ) = F z)
    (x : ℝ) : F x ≠ (e ⟨sphereInfty, Or.inl rfl⟩ : ℂ) := by
  intro hx
  have hxC : (x : ℂ) ∈ closedHalfPlane := by simp [closedHalfPlane]
  have heq : e ⟨sphereFinite x, Or.inr ⟨x, hxC, rfl⟩⟩ =
      e ⟨sphereInfty, Or.inl rfl⟩ :=
    Subtype.ext ((he x hxC).trans hx)
  exact (OnePoint.coe_ne_infty (x : ℂ)) (congrArg Subtype.val (e.injective heq))

/-- Check the actual polygon-to-local-data specialization in the case where
infinity is an interior point of a side. -/
theorem finite_boundary_data :
    Specs.D12Complex.Ch12.SchwarzChristoffel.finite_boundary_data_type := by
  intro n P v α F G a hP hp e he ha hav hinfty
  have hbe : HasBoundaryExtension P F := ⟨e, he⟩
  have hi := (PolygonVertex.boundary_extension_data hbe).2.1
  refine ⟨⟨hP.domain, hP.bounded, hp, e, he, ha, hP.angle_pos, hP.angle_lt_two,
    ?_, ?_, by norm_num, by norm_num, ?_⟩⟩
  · intro j
    rw [hav j]
    exact hP.vertex j
  · intro x hx
    apply hP.side (F x) (PolygonVertex.boundary_real_frontier hp hbe (by simp))
    rintro ⟨j, hj⟩
    have heq : F x = F (a j) := hj.symm.trans (hav j).symm
    have hxx : (x : ℂ) = (a j : ℂ) :=
      hi (by simp [closedHalfPlane]) (by simp [closedHalfPlane]) heq
    exact hx ⟨j, (Complex.ofReal_inj.mp hxx).symm⟩
  · exact hP.side _ (extension_infinity_frontier hp e he) hinfty

/-- In the second source case only the finite n vertices are included;
the (n+1)st angle is recorded separately at infinity. -/
theorem infinity_boundary_data :
    Specs.D12Complex.Ch12.SchwarzChristoffel.infinity_boundary_data_type := by
  intro n P v α F G a hP hp e he ha hav hinfty
  have hbe : HasBoundaryExtension P F := ⟨e, he⟩
  have hi := (PolygonVertex.boundary_extension_data hbe).2.1
  refine ⟨⟨hP.domain, hP.bounded, hp, e, he, ha,
    (fun j => hP.angle_pos j.castSucc), (fun j => hP.angle_lt_two j.castSucc),
    ?_, ?_, hP.angle_pos (Fin.last n), hP.angle_lt_two (Fin.last n), ?_⟩⟩
  · intro j
    rw [hav j]
    exact hP.vertex j.castSucc
  · intro x hx
    apply hP.side (F x) (PolygonVertex.boundary_real_frontier hp hbe (by simp))
    have hn : ∀ j : Fin (n+1), F x ≠ v j := by
      intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · rw [← hinfty]
        exact extension_real_ne_infinity e he x
      · intro hj
        have heq : F x = F (a i) := hj.trans (hav i).symm
        have hxx : (x : ℂ) = (a i : ℂ) :=
          hi (by simp [closedHalfPlane]) (by simp [closedHalfPlane]) heq
        exact hx ⟨i, (Complex.ofReal_inj.mp hxx).symm⟩
    rintro ⟨j, hj⟩
    exact hn j hj.symm
  · rw [hinfty]
    exact hP.vertex (Fin.last n)

/-- Assembly at the level of full Prop types, keeping both missing analytic
claims visible. This implication is not the source theorem itself. -/
theorem assemble : Specs.D12Complex.Ch12.SchwarzChristoffel.assemble_type := by
  intro hcont hdecay n a α β P F G h
  obtain ⟨H, hH, he, hs⟩ := hcont n a α β P F G h
  refine ⟨formula_of_entire_correction n a α F h.biholomorphic.1
    (fun z hz => (AnalyticArcs.biholomorphic_deriv_ne_zero h.biholomorphic hz).1)
    H hH he (hdecay n a α β P F G h H hH he hs), ?_⟩
  exact finite_vertex_factors n a α β P F G h

/-- Both original polygon statements are actual specializations of the
single local-geometric statement, with exactly n or n−1 finite factors. -/
theorem specialize : Specs.D12Complex.Ch12.SchwarzChristoffel.specialize_type := by
  intro hall
  constructor
  · intro n P v α F G a hP hp e he ha hav hinfty
    obtain ⟨h⟩ := finite_boundary_data n P v α F G a hP hp e he ha hav hinfty
    obtain ⟨hformula, hfac⟩ := hall n a α 1 P F G h
    refine ⟨hformula, fun j => ?_⟩
    simpa only [hav j] using hfac j
  · intro n P v α F G a hP hp e he ha hav hinfty
    obtain ⟨h⟩ := infinity_boundary_data n P v α F G a hP hp e he ha hav hinfty
    obtain ⟨hformula, hfac⟩ := hall n a (fun j => α j.castSucc) (α (Fin.last n)) P F G h
    refine ⟨hformula, fun j => ?_⟩
    simpa only [hav j] using hfac j



/-- Finite collections of poles can be avoided on a whole neighborhood. -/
lemma avoid_finite_prevertices {n : ℕ} (a : Fin n → ℝ) (s : Finset (Fin n))
    (x : ℂ) (hx : ∀ j ∈ s, x ≠ (a j : ℂ)) :
    ∃ r : ℝ, 0 < r ∧ ∀ z ∈ ball x r, ∀ j ∈ s, z ≠ (a j : ℂ) := by
  have he : ∀ᶠ z in 𝓝 x, ∀ j ∈ s, z ≠ (a j : ℂ) :=
    s.eventually_all.mpr fun j hj =>
      (isOpen_ne_fun continuous_id continuous_const).mem_nhds (hx j hj)
  exact Metric.eventually_nhds_iff.mp he

lemma differentiableAt_pole_sum {n : ℕ} (a : Fin n → ℝ) (α : Fin n → ℝ)
    (s : Finset (Fin n)) (z : ℂ) (hz : ∀ j ∈ s, z ≠ (a j : ℂ)) :
    DifferentiableAt ℂ (fun w => ∑ j ∈ s, ((α j : ℂ) - 1) / (w - (a j : ℂ))) z := by
  apply DifferentiableAt.fun_sum
  intro j hj
  exact (differentiableAt_const ((α j : ℂ) - 1)).div (differentiableAt_id.sub_const _) (sub_ne_zero.mpr (hz j hj))

/-- The logarithmic derivative and its finite pole correction are holomorphic
in the actual upper half-plane. -/
theorem holomorphic_correction {n : ℕ} (a : Fin n → ℝ) (α : Fin n → ℝ)
    {P : Set ℂ} {F G : ℂ → ℂ} (hp : BiholomorphicPair halfPlane P F G) :
    HolomorphicOn halfPlane (correctedLogDeriv a α F) := by
  have hd := holomorphic_deriv hp.1
  have hdd := holomorphic_deriv hd
  refine ⟨isOpen_halfPlane, fun z hz => ?_⟩
  apply ((hdd.2 z hz).div (hd.2 z hz)
    (AnalyticArcs.biholomorphic_deriv_ne_zero hp hz).1).sub
  apply differentiableAt_pole_sum a α Finset.univ z
  intro j _ hj
  have : z.im = 0 := by rw [hj]; simp
  exact (ne_of_gt hz) this

/-- At each real point the corrected logarithmic derivative has a genuine
holomorphic extension from above. At a vertex only the *other* pole terms
are subtracted from the accepted local extension. -/
theorem local_correction {n : ℕ} {a : Fin n → ℝ} {α : Fin n → ℝ} {β : ℝ}
    {P : Set ℂ} {F G : ℂ → ℂ} (h : BoundaryData a α β P F G) (x : ℝ) :
    ∃ (r : ℝ) (b : ℂ → ℂ), 0 < r ∧ HolomorphicOn (ball (x : ℂ) r) b ∧
      EqOn b (correctedLogDeriv a α F) (ball (x : ℂ) r ∩ halfPlane) := by
  classical
  by_cases hx : x ∈ range a
  · obtain ⟨k, rfl⟩ := hx
    obtain ⟨r, b, hr, hb, he⟩ := (finite_vertex_factors n a α β P F G h k).2
    obtain ⟨s, hs, hav⟩ := avoid_finite_prevertices a (Finset.univ.erase k) (a k) (by
      intro j hj
      exact fun heq => (Finset.mem_erase.mp hj).1
        (h.ordered.injective (Complex.ofReal_inj.mp heq).symm))
    refine ⟨min r s, fun z => b z - ∑ j ∈ Finset.univ.erase k,
      ((α j : ℂ) - 1) / (z - (a j : ℂ)), lt_min hr hs,
      ⟨isOpen_ball, ?_⟩, ?_⟩
    · intro z hz
      exact (hb.2 z (ball_subset_ball (min_le_left _ _) hz)).sub
        (differentiableAt_pole_sum a α _ z
          (hav z (ball_subset_ball (min_le_right _ _) hz)))
    · intro z hz
      have hez := he z ⟨ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
      dsimp [correctedLogDeriv, poleSum]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
      rw [← hez]
      ring
  · obtain ⟨r, b, hr, hb, he⟩ := (PolygonVertex.polygon_vertex_angle_one P F G
      h.domain h.bounded h.biholomorphic ⟨h.extension, h.agrees⟩ x (h.side x hx)).2
    obtain ⟨s, hs, hav⟩ := avoid_finite_prevertices a Finset.univ x (by
      intro j _ heq
      exact hx ⟨j, (Complex.ofReal_inj.mp heq).symm⟩)
    refine ⟨min r s, fun z => b z - poleSum a α z, lt_min hr hs,
      ⟨isOpen_ball, ?_⟩, ?_⟩
    · intro z hz
      exact (hb.2 z (ball_subset_ball (min_le_left _ _) hz)).sub
        (differentiableAt_pole_sum a α _ z
          (hav z (ball_subset_ball (min_le_right _ _) hz)))
    · intro z hz
      have hez := he z ⟨ball_subset_ball (min_le_left _ _) hz.1, hz.2⟩
      simpa [correctedLogDeriv] using congrArg (fun w => w - poleSum a α z) hez.symm

lemma closure_halfPlane : closure halfPlane = closedHalfPlane :=
  Complex.closure_setOfPred_lt_im 0

/-- The canonical upper-side continuous extension agrees with any local
holomorphic continuation, by uniqueness of limits from the genuine domain. -/
lemma extendFrom_eq_local {f b : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hb : HolomorphicOn U b) (he : EqOn b f (U ∩ halfPlane))
    {z : ℂ} (hz : z ∈ U) (hzH : z ∈ closedHalfPlane) :
    extendFrom halfPlane f z = b z := by
  apply extendFrom_eq (closure_halfPlane ▸ hzH)
  apply ((hb.2 z hz).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [nhdsWithin_le_nhds (hU.mem_nhds hz), self_mem_nhdsWithin] with w hw hwH
  exact he ⟨hw, hwH⟩

lemma upper_correction_limit {n : ℕ} {a : Fin n → ℝ} {α : Fin n → ℝ} {β : ℝ}
    {P : Set ℂ} {F G : ℂ → ℂ} (h : BoundaryData a α β P F G)
    {z : ℂ} (hz : z ∈ closedHalfPlane) :
    ∃ w, Tendsto (correctedLogDeriv a α F) (𝓝[halfPlane] z) (𝓝 w) := by
  change 0 ≤ z.im at hz
  rcases lt_or_eq_of_le hz with hpos | hzero
  · exact ⟨correctedLogDeriv a α F z,
      ((holomorphic_correction a α h.biholomorphic).2 z hpos).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds⟩
  · have hzr : (z.re : ℂ) = z := by apply Complex.ext <;> simp [← hzero]
    obtain ⟨r, b, hr, hb, he⟩ := local_correction h z.re
    rw [hzr] at hb he
    refine ⟨b z, ?_⟩
    apply ((hb.2 z (mem_ball_self hr)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hr)),
      self_mem_nhdsWithin] with w hw hwH
    exact he ⟨hw, hwH⟩

lemma continuousOn_upper_correction {n : ℕ} {a : Fin n → ℝ} {α : Fin n → ℝ} {β : ℝ}
    {P : Set ℂ} {F G : ℂ → ℂ} (h : BoundaryData a α β P F G) :
    ContinuousOn (extendFrom halfPlane (correctedLogDeriv a α F)) closedHalfPlane := by
  apply continuousOn_extendFrom
  · exact fun z hz => closure_halfPlane ▸ hz
  · exact fun z hz => upper_correction_limit h hz

/-- A holomorphic function real on a real interval has real derivative there.
The proof restricts the actual complex derivative to real increments. -/
lemma deriv_real_on_diameter {r : ℝ} {x : ℝ} {q : ℂ → ℂ}
    (hq : HolomorphicOn (ball (x : ℂ) r) q)
    (hr : ∀ z ∈ Reflection.diameter (x : ℂ) r, (q z).im = 0)
    {y : ℝ} (hy : (y : ℂ) ∈ ball (x : ℂ) r) : (deriv q (y : ℂ)).im = 0 := by
  have hd := ((hq.2 y hy).hasDerivAt.const_mul (-I)).real_of_complex
  have he : (fun t : ℝ => ((-I) * q t).re) =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [continuous_ofReal.continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds hy)] with t ht
    simpa using hr t ⟨ht, by simp⟩
  have hh := hd.congr_of_eventuallyEq he.symm
  have hh' := hh.unique (hasDerivAt_const y (0 : ℝ))
  simpa using hh'

open private side_frontier_real from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch12.PolygonVertex

/-- A continuation across an open side can be straightened by one affine
map so that both its first and second derivatives are real on the diameter. -/
lemma side_straightening {P : Set ℂ} {F G : ℂ → ℂ}
    (hP : IsDomain P) (hPb : Bornology.IsBounded P)
    (hp : BiholomorphicPair halfPlane P F G) (he : HasBoundaryExtension P F)
    (x : ℝ) (hcorner : Corner P (F x) 1) :
    ∃ (r : ℝ) (q : ℂ → ℂ) (c : ℂ), 0 < r ∧ c ≠ 0 ∧
      HolomorphicOn (ball (x : ℂ) r) q ∧ deriv q (x : ℂ) ≠ 0 ∧
      (∀ z ∈ Reflection.diameter (x : ℂ) r, (q z).im = 0) ∧
      EqOn q (fun z => (F z - F x) / c) (ball (x : ℂ) r ∩ halfPlane) := by
  obtain ⟨t, f, ht, hf, hfn, hfe⟩ :=
    PolygonVertex.polygon_side P F G hP hPb hp he x hcorner
  obtain ⟨c, R, hc, hR, hgeom⟩ := hcorner
  have hc0 : c ≠ 0 := by intro hh; simp [hh] at hc
  have hxH : (x : ℂ) ∈ closedHalfPlane := by simp [closedHalfPlane]
  have hpre := ((PolygonVertex.boundary_extension_data he).1 x hxH).preimage_mem_nhdsWithin
    (isOpen_ball.mem_nhds (mem_ball_self hR))
  obtain ⟨s, hs, hval⟩ := Metric.mem_nhdsWithin_iff.mp hpre
  let q : ℂ → ℂ := fun z => (f z - F x) / c
  have hq : HolomorphicOn (ball (x : ℂ) (min t s)) q := by
    refine ⟨isOpen_ball, fun z hz => ?_⟩
    exact ((hf.2 z (ball_subset_ball (min_le_left _ _) hz)).sub_const _).div_const c
  refine ⟨min t s, q, c, lt_min ht hs, hc0, hq, ?_, ?_, ?_⟩
  · change deriv (fun z => (f z - F x) / c) (x : ℂ) ≠ 0
    rw [((hf.2 x (mem_ball_self ht)).hasDerivAt.sub_const (F x) |>.div_const c).deriv]
    exact div_ne_zero hfn hc0
  · intro z hz
    change ((f z - F x) / c).im = 0
    rw [hfe ⟨ball_subset_ball (min_le_left _ _) hz.1, le_of_eq hz.2.symm⟩]
    exact side_frontier_real hp.2.1.1 hc0 hgeom (boundary_real_frontier hp he hz.2)
      (hval ⟨ball_subset_ball (min_le_right _ _) hz.1, le_of_eq hz.2.symm⟩)
  · intro z hz
    change (f z - F x) / c = (F z - F x) / c
    rw [hfe ⟨ball_subset_ball (min_le_left _ _) hz.1, (show 0 ≤ z.im from le_of_lt hz.2)⟩]

lemma poleSum_real {n : ℕ} (a : Fin n → ℝ) (α : Fin n → ℝ) (x : ℝ) :
    (poleSum a α (x : ℂ)).im = 0 := by
  have he : star (poleSum a α (x : ℂ)) = poleSum a α (x : ℂ) := by
    simp [poleSum]
  exact Complex.conj_eq_iff_im.mp he

/-- On an open side the continuous upper correction is real. Its value is
computed by a limit of the straightened map's logarithmic derivative. -/
lemma upper_correction_real_at_side {n : ℕ} {a : Fin n → ℝ} {α : Fin n → ℝ} {β : ℝ}
    {P : Set ℂ} {F G : ℂ → ℂ} (h : BoundaryData a α β P F G)
    (x : ℝ) (hx : x ∉ range a) :
    (extendFrom halfPlane (correctedLogDeriv a α F) (x : ℂ)).im = 0 := by
  obtain ⟨r, q, c, hr, hc, hq, hqn, hqr, he⟩ := side_straightening h.domain h.bounded
    h.biholomorphic ⟨h.extension, h.agrees⟩ x (h.side x hx)
  have hqd := holomorphic_deriv hq
  have hqdd := holomorphic_deriv hqd
  have hreal1 := deriv_real_on_diameter hq hqr (mem_ball_self hr)
  have hreal2 := deriv_real_on_diameter hqd (fun z hz => by
    have hzR : (z.re : ℂ) = z := by
      apply Complex.ext
      · simp
      · exact hz.2.symm
    have hh := deriv_real_on_diameter hq hqr (hzR.symm ▸ hz.1)
    rwa [hzR] at hh) (mem_ball_self hr)
  have hd (z : ℂ) (hz : z ∈ ball (x : ℂ) r ∩ halfPlane) :
      deriv q z = deriv F z / c := by
    have hloc : q =ᶠ[𝓝 z] fun w => (F w - F x) / c :=
      by
        filter_upwards [(isOpen_ball.inter isOpen_halfPlane).mem_nhds hz] with w hw
        exact he hw
    exact hloc.deriv_eq.trans
      (((h.biholomorphic.1.2 z hz.2).hasDerivAt.sub_const (F x) |>.div_const c).deriv)
  have hdd (z : ℂ) (hz : z ∈ ball (x : ℂ) r ∩ halfPlane) :
      deriv (deriv q) z = deriv (deriv F) z / c := by
    have hloc : deriv q =ᶠ[𝓝 z] fun w => deriv F w / c :=
      by
        filter_upwards [(isOpen_ball.inter isOpen_halfPlane).mem_nhds hz] with w hw
        exact hd w hw
    exact hloc.deriv_eq.trans
      (((holomorphic_deriv h.biholomorphic.1).2 z hz.2).hasDerivAt.div_const c).deriv
  let b : ℂ → ℂ := fun z => deriv (deriv q) z / deriv q z - poleSum a α z
  have hbc : ContinuousAt b (x : ℂ) := by
    apply (((hqdd.2 x (mem_ball_self hr)).continuousAt).div
      ((hqd.2 x (mem_ball_self hr)).continuousAt) hqn).sub
    exact (differentiableAt_pole_sum a α Finset.univ x (by
      intro j _ heq; exact hx ⟨j, (Complex.ofReal_inj.mp heq).symm⟩)).continuousAt
  have hl : Tendsto (correctedLogDeriv a α F) (𝓝[halfPlane] (x : ℂ)) (𝓝 (b x)) := by
    apply (hbc.tendsto.mono_left nhdsWithin_le_nhds).congr'
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hr)),
      self_mem_nhdsWithin] with z hz hzH
    dsimp [b, correctedLogDeriv]
    rw [hd z ⟨hz, hzH⟩, hdd z ⟨hz, hzH⟩, div_div_div_cancel_right₀ hc]
  rw [extendFrom_eq (closure_halfPlane ▸ (show (x : ℂ) ∈ closedHalfPlane by simp [closedHalfPlane])) hl]
  have hL : (deriv (deriv q) (x : ℂ) / deriv q (x : ℂ)).im = 0 :=
    Complex.conj_eq_iff_im.mp (by
      rw [map_div₀, Complex.conj_eq_iff_im.mpr hreal1,
        Complex.conj_eq_iff_im.mpr hreal2])
  simp [b, sub_im, poleSum_real, hL]

/-- Continuity fills in the finitely many prevertices after reality has been
proved on all the open sides. -/
lemma upper_correction_real {n : ℕ} {a : Fin n → ℝ} {α : Fin n → ℝ} {β : ℝ}
    {P : Set ℂ} {F G : ℂ → ℂ} (h : BoundaryData a α β P F G) (x : ℝ) :
    (extendFrom halfPlane (correctedLogDeriv a α F) (x : ℂ)).im = 0 := by
  have hc : Continuous (fun y : ℝ =>
      (extendFrom halfPlane (correctedLogDeriv a α F) (y : ℂ)).im) := by
    exact continuous_im.comp ((continuousOn_upper_correction h).comp_continuous
      continuous_ofReal (fun y => by simp [closedHalfPlane]))
  have hd : Dense ((range a)ᶜ : Set ℝ) := (countable_range a).dense_compl ℝ
  exact congrFun (hc.ext_on hd continuous_const
    (fun y hy => upper_correction_real_at_side h y hy)) x

/-- The corrected logarithmic derivative extends to an entire symmetric
function. Pole removal, real side values, and the global gluing are all
conclusions obtained from the geometric boundary hypotheses. -/
theorem entire_correction : Specs.D12Complex.Ch12.SchwarzChristoffel.entire_correction_type := by
  intro n a α β P F G h
  let b := extendFrom halfPlane (correctedLogDeriv a α F)
  have hc := continuousOn_upper_correction h
  have he : EqOn b (correctedLogDeriv a α F) halfPlane :=
    extendFrom_extends (fun z hz =>
      ((holomorphic_correction a α h.biholomorphic).2 z hz).continuousAt.continuousWithinAt)
  have hb : HolomorphicOn halfPlane b := by
    refine ⟨isOpen_halfPlane, fun z hz => ?_⟩
    apply ((holomorphic_correction a α h.biholomorphic).2 z hz).congr_of_eventuallyEq
    filter_upwards [isOpen_halfPlane.mem_nhds hz] with w hw
    exact he hw
  have hr : ∀ z : ℂ, z.im = 0 → (b z).im = 0 := by
    intro z hz
    have hez : (z.re : ℂ) = z := by
      apply Complex.ext
      · simp
      · exact hz.symm
    simpa only [hez] using upper_correction_real h z.re
  have hlocal (x : ℝ) (r : ℝ) (hrpos : 0 < r) :=
    Reflection.schwarz_reflection (x : ℂ) r b (by simp) hrpos
      (show HolomorphicOn (Reflection.upper (x : ℂ) r) b from
        ⟨isOpen_ball.inter isOpen_halfPlane, fun z hz => hb.2 z hz.2⟩)
      (hc.mono (fun z hz => hz.2)) (fun z hz => hr z hz.2)
  refine ⟨Reflection.extension b, ⟨isOpen_univ, ?_⟩, ?_, ?_⟩
  · intro z _
    have hpos : 0 < dist z (z.re : ℂ) + 1 := by positivity
    exact (hlocal z.re _ hpos).1.2 z (by
      change dist z (z.re : ℂ) < dist z (z.re : ℂ) + 1
      linarith)
  · intro z hz
    change (if 0 ≤ z.im then b z else star (b (star z))) = correctedLogDeriv a α F z
    rw [ite_eq_left (le_of_lt (show 0 < z.im from hz))]
    exact he hz
  · intro z
    have hpos : 0 < dist z (z.re : ℂ) + 1 := by positivity
    exact (hlocal z.re _ hpos).2.2.2 z (by
      change dist z (z.re : ℂ) < dist z (z.re : ℂ) + 1
      linarith)

/-- The half-plane coordinate exchanging zero and infinity. -/
def inversion (z : ℂ) : ℂ := -z⁻¹

def inversionSphere : RiemannSphere → RiemannSphere :=
  Mobius.mobiusMap !![0, -1; 1, 0]

lemma inversionSphere_infty : inversionSphere sphereInfty = sphereFinite 0 := by
  simp [inversionSphere, Mobius.mobiusMap, Mobius.spherePair, sphereInfty]

lemma inversionSphere_zero : inversionSphere (sphereFinite 0) = sphereInfty := by
  simp [inversionSphere, Mobius.mobiusMap, Mobius.spherePair, sphereFinite]

lemma inversionSphere_finite (z : ℂ) (hz : z ≠ 0) :
    inversionSphere (sphereFinite z) = sphereFinite (inversion z) := by
  simp [inversionSphere, Mobius.mobiusMap, Mobius.spherePair, sphereFinite, hz,
    inversion, div_eq_mul_inv]

lemma inversion_involutive (z : ℂ) : inversion (inversion z) = z := by
  simp [inversion]

lemma inversionSphere_involutive : Function.Involutive inversionSphere := by
  intro p
  induction p using OnePoint.rec with
  | infty =>
    change inversionSphere (inversionSphere sphereInfty) = sphereInfty
    rw [inversionSphere_infty, inversionSphere_zero]
  | coe z =>
    change inversionSphere (inversionSphere (sphereFinite z)) = sphereFinite z
    by_cases hz : z = 0
    · subst z; rw [inversionSphere_zero, inversionSphere_infty]
    · rw [inversionSphere_finite z hz, inversionSphere_finite _ (by simpa [inversion] using hz),
        inversion_involutive]

lemma continuous_inversionSphere : Continuous inversionSphere := by
  apply continuousOn_univ.mp
  apply sphereHolomorphicOn_continuousOn
  exact Mobius.mobiusMap_holomorphic _ (by norm_num [Mobius.Regular, Matrix.det_fin_two])

lemma inversion_mem_closedHalfPlane {z : ℂ} (hz : z ∈ closedHalfPlane) :
    inversion z ∈ closedHalfPlane := by
  change 0 ≤ (-z⁻¹).im
  simpa only [neg_im, Complex.inv_im, neg_div, neg_neg] using div_nonneg hz (Complex.normSq_nonneg z)

lemma inversion_mem_halfPlane {z : ℂ} (hz : z ∈ halfPlane) :
    inversion z ∈ halfPlane := by
  have hz0 : z ≠ 0 := by intro he; simp [halfPlane, he] at hz
  change 0 < (-z⁻¹).im
  simpa only [neg_im, Complex.inv_im, neg_div, neg_neg] using div_pos hz (Complex.normSq_pos.mpr hz0)

lemma inversionSphere_mapsTo :
    MapsTo inversionSphere compactifiedClosedHalfPlane compactifiedClosedHalfPlane := by
  intro p hp
  rcases hp with hp | ⟨z, hz, rfl⟩
  · rw [show p = sphereInfty from hp, inversionSphere_infty]
    exact Or.inr ⟨0, by simp [closedHalfPlane], rfl⟩
  · by_cases hz0 : z = 0
    · subst z; rw [inversionSphere_zero]; exact Or.inl rfl
    · rw [inversionSphere_finite z hz0]
      exact Or.inr ⟨inversion z, inversion_mem_closedHalfPlane hz, rfl⟩

/-- Restrict the genuine sphere involution to the compactified closed
half-plane, keeping the given topology at zero and infinity. -/
def inversionHomeomorph : compactifiedClosedHalfPlane ≃ₜ compactifiedClosedHalfPlane where
  toEquiv := {
    toFun := fun p => ⟨inversionSphere p, inversionSphere_mapsTo p.property⟩
    invFun := fun p => ⟨inversionSphere p, inversionSphere_mapsTo p.property⟩
    left_inv := fun p => Subtype.ext (inversionSphere_involutive p)
    right_inv := fun p => Subtype.ext (inversionSphere_involutive p) }
  continuous_toFun := (continuous_inversionSphere.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_inversionSphere.comp continuous_subtype_val).subtype_mk _

/-- The chart pullback retains the actual finite boundary value at source
infinity. The arbitrary total value of the original map at zero is irrelevant. -/
def infinityPullback (F : ℂ → ℂ) (v : ℂ) (z : ℂ) : ℂ :=
  if z = 0 then v else F (inversion z)

lemma infinityPullback_of_mem (F : ℂ → ℂ) (v : ℂ) {z : ℂ} (hz : z ∈ halfPlane) :
    infinityPullback F v z = F (inversion z) := by
  have hz0 : z ≠ 0 := by intro he; simp [halfPlane, he] at hz
  simp [infinityPullback, hz0]

lemma inversion_pair : BiholomorphicPair halfPlane halfPlane inversion inversion := by
  have hh : HolomorphicOn halfPlane inversion := by
    refine ⟨isOpen_halfPlane, fun z hz => ?_⟩
    have hz0 : z ≠ 0 := by intro he; simp [halfPlane, he] at hz
    exact (differentiableAt_inv hz0).neg
  exact ⟨hh, hh, fun _ hz => inversion_mem_halfPlane hz,
    fun _ hz => inversion_mem_halfPlane hz, fun z _ => inversion_involutive z,
    fun z _ => inversion_involutive z⟩

lemma infinityPullback_biholomorphic {P : Set ℂ} {F G : ℂ → ℂ}
    (hp : BiholomorphicPair halfPlane P F G) (v : ℂ) :
    IsBiholomorphism halfPlane P (infinityPullback F v) := by
  have hc := HalfplaneAutomorphisms.pair_comp inversion_pair hp
  apply HalfplaneAutomorphisms.biholomorphism_congr ⟨_, hc⟩
  intro z hz
  exact (infinityPullback_of_mem F v hz).symm

lemma infinityPullback_boundary {P : Set ℂ} {F : ℂ → ℂ}
    (e : compactifiedClosedHalfPlane ≃ₜ closure P)
    (he : ∀ (z : ℂ) (hz : z ∈ closedHalfPlane),
      (e ⟨sphereFinite z, Or.inr ⟨z, hz, rfl⟩⟩ : ℂ) = F z) :
    HasBoundaryExtension P (infinityPullback F (e ⟨sphereInfty, Or.inl rfl⟩)) := by
  refine ⟨inversionHomeomorph.trans e, ?_⟩
  intro z hz
  change (e ⟨inversionSphere (sphereFinite z), _⟩ : ℂ) = _
  by_cases hz0 : z = 0
  · subst z
    simp only [infinityPullback]
    congr 2
    exact Subtype.ext inversionSphere_zero
  · rw [infinityPullback, ite_eq_right hz0]
    have heq : (⟨inversionSphere (sphereFinite z), inversionSphere_mapsTo (Or.inr ⟨z, hz, rfl⟩)⟩ : compactifiedClosedHalfPlane) =
        ⟨sphereFinite (inversion z), Or.inr ⟨inversion z, inversion_mem_closedHalfPlane hz, rfl⟩⟩ :=
      Subtype.ext (inversionSphere_finite z hz0)
    rw [heq]
    exact he (inversion z) (inversion_mem_closedHalfPlane hz)

/-- The given corner at infinity becomes a finite corner in the actual
half-plane chart. Both its factor and corrected logarithmic derivative follow
from the accepted finite-vertex theorem. -/
theorem infinity_corner_factors {n : ℕ} {a : Fin n → ℝ} {α : Fin n → ℝ} {β : ℝ}
    {P : Set ℂ} {F G : ℂ → ℂ} (h : BoundaryData a α β P F G) :
    let φ := infinityPullback F (h.extension ⟨sphereInfty, Or.inl rfl⟩)
    HasCornerFactor φ 0 (φ 0) (β : ℂ) ∧ HasLogDerivExtension φ 0 (β : ℂ) := by
  let φ := infinityPullback F (h.extension ⟨sphereInfty, Or.inl rfl⟩)
  obtain ⟨g, hg⟩ := infinityPullback_biholomorphic h.biholomorphic
    (h.extension ⟨sphereInfty, Or.inl rfl⟩)
  apply PolygonVertex.polygon_vertex P φ g h.domain h.bounded hg
    (infinityPullback_boundary h.extension h.agrees) 0 β h.infinity_angle_pos h.infinity_angle_lt_two
  simpa [φ, infinityPullback] using h.infinity_corner

lemma hasDerivAt_inversion {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt inversion (z⁻¹ ^ 2) z := by
  convert (hasDerivAt_inv hz).neg using 1
  · rfl
  · simp only [neg_neg, inv_pow]

/-- The second-derivative chain rule in the actual inversion chart. -/
lemma logDeriv_inversion {F φ : ℂ → ℂ}
    (hφ : HolomorphicOn halfPlane φ)
    (he : ∀ z ∈ halfPlane, F z = φ (inversion z))
    (hn : ∀ z ∈ halfPlane, deriv φ z ≠ 0)
    {z : ℂ} (hz : z ∈ halfPlane) :
    deriv (deriv F) z / deriv F z =
      z⁻¹ ^ 2 * (deriv (deriv φ) (inversion z) / deriv φ (inversion z)) - 2 * z⁻¹ := by
  have hd (w : ℂ) (hw : w ∈ halfPlane) :
      HasDerivAt F (deriv φ (inversion w) * w⁻¹ ^ 2) w := by
    have hw0 : w ≠ 0 := by intro he; simp [halfPlane, he] at hw
    apply ((hφ.2 _ (inversion_mem_halfPlane hw)).hasDerivAt.comp w
      (hasDerivAt_inversion hw0)).congr_of_eventuallyEq
    filter_upwards [isOpen_halfPlane.mem_nhds hw] with t ht
    exact he t ht
  have hz0 : z ≠ 0 := by intro he; simp [halfPlane, he] at hz
  have h1 := (hd z hz).deriv
  have hh := (((holomorphic_deriv hφ).2 _ (inversion_mem_halfPlane hz)).hasDerivAt.comp z
    (hasDerivAt_inversion hz0)).mul ((hasDerivAt_inv hz0).pow 2)
  have h2 : deriv (deriv F) z = deriv (deriv φ) (inversion z) * z⁻¹ ^ 4 -
      2 * deriv φ (inversion z) * z⁻¹ ^ 3 := by
    have heq : deriv F =ᶠ[𝓝 z] fun w => deriv φ (inversion w) * w⁻¹ ^ 2 := by
      filter_upwards [isOpen_halfPlane.mem_nhds hz] with w hw
      exact (hd w hw).deriv
    rw [heq.deriv_eq]
    convert hh.deriv using 1
    · rfl
    · simp only [Function.comp_apply, Pi.pow_apply, inv_pow,
        Nat.cast_ofNat, Nat.reduceSub, pow_one]
      ring
  rw [h1, h2]
  field_simp [hn _ (inversion_mem_halfPlane hz), hz0]

/-- A full-disk holomorphic remainder in the infinity chart gives the actual
upper exterior identity, including the correct coefficient for an infinity
vertex of arbitrary angle β. -/
theorem infinity_logDeriv {n : ℕ} {a : Fin n → ℝ} {α : Fin n → ℝ} {β : ℝ}
    {P : Set ℂ} {F G : ℂ → ℂ} (h : BoundaryData a α β P F G) :
    ∃ (r : ℝ) (b : ℂ → ℂ), 0 < r ∧ HolomorphicOn (ball (0 : ℂ) r) b ∧
      ∀ z ∈ halfPlane, inversion z ∈ ball (0 : ℂ) r →
        deriv (deriv F) z / deriv F z =
          -((β : ℂ) + 1) * z⁻¹ + z⁻¹ ^ 2 * b (inversion z) := by
  let φ := infinityPullback F (h.extension ⟨sphereInfty, Or.inl rfl⟩)
  obtain ⟨g, hg⟩ := infinityPullback_biholomorphic h.biholomorphic
    (h.extension ⟨sphereInfty, Or.inl rfl⟩)
  obtain ⟨r, b, hr, hb, he⟩ := (infinity_corner_factors h).2
  refine ⟨r, b, hr, hb, ?_⟩
  intro z hz hzr
  have hφ : HolomorphicOn halfPlane φ := hg.1
  have hn : ∀ w ∈ halfPlane, deriv φ w ≠ 0 :=
    fun w hw => (AnalyticArcs.biholomorphic_deriv_ne_zero hg hw).1
  have hcomp : ∀ w ∈ halfPlane, F w = φ (inversion w) := by
    intro w hw
    change F w = infinityPullback F _ (inversion w)
    rw [infinityPullback_of_mem F _ (inversion_mem_halfPlane hw), inversion_involutive]
  rw [logDeriv_inversion hφ hcomp hn hz]
  have hl := he (inversion z) ⟨hzr, inversion_mem_halfPlane hz⟩
  change deriv (deriv φ) (inversion z) / deriv φ (inversion z) -
    ((β : ℂ) - 1) / (inversion z - (0 : ℂ)) = b (inversion z) at hl
  rw [sub_zero] at hl
  rw [(sub_eq_iff_eq_add).mp hl]
  have hz0 : z ≠ 0 := by intro he; simp [halfPlane, he] at hz
  dsimp [inversion]
  field_simp
  ring

lemma tendsto_inversion_cocompact : Tendsto inversion (cocompact ℂ) (𝓝 0) := by
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  unfold inversion
  simpa only [neg_zero] using hi.neg

lemma tendsto_poleSum_cocompact {n : ℕ} (a : Fin n → ℝ) (α : Fin n → ℝ) :
    Tendsto (poleSum a α) (cocompact ℂ) (𝓝 0) := by
  have ht (j : Fin n) : Tendsto (fun z : ℂ => ((α j : ℂ) - 1) / (z - (a j : ℂ)))
      (cocompact ℂ) (𝓝 0) := by
    have hi : Tendsto (fun z : ℂ => (z - (a j : ℂ))⁻¹) (cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded.comp (tendsto_sub_const_cobounded _)
    simpa only [mul_zero, div_eq_mul_inv] using tendsto_const_nhds.mul hi
  unfold poleSum
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => ht j)

/-- For a continuous conjugation-symmetric function an upper-half-plane
limit at infinity determines its full planar limit. Continuity handles the
real axis through closure of the upper exterior. -/
lemma tendsto_zero_of_symmetric_upper {f : ℂ → ℂ} (hc : Continuous f)
    (hs : ∀ z, f (star z) = star (f z))
    (ht : Tendsto f (cocompact ℂ ⊓ 𝓟 halfPlane) (𝓝 0)) :
    Tendsto f (cocompact ℂ) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hev : ∀ᶠ z in cocompact ℂ, z ∈ halfPlane → ‖f z‖ < ε / 2 := by
    have hh := Metric.tendsto_nhds.mp ht (ε / 2) (half_pos hε)
    simpa only [dist_zero_right, eventually_inf_principal] using hh
  rw [← Metric.cobounded_eq_cocompact] at hev
  obtain ⟨R, _, hR⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp hev
  have hclosed : IsClosed {z : ℂ | ‖f z‖ ≤ ε / 2} :=
    isClosed_le hc.norm continuous_const
  have hsub : halfPlane ∩ {z : ℂ | R < ‖z‖} ⊆ {z : ℂ | ‖f z‖ ≤ ε / 2} := by
    intro z hz
    exact (hR (show R ≤ ‖z‖ from le_of_lt hz.2) hz.1).le
  have hbound (z : ℂ) (hz : z ∈ closedHalfPlane) (hzR : R < ‖z‖) : ‖f z‖ ≤ ε / 2 := by
    apply closure_minimal hsub hclosed
    exact (isOpen_lt continuous_const continuous_norm).closure_inter
      ⟨closure_halfPlane ▸ hz, hzR⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_gt_atTop R] with z hzR
  rw [dist_zero_right]
  have hb : ‖f z‖ ≤ ε / 2 := by
    by_cases hz : 0 ≤ z.im
    · exact hbound z hz hzR
    · have hb := hbound (star z) (by
        change 0 ≤ (star z).im
        simpa using (le_of_lt (neg_pos.mpr (lt_of_not_ge hz)) : 0 ≤ -z.im)) (by simpa using hzR)
      simpa only [hs z, norm_star] using hb
  exact lt_of_le_of_lt hb (by linarith)

/-- The entire correction vanishes at infinity in the full planar filter,
using the derived corner expansion in the inversion chart. -/
theorem correction_decay : Specs.D12Complex.Ch12.SchwarzChristoffel.correction_decay_type := by
  intro n a α β P F G h H hH he hs
  obtain ⟨r, b, hr, hb, hlog⟩ := infinity_logDeriv h
  have hbc : ContinuousAt b (0 : ℂ) := (hb.2 0 (mem_ball_self hr)).continuousAt
  have hi : Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  let R : ℂ → ℂ := fun z => -((β : ℂ) + 1) * z⁻¹ + z⁻¹ ^ 2 * b (inversion z) - poleSum a α z
  have ht : Tendsto R (cocompact ℂ) (𝓝 0) := by
    have hh := ((hi.const_mul (-((β : ℂ) + 1))).add
      ((hi.pow 2).mul (hbc.tendsto.comp tendsto_inversion_cocompact))).sub
      (tendsto_poleSum_cocompact a α)
    simpa only [R, Function.comp_apply, mul_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul, add_zero, sub_zero] using hh
  apply tendsto_zero_of_symmetric_upper
    (continuous_iff_continuousAt.mpr (fun z => (hH.2 z (mem_univ z)).continuousAt)) hs
  apply (ht.mono_left inf_le_left).congr'
  filter_upwards [(tendsto_inversion_cocompact.eventually
    (isOpen_ball.mem_nhds (mem_ball_self hr))).filter_mono inf_le_left,
    show ∀ᶠ z in cocompact ℂ ⊓ 𝓟 halfPlane, z ∈ halfPlane from
      Filter.mem_of_superset (Filter.mem_inf_of_right (by simp)) (fun _ hz => hz)] with z hz hzH
  rw [he hzH]
  exact congrArg (fun w => w - poleSum a α z) (hlog z hzH hz).symm

theorem schwarz_christoffel : Specs.D12Complex.Ch12.SchwarzChristoffel.schwarz_christoffel_type :=
  assemble entire_correction correction_decay

theorem finite_prevertices : Specs.D12Complex.Ch12.SchwarzChristoffel.finite_prevertices_type :=
  (specialize schwarz_christoffel).1

theorem infinity_vertex : Specs.D12Complex.Ch12.SchwarzChristoffel.infinity_vertex_type :=
  (specialize schwarz_christoffel).2

end D12Complex.SchwarzChristoffel
