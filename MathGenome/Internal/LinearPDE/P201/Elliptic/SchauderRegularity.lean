import MathGenome.Internal.LinearPDE.P201Specs.Elliptic.SchauderRegularity
import MathGenome.Internal.LinearPDE.P201.Elliptic.ConstantSchauder

import MathGenome.Internal.LinearPDE.P201.Elliptic.BallSchauderSolvability
import MathGenome.Internal.LinearPDE.P201.Elliptic.VariableSchauder
/-!
Conditional derivation of the initially C² interior Schauder theorem.
For the qualitative step we move c*u to the source and solve the equation
with zeroth-order coefficient zero on a small ball. Since u is C², this
new source is Hölder. Continuous-data uniqueness identifies that solution
with u. We then apply the a priori estimate to the original operator.
-/
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology

namespace P201.Elliptic.SchauderRegularity
open P201Specs P201Specs.Elliptic
open P201Specs.Elliptic.NewtonHessian P201Specs.Elliptic.PoissonSchauder
open P201Specs.Elliptic.VariableSchauder P201Specs.Elliptic.BallSchauderSolvability
open P201Specs.Elliptic.SchauderRegularity
open P201.Elliptic.PoissonSchauder P201.Elliptic.ConstantSchauder

/-- Finitely many locally Hölder scalar fields have a common ball on
which all their Hölder bounds are finite. -/
lemma finite_holder_radius {n : ℕ} {ι : Type} [Fintype ι] {α : ℝ}
    {Ω : Domain n} {F : ι → Space n → ℝ}
    (hF : ∀ i, IsHolderLoc α (F i) Ω) {x : Space n} (hx : x ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ball x r ⊆ (Ω : Set (Space n)) ∧
      ∀ i, IsHolderOn α (F i) (ball x r) := by
  classical
  have aux (s : Finset ι) : ∃ r : ℝ, 0 < r ∧
      ball x r ⊆ (Ω : Set (Space n)) ∧
      ∀ i ∈ s, IsHolderOn α (F i) (ball x r) := by
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
      exact ⟨r, hr, hsub, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨r, hr, hsub, hs⟩ := ih
      obtain ⟨R, hR, _, hRi⟩ := hF i x hx
      refine ⟨min r R, lt_min hr hR,
        (ball_subset_ball (min_le_left _ _)).trans hsub, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact isHolderOn_mono hRi (ball_subset_ball (min_le_right _ _))
      · exact isHolderOn_mono (hs j hj) (ball_subset_ball (min_le_left _ _))
  obtain ⟨r, hr, hsub, hs⟩ := aux Finset.univ
  exact ⟨r, hr, hsub, fun i => hs i (Finset.mem_univ _)⟩

/-- A C¹ function on a compact convex set is bounded Hölder for every
exponent between zero and one. Only regularity on that set is needed. -/
lemma contDiffOn_holder_compact_convex {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) {u : Space n → ℝ} {s : Set (Space n)}
    (hu : ContDiffOn ℝ 1 u s) (hs : IsCompact s) (hc : Convex ℝ s) :
    IsHolderOn α u s := by
  obtain ⟨L, hL⟩ := hu.exists_lipschitzOnWith (by norm_num) hc hs
  exact isHolderOn_of_bounded_lipschitz hα hα1
    (boundedOn_of_continuousOn_compact hs hu.continuousOn) hL

/-- Equality on an open set identifies all actual classical derivatives. -/
lemma multiPartial_eqOn_open {n : ℕ} {u v : Space n → ℝ} {s : Set (Space n)}
    (hs : IsOpen s) (h : EqOn u v s) (I : MultiIndex n) :
    EqOn (multiPartial u I) (multiPartial v I) s := by
  intro x hx
  have he : u =ᶠ[𝓝 x] v := mem_of_superset (hs.mem_nhds hx) fun y hy => h hy
  exact (P102.U4.partialWord_eventuallyEq he (I.sort (· ≤ ·))).eq_of_nhds

/-- Continuous-data ball solvability suffices for the qualitative upgrade.
The zeroth-order term is moved to the Hölder source, so no sign condition
on the original c is used. -/
lemma local_regularity_of_continuous_solvability
    (hcontinuous : ContinuousSolvabilityStatement) :
    P201Specs.Elliptic.SchauderRegularity.LocalRegularityStatement := by
  intro n hn α hα hα1 Ω a b c u f ha hcoef hu hf heq
  refine ⟨hu, ?_⟩
  intro x hx
  let F : ((Fin n × Fin n) ⊕ (Fin n ⊕ Bool)) → Space n → ℝ
    | Sum.inl (i, j) => fun y => a y i j
    | Sum.inr (Sum.inl i) => fun y => b y i
    | Sum.inr (Sum.inr false) => c
    | Sum.inr (Sum.inr true) => f
  have hF : ∀ i, IsHolderLoc α (F i) Ω := by
    rintro (⟨i, j⟩ | (i | t))
    · exact hcoef.1 i j
    · exact hcoef.2.1 i
    · cases t
      · exact hcoef.2.2
      · exact hf
  obtain ⟨ρ, hρ, hρΩ, hρF⟩ := finite_holder_radius hF hx
  obtain ⟨R, hR, _, ell, hell, hRa⟩ := ha x hx
  let r : ℝ := min R ρ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r]; linarith [min_le_left R ρ]
  have hrρ : r < ρ := by dsimp [r]; linarith [min_le_right R ρ]
  have hsubρ : closedBall x r ⊆ ball x ρ := closedBall_subset_ball hrρ
  have hsubΩ : closedBall x r ⊆ (Ω : Set (Space n)) := hsubρ.trans hρΩ
  have hcoeff0 : CoefficientsHolderOn α a b (fun _ => 0) (closedBall x r) := by
    refine ⟨fun i j => isHolderOn_mono (hρF (Sum.inl (i, j))) hsubρ,
      fun i => isHolderOn_mono (hρF (Sum.inr (Sum.inl i))) hsubρ, ?_⟩
    exact ⟨0, 0, le_rfl, le_rfl, by simp, by simp⟩
  have hcH : IsHolderOn α c (closedBall x r) :=
    isHolderOn_mono (hρF (Sum.inr (Sum.inr false))) hsubρ
  have hfH : IsHolderOn α f (closedBall x r) :=
    isHolderOn_mono (hρF (Sum.inr (Sum.inr true))) hsubρ
  have huH : IsHolderOn α u (closedBall x r) :=
    contDiffOn_holder_compact_convex hα.le hα1.le
      ((hu.of_le (by norm_num)).mono hsubΩ)
      (isCompact_closedBall x r) (convex_closedBall x r)
  have hsource : IsHolderOn α (fun y => f y - c y * u y) (closedBall x r) := by
    exact isHolderOn_add hfH (isHolderOn_neg (isHolderOn_mul hcH huH))
  have haB : UniformlyEllipticOn ell a (closedBall x r) := by
    have hsubR : closedBall x r ⊆ ball x R := closedBall_subset_ball hrR
    exact ⟨fun y hy => hRa.1 y (hsubR hy), fun y hy => hRa.2 y (hsubR hy)⟩
  let g : C(sphere x r, ℝ) := ⟨fun ζ => u ζ,
    continuousOn_iff_continuous_domRestrict.mp
      (hu.continuousOn.mono (sphere_subset_closedBall.trans hsubΩ))⟩
  obtain ⟨v, hv, hvreg, hunique⟩ := hcontinuous hn α hα hα1 x r hr
    a b (fun _ => 0) ⟨ell, hell, haB⟩ hcoeff0 (by simp)
    (fun y => f y - c y * u y) hsource g
  have huSol : IsBallSolution a b (fun _ => 0) (fun y => f y - c y * u y)
      x r g u := by
    refine ⟨hu.mono (ball_subset_closedBall.trans hsubΩ),
      hu.continuousOn.mono hsubΩ, ?_, fun _ => rfl⟩
    intro y hy
    have h := heq y (hsubΩ (ball_subset_closedBall hy))
    simp only [nondivergenceOperator, zero_mul, add_zero] at h ⊢
    linarith
  have he : EqOn u v (ball x r) :=
    (hunique u huSol).mono ball_subset_closedBall
  obtain ⟨s, hs, _, hvH⟩ := hvreg.2 x (mem_ball_self hr)
  refine ⟨min r s, lt_min hr hs,
    ((ball_subset_ball (min_le_left _ _)).trans ball_subset_closedBall).trans hsubΩ, ?_⟩
  intro i j
  apply isHolderOn_congr (isHolderOn_mono (hvH i j)
    (ball_subset_ball (min_le_right _ _)))
  intro y hy
  exact multiPartial_eqOn_open isOpen_ball he {i, j}
    ((ball_subset_ball (min_le_left _ _)) hy)

/-- Global uniform ellipticity implies the local condition, without any
boundedness, connectedness or boundary assumption on the domain. -/
lemma locallyUniformlyEllipticOn_of_uniform {n : ℕ} {Ω : Domain n}
    {a : Space n → Matrix (Fin n) (Fin n) ℝ} {ell : ℝ}
    (hell : 0 < ell) (ha : UniformlyEllipticOn ell a Ω) :
    LocallyUniformlyEllipticOn a Ω := by
  intro x hx
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp Ω.isOpen x hx
  exact ⟨r, hr, hsub, ell, hell,
    fun y hy => ha.1 y (hsub hy), fun y hy => ha.2 y (hsub hy)⟩

/-- Conditional draft: all frozen premises occur in the prescribed order.
Only continuous-data ball solvability is needed for this assertion. -/
theorem local_regularity_conditional :
    ContinuousSolvabilityStatement →
    HolderSolvabilityStatement →
    LocalBoundaryRegularityStatement →
    GlobalEstimateStatement →
    P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement →
    LocalBoundaryEstimateStatement →
    P201Specs.Elliptic.SchauderRegularity.LocalRegularityStatement := by
  intro hcontinuous _ _ _ _ _
  exact local_regularity_of_continuous_solvability hcontinuous

/-- The quantitative conclusion uses the a priori estimate on the original
operator after the qualitative upgrade. All six conditional premises are
explicit, including those not needed by this proof route. -/
theorem interior_estimate_conditional :
    ContinuousSolvabilityStatement →
    HolderSolvabilityStatement →
    LocalBoundaryRegularityStatement →
    GlobalEstimateStatement →
    P201Specs.Elliptic.VariableSchauder.InteriorEstimateStatement →
    LocalBoundaryEstimateStatement →
    P201Specs.Elliptic.SchauderRegularity.InteriorEstimateStatement := by
  intro hcontinuous _ _ _ hinterior _ n hn α hα hα1 Ω Ω' Ω'' hb hcl hΩ ell K hell hK
  obtain ⟨C, hC, hest⟩ := hinterior hn α hα hα1 Ω Ω' Ω'' hb hcl hΩ ell K hell hK
  refine ⟨C, hC, ?_⟩
  intro a b c ha hcoef hcoeffinite hnorm u f hu hf heq hub hfb
  have hureg := local_regularity_of_continuous_solvability hcontinuous
    hn α hα hα1 Ω a b c u f (locallyUniformlyEllipticOn_of_uniform hell ha)
    hcoef hu hf heq
  exact hest a b c ha hcoef hcoeffinite hnorm u f hureg hf heq hub hfb

end P201.Elliptic.SchauderRegularity

theorem _root_.«P201».«Elliptic».«SchauderRegularity».«interior_estimate» : _root_.«P201Specs».«Elliptic».«SchauderRegularity».«InteriorEstimateStatement» :=
  @_root_.«P201».«Elliptic».«SchauderRegularity».«interior_estimate_conditional» (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«continuous_solvability») (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«holder_solvability») (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«local_boundary_regularity») (@_root_.«P201».«Elliptic».«VariableSchauder».«global_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«interior_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«local_boundary_estimate»)
theorem _root_.«P201».«Elliptic».«SchauderRegularity».«local_regularity» : _root_.«P201Specs».«Elliptic».«SchauderRegularity».«LocalRegularityStatement» :=
  @_root_.«P201».«Elliptic».«SchauderRegularity».«local_regularity_conditional» (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«continuous_solvability») (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«holder_solvability») (@_root_.«P201».«Elliptic».«BallSchauderSolvability».«local_boundary_regularity») (@_root_.«P201».«Elliptic».«VariableSchauder».«global_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«interior_estimate») (@_root_.«P201».«Elliptic».«VariableSchauder».«local_boundary_estimate»)
