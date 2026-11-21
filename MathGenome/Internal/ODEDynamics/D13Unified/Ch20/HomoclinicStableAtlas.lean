import MathGenome.Internal.ODEDynamics.D13Unified.Ch20.GlobalStableManifold
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! A homoclinic orbit in the global stable set and the resulting difference
between the immersed atlas topology and the ambient subspace topology. -/
noncomputable section
open Set Filter Metric Topology
open scoped ContDiff

namespace D13Unified.Ch20.HomoclinicStableAtlas

open Ch06.StateDerivative Ch07 Ch20.GlobalStableManifold
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch11.Flow
open Specs.D13Unified.Ch20.StableGraphs
open Specs.D13Unified.Ch20.HyperbolicSplitting
open Specs.D13Unified.Ch20.PerronRegularity

def field (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1 - 2 * p.1 ^ 3)

theorem field_smooth (k : ℕ∞) : ContDiff ℝ k field := by
  unfold field
  fun_prop

def equation : AutonomousODE (ℝ × ℝ) :=
  ⟨univ, isOpen_univ, fun p => field p, (field_smooth 1).continuous.comp continuous_subtype_val⟩

@[simp] theorem eval_equation (p : ℝ × ℝ) : equation.eval p = field p := by
  simp [AutonomousODE.eval, autonomousEvalValue, equation]

theorem equation_smooth (k : ℕ∞) : ContDiffOn ℝ k equation.eval equation.domain := by
  rw [show equation.eval = field from funext eval_equation]
  exact (field_smooth k).contDiffOn

private def parametrization (u : ℝ) : ℝ × ℝ :=
  (2 * u / (1 + u ^ 2), 2 * u * (1 - u ^ 2) / (1 + u ^ 2) ^ 2)

private theorem denominator_pos (u : ℝ) : 0 < 1 + u ^ 2 := by positivity

private theorem parametrization_continuous : Continuous parametrization := by
  unfold parametrization
  apply Continuous.prodMk
  · exact (continuous_const.mul continuous_id).div
      (continuous_const.add (continuous_id.pow 2)) (fun u => (denominator_pos u).ne')
  · exact ((continuous_const.mul continuous_id).mul
      (continuous_const.sub (continuous_id.pow 2))).div
        ((continuous_const.add (continuous_id.pow 2)).pow 2)
        (fun u => pow_ne_zero _ (denominator_pos u).ne')

/-- The complete orbit with (x=operatorname{sech}t) and (y=x'). -/
def orbit (t : ℝ) : ℝ × ℝ := parametrization (Real.exp t)

@[simp] theorem orbit_zero : orbit 0 = (1, 0) := by
  norm_num [orbit, parametrization]

theorem orbit_smooth : ContDiff ℝ 1 orbit := by
  have he : ContDiff ℝ 1 (fun t : ℝ => Real.exp t) := Real.contDiff_exp
  have hd : ContDiff ℝ 1 (fun t : ℝ => 1 + Real.exp t ^ 2) :=
    contDiff_const.add (he.pow 2)
  exact ((contDiff_const.mul he).div hd (fun t => (denominator_pos _).ne')).prodMk
    (((contDiff_const.mul he).mul (contDiff_const.sub (he.pow 2))).div (hd.pow 2)
      (fun t => pow_ne_zero _ (denominator_pos _).ne'))

theorem orbit_derivative (t : ℝ) : HasDerivAt orbit (field (orbit t)) t := by
  let u := Real.exp t
  have hu := Real.hasDerivAt_exp t
  have hd := (hu.pow 2).const_add 1
  have hne : 1 + u ^ 2 ≠ 0 := (denominator_pos u).ne'
  have hx := (hu.const_mul 2).div hd hne
  have hy := ((hu.const_mul 2).mul ((hu.pow 2).const_sub 1)).div
    (hd.pow 2) (pow_ne_zero 2 hne)
  convert hx.prodMk hy using 1
  · rfl
  apply Prod.ext
  · simp only [orbit, parametrization, field, Pi.pow_apply, Pi.mul_apply, Pi.div_apply]
    norm_num
    ring
  · simp only [orbit, parametrization, field, Pi.pow_apply, Pi.mul_apply, Pi.div_apply]
    norm_num
    field_simp
    ring

private theorem parametrization_zero : parametrization 0 = 0 := by
  ext <;> norm_num [parametrization]

theorem orbit_tendsto_backward : Tendsto orbit atBot (𝓝 0) := by
  have h := (parametrization_continuous.tendsto 0).comp Real.tendsto_exp_atBot
  change Tendsto (fun t => parametrization (Real.exp t)) atBot (𝓝 0)
  simpa only [parametrization_zero, Function.comp_def] using h

theorem orbit_tendsto_forward : Tendsto orbit atTop (𝓝 0) := by
  have hg : Tendsto (fun t => parametrization (Real.exp (-t))) atTop (𝓝 0) := by
    simpa only [parametrization_zero, Function.comp_def] using
      (parametrization_continuous.tendsto 0).comp Real.tendsto_exp_neg_atTop_nhds_zero
  have hn : Continuous (fun p : ℝ × ℝ => (p.1, -p.2)) :=
    continuous_fst.prodMk continuous_snd.neg
  have ht := (hn.tendsto (0 : ℝ × ℝ)).comp hg
  convert ht using 1
  · funext t
    have he : Real.exp t ≠ 0 := Real.exp_ne_zero t
    simp only [orbit, parametrization, Function.comp_apply, Real.exp_neg]
    apply Prod.ext
    · dsimp only
      field_simp
      ring
    · dsimp only
      field_simp
      ring
  · rw [show ((0 : ℝ × ℝ).1, -(0 : ℝ × ℝ).2) = 0 by ext <;> simp]

/-- The explicit trajectory, rebased at any real time, agrees with the
canonical maximal flow of the same autonomous equation. -/
theorem flow_orbit (s t : ℝ) :
    (t, orbit s) ∈ flowDomain equation ∧ flow equation t (orbit s) = orbit (s+t) := by
  let J : OpenTimeInterval := ⟨⟨univ, univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩
  have hs : orbit s ∈ equation.domain := mem_univ _
  have hc : classicalIVPOnValue equation.toODE J (fun t => orbit (s+t)) 0 (orbit s) := by
    refine ⟨⟨(orbit_smooth.comp (contDiff_const.add contDiff_id)).contDiffOn,
      fun _ _ => mem_univ _, ?_⟩, mem_univ _, by simp⟩
    intro t _
    have hd := (orbit_derivative (s+t)).scomp t ((hasDerivAt_id t).const_add s)
    simpa [Function.comp_def] using hd
  have h := (ODE.canonical_solution equation.toODE
    (equation.locallyLipschitzInState_of_contDiffOn (equation_smooth 1))
    0 (orbit s) hs).2.2.2.2.2.1 J _ hc
  exact ⟨⟨hs, h.1 (mem_univ t)⟩, h.2 (mem_univ t)⟩

theorem orbit_mem_stable (s : ℝ) : orbit s ∈ stableSet equation 0 := by
  refine ⟨mem_univ _, fun t _ => (flow_orbit s t).1, ?_⟩
  have hs := orbit_tendsto_forward.comp
    (tendsto_atTop_add_const_right atTop s tendsto_id)
  exact hs.congr (fun t => by simpa [Function.comp_def, add_comm] using (flow_orbit s t).2.symm)

theorem zero_mem_stable : (0 : ℝ × ℝ) ∈ stableSet equation 0 := by
  let J : OpenTimeInterval := ⟨⟨univ, univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩
  have hc : classicalIVPOnValue equation.toODE J (fun _ => 0) 0 0 := by
    refine ⟨⟨contDiffOn_const, fun _ _ => mem_univ _, ?_⟩, mem_univ _, rfl⟩
    intro t _
    have he : field 0 = 0 := by ext <;> simp [field]
    simpa only [AutonomousODE.toODE_eval, eval_equation, he] using hasDerivAt_const t (0 : ℝ × ℝ)
  have h := (ODE.canonical_solution equation.toODE
    (equation.locallyLipschitzInState_of_contDiffOn (equation_smooth 1))
    0 0 (mem_univ _)).2.2.2.2.2.1 J _ hc
  exact ⟨mem_univ _, fun t _ => ⟨mem_univ _, h.1 (mem_univ t)⟩,
    tendsto_const_nhds.congr (fun t => (h.2 (mem_univ t)).symm)⟩

/-- Stable initial data arbitrarily near the saddle escape every radius
(0<hole 1) in forward time. -/
theorem zero_in_closure_of_escaping_stable (ρ : ℝ) (hρ : ρ ≤ 1) :
    (0 : ℝ × ℝ) ∈ closure
      {p ∈ stableSet equation 0 | ∃ t : ℝ, 0 ≤ t ∧ ρ ≤ ‖flow equation t p‖} := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hball := (Metric.tendsto_nhds.mp orbit_tendsto_backward) ε hε
  obtain ⟨s, hs⟩ := (hball.and (eventually_le_atBot (0 : ℝ))).exists
  refine ⟨orbit s, ⟨orbit_mem_stable s, -s, by linarith [hs.2], ?_⟩, ?_⟩
  · rw [(flow_orbit s (-s)).2, add_neg_cancel, orbit_zero]
    simpa [Prod.norm_def] using hρ
  · simpa [dist_comm] using hs.1

theorem zero_in_closure_outside_local_portion (k : ℕ∞)
    {S T : Submodule ℝ (ℝ × ℝ)} {h : S → T} {V : Set S} {ρ : ℝ}
    (H : LocalPortion k equation 0 S T h V ρ) (hρ : ρ ≤ 1) :
    (0 : ℝ × ℝ) ∈ closure (stableSet equation 0 \ (graphPoint 0 h '' V)) := by
  apply closure_mono _ (zero_in_closure_of_escaping_stable ρ hρ)
  rintro p ⟨hp, t, ht, hlarge⟩
  refine ⟨hp, ?_⟩
  rintro ⟨ξ, hξ, rfl⟩
  obtain ⟨η, hη, he⟩ := H.2.2.2.2.2.2 ξ hξ t ht
  have hsmall := (H.2.2.2.2.1 η hη).2
  rw [he, sub_zero] at hsmall
  exact (not_lt_of_ge hlarge) hsmall

theorem zero_stage_eq_local_portion {S T : Submodule ℝ (ℝ × ℝ)} {h : S → T}
    {V : Set S} : backwardStage equation 0 h V 0 = graphPoint 0 h '' V := by
  have hflow (p : ℝ × ℝ) := Ch11.Flow.flow_zero equation (equation_smooth 1) p (mem_univ p)
  ext p
  constructor
  · rintro ⟨ξ, hξ, rfl⟩
    exact ⟨ξ, hξ.1, by simpa [stageMap] using (hflow (graphPoint 0 h ξ)).2.symm⟩
  · rintro ⟨ξ, hξ, rfl⟩
    refine ⟨ξ, ⟨hξ, ?_⟩, ?_⟩
    · simpa [timeDomainValue] using (hflow (graphPoint 0 h ξ)).1
    · simpa [stageMap] using (hflow (graphPoint 0 h ξ)).2

/-- The zero-stage chart gives an open set that fails to be open in the
ambient subspace topology. -/
theorem atlas_topology_ne_subspace (k : ℕ∞)
    {S T : Submodule ℝ (ℝ × ℝ)} {h : S → T} {V : Set S} {ρ : ℝ}
    (H : LocalPortion k equation 0 S T h V ρ) (hρ : ρ ≤ 1)
    (hzero : (0 : ℝ × ℝ) ∈ graphPoint 0 h '' V)
    (A : StableAtlas k equation 0 h V) :
    A.topology ≠ (inferInstance : TopologicalSpace (stableSet equation 0)) := by
  intro heq
  have hop : @IsOpen (stableSet equation 0) A.topology
      {x : stableSet equation 0 | (x : ℝ × ℝ) ∈ graphPoint 0 h '' V} := by
    have hs := A.source_eq 0
    rw [zero_stage_eq_local_portion] at hs
    letI : TopologicalSpace (stableSet equation 0) := A.topology
    simpa only [hs] using (A.chart 0).open_source
  rw [heq] at hop
  obtain ⟨U, hU, hpre⟩ := isOpen_induced_iff.mp hop
  have hz : (⟨0, zero_mem_stable⟩ : stableSet equation 0) ∈
      {x : stableSet equation 0 | (x : ℝ × ℝ) ∈ graphPoint 0 h '' V} := hzero
  have h0U : (0 : ℝ × ℝ) ∈ U := by
    change (⟨0, zero_mem_stable⟩ : stableSet equation 0) ∈ Subtype.val ⁻¹' U
    rw [hpre]
    exact hz
  obtain ⟨p, hpU, hp⟩ := mem_closure_iff.mp
    (zero_in_closure_outside_local_portion k H hρ) U hU h0U
  have hp' : (⟨p, hp.1⟩ : stableSet equation 0) ∈ Subtype.val ⁻¹' U := hpU
  rw [hpre] at hp'
  exact hp.2 hp'

private def saddle : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 1, 0]

private theorem saddle_hyperbolic : hyperbolicValue saddle := by
  intro μ hμ
  change Module.End.HasEigenvalue (Matrix.toLin' (saddle.map Complex.ofReal)) μ at hμ
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin',
    Polynomial.IsRoot, Matrix.charpoly_fin_two] at hμ
  have he : μ ^ 2 - 1 = 0 := by
    simpa [saddle, Matrix.trace, Matrix.det_fin_two, sub_eq_add_neg] using hμ
  have hf : (μ - 1) * (μ + 1) = 0 := by linear_combination he
  rcases mul_eq_zero.mp hf with h | h
  · obtain rfl : μ = 1 := sub_eq_zero.mp h
    simp
  · obtain rfl : μ = -1 := eq_neg_of_add_eq_zero_left h
    simp

private theorem derivative_at_equilibrium :
    HasFDerivAt equation.eval (matrixOperatorEquiv (Module.Basis.finTwoProd ℝ) saddle) 0 := by
  rw [show equation.eval = field from funext eval_equation]
  have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := (0 : ℝ × ℝ))
  have hy := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := (0 : ℝ × ℝ))
  have hd := hy.prodMk (hx.sub ((hx.pow 3).const_smul 2))
  convert hd using 1
  · funext p
    simp [field]
  · apply ContinuousLinearMap.ext
    intro p
    change (Matrix.toLin (Module.Basis.finTwoProd ℝ) (Module.Basis.finTwoProd ℝ) saddle) p = _
    rw [saddle, Matrix.toLin_finTwoProd_apply]
    simp

/-- The atlas furnished by the global stable-manifold construction can
carry a strictly finer topology than the subspace topology. -/
theorem exists_nonembedded_stable_atlas :
    ∃ (h : stableParameters (Module.Basis.finTwoProd ℝ) saddle →
        unstableParameters (Module.Basis.finTwoProd ℝ) saddle)
      (V : Set (stableParameters (Module.Basis.finTwoProd ℝ) saddle)) (ρ : ℝ)
      (A : StableAtlas 1 equation 0 h V),
      LocalPortion 1 equation 0 _ _ h V ρ ∧ ρ ≤ 1 ∧
      (0 : ℝ × ℝ) ∈ closure (stableSet equation 0 \ (graphPoint 0 h '' V)) ∧
      A.topology ≠ (inferInstance : TopologicalSpace (stableSet equation 0)) := by
  let b := Module.Basis.finTwoProd ℝ
  have hreg := equation_smooth 1
  have he : equation.eval 0 = 0 := by ext <;> simp [field]
  obtain ⟨h, V, ρ, hρ, H, hc⟩ :=
    stable_portion_within b equation 0 saddle 1 (mem_univ _) le_rfl hreg he
      derivative_at_equilibrium saddle_hyperbolic 1 zero_lt_one
  have hset := stableSet_eq_stages equation hreg 0 h V H.2.2.2.2.2.1 hc
  have HH := localPortion_stageHypotheses b saddle saddle_hyperbolic 1 le_rfl equation hreg 0 H
  obtain ⟨D, hU, hmaps⟩ := StableStageCompatibility.atlas_package
    (stableParameters b saddle) (ℝ × ℝ) equation 1 (graphPoint 0 h)
    (fun x => StableGraphs.stableParameterProjection b saddle saddle_hyperbolic (x - 0)) V HH
    ⟨0, H.2.2.2.1⟩
  obtain ⟨A⟩ := stableAtlas_of_stages equation 0 1 D hU hmaps hset
  have hzero : (0 : ℝ × ℝ) ∈ graphPoint 0 h '' V := by
    refine ⟨0, H.2.2.2.1, ?_⟩
    simp [graphPoint, graphMap, H.1.2.1]
  exact ⟨h, V, ρ, A, H, hρ, zero_in_closure_outside_local_portion 1 H hρ,
    atlas_topology_ne_subspace 1 H hρ hzero A⟩

end D13Unified.Ch20.HomoclinicStableAtlas
