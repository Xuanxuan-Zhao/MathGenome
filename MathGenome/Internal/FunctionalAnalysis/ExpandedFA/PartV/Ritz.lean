import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.Ritz
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.GalerkinCea
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open scoped InnerProductSpace Topology ComplexConjugate ENNReal
namespace ExpandedFA.PartV.Ritz
open ExpandedFA.Hilbert.Conventions.Spec
open GalerkinCea (galerkin_orthogonality_of_equations)
universe u v

/-- The energy inner product and its complete norm, with both norm structures
explicit throughout the comparison and the transfer of completeness. -/
theorem energy_hilbert_norm : Spec.EnergyHilbertNorm.{u, v} := by
  intro 𝕜 H _ n₀ _ _ a M α hM hα ha
  have hnonneg (x : H) : 0 ≤ RCLike.re (a x x) :=
    (mul_nonneg hα.1.le (sq_nonneg ‖x‖)).trans (hα.2 x)
  have hdefinite (x : H) (hx : a x x = 0) : x = 0 := by
    have hc := hα.2 x
    rw [hx, map_zero] at hc
    have hn : ‖x‖ ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hc hα.1
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg x])
  let c : InnerProductSpace.Core 𝕜 H :=
    { inner := fun x y => a x y
      conj_inner_symm := fun x y => (ha x y).symm
      re_inner_nonneg := hnonneg
      definite := hdefinite
      add_left := fun x y z =>
        congrArg (fun f : H →L[𝕜] 𝕜 => f z) (a.map_add x y)
      smul_left := fun x y r =>
        congrArg (fun f : H →L[𝕜] 𝕜 => f y) (a.map_smulₛₗ r x) }
  have hlower (x : H) :
      Real.sqrt α * ‖x‖ ≤ Real.sqrt (RCLike.re (a x x)) := by
    calc
      Real.sqrt α * ‖x‖ = Real.sqrt (α * ‖x‖ ^ 2) := by
        rw [Real.sqrt_mul hα.1.le, Real.sqrt_sq (norm_nonneg x)]
      _ ≤ Real.sqrt (RCLike.re (a x x)) := Real.sqrt_le_sqrt (hα.2 x)
  have hupper (x : H) :
      Real.sqrt (RCLike.re (a x x)) ≤ Real.sqrt M * ‖x‖ := by
    have hr : RCLike.re (a x x) ≤ M * ‖x‖ ^ 2 := by
      calc
        RCLike.re (a x x) ≤ ‖a x x‖ := RCLike.re_le_norm _
        _ ≤ M * ‖x‖ * ‖x‖ := hM x x
        _ = M * ‖x‖ ^ 2 := by ring
    calc
      Real.sqrt (RCLike.re (a x x)) ≤ Real.sqrt (M * ‖x‖ ^ 2) :=
        Real.sqrt_le_sqrt hr
      _ = Real.sqrt M * ‖x‖ := by
        rw [Real.sqrt_mul' M (sq_nonneg ‖x‖), Real.sqrt_sq (norm_nonneg x)]
  let n₁ : NormedAddCommGroup H := c.toNormedAddCommGroup
  have hf : @UniformContinuous H H
      n₀.toMetricSpace.toUniformSpace n₁.toMetricSpace.toUniformSpace id := by
    have hf : @LipschitzWith H H n₀.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        n₁.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace ⟨Real.sqrt M, Real.sqrt_nonneg M⟩ id := by
      apply @LipschitzWith.of_dist_le_mul H H n₀.toMetricSpace.toPseudoMetricSpace
        n₁.toMetricSpace.toPseudoMetricSpace _ id
      intro x y
      rw [@dist_eq_norm H n₁.toSeminormedAddCommGroup,
        @dist_eq_norm H n₀.toSeminormedAddCommGroup]
      change Real.sqrt (RCLike.re (a (x - y) (x - y))) ≤
        Real.sqrt M * @norm H n₀.toNorm (x - y)
      exact hupper (x - y)
    exact @LipschitzWith.uniformContinuous H H
      n₀.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      n₁.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace _ id hf
  have hs : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα.1
  have hg : @UniformContinuous H H
      n₁.toMetricSpace.toUniformSpace n₀.toMetricSpace.toUniformSpace id := by
    have hg : @LipschitzWith H H n₁.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        n₀.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
        ⟨(Real.sqrt α)⁻¹, (inv_pos.mpr hs).le⟩ id := by
      apply @LipschitzWith.of_dist_le_mul H H n₁.toMetricSpace.toPseudoMetricSpace
        n₀.toMetricSpace.toPseudoMetricSpace _ id
      intro x y
      rw [@dist_eq_norm H n₀.toSeminormedAddCommGroup,
        @dist_eq_norm H n₁.toSeminormedAddCommGroup]
      change @norm H n₀.toNorm (x - y) ≤ (Real.sqrt α)⁻¹ *
        Real.sqrt (RCLike.re (a (x - y) (x - y)))
      have hb := (le_div_iff₀ hs).mpr (by
        simpa only [mul_comm] using hlower (x - y))
      simpa only [div_eq_mul_inv, mul_comm] using hb
    exact @LipschitzWith.uniformContinuous H H
      n₁.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace
      n₀.toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace _ id hg
  have hu : n₁.toMetricSpace.toUniformSpace = n₀.toMetricSpace.toUniformSpace :=
    le_antisymm (le_iff_uniformContinuous_id.mpr hg)
      (le_iff_uniformContinuous_id.mpr hf)
  refine ⟨?_, c, (fun _ _ => rfl), (fun _ _ => rfl), ?_, ?_, ?_⟩
  · intro x
    refine ⟨(RCLike.conj_eq_iff_re.mp (ha x x).symm).symm, hnonneg x, ?_⟩
    exact ⟨hdefinite x, fun hx => by simp [hx]⟩
  · intro x
    exact ⟨rfl, hlower x, hupper x⟩
  · change @CompleteSpace H n₁.toMetricSpace.toUniformSpace
    rw [hu]
    infer_instance
  · exact congrArg (fun u : UniformSpace H => u.toTopologicalSpace) hu

/-- Galerkin orthogonality identifies the native energy orthogonal projection. -/
theorem ritz_energy_projection : Spec.EnergyProjection.{u, v} := by
  intro 𝕜 H _ n₀ _ _ a M α hM hα ha F W hW u u_h hu huh
  have ho := galerkin_orthogonality_of_equations 𝕜 H a F W u u_h hu huh
  obtain ⟨_, c, hc, hi, hnorm, hcomplete, htop⟩ :=
    energy_hilbert_norm 𝕜 H a M α hM hα ha
  refine ⟨c, hc, hnorm, hcomplete, htop, ?_⟩
  letI : Module 𝕜 H := inferInstance
  letI := c.toNormedAddCommGroup
  letI := InnerProductSpace.ofCore c.toCore
  letI : CompleteSpace H := hcomplete
  have hW' : IsClosed (W : Set H) := by
    change @IsClosed H c.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace _
    rw [htop]
    exact hW
  refine ⟨hi, hW', ?_⟩
  letI : CompleteSpace W := hW'.isComplete.completeSpace_coe
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero u_h.property
  intro w hw
  rw [hi, ha, ho ⟨w, hw⟩, map_zero]

/-- The real quadratic form has an exact orthogonal splitting. -/
private theorem ritz_quadratic_pythagoras
    {𝕜 : Type u} {H : Type v} [RCLike 𝕜] [NormedAddCommGroup H]
    [NormedSpace 𝕜 H] (a : BoundedSesquilinearFormValue 𝕜 H H)
    (ha : FormHermitianValue 𝕜 H a) (W : Submodule 𝕜 H)
    (u : H) (u_h : W) (ho : ∀ v : W, a (v : H) (u - (u_h : H)) = 0)
    (v : W) :
    RCLike.re (a (u - (v : H)) (u - (v : H))) =
      RCLike.re (a (u - (u_h : H)) (u - (u_h : H))) +
      RCLike.re (a ((u_h : H) - (v : H)) ((u_h : H) - (v : H))) := by
  have h₁ : a ((u_h : H) - (v : H)) (u - (u_h : H)) = 0 := ho (u_h - v)
  have h₂ : a (u - (u_h : H)) ((u_h : H) - (v : H)) = 0 := by
    rw [ha, h₁, map_zero]
  have he : u - (v : H) = (u - (u_h : H)) + ((u_h : H) - (v : H)) := by abel
  rw [he, a.map_add]
  simp only [add_apply, map_add, h₁, h₂, add_zero, zero_add]

/-- Exact Pythagoras gives the attained and unique energy best approximation. -/
theorem ritz_energy_best_approximation : Spec.EnergyBestApproximation.{u, v} := by
  intro 𝕜 H _ _ _ _ a M α hM hα ha F W hW u u_h hu huh
  have ho := galerkin_orthogonality_of_equations 𝕜 H a F W u u_h hu huh
  have hn (x : H) : 0 ≤ RCLike.re (a x x) :=
    (mul_nonneg hα.1.le (sq_nonneg ‖x‖)).trans (hα.2 x)
  let d := fun v : W => Real.sqrt (RCLike.re (a (u - (v : H)) (u - (v : H))))
  have hp (v : W) : d v ^ 2 = d u_h ^ 2 +
      Real.sqrt (RCLike.re (a ((u_h : H) - (v : H)) ((u_h : H) - (v : H)))) ^ 2 := by
    simp only [d, Real.sq_sqrt (hn _)]
    exact ritz_quadratic_pythagoras a ha W u u_h ho v
  have hm (v : W) : d u_h ≤ d v := by
    have h := hp v
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).mp
      (by nlinarith [sq_nonneg (Real.sqrt (RCLike.re
        (a ((u_h : H) - (v : H)) ((u_h : H) - (v : H)))))])
  have heq (v : W) : d v = d u_h ↔ v = u_h := by
    constructor
    · intro hv
      have h := hp v
      rw [hv, Real.sq_sqrt (hn ((u_h : H) - (v : H)))] at h
      have hc := hα.2 ((u_h : H) - (v : H))
      have hz : ‖(u_h : H) - (v : H)‖ ^ 2 ≤ 0 :=
        nonpos_of_mul_nonpos_right (by linarith) hα.1
      have he : (u_h : H) - (v : H) = 0 :=
        norm_eq_zero.mp (by nlinarith [norm_nonneg ((u_h : H) - (v : H))])
      exact (Subtype.ext (sub_eq_zero.mp he)).symm
    · rintro rfl
      rfl
  refine ⟨hp, ⟨⟨u_h, rfl⟩, ?_⟩, heq, u_h, hm, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact hm v
  · intro w hw
    exact (heq w).mp (le_antisymm (hw u_h) (hm w))

namespace Counterexample
open Spec.Counterexample

variable (𝕜 : Type u) [RCLike 𝕜]

lemma norm_e (i : ℕ+) : ‖e 𝕜 i‖ = 1 := by
  simp [e, lp.norm_single (by norm_num : 0 < (2 : ℝ≥0∞))]

lemma initialSpan_zero : initialSpan 𝕜 0 = ⊥ := by
  simp [initialSpan]

lemma trial_even (n : ℕ) : trialSpace 𝕜 (2*n) = initialSpan 𝕜 n := by
  simp [trialSpace]

lemma trial_odd (n : ℕ) : trialSpace 𝕜 (2*n+1) = ⊥ := by
  simp [trialSpace, Nat.add_mod]

lemma e_mem_initialSpan (i : ℕ+) (n : ℕ) (hi : i.val ≤ n) :
    e 𝕜 i ∈ initialSpan 𝕜 n := by
  change (i : ℕ) ≤ n at hi
  have hip : 0 < (i : ℕ) := i.pos
  let j : Fin n := ⟨(i : ℕ) - 1, by omega⟩
  apply Submodule.subset_span
  refine ⟨j, ?_⟩
  have h : (⟨j.val + 1, Nat.succ_pos _⟩ : ℕ+) = i := by
    apply Subtype.ext
    change (i : ℕ) - 1 + 1 = (i : ℕ)
    omega
  exact congrArg (e 𝕜) h

lemma initialSpan_finite (n : ℕ) : FiniteDimensional 𝕜 (initialSpan 𝕜 n) :=
  FiniteDimensional.span_of_finite 𝕜 (Set.finite_range _)

end Counterexample
open Spec.Counterexample Counterexample

theorem nonnested_trial_description : TrialDescription.{u} := by
  intro 𝕜 _
  exact ⟨by simp [trialSpace, initialSpan_zero], trial_even 𝕜, trial_odd 𝕜⟩

theorem nonnested_closed_trial_spaces : ClosedTrialSpaces.{u} := by
  intro 𝕜 _ m
  have h : FiniteDimensional 𝕜 (trialSpace 𝕜 m) := by
    by_cases hm : m % 2 = 0
    · rw [trialSpace, ite_eq_left hm]
      exact initialSpan_finite 𝕜 _
    · rw [trialSpace, ite_eq_right hm]
      infer_instance
  let := h
  exact ⟨h, (trialSpace 𝕜 m).closed_of_finiteDimensional⟩

/-- Finite coordinate sums lie in even trial spaces and converge to each vector. -/
theorem nonnested_dense_union : DenseUnion.{u} := by
  classical
  intro 𝕜 _ x
  refine mem_closure_of_tendsto (lp.hasSum_single ENNReal.ofNat_ne_top x)
    (Filter.Eventually.of_forall ?_)
  intro A
  apply Set.mem_iUnion.mpr
  refine ⟨2 * A.sup (fun i => i.val), ?_⟩
  rw [trial_even]
  apply Submodule.sum_mem
  intro i hi
  have he := e_mem_initialSpan 𝕜 i (A.sup (fun i => i.val)) (Finset.le_sup hi)
  have hs : lp.single 2 i (x i) = x i • e 𝕜 i := by
    rw [e, ← lp.single_smul]
    simp
  rw [hs]
  exact Submodule.smul_mem _ _ he

theorem nonnested_form_and_data : FormAndData.{u} := by
  intro 𝕜 _
  refine ⟨⟨by norm_num, ?_⟩, ⟨by norm_num, ?_⟩, fun _ _ => rfl, fun _ => rfl⟩
  · intro v u
    simpa only [form, innerSL_apply_apply, one_mul] using norm_inner_le_norm v u
  · intro v
    simpa only [form, innerSL_apply_apply, one_mul] using
      (norm_sq_eq_re_inner (𝕜 := 𝕜) v).le

theorem nonnested_exact_solution : ExactSolution.{u} := by
  intro 𝕜 _
  refine ⟨fun _ => rfl, ?_⟩
  intro u hu
  exact ext_inner_left 𝕜 hu

/-- Distinct Galerkin solutions coincide by testing their difference. -/
private lemma inner_galerkin_unique {𝕜 : Type u} [RCLike 𝕜]
    (W : Submodule 𝕜 (Space 𝕜)) {w z : Space 𝕜} (hw : w ∈ W) (hz : z ∈ W)
    (h : ∀ v ∈ W, inner 𝕜 v w = inner 𝕜 v z) : w = z := by
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := 𝕜)).mp
  rw [inner_sub_right, h (w-z) (W.sub_mem hw hz), sub_self]

theorem nonnested_discrete_solutions : DiscreteSolutions.{u} := by
  intro 𝕜 _ m
  by_cases hm : m % 2 = 0 ∧ 0 < m
  · have he : e 𝕜 1 ∈ trialSpace 𝕜 m := by
      simp only [trialSpace, ite_eq_left hm.1]
      apply e_mem_initialSpan
      dsimp
      omega
    have hs : discreteSolution 𝕜 m = e 𝕜 1 := ite_eq_left hm
    refine ⟨hs.symm ▸ he, ?_, ?_⟩
    · intro v hv
      rw [hs]
      rfl
    · intro w hw h
      rw [hs]
      exact inner_galerkin_unique (trialSpace 𝕜 m) hw he h
  · have hW : trialSpace 𝕜 m = ⊥ := by
      by_cases hz : m = 0
      · subst m
        exact (nonnested_trial_description 𝕜).1
      · have ho : m % 2 ≠ 0 := fun h => hm ⟨h, Nat.pos_of_ne_zero hz⟩
        exact ite_eq_right ho
    have hs : discreteSolution 𝕜 m = 0 := ite_eq_right hm
    refine ⟨hs.symm ▸ (trialSpace 𝕜 m).zero_mem, ?_, ?_⟩
    · intro v hv
      have hv0 : v = 0 := by simpa only [hW, Submodule.mem_bot] using hv
      simp [hv0, form, datum]
    · intro w hw h
      have hw0 : w = 0 := by simpa only [hW, Submodule.mem_bot] using hw
      exact hw0.trans hs.symm

theorem nonnested_odd_solutions : OddSolutions.{u} := by
  intro 𝕜 _ n
  have hs : discreteSolution 𝕜 (2*n+1) = 0 := by
    simp [discreteSolution, Nat.add_mod]
  exact ⟨hs, by rw [hs, sub_zero, norm_e]⟩

theorem nonnested_nonconvergence : Nonconvergence.{u} := by
  intro 𝕜 _ h
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp h (1/2) (by norm_num)
  have hbad := hN (2*N+1) (by omega)
  have he := (nonnested_odd_solutions 𝕜 N).2
  rw [dist_eq_norm, norm_sub_rev, he] at hbad
  norm_num at hbad

theorem nonnested_failure_of_eventual_approximation : FailureOfEventualApproximation.{u} := by
  intro 𝕜 _
  refine ⟨1, by norm_num, ?_⟩
  intro N
  refine ⟨2*N+1, by omega, ?_⟩
  intro v hv
  have hv0 : v = 0 := by simpa only [trial_odd, Submodule.mem_bot] using hv
  rw [hv0, sub_zero, norm_e]

end ExpandedFA.PartV.Ritz
