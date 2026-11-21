import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.Picard
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.PreHilbertBesselParseval
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! The adjoint identity and Bessel give necessity. Square-summable orthonormal
synthesis gives the reciprocal series. The full left closed span identifies its
image with the datum. Orthogonal decomposition then describes the entire fiber
and proves strict minimum norm, with no separability assumption on the kernels.
-/
noncomputable section
universe u v w z
namespace ExpandedFA.PartV.Picard
open scoped InnerProductSpace Topology
open Spec

variable {𝕜 : Type u} {H : Type v} {G : Type w} {J : Type z} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedAddCommGroup G]
  [InnerProductSpace 𝕜 H] [InnerProductSpace 𝕜 G]
  [CompleteSpace H] [CompleteSpace G]

/-- An orthonormal synthesis series converges whenever its scalar coefficients
are square summable, for arbitrary index type and complete ambient space. -/
lemma orthonormal_synthesis_summable (e : J → H) (he : Orthonormal 𝕜 e)
    (c : J → 𝕜) (hc : Summable (fun j => ‖c j‖ ^ 2)) :
    Summable (fun j => c j • e j) := by
  simpa only [LinearIsometry.toSpanSingleton_apply] using
    (he.orthogonalFamily.summable_iff_norm_sq_summable c).mpr hc

/-- The squared norm of a reciprocal eigenvalue coefficient is precisely the
nonnegative quotient appearing in Picard's condition; signs are retained. -/
lemma reciprocal_coefficient_norm_sq (a : ℝ) (b : 𝕜) :
    ‖(a : 𝕜)⁻¹ * b‖ ^ 2 = ‖b‖ ^ 2 / a ^ 2 := by
  simp only [norm_mul, norm_inv, RCLike.norm_ofReal, mul_pow, inv_pow,
    sq_abs, div_eq_mul_inv]
  exact mul_comm _ _

omit [CompleteSpace H] [CompleteSpace G] in
/-- A solution perpendicular to the kernel is uniquely determined and strictly
minimizes the norm in its fiber. -/
lemma solution_properties (K : H →L[𝕜] G) (f : G) (d : H)
    (hd : K d = f) (hp : d ∈ K.ker.orthogonal) : SolutionProperties K f d := by
  have haff (u : H) : K u = f ↔ ∃ z ∈ K.ker, u = d + z := by
    constructor
    · intro hu
      refine ⟨u - d, ?_, (add_sub_cancel _ _).symm⟩
      change K (u - d) = 0
      rw [map_sub, hu, hd, sub_self]
    · rintro ⟨z, hz, rfl⟩
      change K z = 0 at hz
      rw [map_add, hd, hz, add_zero]
  have hpy (z : H) (hz : z ∈ K.ker) :
      ‖d + z‖ ^ 2 = ‖d‖ ^ 2 + ‖z‖ ^ 2 := by
    simpa only [pow_two] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero d z
        (Submodule.inner_left_of_mem_orthogonal hz hp)
  have hmin (u : H) (hu : K u = f) :
      ‖d‖ ≤ ‖u‖ ∧ (‖u‖ = ‖d‖ ↔ u = d) := by
    obtain ⟨z, hz, rfl⟩ := (haff u).mp hu
    have heq := hpy z hz
    constructor
    · nlinarith [sq_nonneg ‖z‖, norm_nonneg d, norm_nonneg (d + z)]
    · constructor
      · intro h
        rw [h] at heq
        have hzs : ‖z‖ * ‖z‖ = 0 := by nlinarith only [heq]
        have hz0 : z = 0 := norm_eq_zero.mp (mul_self_eq_zero.mp hzs)
        simp only [hz0, add_zero]
      · intro h
        exact congrArg norm h
  refine ⟨hd, hp, ?_, haff, hmin, hpy⟩
  intro u hu hup
  obtain ⟨z, hz, heq⟩ := (haff u).mp hu
  have hzperp : z ∈ K.ker.orthogonal := by
    have hh := K.ker.orthogonal.sub_mem hup hp
    simpa only [heq, add_sub_cancel_left] using hh
  have hz0 : z = 0 := inner_self_eq_zero.mp (hzperp z hz)
  simpa only [hz0, add_zero] using heq

/-- Necessity of the two Picard conditions, directly by the adjoint identity
and Bessel's inequality. -/
lemma diagonal_picard_necessary (K : H →L[𝕜] G)
    (e : J → H) (g : J → G) (a : J → ℝ) (he : Orthonormal 𝕜 e)
    (ha : ∀ j, a j ≠ 0)
    (hA : ∀ j, ContinuousLinearMap.adjoint K (g j) = (a j : 𝕜) • e j)
    (u : H) :
    K u ∈ (ContinuousLinearMap.adjoint K).ker.orthogonal ∧
    Summable (fun j => ‖inner 𝕜 (g j) (K u)‖ ^ 2 / a j ^ 2) := by
  have hcoeff (j : J) : inner 𝕜 (g j) (K u) = (a j : 𝕜) * inner 𝕜 (e j) u := by
    rw [← ContinuousLinearMap.adjoint_inner_left, hA j, inner_smul_left,
      RCLike.conj_ofReal]
  constructor
  · intro y hy
    change ContinuousLinearMap.adjoint K y = 0 at hy
    rw [← ContinuousLinearMap.adjoint_inner_left, hy, inner_zero_left]
  · convert he.inner_products_summable u using 1
    apply funext
    intro j
    rw [hcoeff j, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]
    exact mul_div_cancel_left₀ _ (pow_ne_zero 2 (ha j))

/-- Sufficiency and the convergent formula for a diagonal system. -/
lemma diagonal_picard_solution (K : H →L[𝕜] G)
    (e : J → H) (g : J → G) (a : J → ℝ)
    (he : Orthonormal 𝕜 e) (hg : Orthonormal 𝕜 g) (ha : ∀ j, a j ≠ 0)
    (hK : ∀ j, K (e j) = (a j : 𝕜) • g j)
    (hE : (Submodule.span 𝕜 (Set.range e)).topologicalClosure = K.ker.orthogonal)
    (hG : (Submodule.span 𝕜 (Set.range g)).topologicalClosure =
      (ContinuousLinearMap.adjoint K).ker.orthogonal)
    (f : G) (hf : f ∈ (ContinuousLinearMap.adjoint K).ker.orthogonal)
    (hs : Summable (fun j => ‖inner 𝕜 (g j) f‖ ^ 2 / a j ^ 2)) :
    let terms := fun j => ((a j : 𝕜)⁻¹ * inner 𝕜 (g j) f) • e j
    HasSum terms (∑' j, terms j) ∧ SolutionProperties K f (∑' j, terms j) := by
  let c : J → 𝕜 := fun j => (a j : 𝕜)⁻¹ * inner 𝕜 (g j) f
  have hc : Summable (fun j => ‖c j‖ ^ 2) := by
    simpa only [c, reciprocal_coefficient_norm_sq] using hs
  have hsum := orthonormal_synthesis_summable e he c hc
  have hmap (j : J) : K (c j • e j) = inner 𝕜 (g j) f • g j := by
    rw [map_smul, hK j, smul_smul]
    congr 1
    dsimp [c]
    have hne : (a j : 𝕜) ≠ 0 := by exact_mod_cast ha j
    field_simp
  have hrepr : HasSum (fun j => inner 𝕜 (g j) f • g j) f := by
    have hfspan : f ∈ (Submodule.span 𝕜 (Set.range g)).topologicalClosure := by
      rwa [hG]
    exact (Hilbert.PreHilbertBesselParseval.closedSpan_iff_net_convergence
      𝕜 G J g hg f).mp hfspan
  have hd : K (∑' j, c j • e j) = f := by
    have hh := hsum.hasSum.map K K.continuous
    simp only [Function.comp_def, hmap] at hh
    exact hh.unique hrepr
  have hp : (∑' j, c j • e j) ∈ K.ker.orthogonal := by
    apply K.ker.isClosed_orthogonal.mem_of_tendsto hsum.hasSum
    apply Filter.Eventually.of_forall
    intro F
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    rw [← hE]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨hsum.hasSum, solution_properties K f _ hd hp⟩


/-- The two conditions are necessary and sufficient for solvability. -/
theorem picard_criterion : Spec.SingularCriterion.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ K S f
  constructor
  · rintro ⟨u, rfl⟩
    exact diagonal_picard_necessary K S.rightVector S.leftVector S.sigma
      S.right_orthonormal (fun j => ne_of_gt (S.positive j)) S.adjoint_left u
  · rintro ⟨hf, hs⟩
    have h := diagonal_picard_solution K S.rightVector S.leftVector S.sigma
      S.right_orthonormal S.left_orthonormal (fun j => ne_of_gt (S.positive j))
      S.map_right S.right_closedSpan S.left_closedSpan f hf hs
    exact ⟨_, h.2.1⟩

/-- The norm-convergent singular formula is the unique perpendicular and
unique minimum-norm solution, and all solutions form its kernel translate. -/
theorem picard_solution : Spec.SingularSolution.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ K S f hf hs
  exact diagonal_picard_solution K S.rightVector S.leftVector S.sigma
    S.right_orthonormal S.left_orthonormal (fun j => ne_of_gt (S.positive j))
    S.map_right S.right_closedSpan S.left_closedSpan f hf hs


/-- In the empty-system case the compatibility condition is exactly f = 0. -/
theorem picard_empty_compatibility : Spec.EmptyCompatibility.{u, v, w} := by
  intro 𝕜 H G _ _ _ _ _ _ _ K S _ f
  have h : (ContinuousLinearMap.adjoint K).ker.orthogonal = ⊥ := by
    rw [← S.left_closedSpan, Set.range_eq_empty S.leftVector, Submodule.span_empty]
    apply IsClosed.submodule_topologicalClosure_eq
    exact isClosed_singleton
  rw [h, Submodule.mem_bot]


end ExpandedFA.PartV.Picard
