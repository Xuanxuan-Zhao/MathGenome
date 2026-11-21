import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.StoneWeierstrass
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Approximation.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.ZeroAtInftyUnitization
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The compact assertions explicitly specialize the canonical earlier theorem.
For the locally compact assertions, extend functions by zero to `OnePoint X`
and adjoin constants. Nonvanishing separates finite points from infinity.
Subtracting the approximant's value at infinity returns to the original algebra;
the correction has norm at most twice the original approximation error.
-/
namespace ExpandedFA.PartV.StoneWeierstrass

open scoped ZeroAtInfty
open OnePoint
universe u

theorem real_dense : Specs.ExpandedFA.PartV.StoneWeierstrass.RealDensity.{u} := by
  intro K _ _ _ _ A hA
  exact ExpandedFA.Approximation.StoneWeierstrass.real_dense K A hA

theorem complex_dense : Specs.ExpandedFA.PartV.StoneWeierstrass.ComplexDensity.{u} := by
  intro K _ _ _ _ A hA hstar
  exact ExpandedFA.Approximation.StoneWeierstrass.complex_dense K A hA hstar

theorem real_uniform_approximation :
    Specs.ExpandedFA.PartV.StoneWeierstrass.RealUniformApproximation.{u} := by
  intro K _ _ _ _ A hA
  exact ExpandedFA.Approximation.StoneWeierstrass.real_uniform_approximation K A hA

theorem complex_uniform_approximation :
    Specs.ExpandedFA.PartV.StoneWeierstrass.ComplexUniformApproximation.{u} := by
  intro K _ _ _ _ A hA hstar
  exact ExpandedFA.Approximation.StoneWeierstrass.complex_uniform_approximation K A hA hstar

section OnePoint
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {𝕜 : Type*} [RCLike 𝕜]

/-- Adjoining constants to the zero extensions of the original algebra. -/
private def onePointAlgebra (A : NonUnitalSubalgebra 𝕜 C₀(X, 𝕜)) :
    Subalgebra 𝕜 C(OnePoint X, 𝕜) where
  carrier := {g | g.toZeroAtInfty ∈ A}
  add_mem' := by
    intro f g hf hg
    simpa using A.add_mem hf hg
  mul_mem' := by
    intro f g hf hg
    have h := A.add_mem (A.add_mem (A.mul_mem hf hg)
      (A.smul_mem (g ∞) hf)) (A.smul_mem (f ∞) hg)
    have heq : (f * g).toZeroAtInfty =
        f.toZeroAtInfty * g.toZeroAtInfty + g ∞ • f.toZeroAtInfty +
          f ∞ • g.toZeroAtInfty := by
      ext x
      simp only [ContinuousMap.toZeroAtInfty_apply, ZeroAtInftyContinuousMap.add_apply,
        ZeroAtInftyContinuousMap.mul_apply, ZeroAtInftyContinuousMap.smul_apply,
        ContinuousMap.mul_apply, smul_eq_mul]
      ring
    change (f * g).toZeroAtInfty ∈ A
    rw [heq]
    exact h
  algebraMap_mem' := by
    intro c
    have h : (algebraMap 𝕜 C(OnePoint X, 𝕜) c).toZeroAtInfty = 0 := by
      ext x
      simp
    simp [h]

private lemma extension_mem (A : NonUnitalSubalgebra 𝕜 C₀(X, 𝕜))
    {f : C₀(X, 𝕜)} (hf : f ∈ A) : f.toOnePoint ∈ onePointAlgebra A := by
  change f.toOnePoint.toZeroAtInfty ∈ A
  have h : f.toOnePoint.toZeroAtInfty = f := by ext; simp
  rwa [h]

private lemma onePointAlgebra_separates (A : NonUnitalSubalgebra 𝕜 C₀(X, 𝕜))
    (hsep : ∀ x y : X, x ≠ y → ∃ f ∈ A, f x ≠ f y)
    (hnv : ∀ x : X, ∃ f ∈ A, f x ≠ 0) :
    (onePointAlgebra A).SeparatesPoints := by
  intro x y hxy
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => exact (hxy rfl).elim
    | coe y =>
      obtain ⟨f, hf, hfy⟩ := hnv y
      exact ⟨f.toOnePoint, ⟨f.toOnePoint, extension_mem A hf, rfl⟩, by simpa using hfy.symm⟩
  | coe x =>
    induction y using OnePoint.rec with
    | infty =>
      obtain ⟨f, hf, hfx⟩ := hnv x
      exact ⟨f.toOnePoint, ⟨f.toOnePoint, extension_mem A hf, rfl⟩, by simpa using hfx⟩
    | coe y =>
      obtain ⟨f, hf, hfxy⟩ := hsep x y (fun h => hxy (congrArg (fun z : X => (z : OnePoint X)) h))
      exact ⟨f.toOnePoint, ⟨f.toOnePoint, extension_mem A hf, rfl⟩, hfxy⟩

private lemma onePointAlgebra_star (A : NonUnitalSubalgebra 𝕜 C₀(X, 𝕜))
    (hstar : ∀ f ∈ A, star f ∈ A) :
    ∀ g ∈ onePointAlgebra A, star g ∈ onePointAlgebra A := by
  intro g hg
  change (star g).toZeroAtInfty ∈ A
  rw [ContinuousMap.toZeroAtInfty_star]
  exact hstar _ hg

private lemma correction_norm_le (g : C(OnePoint X, 𝕜)) (f : C₀(X, 𝕜)) :
    ‖g.toZeroAtInfty - f‖ ≤ 2 * ‖g - f.toOnePoint‖ := by
  change ‖(g.toZeroAtInfty - f).toBCF‖ ≤ _
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro x
  change ‖(g x - g ∞) - f x‖ ≤ _
  calc
    ‖(g x - g ∞) - f x‖ =
        ‖(g - f.toOnePoint) (x : OnePoint X) - (g - f.toOnePoint) ∞‖ := by
      simp only [ContinuousMap.sub_apply, ZeroAtInftyContinuousMap.toOnePoint_coe,
        ZeroAtInftyContinuousMap.toOnePoint_infty, sub_zero]
      congr 1
      ring
    _ ≤ ‖(g - f.toOnePoint) (x : OnePoint X)‖ + ‖(g - f.toOnePoint) ∞‖ := norm_sub_le _ _
    _ ≤ ‖g - f.toOnePoint‖ + ‖g - f.toOnePoint‖ :=
      add_le_add (ContinuousMap.norm_coe_le_norm _ _) (ContinuousMap.norm_coe_le_norm _ _)
    _ = 2 * ‖g - f.toOnePoint‖ := by ring

private lemma c0_approximation_of_onePoint
    (A : NonUnitalSubalgebra 𝕜 C₀(X, 𝕜))
    (happrox : ∀ (f : C(OnePoint X, 𝕜)) (ε : ℝ), 0 < ε →
      ∃ g ∈ onePointAlgebra A, ‖g - f‖ < ε)
    (f : C₀(X, 𝕜)) (ε : ℝ) (hε : 0 < ε) : ∃ g ∈ A, ‖g - f‖ < ε := by
  obtain ⟨g, hg, herr⟩ := happrox f.toOnePoint (ε / 2) (half_pos hε)
  refine ⟨g.toZeroAtInfty, hg, lt_of_le_of_lt (correction_norm_le g f) ?_⟩
  linarith

end OnePoint

theorem real_c0_uniform_approximation :
    Specs.ExpandedFA.PartV.StoneWeierstrass.RealC0UniformApproximation.{u} := by
  intro X _ _ _ A hsep hnv
  apply c0_approximation_of_onePoint A
  exact ExpandedFA.Approximation.StoneWeierstrass.real_uniform_approximation
    (OnePoint X) (onePointAlgebra A) (onePointAlgebra_separates A hsep hnv)

theorem complex_c0_uniform_approximation :
    Specs.ExpandedFA.PartV.StoneWeierstrass.ComplexC0UniformApproximation.{u} := by
  intro X _ _ _ A hsep hnv hstar
  apply c0_approximation_of_onePoint A
  exact ExpandedFA.Approximation.StoneWeierstrass.complex_uniform_approximation
    (OnePoint X) (onePointAlgebra A) (onePointAlgebra_separates A hsep hnv)
    (onePointAlgebra_star A hstar)

theorem real_c0_dense : Specs.ExpandedFA.PartV.StoneWeierstrass.RealC0Density.{u} := by
  intro X _ _ _ A hsep hnv f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hg, herr⟩ := real_c0_uniform_approximation X A hsep hnv f ε hε
  exact ⟨g, hg, by simpa [dist_eq_norm, norm_sub_rev] using herr⟩

theorem complex_c0_dense : Specs.ExpandedFA.PartV.StoneWeierstrass.ComplexC0Density.{u} := by
  intro X _ _ _ A hsep hnv hstar f
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨g, hg, herr⟩ := complex_c0_uniform_approximation X A hsep hnv hstar f ε hε
  exact ⟨g, hg, by simpa [dist_eq_norm, norm_sub_rev] using herr⟩

end ExpandedFA.PartV.StoneWeierstrass
