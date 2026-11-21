import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.PreHilbertCompletion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.LinearMapCompletion

/-!
The compact self-adjoint corollary before completion, paper.tex 7942–8007.
`IsSymmetric` is the bounded self-adjoint identity on an incomplete space;
no adjoint operator on the whole incomplete space is postulated. Compactness
is compact closure in E itself. The family covers the action of T only and
is not asserted to be a Hilbert basis of E. `HasSum` is norm convergence of
finite partial sums in E; finiteness above every positive threshold includes
multiplicity and expresses convergence of the listed eigenvalues to zero.
-/
noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Hilbert.PreHilbertCompactSpectral.Spec
universe u v

namespace Complexification
variable (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
def Space := E × E
def complexPair (x y : E) : Space E := (x, y)
instance : AddCommGroup (Space E) := inferInstanceAs (AddCommGroup (E × E))
instance : Module ℝ (Space E) := inferInstanceAs (Module ℝ (E × E))
private def J : Module.End ℝ (E × E) where
  toFun p := (-p.2, p.1)
  map_add' x y := by ext <;> simp [add_comm]
  map_smul' a x := by ext <;> simp
private lemma J_sq : J E * J E = -1 := by
  ext p <;> simp [J, Module.End.mul_apply]
instance : Module ℂ (Space E) :=
  Module.compHom (E × E) (Complex.liftAux (J E) (J_sq E)).toRingHom
lemma csmul (a : ℂ) (p : Space E) :
    a • p = complexPair E (a.re • p.1 - a.im • p.2) (a.im • p.1 + a.re • p.2) := by
  change (Complex.liftAux (J E) (J_sq E) a) p = _
  change (a.re • p.1 + a.im • (-p.2), a.re • p.2 + a.im • p.1) = _
  simp [complexPair, sub_eq_add_neg, add_comm]
def ip (p q : Space E) : ℂ :=
  ⟨inner ℝ p.1 q.1 + inner ℝ p.2 q.2,
    inner ℝ p.1 q.2 - inner ℝ p.2 q.1⟩
@[instance_reducible] def core : InnerProductSpace.Core ℂ (Space E) where
  inner := ip E
  conj_inner_symm p q := by
    apply Complex.ext <;> simp [ip, real_inner_comm]
  re_inner_nonneg p := by
    dsimp [ip]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left p q r := by
    change ip E (p.1 + q.1, p.2 + q.2) r = _
    apply Complex.ext <;> simp [ip, inner_add_left] <;> ring
  smul_left p q a := by
    rw [csmul]
    apply Complex.ext <;> simp [ip, complexPair, inner_sub_left, inner_add_left, real_inner_smul_left] <;> ring
  definite p hp := by
    have h := congrArg Complex.re hp
    have he : ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 = 0 := by
      simpa [ip, real_inner_self_eq_norm_sq] using h
    have h1 : p.1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg p.1, sq_nonneg ‖p.2‖])
    have h2 : p.2 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg p.2, sq_nonneg ‖p.1‖])
    exact Prod.ext h1 h2
instance : NormedAddCommGroup (Space E) := (core E).toNormedAddCommGroup
instance : InnerProductSpace ℂ (Space E) := InnerProductSpace.ofCore (core E).toCore
instance : IsScalarTower ℝ ℂ (Space E) where
  smul_assoc r a p := by
    rw [csmul, csmul]
    simp only [Complex.smul_re, Complex.smul_im, smul_eq_mul]
    change ((r * a.re) • p.1 - (r * a.im) • p.2,
      (r * a.im) • p.1 + (r * a.re) • p.2) =
      (r • (a.re • p.1 - a.im • p.2), r • (a.im • p.1 + a.re • p.2))
    ext <;> simp [mul_smul, smul_sub, smul_add]
instance : NormedSpace ℝ (Space E) := NormedSpace.restrictScalars ℝ ℂ (Space E)
end Complexification

/-- Geometry of the explicitly constructed space E ⊕ iE, including the
original real isometry, actual complex inner product, and completeness. -/
def ComplexificationGeometry : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E],
    (∀ p : Complexification.Space E,
      ‖p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2) ∧
    (∃ j : E →ₗᵢ[ℝ] Complexification.Space E,
      (∀ x, j x = Complexification.complexPair E x 0) ∧
      (∀ x y, inner ℂ (j x) (j y) = (inner ℝ x y : ℂ)) ∧
      (∀ p : Complexification.Space E, p = j p.1 + Complex.I • j p.2)) ∧
    (CompleteSpace E → CompleteSpace (Complexification.Space E))

/-- The componentwise complexification preserves boundedness, self-adjointness
and genuine compactness. Its real eigenspaces are exactly complexifications
of the original real eigenspaces, and all its eigenvalues are real. -/
def RealComplexification : Prop :=
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E), T.IsSymmetric →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∃ S : Complexification.Space E →L[ℂ] Complexification.Space E,
      (∀ p, S p = Complexification.complexPair E (T p.1) (T p.2)) ∧
      S.IsSymmetric ∧
      Compactness.DefinitionsSpec.IsCompactLinearMapValue S.toLinearMap ∧
      (∀ (r : ℝ) (p : Complexification.Space E),
        S p = (r : ℂ) • p ↔ T p.1 = r • p.1 ∧ T p.2 = r • p.2) ∧
      (∀ (a : ℂ) (p : Complexification.Space E),
        p ≠ 0 → S p = a • p → a.im = 0)

def CompletionExtension : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E),
    T.IsSymmetric → Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    T.completion.IsSymmetric ∧
      Compactness.DefinitionsSpec.IsCompactLinearMapValue T.completion.toLinearMap ∧
      (∀ x : UniformSpace.Completion E, ∃ y : E, T.completion x = (y : UniformSpace.Completion E))

def SpectralExpansion : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (T : E →L[𝕜] E),
    T.IsSymmetric → Compactness.DefinitionsSpec.IsCompactLinearMapValue T.toLinearMap →
    ∃ (ι : Type u) (_ : Countable ι) (e : ι → E) (a : ι → ℝ),
      Orthonormal 𝕜 e ∧
      (∀ j, a j ≠ 0 ∧ T (e j) = (a j : 𝕜) • e j) ∧
      (∀ x, HasSum (fun j => ((a j : 𝕜) * ⟪e j, x⟫_𝕜) • e j) (T x)) ∧
      (∀ μ : 𝕜, μ ≠ 0 → FiniteDimensional 𝕜 (Module.End.eigenspace T.toLinearMap μ)) ∧
      (∀ ε : ℝ, 0 < ε → {j | ε ≤ |a j|}.Finite) ∧
      (∀ b : ℕ → ι, Function.Injective b →
        Filter.Tendsto (fun n => a (b n)) Filter.atTop (nhds 0)) ∧
      (T = 0 → IsEmpty ι)

end ExpandedFA.Hilbert.PreHilbertCompactSpectral.Spec
