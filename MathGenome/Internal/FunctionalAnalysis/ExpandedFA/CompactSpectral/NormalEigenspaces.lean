import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.NormalEigenspaces
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Adjoint
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactNonzeroSpectrum
import Mathlib.Tactic.LinearCombination

/-!
Normal eigenspace geometry on an arbitrary complex Hilbert space.

The scalar shift of a normal operator is normal. Its kernel agrees with its
adjoint kernel, proving the conjugate-eigenvector identity. The adjoint pairing
then gives orthogonality, and invariance under N and N* gives reduction.
Compactness is used only for finite multiplicity and finite/countable spectra:
the geometric eigenspace embeds in the finite-dimensional stabilized power
kernel from the accepted Riesz theory. A countable union of finite sets outside
the disks of radii 1/(n+1) contains every nonzero eigenvalue.
-/

noncomputable section

namespace ExpandedFA.CompactSpectral.NormalEigenspaces

universe u
open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Normality passes to every scalar shift. -/
lemma normal_scalar_shift (N : H →L[ℂ] H) (hN : IsStarNormal N) (α : ℂ) :
    IsStarNormal (N - α • 1) := by
  let := hN
  apply Commute.isStarNormal_sub
  simp only [star_smul, star_one]
  exact (Commute.one_right N).smul_right _

/-- Equal norms for a normal scalar shift identify its two kernels. -/
theorem normal_shift_kernels : Spec.ShiftKernels.{u} := by
  intro H _ _ _ N hN α
  have h := ContinuousLinearMap.IsStarNormal.ker_adjoint_eq_ker
    (normal_scalar_shift N hN α)
  simpa only [map_sub, map_smulₛₗ, ContinuousLinearMap.adjoint_one,
    starRingEnd_apply] using h.symm

theorem normal_adjoint_eigenvectors : Spec.AdjointEigenvectors.{u} := by
  intro H _ _ _ N hN α x
  have h := SetLike.ext_iff.mp (normal_shift_kernels H N hN α) x
  change (N - α • 1) x = 0 ↔ (N.adjoint - star α • 1) x = 0 at h
  simpa only [sub_apply, smul_apply, one_apply_eq_self, sub_eq_zero] using h

/-- Distinct eigenspaces of a normal operator are orthogonal. -/
theorem normal_orthogonal_eigenspaces : Spec.OrthogonalEigenspaces.{u} := by
  intro H _ _ _ N hN
  rintro α μ hαμ ⟨x, hx⟩ ⟨y, hy⟩
  have hx' := (normal_adjoint_eigenvectors H N hN α x).mp
    (Module.End.mem_eigenspace_iff.mp hx)
  have hy' : N y = μ • y := Module.End.mem_eigenspace_iff.mp hy
  have h := ContinuousLinearMap.adjoint_inner_left N y x
  rw [hx', hy', inner_smul_left, inner_smul_right, starRingEnd_apply, star_star] at h
  have hh : (α - μ) * inner ℂ x y = 0 := by linear_combination h
  exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hαμ)

/-- Every eigenspace is invariant under both N and N*, hence reduces N. -/
theorem normal_reducing_eigenspaces : Spec.ReducingEigenspaces.{u} := by
  intro H _ _ _ N hN α
  let M := Module.End.eigenspace N.toLinearMap α
  have hM : IsClosed (M : Set H) := ContinuousLinearMap.isClosed_eigenspace N α
  apply (Hilbert.Adjoint.reducing_iff_invariant_adjoint ℂ H M hM N).mpr
  constructor
  · intro x hx
    have he : N x = α • x := Module.End.mem_eigenspace_iff.mp hx
    rw [he]
    exact M.smul_mem α hx
  · intro x hx
    have he : N.adjoint x = star α • x :=
      (normal_adjoint_eigenvectors H N hN α x).mp (Module.End.mem_eigenspace_iff.mp hx)
    change N.adjoint x ∈ M
    rw [he]
    exact M.smul_mem (star α) hx

/-- Finite algebraic multiplicity from Riesz theory implies finite geometric
multiplicity, by inclusion in its stabilized power kernel. -/
theorem compact_finite_dimensional_eigenspaces : Spec.FiniteDimensionalEigenspaces.{u} := by
  intro H _ _ _ N hN α hα
  obtain ⟨p, hp, hfin, _, _⟩ :=
    Fredholm.compact_generalized_eigenspace_stabilizes N hN α hα
  let A : H →ₗ[ℂ] H := α • LinearMap.id - N.toLinearMap
  let : FiniteDimensional ℂ (LinearMap.ker (A ^ p)) := hfin
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.ker (A ^ p))
  intro x hx
  have he : N x = α • x := Module.End.mem_eigenspace_iff.mp hx
  have hz : x ∈ LinearMap.ker A := by
    change α • x - N x = 0
    rw [he, sub_self]
  have hi := A.iterateKer.monotone hp
  change LinearMap.ker (A ^ 1) ≤ LinearMap.ker (A ^ p) at hi
  rw [pow_one] at hi
  exact hi hz

theorem compact_eigenvalues_finite_away_from_zero : Spec.FiniteAwayFromZero.{u} := by
  intro H _ _ _ N hN ε hε
  exact Fredholm.compact_eigenvalues_finite_away_from_zero N hN ε hε

/-- Countability comes from compactness, with no separability hypothesis. -/
theorem compact_nonzero_eigenvalues_countable : Spec.CountableNonzeroEigenvalues.{u} := by
  intro H _ _ _ N hN
  let S (n : ℕ) : Set ℂ :=
    {α : ℂ | (∃ x : H, x ≠ 0 ∧ N x = α • x) ∧ 1 / (n + 1 : ℝ) ≤ ‖α‖}
  have hS (n : ℕ) : (S n).Finite :=
    compact_eigenvalues_finite_away_from_zero H N hN _ (by positivity)
  apply (Set.countable_iUnion (fun n => (hS n).countable)).mono
  intro α hα
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hα.1)
  exact Set.mem_iUnion.mpr ⟨n, hα.2, hn.le⟩

end ExpandedFA.CompactSpectral.NormalEigenspaces
