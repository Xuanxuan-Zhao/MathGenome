import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.AdjointSpectra
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.BanachAlgebra.ShiftSpectra
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C04Annihilators
import Mathlib.Analysis.Normed.Module.DoubleDual
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.BanachAdjoint
import Mathlib.Analysis.Normed.Operator.Banach

/-! Shifts and the spectra of the two adjoints (`fa2:p2:shifts`).

For the converse transpose implication, an inverse U of T′ gives
‖x‖ ≤ ‖U‖ ‖Tx‖ by testing against all continuous linear functionals.
Thus T is injective with closed range. Hahn–Banach separates any vector
outside that range; the separating functional would lie in ker T′,
contradicting invertibility. Banach's inverse theorem then gives a bounded
inverse of T. This argument includes the zero space.

The Hilbert adjoint is the star on bounded Hilbert operators. Its
involutive, multiplication-reversing property reflects invertibility;
its conjugate scalar law conjugates the spectrum.
-/
noncomputable section
namespace ExpandedFA.BanachAlgebra.AdjointSpectra

universe u
open ExpandedFA.P1.C04Annihilators

/-- The sequence claims retain the full exponent range of the shared shifts. -/
theorem forward_spectrum : Spec.ForwardSpectrum := ShiftSpectra.forward_spectrum

theorem forward_point_spectrum : Spec.ForwardPointSpectrum :=
  ShiftSpectra.forward_point_spectrum

theorem forward_approximate_spectrum : Spec.ForwardApproximateSpectrum :=
  ShiftSpectra.forward_approximate_spectrum

theorem backward_spectrum : Spec.BackwardSpectrum := ShiftSpectra.backward_spectrum

theorem backward_point_spectrum : Spec.BackwardPointSpectrum :=
  ShiftSpectra.backward_point_spectrum

section Banach
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- Transposing both inverse equations preserves a bounded two-sided inverse. -/
theorem isUnit_transpose_of_isUnit (T : X →L[ℂ] X) (hT : IsUnit T) :
    IsUnit (banachTranspose ℂ X X T) := by
  obtain ⟨S, hTS, hST⟩ := isUnit_iff_exists.mp hT
  apply isUnit_iff_exists.mpr
  refine ⟨banachTranspose ℂ X X S, ?_, ?_⟩
  · ext f x
    change f (S (T x)) = f x
    have h := congrArg (fun A : X →L[ℂ] X => A x) hST
    exact congrArg f h
  · ext f x
    change f (T (S x)) = f x
    have h := congrArg (fun A : X →L[ℂ] X => A x) hTS
    exact congrArg f h

omit [CompleteSpace X] in
/-- A bounded inverse to the transpose gives an ambient norm lower bound. -/
theorem bound_of_transpose_inverse (T : X →L[ℂ] X)
    (U : (X →L[ℂ] ℂ) →L[ℂ] (X →L[ℂ] ℂ))
    (hTU : (banachTranspose ℂ X X T) * U = 1) (x : X) :
    ‖x‖ ≤ ‖U‖ * ‖T x‖ := by
  apply NormedSpace.norm_le_dual_bound ℂ x (mul_nonneg (norm_nonneg U) (norm_nonneg (T x)))
  intro f
  have he : (U f) (T x) = f x :=
    congrArg (fun A : (X →L[ℂ] ℂ) →L[ℂ] (X →L[ℂ] ℂ) => A f x) hTU
  calc
    ‖f x‖ = ‖(U f) (T x)‖ := congrArg norm he.symm
    _ ≤ ‖U f‖ * ‖T x‖ := (U f).le_opNorm _
    _ ≤ (‖U‖ * ‖f‖) * ‖T x‖ :=
      mul_le_mul_of_nonneg_right (U.le_opNorm f) (norm_nonneg _)
    _ = (‖U‖ * ‖T x‖) * ‖f‖ := by ring

/-- Converse invertibility, with closedness and surjectivity proved for T. -/
theorem isUnit_of_isUnit_transpose (T : X →L[ℂ] X)
    (hT : IsUnit (banachTranspose ℂ X X T)) : IsUnit T := by
  obtain ⟨U, hTU, _⟩ := isUnit_iff_exists.mp hT
  have ha : AntilipschitzWith ⟨‖U‖, norm_nonneg U⟩ T :=
    T.antilipschitz_of_bound (bound_of_transpose_inverse T U hTU)
  have hclosed : IsClosed (Set.range T) := ha.isClosed_range T.uniformContinuous
  have hinj := (ContinuousLinearMap.isUnit_iff_bijective.mp hT).1
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  refine ⟨ha.injective, ?_⟩
  intro y
  by_contra hy
  have hnot : y ∉ closure (T.range : Set X) := by
    rw [show (T.range : Set X) = Set.range T from rfl, hclosed.closure_eq]
    exact hy
  obtain ⟨f, hf, hfy⟩ :=
    Unbounded.exists_dual_vanishing_of_not_mem_closure T.range y hnot
  have hfT : banachTranspose ℂ X X T f = 0 := by
    ext x
    exact hf (T x) (T.mem_range_self x)
  have hf0 : f = 0 := hinj (hfT.trans (map_zero _).symm)
  exact hfy (by rw [hf0]; rfl)

end Banach

theorem transpose_invertibility : Spec.TransposeInvertibility.{u} := by
  intro X _ _ _ T
  exact ⟨isUnit_of_isUnit_transpose T, isUnit_transpose_of_isUnit T⟩

theorem transpose_spectrum : Spec.TransposeSpectrum.{u} := by
  intro X _ _ _ T
  change spectrum ℂ (banachTranspose ℂ X X T) = spectrum ℂ T
  ext z
  simp only [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
  have he : banachTranspose ℂ X X (z • (1 : X →L[ℂ] X) - T) =
      z • (1 : (X →L[ℂ] ℂ) →L[ℂ] (X →L[ℂ] ℂ)) - banachTranspose ℂ X X T := by
    ext f x
    change f (z • x - T x) = z • f x - f (T x)
    simp only [map_sub, map_smul]
  rw [← he]
  exact not_congr (transpose_invertibility X _)

theorem hilbert_adjoint_invertibility : Spec.HilbertAdjointInvertibility.{u} := by
  intro H _ _ _ T
  exact isUnit_star

theorem hilbert_adjoint_spectrum : Spec.HilbertAdjointSpectrum.{u} := by
  intro H _ _ _ T
  change spectrum ℂ (star T) = (starRingEnd ℂ) '' spectrum ℂ T
  rw [spectrum.map_star]
  exact Set.image_star.symm

end ExpandedFA.BanachAlgebra.AdjointSpectra
