import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.BauerFikeResolvent
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.MatrixData

noncomputable section

namespace NumAnalysis206.BauerFikeResolvent

set_option maxHeartbeats 400000 in
/-- W39 in the arbitrary vector norm specified by `b` and its ambient space. -/
theorem resolvent_bound : Specs.NumAnalysis206.BauerFikeResolvent.resolvent_bound := by
  intro X _ _ _ n b A V E lam μ hV hA hμ hμA
  let T := Matrix.toLinAlgEquiv b
  have hVi : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V ((Matrix.isUnit_iff_isUnit_det _).mp hV)
  have hVj : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det _).mp hV)
  have hshift : μ • (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal lam =
      V⁻¹ * (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) * V := by
    simp [hA, mul_sub, sub_mul, Matrix.mul_assoc, hVi]
    rw [← Matrix.mul_assoc, hVi, one_mul]
  have huA : IsUnit (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A) := by
    simpa only [spectrum.mem_iff, not_not, Algebra.algebraMap_eq_smul_one] using hμA
  have huVi : IsUnit V⁻¹ := (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_nonsing_inv_det V ((Matrix.isUnit_iff_isUnit_det _).mp hV))
  have hu : IsUnit (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal lam) := by
    rw [hshift]
    exact (huVi.mul huA).mul hV
  have hinv := Matrix.nonsing_inv_mul
    (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal lam)
    ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  have hμT : Module.End.HasEigenvalue (T (A + E)) μ := by
    apply Module.End.HasEigenvalue.of_mem_spectrum
    rw [AlgEquiv.spectrum_eq]
    exact hμ
  obtain ⟨x, hx⟩ := hμT.exists_hasEigenvector
  let z := T V⁻¹ x
  have hVz : T V z = x := by
    change T V (T V⁻¹ x) = x
    rw [← Module.End.mul_apply, ← map_mul, hVj, map_one, Module.End.one_apply]
  have hz : z ≠ 0 := by
    intro hz
    apply hx.2
    rw [← hVz, hz, map_zero]
  have heq : T (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal lam) z =
      T (V⁻¹ * E * V) z := by
    have heig : T A x + T E x = μ • x := by
      simpa only [map_add, LinearMap.add_apply] using hx.apply_eq_smul
    rw [hshift]
    simp only [map_mul, Module.End.mul_apply, hVz]
    congr 1
    simp only [map_sub, map_smul, map_one, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using heig.symm)
  have hfix : T ((μ • (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal lam)⁻¹)
      (T (V⁻¹ * E * V) z) = z := by
    rw [← heq, ← Module.End.mul_apply, ← map_mul, hinv, map_one, Module.End.one_apply]
  let R : X →L[ℂ] X :=
    (T ((μ • (1 : Matrix (Fin n) (Fin n) ℂ) - Matrix.diagonal lam)⁻¹)).toContinuousLinearMap
  let F : X →L[ℂ] X := (T (V⁻¹ * E * V)).toContinuousLinearMap
  have hfix' : R (F z) = z := hfix
  change 1 ≤ ‖R‖ * ‖F‖
  have hchain : ‖z‖ ≤ (‖R‖ * ‖F‖) * ‖z‖ := by
    calc
      ‖z‖ = ‖R (F z)‖ := congrArg norm hfix'.symm
      _ ≤ ‖R‖ * ‖F z‖ := R.le_opNorm (F z)
      _ ≤ ‖R‖ * (‖F‖ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (F.le_opNorm z) (norm_nonneg R)
      _ = (‖R‖ * ‖F‖) * ‖z‖ := (mul_assoc _ _ _).symm
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hz)).mp (by simpa only [one_mul] using hchain)

end NumAnalysis206.BauerFikeResolvent
