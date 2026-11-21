import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Spectral.BauerFikeDistance
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Spectral.LpDiagonalNorm
import Mathlib.Data.Fintype.Lattice

noncomputable section
open scoped NNReal ENNReal
namespace NumAnalysis206.BauerFikeDistance
open NumAnalysis206.MatrixDefinitions

/-- Submultiplicativity for the chosen coordinate norm. -/
lemma subordinateNorm_mul_le {K : Type*} [RCLike K] {X : Type*} [NormedAddCommGroup X] [NormedSpace K X]
    [FiniteDimensional K X] {n : ℕ} (b : Module.Basis (Fin n) K X)
    (A B : Matrix (Fin n) (Fin n) K) :
    subordinateNorm b b (A * B) ≤ subordinateNorm b b A * subordinateNorm b b B := by
  let T := Matrix.toLinAlgEquiv b
  have h : (T (A * B)).toContinuousLinearMap =
      (T A).toContinuousLinearMap * (T B).toContinuousLinearMap := by
    ext x
    simp [map_mul, Module.End.mul_apply]
  change ‖(T (A * B)).toContinuousLinearMap‖ ≤ _
  rw [h]
  exact norm_mul_le _ _

/-- Algebraic similarity identifies all diagonal entries with the spectrum,
including repeated eigenvalues and dimension zero. -/
lemma spectrum_diagonalization {K : Type*} [RCLike K] {n : ℕ} (A V : Matrix (Fin n) (Fin n) K)
    (lam : Fin n → K) (hV : IsUnit V)
    (hA : A = V * Matrix.diagonal lam * V⁻¹) : spectrum K A = Set.range lam := by
  rw [hA]
  have hv : (hV.unit : Matrix (Fin n) (Fin n) K) = V := hV.unit_spec
  rw [← hv, ← Matrix.coe_units_inv, spectrum.units_conjugate, spectrum_diagonal]

/-- A left inverse of the shifted diagonal converts the eigenvector equation
into a fixed vector equation. This works over both real and complex scalars. -/
lemma resolvent_norm_bound {K : Type*} [RCLike K] {X : Type*}
    [NormedAddCommGroup X] [NormedSpace K X] [FiniteDimensional K X]
    {n : ℕ} (b : Module.Basis (Fin n) K X)
    (D F R : Matrix (Fin n) (Fin n) K) (μ : K)
    (hleft : R * (μ • 1 - D) = 1) (hμ : μ ∈ spectrum K (D + F)) :
    1 ≤ subordinateNorm b b R * subordinateNorm b b F := by
  let T := Matrix.toLinAlgEquiv b
  have he : Module.End.HasEigenvalue (T (D + F)) μ :=
    Module.End.HasEigenvalue.of_mem_spectrum (by rwa [AlgEquiv.spectrum_eq])
  obtain ⟨x, hx⟩ := he.exists_hasEigenvector
  have heq : T (μ • 1 - D) x = T F x := by
    have hx' : T D x + T F x = μ • x := by
      simpa only [map_add, LinearMap.add_apply] using hx.apply_eq_smul
    simp only [map_sub, map_smul, map_one, LinearMap.sub_apply,
      LinearMap.smul_apply, Module.End.one_apply]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using hx'.symm)
  let C : X →L[K] X := (T R).toContinuousLinearMap * (T F).toContinuousLinearMap
  have hfix : C x = x := by
    change T R (T F x) = x
    rw [← heq, ← Module.End.mul_apply, ← map_mul, hleft, map_one, Module.End.one_apply]
  have hnorm : 1 ≤ ‖C‖ := by
    have h := C.le_opNorm x
    rw [hfix] at h
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hx.2)).mp
      (by simpa only [one_mul] using h)
  exact hnorm.trans (norm_mul_le _ _)

set_option maxHeartbeats 400000 in
/-- Bauer--Fike in any specified subordinate norm with the diagonal property. -/
theorem distance_bound : Specs.NumAnalysis206.BauerFikeDistance.distance_bound := by
  intro K _ X _ _ _ n b hdiag A V E lam μ hV hA hμ
  let N := subordinateNorm b b
  have hN (M : Matrix (Fin n) (Fin n) K) : 0 ≤ N M := norm_nonneg _
  have hsim := spectrum_diagonalization A V lam hV hA
  have hF : N (V⁻¹ * E * V) ≤ N V * N V⁻¹ * N E := by
    calc
      _ ≤ N (V⁻¹ * E) * N V := subordinateNorm_mul_le b _ _
      _ ≤ (N V⁻¹ * N E) * N V :=
        mul_le_mul_of_nonneg_right (subordinateNorm_mul_le b _ _) (hN V)
      _ = _ := by ring
  have hex : ∃ i : Fin n, ‖μ - lam i‖ ≤ N V * N V⁻¹ * N E := by
    by_cases hμA : μ ∈ spectrum K A
    · rw [hsim] at hμA
      obtain ⟨i, hi⟩ := hμA
      exact ⟨i, by rw [hi, sub_self, norm_zero]; exact mul_nonneg (mul_nonneg (hN V) (hN V⁻¹)) (hN E)⟩
    · have hne (i : Fin n) : μ - lam i ≠ 0 := by
        intro hi
        apply hμA
        rw [hsim]
        exact ⟨i, (sub_eq_zero.mp hi).symm⟩
      have hshift : μ • (1 : Matrix (Fin n) (Fin n) K) - Matrix.diagonal lam =
          Matrix.diagonal (fun i => μ - lam i) := by
        rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
      have hleft : Matrix.diagonal (fun i => (μ - lam i)⁻¹) *
          (μ • (1 : Matrix (Fin n) (Fin n) K) - Matrix.diagonal lam) = 1 := by
        rw [hshift]
        rw [Matrix.diagonal_mul_diagonal]
        rw [← Matrix.diagonal_one]
        apply congrArg Matrix.diagonal
        funext i
        exact inv_mul_cancel₀ (hne i)
      have hVi : V⁻¹ * V = 1 :=
        Matrix.nonsing_inv_mul V ((Matrix.isUnit_iff_isUnit_det _).mp hV)
      have hconj : V⁻¹ * (A + E) * V = Matrix.diagonal lam + V⁻¹ * E * V := by
        simp [hA, mul_add, add_mul, Matrix.mul_assoc, hVi]
        rw [← Matrix.mul_assoc, hVi, one_mul]
      have hμ' : μ ∈ spectrum K (Matrix.diagonal lam + V⁻¹ * E * V) := by
        rw [← hconj]
        have hv : (hV.unit : Matrix (Fin n) (Fin n) K) = V := hV.unit_spec
        rw [← hv, ← Matrix.coe_units_inv, spectrum.units_conjugate']
        exact hμ
      have hr := resolvent_norm_bound b (Matrix.diagonal lam) (V⁻¹ * E * V)
        _ μ hleft hμ'
      rw [hdiag] at hr
      have hs : (Finset.univ : Finset (Fin n)).Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty.mp h] at hr
        norm_num at hr
      obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hs
        (fun i : Fin n => ‖(μ - lam i)⁻¹‖₊)
      rw [hi] at hr
      change 1 ≤ ‖(μ - lam i)⁻¹‖ * N (V⁻¹ * E * V) at hr
      rw [norm_inv] at hr
      have hpos : 0 < ‖μ - lam i‖ := norm_pos_iff.mpr (hne i)
      have hd : ‖μ - lam i‖ ≤ N (V⁻¹ * E * V) := by
        have := mul_le_mul_of_nonneg_left hr (le_of_lt hpos)
        simpa [← mul_assoc, ne_of_gt hpos] using this
      exact ⟨i, hd.trans hF⟩
  obtain ⟨i, hi⟩ := hex
  have : Nonempty (Fin n) := ⟨i⟩
  obtain ⟨j, hj⟩ := Finite.exists_min (fun i : Fin n => ‖μ - lam i‖)
  exact ⟨j, hj, (hj i).trans hi⟩

/-- All subordinate ℓ_p norms satisfy the required diagonal property. -/
theorem lp_distance_bound : Specs.NumAnalysis206.BauerFikeDistance.lp_distance_bound := by
  intro K _ n p hp A V E lam μ hV hA hμ
  have : Fact (1 ≤ p) := ⟨hp⟩
  let b := PiLp.basisFun p K (Fin n)
  have hnorm (M : Matrix (Fin n) (Fin n) K) :
      subordinateNorm b b M = lpOperatorNorm p hp M := by
    simp only [subordinateNorm, lpOperatorNorm, Matrix.toLpLin_eq_toLin, b]
  have hd (d : Fin n → K) : subordinateNorm b b (Matrix.diagonal d) =
      ((Finset.univ.sup fun i => ‖d i‖₊ : ℝ≥0) : ℝ) := by
    rw [hnorm]
    exact LpDiagonalNorm.diagonal_norm p hp d
  simpa only [hnorm] using distance_bound b hd A V E lam μ hV hA hμ

end NumAnalysis206.BauerFikeDistance
