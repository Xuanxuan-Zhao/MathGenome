import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.LinearAlgebra.LUSolveCertificate
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.DoolittleBackward
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.LinearAlgebra.TriangularBackward
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Conditioning.LinearPerturbation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open scoped BigOperators
namespace NumAnalysis206.LinearAlgebra.LUSolveCertificate
open MatrixDefinitions NumAnalysis206.PivotedLU NumAnalysis206.Rounding

/-- Entrywise control of a product by scaled absolute-value factors. -/
theorem product_bound {n : ℕ} (B C L U : Mat ℝ n n) (a c : ℝ)
    (ha : 0 ≤ a) (_hc : 0 ≤ c)
    (hB : ∀ i j, ‖B i j‖ ≤ a * ‖L i j‖)
    (hC : ∀ i j, ‖C i j‖ ≤ c * ‖U i j‖) (i j : Fin n) :
    ‖(B * C) i j‖ ≤ (a * c) * (entrywiseAbs L * entrywiseAbs U) i j := by
  calc
    ‖(B * C) i j‖ ≤ ∑ k, ‖B i k * C k j‖ := by
      simpa only [Matrix.mul_apply] using
        (norm_sum_le Finset.univ (fun k => B i k * C k j))
    _ ≤ ∑ k, (a * ‖L i k‖) * (c * ‖U k j‖) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (hB i k) (hC k j) (norm_nonneg _) (by positivity)
    _ = (a * c) * (entrywiseAbs L * entrywiseAbs U) i j := by
      simp only [Matrix.mul_apply, entrywiseAbs, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- Expanding the perturbed factors yields the advertised conservative constant. -/
theorem combined_bound {n : ℕ} (L U Δ ΔL ΔU : Mat ℝ n n) (f g : ℝ)
    (hg : 0 ≤ g)
    (hΔ : EntrywiseLE (entrywiseAbs Δ) (f • (entrywiseAbs L * entrywiseAbs U)))
    (hL : ∀ i j, |ΔL i j| ≤ g * |L i j|)
    (hU : ∀ i j, |ΔU i j| ≤ g * |U i j|) :
    EntrywiseLE (entrywiseAbs (Δ + ΔL * U + L * ΔU + ΔL * ΔU))
      ((f + 2 * g + g ^ 2) • (entrywiseAbs L * entrywiseAbs U)) := by
  have hL' : ∀ i j, ‖ΔL i j‖ ≤ g * ‖L i j‖ := by simpa only [Real.norm_eq_abs] using hL
  have hU' : ∀ i j, ‖ΔU i j‖ ≤ g * ‖U i j‖ := by simpa only [Real.norm_eq_abs] using hU
  intro i j
  have hb1 := product_bound ΔL U L U g 1 hg zero_le_one hL' (by simp) i j
  have hb2 := product_bound L ΔU L U 1 g zero_le_one hg (by simp) hU' i j
  have hb3 := product_bound ΔL ΔU L U g g hg hg hL' hU' i j
  change ‖Δ i j + (ΔL * U) i j + (L * ΔU) i j + (ΔL * ΔU) i j‖ ≤ _
  calc
    _ ≤ ‖Δ i j‖ + ‖(ΔL * U) i j‖ + ‖(L * ΔU) i j‖ + ‖(ΔL * ΔU) i j‖ :=
      by
        have h1 := norm_add_le (Δ i j) ((ΔL * U) i j)
        have h2 := norm_add_le (Δ i j + (ΔL * U) i j) ((L * ΔU) i j)
        have h3 := norm_add_le (Δ i j + (ΔL * U) i j + (L * ΔU) i j) ((ΔL * ΔU) i j)
        linarith
    _ ≤ f * (entrywiseAbs L * entrywiseAbs U) i j +
          (g * 1) * (entrywiseAbs L * entrywiseAbs U) i j +
          (1 * g) * (entrywiseAbs L * entrywiseAbs U) i j +
          (g * g) * (entrywiseAbs L * entrywiseAbs U) i j :=
      add_le_add (add_le_add (add_le_add (hΔ i j) hb1) hb2) hb3
    _ = _ := by simp only [Matrix.smul_apply, smul_eq_mul]; ring

/-- Removing the row permutation gives a perturbation of the original matrix. -/
theorem unpermute_equation {n : ℕ} (p : Equiv.Perm (Fin n))
    (A Δ : Mat ℝ n n) (b x : Fin n → ℝ)
    (h : (permutationMatrix p * A + Δ).mulVec x =
      (permutationMatrix p).mulVec b) :
    (A + permutationMatrix p.symm * Δ).mulVec x = b := by
  have hinv : permutationMatrix p.symm * permutationMatrix p = (1 : Mat ℝ n n) := by
    rw [permutationMatrix_mul]
    ext i j
    simp [permuteRows, permutationMatrix, Matrix.one_apply, eq_comm]
  have hh := congrArg (fun v => (permutationMatrix p.symm).mulVec v) h
  simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_add,
    hinv, Matrix.one_mul, Matrix.one_mulVec] using hh

/-- Matrix equations act on Euclidean vectors with the same coordinates. -/
theorem euclidean_equation {n : ℕ} (A : Mat ℝ n n) (x b : Fin n → ℝ)
    (h : A.mulVec x = b) : A.toEuclideanLin (WithLp.toLp 2 x) = WithLp.toLp 2 b := by
  apply WithLp.ofLp_injective 2
  exact h

/-- Direct forward corollary, including a zero right-hand side. -/
theorem forward_error : Specs.NumAnalysis206.LinearAlgebra.LUSolveCertificate.forward_error := by
  intro n A Δ b xhat heq E hE
  dsimp only
  intro hsmall
  let D := Δ.toEuclideanLin.toContinuousLinearMap
  let bv : Vec ℝ n := WithLp.toLp 2 b
  let xv : Vec ℝ n := E.symm bv
  have hEq : (E.toContinuousLinearMap + D) (WithLp.toLp 2 xhat) = bv := by
    rw [hE]
    have hh := euclidean_equation (A + Δ) xhat b heq
    simpa only [map_add, LinearMap.add_apply, add_apply,
      LinearMap.coe_toContinuousLinearMap', D, bv] using hh
  obtain ⟨B, hB, hbounds⟩ := NumAnalysis206.Conditioning.perturbedLinearSystems E D hsmall
  obtain ⟨hunique, habs, _⟩ := hbounds bv 0 xv (E.apply_symm_apply bv)
  have hsol : WithLp.toLp 2 xhat = B.symm (bv + 0) :=
    (hunique _).mp (by simpa only [add_zero] using hEq)
  have habs' : ‖WithLp.toLp 2 xhat - xv‖ ≤
      (‖E.symm.toContinuousLinearMap‖ * operatorNorm Δ) * ‖xv‖ /
        (1 - ‖E.symm.toContinuousLinearMap‖ * operatorNorm Δ) := by
    rw [← hsol] at habs
    simpa only [norm_zero, zero_add, D, operatorNorm, div_mul_eq_mul_div, mul_assoc] using habs
  refine ⟨habs', ?_, ?_⟩
  · intro hb
    have hx : xv ≠ 0 := by
      intro hz
      have hbz : bv = 0 := by simpa only [xv, map_zero, E.apply_symm_apply] using congrArg E hz
      apply hb
      exact WithLp.toLp_injective 2 (by simpa only [bv, ← WithLp.toLp_zero] using hbz)
    exact (div_le_iff₀ (norm_pos_iff.mpr hx)).mpr (by
      simpa only [div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using habs')
  · intro hb
    have hx : xv = 0 := by simp [xv, bv, hb]
    have hh : ‖WithLp.toLp 2 xhat‖ ≤ 0 := by simpa only [hx, sub_zero, norm_zero, mul_zero, zero_div] using habs'
    have hzero : WithLp.toLp 2 xhat = (0 : Vec ℝ n) := norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
    refine ⟨?_, hx⟩
    exact WithLp.toLp_injective 2 (by simpa only [WithLp.toLp_zero] using hzero)

/-- W23: composition of the actual factorization and triangular runs. -/
theorem solve_certificate : Specs.NumAnalysis206.LinearAlgebra.LUSolveCertificate.solve_certificate := by
  intro n round u D A hm R hnu b y xhat hdiag hforward hbackward
  have hu3 : BudgetDomain (3 * n) u := by
    refine ⟨hm.1, hm.2.1, ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hnu
  have hu := budgetDomain_mono (show n ≤ 3 * n by omega) hu3
  obtain ⟨Δ, hfactor, hΔ⟩ := Doolittle.backward_error round u D A hm R hnu
  obtain ⟨ΔL, hLsolve, hL, _, _⟩ := TriangularSolve.backward_error round u D true
    R.lower ((permutationMatrix R.permutation).mulVec b) y hm R.triangular.1.1
    (fun i => by rw [R.triangular.1.2 i]; exact one_ne_zero) hforward hu.2.2
  obtain ⟨ΔU, hUsolve, hU, _, _⟩ := TriangularSolve.backward_error round u D false
    R.upper y xhat hm R.triangular.2 hdiag hbackward hu.2.2
  let Δsolve := Δ + ΔL * R.upper + R.lower * ΔU + ΔL * ΔU
  have hproduct : permutationMatrix R.permutation * A + Δsolve =
      (R.lower + ΔL) * (R.upper + ΔU) := by
    dsimp [Δsolve]
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
    rw [← hfactor]
    abel
  have hsolve : (permutationMatrix R.permutation * A + Δsolve).mulVec xhat =
      (permutationMatrix R.permutation).mulVec b := by
    rw [hproduct, ← Matrix.mulVec_mulVec, hUsolve, hLsolve]
  have horig := unpermute_equation R.permutation A Δsolve b xhat hsolve
  refine ⟨Δsolve, hsolve, ?_, horig, forward_error A _ b xhat horig⟩
  exact combined_bound R.lower R.upper Δ ΔL ΔU (gamma (3 * n) u) (gamma n u)
    (gamma_nonneg hu) hΔ hL hU

end NumAnalysis206.LinearAlgebra.LUSolveCertificate
