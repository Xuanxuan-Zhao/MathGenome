import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.Morse
import MathGenome.Internal.MultivariableAnalysis.D04.C05.MorseCoefficients
import MathGenome.Internal.MultivariableAnalysis.D04.C05.SmoothSquareCompletion
import MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin

noncomputable section
open Set Filter Topology
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace D04.Morse
open Specs.D04.C05.Morse
open Specs.D04.C05.SmoothSquareCompletion
open private inverse_neighborhood from MathGenome.Internal.MultivariableAnalysis.D04.C04.InverseFunction

/-- A continuous linear map which multiplies each coordinate by a nonzero
number is invertible, including on the zero-dimensional space. -/
theorem diagonal_derivative_bijective {n : ℕ} (L : E n →L[ℝ] E n)
    (s : Fin n → ℝ) (hs : ∀ i, s i ≠ 0) (hL : ∀ v i, L v i = s i * v i) :
    Function.Bijective L := by
  constructor
  · intro v w h
    ext i
    apply mul_left_cancel₀ (hs i)
    simpa only [hL] using congrArg (fun x : E n => x i) h
  · intro w
    refine ⟨WithLp.toLp 2 (fun i => w i / s i), ?_⟩
    ext i
    rw [hL]
    change s i * (w i / s i) = w i
    field_simp [hs i]

/-- Square completion followed by the inverse function theorem gives actual
coordinate neighborhoods and an inverse with the same regularity. -/
theorem diagonal_coefficient_normal_form : diagonalCoefficientNormalFormType := by
  intro n r hr U A d₀ f hU h0 hreg hsym hdiag hne hid
  obtain ⟨V, d, b, hV, h0V, hVU, hd, hb, hd0, hb0, htri, hsign,
    hquad, hχ, hχ0, ⟨L, hL, hLi⟩, hnorm⟩ :=
    D04.SmoothSquareCompletion.square_completion n r hr U A d₀ hU h0 hreg hsym hdiag hne
  let χ := normalizedCoordinates d b
  have hbijL := diagonal_derivative_bijective L (fun i => Real.sqrt |d₀ i|)
    (fun i => Real.sqrt_ne_zero'.mpr (abs_pos.mpr (hne i))) hLi
  let e : E n ≃L[ℝ] E n := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hbijL.1) (LinearMap.range_eq_top.mpr hbijL.2)
  have he : e.toContinuousLinearMap = fderiv ℝ χ 0 := hL.fderiv.symm
  obtain ⟨X, Y, ψ, hgeom, hψ⟩ := inverse_neighborhood V χ 0 e
    (by exact_mod_cast hr) hV hχ h0V he
  rcases hgeom with ⟨hX, hY, h0X, hχ0Y, hXV, hbij, hmap, hleft, hright,
    hforward, hbackward, hlip, huniq⟩
  have h0Y : (0 : E n) ∈ Y := by simpa only [χ, hχ0] using hχ0Y
  have hψ0 : ψ 0 = 0 := by simpa only [χ, hχ0] using hleft h0X
  refine ⟨X, Y, χ, ψ, hX, hY, h0X, h0Y, hXV.trans hVU,
    hbij, hmap, hleft, hright, hχ0, hψ0, hχ.mono hXV, hψ, ?_⟩
  intro y hy
  have hxV : ψ y ∈ V := hXV (hmap hy)
  have h := (hid (ψ y) (hVU hxV)).trans (hnorm (ψ y) hxV)
  change f (ψ y) - f 0 = ∑ i, Real.sign (d₀ i) * (χ (ψ y) i)^2 at h
  rw [hright hy] at h
  linarith

lemma matrix_associated {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hs : H.IsSymm) :
    QuadraticMap.associated H.toQuadraticForm' = Matrix.toLinearMap₂' ℝ H := by
  apply QuadraticMap.associated_left_inverse ℝ
  intro x y
  simp only [Matrix.toLinearMap₂'_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show H j i = H i j from congrFun (congrFun hs i) j]
  ring

lemma matrix_toMatrix {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (hs : H.IsSymm) :
    QuadraticForm.toMatrix' H.toQuadraticForm' = H := by
  simp only [QuadraticForm.toMatrix', matrix_associated H hs]
  exact (Matrix.toLinearMap₂' ℝ).symm_apply_apply H

lemma diagonal_form {n : ℕ} (w : Fin n → ℝ) :
    (Matrix.diagonal w).toQuadraticForm' = QuadraticMap.weightedSumSquares ℝ w := by
  ext x
  simp [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply, Matrix.diagonal_apply, mul_comm, mul_left_comm]

lemma diagonal_toMatrix {n : ℕ} (w : Fin n → ℝ) :
    QuadraticForm.toMatrix' (QuadraticMap.weightedSumSquares ℝ w) = Matrix.diagonal w := by
  rw [← diagonal_form]
  exact matrix_toMatrix _ (Matrix.isSymm_diagonal w)

theorem sign_diagonalization {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hs : H.IsSymm) (hdet : H.det ≠ 0) :
    ∃ (P : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (w : Fin n → ℝ),
      (∀ i, w i = -1 ∨ w i = 1) ∧
      Matrix.transpose (P.toLinearMap.toMatrix') * H * P.toLinearMap.toMatrix' = Matrix.diagonal w ∧
      H.toQuadraticForm'.comp P.toLinearMap = QuadraticMap.weightedSumSquares ℝ w ∧
      sigPos H.toQuadraticForm' = {i | 0 < w i}.ncard ∧
      sigNeg H.toQuadraticForm' = {i | w i < 0}.ncard := by
  have hn : (QuadraticMap.associated H.toQuadraticForm').SeparatingLeft := by
    rw [matrix_associated H hs]
    exact LinearMap.separatingLeft_toLinearMap₂'_of_det_ne_zero' hdet
  have hx := QuadraticForm.equivalent_one_neg_one_weighted_sum_squared H.toQuadraticForm' hn
  have hdim : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  rw [hdim] at hx
  obtain ⟨w, hw, ⟨e⟩⟩ := hx
  refine ⟨e.symm.toLinearEquiv, w, hw, ?_, ?_, ?_, ?_⟩
  · have he : H.toQuadraticForm'.comp e.symm.toLinearEquiv.toLinearMap =
        QuadraticMap.weightedSumSquares ℝ w := by
      ext x
      exact e.symm.map_app x
    have hm := congrArg QuadraticForm.toMatrix' he
    simpa only [QuadraticForm.toMatrix'_comp, matrix_toMatrix H hs, diagonal_toMatrix] using hm
  · ext x
    exact e.symm.map_app x
  · exact QuadraticForm.sigPos_of_equiv_weightedSumSquares ⟨e⟩
  · exact QuadraticForm.sigNeg_of_equiv_weightedSumSquares ⟨e⟩

lemma positive_iff_index {n : ℕ} (w : Fin n → ℝ) (hm : Antitone w)
    (i : Fin n) : 0 < w i ↔ i.val < (Finset.univ.filter (fun j => 0 < w j)).card := by
  classical
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ Finset.univ.filter (fun j => 0 < w j) := by
      intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.trans_le (hm (Finset.mem_Iic.mp hj))⟩
    have h := Finset.card_le_card hsub
    simp only [Fin.card_Iic] at h
    omega
  · intro hi
    by_contra hn
    have hsub : Finset.univ.filter (fun j => 0 < w j) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hji
      have hh := hm (le_of_not_gt hji)
      exact hn ((Finset.mem_filter.mp hj).2.trans_le hh)
    have h := Finset.card_le_card hsub
    simp only [Fin.card_Iio] at h
    omega

lemma sorted_signs {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, w i = -1 ∨ w i = 1) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i,
      w (σ i) = if i.val < {j | 0 < w j}.ncard then (1 : ℝ) else -1 := by
  classical
  let σ : Equiv.Perm (Fin n) := (Tuple.sort w) * Fin.revPerm
  have hm : Antitone (fun i => w (σ i)) := by
    intro i j hij
    exact Tuple.monotone_sort w (Fin.rev_le_rev.mpr hij)
  have hc : (Finset.univ.filter (fun j => 0 < w (σ j))).card = {j | 0 < w j}.ncard := by
    rw [Set.ncard_eq_toFinset_card']
    apply Finset.card_equiv σ
    simp
  refine ⟨σ, fun i => ?_⟩
  have hh := positive_iff_index (fun i => w (σ i)) hm i
  rw [hc] at hh
  by_cases hi : i.val < {j | 0 < w j}.ncard
  · rw [ite_eq_left hi]
    rcases hw (σ i) with h | h
    · have := hh.mpr hi; linarith
    · exact h
  · rw [ite_eq_right hi]
    rcases hw (σ i) with h | h
    · exact h
    · have : 0 < w (σ i) := by rw [h]; norm_num
      exact (hi (hh.mp this)).elim

theorem ordered_diagonalization {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (hs : H.IsSymm) (hdet : H.det ≠ 0) :
    ∃ P : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ),
      Matrix.transpose P.toLinearMap.toMatrix' * H * P.toLinearMap.toMatrix' =
        Matrix.diagonal (fun i => if i.val < sigPos H.toQuadraticForm' then (1 : ℝ) else -1) := by
  classical
  obtain ⟨P, w, hw, hmatrix, heq, hpos, hneg⟩ := sign_diagonalization H hs hdet
  obtain ⟨σ, hσ⟩ := sorted_signs w hw
  let R := LinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℝ) σ
  let P' := R.trans P
  have heq' : H.toQuadraticForm'.comp P'.toLinearMap =
      QuadraticMap.weightedSumSquares ℝ
        (fun i => if i.val < sigPos H.toQuadraticForm' then (1 : ℝ) else -1) := by
    ext x
    change H.toQuadraticForm' (P (R x)) = _
    have he := congrArg (fun Q : QuadraticForm ℝ (Fin n → ℝ) => Q (R x)) heq
    change H.toQuadraticForm' (P (R x)) = _ at he
    rw [he]
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul]
    rw [← Equiv.sum_comp σ (fun i => w i * ((R x) i * (R x) i))]
    apply Finset.sum_congr rfl
    intro i _
    have hr : (R x) (σ i) = x i := by simp [R, LinearEquiv.piCongrLeft]
    rw [hr]
    rw [hσ i, ← hpos]
  refine ⟨P', ?_⟩
  have hm := congrArg QuadraticForm.toMatrix' heq'
  rw [QuadraticForm.toMatrix'_comp, matrix_toMatrix H hs,
    diagonal_toMatrix (fun i : Fin n => if i.val < sigPos H.toQuadraticForm' then (1 : ℝ) else -1)] at hm
  exact hm

lemma sigPos_pos_smul {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) (c : ℝ) (hc : 0 < c) :
    sigPos (c • Q) = sigPos Q := by
  have hV (V : Submodule ℝ (Fin n → ℝ)) :
      (QuadraticMap.restrict (c • Q) V).PosDef ↔ (QuadraticMap.restrict Q V).PosDef := by
    change (∀ x : V, x ≠ 0 → 0 < c * Q x) ↔ (∀ x : V, x ≠ 0 → 0 < Q x)
    simp only [mul_pos_iff_of_pos_left hc]
  apply le_antisymm
  · obtain ⟨V, hd, hp⟩ := exists_finrank_eq_sigPos_and_posDef (c • Q)
    rw [← hd]
    exact le_sigPos_of_posDef Q ((hV V).mp hp)
  · obtain ⟨V, hd, hp⟩ := exists_finrank_eq_sigPos_and_posDef Q
    rw [← hd]
    exact le_sigPos_of_posDef (c • Q) ((hV V).mpr hp)

lemma sigNeg_pos_smul {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) (c : ℝ) (hc : 0 < c) :
    sigNeg (c • Q) = sigNeg Q := by
  unfold sigNeg
  have he : -(c • Q) = c • (-Q) := by
    ext x
    change -(c * Q x) = c * -(Q x)
    ring
  rw [he]
  exact sigPos_pos_smul (-Q) c hc

lemma quadratic_eq_dot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadratic A v = dotProduct v (A.mulVec v) := by
  simp only [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma quadratic_congruence {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadratic (M.transpose * A * M) v = quadratic A (M.mulVec v) := by
  rw [quadratic_eq_dot, quadratic_eq_dot, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

lemma standardQuadratic_eq {n : ℕ} (p : ℕ) (y : E n) :
    standardQuadratic p y = ∑ i : Fin n, (if i.val < p then (1 : ℝ) else -1) * (y i)^2 := by
  rw [standardQuadratic, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < p <;> simp [hi, Nat.not_lt.mp, Nat.not_le.mpr]

/-- Transport a normal form through a constant linear change of input. -/
theorem normalForm_linear_transport {n : ℕ} (r : ℕ∞ω) (U : Set (E n))
    (f : E n → ℝ) (e : E n ≃L[ℝ] E n) (p : ℕ)
    (h : NormalForm r (e ⁻¹' U) (fun x => f (e x)) 0 p) : NormalForm r U f 0 p := by
  obtain ⟨X, Y, χ, ψ, hX, hY, h0X, h0Y, hXU, hbij, hmap, hleft,
    hright, hχ0, hψ0, hχ, hψ, hform⟩ := h
  let X' := e.symm ⁻¹' X
  have hXe : MapsTo e X X' := by intro x hx; simpa [X'] using hx
  have hXe' : MapsTo e.symm X' X := fun _ hx => hx
  refine ⟨X', Y, (fun x => χ (e.symm x)), (fun y => e (ψ y)),
    hX.preimage e.symm.continuous, hY, ?_, h0Y, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hχ.comp e.symm.contDiff.contDiffOn hXe',
    e.contDiff.contDiffOn.comp hψ (fun _ _ => mem_univ _), ?_⟩
  · simpa [X'] using h0X
  · intro x hx
    have := hXU hx
    simpa using this
  · refine ⟨hbij.1.comp hXe', hbij.2.1.comp e.symm.injective.injOn hXe', ?_⟩
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hbij.2.2 hy
    exact ⟨e x, hXe hx, by simpa using hxy⟩
  · exact hXe.comp hmap
  · intro x hx
    change e (ψ (χ (e.symm x))) = x
    rw [hleft hx, e.apply_symm_apply]
  · intro y hy
    change χ (e.symm (e (ψ y))) = y
    rw [e.symm_apply_apply, hright hy]
  · simpa using hχ0
  · simp [hψ0]
  · intro y hy
    simpa using hform y hy

/-- The algebraic coefficient construction with its actual constant inertia
bridge. No differentiability of a spectral basis as a function of x is used. -/
theorem coefficient_normal_form {n : ℕ} (r : ℕ∞) (hr : 1 ≤ r)
    (U : Set (E n)) (A : E n → Matrix (Fin n) (Fin n) ℝ) (f : E n → ℝ)
    (hU : IsOpen U) (h0 : (0 : E n) ∈ U)
    (hreg : ∀ i j, ContDiffOn ℝ r (fun x => A x i j) U)
    (hsym : ∀ x ∈ U, (A x).IsSymm) (hdet : (A 0).det ≠ 0)
    (hid : ∀ x ∈ U, f x - f 0 = quadratic (A x) (fun i => x i)) :
    NormalForm r U f 0 (sigPos (A 0).toQuadraticForm') := by
  classical
  obtain ⟨P, hP⟩ := ordered_diagonalization (A 0) (hsym 0 h0) hdet
  let e : E n ≃L[ℝ] E n :=
    (((coordinates n).trans P).trans (coordinates n).symm).toContinuousLinearEquiv
  let M := P.toLinearMap.toMatrix'
  let W := e ⁻¹' U
  let B (x : E n) := M.transpose * A (e x) * M
  let p := sigPos (A 0).toQuadraticForm'
  let d₀ (i : Fin n) : ℝ := if i.val < p then 1 else -1
  have hW : IsOpen W := hU.preimage e.continuous
  have h0W : (0 : E n) ∈ W := by simpa [W] using h0
  have heM (x : E n) : (fun i => e x i) = M.mulVec (fun i => x i) := by
    change P (fun i => x i) = _
    have := congrArg (fun L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) => L (fun i => x i))
      (Matrix.toLin'_toMatrix' P.toLinearMap)
    exact this.symm
  have hBreg : ∀ i j, ContDiffOn ℝ r (fun x => B x i j) W := by
    intro i j
    change ContDiffOn ℝ r (fun x => ∑ k, (∑ l, M l i * A (e x) l k) * M k j) W
    apply ContDiffOn.sum
    intro k _
    apply ContDiffOn.mul _ contDiffOn_const
    apply ContDiffOn.sum
    intro l _
    exact contDiffOn_const.mul ((hreg l k).comp e.contDiff.contDiffOn (fun x hx => hx))
  have hBsym : ∀ x ∈ W, ∀ i j, B x i j = B x j i := by
    intro x hx i j
    have h : (B x).IsSymm := by
      change (M.transpose * A (e x) * M).transpose = M.transpose * A (e x) * M
      simp only [Matrix.transpose_mul, Matrix.transpose_transpose, (hsym (e x) hx).eq,
        Matrix.mul_assoc]
    exact (congrFun (congrFun h i) j).symm
  have hB0 : B 0 = Matrix.diagonal d₀ := by simpa [B, M, d₀, p] using hP
  have hd₀ : ∀ i, d₀ i ≠ 0 := by intro i; simp [d₀]; split_ifs <;> norm_num
  have hBid : ∀ x ∈ W, f (e x) - f (e 0) = quadratic (B x) (fun i => x i) := by
    intro x hx
    rw [map_zero, hid (e x) hx]
    rw [show B x = M.transpose * A (e x) * M from rfl,
      quadratic_congruence, ← heM x]
  obtain ⟨X, Y, χ, ψ, hX, hY, h0X, h0Y, hXW, hbij, hmap, hleft, hright,
    hχ0, hψ0, hχ, hψ, hform⟩ := diagonal_coefficient_normal_form n r hr W B d₀
      (fun x => f (e x)) hW h0W hBreg hBsym hB0 hd₀ hBid
  apply normalForm_linear_transport r U f e p
  refine ⟨X, Y, χ, ψ, hX, hY, h0X, h0Y, hXW, hbij, hmap, hleft,
    hright, hχ0, hψ0, hχ, hψ, ?_⟩
  intro y hy
  dsimp only
  rw [hform y hy, standardQuadratic_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < p <;> simp [d₀, hi, Real.sign]

lemma matrix_form_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    (c • H).toQuadraticForm' = c • H.toQuadraticForm' := by
  ext x
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    map_smul, LinearMap.smul_apply, smul_apply]

lemma half_hessian_inertia {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) :
    sigPos ((1/2 : ℝ) • H).toQuadraticForm' = sigPos H.toQuadraticForm' ∧
    sigNeg ((1/2 : ℝ) • H).toQuadraticForm' = sigNeg H.toQuadraticForm' := by
  rw [matrix_form_smul]
  exact ⟨sigPos_pos_smul _ _ (by norm_num), sigNeg_pos_smul _ _ (by norm_num)⟩

/-- Finite regularity, with the critical point centered at zero. -/
theorem morse_centered_finite {n : ℕ} (r : ℕ) (hr : 1 ≤ r)
    (U : Set (E n)) (f : E n → ℝ) (hU : IsOpen U) (h0 : (0 : E n) ∈ U)
    (hf : CrOn (r+2) U f) (hc : totalDerivative f 0 = 0)
    (hdet : (hessian f 0).det ≠ 0) :
    NormalForm r U f 0 (sigPos (hessian f 0).toQuadraticForm') := by
  obtain ⟨ρ, hρ, hρU, hrad, hint, hid, hsym, hz, hreg⟩ :=
    D04.morse_coefficients r hr U f hU h0 hf hc
  have hAreg := (D04.crOn_iff_contDiffOn r (Metric.ball 0 ρ)
    (morseCoefficients f) Metric.isOpen_ball).mp hreg
  have hAdet : (morseCoefficients f 0).det ≠ 0 := by
    rw [hz, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  have h := coefficient_normal_form (r : ℕ∞) (by exact_mod_cast hr)
    (Metric.ball 0 ρ) (morseCoefficients f) f Metric.isOpen_ball (Metric.mem_ball_self hρ)
    (fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp hAreg i) j)
    (fun x hx => hsym x (Metric.ball_subset_closedBall hx)) hAdet
    (fun x hx => hid x (Metric.ball_subset_closedBall hx))
  rw [hz, (half_hessian_inertia (hessian f 0)).1] at h
  obtain ⟨X, Y, χ, ψ, hX, hY, h0X, h0Y, hXball, hrest⟩ := h
  exact ⟨X, Y, χ, ψ, hX, hY, h0X, h0Y,
    hXball.trans (Metric.ball_subset_closedBall.trans hρU), hrest⟩

/-- The same coefficients and one inverse yield smooth coordinates. -/
theorem morse_centered_smooth {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (h0 : (0 : E n) ∈ U) (hf : SmoothOn U f)
    (hc : totalDerivative f 0 = 0) (hdet : (hessian f 0).det ≠ 0) :
    NormalForm ∞ U f 0 (sigPos (hessian f 0).toQuadraticForm') := by
  obtain ⟨ρ, hρ, hρU, hrad, hint, hid, hsym, hz, hreg⟩ :=
    D04.morse_coefficients_smooth U f hU h0 hf hc
  have hAreg := (D04.smoothOn_iff_contDiffOn (Metric.ball 0 ρ)
    (morseCoefficients f) Metric.isOpen_ball).mp hreg
  have hAdet : (morseCoefficients f 0).det ≠ 0 := by
    rw [hz, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hdet
  have h := coefficient_normal_form (⊤ : ℕ∞) (by simp)
    (Metric.ball 0 ρ) (morseCoefficients f) f Metric.isOpen_ball (Metric.mem_ball_self hρ)
    (fun i j => contDiffOn_pi.mp (contDiffOn_pi.mp hAreg i) j)
    (fun x hx => hsym x (Metric.ball_subset_closedBall hx)) hAdet
    (fun x hx => hid x (Metric.ball_subset_closedBall hx))
  rw [hz, (half_hessian_inertia (hessian f 0)).1] at h
  obtain ⟨X, Y, χ, ψ, hX, hY, h0X, h0Y, hXball, hrest⟩ := h
  exact ⟨X, Y, χ, ψ, hX, hY, h0X, h0Y,
    hXball.trans (Metric.ball_subset_closedBall.trans hρU), hrest⟩

/-- Translation commutes with every ordered partial selector, even before
existence of the derivatives is imposed. -/
lemma orderedPartial_translate {n : ℕ} (is : List (Fin n)) (f : E n → ℝ) (a x : E n) :
    orderedPartial is (fun z => f (a + z)) x = orderedPartial is f (a + x) := by
  induction is generalizing x with
  | nil => rfl
  | cons i is ih =>
    change deriv (fun t : ℝ => orderedPartial is (fun z => f (a + z))
      (x + t • standardBasis n i)) 0 =
      deriv (fun t : ℝ => orderedPartial is f ((a + x) + t • standardBasis n i)) 0
    congr 1
    funext t
    rw [ih]
    congr 1
    abel

lemma hessian_translate {n : ℕ} (f : E n → ℝ) (a : E n) :
    hessian (fun x => f (a + x)) 0 = hessian f a := by
  ext i j
  change orderedPartial [i,j] (fun x => f (a + x)) 0 = orderedPartial [i,j] f a
  simpa using orderedPartial_translate [i,j] f a 0

/-- Transport from centered coordinates to the specified critical point. -/
theorem normalForm_translate {n : ℕ} (r : ℕ∞ω) (U : Set (E n))
    (f : E n → ℝ) (a : E n) (p : ℕ)
    (h : NormalForm r ((fun x => a + x) ⁻¹' U) (fun x => f (a + x)) 0 p) :
    NormalForm r U f a p := by
  obtain ⟨X, Y, χ, ψ, hX, hY, h0X, h0Y, hXU, hbij, hmap, hleft,
    hright, hχ0, hψ0, hχ, hψ, hform⟩ := h
  let X' := (fun x => x - a) ⁻¹' X
  have hXe : MapsTo (fun x => a + x) X X' := by
    intro x hx
    simpa [X', add_sub_cancel_left] using hx
  have hXe' : MapsTo (fun x => x - a) X' X := fun _ hx => hx
  have hsub : ContDiff ℝ r (fun x : E n => x - a) := contDiff_id.sub contDiff_const
  have hadd : ContDiff ℝ r (fun x : E n => a + x) := contDiff_const.add contDiff_id
  refine ⟨X', Y, (fun x => χ (x - a)), (fun y => a + ψ y),
    hX.preimage hsub.continuous, hY, ?_, h0Y, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, hχ.comp hsub.contDiffOn hXe',
    hadd.contDiffOn.comp hψ (fun _ _ => mem_univ _), ?_⟩
  · simpa [X'] using h0X
  · intro x hx
    have := hXU hx
    simpa only [mem_preimage, add_sub_cancel] using this
  · refine ⟨hbij.1.comp hXe', ?_, ?_⟩
    · intro x hx y hy hxy
      have := hbij.2.1 hx hy hxy
      have hh := congrArg (fun z => z + a) this
      simpa only [sub_add_cancel] using hh
    · intro y hy
      obtain ⟨x, hx, hxy⟩ := hbij.2.2 hy
      exact ⟨a + x, hXe hx, by simpa only [add_sub_cancel_left] using hxy⟩
  · exact hXe.comp hmap
  · intro x hx
    change a + ψ (χ (x - a)) = x
    rw [hleft hx, add_sub_cancel]
  · intro y hy
    change χ (a + ψ y - a) = y
    rw [add_sub_cancel_left, hright hy]
  · simpa using hχ0
  · simp [hψ0]
  · intro y hy
    simpa using hform y hy

/-- Bounded Morse lemma with exactly C^(r+2) data and C^r coordinates. -/
theorem morse_finite : morse_finiteType := by
  intro n r hr U f a p q hU ha hf hc hsym hdet hp hq hpq
  let V := (fun x : E n => a + x) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have h0V : (0 : E n) ∈ V := by simpa [V] using ha
  have hf' : CrOn (r+2) V (fun x => f (a + x)) := by
    apply (D04.crOn_iff_contDiffOn _ _ _ hV).mpr
    exact ((D04.crOn_iff_contDiffOn (r+2) U f hU).mp hf).comp
      (contDiff_const.add contDiff_id).contDiffOn (fun x hx => hx)
  have hc' : totalDerivative (fun x => f (a + x)) 0 = 0 := by
    change fderiv ℝ (fun x => f (a + x)) 0 = 0
    rw [fderiv_comp_add_left, add_zero]
    exact hc
  have hH := hessian_translate f a
  have hdet' : (hessian (fun x => f (a + x)) 0).det ≠ 0 := by rwa [hH]
  have h := morse_centered_finite r hr V (fun x => f (a + x)) hV h0V hf' hc' hdet'
  rw [hH, hp] at h
  exact normalForm_translate r U f a p h

/-- Smooth Morse lemma, using one smooth coordinate map and inverse. -/
theorem morse_smooth : morse_smoothType := by
  intro n U f a p q hU ha hf hc hsym hdet hp hq hpq
  let V := (fun x : E n => a + x) ⁻¹' U
  have hV : IsOpen V := hU.preimage (continuous_const.add continuous_id)
  have h0V : (0 : E n) ∈ V := by simpa [V] using ha
  have hf' : SmoothOn V (fun x => f (a + x)) := by
    apply (D04.smoothOn_iff_contDiffOn _ _ hV).mpr
    exact ((D04.smoothOn_iff_contDiffOn _ _ hU).mp hf).comp
      (contDiff_const.add contDiff_id).contDiffOn (fun x hx => hx)
  have hc' : totalDerivative (fun x => f (a + x)) 0 = 0 := by
    change fderiv ℝ (fun x => f (a + x)) 0 = 0
    rw [fderiv_comp_add_left, add_zero]
    exact hc
  have hH := hessian_translate f a
  have hdet' : (hessian (fun x => f (a + x)) 0).det ≠ 0 := by rwa [hH]
  have h := morse_centered_smooth V (fun x => f (a + x)) hV h0V hf' hc' hdet'
  rw [hH, hp] at h
  exact normalForm_translate ∞ U f a p h

end D04.Morse
