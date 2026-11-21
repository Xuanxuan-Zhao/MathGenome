import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.SmoothSquareCompletion
import MathGenome.Internal.MultivariableAnalysis.D04.C01.EuclideanInterfaces
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter Topology
open scoped BigOperators ContDiff
namespace D04.SmoothSquareCompletion
open Specs.D04.C05.SmoothSquareCompletion

/-- The residual matrix after the first pivot. Its argument is unchanged. -/
def schurResidual {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0

lemma schurResidual_symmetric {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ i j, A i j = A j i) :
    ∀ i j, schurResidual A i j = schurResidual A j i := by
  intro i j
  simp only [schurResidual, hA i.succ j.succ, mul_comm (A 0 i.succ)]

lemma schurResidual_diagonal {n : ℕ} (d : Fin (n+1) → ℝ) :
    schurResidual (Matrix.diagonal d) = Matrix.diagonal (fun i => d i.succ) := by
  ext i j
  simp [schurResidual, Matrix.diagonal_apply, Fin.succ_inj, Ne.symm (Fin.succ_ne_zero i), Ne.symm (Fin.succ_ne_zero j)]

/-- One exact completion of the square, valid for every vector. -/
lemma quadratic_pivot {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hA : ∀ i j, A i j = A j i) (hp : A 0 0 ≠ 0)
    (v : Fin (n+1) → ℝ) :
    quadratic A v =
      A 0 0 * (v 0 + ∑ j : Fin n, (A 0 j.succ / A 0 0) * v j.succ)^2 +
      quadratic (schurResidual A) (fun i => v i.succ) := by
  classical
  unfold quadratic
  rw [Fin.sum_univ_succ]
  simp only [Fin.sum_univ_succ]
  simp only [schurResidual, sub_mul, Finset.sum_sub_distrib]
  have hcross : ∑ i : Fin n, A i.succ 0 * v i.succ * v 0 =
      (∑ i : Fin n, A 0 i.succ * v i.succ) * v 0 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [hA i.succ 0]
  have hdiv : ∑ j : Fin n, A 0 j.succ / A 0 0 * v j.succ =
      (∑ j : Fin n, A 0 j.succ * v j.succ) / A 0 0 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have houter : ∑ i : Fin n, ∑ j : Fin n,
      A 0 i.succ * A 0 j.succ / A 0 0 * v i.succ * v j.succ =
      (∑ i : Fin n, A 0 i.succ * v i.succ)^2 / A 0 0 := by
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hdiv, houter]
  simp_rw [Finset.sum_add_distrib]
  rw [hcross]
  have hfirst : ∑ j : Fin n, A 0 j.succ * v 0 * v j.succ =
      v 0 * ∑ j : Fin n, A 0 j.succ * v j.succ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfirst]
  field_simp [hp]
  ring

/-- Data produced by finite pivot elimination. The polynomial identity holds
for all vectors, not only for the parameter vector. -/
structure Completion {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) (r : ℕ∞ω) (U : Set X) (a : X)
    (A : X → Matrix (Fin n) (Fin n) ℝ) (d₀ : Fin n → ℝ) where
  V : Set X
  isOpen : IsOpen V
  mem : a ∈ V
  subset : V ⊆ U
  d : Fin n → X → ℝ
  b : Fin n → Fin n → X → ℝ
  regular_d : ∀ i, ContDiffOn ℝ r (d i) V
  regular_b : ∀ i j, ContDiffOn ℝ r (b i j) V
  value_d : ∀ i, d i a = d₀ i
  value_b : ∀ i j, b i j a = 0
  triangular : ∀ i j, j ≤ i → ∀ x, b i j x = 0
  sign_d : ∀ x ∈ V, ∀ i, d i x ≠ 0 ∧ Real.sign (d i x) = Real.sign (d₀ i)
  identity : ∀ x ∈ V, ∀ v : Fin n → ℝ,
    quadratic (A x) v = ∑ i, d i x * (v i + ∑ j, b i j x * v j)^2

lemma sign_eq_of_mul_pos {s t : ℝ} (h : 0 < s * t) :
    s ≠ 0 ∧ Real.sign s = Real.sign t := by
  rcases mul_pos_iff.mp h with h | h
  · exact ⟨ne_of_gt h.1, by rw [Real.sign_of_pos h.1, Real.sign_of_pos h.2]⟩
  · exact ⟨ne_of_lt h.1, by rw [Real.sign_of_neg h.1, Real.sign_of_neg h.2]⟩

/-- Finite elimination preserves exactly the given regularity order, including
∞, because no step differentiates the coefficient functions. -/
theorem exists_completion {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) (r : ℕ∞ω) (U : Set X) (a : X)
    (A : X → Matrix (Fin n) (Fin n) ℝ) (d₀ : Fin n → ℝ)
    (hU : IsOpen U) (ha : a ∈ U)
    (hreg : ∀ i j, ContDiffOn ℝ r (fun x => A x i j) U)
    (hsym : ∀ x ∈ U, ∀ i j, A x i j = A x j i)
    (hdiag : A a = Matrix.diagonal d₀) (hne : ∀ i, d₀ i ≠ 0) :
    Nonempty (Completion n r U a A d₀) := by
  classical
  induction n generalizing U with
  | zero =>
    exact ⟨{
      V := U
      isOpen := hU
      mem := ha
      subset := fun _ hx => hx
      d := fun i => Fin.elim0 i
      b := fun i => Fin.elim0 i
      regular_d := fun i => Fin.elim0 i
      regular_b := fun i => Fin.elim0 i
      value_d := fun i => Fin.elim0 i
      value_b := fun i => Fin.elim0 i
      triangular := fun i => Fin.elim0 i
      sign_d := fun _ _ i => Fin.elim0 i
      identity := by intro x hx v; simp [quadratic] }⟩
  | succ n ih =>
    have hp0 : A a 0 0 = d₀ 0 := by rw [hdiag]; simp
    let W : Set X := U ∩ (fun x => A x 0 0 * d₀ 0) ⁻¹' Ioi 0
    have hW : IsOpen W :=
      ((hreg 0 0).continuousOn.mul_const (d₀ 0)).isOpen_inter_preimage hU isOpen_Ioi
    have haW : a ∈ W := ⟨ha, by change 0 < A a 0 0 * d₀ 0; rw [hp0]; exact mul_self_pos.mpr (hne 0)⟩
    have hWsub : W ⊆ U := fun _ hx => hx.1
    have hp (x : X) (hx : x ∈ W) : A x 0 0 ≠ 0 ∧
        Real.sign (A x 0 0) = Real.sign (d₀ 0) := sign_eq_of_mul_pos hx.2
    let R : X → Matrix (Fin n) (Fin n) ℝ := fun x => schurResidual (A x)
    have hRreg : ∀ i j, ContDiffOn ℝ r (fun x => R x i j) W := by
      intro i j
      exact ((hreg i.succ j.succ).mono hWsub).sub
        ((((hreg 0 i.succ).mono hWsub).mul ((hreg 0 j.succ).mono hWsub)).div
          ((hreg 0 0).mono hWsub) (fun x hx => (hp x hx).1))
    have hRsym : ∀ x ∈ W, ∀ i j, R x i j = R x j i :=
      fun x hx => schurResidual_symmetric (A x) (hsym x hx.1)
    have hRdiag : R a = Matrix.diagonal (fun i => d₀ i.succ) := by
      dsimp [R]
      rw [hdiag, schurResidual_diagonal]
    obtain ⟨c⟩ := ih W R (fun i => d₀ i.succ) hW haW hRreg hRsym hRdiag
      (fun i => hne i.succ)
    let d : Fin (n+1) → X → ℝ := Fin.cons (fun x => A x 0 0) c.d
    let b : Fin (n+1) → Fin (n+1) → X → ℝ :=
      Fin.cons (Fin.cons (fun _ => 0) (fun j x => A x 0 j.succ / A x 0 0))
        (fun i => Fin.cons (fun _ => 0) (c.b i))
    refine ⟨{
      V := c.V
      isOpen := c.isOpen
      mem := c.mem
      subset := c.subset.trans hWsub
      d := d
      b := b
      regular_d := ?_
      regular_b := ?_
      value_d := ?_
      value_b := ?_
      triangular := ?_
      sign_d := ?_
      identity := ?_ }⟩
    · intro i
      refine Fin.cases ?_ (fun i => c.regular_d i) i
      exact (hreg 0 0).mono (c.subset.trans hWsub)
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases contDiffOn_const (fun j => ?_) j
        exact ((hreg 0 j.succ).mono (c.subset.trans hWsub)).div
          ((hreg 0 0).mono (c.subset.trans hWsub))
          (fun x hx => (hp x (c.subset hx)).1)
      · exact Fin.cases contDiffOn_const (fun j => c.regular_b i j) j
    · intro i
      exact Fin.cases hp0 c.value_d i
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases rfl (fun j => ?_) j
        change A a 0 j.succ / A a 0 0 = 0
        rw [hdiag]
        simp [Ne.symm (Fin.succ_ne_zero j)]
      · exact Fin.cases rfl (fun j => c.value_b i j) j
    · intro i j hji x
      revert hji
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases (fun _ => rfl) (fun j hj => ?_) j
        exact (Nat.not_succ_le_zero _ hj).elim
      · refine Fin.cases (fun _ => rfl) (fun j hj => ?_) j
        exact c.triangular i j (Fin.succ_le_succ_iff.mp hj) x
    · intro x hx i
      exact Fin.cases (hp x (c.subset hx)) (fun i => c.sign_d x hx i) i
    · intro x hx v
      rw [quadratic_pivot (A x) (hsym x (hWsub (c.subset hx)))
        (hp x (c.subset hx)).1 v, c.identity x hx (fun i => v i.succ)]
      simp [d, b, Fin.sum_univ_succ]


lemma sign_mul_abs (t : ℝ) : Real.sign t * |t| = t := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [Real.sign_of_neg ht, abs_of_neg ht]; ring
  · simp
  · rw [Real.sign_of_pos ht, abs_of_pos ht, one_mul]

/-- Normalizing the pivots does not cost regularity. -/
theorem normalize_completion {n : ℕ} {r : ℕ∞} (hr : 1 ≤ r)
    {U : Set (E n)} {A : E n → Matrix (Fin n) (Fin n) ℝ} {d₀ : Fin n → ℝ}
    (c : Completion n r U 0 A d₀) :
    ContDiffOn ℝ r (normalizedCoordinates c.d c.b) c.V ∧
    normalizedCoordinates c.d c.b 0 = 0 ∧
    (∃ L : E n →L[ℝ] E n,
      HasFDerivAt (normalizedCoordinates c.d c.b) L 0 ∧
      ∀ v i, L v i = Real.sqrt |d₀ i| * v i) ∧
    (∀ x ∈ c.V, quadratic (A x) (fun i => x i) =
      ∑ i, Real.sign (d₀ i) * (normalizedCoordinates c.d c.b x i)^2) := by
  classical
  have hn : c.V ∈ 𝓝 (0 : E n) := c.isOpen.mem_nhds c.mem
  have hrne : (r : ℕ∞ω) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by simp : (0 : ℕ∞) < 1) hr))
  have hc (i : Fin n) : ContDiffOn ℝ r (fun x : E n => x i) c.V :=
    (contDiffOn_piLp 2).mp contDiffOn_id i
  have hs (i : Fin n) : ContDiffOn ℝ r (fun x => Real.sqrt |c.d i x|) c.V :=
    ((c.regular_d i).abs (fun x hx => (c.sign_d x hx i).1)).sqrt
      (fun x hx => abs_ne_zero.mpr (c.sign_d x hx i).1)
  have ht (i : Fin n) : ContDiffOn ℝ r (fun x => triangularCoordinate c.b x i) c.V :=
    (hc i).add (ContDiffOn.sum (fun j _ => (c.regular_b i j).mul (hc j)))
  have hchi : ContDiffOn ℝ r (normalizedCoordinates c.d c.b) c.V :=
    (contDiffOn_piLp 2).mpr (fun i => (hs i).mul (ht i))
  have hzero : normalizedCoordinates c.d c.b 0 = 0 := by
    ext i
    simp [normalizedCoordinates, triangularCoordinate]
  have htderiv (i : Fin n) : HasFDerivAt (fun x => triangularCoordinate c.b x i)
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i) 0 := by
    have hp (j : Fin n) : HasFDerivAt (𝕜 := ℝ) (fun x : E n => c.b i j x * x j) 0 0 := by
      have hb := ((c.regular_b i j).contDiffAt hn).differentiableAt hrne
      convert hb.hasFDerivAt.fun_mul (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (0 : E n) j) using 1 <;>
        simp [c.value_b i j]
    have hsum := HasFDerivAt.fun_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hp j)
    simpa [triangularCoordinate, Pi.add_apply] using
      (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 (0 : E n) i).fun_add hsum
  have hideriv (i : Fin n) : HasFDerivAt
      (fun x : E n => normalizedCoordinates c.d c.b x i)
      (Real.sqrt |d₀ i| • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin n => ℝ) i) 0 := by
    have h := (((hs i).contDiffAt hn).differentiableAt hrne).hasFDerivAt.fun_mul (htderiv i)
    convert h using 1 <;>
      simp [normalizedCoordinates, triangularCoordinate, c.value_d i]
  let L := fderiv ℝ (normalizedCoordinates c.d c.b) 0
  have hL : HasFDerivAt (normalizedCoordinates c.d c.b) L 0 :=
    ((hchi.contDiffAt hn).differentiableAt hrne).hasFDerivAt
  refine ⟨hchi, hzero, ⟨L, hL, ?_⟩, ?_⟩
  · intro v i
    have he := ((PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2
      (normalizedCoordinates c.d c.b 0) i).comp 0 hL).unique (hideriv i)
    exact congrArg (fun T : E n →L[ℝ] ℝ => T v) he
  · intro x hx
    rw [c.identity x hx]
    apply Finset.sum_congr rfl
    intro i _
    change c.d i x * (x i + ∑ j, c.b i j x * x j)^2 =
      Real.sign (d₀ i) * (Real.sqrt |c.d i x| * (x i + ∑ j, c.b i j x * x j))^2
    rw [mul_pow, Real.sq_sqrt (abs_nonneg _), ← (c.sign_d x hx i).2,
      ← mul_assoc, sign_mul_abs]

/-- Local algebraic square completion, uniformly in finite or smooth regularity. -/
theorem square_completion : squareCompletionType := by
  intro n r hr U A d₀ hU h0 hreg hsym hdiag hne
  obtain ⟨c⟩ := exists_completion n r U 0 A d₀ hU h0 hreg hsym hdiag hne
  obtain ⟨hchi, hz, hD, hq⟩ := normalize_completion hr c
  exact ⟨c.V, c.d, c.b, c.isOpen, c.mem, c.subset,
    c.regular_d, c.regular_b, c.value_d, c.value_b, c.triangular, c.sign_d,
    (fun x hx => c.identity x hx (fun i => x i)), hchi, hz, hD, hq⟩

end D04.SmoothSquareCompletion
