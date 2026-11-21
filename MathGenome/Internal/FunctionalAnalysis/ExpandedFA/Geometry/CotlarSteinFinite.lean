import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Geometry.CotlarSteinFinite
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hilbert.Adjoint
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace ExpandedFA.Geometry.CotlarSteinFinite

/-! The power argument is implemented with nested finite sums of words.
Two ways of pairing a word give the product of adjacent square-root norms.
The row bounds then sum these weights one index at a time. -/

section Words
variable {ι E : Type*} [NormedRing E]

/-- Alternating word in two families of letters. -/
def word (L : Bool → ι → E) : Bool → List ι → E
  | _, [] => 1
  | b, i :: l => L b i * word L (!b) l

/-- Product of the norms after pairing consecutive letters. -/
def pairBound (L : Bool → ι → E) : Bool → List ι → ℝ
  | _, [] => 1
  | b, [i] => ‖L b i‖
  | b, i :: j :: l => ‖L b i * L (!b) j‖ * pairBound L b l

/-- The chain of adjacent square-root norms starting at a fixed index. -/
def chain (L : Bool → ι → E) : Bool → ι → List ι → ℝ
  | _, _, [] => 1
  | b, i, j :: l => Real.sqrt ‖L b i * L (!b) j‖ * chain L (!b) j l

lemma pairBound_nonneg (L : Bool → ι → E) (b : Bool) (l : List ι) :
    0 ≤ pairBound L b l := by
  fun_induction pairBound <;> simp_all [mul_nonneg, norm_nonneg]

lemma chain_nonneg (L : Bool → ι → E) (b : Bool) (i : ι) (l : List ι) :
    0 ≤ chain L b i l := by
  induction l generalizing b i with
  | nil => simp [chain]
  | cons j l ih => exact mul_nonneg (Real.sqrt_nonneg _) (ih _ _)

lemma norm_word_le_pairBound [NormOneClass E] (L : Bool → ι → E) (b : Bool) (l : List ι) :
    ‖word L b l‖ ≤ pairBound L b l := by
  fun_induction pairBound L b l with
  | case1 => simp [word]
  | case2 b i => simp [word]
  | case3 b i j l ih =>
    simpa only [word, pairBound, Bool.not_not, ← mul_assoc] using
      (norm_mul_le (L b i * L (!b) j) (word L b l)).trans
        (mul_le_mul_of_nonneg_left ih (norm_nonneg _))

lemma pairBound_overlap (L : Bool → ι → E) (C : ℝ)
    (hL : ∀ b i, ‖L b i‖ ≤ C) (b : Bool) (i : ι) (l : List ι) :
    pairBound L b (i :: l) * pairBound L (!b) l ≤ C * chain L b i l ^ 2 := by
  induction l generalizing b i with
  | nil => simpa [pairBound, chain] using hL b i
  | cons j l ih =>
    simp only [pairBound, chain]
    calc
      _ = ‖L b i * L (!b) j‖ *
          (pairBound L (!b) (j :: l) * pairBound L b l) := by ring
      _ ≤ ‖L b i * L (!b) j‖ * (C * chain L (!b) j l ^ 2) :=
        mul_le_mul_of_nonneg_left (by simpa using ih (!b) j) (norm_nonneg _)
      _ = _ := by rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]; ring

lemma norm_word_le_chain [NormOneClass E] (L : Bool → ι → E) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ b i, ‖L b i‖ ≤ C) (b : Bool) (i : ι) (l : List ι) :
    ‖word L b (i :: l)‖ ≤ C * chain L b i l := by
  have h₁ := norm_word_le_pairBound L b (i :: l)
  have h₂ : ‖word L b (i :: l)‖ ≤ C * pairBound L (!b) l := by
    exact (norm_mul_le _ _).trans (mul_le_mul (hL b i)
      (norm_word_le_pairBound L (!b) l) (norm_nonneg _) hC)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (chain_nonneg ..))).mp
  calc
    _ ≤ pairBound L b (i :: l) * (C * pairBound L (!b) l) := by
      simpa [pow_two] using mul_le_mul h₁ h₂ (norm_nonneg _) (pairBound_nonneg ..)
    _ = C * (pairBound L b (i :: l) * pairBound L (!b) l) := by ring
    _ ≤ C * (C * chain L b i l ^ 2) :=
      mul_le_mul_of_nonneg_left (pairBound_overlap L C hL b i l) hC
    _ = _ := by ring

variable [Fintype ι]

/-- Sum over all paths of the specified length; repetitions are counted. -/
def pathSum {M : Type*} [AddCommMonoid M] (n : ℕ) (f : List ι → M) : M :=
  match n with
  | 0 => f []
  | n + 1 => ∑ i, pathSum n (fun l => f (i :: l))

lemma pathSum_mono (n : ℕ) {f g : List ι → ℝ} (h : ∀ l, f l ≤ g l) :
    pathSum n f ≤ pathSum n g := by
  induction n generalizing f g with
  | zero => exact h []
  | succ n ih => exact Finset.sum_le_sum fun i _ => ih (fun l => h (i :: l))

lemma pathSum_mul_left {R : Type*} [NonUnitalNonAssocSemiring R]
    (n : ℕ) (a : R) (f : List ι → R) :
    pathSum n (fun l => a * f l) = a * pathSum n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [pathSum, ih, Finset.mul_sum]

lemma norm_pathSum_le (n : ℕ) (f : List ι → E) :
    ‖pathSum n f‖ ≤ pathSum n (fun l => ‖f l‖) := by
  induction n generalizing f with
  | zero => exact le_rfl
  | succ n ih =>
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ih _)

/-- Alternating product of the two row bounds. -/
def rows (r : Bool → ℝ) : Bool → ℕ → ℝ
  | _, 0 => 1
  | b, n + 1 => r b * rows r (!b) n

lemma rows_nonneg (r : Bool → ℝ) (hr : ∀ b, 0 ≤ r b) (b : Bool) (n : ℕ) :
    0 ≤ rows r b n := by
  induction n generalizing b with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hr b) (ih _)

lemma pathSum_chain_le (L : Bool → ι → E) (r : Bool → ℝ)
    (hr : ∀ b, 0 ≤ r b)
    (hrow : ∀ b i, ∑ j, Real.sqrt ‖L b i * L (!b) j‖ ≤ r b)
    (n : ℕ) (b : Bool) (i : ι) :
    pathSum n (chain L b i) ≤ rows r b n := by
  induction n generalizing b i with
  | zero => exact le_rfl
  | succ n ih =>
    simp only [pathSum, chain, pathSum_mul_left, rows]
    calc
      _ ≤ ∑ j, Real.sqrt ‖L b i * L (!b) j‖ * rows r (!b) n :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih _ _) (Real.sqrt_nonneg _)
      _ = (∑ j, Real.sqrt ‖L b i * L (!b) j‖) * rows r (!b) n :=
        (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right (hrow b i) (rows_nonneg r hr _ _)

lemma norm_pathSum_word_le [NormOneClass E] (L : Bool → ι → E) (r : Bool → ℝ)
    (hr : ∀ b, 0 ≤ r b) (C : ℝ) (hC : 0 ≤ C)
    (hL : ∀ b i, ‖L b i‖ ≤ C)
    (hrow : ∀ b i, ∑ j, Real.sqrt ‖L b i * L (!b) j‖ ≤ r b)
    (n : ℕ) (b : Bool) :
    ‖pathSum (n + 1) (word L b)‖ ≤ Fintype.card ι * C * rows r b n := by
  apply (norm_pathSum_le _ _).trans
  simp only [pathSum]
  calc
    _ ≤ ∑ i, C * rows r b n := by
      apply Finset.sum_le_sum
      intro i _
      exact (pathSum_mono n (fun l => norm_word_le_chain L C hC hL b i l)).trans
        (by
          rw [pathSum_mul_left]
          exact mul_le_mul_of_nonneg_left (pathSum_chain_le L r hr hrow n b i) hC)
    _ = _ := by simp [mul_assoc]

lemma pathSum_word_succ (L : Bool → ι → E) (n : ℕ) (b : Bool) :
    pathSum (n + 1) (word L b) = (∑ i, L b i) * pathSum n (word L (!b)) := by
  simp only [pathSum, word, pathSum_mul_left, Finset.sum_mul]

lemma pathSum_word_even (L : Bool → ι → E) (m : ℕ) (b : Bool) :
    pathSum (2 * m) (word L b) = ((∑ i, L b i) * (∑ i, L (!b) i)) ^ m := by
  induction m with
  | zero => simp [pathSum, word]
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
      pathSum_word_succ, pathSum_word_succ]
    simp only [Bool.not_not, ih, pow_succ', mul_assoc]

lemma rows_even (r : Bool → ℝ) (m : ℕ) (b : Bool) :
    rows r b (2 * m) = (r b * r (!b)) ^ m := by
  induction m with
  | zero => simp [rows]
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega]
    simp only [rows, Bool.not_not, ih, pow_succ', mul_assoc]

end Words


section CStar
variable {ι E : Type*} [Fintype ι] [NormedRing E] [StarRing E] [CStarRing E]

/-- The real power comparison used to remove the number of summands. -/
lemma le_of_dyadic_powers_le (x c N : ℝ) (hc : 0 ≤ c)
    (h : ∀ k : ℕ, x ^ (2 ^ k) ≤ N * c ^ (2 ^ k)) : x ≤ c := by
  by_cases hc0 : c = 0
  · have := h 0
    simpa [hc0] using this
  have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
  by_contra hnot
  have hq : 1 < x / c := (one_lt_div hcpos).mpr (lt_of_not_ge hnot)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt N hq
  have hupper : (x / c) ^ (2 ^ k) ≤ N := by
    rw [div_pow, div_le_iff₀ (pow_pos hcpos _)]
    exact h k
  exact (not_lt_of_ge ((pow_le_pow_right₀ hq.le k.lt_two_pow_self.le).trans hupper)) hk

/-- Cotlar's finite estimate in a C⋆-ring. No nonzero-space assumption is needed. -/
theorem norm_sum_le_sqrt_row_bounds (T : ι → E) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ i, ∑ j, Real.sqrt ‖star (T i) * T j‖ ≤ A)
    (hb : ∀ i, ∑ j, Real.sqrt ‖T i * star (T j)‖ ≤ B) :
    ‖∑ i, T i‖ ≤ Real.sqrt (A * B) := by
  classical
  cases subsingleton_or_nontrivial E with
  | inl hE =>
    let := hE
    simp only [Subsingleton.elim (∑ i, T i) 0, norm_zero]
    exact Real.sqrt_nonneg _
  | inr hE =>
    let := hE
    let L : Bool → ι → E := fun b i => if b then star (T i) else T i
    let r : Bool → ℝ := fun b => if b then A else B
    have hr : ∀ b, 0 ≤ r b := by intro b; cases b <;> assumption
    have hnorm (i : ι) : ‖T i‖ ≤ B := by
      have hd : Real.sqrt ‖T i * star (T i)‖ ≤
          ∑ j, Real.sqrt ‖T i * star (T j)‖ :=
        Finset.single_le_sum (f := fun j => Real.sqrt ‖T i * star (T j)‖)
          (fun j _ => Real.sqrt_nonneg _) (Finset.mem_univ i)
      simpa only [CStarRing.norm_self_mul_star, ← pow_two,
        Real.sqrt_sq (norm_nonneg _)] using hd.trans (hb i)
    have hL : ∀ b i, ‖L b i‖ ≤ B := by
      intro b i
      cases b <;> simpa [L] using hnorm i
    have hrow : ∀ b i, ∑ j, Real.sqrt ‖L b i * L (!b) j‖ ≤ r b := by
      intro b i
      cases b
      · simpa [L, r] using hb i
      · simpa [L, r] using ha i
    have hpower (m : ℕ) (hm : m ≠ 0) :
        ‖(star (∑ i, T i) * (∑ i, T i)) ^ m‖ ≤ Fintype.card ι * (A * B) ^ m := by
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      have h := norm_pathSum_word_le L r hr B hB hL hrow (2 * n + 1) true
      have hw : pathSum ((2 * n + 1) + 1) (word L true) =
          (star (∑ i, T i) * (∑ i, T i)) ^ (n + 1) := by
        rw [show (2 * n + 1) + 1 = 2 * (n + 1) by omega, pathSum_word_even]
        simp [L]
      have hrows : rows r true (2 * n + 1) = A * (B * A) ^ n := by
        rw [rows, rows_even]
        rfl
      rw [hw, hrows] at h
      convert h using 1
      rw [pow_succ, mul_comm B A]
      ring
    apply Real.le_sqrt (norm_nonneg _) (mul_nonneg hA hB) |>.mpr
    apply le_of_dyadic_powers_le _ _ (Fintype.card ι) (mul_nonneg hA hB)
    intro k
    have h := hpower (2 ^ k) (by positivity)
    rw [(IsSelfAdjoint.star_mul_self (∑ i, T i)).norm_pow_two_pow k,
      CStarRing.norm_star_mul_self, ← pow_two] at h
    exact h

end CStar

universe u v w

/-- Uniform finite row bounds imply the Cotlar–Stein operator-norm estimate. -/
theorem cotlar_stein_row_estimate : Spec.RowEstimate.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ _ T A B hA hB ha hb
  apply norm_sum_le_sqrt_row_bounds T A B hA hB
  · simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using ha
  · simpa only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.mul_def] using hb

/-- The finite family estimate with the exact two maximum row sums. -/
theorem cotlar_stein_finite : Spec.FiniteEstimate.{u, v, w} := by
  intro 𝕜 H ι _ _ _ _ _ T
  apply cotlar_stein_row_estimate 𝕜 H ι T (Spec.leftBound T) (Spec.rightBound T)
    (by positivity) (by positivity)
  · intro i
    have h := Finset.le_sup (f := fun i => ∑ j, NNReal.sqrt ‖(T i).adjoint.comp (T j)‖₊)
      (Finset.mem_univ i)
    have hc := (NNReal.coe_le_coe).mpr h
    simpa only [Spec.leftBound, NNReal.coe_sum, Real.coe_sqrt, coe_nnnorm] using hc
  · intro i
    have h := Finset.le_sup (f := fun i => ∑ j, NNReal.sqrt ‖(T i).comp (T j).adjoint‖₊)
      (Finset.mem_univ i)
    have hc := (NNReal.coe_le_coe).mpr h
    simpa only [Spec.rightBound, NNReal.coe_sum, Real.coe_sqrt, coe_nnnorm] using hc

end ExpandedFA.Geometry.CotlarSteinFinite
