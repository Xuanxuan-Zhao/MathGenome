import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SchauderHatBasis
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C15SubsetProjections
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open Filter Topology
open scoped BigOperators
universe u
namespace ExpandedFA.P1.SchauderHatBasis
open Spec

variable {𝕜 : Type u} [RCLike 𝕜]

@[simp] theorem hat_midpoint (n : ℕ) (k : Fin (2 ^ n)) :
    hat 𝕜 n k (midpoint n k) = 1 := by
  change ((max 0 (1 - |(2 : ℝ) ^ (n + 1) *
    (((2 * k.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) -
      (2 * (k.val : ℝ) + 1)|) : ℝ) : 𝕜) = 1
  simp [Nat.cast_add, Nat.cast_mul, mul_div_cancel₀]

theorem hat_nonnegative (n : ℕ) (k : Fin (2 ^ n)) (t : Interval) :
    0 ≤ max 0 (1 - |(2 : ℝ) ^ (n + 1) * (t : ℝ) - (2 * (k.val : ℝ) + 1)|) :=
  le_max_left _ _

theorem hat_le_one (n : ℕ) (k : Fin (2 ^ n)) (t : Interval) :
    max 0 (1 - |(2 : ℝ) ^ (n + 1) * (t : ℝ) - (2 * (k.val : ℝ) + 1)|) ≤ 1 := by
  exact max_le (by norm_num) (by linarith [abs_nonneg ((2 : ℝ) ^ (n + 1) * (t : ℝ) - (2 * (k.val : ℝ) + 1))])

@[simp] theorem norm_hat (n : ℕ) (k : Fin (2 ^ n)) : ‖hat 𝕜 n k‖ = 1 := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro t
    change ‖((max 0 (1 - |(2 : ℝ) ^ (n + 1) * (t : ℝ) -
      (2 * (k.val : ℝ) + 1)|) : ℝ) : 𝕜)‖ ≤ 1
    rw [RCLike.norm_ofReal, abs_of_nonneg (hat_nonnegative n k t)]
    exact hat_le_one n k t
  · simpa only [hat_midpoint, norm_one] using
      (hat 𝕜 n k).norm_coe_le_norm (midpoint n k)

theorem normalized_hats : Expected.NormalizedHats := by
  intro 𝕜 _ n k
  exact ⟨hat_midpoint n k, norm_hat n k⟩

@[simp] theorem hat_ne_zero (n : ℕ) (k : Fin (2 ^ n)) : hat 𝕜 n k ≠ 0 := by
  intro h
  have := norm_hat (𝕜 := 𝕜) n k
  rw [h, norm_zero] at this
  norm_num at this

@[simp] theorem linearFunction_one : linearFunction 𝕜 1 = 1 := by
  simp [linearFunction]

theorem basis_nonzero : Expected.NonzeroBasis := by
  intro 𝕜 _ i
  rcases i with _ | (_ | j)
  · exact one_ne_zero
  · intro h
    have hh := congrArg (fun f : FunctionSpace 𝕜 => f 1) h
    exact one_ne_zero (by simpa only [basis, linearFunction_one, ContinuousMap.zero_apply] using hh)
  · exact hat_ne_zero _ _

/-- The coordinate maps are explicit finite linear combinations of evaluations. -/
def coefficientCLM (i : ℕ) : FunctionSpace 𝕜 →L[𝕜] 𝕜 :=
  match i with
  | 0 => ContinuousMap.evalCLM 𝕜 0
  | 1 => ContinuousMap.evalCLM 𝕜 1 -
      ContinuousMap.evalCLM 𝕜 0
  | j + 2 =>
      ContinuousMap.evalCLM 𝕜 (midpoint (hatIndex j).1 (hatIndex j).2) -
        (2 : 𝕜)⁻¹ • (ContinuousMap.evalCLM 𝕜 (leftPoint (hatIndex j).1 (hatIndex j).2) +
          ContinuousMap.evalCLM 𝕜 (rightPoint (hatIndex j).1 (hatIndex j).2))

@[simp] theorem coefficientCLM_apply (i : ℕ) (f : FunctionSpace 𝕜) :
    coefficientCLM i f = coefficients f i := by
  rcases i with _ | (_ | j)
  · rfl
  · rfl
  · simp [coefficientCLM, coefficients, hatCoefficient, div_eq_mul_inv, mul_comm, mul_add]

theorem coefficient_continuity : Expected.CoefficientContinuity := by
  intro 𝕜 _ i
  exact ⟨coefficientCLM i, coefficientCLM_apply i⟩

/-- The explicit partial sums are continuous scalar-linear operators. -/
def partialSumCLM (N : ℕ) : FunctionSpace 𝕜 →L[𝕜] FunctionSpace 𝕜 :=
  ∑ i ∈ Finset.range N, (coefficientCLM i).smulRight (basis 𝕜 i)

@[simp] theorem partialSumCLM_apply (N : ℕ) (f : FunctionSpace 𝕜) :
    partialSumCLM N f = partialSum N f := by
  simp [partialSumCLM, partialSum, C15Basis.Spec.orderedPartialSum]

@[simp] theorem partialSum_zero (f : FunctionSpace 𝕜) : partialSum 0 f = 0 := by
  simp [partialSum, C15Basis.Spec.orderedPartialSum]

@[simp] theorem partialSum_one (f : FunctionSpace 𝕜) :
    partialSum 1 f = ContinuousMap.const Interval (coefficients f 0) := by
  ext t
  simp [partialSum, C15Basis.Spec.orderedPartialSum, basis]

/-- Multiplication by the scale puts the three defining knots at even,
odd, even integers. These identities avoid divisions in geometric proofs. -/
theorem scaled_left (n : ℕ) (k : Fin (2 ^ n)) :
    (2 : ℝ) ^ (n + 1) * (leftPoint n k : ℝ) = 2 * (k.val : ℝ) := by
  change (2 : ℝ) ^ (n + 1) * ((k.val : ℝ) / (2 : ℝ) ^ n) = _
  rw [pow_succ]
  field_simp

theorem scaled_midpoint (n : ℕ) (k : Fin (2 ^ n)) :
    (2 : ℝ) ^ (n + 1) * (midpoint n k : ℝ) = 2 * (k.val : ℝ) + 1 := by
  change (2 : ℝ) ^ (n + 1) * (((2 * k.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (n + 1)) = _
  push_cast
  field_simp

theorem scaled_right (n : ℕ) (k : Fin (2 ^ n)) :
    (2 : ℝ) ^ (n + 1) * (rightPoint n k : ℝ) = 2 * (k.val : ℝ) + 2 := by
  change (2 : ℝ) ^ (n + 1) * (((k.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n) = _
  push_cast
  rw [pow_succ]
  field_simp

theorem left_lt_midpoint (n : ℕ) (k : Fin (2 ^ n)) :
    (leftPoint n k : ℝ) < midpoint n k := by
  have h := scaled_left n k
  have h' := scaled_midpoint n k
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (n + 1)]

theorem midpoint_lt_right (n : ℕ) (k : Fin (2 ^ n)) :
    (midpoint n k : ℝ) < rightPoint n k := by
  have h := scaled_midpoint n k
  have h' := scaled_right n k
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (n + 1)]

/-- The hat is zero to the left of its support, including the endpoint. -/
theorem hat_eq_zero_of_le_left (n : ℕ) (k : Fin (2 ^ n)) (t : Interval)
    (ht : (t : ℝ) ≤ leftPoint n k) : hat 𝕜 n k t = 0 := by
  have hscale := mul_le_mul_of_nonneg_left ht
    (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1))
  rw [scaled_left] at hscale
  change ((max 0 (1 - |(2 : ℝ) ^ (n + 1) * (t : ℝ) -
    (2 * (k.val : ℝ) + 1)|) : ℝ) : 𝕜) = 0
  rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
  exact RCLike.ofReal_zero

/-- The hat is zero to the right of its support, including the endpoint. -/
theorem hat_eq_zero_of_right_le (n : ℕ) (k : Fin (2 ^ n)) (t : Interval)
    (ht : (rightPoint n k : ℝ) ≤ t) : hat 𝕜 n k t = 0 := by
  have hscale := mul_le_mul_of_nonneg_left ht
    (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1))
  rw [scaled_right] at hscale
  change ((max 0 (1 - |(2 : ℝ) ^ (n + 1) * (t : ℝ) -
    (2 * (k.val : ℝ) + 1)|) : ℝ) : 𝕜) = 0
  rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
  exact RCLike.ofReal_zero

/-- The ascending affine branch of the tent. -/
theorem hat_left_half (n : ℕ) (k : Fin (2 ^ n)) (t : Interval)
    (hl : (leftPoint n k : ℝ) ≤ t) (hm : (t : ℝ) ≤ midpoint n k) :
    hat 𝕜 n k t = (((2 : ℝ) ^ (n + 1) * (t : ℝ) - 2 * (k.val : ℝ) : ℝ) : 𝕜) := by
  have hscale := mul_le_mul_of_nonneg_left hl
    (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1))
  have hscale' := mul_le_mul_of_nonneg_left hm
    (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1))
  rw [scaled_left] at hscale
  rw [scaled_midpoint] at hscale'
  change ((max 0 (1 - |(2 : ℝ) ^ (n + 1) * (t : ℝ) -
    (2 * (k.val : ℝ) + 1)|) : ℝ) : 𝕜) = _
  rw [abs_of_nonpos (by linarith), max_eq_right (by linarith)]
  congr 1
  ring

/-- The descending affine branch of the tent. -/
theorem hat_right_half (n : ℕ) (k : Fin (2 ^ n)) (t : Interval)
    (hm : (midpoint n k : ℝ) ≤ t) (hr : (t : ℝ) ≤ rightPoint n k) :
    hat 𝕜 n k t = ((2 * (k.val : ℝ) + 2 - (2 : ℝ) ^ (n + 1) * (t : ℝ) : ℝ) : 𝕜) := by
  have hscale := mul_le_mul_of_nonneg_left hm
    (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1))
  have hscale' := mul_le_mul_of_nonneg_left hr
    (by positivity : (0 : ℝ) ≤ 2 ^ (n + 1))
  rw [scaled_midpoint] at hscale
  rw [scaled_right] at hscale'
  change ((max 0 (1 - |(2 : ℝ) ^ (n + 1) * (t : ℝ) -
    (2 * (k.val : ℝ) + 1)|) : ℝ) : 𝕜) = _
  rw [abs_of_nonneg (by linarith), max_eq_right (by linarith)]
  congr 1
  ring

@[simp] theorem hat_zero (n : ℕ) (k : Fin (2 ^ n)) : hat 𝕜 n k 0 = 0 := by
  apply hat_eq_zero_of_le_left
  exact (leftPoint n k).property.1

@[simp] theorem hat_one (n : ℕ) (k : Fin (2 ^ n)) : hat 𝕜 n k 1 = 0 := by
  apply hat_eq_zero_of_right_le
  exact (rightPoint n k).property.2

/-- Each dyadic level is enumerated once and in increasing spatial order. -/
theorem hatIndex_encode (n : ℕ) (k : Fin (2 ^ n)) :
    hatIndex (2 ^ n + k.val - 1) = ⟨n, k⟩ := by
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  have hi : 2 ^ n + k.val - 1 + 1 = 2 ^ n + k.val := by omega
  have hl : Nat.log 2 (2 ^ n + k.val) = n := by
    apply Nat.log_eq_of_pow_le_of_lt_pow (Nat.le_add_right _ _)
    rw [pow_succ]
    omega
  dsimp only [hatIndex]
  simp_rw [hi, hl]
  simp only [Nat.add_sub_cancel_left]
  congr 1
  · rw [hi, hl]
  · apply (Fin.heq_ext_iff (congrArg (fun m => 2 ^ m) (hi ▸ hl))).mpr
    rfl

/-- Conversely, decoding and then encoding recovers the index. -/
theorem hatIndex_decode (j : ℕ) :
    2 ^ (hatIndex j).1 + (hatIndex j).2.val - 1 = j := by
  have hp : 2 ^ Nat.log 2 (j + 1) ≤ j + 1 := Nat.pow_log_le_self 2 (by omega)
  change 2 ^ Nat.log 2 (j + 1) + (j + 1 - 2 ^ Nat.log 2 (j + 1)) - 1 = j
  omega

@[simp] theorem basis_encode (n : ℕ) (k : Fin (2 ^ n)) :
    basis 𝕜 (2 ^ n + k.val + 1) = hat 𝕜 n k := by
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  have hi : 2 ^ n + k.val + 1 = (2 ^ n + k.val - 1) + 2 := by omega
  rw [hi, basis, hatIndex_encode]

@[simp] theorem coefficients_encode (n : ℕ) (k : Fin (2 ^ n)) (f : FunctionSpace 𝕜) :
    coefficients f (2 ^ n + k.val + 1) = hatCoefficient n k f := by
  have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
  have hi : 2 ^ n + k.val + 1 = (2 ^ n + k.val - 1) + 2 := by omega
  rw [hi, coefficients, hatIndex_encode]

/-- Fine-level hats vanish at every knot of an earlier completed dyadic grid. -/
theorem hat_dyadicPoint_eq_zero (m r q : ℕ) (hq : q ≤ 2 ^ r)
    (hr : r ≤ m) (k : Fin (2 ^ m)) :
    hat 𝕜 m k (dyadicPoint r q hq) = 0 := by
  have hp : (2 : ℝ) ^ r ≠ 0 := by positivity
  have hscale : (2 : ℝ) ^ (m + 1) * (dyadicPoint r q hq : ℝ) =
      2 * ((2 ^ (m - r) * q : ℕ) : ℝ) := by
    change (2 : ℝ) ^ (m + 1) * ((q : ℝ) / (2 : ℝ) ^ r) = _
    push_cast
    rw [pow_succ, ← pow_sub_mul_pow (2 : ℝ) hr]
    field_simp
  change ((max 0 (1 - |(2 : ℝ) ^ (m + 1) * (dyadicPoint r q hq : ℝ) -
    (2 * (k.val : ℝ) + 1)|) : ℝ) : 𝕜) = 0
  rw [hscale]
  by_cases h : 2 ^ (m - r) * q ≤ k.val
  · have hc : (((2 ^ (m - r) * q : ℕ) : ℝ)) ≤ k.val := by exact_mod_cast h
    rw [abs_of_nonpos (by linarith), max_eq_left (by linarith)]
    exact RCLike.ofReal_zero
  · have hc : (k.val : ℝ) + 1 ≤ ((2 ^ (m - r) * q : ℕ) : ℝ) := by
      exact_mod_cast (show k.val + 1 ≤ 2 ^ (m - r) * q by omega)
    rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
    exact RCLike.ofReal_zero

/-- Collocation points in the same order as the basis. -/
def samplePoint : ℕ → Interval
  | 0 => 0
  | 1 => 1
  | j + 2 => midpoint (hatIndex j).1 (hatIndex j).2

@[simp] theorem basis_samplePoint (i : ℕ) : basis 𝕜 i (samplePoint i) = 1 := by
  rcases i with _ | (_ | j)
  · simp [basis, samplePoint]
  · simp [basis, samplePoint]
  · exact hat_midpoint _ _

/-- The collocation matrix is lower triangular, including between incomplete
levels. This suffices for uniqueness of arbitrary convergent expansions. -/
theorem basis_samplePoint_above {i j : ℕ} (hij : i < j) :
    basis 𝕜 j (samplePoint i) = 0 := by
  rcases i with _ | (_ | a)
  · rcases j with _ | (_ | b)
    · omega
    · simp [basis, samplePoint, linearFunction]
    · exact hat_zero _ _
  · rcases j with _ | (_ | b)
    · omega
    · omega
    · exact hat_one _ _
  · rcases j with _ | (_ | b)
    · omega
    · omega
    · change hat 𝕜 (hatIndex b).1 (hatIndex b).2
        (midpoint (hatIndex a).1 (hatIndex a).2) = 0
      have hab : a < b := by omega
      have hl : (hatIndex a).1 ≤ (hatIndex b).1 := by
        change Nat.log 2 (a + 1) ≤ Nat.log 2 (b + 1)
        exact Nat.log_mono_right (by omega)
      rcases lt_or_eq_of_le hl with hl | hl
      · exact hat_dyadicPoint_eq_zero _ _ _ _ (by omega) _
      · apply hat_eq_zero_of_le_left
        have ha := scaled_midpoint (hatIndex a).1 (hatIndex a).2
        have hb := scaled_left (hatIndex b).1 (hatIndex b).2
        have hda := hatIndex_decode a
        have hdb := hatIndex_decode b
        have hk : (hatIndex a).2.val < (hatIndex b).2.val := by
          have hpow := congrArg (fun n => (2 : ℕ) ^ n) hl
          omega
        have hkr : ((hatIndex a).2.val : ℝ) + 1 ≤ (hatIndex b).2.val := by
          exact_mod_cast hk
        rw [congrArg (fun n => (2 : ℝ) ^ (n + 1)) hl] at ha
        nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) ((hatIndex b).1 + 1)]

/-- Evaluation at a collocation point stabilizes after its corresponding term. -/
theorem orderedPartialSum_samplePoint (a : ℕ → 𝕜) (i N : ℕ) (hN : i + 1 ≤ N) :
    C15Basis.Spec.orderedPartialSum (basis 𝕜) a N (samplePoint i) =
      C15Basis.Spec.orderedPartialSum (basis 𝕜) a (i + 1) (samplePoint i) := by
  classical
  simp only [C15Basis.Spec.orderedPartialSum, ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  symm
  apply Finset.sum_subset (Finset.range_mono hN)
  intro j _ hj
  have hij : i < j := by simpa using hj
  rw [basis_samplePoint_above hij, smul_zero]

/-- Every ordered expansion has the same finite collocation data as its limit. -/
theorem expansion_samplePoint {f : FunctionSpace 𝕜} {a : ℕ → 𝕜}
    (ha : Tendsto (C15Basis.Spec.orderedPartialSum (basis 𝕜) a) atTop (𝓝 f)) (i : ℕ) :
    C15Basis.Spec.orderedPartialSum (basis 𝕜) a (i + 1) (samplePoint i) = f (samplePoint i) := by
  have heval := ((ContinuousMap.evalCLM 𝕜 (samplePoint i)).continuous.tendsto f).comp ha
  apply tendsto_nhds_unique _ heval
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop (i + 1)] with N hN
  exact (orderedPartialSum_samplePoint a i N hN).symm

/-- Uniqueness does not presuppose existence or the interpolation identity. -/
theorem expansion_unique {f : FunctionSpace 𝕜} {a b : ℕ → 𝕜}
    (ha : Tendsto (C15Basis.Spec.orderedPartialSum (basis 𝕜) a) atTop (𝓝 f))
    (hb : Tendsto (C15Basis.Spec.orderedPartialSum (basis 𝕜) b) atTop (𝓝 f)) : a = b := by
  funext i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    have heq := (expansion_samplePoint ha i).trans (expansion_samplePoint hb i).symm
    simp only [C15Basis.Spec.orderedPartialSum, Finset.sum_range_succ,
      ContinuousMap.add_apply, ContinuousMap.smul_apply, basis_samplePoint, smul_eq_mul, mul_one] at heq
    have hprefix : (∑ j ∈ Finset.range i, a j • basis 𝕜 j) =
        (∑ j ∈ Finset.range i, b j • basis 𝕜 j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih j (Finset.mem_range.mp hj)]
    rw [hprefix] at heq
    exact add_left_cancel heq

/-- The two endpoints belong to every interpolating partition. -/
theorem endpoints_mem_knots (N : ℕ) :
    (0 : Interval) ∈ knots N ∧
    (1 : Interval) ∈ knots N := by
  constructor <;> simp [knots]

theorem knots_mono : Monotone knots := by
  intro N M hNM
  unfold knots
  apply Finset.union_subset_union_right
  exact Finset.image_subset_image (Finset.range_mono (Nat.sub_le_sub_right hNM 2))

/-- Every point of the nth dyadic grid is already a knot after all hats
of levels below n have been included. -/
theorem dyadicPoint_mem_knots (n q : ℕ) (hq : q ≤ 2 ^ n) :
    dyadicPoint n q hq ∈ knots (2 ^ n + 1) := by
  classical
  induction n generalizing q with
  | zero =>
    have hq' : q = 0 ∨ q = 1 := by have : q ≤ 1 := hq; omega
    rcases hq' with rfl | rfl
    · have he : dyadicPoint 0 0 hq = (0 : Interval) := by apply Subtype.ext; norm_num [dyadicPoint]
      rw [he]
      exact (endpoints_mem_knots _).1
    · have he : dyadicPoint 0 1 hq = (1 : Interval) := by apply Subtype.ext; norm_num [dyadicPoint]
      rw [he]
      exact (endpoints_mem_knots _).2
  | succ n ih =>
    have hp : 0 < (2 : ℕ) ^ n := pow_pos (by decide) _
    obtain ⟨r, hqr | hqr⟩ := Nat.even_or_odd' q
    · have hr : r ≤ 2 ^ n := by rw [hqr, pow_succ] at hq; omega
      have he : dyadicPoint (n + 1) q hq = dyadicPoint n r hr := by
        apply Subtype.ext
        change (q : ℝ) / (2 : ℝ) ^ (n + 1) = (r : ℝ) / (2 : ℝ) ^ n
        rw [hqr, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
        field_simp
      rw [he]
      apply knots_mono (show 2 ^ n + 1 ≤ 2 ^ (n + 1) + 1 by rw [pow_succ]; omega)
      exact ih r hr
    · have hr : r < 2 ^ n := by rw [hqr, pow_succ] at hq; omega
      have he : dyadicPoint (n + 1) q hq = midpoint n ⟨r, hr⟩ := by
        apply Subtype.ext
        simp only [Spec.midpoint, dyadicPoint, hqr]
      rw [he]
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨2 ^ n + r - 1, Finset.mem_range.mpr ?_, ?_⟩
      · rw [pow_succ]
        omega
      · rw [hatIndex_encode n ⟨r, hr⟩]

/-- Adjacent knots in a partition containing a completed grid have at most
that grid's mesh, even when the newest dyadic level is incomplete. -/
theorem adjacent_gap_le {N n : ℕ} (hN : 2 ^ n + 1 ≤ N) {a b : Interval}
    (hab : (a : ℝ) < b)
    (hadj : ∀ c ∈ knots N, ¬ ((a : ℝ) < c ∧ (c : ℝ) < b)) :
    (b : ℝ) - a ≤ 1 / (2 : ℝ) ^ n := by
  classical
  by_contra hgap
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  have ha0 : 0 ≤ (a : ℝ) * 2 ^ n := mul_nonneg a.property.1 hp.le
  have ha1 : (a : ℝ) < 1 := hab.trans_le b.property.2
  let q : ℕ := ⌊(a : ℝ) * (2 : ℝ) ^ n⌋₊ + 1
  have hq : q ≤ 2 ^ n := by
    have hf : ⌊(a : ℝ) * (2 : ℝ) ^ n⌋₊ < 2 ^ n := by
      apply (Nat.floor_lt ha0).mpr
      push_cast
      nlinarith
    omega
  have hc : dyadicPoint n q hq ∈ knots N :=
    knots_mono hN (dyadicPoint_mem_knots n q hq)
  have haq : (a : ℝ) < dyadicPoint n q hq := by
    change (a : ℝ) < (q : ℝ) / (2 : ℝ) ^ n
    apply (lt_div_iff₀ hp).mpr
    simpa only [q, Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one ((a : ℝ) * (2 : ℝ) ^ n)
  have hqb : (dyadicPoint n q hq : ℝ) < b := by
    change (q : ℝ) / (2 : ℝ) ^ n < (b : ℝ)
    apply (div_lt_iff₀ hp).mpr
    have hf := Nat.floor_le ha0
    have hgap' : 1 < ((b : ℝ) - a) * (2 : ℝ) ^ n := by
      exact (div_lt_iff₀ hp).mp (lt_of_not_ge hgap)
    dsimp only [q]
    push_cast
    nlinarith
  exact hadj _ hc ⟨haq, hqb⟩

/-- A point outside a finite partition with both endpoints lies between two
consecutive knots. -/
theorem exists_adjacent_knots (N : ℕ) (t : Interval) (ht : t ∉ knots N) :
    ∃ a ∈ knots N, ∃ b ∈ knots N,
      (a : ℝ) < t ∧ (t : ℝ) < b ∧
      ∀ c ∈ knots N, ¬ ((a : ℝ) < c ∧ (c : ℝ) < b) := by
  classical
  obtain ⟨h0, h1⟩ := endpoints_mem_knots N
  have ht0 : (0 : Interval) < t := by
    apply lt_of_le_of_ne
    · exact t.property.1
    · intro he
      exact ht (he ▸ h0)
  have ht1 : t < (1 : Interval) := by
    apply lt_of_le_of_ne
    · exact t.property.2
    · intro he
      exact ht (he ▸ h1)
  obtain ⟨a, ha, hat, hmax⟩ := Finset.exists_next_left ⟨0, h0, ht0⟩
  obtain ⟨b, hb, htb, hmin⟩ := Finset.exists_next_right ⟨1, h1, ht1⟩
  refine ⟨a, ha, b, hb, hat, htb, ?_⟩
  intro c hc hacb
  rcases lt_trichotomy c t with hct | hct | hct
  · exact (not_lt_of_ge (hmax c hc hct)) hacb.1
  · exact ht (hct ▸ hc)
  · exact (not_lt_of_ge (hmin c hc hct)) hacb.2

/-- Affine interpolation of two values is a convex combination on the interval. -/
theorem norm_affine_le {a b t M : ℝ} (hab : a < b) (hat : a ≤ t) (htb : t ≤ b)
    {x y : 𝕜} (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) :
    ‖((b - t) / (b - a)) • x + ((t - a) / (b - a)) • y‖ ≤ M := by
  have hd : 0 < b - a := sub_pos.mpr hab
  have hα : 0 ≤ (b - t) / (b - a) := div_nonneg (sub_nonneg.mpr htb) hd.le
  have hβ : 0 ≤ (t - a) / (b - a) := div_nonneg (sub_nonneg.mpr hat) hd.le
  have hs : (b - t) / (b - a) + (t - a) / (b - a) = 1 := by
    rw [← add_div]
    have he : b - t + (t - a) = b - a := by ring
    rw [he, div_self hd.ne']
  calc
    _ ≤ ‖((b - t) / (b - a)) • x‖ + ‖((t - a) / (b - a)) • y‖ := norm_add_le _ _
    _ = (b - t) / (b - a) * ‖x‖ + (t - a) / (b - a) * ‖y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg hα, abs_of_nonneg hβ]
    _ ≤ (b - t) / (b - a) * M + (t - a) / (b - a) * M :=
      add_le_add (mul_le_mul_of_nonneg_left hx hα) (mul_le_mul_of_nonneg_left hy hβ)
    _ = M := by rw [← add_mul, hs, one_mul]

/-- Once the exact interpolation identity is established, contractivity follows
also for every incomplete dyadic level. -/
theorem interpolates_norm_le {N : ℕ} {f g : FunctionSpace 𝕜}
    (h : Interpolates N f g) : ‖g‖ ≤ ‖f‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
  intro t
  by_cases ht : t ∈ knots N
  · rw [h.1 t ht]
    exact f.norm_coe_le_norm t
  · obtain ⟨a, ha, b, hb, hat, htb, hadj⟩ := exists_adjacent_knots N t ht
    rw [h.2 a ha b hb (hat.trans htb) hadj t hat.le htb.le]
    exact norm_affine_le (hat.trans htb) hat.le htb.le
      (f.norm_coe_le_norm a) (f.norm_coe_le_norm b)

/-- A convenient interval-affinity predicate, independent of the data f. -/
def AffineOn (a b : Interval) (g : FunctionSpace 𝕜) : Prop :=
  ∀ t : Interval, (a : ℝ) ≤ t → (t : ℝ) ≤ b →
    g t = (((b : ℝ) - t) / ((b : ℝ) - a)) • g a +
      (((t : ℝ) - a) / ((b : ℝ) - a)) • g b

/-- The tent is strictly positive on its open support; zero values therefore
lie outside that open interval. -/
theorem outside_of_hat_eq_zero (n : ℕ) (k : Fin (2 ^ n)) (t : Interval)
    (hz : hat 𝕜 n k t = 0) :
    ¬ ((leftPoint n k : ℝ) < t ∧ (t : ℝ) < rightPoint n k) := by
  intro ht
  have hl := mul_lt_mul_of_pos_left ht.1 (by positivity : (0 : ℝ) < 2 ^ (n + 1))
  have hr := mul_lt_mul_of_pos_left ht.2 (by positivity : (0 : ℝ) < 2 ^ (n + 1))
  rw [scaled_left] at hl
  rw [scaled_right] at hr
  have hpos : 0 < max 0 (1 - |(2 : ℝ) ^ (n + 1) * (t : ℝ) -
      (2 * (k.val : ℝ) + 1)|) := by
    apply lt_max_of_lt_right
    have habs : |(2 : ℝ) ^ (n + 1) * (t : ℝ) - (2 * (k.val : ℝ) + 1)| < 1 :=
      abs_lt.mpr ⟨by linarith, by linarith⟩
    linarith
  have he : max 0 (1 - |(2 : ℝ) ^ (n + 1) * (t : ℝ) -
      (2 * (k.val : ℝ) + 1)|) = 0 := by
    have := congrArg RCLike.re hz
    simpa only [hat, ContinuousMap.coe_mk, RCLike.ofReal_re, map_zero] using this
  linarith

/-- An affine real function, included in either scalar field, interpolates
between any two of its values. -/
theorem real_affine_formula (c d a b t : ℝ) (hab : a < b) :
    ((c * t + d : ℝ) : 𝕜) = ((b - t) / (b - a)) • ((c * a + d : ℝ) : 𝕜) +
      ((t - a) / (b - a)) • ((c * b + d : ℝ) : 𝕜) := by
  rw [RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul,
    ← RCLike.ofReal_mul, ← RCLike.ofReal_mul, ← RCLike.ofReal_add]
  congr 1
  field_simp
  <;> ring

/-- With its three breakpoints excluded from an interval's interior, a hat
is affine throughout that interval. -/
theorem hat_affineOn {a b : Interval} (hab : (a : ℝ) < b)
    (n : ℕ) (k : Fin (2 ^ n))
    (hl : ¬ ((a : ℝ) < leftPoint n k ∧ (leftPoint n k : ℝ) < b))
    (hm : ¬ ((a : ℝ) < midpoint n k ∧ (midpoint n k : ℝ) < b))
    (hr : ¬ ((a : ℝ) < rightPoint n k ∧ (rightPoint n k : ℝ) < b)) :
    AffineOn a b (hat 𝕜 n k) := by
  intro t hat htb
  by_cases hbl : (b : ℝ) ≤ leftPoint n k
  · rw [hat_eq_zero_of_le_left n k t (htb.trans hbl),
      hat_eq_zero_of_le_left n k a (hab.le.trans hbl),
      hat_eq_zero_of_le_left n k b hbl]
    simp
  have hla : (leftPoint n k : ℝ) ≤ a := by
    by_contra h
    exact hl ⟨lt_of_not_ge h, lt_of_not_ge hbl⟩
  by_cases hbm : (b : ℝ) ≤ midpoint n k
  · rw [hat_left_half n k t (hla.trans hat) (htb.trans hbm),
      hat_left_half n k a hla (hab.le.trans hbm),
      hat_left_half n k b (hla.trans hab.le) hbm]
    simpa only [sub_eq_add_neg] using
      real_affine_formula (𝕜 := 𝕜) (2 ^ (n + 1)) (-(2 * (k.val : ℝ))) a b t hab
  have hma : (midpoint n k : ℝ) ≤ a := by
    by_contra h
    exact hm ⟨lt_of_not_ge h, lt_of_not_ge hbm⟩
  by_cases hbr : (b : ℝ) ≤ rightPoint n k
  · rw [hat_right_half n k t (hma.trans hat) (htb.trans hbr),
      hat_right_half n k a hma (hab.le.trans hbr),
      hat_right_half n k b (hma.trans hab.le) hbr]
    convert real_affine_formula (𝕜 := 𝕜) (-(2 ^ (n + 1))) (2 * (k.val : ℝ) + 2) a b t hab using 1 <;>
      congr 1 <;> ring
  have hra : (rightPoint n k : ℝ) ≤ a := by
    by_contra h
    exact hr ⟨lt_of_not_ge h, lt_of_not_ge hbr⟩
  rw [hat_eq_zero_of_right_le n k t (hra.trans hat),
    hat_eq_zero_of_right_le n k a hra,
    hat_eq_zero_of_right_le n k b (hra.trans hab.le)]
  simp

/-- All three breakpoints of an included hat have already been inserted. -/
theorem hat_breakpoints_mem {N j : ℕ} (hj : j + 2 < N) :
    leftPoint (hatIndex j).1 (hatIndex j).2 ∈ knots N ∧
    midpoint (hatIndex j).1 (hatIndex j).2 ∈ knots N ∧
    rightPoint (hatIndex j).1 (hatIndex j).2 ∈ knots N := by
  classical
  have hindex := hatIndex_decode j
  have hlevel : 2 ^ (hatIndex j).1 + 1 ≤ N := by omega
  refine ⟨knots_mono hlevel (dyadicPoint_mem_knots _ _ _), ?_,
    knots_mono hlevel (dyadicPoint_mem_knots _ _ _)⟩
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩

/-- Every included basis function is affine between adjacent partition knots. -/
theorem basis_affineOn {N i : ℕ} (hi : i < N) {a b : Interval} (hab : (a : ℝ) < b)
    (hadj : ∀ c ∈ knots N, ¬ ((a : ℝ) < c ∧ (c : ℝ) < b)) :
    AffineOn a b (basis 𝕜 i) := by
  rcases i with _ | (_ | j)
  · intro t _ _
    simpa only [basis, ContinuousMap.one_apply, zero_mul, zero_add, RCLike.ofReal_one] using
      real_affine_formula (𝕜 := 𝕜) 0 1 a b t hab
  · intro t _ _
    simpa only [basis, linearFunction, ContinuousMap.coe_mk, one_mul, add_zero] using
      real_affine_formula (𝕜 := 𝕜) 1 0 a b t hab
  · obtain ⟨hl, hm, hr⟩ := hat_breakpoints_mem hi
    exact hat_affineOn hab _ _ (hadj _ hl) (hadj _ hm) (hadj _ hr)

/-- Finite synthesis preserves interval-affinity. -/
theorem orderedPartialSum_affineOn {N : ℕ} (a : ℕ → 𝕜) {l r : Interval}
    (hlr : (l : ℝ) < r)
    (hadj : ∀ c ∈ knots N, ¬ ((l : ℝ) < c ∧ (c : ℝ) < r)) :
    AffineOn l r (C15Basis.Spec.orderedPartialSum (basis 𝕜) a N) := by
  intro t hlt htr
  simp only [C15Basis.Spec.orderedPartialSum, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    Finset.smul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [basis_affineOn (Finset.mem_range.mp hi) hlr hadj t hlt htr,
    smul_add, smul_comm (a i), smul_comm (a i)]

/-- Any knot of a prefix is one of the already retained sample points. -/
theorem knots_samplePoint {N : ℕ} (hN : 2 ≤ N) {t : Interval} (ht : t ∈ knots N) :
    ∃ i < N, t = samplePoint i := by
  classical
  rcases Finset.mem_union.mp ht with ht | ht
  · simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨j + 2, by have := Finset.mem_range.mp hj; omega, rfl⟩

/-- Thus a newly inserted hat vanishes at every old knot. -/
theorem basis_zero_on_knots {N : ℕ} (hN : 2 ≤ N) {t : Interval} (ht : t ∈ knots N) :
    basis 𝕜 N t = 0 := by
  obtain ⟨i, hi, rfl⟩ := knots_samplePoint hN ht
  exact basis_samplePoint_above hi

/-- The parent interval of the next midpoint is an old partition interval. -/
theorem next_parent_adjacent (j : ℕ) :
    ∀ c ∈ knots (j + 2), ¬ ((leftPoint (hatIndex j).1 (hatIndex j).2 : ℝ) < c ∧
      (c : ℝ) < rightPoint (hatIndex j).1 (hatIndex j).2) := by
  intro c hc
  apply outside_of_hat_eq_zero (𝕜 := ℝ)
  exact basis_zero_on_knots (by omega) hc

theorem next_parent_mem (j : ℕ) :
    leftPoint (hatIndex j).1 (hatIndex j).2 ∈ knots (j + 2) ∧
    rightPoint (hatIndex j).1 (hatIndex j).2 ∈ knots (j + 2) := by
  have hj := hatIndex_decode j
  have hlevel : 2 ^ (hatIndex j).1 + 1 ≤ j + 2 := by omega
  exact ⟨knots_mono hlevel (dyadicPoint_mem_knots _ _ _),
    knots_mono hlevel (dyadicPoint_mem_knots _ _ _)⟩

theorem midpoint_weights (n : ℕ) (k : Fin (2 ^ n)) :
    ((rightPoint n k : ℝ) - midpoint n k) /
      ((rightPoint n k : ℝ) - leftPoint n k) = 1 / 2 ∧
    ((midpoint n k : ℝ) - leftPoint n k) /
      ((rightPoint n k : ℝ) - leftPoint n k) = 1 / 2 := by
  have hl := scaled_left n k
  have hm := scaled_midpoint n k
  have hr := scaled_right n k
  have hp : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have havg : (midpoint n k : ℝ) * 2 = (leftPoint n k : ℝ) + rightPoint n k := by
    nlinarith
  have hd : (0 : ℝ) < (rightPoint n k : ℝ) - leftPoint n k :=
    sub_pos.mpr ((left_lt_midpoint n k).trans (midpoint_lt_right n k))
  constructor <;> apply (div_eq_iff hd.ne').mpr <;> linarith

@[simp] theorem partialSum_succ (N : ℕ) (f : FunctionSpace 𝕜) :
    partialSum (N + 1) f = partialSum N f + coefficients f N • basis 𝕜 N := by
  simp only [partialSum, C15Basis.Spec.orderedPartialSum, Finset.sum_range_succ]

theorem knots_succ {N : ℕ} (hN : 2 ≤ N) :
    knots (N + 1) = insert (samplePoint N) (knots N) := by
  classical
  obtain ⟨j, rfl⟩ : ∃ j, N = j + 2 := ⟨N - 2, by omega⟩
  simp [knots, samplePoint, Finset.range_add_one]

/-- Inductively the new coefficient corrects just the new midpoint, and
leaves every older interpolated value unchanged. -/
theorem partialSum_matches_knots (f : FunctionSpace 𝕜) (N : ℕ) (hN : 2 ≤ N) :
    ∀ t ∈ knots N, partialSum N f t = f t := by
  classical
  induction N, hN using Nat.le_induction with
  | base =>
    intro t ht
    have ht' : t = 0 ∨ t = 1 := by simpa [knots] using ht
    rcases ht' with rfl | rfl <;>
      simp [partialSum, C15Basis.Spec.orderedPartialSum, Finset.sum_range_succ,
        basis, coefficients, linearFunction]
  | succ N hN ih =>
    intro t ht
    rw [knots_succ hN, Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · obtain ⟨j, rfl⟩ : ∃ j, N = j + 2 := ⟨N - 2, by omega⟩
      obtain ⟨hl, hr⟩ := next_parent_mem j
      have hlt := left_lt_midpoint (hatIndex j).1 (hatIndex j).2
      have htr := midpoint_lt_right (hatIndex j).1 (hatIndex j).2
      have ha := orderedPartialSum_affineOn (coefficients f) (hlt.trans htr) (next_parent_adjacent j)
      change AffineOn _ _ (partialSum (j + 2) f) at ha
      have hmval := ha (midpoint (hatIndex j).1 (hatIndex j).2) hlt.le htr.le
      change partialSum (j + 2) f _ = _ at hmval
      rw [ih _ hl, ih _ hr, (midpoint_weights _ _).1, (midpoint_weights _ _).2] at hmval
      have havg : partialSum (j + 2) f (samplePoint (j + 2)) =
          (f (leftPoint (hatIndex j).1 (hatIndex j).2) +
            f (rightPoint (hatIndex j).1 (hatIndex j).2)) / 2 := by
        change partialSum (j + 2) f (midpoint (hatIndex j).1 (hatIndex j).2) = _
        rw [hmval, RCLike.real_smul_eq_coe_mul, RCLike.real_smul_eq_coe_mul]
        norm_num [div_eq_mul_inv, map_ofNat]
        <;> ring
      rw [partialSum_succ, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        basis_samplePoint, smul_eq_mul, mul_one, havg]
      change _ + (f (samplePoint (j + 2)) -
        (f (leftPoint (hatIndex j).1 (hatIndex j).2) +
          f (rightPoint (hatIndex j).1 (hatIndex j).2)) / 2) = _
      ring
    · rw [partialSum_succ, ContinuousMap.add_apply, ContinuousMap.smul_apply,
        basis_zero_on_knots hN ht, smul_zero, add_zero]
      exact ih t ht

/-- Exact interpolation on every successive dyadic partition, including
prefixes that stop in the middle of a level. -/
theorem interpolation : Expected.Interpolation := by
  intro 𝕜 _
  refine ⟨partialSum_zero, partialSum_one, ?_⟩
  intro N hN f
  refine ⟨partialSum_matches_knots f N hN, ?_⟩
  intro a ha b hb hab hadj t hat htb
  have hp : AffineOn a b (partialSum N f) := orderedPartialSum_affineOn (coefficients f) hab hadj
  have h := hp t hat htb
  rw [partialSum_matches_knots f N hN a ha, partialSum_matches_knots f N hN b hb] at h
  exact h

/-- Uniform continuity turns the interpolation identity into convergence in
supremum norm; the complete grid gives a mesh bound for every later prefix. -/
theorem expansion_of_interpolation (hinterp : Expected.Interpolation.{u}) :
    Expected.Expansion.{u} := by
  intro 𝕜 _ f
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := f.uniform_continuity (ε / 2) (by positivity)
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  have hn' : 1 / (2 : ℝ) ^ n < δ := by simpa only [div_pow, one_pow] using hn
  refine ⟨2 ^ n + 1, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := by have := Nat.one_le_pow n 2 (by decide); omega
  have hi := (hinterp 𝕜).2.2 N hN2 f
  have hnorm : ‖partialSum N f - f‖ ≤ ε / 2 := by
    apply (ContinuousMap.norm_le _ (by positivity : (0 : ℝ) ≤ ε / 2)).mpr
    intro t
    change ‖partialSum N f t - f t‖ ≤ ε / 2
    by_cases ht : t ∈ knots N
    · rw [hi.1 t ht, sub_self, norm_zero]
      positivity
    · obtain ⟨a, ha, b, hb, hat, htb, hadj⟩ := exists_adjacent_knots N t ht
      have hab := hat.trans htb
      have hgap := adjacent_gap_le hN hab hadj
      have hdist_a : dist a t < δ := by
        change |(a : ℝ) - t| < δ
        rw [abs_of_nonpos (by linarith : (a : ℝ) - t ≤ 0)]
        linarith
      have hdist_b : dist b t < δ := by
        change |(b : ℝ) - t| < δ
        rw [abs_of_nonneg (by linarith : 0 ≤ (b : ℝ) - t)]
        linarith
      have hfa : ‖f a - f t‖ ≤ ε / 2 := (by
        simpa only [dist_eq_norm] using (hcont hdist_a).le)
      have hfb : ‖f b - f t‖ ≤ ε / 2 := (by
        simpa only [dist_eq_norm] using (hcont hdist_b).le)
      have hs : ((b : ℝ) - t) / ((b : ℝ) - a) +
          ((t : ℝ) - a) / ((b : ℝ) - a) = 1 := by
        rw [← add_div]
        have he : (b : ℝ) - t + ((t : ℝ) - a) = (b : ℝ) - a := by ring
        rw [he, div_self (sub_pos.mpr hab).ne']
      have he : partialSum N f t - f t =
          (((b : ℝ) - t) / ((b : ℝ) - a)) • (f a - f t) +
          (((t : ℝ) - a) / ((b : ℝ) - a)) • (f b - f t) := by
        rw [hi.2 a ha b hb hab hadj t hat.le htb.le, smul_sub, smul_sub]
        rw [sub_add_sub_comm, ← add_smul, hs, one_smul]
      rw [he]
      exact norm_affine_le hab hat.le htb.le hfa hfb
  rw [dist_eq_norm]
  linarith

/-- Assembly of the Schauder property from interpolation. No continuity or
existence of expansions is assumed in the underlying raw basis predicate. -/
theorem basis_of_interpolation (hinterp : Expected.Interpolation.{u}) :
    Expected.BasisProperty.{u} := by
  intro 𝕜 _
  refine ⟨basis_nonzero 𝕜, fun f => ⟨coefficients f, ?_, ?_⟩⟩
  · exact expansion_of_interpolation hinterp 𝕜 f
  · intro a ha
    exact expansion_unique ha (expansion_of_interpolation hinterp 𝕜 f)

/-- The explicit coefficients are the unique coefficients of any expansion. -/
theorem coordinates_of_interpolation (hinterp : Expected.Interpolation.{u}) :
    Expected.CoordinateFormula.{u} := by
  intro 𝕜 _ f a ha
  exact expansion_unique ha (expansion_of_interpolation hinterp 𝕜 f)

theorem contractivity_of_interpolation (hinterp : Expected.Interpolation.{u}) :
    Expected.Contractivity.{u} := by
  intro 𝕜 _ N f
  rcases N with _ | (_ | N)
  · simp
  · apply (ContinuousMap.norm_le _ (norm_nonneg f)).mpr
    intro t
    rw [partialSum_one]
    exact f.norm_coe_le_norm 0
  · exact interpolates_norm_le ((hinterp 𝕜).2.2 _ (by omega) f)

theorem expansion : Expected.Expansion := expansion_of_interpolation interpolation

theorem basis_property : Expected.BasisProperty := basis_of_interpolation interpolation

theorem coordinate_formula : Expected.CoordinateFormula := coordinates_of_interpolation interpolation

theorem contractivity : Expected.Contractivity := contractivity_of_interpolation interpolation

/-- Positions of the right-of-1/3 midpoints, at every second level. -/
def branchPosition : ℕ → ℕ
  | 0 => 0
  | r + 1 => 4 * branchPosition r + 1

theorem branchPosition_identity (r : ℕ) : 3 * branchPosition r + 1 = 2 ^ (2 * r) := by
  induction r with
  | zero => norm_num [branchPosition]
  | succ r ih =>
    rw [branchPosition, show 2 * (r + 1) = 2 * r + 2 by omega, pow_add]
    norm_num
    omega

def branchFin (r : ℕ) : Fin (2 ^ (2 * r)) :=
  ⟨branchPosition r, by have := branchPosition_identity r; omega⟩

def branchIndex (r : ℕ) : ℕ := 2 ^ (2 * r) + branchPosition r + 1

def thirdPoint : Interval := ⟨1 / 3, by constructor <;> norm_num⟩

theorem branchIndex_injective : Function.Injective branchIndex := by
  intro r s hrs
  have hr := hatIndex_encode (2 * r) (branchFin r)
  have hs := hatIndex_encode (2 * s) (branchFin s)
  have hp : 2 ^ (2 * r) + (branchFin r).val - 1 = branchIndex r - 2 := by
    have := Nat.one_le_pow (2 * r) 2 (by decide)
    dsimp [branchIndex, branchFin]
    omega
  have hp' : 2 ^ (2 * s) + (branchFin s).val - 1 = branchIndex s - 2 := by
    have := Nat.one_le_pow (2 * s) 2 (by decide)
    dsimp [branchIndex, branchFin]
    omega
  rw [hp, hrs, ← hp', hs] at hr
  have := congrArg Sigma.fst hr
  simp only at this
  omega

theorem branch_scale_values (r : ℕ) :
    (2 : ℝ) ^ (2 * r + 1) * ((leftPoint (2 * r) (branchFin r) : ℝ) - 1 / 3) = -2 / 3 ∧
    (2 : ℝ) ^ (2 * r + 1) * ((midpoint (2 * r) (branchFin r) : ℝ) - 1 / 3) = 1 / 3 ∧
    (2 : ℝ) ^ (2 * r + 1) * ((rightPoint (2 * r) (branchFin r) : ℝ) - 1 / 3) = 4 / 3 := by
  have hi : 3 * ((branchFin r).val : ℝ) + 1 = (2 : ℝ) ^ (2 * r) := by
    exact_mod_cast branchPosition_identity r
  have hD : (2 : ℝ) ^ (2 * r + 1) = 2 * (3 * ((branchFin r).val : ℝ) + 1) := by
    rw [pow_succ, ← hi]
    ring
  have hl := scaled_left (2 * r) (branchFin r)
  have hm := scaled_midpoint (2 * r) (branchFin r)
  have hr := scaled_right (2 * r) (branchFin r)
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem branch_hat_third (r : ℕ) : basis 𝕜 (branchIndex r) thirdPoint = ((2 / 3 : ℝ) : 𝕜) := by
  change basis 𝕜 (2 ^ (2 * r) + (branchFin r).val + 1) thirdPoint = _
  rw [basis_encode]
  have hi : 3 * ((branchFin r).val : ℝ) + 1 = (2 : ℝ) ^ (2 * r) := by
    exact_mod_cast branchPosition_identity r
  have he : (2 : ℝ) ^ (2 * r + 1) * (1 / 3) - (2 * ((branchFin r).val : ℝ) + 1) = -1 / 3 := by
    rw [pow_succ, ← hi]
    ring
  change ((max 0 (1 - |(2 : ℝ) ^ (2 * r + 1) * (1 / 3) -
    (2 * ((branchFin r).val : ℝ) + 1)|) : ℝ) : 𝕜) = _
  rw [he]
  norm_num

/-- Continuous clipped steps, of supremum norm at most one. -/
def testFunction (𝕜 : Type u) [RCLike 𝕜] (N : ℕ) : FunctionSpace 𝕜 :=
  ⟨fun t => ((max (-1) (min 1 ((3 * (2 : ℝ) ^ (2 * N + 1)) * ((t : ℝ) - 1 / 3))) : ℝ) : 𝕜), by
    fun_prop⟩

theorem norm_testFunction_le (N : ℕ) : ‖testFunction 𝕜 N‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro t
  change ‖((max (-1) (min 1 ((3 * (2 : ℝ) ^ (2 * N + 1)) * ((t : ℝ) - 1 / 3))) : ℝ) : 𝕜)‖ ≤ 1
  rw [RCLike.norm_ofReal]
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- Along the selected branch, the clipped step has values -1,1,1 at
left endpoint, midpoint, right endpoint. -/
theorem testFunction_branch_values {N r : ℕ} (hrN : r ≤ N) :
    testFunction 𝕜 N (leftPoint (2 * r) (branchFin r)) = -1 ∧
    testFunction 𝕜 N (midpoint (2 * r) (branchFin r)) = 1 ∧
    testFunction 𝕜 N (rightPoint (2 * r) (branchFin r)) = 1 := by
  have hD : (2 : ℝ) ^ (2 * r + 1) ≤ 2 ^ (2 * N + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hp : (0 : ℝ) < 2 ^ (2 * r + 1) := by positivity
  obtain ⟨hl, hm, hr⟩ := branch_scale_values r
  have hneg : (leftPoint (2 * r) (branchFin r) : ℝ) - 1 / 3 < 0 := by nlinarith
  have hpos : 0 < (midpoint (2 * r) (branchFin r) : ℝ) - 1 / 3 := by nlinarith
  have hpos' : 0 < (rightPoint (2 * r) (branchFin r) : ℝ) - 1 / 3 := by nlinarith
  have hleft : 3 * (2 : ℝ) ^ (2 * N + 1) * ((leftPoint (2 * r) (branchFin r) : ℝ) - 1 / 3) ≤ -1 := by
    nlinarith [mul_le_mul_of_nonpos_right hD hneg.le]
  have hmid : 1 ≤ 3 * (2 : ℝ) ^ (2 * N + 1) * ((midpoint (2 * r) (branchFin r) : ℝ) - 1 / 3) := by
    nlinarith [mul_le_mul_of_nonneg_right hD hpos.le]
  have hright : 1 ≤ 3 * (2 : ℝ) ^ (2 * N + 1) * ((rightPoint (2 * r) (branchFin r) : ℝ) - 1 / 3) := by
    nlinarith [mul_le_mul_of_nonneg_right hD hpos'.le]
  constructor
  · change ((max (-1) (min 1 _) : ℝ) : 𝕜) = -1
    rw [min_eq_right (by linarith), max_eq_left hleft]
    simp
  constructor
  · change ((max (-1) (min 1 _) : ℝ) : 𝕜) = 1
    rw [min_eq_left hmid, max_eq_right (by norm_num)]
    simp
  · change ((max (-1) (min 1 _) : ℝ) : 𝕜) = 1
    rw [min_eq_left hright, max_eq_right (by norm_num)]
    simp

theorem testFunction_coefficient {N r : ℕ} (hrN : r ≤ N) :
    coefficients (testFunction 𝕜 N) (branchIndex r) = 1 := by
  change coefficients (testFunction 𝕜 N) (2 ^ (2 * r) + (branchFin r).val + 1) = 1
  rw [coefficients_encode, hatCoefficient]
  obtain ⟨hl, hm, hr⟩ := testFunction_branch_values (𝕜 := 𝕜) hrN
  rw [hl, hm, hr]
  simp

/-- If the basis were unconditional, its finite coordinate projections would
have a common norm bound. The clipped steps have norm at most one, but retaining
N + 1 hats on the even-level branch through 1/3 gives value 2(N + 1)/3 there.
This contradicts that common bound, for either real or complex scalars. -/
theorem conditionality : Expected.Conditionality := by
  intro 𝕜 _ hu
  classical
  let hb := basis_property 𝕜
  obtain ⟨P, hPsum, _, _, _, ⟨C, hC0, hC⟩, _⟩ :=
    C15SubsetProjections.raw_subset_projections hb hu
  have hc (f : FunctionSpace 𝕜) : C15Basis.Spec.rawCoordinates hb f = coefficients f :=
    coordinate_formula 𝕜 f _ (C15Basis.rawCoordinates_tendsto hb f)
  obtain ⟨N, hN⟩ := exists_nat_gt (3 * C / 2)
  let F := (Finset.range (N + 1)).image branchIndex
  let f := testFunction 𝕜 N
  have hsum : P (F : Set ℕ) f = ∑ i ∈ F, coefficients f i • basis 𝕜 i := by
    have hp := (C15Unconditional.hasUnconditionalSum_iff_hasSum _ _).mp (hPsum (F : Set ℕ) f)
    rw [hc] at hp
    have hs0 : HasSum ((F : Set ℕ).indicator (fun i => coefficients f i • basis 𝕜 i))
        (∑ i ∈ F, (F : Set ℕ).indicator (fun j => coefficients f j • basis 𝕜 j) i) :=
      hasSum_sum_of_ne_finset_zero (s := F) (by
        intro i hi
        exact Set.indicator_of_notMem hi _)
    have heq : (∑ i ∈ F, (F : Set ℕ).indicator (fun j => coefficients f j • basis 𝕜 j) i) =
        ∑ i ∈ F, coefficients f i • basis 𝕜 i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Set.indicator_of_mem (show i ∈ (F : Set ℕ) from hi) _
    rw [heq] at hs0
    exact hp.unique hs0
  have hev : P (F : Set ℕ) f thirdPoint =
      (((N + 1 : ℕ) : ℝ) * (2 / 3) : ℝ) := by
    rw [hsum, ContinuousMap.sum_apply]
    dsimp [F]
    rw [Finset.sum_image (fun _ _ _ _ hij => branchIndex_injective hij)]
    have heach : ∀ r ∈ Finset.range (N + 1),
        coefficients f (branchIndex r) * basis 𝕜 (branchIndex r) thirdPoint =
          ((2 / 3 : ℝ) : 𝕜) := by
      intro r hr
      rw [testFunction_coefficient (by simpa using hr), one_mul, branch_hat_third]
    rw [Finset.sum_congr rfl heach]
    simp
  have hnorm : ‖P (F : Set ℕ) f‖ ≤ C := by
    calc
      ‖P (F : Set ℕ) f‖ ≤ ‖P (F : Set ℕ)‖ * ‖f‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * 1 := mul_le_mul (hC _) (norm_testFunction_le N) (norm_nonneg _) hC0
      _ = C := mul_one _
  have hpoint := (P (F : Set ℕ) f).norm_coe_le_norm thirdPoint
  rw [hev, RCLike.norm_ofReal, abs_of_nonneg (by positivity)] at hpoint
  have hnreal : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; rfl
  rw [hnreal] at hpoint
  linarith

end ExpandedFA.P1.SchauderHatBasis
