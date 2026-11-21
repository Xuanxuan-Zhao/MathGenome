import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.ChebyshevLebesgue
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.InterpolationNorm
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.ChebyshevMinimax
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convex.Function

noncomputable section
open Polynomial
open scoped BigOperators

namespace NumAnalysis206.Approximation.ChebyshevLebesgue

abbrev standardNodes := Specs.NumAnalysis206.Approximation.ChebyshevLebesgue.standardNodesValue
abbrev affinePoint := Specs.NumAnalysis206.Approximation.ChebyshevLebesgue.affinePointValue
abbrev affineNodes := Specs.NumAnalysis206.Approximation.ChebyshevLebesgue.affineNodesValue

theorem standardNodes_injective (n : ℕ) : Function.Injective (standardNodes n) := by
  intro i j hij
  apply Fin.ext
  exact Chebyshev.distinctNodes (n + 1) (Finset.mem_range.mpr i.isLt)
    (Finset.mem_range.mpr j.isLt) (congrArg Subtype.val hij)

theorem affinePoint_injective (a b : ℝ) (hab : a < b) :
    Function.Injective (affinePoint a b hab) := by
  intro t u h
  apply Subtype.ext
  have he := congrArg Subtype.val h
  change (a + b) / 2 + (b - a) / 2 * (t : ℝ) =
    (a + b) / 2 + (b - a) / 2 * (u : ℝ) at he
  nlinarith

theorem affineNodes_injective (a b : ℝ) (hab : a < b) (n : ℕ) :
    Function.Injective (affineNodes a b hab n) :=
  (affinePoint_injective a b hab).comp (standardNodes_injective n)

/-- Affine cancellation in the defining product works even at the nodes. -/
theorem cardinal_affine_eval {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x : ι → ℝ) (i : ι) (c d t : ℝ) (hc : c ≠ 0) :
    (cardinal s (fun j => d + c * x j) i).eval (d + c * t) =
      (cardinal s x i).eval t := by
  simp only [cardinal, Specs.NumAnalysis206.Approximation.cardinalValue,
    eval_prod, eval_mul, eval_C, eval_sub, eval_X]
  apply Finset.prod_congr rfl
  intro j hj
  rw [show d + c * x i - (d + c * x j) = c * (x i - x j) by ring,
    show d + c * t - (d + c * x j) = c * (t - x j) by ring,
    mul_inv_rev]
  field_simp

theorem affine_cardinal_values (a b : ℝ) (hab : a < b) (n : ℕ)
    (i : Fin (n + 1)) (t : Set.Icc (-1 : ℝ) 1) :
    (cardinal Finset.univ (fun j => (affineNodes a b hab n j : ℝ)) i).eval
        (affinePoint a b hab t : ℝ) =
      (cardinal Finset.univ (fun j => (standardNodes n j : ℝ)) i).eval (t : ℝ) := by
  exact cardinal_affine_eval Finset.univ _ i ((b - a) / 2) ((a + b) / 2) t (by linarith)

theorem affine_function_values (a b : ℝ) (hab : a < b) (n : ℕ)
    (t : Set.Icc (-1 : ℝ) 1) :
    lebesgueFunction (affineNodes a b hab n) (affinePoint a b hab t) =
      lebesgueFunction (standardNodes n) t := by
  change (∑ i : Fin (n + 1), |(cardinal Finset.univ (fun j => (affineNodes a b hab n j : ℝ)) i).eval (affinePoint a b hab t : ℝ)|) =
    ∑ i : Fin (n + 1), |(cardinal Finset.univ (fun j => (standardNodes n j : ℝ)) i).eval (t : ℝ)|
  simp_rw [affine_cardinal_values]

theorem affinePoint_surjective (a b : ℝ) (hab : a < b) :
    Function.Surjective (affinePoint a b hab) := by
  intro x
  have hd : 0 < b - a := sub_pos.mpr hab
  let t : Set.Icc (-1 : ℝ) 1 := ⟨(2 * (x : ℝ) - a - b) / (b - a), by
    constructor
    · apply (le_div_iff₀ hd).2
      nlinarith [x.property.1]
    · apply (div_le_iff₀ hd).2
      nlinarith [x.property.2]⟩
  refine ⟨t, Subtype.ext ?_⟩
  change (a + b) / 2 + (b - a) / 2 * ((2 * (x : ℝ) - a - b) / (b - a)) = (x : ℝ)
  field_simp
  ring

theorem affine_constant (a b : ℝ) (hab : a < b) (n : ℕ) :
    lebesgueConstant (affineNodes a b hab n) = lebesgueConstant (standardNodes n) := by
  obtain ⟨t, ht, _⟩ := lebesgue_maximum (affineNodes a b hab n) hab
  obtain ⟨u, hu⟩ := affinePoint_surjective a b hab t
  obtain ⟨v, hv, _⟩ := lebesgue_maximum (standardNodes n) (by norm_num)
  apply le_antisymm
  · rw [ht, ← hu, affine_function_values]
    exact lebesgueFunction_le _ _
  · rw [hv, ← affine_function_values a b hab n v]
    exact lebesgueFunction_le _ _

theorem affine_operator_norm (a b : ℝ) (hab : a < b) (n : ℕ) :
    ‖interpolationOperator (affineNodes a b hab n)‖ =
      ‖interpolationOperator (standardNodes n)‖ := by
  rw [interpolation_norm _ hab (affineNodes_injective a b hab n),
    interpolation_norm _ (by norm_num) (standardNodes_injective n), affine_constant]

/-- The value at every node is one for any distinct-node family. -/
theorem lebesgueFunction_at_node {a b : ℝ} {n : ℕ}
    (x : Fin (n + 1) → Set.Icc a b) (hx : Function.Injective x) (i : Fin (n + 1)) :
    lebesgueFunction x (x i) = 1 := by
  have hxr : Set.InjOn (fun j => (x j : ℝ)) (Finset.univ : Finset (Fin (n+1))) := by
    intro j _ k _ h
    exact hx (Subtype.ext h)
  change (∑ j : Fin (n + 1), |(cardinal Finset.univ (fun k => (x k : ℝ)) j).eval (x i : ℝ)|) = 1
  simp_rw [cardinal_eval _ _ hxr _ (Finset.mem_univ _) _ (Finset.mem_univ _),
    apply_ite abs, abs_one, abs_zero]
  simp

theorem at_nodes (n : ℕ) (i : Fin (n + 1)) :
    lebesgueFunction (standardNodes n) (standardNodes n i) = 1 :=
  lebesgueFunction_at_node _ (standardNodes_injective n) i

theorem affine_at_nodes (a b : ℝ) (hab : a < b) (n : ℕ) (i : Fin (n + 1)) :
    lebesgueFunction (affineNodes a b hab n) (affineNodes a b hab n i) = 1 :=
  lebesgueFunction_at_node _ (affineNodes_injective a b hab n) i

theorem singleton : lebesgueConstant (standardNodes 0) = 1 := by
  obtain ⟨t, ht, _⟩ := lebesgue_maximum (standardNodes 0) (by norm_num)
  rw [ht]
  change (∑ i : Fin 1, |(cardinal _ _ i).eval _|) = _
  simp [cardinal, Specs.NumAnalysis206.Approximation.cardinalValue]

/-- Angular positions of the roots, in radians. -/
def angle (m j : ℕ) : ℝ := ((j : ℝ) + 1 / 2) * Real.pi / m

lemma angle_mem (m j : ℕ) (hj : j < m) : angle m j ∈ Set.Ioo 0 Real.pi := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le j).trans_lt hj
  have hjr : (j : ℝ) + 1 ≤ m := by exact_mod_cast hj
  constructor
  · exact div_pos (mul_pos (by positivity) Real.pi_pos) hm
  · apply (div_lt_iff₀ hm).2
    change ((j : ℝ) + 1 / 2) * Real.pi < Real.pi * m
    nlinarith [Real.pi_pos]

lemma node_cos_angle (m j : ℕ) : Chebyshev.node m j = Real.cos (angle m j) := rfl

lemma sin_half_sum_bound (θ φ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
    (hφ : φ ∈ Set.Icc 0 Real.pi) :
    Real.sin φ ≤ 2 * Real.sin ((θ + φ) / 2) := by
  have hs : min (Real.sin (φ / 2)) (Real.sin (φ / 2 + Real.pi / 2)) ≤
      Real.sin ((θ + φ) / 2) := by
    apply ConcaveOn.ge_on_segment (StrictConcaveOn.concaveOn strictConcaveOn_sin_Icc)
      (show φ / 2 ∈ Set.Icc 0 Real.pi by constructor <;> linarith [hφ.1, hφ.2])
      (show φ / 2 + Real.pi / 2 ∈ Set.Icc 0 Real.pi by
        constructor <;> linarith [hφ.1, hφ.2])
    rw [segment_eq_Icc (by linarith [Real.pi_pos])]
    constructor <;> linarith [hθ.1, hθ.2]
  rw [Real.sin_add_pi_div_two] at hs
  have hsin : 0 ≤ Real.sin (φ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hφ.1]) (by linarith [hφ.2, Real.pi_pos])
  have hcos : 0 ≤ Real.cos (φ / 2) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [hφ.1, Real.pi_pos], by linarith [hφ.2]⟩
  have hid : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    rw [← Real.sin_two_mul]; congr 1; ring
  have hb1 := mul_le_mul_of_nonneg_left (Real.cos_le_one (φ / 2)) (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hsin)
  have hb2 := mul_le_mul_of_nonneg_left (Real.sin_le_one (φ / 2)) (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hcos)
  rw [hid]
  rcases le_total (Real.sin (φ / 2)) (Real.cos (φ / 2)) with h | h
  · rw [min_eq_left h] at hs
    nlinarith
  · rw [min_eq_right h] at hs
    nlinarith

lemma cosine_distance_bound (θ φ : ℝ) (hθ : θ ∈ Set.Icc 0 Real.pi)
    (hφ : φ ∈ Set.Icc 0 Real.pi) :
    Real.sin φ * |θ - φ| ≤ Real.pi * |Real.cos θ - Real.cos φ| := by
  have hhalf : |(θ - φ) / 2| ≤ Real.pi / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2
    exact abs_le.mpr ⟨by linarith [hθ.1, hφ.2], by linarith [hθ.2, hφ.1]⟩
  have hsin := Real.mul_abs_le_abs_sin hhalf
  have hsum : 0 ≤ Real.sin ((θ + φ) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1, hφ.1])
      (by linarith [hθ.2, hφ.2])
  have hph := sin_half_sum_bound θ φ hθ hφ
  have ha : |(θ - φ) / 2| = |θ - φ| / 2 := by norm_num [abs_div]
  rw [ha] at hsin
  have hb : |θ - φ| ≤ Real.pi * |Real.sin ((θ - φ) / 2)| := by
    have hh := mul_le_mul_of_nonneg_left hsin Real.pi_pos.le
    field_simp at hh
    linarith
  have hmul := mul_le_mul_of_nonneg_left hb (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hsum)
  have hmul2 := mul_le_mul_of_nonneg_right hph (abs_nonneg (θ - φ))
  rw [Real.cos_sub_cos, abs_mul, abs_mul, abs_of_nonneg hsum]
  norm_num
  nlinarith

lemma derivative_cos_mul_sin (m : ℕ) (φ : ℝ) :
    (Chebyshev.t m).derivative.eval (Real.cos φ) * Real.sin φ =
      m * Real.sin (m * φ) := by
  simp only [Chebyshev.t, Specs.NumAnalysis206.Approximation.Chebyshev.tValue,
    Polynomial.Chebyshev.T_derivative_eq_U, eval_mul, eval_intCast]
  rw [mul_assoc, Polynomial.Chebyshev.U_real_cos]
  push_cast
  ring_nf

lemma sin_mul_angle (m j : ℕ) (hm : 0 < m) :
    Real.sin (m * angle m j) = (-1 : ℝ) ^ j := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : (m : ℝ) * angle m j = Real.pi / 2 + j * Real.pi := by
    dsimp [angle]
    field_simp
    ring
  rw [he, Real.sin_add_nat_mul_pi]
  simp

lemma cos_mul_angle (m j : ℕ) (hm : 0 < m) :
    Real.cos (m * angle m j) = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : (m : ℝ) * angle m j = Real.pi / 2 + j * Real.pi := by
    dsimp [angle]
    field_simp
    ring
  rw [he, Real.cos_add_nat_mul_pi]
  simp

lemma abs_derivative_at_root (m j : ℕ) (hj : j < m) :
    |(Chebyshev.t m).derivative.eval (Chebyshev.node m j)| * Real.sin (angle m j) = m := by
  have hφ := angle_mem m j hj
  have hs : 0 < Real.sin (angle m j) := Real.sin_pos_of_mem_Ioo hφ
  have h := congrArg abs (derivative_cos_mul_sin m (angle m j))
  rw [abs_mul, abs_of_pos hs, sin_mul_angle m j (by omega)] at h
  simpa only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ m from Nat.cast_nonneg m), abs_neg_one_pow,
    mul_one, ← node_cos_angle] using h

lemma cardinal_mul_derivative (m j : ℕ) (hj : j < m) (x : ℝ)
    (hx : x ≠ Chebyshev.node m j) :
    (cardinal (Finset.range m) (Chebyshev.node m) j).eval x *
      (Chebyshev.t m).derivative.eval (Chebyshev.node m j) *
      (x - Chebyshev.node m j) = (Chebyshev.t m).eval x := by
  have hn : Lagrange.nodal (Finset.range m) (Chebyshev.node m) = Chebyshev.monicT m :=
    (Chebyshev.nodalPolynomial m).symm
  have hd : (Chebyshev.t m).derivative.eval (Chebyshev.node m j) ≠ 0 := by
    have hh := abs_derivative_at_root m j hj
    intro h
    rw [h, abs_zero, zero_mul] at hh
    have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le j).trans_lt hj
    linarith
  have h := Lagrange.eval_basis_not_at_node (v := Chebyshev.node m)
    (Finset.mem_range.mpr hj) hx
  rw [Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_range.mpr hj), hn] at h
  change (cardinal (Finset.range m) (Chebyshev.node m) j).eval x = _ at h
  simp only [Chebyshev.monicT, Specs.NumAnalysis206.Approximation.Chebyshev.monicValue,
    eval_mul, eval_C, derivative_mul, derivative_C, zero_mul, zero_add] at h
  rw [h]
  field_simp

lemma cardinal_cos_distance (m j : ℕ) (hj : j < m) (θ : ℝ)
    (hθ : θ ∈ Set.Icc 0 Real.pi) (hne : Real.cos θ ≠ Chebyshev.node m j) :
    |(cardinal (Finset.range m) (Chebyshev.node m) j).eval (Real.cos θ)| *
      m * |θ - angle m j| ≤ Real.pi * |Real.cos (m * θ)| := by
  let A := |(cardinal (Finset.range m) (Chebyshev.node m) j).eval (Real.cos θ)|
  let φ := angle m j
  have hφ := angle_mem m j hj
  have hs : 0 < Real.sin φ := Real.sin_pos_of_mem_Ioo hφ
  have hd := abs_derivative_at_root m j hj
  have hc := congrArg abs (cardinal_mul_derivative m j hj (Real.cos θ) hne)
  rw [abs_mul, abs_mul, Chebyshev.cosine, node_cos_angle] at hc
  have hid : A * m * |Real.cos θ - Real.cos φ| = |Real.cos (m * θ)| * Real.sin φ := by
    calc A * m * |Real.cos θ - Real.cos φ| =
        (A * |(Chebyshev.t m).derivative.eval (Chebyshev.node m j)| *
          |Real.cos θ - Real.cos φ|) * Real.sin φ := by rw [← hd]; ring
    _ = _ := congrArg (· * Real.sin φ) hc
  apply (mul_le_mul_iff_of_pos_right hs).1
  have hdist := cosine_distance_bound θ φ hθ ⟨hφ.1.le, hφ.2.le⟩
  have hmul := mul_le_mul_of_nonneg_left hdist
    (mul_nonneg (show 0 ≤ A from abs_nonneg _) (Nat.cast_nonneg m))
  calc A * m * |θ - φ| * Real.sin φ =
      (A * m) * (Real.sin φ * |θ - φ|) := by ring
    _ ≤ (A * m) * (Real.pi * |Real.cos θ - Real.cos φ|) := hmul
    _ = Real.pi * (|Real.cos (m * θ)| * Real.sin φ) := by rw [← hid]; ring
    _ = _ := by ring

/-- A bounded, nonsingular majorant, also valid at a root. -/
lemma cardinal_regularized_bound (m j : ℕ) (hj : j < m) (θ : ℝ)
    (hθ : θ ∈ Set.Icc 0 Real.pi) :
    |(cardinal (Finset.range m) (Chebyshev.node m) j).eval (Real.cos θ)| ≤
      2 * Real.pi / (1 + m * |θ - angle m j|) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le j).trans_lt hj
  let A := |(cardinal (Finset.range m) (Chebyshev.node m) j).eval (Real.cos θ)|
  have hA : 0 ≤ A := abs_nonneg _
  have hD : 0 ≤ (m : ℝ) * |θ - angle m j| := mul_nonneg hm.le (abs_nonneg _)
  apply (le_div_iff₀ (by linarith : 0 < 1 + (m : ℝ) * |θ - angle m j|)).2
  by_cases he : θ = angle m j
  · subst θ
    have hv := cardinal_eval (Finset.range m) (Chebyshev.node m) (Chebyshev.distinctNodes m)
      j (Finset.mem_range.mpr hj) j (Finset.mem_range.mpr hj)
    simp only [ite_true] at hv
    change _ ≤ _
    rw [← node_cos_angle, hv]
    norm_num
    linarith [Real.two_le_pi]
  · have hφ := angle_mem m j hj
    have hne : Real.cos θ ≠ Chebyshev.node m j := by
      rw [node_cos_angle]
      intro h
      exact he (Real.injOn_cos hθ ⟨hφ.1.le, hφ.2.le⟩ h)
    have hdist := cardinal_cos_distance m j hj θ hθ hne
    have hcos : |Real.cos (m * θ)| ≤ (m : ℝ) * |θ - angle m j| := by
      have h := Real.abs_cos_sub_cos_le (m * θ) (m * angle m j)
      rw [cos_mul_angle m j (by omega), sub_zero,
        ← mul_sub, abs_mul, abs_of_pos hm] at h
      exact h
    have hDpos : 0 < (m : ℝ) * |θ - angle m j| :=
      mul_pos hm (abs_pos.mpr (sub_ne_zero.mpr he))
    have hApi : A ≤ Real.pi := by
      apply (mul_le_mul_iff_of_pos_right hDpos).1
      calc
        A * ((m : ℝ) * |θ - angle m j|) ≤ Real.pi * |Real.cos (m * θ)| := by
          simpa only [mul_assoc] using hdist
        _ ≤ _ := mul_le_mul_of_nonneg_left hcos Real.pi_pos.le
    have hprod : A * ((m : ℝ) * |θ - angle m j|) ≤ Real.pi := by
      have hh := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (m * θ)) Real.pi_pos.le
      nlinarith [hdist]
    change A * (1 + (m : ℝ) * |θ - angle m j|) ≤ _
    nlinarith

/-- A half-integer grid has a uniformly logarithmic regularized reciprocal sum. -/
lemma reciprocal_grid_sum (m : ℕ) (r : ℝ) (hr : r ∈ Set.Icc 0 (m : ℝ)) :
    (∑ j ∈ Finset.range m, (1 : ℝ) / (1 + |r - ((j : ℝ) + 1 / 2)|)) ≤
      4 * (harmonic m : ℝ) := by
  let k := ⌊r⌋₊
  have hk : k ≤ m := Nat.floor_le_of_le hr.2
  have hkr : (k : ℝ) ≤ r := Nat.floor_le hr.1
  have hrk : r < (k : ℝ) + 1 := Nat.lt_floor_add_one r
  let f : ℕ → ℝ := fun j => 1 / (1 + |r - ((j : ℝ) + 1 / 2)|)
  let g : ℕ → ℝ := fun j => 2 / ((j : ℝ) + 1)
  have hleft : ∑ j ∈ (Finset.range m).filter (fun j => j < k), f j ≤
      ∑ j ∈ Finset.range m, g j := by
    apply Finset.sum_le_sum_of_injOn (fun j => k - 1 - j)
    · intro i hi j hj he
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      change k - 1 - i = k - 1 - j at he
      omega
    · intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      have hj' := (Finset.mem_filter.mp hj).2
      apply Finset.mem_range.mpr
      omega
    · intro j hj
      have hjk := (Finset.mem_filter.mp hj).2
      have he : ((k - 1 - j : ℕ) : ℝ) + 1 = (k : ℝ) - j := by
        have hh : k - 1 - j + 1 + j = k := by omega
        have hh' := congrArg (fun v : ℕ => (v : ℝ)) hh
        push_cast at hh'
        linarith
      have hpos : (0 : ℝ) < ((k - 1 - j : ℕ) : ℝ) + 1 := by positivity
      dsimp [f, g]
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + |r - ((j : ℝ) + 1 / 2)|) hpos).2
      rw [he]
      have hab := le_abs_self (r - ((j : ℝ) + 1 / 2))
      nlinarith
    · intro j hj hj'
      dsimp [g]
      positivity
  have hright : ∑ j ∈ (Finset.range m).filter (fun j => ¬ j < k), f j ≤
      ∑ j ∈ Finset.range m, g j := by
    apply Finset.sum_le_sum_of_injOn (fun j => j - k)
    · intro i hi j hj he
      have hi' := (Finset.mem_filter.mp hi).2
      have hj' := (Finset.mem_filter.mp hj).2
      change i - k = j - k at he
      omega
    · intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
      have hj' := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
      apply Finset.mem_range.mpr
      omega
    · intro j hj
      have hjk : k ≤ j := Nat.le_of_not_gt (Finset.mem_filter.mp hj).2
      have he : ((j - k : ℕ) : ℝ) + 1 = (j : ℝ) - k + 1 := by
        rw [Nat.cast_sub hjk]
      have hpos : (0 : ℝ) < ((j - k : ℕ) : ℝ) + 1 := by positivity
      have hjkr : (k : ℝ) ≤ j := by exact_mod_cast hjk
      dsimp [f, g]
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 1 + |r - ((j : ℝ) + 1 / 2)|) hpos).2
      rw [he]
      have hab := neg_le_abs (r - ((j : ℝ) + 1 / 2))
      nlinarith
    · intro j hj hj'
      dsimp [g]
      positivity
  have hg : ∑ j ∈ Finset.range m, g j = 2 * (harmonic m : ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    simp only [g, div_eq_mul_inv, Finset.mul_sum, Nat.cast_add, Nat.cast_one]
  change ∑ j ∈ Finset.range m, f j ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range m) (fun j => j < k) f]
  rw [hg] at hleft hright
  linarith

lemma cardinal_fin_eq_range (m : ℕ) (x : ℕ → ℝ) (i : Fin m) :
    cardinal Finset.univ (fun j : Fin m => x j) i = cardinal (Finset.range m) x i := by
  unfold cardinal Specs.NumAnalysis206.Approximation.cardinalValue
  apply Finset.prod_bij (fun (j : Fin m) _ => (j : ℕ))
  · intro j hj
    obtain ⟨hji, _⟩ := Finset.mem_erase.mp hj
    exact Finset.mem_erase.mpr ⟨fun h => hji (Fin.ext h), Finset.mem_range.mpr j.isLt⟩
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro j hj
    obtain ⟨hji, hjm⟩ := Finset.mem_erase.mp hj
    refine ⟨⟨j, Finset.mem_range.mp hjm⟩, ?_, rfl⟩
    apply Finset.mem_erase.mpr
    exact ⟨fun h => hji (congrArg Fin.val h), Finset.mem_univ _⟩
  · intro j hj
    rfl

lemma cardinal_grid_bound (m j : ℕ) (hj : j < m) (θ : ℝ)
    (hθ : θ ∈ Set.Icc 0 Real.pi) :
    |(cardinal (Finset.range m) (Chebyshev.node m) j).eval (Real.cos θ)| ≤
      2 * Real.pi / (1 + |(m : ℝ) * θ / Real.pi - ((j : ℝ) + 1 / 2)|) := by
  have hm : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le j).trans_lt hj
  have hid : (m : ℝ) * (θ - angle m j) =
      Real.pi * ((m : ℝ) * θ / Real.pi - ((j : ℝ) + 1 / 2)) := by
    dsimp [angle]
    field_simp
  have habs := congrArg abs hid
  simp only [abs_mul, abs_of_pos hm, abs_of_pos Real.pi_pos] at habs
  have hdist : |(m : ℝ) * θ / Real.pi - ((j : ℝ) + 1 / 2)| ≤
      (m : ℝ) * |θ - angle m j| := by
    rw [habs]
    nlinarith [abs_nonneg ((m : ℝ) * θ / Real.pi - ((j : ℝ) + 1 / 2)), Real.two_le_pi]
  apply (cardinal_regularized_bound m j hj θ hθ).trans
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- An explicit absolute bound; optimal constants are not needed for W53. -/
theorem standard_bound (n : ℕ) :
    lebesgueConstant (standardNodes n) ≤ 8 * Real.pi * (1 + Real.log (n + 1)) := by
  obtain ⟨t, ht, _⟩ := lebesgue_maximum (standardNodes n) (by norm_num)
  rw [ht]
  let θ := Real.arccos (t : ℝ)
  have hθ : θ ∈ Set.Icc 0 Real.pi := ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hcos : Real.cos θ = (t : ℝ) := Real.cos_arccos t.property.1 t.property.2
  have hrepr : lebesgueFunction (standardNodes n) t =
      ∑ j ∈ Finset.range (n + 1),
        |(cardinal (Finset.range (n + 1)) (Chebyshev.node (n + 1)) j).eval (Real.cos θ)| := by
    change (∑ i : Fin (n + 1),
      |(cardinal Finset.univ (fun j : Fin (n + 1) => Chebyshev.node (n + 1) j) i).eval (t : ℝ)|) = _
    simp_rw [cardinal_fin_eq_range, ← hcos]
    exact Fin.sum_univ_eq_sum_range (fun j =>
      |(cardinal (Finset.range (n + 1)) (Chebyshev.node (n + 1)) j).eval (Real.cos θ)|) (n + 1)
  rw [hrepr]
  have hr : (n + 1 : ℝ) * θ / Real.pi ∈ Set.Icc 0 (n + 1 : ℝ) := by
    constructor
    · exact div_nonneg (mul_nonneg (by positivity) hθ.1) Real.pi_pos.le
    · apply (div_le_iff₀ Real.pi_pos).2
      exact mul_le_mul_of_nonneg_left hθ.2 (by positivity)
  calc
    (∑ j ∈ Finset.range (n + 1),
        |(cardinal (Finset.range (n + 1)) (Chebyshev.node (n + 1)) j).eval (Real.cos θ)|) ≤
        ∑ j ∈ Finset.range (n + 1),
          2 * Real.pi / (1 + |(n + 1 : ℝ) * θ / Real.pi - ((j : ℝ) + 1 / 2)|) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa only [Nat.cast_add, Nat.cast_one] using
        cardinal_grid_bound (n + 1) j (Finset.mem_range.mp hj) θ hθ
    _ = (2 * Real.pi) * ∑ j ∈ Finset.range (n + 1),
          1 / (1 + |(n + 1 : ℝ) * θ / Real.pi - ((j : ℝ) + 1 / 2)|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (2 * Real.pi) * (4 * (harmonic (n + 1) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact reciprocal_grid_sum (n + 1) _ (by simpa only [Nat.cast_add, Nat.cast_one] using hr)
    _ ≤ (2 * Real.pi) * (4 * (1 + Real.log (n + 1))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [Nat.cast_add, Nat.cast_one] using harmonic_le_one_add_log (n + 1)
    _ = _ := by ring

/-- The same absolute constant works simultaneously for every degree and interval. -/
theorem logarithmic_bound : Specs.NumAnalysis206.Approximation.ChebyshevLebesgue.logarithmicBound := by
  refine ⟨8 * Real.pi, by positivity, ?_⟩
  intro n
  refine ⟨standard_bound n, ?_⟩
  intro a b hab
  change lebesgueConstant (affineNodes a b hab n) ≤ _ ∧
    ‖interpolationOperator (affineNodes a b hab n)‖ ≤ _
  rw [interpolation_norm _ hab (affineNodes_injective a b hab n), affine_constant]
  exact ⟨standard_bound n, standard_bound n⟩

end NumAnalysis206.Approximation.ChebyshevLebesgue







