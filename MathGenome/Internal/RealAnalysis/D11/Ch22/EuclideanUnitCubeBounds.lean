import MathGenome.Internal.RealAnalysis.D11.Ch22.HausdorffOuterMeasure
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch22.EuclideanUnitCubeBounds
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-! Quantitative Euclidean cube bounds.

We explicitly compare the l2 and sup metrics using the two coordinate maps.
Mathlib's sup-metric Hausdorff/volume identity is proved by bounding boxes
and arbitrarily fine grids. The forward map has Lipschitz constant one;
the inverse has constant `n^(1/2)`. Thus the final outer measure and cube
retain the l2 metric, and the upper constant is `n^(n/2)`, not one.
-/

noncomputable section

open Set Metric MeasureTheory
open scoped NNReal ENNReal

namespace D11.Ch22.EuclideanUnitCubeBounds

open D11.Ch03

theorem hausdorffOuterMeasure_eq_native {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] (s : ℝ≥0) (E : Set X) :
    hausdorffOuterMeasure s E = Measure.hausdorffMeasure (s : ℝ) E := by
  rw [hausdorffOuterMeasure_eq_mkMetric']
  exact congrFun (OuterMeasure.coe_mkMetric (fun r => r ^ (s : ℝ))) E

private theorem sup_cube_mass (n : ℕ) :
    Measure.hausdorffMeasure (n : ℝ)
      (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) = 1 := by
  have h := MeasureTheory.hausdorffMeasure_pi_real (ι := Fin n)
  simp only [Fintype.card_fin] at h
  rw [h, Set.pi_univ_Icc]
  simp [Real.volume_Icc_pi]

private theorem ofLp_cube (n : ℕ) :
    WithLp.ofLp '' closedBox (0 : Fin n → ℝ) 1 =
      Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact fun j _ => hy j
  · intro hx
    exact ⟨WithLp.toLp 2 x, fun j => hx j (Set.mem_univ _), rfl⟩

private theorem toLp_cube (n : ℕ) :
    WithLp.toLp 2 '' Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) =
      closedBox (0 : Fin n → ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact fun j => hy j (Set.mem_univ _)
  · intro hx
    exact ⟨WithLp.ofLp x, fun j _ => hx j, rfl⟩

/-- Bounding-box lower estimate for every countable cover, including covers
with nonmeasurable or unbounded entries. -/
theorem arbitrary_cover_lower (n : ℕ) (_hn : 1 ≤ n)
    (U : ℕ → Set (Point n))
    (hU : closedBox (0 : Fin n → ℝ) 1 ⊆ ⋃ j, U j) :
    1 ≤ ∑' j, ediam (U j) ^ (n : ℝ) := by
  have hmass : volume (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) = 1 := by
    simpa only [← hausdorffMeasure_pi_real (ι := Fin n), Fintype.card_fin]
      using sup_cube_mass n
  rw [← hmass]
  calc
    volume (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) ≤
        volume (⋃ j, WithLp.ofLp '' U j) := by
      apply measure_mono
      rw [← ofLp_cube n]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hU hx)
      exact Set.mem_iUnion.mpr ⟨j, Set.mem_image_of_mem _ hj⟩
    _ ≤ ∑' j, volume (WithLp.ofLp '' U j) := measure_iUnion_le _
    _ ≤ ∑' j, ediam (U j) ^ (n : ℝ) := by
      apply ENNReal.tsum_le_tsum
      intro j
      have hd : ediam (WithLp.ofLp '' U j) ≤ ediam (U j) := by
        simpa only [ENNReal.coe_one, one_mul] using
          (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℝ)).ediam_image_le (U j)
      calc
        volume (WithLp.ofLp '' U j) ≤ ediam (WithLp.ofLp '' U j) ^ n := by
          simpa only [Fintype.card_fin] using
            Real.volume_pi_le_diam_pow (WithLp.ofLp '' U j)
        _ ≤ ediam (U j) ^ n := pow_le_pow_left' hd n
        _ = ediam (U j) ^ (n : ℝ) := (ENNReal.rpow_natCast _ _).symm

/-- The coefficient-one Hausdorff outer mass of the Euclidean unit cube lies
between one and `n^(n/2)`. -/
theorem unit_cube_bounds (n : ℕ) (_hn : 1 ≤ n) :
    1 ≤ hausdorffOuterMeasure (n : ℝ≥0) (closedBox (0 : Fin n → ℝ) 1) ∧
    hausdorffOuterMeasure (n : ℝ≥0) (closedBox (0 : Fin n → ℝ) 1) ≤
      ENNReal.ofReal ((n : ℝ) ^ ((n : ℝ) / 2)) := by
  rw [hausdorffOuterMeasure_eq_native]
  simp only [NNReal.coe_natCast]
  constructor
  · have h := (PiLp.lipschitzWith_ofLp 2 (fun _ : Fin n => ℝ)).hausdorffMeasure_image_le
      (d := (n : ℝ)) (Nat.cast_nonneg n) (closedBox (0 : Fin n → ℝ) 1)
    simpa only [ofLp_cube, sup_cube_mass, ENNReal.coe_one, ENNReal.one_rpow,
      one_mul] using h
  · have h := (PiLp.lipschitzWith_toLp 2 (fun _ : Fin n => ℝ)).hausdorffMeasure_image_le
      (d := (n : ℝ)) (Nat.cast_nonneg n)
      (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1))
    simp only [toLp_cube, sup_cube_mass, mul_one, Fintype.card_fin] at h
    norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat] at h
    rw [ENNReal.coe_rpow_of_nonneg _ (by positivity), ← ENNReal.rpow_mul] at h
    convert h using 1
    rw [← ENNReal.ofReal_rpow_of_nonneg (Nat.cast_nonneg n) (by positivity),
      ENNReal.ofReal_natCast, ENNReal.coe_natCast]
    congr 1
    ring

theorem unit_interval_mass :
    hausdorffOuterMeasure (1 : ℝ≥0) (closedBox (0 : Fin 1 → ℝ) 1) = 1 := by
  obtain ⟨hl, hu⟩ := unit_cube_bounds 1 (by rfl)
  exact le_antisymm (by simpa using hu) (by simpa using hl)

end D11.Ch22.EuclideanUnitCubeBounds
