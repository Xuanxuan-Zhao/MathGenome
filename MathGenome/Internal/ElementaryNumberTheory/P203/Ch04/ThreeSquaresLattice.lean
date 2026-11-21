import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch04.ThreeSquaresLattice
import MathGenome.Internal.ElementaryNumberTheory.P203.Ch04.LatticeBall
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
namespace P203.Ch04
open MeasureTheory P203Specs.Ch04

lemma threeSquaresMatrix_apply (n b : ℕ) (u v r s t : ℤ) :
    WithLp.toLp 2 ((threeSquaresMatrix n b u v).mulVec
      (fun i ↦ (![r, s, t] i : ℝ))) = threeSquaresPoint n b u v r s t := by
  ext i
  fin_cases i <;>
    simp [threeSquaresMatrix, threeSquaresPoint, latticeX, latticeW,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;> try ring1
  calc
    _ = ((b : ℝ) / Real.sqrt b) * r +
        (u : ℝ) * (Real.sqrt b)⁻¹ * s := by
          rw [Real.div_sqrt]
          simp only [div_eq_mul_inv]
    _ = _ := by ring

lemma threeSquaresMatrix_det (n b : ℕ) (u v : ℤ) (hb : 0 < b) :
    (threeSquaresMatrix n b u v).det =
      (n : ℝ) * Real.sqrt b * Real.sqrt ((n : ℝ) / b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hs := Real.sq_sqrt hbR.le
  have hs0 : Real.sqrt (b : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hbR)
  have hbdiv : (b : ℝ) / Real.sqrt b = Real.sqrt b :=
    (div_eq_iff hs0).2 (by nlinarith)
  simp [threeSquaresMatrix, Matrix.det_fin_three, hbdiv]

lemma threeSquares_sqrt_product (n b : ℕ) (hb : 0 < b) :
    Real.sqrt (b : ℝ) * Real.sqrt ((n : ℝ) / b) = Real.sqrt n := by
  rw [← Real.sqrt_mul (by positivity)]
  congr 1
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  field_simp

lemma threeSquares_rpow (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * Real.sqrt n := by
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add (by positivity), Real.rpow_one, ← Real.sqrt_eq_rpow]

lemma threeSquares_ball_volume (n : ℕ) (hn : 0 < n) :
    volume.real (Metric.ball (0 : EuclideanSpace ℝ (Fin 3))
      (Real.sqrt (2 * (n : ℝ)))) =
      (8 * Real.sqrt 2 * Real.pi / 3) * (n : ℝ) ^ (3 / 2 : ℝ) := by
  rw [Measure.real, EuclideanSpace.volume_ball_fin_three,
    ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity),
    threeSquares_rpow n hn, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ n)
  calc
    _ = (Real.sqrt 2 ^ 2) * (Real.sqrt (n : ℝ) ^ 2) *
      (4 * Real.sqrt 2 * Real.pi / 3 * Real.sqrt n) := by ring
    _ = _ := by rw [h2, hn2]; ring

theorem threeSquares_lattice_geometry : threeSquaresLatticeGeometry := by
  intro n b u v hn hb
  have hd := threeSquaresMatrix_det n b u v hb
  have he : (threeSquaresMatrix n b u v).det = (n : ℝ) * Real.sqrt n := by
    rw [hd, mul_assoc, threeSquares_sqrt_product n b hb]
  have hp : 0 < (threeSquaresMatrix n b u v).det := by rw [he]; positivity
  refine ⟨threeSquaresMatrix_apply n b u v, hd, he, hp, ?_,
    threeSquares_ball_volume n hn, ?_⟩
  · rw [abs_of_pos hp, he, threeSquares_rpow n hn]
  · rw [threeSquares_ball_volume n hn]
    have hs : 1 < Real.sqrt (2 : ℝ) := by
      have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      have := Real.sqrt_nonneg (2 : ℝ)
      nlinarith
    have hpi := Real.pi_gt_three
    have hc : 8 < 8 * Real.sqrt 2 * Real.pi / 3 := by nlinarith
    exact mul_lt_mul_of_pos_right hc (Real.rpow_pos_of_pos (by positivity) _)

lemma latticeS_relation (n b : ℕ) (u r s : ℤ)
    (hu : (b : ℤ) ∣ u ^ 2 + n) :
    (b : ℤ) * latticeS n b u r s = latticeW b u r s ^ 2 + n * s ^ 2 := by
  have hq := Int.mul_ediv_cancel' hu
  dsimp [latticeS, latticeW]
  calc
    _ = (b : ℤ) ^ 2 * r ^ 2 + 2 * b * u * r * s +
        (b * ((u ^ 2 + n) / b)) * s ^ 2 := by ring
    _ = _ := by rw [hq]; ring

lemma lattice_norm_dvd (n b : ℕ) (u v r s t : ℤ)
    (hcop : n.Coprime b) (hu : (b : ℤ) ∣ u ^ 2 + n)
    (hv : (n : ℤ) ∣ (b : ℤ) * v ^ 2 + 1) :
    (n : ℤ) ∣ latticeX n b u v r s t ^ 2 + latticeS n b u r s := by
  apply Int.dvd_of_dvd_mul_right_of_gcd_one (b := (b : ℤ))
  · obtain ⟨k, hk⟩ := hv
    refine ⟨k * latticeW b u r s ^ 2 +
      b * (2 * v * latticeW b u r s * t + n * t ^ 2) + s ^ 2, ?_⟩
    dsimp only [latticeX]
    linear_combination (latticeW b u r s ^ 2) * hk + latticeS_relation n b u r s hu
  · simpa only [Int.gcd_natCast_natCast] using hcop

lemma latticeS_real (n b : ℕ) (u r s : ℤ) (hb : 0 < b)
    (hu : (b : ℤ) ∣ u ^ 2 + n) :
    (latticeS n b u r s : ℝ) =
      ((latticeW b u r s : ℝ) ^ 2 + n * (s : ℝ) ^ 2) / b ∧
    (latticeS n b u r s : ℝ) =
      ((latticeW b u r s : ℝ) / Real.sqrt b) ^ 2 +
      (Real.sqrt ((n : ℝ) / b) * s) ^ 2 := by
  have hb0 : (b : ℝ) ≠ 0 := by positivity
  have hrel : (b : ℝ) * (latticeS n b u r s : ℝ) =
      (latticeW b u r s : ℝ) ^ 2 + n * (s : ℝ) ^ 2 := by
    exact_mod_cast latticeS_relation n b u r s hu
  have hfrac : (latticeS n b u r s : ℝ) =
      ((latticeW b u r s : ℝ) ^ 2 + n * (s : ℝ) ^ 2) / b :=
    (eq_div_iff hb0).2 (by linarith)
  refine ⟨hfrac, ?_⟩
  rw [hfrac, div_pow, mul_pow, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)]
  field_simp

theorem threeSquares_lattice : threeSquaresLattice := by
  intro n b u v hn hb hcop hu hv
  obtain ⟨happly, hd, he, hp, habs, hvol, hvolgt⟩ :=
    threeSquares_lattice_geometry n b u v hn hb
  obtain ⟨z, hz0, hzball⟩ := minkowski_ball (threeSquaresMatrix n b u v)
    (ne_of_gt hp) (Real.sqrt (2 * (n : ℝ))) (by rwa [habs])
  have hzeta : z = ![z 0, z 1, z 2] := by ext i; fin_cases i <;> rfl
  rw [hzeta, happly] at hz0 hzball
  let r := z 0
  let s := z 1
  let t := z 2
  let S := latticeS n b u r s
  let X := latticeX n b u v r s t
  let p := threeSquaresPoint n b u v r s t
  have hS := latticeS_real n b u r s hb hu
  have hSn : (S : ℝ) = (p 1) ^ 2 + (p 2) ^ 2 := hS.2
  have hnorm : ‖p‖ ^ 2 = ((X ^ 2 + S : ℤ) : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    push_cast
    change (X : ℝ) ^ 2 + (p 1) ^ 2 + (p 2) ^ 2 = (X : ℝ) ^ 2 + S
    rw [hSn]
    ring
  have hposR : (0 : ℝ) < ((X ^ 2 + S : ℤ) : ℝ) := by
    rw [← hnorm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hz0)
  have hltR : (((X ^ 2 + S : ℤ) : ℝ)) < 2 * (n : ℝ) := by
    have hm : ‖p‖ < Real.sqrt (2 * (n : ℝ)) := by
      simpa only [Metric.mem_ball, dist_zero_right] using hzball
    rw [← hnorm, ← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * n)]
    exact (sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).2 hm
  have hpos : 0 < X ^ 2 + S := by exact_mod_cast hposR
  have hlt : X ^ 2 + S < 2 * (n : ℤ) := by exact_mod_cast hltR
  have hdvd : (n : ℤ) ∣ X ^ 2 + S := lattice_norm_dvd n b u v r s t hcop hu hv
  have heq : X ^ 2 + S = n := by
    obtain ⟨k, hk⟩ := hdvd
    have hnZ : (0 : ℤ) < n := by exact_mod_cast hn
    have hkpos : 0 < k := by nlinarith
    have hklt : k < 2 := by nlinarith
    have : k = 1 := by omega
    simpa [this] using hk
  have hSnonneg : 0 ≤ S := by
    have : (0 : ℝ) ≤ S := by rw [hSn]; positivity
    exact_mod_cast this
  refine ⟨r, s, t, hz0, hzball, rfl, hSn, hS.1, hdvd, hpos, hlt, heq,
    hSnonneg, ?_, latticeS_relation n b u r s hu⟩
  have := sq_nonneg X
  omega

end P203.Ch04
