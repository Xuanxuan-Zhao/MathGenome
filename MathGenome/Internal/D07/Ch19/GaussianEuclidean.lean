import MathGenome.Internal.Specs.D07.Ch19.GaussianEuclidean
import MathGenome.Internal.D07.Ch10.EuclideanPid
import MathGenome.Internal.D07.Ch10.PidUfd
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Gaussian norm, units, nearest-coordinate division, and its PID/UFD consequences. -/

namespace D07.Ch19.GaussianEuclidean

open Specs.D07.Ch19.GaussianEuclidean

theorem complex_embedding : ComplexEmbedding := by
  refine ⟨GaussianInt.toComplex_injective, ?_⟩
  intro c
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z.re, z.im, GaussianInt.toComplex_def z⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨⟨a, b⟩, GaussianInt.toComplex_def' a b⟩

theorem norm_properties : NormProperties := by
  intro z
  refine ⟨?_, GaussianInt.norm_nonneg z, GaussianInt.norm_eq_zero,
    GaussianInt.norm_pos, Zsqrtd.norm_eq_mul_conj z,
    GaussianInt.intCast_real_norm z, GaussianInt.toComplex_star z⟩
  simp [Zsqrtd.norm, pow_two]

theorem norm_multiplicative : NormMultiplicative :=
  Zsqrtd.norm_mul

theorem units : Units := by
  intro z
  have hu : IsUnit z ↔ z.norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by decide : (-1 : ℤ) ≤ 0) z).symm
  refine ⟨hu, ?_, ?_⟩
  · constructor
    · intro hz
      have hn : z.re ^ 2 + z.im ^ 2 = 1 := (norm_properties z).1.symm.trans hz
      have hre : -1 ≤ z.re ∧ z.re ≤ 1 := by
        constructor <;> nlinarith [sq_nonneg z.im]
      have him : -1 ≤ z.im ∧ z.im ≤ 1 := by
        constructor <;> nlinarith [sq_nonneg z.re]
      rcases z with ⟨a, b⟩
      dsimp at hn hre him
      rcases hre with ⟨ha, ha'⟩
      rcases him with ⟨hb, hb'⟩
      interval_cases a <;> interval_cases b <;>
        norm_num at hn <;> norm_num [Zsqrtd.ext_iff]
    · rintro (rfl | rfl | rfl | rfl) <;> norm_num [Zsqrtd.norm]
  · intro hz
    have hn := (norm_properties z).2.2.2.2.1
    rw [hu.mp hz, Int.cast_one] at hn
    exact ⟨hn.symm, by simpa [mul_comm] using hn.symm⟩

theorem quotient_rounding : QuotientRounding := by
  intro z w
  dsimp
  have hre : (z / w).re = round ((z : ℂ) / (w : ℂ)).re := by
    apply Int.cast_injective (α := ℝ)
    simpa only [GaussianInt.intCast_re] using GaussianInt.toComplex_re_div z w
  have him : (z / w).im = round ((z : ℂ) / (w : ℂ)).im := by
    apply Int.cast_injective (α := ℝ)
    simpa only [GaussianInt.intCast_im] using GaussianInt.toComplex_im_div z w
  have hre' : |((z : ℂ) / (w : ℂ)).re - ((z / w).re : ℝ)| ≤ 1 / 2 := by
    rw [hre]
    exact abs_sub_round _
  have him' : |((z : ℂ) / (w : ℂ)).im - ((z / w).im : ℝ)| ≤ 1 / 2 := by
    rw [him]
    exact abs_sub_round _
  refine ⟨hre, him, hre', him', ?_⟩
  have h := GaussianInt.normSq_le_normSq_of_re_le_of_im_le
    (x := (z : ℂ) / (w : ℂ) - ((z / w : GaussianInt) : ℂ))
    (y := (1 / 2 + 1 / 2 * Complex.I : ℂ))
    (by simpa using hre') (by simpa using him')
  norm_num [Complex.normSq] at h ⊢
  exact h

theorem division_estimate : DivisionEstimate := by
  intro z w hw
  dsimp
  have hwC : (w : ℂ) ≠ 0 := GaussianInt.toComplex_eq_zero.not.mpr hw
  have hn := (quotient_rounding z w).2.2.2.2
  have heq : ((z - z / w * w).norm : ℝ) = (w.norm : ℝ) *
      Complex.normSq ((z : ℂ) / (w : ℂ) - ((z / w : GaussianInt) : ℂ)) := by
    rw [GaussianInt.intCast_real_norm, GaussianInt.intCast_real_norm,
      ← Complex.normSq_mul]
    congr 1
    simp only [map_sub, map_mul, mul_sub, mul_div_cancel₀ _ hwC]
    ring
  have hle : ((z - z / w * w).norm : ℝ) ≤ (w.norm : ℝ) / 2 := by
    rw [heq]
    have hw0 : (0 : ℝ) ≤ (w.norm : ℝ) := by
      exact_mod_cast GaussianInt.norm_nonneg w
    nlinarith
  refine ⟨by ring, heq, hle, ?_⟩
  have hwpos : (0 : ℝ) < (w.norm : ℝ) := by
    exact_mod_cast GaussianInt.norm_pos.mpr hw
  have hlt : ((z - z / w * w).norm : ℝ) < (w.norm : ℝ) := by linarith
  exact_mod_cast hlt

theorem norm_euclidean_data : NormEuclideanData := by
  refine ⟨{
    smaller := fun a b => a.norm.natAbs < b.norm.natAbs
    wellFounded := (measure (fun a : GaussianInt => a.norm.natAbs)).wf
    quotient := fun a b => a / b
    remainder := fun a b => a - (a / b) * b
    division := fun a b hb => (division_estimate a b hb).1
    decrease := ?_ }, rfl, rfl, rfl⟩
  intro a b hb
  right
  apply Int.ofNat_lt.mp
  simpa only [GaussianInt.abs_natCast_norm] using (division_estimate a b hb).2.2.2

theorem euclidean : Euclidean := by
  obtain ⟨d, _⟩ := norm_euclidean_data
  exact (D07.Ch10.EuclideanDefinition.divisionDataCharacterization GaussianInt).mp ⟨d⟩

theorem principal_ideal_domain : PrincipalIdealDomain :=
  D07.Ch10.EuclideanPid.euclidean_implies_pid GaussianInt euclidean

theorem unique_factorization : UniqueFactorization :=
  D07.Ch10.PidUfd.pid_is_ufd GaussianInt principal_ideal_domain

end D07.Ch19.GaussianEuclidean
