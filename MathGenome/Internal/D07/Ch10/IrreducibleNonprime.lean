import MathGenome.Internal.Specs.D07.Ch10.IrreducibleNonprime
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The example `3 ∈ ℤ[√(-5)]`, with its norm and explicit nonprimality witnesses. -/

namespace D07.Ch10.IrreducibleNonprime

open Specs.D07.Ch10.IrreducibleNonprime

@[simp] private theorem toComplex_re (z : R) : (toComplex z).re = (z.re : ℝ) := by
  simp [toComplex, root]

@[simp] private theorem toComplex_im (z : R) :
    (toComplex z).im = (z.im : ℝ) * Real.sqrt 5 := by
  simp [toComplex, root]

theorem complexRealization : ComplexRealization := by
  have hsqr : root * root = (-5 : ℂ) := by
    apply Complex.ext <;> norm_num [root, Complex.mul_re, Complex.mul_im,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  refine ⟨hsqr, ?_, ?_, ?_, ?_, ?_⟩
  · intro z w h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [toComplex_re] at hre
    simp only [toComplex_im] at him
    have hs : Real.sqrt 5 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    exact Zsqrtd.ext (Int.cast_injective hre)
      (Int.cast_injective (mul_right_cancel₀ hs him))
  · simp [toComplex]
  · intro z w
    let f : R →+* ℂ := Zsqrtd.lift ⟨root, by simpa using hsqr⟩
    change f (z + w) = f z + f w ∧ f (z * w) = f z * f w
    exact ⟨f.map_add z w, f.map_mul z w⟩
  · intro z
    apply Complex.ext <;> simp
  · ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z.re, z.im, rfl⟩
    · rintro ⟨a, b, rfl⟩
      exact ⟨⟨a, b⟩, rfl⟩

theorem normFormula : NormFormula := by
  intro a b
  simp only [Zsqrtd.norm]
  ring

theorem normMultiplicative : NormMultiplicative := Zsqrtd.norm_mul

theorem conjugateNorm : ConjugateNorm := by
  intro z
  exact ⟨(Zsqrtd.norm_eq_mul_conj z).symm,
    (mul_comm (star z) z).trans (Zsqrtd.norm_eq_mul_conj z).symm⟩

theorem normNonnegativeAndZero : NormNonnegativeAndZero := by
  exact ⟨Zsqrtd.norm_nonneg (by norm_num), Zsqrtd.norm_eq_zero_iff (by norm_num)⟩

theorem domain : Domain := by
  let : NoZeroDivisors R := ⟨fun {a b} hab => by
    have h : Zsqrtd.norm a * Zsqrtd.norm b = 0 := by
      rw [← Zsqrtd.norm_mul, hab, Zsqrtd.norm_zero]
    exact (mul_eq_zero.mp h).imp
      ((normNonnegativeAndZero.2 a).mp) ((normNonnegativeAndZero.2 b).mp)⟩
  exact NoZeroDivisors.to_isDomain R

private theorem norm_eq_coordinates (z : R) :
    Zsqrtd.norm z = z.re ^ 2 + 5 * z.im ^ 2 := normFormula z.re z.im

theorem normOne : NormOne := by
  intro z
  constructor
  · intro h
    rw [norm_eq_coordinates] at h
    have hb : z.im = 0 := by
      have hsq : z.im ^ 2 = 0 := by nlinarith [sq_nonneg z.re, sq_nonneg z.im]
      nlinarith [sq_nonneg z.im]
    have ha : z.re = 1 ∨ z.re = -1 := by
      rw [hb] at h
      have hz : (z.re - 1) * (z.re + 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp hz with hz | hz
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    rcases ha with ha | ha
    · left; ext <;> simp [ha, hb]
    · right; ext <;> simp [ha, hb]
  · rintro (rfl | rfl) <;> norm_num

theorem units : Units := by
  intro z
  exact (Zsqrtd.norm_eq_one_iff' (by norm_num) z).symm.trans (normOne z)

theorem conjugateInverse : ConjugateInverse := by
  intro z hz
  have hn : Zsqrtd.norm z = 1 := (Zsqrtd.norm_eq_one_iff' (by norm_num) z).mpr hz
  simpa [hn] using conjugateNorm z

theorem normThreeImpossible : NormThreeImpossible := by
  intro a b h
  have hb : b = 0 := by
    have hsq : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    nlinarith [sq_nonneg b]
  rw [hb] at h
  have ha : -2 ≤ a ∧ a ≤ 2 := by constructor <;> nlinarith
  obtain ⟨ha₁, ha₂⟩ := ha
  interval_cases a <;> norm_num at h

theorem threeIrreducible : ThreeIrreducible := by
  have hn : Zsqrtd.norm (3 : R) = 9 := by norm_num [Zsqrtd.norm]
  have hnu : ¬IsUnit (3 : R) := by
    intro h
    have := (Zsqrtd.norm_eq_one_iff' (by norm_num) (3 : R)).mpr h
    omega
  refine ⟨hnu, ?_⟩
  intro u v huv
  by_cases hu : IsUnit u
  · exact Or.inl hu
  by_cases hv : IsUnit v
  · exact Or.inr hv
  exfalso
  have hprod : Zsqrtd.norm u * Zsqrtd.norm v = 9 := by
    rw [← Zsqrtd.norm_mul, ← huv, hn]
  have hu0 : 0 ≤ Zsqrtd.norm u := normNonnegativeAndZero.1 u
  have hv0 : 0 ≤ Zsqrtd.norm v := normNonnegativeAndZero.1 v
  have hu1 : Zsqrtd.norm u ≠ 1 :=
    fun h => hu ((Zsqrtd.norm_eq_one_iff' (by norm_num) u).mp h)
  have hv1 : Zsqrtd.norm v ≠ 1 :=
    fun h => hv ((Zsqrtd.norm_eq_one_iff' (by norm_num) v).mp h)
  have hu2 : 2 ≤ Zsqrtd.norm u := by
    have hne : Zsqrtd.norm u ≠ 0 := by intro h; rw [h] at hprod; norm_num at hprod
    omega
  have hv2 : 2 ≤ Zsqrtd.norm v := by
    have hne : Zsqrtd.norm v ≠ 0 := by intro h; rw [h] at hprod; norm_num at hprod
    omega
  have hu4 : Zsqrtd.norm u ≤ 4 := by nlinarith
  have hu3 : Zsqrtd.norm u = 3 := by
    have hc : Zsqrtd.norm u = 2 ∨ Zsqrtd.norm u = 3 ∨ Zsqrtd.norm u = 4 := by omega
    rcases hc with h | h | h
    · rw [h] at hprod; omega
    · exact h
    · rw [h] at hprod; omega
  exact normThreeImpossible u.re u.im ((norm_eq_coordinates u).symm.trans hu3)

theorem integerDivisibility : IntegerDivisibility := Zsqrtd.intCast_dvd

theorem witnessProduct : WitnessProduct := by
  ext <;> norm_num [Zsqrtd.re_mul, Zsqrtd.im_mul]

theorem threeDividesProduct : ThreeDividesProduct := by
  unfold ThreeDividesProduct
  rw [witnessProduct]
  exact ⟨3, by norm_num⟩

theorem threeNotDividesFactors : ThreeNotDividesFactors := by
  constructor
  · intro h
    have h' := (integerDivisibility 3 _).mp h
    norm_num at h'
  · intro h
    have h' := (integerDivisibility 3 _).mp h
    norm_num at h'

theorem threeNotPrime : ThreeNotPrime := by
  intro hp
  exact (hp.dvd_or_dvd threeDividesProduct).elim
    threeNotDividesFactors.1 threeNotDividesFactors.2

end D07.Ch10.IrreducibleNonprime
