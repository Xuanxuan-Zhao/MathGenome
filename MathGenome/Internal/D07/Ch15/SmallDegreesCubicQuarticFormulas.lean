import MathGenome.Internal.Specs.D07.Ch15.SmallDegreesCubicQuarticFormulas
import MathGenome.Internal.D07.Ch15.RootsUnity
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

namespace D07.Ch15.SmallDegreesCubicQuarticFormulas

open Polynomial
open Specs.D07.Ch15.SmallDegreesCubicQuarticFormulas
universe u v

/-- Completing the square as a polynomial identity, without distinct-root assumptions. -/
theorem quadratic_formula : QuadraticFormula.{u} := by
  intro F _ _ a b c s ha hs
  let r₁ := (-b + s) / (2 * a)
  let r₂ := (-b - s) / (2 * a)
  have hsum : a * (r₁ + r₂) = -b := by
    dsimp [r₁, r₂]
    field_simp
    ring
  have hprod : a * r₁ * r₂ = c := by
    dsimp [r₁, r₂]
    field_simp
    linear_combination -hs
  change C a * X ^ 2 + C b * X + C c = C a * (X - C r₁) * (X - C r₂)
  calc
    _ = C a * X ^ 2 - C (a * (r₁ + r₂)) * X + C (a * r₁ * r₂) := by
      rw [hsum, hprod, C_neg]
      ring
    _ = _ := by
      simp only [C_mul, C_add]
      ring

theorem quadratic_choices : QuadraticChoices.{u} := by
  intro F _ _ _ a b c
  exact IsAlgClosed.exists_pow_nat_eq _ (by decide)

theorem cubic_depression : CubicDepression.{u} := by
  intro F _ _ a b c y
  ring

theorem cardano_choices : CardanoChoices.{u} := by
  intro F _ _ _ p q
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (q ^ 2 / 4 + p ^ 3 / 27) (by decide : 0 < 2)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (-q / 2 + d) (by decide : 0 < 3)
  obtain ⟨ζ, hζ⟩ := RootsUnity.primitive_root_exists F F 3 (by decide) (by norm_num)
  exact ⟨d, u, ζ, hd, hu, hζ⟩

theorem cardano_relations : CardanoRelations.{u} := by
  intro F _ _ p q d u hd hu hne
  dsimp
  have hv : (-p / (3 * u)) ^ 3 = -q / 2 - d := by
    field_simp
    linear_combination 54 * hd + (54 * d + 27 * q) * hu
  refine ⟨hv, ?_, ?_⟩
  · rw [hv, hu]
    ring
  · field_simp

/-- Exact order three gives the two coefficient identities needed for Cardano. -/
theorem primitive_cube_relations {F : Type u} [Field F] (ζ : F)
    (hζ : IsPrimitiveRoot ζ 3) : ζ ^ 3 = 1 ∧ ζ ^ 2 = -ζ - 1 := by
  refine ⟨hζ.pow_eq_one, ?_⟩
  have hne : ζ - 1 ≠ 0 := sub_ne_zero.mpr (hζ.ne_one (by decide))
  have hprod : (ζ - 1) * (ζ ^ 2 + ζ + 1) = 0 := by
    linear_combination hζ.pow_eq_one
  have hz := (mul_eq_zero.mp hprod).resolve_left hne
  linear_combination hz

/-- A scalar factorization used to avoid imposing distinctness on the roots. -/
theorem cubic_product {F : Type u} [Field F] (u v ζ y : F)
    (hζ : IsPrimitiveRoot ζ 3) :
    (y - (u + v)) * (y - (ζ * u + ζ ^ 2 * v)) *
      (y - (ζ ^ 2 * u + ζ * v)) = y ^ 3 - 3 * u * v * y - (u ^ 3 + v ^ 3) := by
  obtain ⟨h3, h2⟩ := primitive_cube_relations ζ hζ
  have h4 : ζ ^ 4 = ζ := by rw [show 4 = 3 + 1 from rfl, pow_succ, h3, one_mul]
  ring_nf
  simp only [h2, h3, h4]
  ring

theorem cubic_factorization : CubicFactorization.{u} := by
  intro F _ _ p q u v ζ hζ hsum hmul
  apply Polynomial.funext
  intro y
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub]
  rw [cubic_product u v ζ y hζ, hsum, hmul]
  ring

theorem cubic_indexing : CubicIndexing.{u} := by
  intro F _ _ u v ζ hζ j
  have h3 := hζ.pow_eq_one
  have hi : ζ⁻¹ = ζ ^ 2 := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ'] using h3
  have hi2 : (ζ ^ 2)⁻¹ = ζ := by
    apply inv_eq_of_mul_eq_one_right
    simpa only [← pow_succ] using h3
  fin_cases j <;> simp [zpow_neg, hi, hi2]

theorem cardano_factorization : CardanoFactorization.{u} := by
  intro F _ _ p q d u ζ hd hu hne hζ
  have hv := cardano_relations F p q d u hd hu hne
  exact cubic_factorization F p q u _ ζ hζ hv.2.1 hv.2.2

theorem cardano_indexed_factorization : CardanoIndexedFactorization.{u} := by
  intro F _ _ p q d u ζ hd hu hne hζ
  dsimp
  rw [cardano_factorization F p q d u ζ hd hu hne hζ]
  conv_rhs => arg 2; ext j; rw [cubic_indexing F u (-p / (3 * u)) ζ hζ j]
  simp [Fin.prod_univ_succ]
  ring

theorem cardano_zero_branch : CardanoZeroBranch.{u} := by
  intro F _ _ p q d u ζ hd hu hz hζ
  subst u
  simp only [zero_pow (by decide : 3 ≠ 0)] at hu
  have hds : d = q / 2 := by linear_combination -hu
  rw [hds] at hd
  have hp3 : p ^ 3 = 0 := by
    linear_combination -27 * hd
  have hp : p = 0 := (pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hp3
  refine ⟨hp, ?_⟩
  intro w hw
  simpa only [add_zero, mul_zero] using
    cubic_factorization F p q w 0 ζ hζ (by simpa using hw) (by simp [hp])

theorem cube_root_choices : CubeRootChoices.{u} := by
  intro F _ _ _ q
  exact IsAlgClosed.exists_pow_nat_eq _ (by decide)

theorem quartic_depression : QuarticDepression.{u} := by
  intro F _ _ a b c d y
  ring

theorem biquadratic_choices : BiquadraticChoices.{u} := by
  intro F _ _ _ p r
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (p ^ 2 - 4 * r) (by decide : 0 < 2)
  obtain ⟨s₁, h₁⟩ := IsAlgClosed.exists_pow_nat_eq ((-p + t) / 2) (by decide : 0 < 2)
  obtain ⟨s₂, h₂⟩ := IsAlgClosed.exists_pow_nat_eq ((-p - t) / 2) (by decide : 0 < 2)
  exact ⟨t, s₁, s₂, ht, h₁, h₂⟩

theorem biquadratic_factorization : BiquadraticFactorization.{u} := by
  intro F _ _ p r t s₁ s₂ ht h₁ h₂
  apply Polynomial.funext
  intro y
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub]
  calc
    y ^ 4 + p * y ^ 2 + r =
        (y ^ 2 - (-p + t) / 2) * (y ^ 2 - (-p - t) / 2) := by
      linear_combination ht / 4
    _ = (y ^ 2 - s₁ ^ 2) * (y ^ 2 - s₂ ^ 2) := by rw [h₁, h₂]
    _ = _ := by ring

theorem resolvent_exists : ResolventExists.{u} := by
  intro F _ _ _ p q r
  let f : Polynomial F := C 8 * X ^ 3 + C (-4 * p) * X ^ 2 + C (-8 * r) * X + C (4 * p * r - q ^ 2)
  have hd : f.degree = 3 := degree_cubic (by norm_num : (8 : F) ≠ 0)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root f (by rw [hd]; decide)
  have he : 8 * z ^ 3 + (-4 * p) * z ^ 2 + (-8 * r) * z + (4 * p * r - q ^ 2) = 0 := by
    simpa [f, Polynomial.IsRoot] using hz
  refine ⟨z, ?_⟩
  linear_combination -he

/-- The nonzero linear coefficient prevents a zero denominator in Ferrari. -/
theorem ferrari_nonzero {F : Type u} [Field F] (p q r z : F)
    (hq : q ≠ 0) (hz : q ^ 2 = 4 * (2 * z - p) * (z ^ 2 - r)) :
    2 * z - p ≠ 0 := by
  intro he
  rw [he, mul_zero, zero_mul] at hz
  exact hq ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hz)

theorem ferrari_choices : FerrariChoices.{u} := by
  intro F _ _ _ p q r z hq hz
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (2 * z - p) (by decide : 0 < 2)
  refine ⟨u, hu, ?_⟩
  intro h
  apply ferrari_nonzero p q r z hq hz
  simpa [h] using hu.symm

theorem ferrari_relations : FerrariRelations.{u} := by
  intro F _ _ p q r z u hq hz hu
  have hne := ferrari_nonzero p q r z hq hz
  have hune : u ≠ 0 := by
    intro h
    apply hne
    simpa [h] using hu.symm
  refine ⟨hne, hune, ?_, ?_⟩
  · field_simp
    linear_combination hz - 4 * (z ^ 2 - r) * hu
  · field_simp

theorem ferrari_factorization : FerrariFactorization.{u} := by
  intro F _ _ p q r z u hq hz hu
  obtain ⟨_, _, hv, huv⟩ := ferrari_relations F p q r z u hq hz hu
  dsimp at hv huv ⊢
  constructor <;> apply Polynomial.funext <;> intro y <;>
    simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub]
  · linear_combination y ^ 2 * hu + y * huv + hv
  · linear_combination y ^ 2 * hu + y * huv + hv

theorem ferrari_quadratic_choices : FerrariQuadraticChoices.{u} := by
  intro F _ _ _ z u v
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (u ^ 2 - 4 * (z - v)) (by decide : 0 < 2)
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (u ^ 2 - 4 * (z + v)) (by decide : 0 < 2)
  exact ⟨s, t, hs, ht⟩

theorem ferrari_four_roots : FerrariFourRoots.{u} := by
  intro F _ _ p q r z u s t hq hz hu
  dsimp
  intro hs ht
  have h₁ := quadratic_formula F 1 (-u) (z - -q / (2 * u)) s (by norm_num)
    (by simpa only [neg_sq, one_mul, mul_one] using hs)
  have h₂ := quadratic_formula F 1 u (z + -q / (2 * u)) t (by norm_num)
    (by simpa only [one_mul, mul_one] using ht)
  have hf := (ferrari_factorization F p q r z u hq hz hu).2
  simp only [C_1, one_mul, mul_one, neg_neg, C_neg] at h₁ h₂
  rw [show X ^ 2 - C u * X + C (z - -q / (2 * u)) =
      X ^ 2 + -C u * X + C (z - -q / (2 * u)) by ring] at hf
  rw [h₁, h₂] at hf
  exact hf.trans (by ring)

theorem cubic_in_algebraic_closure : CubicInAlgebraicClosure.{u, v} := by
  intro K Ω _ _ _ _ _ p q
  let : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  dsimp
  obtain ⟨d, u, ζ, hd, hu, hζ⟩ := cardano_choices Ω (algebraMap K Ω p) (algebraMap K Ω q)
  refine ⟨d, u, ζ, hd, hu, hζ, ?_, ?_⟩
  · intro hne
    exact cardano_indexed_factorization Ω _ _ d u ζ hd hu hne hζ
  · intro hz
    have h := cardano_zero_branch Ω (algebraMap K Ω p) (algebraMap K Ω q) d u ζ hd hu hz hζ
    refine ⟨?_, ?_⟩
    · apply (algebraMap K Ω).injective
      simpa only [map_zero] using h.1
    · obtain ⟨w, hw⟩ := cube_root_choices Ω (algebraMap K Ω q)
      exact ⟨w, hw, h.2 w hw⟩

theorem quartic_in_algebraic_closure : QuarticInAlgebraicClosure.{u, v} := by
  intro K Ω _ _ _ _ _ p q r
  let : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  let : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  dsimp
  constructor
  · intro hq
    obtain ⟨t, s₁, s₂, ht, h₁, h₂⟩ := biquadratic_choices Ω (algebraMap K Ω p) (algebraMap K Ω r)
    refine ⟨t, s₁, s₂, ht, h₁, h₂, ?_⟩
    simpa only [hq, map_zero, C_0, zero_mul, add_zero] using
      biquadratic_factorization Ω _ _ t s₁ s₂ ht h₁ h₂
  · intro hq
    have hq' : algebraMap K Ω q ≠ 0 := by simpa only [ne_eq, map_eq_zero] using hq
    obtain ⟨z, hz⟩ := resolvent_exists Ω (algebraMap K Ω p) (algebraMap K Ω q) (algebraMap K Ω r)
    obtain ⟨u, hu, hune⟩ := ferrari_choices Ω _ _ _ z hq' hz
    obtain ⟨s, t, hs, ht⟩ := ferrari_quadratic_choices Ω z u (-(algebraMap K Ω q) / (2 * u))
    exact ⟨z, u, s, t, hz, hu, hune, hs, ht,
      ferrari_four_roots Ω _ _ _ z u s t hq' hz hu hs ht⟩

end D07.Ch15.SmallDegreesCubicQuarticFormulas
