import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.SpecializationData
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationCoefficients

/-!
# Substitution and reduction of regular coefficients

Taylor expansion sends a denominator that is nonzero at the specified point to a
unit in the power-series ring. This gives the lift of a regular polynomial and
identifies its reduction with ordinary specialization.
-/

open scoped Polynomial

namespace GaloisFormalization.IG.SpecializationCoefficients

open SpecializationData
open Specs.GaloisFormalization.IG.SpecializationCoefficients

noncomputable section

abbrev regularSeries := @Specs.GaloisFormalization.IG.SpecializationCoefficients.regularSeries

abbrev polynomialLift := @Specs.GaloisFormalization.IG.SpecializationCoefficients.polynomialLift

abbrev laurentMap := @Specs.GaloisFormalization.IG.SpecializationCoefficients.laurentMap

theorem substitution_injective : SubstitutionInjective := by
  intro k _ ℓ _ _ a
  exact (substitution ℓ a).injective

theorem substitution_C : SubstitutionC := by
  intro k _ ℓ _ _ a c
  simpa only [RatFunc.algebraMap_eq_C, HahnSeries.algebraMap_apply',
    PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C] using (substitution ℓ a).commutes c

theorem substitution_div : SubstitutionDiv :=
  Specs.GaloisFormalization.IG.SpecializationCoefficients.substitution_div

private theorem substitution_polynomial {k : Type*} [Field k]
    (ℓ : Type*) [Field ℓ] [Algebra k ℓ] (a : k) (p : k[X]) :
    substitution ℓ a (algebraMap k[X] (RatFunc k) p) =
      powerToLaurent ℓ (polynomialSeries ℓ a p) := by
  simpa only [map_one, div_one] using substitution_div ℓ a p 1

theorem substitution_sub_C : SubstitutionSubC := by
  intro k _ ℓ _ _ a
  rw [← RatFunc.algebraMap_X, ← RatFunc.algebraMap_C, ← map_sub, substitution_polynomial]
  change powerToLaurent ℓ
    (PowerSeries.map (algebraMap k ℓ)
      (↑(Polynomial.taylorAlgHom a (Polynomial.X - Polynomial.C a)) : PowerSeries k)) = _
  rw [map_sub, Polynomial.taylorAlgHom_apply, Polynomial.taylorAlgHom_apply,
    Polynomial.taylor_X, Polynomial.taylor_C, add_sub_cancel_right, Polynomial.coe_X,
    PowerSeries.map_X]
  exact powerToLaurent_X ℓ

theorem regularAt_div : RegularAtDiv := by
  intro k _ a p q hq
  exact fun h =>
    hq (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (RatFunc.denom_div_dvd p q) h)

theorem fraction_specializes : FractionSpecializes := by
  intro k _ ℓ _ _ a p q hq
  refine ⟨polynomialSeries ℓ a p * (polynomialSeries ℓ a q)⁻¹,
    powerToLaurent_fraction ℓ a p q hq, ?_⟩
  rw [map_mul, PowerSeries.constantCoeff_inv, polynomialSeries_constantCoeff,
    polynomialSeries_constantCoeff, div_eq_mul_inv, map_mul, map_inv₀]

theorem powerToLaurent_regularSeries : PowerToLaurentRegularSeries :=
  Specs.GaloisFormalization.IG.SpecializationCoefficients.powerToLaurent_regularSeries

theorem constantCoeff_regularSeries : ConstantCoeffRegularSeries := by
  intro k _ ℓ _ _ a x
  change PowerSeries.constantCoeff
    (polynomialSeries ℓ a (x : RatFunc k).num * (polynomialSeries ℓ a (x : RatFunc k).denom)⁻¹) =
      algebraMap k ℓ (RatFunc.eval (RingHom.id k) a (x : RatFunc k))
  simp only [map_mul, PowerSeries.constantCoeff_inv, polynomialSeries_constantCoeff,
    RatFunc.eval, Polynomial.eval₂_id, div_eq_mul_inv, map_inv₀]

theorem polynomialLift_laurent : PolynomialLiftLaurent := by
  intro k _ ℓ _ _ a f hf
  apply Polynomial.ext
  intro n
  change (((regularPolynomial a f hf).map (regularSeries ℓ a)).map (powerToLaurent ℓ)).coeff n = _
  rw [Polynomial.coeff_map, Polynomial.coeff_map, powerToLaurent_regularSeries,
    Polynomial.coeff_map]
  exact congrArg (substitution ℓ a) (Polynomial.coeff_toSubring f (regularCoefficients a) _)

theorem polynomialLift_reduction : PolynomialLiftReduction := by
  intro k _ ℓ _ _ a f hf
  apply Polynomial.ext
  intro n
  change (((regularPolynomial a f hf).map (regularSeries ℓ a)).map
    PowerSeries.constantCoeff).coeff n =
      (((regularPolynomial a f hf).map (evalRegular a)).map (algebraMap k ℓ)).coeff n
  simp only [Polynomial.coeff_map, constantCoeff_regularSeries]

theorem polynomialLift_reduction_base : PolynomialLiftReductionBase := by
  intro k _ a f hf
  simpa only [Algebra.algebraMap_self, Polynomial.map_id] using
    polynomialLift_reduction k a f hf

theorem polynomialLift_monicDegree : PolynomialLiftMonicDegree := by
  intro k _ ℓ _ _ a f hf h
  have hreg : (regularPolynomial a f hf).Monic :=
    (Polynomial.monic_toSubring _ _ _).mpr h
  exact ⟨hreg.map _, (hreg.natDegree_map _).trans (Polynomial.natDegree_toSubring _ _ _)⟩

theorem specialize_monicDegree : SpecializeMonicDegree := by
  intro k _ a f hf h
  have hreg : (regularPolynomial a f hf).Monic :=
    (Polynomial.monic_toSubring _ _ _).mpr h
  exact ⟨hreg.map _, (hreg.natDegree_map _).trans (Polynomial.natDegree_toSubring _ _ _)⟩

@[simp]
theorem laurentMap_coeff {R S : Type*} [CommRing R] [CommRing S]
    (g : R →+* S) (x : LaurentSeries R) (n : ℤ) :
    (laurentMap g x).coeff n = g (x.coeff n) :=
  rfl

private theorem laurentMap_powerToLaurent {ℓ m : Type*} [Field ℓ] [Field m]
    (g : ℓ →+* m) (F : PowerSeries ℓ) :
    laurentMap g (powerToLaurent ℓ F) = powerToLaurent m (PowerSeries.map g F) := by
  ext n
  change (laurentMap g (F : LaurentSeries ℓ)).coeff n =
    ((PowerSeries.map g F : PowerSeries m) : LaurentSeries m).coeff n
  simp only [laurentMap_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_map, apply_ite g,
    map_zero]

private theorem polynomialSeries_map {k : Type*} [Field k] (ℓ m : Type*)
    [Field ℓ] [Field m] [Algebra k ℓ] [Algebra k m] [Algebra ℓ m] [IsScalarTower k ℓ m]
    (a : k) (p : k[X]) :
    PowerSeries.map (algebraMap ℓ m) (polynomialSeries ℓ a p) = polynomialSeries m a p := by
  ext n
  change PowerSeries.coeff n
    (PowerSeries.map (algebraMap ℓ m) (PowerSeries.map (algebraMap k ℓ)
      (↑(Polynomial.taylor a p) : PowerSeries k))) =
    PowerSeries.coeff n (PowerSeries.map (algebraMap k m)
      (↑(Polynomial.taylor a p) : PowerSeries k))
  simp only [PowerSeries.coeff_map, Polynomial.coeff_coe]
  exact (IsScalarTower.algebraMap_apply k ℓ m _).symm

theorem substitution_naturality : SubstitutionNaturality := by
  intro k _ ℓ _ _ m _ _ _ _ a
  apply RingHom.ext
  intro x
  change laurentMap (algebraMap ℓ m) (substitution ℓ a x) = substitution m a x
  rw [← RatFunc.num_div_denom x, substitution_div, substitution_div,
    map_div₀, laurentMap_powerToLaurent, laurentMap_powerToLaurent,
    polynomialSeries_map, polynomialSeries_map]

theorem regularSeries_naturality : RegularSeriesNaturality := by
  intro k _ ℓ _ _ m _ _ _ _ a
  apply RingHom.ext
  intro x
  apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := m))
  change powerToLaurent m (PowerSeries.map (algebraMap ℓ m) (regularSeries ℓ a x)) =
    powerToLaurent m (regularSeries m a x)
  rw [← laurentMap_powerToLaurent, powerToLaurent_regularSeries, powerToLaurent_regularSeries]
  exact DFunLike.congr_fun (substitution_naturality ℓ m a) (x : RatFunc k)

theorem polynomialLift_naturality : PolynomialLiftNaturality := by
  intro k _ ℓ _ _ m _ _ _ _ a f hf
  change (((regularPolynomial a f hf).map (regularSeries ℓ a)).map
    (PowerSeries.map (algebraMap ℓ m))) = (regularPolynomial a f hf).map (regularSeries m a)
  rw [Polynomial.map_map, regularSeries_naturality]

end

end GaloisFormalization.IG.SpecializationCoefficients
