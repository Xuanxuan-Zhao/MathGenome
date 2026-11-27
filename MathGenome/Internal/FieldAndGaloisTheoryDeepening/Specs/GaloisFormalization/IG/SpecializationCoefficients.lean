import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationData
import Mathlib.RingTheory.PowerSeries.Inverse

open scoped Polynomial

namespace Specs.GaloisFormalization.IG.SpecializationCoefficients

open SpecializationData

noncomputable section

universe uk uℓ um

variable {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]

theorem polynomialSeries_constantCoeff (a : k) (p : k[X]) :
    PowerSeries.constantCoeff (polynomialSeries ℓ a p) = algebraMap k ℓ (p.eval a) := by
  change algebraMap k ℓ ((Polynomial.taylor a p).coeff 0) = _
  rw [Polynomial.taylor_coeff_zero]

theorem substitution_div (a : k) (p q : k[X]) :
    substitution ℓ a (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q) =
      powerToLaurent ℓ (polynomialSeries ℓ a p) / powerToLaurent ℓ (polynomialSeries ℓ a q) := by
  unfold substitution
  exact RatFunc.liftAlgHom_apply_div _ _ _ _

theorem powerToLaurent_fraction (a : k) (p q : k[X]) (hq : q.eval a ≠ 0) :
    powerToLaurent ℓ (polynomialSeries ℓ a p * (polynomialSeries ℓ a q)⁻¹) =
      substitution ℓ a (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q) := by
  have hq₀ : PowerSeries.constantCoeff (polynomialSeries ℓ a q) ≠ 0 := by
    rw [polynomialSeries_constantCoeff]
    exact map_ne_zero (algebraMap k ℓ) |>.mpr hq
  have hq₁ : powerToLaurent ℓ ((polynomialSeries ℓ a q)⁻¹) *
      powerToLaurent ℓ (polynomialSeries ℓ a q) = 1 := by
    rw [← map_mul, PowerSeries.inv_mul_cancel _ hq₀, map_one]
  rw [substitution_div, eq_div_iff (right_ne_zero_of_mul (hq₁.trans_ne one_ne_zero)),
    map_mul, mul_assoc, hq₁, mul_one]

private def expand (a : k) (x : regularCoefficients a) : PowerSeries ℓ :=
  polynomialSeries ℓ a (x : RatFunc k).num * (polynomialSeries ℓ a (x : RatFunc k).denom)⁻¹

private theorem powerToLaurent_expand (a : k) (x : regularCoefficients a) :
    powerToLaurent ℓ (expand ℓ a x) = substitution ℓ a (x : RatFunc k) := by
  unfold expand
  rw [powerToLaurent_fraction ℓ a _ _ x.property, RatFunc.num_div_denom]

/-- Expand a regular rational function as the quotient of the Taylor series of its
reduced numerator and denominator. -/
def regularSeries (a : k) : regularCoefficients a →+* PowerSeries ℓ where
  toFun := expand ℓ a
  map_zero' := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by
    change powerToLaurent ℓ (expand ℓ a 0) = powerToLaurent ℓ 0
    simp only [powerToLaurent_expand, ZeroMemClass.coe_zero, map_zero])
  map_one' := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by
    change powerToLaurent ℓ (expand ℓ a 1) = powerToLaurent ℓ 1
    simp only [powerToLaurent_expand, OneMemClass.coe_one, map_one])
  map_add' x y := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by
    change powerToLaurent ℓ (expand ℓ a (x + y)) =
      powerToLaurent ℓ (expand ℓ a x + expand ℓ a y)
    rw [map_add, powerToLaurent_expand, powerToLaurent_expand, powerToLaurent_expand]
    exact map_add (substitution ℓ a) _ _)
  map_mul' x y := HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by
    change powerToLaurent ℓ (expand ℓ a (x * y)) =
      powerToLaurent ℓ (expand ℓ a x * expand ℓ a y)
    rw [map_mul, powerToLaurent_expand, powerToLaurent_expand, powerToLaurent_expand]
    exact map_mul (substitution ℓ a) _ _)

theorem powerToLaurent_regularSeries (a : k) (x : regularCoefficients a) :
    powerToLaurent ℓ (regularSeries ℓ a x) = substitution ℓ a (x : RatFunc k) :=
  powerToLaurent_expand ℓ a x

/-- The polynomial (f(a+u,X)) over the power-series ring. -/
def polynomialLift (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f) :
    (PowerSeries ℓ)[X] :=
  (regularPolynomial a f hf).map (regularSeries ℓ a)

/-- Apply a ring homomorphism coefficientwise to Laurent series, fixing the series variable. -/
def laurentMap {R : Type uℓ} {S : Type um} [CommRing R] [CommRing S] (g : R →+* S) :
    LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map g
  map_zero' := HahnSeries.map_zero g.toZeroHom
  map_one' := HahnSeries.map_one g.toMonoidWithZeroHom
  map_add' _ _ := HahnSeries.map_add g.toAddMonoidHom
  map_mul' _ _ := HahnSeries.map_mul g.toNonUnitalRingHom

set_option linter.checkUnivs false in
def RegularSeriesType := ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
  (a : k), regularCoefficients a →+* PowerSeries ℓ

set_option linter.checkUnivs false in
def PolynomialLiftType := ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
  (a : k) (f : (RatFunc k)[X]), PolynomialRegularAt a f → (PowerSeries ℓ)[X]

set_option linter.checkUnivs false in
def LaurentMapType := ∀ {R : Type uℓ} {S : Type um} [CommRing R] [CommRing S],
  (R →+* S) → LaurentSeries R →+* LaurentSeries S

abbrev SubstitutionInjective : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ] (a : k),
    Function.Injective (substitution ℓ a)

abbrev SubstitutionC : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ] (a c : k),
    substitution ℓ a (RatFunc.C c) = HahnSeries.C (algebraMap k ℓ c)

abbrev SubstitutionSubC : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ] (a : k),
    substitution ℓ a (RatFunc.X - RatFunc.C a) = uniformizer ℓ

abbrev SubstitutionDiv : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ] (a : k) (p q : k[X]),
    substitution ℓ a (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q) =
      powerToLaurent ℓ (polynomialSeries ℓ a p) / powerToLaurent ℓ (polynomialSeries ℓ a q)

abbrev RegularAtDiv : Prop :=
  ∀ {k : Type uk} [Field k] (a : k) (p q : k[X]), q.eval a ≠ 0 →
    RegularAt a (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q)

abbrev FractionSpecializes : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (p q : k[X]), q.eval a ≠ 0 →
    ∃ F : PowerSeries ℓ,
      powerToLaurent ℓ F =
        substitution ℓ a (algebraMap k[X] (RatFunc k) p / algebraMap k[X] (RatFunc k) q) ∧
      PowerSeries.constantCoeff F = algebraMap k ℓ (p.eval a / q.eval a)

abbrev PowerToLaurentRegularSeries : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (x : regularCoefficients a),
    powerToLaurent ℓ (regularSeries ℓ a x) = substitution ℓ a (x : RatFunc k)

abbrev ConstantCoeffRegularSeries : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (x : regularCoefficients a),
    PowerSeries.constantCoeff (regularSeries ℓ a x) = algebraMap k ℓ (evalRegular a x)

abbrev PolynomialLiftLaurent : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f),
    (polynomialLift ℓ a f hf).map (powerToLaurent ℓ) = f.map (substitution ℓ a).toRingHom

abbrev PolynomialLiftReduction : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f),
    (polynomialLift ℓ a f hf).map PowerSeries.constantCoeff =
      (specialize a f hf).map (algebraMap k ℓ)

abbrev PolynomialLiftReductionBase : Prop :=
  ∀ {k : Type uk} [Field k] (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f),
    (polynomialLift k a f hf).map PowerSeries.constantCoeff = specialize a f hf

abbrev PolynomialLiftMonicDegree : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f), f.Monic →
    (polynomialLift ℓ a f hf).Monic ∧ (polynomialLift ℓ a f hf).natDegree = f.natDegree

abbrev SpecializeMonicDegree : Prop :=
  ∀ {k : Type uk} [Field k] (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f),
    f.Monic → (specialize a f hf).Monic ∧ (specialize a f hf).natDegree = f.natDegree

abbrev SubstitutionNaturality : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (m : Type um) [Field m] [Algebra k m] [Algebra ℓ m] [IsScalarTower k ℓ m] (a : k),
    (laurentMap (algebraMap ℓ m)).comp (substitution ℓ a).toRingHom =
      (substitution m a).toRingHom

abbrev RegularSeriesNaturality : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (m : Type um) [Field m] [Algebra k m] [Algebra ℓ m] [IsScalarTower k ℓ m] (a : k),
    (PowerSeries.map (algebraMap ℓ m)).comp (regularSeries ℓ a) = regularSeries m a

abbrev PolynomialLiftNaturality : Prop :=
  ∀ {k : Type uk} [Field k] (ℓ : Type uℓ) [Field ℓ] [Algebra k ℓ]
    (m : Type um) [Field m] [Algebra k m] [Algebra ℓ m] [IsScalarTower k ℓ m]
    (a : k) (f : (RatFunc k)[X]) (hf : PolynomialRegularAt a f),
    (polynomialLift ℓ a f hf).map (PowerSeries.map (algebraMap ℓ m)) =
      polynomialLift m a f hf

end

end Specs.GaloisFormalization.IG.SpecializationCoefficients
