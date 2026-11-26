import Mathlib.LinearAlgebra.Basis.Basic
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.FrobeniusCoefficientDefinitions

namespace CommutativeAlgebraNotes

universe v u

noncomputable section

/-- The subfield of `p`-th powers in a field of characteristic `p`. -/
def frobeniusSubfield (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p] :
    Subfield L :=
  (frobenius L p).fieldRange

@[simp]
theorem mem_frobeniusSubfield {L : Type*} [Field L] {p : ℕ} [Fact p.Prime] [CharP L p]
    {x : L} : x ∈ frobeniusSubfield L p ↔ ∃ y : L, y ^ p = x :=
  Iff.rfl

/-- Exponents for the restricted monomials of a family indexed by `ι`. -/
abbrev RestrictedExponents (ι : Type*) (p : ℕ) :=
  { e : ι →₀ ℕ // ∀ i, e i < p }

/-- The product of the powers indicated by the finitely supported exponent vector. -/
def restrictedMonomial {ι : Type v} {L : Type u} [Field L] {p : ℕ} (a : ι → L)
    (e : RestrictedExponents ι p) : L :=
  e.val.prod fun i n => a i ^ n

section PBases

variable {ι : Type v} {L : Type u} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
  (H : Subfield L)

/-- Over a subfield containing the `p`-th powers, a family is `p`-independent
if its restricted monomials are linearly independent. -/
def PIndependent (_hH : frobeniusSubfield L p ≤ H) (a : ι → L) : Prop :=
  LinearIndependent H (restrictedMonomial (p := p) a)

/-- A `p`-basis over a subfield containing the `p`-th powers is a family whose
restricted monomials are linearly independent and span the field. -/
def IsPBasis (hH : frobeniusSubfield L p ≤ H) (a : ι → L) : Prop :=
  PIndependent p H hH a ∧ Submodule.span H (Set.range (restrictedMonomial (p := p) a)) = ⊤

variable {p H}

/-- The vector-space basis furnished by a `p`-basis. -/
def IsPBasis.basis {hH : frobeniusSubfield L p ≤ H} {a : ι → L}
    (ha : IsPBasis p H hH a) : Module.Basis (RestrictedExponents ι p) H L :=
  Module.Basis.mk ha.1 ha.2.ge

@[simp]
theorem IsPBasis.basis_apply {hH : frobeniusSubfield L p ≤ H} {a : ι → L}
    (ha : IsPBasis p H hH a) (e : RestrictedExponents ι p) :
    ha.basis e = restrictedMonomial a e :=
  Module.Basis.mk_apply _ _ e

end PBases

/-- The ring `k[[u₁,…,uᵣ]][v₁,…,vₛ]`, including empty variable families. -/
abbrev CoefficientTowerBase (k : Type*) [CommSemiring k] (r s : ℕ) :=
  MvPolynomial (Fin s) (MvPowerSeries (Fin r) k)

section TowerMaps

variable (k : Type*) [CommSemiring k] (r s : ℕ)

/-- The inclusion of the power-series coefficient ring as constant polynomials. -/
def towerPowerSeries : MvPowerSeries (Fin r) k →+* CoefficientTowerBase k r s :=
  MvPolynomial.C

/-- The inclusion of `k` as constant power series and then constant polynomials. -/
def towerCoefficient : k →+* CoefficientTowerBase k r s :=
  (towerPowerSeries k r s).comp MvPowerSeries.C

/-- The inner, power-series variables in the tower ring. -/
def towerPowerSeriesVariable (i : Fin r) : CoefficientTowerBase k r s :=
  towerPowerSeries k r s (MvPowerSeries.X i)

/-- The outer, polynomial variables in the tower ring. -/
def towerPolynomialVariable (j : Fin s) : CoefficientTowerBase k r s :=
  MvPolynomial.X j

theorem towerPowerSeries_injective : Function.Injective (towerPowerSeries k r s) :=
  MvPolynomial.C_injective _ _

theorem towerCoefficient_injective : Function.Injective (towerCoefficient k r s) :=
  (towerPowerSeries_injective k r s).comp MvPowerSeries.C_injective

theorem towerPowerSeriesVariable_injective [Nontrivial k] :
    Function.Injective (towerPowerSeriesVariable k r s) :=
  fun _ _ h => MvPowerSeries.X_inj.mp (towerPowerSeries_injective k r s h)

theorem towerPolynomialVariable_injective [Nontrivial k] :
    Function.Injective (towerPolynomialVariable k r s) :=
  MvPolynomial.X_injective

end TowerMaps

end

end CommutativeAlgebraNotes
