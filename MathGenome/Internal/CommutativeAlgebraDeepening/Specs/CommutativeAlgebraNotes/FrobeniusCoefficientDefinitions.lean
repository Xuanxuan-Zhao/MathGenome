import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors

/-! Specifications for the coefficient ring and the positive-characteristic
field definitions in Section 5.2 and Lemma 5.4. -/

namespace Specs.CommutativeAlgebraNotes.FrobeniusCoefficientDefinitions

universe v u

noncomputable section

def FrobeniusSubfieldType :=
  ∀ (L : Type u) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p], Subfield L

def frobeniusSubfield : FrobeniusSubfieldType.{u} :=
  fun L [_] p [_] [_] => (frobenius L p).fieldRange

def RestrictedExponentsType := Type v → ℕ → Type v

abbrev RestrictedExponents (ι : Type v) (p : ℕ) : Type v :=
  { e : ι →₀ ℕ // ∀ i, e i < p }

set_option linter.checkUnivs false in
def RestrictedMonomialType :=
  ∀ {ι : Type v} {L : Type u} [Field L] {p : ℕ}, (ι → L) → RestrictedExponents ι p → L

def restrictedMonomial : RestrictedMonomialType.{v, u} :=
  fun {_} {_} [_] {_} a e => e.val.prod fun i n => a i ^ n

set_option linter.checkUnivs false in
def PFamilyPredicateType :=
  ∀ {ι : Type v} {L : Type u} [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (H : Subfield L), frobeniusSubfield L p ≤ H → (ι → L) → Prop

def pIndependent : PFamilyPredicateType.{v, u} :=
  fun {_} {_} [_] p [_] [_] H _ a => LinearIndependent H (restrictedMonomial (p := p) a)

def isPBasis : PFamilyPredicateType.{v, u} :=
  fun {_} {_} [_] p [_] [_] H _ a =>
    LinearIndependent H (restrictedMonomial (p := p) a) ∧
      Submodule.span H (Set.range (restrictedMonomial (p := p) a)) = ⊤

def CoefficientTowerBaseType := ∀ (k : Type u) [CommSemiring k], ℕ → ℕ → Type u

abbrev CoefficientTowerBase (k : Type u) [CommSemiring k] (r s : ℕ) : Type u :=
  MvPolynomial (Fin s) (MvPowerSeries (Fin r) k)

def TowerPowerSeriesType :=
  ∀ (k : Type u) [CommSemiring k] (r s : ℕ),
    MvPowerSeries (Fin r) k →+* CoefficientTowerBase k r s

def towerPowerSeries : TowerPowerSeriesType.{u} := fun _ [_] _ _ => MvPolynomial.C

def TowerCoefficientType :=
  ∀ (k : Type u) [CommSemiring k] (r s : ℕ), k →+* CoefficientTowerBase k r s

def towerCoefficient : TowerCoefficientType.{u} :=
  fun _ [_] _ _ => MvPolynomial.C.comp MvPowerSeries.C

def TowerPowerSeriesVariableType :=
  ∀ (k : Type u) [CommSemiring k] (r s : ℕ), Fin r → CoefficientTowerBase k r s

def towerPowerSeriesVariable : TowerPowerSeriesVariableType.{u} :=
  fun _ [_] _ _ i => MvPolynomial.C (MvPowerSeries.X i)

def TowerPolynomialVariableType :=
  ∀ (k : Type u) [CommSemiring k] (r s : ℕ), Fin s → CoefficientTowerBase k r s

def towerPolynomialVariable : TowerPolynomialVariableType.{u} :=
  fun _ [_] _ _ => MvPolynomial.X

-- The canonical tower also supports fraction fields and Frobenius in downstream Specs.
instance (k : Type u) [CommRing k] [IsDomain k] (r s : ℕ) :
    IsDomain (CoefficientTowerBase k r s) :=
  NoZeroDivisors.to_isDomain _

instance (k : Type u) [CommSemiring k] (p : ℕ) [CharP k p] (r s : ℕ) :
    CharP (CoefficientTowerBase k r s) p :=
  charP_of_injective_ringHom (f := towerCoefficient k r s)
    ((MvPolynomial.C_injective (Fin s) (MvPowerSeries (Fin r) k)).comp
      MvPowerSeries.C_injective) p

end

end Specs.CommutativeAlgebraNotes.FrobeniusCoefficientDefinitions
