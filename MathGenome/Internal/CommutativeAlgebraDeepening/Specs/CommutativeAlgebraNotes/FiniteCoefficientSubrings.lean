import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.PBases
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

namespace Specs.CommutativeAlgebraNotes.FiniteCoefficientSubrings

open FrobeniusCoefficientDefinitions PBases

universe u v
noncomputable section

/-- Embed the coefficient subfield and multiply both sets of exponents by (p). -/
def embedding {k : Type u} [Field k] (H : Subfield k)
    (p : ℕ) (hp : p ≠ 0) (r s : ℕ) :
    CoefficientTowerBase H r s →+* CoefficientTowerBase k r s :=
  (MvPolynomial.expand p).toRingHom.comp
    (MvPolynomial.map ((MvPowerSeries.expand p hp).toRingHom.comp (MvPowerSeries.map H.subtype)))

abbrev Index {ι : Type v} (J : Finset ι) (p r s : ℕ) :=
  RestrictedExponents {i : ι // i ∈ J} p ×
    RestrictedExponents (Fin r) p × RestrictedExponents (Fin s) p

variable {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
  {ι : Type v}

private theorem prime_ne_zero : p ≠ 0 := (Fact.out : p.Prime).ne_zero

/-- The coefficient subring associated to a finite subset of the p-basis. -/
def coefficientSubring (a : ι → k) (J : Finset ι) (r s : ℕ) :
    Subring (CoefficientTowerBase k r s) :=
  (embedding (complementField (p := p) a J) p prime_ne_zero r s).range

/-- The image of the fraction field of a subring in the ambient fraction field. -/
def fractionSubfield {S : Type u} [CommRing S] [IsDomain S] (T : Subring S) :
    Subfield (FractionRing S) :=
  let g := (algebraMap S (FractionRing S)).comp T.subtype
  (IsFractionRing.lift (K := FractionRing T) (g := g)
    ((IsFractionRing.injective S (FractionRing S)).comp Subtype.val_injective)).fieldRange

/-- The restricted coefficient and variable monomial at the indicated exponents. -/
def basisMonomial (a : ι → k) (J : Finset ι) {r s : ℕ} (i : Index J p r s) :
    CoefficientTowerBase k r s :=
  MvPolynomial.monomial i.2.2.val
    (MvPowerSeries.monomial i.2.1.val (restrictedMonomial (fun j : J => a j) i.1))

def EmbeddingType :=
  ∀ {k : Type u} [Field k] (H : Subfield k) (p : ℕ), p ≠ 0 → ∀ (r s : ℕ),
    CoefficientTowerBase H r s →+* CoefficientTowerBase k r s

def EmbeddingInjective : Prop :=
  ∀ {k : Type u} [Field k] (H : Subfield k) (p : ℕ) (hp : p ≠ 0) (r s : ℕ),
    Function.Injective (embedding H p hp r s)

set_option linter.checkUnivs false in
def CoefficientSubringType :=
  ∀ {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type v}
    (_a : ι → k) (_J : Finset ι) (r s : ℕ), Subring (CoefficientTowerBase k r s)

def FractionSubfieldType :=
  ∀ {S : Type u} [CommRing S] [IsDomain S] (_T : Subring S), Subfield (FractionRing S)

def RestrictedMonomialBasis : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type v}
    (a : ι → k), isPBasis p (frobeniusSubfield k p) le_rfl a →
    ∀ (J : Finset ι) (r s : ℕ),
      ∃ B : Module.Basis (Index J p r s) (coefficientSubring (p := p) a J r s)
          (CoefficientTowerBase k r s),
        (∀ i, B i = basisMonomial (p := p) a J i) ∧ 1 ∈ Set.range B

def CoefficientSubringFiniteFree : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type v}
    (a : ι → k), isPBasis p (frobeniusSubfield k p) le_rfl a →
    ∀ (J : Finset ι) (r s : ℕ),
      Module.Finite (coefficientSubring (p := p) a J r s) (CoefficientTowerBase k r s) ∧
        Module.Free (coefficientSubring (p := p) a J r s) (CoefficientTowerBase k r s)

def FrobeniusLeCoefficientSubring : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type v}
    (a : ι → k) (J : Finset ι) (r s : ℕ),
    (frobenius (CoefficientTowerBase k r s) p).range ≤ coefficientSubring (p := p) a J r s

def CoefficientSubringIntersection : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type v}
    (a : ι → k), isPBasis p (frobeniusSubfield k p) le_rfl a →
    ∀ r s : ℕ,
      (⨅ J : Finset ι, coefficientSubring (p := p) a J r s) =
        (frobenius (CoefficientTowerBase k r s) p).range

def FractionSubfieldIntersectionWithBase : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type v}
    (a : ι → k), isPBasis p (frobeniusSubfield k p) le_rfl a →
    ∀ (J : Finset ι) (r s : ℕ),
      (fractionSubfield (coefficientSubring (p := p) a J r s)).toSubring.comap
        (algebraMap (CoefficientTowerBase k r s) (FractionRing (CoefficientTowerBase k r s))) =
          coefficientSubring (p := p) a J r s

def FractionSubfieldIntersection : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type v}
    (a : ι → k), isPBasis p (frobeniusSubfield k p) le_rfl a →
    ∀ r s : ℕ,
      (⨅ J : Finset ι, fractionSubfield (coefficientSubring (p := p) a J r s)) =
        frobeniusSubfield (FractionRing (CoefficientTowerBase k r s)) p

def CoefficientSubringAntitone : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type v}
    (a : ι → k) (r s : ℕ),
    Antitone (fun J => coefficientSubring (p := p) a J r s)

def FractionSubfieldDirected : Prop :=
  ∀ {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] {ι : Type v}
    (a : ι → k) (r s : ℕ),
    (Set.range (fun J => fractionSubfield (coefficientSubring (p := p) a J r s))).Nonempty ∧
      Directed (· ≥ ·) (fun J => fractionSubfield (coefficientSubring (p := p) a J r s))

end

end Specs.CommutativeAlgebraNotes.FiniteCoefficientSubrings
