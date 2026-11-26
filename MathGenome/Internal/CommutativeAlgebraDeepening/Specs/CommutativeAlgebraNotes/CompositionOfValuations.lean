import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace CommutativeAlgebraNotes.CompositionOfValuations.Spec

universe u

variable {K : Type u} [Field K]

/-- The inverse image of `W` along the residue map, viewed as a subring of `K`. -/
def pullback (U : ValuationSubring K) (W : ValuationSubring (IsLocalRing.ResidueField U)) :
    Subring K :=
  (W.toSubring.comap (IsLocalRing.residue U)).map U.subtype

/-- The restriction of the residue map of `U` to a subring mapping into `W`. -/
noncomputable def residueHom (U : ValuationSubring K)
    (W : ValuationSubring (IsLocalRing.ResidueField U))
    (V : ValuationSubring K) (h : V ≤ U)
    (hW : ∀ x : V, IsLocalRing.residue U (V.inclusion U h x) ∈ W) : V →+* W :=
  ((IsLocalRing.residue U).comp (V.inclusion U h)).codRestrict W.toSubring hW

/-- The composition assertion of Theorem 5.19, with the residue-induced quotient
isomorphism and the localization identified as a valuation subring of `K`. -/
def Composition : Prop :=
  ∀ {K : Type u} [Field K] (U : ValuationSubring K)
      (W : ValuationSubring (IsLocalRing.ResidueField U)),
    ∃ (V : ValuationSubring K) (h : V ≤ U)
        (hW : ∀ x : V, IsLocalRing.residue U (V.inclusion U h x) ∈ W),
      V.toSubring = pullback U W ∧
        let f := residueHom U W V h hW
        let P := RingHom.ker f
        letI : P.IsPrime := RingHom.ker_isPrime f
        (∃ e : V ⧸ P ≃+* W, ∀ x : V, e (Ideal.Quotient.mk P x) = f x) ∧
          V.ofPrime P = U

end CommutativeAlgebraNotes.CompositionOfValuations.Spec
