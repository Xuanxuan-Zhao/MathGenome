import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorLocalization
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.SimpleDifferentialDomain
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.SimpleDifferenceComponents

namespace GaloisFormalization.PV.Specs

universe u v

/-- The constants of any simple operator ring form a field. -/
def simpleConstantsAreField : Prop :=
  ∀ {kind : OperatorKind} {R : Type u} [CommRing R] (D : operator kind R),
    isSimple D → IsField (constantSubring D)

/-- The total ring of fractions of a simple operator ring is operator simple
for the compatible operator of `fractionOperatorExistsUnique`. -/
def simpleFractionRingIsSimple : Prop :=
  ∀ {kind : OperatorKind} {R : Type u} {K : Type v}
    [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
    (D : operator kind R) (E : operator kind K),
    isSimple D → commutes D E (algebraMap R K) → isSimple E

/-- The canonical inclusion into the total ring of fractions identifies the
constant rings. This holds without a Noetherian or characteristic hypothesis. -/
def simpleFractionRingConstants : Prop :=
  ∀ {kind : OperatorKind} {R : Type u} {K : Type v}
    [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
    (D : operator kind R) (E : operator kind K),
    isSimple D → ∀ h : commutes D E (algebraMap R K),
      Function.Bijective (mapConstants (D := D) (E := E) ⟨algebraMap R K, h⟩) ∧
      IsField (constantSubring E)

/-- In the differential case the ring is a domain and its total ring of
fractions is a field. The extension obeys `localizedDerivationQuotientRule`. -/
def simpleDifferentialFractionField : Prop :=
  ∀ {R : Type u} {K : Type v}
    [CommRing R] [Algebra ℚ R] [IsNoetherianRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    (D : operator .differential R), isSimple D → IsDomain R ∧ IsField K

/-- In the difference case the product of minimal-prime quotients extends
coordinatewise to the total ring of fractions. The operator on the product
of fields uses the same transitive permutation and induces the fraction map
of each isomorphism between the domain factors. -/
def simpleDifferenceFractionComponents : Prop :=
  ∀ {R : Type u} {K : Type v} [CommRing R] [IsNoetherianRing R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    (σ : R ≃+* R) (τ : K ≃+* K),
    isSimple (difference σ) → commutes (difference σ) (difference τ) (algebraMap R K) →
    Finite (minimalPrimes R) ∧ Nonempty (minimalPrimes R) ∧
    (∀ i : minimalPrimes R, IsDomain (R ⧸ i.val)) ∧
    (∀ i : minimalPrimes R, IsField (FractionRing (R ⧸ i.val))) ∧
    ∃ (e : R ≃+* ((i : minimalPrimes R) → R ⧸ i.val))
      (p : Equiv.Perm (minimalPrimes R))
      (f : (i : minimalPrimes R) → (R ⧸ i.val) ≃+* (R ⧸ (p i).val))
      (eK : K ≃+* ((i : minimalPrimes R) → FractionRing (R ⧸ i.val))),
      (∀ i, (p i).val = i.val.map σ.toRingHom) ∧
      (∀ i j, ∃ n : ℤ, (p ^ n) i = j) ∧
      (∀ x i, e x i = Ideal.Quotient.mk i.val x) ∧
      (∀ x i, e (σ x) (p i) = f i (e x i)) ∧
      (∀ x i, eK (algebraMap R K x) i =
        algebraMap (R ⧸ i.val) (FractionRing (R ⧸ i.val)) (e x i)) ∧
      (∀ q i, eK (τ q) (p i) =
        fractionRingEquiv (K := FractionRing (R ⧸ i.val))
          (L := FractionRing (R ⧸ (p i).val)) (f i) (eK q i))

end GaloisFormalization.PV.Specs
