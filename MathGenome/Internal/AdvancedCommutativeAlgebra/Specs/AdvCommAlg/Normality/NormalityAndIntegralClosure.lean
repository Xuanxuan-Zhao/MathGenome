import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Normality.TotalQuotientProduct

/-! Independent specifications for SN-04, paper.tex:4104–4110 and 4132–4159.
The ambient ring is reduced and Noetherian; it need not be a domain or nonzero.
The product is indexed by all minimal primes, and each factor is explicitly
`A/p`, with fraction field `MinimalFraction A p`. Compatibility of both product
maps identifies the field factors with the factors of the total quotient ring.
-/
universe u v w
namespace AdvCommAlg.Normality.Specs

/-- Normality means integrally closed domains at every prime localization,
while the right side means integral closure inside the total quotient ring. -/
def isNormal_iff_integral_totalQuotientType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A],
    IsNormalValue A ↔ ∀ z : FractionRing A, IsIntegral A z →
      ∃ a : A, algebraMap A (FractionRing A) a = z

/-- Mathlib's integral closure predicate uses the total fraction ring even
for a ring with zero divisors. -/
def isNormal_iff_isIntegrallyClosedType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A],
    IsNormalValue A ↔ IsIntegrallyClosed A

/-- The finite decomposition and its compatible decomposition of total
fractions. Domain hypotheses on the components are conclusions here. -/
def exists_normal_product_decompositionType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [IsReduced A],
    IsNormalValue A →
    Finite (MinimalPrime A) ∧
    ∃ e : A ≃+* (∀ p : MinimalPrime A, A ⧸ p.val),
      (∀ p : MinimalPrime A, IsDomain (A ⧸ p.val) ∧ IsIntegrallyClosed (A ⧸ p.val)) ∧
      (∀ (a : A) (p : MinimalPrime A), e a p = Ideal.Quotient.mk p.val a) ∧
      ∃ eQ : FractionRing A ≃+* (∀ p : MinimalPrime A, MinimalFraction A p),
        ∀ (a : A) (p : MinimalPrime A),
          eQ (algebraMap A (FractionRing A) a) p =
            algebraMap (A ⧸ p.val) (MinimalFraction A p) (e a p)

/-- Any finite product decomposition into integrally closed domains implies
local normality. No Noetherianity assumption on the factors is added. -/
def isNormal_of_product_decompositionType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (ι : Type v) [Finite ι] (B : ι → Type w) [∀ i, CommRing (B i)]
    [∀ i, IsDomain (B i)] [∀ i, IsIntegrallyClosed (B i)],
    (A ≃+* (∀ i, B i)) → IsNormalValue A

/-- For the zero ring the same canonical construction is the empty product. -/
def exists_empty_product_decompositionType : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] [Subsingleton A],
    IsEmpty (MinimalPrime A) ∧
    ∃ e : A ≃+* (∀ p : MinimalPrime A, A ⧸ p.val),
      (∀ (a : A) (p : MinimalPrime A), e a p = Ideal.Quotient.mk p.val a) ∧
      ∀ p : MinimalPrime A, IsDomain (A ⧸ p.val) ∧ IsIntegrallyClosed (A ⧸ p.val)

end AdvCommAlg.Normality.Specs
