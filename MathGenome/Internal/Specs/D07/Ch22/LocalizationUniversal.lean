import MathGenome.Internal.Specs.D07.Ch22.LocalizationConstruction
import MathGenome.Internal.Specs.D07.Ch22.LocalizationUniversalAwayPolynomialQuotient
import MathGenome.Internal.Specs.D07.Ch08.FractionUniversal
import Mathlib.Algebra.MvPolynomial.Eval

/-!
Independent statements for K07.22.localization_universal, paper.tex:7082–7124.
All rings and targets are commutative and unital, including zero rings.
The localization and its canonical map are those of LocalizationConstruction.
The presentation and its nilpotent case are covered by the separate prerequisite
LocalizationUniversalAwayPolynomialQuotient, whose statements are reused below.
-/

universe u v

namespace Specs.D07.Ch22.LocalizationUniversal

noncomputable section

/-- Existence and uniqueness for every map which inverts the denominators. -/
def ExtensionUnique : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (S : Submonoid R) (f : R →+* A),
    (∀ s : S, IsUnit (f s)) →
      ∃! g : Localization S →+* A, g.comp (algebraMap R (Localization S)) = f

/-- In a ring without a global inverse operation, use any unit with value f(s).
This is the formula f(a)/f(s), for every extension, not just a chosen lift. -/
def FractionFormula : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (S : Submonoid R) (f : R →+* A) (g : Localization S →+* A),
    g.comp (algebraMap R (Localization S)) = f →
    ∀ (a : R) (s : S) (t : Aˣ), (t : A) = f s →
      g (Localization.mk a s) = f a * (↑(t⁻¹) : A)

/-- Conversely, existence of an extension forces the unit condition. -/
def ExtensionCriterion : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A]
    (S : Submonoid R) (f : R →+* A),
    (∃ g : Localization S →+* A, g.comp (algebraMap R (Localization S)) = f) ↔
      ∀ s : S, IsUnit (f s)

/-- The kernel is exactly the set of elements annihilated by some denominator. -/
def KernelFormula : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R) (a : R),
    a ∈ RingHom.ker (algebraMap R (Localization S)) ↔
      ∃ s : S, (s : R) * a = 0

/-- Subsingleton is precisely the zero-ring condition, with no source restriction. -/
def ZeroRingIff : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R),
    Subsingleton (Localization S) ↔ (0 : R) ∈ S

/-- The usual restriction excluding zero ensures a nonzero localization. -/
def NonzeroIff : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R),
    Nontrivial (Localization S) ↔ (0 : R) ∉ S

/-- Exactly the paper's injectivity of each left multiplication map. -/
def InjectiveIff : Prop :=
  ∀ (R : Type u) [CommRing R] (S : Submonoid R),
    Function.Injective (algebraMap R (Localization S)) ↔
      ∀ s : S, Function.Injective (fun a : R => (s : R) * a)

/-- A zero source ring makes every denominator set contain zero and every
localization a zero ring. -/
def ZeroBaseRing : Prop :=
  ∀ (R : Type u) [CommRing R] [Subsingleton R] (S : Submonoid R),
    (0 : R) ∈ S ∧ Subsingleton (Localization S)

/-- For a domain the canonical fraction ring literally is this localization;
the denominator condition is exactly nonzeroness. The field and embedding,
and the universal property for arbitrary commutative ring targets, are retained. -/
def FractionFieldRecovery : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R],
    (∀ b : R, b ∈ nonZeroDivisors R ↔ b ≠ 0) ∧
    (∃ e : Localization (nonZeroDivisors R) ≃+* FractionRing R,
      ∀ a, e (algebraMap R (Localization (nonZeroDivisors R)) a) =
        algebraMap R (FractionRing R) a) ∧
    IsField (FractionRing R) ∧
    Function.Injective (algebraMap R (FractionRing R)) ∧
    ∀ (A : Type v) [CommRing A] (f : R →+* A),
      (∀ b : R, b ≠ 0 → IsUnit (f b)) →
      ∃! g : FractionRing R →+* A, g.comp (algebraMap R (FractionRing R)) = f

/-- The field-target form of the fraction-field universal property is obtained
on this very localization, and its unique extension is injective. -/
def FractionFieldEmbedding : Prop :=
  ∀ (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [Field K]
    (f : R →+* K), Function.Injective f →
    ∃ g : Localization (nonZeroDivisors R) →+* K,
      g.comp (algebraMap R (Localization (nonZeroDivisors R))) = f ∧
      Function.Injective g ∧
      ∀ h : Localization (nonZeroDivisors R) →+* K,
        h.comp (algebraMap R (Localization (nonZeroDivisors R))) = f → h = g

/-! The example uses the literal bivariate polynomial ring, with variables
indexed by Fin 2: x = X 0 and y = X 1, followed by the principal ideal (xy). -/

open Polynomial

abbrev CrossingIdeal (k : Type u) [CommRing k] : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span ({MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)} :
    Set (MvPolynomial (Fin 2) k))

abbrev CrossingRing (k : Type u) [CommRing k] :=
  MvPolynomial (Fin 2) k ⧸ CrossingIdeal k

def crossingX (k : Type u) [CommRing k] : CrossingRing k :=
  Ideal.Quotient.mk (CrossingIdeal k) (MvPolynomial.X 0)

def crossingY (k : Type u) [CommRing k] : CrossingRing k :=
  Ideal.Quotient.mk (CrossingIdeal k) (MvPolynomial.X 1)

/-- Evaluation x ↦ 0, y ↦ Y witnesses y ≠ 0 in k[x,y]/(xy).
Inverting x kills this specific nonzero y and hence is not injective.
The assertion holds for every nonzero commutative coefficient ring, in particular
for a coefficient field k. -/
def ZeroDivisorExample : Prop :=
  ∀ (k : Type u) [CommRing k] [Nontrivial k],
    (∃ ev : CrossingRing k →+* Polynomial k,
      ev (crossingX k) = 0 ∧ ev (crossingY k) = X ∧
      ∀ a : k, ev (Ideal.Quotient.mk (CrossingIdeal k) (MvPolynomial.C a)) = C a) ∧
    crossingY k ≠ 0 ∧ crossingX k * crossingY k = 0 ∧
    LocalizationConstruction.LocalizationMapValue (CrossingRing k)
      (Submonoid.powers (crossingX k)) (crossingY k) = 0 ∧
    ¬ Function.Injective
      (fun a : CrossingRing k =>
        LocalizationConstruction.LocalizationMapValue (CrossingRing k)
          (Submonoid.powers (crossingX k)) a)

/-- The separate prerequisite gives the displayed R[T]/(fT-1) equivalence,
including the nilpotent and zero coefficient ring cases. -/
def PrincipalPresentation : Prop :=
  (∀ (R : Type u) [CommRing R] (f : R),
    Nonempty (Localization.Away f ≃ₐ[R]
      LocalizationUniversalAwayPolynomialQuotient.Presentation R f)) ∧
  LocalizationUniversalAwayPolynomialQuotient.NilpotentCase.{u} ∧
  LocalizationUniversalAwayPolynomialQuotient.ZeroRingCase.{u}

end

end Specs.D07.Ch22.LocalizationUniversal
