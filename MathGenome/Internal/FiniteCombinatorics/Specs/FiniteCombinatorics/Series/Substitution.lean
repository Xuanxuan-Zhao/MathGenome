import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Series.CoefficientAlgebra

/-!
Independent specifications for the substitution part of paper.tex, p204:W12.
All series use the shared `PowerSeries` representation. The operation is the
canonical formal substitution; every law involving a general inner series is
restricted to zero constant coefficient, with no condition on its linear term.
The coefficient formula gives the coefficientwise meaning of the infinite sum.
The two inverse assertions of W12 belong to separate goals.
-/

noncomputable section

universe u

namespace Specs.FiniteCombinatorics.Series.Substitution

open scoped BigOperators

def composeType : Type (u + 1) :=
  ∀ {R : Type u} [CommRing R], PowerSeries R → PowerSeries R → PowerSeries R

def composeValue : composeType :=
  fun {_} [_] A B => A.subst B

/-- The j-th power of a zero-constant series has no terms below degree j. -/
def PowerCoefficientsVanish : Prop :=
  ∀ {R : Type u} [CommRing R] (B : PowerSeries R),
    PowerSeries.constantCoeff B = 0 → ∀ n j : ℕ, n < j →
      PowerSeries.coeff n (B ^ j) = 0

/-- Only j ≤ n contributes to degree n in A(B) = ∑ a_j B^j. -/
def CompositionCoefficients : Prop :=
  ∀ {R : Type u} [CommRing R] (A B : PowerSeries R),
    PowerSeries.constantCoeff B = 0 → ∀ n : ℕ,
      PowerSeries.coeff n (composeValue A B) =
        ∑ j ∈ Finset.range (n + 1),
          PowerSeries.coeff j A * PowerSeries.coeff n (B ^ j)

def CompositionConstant : Prop :=
  ∀ {R : Type u} [CommRing R] (A B : PowerSeries R),
    PowerSeries.constantCoeff B = 0 →
      PowerSeries.constantCoeff (composeValue A B) = PowerSeries.constantCoeff A

def CompositionAdd : Prop :=
  ∀ {R : Type u} [CommRing R] (A D B : PowerSeries R),
    PowerSeries.constantCoeff B = 0 →
      composeValue (A + D) B = composeValue A B + composeValue D B

def CompositionMul : Prop :=
  ∀ {R : Type u} [CommRing R] (A D B : PowerSeries R),
    PowerSeries.constantCoeff B = 0 →
      composeValue (A * D) B = composeValue A B * composeValue D B

def CompositionAssoc : Prop :=
  ∀ {R : Type u} [CommRing R] (A B C : PowerSeries R),
    PowerSeries.constantCoeff B = 0 → PowerSeries.constantCoeff C = 0 →
      composeValue (composeValue A B) C = composeValue A (composeValue B C)

def CompositionRightIdentity : Prop :=
  ∀ {R : Type u} [CommRing R] (A : PowerSeries R),
    composeValue A PowerSeries.X = A

def CompositionLeftIdentity : Prop :=
  ∀ {R : Type u} [CommRing R] (B : PowerSeries R),
    PowerSeries.constantCoeff B = 0 → composeValue PowerSeries.X B = B

def CompositionC : Prop :=
  ∀ {R : Type u} [CommRing R] (r : R) (B : PowerSeries R),
    PowerSeries.constantCoeff B = 0 →
      composeValue (PowerSeries.C r) B = PowerSeries.C r

/-- The formal chain rule over arbitrary commutative rings. -/
def CompositionDerivative : Prop :=
  ∀ {R : Type u} [CommRing R] (A B : PowerSeries R),
    PowerSeries.constantCoeff B = 0 →
      PowerSeries.derivative (composeValue A B) =
        composeValue (PowerSeries.derivative A) B * PowerSeries.derivative B

end Specs.FiniteCombinatorics.Series.Substitution
