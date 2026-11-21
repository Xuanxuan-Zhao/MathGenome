import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.PrimaryDecomposition
import MathGenome.Internal.AlgebraCore.Specs.P103.Ch05.PrimaryLocalizationUniqueness
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Ideal.IsPrimary

/-! Corollary 5.6 and its example, paper.tex:1023–1031.
The polynomial ring has precisely two variables and an arbitrary field of coefficients.
All ideal predicates below use the usual ideal radical, rather than an assumed certificate. -/
namespace P103.Specs.Ch05.PrimaryIdealsExample
universe u
open P103.Specs.Ch05.PrimarySubmodules
open P103.Specs.Ch05.AssociatedPrimesInterface
open P103.Specs.Ch05.PrimaryLocalizationUniqueness

/-- The source's ideal form of the primary condition, including properness. -/
def PrimaryIdeal {R : Type u} [CommRing R] (Q : Ideal R) : Prop :=
  Q ≠ ⊤ ∧ ∀ a b : R, a * b ∈ Q → b ∉ Q → a ∈ Q.radical

structure IsIdealDecomposition {R : Type u} [CommRing R]
    (I : Ideal R) (s : Finset (Ideal R)) : Prop where
  nonempty : s.Nonempty
  primary : ∀ Q ∈ s, PrimaryIdeal Q
  intersection : (⨅ Q ∈ s, Q) = I
  distinct : (s : Set (Ideal R)).Pairwise (fun Q P => Q.radical ≠ P.radical)
  irredundant : ∀ Q ∈ s, (⨅ P ∈ s.erase Q, P) ≠ I

def primaryBridgeType : Prop := ∀ (R : Type u) [CommRing R] (Q : Ideal R),
  PrimaryIdeal Q ↔ primaryValue R R Q

def radicalBridgeType : Prop := ∀ (R : Type u) [CommRing R] (Q : Ideal R),
  radicalValue R R Q = Q.radical

def existsDecompositionType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ →
    ∃ s : Finset (Ideal R), IsIdealDecomposition I s

def associatedRadicalsType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (s : Finset (Ideal R)), IsIdealDecomposition I s →
    associatedPrimesValue R (R ⧸ I) = (fun Q : Ideal R => Q.radical) '' (s : Set _)

def minimalComponentType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (s : Finset (Ideal R)), IsIdealDecomposition I s → ∀ p : PrimeSpectrum R,
    Minimal (fun q => q ∈ associatedPrimesValue R (R ⧸ I)) p.asIdeal →
    (∃ Q ∈ s, Q.radical = p.asIdeal) ∧
    ∀ Q ∈ s, Q.radical = p.asIdeal → Q = contractionValue R R p.asIdeal.primeCompl I

def minimalComponentUniqueType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (s t : Finset (Ideal R)), IsIdealDecomposition I s → IsIdealDecomposition I t →
    ∀ p : PrimeSpectrum R,
    Minimal (fun q => q ∈ associatedPrimesValue R (R ⧸ I)) p.asIdeal →
    ∀ Q ∈ s, ∀ P ∈ t, Q.radical = p.asIdeal → P.radical = p.asIdeal → Q = P

abbrev Plane (k : Type u) [CommSemiring k] := MvPolynomial (Fin 2) k
noncomputable def exampleI (k : Type u) [Field k] : Ideal (Plane k) :=
  Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1}
noncomputable def exampleP (k : Type u) [Field k] : Ideal (Plane k) :=
  Ideal.span {MvPolynomial.X 0}
noncomputable def exampleQ (k : Type u) [Field k] : Ideal (Plane k) :=
  Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 1}
noncomputable def exampleQ' (k : Type u) [Field k] : Ideal (Plane k) :=
  Ideal.span {MvPolynomial.X 0 ^ 2, MvPolynomial.X 0 * MvPolynomial.X 1,
    MvPolynomial.X 1 ^ 2}
noncomputable def exampleM (k : Type u) [Field k] : Ideal (Plane k) :=
  Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1}

def exampleIntersectionsType : Prop := ∀ (k : Type u) [Field k],
  exampleI k = exampleP k ⊓ exampleQ k ∧ exampleI k = exampleP k ⊓ exampleQ' k

def exampleComponentsType : Prop := ∀ (k : Type u) [Field k],
  exampleQ k ≠ exampleQ' k ∧ (exampleP k).IsPrime ∧
  (exampleM k).IsMaximal ∧ PrimaryIdeal (exampleQ k) ∧ PrimaryIdeal (exampleQ' k) ∧
  (exampleP k).radical = exampleP k ∧ (exampleQ k).radical = exampleM k ∧
  (exampleQ' k).radical = exampleM k

noncomputable def exampleDecompositionsType : Prop := ∀ (k : Type u) [Field k],
  IsIdealDecomposition (exampleI k) {exampleP k, exampleQ k} ∧
  IsIdealDecomposition (exampleI k) {exampleP k, exampleQ' k}

def exampleAssociatedType : Prop := ∀ (k : Type u) [Field k],
  associatedPrimesValue (Plane k) (Plane k ⧸ exampleI k) = {exampleP k, exampleM k} ∧
  Minimal (fun p => p ∈ associatedPrimesValue (Plane k) (Plane k ⧸ exampleI k))
    (exampleP k) ∧
  exampleM k ∈ associatedPrimesValue (Plane k) (Plane k ⧸ exampleI k) ∧
  ¬ Minimal (fun p => p ∈ associatedPrimesValue (Plane k) (Plane k ⧸ exampleI k))
    (exampleM k) ∧ exampleP k < exampleM k
end P103.Specs.Ch05.PrimaryIdealsExample
