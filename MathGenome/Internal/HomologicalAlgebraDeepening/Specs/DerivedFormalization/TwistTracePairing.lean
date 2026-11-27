import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveTwistCohomology
import Mathlib.LinearAlgebra.PerfectPairing.Basic

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AdvancedHomologicalAlgebra.Cech
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues
open DerivedFormalization.ProjectiveTwists
open DerivedFormalization.LaurentCechCohomology
open Specs.DerivedFormalization.OrderedCechComparison
open Specs.DerivedFormalization.ProjectiveCechComparison
open Specs.DerivedFormalization.ProjectiveTwistCohomology

namespace Specs.DerivedFormalization.TwistTracePairing

universe u

attribute [local instance] HasDerivedCategory.standard

def traceDegree (n : ℕ) : ℤ := -(n : ℤ) - 1

def traceExponent (n : ℕ) : TopExponents n (traceDegree n) :=
  ⟨⟨fun _ ↦ -1, by simp [traceDegree, Index]; omega⟩, fun _ ↦ by change (-1 : ℤ) < 0; decide⟩

def complement {n : ℕ} {m : ℤ} (a : PolynomialExponents n m) :
    TopExponents n (traceDegree n - m) :=
  ⟨⟨fun i ↦ -1 - (a.val i : ℤ), by
      rw [Finset.sum_sub_distrib, a.property]
      simp [Index, traceDegree]
      omega⟩, fun i ↦ by change -1 - (a.val i : ℤ) < 0; have := Int.natCast_nonneg (a.val i); omega⟩

variable (k : Type u) [Field k] (n : ℕ)

def polynomialMonomial {m : ℤ} (a : PolynomialExponents n m) :
    polynomialDegree k n m :=
  ⟨MvPolynomial.monomial a.val 1, by
    classical
    intro b hb
    have : b = a.val := by
      by_contra h
      exact hb (by simp [MvPolynomial.coeff_monomial, Ne.symm h])
    simpa [this] using a.property⟩

abbrev GroundSections (F : SheafOfModules.{u} (R k n)) :=
  (GroundRestriction k n).obj ((SheafOfModules.evaluation (R k n) (op (globalOpen k n))).obj F)

variable [EnoughInjectives (AmbientSheaves.{u} (R k n))]

/-- The degree-zero derived-functor unit on actual global sections. -/
def sectionUnit (F : SheafOfModules.{u} (R k n)) :
    GroundSections k n F ⟶ GroundCohomology k n F 0 :=
  (GroundRestriction k n).map
    (ModuleCat.ofHom (ULift.moduleEquiv.symm.toLinearMap) ≫
      (rightDegreeZeroUnit (sectionsValue.{u} (R k n) (globalOpen k n))).app
        ((liftSheafCoefficients.{u,u,u,u} (R k n)).obj F))

def cohomologyMap {F G : SheafOfModules.{u} (R k n)} (f : F ⟶ G) (q : ℕ) :
    GroundCohomology k n F q ⟶ GroundCohomology k n G q :=
  (GroundRestriction k n).map
    ((coefficientCohomologyValue (Base k n) (R k n) (globalOpen k n) q).map f)

/-- Actual multiplication by a degree-zero class, acting on derived global sections.
The equality of twist degrees just identifies the product twist with the trace twist. -/
def traceAction {T : TwistFamily k n} (μ : GlobalMultiply k n T)
    {a b : ℤ} (h : a + b = traceDegree n) (s : GroundSections k n (T a)) :
    GroundCohomology k n (T b) n ⟶ GroundCohomology k n (T (traceDegree n)) n :=
  cohomologyMap k n (μ a b s ≫ eqToHom (congrArg T h)) n

/-- Trace and pairing data on the specified cover and twists. -/
def tracePairingOn (c : Cover (globalOpen k n) (Index n)) (T : TwistFamily k n)
    (w : SectionCoordinates k n T) (d : LocalizedCoordinates k n c T)
    (μ : GlobalMultiply k n T) (hA : ∀ m, AcyclicOnIntersections (R k n) c (T m))
    (hOrd : OrderedComparison (R k n) c) : Prop :=
  let H := fun m q ↦ GroundCohomology k n (T m) q
  ∃ (e₀ : ∀ m, polynomialDegree k n m ≃ₗ[k] H m 0)
    (eₙ : ∀ m, (TopExponents n m →₀ k) ≃ₗ[k] H m n)
    (τ : H (traceDegree n) n →ₗ[k] k)
    (P : ∀ m q r, q + r = n → H m q →ₗ[k] H (traceDegree n - m) r →ₗ[k] k),
    (∀ m (f : polynomialDegree k n m),
      ∃ s : GroundSections k n (T m), sectionUnit k n (T m) s = e₀ m f ∧
        ∀ x, (w m (globalOpen k n) s).val x = intoFraction k n f.val) ∧
    (∀ m (f : TopExponents n m →₀ k), ∃ z : (GroundComplex k n c (T m)).cycles n,
      (descentIso k n c hOrd (T m) (hA m) n).hom
          ((GroundComplex k n c (T m)).homologyπ n z) = eₙ m f ∧
      ∀ t : IncreasingTuple (Index n) n,
        chartToLaurent k n (tupleIndices n t.1) (localizedRepresentative k n c d z t) =
          AddMonoidAlgebra.ofCoeff
            (Finsupp.mapDomain (fun a : TopExponents n m ↦ a.val.val) f)) ∧
    (∀ f, τ (eₙ (traceDegree n) f) = f (traceExponent n)) ∧
    (∀ m q r (hqr : q + r = n), (P m q r hqr).IsPerfPair) ∧
    (∀ m (s : GroundSections k n (T m)) (y : H (traceDegree n - m) n),
      P m 0 n (Nat.zero_add n) (sectionUnit k n (T m) s) y =
        τ (traceAction k n μ (by omega : m + (traceDegree n - m) = traceDegree n) s y)) ∧
    (∀ m (x : H m n) (s : GroundSections k n (T (traceDegree n - m))),
      P m n 0 (Nat.add_zero n) x (sectionUnit k n (T (traceDegree n - m)) s) =
        τ (traceAction k n μ (by omega : traceDegree n - m + m = traceDegree n) s x)) ∧
    (∀ m q r (_ : q + r = n), 0 < q → 0 < r → IsZero (H m q) ∧
      IsZero (H (traceDegree n - m) r)) ∧
    (∀ m (a : PolynomialExponents n m) (b : TopExponents n (traceDegree n - m)),
      P m 0 n (Nat.zero_add n) (e₀ m (polynomialMonomial k n a)) (eₙ _ (Finsupp.single b 1)) =
        if b = complement a then 1 else 0)

/-- The trace and the perfect pairings on the actual derived global sections of the
twists. At either endpoint the cup product is the derived map of multiplication
by the global section. In the interior the source factors vanish. -/
def tracePairingType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 1 ≤ n →
    ∃ (c : Cover (globalOpen k n) (Index n)) (T : TwistFamily k n)
      (w : SectionCoordinates k n T) (d : LocalizedCoordinates k n c T)
      (μ : GlobalMultiply k n T)
      (h : EnoughInjectives (AmbientSheaves.{u} (R k n))),
      letI := h
      c.opens = chart k n ∧ TwistCoordinates k n w ∧
      LocalizedTerms k n c w d ∧ GlobalMultiplyFormula k n w μ ∧
      ∃ (hA : ∀ m, AcyclicOnIntersections (R k n) c (T m))
        (hOrd : OrderedComparison (R k n) c),
        tracePairingOn k n c T w d μ hA hOrd

end Specs.DerivedFormalization.TwistTracePairing
