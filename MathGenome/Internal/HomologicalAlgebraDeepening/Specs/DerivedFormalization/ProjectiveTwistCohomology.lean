import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveCechComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.LaurentCechCohomology
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open AdvancedHomologicalAlgebra.Cech
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients
open DerivedFormalization.ProjectiveTwists
open DerivedFormalization.LaurentCechCohomology
open Specs.DerivedFormalization.ProjectiveCechComparison
open Specs.DerivedFormalization.OrderedCechComparison

namespace Specs.DerivedFormalization.ProjectiveTwistCohomology

universe u

variable (k : Type u) [Field k] (n : ℕ)

private def restrictHomologyIso {A B : Type u} [Ring A] [Ring B] (f : A →+* B)
    (K : CochainComplex (ModuleCat.{u} B) ℕ) (q : ℕ) {M : ModuleCat.{u} B}
    (a : K.homology q ≅ M) :
    (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex (.up ℕ)).obj K).homology q ≅
      (ModuleCat.restrictScalars.{u} f).obj M :=
  (K.sc q).mapHomologyIso (ModuleCat.restrictScalars.{u} f) ≪≫
    (ModuleCat.restrictScalars.{u} f).mapIso a

/-- Restrict the ordered descent isomorphism along the structure map from the ground field. -/
def descentIso (c : Cover (globalOpen k n) (Index n))
    [EnoughInjectives (AmbientSheaves.{u} (R k n))]
    (h : OrderedComparison (R k n) c)
    (F : SheafOfModules.{u} (R k n)) (hF : AcyclicOnIntersections (R k n) c F) (q : ℕ) :
    (GroundComplex k n c F).homology q ≅ GroundCohomology k n F q :=
  restrictHomologyIso (groundScalarsValue k n) (CechComplex k n c F) q
    (h.choose_spec.choose_spec.choose_spec.choose F hF q)

/-- Read a Čech cocycle as a localized homogeneous polynomial on one intersection. -/
def localizedRepresentative (c : Cover (globalOpen k n) (Index n))
    {T : TwistFamily k n} (d : LocalizedCoordinates k n c T) {m : ℤ} {q : ℕ}
    (z : (GroundComplex k n c (T m)).cycles q) (t : IncreasingTuple (Index n) q) :
    ChartLocalization k n (tupleIndices n t.1) :=
  let s : IncreasingCochains (R k n) c (T m).val q :=
    (GroundComplex k n c (T m)).iCycles q z
  ((d m q t.1).symm (s t)).val

/-- The class formulas for one twist, in terms of its Čech cocycles and descent map. -/
def twistClassFormula (m : ℤ) (C : CochainComplex (ModuleCat.{u} k) ℕ)
    (H : ℕ → ModuleCat.{u} k) (δ : ∀ q, C.homology q ≅ H q)
    (ρ : ∀ (q : ℕ), C.cycles q → (t : IncreasingTuple (Index n) q) →
      ChartLocalization k n (tupleIndices n t.val)) : Prop :=
  (∃ e : polynomialDegree k n m ≃ₗ[k] H 0,
    ∀ f, ∃ z : C.cycles 0,
      (δ 0).hom (C.homologyπ 0 z) = e f ∧
      ∀ t : IncreasingTuple (Index n) 0, ρ 0 z t = algebraMap _ _ f.val) ∧
  (∃ e : (TopExponents n m →₀ k) ≃ₗ[k] H n,
    ∀ f, ∃ z : C.cycles n,
      (δ n).hom (C.homologyπ n z) = e f ∧
      ∀ t : IncreasingTuple (Index n) n,
        chartToLaurent k n (tupleIndices n t.val) (ρ n z t) =
          AddMonoidAlgebra.ofCoeff
            (Finsupp.mapDomain (fun a : TopExponents n m ↦ a.val.val) f)) ∧
  (∀ q : ℕ, 0 < q → q ≠ n → IsZero (H q)) ∧
  (m < 0 → polynomialDegree k n m = ⊥ ∧ IsZero (H 0)) ∧
  (IsEmpty (TopExponents n m) → IsZero (H n))

/-- The class formulas with the geometric complex and its ordered descent map. -/
def descendedTwistClassFormula (c : Cover (globalOpen k n) (Index n))
    {T : TwistFamily k n} (d : LocalizedCoordinates k n c T)
    [EnoughInjectives (AmbientSheaves.{u} (R k n))] (hOrd : OrderedComparison (R k n) c)
    (m : ℤ) (hA : AcyclicOnIntersections (R k n) c (T m)) : Prop :=
  twistClassFormula k n m (GroundComplex k n c (T m)) (GroundCohomology k n (T m))
    (descentIso k n c hOrd (T m) hA) (fun _ z t ↦ localizedRepresentative k n c d z t)

/-- Cohomology of the projective twists in their rational-function model. The maps in
degrees zero and n send the indicated polynomial and Laurent cocycles through Čech descent. -/
def cohomologyType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 1 ≤ n →
    ∃ (c : Cover (globalOpen k n) (Index n)) (T : TwistFamily k n)
      (w : SectionCoordinates k n T) (d : LocalizedCoordinates k n c T)
      (μ : GlobalMultiply k n T)
      (h : EnoughInjectives (AmbientSheaves.{u} (R k n))),
      letI := h
      c.opens = chart k n ∧
      TwistCoordinates k n w ∧ LocalizedTerms k n c w d ∧
      GlobalMultiplyFormula k n w μ ∧
      (∀ l : ℕ, polynomialDegree k n (l : ℤ) = grading k n l) ∧
      ∃ (hA : ∀ m, AcyclicOnIntersections (R k n) c (T m))
        (hOrd : OrderedComparison (R k n) c),
        ∀ m : ℤ, descendedTwistClassFormula k n c d hOrd m (hA m)

end Specs.DerivedFormalization.ProjectiveTwistCohomology
