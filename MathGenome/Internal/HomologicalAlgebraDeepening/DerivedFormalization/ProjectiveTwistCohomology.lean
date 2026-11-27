import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveTwistCohomology
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveCechComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveChartComplexBridge
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ProjectiveCechClassComputation

set_option Elab.async false
set_option cleanup.letToHave false

noncomputable section

open CategoryTheory
open AdvancedHomologicalAlgebra.Cech (Cover)
open AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients (AcyclicOnIntersections)
open AdvancedHomologicalAlgebra.SheafUniverseTransport (AmbientSheaves)
open DerivedFormalization.LaurentCechCohomology
open DerivedFormalization.ProjectiveCechComparison
open DerivedFormalization.ProjectiveTwists (Index ChartLocalization chart)
open Specs.DerivedFormalization.OrderedCechComparison
open Specs.DerivedFormalization.ProjectiveCechComparison
open Specs.DerivedFormalization.ProjectiveTwistCohomology

namespace DerivedFormalization.ProjectiveTwistCohomology

universe u

private theorem tupleIndices_card {n q : ℕ} (t : IncreasingTuple (Index n) q) :
    (tupleIndices n t.val).card = q + 1 := by
  simp [tupleIndices, Finset.card_image_of_injective _ t.property.injective]

private structure ClassComparison (k : Type u) [Field k] (n : ℕ) (m : ℤ)
    (C : CochainComplex (ModuleCat.{u} k) ℕ)
    (ρ : ∀ (q : ℕ), C.cycles q → (t : IncreasingTuple (Index n) q) →
      ChartLocalization k n (tupleIndices n t.val)) where
  squareZero : ∀ p, (differential k n m (p + 1)).comp (differential k n m p) = 0
  termEquiv : ∀ p : ℤ, Term k n m p ≃ₗ[k] LocalizedTerm k n m p
  coeff : ∀ (p : ℤ) (x : Term k n m p) (J : Faces n p) (a : Exponents n m),
    (chartToLaurent k n J.val (termEquiv p x J).val).coeff a.val = (x a).val J.val
  homologyIso : ∀ q : ℕ, (orderedComplex k n m squareZero).homology (q : ℤ) ≅ C.homology q
  cyclesMap : ∀ q : ℕ, (orderedComplex k n m squareZero).cycles (q : ℤ) ⟶ C.cycles q
  homologyπ : ∀ (q : ℕ) (z : (orderedComplex k n m squareZero).cycles (q : ℤ)),
    (homologyIso q).hom ((orderedComplex k n m squareZero).homologyπ (q : ℤ) z) =
      C.homologyπ q (cyclesMap q z)
  laurent : ∀ (q : ℕ) (z : (orderedComplex k n m squareZero).cycles (q : ℤ))
    (t : IncreasingTuple (Index n) q),
    ∃ h : ((tupleIndices n t.val).card : ℤ) = (q : ℤ) + 1 ∧ (tupleIndices n t.val).Nonempty,
      let J : Faces n (q : ℤ) := ⟨tupleIndices n t.val, h⟩
      chartToLaurent k n (tupleIndices n t.val) (ρ q (cyclesMap q z) t) =
        chartToLaurent k n J.val
          (termEquiv (q : ℤ) ((orderedComplex k n m squareZero).iCycles (q : ℤ) z) J).val

set_option maxHeartbeats 60000 in
private theorem classesFromComparison (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) (m : ℤ)
    (C : CochainComplex (ModuleCat.{u} k) ℕ) (H : ℕ → ModuleCat.{u} k)
    (δ : ∀ q, C.homology q ≅ H q)
    (ρ : ∀ (q : ℕ), C.cycles q → (t : IncreasingTuple (Index n) q) →
      ChartLocalization k n (tupleIndices n t.val))
    (comparison : ClassComparison k n m C ρ) : twistClassFormula k n m C H δ ρ := by
  let I (q : ℕ) := IncreasingTuple (Index n) q
  let V (q : ℕ) (t : I q) := tupleIndices n t.val
  have hcard (q : ℕ) (t : I q) : (V q t).card = q + 1 := tupleIndices_card t
  have hV (q : ℕ) (t : I q) : (V q t).Nonempty :=
    Finset.card_pos.mp ((hcard q t).symm ▸ Nat.succ_pos q)
  unfold twistClassFormula
  refine ProjectiveCechClassComputation.transportedCechClasses.{u, 0} k n hn m
    comparison.squareZero comparison.termEquiv comparison.coeff C H δ comparison.homologyIso
    comparison.cyclesMap comparison.homologyπ I V hV hcard ρ ?_
  intro q z t
  obtain ⟨_, h⟩ := comparison.laurent q z t
  exact h

set_option maxHeartbeats 60000 in
private theorem classComparisonOfBridge (k : Type u) [Field k] (n : ℕ) (m : ℤ)
    (sq : ∀ p, (differential k n m (p + 1)).comp (differential k n m p) = 0)
    (e : ∀ p : ℤ, Term k n m p ≃ₗ[k] LocalizedTerm k n m p)
    (hcoeff : ∀ (p : ℤ) (x : Term k n m p) (J : Faces n p) (a : Exponents n m),
      (chartToLaurent k n J.val (e p x J).val).coeff a.val = (x a).val J.val)
    (C : CochainComplex (ModuleCat.{u} k) ℕ)
    (ρ : ∀ (q : ℕ), C.cycles q → (t : IncreasingTuple (Index n) q) →
      ChartLocalization k n (tupleIndices n t.val))
    (h : let K := orderedComplex k n m sq
      ∃ (φ : K.restriction ComplexShape.embeddingUpNat ≅ C)
        (β : ∀ q : ℕ, K.homology (q : ℤ) ≅ C.homology q)
        (g : ∀ q : ℕ, K.cycles (q : ℤ) ⟶ C.cycles q),
        ∀ (q : ℕ) (z : K.cycles (q : ℤ)),
          (β q).hom (K.homologyπ (q : ℤ) z) = C.homologyπ q (g q z) ∧
          C.iCycles q (g q z) = φ.hom.f q (K.iCycles (q : ℤ) z) ∧
          ∀ t : IncreasingTuple (Index n) q,
            ∃ h : ((tupleIndices n t.val).card : ℤ) = (q : ℤ) + 1 ∧
                (tupleIndices n t.val).Nonempty,
              let J : Faces n (q : ℤ) := ⟨tupleIndices n t.val, h⟩
              chartToLaurent k n (tupleIndices n t.val) (ρ q (g q z) t) =
                chartToLaurent k n J.val (e (q : ℤ) (K.iCycles (q : ℤ) z) J).val) :
    Nonempty (ClassComparison k n m C ρ) := by
  obtain ⟨_, β, g, hcycles⟩ := h
  exact ⟨⟨sq, e, hcoeff, β, g, (fun q z ↦ (hcycles q z).1),
    (fun q z ↦ (hcycles q z).2.2)⟩⟩

set_option maxHeartbeats 95000 in
private theorem chartClassComparison (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) (m : ℤ)
    (c : Cover (globalOpen k n) (Index n)) (T : TwistFamily k n)
    (w : SectionCoordinates k n T) (d : LocalizedCoordinates k n c T)
    (hc : c.opens = chart k n) (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (hdifferential : LocalizedDifferential k n c d) :
    Nonempty (ClassComparison k n m (GroundComplex k n c (T m))
      (fun _ z t ↦ localizedRepresentative k n c d z t)) := by
  have sq := differentialSquareZero k n m
  obtain ⟨e, hcoeff, he⟩ := localizedComplexComparison k n m
  refine classComparisonOfBridge k n m sq e hcoeff (GroundComplex k n c (T m))
    (fun _ z t ↦ localizedRepresentative k n c d z t) ?_
  dsimp only [localizedRepresentative]
  exact ProjectiveChartComplexBridge.comparison k n hn m c T w d hc hw hd hdifferential sq e he

set_option maxHeartbeats 60000 in
private theorem cohomologyOnCover (k : Type u) [Field k] (n : ℕ) (hn : 1 ≤ n) (m : ℤ)
    (c : Cover (globalOpen k n) (Index n)) (T : TwistFamily k n)
    (w : SectionCoordinates k n T) (d : LocalizedCoordinates k n c T)
    (hc : c.opens = chart k n) (hw : TwistCoordinates k n w) (hd : LocalizedTerms k n c w d)
    (hdifferential : LocalizedDifferential k n c d)
    [EnoughInjectives (AmbientSheaves.{u} (R k n))] (hOrd : OrderedComparison (R k n) c)
    (hA : AcyclicOnIntersections (R k n) c (T m)) :
    descendedTwistClassFormula k n c d hOrd m hA := by
  unfold descendedTwistClassFormula
  exact classesFromComparison k n hn m (GroundComplex k n c (T m))
    (GroundCohomology k n (T m)) (descentIso k n c hOrd (T m) hA)
    (fun _ z t ↦ localizedRepresentative k n c d z t)
    (Classical.choice (chartClassComparison k n hn m c T w d hc hw hd hdifferential))

set_option maxHeartbeats 60000 in
/-- The polynomial and Laurent cocycles compute the cohomology of the standard twists. -/
theorem cohomology : cohomologyType.{u} := by
  intro k _ n hn
  obtain ⟨c, T, w, d, μ, hinj, hc, hw, hd, hdifferential, hμ, _, hA, hOrd, _⟩ :=
    projectiveComparison k n hn
  let _ := hinj
  exact ⟨c, T, w, d, μ, hinj, hc, hw, hd, hμ, (polynomialGrading k n).1, hA, hOrd,
    fun m ↦ cohomologyOnCover k n hn m c T w d hc hw hd hdifferential hOrd (hA m)⟩

end DerivedFormalization.ProjectiveTwistCohomology
