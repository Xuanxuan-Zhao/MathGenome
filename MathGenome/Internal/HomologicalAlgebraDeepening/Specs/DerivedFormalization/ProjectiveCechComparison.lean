import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.ProjectiveTwists
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.OrderedCechComparison
import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open HomologicalComplex
open AdvancedHomologicalAlgebra.Cech AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.CechSequenceOriginal
open AdvancedHomologicalAlgebra.SheafUniverseTransport
open AdvancedHomologicalAlgebra.AcyclicCoverOriginalCoefficients
open Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
open Specs.DerivedFormalization.OrderedCechComparison
open DerivedFormalization.ProjectiveTwists

namespace Specs.DerivedFormalization.ProjectiveCechComparison

universe u

variable (k : Type u) [Field k] (n : ℕ)

abbrev R := moduleRingSheaf k n
abbrev globalOpen : OpensOfProj k n := ⊤
abbrev GlobalRing := sectionRing (R k n) (globalOpen k n)

def coverValue (h : ⨆ i, chart k n i = ⊤) :
    Cover (globalOpen k n) (Index n) :=
  ⟨chart k n, fun _ ↦ le_top, h⟩

def tupleIndices {p : ℕ} (t : Fin (p + 1) → Index n) : Finset (Index n) :=
  Finset.univ.image t

abbrev CechComplex (c : Cover (globalOpen k n) (Index n)) (F : SheafOfModules.{u} (R k n)) :=
  increasingComplex (R k n) c F.val

abbrev Cohomology (F : SheafOfModules.{u} (R k n)) (V : OpensOfProj k n)
    [EnoughInjectives (AmbientSheaves.{u} (R k n))] (q : ℕ) :=
  (coefficientCohomologyValue (Base k n) (R k n) V q).obj F


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

section Comparison

variable {X : TopCat.{u}} (S : X.Sheaf RingCat.{u}) {U : Opens X}
  {I : Type} [LinearOrder I] (c : Cover U I)

abbrev IncreasingH (F : SheafOfModules.{u} S) (q : ℕ) :=
  (increasingComplex S c F.val).homology q

abbrev SectionH [EnoughInjectives (SheafOfModules.{u} S)] :=
  coefficientCohomologyValue.{u,u,u} X S U

/-- The increasing-index comparison descends the normalized all-tuples map. -/
def OrderedComparison [EnoughInjectives (SheafOfModules.{u} S)] : Prop :=
  ∃ (_ : Nonempty (Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.NaturalityData.{u,u,u,0} S c))
    (e : CoefficientComparison.{u,u,u,0} S c)
    (η : ∀ q, sourceCohomology.{u,u,u,0} S c q ⟶
      originalSectionCohomology.{u,u,u,0} S c q)
    (α : ∀ (F : SheafOfModules.{u} S), AcyclicOnIntersections S c F → ∀ q,
      IncreasingH S c F q ≅ (SectionH S (U := U) q).obj F),
    (∀ (D : Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.NaturalityData.{u,u,u,0} S c) (F : SheafOfModules.{u} S)
        (J : InjectiveResolution (nativeCoefficient S F)),
      ∃ β, IsVerticalAugmentation S c e F J β ∧ AgreesWithModel S c D e η F J β) ∧
    (∀ F (hF : AcyclicOnIntersections S c F) q,
      homologyMap (projection S c F.val) q ≫ (α F hF q).hom =
        ModuleCat.ofHom (originalComparisonMap S c q (η q) F)) ∧
    ∀ (F G : SheafOfModules.{u} S)
      (hF : AcyclicOnIntersections S c F) (hG : AcyclicOnIntersections S c G)
      (f : F ⟶ G) q,
      homologyMap (increasingMap S c f.val) q ≫ (α G hG q).hom =
        (α F hF q).hom ≫ (SectionH S (U := U) q).map f

end Comparison

def orderedComparisonType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ) (c : Cover (globalOpen k n) (Index n)),
    ∃ h : EnoughInjectives (AmbientSheaves.{u} (R k n)),
      letI := h
      OrderedComparison (R k n) c

def groundScalarsType := ∀ (k : Type u) [Field k] (n : ℕ), k →+* GlobalRing k n

/-- Restriction of scalars uses the structure morphism of projective space. -/
def groundScalarsValue : k →+* GlobalRing k n :=
  ((Expected.structureMapValue k n).appTop.hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom


abbrev GroundRestriction := ModuleCat.restrictScalars.{u} (groundScalarsValue k n)

abbrev GroundComplex (c : Cover (globalOpen k n) (Index n)) (F : SheafOfModules.{u} (R k n)) :=
  ((GroundRestriction k n).mapHomologicalComplex (.up ℕ)).obj (CechComplex k n c F)

abbrev GroundCohomology (F : SheafOfModules.{u} (R k n))
    [EnoughInjectives (AmbientSheaves.{u} (R k n))] (q : ℕ) :=
  (GroundRestriction k n).obj (Cohomology k n F (globalOpen k n) q)


abbrev TwistFamily := ℤ → SheafOfModules.{u} (R k n)

abbrev SectionCoordinates (T : TwistFamily k n) :=
  ∀ m (U : OpensOfProj k n), (T m).val.obj (op U) ≃ TwistSections k n m U

/-- The module operations and restrictions of the twist in its local rational-function model. -/
def TwistCoordinates {T : TwistFamily k n} (w : SectionCoordinates k n T) : Prop :=
  (∀ m U (a b : (T m).val.obj (op U)) x,
    (w m U (a + b)).val x = (w m U a).val x + (w m U b).val x) ∧
  (∀ m U (r : sectionRing (R k n) U) (a : (T m).val.obj (op U)) x,
    (w m U (r • a)).val x = structureToFunctions k n U r x * (w m U a).val x) ∧
  ∀ m U V (h : V ≤ U) (a : (T m).val.obj (op U)),
    w m V ((T m).val.map (homOfLE h).op a) = restriction k n h m (w m U a)

abbrev LocalizedCoordinates (c : Cover (globalOpen k n) (Index n)) (T : TwistFamily k n) :=
  ∀ m (p : ℕ) (t : Fin (p + 1) → Index n),
    DegreePiece k n (tupleIndices n t) m ≃ (T m).val.obj (op (tupleOpen c t))

/-- The coefficient identifications use the homogeneous fractions in the indicated localization. -/
def LocalizedTerms (c : Cover (globalOpen k n) (Index n)) {T : TwistFamily k n}
    (w : SectionCoordinates k n T) (d : LocalizedCoordinates k n c T) : Prop :=
  ∀ m p t a x,
    (w m (tupleOpen c t) (d m p t a)).val x =
      chartToFraction k n (tupleIndices n t) a.val

/-- The alternating differential is the signed sum of face restrictions,
in the common fraction-field coordinates of the localizations. -/
def LocalizedDifferential (c : Cover (globalOpen k n) (Index n)) {T : TwistFamily k n}
    (d : LocalizedCoordinates k n c T) : Prop :=
  ∀ m (p : ℕ) (s : IncreasingCochains (R k n) c (T m).val p)
      (t : IncreasingTuple (Index n) (p + 1)),
    chartToFraction k n (tupleIndices n t.1)
        ((d m (p + 1) t.1).symm (increasingDifferential (R k n) c (T m).val p s t)).val =
      ∑ j : Fin (p + 2), ((-1 : ℤ) ^ j.val) •
        chartToFraction k n (tupleIndices n (t.1 ∘ j.succAbove))
          ((d m p (t.1 ∘ j.succAbove)).symm
            (s ⟨t.1 ∘ j.succAbove, t.2.comp j.strictMono_succAbove⟩)).val

abbrev GlobalMultiply (T : TwistFamily k n) :=
  ∀ (a b : ℤ), (T a).val.obj (op (globalOpen k n)) → (T b ⟶ T (a + b))

/-- A global section acts through its restriction and multiplication of local sections. -/
def GlobalMultiplyFormula {T : TwistFamily k n} (w : SectionCoordinates k n T)
    (μ : GlobalMultiply k n T) : Prop :=
  ∀ a b s U (z : (T b).val.obj (op U)) x,
    (w (a + b) U ((μ a b s).val.app (op U) z)).val x =
      (w a (globalOpen k n) s).val ⟨x, trivial⟩ * (w b U z).val x

/-- Ordered Čech descent for all twists of projective space with the localized polynomial
coordinates, including the coefficient morphisms induced by multiplication. -/
def projectiveComparisonType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ), 1 ≤ n →
    ∃ (c : Cover (globalOpen k n) (Index n)) (T : TwistFamily k n)
      (w : SectionCoordinates k n T) (d : LocalizedCoordinates k n c T)
      (μ : GlobalMultiply k n T)
      (h : EnoughInjectives (AmbientSheaves.{u} (R k n))),
      letI := h
      c.opens = chart k n ∧
        TwistCoordinates k n w ∧ LocalizedTerms k n c w d ∧ LocalizedDifferential k n c d ∧
        GlobalMultiplyFormula k n w μ ∧
        (∀ m J, J.Nonempty → ∀ q, 0 < q →
          IsZero (Cohomology k n (T m) (intersection k n J) q)) ∧
        (∀ m, AcyclicOnIntersections (R k n) c (T m)) ∧
        OrderedComparison (R k n) c ∧
        (∀ m q, Nonempty ((GroundComplex k n c (T m)).homology q ≅
          GroundCohomology k n (T m) q))

end Specs.DerivedFormalization.ProjectiveCechComparison
