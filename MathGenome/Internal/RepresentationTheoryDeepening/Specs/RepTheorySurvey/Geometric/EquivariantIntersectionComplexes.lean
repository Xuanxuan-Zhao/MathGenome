import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SchubertFiniteJetActions
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ClosedEquivarianceExtension
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionConstantDescent

noncomputable section

set_option autoImplicit false

open CategoryTheory Topology
open scoped MatrixGroups

namespace RepTheorySurvey.Geometric.EquivariantIntersectionComplexesSpecs

open Analytic Analytic.IntersectionComplex
open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs
open ClosedEquivarianceExtensionSpecs (parameterInclusion projectionSquare ActionSquares
  ComparisonsAreIso MatchesComparisons above)
export ClosedEquivarianceExtensionSpecs (DerivedAdjunctions)
open ConvolutionConstantDescentSpec (shiftedConstantPullback)

/-- Level `k` uses jets modulo `t^(k+1)`. -/
abbrev PositiveJet (k : ℕ) := GLJets 2 (k + 1) (Nat.succ_pos k)

def jetTruncation {k l : ℕ} (h : k ≤ l) : PositiveJet l →* PositiveJet k :=
  Matrix.GeneralLinearGroup.map (truncateJet (Nat.succ_le_succ h))

structure ContinuousJets : Prop where
  coefficientOpen : ∀ k, IsOpenEmbedding
    (fun g : PositiveJet k ↦ jetMatrixCoefficients g.val)
  topologicalGroup : ∀ k, IsTopologicalGroup (PositiveJet k)
  truncation : ∀ {k l : ℕ} (h : k ≤ l), Continuous (jetTruncation h)

private theorem truncateJet_id {k : ℕ} (x : JetRing k) :
    truncateJet (le_refl k) x = x :=
  congrArg (fun f : JetRing k →+* JetRing k ↦ f x) Ideal.Quotient.factor_eq

private theorem truncateJet_comp {k l m : ℕ} (h : k ≤ l) (j : l ≤ m) (x : JetRing m) :
    truncateJet h (truncateJet j x) = truncateJet (h.trans j) x :=
  Ideal.Quotient.factor_comp_apply _ _ x

/-- The actual two-by-two jet groups in their coefficient topologies. -/
def jetSystem (c : ContinuousJets) : JetSystem.{0} where
  group k :=
    { space := TopCat.of (PositiveJet k)
      group := inferInstance
      topologicalGroup := c.topologicalGroup k }
  truncate _ _ h := TopCat.ofHom ⟨jetTruncation h, c.truncation h⟩
  truncate_one h := (jetTruncation h).map_one
  truncate_mul h a b := (jetTruncation h).map_mul a b
  truncate_id _ := TopCat.ext fun g ↦ by
    apply Units.ext
    funext i j
    exact truncateJet_id (g.val i j)
  truncate_comp h j := TopCat.ext fun g ↦ by
    apply Units.ext
    funext a b
    exact truncateJet_comp (Nat.succ_le_succ h) (Nat.succ_le_succ j) (g.val a b)

abbrev GL2JetParameters := ContinuousJets

abbrev GL2JetParameters.toJetSystem (J : GL2JetParameters) : JetSystem.{0} := jetSystem J

/-- The action is the reduction of the positive-loop lattice action and preserves the orbit strata. -/
def ActualSchubertAction {c : ContinuousJets} (ab : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) (A : JetAction (jetSystem c) (SchubertSpace ab N hN)) : Prop :=
  A.cutoff = difference ab - 1 ∧
  (∀ (k : ℕ) (hk : A.cutoff ≤ k) (g : GL (Fin 2) O)
      (p : SchubertSpace ab N hN) (L : BoundedLattice 2 N),
    schubertPointSubspace p = boundedSubspace L →
      schubertPointSubspace ((A.action k hk).act (reduceGL 2 (k + 1) (Nat.succ_pos k) g, p)) =
        latticeSubspace (-(N : ℤ)) (2 * N) (positiveGLMap 2 g • L.val)) ∧
  ∀ (k : ℕ) (hk : A.cutoff ≤ k) (g : PositiveJet k)
    (p : SchubertSpace ab N hN) (i : OrbitIndex ab),
    (A.action k hk).act (g, p) ∈ orbitPoints ab N hN i ↔ p ∈ orbitPoints ab N hN i

structure SchubertJetAction (J : GL2JetParameters) (ab : DominantPair) (N : ℕ)
    (hN : OrbitBound ab N) where
  action : JetAction J.toJetSystem (SchubertSpace ab N hN)
  actual : ActualSchubertAction ab N hN action

/-- Compatibility of a map with the actions at all common levels. -/
def Intertwines {J : JetSystem.{0}} {X Y : TopCat.{0}}
    (A : JetAction J X) (B : JetAction J Y) (f : X ⟶ Y) : Prop :=
  ∀ (k : ℕ) (hx : A.cutoff ≤ k) (hy : B.cutoff ≤ k),
    parameterInclusion (J.group k) f ≫ (B.action k hy).act = (A.action k hx).act ≫ f

abbrev JetMapsCommute := @Intertwines

/-- The action-to-projection arrow pulled back from the target along an equivariant map. -/
def restrictedArrow {J : JetSystem.{0}} {X Y : TopCat.{0}} {A : JetAction J X}
    {B : JetAction J Y} {f : X ⟶ Y} (h : JetMapsCommute A B f) {G : Derived Y}
    (e : B.Equivariance G) (k : ℕ) (hx : A.cutoff ≤ k) (hy : B.cutoff ≤ k) :
    (derivedInverseImage (A.action k hx).act).obj ((derivedInverseImage f).obj G) ⟶
      (derivedInverseImage (AnalyticAction.projection (J.group k) X)).obj
        ((derivedInverseImage f).obj G) :=
  let H := J.group k
  (derivedInverseImageComposition (A.action k hx).act f).inv.app G ≫
    pullbackMorphism (parameterInclusion H f) (h k hx hy) (projectionSquare H f)
      (e.datum k hy).iso.hom ≫
    (derivedInverseImageComposition (AnalyticAction.projection H X) f).hom.app G

/-- A morphism to a pulled-back equivariant object commutes with the action-to-projection arrows. -/
def IntertwinesPullback {J : JetSystem.{0}} {X Y : TopCat.{0}}
    {A : JetAction J X} {B : JetAction J Y} {f : X ⟶ Y} (h : Intertwines A B f)
    {F : Derived X} {G : Derived Y} (e : A.Equivariance F) (e' : B.Equivariance G)
    (v : F ⟶ (derivedInverseImage f).obj G) : Prop :=
  ∀ (k : ℕ) (hx : A.cutoff ≤ k) (hy : B.cutoff ≤ k),
    (derivedInverseImage (A.action k hx).act).map v ≫ restrictedArrow h e' k hx hy =
      (e.datum k hx).iso.hom ≫
        (derivedInverseImage (AnalyticAction.projection (J.group k) X)).map v

/-- The comparison of the restriction of an attachment with the smaller IC is the
ordinary truncation map followed by the derived adjunction counit. -/
def attachmentRestriction {U X : TopCat.{0}} {d s : ℕ} (D : DimensionFiltration U d)
    (j : U ⟶ X) (hj : IsOpenEmbedding j)
    (a : boundedBelowInverseImage j ⊣ derivedDirectImage j) :
    (boundedBelowInverseImage j).obj ((attachment j hj s).obj (complex D)) ⟶ complex D :=
  (boundedBelowInverseImage j).map ((attachmentInclusion j hj s).app (complex D)) ≫
    a.counit.app (complex D)

/-- Normalize an IC datum by the coefficient comparison on the top stratum and
by equivariance of the canonical restriction to the preceding open stage. -/
inductive NormalizedICDatum {J : JetSystem.{0}} (a : DerivedAdjunctions.{0}) :
    {X : TopCat.{0}} → {d : ℕ} → (A : JetAction J X) →
      (D : DimensionFiltration X d) → A.Equivariance (complex D).obj → Prop
  | top {X : TopCat.{0}} {d : ℕ} {A : JetAction J X}
      (e : A.Equivariance (shiftedConstant X d).obj)
      (coefficients : ∀ (k : ℕ) (hk : A.cutoff ≤ k),
        (e.datum k hk).iso = shiftedConstantPullback (A.action k hk).act d ≪≫
          (shiftedConstantPullback (AnalyticAction.projection (J.group k) X) d).symm) :
      NormalizedICDatum (@a) A (.top X d) e
  | attach {U X : TopCat.{0}} {d s : ℕ} {D : DimensionFiltration U d}
      {j : U ⟶ X} {hj : IsOpenEmbedding j} {hs : s < d}
      {A : JetAction J X} {B : JetAction J U} (hB : B.cutoff = A.cutoff)
      (h : Intertwines B A j)
      (e : A.Equivariance (complex (.attach D j hj hs)).obj)
      (e' : B.Equivariance (complex D).obj)
      (prev : NormalizedICDatum (@a) B D e')
      (hR : IsIso (attachmentRestriction (s := s) D j hj (a j)))
      (comm : IntertwinesPullback h e' e
        ((@asIso _ _ _ _ _ hR).inv.hom)) :
      NormalizedICDatum (@a) A (.attach D j hj hs) e

/-- Extension by zero on an invariant closed subset has the equivariance transported
by the canonical action and projection adjunction mates. -/
def ClosedExtensionCompatibility (J : JetSystem.{0}) : Prop :=
  ∀ {X : TopCat.{0}} {Z : Set X} (hZ : IsClosed Z)
    (A : JetAction J X) (B : JetAction J (TopCat.of Z)) (h : ActionSquares A B)
    (a : DerivedAdjunctions.{0})
    (b : boundedBelowInverseImage (closedInclusion Z) ⊣ LocalSheaf.closedExtensionPlus hZ)
    (F : BoundedBelow (TopCat.of Z)) (β : B.Equivariance F.obj),
    ComparisonsAreIso hZ h (@a) b F ∧
      ∃ α : (above A B.cutoff).Equivariance ((LocalSheaf.closedExtensionPlus hZ).obj F).obj,
        MatchesComparisons hZ h (@a) b F β α

namespace Expected

/-- Every actual reduced Schubert closure has its normalized rational IC equivariance
at all jet levels above its cutoff. Stratified equivariant homeomorphisms and stable
closed inclusions preserve the resulting equivariant complexes. -/
def EquivariantIntersectionComplexes : Prop :=
  Nonempty DerivedAdjunctions.{0} ∧
  (∀ {X : TopCat.{0}} {Z : Set X} (hZ : IsClosed Z),
    Nonempty (boundedBelowInverseImage (closedInclusion Z) ⊣ LocalSheaf.closedExtensionPlus hZ)) ∧
  (∀ J : JetSystem.{0}, ClosedExtensionCompatibility J) ∧
  ∃ c : ContinuousJets,
    (∀ (a : DerivedAdjunctions.{0}) (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N),
      ∃ (A : SchubertJetAction c ab N hN) (P : Stratification (SchubertSpace ab N hN))
        (D : DimensionFiltration (SchubertSpace ab N hN) (orbitDimension ab (difference ab / 2))),
        IsNormalizedOrbitIC ab N hN (𝟙 _) (difference ab / 2) P D ∧
          ∃ e : A.action.Equivariance (complex D).obj, NormalizedICDatum (@a) A.action D e) ∧
    (∀ (a : DerivedAdjunctions.{0}) (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
      (A : JetAction (jetSystem c) (SchubertSpace ab N hN)), ActualSchubertAction ab N hN A →
      ∀ (P : Stratification (SchubertSpace ab N hN))
        (D : DimensionFiltration (SchubertSpace ab N hN) (orbitDimension ab (difference ab / 2))),
        IsNormalizedOrbitIC ab N hN (𝟙 _) (difference ab / 2) P D →
        ∃! e : A.Equivariance (complex D).obj, NormalizedICDatum (@a) A D e) ∧
    ∀ (a : DerivedAdjunctions.{0}) {X Y : TopCat.{0}} {s : ℕ}
      {A : JetAction (jetSystem c) X} {B : JetAction (jetSystem c) Y}
      {e : X ≅ Y} (h : Intertwines A B e.hom)
      {P : DimensionFiltration X s} {Q : DimensionFiltration Y s},
      A.cutoff ≤ B.cutoff → FiltrationIso e P Q →
      ∀ {α : A.Equivariance (complex P).obj}, NormalizedICDatum (@a) A P α →
        ∃ (β : B.Equivariance (complex Q).obj)
          (v : (complex P).obj ≅ (derivedInverseImage e.hom).obj (complex Q).obj),
          NormalizedICDatum (@a) B Q β ∧ IntertwinesPullback h α β v.hom

end Expected
end RepTheorySurvey.Geometric.EquivariantIntersectionComplexesSpecs
