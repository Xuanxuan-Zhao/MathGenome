import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.EquivariantIntersectionComplexes

noncomputable section

set_option autoImplicit false

open CategoryTheory

namespace RepTheorySurvey.Geometric.CentralTranslationBoundedJetSupportSpecs

open Analytic LocalSheaf
open LatticeModelSpecs BoundedLatticeSpecs RankTwoSchubertStrataSpecs
open SchubertIntersectionConstructibilitySpecs EquivariantIntersectionComplexesSpecs

/-- The occupied Schubert space as a closed subspace of the bounded lattice stage,
with the bounded window action and its compatible action on the support. -/
def BoundedSchubertSupport {J : GL2JetParameters} {ab : DominantPair} {N : ℕ}
    {hN : OrbitBound ab N} (A : SchubertJetAction J ab N hN) : Prop :=
  let Y := TopCat.of (BoundedLattice 2 N)
  let Z : Set Y := schubertLatticeSet ab N
  ∃ (_ : IsClosed Z)
    (v : SchubertSpace ab N hN ≅ TopCat.of Z)
    (B : JetAction J.toJetSystem Y)
    (A_Z : JetAction J.toJetSystem (TopCat.of Z)),
    (∀ p, schubertPointSubspace p = boundedSubspace (v.hom p).val) ∧
    B.cutoff = 2 * N - 1 ∧
    (∀ (k : ℕ) (hk : B.cutoff ≤ k) (hw : 2 * N ≤ k + 1) (g : PositiveJet k) (L : Y),
      boundedSubspace ((B.action k hk).act (g, L)) =
        (boundedSubspace L).map (windowJetLinear (-(N : ℤ)) hw g.val)) ∧
    JetMapsCommute A.action A_Z v.hom ∧
    JetMapsCommute A_Z B (closedInclusion Z)

def BoundedJetSupport : Prop :=
  ∀ (J : GL2JetParameters) (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (A : SchubertJetAction J ab N hN), BoundedSchubertSupport A

/-- Every finite jet action identified equivariantly with the Schubert action
at common levels has a cutoff at least as large as the Schubert cutoff. -/
def SchubertJetCutoffMinimal : Prop :=
  ∀ (J : GL2JetParameters) (ab : DominantPair) (N : ℕ) (hN : OrbitBound ab N)
    (A : SchubertJetAction J ab N hN) (Y : TopCat.{0})
    (A' : JetAction J.toJetSystem Y) (v' : SchubertSpace ab N hN ≅ Y),
    JetMapsCommute A.action A' v'.hom → A.action.cutoff ≤ A'.cutoff

end RepTheorySurvey.Geometric.CentralTranslationBoundedJetSupportSpecs
