import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.SingularCochainSheaves
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SmallChainHomology

noncomputable section

open CategoryTheory Opposite TopologicalSpace
open P202Specs.CohomologyPairs P202Specs.SmallChainHomology

universe u

namespace RepTheorySurvey.Geometric.Analytic.SmallCochains

open SingularCochains

/-- Restriction of sections of the degreewise sheafified cochain complex. -/
def sectionsRestriction {X : TopCat.{u}} {V U : Opens X} (i : V ⟶ U) :
    evaluatedComplex U ⟶ evaluatedComplex V :=
  (NatTrans.mapHomologicalComplex ((evaluation (Opens X)ᵒᵖ Coeff.{u}).map i.op) (.up ℤ)).app
    (((TopCat.Sheaf.forget Coeff.{u} X).mapHomologicalComplex (.up ℤ)).obj (sheafComplex X))

namespace Expected

def SectionsRestrictionType := ∀ {X : TopCat.{u}} {V U : Opens X},
  (V ⟶ U) → (evaluatedComplex U ⟶ evaluatedComplex V)

/-- The two restrictions commute with the actual sheafification map. -/
def RestrictionNaturality : Prop :=
  ∀ {X : TopCat.{u}} {V U : Opens X} (i : V ⟶ U),
    (ordinaryCochainFunctor ℚ Values.{u}).map ((Opens.toTopCat X).map i).op ≫ sectionMap V =
      sectionMap U ≫ sectionsRestriction i

/-- A cochain sheafifies to zero exactly when it vanishes on all simplices
whose image lies in a member of some open cover of the given open set. -/
def KernelCharacterization : Prop :=
  ∀ {X : TopCat.{u}} (U : Opens X) (q : ℕ)
    (c : (ordinaryCochains ℚ Values.{u} (TopCat.of U)).X (q : ℤ)),
    (sectionMap U).f (q : ℤ) c = 0 ↔
      ∃ (ι : Type u) (cover : OpenCover (TopCat.of U) ι),
        ∀ (s : SimplexIn U q) (i : ι), Set.range s ⊆ cover.sets i →
          coordinates U q c s = 0

/-- On every open of a second-countable locally compact Hausdorff space,
the sheafification map on ordinary rational singular cochains is a quasi-isomorphism. -/
def Comparison : Prop :=
  ∀ (X : TopCat.{u}) [SecondCountableTopology X] [LocallyCompactSpace X] [T2Space X]
    (U : Opens X), QuasiIso (sectionMap U)

end Expected
end RepTheorySurvey.Geometric.Analytic.SmallCochains
