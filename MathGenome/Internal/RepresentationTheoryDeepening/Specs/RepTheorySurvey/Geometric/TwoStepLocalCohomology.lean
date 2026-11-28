import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.NilpotentConeChart
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConstantSheafComparison
import Mathlib.CategoryTheory.Functor.Const

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open P202Specs.CohomologyPairs P202Specs.RelativeSingularChains
open scoped ZeroObject

namespace RepTheorySurvey.Geometric.TwoStepLocalCohomologySpecs

open LatticeModelSpecs NilpotentConeChartSpecs
open Analytic Analytic.ConstantSheafCohomology Analytic.SingularCochains

abbrev ChartSpace := TopCat.of shortLatticeChartSet
abbrev PositiveRadius := {r : ℝ // 0 < r}

/-- The actual second projection chart of the colength-two lattice stage. -/
structure RadialChart where
  isOpen : IsOpen shortLatticeChartSet
  toLattice : Cone ≃ₜ shortLatticeChartSet
  graphCoordinates : ∀ z : Cone, latticeSubspace 0 2 (toLattice z).val.val =
    grassmannianSubspace (windowBasis 2 0 2) (windowDimension_le shortDimension)
      (shortGraphPoint (graphCoefficientMatrix z.val.1 z.val.2.1 z.val.2.2))
  vertex_eq : (toLattice coneVertex).val.val = scalarLattice 2 1

abbrev RadialChart.vertex (c : RadialChart) : ChartSpace := c.toLattice coneVertex

theorem RadialChart.closedVertex (c : RadialChart) : IsClosed ({c.vertex} : Set ChartSpace) := by
  have h : c.toLattice.symm ⁻¹' ({coneVertex} : Set Cone) = {c.vertex} := by
    ext x
    exact c.toLattice.symm_apply_eq
  rw [← h]
  exact (isClosed_singleton (x := coneVertex)).preimage c.toLattice.symm.continuous

private theorem continuous_radialSize : Continuous radialSize := by
  unfold radialSize
  exact Real.continuous_sqrt.comp
    ((continuous_fst.comp (continuous_snd.comp continuous_subtype_val)).norm.add
      (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)).norm)

/-- The opens cut out by the radial norm of the quadratic parametrization. -/
def RadialChart.balls (c : RadialChart) : PositiveRadius ⥤ Opens ChartSpace :=
  Monotone.functor (f := fun r ↦
    ⟨{x | radialSize (c.toLattice.symm x) < r.val},
      isOpen_lt (continuous_radialSize.comp c.toLattice.symm.continuous) continuous_const⟩)
    (by
      intro r s h x hx
      change radialSize (c.toLattice.symm x) < r.val at hx
      change radialSize (c.toLattice.symm x) < s.val
      exact hx.trans_le (show r.val ≤ s.val from h))

/-- Complementing a fixed closed set in an open commutes with inclusion of opens. -/
def withoutClosed {X : TopCat} {Z : Set X} (hZ : IsClosed Z) : Opens X ⥤ Opens X :=
  Monotone.functor (f := fun U ↦ U ⊓ complementOpen Z hZ)
    (fun _ _ h ↦ inf_le_inf_right _ h)

/-- The pair of an open and its complement of a fixed closed support. -/
def openPairs {X : TopCat} {Z : Set X} (hZ : IsClosed Z) : Opens X ⥤ Pair where
  obj U := openPair (homOfLE inf_le_left : (withoutClosed hZ).obj U ⟶ U)
  map j := openPairInclusion (homOfLE inf_le_left) (homOfLE inf_le_left)
    j ((withoutClosed hZ).map j)
  map_id U := PairMap.ext _ _ ((Opens.toTopCat X).map_id U)
  map_comp j k := PairMap.ext _ _ ((Opens.toTopCat X).map_comp j k)

abbrev RadialChart.puncturedBalls (c : RadialChart) : PositiveRadius ⥤ Opens ChartSpace :=
  c.balls ⋙ withoutClosed c.closedVertex

abbrev RadialChart.pairs (c : RadialChart) : PositiveRadius ⥤ Pair :=
  c.balls ⋙ openPairs c.closedVertex

abbrev singularOnOpens (X : TopCat) (q : ℤ) :=
  (Opens.toTopCat X).op ⋙ ordinaryCohomologyFunctor ℚ Values.{0} q

abbrev singularSupported {X : TopCat} {Z : Set X} (hZ : IsClosed Z) (q : ℤ) :=
  (openPairs hZ).op ⋙ relativeCohomologyFunctor ℚ Values.{0} q

abbrev sheafOnOpens (X : TopCat) (q : ℤ) :=
  LocalSheaf.derivedOpenCohomology (𝟭 (Sheaves X))
    (LocalSheaf.sheafInDegreeZero (rational X)) q

abbrev sheafSupported {X : TopCat} {Z : Set X} (hZ : IsClosed Z) (q : ℤ) :=
  LocalSheaf.derivedOpenCohomology (extraordinaryInverseImage hZ ⋙ directImage (closedInclusion Z))
    (LocalSheaf.sheafInDegreeZero (rational X)) q

/-- The topology hypotheses of the constant-sheaf comparison. -/
def ComparisonTopology (X : TopCat) : Prop :=
  SecondCountableTopology X ∧ LocallyCompactSpace X ∧ T2Space X ∧ HasContractibleOpenBasis X

abbrev RadialChart.absolute (c : RadialChart) (q : ℤ) :=
  c.balls.op ⋙ singularOnOpens ChartSpace q

abbrev RadialChart.punctured (c : RadialChart) (q : ℤ) :=
  c.puncturedBalls.op ⋙ singularOnOpens ChartSpace q

abbrev RadialChart.relative (c : RadialChart) (q : ℤ) :=
  c.balls.op ⋙ singularSupported c.closedVertex q

/-- Restriction from each ball to its punctured open, on actual singular cohomology. -/
def RadialChart.restriction (c : RadialChart) (q : ℤ) (r : PositiveRadius) :
    (c.absolute q).obj (op r) ⟶ (c.punctured q).obj (op r) :=
  (singularOnOpens ChartSpace q).map
    (homOfLE inf_le_left : c.puncturedBalls.obj r ⟶ c.balls.obj r).op

/-- The rational cohomology value in a specified set of integer degrees. -/
def cohomologyValue (degrees : Finset ℤ) (q : ℤ) : Coeff.{0} :=
  if q ∈ degrees then ModuleCat.of ℚ ℚ else 0

abbrev constantValue (degrees : Finset ℤ) (q : ℤ) : PositiveRadiusᵒᵖ ⥤ Coeff.{0} :=
  (Functor.const _).obj (cohomologyValue degrees q)

def degreeZeroValueIso : cohomologyValue {0, 3} 0 ≅ cohomologyValue {0} 0 :=
  eqToIso (by simp [cohomologyValue])

/-- The actual analytic group GL₂(ℂ[[t]]/(t²)). -/
abbrev JetGroup := TopCat.of (GLJets 2 2 (by decide))

abbrev JetChart (D : Opens JetGroup) := TopCat.of (D × ChartSpace)

def jetBall (c : RadialChart) (D : Opens JetGroup) (r : PositiveRadius) : Opens (JetChart D) :=
  ⟨Prod.snd ⁻¹' (c.balls.obj r : Set ChartSpace), (c.balls.obj r).isOpen.preimage continuous_snd⟩

theorem jetSupportClosed (c : RadialChart) (D : Opens JetGroup) :
    IsClosed (Prod.snd ⁻¹' ({c.vertex} : Set ChartSpace) : Set (JetChart D)) :=
  c.closedVertex.preimage continuous_snd

abbrev jetPair (c : RadialChart) (D : Opens JetGroup) (r : PositiveRadius) : Pair :=
  (openPairs (jetSupportClosed c D)).obj (jetBall c D r)

/-- Projection of the product radial pair to the lattice radial pair. -/
def jetPairProjection (c : RadialChart) (D : Opens JetGroup) (r : PositiveRadius) :
    jetPair c D r ⟶ c.pairs.obj r :=
  ⟨TopCat.ofHom ⟨fun x ↦ ⟨x.val.2, x.property⟩,
      (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩,
    fun _ hx ↦ hx⟩

namespace Expected

/-- Radial opens give a nested cofinal neighborhood basis in the actual lattice
stage, as well as in the open chart. -/
def RadialNeighborhoodBasis : Prop :=
  ∃ c : RadialChart,
    (nhds c.vertex).HasBasis (fun _ : PositiveRadius ↦ True)
      (fun r ↦ (c.balls.obj r : Set ChartSpace)) ∧
    (nhds c.vertex.val).HasBasis (fun _ : PositiveRadius ↦ True)
      (fun r ↦ Subtype.val '' (c.balls.obj r : Set ChartSpace))

/-- Ordinary and relative singular cohomology on the entire nested radial basis.
The natural isomorphisms identify all shrinking maps with identity maps. -/
def RadialSingularCohomology : Prop :=
  ∀ c : RadialChart,
    ∃ (e : ∀ q : ℤ, c.absolute q ≅ constantValue {0} q)
      (f : ∀ q : ℤ, c.punctured q ≅ constantValue {0, 3} q)
      (_g : ∀ q : ℤ, c.relative q ≅ constantValue {4} q),
      ∀ r : PositiveRadius, IsIso (c.restriction 0 r) ∧
        c.restriction 0 r ≫ (f 0).hom.app (op r) ≫ degreeZeroValueIso.hom =
          (e 0).hom.app (op r)

/-- Comparison with sections of the actual constant sheaf and sections supported
at the vertex, naturally in the opens and hence along the radial basis. -/
def RadialSheafCohomology : Prop :=
  ∀ c : RadialChart,
    ComparisonTopology ChartSpace ∧
    (∀ r : PositiveRadius, ComparisonTopology (TopCat.of (c.balls.obj r)) ∧
      ComparisonTopology (TopCat.of (c.puncturedBalls.obj r))) ∧
    ∀ q : ℤ,
      Nonempty (singularOnOpens ChartSpace q ≅ sheafOnOpens ChartSpace q) ∧
      Nonempty (singularSupported c.closedVertex q ≅ sheafSupported c.closedVertex q)

/-- A contractible open in the two-jet group contributes no extra relative
cohomology. The comparison is induced by projection from the product pair. -/
def JetProductCohomology : Prop :=
  ∀ (c : RadialChart) (D : Opens JetGroup),
    ContractibleSpace D →
    ComparisonTopology (JetChart D) ∧
    ∀ q : ℤ,
      Nonempty (singularSupported (jetSupportClosed c D) q ≅
        sheafSupported (jetSupportClosed c D) q) ∧
      ∀ r : PositiveRadius,
        IsIso ((relativeCohomologyFunctor ℚ Values.{0} q).map (jetPairProjection c D r).op) ∧
        Nonempty (relativeCohomology ℚ Values.{0} (jetPair c D r) q ≅ cohomologyValue {4} q)

end Expected
end RepTheorySurvey.Geometric.TwoStepLocalCohomologySpecs
