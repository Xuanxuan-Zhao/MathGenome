import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.MinusculeAndTwoStep
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.ProjectiveSpaces
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.LinearAlgebra.TensorProduct.Prod

namespace RepTheorySurvey.Geometric.ConvolutionBundleSpecs

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups (Points SchemeOver TestAlgebra mapPoints)
open LinearAlgebraicGroups.Specs.GrassmannianCharts (coordinates)
open LatticeModelSpecs BoundedLatticeSpecs MinusculeAndTwoStepSpecs
open scoped MatrixGroups TensorProduct

abbrev LatticeQuotient (L : GL2Lattice) (P : Submodule O L.val) :=
  @HasQuotient.Quotient _ _ (@Submodule.hasQuotient O (L.val : Type)
    inferInstance inferInstance inferInstance) P

def latticeQuotientMk (L : GL2Lattice) (P : Submodule O L.val) (x : L.val) :
    LatticeQuotient L P :=
  @Submodule.Quotient.mk O (L.val : Type) inferInstance inferInstance inferInstance P x

/-- The relative quotient for a pair of lattices with the second contained in the first. -/
abbrev RelativeQuotient (L₁ L₂ : GL2Lattice) :=
  LatticeQuotient L₁ (L₂.val.comap L₁.val.subtype)

/-- Flags of the actual Laurent-series lattices with successive colength one. -/
def IsFlag (L : GL2Lattice × GL2Lattice) : Prop :=
  L.1 ∈ colength 1 ∧ L.2.val ≤ L.1.val ∧
    Module.Finite ℂ (RelativeQuotient L.1 L.2) ∧
    Module.finrank ℂ (RelativeQuotient L.1 L.2) = 1

abbrev Flags := { L : GL2Lattice × GL2Lattice // IsFlag L }

abbrev Loop := GL (Fin 2) K
abbrev Positive := GL (Fin 2) O

def firstStage : Set (Grassmannian (PositiveGL 2)) :=
  {c | ∃ g : Loop, coset (PositiveGL 2) g = c ∧ g • standardLattice 2 ∈ colength 1}

abbrev OrderedProduct (h : StableStage (PositiveGL 2) (colength 1)) :=
  TwistedProduct (PositiveGL 2) firstStage (colength 1) h

/-- The map from the shared twisted product is given on every representative by
its first lattice and the translate of its second modification. -/
def TwistedFlags : Prop :=
  ∃ h : StableStage (PositiveGL 2) (colength 1),
    ∃ e : OrderedProduct h ≃ Flags,
      (∀ p : Representatives (PositiveGL 2) firstStage (colength 1),
        (e (Quotient.mk (twistRel (PositiveGL 2) firstStage (colength 1)) p)).val =
          (p.val.1 • standardLattice 2, p.val.1 • p.val.2)) ∧
      (∀ F : Flags,
        F.val.2 ∈ colength 2 ∧ (scalarLattice 2 2).val ≤ F.val.2.val ∧
        Submodule.map (t • (LinearMap.id : Coordinates 2 →ₗ[O] Coordinates 2))
          F.val.1.val ≤ F.val.2.val)

abbrev IncidenceAmbient : SchemeOver ℂ := projectiveScheme ⨯ twoStepScheme

def firstPlane (p : ProjectivePoints) : Submodule ℂ V :=
  grassmannianSubspace projectiveBasis projectiveRank p

def secondPlane (p : Points twoStepScheme complexAlgebra) : Submodule ℂ (V × V) :=
  grassmannianSubspace twoStepBasis twoStepRank (p ≫ twoStepSchemeInGrassmannian)

/-- The first lattice modulo t² has coefficients in S × V, and its
t-multiple modulo t² is 0 × S. -/
def IncidenceCondition (S : Submodule ℂ V) (P : Submodule ℂ (V × V)) : Prop :=
  (⊥ : Submodule ℂ V).prod S ≤ P ∧ P ≤ S.prod ⊤

def incidenceLocus : Set (Points IncidenceAmbient complexAlgebra) :=
  {q | IncidenceCondition
    (firstPlane (q ≫ prod.fst)) (secondPlane (q ≫ prod.snd))}

/-- The reduced incidence scheme, retaining its embedding in the product with
the shared two-step Schubert model. -/
def incidenceScheme : SchemeOver ℂ := reducedClosureScheme IncidenceAmbient incidenceLocus

def incidenceInclusion : incidenceScheme ⟶ IncidenceAmbient :=
  reducedClosureInclusion IncidenceAmbient incidenceLocus

def firstProjection : incidenceScheme ⟶ projectiveScheme := incidenceInclusion ≫ prod.fst

def terminalProjection : incidenceScheme ⟶ twoStepScheme := incidenceInclusion ≫ prod.snd

def incidenceCoordinates (q : Points incidenceScheme complexAlgebra) :
    ProjectivePoints × GrassmannianPoints twoStepBasis twoStepRank :=
  (q ≫ firstProjection, q ≫ terminalProjection ≫ twoStepSchemeInGrassmannian)

instance incidenceAnalyticTopology : TopologicalSpace (Points incidenceScheme complexAlgebra) :=
  TopologicalSpace.induced incidenceCoordinates
    (inferInstanceAs (TopologicalSpace (ProjectivePoints ×
      GrassmannianPoints twoStepBasis twoStepRank)))

/-- Both projections agree with the actual lattices in the length-one and
length-two windows. In particular the second projection is convolution. -/
def LatticeIncidence : Prop :=
  IsReduced incidenceScheme.left ∧ IsClosedImmersion incidenceInclusion.left ∧
  ∃ e : Flags ≃ₜ Points incidenceScheme complexAlgebra,
    ∀ L : Flags,
      firstPlane (e L ≫ firstProjection) =
        (latticeSubspace 0 1 L.val.1).map constantCoordinates.toLinearMap ∧
      secondPlane (e L ≫ terminalProjection) =
        (latticeSubspace 0 2 L.val.2).map twoStepCoordinates.toLinearMap

/-- The coefficients of a vector of a first lattice, taken modulo t²L₀. -/
def firstLatticeCoefficients (L : Colength 1) (x : L.val.val) : V × V :=
  let v : (scalarLattice 2 0).val := ⟨x.val, L.property.1 x.property⟩
  twoStepCoordinates (latticeQuotientMk (scalarLattice 2 0) (windowLower 2 0 2) v)

def firstLatticeShift (L : Colength 1) : Submodule O L.val.val :=
  (t • (LinearMap.id : L.val.val →ₗ[O] L.val.val)).range

/-- Constant and linear coefficients induce the stated splitting of L₁/tL₁. -/
def FirstLatticeQuotient : Prop :=
  ∀ L : Colength 1,
    let S := (latticeSubspace 0 1 L.val).map constantCoordinates.toLinearMap
    ∃ e : LatticeQuotient L.val (firstLatticeShift L) ≃ₗ[ℂ] (S × (V ⧸ S)),
      ∀ x : L.val.val,
        (e (latticeQuotientMk L.val (firstLatticeShift L) x)).1.val = (firstLatticeCoefficients L x).1 ∧
        (e (latticeQuotientMk L.val (firstLatticeShift L) x)).2 = S.mkQ (firstLatticeCoefficients L x).2

abbrev Coefficients (R : TestAlgebra ℂ) := R ⊗[ℂ] V

def tautological (R : TestAlgebra ℂ) (p : Points projectiveScheme R) :
    Submodule R (Coefficients R) :=
  ((grassmannianCharts projectiveBasis projectiveRank).affinePoints.hom.app R p).toSubmodule

def twoStepAffinePlane (R : TestAlgebra ℂ) (p : Points twoStepScheme R) :
    Submodule R (Coefficients R × Coefficients R) :=
  (((grassmannianCharts twoStepBasis twoStepRank).affinePoints.hom.app R
    (p ≫ twoStepSchemeInGrassmannian)).toSubmodule).map
      (TensorProduct.prodRight ℂ R R V V).toLinearMap

abbrev BundleFiber (R : TestAlgebra ℂ) (S : Submodule R (Coefficients R)) :=
  S × (Coefficients R ⧸ S)

/-- The quotient of S × V by 0 × S is the bundle fibre S ⊕ t(V/S). -/
def bundleQuotient (R : TestAlgebra ℂ) (S : Submodule R (Coefficients R)) :
    (S.prod (⊤ : Submodule R (Coefficients R))) →ₗ[R] BundleFiber R S where
  toFun v := (⟨v.val.1, v.property.1⟩, S.mkQ v.val.2)
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/-- The standard determinant on the two coefficient vectors. -/
def volume (R : TestAlgebra ℂ) (x y : Coefficients R) : R :=
  let c := coordinates (Pi.basisFun ℂ (Fin 2)) R
  c x 0 * c y 1 - c x 1 * c y 0

/-- Lines in S ⊕ t(V/S). The rank-one projective quotient convention here
defines lines since the ambient module is locally free of rank two. -/
abbrev BundleLine (R : TestAlgebra ℂ) (p : Points projectiveScheme R) :=
  Module.Grassmannian R (BundleFiber R (tautological R p)) 1

def coefficientChange {R T : TestAlgebra ℂ} (a : R ⟶ T) :
    Coefficients R →ₗ[ℂ] Coefficients T :=
  TensorProduct.map a.hom.toLinearMap LinearMap.id

/-- The change of base of a line, described as the span of the coefficient
images of the inverse-image plane. This description uses any representative
of the linear coefficient modulo the tautological line. -/
def changeBundleLine {R T : TestAlgebra ℂ} (a : R ⟶ T)
    {p : Points projectiveScheme R} {p' : Points projectiveScheme T} (B : BundleLine R p) :
    Submodule T (BundleFiber T (tautological T p')) :=
  Submodule.span T {z | ∃ (x : tautological R p) (y : Coefficients R),
    (x, (tautological R p).mkQ y) ∈ B.toSubmodule ∧
    ∃ hx : coefficientChange a x.val ∈ tautological T p',
      z = (⟨coefficientChange a x.val, hx⟩, (tautological T p').mkQ (coefficientChange a y))}

/-- Representation on affine tests of the projective bundle of lines. The
second plane is an inverse image on every test ring, and the determinant
identifies the complementary quotient with the dual of the tautological line. -/
def ProjectiveBundle : Prop :=
  (∀ (R : TestAlgebra ℂ) (p : Points projectiveScheme R),
    let S := tautological R p
    ∃ e : (Coefficients R ⧸ S) ≃ₗ[R] Module.Dual R S,
      ∀ (x : S) (y : Coefficients R), e (S.mkQ y) x = volume R x.val y) ∧
  ∃ e : ∀ R : TestAlgebra ℂ,
    Points incidenceScheme R ≃ (Σ p : Points projectiveScheme R, BundleLine R p),
    (∀ (R : TestAlgebra ℂ) (q : Points incidenceScheme R),
      (e R q).1 = q ≫ firstProjection ∧
      let S := tautological R (e R q).1
      twoStepAffinePlane R (q ≫ terminalProjection) =
        (((e R q).2.toSubmodule.comap (bundleQuotient R S)).map (S.prod ⊤).subtype)) ∧
    (∀ {R T : TestAlgebra ℂ} (a : R ⟶ T) (q : Points incidenceScheme R),
      (e T (mapPoints a q)).2.toSubmodule =
        changeBundleLine a (p' := (e T (mapPoints a q)).1) (e R q).2)

/-- Smoothness, projectivity over ℂ, and properness of the incidence projection. -/
def SurfaceGeometry : Prop :=
  Smooth incidenceScheme.hom ∧
  (∃ (n : ℕ) (j : incidenceScheme ⟶
      LinearAlgebraicGroups.Specs.ProjectiveSpaces.coordinateProjectiveSpace ℂ (Fin (n + 1))),
    IsClosedImmersion j.left) ∧
  IsProper terminalProjection.left

/-- The induced action is given by multiplication on both subspaces modulo
t². For positive loops it is the original diagonal action on the flags. -/
def FlagJetAction : Prop :=
  ∃ ρ : MulAction (GLJets 2 2 (by omega)) Flags,
    (∀ (g : GLJets 2 2 (by omega)) (L : Flags),
      latticeSubspace 0 2 (ρ.smul g L).val.1 =
        (latticeSubspace 0 2 L.val.1).map (windowJetLinear 0 (le_refl 2) g.val) ∧
      latticeSubspace 0 2 (ρ.smul g L).val.2 =
        (latticeSubspace 0 2 L.val.2).map (windowJetLinear 0 (le_refl 2) g.val)) ∧
    (∀ (g : Positive) (L : Flags),
      (ρ.smul (reduceGL 2 2 (by omega) g) L).val =
        (positiveGLMap 2 g • L.val.1, positiveGLMap 2 g • L.val.2))

end

end RepTheorySurvey.Geometric.ConvolutionBundleSpecs
