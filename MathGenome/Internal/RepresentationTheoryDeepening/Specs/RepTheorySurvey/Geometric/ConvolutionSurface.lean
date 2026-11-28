import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionBundle
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.KrullDimension

namespace RepTheorySurvey.Geometric.ConvolutionSurfaceSpecs

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open LinearAlgebraicGroups (Points SchemeOver TestAlgebra mapPoints testSpec)
open LinearAlgebraicGroups.Specs.GrassmannianCharts (coordinates)
open LatticeModelSpecs MinusculeAndTwoStepSpecs ConvolutionBundleSpecs
open scoped TensorProduct

/-- The ordered product, the actual lattice flags, and their common projective
bundle model, with the proper projection to the last lattice. -/
def SurfaceIdentification : Prop :=
  TwistedFlags ∧ LatticeIncidence ∧ FirstLatticeQuotient ∧ ProjectiveBundle ∧ SurfaceGeometry

abbrev complexPointScheme : SchemeOver ℂ := (testSpec ℂ).obj (op complexAlgebra)

def toComplexPoint (Y : SchemeOver ℂ) : Y ⟶ complexPointScheme :=
  Over.homMk Y.hom (by
    rw [AlgebraicGeometry.algSpec_obj_hom]
    change Y.hom ≫ Spec.map (𝟙 (CommRingCat.of ℂ)) = Y.hom
    rw [AlgebraicGeometry.Spec.map_id, Category.comp_id])

/-- The closed point with terminal lattice tL₀, in the shared Schubert model. -/
def ScalarTerminalPoint (x : Points twoStepScheme complexAlgebra) : Prop :=
  IsClosedImmersion x.left ∧
  secondPlane x = (latticeSubspace 0 2 scalarPoint).map twoStepCoordinates.toLinearMap ∧
  secondPlane x = (⊥ : Submodule ℂ V).prod ⊤

def openOver {X : SchemeOver ℂ} (U : X.left.Opens) : SchemeOver ℂ :=
  Over.mk (U.ι ≫ X.hom)

def openOverInclusion {X : SchemeOver ℂ} (U : X.left.Opens) : openOver U ⟶ X :=
  Over.homMk U.ι rfl

/-- Over the open orbit the base change of convolution is an isomorphism.
On affine tests the inverse takes the constant-coefficient image of the
terminal plane as the first line. In lattice terms this is L₂ + tL₀. -/
def OpenOrbitIsomorphism : Prop :=
  ∃ (x : Points twoStepScheme complexAlgebra) (U : twoStepScheme.left.Opens),
    ScalarTerminalPoint x ∧
    (U : Set twoStepScheme.left) = {pointLocation x}ᶜ ∧
    (∀ (p : Points twoStepScheme complexAlgebra) (L : Colength 2),
      secondPlane p = (latticeSubspace 0 2 L.val).map twoStepCoordinates.toLinearMap →
      (pointLocation p ∈ U ↔ L.val ∈ gl2Orbit twoStepPair)) ∧
    let j := openOverInclusion U
    let Y := pullback terminalProjection j
    let i : Y ⟶ incidenceScheme := pullback.fst terminalProjection j
    ∃ e : Y ≅ openOver U,
      e.hom = pullback.snd terminalProjection j ∧
      (∀ (R : TestAlgebra ℂ) (p : Points (openOver U) R),
        tautological R (p ≫ e.inv ≫ i ≫ ConvolutionBundleSpecs.firstProjection) =
          (twoStepAffinePlane R (p ≫ j)).map
            (LinearMap.fst R (Coefficients R) (Coefficients R))) ∧
      ∀ (p : Points (openOver U) complexAlgebra) (F : Flags),
        firstPlane (p ≫ e.inv ≫ i ≫ ConvolutionBundleSpecs.firstProjection) =
          (latticeSubspace 0 1 F.val.1).map constantCoordinates.toLinearMap →
        secondPlane (p ≫ j) =
          (latticeSubspace 0 2 F.val.2).map twoStepCoordinates.toLinearMap →
        F.val.1.val = F.val.2.val ⊔ scalarPoint.val

/-- The section corresponding to the summand t(V/S), with the
scheme-theoretic fibre square over the indicated terminal point. -/
def ExceptionalSection (x : Points twoStepScheme complexAlgebra)
    (s : projectiveScheme ⟶ incidenceScheme) : Prop :=
  ScalarTerminalPoint x ∧
  IsClosedImmersion s.left ∧
  s ≫ ConvolutionBundleSpecs.firstProjection = 𝟙 projectiveScheme ∧
  IsPullback s (toComplexPoint projectiveScheme) terminalProjection x ∧
  ∀ (R : TestAlgebra ℂ) (p : Points projectiveScheme R) (B : BundleLine R p),
    let S := tautological R p
    twoStepAffinePlane R (p ≫ s ≫ terminalProjection) =
      ((B.toSubmodule.comap (bundleQuotient R S)).map (S.prod ⊤).subtype) ↔
      B.toSubmodule = (⊥ : Submodule R S).prod ⊤

/-- The analytic fibre has its topology from the shared incidence space.
Codimension is the height of the closed point in the Schubert surface. -/
def ExceptionalFibre : Prop :=
  ∃ (x : Points twoStepScheme complexAlgebra) (s : projectiveScheme ⟶ incidenceScheme),
    ExceptionalSection x s ∧
    (∃ e : ProjectivePoints ≃ₜ
        {q : Points incidenceScheme complexAlgebra // q ≫ terminalProjection = x},
      ∀ p, (e p).val = p ≫ s) ∧
    topologicalKrullDim projectiveScheme.left = 1 ∧
    Order.coheight (pointLocation x) = 2 ∧
    (↑(Order.coheight (pointLocation x)) : WithBot ℕ∞) =
      topologicalKrullDim projectiveScheme.left + topologicalKrullDim projectiveScheme.left

/-- The fibres of Hom(t(V/S), S), using the shared coefficient of t. -/
abbrev NormalLinearMaps (R : TestAlgebra ℂ) (p : Points projectiveScheme R) :=
  (Coefficients R ⧸ tautological R p) →ₗ[R] tautological R p

def graphEndomorphism {R : TestAlgebra ℂ} {p : Points projectiveScheme R}
    (f : NormalLinearMaps R p) : Coefficients R →ₗ[R] Coefficients R :=
  (tautological R p).subtype.comp (f.comp (tautological R p).mkQ)

def graphPlane {R : TestAlgebra ℂ} {p : Points projectiveScheme R}
    (f : NormalLinearMaps R p) : Submodule R (Coefficients R × Coefficients R) :=
  ((graphEndomorphism f).prod LinearMap.id).range

/-- The first infinitesimal neighbourhood cut out by the square of the ideal
of a section inside its graph chart. -/
def firstNeighbourhood {X : SchemeOver ℂ} (s : projectiveScheme ⟶ X) : SchemeOver ℂ :=
  Over.mk ((s.left.ker ^ 2).subschemeι ≫ X.hom)

def firstNeighbourhoodInclusion {X : SchemeOver ℂ} (s : projectiveScheme ⟶ X) :
    firstNeighbourhood s ⟶ X :=
  Over.homMk (s.left.ker ^ 2).subschemeι rfl

/-- Products of entries generate the square of the ideal of the zero
section in the graph coordinates. -/
def GraphEntriesSquareZero {R : TestAlgebra ℂ} {p : Points projectiveScheme R}
    (f : NormalLinearMaps R p) : Prop :=
  let c := coordinates (Pi.basisFun ℂ (Fin 2)) R
  let m := fun (i j : Fin 2) ↦ c (graphEndomorphism f (c.symm (Pi.single j 1))) i
  ∀ i j k l, m i j * m k l = 0

/-- The actual incidence neighbourhood of the exceptional section is the
total space of Hom(t(V/S), S). On every affine test, the isomorphism gives the
graph in the same terminal plane coordinates. Its zero section and first
infinitesimal neighbourhood identify the algebraic normal bundle. The
determinant identifies it with the tensor square of the tautological line. -/
def ExceptionalNormalBundle : Prop :=
  ∃ (x : Points twoStepScheme complexAlgebra) (s : projectiveScheme ⟶ incidenceScheme),
    ExceptionalSection x s ∧
    ∃ (U : incidenceScheme.left.Opens) (sU : projectiveScheme ⟶ openOver U),
      sU ≫ openOverInclusion U = s ∧
      (∀ (R : TestAlgebra ℂ) (q : Points incidenceScheme R),
        (∃ r : Points (openOver U) R, r ≫ openOverInclusion U = q) ↔
          Function.Bijective (fun z : twoStepAffinePlane R (q ≫ terminalProjection) ↦ z.val.2)) ∧
      ∃ e : ∀ R : TestAlgebra ℂ,
          Points (openOver U) R ≃ (Σ p : Points projectiveScheme R, NormalLinearMaps R p),
        (∀ (R : TestAlgebra ℂ) (q : Points (openOver U) R),
          (e R q).1 = q ≫ openOverInclusion U ≫ ConvolutionBundleSpecs.firstProjection ∧
          twoStepAffinePlane R (q ≫ openOverInclusion U ≫ terminalProjection) =
            graphPlane (e R q).2) ∧
        (∀ (R : TestAlgebra ℂ) (p : Points projectiveScheme R),
          e R (p ≫ sU) = ⟨p, 0⟩) ∧
        (∀ {R T : TestAlgebra ℂ} (a : R ⟶ T) (q : Points (openOver U) R)
          (v : Coefficients R),
          graphEndomorphism (e T (mapPoints a q)).2 (coefficientChange a v) =
            coefficientChange a (graphEndomorphism (e R q).2 v)) ∧
        (∀ (R : TestAlgebra ℂ) (q : Points (openOver U) R),
          (∃ r : Points (firstNeighbourhood sU) R, r ≫ firstNeighbourhoodInclusion sU = q) ↔
            GraphEntriesSquareZero (e R q).2) ∧
        ∀ (R : TestAlgebra ℂ) (p : Points projectiveScheme R),
          let S := tautological R p
          ∃ h : (S ⊗[R] S) ≃ₗ[R] NormalLinearMaps R p,
            ∀ (u v : S) (w : Coefficients R),
              h (u ⊗ₜ[R] v) (S.mkQ w) = volume R v.val w • u

end

end RepTheorySurvey.Geometric.ConvolutionSurfaceSpecs
