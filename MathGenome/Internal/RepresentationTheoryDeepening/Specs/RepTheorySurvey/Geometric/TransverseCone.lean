import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.ConvolutionSurface
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.NilpotentConeChart

namespace RepTheorySurvey.Geometric.TransverseConeSpecs

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open LinearAlgebraicGroups (Points SchemeOver TestAlgebra mapPoints testSpec)
open LinearAlgebraicGroups.Specs.GrassmannianCharts (chartScheme coordinates)
open LatticeModelSpecs MinusculeAndTwoStepSpecs ConvolutionBundleSpecs ConvolutionSurfaceSpecs
open NilpotentConeChartSpecs
open scoped TensorProduct unitInterval

abbrev coneScheme : SchemeOver ℂ :=
  (testSpec ℂ).obj (op (CommAlgCat.of ℂ ConeCoordinateRing))

/-- The quadratic coordinates, viewed in the second-projection pivot chart. -/
def coneInPivot : coneScheme ⟶ chartScheme (k := ℂ) secondPivot :=
  (testSpec ℂ).map (CommAlgCat.ofHom quadraticChartHom).op

def coneEvaluation (z : Cone) : ConeCoordinateRing →ₐ[ℂ] ℂ := by
  let f : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] ℂ :=
    MvPolynomial.aeval ![z.val.1, z.val.2.1, z.val.2.2]
  refine Ideal.Quotient.liftₐ quadraticIdeal f ?_
  have h : quadraticIdeal ≤ RingHom.ker f.toRingHom := by
    rw [quadraticIdeal, Ideal.span_singleton_le_iff_mem]
    change f quadraticEquation = 0
    simpa [f, quadraticEquation] using z.property
  exact fun p hp ↦ h hp

def conePoint (z : Cone) : Points coneScheme complexAlgebra :=
  (testSpec ℂ).map (CommAlgCat.ofHom (coneEvaluation z)).op

def conePointCoordinate {R : TestAlgebra ℂ} (q : Points coneScheme R) (i : Fin 3) : R :=
  ((algSpec.fullyFaithful (R := CommRingCat.of ℂ)).preimage q).unop.hom (coneCoordinate i)

/-- The terminal endomorphism on the actual coefficients after extension of scalars. -/
def coneEndomorphism {R : TestAlgebra ℂ} (q : Points coneScheme R) :
    Coefficients R →ₗ[R] Coefficients R :=
  let b := coordinates (Pi.basisFun ℂ (Fin 2)) R
  let A := graphCoefficientMatrix (conePointCoordinate q 0) (conePointCoordinate q 1)
    (conePointCoordinate q 2)
  b.symm.toLinearMap.comp ((Matrix.toLin' A).comp b.toLinearMap)

/-- The second pivot on the shared reduced Schubert scheme. -/
def IsTerminalConeChart (c : coneScheme ⟶ twoStepScheme) : Prop :=
  IsOpenImmersion c.left ∧
    IsPullback coneInPivot c ((grassmannianCharts twoStepBasis twoStepRank).chart secondPivot)
      twoStepSchemeInGrassmannian

/-- In the coefficient window the two lattice inclusions give precisely the
image and kernel conditions on the actual first line. -/
def WindowContainments : Prop :=
  ∀ (L₁ : Colength 1) (L₂ : ShortLatticeStage) (A : V →ₗ[ℂ] V),
    (latticeSubspace 0 2 L₂.val).map twoStepCoordinates.toLinearMap =
      (A.prod LinearMap.id).range →
    let S := (latticeSubspace 0 1 L₁.val).map constantCoordinates.toLinearMap
    (L₂.val.val ≤ L₁.val.val ↔ A.range ≤ S) ∧
    (Submodule.map (t • (LinearMap.id : Coordinates 2 →ₗ[O] Coordinates 2))
      L₁.val.val ≤ L₂.val.val ↔ S ≤ A.ker)

/-- Pulling back convolution along the entire affine chart retains both maps. -/
abbrev ChartInverseImage (c : coneScheme ⟶ twoStepScheme) :=
  pullback terminalProjection c

def InverseImageBundle (c : coneScheme ⟶ twoStepScheme)
    (s : projectiveScheme ⟶ incidenceScheme) : Prop :=
  let Y := ChartInverseImage c
  let i : Y ⟶ incidenceScheme := pullback.fst terminalProjection c
  let m : Y ⟶ coneScheme := pullback.snd terminalProjection c
  ∃ (sY : projectiveScheme ⟶ Y)
    (e : ∀ R : TestAlgebra ℂ,
      Points Y R ≃ (Σ p : Points projectiveScheme R, NormalLinearMaps R p)),
    sY ≫ i = s ∧ sY ≫ m = toComplexPoint projectiveScheme ≫ conePoint coneVertex ∧
    (∀ (R : TestAlgebra ℂ) (q : Points Y R),
      (e R q).1 = q ≫ i ≫ firstProjection ∧
      twoStepAffinePlane R (q ≫ i ≫ terminalProjection) = graphPlane (e R q).2 ∧
      coneEndomorphism (q ≫ m) = graphEndomorphism (e R q).2) ∧
    (∀ (R : TestAlgebra ℂ) (p : Points projectiveScheme R),
      e R (p ≫ sY) = ⟨p, 0⟩) ∧
    (∀ {R T : TestAlgebra ℂ} (a : R ⟶ T) (q : Points Y R) (v : Coefficients R),
      graphEndomorphism (e T (mapPoints a q)).2 (coefficientChange a v) =
        coefficientChange a (graphEndomorphism (e R q).2 v)) ∧
    ∀ (R : TestAlgebra ℂ) (p : Points projectiveScheme R),
      let S := tautological R p
      ∃ h : (S ⊗[R] S) ≃ₗ[R] NormalLinearMaps R p,
        ∀ (u v : S) (w : Coefficients R),
          h (u ⊗ₜ[R] v) (S.mkQ w) = volume R v.val w • u

/-- Fibrewise scaling acts on the three graph-matrix entries by the same factor. -/
def scaleCone (a : ℂ) (z : Cone) : Cone :=
  ⟨(a * z.val.1, a * z.val.2.1, a * z.val.2.2), by
    change (a * z.val.1) ^ 2 + (a * z.val.2.1) * (a * z.val.2.2) = 0
    rw [show (a * z.val.1) ^ 2 + (a * z.val.2.1) * (a * z.val.2.2) =
      a ^ 2 * (z.val.1 ^ 2 + z.val.2.1 * z.val.2.2) by ring, z.property, mul_zero]⟩

/-- Matrix balls use the maximum norm of the entries of the trace-zero matrix. -/
inductive BallCoordinates where
  | matrix
  | radial

def coneBall : BallCoordinates → ℝ → Set Cone
  | .matrix, r => {z | ‖z.val‖ < r}
  | .radial, r => {z | radialSize z < r}

abbrev AnalyticInverseImage (c : coneScheme ⟶ twoStepScheme) (U : Set Cone) :=
  {q : Points incidenceScheme complexAlgebra //
    ∃ z ∈ U, q ≫ terminalProjection = conePoint z ≫ c}

/-- The contractions of all the balls use the same pointwise formula, so their
restrictions agree under inclusion. Their topology is the incidence topology. -/
def FibrewiseContractions (c : coneScheme ⟶ twoStepScheme)
    (s : projectiveScheme ⟶ incidenceScheme) : Prop :=
  ∃ H : ∀ (k : BallCoordinates) (r : ℝ), 0 < r →
      C(I × AnalyticInverseImage c (coneBall k r), AnalyticInverseImage c (coneBall k r)),
    (∀ (k : BallCoordinates) (r : ℝ) (hr : 0 < r)
      (q : AnalyticInverseImage c (coneBall k r)),
      H k r hr (1, q) = q ∧
      (H k r hr (0, q)).val = (q.val ≫ firstProjection) ≫ s ∧
      ∀ (a : I) (z : Cone), q.val ≫ terminalProjection = conePoint z ≫ c →
        (H k r hr (a, q)).val ≫ firstProjection = q.val ≫ firstProjection ∧
        (H k r hr (a, q)).val ≫ terminalProjection =
          conePoint (scaleCone ((a : ℝ) : ℂ) z) ≫ c) ∧
    (∀ (k : BallCoordinates) (r : ℝ) (hr : 0 < r)
      (q : AnalyticInverseImage c (coneBall k r)) (a : I),
      q.val ≫ terminalProjection = conePoint coneVertex ≫ c → H k r hr (a, q) = q) ∧
    ∀ (k l : BallCoordinates) (r d : ℝ) (hr : 0 < r) (hd : 0 < d)
      (h : coneBall k r ⊆ coneBall l d) (q : AnalyticInverseImage c (coneBall k r)) (a : I),
      let q' : AnalyticInverseImage c (coneBall l d) :=
        ⟨q.val, by obtain ⟨z, hz, hq⟩ := q.property; exact ⟨z, h hz, hq⟩⟩
      (H l d hd (a, q')).val = (H k r hr (a, q)).val

open NilpotentConeChartSpecs.Expected in
/-- The reduced transverse chart and its analytic link, with the inverse image
in the ordered lattice space and its compatible deformation retractions. -/
def TransverseCone : Prop :=
  ReducedQuadraticChart ∧
  PolynomialParametrization ∧ AntipodalQuotientHomeomorphism ∧ RadialNeighborhoods ∧
  WindowContainments ∧
  ∃ (c : coneScheme ⟶ twoStepScheme) (x : Points twoStepScheme complexAlgebra)
    (s : projectiveScheme ⟶ incidenceScheme),
    IsTerminalConeChart c ∧ ExceptionalSection x s ∧ conePoint coneVertex ≫ c = x ∧
    IsOpen shortChartSet ∧ IsOpen shortLatticeChartSet ∧
    (∃ (e : Cone ≃ₜ shortChartSet) (eL : Cone ≃ₜ shortLatticeChartSet),
      (∀ z : Cone, (e z).val.val =
        shortGraphPoint (graphCoefficientMatrix z.val.1 z.val.2.1 z.val.2.2)) ∧
      (∀ z : Cone, latticeSubspace 0 2 (eL z).val.val =
        grassmannianSubspace (windowBasis 2 0 2)
          (windowDimension_le NilpotentConeChartSpecs.shortDimension) (e z).val.val) ∧
      (eL coneVertex).val.val = scalarPoint ∧
      ∀ z : Cone, secondPlane (conePoint z ≫ c) =
        (latticeSubspace 0 2 (eL z).val.val).map twoStepCoordinates.toLinearMap) ∧
    InverseImageBundle c s ∧ FibrewiseContractions c s

end

end RepTheorySurvey.Geometric.TransverseConeSpecs
