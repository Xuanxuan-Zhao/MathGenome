import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.LatticeModels
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Homotopy.Contractible
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.RealProjectiveHomology

namespace RepTheorySurvey.Geometric.NilpotentConeChartSpecs

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LinearAlgebraicGroups.Specs.GrassmannianCharts
open LatticeModelSpecs
open scoped Matrix

/-- The quadratic cone with the subspace topology from complex coordinates `(u,v,w)`. -/
abbrev Cone := {z : ℂ × ℂ × ℂ // z.1 ^ 2 + z.2.1 * z.2.2 = 0}

/-- The vertex of the transverse cone. -/
def coneVertex : Cone := ⟨(0, 0, 0), by simp⟩

/-- The polynomial map whose fibres are the antipodal orbits. -/
def parametrize (p : ℂ × ℂ) : Cone :=
  ⟨(p.1 * p.2, -(p.1 ^ 2), p.2 ^ 2), by dsimp; ring⟩

def antipodalSetoid : Setoid (ℂ × ℂ) where
  r p q := p = q ∨ p = -q
  iseqv := {
    refl := fun p => Or.inl rfl
    symm := by
      rintro p q (h | h)
      · exact Or.inl h.symm
      · exact Or.inr (by rw [h, neg_neg])
    trans := by
      rintro p q r (h | h) (k | k)
      · exact Or.inl (h.trans k)
      · exact Or.inr (h.trans k)
      · exact Or.inr (by rw [h, k])
      · exact Or.inl (by rw [h, k, neg_neg]) }

abbrev AntipodalQuotient := Quotient antipodalSetoid

namespace Expected

/-- Properness and the full fibre calculation, including the singleton over the vertex. -/
def PolynomialParametrization : Prop :=
  IsProperMap parametrize ∧ Function.Surjective parametrize ∧
    (∀ p q : ℂ × ℂ, parametrize p = parametrize q ↔ antipodalSetoid.r p q) ∧
    (∀ p : ℂ × ℂ, parametrize p = coneVertex ↔ p = 0)

/-- The homeomorphism induced on the actual quotient by the polynomial parametrization. -/
def AntipodalQuotientHomeomorphism : Prop :=
  ∃ e : AntipodalQuotient ≃ₜ Cone,
    (∀ p : ℂ × ℂ, e (Quotient.mk antipodalSetoid p) = parametrize p) ∧
    e (Quotient.mk antipodalSetoid 0) = coneVertex

end Expected

def shortDimension : WindowDimension 2 0 2 := by
  refine ⟨2, ?_⟩
  have h := (windowCoordinates 2 0 2).finrank_eq
  rw [Module.finrank_fintype_fun_eq_card] at h
  rw [h]
  decide

def secondPivot : Pivot (Fin 2 × Fin 2) 2 :=
  ⟨{(0, 1), (1, 1)}, by decide⟩

abbrev ShortChartMatrix (R : Type) :=
  Matrix (Outside secondPivot) (Inside secondPivot) R

def shortGraphCoordinates {R : Type} (A : Matrix (Fin 2) (Fin 2) R) :
    ShortChartMatrix R :=
  fun i j ↦ A i.val.1 j.val.1

def graphCoefficientMatrix {R : Type} [Ring R] (u v w : R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![u, v; w, -u]

def shortGraphPoint (A : Matrix (Fin 2) (Fin 2) ℂ) :
    WindowPoints 2 0 2 shortDimension :=
  grassmannianChartPoint (windowBasis 2 0 2) (windowDimension_le shortDimension)
    secondPivot (shortGraphCoordinates A)

abbrev ShortStablePoints :=
  StablePoints (windowBasis 2 0 2) (windowDimension_le shortDimension) (windowOperator 2 0 2)

def shortChartSet : Set ShortStablePoints :=
  fun p ↦ p.val ∈ Set.range shortGraphPoint

def quadraticEquation : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 * MvPolynomial.X 2

def quadraticIdeal : Ideal (MvPolynomial (Fin 3) ℂ) :=
  Ideal.span {quadraticEquation}

abbrev ConeCoordinateRing := MvPolynomial (Fin 3) ℂ ⧸ quadraticIdeal

def coneCoordinate (i : Fin 3) : ConeCoordinateRing :=
  Ideal.Quotient.mk quadraticIdeal (MvPolynomial.X i)

def quadraticChartHom :
    chartAlgebra (k := ℂ) secondPivot →ₐ[ℂ] ConeCoordinateRing :=
  MvPolynomial.aeval fun ij ↦
    shortGraphCoordinates (graphCoefficientMatrix
      (coneCoordinate 0) (coneCoordinate 1) (coneCoordinate 2)) ij.1 ij.2

def shortChartInclusion :=
  chartInclusion (windowBasis 2 0 2) (windowDimension_le shortDimension) secondPivot

def shortStableInclusion :=
  (reducedClosureInclusion (grassmannianCharts
    (windowBasis 2 0 2) (windowDimension_le shortDimension)).scheme
    {p | StablePlane (windowBasis 2 0 2) (windowDimension_le shortDimension)
      (windowOperator 2 0 2) p}).left

namespace Expected

/-- On the actual second pivot, the square-zero graph equations cut out the
quadratic cone after reduction, with the indicated graph coordinates. -/
def ReducedQuadraticChart : Prop :=
  (∀ A : Matrix (Fin 2) (Fin 2) ℂ,
    StablePlane (windowBasis 2 0 2) (windowDimension_le shortDimension)
      (windowOperator 2 0 2) (shortGraphPoint A) ↔ A * A = 0) ∧
  Function.Surjective quadraticChartHom ∧
  RingHom.ker quadraticChartHom.toRingHom =
    reducedStabilityIdeal secondPivot
      (operatorInCoordinates (windowBasis 2 0 2) (windowOperator 2 0 2)) ∧
  ∃ e : pullback shortChartInclusion shortStableInclusion ≅
      Spec (CommRingCat.of ConeCoordinateRing),
    e.hom ≫ Spec.map (CommRingCat.ofHom quadraticChartHom.toRingHom) =
      pullback.fst shortChartInclusion shortStableInclusion

end Expected

abbrev ShortLatticeStage :=
  {L : GL2Lattice // (scalarLattice 2 2).val ≤ L.val ∧
    L.val ≤ (scalarLattice 2 0).val ∧
    Module.finrank ℂ (latticeSubspace 0 2 L) = 2}

def shortLatticeChartSet : Set ShortLatticeStage :=
  fun L ↦ ∃ A : Matrix (Fin 2) (Fin 2) ℂ,
    latticeSubspace 0 2 L.val =
      grassmannianSubspace (windowBasis 2 0 2) (windowDimension_le shortDimension)
        (shortGraphPoint A)

namespace Expected

/-- The analytic chart uses the canonical Grassmannian graph topology and the
lattice topology from the affine Grassmannian, with the same graph coordinates. -/
def AnalyticQuadraticChart : Prop :=
  IsOpen shortChartSet ∧ IsOpen shortLatticeChartSet ∧
  ∃ (e : Cone ≃ₜ shortChartSet) (eL : Cone ≃ₜ shortLatticeChartSet),
    (∀ z : Cone, (e z).val.val =
      shortGraphPoint (graphCoefficientMatrix z.val.1 z.val.2.1 z.val.2.2)) ∧
    (∀ z : Cone, latticeSubspace 0 2 (eL z).val.val =
      grassmannianSubspace (windowBasis 2 0 2) (windowDimension_le shortDimension)
        (e z).val.val) ∧
    (eL coneVertex).val.val = scalarLattice 2 1

end Expected

open P202Specs.RealProjectiveHomology (Space quotientMap)
open P202Specs.SpheresDisks (sphere)
open scoped unitInterval

/-- The radius of either preimage of the point under the quadratic map. -/
def radialSize (z : Cone) : ℝ := Real.sqrt (‖z.val.2.1‖ + ‖z.val.2.2‖)

/-- Real Euclidean coordinates grouped into two complex coordinates. -/
def realComplexCoordinates (x : EuclideanSpace ℝ (Fin 4)) : ℂ × ℂ :=
  (⟨x 0, x 1⟩, ⟨x 2, x 3⟩)

abbrev RadialBall (r : ℝ) := {z : Cone // radialSize z < r}

abbrev PuncturedBall (r : ℝ) :=
  {z : Cone // radialSize z < r ∧ z ≠ coneVertex}

abbrev ProjectiveLink := Space 3

/-- The open truncated cone on the actual antipodal quotient of the unit sphere. -/
def radialConeSetoid (r : ℝ) : Setoid (Set.Ico (0 : ℝ) r × ProjectiveLink) where
  r x y := x = y ∨ ((x.1 : ℝ) = 0 ∧ (y.1 : ℝ) = 0)
  iseqv := by
    refine ⟨fun x ↦ Or.inl rfl, ?_, ?_⟩
    · rintro x y (h | h)
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    · rintro x y z (rfl | h) (rfl | k)
      · exact Or.inl rfl
      · exact Or.inr k
      · exact Or.inr h
      · exact Or.inr ⟨h.1, k.2⟩

abbrev RadialCone (r : ℝ) := Quotient (radialConeSetoid r)

def puncturedInclusion {r s : ℝ} (hrs : r ≤ s) (z : PuncturedBall r) :
    PuncturedBall s :=
  ⟨z.val, z.property.1.trans_le hrs, z.property.2⟩

def radialIntervalInclusion {r s : ℝ} (hrs : r ≤ s) (t : Set.Ioo (0 : ℝ) r) :
    Set.Ioo (0 : ℝ) s :=
  ⟨t.val, t.property.1, t.property.2.trans_le hrs⟩

def radialContractionTarget {r : ℝ} (hr : 0 < r) :
    C(RadialBall r, RadialBall r) :=
  ContinuousMap.const _ ⟨coneVertex, by simpa [radialSize, coneVertex] using hr⟩

def puncturedContractionTarget {r : ℝ} (hr : 0 < r)
    (e : Set.Ioo (0 : ℝ) r × ProjectiveLink ≃ₜ PuncturedBall r) :
    C(PuncturedBall r, PuncturedBall r) where
  toFun z := e (⟨r / 2, by constructor <;> linarith⟩, (e.symm z).2)
  continuous_toFun :=
    e.continuous.comp (continuous_const.prodMk (continuous_snd.comp e.symm.continuous))

namespace Expected

/-- The cofinal analytic vertex neighborhoods and their radial identifications with
the truncated cone on the actual real projective link, compatible with shrinking. -/
def RadialNeighborhoods : Prop :=
  (∃ e : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 2),
    ∀ x, ((e x) 0, (e x) 1) = realComplexCoordinates x) ∧
  (∀ r > 0, IsOpen {z : Cone | radialSize z < r} ∧
    {z : Cone | radialSize z < r} ∈ nhds coneVertex) ∧
  (∀ U ∈ nhds coneVertex, ∃ r > 0, {z : Cone | radialSize z < r} ⊆ U) ∧
  ∃ (e : ∀ r : ℝ, 0 < r → RadialCone r ≃ₜ RadialBall r)
    (f : ∀ r : ℝ, 0 < r → Set.Ioo (0 : ℝ) r × ProjectiveLink ≃ₜ PuncturedBall r),
    (∀ (r : ℝ) (hr : 0 < r) (s : Set.Ico (0 : ℝ) r) (p : sphere 3),
      (e r hr (Quotient.mk (radialConeSetoid r) (s, quotientMap 3 p))).val =
        parametrize ((s : ℝ) • realComplexCoordinates p.val)) ∧
    (∀ (r : ℝ) (hr : 0 < r) (s : Set.Ioo (0 : ℝ) r) (p : sphere 3),
      (f r hr (s, quotientMap 3 p)).val =
        parametrize ((s : ℝ) • realComplexCoordinates p.val)) ∧
    (∀ (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s)
      (x : Set.Ioo (0 : ℝ) r × ProjectiveLink),
      puncturedInclusion hrs (f r hr x) = f s hs (radialIntervalInclusion hrs x.1, x.2)) ∧
    (∀ (r : ℝ) (hr : 0 < r),
      Nonempty ((ContinuousMap.id (RadialBall r)).HomotopyRel (radialContractionTarget hr)
        {z : RadialBall r | z.val = coneVertex})) ∧
    (∀ (r : ℝ) (hr : 0 < r),
      Nonempty ((ContinuousMap.id (PuncturedBall r)).HomotopyRel
        (puncturedContractionTarget hr (f r hr))
        {z : PuncturedBall r | (f r hr).symm z |>.1.val = r / 2}))

end Expected
end

end RepTheorySurvey.Geometric.NilpotentConeChartSpecs
