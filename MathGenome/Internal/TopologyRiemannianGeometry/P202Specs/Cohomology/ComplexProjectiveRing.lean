import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.ComplexProjectiveHomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.UniversalCoefficientsCohomology
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Products.CupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.ThomClass
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CompactOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SpheresDisks
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Algebra.Polynomial.Basic

/-!
Independent translation of the complex-projective part of
`prop:p202-cohomology-rings`, paper.tex 2598–2603 and 2621–2643.

The objects here are the actual projective quotient and the fixed singular
cohomology modules. The algebraic presentation below uses the given singular
cup product. The geometric targets also require the complex-normal hyperplane Thom class,
its restrictions to every standard projective subspace, and local and global
fundamental-class evaluations equal to one. Positive ordered complex simplices
fix all orientation signs. These data occur as conclusions, never as assumed
certificates.
-/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped DirectSum
namespace P202Specs.ComplexProjectiveRing
open P202.ComplexProjective P202Specs.SingularChains P202Specs.CupProduct
  P202Specs.CohomologyPairs

abbrev projectiveSpace (m : ℕ) : TopCat := TopCat.of (Space m)
abbrev cohomology (m n : ℕ) := H ℤ (projectiveSpace m) n
abbrev totalCohomology (m : ℕ) := HStar ℤ (projectiveSpace m)

/-- The actual UCT evaluation arrow, with values in the unrestricted dual. -/
abbrev evaluation (m n : ℕ) :=
  P202Specs.UniversalCoefficientsCohomology.evaluation ℤ ℤ
    (ordinaryComplex ℤ ℤ (projectiveSpace m)) (n : ℤ)

/-- The same cycle evaluation on the actual relative singular complex. -/
abbrev relativeEvaluation (P : P202Specs.RelativeSingularChains.Pair) (n : ℕ) :=
  P202Specs.UniversalCoefficientsCohomology.evaluation ℤ ℤ
    (P202Specs.RelativeSingularChains.ordinary ℤ ℤ P) (n : ℤ)

/-- Forget support by the original inclusion of relative cochains. -/
abbrev ordinaryImage (P : P202Specs.RelativeSingularChains.Pair) (n : ℕ) :=
  (HomologicalComplex.homologyMap (relativeToAbsolute ℤ ℤ P) (n : ℤ)).hom

/-- The original chain quotient takes an absolute cycle to a relative cycle. -/
abbrev absoluteToRelative (P : P202Specs.RelativeSingularChains.Pair) (n : ℕ) :=
  (HomologicalComplex.homologyMap
    (P202Specs.RelativeSingularChains.projection (ordinaryFunctor ℤ ℤ) P) (n : ℤ)).hom

/-- Additive computation, including the point case and all vanishing degrees. -/
def groups_type : Prop := ∀ m n : ℕ,
  ((∃ r ≤ m, n = 2*r) → Nonempty (cohomology m n ≃ₗ[ℤ] ℤ)) ∧
  ((¬ ∃ r ≤ m, n = 2*r) → IsZero (ordinaryCohomology ℤ ℤ (projectiveSpace m) (n : ℤ)))

/-- Evaluation, not just an abstract additive isomorphism, is an isomorphism. -/
def evaluation_type : Prop := ∀ m n : ℕ, Function.Bijective (evaluation m n)

/-- Every degree-two class has the required top truncation for the actual cup
ring. This alone does not assert that a particular class generates it. -/
def truncation_type : Prop := ∀ (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)),
  letI := C.gradedRing
  ∀ v : cohomology m 2,
    (DirectSum.of (H ℤ (projectiveSpace m)) 2 v) ^ (m+1) = 0

def truncationIdeal (m : ℕ) : Ideal (Polynomial ℤ) :=
  Ideal.span ({Polynomial.X ^ (m+1)} : Set (Polynomial ℤ))

abbrev truncatedPolynomial (m : ℕ) := Polynomial ℤ ⧸ truncationIdeal m

def polynomialClass (m : ℕ) : Polynomial ℤ →+* truncatedPolynomial m :=
  Ideal.Quotient.mk (truncationIdeal m)

/-- The polynomial homomorphism factors through the asserted truncation ideal
for every degree-two class; no assertion of bijectivity is hidden here. -/
def polynomialMap_type : Prop := ∀ (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)),
  letI := C.gradedRing
  ∀ v : cohomology m 2,
    ∃ f : truncatedPolynomial m →+* totalCohomology m,
      f (polynomialClass m Polynomial.X) = DirectSum.of (H ℤ (projectiveSpace m)) 2 v

/-- The point endpoint has the quotient by X, and its variable maps to zero. -/
def pointPresentation_type : Prop := ∀ (C : CohomologyRing ℤ (projectiveSpace 0)),
  letI := C.gradedRing
  ∃ e : truncatedPolynomial 0 ≃+* totalCohomology 0,
    e (polynomialClass 0 Polynomial.X) = 0

/-- The powers are primitive in their actual homogeneous modules. This is
an intermediate condition, not a premise of the original projective theorem. -/
def PrimitivePowers (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m))
    (v : cohomology m 2) : Prop :=
  letI := C.gradedRing
  ∀ i : ℕ, i ≤ m → ∃ b : cohomology m (2*i),
    Function.Bijective (fun z : ℤ => z • b) ∧
      (DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^i =
        DirectSum.of (H ℤ (projectiveSpace m)) (2*i) b

/-- The algebraic presentation, with X sent to a homogeneous degree-two class.
The homogeneous-powers clause records the grading in addition to the ring
isomorphism; each polynomial monomial maps into cohomological degree 2*i.
The full geometric characterization is imposed separately by
`geometricPresentation_type` below. -/
def presentation_type : Prop := ∀ (m : ℕ)
    (C : CohomologyRing ℤ (projectiveSpace m)),
  letI := C.gradedRing
  ∃ (v : cohomology m 2) (e : truncatedPolynomial m ≃+* totalCohomology m),
    e (polynomialClass m Polynomial.X) = DirectSum.of (H ℤ (projectiveSpace m)) 2 v ∧
    ∀ i : ℕ, i ≤ m → ∃ b : cohomology m (2*i),
      Function.Bijective (fun z : ℤ => z • b) ∧
      e ((polynomialClass m Polynomial.X)^i) =
        DirectSum.of (H ℤ (projectiveSpace m)) (2*i) b

open P202.ComplexProjective P202Specs.SingularChains P202Specs.RelativeSingularChains
  P202Specs.CohomologyPairs P202Specs.CupProduct
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MapClassData SmoothManifolds.BundleOperationsData
  SmoothManifolds.AbstractTubularData

/-- Barycentrics map to real coordinates t_(j+1)-t_0. The derivative has
positive determinant n+1, so this is the usual ordered Euclidean orientation. -/
def positiveSimplexCoordinates (n : ℕ) (x : P202.Cellular.StandardSimplex n) : Fin n → ℝ :=
  fun j => x.weights j.succ - x.weights 0

/-- Complex coordinates are ordered Re z_0, Im z_0, Re z_1, Im z_1, ... . -/
def complexSimplexCoordinates (i : ℕ) (x : P202.Cellular.StandardSimplex (2*i)) :
    Fin i → ℂ :=
  fun j => (positiveSimplexCoordinates (2*i) x ⟨2*j.val, by omega⟩ : ℂ) +
    Complex.I * (positiveSimplexCoordinates (2*i) x ⟨2*j.val+1, by omega⟩ : ℂ)

/-- The origin of the last-coordinate affine chart, including i=0. -/
def projectiveOrigin (i : ℕ) : Space i := affineChart i i (by omega) 0

/-- The standard positively oriented simplex in the last-coordinate affine chart. -/
def positiveProjectiveSimplex (i : ℕ) (x : P202.Cellular.StandardSimplex (2*i)) : Space i :=
  affineChart i i (by omega) (complexSimplexCoordinates i x)

/-- The hyperplane used throughout is the shared zero-padding CP^m → CP^(m+1). -/
abbrev hyperplaneInclusion (m : ℕ) : Space m → Space (m+1) :=
  inclusion (m+1) m (by omega)

/-- A complex transverse line to that hyperplane at [1:0:...:0]. -/
def complexNormalVector (m : ℕ) (w : ℂ) : Fin (m+2) → ℂ :=
  fun j => if j.val = 0 then 1 else if j.val = m+1 then w else 0

lemma complexNormalVector_nonzero (m : ℕ) (w : ℂ) : complexNormalVector m w ≠ 0 := by
  intro h
  have := congrFun h 0
  simpa [complexNormalVector] using this

def complexNormalSlice (m : ℕ) (w : ℂ) : Space (m+1) :=
  mk (complexNormalVector m w) (complexNormalVector_nonzero m w)

def positiveNormalSimplex (m : ℕ) (x : P202.Cellular.StandardSimplex 2) : Space (m+1) :=
  complexNormalSlice m (complexSimplexCoordinates 1 x 0)

/-- Exact sign-normalization of a local complex fundamental class by the
explicit standard positive simplex. Cycle existence and the pair-map formula
are conclusions carried by a witness, never assumed as upstream facts. -/
structure ComplexFundamentalData (i : ℕ) where
  manifold : P202Specs.LocalOrientation.Manifold (2*i) (Space i)
  orientation : P202Specs.LocalOrientation.Orientation ℤ manifold
  localSimplex : P202Specs.SpheresDisks.simplexPair (2*i) ⟶
    P202Specs.LocalOrientation.localPair (Space i) (projectiveOrigin i)
  localSimplex_formula : ∀ x, localSimplex.map x = positiveProjectiveSimplex i x
  simplex_cycle : (ordinary ℤ ℤ (P202Specs.SpheresDisks.simplexPair (2*i))).d
    ((2*i : ℕ) : ℤ) (((2*i : ℕ) : ℤ)-1)
    (P202Specs.SpheresDisks.relativeAffineChain ℤ ℤ (2*i) 1) = 0
  orientation_positive : ((relativeHomologyFunctor ℤ ℤ ((2*i : ℕ) : ℤ)).map localSimplex)
    (P202Specs.SpheresDisks.classOf ℤ _ ((2*i : ℕ) : ℤ)
      (P202Specs.SpheresDisks.relativeAffineChain ℤ ℤ (2*i) 1) simplex_cycle) =
      orientation.val (projectiveOrigin i)
  fundamental : homology ℤ ℤ (projectiveSpace i) ((2*i : ℕ) : ℤ)
  fundamental_values : P202Specs.CompactOrientation.HasLocalValues ℤ orientation.val Set.univ
    (P202Specs.CompactOrientation.absoluteToSupported ℤ (Space i) (2*i) fundamental)

/-- The actual hyperplane normal bundle, its locally compatible orientation,
and its Thom class. Evaluation on the specified complex transverse line fixes
its sign to the complex normal orientation; it is not an arbitrary generator. -/
structure HyperplaneThomData (m : ℕ) where
  sourceAtlas : SmoothManifold (2*m) .euclidean (Space m)
  targetAtlas : SmoothManifold (2*(m+1)) .euclidean (Space (m+1))
  embedding : IsSmoothEmbedding sourceAtlas targetAtlas (hyperplaneInclusion m)
  normal : NormalBundle sourceAtlas targetAtlas (hyperplaneInclusion m)
  orientation : P202Specs.ThomClass.Orientation ℤ normal 2
  tubular : TubularNeighborhood normal
  tubular_normalized : P202Specs.ThomClass.NormalCompatible normal tubular
  thom : relativeCohomology ℤ ℤ (P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)) 2
  thom_fiber_values : P202Specs.ThomClass.HasFiberValues ℤ orientation thom
  positiveSlice : P202Specs.SpheresDisks.simplexPair 2 ⟶
    P202Specs.ThomClass.ambientPair (hyperplaneInclusion m)
  positiveSlice_formula : ∀ x, positiveSlice.map x = positiveNormalSimplex m x
  simplex_cycle : (ordinary ℤ ℤ (P202Specs.SpheresDisks.simplexPair 2)).d 2 (2-1)
    (P202Specs.SpheresDisks.relativeAffineChain ℤ ℤ 2 1) = 0
  complex_normal_positive : relativeEvaluation _ 2 thom
    (((relativeHomologyFunctor ℤ ℤ 2).map positiveSlice)
      (P202Specs.SpheresDisks.classOf ℤ _ 2
        (P202Specs.SpheresDisks.relativeAffineChain ℤ ℤ 2 1) simplex_cycle)) = 1

/-- All geometric clauses required of the selected degree-two class. The zero
space has the zero degree-two class; positive-dimensional spaces use the
ordinary image of the specified complex-normal hyperplane Thom class. -/
def GeometricGenerator (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m))
    (v : cohomology m 2) : Prop :=
  (m = 0 → v = 0) ∧
  (∀ k, ∀ h : m = k+1, ∃ d : HyperplaneThomData k,
    h ▸ v = ordinaryImage _ 2 d.thom) ∧
  letI := C.gradedRing
  ∀ i (hi : i ≤ m), ∃ (ι : projectiveSpace i ⟶ projectiveSpace m)
    (d : ComplexFundamentalData i)
    (a : relativeCohomology ℤ ℤ
      (P202Specs.LocalOrientation.localPair (Space i) (projectiveOrigin i)) ((2*i : ℕ) : ℤ))
    (b : cohomology m (2*i)),
    (∀ x, ι x = inclusion m i hi x) ∧
    Function.Bijective (fun z : ℤ => z • a) ∧
    relativeEvaluation _ (2*i) a (d.orientation.val (projectiveOrigin i)) = 1 ∧
    (DirectSum.of (H ℤ (projectiveSpace m)) 2 v)^i =
      DirectSum.of (H ℤ (projectiveSpace m)) (2*i) b ∧
    hPullback ℤ ι (2*i) b = ordinaryImage _ (2*i) a ∧
    evaluation i (2*i) (hPullback ℤ ι (2*i) b) d.fundamental = 1

/-- Existence of the geometric generator is an unconditional conclusion. -/
def geometricGenerator_type : Prop := ∀ (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m)),
  ∃ v : cohomology m 2, GeometricGenerator m C v

/-- The full geometric ring presentation, with no geometric certificate as
a premise. -/
def geometricPresentation_type : Prop :=
  ∀ (m : ℕ) (C : CohomologyRing ℤ (projectiveSpace m)),
  letI := C.gradedRing
  ∃ (v : cohomology m 2) (e : truncatedPolynomial m ≃+* totalCohomology m),
    GeometricGenerator m C v ∧
    e (polynomialClass m Polynomial.X) = DirectSum.of (H ℤ (projectiveSpace m)) 2 v ∧
    ∀ i : ℕ, i ≤ m → ∃ b : cohomology m (2*i),
      Function.Bijective (fun z : ℤ => z • b) ∧
      e ((polynomialClass m Polynomial.X)^i) =
        DirectSum.of (H ℤ (projectiveSpace m)) (2*i) b


/-- Actual compatible complex orientations and ordinary fundamental classes,
normalized by the specified positive simplex, in every dimension. -/
def fundamentalClasses_type : Prop := ∀ i : ℕ, Nonempty (ComplexFundamentalData i)

/-- The geometric conclusion at the point, including the local unit evaluation. -/
def pointGeometricGenerator_type : Prop :=
  ∀ C : CohomologyRing ℤ (projectiveSpace 0), GeometricGenerator 0 C 0

/-- Existence of the genuine complex-normal hyperplane Thom data, including
all normalized tubular fiber values and the positive transverse evaluation. -/
def hyperplaneThomClasses_type : Prop := ∀ m : ℕ, Nonempty (HyperplaneThomData m)

/-- The full geometric conclusion on the projective line. -/
def lineGeometricGenerators_type : Prop :=
  ∀ C : CohomologyRing ℤ (projectiveSpace 1),
    ∃ v : cohomology 1 2, GeometricGenerator 1 C v


end P202Specs.ComplexProjectiveRing
