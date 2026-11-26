import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels
import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.CSA.NormOneGroup
import Mathlib.Algebra.CharP.Two
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.Algebra.Group.Units.Opposite
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Algebra

namespace LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover

open CliffordAlgebra
open _root_.LinearAlgebraicGroups.Albert.CliffordSpecification (hyperbolicOperator)

universe u v

abbrev CreationSpace (R : Type u) (m : ℕ) := Fin m → R

abbrev SplitClifford (R : Type u) [CommRing R] (m : ℕ) :=
  CliffordAlgebra (QuadraticForm.dualProd R (CreationSpace R m))

/-- The action of a creation-space automorphism on the hyperbolic space. -/
def splitScaleAction {R : Type u} [CommRing R] {m : ℕ}
    (t : CreationSpace R m ≃ₗ[R] CreationSpace R m)
    (x : Module.Dual R (CreationSpace R m) × CreationSpace R m) :
    Module.Dual R (CreationSpace R m) × CreationSpace R m :=
  (x.1.comp t.symm.toLinearMap, t x.2)

/-- The split Clifford calculation over every test ring. The creation space may
include additional coordinates on which the scale acts by the identity. -/
def SplitExteriorScaleCover : Prop :=
  ∀ (R : Type u) [CommRing R] (m : ℕ),
    let E := CreationSpace R m
    let q := QuadraticForm.dualProd R E
    ∃ (e : SplitClifford R m ≃ₐ[R] Module.End R (ExteriorAlgebra R E))
      (lift : ((E ≃ₗ[R] E) × Rˣ) →* (SplitClifford R m)ˣ),
      (∀ x, e (ι q x) = hyperbolicOperator x) ∧
      (∀ t (s : Rˣ),
        e (lift (t, s)).val = (↑s⁻¹ : R) • (ExteriorAlgebra.map t.toLinearMap).toLinearMap ∧
        (lift (t, s)).val ∈ evenOdd q 0 ∧
        (∀ x, (lift (t, s)).val * ι q x = ι q (splitScaleAction t x) * (lift (t, s)).val) ∧
        reverse (lift (t, s)).val * (lift (t, s)).val =
          algebraMap R _ ((↑s⁻¹ : R) ^ 2 * LinearMap.det t.toLinearMap) ∧
        (reverse (lift (t, s)).val * (lift (t, s)).val = 1 ↔
          LinearMap.det t.toLinearMap = (s : R) ^ 2)) ∧
      (∀ t (a : (SplitClifford R m)ˣ),
        (∀ x, a.val * ι q x = ι q (splitScaleAction t x) * a.val) →
        ∃! s : Rˣ, a = lift (t, s)) ∧
      ∀ s : Rˣ, lift (1, s) = Units.map (algebraMap R _).toMonoidHom s⁻¹

open scoped TensorProduct
open _root_.Specs.RM03.CSA (isCentralSimple degree reducedNorm)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

/-- The componentwise group of unit pairs satisfying the square-root equation. -/
def scalePairs {C R : Type u} [Ring C] [CommRing R] (N : Cˣ →* Rˣ) :
    Subgroup (Cˣ × Rˣ) :=
  (N.comp (MonoidHom.fst Cˣ Rˣ)).eqLocus
    ((powMonoidHom 2).comp (MonoidHom.snd Cˣ Rˣ))

/-- The reduced norm on degree-two scalar-extended units and its restriction
to the scalar units. There is no restriction on the coefficient algebra. -/
def QuaternionNormOnUnits : Prop :=
  ∀ {F B : Type u} [Field F] [Ring B] [Algebra F B]
    (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {J : Type u} [Fintype J] (b : Module.Basis J F B)
      (R : Type u) [CommRing R] [Algebra F R],
      ∃ N : (R ⊗[F] B)ˣ →* Rˣ,
        (∀ t, (N t : R) = normAt hB b t.val) ∧
        ∀ s, N (Units.map (algebraMap R (R ⊗[F] B)).toMonoidHom s) = s ^ 2

/-- On local-field points the product uses the ordinary unit topologies of
the field and of the quaternion algebra with its compatible vector space topology.
The proof only needs continuity of multiplication and of scalar multiplication. -/
def LocalScaleCover : Prop :=
  ∀ {F B : Type u} [Field F] [DivisionRing B] [Algebra F B]
    [TopologicalSpace F] [TopologicalSpace B] [IsTopologicalRing F] [IsTopologicalRing B]
    [ContinuousSMul F B] (hB : isCentralSimple F B), degree F B = 2 →
    ∃ (N : Bˣ →* Fˣ) (e : scalePairs N ≃ₜ* N.ker × Fˣ),
      (∀ t, (N t : F) = reducedNorm hB t.val) ∧
      (∀ x, (e x).1.val = x.val.1 *
        (Units.map (algebraMap F B).toMonoidHom x.val.2)⁻¹ ∧ (e x).2 = x.val.2) ∧
      (∀ (b : N.ker) (s : Fˣ), (e.symm (b,s)).val =
        (b.val * Units.map (algebraMap F B).toMonoidHom s, s)) ∧
      ∀ (H : Subgroup (scalePairs N)) (A : Set N.ker), IsClosed (H : Set (scalePairs N)) →
        Dense A →
        (∀ s, e.symm (1,s) ∈ H) →
        (∀ b ∈ A, e.symm (b,1) ∈ H) → H = ⊤

/-- A normalized square root of a fixed unit in the coordinate ring of an
integral pointed variety is unique, including in characteristic two. -/
def NormalizedSquareRoot : Prop :=
  ∀ {F C : Type u} [Field F] [CommRing C] [IsDomain C] [Algebra F C]
    (point : C →ₐ[F] F) (x y : Cˣ),
    point x.val = 1 → point y.val = 1 → x ^ 2 = y ^ 2 → x = y

/-- The square map on a characteristic-two valued field is a topological
embedding. Its inverse on the range is the unique continuous square root. -/
def ValuedSquareRoot : Prop :=
  ∀ (F : Type u) [Field F] [CharP F 2] [TopologicalSpace F]
    [ValuativeRel F] [IsValuativeTopology F], Topology.IsEmbedding (fun s : F => s ^ 2)

/-- The base change of the augmentation at the distinguished rational point. -/
def extendPoint {F K C : Type u} [Field F] [Field K] [Algebra F K] [CommRing C] [Algebra F C]
    (p : C →ₐ[F] F) : K ⊗[F] C →ₐ[K] K :=
  (Algebra.TensorProduct.rid F K K).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id K K) p)

/-- A normalized square root in the integral split coordinate ring descends
through a finite Galois splitting field. The assertion concerns coordinate
rings, so evaluation includes nonreduced test algebras. -/
def GaloisSquareRootDescent : Prop :=
  ∀ {F K C : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [CommRing C] [Algebra F C] [IsDomain (K ⊗[F] C)]
    (p : C →ₐ[F] F) (n : Cˣ) (s : (K ⊗[F] C)ˣ),
    extendPoint (K := K) p s.val = 1 →
    s ^ 2 = Units.map (Algebra.TensorProduct.includeRight : C →ₐ[F] K ⊗[F] C).toMonoidHom n →
    ∃! r : Cˣ, Units.map (Algebra.TensorProduct.includeRight : C →ₐ[F] K ⊗[F] C).toMonoidHom r = s

/-- The first-coordinate map to the scale group. -/
def scaleProjection {C R : Type u} [Ring C] [CommRing R] {N : Cˣ →* Rˣ} :
    scalePairs N →* Cˣ :=
  (MonoidHom.fst Cˣ Rˣ).comp (scalePairs N).subtype

/-- The kernel of the projection retains the full square-one unit scheme. -/
def ScalePairKernel : Prop :=
  ∀ {C R : Type u} [Ring C] [CommRing R] (N : Cˣ →* Rˣ),
    ∃ e : (scaleProjection (N := N)).ker ≃* rootsOfUnity 2 R,
      ∀ x, (e x).val = x.val.val.2

open _root_.LinearAlgebraicGroups.Albert.SplitSpinSpecification (scaleRow)

/-- Over a splitting field the pair equation has the variety coordinates of
`SL₂ × Gₘ`, with the row rescaling given on every test ring. -/
def SplitScaleParameters : Prop :=
  ∀ (R : Type u) [CommRing R],
    let P := {p : Matrix (Fin 2) (Fin 2) R × Rˣ // p.1.det = (p.2 : R) ^ 2}
    ∃ e : P ≃ (Matrix.SpecialLinearGroup (Fin 2) R × Rˣ),
      ∀ p : P, (e p).1.val = scaleRow 0 ((↑p.val.2⁻¹ : R) ^ 2) p.val.1 ∧
        (e p).2 = p.val.2

/-- Acting on two creation coordinates and their duals, and trivially on
the complementary hyperbolic coordinates, leaves determinant `det(t)`. -/
def SplitScaleDeterminant : Prop :=
  ∀ (R : Type u) [CommRing R] (t : CreationSpace R 2 ≃ₗ[R] CreationSpace R 2) (d : ℕ),
    let j : CreationSpace R (2 + d) ≃ₗ[R] CreationSpace R 2 × CreationSpace R d :=
      ((LinearEquiv.piCongrLeft R (fun _ : Fin (2 + d) => R) finSumFinEquiv).symm).trans
        (LinearEquiv.sumArrowLequivProdArrow (Fin 2) (Fin d) R R)
    let T := (j.trans (t.prodCongr (LinearEquiv.refl R (CreationSpace R d)))).trans j.symm
    LinearMap.det T.toLinearMap = LinearMap.det t.toLinearMap

/-- The identities on algebraic families are identities in their pointed
coordinate rings. This applies to the scalar and fixed-commutator families
on the geometrically integral groups `Gₘ` and `GL₁(B)`. -/
def NormalizedScaleFamilies : Prop :=
  ∀ {F B C : Type u} [Field F] [Ring B] [Algebra F B] [CommRing C] [IsDomain C] [Algebra F C]
    (hB : isCentralSimple F B), degree F B = 2 →
    ∀ {J : Type u} [Fintype J] (b : Module.Basis J F B) (point : C →ₐ[F] F),
      (∀ c s : Cˣ,
        point c.val = 1 → point s.val = 1 →
        normAt hB b (algebraMap C (C ⊗[F] B) c.val) = s.val ^ 2 → s = c) ∧
      ∀ (a d : (C ⊗[F] B)ˣ) (s : Cˣ), point s.val = 1 →
        normAt hB b (a * d * a⁻¹ * d⁻¹ : (C ⊗[F] B)ˣ).val = s.val ^ 2 → s = 1

/-- The comparison of the affine scale preimage and the norm-square cover
descends from a finite Galois splitting field. Here `A` is the scale group's
coordinate algebra, `C` is the preimage's coordinate algebra, and `D` is the
coordinate algebra obtained by adjoining the invertible square root of the norm.
The maps `j` and `i` are the two projections on coordinate rings. -/
def ScaleComparisonDescent : Prop :=
  ∀ {F K A C D : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [CommRing A] [Algebra F A] [CommRing C] [Algebra F C] [CommRing D] [Algebra F D]
    [IsDomain (K ⊗[F] C)]
    (i : A →ₐ[F] C) (j : A →ₐ[F] D) (p : C →ₐ[F] F) (n : Aˣ) (s : Dˣ),
    s ^ 2 = Units.map j.toMonoidHom n →
    (∀ {R : Type u} [CommRing R] [Algebra F R] (f g : D →ₐ[F] R),
      f.comp j = g.comp j → f s.val = g s.val → f = g) →
    ∀ e : (K ⊗[F] D) ≃ₐ[K] (K ⊗[F] C),
      (∀ a : A, e (1 ⊗ₜ[F] j a) = 1 ⊗ₜ[F] i a) →
      extendPoint p (e (1 ⊗ₜ[F] s.val)) = 1 →
      ∃ e₀ : D ≃ₐ[F] C, e₀.toAlgHom.comp j = i ∧
        Algebra.TensorProduct.map (AlgHom.id K K) e₀.toAlgHom = e.toAlgHom

section SplitCoordinates

open Polynomial

/-- The equation `a d - b c = 1` with `a` the coefficient ring's polynomial variable
and `d` the adjoined root. The coefficients have variables `b, c, s`. -/
noncomputable def splitScaleRelation (F : Type u) [Field F] :
    Polynomial (Polynomial (MvPolynomial (Fin 3) F)) :=
  C X * X - C (C (MvPolynomial.X 0 * MvPolynomial.X 1 + 1))

abbrev SplitScaleAffineRing (F : Type u) [Field F] := AdjoinRoot (splitScaleRelation F)

noncomputable abbrev splitScaleVariable (F : Type u) [Field F] : SplitScaleAffineRing F :=
  AdjoinRoot.of (splitScaleRelation F) (C (MvPolynomial.X 2))

/-- The coordinate ring of the split variety in determinant-one coordinates. -/
abbrev SplitScaleCoordinateRing (F : Type u) [Field F] :=
  Localization.Away (splitScaleVariable F)

def SplitScaleCoordinateDomain : Prop :=
  ∀ (F : Type u) [Field F], IsDomain (SplitScaleCoordinateRing F)

end SplitCoordinates

section QuaternionModel

open CategoryTheory AlgebraicGeometry Matrix MulOpposite
open scoped Matrix CategoryTheory.MonObj
open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Specs.Arithmetic.NontrialitarianSpinModels
  (DescendedQuadraticPair SpinModel symmetricPart)
open _root_.LinearAlgebraicGroups.Specs.SymplecticDivisionForms
  (Involution antiValue extendAnti dagger hermitianValue tensorMap)
open _root_.LinearAlgebraicGroups.Specs.SymplecticInvolutionModels (quaternionConjugate)
open _root_.RM03.Brauer.SemilinearDescent (AlgebraAction)

abbrev QuaternionPairIndex (d : ℕ) := Fin 2 ⊕ Fin d

/-- Gram matrix of the ordered quaternionic basis `e,f,W`. In characteristic
two the upper and lower off-diagonal entries of the plane are both one. -/
def quaternionHyperbolicGram {B : Type u} [Ring B] {d : ℕ}
    (W : Matrix (Fin d) (Fin d) B) : Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B :=
  Matrix.fromBlocks !![0, 1; -1, 0] 0 0 W

variable {F K I B : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}

/-- A basis adapted to the hyperbolic quaternion pair, together with the
ordinary scalar extension of the change to matrix coordinates. In
characteristic two the last field identifies the generalized quadratic form
of the semitrace with `Q(x,y,z) = [bar(x)z]+Q_W(y)`. -/
structure QuaternionHyperbolicPresentation (D : DescendedQuadraticPair ρ)
    (hB : isCentralSimple F B) (d : ℕ) where
  conjugation : Involution F B
  canonical : ∀ x, antiValue conjugation.anti x = quaternionConjugate hB x
  complement : (Matrix (Fin d) (Fin d) B)ˣ
  matrixModel : ρ.fixedSubalgebra ≃ₐ[F] Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) B
  matrixAt : ∀ (R : TestAlgebra F), (R ⊗[F] ρ.fixedSubalgebra) ≃ₐ[R]
    Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) (R ⊗[F] B)
  matrixAtFormula : ∀ (R : TestAlgebra F) (r : R) (x : ρ.fixedSubalgebra),
    matrixAt R (r ⊗ₜ[F] x) = (matrixModel x).map (fun b => r ⊗ₜ[F] b)
  adjoint : ∀ x : ρ.fixedSubalgebra,
    quaternionHyperbolicGram complement.val * matrixModel (D.involution.toLinearMap x) =
      dagger conjugation.anti (matrixModel x) * quaternionHyperbolicGram complement.val
  quadratic : (2 : F) = 0 →
    ∃ (ℓ : ρ.fixedSubalgebra) (ℓW : Matrix (Fin d) (Fin d) B),
      ℓ + D.involution.toLinearMap ℓ = 1 ∧
      (∀ s : symmetricPart D.involution, D.semitrace s = -(_root_.Specs.RM03.CSA.reducedCharpoly D.centralSimple (ℓ * s.val)).coeff
        (degree F ρ.fixedSubalgebra - 1)) ∧
      ∀ (x z : B) (y : Fin d → B),
        let v : QuaternionPairIndex d → B := Sum.elim ![x,z] y
        hermitianValue conjugation.anti (quaternionHyperbolicGram complement.val)
            v (matrixModel ℓ *ᵥ v) -
          (antiValue conjugation.anti x * z + hermitianValue conjugation.anti complement.val y (ℓW *ᵥ y))
          ∈ Set.range (algebraMap F B)

/-- Transport a unit by inverse conjugation. Both operations reverse the
multiplication order, so their composite preserves it. -/
def inverseConjugateUnit {C : Type u} [Ring C] (σ : C →* Cᵐᵒᵖ) : Cˣ →* Cˣ where
  toFun t := (Units.opEquiv (Units.map σ t)).unop⁻¹
  map_one' := by simp
  map_mul' t t' := by rw [map_mul, map_mul, unop_mul, _root_.mul_inv_rev]

/-- The diagonal action on the displayed right quaternion coordinates. -/
def diagonalQuaternionScale {C : Type u} [Ring C] (σ : C →* Cᵐᵒᵖ) (d : ℕ) :
    Cˣ →* (Matrix (QuaternionPairIndex d) (QuaternionPairIndex d) C)ˣ :=
  ((Units.map (Matrix.diagonalRingHom (n := QuaternionPairIndex d) (α := C)).toMonoidHom).comp
    (MulEquiv.piUnits :
      (QuaternionPairIndex d → C)ˣ ≃* (QuaternionPairIndex d → Cˣ)).symm.toMonoidHom).comp
      { toFun := fun t => Sum.elim ![t, inverseConjugateUnit σ t] (fun _ => 1)
        map_one' := by
          funext i
          rcases i with i | i
          · fin_cases i <;> simp
          · rfl
        map_mul' := by
          intro t t'
          funext i
          rcases i with i | i
          · fin_cases i <;> simp
          · simp }

/-- The scale endomorphism of the actual scalar extension of the descended
central simple algebra. -/
noncomputable def quaternionScale {D : DescendedQuadraticPair ρ}
    {hB : isCentralSimple F B} {d : ℕ} (Q : QuaternionHyperbolicPresentation D hB d)
    (R : TestAlgebra F) : (R ⊗[F] B)ˣ →* (R ⊗[F] ρ.fixedSubalgebra)ˣ :=
  (Units.map (Q.matrixAt R).symm.toMonoidHom).comp
    (diagonalQuaternionScale (extendAnti Q.conjugation.anti R).toMonoidHom d)

/-- The vector projection to the unit group of the descended algebra. -/
noncomputable def spinVectorProjection {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (P : SpinModel G D) (R : TestAlgebra F) :
    Points G.val.X R →* (R ⊗[F] ρ.fixedSubalgebra)ˣ :=
  (P.fullPoints R).comp (((groupPointsFunctor F).map (P.projection ≫ P.inclusion)).app R).hom

/-- The genuine pullback of the vector projection along the scale subgroup,
defined on every test algebra. Its multiplication is the product law. -/
noncomputable def spinScalePreimage {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ}
    (P : SpinModel G D) {hB : isCentralSimple F B} {d : ℕ} (Q : QuaternionHyperbolicPresentation D hB d)
    (R : TestAlgebra F) :
    Subgroup (Points G.val.X R × (R ⊗[F] B)ˣ) :=
  ((spinVectorProjection P R).comp (MonoidHom.fst _ _)).eqLocus
    ((quaternionScale Q R).comp (MonoidHom.snd _ _))

/-- The full scheme preimage over the quaternion hyperbolic scale subgroup,
with its projection, scalar kernel, and scalar extension on test algebras. -/
def SpinScaleCover : Prop :=
  ∀ {F K I B : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    [Fintype I] [DecidableEq I] [DivisionRing B] [Algebra F B]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
    {G : AffineAlgebraicGroup F} {D : DescendedQuadraticPair ρ} (P : SpinModel G D),
    4 ≤ Fintype.card I → ∀ (hB : isCentralSimple F B), degree F B = 2 →
    ∀ (d : ℕ) (Q : QuaternionHyperbolicPresentation D hB d)
      {J : Type u} [Fintype J] (b : Module.Basis J F B),
    (∀ (R : TestAlgebra F) (t : (R ⊗[F] B)ˣ),
      ∃ a : Points P.neutral.val.X R,
        P.fullPoints R (a ≫ P.inclusion.hom.hom) = quaternionScale Q R t) ∧
    ∃ (N : ∀ R : TestAlgebra F, (R ⊗[F] B)ˣ →* Rˣ)
      (e : ∀ R : TestAlgebra F, spinScalePreimage P Q R ≃* scalePairs (N R)),
      (∀ (R : TestAlgebra F) (t : (R ⊗[F] B)ˣ), (N R t : R) = normAt hB b t.val) ∧
      (∀ R x, (e R x).val.1 = x.val.2) ∧
      (∀ (R S : TestAlgebra F) (f : R ⟶ S) (x : spinScalePreimage P Q R) (y : spinScalePreimage P Q S),
        y.val.1 = mapPoints f x.val.1 →
        y.val.2 = Units.map (tensorMap B f.hom).toMonoidHom x.val.2 →
        (e S y).val.2 = Units.map f.hom.toMonoidHom (e R x).val.2) ∧
      (∀ (R : TestAlgebra F) (z : Points P.kernel.group.X R),
        ∃ x : spinScalePreimage P Q R, x.val = (z ≫ P.kernel.inclusion.hom.hom, 1) ∧
          (e R x).val = (1, (P.kernelPoints R z).val)) ∧
      ∃ (H : AffineAlgebraicGroup F) (incl : H.val ⟶ G.val)
        (φ : ∀ R : TestAlgebra F, Points H.val.X R ≃* spinScalePreimage P Q R),
        IsClosedImmersion incl.hom.hom.left ∧ Smooth H.val.X.hom ∧
        GeometricallyConnected H.val.X.hom ∧ GeometricallyReduced H.val.X.hom ∧
        (∀ (R : TestAlgebra F) (x : Points H.val.X R), (φ R x).val.1 = x ≫ incl.hom.hom) ∧
        (∀ (R S : TestAlgebra F) (f : R ⟶ S) (x : Points H.val.X R),
          (φ S (mapPoints f x)).val.2 = Units.map (tensorMap B f.hom).toMonoidHom (φ R x).val.2) ∧
        ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L) (_ : IsGalois F L)
          (E : ∀ S : TestAlgebra L, let R := (restrictTestAlgebra F L).obj S
            (R ⊗[F] B) ≃ₐ[S] Matrix (Fin 2) (Fin 2) S)
          (ξ : ∀ S : TestAlgebra L, Points ((groupBaseChange F L).obj H.val).X S ≃
            (Matrix.SpecialLinearGroup (Fin 2) S × Sˣ)),
          (∀ (S : TestAlgebra L), let R := (restrictTestAlgebra F L).obj S
            ∀ (t : (R ⊗[F] B)ˣ), (E S t.val).det = (N R t : R)) ∧
          (∀ (S : TestAlgebra L) (x : Points ((groupBaseChange F L).obj H.val).X S),
            let R := (restrictTestAlgebra F L).obj S
            let z := (e R (φ R (baseChangePoint F L H.val.X S x))).val
            (ξ S x).1.val = scaleRow 0 ((↑z.2⁻¹ : S) ^ 2) (E S z.1.val) ∧ (ξ S x).2 = z.2) ∧
          ∀ (S T : TestAlgebra L) (g : S ⟶ T) (x : Points ((groupBaseChange F L).obj H.val).X S),
            ξ T (mapPoints g x) =
              (Matrix.SpecialLinearGroup.map g.hom.toRingHom (ξ S x).1,
                Units.map g.hom.toMonoidHom (ξ S x).2)

end QuaternionModel

end LinearAlgebraicGroups.Specs.Arithmetic.QuaternionSpinScaleCover
