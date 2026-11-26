import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.IntegralZornDirections
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.FrameTangentRank
import Mathlib.LinearAlgebra.Matrix.Trace
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SmoothIdentityCriterion

namespace LinearAlgebraicGroups.Albert.ShortDirectionSpecification

open _root_.LinearAlgebraicGroups.Composition
open CubicSpecification TrialitySpecification HermitianSpecification FrameSpecification

universe u

abbrev Square (R : Type u) := Matrix (Fin 3) (Fin 3) R

abbrev ThreeMatrices (R : Type u) := Square R × Square R × Square R

variable {R : Type u} [CommRing R]

/-- The matrix (A) uses the lower scalar in position (j,ell)
and the upper scalar in position (ell,j) for a cyclic triple. -/
def matrixCoordinates (x : Model R) : ThreeMatrices R :=
  let c := fun i => Zorn.coordinates R (x.2 i)
  ( ![![x.1 0, (c 2).2.2.2, (c 1).1],
      ![(c 2).1, x.1 1, (c 0).2.2.2],
      ![(c 1).2.2.2, (c 0).1, x.1 2]],
    fun i j => (c i).2.1 j,
    fun i j => -(c j).2.2.1 i )

/-- The determinant-trace cubic in the source coordinates. -/
def matrixNorm (x : ThreeMatrices R) : R :=
  x.1.det + x.2.1.det + x.2.2.det - (x.1 * x.2.1 * x.2.2).trace

abbrev splitNorm (x : Model R) : R :=
  cubicNorm (Composition.ZornSpecification.norm R) (fun _ => 1) x

def MatrixCoordinatesType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ e : Model R ≃ₗ[R] ThreeMatrices R, ∀ x, e x = matrixCoordinates x

def MatrixNormType : Prop :=
  ∀ (R : Type u) [CommRing R],
    matrixCoordinates (cubicUnit (R := R) (A := Zorn R)) =
      ((1 : Square R), 0, 0) ∧
    ∀ x : Model R, splitNorm x = matrixNorm (matrixCoordinates x)

/-- The specified action on the three matrices. -/
def matrixAction (g : Matrix.SpecialLinearGroup (Fin 3) R)
    (x : ThreeMatrices R) : ThreeMatrices R :=
  let G : Square R := g
  let H : Square R := ↑(g⁻¹)
  (G * x.1 * H, G * x.2.1, x.2.2 * H)

def MatrixActionType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 3) R →* (Model R ≃ₗ[R] Model R),
      (∀ g x, matrixCoordinates (ρ g x) = matrixAction g (matrixCoordinates x)) ∧
      (∀ g, ρ g cubicUnit = cubicUnit) ∧
      ∀ g x, splitNorm (ρ g x) = splitNorm x

/-- The action is compatible with all scalar homomorphisms. -/
def MatrixActionNaturalityType : Prop :=
  ∀ (ρ : ∀ (R : Type u) [CommRing R],
      Matrix.SpecialLinearGroup (Fin 3) R →* (Model R ≃ₗ[R] Model R)),
    (∀ (R : Type u) [CommRing R] g x,
      matrixCoordinates (ρ R g x) = matrixAction g (matrixCoordinates x)) →
    ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
      (g : Matrix.SpecialLinearGroup (Fin 3) R) (x : Model R),
        mapModel f (ρ R g x) = ρ S (Matrix.SpecialLinearGroup.map f g) (mapModel f x)

/-- Frame evaluation for the family (I+tE_{ell j}), where ((i,j,ell)) is cyclic.
This formula holds over every scalar algebra, in particular on dual numbers. -/
def TransvectionFrameType : Prop :=
  ∀ (R : Type u) [CommRing R],
    ∃ ρ : Matrix.SpecialLinearGroup (Fin 3) R →* (Model R ≃ₗ[R] Model R),
      (∀ g x, matrixCoordinates (ρ g x) = matrixAction g (matrixCoordinates x)) ∧
      ∀ i : Fin 3, ∃ τ : Multiplicative R →* Matrix.SpecialLinearGroup (Fin 3) R,
        ∀ t : R, let g := τ (Multiplicative.ofAdd t)
          (g : Square R) = Matrix.transvection (cyclicPrev i) (cyclicNext i) t ∧
          ρ g (frameAxis i) = frameAxis i ∧
          ρ g (frameAxis (cyclicNext i)) = frameAxis (cyclicNext i) +
            t • singleBlockCoordinates i (Composition.ZornSpecification.first R) ∧
          ρ g (frameAxis (cyclicPrev i)) = frameAxis (cyclicPrev i) -
            t • singleBlockCoordinates i (Composition.ZornSpecification.first R)

/-- Evaluation records the coefficient on each incident block at the first
of its two endpoints in cyclic order. -/
def frameEvaluation (R : Type u) [CommRing R] :
    Module.End R (Model R) →ₗ[R] (Fin 3 → Zorn R) where
  toFun D i := (D (frameAxis (cyclicNext i))).2 i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The full ordered-frame differential is determined by its three incident
values, with opposite signs at the two endpoints of each block. -/
def FrameEvaluationType : Prop :=
  ∀ (R : Type u) [CommRing R]
    (J : _root_.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan R (Model R)),
    J.unit = cubicUnit → (∀ x y, J.groundOp x y = modelOp x y) →
    ∀ D : Module.End R (Model R),
      _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms.IsQuadraticDerivation J D →
      ∀ i : Fin 3, D (frameAxis i) = (0, fun j =>
        if i = cyclicNext j then frameEvaluation R D j
        else if i = cyclicPrev j then -(frameEvaluation R D j) else 0)

/-- The kernel is exactly the derivations fixing the entire ordered frame. -/
def FrameEvaluationKernelType : Prop :=
  ∀ (R : Type u) [CommRing R]
    (J : _root_.Specs.LinearAlgebraicGroups.Albert.QuadraticJordan R (Model R)),
    J.unit = cubicUnit → (∀ x y, J.groundOp x y = modelOp x y) →
    ∀ D : Module.End R (Model R),
      _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms.IsQuadraticDerivation J D →
      (frameEvaluation R D = 0 ↔ ∀ i, D (frameAxis i) = 0)

open _root_.Specs.LinearAlgebraicGroups.Albert
open _root_.Specs.LinearAlgebraicGroups.Albert.Automorphisms
open IntegralZornDirectionsSpecification (DirectionIndex direction)
open scoped TensorProduct DualNumber

/-- Integral additive families in the automorphism group, with their action on the frame. -/
structure IntegralShortFamilies where
  family : ∀ (R : Type u) [CommRing R], Fin 3 → DirectionIndex →
    Multiplicative R →* (Model R ≃ₗ[R] Model R)
  natural : ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (i : Fin 3) (j : DirectionIndex) (t : R) (x : Model R),
    mapModel f (family R i j (Multiplicative.ofAdd t) x) =
      family S i j (Multiplicative.ofAdd (f t)) (mapModel f x)
  preserves : ∀ (R : Type u) [CommRing R] (J : QuadraticJordan R (Model R)),
    J.unit = cubicUnit → (∀ x y, J.groundOp x y = modelOp x y) →
    ∀ i j t, (SplitSpecification.ParaQuadratic.ofJordan J).IsIso
      (SplitSpecification.ParaQuadratic.ofJordan J) (family R i j (Multiplicative.ofAdd t))
  evaluates : ∀ (R : Type u) [CommRing R] (i : Fin 3) (j : DirectionIndex) (t : R),
    let a := family R i j (Multiplicative.ofAdd t)
    a (frameAxis i) = frameAxis i ∧
    a (frameAxis (cyclicNext i)) = frameAxis (cyclicNext i) +
      t • singleBlockCoordinates i (direction R j) ∧
    a (frameAxis (cyclicPrev i)) = frameAxis (cyclicPrev i) -
      t • singleBlockCoordinates i (direction R j)

def IntegralShortFamiliesType : Prop := Nonempty IntegralShortFamilies.{u}

/-- The tangent module of the quadratic automorphism functor in the split coordinates. -/
def splitDerivations (J : QuadraticJordan R (Model R)) : Submodule R (Module.End R (Model R)) where
  carrier := {D | IsQuadraticDerivation J D}
  zero_mem' := by simp [IsQuadraticDerivation, QuadraticJordan.polar]
  add_mem' := by
    intro D E hD hE
    refine ⟨by simp [hD.1, hE.1], ?_⟩
    intro S _ _ x y
    simp only [LinearMap.baseChange_add, LinearMap.add_apply, hD.2 S x y, hE.2 S x y, map_add]
    abel
  smul_mem' := by
    intro c D hD
    refine ⟨by simp [hD.1], ?_⟩
    intro S _ _ x y
    simp only [LinearMap.baseChange_smul, LinearMap.smul_apply, hD.2 S x y,
      LinearMap.map_smul_of_tower, smul_add]

/-- The short-family differential is defined by its action on the dual-number extension. -/
def ShortDifferentialsType : Prop :=
  ∃ F : IntegralShortFamilies.{u},
    ∀ (k : Type u) [Field k] (J : QuadraticJordan k (Model k)),
      J.unit = cubicUnit → (∀ x y, J.groundOp x y = modelOp x y) →
      ∃ D : Fin 3 → DirectionIndex → splitDerivations J,
        (∀ i j x,
          F.family (DualNumber k) i j (Multiplicative.ofAdd ε)
            (modelBaseChange k (DualNumber k) x) =
              modelBaseChange k (DualNumber k) (infinitesimal (D i j).val x)) ∧
        ∀ i j, frameEvaluation k (D i j).val = Pi.single i (direction k j)

def SplitTangentRankType : Prop :=
  ∀ (k : Type u) [Field k] (J : QuadraticJordan k (Model k)),
    J.unit = cubicUnit → (∀ x y, J.groundOp x y = modelOp x y) →
    Function.Surjective ((frameEvaluation k).domRestrict (splitDerivations J)) ∧
    LinearMap.ker ((frameEvaluation k).domRestrict (splitDerivations J)) =
      (FrameTangentSpecification.frameDerivations J).comap (splitDerivations J).subtype ∧
    Module.finrank k (splitDerivations J) = 52


/-- The ordered-frame kernel is identified using the represented frame group on dual numbers. -/
def FrameLieKernelType : Prop :=
  ∀ (k : Type u) [Field k] (J : QuadraticJordan k (Model k)),
    J.unit = cubicUnit → (∀ x y, J.groundOp x y = modelOp x y) →
    ∃ (G : FrameTangentSpecification.FrameRepresentation k)
      (m : _root_.LinearAlgebraicGroups.Specs.LieVectorStructure G.group),
      letI := m.addGroup
      letI := m.module
      let K := LinearMap.ker ((frameEvaluation k).domRestrict (splitDerivations J))
      ∃ e : K ≃ₗ[k] _root_.LinearAlgebraicGroups.Specs.Lie k G.group,
        (∀ D x, (G.points (CommAlgCat.of k (DualNumber k))
          (e D).toMul.val).val (modelBaseChange k (DualNumber k) x) =
            modelBaseChange k (DualNumber k) (infinitesimal D.val.val x)) ∧
        Module.finrank k K = 28

/-- Coordinates for the closed integral automorphism scheme of the split Albert model. -/
structure IntegralPresentation where
  jordan : QuadraticJordan ℤ (Model ℤ)
  unit_eq : jordan.unit = cubicUnit
  ground_op : ∀ x y, jordan.groundOp x y = modelOp x y
  basis : Module.Basis (Fin 27) ℤ (Model ℤ)
  subgroup : MatrixSubgroup ℤ (Fin 27)
  equations : OperationEquationIndex (Fin 27) → MatrixCoordinates ℤ (Fin 27)
  cutsOut : CutsOut (Ideal.span (Set.range equations)) subgroup
  presents : ∀ (S : Type) [CommRing S] [Algebra ℤ S] (g : Matrix.GeneralLinearGroup (Fin 27) S),
    g ∈ subgroup.subgroup S ↔
      PreservesQuadratic jordan S (Automorphisms.matrixAction basis S g)

abbrev IntegralPresentation.Coordinates (P : IntegralPresentation) :=
  MatrixCoordinates ℤ (Fin 27) ⧸ Ideal.span (Set.range P.equations)

/-- This algebra map describes the identity section, using the universal matrix in the quotient. -/
def IntegralPresentation.IsIdentity (P : IntegralPresentation) (e : P.Coordinates →ₐ[ℤ] ℤ) : Prop :=
  ∀ i j, e (Ideal.Quotient.mk _ (coordinateMatrix (R := ℤ) i j)) =
    (1 : Matrix (Fin 27) (Fin 27) ℤ) i j

/-- A basis of relative standard smooth neighborhoods of dimension 52 covers the
integral identity section. Field-valued identity points include all its scheme points
by taking the residue field. -/
def IntegralSmoothIdentityType : Prop :=
  ∃ (P : IntegralPresentation) (e : P.Coordinates →ₐ[ℤ] ℤ),
    P.IsIdentity e ∧
    ∀ (k : Type) [Field k], ∃ f : P.Coordinates,
      algebraMap ℤ k (e f) ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension 52 ℤ (Localization.Away f)

end LinearAlgebraicGroups.Albert.ShortDirectionSpecification
