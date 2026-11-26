import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.AffineWeilRestriction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.CharacterDescent
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

open CategoryTheory CategoryTheory.Limits Opposite WithConv
open LinearAlgebraicGroups.WeilRestriction
open LinearAlgebraicGroups.Specs.StandardGroups (multiplicativePoints)
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.NormOneTorus

/-- There is exactly one nonidentity automorphism of a separable quadratic extension. -/
def QuadraticAutomorphism : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsQuadraticExtension k K] [Algebra.IsSeparable k K],
    ∃! σ : Gal(K/k), σ ≠ 1

/-- Over any algebra over the splitting field, evaluate at the two embeddings.
The determinant of multiplication becomes the product of the two coordinates. -/
def QuadraticTensorSplitting : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsQuadraticExtension k K] [Algebra.IsSeparable k K]
    (σ : Gal(K/k)), σ ≠ 1 →
    ∀ (R : Type u) [CommRing R] [Algebra k R] [Algebra K R] [IsScalarTower k K R],
      ∃ e : R ⊗[k] K ≃ₐ[R] R × R,
        (∀ (r : R) (b : K),
          e (r ⊗ₜ b) = (r * algebraMap K R b, r * algebraMap K R (σ b))) ∧
        ∀ x, Algebra.norm R x = (e x).1 * (e x).2

noncomputable section

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- The norm is characterized by the B04 determinant formula on every test algebra. -/
def RealizesNorm {W H : AffineAlgebraicGroup k}
    (e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K)
    (t : (groupPointsFunctor k).obj H.val ≅ multiplicativePoints k)
    (n : W.val ⟶ H.val) : Prop :=
  ∀ (R : TestAlgebra k) (x : ((groupPointsFunctor k).obj W.val).obj R),
    (t.hom.app R (((groupPointsFunctor k).map n).app R x) : Rˣ).val =
      pointNorm k K R (e.hom.app R x : (R ⊗[k] K)ˣ).val

/-- The norm-one points form the kernel subgroup of the determinant on the unit group. -/
abbrev normOnePoints (k K : Type u) [Field k] [Field K] [Algebra k K]
    (R : TestAlgebra k) : Subgroup (R ⊗[k] K)ˣ :=
  (Units.map (pointNorm k K R)).ker

/-- Scheme kernel with its specified inclusion on all points. -/
structure KernelModel {W H : AffineAlgebraicGroup k}
    (e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K)
    (n : W.val ⟶ H.val) where
  coordinate : HopfAlgebraCategory k
  finiteType : Algebra.FiniteType k coordinate
  inclusion : specGroup coordinate ⟶ W.val
  pullback : IsPullback inclusion (specGroupMap (hopfUnit coordinate)) n
    (0 : specGroup (CommHopfAlgCat.of k k) ⟶ H.val)
  points : ∀ R : TestAlgebra k, (convolutionPoints coordinate).obj R ≃* normOnePoints k K R
  points_inclusion : ∀ (R : TestAlgebra k) (f : WithConv (coordinate →ₐ[k] R)),
    ((points R f : normOnePoints k K R) : (R ⊗[k] K)ˣ) =
      e.hom.app R (((groupPointsFunctor k).map inclusion).app R
        ((testSpec k).map (CommAlgCat.ofHom f.ofConv).op))

/-- The determinant norm has an affine finite-type scheme kernel. -/
def NormKernel : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    (W H : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K)
    (t : (groupPointsFunctor k).obj H.val ≅ multiplicativePoints k)
    (n : W.val ⟶ H.val), RealizesNorm e t n → Nonempty (KernelModel e n)

section Splitting

open DiagonalizableGroups CharacterDescent
open LinearAlgebraicGroups.Descent (SemilinearAction)

variable {L : Type u} [Field L] [Algebra k L]

/-- Evaluate the scalar algebra into a test algebra via one field embedding. -/
def testEmbedding (j : K →ₐ[k] L) (R : TestAlgebra L) : K →ₐ[k] (restrictTestAlgebra k L).obj R where
  toRingHom := (algebraMap L R).comp j.toRingHom
  commutes' a := congrArg (algebraMap L R) (j.commutes a)

/-- The map of a scalar-extended test algebra induced by a chosen embedding. -/
def evaluateEmbedding (R : TestAlgebra k) (j : K →ₐ[k] R) :
    R ⊗[k] K →ₐ[R] R :=
  AlgHom.liftEquiv k R K R j

/-- The split coordinate algebra, normalized by the first embedding of the scalar algebra. -/
def NormalizedSplitting {W H : AffineAlgebraicGroup k}
    {e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K} {n : W.val ⟶ H.val}
    (T : KernelModel e n) (j : K →ₐ[k] L) (σ : Gal(K/k)) : Prop :=
  ∃ d : groupAlgebra L IntegerCharacters ≅ extendedHopf L T.coordinate,
    ∀ (R : TestAlgebra L) (f : extendedHopf L T.coordinate →ₐ[L] R),
      let S := (restrictTestAlgebra k L).obj R
      letI : IsScalarTower k L S := IsScalarTower.of_algebraMap_eq' rfl
      let f₀ := (AlgHom.liftEquiv k L T.coordinate S).symm f
      let w := (T.points S (toConv f₀)).val.val
      let u := f (d.hom.hom (MonoidAlgebra.of L IntegerCharacters integerGenerator))
      (evaluateEmbedding S (testEmbedding j R) w,
        evaluateEmbedding S ((testEmbedding j R).comp σ.toAlgHom) w) =
      (u, f (d.hom.hom (MonoidAlgebra.of L IntegerCharacters (integerGenerator⁻¹))))

/-- A rank-one torus split by the quadratic extension, with its specified parameter. -/
def KernelSplitting : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsQuadraticExtension k K] [Algebra.IsSeparable k K]
    (σ : Gal(K/k)), σ ≠ 1 →
    ∀ (W H : AffineAlgebraicGroup k)
      (e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K)
      (n : W.val ⟶ H.val) (T : KernelModel e n),
      IsTorus T.coordinate ∧
      Nonempty ((groupBaseChange k K).obj (specGroup T.coordinate) ≅
        specGroup (groupAlgebra K IntegerCharacters)) ∧
      ∀ (L : Type u) [Field L] [Algebra k L] (j : K →ₐ[k] L),
        NormalizedSplitting T j σ

/-- The character lattice over every field containing the quadratic splitting field.
In a compatible separable closure this is the geometric lattice, with the action
factoring through restriction to the quadratic extension. -/
def CharacterAction : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    [Algebra.IsQuadraticExtension k K] [Algebra.IsSeparable k K]
    (W H : AffineAlgebraicGroup k)
    (e : (groupPointsFunctor k).obj W.val ≅ extendedUnits k K)
    (n : W.val ⟶ H.val) (T : KernelModel e n)
    (L : Type u) [Field L] [Algebra k L] [Algebra K L] [IsScalarTower k K L],
    ∃ χ : IntegerCharacters.{u} ≃* GeometricCharacters L T.coordinate,
      ∀ (τ : Gal(L/k)) (m : IntegerCharacters.{u}),
        let a := (SemilinearAction.scalarExtension (k := k) (K := L) T.coordinate).act τ
        (AlgEquiv.restrictNormalHom K τ = 1 → a (χ m).val = (χ m).val) ∧
        (AlgEquiv.restrictNormalHom K τ ≠ 1 → a (χ m).val = (χ m⁻¹).val)

end Splitting

/-- The two coordinates of an element of the scalar-extended complex plane. -/
abbrev complexCoordinates (R : TestAlgebra ℝ) : (R ⊗[ℝ] ℂ) ≃ₗ[R] (Fin 2 → R) :=
  (Complex.basisOneI.baseChange R).equivFun

/-- The affine circle on every real test algebra, with coordinates in the basis (1,i). -/
def RealCircleEquation : Prop :=
  ∀ (W H : AffineAlgebraicGroup ℝ)
    (e : (groupPointsFunctor ℝ).obj W.val ≅ extendedUnits ℝ ℂ)
    (n : W.val ⟶ H.val) (T : KernelModel e n),
    ∃ c : ∀ R : TestAlgebra ℝ, (convolutionPoints T.coordinate).obj R ≃
        {v : Fin 2 → R // v 0 ^ 2 + v 1 ^ 2 = 1},
      (∀ (R : TestAlgebra ℝ) (f : (convolutionPoints T.coordinate).obj R),
        (c R f).val = complexCoordinates R (T.points R f).val.val) ∧
      ∀ {R S : TestAlgebra ℝ} (a : R ⟶ S) (f : (convolutionPoints T.coordinate).obj R) (i : Fin 2),
        (c S ((convolutionPoints T.coordinate).map a f)).val i = a.hom ((c R f).val i)

/-- The determinant and matrix of complex multiplication over any real test algebra. -/
def ComplexMultiplication : Prop :=
  ∀ (R : TestAlgebra ℝ) (z : R ⊗[ℝ] ℂ),
    let v := complexCoordinates R z
    Algebra.leftMulMatrix (Complex.basisOneI.baseChange R) z =
      !![v 0, -v 1; v 1, v 0] ∧ pointNorm ℝ ℂ R z = v 0 ^ 2 + v 1 ^ 2

/-- The real affine circle acts rationally on the real plane. -/
def RealCircleAction : Prop :=
  ∀ (W H L : AffineAlgebraicGroup ℝ)
    (e : (groupPointsFunctor ℝ).obj W.val ≅ extendedUnits ℝ ℂ)
    (n : W.val ⟶ H.val) (T : KernelModel e n)
    (g : (groupPointsFunctor ℝ).obj L.val ≅ StandardGroups.generalLinearPoints ℝ (Fin 2)),
    ∃ ρ : specGroup T.coordinate ⟶ L.val,
      ∀ (R : TestAlgebra ℝ) (f : WithConv (T.coordinate →ₐ[ℝ] R)),
        let z := (T.points R f).val.val
        let v := complexCoordinates R z
        (g.hom.app R (((groupPointsFunctor ℝ).map ρ).app R
          ((testSpec ℝ).map (CommAlgCat.ofHom f.ofConv).op)) :
          Matrix.GeneralLinearGroup (Fin 2) R).val = !![v 0, -v 1; v 1, v 0]

end
end LinearAlgebraicGroups.Specs.NormOneTorus
