import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.IdentityTangent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.FaithfulLinearization
import Mathlib.Algebra.Lie.BaseChange

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

namespace InfinitesimalCommutator

/-- The algebra with independent square-zero variables `s,t`, with `s` the
inner dual number and `t` the outer dual number. -/
abbrev TwoVariables (R : Type*) := DualNumber (DualNumber R)

/-- Change the coefficients of a dual number. -/
def mapCoefficients {R S : Type*} [Ring R] [Ring S] (f : R →+* S) :
    DualNumber R →+* DualNumber S where
  toFun z := (f z.fst, f z.snd)
  map_zero' := by apply TrivSqZeroExt.ext <;> exact map_zero f
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one f
    · exact map_zero f
  map_add' x y := by apply TrivSqZeroExt.ext <;> exact map_add f _ _
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul f _ _
    · change f (x.fst * y.snd + x.snd * y.fst) = _
      rw [map_add, map_mul, map_mul]
      rfl

variable (k : Type u) [Field k]

/-- The map `ε ↦ s`. -/
def liftS : DualNumber k →ₐ[k] TwoVariables k :=
  TrivSqZeroExt.inlAlgHom k (DualNumber k) (DualNumber k)

/-- The map `ε ↦ t`. -/
def liftT : DualNumber k →ₐ[k] TwoVariables k where
  toRingHom := mapCoefficients (algebraMap k (DualNumber k))
  commutes' _ := rfl

/-- The map `ε ↦ st`. -/
def liftST : DualNumber k →ₐ[k] TwoVariables k where
  toFun z := ((z.fst, 0), (0, z.snd))
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := by
    apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext <;>
      first | rfl | exact (zero_add (0 : k)).symm
  map_mul' x y := by
    apply TrivSqZeroExt.ext <;> apply TrivSqZeroExt.ext
    · rfl
    · change 0 = x.fst * 0 + 0 * y.fst
      simp
    · change 0 = x.fst * 0 + 0 * y.fst
      simp
    · change x.fst * y.snd + x.snd * y.fst =
        x.fst * y.snd + 0 * 0 + (0 * 0 + x.snd * y.fst)
      simp
  commutes' _ := rfl

variable {k}

/-- Push two tangent lifts into the same two-variable algebra and take the
commutator in the order `xyx⁻¹y⁻¹`. -/
def commutator (F : TestAlgebra k ⥤ GrpCat.{u}) (p q : DualKernel F) :
    F.obj (CommAlgCat.of k (TwoVariables k)) :=
  let x := (F.map (CommAlgCat.ofHom (liftS k))).hom p.toMul.val
  let y := (F.map (CommAlgCat.ofHom (liftT k))).hom q.toMul.val
  x * y * x⁻¹ * y⁻¹

def IsBracket (F : TestAlgebra k ⥤ GrpCat.{u})
    (b : DualKernel F → DualKernel F → DualKernel F) : Prop :=
  ∀ p q, (F.map (CommAlgCat.ofHom (liftST k))).hom (b p q).toMul.val =
    commutator F p q

/-- The matrix of the differential, given by the coefficient of `ε` on
each entry of the matrix of the dual-number point. -/
def matrixDifferential {G L : Specs.GroupScheme k}
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (f : G ⟶ L)
    (l : (groupPointsFunctor k).obj L ≅ Specs.StandardGroups.generalLinearPoints k ι)
    (p : Specs.Lie k G) : Matrix ι ι k :=
  fun i j =>
    (((l.hom.app (CommAlgCat.of k (DualNumber k))).hom
      (mapPointKernel f p).toMul.val : Matrix.GeneralLinearGroup ι (DualNumber k)).val i j).snd

end InfinitesimalCommutator

namespace Specs

open InfinitesimalCommutator

/-- The two-variable algebra represents pairs of independent square-zero
elements, the universal property of the indicated polynomial quotient. -/
def TwoVariablesUniversalProperty : Prop :=
  ∀ (k R : Type u) [Field k] [CommRing R] [Algebra k R],
    ∃ e : (TwoVariables k →ₐ[k] R) ≃ {z : R × R // z.1 * z.1 = 0 ∧ z.2 * z.2 = 0},
      ∀ f, (e f).val = (f (liftS k DualNumber.eps), f (liftT k DualNumber.eps)) ∧
        f (liftST k DualNumber.eps) = (e f).val.1 * (e f).val.2

def IntrinsicLieBracketType :=
  ∀ (k : Type u) [Field k] (G : GroupScheme k) [IsAffine G.X.left],
    Lie k G → Lie k G → Lie k G

/-- Choose the tangent coefficient characterized by the mixed lift equation. -/
def intrinsicLieBracket : IntrinsicLieBracketType.{u} := fun k _ G _ p q =>
  let F := (groupPointsFunctor k).obj G
  letI : Nonempty (Lie k G) := ⟨0⟩
  Classical.epsilon fun r : Lie k G =>
    (F.map (CommAlgCat.ofHom (liftST k))).hom r.toMul.val = commutator F p q

def IntrinsicLieBracketCorrect : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme k) [IsAffine G.X.left],
    IsBracket ((groupPointsFunctor k).obj G) (intrinsicLieBracket k G)

/-- The Lie structure on the actual identity tangent kernel. -/
structure IdentityLieStructure {k : Type u} [Field k] (G : GroupScheme k) where
  lieRing : LieRing (Lie k G)
  group_law : lieRing.toAddCommGroup.toAddGroup = (inferInstance : AddGroup (PointKernel G))
  lieAlgebra : @LieAlgebra k (Lie k G) _ lieRing
  scalar_law : lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul.smul = scalePointKernel G
  commutator_law : IsBracket ((groupPointsFunctor k).obj G) lieRing.toBracket.bracket

def IdentityLieBracket : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k),
    Nonempty (IdentityLieStructure G.val)

def IdentityLieBracketUnique : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme k) [IsAffine G.X.left]
    (b c : Lie k G → Lie k G → Lie k G),
    IsBracket ((groupPointsFunctor k).obj G) b →
    IsBracket ((groupPointsFunctor k).obj G) c → b = c

def IdentityLieBracketNaturality : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme k) [IsAffine G.X.left] [IsAffine H.X.left]
    (f : G ⟶ H) (b : IdentityLieStructure G) (c : IdentityLieStructure H)
    (p q : Lie k G),
    mapPointKernel f (b.lieRing.toBracket.bracket p q) =
      c.lieRing.toBracket.bracket (mapPointKernel f p) (mapPointKernel f q)

/-- The Lie homomorphism has the original point-kernel differential as its
underlying function. -/
def IdentityDifferentialLieHom : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme k) [IsAffine G.X.left] [IsAffine H.X.left]
    (f : G ⟶ H) (b : IdentityLieStructure G) (c : IdentityLieStructure H),
    letI := b.lieRing
    letI := b.lieAlgebra
    letI := c.lieRing
    letI := c.lieAlgebra
    ∃ d : Lie k G →ₗ⁅k⁆ Lie k H, ∀ p, d p = mapPointKernel f p

def IdentityLieBracketMatrix : Prop :=
  ∀ (k : Type u) [Field k] (G L : GroupScheme k) [IsAffine G.X.left] [IsAffine L.X.left]
    (ι : Type u) [Fintype ι] [DecidableEq ι]
    (f : G ⟶ L) (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι),
    IsClosedImmersion f.hom.hom.left →
    Function.Injective (matrixDifferential f l) ∧
      ∀ (b : IdentityLieStructure G) (p q : Lie k G),
        matrixDifferential f l (b.lieRing.toBracket.bracket p q) =
          matrixDifferential f l p * matrixDifferential f l q -
            matrixDifferential f l q * matrixDifferential f l p

def IdentityLieBracketBaseChange : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] (G : AffineAlgebraicGroup k),
    let H := (groupBaseChange k K).obj G.val
    Nonempty (IdentityLieStructure H) ∧
    ∀ (b : IdentityLieStructure G.val) (c : IdentityLieStructure H),
      letI := b.lieRing
      letI := b.lieAlgebra
      letI := c.lieRing
      letI := c.lieAlgebra
      ∃ e : (K ⊗[k] Lie k G.val) ≃ₗ⁅K⁆ Lie K H,
        ∀ p : Lie k G.val,
          baseChangePoint k K G.val.X (CommAlgCat.of K (DualNumber K))
            (e (1 ⊗ₜ[k] p)).toMul.val =
          mapPoints (extendDualNumber K) p.toMul.val

end Specs

end
end LinearAlgebraicGroups
