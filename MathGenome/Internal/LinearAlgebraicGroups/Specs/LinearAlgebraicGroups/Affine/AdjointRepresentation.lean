import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.LieBracket

open AlgebraicGeometry CategoryTheory
open scoped Matrix TensorProduct

universe u

namespace LinearAlgebraicGroups
namespace Specs.AdjointRepresentation

noncomputable section

variable {k : Type u} [Field k]

/-- Extend coefficients while retaining the square-zero generator. -/
def dualMap {R S : TestAlgebra k} (a : R ⟶ S) :
    CommAlgCat.of k (DualNumber R) ⟶ CommAlgCat.of k (DualNumber S) :=
  CommAlgCat.ofHom {
    toRingHom := InfinitesimalCommutator.mapCoefficients a.hom.toRingHom
    commutes' := fun r => TrivSqZeroExt.ext (a.hom.commutes r) (map_zero a.hom) }

abbrev reduction (R : TestAlgebra k) : CommAlgCat.of k (DualNumber R) ⟶ R :=
  CommAlgCat.ofHom (TrivSqZeroExt.fstHom k R R)

abbrev constants (R : TestAlgebra k) : R ⟶ CommAlgCat.of k (DualNumber R) :=
  CommAlgCat.ofHom (TrivSqZeroExt.inlAlgHom k R R)

def scale (R : TestAlgebra k) (r : R) :
    CommAlgCat.of k (DualNumber R) ⟶ CommAlgCat.of k (DualNumber R) :=
  CommAlgCat.ofHom {
    toFun := fun z => (z.fst, r * z.snd)
    map_zero' := TrivSqZeroExt.ext rfl (mul_zero r)
    map_one' := TrivSqZeroExt.ext rfl (mul_zero r)
    map_add' := fun x y => TrivSqZeroExt.ext rfl (mul_add r x.snd y.snd)
    map_mul' := fun x y => TrivSqZeroExt.ext rfl (by
      change r * (x.fst * y.snd + x.snd * y.fst) =
        x.fst * (r * y.snd) + (r * x.snd) * y.fst
      ring)
    commutes' := fun _ => TrivSqZeroExt.ext rfl (mul_zero r) }

abbrev GroupPoints (G : GroupScheme k) (R : TestAlgebra k) :=
  ((groupPointsFunctor k).obj G).obj R

/-- The relative identity tangent as the kernel of reduction on points. -/
abbrev RelativeTangent (G : GroupScheme k) (R : TestAlgebra k) :=
  Additive (((groupPointsFunctor k).obj G).map (reduction R)).hom.ker

/-- Coordinates of the relative tangent in the scalar-extended basis. The
identification of `R ⊗[k] Lie k G` with `ι → R` is `(b.baseChange R).equivFun`. -/
structure TangentCoordinates (G : GroupScheme k) (ι : Type u) [Fintype ι]
    [DecidableEq ι] [AddCommGroup (Lie k G)] [Module k (Lie k G)]
    (b : Module.Basis ι k (Lie k G)) where
  equiv (R : TestAlgebra k) : (ι → R) ≃+ RelativeTangent G R
  smul (R : TestAlgebra k) (r : R) (v : ι → R) :
    (equiv R (r • v)).toMul.val =
      mapPoints (scale R r) (equiv R v).toMul.val
  naturality {R S : TestAlgebra k} (a : R ⟶ S) (v : ι → R) :
    (equiv S (fun i => a.hom (v i))).toMul.val =
      mapPoints (dualMap a) (equiv R v).toMul.val
  at_base (p : Lie k G) :
    (equiv (CommAlgCat.of k k) (b.equivFun p)).toMul.val = p.toMul.val

/-- Conjugate a tangent lift by the constant lift of an ordinary point. -/
def conjugate {G : GroupScheme k} {R : TestAlgebra k}
    (g : GroupPoints G R) (p : RelativeTangent G R) :
    GroupPoints G (CommAlgCat.of k (DualNumber R)) :=
  let c := (((groupPointsFunctor k).obj G).map (constants R)).hom g
  c * p.toMul.val * c⁻¹

/-- Restricting the base field commutes with adjoining a square-zero generator. -/
def dualRestriction (K : Type u) [Field K] [Algebra k K] (R : TestAlgebra K) :
    (restrictTestAlgebra k K).obj (CommAlgCat.of K (DualNumber R)) ≅
      CommAlgCat.of k (DualNumber ((restrictTestAlgebra k K).obj R)) := by
  let A := (restrictTestAlgebra k K).obj (CommAlgCat.of K (DualNumber R))
  let B := CommAlgCat.of k (DualNumber ((restrictTestAlgebra k K).obj R))
  change A ≅ B
  have h (t : k) :
      @algebraMap k A _ _ A.algebra t = @algebraMap k B _ _ B.algebra t := by
    apply TrivSqZeroExt.ext <;> rfl
  let f : @AlgHom k A B _ _ _ A.algebra B.algebra :=
    @AlgHom.mk k A B _ _ _ A.algebra B.algebra (RingHom.id _) h
  let g : @AlgHom k B A _ _ _ B.algebra A.algebra :=
    @AlgHom.mk k B A _ _ _ B.algebra A.algebra (RingHom.id _) (fun t => (h t).symm)
  refine ⟨ConcreteCategory.ofHom (C := CommAlgCat k) (X := A) (Y := B) f,
    ConcreteCategory.ofHom (C := CommAlgCat k) (X := B) (Y := A) g, ?_, ?_⟩
  · exact CommAlgCat.hom_ext (@AlgHom.ext k A A _ _ _ A.algebra A.algebra _ _ (fun _ => rfl))
  · exact CommAlgCat.hom_ext (@AlgHom.ext k B B _ _ _ B.algebra B.algebra _ _ (fun _ => rfl))

/-- The base change of the scheme homomorphism acts by conjugation in the
basis transported by the canonical scalar-extension map on the Lie algebra. -/
def ScalarExtension {G L : GroupScheme k} {ι : Type u} [Fintype ι] [DecidableEq ι]
    (s : IdentityLieStructure G)
    (b : letI := s.lieRing; letI := s.lieAlgebra; Module.Basis ι k (Lie k G))
    (T : letI := s.lieRing; letI := s.lieAlgebra; TangentCoordinates G ι b)
    (l : (groupPointsFunctor k).obj L ≅ StandardGroups.generalLinearPoints k ι)
    (Ad : G ⟶ L) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K],
    let H := (groupBaseChange k K).obj G
    ∀ (sK : IdentityLieStructure H),
      letI := s.lieRing
      letI := s.lieAlgebra
      letI := sK.lieRing
      letI := sK.lieAlgebra
      ∃ (e : (K ⊗[k] Lie k G) ≃ₗ⁅K⁆ Lie K H)
        (TK : TangentCoordinates H ι ((b.baseChange K).map e.toLinearEquiv)),
        (∀ p : Lie k G,
          baseChangePoint k K G.X (CommAlgCat.of K (DualNumber K)) (e (1 ⊗ₜ[k] p)).toMul.val =
            mapPoints (extendDualNumber K) p.toMul.val) ∧
        (∀ (R : TestAlgebra K) (v : ι → R),
          mapPoints (dualRestriction (k := k) K R).hom
            (baseChangePoint k K G.X (CommAlgCat.of K (DualNumber R)) (TK.equiv R v).toMul.val) =
            (T.equiv ((restrictTestAlgebra k K).obj R) v).toMul.val) ∧
        ∀ (R : TestAlgebra K) (g : GroupPoints H R) (v : ι → R),
          let g' := ((groupPointsFunctor K).map ((groupBaseChange k K).map Ad)).app R g
          let M := (l.hom.app ((restrictTestAlgebra k K).obj R)).hom
            (baseChangePoint k K L.X R g')
          (TK.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (TK.equiv R v)

/-- The adjoint homomorphism represents conjugation on every relative tangent,
and its differential in the same basis represents the Lie bracket. -/
def ConjugationRepresentation : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (s : IdentityLieStructure G.val),
    letI := s.lieRing
    letI := s.lieAlgebra
    ∃ (n : ℕ) (b : Module.Basis (ULift.{u} (Fin n)) k (Lie k G.val))
      (T : TangentCoordinates G.val (ULift.{u} (Fin n)) b)
      (L : AffineAlgebraicGroup k)
      (l : (groupPointsFunctor k).obj L.val ≅ StandardGroups.generalLinearPoints k (ULift.{u} (Fin n)))
      (Ad : G.val ⟶ L.val),
      (∀ (R : TestAlgebra k) (g : GroupPoints G.val R) (v : ULift.{u} (Fin n) → R),
        let M := (l.hom.app R).hom (((groupPointsFunctor k).map Ad).app R g)
        (T.equiv R (M.val *ᵥ v)).toMul.val = conjugate g (T.equiv R v)) ∧
      (∀ (x y : Lie k G.val),
        InfinitesimalCommutator.matrixDifferential Ad l x *ᵥ b.equivFun y =
          b.equivFun ⁅x, y⁆) ∧ ScalarExtension s b T l Ad

/-- The identity tangent, its functorial Lie algebra, and the adjoint representation. -/
def LieAlgebraAndAdjoint : Prop :=
  LieAffineComparison.{u} ∧
  LieFunctoriality.{u} ∧
  IdentityLieBracket.{u} ∧
  IdentityDifferentialLieHom.{u} ∧
  IdentityLieBracketBaseChange.{u} ∧
  ConjugationRepresentation.{u}

end

end Specs.AdjointRepresentation
end LinearAlgebraicGroups
