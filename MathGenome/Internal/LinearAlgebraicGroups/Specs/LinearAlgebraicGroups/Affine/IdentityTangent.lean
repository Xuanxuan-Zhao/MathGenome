import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.HopfAlgebras
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.TangentCotangent
import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

open AlgebraicGeometry CategoryTheory Opposite Coalgebra Bialgebra WithConv
open Specs.AdvCommAlg.Differentials.Tangent
open TensorProduct

universe u

namespace LinearAlgebraicGroups

noncomputable section

variable {k : Type u} [Field k]

/-- The cotangent space at a specified rational point. -/
abbrev PointCotangent {A : Type u} [CommRing A] [Algebra k A] (x : A →ₐ[k] k) :=
  (RingHom.ker x.toRingHom).Cotangent

/-- The dual of the cotangent space at a specified rational point. -/
abbrev PointTangent {A : Type u} [CommRing A] [Algebra k A] (x : A →ₐ[k] k) :=
  Module.Dual k (PointCotangent x)

/-- Reduction from dual-number points to ordinary points. -/
abbrev dualReduction (k : Type u) [Field k] :
    CommAlgCat.of k (DualNumber k) ⟶ CommAlgCat.of k k :=
  CommAlgCat.ofHom (TrivSqZeroExt.fstHom k k k)

abbrev reduceTangentPoints (G : Specs.GroupScheme k) :=
  (((groupPointsFunctor k).obj G).map (dualReduction k)).hom

abbrev DualKernel (F : TestAlgebra k ⥤ GrpCat.{u}) :=
  Additive (F.map (dualReduction k)).hom.ker

/-- The additive type of the kernel of reduction on points of a group scheme. -/
abbrev PointKernel (G : Specs.GroupScheme k) := Additive (reduceTangentPoints G).ker

/-- Substitution of the dual-number generator by a scalar times itself. -/
def dualNumberScale (s : k) : DualNumber k →ₐ[k] DualNumber k :=
  TrivSqZeroExt.map (s • (LinearMap.id : k →ₗ[k] k))

/-- The map on the tangent kernel induced by substitution in the test algebra. -/
def scaleDualKernel (F : TestAlgebra k ⥤ GrpCat.{u}) (s : k) (p : DualKernel F) :
    DualKernel F := by
  let b := CommAlgCat.ofHom (dualNumberScale s)
  let r := CommAlgCat.ofHom (TrivSqZeroExt.fstHom k k k)
  have hr : b ≫ r = r := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro a
    change (dualNumberScale s a).fst = a.fst
    exact TrivSqZeroExt.fst_map _ _
  refine ⟨(F.map b).hom p.toMul.val, ?_⟩
  change (F.map r).hom ((F.map b).hom p.toMul.val) = 1
  have h := congrArg (fun f => (F.map f).hom p.toMul.val) hr
  rw [F.map_comp] at h
  exact h.trans p.toMul.property

abbrev scalePointKernel (G : Specs.GroupScheme k) :=
  scaleDualKernel ((groupPointsFunctor k).obj G)

/-- A natural homomorphism of point functors induces a map on their reduction kernels. -/
def mapDualKernel {F H : TestAlgebra k ⥤ GrpCat.{u}} (f : F ⟶ H) :
    DualKernel F →+ DualKernel H := by
  let r := dualReduction k
  let b := CommAlgCat.of k (DualNumber k)
  let elt (p : DualKernel F) : DualKernel H := ⟨(f.app b).hom p.toMul.val, by
    change (H.map r).hom ((f.app b).hom p.toMul.val) = 1
    have h := congrArg (fun g => GrpCat.Hom.hom g p.toMul.val) (f.naturality r)
    change (f.app _).hom ((F.map r).hom p.toMul.val) = _ at h
    rw [p.toMul.property, map_one] at h
    exact h.symm⟩
  exact {
    toFun := elt
    map_zero' := Subtype.ext (map_one (f.app b).hom)
    map_add' := fun p q => Subtype.ext (map_mul (f.app b).hom p.toMul.val q.toMul.val) }

/-- The differential on point kernels is induced by the original group homomorphism. -/
abbrev mapPointKernel {G H : Specs.GroupScheme k} (f : G ⟶ H) :
    PointKernel G →+ PointKernel H := mapDualKernel ((groupPointsFunctor k).map f)

/-- In Hopf coordinates the point kernel is exactly the lifts of the counit. -/
def hopfKernelLifts (A : HopfAlgebraCategory k) :
    DualKernel (convolutionPoints A) ≃ PointLifts k A k (counitAlgHom k A) where
  toFun p := ⟨p.toMul.val.ofConv,
    congrArg WithConv.ofConv p.toMul.property⟩
  invFun p := ⟨toConv p.val, congrArg toConv p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The group scheme associated to a Hopf algebra. -/
abbrev hopfSpectrum (A : HopfAlgebraCategory k) : Specs.GroupScheme k :=
  (hopfSpec (CommRingCat.of k)).obj (op A)

section FieldExtension

variable (K : Type u) [Field K] [Algebra k K]

/-- Coordinate Hopf algebra after extension of the base field. -/
abbrev extendHopf (A : HopfAlgebraCategory k) : HopfAlgebraCategory K :=
  CommHopfAlgCat.of K (K ⊗[k] A)

/-- The kernel of the counit in Hopf coordinates for the identity tangent. -/
abbrev IdentityTangent.augmentationIdeal (A : HopfAlgebraCategory k) :=
  RingHom.ker (counitAlgHom k A).toRingHom

abbrev includeCoordinates (A : HopfAlgebraCategory k) : A →ₐ[k] K ⊗[k] A :=
  Algebra.TensorProduct.includeRight

theorem includeCoordinates_mem_augmentation (A : HopfAlgebraCategory k)
    (a : IdentityTangent.augmentationIdeal A) :
    includeCoordinates K A a.val ∈ IdentityTangent.augmentationIdeal (extendHopf K A) := by
  have h := congrArg (fun f : A →ₐ[k] K => f a.val)
    (Bialgebra.counitAlgHom_comp_includeRight (R := k) (A := K) (B := A))
  change counitAlgHom K (K ⊗[k] A) (includeCoordinates K A a.val) =
    algebraMap k K (counitAlgHom k A a.val) at h
  exact RingHom.mem_ker.mpr (h.trans (by rw [show counitAlgHom k A a.val = 0 from
    RingHom.mem_ker.mp a.property, map_zero]))

/-- Restrict a point of the extended coordinate algebra along the inclusion of coordinates. -/
def restrictCoordinatePoint {A : HopfAlgebraCategory k} {R : TestAlgebra K}
    (f : extendHopf K A →ₐ[K] R) : A →ₐ[k] (restrictTestAlgebra k K).obj R where
  toRingHom := f.toRingHom.comp (includeCoordinates K A).toRingHom
  commutes' t := by
    change f (includeCoordinates K A (algebraMap k A t)) = algebraMap K R (algebraMap k K t)
    rw [(includeCoordinates K A).commutes]
    rw [IsScalarTower.algebraMap_apply k K (K ⊗[k] A), f.commutes]

abbrev restrictCoordinateRingPoint {A : HopfAlgebraCategory k} {R : TestAlgebra K}
    (f : extendHopf K A →ₐ[K] R) : A →+* R :=
  (restrictCoordinatePoint K f).toRingHom

/-- Extend both coordinates of a dual number along the field homomorphism. -/
def dualNumberCoefficients : DualNumber k →+* DualNumber K where
  toFun z := (algebraMap k K z.fst, algebraMap k K z.snd)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' x y := by
    apply TrivSqZeroExt.ext
    · exact map_add (algebraMap k K) x.fst y.fst
    · exact map_add (algebraMap k K) x.snd y.snd
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul (algebraMap k K) x.fst y.fst
    · change algebraMap k K (x.fst * y.snd + x.snd * y.fst) =
        algebraMap k K x.fst * algebraMap k K y.snd + algebraMap k K x.snd * algebraMap k K y.fst
      simp only [map_add, map_mul]

def extendDualNumber : CommAlgCat.of k (DualNumber k) ⟶
    (restrictTestAlgebra k K).obj (CommAlgCat.of K (DualNumber K)) := by
  let R := (restrictTestAlgebra k K).obj (CommAlgCat.of K (DualNumber K))
  letI : Algebra k R := R.algebra
  let f : DualNumber k →ₐ[k] R :=
    { dualNumberCoefficients K with
      commutes' := fun t => by
        apply TrivSqZeroExt.ext
        · rfl
        · exact map_zero (algebraMap k K) }
  exact ConcreteCategory.ofHom (C := CommAlgCat k) (X := CommAlgCat.of k (DualNumber k)) (Y := R) f

end FieldExtension

namespace Specs

def LieType := ∀ (k : Type u) [Field k], GroupScheme k → Type u

abbrev Lie : LieType.{u} := fun _ _ G => PointKernel G

def DualNumberScaling : Prop :=
  ∀ (k : Type u) [Field k] (s : k),
    dualNumberScale s (DualNumber.eps : DualNumber k) = s • DualNumber.eps

def CounitDerivationLifts : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k),
    let x := counitAlgHom k A
    letI := x.toRingHom.toAlgebra
    ∃ e : Derivation k A k ≃ PointLifts k A k x,
      (∀ (D : Derivation k A k) (a : A), (e D).val a = (x a, D a)) ∧
      (e 0).val = (TrivSqZeroExt.inlAlgHom k k k).comp x

/-- Equivalence with derivations, using the canonical restriction to the augmentation ideal. -/
def PointTangentDerivations : Prop :=
  ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A] (x : A →ₐ[k] k),
    letI := x.toRingHom.toAlgebra
    ∃ e : PointTangent x ≃ₗ[k] Derivation k A k,
      ∀ (L : PointTangent x) (b : RingHom.ker x.toRingHom), e L b.val = L (Ideal.toCotangent _ b)

def PointTangentLifts : Prop :=
  ∀ (k A : Type u) [Field k] [CommRing A] [Algebra k A] (x : A →ₐ[k] k),
    ∃ e : PointTangent x ≃ PointLifts k A k x,
      (∀ (L : PointTangent x) (b : RingHom.ker x.toRingHom),
        ((e L).val b).snd = L (Ideal.toCotangent _ b)) ∧
      (e 0).val = (TrivSqZeroExt.inlAlgHom k k k).comp x

def HopfTangentComparison : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k),
    let x := counitAlgHom k A
    ∃ e : PointTangent x ≃+ DualKernel (convolutionPoints A),
      (∀ (L : PointTangent x) (b : RingHom.ker x.toRingHom),
        ((hopfKernelLifts A (e L)).val b).snd = L (Ideal.toCotangent _ b)) ∧
      ∀ (s : k) (L : PointTangent x), e (s • L) = scaleDualKernel _ s (e L)

/-- The identification uses the spectrum of the actual counit lift. -/
def MatchesHopfPresentation {A : HopfAlgebraCategory k} {G : GroupScheme k}
    (i : hopfSpectrum A ≅ G) : Prop :=
  let x := counitAlgHom k A
  ∃ e : PointTangent x ≃+ Lie k G,
    (∀ L : PointTangent x, ∃ f : PointLifts k A k x,
      (e L).toMul.val.left = Spec.map (CommRingCat.ofHom f.val.toRingHom) ≫
          i.hom.hom.hom.left ∧
      ∀ b : RingHom.ker x.toRingHom, (f.val b).snd = L (Ideal.toCotangent _ b)) ∧
    ∀ (s : k) (L : PointTangent x), e (s • L) = scalePointKernel G s (e L)

def LiePresentation : Prop :=
  ∀ (k : Type u) [Field k] (A : HopfAlgebraCategory k)
    (G : GroupScheme k) (i : hopfSpectrum A ≅ G), MatchesHopfPresentation i

def LieAffineComparison : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineGroupCategory k),
    ∃ h : (affineHopfSpec k).IsEquivalence,
      letI := h
      MatchesHopfPresentation
        ((affineGroupInclusion k).mapIso ((affineHopfSpec k).asEquivalence.counitIso.app G))

def LieFunctoriality : Prop :=
  ∀ (k : Type u) [Field k],
    (∀ {G H : GroupScheme k} (f : G ⟶ H) (s : k) (p : Lie k G),
      mapPointKernel f (scalePointKernel G s p) = scalePointKernel H s (mapPointKernel f p)) ∧
    (∀ (G : GroupScheme k) (p : Lie k G), mapPointKernel (𝟙 G) p = p) ∧
    (∀ (G H J : GroupScheme k) (f : G ⟶ H) (g : H ⟶ J) (p : Lie k G),
      mapPointKernel (f ≫ g) p = mapPointKernel g (mapPointKernel f p))

def HopfLieBaseChange : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) [Algebra.FiniteType k A],
    ∃ e : K ⊗[k] PointTangent (counitAlgHom k A) ≃ₗ[K]
        PointTangent (counitAlgHom K (extendHopf K A)),
      ∀ (t : K) (L : PointTangent (counitAlgHom k A)) (a : IdentityTangent.augmentationIdeal A),
        e (t ⊗ₜ[k] L) ((IdentityTangent.augmentationIdeal (extendHopf K A)).toCotangent
          ⟨includeCoordinates K A a.val, includeCoordinates_mem_augmentation K A a⟩) =
          t * algebraMap k K (L ((IdentityTangent.augmentationIdeal A).toCotangent a))

/-- The spectrum of the extended Hopf algebra represents the actual pullback group. -/
def HopfSpectrumBaseChange : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] (A : HopfAlgebraCategory k),
    ∃ i : hopfSpectrum (extendHopf K A) ≅ (groupBaseChange k K).obj (hopfSpectrum A),
      ∀ (R : TestAlgebra K) (f : extendHopf K A →ₐ[K] R),
        let p := (Spec.mapMulEquiv (R := K) (S := extendHopf K A) (T := R)) (toConv f)
        (baseChangePoint k K (hopfSpectrum A).X R (p ≫ i.hom.hom.hom)).left =
          Spec.map (CommRingCat.ofHom (restrictCoordinateRingPoint K f))

/-- The vector space structure uses the group-kernel operations and dual-number scaling. -/
structure LieVectorStructure (G : GroupScheme k) where
  addGroup : AddCommGroup (Lie k G)
  group_law : addGroup.toAddGroup = (inferInstance : AddGroup (PointKernel G))
  module : @Module k (Lie k G) _ addGroup.toAddCommMonoid
  scalar_law : module.toDistribMulAction.toMulAction.toSMul.smul = scalePointKernel G

/-- The scalar extension of the actual group kernel is canonical on pure generators. -/
def LieBaseChange : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] (G : AffineAlgebraicGroup k),
    let G' := (groupBaseChange k K).obj G.val
    ∃ (m : LieVectorStructure G.val) (n : LieVectorStructure G'),
      letI := m.addGroup
      letI := m.module
      letI := n.addGroup
      letI := n.module
      ∃ e : K ⊗[k] Lie k G.val ≃ₗ[K] Lie K G',
        ∀ p : Lie k G.val,
          baseChangePoint k K G.val.X (CommAlgCat.of K (DualNumber K))
            (e (1 ⊗ₜ[k] p)).toMul.val =
          mapPoints (extendDualNumber K) p.toMul.val

end Specs
end
end LinearAlgebraicGroups
