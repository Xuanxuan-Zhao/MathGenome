import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SimplicialRelativeParametrizations
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.OrientedSimplicialAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory CategoryTheory.Preadditive
open scoped Simplicial TensorProduct
universe u v w

open private P202Specs.RelativeParametrizations.differential P202Specs.RelativeParametrizations.faceMap
  P202Specs.RelativeParametrizations.differential_squared
  from MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SimplicialRelativeParametrizations

namespace P202.RelativeParametrizations
open P202.Cellular P202Specs.RelativeParametrizations
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

def deltaChainComplex (D : DeltaComplex.{w}) :
    ChainComplex (ModuleCat.{max v w} R) ℕ := deltaComplex R A D

theorem deltaBoundary_zero (D : DeltaComplex.{w}) (n : ℕ) :
    (deltaComplex R A D).d 0 n = 0 := by
  exact (deltaComplex R A D).shape 0 n (by simp [ComplexShape.down_Rel])

theorem deltaBoundary_eq (D : DeltaComplex.{w}) (n : ℕ) :
    ((deltaComplex R A D).d (n+1) n).hom = deltaBoundary R A D n := by
  simp [deltaComplex, deltaBoundary, P202Specs.RelativeParametrizations.differential, P202Specs.RelativeParametrizations.faceMap]

theorem deltaBoundary_single (D : DeltaComplex.{w}) (n : ℕ)
    (s : D.Simplex (n+1)) (a : A) :
    deltaBoundary R A D n (Finsupp.single s a) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.single (deltaFace D i s) a := by
  classical
  simp [deltaBoundary, LinearMap.sum_apply, LinearMap.smul_apply]

theorem deltaBoundary_squared (D : DeltaComplex.{w}) (n : ℕ) :
    (deltaBoundary R A D n).comp (deltaBoundary R A D (n+1)) = 0 := by
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero,
    P202Specs.RelativeParametrizations.differential, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    P202Specs.RelativeParametrizations.faceMap, ModuleCat.hom_ofHom, deltaBoundary]
    using congrArg ModuleCat.Hom.hom
      (P202Specs.RelativeParametrizations.differential_squared R A D n)

theorem deltaCoefficientEquiv_single (D : DeltaComplex.{w}) (n : ℕ)
    (s : D.Simplex n) (r : R) (a : A) :
    deltaCoefficientEquiv R A D n (Finsupp.single s r ⊗ₜ[R] a) =
      Finsupp.single s (r • a) := by
  classical
  ext t
  simp [deltaCoefficientEquiv, Finsupp.single_apply, ite_smul]

theorem deltaCoefficientEquiv_boundary (D : DeltaComplex.{w}) (n : ℕ)
    (x : DeltaChains R D (n+1) ⊗[R] A) :
    deltaBoundary R A D n (deltaCoefficientEquiv R A D (n+1) x) =
      deltaCoefficientEquiv R A D n ((deltaBoundary R R D n).rTensor A x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c a =>
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [TensorProduct.add_tmul, map_add, hc, hd]
    | single s r =>
      rw [LinearMap.rTensor_tmul, deltaBoundary_single, deltaCoefficientEquiv_single,
        deltaBoundary_single, TensorProduct.sum_tmul, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rcases neg_one_pow_eq_or ℤ i.val with hi | hi <;>
        simp [hi, TensorProduct.neg_tmul, deltaCoefficientEquiv_single]

theorem deltaSingularSimplex_face (D : DeltaComplex.{w}) (n : ℕ)
    (i : Fin (n+2)) (s : D.Simplex (n+1)) :
    deltaSingularSimplex D n (deltaFace D i s) =
      P202Specs.SingularChains.face i (deltaSingularSimplex D (n+1) s) := by
  apply (P202Specs.SingularChains.simplexEquiv _ n).injective
  ext x
  change D.simplexChart n (deltaFace D i s) x =
    D.simplexChart (n+1) s (orderedAffineFace i.succAboveOrderEmb x)
  exact Quotient.sound (Relation.EqvGen.rel _ _
    (DeltaComplex.FaceRelation.face i.succAboveOrderEmb s x))

theorem deltaParametrizationLinear_single (D : DeltaComplex.{w}) (n : ℕ)
    (s : D.Simplex n) (a : A) :
    deltaParametrizationLinear R A D n (Finsupp.single s a) =
      Finsupp.single (deltaSingularSimplex D n s) a := by
  simp [deltaParametrizationLinear]

theorem deltaAffineChainMap (D : DeltaComplex.{w}) :
    ∃ f : deltaComplex R A D ⟶
      P202Specs.SingularChains.complex R A (TopCat.of D.Realization),
      ∀ n, (f.f n).hom = deltaParametrizationLinear R A D n := by
  refine ⟨ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (deltaParametrizationLinear R A D n)) ?_, fun _ => rfl⟩
  intro n
  apply ModuleCat.hom_ext
  change (P202Specs.SingularChains.boundary R A _ n).comp
    (deltaParametrizationLinear R A D (n+1)) =
      (deltaParametrizationLinear R A D n).comp
        (((deltaComplex R A D).d (n+1) n).hom)
  rw [deltaBoundary_eq R A D]
  apply Finsupp.lhom_ext
  intro s a
  change P202Specs.SingularChains.boundary R A _ n
    (deltaParametrizationLinear R A D (n+1) (Finsupp.single s a)) =
    deltaParametrizationLinear R A D n (deltaBoundary R A D n (Finsupp.single s a))
  rw [deltaParametrizationLinear_single R A, P202.SingularChains.boundary_single R A,
    deltaBoundary_single R A]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [deltaParametrizationLinear_single R A, deltaSingularSimplex_face]

theorem deltaPushforward_single {D E : DeltaComplex.{w}} (f : DeltaMap D E)
    (n : ℕ) (s : D.Simplex n) (a : A) :
    deltaPushforward R A f n (Finsupp.single s a) = Finsupp.single (f.simplex n s) a := by
  simp [deltaPushforward]

theorem deltaPushforward_chainMap {D E : DeltaComplex.{w}} (f : DeltaMap D E) :
    ∃ F : deltaComplex R A D ⟶ deltaComplex R A E,
      ∀ n, (F.f n).hom = deltaPushforward R A f n := by
  refine ⟨ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (deltaPushforward R A f n)) ?_, fun _ => rfl⟩
  intro n
  apply ModuleCat.hom_ext
  change (((deltaComplex R A E).d (n+1) n).hom).comp (deltaPushforward R A f (n+1)) =
    (deltaPushforward R A f n).comp (((deltaComplex R A D).d (n+1) n).hom)
  rw [deltaBoundary_eq R A E, deltaBoundary_eq R A D]
  apply Finsupp.lhom_ext
  intro s a
  change deltaBoundary R A E n (deltaPushforward R A f (n+1) (Finsupp.single s a)) =
    deltaPushforward R A f n (deltaBoundary R A D n (Finsupp.single s a))
  rw [deltaPushforward_single, deltaBoundary_single R A, deltaBoundary_single R A]
  simp only [map_sum, map_zsmul, deltaPushforward_single R A, deltaFace, f.face]

namespace Simplicial
open P202Specs.OrientedSimplicialAlgebra
open P202Specs.RelativeParametrizations.Simplicial
attribute [local instance] vertexOrder
variable {V : Type w} (K : AbstractSimplicialComplex V)

theorem parametrization_value (n : ℕ) (s : Simplex K n) (x : StandardSimplex n) :
    (parametrization K n s x).1 = x.map s.1 := by
  classical
  exact Convexity.StdSimplex.map_map _ _ _

theorem singularSimplex_face (n : ℕ) (i : Fin (n+2)) (s : Simplex K (n+1)) :
    singularSimplex K n (face i s) =
      P202Specs.SingularChains.face i (singularSimplex K (n+1) s) := by
  apply (P202Specs.SingularChains.simplexEquiv _ n).injective
  rw [P202.SingularChains.simplexEquiv_face]
  change parametrization K n (face i s) =
    (parametrization K (n+1) s).comp (P202Specs.SingularChains.faceInclusion i)
  ext x
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, parametrization_value, parametrization_value]
  apply Convexity.StdSimplex.ext
  change x.weights.mapDomain (face i s).1 =
    ((P202Specs.SingularChains.faceInclusion i x).weights).mapDomain s.1
  rw [P202.SingularChains.faceInclusion_weights, ← Finsupp.mapDomain_comp]
  rfl

theorem affineLinear_single (n : ℕ) (s : Simplex K n) (a : A) :
    affineLinear K R A n (Finsupp.single s a) =
      Finsupp.single (singularSimplex K n s) a := by
  simp [affineLinear]

theorem affineChainMap :
    ∃ f : complex R A (K := K) ⟶
      P202Specs.SingularChains.complex R A (TopCat.of K.Realization),
      ∀ n, (f.f n).hom = affineLinear K R A n := by
  refine ⟨ChainComplex.ofHom
    (fun n => ModuleCat.ofHom (affineLinear K R A n)) ?_, fun _ => rfl⟩
  intro n
  apply ModuleCat.hom_ext
  change (P202Specs.SingularChains.boundary R A _ n).comp
    (affineLinear K R A (n+1)) =
      (affineLinear K R A n).comp (((complex R A (K := K)).d (n+1) n).hom)
  rw [P202.OrientedSimplicialAlgebra.boundary_eq]
  apply Finsupp.lhom_ext
  intro s a
  change P202Specs.SingularChains.boundary R A _ n
    (affineLinear K R A (n+1) (Finsupp.single s a)) =
      affineLinear K R A n (boundary R A n (Finsupp.single s a))
  rw [affineLinear_single R A K, P202.SingularChains.boundary_single R A,
    P202.OrientedSimplicialAlgebra.boundary_single R A]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [affineLinear_single R A K, singularSimplex_face]

end Simplicial

namespace Quotient
variable {R} {C E : ChainComplex (ModuleCat.{w} R) ℕ}

theorem inclusion_injective (S : ChainSelection R C) (n : ℕ) :
    Function.Injective ((S.inclusion.f n).hom) := Subtype.val_injective

theorem projection_surjective (S : ChainSelection R C) (n : ℕ) :
    Function.Surjective ((S.projection.f n).hom) := (S.module n).mkQ_surjective

theorem projection_kernel (S : ChainSelection R C) (n : ℕ) :
    LinearMap.ker ((S.projection.f n).hom) = S.module n := Submodule.ker_mkQ _

theorem boundary_mk (S : ChainSelection R C) (n : ℕ) (x : C.X (n+1)) :
    ((S.quotient.d (n+1) n).hom) ((S.module (n+1)).mkQ x) =
      (S.module n).mkQ ((C.d (n+1) n).hom x) := by
  simp [ChainSelection.quotient, ChainSelection.quotientBoundary]

theorem boundary_zero (S : ChainSelection R C) (n : ℕ) : S.quotient.d 0 n = 0 :=
  S.quotient.shape 0 n (by simp [ComplexShape.down_Rel])

theorem boundary_squared (S : ChainSelection R C) (n : ℕ) :
    ((S.quotient.d (n+1) n).hom).comp ((S.quotient.d (n+2) (n+1)).hom) = 0 :=
  congrArg ModuleCat.Hom.hom (S.quotient.d_comp_d (n+2) (n+1) n)

theorem map_mk (S : ChainSelection R C) (T : ChainSelection R E)
    (f : C ⟶ E) (hf : ∀ n x, x ∈ S.module n → (f.f n).hom x ∈ T.module n)
    (n : ℕ) (x : C.X n) :
    (((S.quotientMap T f hf).f n).hom) ((S.module n).mkQ x) =
      (T.module n).mkQ ((f.f n).hom x) := rfl

end Quotient

/-- The singular submodule used by the quotient is exactly the image of the
shared singular chain functor applied to the actual subspace inclusion. -/
theorem singularSelection_range (X : TopCat.{w}) (Y : Set X) (n : ℕ) :
    LinearMap.range ((P202Specs.SingularChains.chainMap R A
      (subspaceInclusion X Y)).f n).hom = (singularSelection R A X Y).module n := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply map_supported (M := P202Specs.SingularChains.Chains A X n)
      R A Set.univ _
      ((P202Specs.SingularChains.chainMap R A (subspaceInclusion X Y)).f n).hom ?_ x
      ((Finsupp.mem_supported R _).mpr (Set.subset_univ _))
    intro s _ a
    erw [P202.SingularChains.chainMap_single R A]
    apply Finsupp.single_mem_supported
    intro t
    rw [P202.SingularChains.simplexEquiv_postcomp]
    exact (P202Specs.SingularChains.simplexEquiv (TopCat.of Y) n s t).2
  · intro x hx
    change (LinearMap.id : P202Specs.SingularChains.Chains A X n →ₗ[R]
      P202Specs.SingularChains.Chains A X n) x ∈ _
    apply map_supported (M := P202Specs.SingularChains.Chains A X n)
      R A _ _ LinearMap.id ?_ x hx
    intro s hs a
    let g : C(StandardSimplex n, Y) :=
      ⟨fun t => ⟨P202Specs.SingularChains.simplexEquiv X n s t, hs t⟩,
        (P202Specs.SingularChains.simplexEquiv X n s).continuous.subtype_mk _⟩
    let s' := (P202Specs.SingularChains.simplexEquiv (TopCat.of Y) n).symm g
    refine ⟨Finsupp.single s' a, ?_⟩
    erw [P202.SingularChains.chainMap_single R A]
    congr 1

theorem deltaEmpty_module (D : DeltaComplex.{w}) (n : ℕ) :
    (deltaSelection R A D (DeltaSubcomplex.empty D)).module n = ⊥ :=
  Finsupp.supported_empty

/-- The selected Δ chains are exactly finite chains on the selected labels. -/
def deltaSelectedEquiv (D : DeltaComplex.{w}) (S : DeltaSubcomplex D) (n : ℕ) :
    (deltaSelection R A D S).module n ≃ₗ[R] ((S.selected n) →₀ A) :=
  Finsupp.supportedEquivFinsupp (R := R) _

def deltaPairComplex (D : DeltaComplex.{w}) (S : DeltaSubcomplex D) :=
  deltaRelativeComplex R A D S

theorem deltaRelativeBoundary_single (D : DeltaComplex.{w}) (S : DeltaSubcomplex D)
    (n : ℕ) (s : D.Simplex (n+1)) (a : A) :
    ((deltaRelativeComplex R A D S).d (n+1) n).hom
      (((deltaSelection R A D S).module (n+1)).mkQ (Finsupp.single s a)) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        (((deltaSelection R A D S).module n).mkQ (Finsupp.single (deltaFace D i s) a)) := by
  erw [Quotient.boundary_mk, deltaBoundary_eq R A D, deltaBoundary_single R A]
  simp only [map_sum, map_zsmul]

theorem deltaAffine_preserves (D : DeltaComplex.{w}) (S : DeltaSubcomplex D)
    (n : ℕ) (x : DeltaChains A D n) (hx : x ∈ (deltaSelection R A D S).module n) :
    deltaParametrizationLinear R A D n x ∈
      (singularSelection R A (TopCat.of D.Realization) S.carrier).module n := by
  apply map_supported R A _ _ (deltaParametrizationLinear R A D n) ?_ x hx
  intro s hs a
  rw [deltaParametrizationLinear_single R A]
  apply Finsupp.single_mem_supported
  intro t
  exact ⟨n, s, hs, t, by simp [deltaSingularSimplex, deltaParametrization]⟩

theorem deltaRelativeAffineChainMap (D : DeltaComplex.{w}) (S : DeltaSubcomplex D) :
    ∃ f : deltaRelativeComplex R A D S ⟶
      singularRelativeComplex R A (TopCat.of D.Realization) S.carrier,
      ∀ n x, (f.f n).hom (((deltaSelection R A D S).module n).mkQ x) =
        ((singularSelection R A (TopCat.of D.Realization) S.carrier).module n).mkQ
          (deltaParametrizationLinear R A D n x) := by
  obtain ⟨f, hf⟩ := deltaAffineChainMap R A D
  have hp : ∀ n x, x ∈ (deltaSelection R A D S).module n →
      (f.f n).hom x ∈
        (singularSelection R A (TopCat.of D.Realization) S.carrier).module n := by
    intro n x hx
    rw [hf]
    exact deltaAffine_preserves R A D S n x hx
  exact ⟨(deltaSelection R A D S).quotientMap
    (singularSelection R A (TopCat.of D.Realization) S.carrier) f hp,
    by intro n x; erw [Quotient.map_mk, hf]; rfl⟩

theorem deltaInclusion (D : DeltaComplex.{w}) (S : DeltaSubcomplex D) :
    ∃ f : deltaComplex R A S.asComplex ⟶ deltaComplex R A D,
      (∀ n, (f.f n).hom = deltaPushforward R A S.inclusion n) ∧
      (∀ n, Function.Injective (f.f n).hom) ∧
      (∀ n, LinearMap.range (f.f n).hom = (deltaSelection R A D S).module n) := by
  obtain ⟨f, hf⟩ := deltaPushforward_chainMap R A S.inclusion
  refine ⟨f, hf, ?_, ?_⟩
  · intro n
    rw [hf]
    exact Finsupp.mapDomain_injective Subtype.val_injective
  · intro n
    rw [hf]
    change LinearMap.range (Finsupp.lmapDomain A R (Subtype.val : S.selected n → _)) = _
    rw [LinearMap.range_eq_map, ← Finsupp.supported_univ,
      Finsupp.lmapDomain_supported, Set.image_univ, Subtype.range_val]
    rfl

theorem deltaPushforward_preserves {D E : DeltaComplex.{w}} (S : DeltaSubcomplex D)
    (T : DeltaSubcomplex E) (f : DeltaMap D E)
    (hpair : ∀ n s, s ∈ S.selected n → f.simplex n s ∈ T.selected n)
    (n : ℕ) (x : DeltaChains A D n) (hx : x ∈ (deltaSelection R A D S).module n) :
    deltaPushforward R A f n x ∈ (deltaSelection R A E T).module n := by
  apply map_supported R A _ _ (deltaPushforward R A f n) ?_ x hx
  intro s hs a
  rw [deltaPushforward_single]
  exact Finsupp.single_mem_supported R a (hpair n s hs)

theorem deltaRelativePushforward {D E : DeltaComplex.{w}} (S : DeltaSubcomplex D)
    (T : DeltaSubcomplex E) (f : DeltaMap D E)
    (hpair : ∀ n s, s ∈ S.selected n → f.simplex n s ∈ T.selected n) :
    ∃ F : deltaRelativeComplex R A D S ⟶ deltaRelativeComplex R A E T,
      ∀ n x, (F.f n).hom (((deltaSelection R A D S).module n).mkQ x) =
        ((deltaSelection R A E T).module n).mkQ (deltaPushforward R A f n x) := by
  obtain ⟨F, hF⟩ := deltaPushforward_chainMap R A f
  have hp : ∀ n x, x ∈ (deltaSelection R A D S).module n →
      (F.f n).hom x ∈ (deltaSelection R A E T).module n := by
    intro n x hx
    rw [hF]
    exact deltaPushforward_preserves R A S T f hpair n x hx
  exact ⟨(deltaSelection R A D S).quotientMap (deltaSelection R A E T) F hp,
    by intro n x; erw [Quotient.map_mk, hF]; rfl⟩

namespace Simplicial
open P202Specs.OrientedSimplicialAlgebra
open P202Specs.RelativeParametrizations.Simplicial
attribute [local instance] vertexOrder
variable {V : Type w} (K : AbstractSimplicialComplex V)

def pairComplex (S : Subcomplex K) := relativeComplex R A K S

theorem empty_module (n : ℕ) :
    (selection R A K (Subcomplex.empty K)).module n = ⊥ :=
  Finsupp.supported_empty

theorem relativeBoundary_single (S : Subcomplex K) (n : ℕ)
    (s : Simplex K (n+1)) (a : A) :
    ((relativeComplex R A K S).d (n+1) n).hom
      (((selection R A K S).module (n+1)).mkQ (Finsupp.single s a)) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val •
        (((selection R A K S).module n).mkQ (Finsupp.single (face i s) a)) := by
  erw [Quotient.boundary_mk, P202.OrientedSimplicialAlgebra.boundary_eq R A,
    P202.OrientedSimplicialAlgebra.boundary_single R A]
  simp only [map_sum, map_zsmul]

theorem parametrization_lands (S : Subcomplex K) (n : ℕ) (s : Simplex K n)
    (hs : s ∈ S.selected K n) (t : StandardSimplex n) :
    parametrization K n s t ∈ S.carrier K := by
  change (parametrization K n s t).1.weights.support ∈ S.complex.simplices
  rw [parametrization_value]
  apply S.complex.face hs _ (Convexity.StdSimplex.support_weights_nonempty _)
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem affine_preserves (S : Subcomplex K) (n : ℕ) (x : Chains K A n)
    (hx : x ∈ (selection R A K S).module n) :
    affineLinear K R A n x ∈
      (singularSelection R A (TopCat.of K.Realization) (S.carrier K)).module n := by
  apply map_supported R A _ _ (affineLinear K R A n) ?_ x hx
  intro s hs a
  rw [affineLinear_single R A K]
  apply Finsupp.single_mem_supported
  intro t
  simpa [singularSimplex] using parametrization_lands K S n s hs t

theorem relativeAffineChainMap (S : Subcomplex K) :
    ∃ f : relativeComplex R A K S ⟶
      singularRelativeComplex R A (TopCat.of K.Realization) (S.carrier K),
      ∀ n x, (f.f n).hom (((selection R A K S).module n).mkQ x) =
        ((singularSelection R A (TopCat.of K.Realization) (S.carrier K)).module n).mkQ
          (affineLinear K R A n x) := by
  obtain ⟨f, hf⟩ := affineChainMap R A K
  have hp : ∀ n x, x ∈ (selection R A K S).module n →
      (f.f n).hom x ∈
        (singularSelection R A (TopCat.of K.Realization) (S.carrier K)).module n := by
    intro n x hx
    rw [hf]
    exact affine_preserves R A K S n x hx
  exact ⟨(selection R A K S).quotientMap
    (singularSelection R A (TopCat.of K.Realization) (S.carrier K)) f hp,
    by intro n x; erw [Quotient.map_mk, hf]; rfl⟩

theorem inclusion_range (S : Subcomplex K) (n : ℕ) :
    LinearMap.range (pushforward R A (SimplicialMap.inclusion S.subset) n) =
      (selection R A K S).module n := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    apply map_supported R A Set.univ _
      (pushforward R A (SimplicialMap.inclusion S.subset) n) ?_ x (by
        exact (Finsupp.mem_supported R _).mpr (Set.subset_univ _))
    intro s _ a
    rw [P202.OrientedSimplicialAlgebra.pushforward_inclusion_single R A]
    exact Finsupp.single_mem_supported R a s.2
  · intro x hx
    change (LinearMap.id : Chains K A n →ₗ[R] Chains K A n) x ∈
      LinearMap.range (pushforward R A (SimplicialMap.inclusion S.subset) n)
    apply map_supported R A _ _ LinearMap.id ?_ x hx
    intro s hs a
    refine ⟨Finsupp.single (⟨s.1, hs⟩ : Simplex S.complex n) a, ?_⟩
    rw [P202.OrientedSimplicialAlgebra.pushforward_inclusion_single R A]
    rfl

theorem inclusion_chainMap (S : Subcomplex K) :
    ∃ f : complex R A (K := S.complex) ⟶ complex R A (K := K),
      (∀ n, (f.f n).hom = pushforward R A (SimplicialMap.inclusion S.subset) n) ∧
      (∀ n, Function.Injective (f.f n).hom) ∧
      (∀ n, LinearMap.range (f.f n).hom = (selection R A K S).module n) := by
  obtain ⟨f, hf⟩ := P202.OrientedSimplicialAlgebra.pushforward_chainMap R A
    (SimplicialMap.inclusion S.subset)
  refine ⟨f, hf, ?_, ?_⟩
  · intro n
    rw [hf]
    exact P202.OrientedSimplicialAlgebra.pushforward_inclusion_injective R A _ n
  · intro n
    rw [hf]
    exact inclusion_range R A K S n

private theorem sorted_vertices {n : ℕ} {L : AbstractSimplicialComplex V}
    (s : VertexTuple L n) (hs : Function.Injective s.1) :
    Finset.univ.image (sorted s hs).1 = Finset.univ.image s.1 := by
  classical
  change Finset.univ.image (s.1 ∘ Tuple.sort s.1) = _
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  exact ⟨fun ⟨i, hi⟩ => ⟨Tuple.sort s.1 i, hi⟩,
    fun ⟨i, hi⟩ => ⟨(Tuple.sort s.1).symm i, by simpa using hi⟩⟩

theorem pushforward_preserves {W : Type w} (L : AbstractSimplicialComplex W)
    (S : Subcomplex K) (T : Subcomplex L) (f : SimplicialMap (K := K) L)
    (hpair : ∀ s ∈ S.complex.simplices, s.image f.vertices ∈ T.complex.simplices)
    (n : ℕ) (x : Chains K A n) (hx : x ∈ (selection R A K S).module n) :
    pushforward R A f n x ∈ (selection R A L T).module n := by
  apply map_supported R A _ _ (pushforward R A f n) ?_ x hx
  intro s hs a
  rw [P202.OrientedSimplicialAlgebra.pushforward_single R A]
  classical
  dsimp [oriented]
  split
  · apply zsmul_mem
    apply Finsupp.single_mem_supported
    change Finset.univ.image (sorted _ _).1 ∈ T.complex.simplices
    rw [sorted_vertices]
    simpa only [SimplicialMap.imageTuple, ← Finset.image_image] using
      hpair (Finset.univ.image s.1) hs
  · exact Submodule.zero_mem _

theorem relativePushforward {W : Type w} (L : AbstractSimplicialComplex W)
    (S : Subcomplex K) (T : Subcomplex L) (f : SimplicialMap (K := K) L)
    (hpair : ∀ s ∈ S.complex.simplices, s.image f.vertices ∈ T.complex.simplices) :
    ∃ F : relativeComplex R A K S ⟶ relativeComplex R A L T,
      ∀ n x, (F.f n).hom (((selection R A K S).module n).mkQ x) =
        ((selection R A L T).module n).mkQ (pushforward R A f n x) := by
  obtain ⟨F, hF⟩ := P202.OrientedSimplicialAlgebra.pushforward_chainMap R A f
  have hp : ∀ n x, x ∈ (selection R A K S).module n →
      (F.f n).hom x ∈ (selection R A L T).module n := by
    intro n x hx
    rw [hF]
    exact pushforward_preserves R A K L S T f hpair n x hx
  exact ⟨(selection R A K S).quotientMap (selection R A L T) F hp,
    by intro n x; erw [Quotient.map_mk, hF]; rfl⟩

end Simplicial
end P202.RelativeParametrizations
