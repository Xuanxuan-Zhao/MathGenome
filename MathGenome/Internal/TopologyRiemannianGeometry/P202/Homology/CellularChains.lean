import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.CellularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.RelativeSingularChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellStructures
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularDegreeZero
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.LinearAlgebra.Finsupp.Pi

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SpheresDisks
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.Excision
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SubcomplexNeighborhoods
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.GoodPairQuotient
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! Cellular chain construction and functoriality for the specified CW structure.
The relative groups throughout are the shared singular homology, not a free
module substituted for it. The characteristic disk classes give finite-support cell coordinates in all
dimensions, and all other nonnegative skeletal relative groups vanish. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w

namespace P202.Homology
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.ChainLES P202Specs.CellularChains

theorem cellularSkeletalIndexing : Expected.skeletalIndexing.{w} := by
  intro X _ _ n
  refine ⟨(P202.Topology.skeletonIndexing n).symm, ?_⟩
  ext x
  simp only [skeletonLT, skeleton, Set.mem_iUnion]
  constructor
  · rintro ⟨m, hm, c, hx⟩
    exact ⟨m, by omega, c, hx⟩
  · rintro ⟨m, hm, c, hx⟩
    exact ⟨m, by omega, c, hx⟩

theorem cellularMapCriterion : Expected.mapCriterion.{w} := by
  intro X Y _ _ _ _ f
  constructor
  · intro h n
    rw [P202.Topology.skeletonIndexing (X := X) n,
      P202.Topology.skeletonIndexing (X := Y) n]
    exact h (n+1)
  · intro h n
    cases n with
    | zero =>
      intro x hx
      simp only [skeletonLT, Set.mem_iUnion] at hx
      obtain ⟨m, hm, _⟩ := hx
      omega
    | succ n =>
      rw [← P202.Topology.skeletonIndexing (X := X) n,
        ← P202.Topology.skeletonIndexing (X := Y) n]
      exact h n

/-- The actual ordinary nonnegative cellular chain complex. -/
def cellularChainComplex (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    ChainComplex (ModuleCat.{max v w} R) ℕ := cellularComplex X R M

theorem cellularFormulas :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    skeleton X (-1) = ∅ ∧
    (∀ n, (cellularComplex X R M).X n = relativeHomology R M (skeletalPair X n) (n : ℤ)) ∧
    (∀ j, (cellularComplex X R M).d 0 j = 0) ∧
    (∀ n, ∃ h : DegreewiseShortExact (sequence (ordinaryFunctor R M) (skeletalPair X (n+1))),
      (cellularComplex X R M).d (n+1) n =
        connecting h ((n+1 : ℕ) : ℤ) (n : ℤ) (by simp) ≫
        (homologyFunctor R M (n : ℤ)).map
          (lowerMap X (n+1)) ≫
        homologyMap (projection (ordinaryFunctor R M) (skeletalPair X n)) (n : ℤ)) := by
  intro X _ _ R _ M _ _
  refine ⟨P202.Topology.negativeSkeleton, fun _ => rfl, ?_, ?_⟩
  · intro j
    exact (cellularComplex X R M).shape 0 j (by simp)
  · intro n
    let h := P202.RelativeSingularChains.ordinary_short_exact R M (skeletalPair X (n+1))
    refine ⟨h, ?_⟩
    simp only [cellularComplex, ChainComplex.of_d]
    change differential X R M n = _
    rw [differential, pairConnecting_eq R M _ _ h]

theorem cellularSquareZero :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ),
    differential X R M (n+1) ≫ differential X R M n = 0 := by
  intro X _ _ R _ M _ _ n
  exact differential_comp X R M n

section Maps
variable {X Y Z : Type w} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [CWStructure X] [CWStructure Y] [CWStructure Z]
  (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

lemma lowerHomeomorph_natural (f : CellularMap X Y) (n : ℕ) :
    (lowerMap X n) ≫ f.onSkeleton n =
      (f.onPair n).restrict ≫ lowerMap Y n := rfl

lemma pairConnecting_natural {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ) :
    pairConnecting R M P n ≫ homologyMap ((ordinaryFunctor R M).map f.restrict) (n : ℤ) =
      homologyMap (relativeMap (ordinaryFunctor R M) f) ((n+1 : ℕ) : ℤ) ≫
        pairConnecting R M Q n := by
  rw [pairConnecting_eq R M P n (P202.RelativeSingularChains.ordinary_short_exact R M P),
    pairConnecting_eq R M Q n (P202.RelativeSingularChains.ordinary_short_exact R M Q)]
  exact HomologicalComplex.HomologySequence.δ_naturality (sequenceMap (ordinaryFunctor R M) f)
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (P202.RelativeSingularChains.ordinary_short_exact R M P))
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (P202.RelativeSingularChains.ordinary_short_exact R M Q)) _ _ _

lemma cellularDegreeMap_comm (f : CellularMap X Y) (n : ℕ) :
    cellularDegreeMap R M f (n+1) ≫ differential Y R M n =
      differential X R M n ≫ cellularDegreeMap R M f n := by
  let K := ordinaryFunctor R M
  have hδ := pairConnecting_natural R M (f.onPair (n+1)) n
  have hπ := congrArg (fun a => homologyMap a (n : ℤ))
    (projection_map K (f.onPair n))
  simp only [homologyMap_comp] at hπ
  have hlow := congrArg ((homologyFunctor R M (n : ℤ)).map ·)
    (lowerHomeomorph_natural f (n+1))
  simp only [CategoryTheory.Functor.map_comp] at hlow
  change homologyMap (K.map (lowerMap X (n+1))) (n : ℤ) ≫
      homologyMap (K.map (f.onSkeleton (n+1))) (n : ℤ) =
    homologyMap (K.map (f.onPair (n+1)).restrict) (n : ℤ) ≫
      homologyMap (K.map (lowerMap Y (n+1))) (n : ℤ) at hlow
  change homologyMap (relativeMap K (f.onPair (n+1))) ((n+1 : ℕ) : ℤ) ≫
      (pairConnecting R M (skeletalPair Y (n+1)) n ≫
      (homologyFunctor R M (n : ℤ)).map (lowerMap Y (n+1)) ≫
      homologyMap (projection K (skeletalPair Y n)) (n : ℤ)) =
    (pairConnecting R M (skeletalPair X (n+1)) n ≫
      (homologyFunctor R M (n : ℤ)).map (lowerMap X (n+1)) ≫
      homologyMap (projection K (skeletalPair X n)) (n : ℤ)) ≫
      homologyMap (relativeMap K (f.onPair n)) (n : ℤ)
  simp only [Category.assoc]
  rw [← Category.assoc, ← hδ, Category.assoc]
  congr 1
  change homologyMap (K.map (f.onPair (n+1)).restrict) (n : ℤ) ≫
      homologyMap (K.map (lowerMap Y (n+1))) (n : ℤ) ≫
      homologyMap (projection K (skeletalPair Y n)) (n : ℤ) =
    homologyMap (K.map (lowerMap X (n+1))) (n : ℤ) ≫
      homologyMap (projection K (skeletalPair X n)) (n : ℤ) ≫
      homologyMap (relativeMap K (f.onPair n)) (n : ℤ)
  rw [← Category.assoc, ← hlow, Category.assoc]
  exact congrArg (homologyMap (K.map (lowerMap X (n+1))) (n : ℤ) ≫ ·) hπ.symm

/-- No change of chain groups: each component is the map on the skeletal pair. -/
def cellularChainMap (f : CellularMap X Y) :
    cellularComplex X R M ⟶ cellularComplex Y R M :=
  ChainComplex.ofHom (cellularDegreeMap R M f) (fun n => by
    simpa only [cellularComplex, ChainComplex.of_d] using cellularDegreeMap_comm R M f n)

@[simp] lemma cellularChainMap_f (f : CellularMap X Y) (n : ℕ) :
    (cellularChainMap R M f).f n = cellularDegreeMap R M f n := rfl

@[simp] theorem cellularChainMap_id :
    cellularChainMap R M (CellularMap.id X) = 𝟙 (cellularComplex X R M) := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (relativeHomologyFunctor R M (n : ℤ)).map (𝟙 (skeletalPair X n)) = 𝟙 _
  exact CategoryTheory.Functor.map_id _ _

@[simp] theorem cellularChainMap_comp (f : CellularMap X Y) (g : CellularMap Y Z) :
    cellularChainMap R M (g.comp f) = cellularChainMap R M f ≫ cellularChainMap R M g := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (relativeHomologyFunctor R M (n : ℤ)).map (f.onPair n ≫ g.onPair n) = _
  exact CategoryTheory.Functor.map_comp _ _ _

end Maps

theorem cellularMaps :
  ∀ (X Y : Type w) [TopologicalSpace X] [TopologicalSpace Y] [CWStructure X] [CWStructure Y]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (f : CellularMap X Y),
    ∃ F : cellularComplex X R M ⟶ cellularComplex Y R M,
      ∀ n, F.f n = cellularDegreeMap R M f n := by
  intro X Y _ _ _ _ R _ M _ _ f
  exact ⟨cellularChainMap R M f, fun _ => rfl⟩

section ZeroSkeleton
variable (X : Type w) [TopologicalSpace X] [CWStructure X]

lemma skeletalSpace_zero_isEmpty : IsEmpty (skeletalSpace X 0) := by
  refine ⟨fun x => ?_⟩
  have hx := x.property
  simp only [skeletonLT, Set.mem_iUnion] at hx
  obtain ⟨m, hm, _⟩ := hx
  omega

lemma zeroSkeleton_discrete : DiscreteTopology (skeletalSpace X 1) := by
  letI := skeletalSpace_zero_isEmpty X
  haveI : DiscreteTopology (Disk 0) := inferInstance
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  exact (CWStructure.attachment_quotient (X := X) 0).isCoinducing.isOpen_preimage.mp
    (isOpen_discrete _)

/-- The point of the oriented zero-dimensional characteristic disk. -/
def zeroDiskPoint : OpenDisk 0 := ⟨0, by simp⟩

def vertex (c : Cell X 0) : skeletalSpace X 1 :=
  ⟨interiorMap X 0 c zeroDiskPoint, Set.mem_iUnion.mpr ⟨0,
    Set.mem_iUnion.mpr ⟨by omega, Set.mem_iUnion.mpr ⟨c, ⟨zeroDiskPoint, rfl⟩⟩⟩⟩⟩

lemma vertex_bijective : Function.Bijective (vertex X) := by
  constructor
  · intro c d h
    by_contra hne
    have hcd : (⟨0, c⟩ : Σ n, Cell X n) ≠ ⟨0, d⟩ := by
      intro he
      cases he
      exact hne rfl
    have hd : (vertex X c).val ∈ openCell X 0 d := by
      rw [h]
      exact ⟨zeroDiskPoint, rfl⟩
    exact Set.disjoint_left.mp
      (CWStructure.disjoint_interiors (Set.mem_univ _) (Set.mem_univ _) hcd)
      (show (vertex X c).val ∈ openCell X 0 c from ⟨zeroDiskPoint, rfl⟩) hd
  · intro x
    have hx := x.property
    simp only [skeletonLT, Set.mem_iUnion] at hx
    obtain ⟨m, hm, c, y, hy⟩ := hx
    have hm0 : m = 0 := by omega
    subst m
    refine ⟨c, ?_⟩
    apply Subtype.ext
    have hz : y = zeroDiskPoint := Subsingleton.elim _ _
    simpa only [vertex, hz] using hy

def vertexEquiv : Cell X 0 ≃ skeletalSpace X 1 := Equiv.ofBijective (vertex X) (vertex_bijective X)

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Ordinary relative chains with empty second term are identified by the
actual quotient projection, for arbitrary module coefficients. -/
lemma emptySubspace_projection_isIso (P : Pair.{w}) [IsEmpty P.sub] :
    IsIso (projection (ordinaryFunctor R M) P) := by
  apply cokernel.π_of_zero
  apply HomologicalComplex.Hom.ext
  funext k
  exact (P202.SingularDegreeZero.emptyOrdinaryX R M P.sub k).eq_of_src _ _

lemma zeroSkeleton_projection_isIso :
    IsIso (projection (ordinaryFunctor R M) (skeletalPair X 0)) := by
  letI := skeletalSpace_zero_isEmpty X
  haveI : IsEmpty (skeletalPair X 0).sub :=
    ⟨fun x => isEmptyElim (lowerHomeomorph X 0 x)⟩
  exact emptySubspace_projection_isIso R M _

def zeroCellEquiv : chainGroup X R M 0 ≃ₗ[R] (Cell X 0 →₀ M) := by
  letI := zeroSkeleton_discrete X
  letI := zeroSkeleton_projection_isIso X R M
  exact (asIso (homologyMap (projection (ordinaryFunctor R M) (skeletalPair X 0)) 0)).symm.toLinearEquiv |>.trans
    ((P202.SingularDegreeZero.totallyDisconnectedZero R M (skeletalSpace X 1)).trans
      (Finsupp.mapDomain.linearEquiv M R (vertexEquiv X).symm))

lemma zeroSkeleton_vanishing (j : ℕ) (hj : j ≠ 0) :
    IsZero (relativeHomology R M (skeletalPair X 0) (j : ℤ)) := by
  letI := zeroSkeleton_discrete X
  letI := zeroSkeleton_projection_isIso X R M
  exact (P202.SingularDegreeZero.totallyDisconnectedHomology R M (skeletalSpace X 1)
    (j : ℤ) (by exact_mod_cast hj)).of_iso
      (asIso (homologyMap (projection (ordinaryFunctor R M) (skeletalPair X 0)) (j : ℤ))).symm

end ZeroSkeleton

theorem cellularZeroSkeleton :
  ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M],
    DiscreteTopology (skeletalSpace X 1) ∧
    Nonempty (chainGroup X R M 0 ≃ₗ[R] (Cell X 0 →₀ M)) ∧
    ∀ j : ℕ, j ≠ 0 → IsZero (relativeHomology R M (skeletalPair X 0) (j : ℤ)) := by
  intro X _ _ R _ M _ _
  exact ⟨zeroSkeleton_discrete X, ⟨zeroCellEquiv X R M⟩, zeroSkeleton_vanishing X R M⟩

end P202.Homology



open scoped TensorProduct Simplicial
open Opposite Set Topology

namespace P202.Homology.CoefficientExtension
open P202Specs.SingularChains P202Specs.RelativeSingularChains
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Extending the nonnegative relative sequence preserves its cokernel. -/
lemma extendedRelative_shortExact (P : Pair.{w}) :
    ((sequence (chainFunctor R M) P).map
      ((degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R))).ShortExact :=
  P202.MayerVietoris.extend_shortExact (degreeEmbedding 0) _
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (P202.RelativeSingularChains.sequence_shortExact (chainFunctor R M) P))

/-- The independently constructed ordinary relative complex is the extension
of the nonnegative relative complex, by uniqueness of the cokernel. -/
def ordinaryRelativeExtensionIso (P : Pair.{w}) :
    ordinary R M P ≅ (nonnegative R M P).extend (degreeEmbedding 0) :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (inclusion (ordinaryFunctor R M) P))
    (extendedRelative_shortExact R M P).gIsCokernel

@[reassoc] lemma ordinaryRelativeExtensionIso_projection (P : Pair.{w}) :
    projection (ordinaryFunctor R M) P ≫ (ordinaryRelativeExtensionIso R M P).hom =
      HomologicalComplex.extendMap (projection (chainFunctor R M) P) (degreeEmbedding 0) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (inclusion (ordinaryFunctor R M) P))
    (extendedRelative_shortExact R M P).gIsCokernel (.one)

lemma ordinaryRelativeExtensionIso_natural {P Q : Pair.{w}} (f : P ⟶ Q) :
    relativeMap (ordinaryFunctor R M) f ≫ (ordinaryRelativeExtensionIso R M Q).hom =
      (ordinaryRelativeExtensionIso R M P).hom ≫
        HomologicalComplex.extendMap (relativeMap (chainFunctor R M) f) (degreeEmbedding 0) := by
  apply (cancel_epi (projection (ordinaryFunctor R M) P)).mp
  rw [← Category.assoc, projection_map]
  rw [Category.assoc, ordinaryRelativeExtensionIso_projection]
  rw [← Category.assoc, ordinaryRelativeExtensionIso_projection]
  change ((degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R)).map
      (chainMap R M f.map) ≫
    ((degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R)).map
      (projection (chainFunctor R M) Q) =
    ((degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R)).map
      (projection (chainFunctor R M) P) ≫
    ((degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R)).map
      (relativeMap (chainFunctor R M) f)
  rw [← Functor.map_comp, ← Functor.map_comp, projection_map]

/-- The shared integer-indexed ordinary relative homology in every nonnegative
integer degree is canonically its nonnegative relative homology. -/
def ordinaryRelativeHomologyIso (P : Pair.{w}) (n : ℕ) :
    relativeHomology R M P (n : ℤ) ≅ (nonnegative R M P).homology n :=
  (HomologicalComplex.homologyFunctor _ _ (n : ℤ)).mapIso
      (ordinaryRelativeExtensionIso R M P) ≪≫
    (nonnegative R M P).extendHomologyIso (degreeEmbedding 0)
      (j := n) (by change (0 : ℤ) + (n : ℤ) = n; omega)

lemma ordinaryRelativeHomologyIso_natural {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ) :
    homologyMap (relativeMap (ordinaryFunctor R M) f) (n : ℤ) ≫
        (ordinaryRelativeHomologyIso R M Q n).hom =
      (ordinaryRelativeHomologyIso R M P n).hom ≫
        homologyMap (relativeMap (chainFunctor R M) f) n := by
  dsimp only [ordinaryRelativeHomologyIso, Iso.trans_hom, Functor.mapIso_hom]
  change homologyMap _ _ ≫ (homologyMap _ _ ≫ _) = (homologyMap _ _ ≫ _) ≫ _
  rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ordinaryRelativeExtensionIso_natural, HomologicalComplex.homologyMap_comp,
    Category.assoc, HomologicalComplex.extendHomologyIso_hom_naturality]
  simp only [Category.assoc]

lemma ordinaryRelativeHomologyMap_isIso_iff {P Q : Pair.{w}} (f : P ⟶ Q) (n : ℕ) :
    IsIso (homologyMap (relativeMap (ordinaryFunctor R M) f) (n : ℤ)) ↔
      IsIso (homologyMap (relativeMap (chainFunctor R M) f) n) := by
  exact (MorphismProperty.isomorphisms (ModuleCat.{max v w} R)).arrow_mk_iso_iff
    (Arrow.isoMk (ordinaryRelativeHomologyIso R M P n)
      (ordinaryRelativeHomologyIso R M Q n) (ordinaryRelativeHomologyIso_natural R M f n).symm)

end P202.Homology.CoefficientExtension

namespace P202.Homology.Coefficients
open P202.SpheresDisks.IntegralCoefficients
open P202Specs.SingularChains P202Specs.RelativeSingularChains
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Tensoring integral modules with any coefficient module preserves cokernels.
This is right exactness, without a flatness hypothesis. -/
instance tensorPreservesCokernel {A B : ModuleCat.{w} ℤ} (f : A ⟶ B) :
    PreservesColimit (parallelPair f 0) (integralTensorFunctor R M) := by
  let F := integralTensorFunctor R M
  let S := (ShortComplex.cokernelSequence f).map F
  have hg : Function.Surjective (cokernel.π f) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have he : Function.Exact f (cokernel.π f) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (ShortComplex.cokernelSequence_exact f)
  haveI : Epi S.g := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    exact LinearMap.lTensor_surjective M hg
  have hS : S.Exact := by
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact lTensor_exact M he hg
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
  exact (isColimitMapCoconeCoforkEquiv' F (cokernel.condition f)).symm hS.gIsCokernel

instance tensorPreservesFiniteColimits :
    PreservesFiniteColimits (integralTensorFunctor.{u,v,w} R M) :=
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-- The coefficient tensor identification on the ordinary singular chain complex. -/
def tensorComplexIso (X : TopCat.{w}) :
    ((integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)).obj
      (complex ℤ ℤ X) ≅ complex R M X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (integralTensorChainsEquiv R M X n).toModuleIso) (by
      intro i j hij
      have hi : j+1 = i := hij
      subst i
      apply ModuleCat.hom_ext
      ext z
      exact (integralTensorChainsEquiv_boundary R M X j z).symm)

lemma tensorComplexIso_natural {X Y : TopCat.{w}} (f : X ⟶ Y) :
    ((integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)).map (chainMap ℤ ℤ f) ≫
      (tensorComplexIso R M Y).hom =
    (tensorComplexIso R M X).hom ≫ chainMap R M f := by
  classical
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply TensorProduct.AlgebraTensorModule.ext
  intro m z
  change integralTensorChainsEquiv R M Y n
      (m ⊗ₜ[ℤ] (chainMap ℤ ℤ f).f n z) =
    (chainMap R M f).f n (integralTensorChainsEquiv R M X n (m ⊗ₜ[ℤ] z))
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z z' hz hz' => simpa only [TensorProduct.tmul_add, map_add] using congrArg₂ (· + ·) hz hz'
  | single s a =>
    change integralTensorChainsEquiv R M Y n
        (m ⊗ₜ[ℤ] (chainMap ℤ ℤ f).f n (Finsupp.single s a)) =
      (chainMap R M f).f n
        (integralTensorChainsEquiv R M X n (m ⊗ₜ[ℤ] Finsupp.single s a))
    simp only [P202.SingularChains.chainMap_single, integralTensorChainsEquiv_tmul_single]

/-- Tensoring the actual relative quotient, using right exactness. -/
def tensorRelativeIso (P : Pair.{w}) :
    ((integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)).obj
      (nonnegative ℤ ℤ P) ≅ nonnegative R M P :=
  let F := (integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)
  (PreservesCokernel.iso F (inclusion (chainFunctor ℤ ℤ) P)) ≪≫
    cokernel.mapIso _ _ (tensorComplexIso R M P.sub) (tensorComplexIso R M P.space)
      (tensorComplexIso_natural R M P.inclusion)


@[reassoc] lemma tensorRelativeIso_projection (P : Pair.{w}) :
    ((integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)).map
        (projection (chainFunctor ℤ ℤ) P) ≫ (tensorRelativeIso R M P).hom =
      (tensorComplexIso R M P.space).hom ≫ projection (chainFunctor R M) P := by
  dsimp only [tensorRelativeIso, Iso.trans_hom]
  rw [← Category.assoc, PreservesCokernel.π_iso_hom]
  exact cokernel.π_desc _ _ _

lemma tensorRelativeIso_natural {P Q : Pair.{w}} (f : P ⟶ Q) :
    ((integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)).map
        (relativeMap (chainFunctor ℤ ℤ) f) ≫ (tensorRelativeIso R M Q).hom =
      (tensorRelativeIso R M P).hom ≫ relativeMap (chainFunctor R M) f := by
  let F := (integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)
  apply (cancel_epi (F.map (projection (chainFunctor ℤ ℤ) P))).mp
  rw [← Category.assoc, ← F.map_comp, projection_map, F.map_comp, Category.assoc,
    tensorRelativeIso_projection, tensorRelativeIso_projection_assoc]
  rw [← Category.assoc, tensorComplexIso_natural, Category.assoc, projection_map]

/-- A quasi-isomorphism between integral relative singular complexes remains one
with arbitrary coefficients: both integral complexes are degreewise free, so
it is a chain homotopy equivalence before tensoring. -/
lemma relativeMap_quasiIso_of_integral {P Q : Pair.{w}} (f : P ⟶ Q)
    [QuasiIso (relativeMap (chainFunctor ℤ ℤ) f)] :
    QuasiIso (relativeMap (chainFunctor R M) f) := by
  have hproj (P : Pair.{w}) (k : ℕ) : Projective ((nonnegative ℤ ℤ P).X k) := by
    obtain ⟨b, _⟩ := P202.RelativeSingularChains.quotient_basis ℤ P k
    exact ModuleCat.projective_of_free b
  have : ∀ k, Projective ((nonnegative ℤ ℤ P).X k) := hproj P
  have : ∀ k, Projective ((nonnegative ℤ ℤ Q).X k) := hproj Q
  let F := (integralTensorFunctor R M).mapHomologicalComplex (.down ℕ)
  haveI : QuasiIso (F.map (relativeMap (chainFunctor ℤ ℤ) f)) :=
    P202.SpheresDisks.ConcentratedHomology.map_quasiIso_of_projective
      (integralTensorFunctor R M) _
  haveI : QuasiIso (F.map (relativeMap (chainFunctor ℤ ℤ) f) ≫
      (tensorRelativeIso R M Q).hom) := inferInstance
  rw [tensorRelativeIso_natural] at this
  exact (quasiIso_iff_comp_left (tensorRelativeIso R M P).hom _).mp this

/-- Excision with an arbitrary module of coefficients, in the nonnegative model. -/
lemma excision_nonnegative (D : P202Specs.Excision.Data.{w}) (n : ℕ) :
    IsIso (homologyMap (relativeMap (chainFunctor R M) D.inclusion) n) := by
  haveI : QuasiIso (relativeMap (chainFunctor ℤ ℤ) D.inclusion) := by
    rw [quasiIso_iff]
    intro i
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact P202.Excision.isomorphism ℤ D i
  haveI := relativeMap_quasiIso_of_integral R M D.inclusion
  infer_instance


/-- Excision for the shared integer-indexed ordinary relative homology,
with arbitrary modules and arbitrary universe sizes. -/
lemma excision (D : P202Specs.Excision.Data.{w}) (n : ℕ) :
    IsIso (homologyMap (relativeMap (ordinaryFunctor R M) D.inclusion) (n : ℤ)) :=
  (P202.Homology.CoefficientExtension.ordinaryRelativeHomologyMap_isIso_iff R M _ n).mpr
    (excision_nonnegative R M D n)

end P202.Homology.Coefficients


namespace P202.Homology.CellSums
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open Opposite
open scoped Simplicial

/-- Finite direct sums indexed by any set of cell labels. -/
def sumModuleFunctor (R : Type u) [CommRing R] (I : Type w) :
    ModuleCat.{max v w} R ⥤ ModuleCat.{max v w} R where
  obj A := ModuleCat.of R (I →₀ A)
  map f := ModuleCat.ofHom (Finsupp.mapRange.linearMap f.hom)
  map_id A := by ext x i; rfl
  map_comp f g := by ext x i; rfl

instance (R : Type u) [CommRing R] (I : Type w) :
    (sumModuleFunctor.{u,v,w} R I).Additive where
  map_add := by
    intros
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Finsupp.ext
    intro i
    rfl

/-- Direct sums are exact, also when the index set is infinite or empty. -/
instance (R : Type u) [CommRing R] (I : Type w) :
    (sumModuleFunctor.{u,v,w} R I).PreservesHomology := by
  apply CategoryTheory.Functor.preservesHomology_of_map_exact
  intro S hS
  rw [CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range (Finsupp.mapRange.linearMap S.f.hom) =
    LinearMap.ker (Finsupp.mapRange.linearMap S.g.hom)
  ext x
  change x ∈ Set.range (Finsupp.mapRange S.f.hom (map_zero _)) ↔
    Finsupp.mapRange S.g.hom (map_zero _) x = 0
  rw [Finsupp.range_mapRange]
  change (∀ i, x i ∈ LinearMap.range S.f.hom) ↔ _
  rw [hS.moduleCat_range_eq_ker]
  simp [Finsupp.ext_iff]

/-- A simplex in a topological disjoint union is in one and only one summand.
Connectedness and nonemptiness of the simplex are both used by the library
homeomorphism, so no finiteness or nonemptiness of `I` is required. -/
def sumSimplexEquiv (I : Type w) (X : TopCat.{w}) (n : ℕ) :
    Simplex (TopCat.of (Σ _ : I, X)) n ≃ I × Simplex X n :=
  (simplexEquiv _ n).trans
    ((ContinuousMap.sigmaCodHomeomorph
      (Convexity.StdSimplex ℝ (Fin (n+1))) (fun _ : I => X)).toEquiv.trans
      ((Equiv.sigmaCongrRight (fun _ => (simplexEquiv X n).symm)).trans
        (Equiv.sigmaEquivProd I (Simplex X n))))

variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Grouping finite singular chains by their disjoint summand. -/
def sumChainsEquiv (I : Type w) (X : TopCat.{w}) (n : ℕ) :
    Chains M (TopCat.of (Σ _ : I, X)) n ≃ₗ[R] I →₀ Chains M X n :=
  (Finsupp.mapDomain.linearEquiv M R (sumSimplexEquiv I X n)).trans
    (Finsupp.curryLinearEquiv R)

/-- Inclusion of a disjoint summand. -/
def sumInclusion (I : Type w) (X : TopCat.{w}) (i : I) :
    X ⟶ TopCat.of (Σ _ : I, X) :=
  TopCat.ofHom (ContinuousMap.sigmaMk (X := fun _ : I => X) i)

lemma sumSimplexEquiv_symm (I : Type w) (X : TopCat.{w}) (n : ℕ)
    (i : I) (s : Simplex X n) :
    (sumSimplexEquiv I X n).symm (i, s) =
      (TopCat.toSSet.map (sumInclusion I X i)).app (op ⦋n⦌) s := by
  apply (simplexEquiv _ n).injective
  rw [P202.SingularChains.simplexEquiv_postcomp]
  simp [sumSimplexEquiv, sumInclusion, Equiv.sigmaCongrRight]

lemma sumChainsEquiv_symm_single (I : Type w) (X : TopCat.{w}) (n : ℕ)
    (i : I) (s : Simplex X n) (m : M) :
    (sumChainsEquiv R M I X n).symm (Finsupp.single i (Finsupp.single s m)) =
      Finsupp.single ((TopCat.toSSet.map (sumInclusion I X i)).app (op ⦋n⦌) s) m := by
  change (Finsupp.mapDomain.linearEquiv M R (sumSimplexEquiv I X n)).symm
    ((Finsupp.single i (Finsupp.single s m)).uncurry) = _
  rw [Finsupp.uncurry_single]
  simp [sumSimplexEquiv_symm]

/-- The decomposition into summands respects the complete singular boundary. -/
def sumComplexIso (I : Type w) (X : TopCat.{w}) :
    ((sumModuleFunctor.{u,v,w} R I).mapHomologicalComplex (.down ℕ)).obj
      (complex R M X) ≅ complex R M (TopCat.of (Σ _ : I, X)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (sumChainsEquiv R M I X n).symm.toModuleIso) (by
      intro a b hab
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext
      intro i z
      change (complex R M _).d a b ((sumChainsEquiv R M I X a).symm
          (Finsupp.single i z)) =
        (sumChainsEquiv R M I X b).symm
          (Finsupp.mapRange ((complex R M X).d a b).hom (map_zero _) (Finsupp.single i z))
      have hs (n : ℕ) (c : Chains M X n) :
          (sumChainsEquiv R M I X n).symm (Finsupp.single i c) =
            (chainMap R M (sumInclusion I X i)).f n c := by
        induction c using Finsupp.induction_linear with
        | zero => simp
        | add c d hc hd => simp [hc, hd]
        | single s m =>
          rw [sumChainsEquiv_symm_single, P202.SingularChains.chainMap_single]
      rw [hs]
      simp only [Finsupp.mapRange_single]
      rw [hs]
      exact congrArg (fun f => f z) ((chainMap R M (sumInclusion I X i)).comm a b))


/-- Direct sums commute with extending a chain complex by zero. -/
def sumExtendXIso {ι : Type*} {c : ComplexShape ι} (I : Type w)
    (K : HomologicalComplex (ModuleCat.{max v w} R) c) (o : Option ι) :
    (sumModuleFunctor R I).obj (HomologicalComplex.extend.X K o) ≅
      HomologicalComplex.extend.X
        (((sumModuleFunctor R I).mapHomologicalComplex c).obj K) o :=
  match o with
  | some _ => Iso.refl _
  | none => IsZero.iso ((sumModuleFunctor R I).map_isZero (isZero_zero _)) (isZero_zero _)

lemma sumExtendXIso_comm {ι : Type*} {c : ComplexShape ι} (I : Type w)
    (K : HomologicalComplex (ModuleCat.{max v w} R) c) (o p : Option ι) :
    (sumExtendXIso R I K o).hom ≫
        HomologicalComplex.extend.d (((sumModuleFunctor R I).mapHomologicalComplex c).obj K) o p =
      (sumModuleFunctor R I).map (HomologicalComplex.extend.d K o p) ≫
        (sumExtendXIso R I K p).hom := by
  cases o <;> cases p <;> simp [sumExtendXIso, HomologicalComplex.extend.d]

def sumExtendIso {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (I : Type w) (K : HomologicalComplex (ModuleCat.{max v w} R) c)
    (e : c.Embedding c') :
    ((sumModuleFunctor R I).mapHomologicalComplex c').obj (K.extend e) ≅
      (((sumModuleFunctor R I).mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun n => sumExtendXIso R I K (e.r n)) (by
    intro a b hab
    exact sumExtendXIso_comm R I K (e.r a) (e.r b))

def sumOrdinaryIso (I : Type w) (X : TopCat.{w}) :
    ((sumModuleFunctor.{u,v,w} R I).mapHomologicalComplex (.down ℤ)).obj
      (ordinaryComplex R M X) ≅ ordinaryComplex R M (TopCat.of (Σ _ : I, X)) :=
  sumExtendIso R I (complex R M X) (degreeEmbedding 0) ≪≫
    ((degreeEmbedding 0).extendFunctor _).mapIso (sumComplexIso R M I X)


/-- The disjoint union of copies of a topological pair. -/
def sumPair (I : Type w) (P : Pair.{w}) : Pair.{w} :=
  ⟨TopCat.of (Σ _ : I, P.space), {x | x.2 ∈ P.subspace}⟩

def sumSubEquiv (I : Type w) (P : Pair.{w}) :
    (Σ _ : I, P.sub) ≃ (sumPair I P).sub where
  toFun x := ⟨⟨x.1, x.2.val⟩, x.2.property⟩
  invFun x := ⟨x.val.1, ⟨x.val.2, x.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sumSubHomeomorph (I : Type w) (P : Pair.{w}) :
    (Σ _ : I, P.sub) ≃ₜ (sumPair I P).sub :=
  (sumSubEquiv I P).toHomeomorphOfIsInducing (by
    have h : Topology.IsInducing
        ((Subtype.val : (sumPair I P).sub → (Σ _ : I, P.space)) ∘ sumSubEquiv I P) :=
      (Topology.isInducing_sigmaMap (σ := fun _ : I => P.sub)
        (τ := fun _ : I => P.space) (f₁ := id)
        (f₂ := fun _ : I => (Subtype.val : P.sub → P.space)) Function.injective_id).mpr
          (fun _ => Topology.IsInducing.subtypeVal)
    exact Topology.IsInducing.subtypeVal.of_comp_iff.mp h)

def sumPairInclusion (I : Type w) (P : Pair.{w}) (i : I) : P ⟶ sumPair I P :=
  ⟨sumInclusion I P.space i, fun _ h => h⟩


lemma sumChainsEquiv_symm_single_chain (I : Type w) (X : TopCat.{w}) (n : ℕ)
    (i : I) (c : Chains M X n) :
    (sumChainsEquiv R M I X n).symm (Finsupp.single i c) =
      (chainMap R M (sumInclusion I X i)).f n c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [hc, hd]
  | single s m =>
    rw [sumChainsEquiv_symm_single, P202.SingularChains.chainMap_single]

def sumMap (I : Type w) {X Y : TopCat.{w}} (f : X ⟶ Y) :
    TopCat.of (Σ _ : I, X) ⟶ TopCat.of (Σ _ : I, Y) :=
  TopCat.ofHom ⟨Sigma.map id (fun _ => f), by
    exact Continuous.sigma_map (fun _ => f.hom.continuous)⟩

lemma sumComplexIso_natural (I : Type w) {X Y : TopCat.{w}} (f : X ⟶ Y) :
    ((sumModuleFunctor R I).mapHomologicalComplex (.down ℕ)).map (chainMap R M f) ≫
        (sumComplexIso R M I Y).hom =
      (sumComplexIso R M I X).hom ≫ chainMap R M (sumMap I f) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro i c
  change (sumChainsEquiv R M I Y n).symm
      (Finsupp.mapRange ((chainMap R M f).f n).hom (map_zero _) (Finsupp.single i c)) =
    (chainMap R M (sumMap I f)).f n
      ((sumChainsEquiv R M I X n).symm (Finsupp.single i c))
  rw [Finsupp.mapRange_single, sumChainsEquiv_symm_single_chain,
    sumChainsEquiv_symm_single_chain]
  have h : f ≫ sumInclusion I Y i = sumInclusion I X i ≫ sumMap I f := rfl
  have hh := congrArg (fun q => (chainMap R M q).f n) h
  simp only [P202.SingularChains.chainMap_comp, HomologicalComplex.comp_f] at hh
  exact congrArg (fun q => q c) hh


lemma sumExtendXIso_natural {ι : Type*} {c : ComplexShape ι} (I : Type w)
    {K L : HomologicalComplex (ModuleCat.{max v w} R) c} (φ : K ⟶ L) (o : Option ι) :
    (sumModuleFunctor R I).map (HomologicalComplex.extend.mapX φ o) ≫
        (sumExtendXIso R I L o).hom =
      (sumExtendXIso R I K o).hom ≫ HomologicalComplex.extend.mapX
        (((sumModuleFunctor R I).mapHomologicalComplex c).map φ) o := by
  cases o <;> simp [sumExtendXIso, HomologicalComplex.extend.mapX]

lemma sumExtendIso_natural {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (I : Type w) {K L : HomologicalComplex (ModuleCat.{max v w} R) c}
    (φ : K ⟶ L) (e : c.Embedding c') :
    ((sumModuleFunctor R I).mapHomologicalComplex c').map
        (HomologicalComplex.extendMap φ e) ≫ (sumExtendIso R I L e).hom =
      (sumExtendIso R I K e).hom ≫
        HomologicalComplex.extendMap (((sumModuleFunctor R I).mapHomologicalComplex c).map φ) e := by
  ext n : 1
  exact sumExtendXIso_natural R I φ (e.r n)

lemma sumOrdinaryIso_natural (I : Type w) {X Y : TopCat.{w}} (f : X ⟶ Y) :
    ((sumModuleFunctor R I).mapHomologicalComplex (.down ℤ)).map ((ordinaryFunctor R M).map f) ≫
        (sumOrdinaryIso R M I Y).hom =
      (sumOrdinaryIso R M I X).hom ≫ (ordinaryFunctor R M).map (sumMap I f) := by
  change ((sumModuleFunctor R I).mapHomologicalComplex (.down ℤ)).map
      (HomologicalComplex.extendMap (chainMap R M f) (degreeEmbedding 0)) ≫
    ((sumExtendIso R I (complex R M Y) (degreeEmbedding 0)).hom ≫
      ((degreeEmbedding 0).extendFunctor _).map (sumComplexIso R M I Y).hom) =
    ((sumExtendIso R I (complex R M X) (degreeEmbedding 0)).hom ≫
      ((degreeEmbedding 0).extendFunctor _).map (sumComplexIso R M I X).hom) ≫
      HomologicalComplex.extendMap (chainMap R M (sumMap I f)) (degreeEmbedding 0)
  rw [← Category.assoc, sumExtendIso_natural, Category.assoc]
  have h := congrArg (((degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R)).map)
    (sumComplexIso_natural R M I f)
  simp only [Functor.map_comp] at h
  have hh := congrArg
    (fun q => (sumExtendIso R I (complex R M X) (degreeEmbedding 0)).hom ≫ q) h
  dsimp only [ComplexShape.Embedding.extendFunctor, chainFunctor, complex] at hh ⊢
  simpa only [Category.assoc] using hh


instance sumModule_preservesFiniteColimits (I : Type w) :
    PreservesFiniteColimits (sumModuleFunctor.{u,v,w} R I) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

def sumSubOrdinaryIso (I : Type w) (P : Pair.{w}) :
    ((sumModuleFunctor R I).mapHomologicalComplex (.down ℤ)).obj (ordinaryComplex R M P.sub) ≅
      ordinaryComplex R M (sumPair I P).sub :=
  sumOrdinaryIso R M I P.sub ≪≫
    (ordinaryFunctor R M).mapIso (TopCat.isoOfHomeo (sumSubHomeomorph I P))

lemma sumOrdinaryIso_inclusion (I : Type w) (P : Pair.{w}) :
    ((sumModuleFunctor R I).mapHomologicalComplex (.down ℤ)).map
        (inclusion (ordinaryFunctor R M) P) ≫ (sumOrdinaryIso R M I P.space).hom =
      (sumSubOrdinaryIso R M I P).hom ≫ inclusion (ordinaryFunctor R M) (sumPair I P) := by
  have h : sumMap I P.inclusion =
      (TopCat.isoOfHomeo (sumSubHomeomorph I P)).hom ≫ (sumPair I P).inclusion := rfl
  have hn := sumOrdinaryIso_natural R M I P.inclusion
  rw [h, Functor.map_comp] at hn
  exact hn

def sumRelativeIso (I : Type w) (P : Pair.{w}) :
    ((sumModuleFunctor R I).mapHomologicalComplex (.down ℤ)).obj (ordinary R M P) ≅
      ordinary R M (sumPair I P) :=
  PreservesCokernel.iso ((sumModuleFunctor R I).mapHomologicalComplex (.down ℤ))
      (inclusion (ordinaryFunctor R M) P) ≪≫
    cokernel.mapIso _ (inclusion (ordinaryFunctor R M) (sumPair I P))
      (sumSubOrdinaryIso R M I P) (sumOrdinaryIso R M I P.space)
      (sumOrdinaryIso_inclusion R M I P)

def sumRelativeHomologyIso (I : Type w) (P : Pair.{w}) (n : ℤ) :
    (sumModuleFunctor R I).obj (relativeHomology R M P n) ≅
      relativeHomology R M (sumPair I P) n :=
  (((ordinary R M P).sc n).mapHomologyIso (sumModuleFunctor R I)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ n).mapIso (sumRelativeIso R M I P)


/-- The canonical inclusion into one direct summand. -/
def sumSingle (I : Type w) (i : I) :
    𝟭 (ModuleCat.{max v w} R) ⟶ sumModuleFunctor.{u,v,w} R I where
  app A := ModuleCat.ofHom (Finsupp.lsingle i)
  naturality _ _ f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change Finsupp.single i (f x) =
      Finsupp.mapRange f.hom (map_zero _) (Finsupp.single i x)
    simp only [Finsupp.mapRange_single]

def sumSingleComplex {ι : Type*} {c : ComplexShape ι} (I : Type w) (i : I)
    (K : HomologicalComplex (ModuleCat.{max v w} R) c) :
    K ⟶ ((sumModuleFunctor R I).mapHomologicalComplex c).obj K :=
  (NatTrans.mapHomologicalComplex (sumSingle R I i) c).app K

lemma sumComplexIso_single (I : Type w) (X : TopCat.{w}) (i : I) :
    sumSingleComplex R I i (complex R M X) ≫ (sumComplexIso R M I X).hom =
      chainMap R M (sumInclusion I X i) := by
  ext n : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  exact sumChainsEquiv_symm_single_chain R M I X n i c

lemma sumExtendXIso_single {ι : Type*} {c : ComplexShape ι} (I : Type w) (i : I)
    (K : HomologicalComplex (ModuleCat.{max v w} R) c) (o : Option ι) :
    (sumSingle R I i).app (HomologicalComplex.extend.X K o) ≫ (sumExtendXIso R I K o).hom =
      HomologicalComplex.extend.mapX (sumSingleComplex R I i K) o := by
  cases o with
  | none => exact (isZero_zero _).eq_of_src _ _
  | some j => simp [sumExtendXIso, HomologicalComplex.extend.mapX, sumSingleComplex, HomologicalComplex.extend.X]

lemma sumExtendIso_single {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (I : Type w) (i : I) (K : HomologicalComplex (ModuleCat.{max v w} R) c)
    (e : c.Embedding c') :
    sumSingleComplex R I i (K.extend e) ≫ (sumExtendIso R I K e).hom =
      HomologicalComplex.extendMap (sumSingleComplex R I i K) e := by
  ext n : 1
  exact sumExtendXIso_single R I i K (e.r n)

lemma sumOrdinaryIso_single (I : Type w) (X : TopCat.{w}) (i : I) :
    sumSingleComplex R I i (ordinaryComplex R M X) ≫ (sumOrdinaryIso R M I X).hom =
      (ordinaryFunctor R M).map (sumInclusion I X i) := by
  change sumSingleComplex R I i ((complex R M X).extend (degreeEmbedding 0)) ≫
    ((sumExtendIso R I (complex R M X) (degreeEmbedding 0)).hom ≫
      HomologicalComplex.extendMap (sumComplexIso R M I X).hom (degreeEmbedding 0)) =
    HomologicalComplex.extendMap (chainMap R M (sumInclusion I X i)) (degreeEmbedding 0)
  rw [← Category.assoc, sumExtendIso_single, ← HomologicalComplex.extendMap_comp,
    sumComplexIso_single]

@[reassoc] lemma sumRelativeIso_projection (I : Type w) (P : Pair.{w}) :
    ((sumModuleFunctor R I).mapHomologicalComplex (.down ℤ)).map
        (projection (ordinaryFunctor R M) P) ≫ (sumRelativeIso R M I P).hom =
      (sumOrdinaryIso R M I P.space).hom ≫ projection (ordinaryFunctor R M) (sumPair I P) := by
  dsimp only [sumRelativeIso, Iso.trans_hom, cokernel.mapIso_hom]
  rw [← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]

lemma sumRelativeIso_single (I : Type w) (P : Pair.{w}) (i : I) :
    sumSingleComplex R I i (ordinary R M P) ≫ (sumRelativeIso R M I P).hom =
      relativeMap (ordinaryFunctor R M) (sumPairInclusion I P i) := by
  apply (cancel_epi (projection (ordinaryFunctor R M) P)).mp
  have h := (NatTrans.mapHomologicalComplex (sumSingle R I i) (.down ℤ)).naturality
    (projection (ordinaryFunctor R M) P)
  change projection (ordinaryFunctor R M) P ≫ sumSingleComplex R I i (ordinary R M P) =
    sumSingleComplex R I i (ordinaryComplex R M P.space) ≫
      ((sumModuleFunctor R I).mapHomologicalComplex (.down ℤ)).map
        (projection (ordinaryFunctor R M) P) at h
  rw [← Category.assoc, h, Category.assoc, sumRelativeIso_projection,
    ← Category.assoc, sumOrdinaryIso_single, projection_map]
  rfl


lemma shortComplex_mapHomologyIso_id
    {C : Type*} [Category C] [Preadditive C] [CategoryWithHomology C]
    (S : ShortComplex C) :
    S.mapHomologyIso (𝟭 C) = Iso.refl S.homology := by
  let d := S.homologyData.left
  let γ : ShortComplex.LeftHomologyMapData (𝟙 S) (d.map (𝟭 C)) d :=
    { φK := 𝟙 _
      φH := 𝟙 _
      commi := by simp [d]
      commf' := by simp [d]
      commπ := by simp [d] }
  have h := γ.homologyMap_eq
  rw [d.mapHomologyIso_eq (𝟭 C)]
  apply Iso.ext
  simpa [γ] using h.symm

lemma sumSingleComplex_homology {ι : Type*} {c : ComplexShape ι}
    (I : Type w) (i : I) (K : HomologicalComplex (ModuleCat.{max v w} R) c) (n : ι) :
    homologyMap (sumSingleComplex R I i K) n ≫
        ((K.sc n).mapHomologyIso (sumModuleFunctor R I)).hom =
      (sumSingle R I i).app (K.homology n) := by
  have h := NatTrans.app_homology (sumSingle R I i) (K.sc n)
  rw [shortComplex_mapHomologyIso_id] at h
  dsimp only [Functor.id_obj, Iso.refl_inv] at h
  rw [Category.id_comp] at h
  exact h.symm

@[reassoc] lemma sumRelativeHomologyIso_single_map (I : Type w) (P : Pair.{w})
    (n : ℤ) (i : I) :
    (sumSingle R I i).app (relativeHomology R M P n) ≫
        (sumRelativeHomologyIso R M I P n).hom =
      homologyMap (relativeMap (ordinaryFunctor R M) (sumPairInclusion I P i)) n := by
  rw [← sumSingleComplex_homology R I i (ordinary R M P) n]
  change (homologyMap (sumSingleComplex R I i (ordinary R M P)) n ≫
      (((ordinary R M P).sc n).mapHomologyIso (sumModuleFunctor R I)).hom) ≫
    ((((ordinary R M P).sc n).mapHomologyIso (sumModuleFunctor R I)).inv ≫
      homologyMap (sumRelativeIso R M I P).hom n) = _
  rw [Category.assoc, Iso.hom_inv_id_assoc, ← homologyMap_comp,
    sumRelativeIso_single]

lemma sumRelativeHomologyIso_single (I : Type w) (P : Pair.{w}) (n : ℤ)
    (i : I) (a : relativeHomology R M P n) :
    (sumRelativeHomologyIso R M I P n).hom (Finsupp.single i a) =
      (relativeHomologyFunctor R M n).map (sumPairInclusion I P i) a :=
  congrArg (fun q => q a) (sumRelativeHomologyIso_single_map R M I P n i)

end P202.Homology.CellSums


namespace P202.Homology.DiskBridge
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- Singular simplices transport along homeomorphisms across universes. -/
def simplexTransport {X : TopCat.{0}} {Y : TopCat.{w}} (e : X ≃ₜ Y) (n : ℕ) :
    Simplex X n ≃ Simplex Y n :=
  (simplexEquiv X n).trans
    ((Homeomorph.continuousMapCongr (Homeomorph.refl _) e).trans (simplexEquiv Y n).symm)

lemma simplexTransport_face {X : TopCat.{0}} {Y : TopCat.{w}} (e : X ≃ₜ Y)
    {n : ℕ} (i : Fin (n+2)) (s : Simplex X (n+1)) :
    simplexTransport e n (face i s) = face i (simplexTransport e (n+1) s) := by
  apply (simplexEquiv Y n).injective
  rw [P202.SingularChains.simplexEquiv_face]
  simp only [simplexTransport, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [P202.SingularChains.simplexEquiv_face]
  ext x
  rfl

/-- Raising the coefficient universe compensates for raising the space universe. -/
def chainsTransport {X : TopCat.{0}} {Y : TopCat.{w}} (e : X ≃ₜ Y) (n : ℕ) :
    Chains (ULift.{w} M) X n ≃ₗ[R] Chains M Y n :=
  (Finsupp.mapRange.linearEquiv (ULift.moduleEquiv : ULift.{w} M ≃ₗ[R] M)).trans
    (Finsupp.mapDomain.linearEquiv M R (simplexTransport e n))

@[simp] lemma chainsTransport_single {X : TopCat.{0}} {Y : TopCat.{w}}
    (e : X ≃ₜ Y) (n : ℕ) (s : Simplex X n) (m : ULift.{w} M) :
    chainsTransport R M e n (Finsupp.single s m) =
      Finsupp.single (simplexTransport e n s) m.down := by
  simp [chainsTransport, Finsupp.mapDomain.linearEquiv]

def complexTransport {X : TopCat.{0}} {Y : TopCat.{w}} (e : X ≃ₜ Y) :
    complex R (ULift.{w} M) X ≅ complex R M Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (chainsTransport R M e n).toModuleIso) (by
      intro i j hij
      have he : j+1 = i := hij
      subst i
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext
      intro s m
      change boundary R M Y j (chainsTransport R M e (j+1) (Finsupp.single s m)) =
        chainsTransport R M e j (boundary R (ULift.{w} M) X j (Finsupp.single s m))
      rw [chainsTransport_single, P202.SingularChains.boundary_single,
        P202.SingularChains.boundary_single, map_sum]
      simp only [map_zsmul, chainsTransport_single, simplexTransport_face])

lemma simplexTransport_natural {X X' : TopCat.{0}} {Y Y' : TopCat.{w}}
    (e : X ≃ₜ Y) (e' : X' ≃ₜ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : ∀ x, e' (f x) = g (e x)) (n : ℕ) (s : Simplex X n) :
    simplexTransport e' n ((TopCat.toSSet.map f).app (op ⦋n⦌) s) =
      (TopCat.toSSet.map g).app (op ⦋n⦌) (simplexTransport e n s) := by
  apply (simplexEquiv Y' n).injective
  rw [P202.SingularChains.simplexEquiv_postcomp]
  simp only [simplexTransport, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [P202.SingularChains.simplexEquiv_postcomp]
  ext x
  exact h _

lemma complexTransport_natural {X X' : TopCat.{0}} {Y Y' : TopCat.{w}}
    (e : X ≃ₜ Y) (e' : X' ≃ₜ Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : ∀ x, e' (f x) = g (e x)) :
    chainMap R (ULift.{w} M) f ≫ (complexTransport R M e').hom =
      (complexTransport R M e).hom ≫ chainMap R M g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro s m
  change chainsTransport R M e' n ((chainMap R (ULift.{w} M) f).f n (Finsupp.single s m)) =
    (chainMap R M g).f n (chainsTransport R M e n (Finsupp.single s m))
  rw [P202.SingularChains.chainMap_single, chainsTransport_single,
    chainsTransport_single, P202.SingularChains.chainMap_single,
    simplexTransport_natural e e' f g h]

def ordinaryTransport {X : TopCat.{0}} {Y : TopCat.{w}} (e : X ≃ₜ Y) :
    ordinaryComplex R (ULift.{w} M) X ≅ ordinaryComplex R M Y :=
  ((degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R)).mapIso (complexTransport R M e)

def relativeTransport {P : Pair.{0}} {Q : Pair.{w}} (e : P.space ≃ₜ Q.space)
    (es : P.sub ≃ₜ Q.sub) (h : ∀ x : P.sub, e x.val = (es x).val) :
    ordinary R (ULift.{w} M) P ≅ ordinary R M Q :=
  cokernel.mapIso (inclusion (ordinaryFunctor R (ULift.{w} M)) P)
    (inclusion (ordinaryFunctor R M) Q)
    (ordinaryTransport R M es) (ordinaryTransport R M e) (by
      change ((degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R)).map
        (chainMap R (ULift.{w} M) P.inclusion) ≫
          ((degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R)).map
            (complexTransport R M e).hom =
        ((degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R)).map
          (complexTransport R M es).hom ≫
        ((degreeEmbedding 0).extendFunctor (ModuleCat.{max v w} R)).map
          (chainMap R M Q.inclusion)
      rw [← Functor.map_comp, ← Functor.map_comp,
        complexTransport_natural R M es e P.inclusion Q.inclusion h])

def diskBoundaryTransport (n : ℕ) :
    (P202Specs.SpheresDisks.diskPair n).sub ≃ₜ (referenceDiskPair.{w} n).sub where
  toFun x := ⟨ULift.up x.val, x.property⟩
  invFun x := ⟨x.val.down, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_uliftUp.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_uliftDown.comp continuous_subtype_val).subtype_mk _

def referenceDiskRelativeIso (n : ℕ) :
    ordinary R (ULift.{w} M) (P202Specs.SpheresDisks.diskPair n) ≅
      ordinary R M (referenceDiskPair.{w} n) :=
  relativeTransport R M (referenceDiskHomeomorph n).symm (diskBoundaryTransport n)
    (fun _ => rfl)

def referenceDiskHomologyIso (n : ℕ) (j : ℤ) :
    relativeHomology R (ULift.{w} M) (P202Specs.SpheresDisks.diskPair n) j ≅
      relativeHomology R M (referenceDiskPair.{w} n) j :=
  (HomologicalComplex.homologyFunctor _ _ j).mapIso (referenceDiskRelativeIso R M n)

lemma referenceDiskHomology_of
    (hd : P202Specs.SpheresDisks.diskHomology_type.{u,max v w}) (n j : ℕ) :
    (j = n → Nonempty (relativeHomology R M (referenceDiskPair.{w} n) (j : ℤ) ≃ₗ[R] M)) ∧
    (j ≠ n → IsZero (relativeHomology R M (referenceDiskPair.{w} n) (j : ℤ))) := by
  let e := referenceDiskHomologyIso R M n (j : ℤ)
  constructor
  · intro hj
    obtain ⟨f⟩ := (hd R (ULift.{w} M) n j).1 hj
    exact ⟨(e.symm.toLinearEquiv.trans f).trans ULift.moduleEquiv⟩
  · intro hj
    exact e.isZero_iff.mp ((hd R (ULift.{w} M) n j).2 hj)

theorem referenceDiskHomology (n j : ℕ) :
    (j = n → Nonempty (relativeHomology R M (referenceDiskPair.{w} n) (j : ℤ) ≃ₗ[R] M)) ∧
    (j ≠ n → IsZero (relativeHomology R M (referenceDiskPair.{w} n) (j : ℤ))) :=
  referenceDiskHomology_of R M P202.SpheresDisks.diskHomology n j

end P202.Homology.DiskBridge


namespace P202.Homology.CellLocalization
open P202.Cellular P202Specs.CellularChains P202Specs.RelativeSingularChains
open P202Specs.SingularChains P202Specs.ChainLES
variable (X : Type w) [TopologicalSpace X] [CWStructure X]

/-- The lower skeleton, with exactly the cells of dimension less than n. -/
def skeletalSubcomplex (n : ℕ) : Subcomplex X where
  cells m := { c | m < n }
  contains_closures := by
    intro m c hm x hx
    rw [P202.Topology.closureOpenCell m c] at hx
    obtain ⟨y, rfl⟩ := hx
    have hmem := P202.Topology.skeletonLT_mono (Nat.succ_le_of_lt hm)
      (P202.Topology.characteristic_mem_skeletonLT m c y)
    obtain ⟨k, hk, d, hd⟩ := by
      simpa only [skeletonLT, mem_iUnion] using hmem
    exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨⟨d, hk⟩, hd⟩⟩

@[simp] lemma skeletalSubcomplex_carrier (n : ℕ) :
    (skeletalSubcomplex X n).carrier = skeletonLT X n := by
  ext x
  simp only [Subcomplex.carrier, skeletalSubcomplex, skeletonLT, mem_iUnion]
  constructor
  · rintro ⟨m, ⟨c, hmc⟩, hx⟩
    exact ⟨m, hmc, c, hx⟩
  · rintro ⟨m, hm, c, hx⟩
    exact ⟨m, ⟨c, hm⟩, hx⟩

lemma lowerSkeleton_closed (n : ℕ) : IsClosed (skeletalPair X n).subspace := by
  have h := P202.Topology.subcomplexClosed (skeletalSubcomplex X n)
  rw [skeletalSubcomplex_carrier] at h
  exact h.preimage continuous_subtype_val

/-- The old skeleton with all open radial collars attached. -/
def collarNeighborhood (n : ℕ) : Set (skeletalSpace X (n+1)) :=
  P202.Topology.neighborhoodAttachment (skeletalSubcomplex X n) n univ

lemma collarNeighborhood_open (n : ℕ) : IsOpen (collarNeighborhood X n) := by
  exact P202.Topology.isOpen_neighborhoodAttachment
    P202.Topology.closureOpenCell _ n isOpen_univ (by simp)

lemma collarNeighborhood_contains (n : ℕ) :
    (skeletalPair X n).subspace ⊆ collarNeighborhood X n := by
  intro x hx
  apply P202.Topology.neighborhoodAttachment_contains
    P202.Topology.closureOpenCell _ n (by simp)
  rwa [skeletalSubcomplex_carrier]

lemma collarNeighborhood_deformation (n : ℕ) :
    StrongDeformationRetracts (skeletalPair X n).subspace (collarNeighborhood X n) := by
  let W : Set (skeletonLT X n) := univ
  let H : C(W × Interval, W) :=
    ⟨fun p => p.1, continuous_fst⟩
  obtain ⟨H', hzero, hone, hfix, _⟩ :=
    P202.Topology.exists_neighborhoodAttachment_homotopy
      P202.Topology.closureOpenCell (skeletalSubcomplex X n) n isOpen_univ
      (by simp) H (by intro x; rfl)
      (by intro x; change x.1.1 ∈ (skeletalSubcomplex X n).carrier;
          simpa only [skeletalSubcomplex_carrier] using x.1.2)
      (by intros; rfl)
  refine ⟨collarNeighborhood_contains X n, H', hzero, ?_, ?_⟩
  · intro x
    change (H' (x, 1)).1.1 ∈ skeletonLT X n
    simpa only [skeletalSubcomplex_carrier] using hone x
  · intro x t hx
    change x.1.1 ∈ skeletonLT X n at hx
    exact hfix x t (by simpa only [skeletalSubcomplex_carrier] using hx)

/-- All open n-cells are simultaneously an open disjoint union in the next skeleton. -/
def interiorSource (n : ℕ) : (Σ _ : Cell X n, OpenDisk n) →
    (skeletonLT X n ⊕ (Σ _ : Cell X n, Disk n)) :=
  fun p => Sum.inr ⟨p.1, interiorInclusion n p.2⟩

lemma interiorSource_openEmbedding (n : ℕ) : IsOpenEmbedding (interiorSource X n) := by
  have h : IsOpenEmbedding (interiorInclusion n) :=
    IsOpenEmbedding.of_isEmbedding_isOpenMap (IsEmbedding.inclusion Metric.ball_subset_closedBall)
      (Metric.isOpen_ball.isOpenMap_inclusion Metric.ball_subset_closedBall)
  change IsOpenEmbedding (Sum.inr ∘ (@Sigma.map (Cell X n) (Cell X n)
    (fun _ => OpenDisk n) (fun _ => Disk n) id (fun _ => interiorInclusion n)))
  exact IsOpenEmbedding.inr.comp
    ((isOpenEmbedding_sigmaMap Function.injective_id).mpr (fun _ => h))

lemma attachment_interior_fiber (n : ℕ) (p : Σ _ : Cell X n, OpenDisk n)
    (q : skeletonLT X n ⊕ (Σ _ : Cell X n, Disk n))
    (he : attachmentProjection X CWStructure.boundary_lands n q =
      attachmentProjection X CWStructure.boundary_lands n (interiorSource X n p)) :
    q = interiorSource X n p := by
  rcases p with ⟨c, x⟩
  cases q with
  | inl y =>
    exfalso
    apply P202.Topology.openCell_not_mem_skeletonLT (x := interiorMap X n c x)
      (mem_range_self x)
    have hv : y.1 = interiorMap X n c x := congrArg Subtype.val he
    rw [← hv]
    exact y.2
  | inr q =>
    rcases q with ⟨d, y⟩
    have hev : interiorMap X n c x = characteristic X n d y :=
      (congrArg Subtype.val he).symm
    obtain ⟨hcd, hxy⟩ := P202.Topology.characteristic_interior_fiber x y hev
    subst d
    simp only [interiorSource, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    exact hxy.symm

def cellInteriorMap (n : ℕ) : (Σ _ : Cell X n, OpenDisk n) →
    {x : skeletalSpace X (n+1) // x ∉ (skeletalPair X n).subspace} :=
  fun p => ⟨diskToSkeleton X CWStructure.boundary_lands n p.1 (interiorInclusion n p.2),
    P202.Topology.openCell_not_mem_skeletonLT (mem_range_self p.2)⟩

lemma cellInteriorMap_bijective (n : ℕ) : Function.Bijective (cellInteriorMap X n) := by
  constructor
  · intro p q hpq
    have he : attachmentProjection X CWStructure.boundary_lands n (interiorSource X n p) =
        attachmentProjection X CWStructure.boundary_lands n (interiorSource X n q) :=
      congrArg Subtype.val hpq
    exact (interiorSource_openEmbedding X n).injective
      (attachment_interior_fiber X n q (interiorSource X n p) he)
  · intro x
    obtain ⟨p, hp⟩ := (CWStructure.attachment_quotient n).surjective x.1
    cases p with
    | inl y => exact (x.2 (by rw [← hp]; exact y.2)).elim
    | inr p =>
      rcases p with ⟨c, y⟩
      rcases P202.Topology.disk_interior_or_boundary n y with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨⟨c, y⟩, Subtype.ext hp⟩
      · exact (x.2 (by rw [← hp]; exact CWStructure.boundary_lands n c (mem_univ y))).elim

lemma cellInteriorMap_continuous (n : ℕ) : Continuous (cellInteriorMap X n) := by
  apply Continuous.subtype_mk
  exact (CWStructure.attachment_quotient n).continuous.comp
    (interiorSource_openEmbedding X n).continuous

lemma cellInteriorMap_open (n : ℕ) : IsOpenMap (cellInteriorMap X n) := by
  intro U hU
  let q := attachmentProjection X CWStructure.boundary_lands n
  let V := interiorSource X n '' U
  have hV : IsOpen V := (interiorSource_openEmbedding X n).isOpenMap U hU
  have hsat : ∀ a b, q a = q b → (a ∈ V ↔ b ∈ V) := by
    intro a b hab
    constructor
    · rintro ⟨p, hp, hpa⟩
      have hbp : b = interiorSource X n p :=
        attachment_interior_fiber X n p b (hab.symm.trans (congrArg q hpa).symm)
      exact ⟨p, hp, hbp.symm⟩
    · rintro ⟨p, hp, hpb⟩
      have hap : a = interiorSource X n p :=
        attachment_interior_fiber X n p a (hab.trans (congrArg q hpb).symm)
      exact ⟨p, hp, hap.symm⟩
  have hqV : IsOpen (q '' V) :=
    P202.Topology.isOpen_image_of_saturated (CWStructure.attachment_quotient n) hV hsat
  have he : cellInteriorMap X n '' U = Subtype.val ⁻¹' (q '' V) := by
    ext x
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨interiorSource X n p, ⟨p, hp, rfl⟩, rfl⟩
    · rintro ⟨a, ⟨p, hp, rfl⟩, hpa⟩
      exact ⟨p, hp, Subtype.ext hpa⟩
  rw [he]
  exact hqV.preimage continuous_subtype_val

def cellInteriorHomeomorph (n : ℕ) : (Σ _ : Cell X n, OpenDisk n) ≃ₜ
    {x : skeletalSpace X (n+1) // x ∉ (skeletalPair X n).subspace} :=
  (Equiv.ofBijective (cellInteriorMap X n) (cellInteriorMap_bijective X n)).toHomeomorphOfContinuousOpen (cellInteriorMap_continuous X n) (cellInteriorMap_open X n)

/-- The disjoint family of characteristic disk pairs before attachment. -/
def characteristicDiskSumPair (n : ℕ) : Pair.{w} :=
  ⟨TopCat.of (Σ _ : Cell X n, Disk n), {p | ‖p.2.1‖ = 1}⟩

def characteristicDiskSumMap (n : ℕ) : characteristicDiskSumPair X n ⟶ skeletalPair X n where
  map := TopCat.ofHom ⟨fun p => diskToSkeleton X CWStructure.boundary_lands n p.1 p.2,
    continuous_sigma (fun c => P202.Topology.continuous_diskToSkeleton n c)⟩
  mapsTo := by
    intro p hp
    change ‖p.2.1‖ = 1 at hp
    exact CWStructure.boundary_lands n p.1 (Set.mem_univ ⟨p.2.1, by
      simpa only [Metric.mem_sphere, dist_zero_right] using hp⟩)

lemma characteristicDiskSumMap_preimage_lower (n : ℕ) :
    (characteristicDiskSumMap X n).map ⁻¹' (skeletalPair X n).subspace =
      (characteristicDiskSumPair X n).subspace := by
  ext p
  constructor
  · intro hp
    rcases P202.Topology.disk_interior_or_boundary n p.2 with ⟨y, hy⟩ | ⟨y, hy⟩
    · exfalso
      apply P202.Topology.openCell_not_mem_skeletonLT (x := interiorMap X n p.1 y)
        (mem_range_self y)
      change characteristic X n p.1 p.2 ∈ skeletonLT X n at hp
      rwa [← hy] at hp
    · change ‖p.2.1‖ = 1
      rw [← hy]
      exact P202.Topology.Collar.norm_boundaryInclusion n y
  · intro hp
    exact (characteristicDiskSumMap X n).mapsTo hp

def diskSumCollar (n : ℕ) : Set (characteristicDiskSumPair X n).space :=
  {p | 1 / 2 < ‖p.2.1‖}

lemma diskSumCollar_open (n : ℕ) : IsOpen (diskSumCollar X n) := by
  apply isOpen_sigma_iff.mpr
  intro c
  exact isOpen_lt continuous_const continuous_subtype_val.norm

lemma diskSumBoundary_closed (n : ℕ) : IsClosed (characteristicDiskSumPair X n).subspace := by
  apply isClosed_sigma_iff.mpr
  intro c
  exact isClosed_eq continuous_subtype_val.norm continuous_const

lemma diskSumBoundary_subset_collar (n : ℕ) :
    (characteristicDiskSumPair X n).subspace ⊆ diskSumCollar X n := by
  intro p hp
  change 1 / 2 < ‖p.2.1‖
  change ‖p.2.1‖ = 1 at hp
  rw [hp]
  norm_num

lemma characteristicDiskSumMap_preimage_collar (n : ℕ) :
    (characteristicDiskSumMap X n).map ⁻¹' collarNeighborhood X n = diskSumCollar X n := by
  ext p
  have h := P202.Topology.mem_neighborhoodAttachment_projection
    P202.Topology.closureOpenCell (skeletalSubcomplex X n) n (W := univ) (by simp) (Sum.inr p)
  change _ ∈ collarNeighborhood X n ↔ 1 / 2 < ‖p.2.1‖
  rw [show (characteristicDiskSumMap X n).map p =
    attachmentProjection X CWStructure.boundary_lands n (Sum.inr p) from rfl]
  change attachmentProjection X CWStructure.boundary_lands n (Sum.inr p) ∈
    P202.Topology.neighborhoodAttachment (skeletalSubcomplex X n) n univ ↔ _
  rw [h]
  change (n < n ∨ p.2 ∈ P202.Topology.Collar.diskCollar n
    (attachingMap n p.1 ⁻¹' univ)) ↔ _
  simp only [lt_self_iff_false, false_or, preimage_univ]
  constructor
  · rintro ⟨x, _, hx⟩
    rw [← hx]
    exact x.2
  · intro hp
    exact ⟨⟨p.2, hp⟩, mem_univ _, rfl⟩

open P202.Topology.Collar

def outerDiskDeformation (n : ℕ) : C(OuterDisk n × Interval, OuterDisk n) where
  toFun p := ⟨diskPoint n (advance (diskRadius n p.1) p.2, diskDirection n p.1),
    diskPoint_mem_outer n _⟩
  continuous_toFun := ((continuous_diskPoint n).comp
    (((continuous_advance).comp ((continuous_diskRadius n).comp continuous_fst |>.prodMk
      continuous_snd)).prodMk ((continuous_diskDirection n).comp continuous_fst))).subtype_mk _

@[simp] lemma outerDiskDeformation_zero (n : ℕ) (x : OuterDisk n) :
    outerDiskDeformation n (x, 0) = x := by
  apply Subtype.ext
  change diskPoint n (advance (diskRadius n x) 0, diskDirection n x) = x.1
  rw [advance_zero]
  exact congrArg Subtype.val ((diskCoordinates n).symm_apply_apply x)

lemma outerDiskDeformation_one (n : ℕ) (x : OuterDisk n) :
    ‖(outerDiskDeformation n (x, 1)).1.1‖ = 1 := by
  change ‖(diskPoint n (advance (diskRadius n x) 1, diskDirection n x)).1‖ = 1
  rw [advance_one, norm_diskPoint]
  rfl

lemma outerDiskDeformation_fixed (n : ℕ) (x : OuterDisk n) (t : Interval)
    (hx : ‖x.1.1‖ = 1) : outerDiskDeformation n (x, t) = x := by
  have hr : advance (diskRadius n x) t = diskRadius n x := by
    apply Subtype.ext
    change min (‖x.1.1‖ + (t : ℝ)) 1 = ‖x.1.1‖
    rw [hx]
    exact min_eq_right (by linarith [t.2.1])
  apply Subtype.ext
  change diskPoint n (advance (diskRadius n x) t, diskDirection n x) = x.1
  rw [hr]
  exact congrArg Subtype.val ((diskCoordinates n).symm_apply_apply x)

def sumOuterDiskMap (n : ℕ) : (Σ _ : Cell X n, OuterDisk n) →
    (characteristicDiskSumPair X n).space := fun p => ⟨p.1, p.2.1⟩

lemma sumOuterDiskMap_embedding (n : ℕ) : IsEmbedding (sumOuterDiskMap X n) := by
  change IsEmbedding (@Sigma.map (Cell X n) (Cell X n) (fun _ => OuterDisk n)
    (fun _ => Disk n) id (fun _ => Subtype.val))
  exact (isEmbedding_sigmaMap Function.injective_id).mpr (fun _ => IsEmbedding.subtypeVal)

lemma sumOuterDiskMap_range (n : ℕ) : range (sumOuterDiskMap X n) = diskSumCollar X n := by
  ext p
  constructor
  · rintro ⟨⟨c, y⟩, rfl⟩
    exact y.2
  · intro hp
    exact ⟨⟨p.1, ⟨p.2, hp⟩⟩, rfl⟩

def sumOuterDiskHomeomorph (n : ℕ) :
    (Σ _ : Cell X n, OuterDisk n) ≃ₜ diskSumCollar X n :=
  (sumOuterDiskMap_embedding X n).toHomeomorph.trans
    (Homeomorph.setCongr (sumOuterDiskMap_range X n))

def sumOuterDiskDeformation (n : ℕ) : C((Σ _ : Cell X n, OuterDisk n) × Interval,
    (Σ _ : Cell X n, OuterDisk n)) where
  toFun p := ⟨p.1.1, outerDiskDeformation n (p.1.2, p.2)⟩
  continuous_toFun := by
    have hc : Continuous (fun p : (Σ _ : Cell X n, OuterDisk n × Interval) =>
        (⟨p.1, outerDiskDeformation n p.2⟩ : Σ _ : Cell X n, OuterDisk n)) :=
      continuous_sigma (fun c => continuous_sigmaMk.comp (outerDiskDeformation n).continuous)
    exact hc.comp (Homeomorph.sigmaProdDistrib (X := fun _ : Cell X n => OuterDisk n)
      (Y := Interval)).continuous

lemma diskSumCollar_deformation (n : ℕ) :
    StrongDeformationRetracts (characteristicDiskSumPair X n).subspace (diskSumCollar X n) := by
  let e := sumOuterDiskHomeomorph X n
  let H : C(diskSumCollar X n × Interval, diskSumCollar X n) :=
    ⟨fun p => e (sumOuterDiskDeformation X n (e.symm p.1, p.2)),
      e.continuous.comp ((sumOuterDiskDeformation X n).continuous.comp
        ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))⟩
  have he : ∀ (p : Σ _ : Cell X n, OuterDisk n), (e p).1 = ⟨p.1, p.2.1⟩ := by
    intro p
    rfl
  refine ⟨diskSumBoundary_subset_collar X n, H, ?_, ?_, ?_⟩
  · intro x
    apply e.symm.injective
    simp only [H, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
    have hp := outerDiskDeformation_zero n (e.symm x).2
    exact Sigma.ext (by rfl) (by simpa only [sumOuterDiskDeformation, ContinuousMap.coe_mk] using heq_of_eq hp)
  · intro x
    change ‖(e (sumOuterDiskDeformation X n (e.symm x, 1))).1.2.1‖ = 1
    rw [he]
    exact outerDiskDeformation_one n (e.symm x).2
  · intro x t hx
    have hx' : ‖(e.symm x).2.1.1‖ = 1 := by
      change ‖x.1.2.1‖ = 1 at hx
      have hxv : (e (e.symm x)).1 = x.1 := congrArg Subtype.val (e.apply_symm_apply x)
      rw [he] at hxv
      exact (congrArg (fun p : (characteristicDiskSumPair X n).space => ‖p.2.1‖) hxv).trans hx
    apply e.symm.injective
    simp only [H, ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
    have hp := outerDiskDeformation_fixed n (e.symm x).2 t hx'
    exact Sigma.ext (by rfl) (by simpa only [sumOuterDiskDeformation, ContinuousMap.coe_mk] using heq_of_eq hp)

def diskInteriorComplementMap (n : ℕ) : (Σ _ : Cell X n, OpenDisk n) →
    {p : (characteristicDiskSumPair X n).space // p ∉ (characteristicDiskSumPair X n).subspace} :=
  fun p => ⟨⟨p.1, interiorInclusion n p.2⟩, by
    change ‖p.2.1‖ ≠ 1
    exact ne_of_lt (by simpa only [Metric.mem_ball, dist_zero_right] using p.2.2)⟩

lemma diskInteriorComplementMap_embedding (n : ℕ) : IsEmbedding (diskInteriorComplementMap X n) := by
  apply IsEmbedding.subtypeVal.of_comp_iff.mp
  change IsEmbedding (@Sigma.map (Cell X n) (Cell X n) (fun _ => OpenDisk n)
    (fun _ => Disk n) id (fun _ => interiorInclusion n))
  exact (isEmbedding_sigmaMap Function.injective_id).mpr
    (fun _ => IsEmbedding.inclusion Metric.ball_subset_closedBall)

lemma diskInteriorComplementMap_surjective (n : ℕ) :
    Function.Surjective (diskInteriorComplementMap X n) := by
  intro p
  have hp : ‖p.1.2.1‖ < 1 := lt_of_le_of_ne
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using p.1.2.2)
    (by exact p.2)
  exact ⟨⟨p.1.1, ⟨p.1.2.1, by simpa only [Metric.mem_ball, dist_zero_right] using hp⟩⟩, rfl⟩

def diskInteriorComplementHomeomorph (n : ℕ) : (Σ _ : Cell X n, OpenDisk n) ≃ₜ
    {p : (characteristicDiskSumPair X n).space // p ∉ (characteristicDiskSumPair X n).subspace} :=
  (diskInteriorComplementMap_embedding X n).toHomeomorphOfSurjective
    (diskInteriorComplementMap_surjective X n)

def diskCollarExcision (n : ℕ) : P202Specs.Excision.Data.{w} where
  pair := ⟨(characteristicDiskSumPair X n).space, diskSumCollar X n⟩
  removed := (characteristicDiskSumPair X n).subspace
  subset := diskSumBoundary_subset_collar X n
  closure_subset := by
    rw [(diskSumBoundary_closed X n).closure_eq, (diskSumCollar_open X n).interior_eq]
    exact diskSumBoundary_subset_collar X n

def skeletalCollarExcision (n : ℕ) : P202Specs.Excision.Data.{w} where
  pair := ⟨(skeletalPair X n).space, collarNeighborhood X n⟩
  removed := (skeletalPair X n).subspace
  subset := collarNeighborhood_contains X n
  closure_subset := by
    rw [(lowerSkeleton_closed X n).closure_eq, (collarNeighborhood_open X n).interior_eq]
    exact collarNeighborhood_contains X n

def collarExcisionMap (n : ℕ) : P202Specs.Excision.Map
    (diskCollarExcision X n) (skeletalCollarExcision X n) where
  pairMap := ⟨(characteristicDiskSumMap X n).map, by
    intro p hp
    have he := characteristicDiskSumMap_preimage_collar X n
    change p ∈ (characteristicDiskSumMap X n).map ⁻¹' collarNeighborhood X n
    rwa [he]⟩
  outside := by
    intro p hp hq
    apply hp
    have he := characteristicDiskSumMap_preimage_lower X n
    change p ∈ (characteristicDiskSumPair X n).subspace
    rw [← he]
    exact hq

def complementHomeomorph (n : ℕ) : (diskCollarExcision X n).excised.space ≃ₜ
    (skeletalCollarExcision X n).excised.space :=
  (diskInteriorComplementHomeomorph X n).symm.trans (cellInteriorHomeomorph X n)

lemma complementHomeomorph_eq (n : ℕ) (p : (diskCollarExcision X n).excised.space) :
    complementHomeomorph X n p = (collarExcisionMap X n).excised.map p := by
  obtain ⟨q, rfl⟩ := (diskInteriorComplementHomeomorph X n).surjective p
  exact congrArg (fun z => cellInteriorHomeomorph X n z)
    ((diskInteriorComplementHomeomorph X n).symm_apply_apply q)

def complementPairIso (n : ℕ) : (diskCollarExcision X n).excised ≅
    (skeletalCollarExcision X n).excised :=
  P202.GoodPairQuotient.pairIsoOfHomeomorph _ _ (complementHomeomorph X n) (by
    intro p
    rw [complementHomeomorph_eq]
    change p.1 ∈ diskSumCollar X n ↔
      (characteristicDiskSumMap X n).map p.1 ∈ collarNeighborhood X n
    exact (congrArg (fun s => p.1 ∈ s) (characteristicDiskSumMap_preimage_collar X n)).to_iff.symm)

lemma complementPairIso_hom (n : ℕ) :
    (complementPairIso X n).hom = (collarExcisionMap X n).excised := by
  apply PairMap.ext
  ext p
  exact complementHomeomorph_eq X n p

section Algebra
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

lemma relativeMap_isIso_of_absolute {P Q : Pair.{w}} (f : P ⟶ Q)
    (hsub : ∀ k : ℤ, IsIso (homologyMap ((ordinaryFunctor R M).map f.restrict) k))
    (hspace : ∀ k : ℤ, IsIso (homologyMap ((ordinaryFunctor R M).map f.map) k)) (k : ℤ) :
    IsIso (homologyMap (relativeMap (ordinaryFunctor R M) f) k) := by
  let hs P := HomologicalComplex.shortExact_of_degreewise_shortExact
    (sequence (ordinaryFunctor R M) P)
    (P202.RelativeSingularChains.sequence_shortExact (ordinaryFunctor R M) P)
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (sequenceMap (ordinaryFunctor R M) f) (hs P) (hs Q) k
  · have := hsub k
    change Epi (homologyMap ((ordinaryFunctor R M).map f.restrict) k)
    infer_instance
  · exact hspace k
  · intro j _
    exact hsub j
  · intro j _
    have := hspace j
    change Mono (homologyMap ((ordinaryFunctor R M).map f.map) j)
    infer_instance

/-- Enlarging a second term along an actual SDR preserves relative homology,
including empty spaces and second terms. -/
lemma enlargement_isIso (P : Pair.{w}) (N : Set P.space)
    (h : StrongDeformationRetracts P.subspace N) (k : ℤ) :
    IsIso (homologyMap (relativeMap (ordinaryFunctor R M)
      (⟨𝟙 P.space, h.1⟩ : P ⟶ ⟨P.space, N⟩)) k) := by
  rcases h with ⟨hAN, H, hzero, hone, hfix⟩
  let f : P ⟶ (⟨P.space, N⟩ : Pair.{w}) := ⟨𝟙 _, hAN⟩
  let r : (⟨P.space, N⟩ : Pair.{w}).sub ⟶ P.sub :=
    TopCat.ofHom ⟨fun x => ⟨(H (x, 1)).1, hone x⟩,
      (continuous_subtype_val.comp (H.continuous.comp
        (continuous_id.prodMk continuous_const))).subtype_mk _⟩
  have hfr : TopCat.Homotopy (f.restrict ≫ r) (𝟙 P.sub) := by
    refine ⟨⟨fun p => p.2, continuous_snd⟩, ?_, ?_⟩
    · intro a
      apply Subtype.ext
      exact (congrArg Subtype.val (hfix ⟨a.1, hAN a.2⟩ 1 a.2)).symm
    · intro a
      rfl
  have hrf : TopCat.Homotopy (r ≫ f.restrict) (𝟙 (⟨P.space, N⟩ : Pair.{w}).sub) := by
    apply TopCat.Homotopy.symm
    refine ⟨⟨fun p => H (p.2, p.1), H.continuous.comp (continuous_snd.prodMk continuous_fst)⟩, ?_, ?_⟩
    · exact hzero
    · intro x
      apply Subtype.ext
      rfl
  apply relativeMap_isIso_of_absolute R M f
  · intro j
    exact (P202.PrismHomotopy.homologyIso R M f.restrict r hfr hrf j).1
  · intro j
    change IsIso ((homologyFunctor R M j).map (𝟙 P.space))
    infer_instance

lemma collarExcisionMap_isIso (n j : ℕ) :
    IsIso (homologyMap (relativeMap (ordinaryFunctor R M) (collarExcisionMap X n).pairMap)
      (j : ℤ)) := by
  let F := relativeHomologyFunctor R M (j : ℤ)
  haveI : IsIso (F.map (diskCollarExcision X n).inclusion) :=
    P202.Homology.Coefficients.excision R M (diskCollarExcision X n) j
  haveI : IsIso (F.map (skeletalCollarExcision X n).inclusion) :=
    P202.Homology.Coefficients.excision R M (skeletalCollarExcision X n) j
  haveI : IsIso (F.map (collarExcisionMap X n).excised) := by
    rw [← complementPairIso_hom]
    infer_instance
  have h := congrArg F.map (collarExcisionMap X n).square
  simp only [Functor.map_comp] at h
  haveI : IsIso (F.map (diskCollarExcision X n).inclusion ≫
      F.map (collarExcisionMap X n).pairMap) := by
    rw [h]
    infer_instance
  change IsIso (F.map (collarExcisionMap X n).pairMap)
  exact IsIso.of_isIso_comp_left (F.map (diskCollarExcision X n).inclusion) _

/-- Characteristic disks localize the skeletal relative groups, in all degrees
and with arbitrary module coefficients and arbitrarily many cells. -/
lemma characteristicDiskSumMap_isIso (n j : ℕ) :
    IsIso ((relativeHomologyFunctor R M (j : ℤ)).map (characteristicDiskSumMap X n)) := by
  let a : characteristicDiskSumPair X n ⟶ (diskCollarExcision X n).pair :=
    ⟨𝟙 _, diskSumBoundary_subset_collar X n⟩
  let b : skeletalPair X n ⟶ (skeletalCollarExcision X n).pair :=
    ⟨𝟙 _, collarNeighborhood_contains X n⟩
  let F := relativeHomologyFunctor R M (j : ℤ)
  haveI : IsIso (F.map a) := enlargement_isIso R M _ _ (diskSumCollar_deformation X n) _
  haveI : IsIso (F.map b) := enlargement_isIso R M _ _ (collarNeighborhood_deformation X n) _
  haveI : IsIso (F.map (collarExcisionMap X n).pairMap) := collarExcisionMap_isIso X R M n j
  have hs : characteristicDiskSumMap X n ≫ b = a ≫ (collarExcisionMap X n).pairMap := by
    apply PairMap.ext
    rfl
  have h := congrArg F.map hs
  simp only [Functor.map_comp] at h
  haveI : IsIso (F.map (characteristicDiskSumMap X n) ≫ F.map b) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.map b)

end Algebra
end P202.Homology.CellLocalization


namespace P202.Homology.DiskSumBridge
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains

/-- The disjoint family of reference disk pairs, before forgetting the lifts. -/
abbrev liftedDiskSumPair (I : Type w) (n : ℕ) : Pair.{w} :=
  P202.Homology.CellSums.sumPair I (referenceDiskPair.{w} n)

/-- The same family represented by unlifted Euclidean disks. -/
def unliftedDiskSumPair (I : Type w) (n : ℕ) : Pair.{w} :=
  ⟨TopCat.of (Σ _ : I, Disk n), {p | ‖p.2.val‖ = 1}⟩

/-- Forgetting each universe lift is a homeomorphism of the disjoint families. -/
def diskSumHomeomorph (I : Type w) (n : ℕ) :
    (liftedDiskSumPair I n).space ≃ₜ (unliftedDiskSumPair I n).space where
  toEquiv := Equiv.sigmaCongrRight (fun _ => Equiv.ulift)
  continuous_toFun := continuous_sigma (fun _ => continuous_sigmaMk.comp continuous_uliftDown)
  continuous_invFun := continuous_sigma (fun _ => continuous_sigmaMk.comp continuous_uliftUp)

/-- The preceding homeomorphism preserves the boundary of every summand. -/
def diskSumPairIso (I : Type w) (n : ℕ) :
    liftedDiskSumPair I n ≅ unliftedDiskSumPair I n where
  hom := ⟨TopCat.ofHom ⟨diskSumHomeomorph I n, (diskSumHomeomorph I n).continuous⟩, fun _ h => h⟩
  inv := ⟨TopCat.ofHom ⟨(diskSumHomeomorph I n).symm, (diskSumHomeomorph I n).symm.continuous⟩, fun _ h => h⟩
  hom_inv_id := by
    apply PairMap.ext
    apply TopCat.hom_ext
    ext p
    exact (diskSumHomeomorph I n).left_inv p
  inv_hom_id := by
    apply PairMap.ext
    apply TopCat.hom_ext
    ext p
    exact (diskSumHomeomorph I n).right_inv p

/-- Inclusion of a lifted reference disk in its disjoint family. -/
abbrev referenceDiskSumInclusion (I : Type w) (n : ℕ) (i : I) :
    referenceDiskPair.{w} n ⟶ liftedDiskSumPair I n :=
  P202.Homology.CellSums.sumPairInclusion I (referenceDiskPair.{w} n) i

/-- After forgetting the lifts, a summand inclusion inserts its unlifted disk. -/
@[simp] lemma referenceDiskSumInclusion_comp (I : Type w) (n : ℕ) (i : I)
    (x : (referenceDiskPair.{w} n).space) :
    ((referenceDiskSumInclusion I n i ≫ (diskSumPairIso I n).hom).map x) = ⟨i, x.down⟩ := rfl

/-- Inserting one reference disk and attaching its unlifted summand is exactly
its characteristic map as specified independently for the skeletal pair. -/
lemma referenceDiskSum_characteristic {X : Type w} [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) :
    referenceDiskSumInclusion (Cell X n) n c ≫ (diskSumPairIso (Cell X n) n).hom ≫
      P202.Homology.CellLocalization.characteristicDiskSumMap X n =
        characteristicPairMap n c := by
  apply PairMap.ext
  apply TopCat.hom_ext
  ext x
  rfl

/-- The lifted characteristic map is the same family of characteristic maps,
through the boundary-preserving homeomorphism of disjoint disk families. -/
def liftedCharacteristicMap (X : Type w) [TopologicalSpace X] [CWStructure X] (n : ℕ) :
    liftedDiskSumPair (Cell X n) n ⟶ skeletalPair X n :=
  (diskSumPairIso (Cell X n) n).hom ≫
    P202.Homology.CellLocalization.characteristicDiskSumMap X n

lemma liftedCharacteristicMap_summand (X : Type w) [TopologicalSpace X] [CWStructure X]
    (n : ℕ) (c : Cell X n) :
    referenceDiskSumInclusion (Cell X n) n c ≫ liftedCharacteristicMap X n =
      characteristicPairMap n c := referenceDiskSum_characteristic n c

lemma liftedCharacteristicMap_homology_isIso (X : Type w) [TopologicalSpace X]
    [CWStructure X] (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (j : ℤ)
    [IsIso ((relativeHomologyFunctor R M j).map
      (P202.Homology.CellLocalization.characteristicDiskSumMap X n))] :
    IsIso ((relativeHomologyFunctor R M j).map (liftedCharacteristicMap X n)) := by
  dsimp only [liftedCharacteristicMap]
  rw [Functor.map_comp]
  infer_instance

lemma liftedCharacteristicMap_isIso (X : Type w) [TopologicalSpace X]
    [CWStructure X] (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    (n j : ℕ) :
    IsIso ((relativeHomologyFunctor R M (j : ℤ)).map (liftedCharacteristicMap X n)) := by
  haveI := P202.Homology.CellLocalization.characteristicDiskSumMap_isIso X R M n j
  exact liftedCharacteristicMap_homology_isIso X R M n (j : ℤ)

end P202.Homology.DiskSumBridge


namespace P202.Homology
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains CellSums DiskSumBridge
variable (X : Type w) [TopologicalSpace X] [CWStructure X]
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]

/-- The characteristic maps identify the skeletal relative group with a direct
sum of relative disk groups. -/
def cellGroupSumIso (n j : ℕ)
    :
    (sumModuleFunctor R (Cell X n)).obj
      (relativeHomology R M (referenceDiskPair.{w} n) (j : ℤ)) ≅
        relativeHomology R M (skeletalPair X n) (j : ℤ) :=
  by
    haveI := CellLocalization.characteristicDiskSumMap_isIso X R M n j
    haveI := liftedCharacteristicMap_homology_isIso X R M n (j : ℤ)
    exact sumRelativeHomologyIso R M (Cell X n) (referenceDiskPair.{w} n) (j : ℤ) ≪≫
      asIso ((relativeHomologyFunctor R M (j : ℤ)).map (liftedCharacteristicMap X n))

/-- Cell coordinates for any common choice of a disk orientation. -/
def orientedCellEquiv (n : ℕ)
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)) :
    chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M) :=
  (cellGroupSumIso X R M n n).symm.toLinearEquiv.trans
    (Finsupp.mapRange.linearEquiv g.symm)


lemma cellGroupSumIso_single (n j : ℕ) (c : Cell X n)
    (a : relativeHomology R M (referenceDiskPair.{w} n) (j : ℤ)) :
    (cellGroupSumIso X R M n j).hom (Finsupp.single c a) =
      (relativeHomologyFunctor R M (j : ℤ)).map (characteristicPairMap n c) a := by
  change (relativeHomologyFunctor R M (j : ℤ)).map (liftedCharacteristicMap X n)
      ((sumRelativeHomologyIso R M (Cell X n) (referenceDiskPair.{w} n) (j : ℤ)).hom
        (Finsupp.single c a)) = _
  rw [sumRelativeHomologyIso_single]
  change ((relativeHomologyFunctor R M (j : ℤ)).map
      (sumPairInclusion (Cell X n) (referenceDiskPair.{w} n) c) ≫
    (relativeHomologyFunctor R M (j : ℤ)).map (liftedCharacteristicMap X n)) a = _
  rw [← Functor.map_comp, liftedCharacteristicMap_summand]

lemma orientedCellEquiv_characteristic (n : ℕ)
    (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ))
    (c : Cell X n) (m : M) :
    orientedCellEquiv X R M n g
        ((relativeHomologyFunctor R M (n : ℤ)).map (characteristicPairMap n c) (g m)) =
      Finsupp.single c m := by
  rw [← cellGroupSumIso_single X R M n n c (g m)]
  change Finsupp.mapRange.linearEquiv g.symm
      ((cellGroupSumIso X R M n n).inv ((cellGroupSumIso X R M n n).hom
        (Finsupp.single c (g m)))) = _
  rw [ModuleCat.inv_hom_apply]
  simp

end P202.Homology

namespace P202.Homology
open P202.Cellular P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CellularChains CellSums

/-- The cell summands are exactly the characteristic relative disk classes. -/
theorem cellularOrientedCoordinates :
    ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
      (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ)
      (g : M ≃ₗ[R] relativeHomology R M (referenceDiskPair.{w} n) (n : ℤ)),
      ∃ e : chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M),
        ∀ c m, e ((relativeHomologyFunctor R M (n : ℤ)).map
          (characteristicPairMap n c) (g m)) = Finsupp.single c m := by
  intro X _ _ R _ M _ _ n g
  exact ⟨orientedCellEquiv X R M n g, orientedCellEquiv_characteristic X R M n g⟩

/-- A direct sum, with no restriction on the number of cells. -/
theorem cellularCellGroups :
    ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
      (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n : ℕ),
      Nonempty (chainGroup X R M n ≃ₗ[R] (Cell X n →₀ M)) := by
  intro X _ _ R _ M _ _ n
  obtain ⟨g⟩ := (DiskBridge.referenceDiskHomology R M n n).1 rfl
  exact ⟨orientedCellEquiv X R M n g.symm⟩

/-- All other nonnegative degrees of a consecutive skeletal pair vanish. -/
theorem cellularRelativeVanishing :
    ∀ (X : Type w) [TopologicalSpace X] [CWStructure X]
      (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] (n j : ℕ),
      j ≠ n → IsZero (relativeHomology R M (skeletalPair X n) (j : ℤ)) := by
  intro X _ _ R _ M _ _ n j hjn
  apply (cellGroupSumIso X R M n j).isZero_iff.mp
  exact (sumModuleFunctor R (Cell X n)).map_isZero
    ((DiskBridge.referenceDiskHomology R M n j).2 hjn)

end P202.Homology

