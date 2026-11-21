import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CompactSupportMayerVietoris
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Products.RelativeCupProduct
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.Pairs
import Mathlib.Algebra.Exact.Basic
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.CompactSupportDualityMap
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.MayerVietoris
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Classical
open CategoryTheory
universe u v w t
namespace P202.CompactSupportMV
open P202Specs.CompactSupport

/-! Internal support and finite-stage constructions retained from the earlier
partial implementation. These are implementation helpers; the frozen independent
interface is `P202Specs.CompactSupportMayerVietoris`. -/
open P202Specs.CompactSupport

/-- The directed index used for the finite-support sequences. -/
abbrev SupportPair (M : Type v) [TopologicalSpace M] (U V : Set M) :=
  Support U × Support V

/-- Union of the two actual ambient compact images. -/
def unionSupport (M : Type v) [TopologicalSpace M] (U V : Set M)
    (s : SupportPair M U V) : Support M :=
  ambientSupport M U s.1 ⊔ ambientSupport M V s.2

/-- Intersection of the two actual ambient compact images. -/
def intersectionSupport (M : Type v) [TopologicalSpace M] [T2Space M]
    (U V : Set M) (s : SupportPair M U V) : Support M :=
  ambientSupport M U s.1 ⊓ ambientSupport M V s.2

/-- A linear directed system, with its laws and its actual component modules. -/
structure ModuleSystem (R : Type u) [CommRing R] (ι : Type v) [Preorder ι] where
  obj : ι → ModuleCat.{w} R
  transition : ∀ i j, i ≤ j → obj i →ₗ[R] obj j
  self : ∀ i x, transition i i le_rfl x = x
  trans : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) x,
    transition j k hjk (transition i j hij x) = transition i k (hij.trans hjk) x

namespace ModuleSystem
variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι]

instance (F : ModuleSystem.{u,v,w} R ι) :
    DirectedSystem (fun i => ↥(F.obj i)) (fun i j h => (F.transition i j h).toFun) where
  map_self := F.self
  map_map := fun {k j i} hij hjk x => F.trans i j k hij hjk x

abbrev Limit (F : ModuleSystem.{u,v,w} R ι) :=
  Module.DirectLimit (fun i => ↥(F.obj i)) F.transition

/-- A morphism of systems, not merely a family of unrelated maps. -/
structure Map (F : ModuleSystem.{u,v,w} R ι) (G : ModuleSystem.{u,v,t} R ι) where
  component : ∀ i, F.obj i →ₗ[R] G.obj i
  comm : ∀ i j h, (component j).comp (F.transition i j h) =
    (G.transition i j h).comp (component i)

def Map.limit {F : ModuleSystem.{u,v,w} R ι} {G : ModuleSystem.{u,v,t} R ι}
    (f : Map F G) : F.Limit →ₗ[R] G.Limit :=
  Module.DirectLimit.map f.component f.comm

variable {κ : Type t} [Preorder κ]

/-- Restrict a directed system along a monotone map of indices. -/
def reindex (F : ModuleSystem.{u,v,w} R ι) (φ : κ → ι) (hφ : Monotone φ) :
    ModuleSystem.{u,t,w} R κ where
  obj i := F.obj (φ i)
  transition i j h := F.transition (φ i) (φ j) (hφ h)
  self i x := F.self (φ i) x
  trans i j k hij hjk x := F.trans (φ i) (φ j) (φ k) (hφ hij) (hφ hjk) x

/-- The canonical comparison induced by reindexing. -/
def reindexMap (F : ModuleSystem.{u,v,w} R ι) (φ : κ → ι) (hφ : Monotone φ) :
    (F.reindex φ hφ).Limit →ₗ[R] F.Limit :=
  Module.DirectLimit.lift R κ _ _
    (fun i => Module.DirectLimit.of R ι _ F.transition (φ i))
    (by intro i j h x; exact Module.DirectLimit.of_f)

@[simp] theorem reindexMap_of (F : ModuleSystem.{u,v,w} R ι)
    (φ : κ → ι) (hφ : Monotone φ) (i : κ) (x : F.obj (φ i)) :
    F.reindexMap φ hφ
      (Module.DirectLimit.of R κ _ (F.reindex φ hφ).transition i x) =
      Module.DirectLimit.of R ι _ F.transition (φ i) x :=
  Module.DirectLimit.lift_of _ _ _

end ModuleSystem

/-- The original supported cohomology system, exposed in the common module
system interface without replacing its modules or maps. -/
def cohomologySystem (R : Type u) [CommRing R] (M : Type v)
    [TopologicalSpace M] (p : ℤ) : ModuleSystem R (Support M) where
  obj K := supportedCohomology R M p K
  transition := transition R M p
  self K x := DirectedSystem.map_self' (transition R M p) x
  trans K L N hKL hLN x := DirectedSystem.map_map' (transition R M p) hKL hLN x

lemma unionSupport_mono (M : Type v) [TopologicalSpace M] (U V : Set M) :
    Monotone (unionSupport M U V) := by
  intro s t h
  exact sup_le_sup (ambientSupport_mono M U h.1) (ambientSupport_mono M V h.2)

lemma intersectionSupport_mono (M : Type v) [TopologicalSpace M] [T2Space M]
    (U V : Set M) : Monotone (intersectionSupport M U V) := by
  intro s t h
  exact inf_le_inf (ambientSupport_mono M U h.1) (ambientSupport_mono M V h.2)

lemma intersectionSupport_subset (M : Type v) [TopologicalSpace M] [T2Space M]
    (U V : Set M) (s : SupportPair M U V) :
    (intersectionSupport M U V s : Set M) ⊆ U ∩ V := by
  rintro x ⟨⟨a, _, rfl⟩, b, _, hb⟩
  exact ⟨a.property, hb ▸ b.property⟩

/-- The intersection compact as a compact in the intersection subspace,
using the original subspace topology. -/
def intersectionIn (M : Type v) [TopologicalSpace M] [T2Space M]
    (U V : Set M) (s : SupportPair M U V) : Support ↥(U ∩ V) where
  carrier := Subtype.val ⁻¹' (intersectionSupport M U V s : Set M)
  isCompact' := (Topology.IsInducing.subtypeVal (t := U ∩ V)).isCompact_preimage'
    (intersectionSupport M U V s).isCompact
    (by
      intro x hx
      exact ⟨⟨x, intersectionSupport_subset M U V s hx⟩, rfl⟩)

lemma ambient_intersectionIn (M : Type v) [TopologicalSpace M] [T2Space M]
    (U V : Set M) (s : SupportPair M U V) :
    ambientSupport M (U ∩ V) (intersectionIn M U V s) = intersectionSupport M U V s := by
  apply TopologicalSpace.Compacts.ext
  apply Set.image_preimage_eq_of_subset
  intro x hx
  exact ⟨⟨x, intersectionSupport_subset M U V s hx⟩, rfl⟩

lemma intersectionIn_mono (M : Type v) [TopologicalSpace M] [T2Space M]
    (U V : Set M) : Monotone (intersectionIn M U V) := by
  intro s t h x hx
  exact intersectionSupport_mono M U V h hx

/-! The finite-stage sequence for two arbitrary subspaces.  In the compact
support application these are the complements of the two compact supports. -/
section FiniteStage
open CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.SingularChains P202Specs.RelativeSingularChains
  P202Specs.CohomologyPairs P202Specs.RelativeCupProduct
variable (R : Type u) [CommRing R] (P : TwoSubspaces.{v})

abbrev intersectionPair : Pair.{v} := ⟨P.space, P.left ∩ P.right⟩

def leftIntersectionMap : intersectionPair P ⟶ P.leftPair :=
  ⟨𝟙 P.space, Set.inter_subset_left⟩
def rightIntersectionMap : intersectionPair P ⟶ P.rightPair :=
  ⟨𝟙 P.space, Set.inter_subset_right⟩

/-- A map respecting both subspaces respects their intersection. -/
def intersectionMap {P Q : TwoSubspaces.{v}} (f : P.Map Q) :
    intersectionPair P ⟶ intersectionPair Q :=
  ⟨f.map, fun _ h => ⟨f.left h.1, f.right h.2⟩⟩

/-- Quotienting by either subspace and then by their sum. -/
def leftQuotientToSum : ordinary R R P.leftPair ⟶ sumQuotient R P :=
  cokernel.desc _ (sumProjection R P) (by
    rw [show inclusion (ordinaryFunctor R R) P.leftPair = biprod.inl ≫ sumInclusion R P
      from (biprod.inl_desc _ _).symm, Category.assoc]
    simp only [sumProjection, cokernel.condition, comp_zero])
def rightQuotientToSum : ordinary R R P.rightPair ⟶ sumQuotient R P :=
  cokernel.desc _ (sumProjection R P) (by
    rw [show inclusion (ordinaryFunctor R R) P.rightPair = biprod.inr ≫ sumInclusion R P
      from (biprod.inr_desc _ _).symm, Category.assoc]
    simp only [sumProjection, cokernel.condition, comp_zero])

def sumToLeft : sumCochains R P ⟶ relativeCochains R R P.leftPair :=
  (dualComplexFunctor R R (.down ℤ)).map (leftQuotientToSum R P).op
def sumToRight : sumCochains R P ⟶ relativeCochains R R P.rightPair :=
  (dualComplexFunctor R R (.down ℤ)).map (rightQuotientToSum R P).op

def leftToIntersection : relativeCochains R R P.leftPair ⟶
    relativeCochains R R (intersectionPair P) :=
  (relativeCochainFunctor R R).map (leftIntersectionMap P).op
def rightToIntersection : relativeCochains R R P.rightPair ⟶
    relativeCochains R R (intersectionPair P) :=
  (relativeCochainFunctor R R).map (rightIntersectionMap P).op

lemma quotientToSum_square :
    relativeMap (ordinaryFunctor R R) (leftIntersectionMap P) ≫ leftQuotientToSum R P =
    relativeMap (ordinaryFunctor R R) (rightIntersectionMap P) ≫ rightQuotientToSum R P := by
  apply (cancel_epi (projection (ordinaryFunctor R R) (intersectionPair P))).mp
  simp only [← Category.assoc, projection_map]
  simp [leftQuotientToSum, rightQuotientToSum, leftIntersectionMap,
    rightIntersectionMap, Category.assoc, projection]

lemma sumToIntersection_square :
    sumToLeft R P ≫ leftToIntersection R P =
    sumToRight R P ≫ rightToIntersection R P := by
  change (dualComplexFunctor R R (.down ℤ)).map (leftQuotientToSum R P).op ≫
      (dualComplexFunctor R R (.down ℤ)).map
        (relativeMap (ordinaryFunctor R R) (leftIntersectionMap P)).op = _
  rw [← Functor.map_comp, ← op_comp, quotientToSum_square]
  rw [op_comp, Functor.map_comp]
  rfl

/-- Source convention: the first map is (a,-a), the second is addition. -/
def finiteSequence : ShortComplex (CochainComplex (ModuleCat.{max u v} R) ℤ) :=
  ShortComplex.mk (biprod.lift (sumToLeft R P) (-sumToRight R P))
    (biprod.desc (leftToIntersection R P) (rightToIntersection R P)) (by
      rw [biprod.lift_desc, Preadditive.neg_comp, sumToIntersection_square R P]
      exact add_neg_cancel _)

end FiniteStage

section CompactStage
open CategoryTheory.Limits HomologicalComplex
open P202Specs.RelativeSingularChains P202Specs.RelativeCupProduct
  P202Specs.CohomologyPairs P202Specs.LocalOrientation

/-- The two complements used in the source finite-support construction. -/
def supportComplements (M : Type v) [TopologicalSpace M] (K L : Support M) :
    TwoSubspaces.{v} := ⟨TopCat.of M, (K : Set M)ᶜ, (L : Set M)ᶜ⟩

lemma supportComplements_union (M : Type v) [TopologicalSpace M] [T2Space M]
    (K L : Support M) :
    (supportComplements M K L).unionPair = supportedPair M (K ⊓ L : Support M) := by
  apply congrArg (fun s => (⟨TopCat.of M, s⟩ : Pair))
  ext x
  simp [supportComplements, supportedPair] <;> tauto

lemma supportComplements_intersection (M : Type v) [TopologicalSpace M]
    (K L : Support M) :
    intersectionPair (supportComplements M K L) = supportedPair M (K ⊔ L : Support M) := by
  apply congrArg (fun s => (⟨TopCat.of M, s⟩ : Pair))
  ext x
  simp [supportComplements, supportedPair] <;> tauto

/-- The comparison has the original supported cochains as its source and the
actual dual of the sum quotient as its target. -/
def supportComparison (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] [T2Space M] (K L : Support M) :
    supportedCochains R M (K ⊓ L) ⟶ sumCochains R (supportComplements M K L) :=
  eqToHom (congrArg (relativeCochains R R) (supportComplements_union M K L).symm) ≫
    P202Specs.RelativeCupProduct.unionComparison R (supportComplements M K L)

end CompactStage

namespace Expected

/-- In fact every compact is exactly one of these unions, not just contained
in one. This includes a compact meeting neither or only one cover member. -/
def compactUnionCofinal : Prop := ∀ (M : Type v) [TopologicalSpace M] [T2Space M]
    (U V : Set M), IsOpen U → IsOpen V → U ∪ V = Set.univ →
    ∀ C : Support M, ∃ s : SupportPair M U V, unionSupport M U V s = C

/-- Every compact of the intersection is exactly an intersection of images
of compacts of the two pieces. The equality is in the original ambient space. -/
def compactIntersectionCofinal : Prop :=
  ∀ (M : Type v) [TopologicalSpace M] [T2Space M] (U V : Set M)
    (C : Support ↥(U ∩ V)),
    ∃ s : SupportPair M U V,
      intersectionSupport M U V s = ambientSupport M (U ∩ V) C

/-- Exactness is preserved by the genuine filtered module colimit. This
applies degree by degree, including degree zero and negative degrees; there
is no assumption of injectivity on any transition map. -/
def filteredExactness : Prop := ∀ (R : Type u) [CommRing R]
    (ι : Type v) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (F G H : ModuleSystem.{u,v,w} R ι)
    (f : F.Map G) (g : G.Map H),
    (∀ i, Function.Exact (f.component i) (g.component i)) →
      Function.Exact f.limit g.limit

/-- A monotone cofinal change of directed indices preserves the actual
module colimit, with the comparison fixed by its values on representatives. -/
def cofinalReindex : Prop := ∀ (R : Type u) [CommRing R]
    (ι : Type v) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (κ : Type t) [Preorder κ] [Nonempty κ] [IsDirectedOrder κ]
    (F : ModuleSystem.{u,v,w} R ι) (φ : κ → ι) (hφ : Monotone φ),
    (∀ i, ∃ j, i ≤ φ j) → Function.Bijective (F.reindexMap φ hφ)

/-- Reindexing by unions gives precisely compactly supported cohomology
of the union, in every integer degree. -/
def unionColimit : Prop := ∀ (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] [T2Space M] (U V : Set M),
    IsOpen U → IsOpen V → U ∪ V = Set.univ → ∀ p : ℤ,
      Function.Bijective ((cohomologySystem R M p).reindexMap
        (unionSupport M U V) (unionSupport_mono M U V))

/-- Reindexing by intersections gives precisely compactly supported
cohomology of the intersection, in every integer degree. -/
def intersectionColimit : Prop := ∀ (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] [T2Space M] (U V : Set M) (p : ℤ),
      Function.Bijective ((cohomologySystem R ↥(U ∩ V) p).reindexMap
        (intersectionIn M U V) (intersectionIn_mono M U V))


/-- The actual finite-support cochain sequence is short exact in every
integer degree, without openness or any restriction on the coefficient ring. -/
def finiteShortExact : Prop := ∀ (R : Type u) [CommRing R]
    (P : P202Specs.RelativeCupProduct.TwoSubspaces.{v}),
    P202Specs.ChainLES.DegreewiseShortExact (finiteSequence R P)

/-- The finite-stage long exact sequence uses the positive coboundary of the
left component of a lift, including degree zero. -/
def finiteLongExact : Prop := ∀ (R : Type u) [CommRing R]
    (P : P202Specs.RelativeCupProduct.TwoSubspaces.{v}),
    ∃ h : P202Specs.ChainLES.DegreewiseShortExact (finiteSequence R P),
      (∀ p : ℤ, (P202Specs.ChainLES.segment h p (p+1) (by simp)).Exact) ∧
      P202Specs.ChainLES.LiftsExist (finiteSequence R P) h ∧
      P202Specs.ChainLES.LiftFormula (finiteSequence R P) h ∧
      P202Specs.ChainLES.Independence (finiteSequence R P) h


/-- Compactness and Hausdorffness make the complements open, so the comparison
with support on the intersection is an isomorphism on cohomology in every degree. -/
def finiteSupportComparison : Prop := ∀ (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] [T2Space M] (K L : Support M) (p : ℤ),
    IsIso (HomologicalComplex.homologyMap (supportComparison R M K L) p)


/-- Naturality of the finite-stage connecting maps. The three component maps
are fixed by the ordinary pullbacks, not chosen independently of the spaces. -/
def finiteNaturality : Prop := ∀ (R : Type u) [CommRing R]
    (P Q : P202Specs.RelativeCupProduct.TwoSubspaces.{v}) (f : P.Map Q),
    ∃ (hP : P202Specs.ChainLES.DegreewiseShortExact (finiteSequence R P))
      (hQ : P202Specs.ChainLES.DegreewiseShortExact (finiteSequence R Q))
      (φ : finiteSequence R Q ⟶ finiteSequence R P),
      φ.τ₂ = CategoryTheory.Limits.biprod.map
        ((P202Specs.CohomologyPairs.relativeCochainFunctor R R).map f.leftMap.op)
        ((P202Specs.CohomologyPairs.relativeCochainFunctor R R).map f.rightMap.op) ∧
      φ.τ₃ = (P202Specs.CohomologyPairs.relativeCochainFunctor R R).map (intersectionMap f).op ∧
      φ.τ₁ ≫ P202Specs.RelativeCupProduct.sumToAbsolute R P =
        P202Specs.RelativeCupProduct.sumToAbsolute R Q ≫
          (P202Specs.CohomologyPairs.ordinaryCochainFunctor R R).map f.map.op ∧
      ∀ p : ℤ, P202Specs.ChainLES.connecting hQ p (p+1) (by simp) ≫
          HomologicalComplex.homologyMap φ.τ₁ (p+1) =
        HomologicalComplex.homologyMap φ.τ₃ p ≫
          P202Specs.ChainLES.connecting hP p (p+1) (by simp)

end Expected


/-- A compact contained in a subspace is compact in that subspace, with
ambient image exactly the original compact. No closedness of the subspace
is required. -/
lemma compact_in_subspace (M : Type v) [TopologicalSpace M] (U : Set M)
    (C : Support M) (hC : (C : Set M) ⊆ U) :
    ∃ K : Support U, ambientSupport M U K = C := by
  have hr : (C : Set M) ⊆ Set.range (Subtype.val : U → M) := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hC
  have h := (TopologicalSpace.Compacts.range_map
    (Topology.IsInducing.subtypeVal (t := U)))
  have hmem : C ∈ Set.range (TopologicalSpace.Compacts.map
      (Subtype.val : U → M) continuous_subtype_val) := h.symm ▸ hr
  exact hmem

/-- The finite closed refinement in the source is provided by the compact
binary-cover lemma, which also proves exact equality with the compact. -/
theorem compactUnionCofinal : Expected.compactUnionCofinal.{v} := by
  intro M _ _ U V hU hV hcover C
  obtain ⟨K, L, hK, hL, hKU, hLV, hKL⟩ := C.isCompact.binary_compact_cover hU hV
    (by rw [hcover]; exact Set.subset_univ _)
  obtain ⟨K', hK'⟩ := compact_in_subspace M U ⟨K, hK⟩ hKU
  obtain ⟨L', hL'⟩ := compact_in_subspace M V ⟨L, hL⟩ hLV
  refine ⟨(K', L'), ?_⟩
  unfold unionSupport
  rw [hK', hL']
  apply TopologicalSpace.Compacts.ext
  exact hKL.symm

/-- An intersection compact can be viewed as a compact in either piece.
Their two ambient images are the same original compact. -/
theorem compactIntersectionCofinal : Expected.compactIntersectionCofinal.{v} := by
  intro M _ _ U V C
  let A := ambientSupport M (U ∩ V) C
  have hA : (A : Set M) ⊆ U ∩ V := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  obtain ⟨K, hK⟩ := compact_in_subspace M U A (hA.trans Set.inter_subset_left)
  obtain ⟨L, hL⟩ := compact_in_subspace M V A (hA.trans Set.inter_subset_right)
  refine ⟨(K, L), ?_⟩
  simp only [intersectionSupport, hK, hL, inf_idem]
  rfl

/-- A filtered colimit retains exactness because a zero in the colimit
already vanishes at a later stage. All maps here are the canonical maps of
the given systems. -/
theorem filteredExactness : Expected.filteredExactness.{u,v,w} := by
  intro R _ ι _ _ _ F G H f g hex z
  constructor
  · intro hz
    obtain ⟨i, y, rfl⟩ := Module.DirectLimit.exists_of z
    change Module.DirectLimit.map g.component g.comm
      (Module.DirectLimit.of R ι (fun i => ↥(G.obj i)) G.transition i y) = 0 at hz
    rw [Module.DirectLimit.map_apply_of] at hz
    obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hz
    have hgy : g.component j (G.transition i j hij y) = 0 := by
      rw [show g.component j (G.transition i j hij y) =
        H.transition i j hij (g.component i y) from
          congrArg (fun k => k y) (g.comm i j hij)]
      exact hj
    obtain ⟨x, hx⟩ := (hex j (G.transition i j hij y)).mp hgy
    refine ⟨Module.DirectLimit.of R ι (fun i => ↥(F.obj i)) F.transition j x, ?_⟩
    change Module.DirectLimit.map f.component f.comm _ = _
    rw [Module.DirectLimit.map_apply_of, hx, Module.DirectLimit.of_f]
  · rintro ⟨x, rfl⟩
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of x
    change Module.DirectLimit.map g.component g.comm
      (Module.DirectLimit.map f.component f.comm _) = 0
    rw [Module.DirectLimit.map_apply_of, Module.DirectLimit.map_apply_of,
      (hex i).apply_apply_eq_zero, map_zero]

/-- The comparison is an isomorphism for every monotone cofinal index map.
In particular the result does not assume any transition map is injective. -/
theorem cofinalReindex : ∀ (R : Type u) [CommRing R]
    (ι : Type v) [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (κ : Type t) [Preorder κ] [Nonempty κ] [IsDirectedOrder κ]
    (F : ModuleSystem.{u,v,w} R ι) (φ : κ → ι) (hφ : Monotone φ),
    (∀ i, ∃ j, i ≤ φ j) → Function.Bijective (F.reindexMap φ hφ) := by
  intro R _ ι _ _ _ κ _ _ _ F φ hφ hcofinal
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨i, a, rfl⟩ := Module.DirectLimit.exists_of z
    rw [ModuleSystem.reindexMap_of F φ hφ i a] at hz
    obtain ⟨k, hik, hk⟩ := Module.DirectLimit.of.zero_exact hz
    obtain ⟨j, hkj⟩ := hcofinal k
    obtain ⟨l, hil, hjl⟩ := exists_ge_ge i j
    have hkl : k ≤ φ l := hkj.trans (hφ hjl)
    have ha : F.transition (φ i) (φ l) (hφ hil) a = 0 := by
      rw [← F.trans (φ i) k (φ l) hik hkl a, hk, map_zero]
    rw [← Module.DirectLimit.of_f (f := (F.reindex φ hφ).transition)
      (hij := hil) (x := a)]
    change Module.DirectLimit.of R κ _ (F.reindex φ hφ).transition l
      (F.transition (φ i) (φ l) (hφ hil) a) = 0
    rw [ha, map_zero]
  · intro z
    obtain ⟨i, x, rfl⟩ := Module.DirectLimit.exists_of z
    obtain ⟨j, hij⟩ := hcofinal i
    refine ⟨Module.DirectLimit.of R κ _ (F.reindex φ hφ).transition j
      (F.transition i (φ j) hij x), ?_⟩
    rw [ModuleSystem.reindexMap_of, Module.DirectLimit.of_f]


theorem unionColimit : Expected.unionColimit.{u,v} := by
  intro R _ M _ _ U V hU hV hcover p
  apply cofinalReindex R (Support M) (SupportPair M U V)
  intro C
  obtain ⟨s, hs⟩ := compactUnionCofinal M U V hU hV hcover C
  exact ⟨s, hs.ge⟩

theorem intersectionColimit : Expected.intersectionColimit.{u,v} := by
  intro R _ M _ _ U V p
  apply cofinalReindex R (Support ↥(U ∩ V)) (SupportPair M U V)
  intro C
  obtain ⟨s, hs⟩ := compactIntersectionCofinal M U V C
  refine ⟨s, le_of_eq ?_⟩
  apply TopologicalSpace.Compacts.map_injective continuous_subtype_val Subtype.val_injective
  change ambientSupport M (U ∩ V) C = ambientSupport M (U ∩ V) (intersectionIn M U V s)
  rw [ambient_intersectionIn, hs]

section FiniteStage
open CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.SingularChains P202Specs.RelativeSingularChains
  P202Specs.CohomologyPairs P202Specs.RelativeCupProduct
variable (R : Type u) [CommRing R] (P : TwoSubspaces.{v})

lemma sumToLeft_absolute : sumToLeft R P ≫ relativeToAbsolute R R P.leftPair =
    sumToAbsolute R P := by
  change (dualComplexFunctor R R (.down ℤ)).map (leftQuotientToSum R P).op ≫
    (dualComplexFunctor R R (.down ℤ)).map (projection (ordinaryFunctor R R) P.leftPair).op = _
  rw [← Functor.map_comp, ← op_comp]
  simp [leftQuotientToSum, projection]

lemma sumToRight_absolute : sumToRight R P ≫ relativeToAbsolute R R P.rightPair =
    sumToAbsolute R P := by
  change (dualComplexFunctor R R (.down ℤ)).map (rightQuotientToSum R P).op ≫
    (dualComplexFunctor R R (.down ℤ)).map (projection (ordinaryFunctor R R) P.rightPair).op = _
  rw [← Functor.map_comp, ← op_comp]
  simp [rightQuotientToSum, projection]

lemma leftToIntersection_absolute :
    leftToIntersection R P ≫ relativeToAbsolute R R (intersectionPair P) =
      relativeToAbsolute R R P.leftPair := by
  have h := (cochainSequenceMap R R (leftIntersectionMap P)).comm₁₂
  change leftToIntersection R P ≫ relativeToAbsolute R R (intersectionPair P) =
    relativeToAbsolute R R P.leftPair ≫ (ordinaryCochainFunctor R R).map (𝟙 P.space).op at h
  have hi : (ordinaryCochainFunctor R R).map (𝟙 P.space).op = 𝟙 _ :=
    (ordinaryCochainFunctor R R).map_id (op P.space)
  exact h.trans (by rw [hi, Category.comp_id])

lemma rightToIntersection_absolute :
    rightToIntersection R P ≫ relativeToAbsolute R R (intersectionPair P) =
      relativeToAbsolute R R P.rightPair := by
  have h := (cochainSequenceMap R R (rightIntersectionMap P)).comm₁₂
  change rightToIntersection R P ≫ relativeToAbsolute R R (intersectionPair P) =
    relativeToAbsolute R R P.rightPair ≫ (ordinaryCochainFunctor R R).map (𝟙 P.space).op at h
  have hi : (ordinaryCochainFunctor R R).map (𝟙 P.space).op = 𝟙 _ :=
    (ordinaryCochainFunctor R R).map_id (op P.space)
  exact h.trans (by rw [hi, Category.comp_id])

lemma relativeToAbsolute_injective (Q : Pair.{v}) (p : ℤ) :
    Function.Injective ((relativeToAbsolute R R Q).f p) :=
  (P202.CohomologyPairs.short_exact R R Q p).moduleCat_injective_f

/-- Exactness of a cokernel dual needs no projectivity or injectivity. -/
lemma sumToAbsolute_range (p : ℤ)
    (a : (ordinaryCochains R R P.space).X p)
    (hl : (restriction R R P.leftPair).f p a = 0)
    (hr : (restriction R R P.rightPair).f p a = 0) :
    ∃ b : (sumCochains R P).X p, (sumToAbsolute R P).f p b = a := by
  change (ordinaryComplex R R P.space).X p →ₗ[R] R at a
  change a.comp ((inclusion (ordinaryFunctor R R) P.leftPair).f p).hom = 0 at hl
  change a.comp ((inclusion (ordinaryFunctor R R) P.rightPair).f p).hom = 0 at hr
  let S := (ShortComplex.cokernelSequence (sumInclusion R P)).map (eval _ _ p)
  have hS : S.Exact := (ShortComplex.cokernelSequence_exact _).map (eval _ _ p)
  have hzero : S.f ≫ ModuleCat.ofHom
      ((ULift.moduleEquiv (R := R) (M := R)).symm.toLinearMap.comp a) = 0 := by
    change (sumInclusion R P).f p ≫ _ = 0
    apply biprodX_ext_from
    · simp only [comp_zero]
      rw [← Category.assoc]
      change ((biprod.inl : ordinaryComplex R R P.leftPair.sub ⟶
          ordinaryComplex R R P.leftPair.sub ⊞ ordinaryComplex R R P.rightPair.sub).f p ≫
        (biprod.desc (inclusion (ordinaryFunctor R R) P.leftPair)
          (inclusion (ordinaryFunctor R R) P.rightPair)).f p) ≫ _ = 0
      rw [biprod_inl_desc_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ULift.up (a ((inclusion (ordinaryFunctor R R) P.leftPair).f p x)) = 0
      exact congrArg ULift.up (congrArg (fun f : _ →ₗ[R] R => f x) hl)
    · simp only [comp_zero]
      rw [← Category.assoc]
      change ((biprod.inr : ordinaryComplex R R P.rightPair.sub ⟶
          ordinaryComplex R R P.leftPair.sub ⊞ ordinaryComplex R R P.rightPair.sub).f p ≫
        (biprod.desc (inclusion (ordinaryFunctor R R) P.leftPair)
          (inclusion (ordinaryFunctor R R) P.rightPair)).f p) ≫ _ = 0
      rw [biprod_inr_desc_f]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change ULift.up (a ((inclusion (ordinaryFunctor R R) P.rightPair).f p x)) = 0
      exact congrArg ULift.up (congrArg (fun f : _ →ₗ[R] R => f x) hr)
  have hker : S.g.hom.ker ≤ a.ker := by
    intro c hc
    obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff S).mp hS c hc
    change a c = 0
    rw [← hb]
    exact congrArg ULift.down (congrArg (fun f => f b) hzero)
  have hp : Function.Surjective S.g := by
    change Function.Surjective ((sumProjection R P).f p)
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  refine ⟨S.g.hom.liftOfSurjective hp ⟨a, hker⟩, ?_⟩
  apply LinearMap.ext
  intro c
  exact LinearMap.equivOfSurjective_apply hp hker

/-- A vanishing coordinate cochain is an actual relative cochain. -/
lemma relativeValue_range (Q : Pair.{v}) (p : ℕ)
    (a : Chains R Q.space p →ₗ[R] R) (ha : a ∈ vanishingCochains R R Q p) :
    ∃ b : (relativeCochains R R Q).X (p : ℤ),
      ordinaryCochainsEquiv R R Q.space p ((relativeToAbsolute R R Q).f (p : ℤ) b) = a := by
  obtain ⟨e, he⟩ := P202.CohomologyPairs.quotient_vanishing R R Q p
  let b := (quotientCochainsEquiv R R Q p).symm (e.symm ⟨a, ha⟩)
  refine ⟨b, ?_⟩
  apply LinearMap.ext
  intro c
  rw [← P202.CohomologyPairs.quotient_identification R R Q p b c]
  dsimp only [b]
  rw [LinearEquiv.apply_symm_apply, ← he]
  simp

/-- Assign each simplex value to the left component unless the simplex lies
in the left subspace, in which case assign it to the right component. -/
lemma relative_decomposition (p : ℕ)
    (a : (relativeCochains R R (intersectionPair P)).X (p : ℤ)) :
    ∃ b : (relativeCochains R R P.leftPair).X (p : ℤ),
    ∃ c : (relativeCochains R R P.rightPair).X (p : ℤ),
      (leftToIntersection R P).f (p : ℤ) b +
        (rightToIntersection R P).f (p : ℤ) c = a := by
  let v := ordinaryCochainsEquiv R R P.space p
    ((relativeToAbsolute R R (intersectionPair P)).f (p : ℤ) a)
  have hv := P202.RelativeCupProduct.relativeValue_vanishes R (intersectionPair P) p a
  let b : Chains R P.space p →ₗ[R] R := Finsupp.linearCombination R
    (fun s => if InSubspace P.leftPair p s then 0 else v (Finsupp.single s 1))
  have hb : b ∈ vanishingCochains R R P.leftPair p := by
    apply (P202.CohomologyPairs.vanishing_on_simplices R R P.leftPair p b).mpr
    intro s hs
    simp [b, hs]
  have hc : v-b ∈ vanishingCochains R R P.rightPair p := by
    apply (P202.CohomologyPairs.vanishing_on_simplices R R P.rightPair p (v-b)).mpr
    intro s hs
    by_cases hl : InSubspace P.leftPair p s
    · have hv0 := (P202.CohomologyPairs.vanishing_on_simplices R R
        (intersectionPair P) p v).mp hv s (fun x => ⟨hl x, hs x⟩)
      simp [b, hl, hv0]
    · simp [b, hl]
  obtain ⟨b', hb'⟩ := relativeValue_range R P.leftPair p b hb
  obtain ⟨c', hc'⟩ := relativeValue_range R P.rightPair p (v-b) hc
  refine ⟨b', c', ?_⟩
  apply relativeToAbsolute_injective R (intersectionPair P) (p : ℤ)
  apply (ordinaryCochainsEquiv R R P.space p).injective
  rw [map_add, map_add]
  have hleft := congrArg (fun f => ordinaryCochainsEquiv R R P.space p (f.f (p : ℤ) b'))
    (leftToIntersection_absolute R P)
  have hright := congrArg (fun f => ordinaryCochainsEquiv R R P.space p (f.f (p : ℤ) c'))
    (rightToIntersection_absolute R P)
  change ordinaryCochainsEquiv R R P.space p
      ((leftToIntersection R P ≫ relativeToAbsolute R R (intersectionPair P)).f (p : ℤ) b') +
    ordinaryCochainsEquiv R R P.space p
      ((rightToIntersection R P ≫ relativeToAbsolute R R (intersectionPair P)).f (p : ℤ) c') = v
  rw [hleft, hright, hb', hc']
  exact add_sub_cancel _ _

/-- Elements of a biproduct of complexes are determined by their two components. -/
lemma biprod_element_ext {K L : CochainComplex (ModuleCat.{max u v} R) ℤ}
    (p : ℤ) {a b : (K ⊞ L).X p}
    (h₁ : (biprod.fst : K ⊞ L ⟶ K).f p a = (biprod.fst : K ⊞ L ⟶ K).f p b)
    (h₂ : (biprod.snd : K ⊞ L ⟶ L).f p a = (biprod.snd : K ⊞ L ⟶ L).f p b) : a = b := by
  have ha := congrArg (fun f => f a) (biprod_total_f (K := K) (L := L) p)
  have hb := congrArg (fun f => f b) (biprod_total_f (K := K) (L := L) p)
  change (biprod.inl : K ⟶ K ⊞ L).f p ((biprod.fst : K ⊞ L ⟶ K).f p a) +
    (biprod.inr : L ⟶ K ⊞ L).f p ((biprod.snd : K ⊞ L ⟶ L).f p a) = a at ha
  change (biprod.inl : K ⟶ K ⊞ L).f p ((biprod.fst : K ⊞ L ⟶ K).f p b) +
    (biprod.inr : L ⟶ K ⊞ L).f p ((biprod.snd : K ⊞ L ⟶ L).f p b) = b at hb
  rw [← ha, ← hb, h₁, h₂]

lemma finite_first_injective (p : ℤ) :
    Function.Injective ((finiteSequence R P).f.f p) := by
  intro a b hab
  have h := congrArg ((biprod.fst :
      relativeCochains R R P.leftPair ⊞ relativeCochains R R P.rightPair ⟶ _).f p) hab
  change (biprod.fst :
      relativeCochains R R P.leftPair ⊞ relativeCochains R R P.rightPair ⟶ _).f p
      ((biprod.lift (sumToLeft R P) (-sumToRight R P)).f p a) =
    (biprod.fst : relativeCochains R R P.leftPair ⊞ relativeCochains R R P.rightPair ⟶ _).f p
      ((biprod.lift (sumToLeft R P) (-sumToRight R P)).f p b) at h
  simp only [← ModuleCat.comp_apply, biprod_lift_fst_f] at h
  apply P202.RelativeCupProduct.sumToAbsolute_injective R P p
  have H := congrArg ((relativeToAbsolute R R P.leftPair).f p) h
  change (sumToLeft R P ≫ relativeToAbsolute R R P.leftPair).f p a =
    (sumToLeft R P ≫ relativeToAbsolute R R P.leftPair).f p b at H
  rwa [sumToLeft_absolute] at H

lemma finite_sum_surjective (p : ℤ) :
    Function.Surjective ((finiteSequence R P).g.f p) := by
  intro a
  by_cases hp : 0 ≤ p
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    obtain ⟨b, c, hbc⟩ := relative_decomposition R P n a
    refine ⟨(biprod.inl : relativeCochains R R P.leftPair ⟶
        relativeCochains R R P.leftPair ⊞ relativeCochains R R P.rightPair).f (n : ℤ) b +
      (biprod.inr : relativeCochains R R P.rightPair ⟶
        relativeCochains R R P.leftPair ⊞ relativeCochains R R P.rightPair).f (n : ℤ) c, ?_⟩
    change (biprod.desc (leftToIntersection R P) (rightToIntersection R P)).f (n : ℤ) _ = a
    rw [map_add]
    simpa only [← ModuleCat.comp_apply, biprod_inl_desc_f, biprod_inr_desc_f] using hbc
  · have hz := ((P202.CohomologyPairs.negative R R).2 (intersectionPair P) p (by omega)).1
    refine ⟨0, ?_⟩
    change (biprod.desc (leftToIntersection R P) (rightToIntersection R P)).f p 0 = a
    exact @Subsingleton.elim ((relativeCochains R R (intersectionPair P)).X p)
      (ModuleCat.subsingleton_of_isZero hz) _ _

lemma finite_middle_exact (p : ℤ)
    (y : ((finiteSequence R P).X₂).X p)
    (hy : (finiteSequence R P).g.f p y = 0) :
    ∃ a, (finiteSequence R P).f.f p a = y := by
  let K := relativeCochains R R P.leftPair
  let L := relativeCochains R R P.rightPair
  let x := (biprod.fst : K ⊞ L ⟶ K).f p y
  let z := (biprod.snd : K ⊞ L ⟶ L).f p y
  have hsum : (leftToIntersection R P).f p x + (rightToIntersection R P).f p z = 0 := by
    change (biprod.desc (leftToIntersection R P) (rightToIntersection R P)).f p y = 0 at hy
    rw [biprod.desc_eq] at hy
    exact hy
  have hab : (relativeToAbsolute R R P.leftPair).f p x =
      -(relativeToAbsolute R R P.rightPair).f p z := by
    have h := congrArg ((relativeToAbsolute R R (intersectionPair P)).f p) hsum
    rw [map_add, map_zero] at h
    change (leftToIntersection R P ≫ relativeToAbsolute R R (intersectionPair P)).f p x +
      (rightToIntersection R P ≫ relativeToAbsolute R R (intersectionPair P)).f p z = 0 at h
    rw [leftToIntersection_absolute, rightToIntersection_absolute] at h
    exact eq_neg_of_add_eq_zero_left h
  have hl : (restriction R R P.leftPair).f p
      ((relativeToAbsolute R R P.leftPair).f p x) = 0 :=
    congrArg (fun f => f.f p x) (cochainSequence R R P.leftPair).zero
  have hr : (restriction R R P.rightPair).f p
      ((relativeToAbsolute R R P.leftPair).f p x) = 0 := by
    rw [hab, map_neg]
    have h := congrArg (fun f => f.f p z) (cochainSequence R R P.rightPair).zero
    change (restriction R R P.rightPair).f p ((relativeToAbsolute R R P.rightPair).f p z) = 0 at h
    rw [h, neg_zero]
  obtain ⟨a, ha⟩ := sumToAbsolute_range R P p _ hl hr
  have hleft : (sumToLeft R P).f p a = x := by
    apply relativeToAbsolute_injective R P.leftPair p
    change (sumToLeft R P ≫ relativeToAbsolute R R P.leftPair).f p a = _
    rw [sumToLeft_absolute]
    exact ha
  have hright : (sumToRight R P).f p a = -z := by
    apply relativeToAbsolute_injective R P.rightPair p
    rw [map_neg]
    change (sumToRight R P ≫ relativeToAbsolute R R P.rightPair).f p a = _
    rw [sumToRight_absolute]
    exact ha.trans hab
  refine ⟨a, biprod_element_ext R p ?_ ?_⟩
  · change (biprod.fst : K ⊞ L ⟶ K).f p
      ((biprod.lift (sumToLeft R P) (-sumToRight R P)).f p a) = x
    rw [← ModuleCat.comp_apply, biprod_lift_fst_f]
    exact hleft
  · change (biprod.snd : K ⊞ L ⟶ L).f p
      ((biprod.lift (sumToLeft R P) (-sumToRight R P)).f p a) = z
    rw [← ModuleCat.comp_apply, biprod_lift_snd_f]
    change -((sumToRight R P).f p a) = z
    rw [hright, neg_neg]

end FiniteStage

theorem finiteShortExact : Expected.finiteShortExact.{u,v} := by
  intro R _ P
  apply (P202.ChainLES.module_hypothesis _).mpr
  intro p
  exact ⟨finite_first_injective R P p, finite_middle_exact R P p, finite_sum_surjective R P p⟩

theorem finiteLongExact : Expected.finiteLongExact.{u,v} := by
  intro R _ P
  let h := finiteShortExact R P
  exact ⟨h, fun p => (P202.ChainLES.exactness _ h).2 p (p+1) (by simp),
    P202.ChainLES.module_lift _ h⟩

theorem finiteSupportComparison : Expected.finiteSupportComparison.{u,v} := by
  intro R _ M _ _ K L p
  have h : (supportComplements M K L).IsOpen :=
    ⟨K.isCompact.isClosed.isOpen_compl, L.isCompact.isClosed.isOpen_compl⟩
  haveI := P202.RelativeCupProduct.comparison R (supportComplements M K L) h p
  unfold supportComparison
  rw [HomologicalComplex.homologyMap_comp]
  infer_instance

section Naturality
open CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.SingularChains P202Specs.RelativeSingularChains
  P202Specs.CohomologyPairs P202Specs.RelativeCupProduct
variable (R : Type u) [CommRing R] {P Q : TwoSubspaces.{v}} (f : P.Map Q)

lemma sumToLeft_natural :
    P202.RelativeCupProduct.sumCochainMap R f ≫ sumToLeft R P =
      sumToLeft R Q ≫ (relativeCochainFunctor R R).map f.leftMap.op := by
  haveI : Mono (relativeToAbsolute R R P.leftPair) := mono_of_mono_f _
    (fun p => (P202.CohomologyPairs.short_exact R R P.leftPair p).mono_f)
  have h := (cochainSequenceMap R R f.leftMap).comm₁₂
  change (relativeCochainFunctor R R).map f.leftMap.op ≫ relativeToAbsolute R R P.leftPair =
    relativeToAbsolute R R Q.leftPair ≫ (ordinaryCochainFunctor R R).map f.map.op at h
  apply (cancel_mono (relativeToAbsolute R R P.leftPair)).mp
  rw [Category.assoc, sumToLeft_absolute, P202.RelativeCupProduct.sumCochainMap_absolute,
    Category.assoc, h, ← Category.assoc, sumToLeft_absolute]

lemma sumToRight_natural :
    P202.RelativeCupProduct.sumCochainMap R f ≫ sumToRight R P =
      sumToRight R Q ≫ (relativeCochainFunctor R R).map f.rightMap.op := by
  haveI : Mono (relativeToAbsolute R R P.rightPair) := mono_of_mono_f _
    (fun p => (P202.CohomologyPairs.short_exact R R P.rightPair p).mono_f)
  have h := (cochainSequenceMap R R f.rightMap).comm₁₂
  change (relativeCochainFunctor R R).map f.rightMap.op ≫ relativeToAbsolute R R P.rightPair =
    relativeToAbsolute R R Q.rightPair ≫ (ordinaryCochainFunctor R R).map f.map.op at h
  apply (cancel_mono (relativeToAbsolute R R P.rightPair)).mp
  rw [Category.assoc, sumToRight_absolute, P202.RelativeCupProduct.sumCochainMap_absolute,
    Category.assoc, h, ← Category.assoc, sumToRight_absolute]

lemma leftToIntersection_natural :
    (relativeCochainFunctor R R).map f.leftMap.op ≫ leftToIntersection R P =
      leftToIntersection R Q ≫ (relativeCochainFunctor R R).map (intersectionMap f).op := by
  have h : leftIntersectionMap P ≫ f.leftMap = intersectionMap f ≫ leftIntersectionMap Q := by
    apply PairMap.ext; rfl
  change (relativeCochainFunctor R R).map f.leftMap.op ≫
    (relativeCochainFunctor R R).map (leftIntersectionMap P).op = _
  rw [← Functor.map_comp, ← op_comp, h, op_comp, Functor.map_comp]
  rfl

lemma rightToIntersection_natural :
    (relativeCochainFunctor R R).map f.rightMap.op ≫ rightToIntersection R P =
      rightToIntersection R Q ≫ (relativeCochainFunctor R R).map (intersectionMap f).op := by
  have h : rightIntersectionMap P ≫ f.rightMap = intersectionMap f ≫ rightIntersectionMap Q := by
    apply PairMap.ext; rfl
  change (relativeCochainFunctor R R).map f.rightMap.op ≫
    (relativeCochainFunctor R R).map (rightIntersectionMap P).op = _
  rw [← Functor.map_comp, ← op_comp, h, op_comp, Functor.map_comp]
  rfl

/-- Pullback of the finite-stage short exact sequences. -/
def finiteSequenceMap : finiteSequence R Q ⟶ finiteSequence R P :=
  ShortComplex.Hom.mk (P202.RelativeCupProduct.sumCochainMap R f)
    (biprod.map ((relativeCochainFunctor R R).map f.leftMap.op)
      ((relativeCochainFunctor R R).map f.rightMap.op))
    ((relativeCochainFunctor R R).map (intersectionMap f).op)
    (by
      change _ ≫ biprod.lift (sumToLeft R P) (-sumToRight R P) =
        biprod.lift (sumToLeft R Q) (-sumToRight R Q) ≫ _
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst,
          biprod.lift_fst_assoc]
        exact sumToLeft_natural R f
      · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
          biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp]
        exact congrArg Neg.neg (sumToRight_natural R f))
    (by
      change _ ≫ biprod.desc (leftToIntersection R P) (rightToIntersection R P) =
        biprod.desc (leftToIntersection R Q) (rightToIntersection R Q) ≫ _
      apply biprod.hom_ext'
      · simp only [biprod.inl_map_assoc, biprod.inl_desc, biprod.inl_desc_assoc]
        exact leftToIntersection_natural R f
      · simp only [biprod.inr_map_assoc, biprod.inr_desc, biprod.inr_desc_assoc]
        exact rightToIntersection_natural R f)

end Naturality

theorem finiteNaturality : Expected.finiteNaturality.{u,v} := by
  intro R _ P Q f
  let φ := finiteSequenceMap R f
  refine ⟨finiteShortExact R P, finiteShortExact R Q, φ, rfl, rfl, ?_, ?_⟩
  · exact P202.RelativeCupProduct.sumCochainMap_absolute R f
  · intro p
    exact (P202.ChainLES.naturality φ (finiteShortExact R Q) (finiteShortExact R P)).2.2
      p (p+1) (by simp)

section FiniteCycleSplitting
open CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.SingularChains P202Specs.RelativeSingularChains
  P202Specs.CohomologyPairs P202Specs.RelativeCupProduct
variable (R : Type u) [CommRing R] (P : TwoSubspaces.{v})

/-- A finite-stage cocycle has a genuine two-piece lift. Its left coboundary
is a cycle in the dual sum quotient and represents the positive connecting
homomorphism. The equalities retain the original absolute cochain values. -/
theorem finiteCycleSplitting (p : ℤ)
    (a : (relativeCochains R R (intersectionPair P)).cycles p) :
    ∃ (aP : (relativeCochains R R P.leftPair).X p)
      (aQ : (relativeCochains R R P.rightPair).X p)
      (z : (sumCochains R P).cycles (p+1)),
      (relativeToAbsolute R R P.leftPair).f p aP +
          (relativeToAbsolute R R P.rightPair).f p aQ =
        (relativeToAbsolute R R (intersectionPair P)).f p
          ((relativeCochains R R (intersectionPair P)).iCycles p a) ∧
      (sumToAbsolute R P).f (p+1) ((sumCochains R P).iCycles (p+1) z) =
        (ordinaryCochains R R P.space).d p (p+1)
          ((relativeToAbsolute R R P.leftPair).f p aP) ∧
      P202Specs.ChainLES.connecting (finiteShortExact R P) p (p+1) (by simp)
          ((relativeCochains R R (intersectionPair P)).homologyπ p a) =
        (sumCochains R P).homologyπ (p+1) z := by
  let S := finiteSequence R P
  have ha : S.X₃.d p (p+1) (S.X₃.iCycles p a) = 0 :=
    congrArg (fun f => f a) (S.X₃.iCycles_d p (p+1))
  obtain ⟨c, hc, x, ⟨hx, hclosed⟩, _⟩ :=
    (P202.ChainLES.module_lift S (finiteShortExact R P)).1 p (p+1) (by simp)
      (S.X₃.iCycles p a) ha
  let aP := (biprod.fst : S.X₂ ⟶ relativeCochains R R P.leftPair).f p c
  let aQ := (biprod.snd : S.X₂ ⟶ relativeCochains R R P.rightPair).f p c
  let z : S.X₁.cycles (p+1) := S.X₁.cyclesMk x
    ((ComplexShape.up ℤ).next (p+1)) rfl (hclosed _)
  have hz : S.X₁.iCycles (p+1) z = x := by
    dsimp only [z]
    exact HomologicalComplex.i_cyclesMk S.X₁ x _ rfl (hclosed _)
  refine ⟨aP, aQ, z, ?_, ?_, ?_⟩
  · have hsum : (leftToIntersection R P).f p aP +
        (rightToIntersection R P).f p aQ = S.X₃.iCycles p a := by
      change (biprod.desc (leftToIntersection R P) (rightToIntersection R P)).f p c = _ at hc
      rw [biprod.desc_eq] at hc
      exact hc
    have h := congrArg ((relativeToAbsolute R R (intersectionPair P)).f p) hsum
    rw [map_add] at h
    change (leftToIntersection R P ≫ relativeToAbsolute R R (intersectionPair P)).f p aP +
      (rightToIntersection R P ≫ relativeToAbsolute R R (intersectionPair P)).f p aQ = _ at h
    rwa [leftToIntersection_absolute, rightToIntersection_absolute] at h
  · have hfst := congrArg
      ((biprod.fst : S.X₂ ⟶ relativeCochains R R P.leftPair).f (p+1)) hx
    change (biprod.fst : S.X₂ ⟶ relativeCochains R R P.leftPair).f (p+1)
        ((biprod.lift (sumToLeft R P) (-sumToRight R P)).f (p+1) x) =
      (biprod.fst : S.X₂ ⟶ relativeCochains R R P.leftPair).f (p+1) (S.X₂.d p (p+1) c) at hfst
    rw [← ModuleCat.comp_apply, biprod_lift_fst_f] at hfst
    have hcomm := congrArg (fun f => f c)
      ((biprod.fst : S.X₂ ⟶ relativeCochains R R P.leftPair).comm p (p+1))
    change (relativeCochains R R P.leftPair).d p (p+1) aP =
      (biprod.fst : S.X₂ ⟶ relativeCochains R R P.leftPair).f (p+1) (S.X₂.d p (p+1) c) at hcomm
    have hleft : (sumToLeft R P).f (p+1) x =
        (relativeCochains R R P.leftPair).d p (p+1) aP := hfst.trans hcomm.symm
    calc
      (sumToAbsolute R P).f (p+1) ((sumCochains R P).iCycles (p+1) z) =
          (sumToAbsolute R P).f (p+1) x :=
        congrArg ((sumToAbsolute R P).f (p+1)) hz
      _ = (relativeToAbsolute R R P.leftPair).f (p+1) ((sumToLeft R P).f (p+1) x) :=
        congrArg (fun f => f.f (p+1) x) (sumToLeft_absolute R P).symm
      _ = (relativeToAbsolute R R P.leftPair).f (p+1)
          ((relativeCochains R R P.leftPair).d p (p+1) aP) := congrArg _ hleft
      _ = _ := (congrArg (fun f => f aP)
        ((relativeToAbsolute R R P.leftPair).comm p (p+1))).symm
  · have hmk : S.X₃.cyclesMk (S.X₃.iCycles p a) (p+1)
        ((ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel p (p+1) by simp)) ha = a := by
      apply (ModuleCat.mono_iff_injective (S.X₃.iCycles p)).mp inferInstance
      exact HomologicalComplex.i_cyclesMk S.X₃ (S.X₃.iCycles p a) (p+1) _ ha
    have hδ := (P202.ChainLES.module_lift S (finiteShortExact R P)).2.1
      p (p+1) (by simp) (S.X₃.iCycles p a) ha c hc x hx (hclosed _)
    change P202Specs.ChainLES.connecting (finiteShortExact R P) p (p+1) (by simp)
        (S.X₃.homologyπ p (S.X₃.cyclesMk (S.X₃.iCycles p a) (p+1) _ ha)) =
      S.X₁.homologyπ (p+1) z at hδ
    rwa [hmk] at hδ

end FiniteCycleSplitting

end P202.CompactSupportMV

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris

variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

/-- The source open subspace and its preimage in an ambient subspace are
homeomorphic, while retaining the actual source subtype as the domain. -/
def subsetPreimageHomeomorph {B E : Set M} (h : B ⊆ E) :
    B ≃ₜ {x : E | x.val ∈ B} where
  toFun x := ⟨⟨x.val, h x.property⟩, x.property⟩
  invFun x := ⟨x.val.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

lemma subsetPullback_isIso {B E : Set M} (h : B ⊆ E) (hB : IsOpen B)
    (K : Support B) (p : ℤ) : IsIso (subsetPullback R h K p) := by
  let U : Set E := Subtype.val ⁻¹' B
  have hU : IsOpen U := hB.preimage continuous_subtype_val
  let S := supportInSubset h K
  have hSU : (S : Set E) ⊆ U := by
    rintro x ⟨y, hy, rfl⟩
    exact y.property
  let D := P202.LocalOrientation.openSupportExcisionData U hU S S.isCompact.isClosed hSU
  let e₁ := P202.LocalOrientation.supportedPairIsoOfHomeomorph
    (subsetPreimageHomeomorph M h) (K : Set B) (Subtype.val ⁻¹' (S : Set E))
    (fun x => by
      change x ∈ K ↔ subsetInclusion h x ∈ S
      constructor
      · exact fun hx => ⟨x, hx, rfl⟩
      · rintro ⟨y, hy, he⟩
        have he' : y = x := Subtype.ext (congrArg (fun z : E => z.val) he)
        exact he' ▸ hy)
  let e₂ := P202.LocalOrientation.openSupportExcisionIso U hU S S.isCompact.isClosed hSU
  have hf : subsetPairInclusion h K = e₁.hom ≫ e₂.hom ≫ D.inclusion := by
    apply PairMap.ext
    rfl
  haveI := P202.CohomologyExcisionMV.excision R R D p
  change IsIso ((relativeCohomologyFunctor R R p).map (subsetPairInclusion h K).op)
  rw [hf, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

lemma supportInSubset_mono {B E : Set M} (h : B ⊆ E) {K L : Support B}
    (hKL : K ≤ L) : supportInSubset h K ≤ supportInSubset h L := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, hKL hy, rfl⟩

/-- Inverse excision for the actual inclusion between subspaces. -/
def extendSubsetAt {B E : Set M} (h : B ⊆ E) (hB : IsOpen B)
    (K : Support B) (p : ℤ) :
    supportedCohomology R B p K →ₗ[R]
      supportedCohomology R E p (supportInSubset h K) := by
  haveI := subsetPullback_isIso R M h hB K p
  exact (asIso (subsetPullback R h K p)).inv.hom

@[simp] lemma subsetPullback_extendSubsetAt {B E : Set M} (h : B ⊆ E) (hB : IsOpen B)
    (K : Support B) (p : ℤ) (a : supportedCohomology R B p K) :
    subsetPullback R h K p (extendSubsetAt R M h hB K p a) = a := by
  haveI := subsetPullback_isIso R M h hB K p
  exact congrArg (fun f => f a) (asIso (subsetPullback R h K p)).inv_hom_id

@[simp] lemma extendSubsetAt_subsetPullback {B E : Set M} (h : B ⊆ E) (hB : IsOpen B)
    (K : Support B) (p : ℤ)
    (b : supportedCohomology R E p (supportInSubset h K)) :
    extendSubsetAt R M h hB K p (subsetPullback R h K p b) = b := by
  haveI := subsetPullback_isIso R M h hB K p
  exact congrArg (fun f => f b) (asIso (subsetPullback R h K p)).hom_inv_id

lemma subsetPullback_transition {B E : Set M} (h : B ⊆ E) (p : ℤ)
    {K L : Support B} (hKL : K ≤ L)
    (b : supportedCohomology R E p (supportInSubset h K)) :
    subsetPullback R h L p
      (transition R E p (supportInSubset h K) (supportInSubset h L)
        (supportInSubset_mono M h hKL) b) =
      transition R B p K L hKL (subsetPullback R h K p b) := by
  have hs : subsetPairInclusion h L ≫ supportPairMap E (supportInSubset_mono M h hKL) =
      supportPairMap B hKL ≫ subsetPairInclusion h K := by
    apply PairMap.ext
    rfl
  have H := congrArg ((relativeCohomologyFunctor R R p).map) (congrArg Quiver.Hom.op hs)
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp] at H
  exact congrArg (fun f => f b) H

lemma extendSubsetAt_compatible {B E : Set M} (h : B ⊆ E) (hB : IsOpen B)
    (p : ℤ) {K L : Support B} (hKL : K ≤ L) (a : supportedCohomology R B p K) :
    extendSubsetAt R M h hB L p (transition R B p K L hKL a) =
      transition R E p (supportInSubset h K) (supportInSubset h L)
        (supportInSubset_mono M h hKL) (extendSubsetAt R M h hB K p a) := by
  haveI := subsetPullback_isIso R M h hB L p
  apply (asIso (subsetPullback R h L p)).toLinearEquiv.injective
  change subsetPullback R h L p _ = subsetPullback R h L p _
  rw [subsetPullback_extendSubsetAt]
  have hs : subsetPairInclusion h L ≫ supportPairMap E (supportInSubset_mono M h hKL) =
      supportPairMap B hKL ≫ subsetPairInclusion h K := by
    apply PairMap.ext
    rfl
  have H := congrArg ((relativeCohomologyFunctor R R p).map) (congrArg Quiver.Hom.op hs)
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp] at H
  have H' := congrArg (fun f => f (extendSubsetAt R M h hB K p a)) H
  change transition R B p K L hKL a = _
  change _ = transition R B p K L hKL
    (subsetPullback R h K p (extendSubsetAt R M h hB K p a)) at H'
  rw [subsetPullback_extendSubsetAt] at H'
  exact H'.symm

/-- Extension of compact cohomology along a named inclusion of open subspaces. -/
def extendSubset {B E : Set M} (h : B ⊆ E) (hB : IsOpen B) (p : ℤ) :
    CompactCohomology R B p →ₗ[R] CompactCohomology R E p :=
  descend R B p
    (fun K => (ofSupport R E p (supportInSubset h K)).comp (extendSubsetAt R M h hB K p))
    (by
      intro K L hKL a
      simp only [LinearMap.comp_apply, extendSubsetAt_compatible,
        P202.CompactSupport.ofSupport_transition])

@[simp] lemma extendSubset_ofSupport {B E : Set M} (h : B ⊆ E) (hB : IsOpen B)
    (p : ℤ) (K : Support B) (a : supportedCohomology R B p K) :
    extendSubset R M h hB p (ofSupport R B p K a) =
      ofSupport R E p (supportInSubset h K) (extendSubsetAt R M h hB K p a) := by
  simp only [extendSubset, P202.CompactSupport.descend_ofSupport, LinearMap.comp_apply]

lemma extendSubset_represents {B E : Set M} (h : B ⊆ E) (hB : IsOpen B)
    (p : ℤ) (K : Support B) (b : supportedCohomology R E p (supportInSubset h K)) :
    extendSubset R M h hB p (ofSupport R B p K (subsetPullback R h K p b)) =
      ofSupport R E p (supportInSubset h K) b := by
  rw [extendSubset_ofSupport]
  haveI := subsetPullback_isIso R M h hB K p
  have H := congrArg (fun f => f b) (asIso (subsetPullback R h K p)).hom_inv_id
  change extendSubsetAt R M h hB K p (subsetPullback R h K p b) = b at H
  rw [H]

/-- Actual intersection-to-left extension, without identifying intersection
with a nested subtype. -/
def intersectionExtendLeft (C : Cover M) : IntersectionExtension R M C C.left :=
  extendSubset R M Set.inter_subset_left (C.left_open.inter C.right_open)

def intersectionExtendRight (C : Cover M) : IntersectionExtension R M C C.right :=
  extendSubset R M Set.inter_subset_right (C.left_open.inter C.right_open)

lemma intersectionExtendLeft_represents (C : Cover M) :
    ExtensionRepresents R M C Set.inter_subset_left (intersectionExtendLeft R M C) :=
  extendSubset_represents R M Set.inter_subset_left (C.left_open.inter C.right_open)

lemma intersectionExtendRight_represents (C : Cover M) :
    ExtensionRepresents R M C Set.inter_subset_right (intersectionExtendRight R M C) :=
  extendSubset_represents R M Set.inter_subset_right (C.left_open.inter C.right_open)

lemma ambientSupport_supportInSubset {B E : Set M} (h : B ⊆ E) (K : Support B) :
    ambientSupport M E (supportInSubset h K) = ambientSupport M B K := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨subsetInclusion h y, ⟨y, hy, rfl⟩, rfl⟩

/-- The representative law uniquely fixes every supplied ambient extension. -/
lemma dualityData_extend_eq (d : DualityData.{u,v} R) (U : Set M) (hU : IsOpen U)
    (p : ℤ) : d.extend M U hU p = P202.CompactSupport.extendOpen R M U hU p := by
  apply P202.CompactSupport.hom_ext
  intro K
  ext a
  let b := P202.CompactSupport.extendAt R M U hU K p a
  have hb : openPullback R M U K p b = a :=
    P202.CompactSupport.openPullback_extendAt R M U hU K p a
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hb,
    d.extension_represents M U hU p K b, P202.CompactSupport.extendOpen_ofSupport,
    hb]

/-- Actual subspace extension is functorial with the already supplied
extension to the ambient manifold; support equality is mediated by its ordinary
transition map rather than silently identifying different support expressions. -/
lemma extendSubset_toAmbient (d : DualityData.{u,v} R)
    {B E : Set M} (h : B ⊆ E) (hB : IsOpen B) (hE : IsOpen E) (p : ℤ) :
    (d.extend M E hE p).comp (extendSubset R M h hB p) = d.extend M B hB p := by
  apply P202.CompactSupport.hom_ext
  intro K
  ext a
  let S := supportInSubset h K
  let hS : ambientSupport M E S ≤ ambientSupport M B K :=
    le_of_eq (ambientSupport_supportInSubset M h K)
  let bE := extendSubsetAt R M h hB K p a
  let bM := P202.CompactSupport.extendAt R M E hE S p bE
  have hbE : openPullback R M E S p bM = bE :=
    P202.CompactSupport.openPullback_extendAt R M E hE S p bE
  have hs : openPairInclusion M B K ≫ supportPairMap M hS =
      subsetPairInclusion h K ≫ openPairInclusion M E S := by
    apply PairMap.ext
    rfl
  have H := congrArg ((relativeCohomologyFunctor R R p).map) (congrArg Quiver.Hom.op hs)
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp] at H
  have hbB : openPullback R M B K p
      (transition R M p (ambientSupport M E S) (ambientSupport M B K) hS bM) = a := by
    have H' := congrArg (fun f => f bM) H
    change openPullback R M B K p
      (transition R M p (ambientSupport M E S) (ambientSupport M B K) hS bM) =
        subsetPullback R h K p (openPullback R M E S p bM) at H'
    rw [H', hbE]
    exact subsetPullback_extendSubsetAt R M h hB K p a
  change d.extend M E hE p (extendSubset R M h hB p (ofSupport R B p K a)) =
    d.extend M B hB p (ofSupport R B p K a)
  rw [extendSubset_ofSupport]
  change d.extend M E hE p (ofSupport R E p S bE) = _
  rw [← hbE, d.extension_represents M E hE p S bM]
  conv_rhs => rw [← hbB, d.extension_represents M B hB p K]
  exact (P202.CompactSupport.ofSupport_transition R M p
    (ambientSupport M E S) (ambientSupport M B K) hS bM).symm

lemma intersection_first_sum_zero (d : DualityData.{u,v} R) (C : Cover M) (p : ℤ) :
    first R M C (intersectionExtendLeft R M C) (intersectionExtendRight R M C) p ≫
      sum R M d C p = 0 := by
  rw [first, sum, biprod.lift_desc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change d.extend M C.left C.left_open p
      (extendSubset R M Set.inter_subset_left (C.left_open.inter C.right_open) p a) +
    d.extend M C.right C.right_open p
      (-(extendSubset R M Set.inter_subset_right (C.left_open.inter C.right_open) p a)) = 0
  rw [map_neg]
  have hL := LinearMap.congr_fun
    (extendSubset_toAmbient R M d Set.inter_subset_left
      (C.left_open.inter C.right_open) C.left_open p) a
  have hR := LinearMap.congr_fun
    (extendSubset_toAmbient R M d Set.inter_subset_right
      (C.left_open.inter C.right_open) C.right_open p) a
  change d.extend M C.left C.left_open p
      (extendSubset R M Set.inter_subset_left (C.left_open.inter C.right_open) p a) =
      d.extend M C.intersection (C.left_open.inter C.right_open) p a at hL
  change d.extend M C.right C.right_open p
      (extendSubset R M Set.inter_subset_right (C.left_open.inter C.right_open) p a) =
      d.extend M C.intersection (C.left_open.inter C.right_open) p a at hR
  rw [hL, hR, add_neg_cancel]

end P202.CompactSupportMV

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactSupport

/-- The chart restriction construction also applies to the empty open set. -/
def openManifold {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : Manifold n M) (U : Set M) (hU : IsOpen U) : Manifold n U := by
  letI := A.hausdorff
  letI := A.secondCountable
  refine ⟨inferInstance, inferInstance,
    {e | ∃ hne : Nonempty U, ∃ c ∈ A.atlas,
      e = c.subtypeRestr (s := ⟨U, hU⟩) hne}, ?_⟩
  intro x
  obtain ⟨c, hc, hx⟩ := A.covers x.val
  refine ⟨c.subtypeRestr (s := ⟨U, hU⟩) ⟨x⟩, ⟨⟨x⟩, c, hc, rfl⟩, ?_⟩
  simpa only [OpenPartialHomeomorph.subtypeRestr_source, Set.mem_preimage] using hx

lemma openPairInclusion_homology_isIso (R : Type u) [CommRing R]
    {M : Type v} [TopologicalSpace M] [T2Space M]
    (U : Set M) (hU : IsOpen U) (K : Support U) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (openPairInclusion M U K)) := by
  obtain ⟨e, he⟩ := P202.CompactSupport.openPairInclusion_factor M U hU K
    (ambientSupport M U K).isCompact.isClosed
  let E := P202.LocalOrientation.openSupportExcisionData U hU (ambientSupport M U K)
    (ambientSupport M U K).isCompact.isClosed (by rintro x ⟨y, _, rfl⟩; exact y.property)
  haveI := P202.LocalOrientation.excision_integer R E j
  rw [he, Functor.map_comp]
  infer_instance

/-- Local generators on an open subset are pulled back by the actual excision map. -/
def openLocalChoice (R : Type u) [CommRing R] {n : ℕ}
    {M : Type v} [TopologicalSpace M] [T2Space M]
    (U : Set M) (hU : IsOpen U) (o : LocalChoice R n M) : LocalChoice R n U := by
  intro x
  haveI := P202.LocalOrientation.openLocalInclusion_isIso R U hU x n
  exact (inv ((relativeHomologyFunctor R R (n : ℤ)).map
    (P202Specs.LocalOrientation.openLocalInclusion U x))) (o x.val)

lemma openLocalChoice_compatible (R : Type u) [CommRing R] {n : ℕ}
    {M : Type v} [TopologicalSpace M] [T2Space M]
    (U : Set M) (hU : IsOpen U) (o : LocalChoice R n M) :
    OpenOrientationCompatible R M o (openLocalChoice R U hU o) := by
  intro x
  haveI := P202.LocalOrientation.openLocalInclusion_isIso R U hU x n
  change ((relativeHomologyFunctor R R (n : ℤ)).map
    (P202Specs.LocalOrientation.openLocalInclusion U x))
    ((inv ((relativeHomologyFunctor R R (n : ℤ)).map
      (P202Specs.LocalOrientation.openLocalInclusion U x))) (o x.val)) = _
  exact congrArg (fun f => f (o x.val))
    (IsIso.inv_hom_id ((relativeHomologyFunctor R R (n : ℤ)).map
      (P202Specs.LocalOrientation.openLocalInclusion U x)))

lemma openLocalChoice_generator (R : Type u) [CommRing R] {n : ℕ}
    {M : Type v} [TopologicalSpace M] [T2Space M]
    (U : Set M) (hU : IsOpen U) (o : LocalChoice R n M)
    (ho : ∀ x, IsGenerator R (o x)) (x : U) :
    IsGenerator R (openLocalChoice R U hU o x) := by
  haveI := P202.LocalOrientation.openLocalInclusion_isIso R U hU x n
  let e := (asIso ((relativeHomologyFunctor R R (n : ℤ)).map
    (P202Specs.LocalOrientation.openLocalInclusion U x))).toLinearEquiv
  apply (P202.LocalOrientation.generator_map_iff R e _).mp
  change IsGenerator R (((relativeHomologyFunctor R R (n : ℤ)).map
    (P202Specs.LocalOrientation.openLocalInclusion U x)) (openLocalChoice R U hU o x))
  rw [openLocalChoice_compatible]
  exact ho x.val

lemma openLocalChoice_orientation (R : Type u) [CommRing R] {n : ℕ}
    {M : Type v} [TopologicalSpace M] (A : Manifold n M) (o : Orientation R A)
    (U : Set M) (hU : IsOpen U) (AU : Manifold n U) :
    letI : T2Space M := A.hausdorff
    IsOrientation R AU (openLocalChoice R U hU o.val) := by
  letI := A.hausdorff
  refine ⟨openLocalChoice_generator R U hU o.val o.property.1, ?_⟩
  intro x
  obtain ⟨B, hxB, _⟩ := P202.LocalOrientation.coordinateBall_basis AU x
    isOpen_univ (Set.mem_univ x)
  let K : Support U := ⟨B.closed, P202.LocalOrientation.ball_closed_compact B⟩
  let f := (relativeHomologyFunctor R R (n : ℤ)).map (openPairInclusion M U K)
  haveI : IsIso f := openPairInclusion_homology_isIso R U hU K n
  let g : SupportedGroup R U B.closed n :=
    (inv f) (P202.CompactSupport.fundamentalClass R M A o (ambientSupport M U K))
  have hg (y : U) (hy : y ∈ B.closed) :
      restrictPoint R hy n g = openLocalChoice R U hU o.val y := by
    haveI := P202.LocalOrientation.openLocalInclusion_isIso R U hU y n
    apply (asIso ((relativeHomologyFunctor R R (n : ℤ)).map
      (P202Specs.LocalOrientation.openLocalInclusion U y))).toLinearEquiv.injective
    change ((relativeHomologyFunctor R R (n : ℤ)).map
      (P202Specs.LocalOrientation.openLocalInclusion U y)) (restrictPoint R hy n g) =
      ((relativeHomologyFunctor R R (n : ℤ)).map
        (P202Specs.LocalOrientation.openLocalInclusion U y)) (openLocalChoice R U hU o.val y)
    rw [openLocalChoice_compatible]
    have hs : openPairInclusion M U K ≫
        pointMap (show y.val ∈ ambientSupport M U K from ⟨y, hy, rfl⟩) =
        pointMap hy ≫ P202Specs.LocalOrientation.openLocalInclusion U y :=
      PairMap.ext _ _ rfl
    have H := congrArg (fun f => f g)
      (congrArg ((relativeHomologyFunctor R R (n : ℤ)).map) hs)
    simp only [Functor.map_comp, ModuleCat.comp_apply] at H
    change restrictPoint R _ n (f g) =
      ((relativeHomologyFunctor R R (n : ℤ)).map
        (P202Specs.LocalOrientation.openLocalInclusion U y)) (restrictPoint R hy n g) at H
    rw [← H]
    change restrictPoint R _ n (f ((inv f)
      (P202.CompactSupport.fundamentalClass R M A o (ambientSupport M U K)))) = _
    have hi : f ((inv f) (P202.CompactSupport.fundamentalClass R M A o
        (ambientSupport M U K))) =
        P202.CompactSupport.fundamentalClass R M A o (ambientSupport M U K) :=
      congrArg (fun h => h (P202.CompactSupport.fundamentalClass R M A o
        (ambientSupport M U K))) (IsIso.inv_hom_id f)
    rw [hi]
    exact P202.CompactSupport.fundamentalClass_values R M A o
      (ambientSupport M U K) y.val ⟨y, hy, rfl⟩
  refine ⟨B, hxB, g, ?_, fun y hy => hg y (B.interior_subset_closed hy)⟩
  apply (P202.LocalOrientation.generator_map_iff R
    (P202.LocalOrientation.ballPointEquiv P202.LocalOrientation.ballRestriction R B hxB) g).mp
  change IsGenerator R (restrictPoint R (B.interior_subset_closed hxB) n g)
  rw [hg]
  exact openLocalChoice_generator R U hU o.val o.property.1 x

def openOrientation (R : Type u) [CommRing R] {n : ℕ}
    {M : Type v} [TopologicalSpace M] (A : Manifold n M) (o : Orientation R A)
    (U : Set M) (hU : IsOpen U) (AU : Manifold n U) : Orientation R AU := by
  letI := A.hausdorff
  exact ⟨openLocalChoice R U hU o.val, openLocalChoice_orientation R A o U hU AU⟩

lemma openOrientation_compatible (R : Type u) [CommRing R] {n : ℕ}
    {M : Type v} [TopologicalSpace M] (A : Manifold n M) (o : Orientation R A)
    (U : Set M) (hU : IsOpen U) (AU : Manifold n U) :
    OpenOrientationCompatible R M o.val (openOrientation R A o U hU AU).val := by
  letI := A.hausdorff
  exact openLocalChoice_compatible R U hU o.val


/-- Local pair inclusion between two actual ambient subsets. -/
def subsetLocalInclusion {M : Type v} [TopologicalSpace M]
    {B E : Set M} (h : B ⊆ E) (x : B) :
    localPair B x ⟶ localPair E
      (P202Specs.CompactSupportMayerVietoris.subsetInclusion h x) where
  map := TopCat.ofHom (P202Specs.CompactSupportMayerVietoris.subsetInclusion h)
  mapsTo := by
    intro y hy he
    exact hy (Subtype.ext (congrArg (fun z : E => z.val) he))

lemma subsetLocalInclusion_compatible (R : Type u) [CommRing R] {n : ℕ}
    {M : Type v} [TopologicalSpace M] [T2Space M]
    {B E : Set M} (h : B ⊆ E) (hE : IsOpen E)
    (oM : LocalChoice R n M) (oB : LocalChoice R n B) (oE : LocalChoice R n E)
    (hB : OpenOrientationCompatible R M oM oB)
    (hEC : OpenOrientationCompatible R M oM oE) (x : B) :
    ((relativeHomologyFunctor R R (n : ℤ)).map (subsetLocalInclusion h x)) (oB x) =
      oE (P202Specs.CompactSupportMayerVietoris.subsetInclusion h x) := by
  let y := P202Specs.CompactSupportMayerVietoris.subsetInclusion h x
  haveI := P202.LocalOrientation.openLocalInclusion_isIso R E hE y n
  apply (asIso ((relativeHomologyFunctor R R (n : ℤ)).map
    (P202Specs.LocalOrientation.openLocalInclusion E y))).toLinearEquiv.injective
  have hs : subsetLocalInclusion h x ≫
      P202Specs.LocalOrientation.openLocalInclusion E y =
      P202Specs.LocalOrientation.openLocalInclusion B x := PairMap.ext _ _ rfl
  have H := congrArg (fun f => f (oB x))
    (congrArg ((relativeHomologyFunctor R R (n : ℤ)).map) hs)
  simp only [Functor.map_comp, ModuleCat.comp_apply] at H
  change ((relativeHomologyFunctor R R (n : ℤ)).map
    (P202Specs.LocalOrientation.openLocalInclusion E y))
      (((relativeHomologyFunctor R R (n : ℤ)).map (subsetLocalInclusion h x)) (oB x)) = _
  rw [H]
  exact (hB x).trans (hEC y).symm

end P202.CompactSupportMV

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMayerVietoris
open P202Specs.CompactSupportMayerVietoris P202Specs.CompactSupport
open P202Specs.LocalOrientation P202Specs.SingularChains

variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

/-- The current gluing interface's union cofinality follows from the stronger
finite closed refinement, which realizes every compact exactly. -/
theorem union_cofinal (C : Cover M) : UnionCofinal M C := by
  intro N
  obtain ⟨⟨K,L⟩, h⟩ := P202.CompactSupportMV.compactUnionCofinal M C.left C.right
    C.left_open C.right_open C.covers N
  exact ⟨K, L, le_of_eq h.symm⟩

/-- Every finite-stage intersection is an actual compact in the intersection
subspace; these compacts are cofinal, including the empty compact. -/
theorem intersection_cofinal (C : Cover M) : IntersectionCofinal M C := by
  constructor
  · intro K L
    exact ⟨P202.CompactSupportMV.intersectionIn M C.left C.right (K,L),
      P202.CompactSupportMV.ambient_intersectionIn M C.left C.right (K,L)⟩
  · intro N
    obtain ⟨⟨K,L⟩, h⟩ := P202.CompactSupportMV.compactIntersectionCofinal M C.left C.right N
    exact ⟨K, L, le_of_eq h.symm⟩

/-- The already proved ordinary finite-chain sequence, with its positive
boundary-of-a-left-lift normalization, supplies the homology row. -/
theorem ordinary_sequence :
    ∃ δ : P202Specs.MayerVietoris.Connecting.{u,v,0} (ordinaryChains R),
      P202Specs.MayerVietoris.Exact (ordinaryChains R) δ ∧
      P202Specs.MayerVietoris.Natural (ordinaryChains R) δ ∧
      P202Specs.MayerVietoris.BoundaryFormula (ordinaryChains R) δ :=
  (P202.MayerVietoris.mayerVietoris R .ordinary).1

/-- The cap square at the sum arrow uses exactly the existing duality maps
and extension maps. It requires only the inherited orientation compatibility. -/
theorem cap_sum (d : DualityData.{u,v} R) (n : ℕ) (A : Manifold n M)
    (o : Orientation R A) (C : Cover M)
    (AL : Manifold n C.left) (AR : Manifold n C.right)
    (oL : Orientation R AL) (oR : Orientation R AR)
    (hL : OpenOrientationCompatible R M o.val oL.val)
    (hR : OpenOrientationCompatible R M o.val oR.val) (p : ℤ) :
    sum R M d C p ≫ ModuleCat.ofHom (d.D n M A o p) =
      biprod.map (ModuleCat.ofHom (d.D n C.left AL oL p))
        (ModuleCat.ofHom (d.D n C.right AR oR p)) ≫
        P202Specs.MayerVietoris.sum (ordinaryChains R) C.ordinary ((n : ℤ)-p) := by
  apply biprod.hom_ext'
  · simp only [sum, P202Specs.MayerVietoris.sum, biprod.inl_desc_assoc,
      biprod.inl_map_assoc, biprod.inl_desc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (d.naturality n M A o C.left C.left_open AL oL hL p a).symm
  · simp only [sum, P202Specs.MayerVietoris.sum, biprod.inr_desc_assoc,
      biprod.inr_map_assoc, biprod.inr_desc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (d.naturality n M A o C.right C.right_open AR oR hR p a).symm

end P202.CompactSupportMayerVietoris

namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open P202Specs.CompactSupport P202Specs.CohomologyPairs
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

/-- The De Morgan identification at the union support, as an actual map
of the original relative cochain complexes. -/
def unionSupportComparison (K L : Support M) :
    supportedCochains R M (K ⊔ L) ⟶
      (finiteSequence R (supportComplements M K L)).X₃ :=
  eqToHom (congrArg (relativeCochains R R)
    (supportComplements_intersection M K L).symm)

/-- The finite-stage connecting arrow with the actual supported cohomology
of K∩L as target. Both its normalization and its comparison are fixed. -/
def supportConnecting (K L : Support M) (p : ℤ) :
    supportedCohomology R M p (K ⊔ L) ⟶
      supportedCohomology R M (p+1) (K ⊓ L) := by
  haveI := finiteSupportComparison R M K L (p+1)
  exact homologyMap (unionSupportComparison R M K L) p ≫
    P202Specs.ChainLES.connecting (finiteShortExact R (supportComplements M K L))
      p (p+1) (by simp) ≫
    inv (homologyMap (supportComparison R M K L) (p+1))

/-- This equality records the positive cochain connecting convention before
excision, rather than specifying it only after extension to the ambient space. -/
lemma supportConnecting_comparison (K L : Support M) (p : ℤ) :
    supportConnecting R M K L p ≫ homologyMap (supportComparison R M K L) (p+1) =
      homologyMap (unionSupportComparison R M K L) p ≫
        P202Specs.ChainLES.connecting (finiteShortExact R (supportComplements M K L))
          p (p+1) (by simp) := by
  haveI := finiteSupportComparison R M K L (p+1)
  simp only [supportConnecting, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

/-- A finite-support connecting value in the actual intersection's compact
cohomology. Naturality in the two supports is the remaining requirement before
this family can be descended to the full compact-support connecting map. -/
def connectingAtSupports (C : P202Specs.CompactSupportMayerVietoris.Cover M)
    (K : Support C.left) (L : Support C.right) (p : ℤ) :
    supportedCohomology R M p
        (ambientSupport M C.left K ⊔ ambientSupport M C.right L) →ₗ[R]
      CompactCohomology R C.intersection (p+1) := by
  let J := intersectionIn M C.left C.right (K,L)
  have hJ := ambient_intersectionIn M C.left C.right (K,L)
  exact (ofSupport R C.intersection (p+1) J).comp
    (supportConnecting R M (ambientSupport M C.left K) (ambientSupport M C.right L) p ≫
      eqToHom (congrArg (supportedCohomology R M (p+1)) hJ.symm) ≫
      openPullback R M C.intersection J (p+1)).hom

end P202.CompactSupportMV

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMayerVietoris
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.CompactSupportMayerVietoris P202Specs.CompactSupport
open P202Specs.LocalOrientation P202Specs.SingularChains
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

/-- Geometric and orientation data for every member of an ordered open cover.
No connectedness, nonemptiness or positive-dimension hypothesis is used. -/
structure OrientedCoverData {n : ℕ} (A : Manifold n M) (o : Orientation R A) (C : Cover M) where
  leftManifold : Manifold n C.left
  rightManifold : Manifold n C.right
  intersectionManifold : Manifold n C.intersection
  leftOrientation : Orientation R leftManifold
  rightOrientation : Orientation R rightManifold
  intersectionOrientation : Orientation R intersectionManifold
  left_compatible : OpenOrientationCompatible R M o.val leftOrientation.val
  right_compatible : OpenOrientationCompatible R M o.val rightOrientation.val
  intersection_compatible : OpenOrientationCompatible R M o.val intersectionOrientation.val

/-- The open cover inherits its manifold structures and ambient orientation. -/
def orientedCoverData {n : ℕ} (A : Manifold n M) (o : Orientation R A) (C : Cover M) :
    OrientedCoverData R M A o C where
  leftManifold := P202.CompactSupportMV.openManifold A C.left C.left_open
  rightManifold := P202.CompactSupportMV.openManifold A C.right C.right_open
  intersectionManifold := P202.CompactSupportMV.openManifold A C.intersection
    (C.left_open.inter C.right_open)
  leftOrientation := P202.CompactSupportMV.openOrientation R A o C.left C.left_open _
  rightOrientation := P202.CompactSupportMV.openOrientation R A o C.right C.right_open _
  intersectionOrientation := P202.CompactSupportMV.openOrientation R A o C.intersection
    (C.left_open.inter C.right_open) _
  left_compatible := P202.CompactSupportMV.openOrientation_compatible R A o C.left C.left_open _
  right_compatible := P202.CompactSupportMV.openOrientation_compatible R A o C.right C.right_open _
  intersection_compatible := P202.CompactSupportMV.openOrientation_compatible R A o C.intersection
    (C.left_open.inter C.right_open) _

end P202.CompactSupportMayerVietoris

namespace P202.CompactSupportMV
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation P202Specs.CompactSupport

lemma dualityData_D_nat_eq (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    {n : ℕ} {X : Type v} [TopologicalSpace X] (A : Manifold n X) (o : Orientation R A)
    (p : ℕ) : d.D n X A o (p : ℤ) = P202.CompactSupport.dualityInt R X A o (p : ℤ) := by
  apply LinearMap.ext
  intro a
  obtain ⟨K, b, rfl⟩ := P202.CompactSupport.representatives R X (p : ℤ) a
  obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((supportedCochains R X K).homologyπ (p : ℤ))).mp inferInstance b
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective
    ((ordinary R R (supportedPair X K)).homologyπ (n : ℤ))).mp inferInstance
      (P202.CompactSupport.fundamentalClass R X A o K)
  obtain ⟨c, hc⟩ := P202.CapProducts.projection_surjective R (supportedPair X K) (n : ℤ)
    ((ordinary R R (supportedPair X K)).iCycles (n : ℤ) z)
  have hzv : P202Specs.CompactOrientation.HasLocalValues R o.val K
      ((ordinary R R (supportedPair X K)).homologyπ (n : ℤ) z) := by
    rw [hz]
    exact P202.CompactSupport.fundamentalClass_values R X A o K
  obtain ⟨v, hv, hd⟩ := d.represents n X A o p K a z c hc hzv
  obtain ⟨w, hw, hcanonical⟩ := P202.CompactSupport.duality_represents R X A o p K a z c hc hzv
  have hvw : v = w := (ModuleCat.mono_iff_injective
    ((ordinaryComplex R R (TopCat.of X)).iCycles ((n : ℤ)-p))).mp inferInstance
      (hv.trans hw.symm)
  rw [hvw] at hd
  exact hd.trans hcanonical.symm

lemma dualityData_D_eq (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    {n : ℕ} {X : Type v} [TopologicalSpace X] (A : Manifold n X) (o : Orientation R A)
    (p : ℤ) : d.D n X A o p = P202.CompactSupport.dualityInt R X A o p := by
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact dualityData_D_nat_eq R d A o p
  · rw [d.negative n X A o p (by omega),
      P202.CompactSupport.dualityInt_negative R X A o p (by omega)]

lemma fundamentalClass_subset (R : Type u) [CommRing R]
    {n : ℕ} {M : Type v} [TopologicalSpace M] [T2Space M]
    {B E : Set M} (h : B ⊆ E) (hE : IsOpen E)
    (AB : Manifold n B) (AE : Manifold n E) (oB : Orientation R AB) (oE : Orientation R AE)
    (oM : LocalChoice R n M)
    (hB : OpenOrientationCompatible R M oM oB.val)
    (hEC : OpenOrientationCompatible R M oM oE.val) (K : Support B) :
    ((relativeHomologyFunctor R R (n : ℤ)).map
      (P202Specs.CompactSupportMayerVietoris.subsetPairInclusion h K))
        (P202.CompactSupport.fundamentalClass R B AB oB K) =
      P202.CompactSupport.fundamentalClass R E AE oE
        (P202Specs.CompactSupportMayerVietoris.supportInSubset h K) := by
  apply P202.CompactOrientation.hasLocalValues_unique R
    (P202.CompactOrientation.localDetection R n E AE
      (P202Specs.CompactSupportMayerVietoris.supportInSubset h K)
      (P202Specs.CompactSupportMayerVietoris.supportInSubset h K).isCompact)
    _ (P202.CompactSupport.fundamentalClass_values R E AE oE _)
  rintro y ⟨x, hx, rfl⟩
  have hs : P202Specs.CompactSupportMayerVietoris.subsetPairInclusion h K ≫
      pointMap (show P202Specs.CompactSupportMayerVietoris.subsetInclusion h x ∈
        P202Specs.CompactSupportMayerVietoris.supportInSubset h K from ⟨x, hx, rfl⟩) =
      pointMap hx ≫ subsetLocalInclusion h x := PairMap.ext _ _ rfl
  have H := congrArg (fun f => f (P202.CompactSupport.fundamentalClass R B AB oB K))
    (congrArg ((relativeHomologyFunctor R R (n : ℤ)).map) hs)
  simp only [Functor.map_comp, ModuleCat.comp_apply] at H
  change restrictPoint R _ n
    (((relativeHomologyFunctor R R (n : ℤ)).map
      (P202Specs.CompactSupportMayerVietoris.subsetPairInclusion h K))
        (P202.CompactSupport.fundamentalClass R B AB oB K)) =
    ((relativeHomologyFunctor R R (n : ℤ)).map (subsetLocalInclusion h x))
      (restrictPoint R hx n (P202.CompactSupport.fundamentalClass R B AB oB K)) at H
  rw [H]
  exact (congrArg (((relativeHomologyFunctor R R (n : ℤ)).map (subsetLocalInclusion h x)))
    (P202.CompactSupport.fundamentalClass_values R B AB oB K x hx)).trans
      (subsetLocalInclusion_compatible R h hE oM oB.val oE.val hB hEC x)

lemma duality_subset_nat (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    {n : ℕ} {M : Type v} [TopologicalSpace M] [T2Space M]
    {B E : Set M} (h : B ⊆ E) (hBO : IsOpen B) (hEO : IsOpen E)
    (AB : Manifold n B) (AE : Manifold n E) (oB : Orientation R AB) (oE : Orientation R AE)
    (oM : LocalChoice R n M)
    (hB : OpenOrientationCompatible R M oM oB.val)
    (hE : OpenOrientationCompatible R M oM oE.val) (p : ℕ)
    (a : CompactCohomology R B (p : ℤ)) :
    homologyMap (P202.CompactSupport.ordinaryMap R
      (TopCat.ofHom (P202Specs.CompactSupportMayerVietoris.subsetInclusion h))) ((n : ℤ)-p)
      (d.D n B AB oB (p : ℤ) a) =
    d.D n E AE oE (p : ℤ) (extendSubset R M h hBO (p : ℤ) a) := by
  rw [dualityData_D_nat_eq, dualityData_D_nat_eq,
    P202.CompactSupport.dualityInt_nat, P202.CompactSupport.dualityInt_nat]
  obtain ⟨K, a, rfl⟩ := P202.CompactSupport.representatives R B (p : ℤ) a
  rw [extendSubset_ofSupport, P202.CompactSupport.duality_ofSupport,
    P202.CompactSupport.duality_ofSupport]
  let b := extendSubsetAt R M h hBO K (p : ℤ) a
  have hb : P202Specs.CompactSupportMayerVietoris.subsetPullback R h K (p : ℤ) b = a :=
    subsetPullback_extendSubsetAt R M h hBO K (p : ℤ) a
  change homologyMap (P202.CompactSupport.ordinaryMap R
    (P202Specs.CompactSupportMayerVietoris.subsetPairInclusion h K).map) ((n : ℤ)-p)
      ((P202.CapProducts.relativeSystem R (supportedPair B K)).homologyOp p (n : ℤ) a
        (P202.CompactSupport.fundamentalClass R B AB oB K)) =
    (P202.CapProducts.relativeSystem R
      (supportedPair E (P202Specs.CompactSupportMayerVietoris.supportInSubset h K))).homologyOp
        p (n : ℤ) b
        (P202.CompactSupport.fundamentalClass R E AE oE
          (P202Specs.CompactSupportMayerVietoris.supportInSubset h K))
  rw [← hb]
  exact (P202.CompactSupport.homologyCap_natural R
    (P202Specs.CompactSupportMayerVietoris.subsetPairInclusion h K) p (n : ℤ) b
    (P202.CompactSupport.fundamentalClass R B AB oB K)).trans
      (congrArg ((P202.CapProducts.relativeSystem R
        (supportedPair E (P202Specs.CompactSupportMayerVietoris.supportInSubset h K))).homologyOp
          p (n : ℤ) b) (fundamentalClass_subset R h hEO AB AE oB oE oM hB hE K))

lemma duality_subset (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    {n : ℕ} {M : Type v} [TopologicalSpace M] [T2Space M]
    {B E : Set M} (h : B ⊆ E) (hBO : IsOpen B) (hEO : IsOpen E)
    (AB : Manifold n B) (AE : Manifold n E) (oB : Orientation R AB) (oE : Orientation R AE)
    (oM : LocalChoice R n M)
    (hB : OpenOrientationCompatible R M oM oB.val)
    (hE : OpenOrientationCompatible R M oM oE.val) (p : ℤ)
    (a : CompactCohomology R B p) :
    homologyMap (P202.CompactSupport.ordinaryMap R
      (TopCat.ofHom (P202Specs.CompactSupportMayerVietoris.subsetInclusion h))) ((n : ℤ)-p)
      (d.D n B AB oB p a) =
    d.D n E AE oE p (extendSubset R M h hBO p a) := by
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact duality_subset_nat R d h hBO hEO AB AE oB oE oM hB hE p a
  · rw [d.negative n B AB oB p (by omega), d.negative n E AE oE p (by omega),
      LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

theorem cap_first (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]
    (d : DualityData.{u,v} R) (n : ℕ) (C : P202Specs.CompactSupportMayerVietoris.Cover M)
    (AL : Manifold n C.left) (AR : Manifold n C.right)
    (AW : Manifold n C.intersection)
    (oL : Orientation R AL) (oR : Orientation R AR) (oW : Orientation R AW)
    (oM : LocalChoice R n M)
    (hL : OpenOrientationCompatible R M oM oL.val)
    (hR : OpenOrientationCompatible R M oM oR.val)
    (hW : OpenOrientationCompatible R M oM oW.val) (p : ℤ) :
    P202Specs.CompactSupportMayerVietoris.first R M C
        (intersectionExtendLeft R M C) (intersectionExtendRight R M C) p ≫
      biprod.map (ModuleCat.ofHom (d.D n C.left AL oL p))
        (ModuleCat.ofHom (d.D n C.right AR oR p)) =
    ModuleCat.ofHom (d.D n C.intersection AW oW p) ≫
      P202Specs.MayerVietoris.first
        (P202Specs.CompactSupportMayerVietoris.ordinaryChains R) C.ordinary ((n : ℤ)-p) := by
  apply biprod.hom_ext
  · simp only [P202Specs.CompactSupportMayerVietoris.first, P202Specs.MayerVietoris.first,
      Category.assoc, biprod.map_fst, biprod.lift_fst_assoc]
    erw [biprod.lift_fst]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (duality_subset R d Set.inter_subset_left (C.left_open.inter C.right_open)
      C.left_open AW AL oW oL oM hW hL p a).symm
  · simp only [P202Specs.CompactSupportMayerVietoris.first, P202Specs.MayerVietoris.first,
      Category.assoc, biprod.map_snd, biprod.lift_snd_assoc]
    erw [biprod.lift_snd]
    rw [Preadditive.neg_comp, Preadditive.comp_neg]
    congr 1
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (duality_subset R d Set.inter_subset_right (C.left_open.inter C.right_open)
      C.right_open AW AR oW oR oM hW hR p a).symm

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CohomologyPairs
open P202Specs.RelativeSingularChains P202Specs.RelativeCupProduct
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

/-- Increasing supports induces the reverse inclusion of their two complements. -/
def supportComplementMap {K L K' L' : Support M} (hK : K ≤ K') (hL : L ≤ L') :
    (supportComplements M K' L').Map (supportComplements M K L) where
  map := 𝟙 _
  left := fun _ hx h => hx (hK h)
  right := fun _ hx h => hx (hL h)

lemma pair_eqToHom_map {P Q : Pair.{v}} (h : P = Q) :
    (eqToHom h).map = eqToHom (congrArg Pair.space h) := by
  cases h
  rfl

lemma pair_sameSpace_eqToHom_map (X : TopCat.{v}) (B E : Set X)
    (h : (⟨X,B⟩ : Pair) = ⟨X,E⟩) : (eqToHom h).map = 𝟙 X := by
  rw [pair_eqToHom_map]
  rfl

lemma supportUnion_pair_square {K L K' L' : Support M} (hK : K ≤ K') (hL : L ≤ L') :
    eqToHom (supportComplements_union M K' L') ≫ supportPairMap M (inf_le_inf hK hL) =
      (supportComplementMap M hK hL).unionMap ≫ eqToHom (supportComplements_union M K L) := by
  apply PairMap.ext
  change (eqToHom (supportComplements_union M K' L')).map ≫ 𝟙 (TopCat.of M) =
    𝟙 (TopCat.of M) ≫ (eqToHom (supportComplements_union M K L)).map
  rw [pair_sameSpace_eqToHom_map, pair_sameSpace_eqToHom_map]
  rfl

lemma supportIntersection_pair_square {K L K' L' : Support M} (hK : K ≤ K') (hL : L ≤ L') :
    eqToHom (supportComplements_intersection M K' L') ≫ supportPairMap M (sup_le_sup hK hL) =
      intersectionMap (supportComplementMap M hK hL) ≫
        eqToHom (supportComplements_intersection M K L) := by
  apply PairMap.ext
  change (eqToHom (supportComplements_intersection M K' L')).map ≫ 𝟙 (TopCat.of M) =
    𝟙 (TopCat.of M) ≫ (eqToHom (supportComplements_intersection M K L)).map
  rw [pair_sameSpace_eqToHom_map, pair_sameSpace_eqToHom_map]
  rfl

lemma relativeCochain_eqToHom {P Q : Pair.{v}} (h : P = Q) :
    (relativeCochainFunctor R R).map (eqToHom h).op =
      eqToHom (congrArg (relativeCochains R R) h.symm) := by
  cases h
  exact (relativeCochainFunctor R R).map_id (op P)

lemma supportComparison_natural {K L K' L' : Support M} (hK : K ≤ K') (hL : L ≤ L') :
    cochainTransition R M (inf_le_inf hK hL) ≫ supportComparison R M K' L' =
      supportComparison R M K L ≫
        P202.RelativeCupProduct.sumCochainMap R (supportComplementMap M hK hL) := by
  have H := congrArg (fun f => (relativeCochainFunctor R R).map f.op)
    (supportUnion_pair_square M hK hL)
  simp only [op_comp, Functor.map_comp, relativeCochain_eqToHom] at H
  change cochainTransition R M (inf_le_inf hK hL) ≫
      eqToHom (congrArg (relativeCochains R R) (supportComplements_union M K' L').symm) =
    eqToHom (congrArg (relativeCochains R R) (supportComplements_union M K L).symm) ≫
      (relativeCochainFunctor R R).map (supportComplementMap M hK hL).unionMap.op at H
  dsimp only [supportComparison]
  rw [← Category.assoc, H, Category.assoc,
    P202.RelativeCupProduct.unionComparison_natural, ← Category.assoc]

lemma unionSupportComparison_natural {K L K' L' : Support M} (hK : K ≤ K') (hL : L ≤ L') :
    cochainTransition R M (sup_le_sup hK hL) ≫ unionSupportComparison R M K' L' =
      unionSupportComparison R M K L ≫
        (relativeCochainFunctor R R).map (intersectionMap (supportComplementMap M hK hL)).op := by
  have H := congrArg (fun f => (relativeCochainFunctor R R).map f.op)
    (supportIntersection_pair_square M hK hL)
  simp only [op_comp, Functor.map_comp, relativeCochain_eqToHom] at H
  exact H

/-- Naturality of the genuine finite-support connecting maps for increasing
both compact supports. -/
lemma supportConnecting_natural {K L K' L' : Support M}
    (hK : K ≤ K') (hL : L ≤ L') (p : ℤ) :
    homologyMap (cochainTransition R M (sup_le_sup hK hL)) p ≫
        supportConnecting R M K' L' p =
      supportConnecting R M K L p ≫
        homologyMap (cochainTransition R M (inf_le_inf hK hL)) (p+1) := by
  let f := supportComplementMap M hK hL
  let δ := P202Specs.ChainLES.connecting (finiteShortExact R (supportComplements M K L))
    p (p+1) (by simp)
  let δ' := P202Specs.ChainLES.connecting (finiteShortExact R (supportComplements M K' L'))
    p (p+1) (by simp)
  let q := P202.RelativeCupProduct.sumCochainMap R f
  let r := (relativeCochainFunctor R R).map (intersectionMap f).op
  have hδ : δ ≫ homologyMap q (p+1) = homologyMap r p ≫ δ' :=
    (P202.ChainLES.naturality (finiteSequenceMap R f)
      (finiteShortExact R (supportComplements M K L))
      (finiteShortExact R (supportComplements M K' L'))).2.2 p (p+1) (by simp)
  have hU : homologyMap (cochainTransition R M (sup_le_sup hK hL)) p ≫
      homologyMap (unionSupportComparison R M K' L') p =
    homologyMap (unionSupportComparison R M K L) p ≫ homologyMap r p := by
    simpa only [homologyMap_comp] using
      congrArg (fun g => homologyMap g p) (unionSupportComparison_natural R M hK hL)
  have hI : homologyMap (cochainTransition R M (inf_le_inf hK hL)) (p+1) ≫
      homologyMap (supportComparison R M K' L') (p+1) =
    homologyMap (supportComparison R M K L) (p+1) ≫ homologyMap q (p+1) := by
    simpa only [homologyMap_comp] using
      congrArg (fun g => homologyMap g (p+1)) (supportComparison_natural R M hK hL)
  haveI := finiteSupportComparison R M K' L' (p+1)
  apply (cancel_mono (homologyMap (supportComparison R M K' L') (p+1))).mp
  rw [Category.assoc, supportConnecting_comparison,
    ← Category.assoc, hU, Category.assoc, ← hδ,
    ← Category.assoc, ← supportConnecting_comparison,
    Category.assoc, ← hI, ← Category.assoc]

lemma supportConnecting_transition {K L K' L' : Support M}
    (hK : K ≤ K') (hL : L ≤ L') (p : ℤ)
    (a : supportedCohomology R M p (K ⊔ L)) :
    supportConnecting R M K' L' p
        (transition R M p (K ⊔ L) (K' ⊔ L') (sup_le_sup hK hL) a) =
      transition R M (p+1) (K ⊓ L) (K' ⊓ L') (inf_le_inf hK hL)
        (supportConnecting R M K L p a) :=
  congrArg (fun f => f a) (supportConnecting_natural R M hK hL p)

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation P202Specs.CompactSupport

variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]

/-- Restriction along a subspace inclusion commutes with an increase of the
compact support, by the square of the actual supported pair maps. -/
lemma openPullback_transition (W : Set M) (p : ℤ) {J J' : Support W} (h : J ≤ J')
    (a : supportedCohomology R M p (ambientSupport M W J)) :
    openPullback R M W J' p
      (transition R M p (ambientSupport M W J) (ambientSupport M W J')
        (ambientSupport_mono M W h) a) =
      transition R W p J J' h (openPullback R M W J p a) := by
  have hs : openPairInclusion M W J' ≫ supportPairMap M (ambientSupport_mono M W h) =
      supportPairMap W h ≫ openPairInclusion M W J := by
    apply PairMap.ext
    rfl
  have H := congrArg ((relativeCohomologyFunctor R R p).map) (congrArg Quiver.Hom.op hs)
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp] at H
  exact congrArg (fun f => f a) H

/-- In compact cohomology the excision pullback is unchanged by increasing the
support in the fixed subspace. No openness assumption is needed for naturality. -/
lemma ofSupport_openPullback_transition (W : Set M) (p : ℤ)
    {J J' : Support W} (h : J ≤ J')
    (a : supportedCohomology R M p (ambientSupport M W J)) :
    ofSupport R W p J'
      (openPullback R M W J' p
        (transition R M p (ambientSupport M W J) (ambientSupport M W J')
          (ambientSupport_mono M W h) a)) =
      ofSupport R W p J (openPullback R M W J p a) := by
  rw [openPullback_transition R M W p h a]
  exact P202.CompactSupport.ofSupport_transition R W p J J' h
    (openPullback R M W J p a)

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CohomologyPairs
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

lemma transition_eqToHom (p : ℤ) {K L K' L' : Support M}
    (hK : K = K') (hL : L = L') (h : K ≤ L) (h' : K' ≤ L') :
    ModuleCat.ofHom (transition R M p K L h) ≫
        eqToHom (congrArg (supportedCohomology R M p) hL) =
      eqToHom (congrArg (supportedCohomology R M p) hK) ≫
        ModuleCat.ofHom (transition R M p K' L' h') := by
  subst K'
  subst L'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

lemma connectingAtSupports_compatible
    (C : P202Specs.CompactSupportMayerVietoris.Cover M) (p : ℤ)
    {K K' : Support C.left} {L L' : Support C.right} (hK : K ≤ K') (hL : L ≤ L')
    (a : supportedCohomology R M p
      (ambientSupport M C.left K ⊔ ambientSupport M C.right L)) :
    connectingAtSupports R M C K' L' p
      (transition R M p
        (ambientSupport M C.left K ⊔ ambientSupport M C.right L)
        (ambientSupport M C.left K' ⊔ ambientSupport M C.right L')
        (sup_le_sup (ambientSupport_mono M C.left hK) (ambientSupport_mono M C.right hL)) a) =
      connectingAtSupports R M C K L p a := by
  let J := intersectionIn M C.left C.right (K,L)
  let J' := intersectionIn M C.left C.right (K',L')
  have hJ : J ≤ J' := intersectionIn_mono M C.left C.right ⟨hK,hL⟩
  have he := ambient_intersectionIn M C.left C.right (K,L)
  have he' := ambient_intersectionIn M C.left C.right (K',L')
  let b := supportConnecting R M (ambientSupport M C.left K) (ambientSupport M C.right L) p a
  change ofSupport R C.intersection (p+1) J'
      (openPullback R M C.intersection J' (p+1)
        ((eqToHom (congrArg (supportedCohomology R M (p+1)) he'.symm))
          (supportConnecting R M (ambientSupport M C.left K') (ambientSupport M C.right L') p
            (transition R M p _ _ _ a)))) =
    ofSupport R C.intersection (p+1) J
      (openPullback R M C.intersection J (p+1)
        ((eqToHom (congrArg (supportedCohomology R M (p+1)) he.symm)) b))
  rw [supportConnecting_transition R M (ambientSupport_mono M C.left hK)
    (ambientSupport_mono M C.right hL) p a]
  have H := congrArg (fun f => f b) (transition_eqToHom R M (p+1) he.symm he'.symm
    (inf_le_inf (ambientSupport_mono M C.left hK) (ambientSupport_mono M C.right hL))
    (ambientSupport_mono M C.intersection hJ))
  change (eqToHom (congrArg (supportedCohomology R M (p+1)) he'.symm))
      (transition R M (p+1) _ _ _ b) =
    transition R M (p+1) _ _ (ambientSupport_mono M C.intersection hJ)
      ((eqToHom (congrArg (supportedCohomology R M (p+1)) he.symm)) b) at H
  exact (congrArg (fun b' : supportedCohomology R M (p+1) (ambientSupport M C.intersection J') =>
      ofSupport R C.intersection (p+1) J'
        (openPullback R M C.intersection J' (p+1) b')) H).trans
    (ofSupport_openPullback_transition R M C.intersection (p+1) hJ _)

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris
namespace ModuleSystem
variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι]

def of (F : ModuleSystem.{u,v,w} R ι) (i : ι) : F.obj i →ₗ[R] F.Limit :=
  Module.DirectLimit.of R ι _ F.transition i

def lift (F : ModuleSystem.{u,v,w} R ι) {V : Type*} [AddCommGroup V] [Module R V]
    (f : ∀ i, F.obj i →ₗ[R] V)
    (hf : ∀ i j h a, f j (F.transition i j h a) = f i a) : F.Limit →ₗ[R] V :=
  Module.DirectLimit.lift R ι _ F.transition f hf

@[simp] lemma lift_of (F : ModuleSystem.{u,v,w} R ι) {V : Type*}
    [AddCommGroup V] [Module R V] (f : ∀ i, F.obj i →ₗ[R] V)
    (hf : ∀ i j h a, f j (F.transition i j h a) = f i a) (i : ι) (a : F.obj i) :
    F.lift f hf (F.of i a) = f i a :=
  Module.DirectLimit.lift_of _ _ _

@[simp] lemma reindexMap_of_system {κ : Type*} [Preorder κ]
    (F : ModuleSystem.{u,v,w} R ι) (φ : κ → ι) (hφ : Monotone φ)
    (i : κ) (a : F.obj (φ i)) :
    F.reindexMap φ hφ ((F.reindex φ hφ).of i a) = F.of (φ i) a :=
  reindexMap_of F φ hφ i a

end ModuleSystem

variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

/-- Canonical cofinal-union identification, with the original Hc(M) as target. -/
def unionColimitEquiv (C : Cover M) (p : ℤ) :
    ((cohomologySystem R M p).reindex (unionSupport M C.left C.right)
      (unionSupport_mono M C.left C.right)).Limit ≃ₗ[R] CompactCohomology R M p :=
  LinearEquiv.ofBijective _ (unionColimit R M C.left C.right
    C.left_open C.right_open C.covers p)

@[simp] lemma unionColimitEquiv_of (C : Cover M) (p : ℤ)
    (s : SupportPair M C.left C.right)
    (a : supportedCohomology R M p (unionSupport M C.left C.right s)) :
    unionColimitEquiv R M C p
      (((cohomologySystem R M p).reindex (unionSupport M C.left C.right)
          (unionSupport_mono M C.left C.right)).of s a) =
      ofSupport R M p (unionSupport M C.left C.right s) a :=
by
  exact ModuleSystem.reindexMap_of_system (cohomologySystem R M p)
    (unionSupport M C.left C.right) (unionSupport_mono M C.left C.right) s a

/-- Compatible linear maps on support pairs descend to the original compact
cohomology module because the unions are cofinal. -/
def descendUnionSupports (C : Cover M) (p : ℤ)
    {V : Type w} [AddCommGroup V] [Module R V]
    (f : ∀ s : SupportPair M C.left C.right,
      supportedCohomology R M p (unionSupport M C.left C.right s) →ₗ[R] V)
    (hf : ∀ s t (h : s ≤ t) a,
      f t (transition R M p _ _ (unionSupport_mono M C.left C.right h) a) = f s a) :
    CompactCohomology R M p →ₗ[R] V :=
  (((cohomologySystem R M p).reindex (unionSupport M C.left C.right)
      (unionSupport_mono M C.left C.right)).lift f hf).comp
        (unionColimitEquiv R M C p).symm.toLinearMap

@[simp] lemma descendUnionSupports_ofSupport (C : Cover M) (p : ℤ)
    {V : Type w} [AddCommGroup V] [Module R V]
    (f : ∀ s : SupportPair M C.left C.right,
      supportedCohomology R M p (unionSupport M C.left C.right s) →ₗ[R] V)
    (hf : ∀ s t (h : s ≤ t) a,
      f t (transition R M p _ _ (unionSupport_mono M C.left C.right h) a) = f s a)
    (s : SupportPair M C.left C.right)
    (a : supportedCohomology R M p (unionSupport M C.left C.right s)) :
    descendUnionSupports R M C p f hf
      (ofSupport R M p (unionSupport M C.left C.right s) a) = f s a := by
  rw [← unionColimitEquiv_of R M C p s a]
  simp only [descendUnionSupports, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, ModuleSystem.lift_of]
  rfl

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

/-- The actual compact-support connecting arrow, descended from the positive
finite cochain connecting maps and valued in the actual intersection subtype. -/
def compactConnecting (C : Cover M) : Connecting R M C :=
  fun p => descendUnionSupports R M C p
    (fun s => connectingAtSupports R M C s.1 s.2 p)
    (fun s t h a => connectingAtSupports_compatible R M C p h.1 h.2 a)

/-- The global connecting arrow retains its finite-support normalization. -/
@[simp] lemma compactConnecting_ofSupport (C : Cover M) (p : ℤ)
    (K : Support C.left) (L : Support C.right)
    (a : supportedCohomology R M p
      (ambientSupport M C.left K ⊔ ambientSupport M C.right L)) :
    compactConnecting R M C p
      (ofSupport R M p (ambientSupport M C.left K ⊔ ambientSupport M C.right L) a) =
      connectingAtSupports R M C K L p a :=
  descendUnionSupports_ofSupport R M C p
    (fun s => connectingAtSupports R M C s.1 s.2 p)
    (fun s t h a => connectingAtSupports_compatible R M C p h.1 h.2 a) (K,L) a

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CohomologyPairs
open P202Specs.RelativeSingularChains P202Specs.RelativeCupProduct
open P202Specs.CompactSupportMayerVietoris P202Specs.LocalOrientation
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

lemma unionSupportComparison_absolute (K L : Support M) :
    unionSupportComparison R M K L ≫
        relativeToAbsolute R R (intersectionPair (supportComplements M K L)) =
      cochainInclusion R M (K ⊔ L) := by
  let e := supportComplements_intersection M K L
  have h := (cochainSequenceMap R R (eqToHom e)).comm₁₂
  change (relativeCochainFunctor R R).map (eqToHom e).op ≫
      relativeToAbsolute R R (intersectionPair (supportComplements M K L)) =
    cochainInclusion R M (K ⊔ L) ≫ (ordinaryCochainFunctor R R).map (eqToHom e).map.op at h
  have hm : (eqToHom e).map = 𝟙 (TopCat.of M) :=
    pair_sameSpace_eqToHom_map _ _ _ e
  have hi : (ordinaryCochainFunctor R R).map (𝟙 (op (TopCat.of M))) =
      𝟙 (ordinaryCochains R R (TopCat.of M)) :=
    (ordinaryCochainFunctor R R).map_id _
  rw [relativeCochain_eqToHom, hm] at h
  change unionSupportComparison R M K L ≫
      relativeToAbsolute R R (intersectionPair (supportComplements M K L)) =
    cochainInclusion R M (K ⊔ L) ≫ (ordinaryCochainFunctor R R).map (𝟙 (op (TopCat.of M))) at h
  rw [hi, Category.comp_id] at h
  exact h

lemma supportedCohomology_eqToHom (q : ℤ) {K L : Support M} (h : K = L) :
    (relativeCohomologyFunctor R R q).map (eqToHom (congrArg (fun S : Support M => supportedPair M (S : Set M)) h)).op =
      eqToHom (congrArg (supportedCohomology R M q) h.symm) := by
  cases h
  exact (relativeCohomologyFunctor R R q).map_id _

lemma intersectionPairMap_supportComparison (C : Cover M)
    (K : Support C.left) (L : Support C.right) (J : Support C.intersection)
    (hJ : ambientSupport M C.intersection J =
      ambientSupport M C.left K ⊓ ambientSupport M C.right L) (q : ℤ) :
    (relativeCohomologyFunctor R R q).map (intersectionPairMap M C K L J hJ).op ≫
        homologyMap (P202Specs.RelativeCupProduct.unionComparison R (complementPair M C K L)) q =
      eqToHom (congrArg (supportedCohomology R M q) hJ) ≫
        homologyMap (supportComparison R M (ambientSupport M C.left K) (ambientSupport M C.right L)) q := by
  let e := supportComplements_union M (ambientSupport M C.left K) (ambientSupport M C.right L)
  have hp : intersectionPairMap M C K L J hJ =
      eqToHom e ≫ eqToHom (congrArg (fun S : Support M => supportedPair M (S : Set M)) hJ.symm) := by
    apply PairMap.ext
    change 𝟙 (TopCat.of M) =
      (eqToHom e).map ≫ (eqToHom (congrArg (fun S : Support M => supportedPair M (S : Set M)) hJ.symm)).map
    rw [pair_sameSpace_eqToHom_map, pair_sameSpace_eqToHom_map]
    rfl
  have he : (relativeCohomologyFunctor R R q).map (eqToHom e).op =
      homologyMap (eqToHom (congrArg (relativeCochains R R) e.symm)) q := by
    change homologyMap ((relativeCochainFunctor R R).map (eqToHom e).op) q = _
    rw [relativeCochain_eqToHom]
  rw [hp, op_comp, Functor.map_comp, supportedCohomology_eqToHom R M q hJ.symm, he, Category.assoc]
  change _ = _ ≫ homologyMap
    (eqToHom (congrArg (relativeCochains R R) e.symm) ≫
      P202Specs.RelativeCupProduct.unionComparison R (complementPair M C K L)) q
  rw [homologyMap_comp]

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.CompactSupport P202Specs.CohomologyPairs
open P202Specs.RelativeSingularChains P202Specs.RelativeCupProduct
open P202Specs.CompactSupportMayerVietoris P202Specs.LocalOrientation
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

/-- The descended connecting homomorphism has the actual positive supported
cochain splitting formula, with its value retained in compact cohomology of the
intersection. -/
theorem compactConnecting_formula (C : Cover M) :
    ConnectingFormula R M C (compactConnecting R M C) := by
  intro K L p a
  let U := ambientSupport M C.left K
  let V := ambientSupport M C.right L
  let P := supportComplements M U V
  let F := unionSupportComparison R M U V
  let a' := cyclesMap F p a
  obtain ⟨aP, aQ, z, hsplit, hcob, hconn⟩ := finiteCycleSplitting R P p a'
  let J := intersectionIn M C.left C.right (K,L)
  have hJ : ambientSupport M C.intersection J = U ⊓ V :=
    ambient_intersectionIn M C.left C.right (K,L)
  let b₀ := supportConnecting R M U V p ((supportedCochains R M (U ⊔ V)).homologyπ p a)
  let b : supportedCohomology R M (p+1) (ambientSupport M C.intersection J) :=
    (eqToHom (congrArg (supportedCohomology R M (p+1)) hJ.symm)) b₀
  refine ⟨J, hJ, aP, aQ, z, b, ?_, hcob, ?_, ?_⟩
  · have ha' : (relativeCochains R R (intersectionPair P)).iCycles p a' =
        F.f p ((supportedCochains R M (U ⊔ V)).iCycles p a) :=
      congrArg (fun f => f a) (cyclesMap_i F p)
    calc
      (cochainInclusion R M U).f p aP + (cochainInclusion R M V).f p aQ =
          (relativeToAbsolute R R (intersectionPair P)).f p
            ((relativeCochains R R (intersectionPair P)).iCycles p a') := hsplit
      _ = (relativeToAbsolute R R (intersectionPair P)).f p
          (F.f p ((supportedCochains R M (U ⊔ V)).iCycles p a)) :=
        congrArg ((relativeToAbsolute R R (intersectionPair P)).f p) ha'
      _ = _ := congrArg
        (fun f => f.f p ((supportedCochains R M (U ⊔ V)).iCycles p a))
        (unionSupportComparison_absolute R M U V)
  · have hb₀ : homologyMap (supportComparison R M U V) (p+1) b₀ =
        (sumCochains R P).homologyπ (p+1) z := by
      have H := congrArg (fun f => f ((supportedCochains R M (U ⊔ V)).homologyπ p a))
        (supportConnecting_comparison R M U V p)
      change homologyMap (supportComparison R M U V) (p+1) b₀ =
        P202Specs.ChainLES.connecting (finiteShortExact R P) p (p+1) (by simp)
          (homologyMap F p ((supportedCochains R M (U ⊔ V)).homologyπ p a)) at H
      have hπ : homologyMap F p ((supportedCochains R M (U ⊔ V)).homologyπ p a) =
          (relativeCochains R R (intersectionPair P)).homologyπ p a' :=
        congrArg (fun f => f a) (homologyπ_naturality F p)
      exact H.trans ((congrArg
        (P202Specs.ChainLES.connecting (finiteShortExact R P) p (p+1) (by simp)) hπ).trans hconn)
    have hcast : (eqToHom (congrArg (supportedCohomology R M (p+1)) hJ)) b = b₀ := by
      change ((eqToHom (congrArg (supportedCohomology R M (p+1)) hJ.symm)) ≫
        eqToHom (congrArg (supportedCohomology R M (p+1)) hJ)) b₀ = b₀
      rw [eqToHom_trans]
      rfl
    have H := congrArg (fun f => f b) (intersectionPairMap_supportComparison R M C K L J hJ (p+1))
    exact H.trans ((congrArg (homologyMap (supportComparison R M U V) (p+1)) hcast).trans hb₀)
  · exact compactConnecting_ofSupport R M C p K L
      ((supportedCochains R M (U ⊔ V)).homologyπ p a)

end P202.CompactSupportMV

/-! Further finite-chain, representative, and edge-degree gluing lemmas. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Classical
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV
variable {R : Type u} [CommRing R]

lemma cochain_class_zero_iff (K : CochainComplex (ModuleCat.{v} R) ℤ) (p : ℤ)
    (z : K.cycles (p+1)) : K.homologyπ (p+1) z = 0 ↔
      ∃ x : K.X p, K.d p (p+1) x = K.iCycles (p+1) z := by
  change (K.sc (p+1)).homologyπ z = 0 ↔ _
  rw [P202.CupProduct.shortComplex_homologyπ_eq_zero_iff]
  change (∃ x : K.X ((ComplexShape.up ℤ).prev (p+1)), K.d _ _ x = K.iCycles _ z) ↔ _
  rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel p (p+1) by simp)]

/-- A cohomology comparison lifts a cycle up to an actual coboundary. -/
lemma cycle_representative_adjustment
    {K : CochainComplex (ModuleCat.{v} R) ℤ}
    {L : CochainComplex (ModuleCat.{v} R) ℤ}
    (f : K ⟶ L) (p : ℤ) [IsIso (homologyMap f (p+1))]
    (z : L.cycles (p+1)) :
    ∃ (b : K.cycles (p+1)) (r : L.X p),
      L.iCycles (p+1) z = f.f (p+1) (K.iCycles (p+1) b) + L.d p (p+1) r ∧
      K.homologyπ (p+1) b = inv (homologyMap f (p+1)) (L.homologyπ (p+1) z) := by
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ (p+1))).mp inferInstance
    (inv (homologyMap f (p+1)) (L.homologyπ (p+1) z))
  have hfb : L.homologyπ (p+1) (cyclesMap f (p+1) b) = L.homologyπ (p+1) z := by
    rw [← ModuleCat.comp_apply, ← homologyπ_naturality, ModuleCat.comp_apply, hb]
    change (inv (homologyMap f (p+1)) ≫ homologyMap f (p+1)) _ = _
    rw [IsIso.inv_hom_id]
    rfl
  have hz : L.homologyπ (p+1) (z - cyclesMap f (p+1) b) = 0 := by
    rw [map_sub, hfb, sub_self]
  obtain ⟨r, hr⟩ := (cochain_class_zero_iff L p _).mp hz
  refine ⟨b, r, ?_, hb⟩
  rw [map_sub] at hr
  have hi : L.iCycles (p+1) (cyclesMap f (p+1) b) = f.f (p+1) (K.iCycles (p+1) b) :=
    congrArg (fun g => g b) (cyclesMap_i f (p+1))
  rw [hi] at hr
  exact (sub_eq_iff_eq_add.mp hr.symm).trans (add_comm _ _)

open P202Specs.CompactSupport P202Specs.CohomologyPairs
open P202Specs.RelativeSingularChains P202Specs.RelativeCupProduct
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

lemma supportComparison_absolute (K L : Support M) :
    supportComparison R M K L ≫ sumToAbsolute R (supportComplements M K L) =
      cochainInclusion R M (K ⊓ L) := by
  let e := supportComplements_union M K L
  have h := (cochainSequenceMap R R (eqToHom e)).comm₁₂
  change (relativeCochainFunctor R R).map (eqToHom e).op ≫
      relativeToAbsolute R R (supportComplements M K L).unionPair =
    cochainInclusion R M (K ⊓ L) ≫ (ordinaryCochainFunctor R R).map (eqToHom e).map.op at h
  have hm : (eqToHom e).map = 𝟙 (TopCat.of M) :=
    pair_sameSpace_eqToHom_map _ _ _ e
  have hi : (ordinaryCochainFunctor R R).map (𝟙 (op (TopCat.of M))) =
      𝟙 (ordinaryCochains R R (TopCat.of M)) :=
    (ordinaryCochainFunctor R R).map_id _
  rw [relativeCochain_eqToHom, hm] at h
  change eqToHom (congrArg (relativeCochains R R) e.symm) ≫
      relativeToAbsolute R R (supportComplements M K L).unionPair =
    cochainInclusion R M (K ⊓ L) ≫ (ordinaryCochainFunctor R R).map (𝟙 (op (TopCat.of M))) at h
  rw [hi, Category.comp_id] at h
  change (eqToHom (congrArg (relativeCochains R R) e.symm) ≫
    P202Specs.RelativeCupProduct.unionComparison R (supportComplements M K L)) ≫ _ = _
  rw [Category.assoc, P202.RelativeCupProduct.comparison_absolute]
  exact h

private lemma split_sub_add_cancel {B : Type*} [AddCommGroup B] (x y s : B) :
    (x-s) + (y+s) = x+y := by abel

set_option maxHeartbeats 1000000 in
/-- The supported connecting class has a supported cocycle representative whose
absolute cochain is exactly the left coboundary of a compatible splitting. -/
theorem supportCycleSplitting (K L : Support M) (p : ℤ)
    (a : (supportedCochains R M (K ⊔ L)).cycles p) :
    ∃ (aP : (supportedCochains R M K).X p)
      (aQ : (supportedCochains R M L).X p)
      (b : (supportedCochains R M (K ⊓ L)).cycles (p+1)),
      (cochainInclusion R M K).f p aP + (cochainInclusion R M L).f p aQ =
        (cochainInclusion R M (K ⊔ L)).f p
          ((supportedCochains R M (K ⊔ L)).iCycles p a) ∧
      (cochainInclusion R M (K ⊓ L)).f (p+1)
          ((supportedCochains R M (K ⊓ L)).iCycles (p+1) b) =
        (ordinaryCochains R R (TopCat.of M)).d p (p+1)
          ((cochainInclusion R M K).f p aP) ∧
      supportConnecting R M K L p ((supportedCochains R M (K ⊔ L)).homologyπ p a) =
        (supportedCochains R M (K ⊓ L)).homologyπ (p+1) b := by
  let P := supportComplements M K L
  let F := unionSupportComparison R M K L
  let a' := cyclesMap F p a
  obtain ⟨aP, aQ, z, hsplit, hcob, hconn⟩ := finiteCycleSplitting R P p a'
  haveI := finiteSupportComparison R M K L (p+1)
  obtain ⟨b, r, hz, hb⟩ := cycle_representative_adjustment (supportComparison R M K L) p z
  let s := (sumToAbsolute R P).f p r
  have hrL : (cochainInclusion R M K).f p ((sumToLeft R P).f p r) = s :=
    congrArg (fun g => g.f p r) (sumToLeft_absolute R P)
  have hrR : (cochainInclusion R M L).f p ((sumToRight R P).f p r) = s :=
    congrArg (fun g => g.f p r) (sumToRight_absolute R P)
  have hπ : homologyMap F p ((supportedCochains R M (K ⊔ L)).homologyπ p a) =
      (relativeCochains R R (intersectionPair P)).homologyπ p a' :=
    congrArg (fun g => g a) (homologyπ_naturality F p)
  refine ⟨aP - (sumToLeft R P).f p r, aQ + (sumToRight R P).f p r, b, ?_, ?_, ?_⟩
  · rw [map_sub, map_add, hrL, hrR]
    have ha' : (relativeCochains R R (intersectionPair P)).iCycles p a' =
        F.f p ((supportedCochains R M (K ⊔ L)).iCycles p a) :=
      congrArg (fun g => g a) (cyclesMap_i F p)
    have H : (cochainInclusion R M K).f p aP + (cochainInclusion R M L).f p aQ =
        (cochainInclusion R M (K ⊔ L)).f p
          ((supportedCochains R M (K ⊔ L)).iCycles p a) := by
      calc
        _ = (relativeToAbsolute R R (intersectionPair P)).f p
              ((relativeCochains R R (intersectionPair P)).iCycles p a') := hsplit
        _ = _ := by
          rw [ha']
          exact congrArg (fun g => g.f p ((supportedCochains R M (K ⊔ L)).iCycles p a))
            (unionSupportComparison_absolute R M K L)
    calc
      _ = (cochainInclusion R M K).f p aP + (cochainInclusion R M L).f p aQ :=
        split_sub_add_cancel (B := (ordinaryCochains R R (TopCat.of M)).X p) _ _ _
      _ = _ := H
  · rw [map_sub, hrL, map_sub]
    have H := congrArg ((sumToAbsolute R P).f (p+1)) hz
    rw [map_add] at H
    have Hf : (sumToAbsolute R P).f (p+1)
        ((supportComparison R M K L).f (p+1)
          ((supportedCochains R M (K ⊓ L)).iCycles (p+1) b)) =
        (cochainInclusion R M (K ⊓ L)).f (p+1)
          ((supportedCochains R M (K ⊓ L)).iCycles (p+1) b) :=
      congrArg (fun g => g.f (p+1) ((supportedCochains R M (K ⊓ L)).iCycles (p+1) b))
        (supportComparison_absolute R M K L)
    have Hd : (sumToAbsolute R P).f (p+1) ((sumCochains R P).d p (p+1) r) =
        (ordinaryCochains R R (TopCat.of M)).d p (p+1) s :=
      (congrArg (fun g => g r) ((sumToAbsolute R P).comm p (p+1))).symm
    rw [hcob, Hf, Hd] at H
    exact (eq_sub_iff_add_eq).mpr H.symm
  · change inv (homologyMap (supportComparison R M K L) (p+1))
      (P202Specs.ChainLES.connecting (finiteShortExact R P) p (p+1) (by simp)
        (homologyMap F p ((supportedCochains R M (K ⊔ L)).homologyπ p a))) = _
    rw [hπ, hconn]
    exact hb.symm

open P202Specs.CompactSupportMayerVietoris

lemma supportHomology_cast (q : ℤ) {K L : Support M} (h : K = L) :
    homologyMap (eqToHom (congrArg (supportedCochains R M) h)) q =
      eqToHom (congrArg (supportedCohomology R M q) h) := by
  cases h
  simp only [eqToHom_refl, homologyMap_id]

/-- Restrict the actual support intersection to the actual open intersection. -/
def intersectionCochainRestriction (C : Cover M)
    (K : Support C.left) (L : Support C.right) :
    supportedCochains R M
      (ambientSupport M C.left K ⊓ ambientSupport M C.right L) ⟶
      supportedCochains R C.intersection (intersectionIn M C.left C.right (K,L)) :=
  eqToHom (congrArg (supportedCochains R M)
    (ambient_intersectionIn M C.left C.right (K,L)).symm) ≫
    (relativeCochainFunctor R R).map
      (openPairInclusion M C.intersection (intersectionIn M C.left C.right (K,L))).op

lemma intersectionCochainRestriction_homology (C : Cover M)
    (K : Support C.left) (L : Support C.right) (q : ℤ) :
    homologyMap (intersectionCochainRestriction R M C K L) q =
      eqToHom (congrArg (supportedCohomology R M q)
        (ambient_intersectionIn M C.left C.right (K,L)).symm) ≫
      openPullback R M C.intersection (intersectionIn M C.left C.right (K,L)) q := by
  rw [intersectionCochainRestriction, homologyMap_comp,
    supportHomology_cast R M q (ambient_intersectionIn M C.left C.right (K,L)).symm]
  rfl

/-- The global connecting map on a finite representative can be evaluated on
an actual supported cocycle of the intersection, before any ambient extension. -/
lemma compactConnecting_ofCycle (C : Cover M)
    (K : Support C.left) (L : Support C.right) (p : ℤ)
    (a : supportedCohomology R M p
      (ambientSupport M C.left K ⊔ ambientSupport M C.right L))
    (b : (supportedCochains R M
      (ambientSupport M C.left K ⊓ ambientSupport M C.right L)).cycles (p+1))
    (hb : supportConnecting R M (ambientSupport M C.left K) (ambientSupport M C.right L) p a =
      (supportedCochains R M
        (ambientSupport M C.left K ⊓ ambientSupport M C.right L)).homologyπ (p+1) b) :
    compactConnecting R M C p
      (ofSupport R M p (ambientSupport M C.left K ⊔ ambientSupport M C.right L) a) =
      ofSupport R C.intersection (p+1) (intersectionIn M C.left C.right (K,L))
        ((supportedCochains R C.intersection
          (intersectionIn M C.left C.right (K,L))).homologyπ (p+1)
            (cyclesMap (intersectionCochainRestriction R M C K L) (p+1) b)) := by
  rw [compactConnecting_ofSupport]
  let J := intersectionIn M C.left C.right (K,L)
  let f := intersectionCochainRestriction R M C K L
  calc
    connectingAtSupports R M C K L p a =
        ofSupport R C.intersection (p+1) J
          (homologyMap f (p+1)
            (supportConnecting R M (ambientSupport M C.left K) (ambientSupport M C.right L) p a)) := by
      rw [show f = intersectionCochainRestriction R M C K L from rfl,
        intersectionCochainRestriction_homology]
      rfl
    _ = ofSupport R C.intersection (p+1) J
          (homologyMap f (p+1)
            ((supportedCochains R M
              (ambientSupport M C.left K ⊓ ambientSupport M C.right L)).homologyπ (p+1) b)) := by rw [hb]
    _ = _ := congrArg (ofSupport R C.intersection (p+1) J)
      (congrArg (fun g => g b) (homologyπ_naturality f (p+1)))
end P202.CompactSupportMV


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.CompactSupportMV
open P202Specs.CompactSupportMayerVietoris P202Specs.CompactSupport
open P202Specs.SingularChains P202Specs.LocalOrientation
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

lemma ofSupport_openPullback_eq_zero_iff (U : Set M) (hU : IsOpen U) (p : ℤ)
    (K : Support U) (b : supportedCohomology R M p (ambientSupport M U K)) :
    ofSupport R U p K (openPullback R M U K p b) = 0 ↔
      ∃ (K' : Support U) (h : K ≤ K'),
        transition R M p (ambientSupport M U K) (ambientSupport M U K')
          (ambientSupport_mono M U h) b = 0 := by
  constructor
  · intro hb
    have he : ofSupport R U p K (openPullback R M U K p b) = ofSupport R U p K 0 := by
      simpa using hb
    obtain ⟨K', hKK', _, htrans⟩ :=
      (P202.CompactSupport.equalityWitness R U p K K (openPullback R M U K p b) 0).mp he
    refine ⟨K', hKK', ?_⟩
    haveI := P202.CompactSupport.openExcision R M U hU K' p
    apply (ModuleCat.mono_iff_injective (openPullback R M U K' p)).mp inferInstance
    rw [openPullback_transition R M U p hKK' b]
    simpa using htrans
  · rintro ⟨K', hKK', htrans⟩
    rw [← ofSupport_openPullback_transition R M U p hKK' b, htrans]
    simp

lemma exists_openPullback_representative (U : Set M) (hU : IsOpen U) (p : ℤ)
    (a : CompactCohomology R U p) :
    ∃ (K : Support U) (b : supportedCohomology R M p (ambientSupport M U K)),
      a = ofSupport R U p K (openPullback R M U K p b) := by
  obtain ⟨K, b, hb⟩ := P202.CompactSupport.representatives R U p a
  haveI := P202.CompactSupport.openExcision R M U hU K p
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (openPullback R M U K p)).mp inferInstance b
  exact ⟨K, c, hb.symm.trans (congrArg (ofSupport R U p K) hc).symm⟩

end P202.CompactSupportMV


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.CompactSupportMV
open P202Specs.CompactSupportMayerVietoris P202Specs.CompactSupport
open P202Specs.SingularChains P202Specs.RelativeSingularChains P202Specs.LocalOrientation

variable (R : Type u) [CommRing R] (X : TopCat.{v})

abbrev ordinarySubspaceRange (B : Set X) (j : ℤ) :
    Submodule R ((ordinaryComplex R R X).X j) :=
  ((inclusion (ordinaryFunctor R R) ⟨X,B⟩).f j).hom.range

lemma ordinary_subspace_injective (B : Set X) (j : ℤ) :
    Function.Injective ((inclusion (ordinaryFunctor R R) ⟨X,B⟩).f j) :=
  (ModuleCat.mono_iff_injective _).mp inferInstance

lemma ordinarySubspaceRange_d {B : Set X} {i j : ℤ}
    (c : (ordinaryComplex R R X).X i) (hc : c ∈ ordinarySubspaceRange R X B i) :
    (ordinaryComplex R R X).d i j c ∈ ordinarySubspaceRange R X B j := by
  obtain ⟨b, rfl⟩ := hc
  refine ⟨(ordinaryComplex R R (TopCat.of B)).d i j b, ?_⟩
  exact congrArg (fun f => f b) ((inclusion (ordinaryFunctor R R) ⟨X,B⟩).comm i j).symm

lemma ordinarySubspaceRange_mono {B E : Set X} (h : B ⊆ E) (j : ℤ) :
    ordinarySubspaceRange R X B j ≤ ordinarySubspaceRange R X E j := by
  intro c hc
  obtain ⟨b, rfl⟩ := hc
  let f : TopCat.of B ⟶ TopCat.of E := TopCat.ofHom (subsetInclusion h)
  refine ⟨((ordinaryFunctor R R).map f).f j b, ?_⟩
  have hf : f ≫ (Pair.inclusion ⟨X,E⟩) = Pair.inclusion ⟨X,B⟩ := rfl
  have hm := congrArg (fun k => k.f j b) ((ordinaryFunctor R R).map_comp f (Pair.inclusion ⟨X,E⟩))
  change ((ordinaryFunctor R R).map (f ≫ Pair.inclusion ⟨X,E⟩)).f j b =
    ((inclusion (ordinaryFunctor R R) ⟨X,E⟩).f j) (((ordinaryFunctor R R).map f).f j b) at hm
  exact hm.symm.trans (congrArg (fun k => ((ordinaryFunctor R R).map k).f j b) hf)

lemma ordinarySubspaceRange_nat_iff (B : Set X) (j : ℕ)
    (c : (ordinaryComplex R R X).X (j : ℤ)) :
    c ∈ ordinarySubspaceRange R X B (j : ℤ) ↔
      (ordinaryNonnegativeIso R R X j).hom c ∈
        ((chainMap R R (Pair.inclusion ⟨X,B⟩)).f j).hom.range := by
  constructor
  · rintro ⟨b, rfl⟩
    refine ⟨(ordinaryNonnegativeIso R R (TopCat.of B) j).hom b, ?_⟩
    exact (P202.CapProducts.ordinary_chainMap_hom R (Pair.inclusion ⟨X,B⟩) j b).symm
  · rintro ⟨b, hb⟩
    refine ⟨(ordinaryNonnegativeIso R R (TopCat.of B) j).inv b, ?_⟩
    apply (ModuleCat.mono_iff_injective (ordinaryNonnegativeIso R R X j).hom).mp inferInstance
    rw [P202.CapProducts.ordinary_chainMap_hom]
    simpa using hb

lemma ordinarySubspaceRange_intersection (B E : Set X) (j : ℤ) :
    ordinarySubspaceRange R X (B ∩ E) j =
      ordinarySubspaceRange R X B j ⊓ ordinarySubspaceRange R X E j := by
  ext c
  by_cases hj : 0 ≤ j
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    simp only [Submodule.mem_inf, ordinarySubspaceRange_nat_iff]
    rw [← Submodule.mem_inf, ← P202.MayerVietoris.range_intersection R X B E j]
  · haveI : Subsingleton ((ordinaryComplex R R X).X j) :=
      ModuleCat.subsingleton_of_isZero
        (P202.SingularChains.ordinary_negative_chains R R X j (by omega))
    have hc : c = 0 := Subsingleton.elim c 0
    subst c
    simp

lemma ordinarySubspaceRange_preimage (B E : Set X) (j : ℤ)
    (c : (ordinaryComplex R R (TopCat.of B)).X j) :
    (inclusion (ordinaryFunctor R R) ⟨X,B⟩).f j c ∈ ordinarySubspaceRange R X E j ↔
      c ∈ ordinarySubspaceRange R (TopCat.of B) (Subtype.val ⁻¹' E) j := by
  let S : Set B := Subtype.val ⁻¹' E
  constructor
  · intro hc
    have hi : (inclusion (ordinaryFunctor R R) ⟨X,B⟩).f j c ∈
        ordinarySubspaceRange R X (B ∩ E) j := by
      rw [ordinarySubspaceRange_intersection]
      exact ⟨⟨c, rfl⟩, hc⟩
    obtain ⟨d, hd⟩ := hi
    let f : TopCat.of ↥(B ∩ E) ⟶ TopCat.of S := TopCat.ofHom
      ⟨fun x => ⟨⟨x.val, x.property.1⟩, x.property.2⟩,
        (continuous_subtype_val.subtype_mk _).subtype_mk _⟩
    refine ⟨((ordinaryFunctor R R).map f).f j d, ?_⟩
    apply ordinary_subspace_injective R X B j
    let g : TopCat.of S ⟶ X := Pair.inclusion ⟨TopCat.of B,S⟩ ≫ Pair.inclusion ⟨X,B⟩
    have hg : f ≫ g = Pair.inclusion ⟨X,B ∩ E⟩ := rfl
    have hmap := congrArg (fun k => k.f j d) ((ordinaryFunctor R R).map_comp f g)
    rw [hg] at hmap
    have hcompose := congrArg (fun k => k.f j (((ordinaryFunctor R R).map f).f j d))
      ((ordinaryFunctor R R).map_comp (Pair.inclusion ⟨TopCat.of B,S⟩) (Pair.inclusion ⟨X,B⟩))
    exact hcompose.symm.trans (hmap.symm.trans hd)
  · rintro ⟨d, rfl⟩
    let f : TopCat.of S ⟶ TopCat.of E := TopCat.ofHom
      ⟨fun x => ⟨x.val.val, x.property⟩,
        (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
    refine ⟨((ordinaryFunctor R R).map f).f j d, ?_⟩
    have hf : f ≫ Pair.inclusion ⟨X,E⟩ =
        Pair.inclusion ⟨TopCat.of B,S⟩ ≫ Pair.inclusion ⟨X,B⟩ := rfl
    have H := congrArg (fun k => k.f j d) (congrArg ((ordinaryFunctor R R).map) hf)
    simp only [Functor.map_comp, HomologicalComplex.comp_f, ModuleCat.comp_apply] at H
    exact H

end P202.CompactSupportMV


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Classical
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris
open P202Specs.SmallChainHomology

/-- An arbitrary relative homology class has a lift with chains subordinate to
any prescribed open cover. The class and all maps are the ordinary singular ones. -/
lemma small_relative_cycle_lift (R : Type u) [CommRing R] (X : TopCat.{v})
    {ι : Type w} (T : OpenCover X ι) (A : Set X) (n : ℕ)
    (a : (ordinary R R ⟨X, A⟩).homology (n : ℤ)) :
    ∃ (c : (ordinaryComplex R R X).X (n : ℤ))
      (z : (ordinary R R ⟨X, A⟩).cycles (n : ℤ)),
      (projection (ordinaryFunctor R R) ⟨X, A⟩).f (n : ℤ) c =
        (ordinary R R ⟨X, A⟩).iCycles (n : ℤ) z ∧
      (ordinary R R ⟨X, A⟩).homologyπ (n : ℤ) z = a ∧
      (ordinaryNonnegativeIso R R X n).hom c ∈ smallModule R T n := by
  let e := degreeEmbedding 0
  let S := smallRelativeComplex R T A
  let q := cokernel.π (smallSubspaceInclusion R T A)
  let f : S.extend e ⟶ ordinary R R ⟨X, A⟩ :=
    extendMap (smallRelativeInclusion R T A) e ≫
      (P202.LocalOrientation.relativeExtensionIso R ⟨X, A⟩).inv
  haveI : QuasiIso (smallRelativeInclusion R T A) := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact P202.SmallChainHomology.relativeComparison R X ι T A k
  haveI : QuasiIso f := inferInstance
  obtain ⟨y, hy⟩ := (ModuleCat.epi_iff_surjective ((S.extend e).homologyπ (n : ℤ))).mp
    inferInstance ((inv (homologyMap f (n : ℤ))) a)
  have hS := P202.MayerVietoris.extend_shortExact e
    (ShortComplex.cokernelSequence (smallSubspaceInclusion R T A))
    (P202.SmallChainHomology.smallSequence_shortExact R X T A)
  haveI : Epi (extendMap q e) := hS.epi_g
  obtain ⟨b, hb⟩ := (ModuleCat.epi_iff_surjective ((extendMap q e).f (n : ℤ))).mp
    inferInstance ((S.extend e).iCycles (n : ℤ) y)
  let c := (extendMap (smallInclusion R T) e).f (n : ℤ) b
  let z := cyclesMap f (n : ℤ) y
  refine ⟨c, z, ?_, ?_, ?_⟩
  · have hq : q ≫ smallRelativeInclusion R T A =
        smallInclusion R T ≫ projection (chainFunctor R R) ⟨X, A⟩ :=
      cokernel.π_desc _ _ _
    have hf : extendMap q e ≫ f =
        extendMap (smallInclusion R T) e ≫ projection (ordinaryFunctor R R) ⟨X, A⟩ := by
      dsimp [f]
      rw [← Category.assoc, ← extendMap_comp, hq, extendMap_comp]
      rw [Category.assoc]
      congr 1
      apply (cancel_mono (P202.LocalOrientation.relativeExtensionIso R ⟨X, A⟩).hom).mp
      rw [Category.assoc, Iso.inv_hom_id, Category.comp_id,
        P202.LocalOrientation.relativeExtensionIso_projection]
    change (projection (ordinaryFunctor R R) ⟨X, A⟩).f (n : ℤ)
      ((extendMap (smallInclusion R T) e).f (n : ℤ) b) =
        (ordinary R R ⟨X, A⟩).iCycles (n : ℤ) (cyclesMap f (n : ℤ) y)
    have H := congrArg (fun g => g.f (n : ℤ) b) hf
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply, hb] at H
    exact H.symm.trans (congrArg (fun h => h y) (cyclesMap_i f (n : ℤ))).symm
  · change (ordinary R R ⟨X, A⟩).homologyπ (n : ℤ) (cyclesMap f (n : ℤ) y) = a
    rw [← ModuleCat.comp_apply, ← homologyπ_naturality, ModuleCat.comp_apply, hy]
    exact Iso.inv_hom_id_apply (asIso (homologyMap f (n : ℤ))) a
  · dsimp [c]
    rw [extendMap_f _ e (i := n) (by change (0 : ℤ) + n = n; omega)]
    change (ordinaryNonnegativeIso R R X n).hom
      ((ordinaryNonnegativeIso R R X n).inv
        ((smallInclusion R T).f n
          (((smallComplex R T).extendXIso e (by change (0 : ℤ) + n = n; omega)).hom b))) ∈ _
    rw [Iso.inv_hom_id_apply]
    exact (((smallComplex R T).extendXIso e
      (by change (0 : ℤ) + n = n; omega)).hom b).property

/-- The three open sets used to split the relative fundamental chain. -/
def capSmallCover (M : Type v) [TopologicalSpace M] [T2Space M]
    (C : Cover M) (K : Support C.left) (L : Support C.right) :
    OpenCover (TopCat.of M) (Fin 3) where
  sets := ![C.left ∩ (ambientSupport M C.right L : Set M)ᶜ,
    C.intersection, C.right ∩ (ambientSupport M C.left K : Set M)ᶜ]
  isOpen i := by
    fin_cases i
    · exact C.left_open.inter (ambientSupport M C.right L).isCompact.isClosed.isOpen_compl
    · exact C.left_open.inter C.right_open
    · exact C.right_open.inter (ambientSupport M C.left K).isCompact.isClosed.isOpen_compl
  covers x := by
    have hx : x ∈ C.left ∪ C.right := by rw [C.covers]; trivial
    by_cases hU : x ∈ C.left
    · by_cases hV : x ∈ C.right
      · exact ⟨1, hU, hV⟩
      · refine ⟨0, hU, ?_⟩
        rintro ⟨y, _, rfl⟩
        exact hV y.property
    · have hV : x ∈ C.right := hx.resolve_left hU
      refine ⟨2, hV, ?_⟩
      rintro ⟨y, _, rfl⟩
      exact hU y.property

/-- Partition of a chain subordinate to three sets. Each output is supported in
its own actual simplex basis subset; no local finiteness is needed. -/
lemma small_three_split (R : Type u) [CommRing R] (X : TopCat.{v})
    (T : OpenCover X (Fin 3)) (n : ℕ) (c : Chains R X n)
    (hc : c ∈ smallModule R T n) :
    ∃ c₀ c₁ c₂ : Chains R X n,
      c₀ ∈ Finsupp.supported R R (P202.MayerVietoris.simplexSet X (T.sets 0) n) ∧
      c₁ ∈ Finsupp.supported R R (P202.MayerVietoris.simplexSet X (T.sets 1) n) ∧
      c₂ ∈ Finsupp.supported R R (P202.MayerVietoris.simplexSet X (T.sets 2) n) ∧
      c = c₀ + c₁ + c₂ := by
  have hsets : {s | ∃ i, Set.range (simplexEquiv X n s) ⊆ T.sets i} =
      (P202.MayerVietoris.simplexSet X (T.sets 0) n ∪
        P202.MayerVietoris.simplexSet X (T.sets 1) n) ∪
        P202.MayerVietoris.simplexSet X (T.sets 2) n := by
    ext s
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inl hi)
      · exact Or.inl (Or.inr hi)
      · exact Or.inr hi
    · rintro ((h | h) | h)
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
      · exact ⟨2, h⟩
  change c ∈ Finsupp.supported R R _ at hc
  rw [hsets, Finsupp.supported_union, Finsupp.supported_union] at hc
  obtain ⟨c₀₁, hc₀₁, c₂, hc₂, h⟩ := Submodule.mem_sup.mp hc
  obtain ⟨c₀, hc₀, c₁, hc₁, h₀₁⟩ := Submodule.mem_sup.mp hc₀₁
  exact ⟨c₀, c₁, c₂, hc₀, hc₁, hc₂, h.symm.trans (by rw [← h₀₁])⟩

end P202.CompactSupportMV


namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris
open P202Specs.SmallChainHomology P202Specs.CompactOrientation

/-- Three-way small representative of an ordinary relative class, retaining
both its class and the actual ambient subspace-chain ranges. -/
lemma small_relative_three_split (R : Type u) [CommRing R] (X : TopCat.{v})
    (T : OpenCover X (Fin 3)) (A : Set X) (n : ℕ)
    (a : (ordinary R R ⟨X, A⟩).homology (n : ℤ)) :
    ∃ (c₀ c₁ c₂ : (ordinaryComplex R R X).X (n : ℤ))
      (z : (ordinary R R ⟨X, A⟩).cycles (n : ℤ)),
      (projection (ordinaryFunctor R R) ⟨X, A⟩).f (n : ℤ) (c₀+c₁+c₂) =
        (ordinary R R ⟨X, A⟩).iCycles (n : ℤ) z ∧
      (ordinary R R ⟨X, A⟩).homologyπ (n : ℤ) z = a ∧
      c₀ ∈ ordinarySubspaceRange R X (T.sets 0) n ∧
      c₁ ∈ ordinarySubspaceRange R X (T.sets 1) n ∧
      c₂ ∈ ordinarySubspaceRange R X (T.sets 2) n := by
  obtain ⟨c, z, hc, hz, hsmall⟩ := small_relative_cycle_lift R X T A n a
  obtain ⟨v₀, v₁, v₂, h₀, h₁, h₂, hv⟩ := small_three_split R X T n
    ((ordinaryNonnegativeIso R R X n).hom c) hsmall
  let c₀ := (ordinaryNonnegativeIso R R X n).inv v₀
  let c₁ := (ordinaryNonnegativeIso R R X n).inv v₁
  let c₂ := (ordinaryNonnegativeIso R R X n).inv v₂
  have he : c₀+c₁+c₂=c := by
    apply (ModuleCat.mono_iff_injective (ordinaryNonnegativeIso R R X n).hom).mp inferInstance
    simp only [map_add, c₀, c₁, c₂, Iso.inv_hom_id_apply]
    exact hv.symm
  refine ⟨c₀,c₁,c₂,z, he ▸ hc, hz, ?_, ?_, ?_⟩
  · rw [ordinarySubspaceRange_nat_iff, P202.MayerVietoris.range_subspaceInclusion]
    simpa [c₀] using h₀
  · rw [ordinarySubspaceRange_nat_iff, P202.MayerVietoris.range_subspaceInclusion]
    simpa [c₁] using h₁
  · rw [ordinarySubspaceRange_nat_iff, P202.MayerVietoris.range_subspaceInclusion]
    simpa [c₂] using h₂

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris
open P202Specs.SmallChainHomology P202Specs.CompactOrientation

/-- Removing chains away from a smaller support from a fundamental lift leaves
the actual inherited fundamental class in the open subspace. -/
lemma fundamental_piece_class (R : Type u) [CommRing R]
    {n : ℕ} {M : Type v} [TopologicalSpace M] [T2Space M]
    (A : Manifold n M) (o : Orientation R A)
    (U : Set M) (hU : IsOpen U) (AU : Manifold n U) (oU : Orientation R AU)
    (ho : OpenOrientationCompatible R M o.val oU.val)
    (K : Support M) (J : Support U) (hJK : ambientSupport M U J ≤ K)
    (c : (ordinaryComplex R R (TopCat.of M)).X (n : ℤ))
    (z : (ordinary R R (supportedPair M K)).cycles (n : ℤ))
    (hc : (projection (ordinaryFunctor R R) (supportedPair M K)).f (n : ℤ) c =
      (ordinary R R (supportedPair M K)).iCycles (n : ℤ) z)
    (hz : (ordinary R R (supportedPair M K)).homologyπ (n : ℤ) z =
      P202.CompactSupport.fundamentalClass R M A o K)
    (cU : (ordinaryComplex R R (TopCat.of U)).X (n : ℤ))
    (hremove : c - (show ordinaryComplex R R (TopCat.of U) ⟶
        ordinaryComplex R R (TopCat.of M) from
        inclusion (ordinaryFunctor R R) ⟨TopCat.of M,U⟩).f (n : ℤ) cU ∈
      ordinarySubspaceRange R (TopCat.of M) (ambientSupport M U J : Set M)ᶜ (n : ℤ)) :
    ∃ zU : (ordinary R R (supportedPair U J)).cycles (n : ℤ),
      (projection (ordinaryFunctor R R) (supportedPair U J)).f (n : ℤ) cU =
        (ordinary R R (supportedPair U J)).iCycles (n : ℤ) zU ∧
      (ordinary R R (supportedPair U J)).homologyπ (n : ℤ) zU =
        P202.CompactSupport.fundamentalClass R U AU oU J := by
  let X := TopCat.of M
  let KJ := ambientSupport M U J
  let i : ordinaryComplex R R (TopCat.of U) ⟶ ordinaryComplex R R X :=
    inclusion (ordinaryFunctor R R) ⟨X,U⟩
  let pK : ordinaryComplex R R X ⟶ ordinary R R (supportedPair M K) :=
    projection (ordinaryFunctor R R) (supportedPair M K)
  let pJ : ordinaryComplex R R X ⟶ ordinary R R (supportedPair M KJ) :=
    projection (ordinaryFunctor R R) (supportedPair M KJ)
  let pU : ordinaryComplex R R (TopCat.of U) ⟶ ordinary R R (supportedPair U J) :=
    projection (ordinaryFunctor R R) (supportedPair U J)
  change pK.f (n : ℤ) c = _ at hc
  change c - i.f (n : ℤ) cU ∈ _ at hremove
  have hdc : (ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) c ∈
      ordinarySubspaceRange R X (K : Set M)ᶜ ((n : ℤ)-1) := by
    apply (P202.CapProducts.projection_kernel R (supportedPair M K) ((n : ℤ)-1) _).mp
    change pK.f ((n : ℤ)-1) ((ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) c) = 0
    rw [← ModuleCat.comp_apply, ← pK.comm, ModuleCat.comp_apply, hc]
    exact P202.CapProducts.chain_cycle_closed _ _ z
  have hdtotal : (ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) c ∈
      ordinarySubspaceRange R X (KJ : Set M)ᶜ ((n : ℤ)-1) :=
    ordinarySubspaceRange_mono R X (Set.compl_subset_compl.mpr hJK) _ hdc
  have hdremoved := ordinarySubspaceRange_d R X (j := (n : ℤ)-1) _ hremove
  have hdU : i.f ((n : ℤ)-1)
      ((ordinaryComplex R R (TopCat.of U)).d (n : ℤ) ((n : ℤ)-1) cU) ∈
      ordinarySubspaceRange R X (KJ : Set M)ᶜ ((n : ℤ)-1) := by
    have he : i.f ((n : ℤ)-1)
        ((ordinaryComplex R R (TopCat.of U)).d (n : ℤ) ((n : ℤ)-1) cU) =
        (ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) c -
          (ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) (c-i.f (n : ℤ) cU) := by
      rw [map_sub]
      have H := congrArg (fun f => f cU) (i.comm (n : ℤ) ((n : ℤ)-1))
      simp only [ModuleCat.comp_apply] at H
      rw [← H]
      abel
    rw [he]
    exact (ordinarySubspaceRange R X (KJ : Set M)ᶜ _).sub_mem hdtotal hdremoved
  have hpre : (Subtype.val : U → M) ⁻¹' (KJ : Set M) = (J : Set U) := by
    ext x
    constructor
    · rintro ⟨y, hy, he⟩
      exact Subtype.val_injective he ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hdU' : (ordinaryComplex R R (TopCat.of U)).d (n : ℤ) ((n : ℤ)-1) cU ∈
      ordinarySubspaceRange R (TopCat.of U) (J : Set U)ᶜ ((n : ℤ)-1) := by
    have H := (ordinarySubspaceRange_preimage R X U (KJ : Set M)ᶜ _ _).mp hdU
    have hsub : ((Subtype.val : U → M) ⁻¹' (KJ : Set M)ᶜ) ⊆ (J : Set U)ᶜ := by
      intro x hx hxJ
      exact hx ⟨x, hxJ, rfl⟩
    exact ordinarySubspaceRange_mono R (TopCat.of U) hsub _ H
  have hcycle : (ordinary R R (supportedPair U J)).d (n : ℤ) ((n : ℤ)-1)
      (pU.f (n : ℤ) cU) = 0 := by
    rw [← ModuleCat.comp_apply, pU.comm, ModuleCat.comp_apply]
    exact (P202.CapProducts.projection_kernel R (supportedPair U J) _ _).mpr hdU'
  let zU := P202.CapProducts.chainCycle (ordinary R R (supportedPair U J))
    (n : ℤ) (pU.f (n : ℤ) cU) hcycle
  have hzU : (ordinary R R (supportedPair U J)).iCycles (n : ℤ) zU =
      pU.f (n : ℤ) cU := P202.CapProducts.chainCycle_i _ _ _ _
  refine ⟨zU, hzU.symm, ?_⟩
  let r := relativeMap (ordinaryFunctor R R) (supportPairMap M hJK)
  let zJ := cyclesMap r (n : ℤ) z
  have hzJ : pJ.f (n : ℤ) c = (ordinary R R (supportedPair M KJ)).iCycles (n : ℤ) zJ := by
    have Hsquare := projection_map (ordinaryFunctor R R) (supportPairMap M hJK)
    have hid : (supportPairMap M hJK).map = 𝟙 X := rfl
    rw [hid] at Hsquare
    erw [(ordinaryFunctor R R).map_id X, Category.id_comp] at Hsquare
    have H := congrArg (fun f => f.f (n : ℤ) c) Hsquare
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at H
    change r.f (n : ℤ) (pK.f (n : ℤ) c) = pJ.f (n : ℤ) c at H
    rw [hc] at H
    exact H.symm.trans (congrArg (fun f => f z) (cyclesMap_i r (n : ℤ))).symm
  have hrm : pJ.f (n : ℤ) c = pJ.f (n : ℤ) (i.f (n : ℤ) cU) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (P202.CapProducts.projection_kernel R (supportedPair M KJ) _ _).mpr hremove
  let f := relativeMap (ordinaryFunctor R R) (openPairInclusion M U J)
  have hcycles : cyclesMap f (n : ℤ) zU = zJ := by
    apply (ModuleCat.mono_iff_injective ((ordinary R R (supportedPair M KJ)).iCycles (n : ℤ))).mp inferInstance
    have H := congrArg (fun f => f.f (n : ℤ) cU)
      (projection_map (ordinaryFunctor R R) (openPairInclusion M U J))
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at H
    change f.f (n : ℤ) (pU.f (n : ℤ) cU) = pJ.f (n : ℤ) (i.f (n : ℤ) cU) at H
    rw [← ModuleCat.comp_apply, cyclesMap_i, ModuleCat.comp_apply, hzU, H, ← hrm, hzJ]
  haveI := openPairInclusion_homology_isIso R U hU J n
  apply (ModuleCat.mono_iff_injective ((relativeHomologyFunctor R R (n : ℤ)).map
    (openPairInclusion M U J))).mp inferInstance
  rw [P202.CompactSupport.fundamentalClass_open R M A o U AU oU ho J]
  change homologyMap f (n : ℤ) ((ordinary R R (supportedPair U J)).homologyπ (n : ℤ) zU) = _
  rw [← ModuleCat.comp_apply, homologyπ_naturality, ModuleCat.comp_apply, hcycles]
  change (ordinary R R (supportedPair M KJ)).homologyπ (n : ℤ) (cyclesMap r (n : ℤ) z) = _
  rw [← ModuleCat.comp_apply, ← homologyπ_naturality, ModuleCat.comp_apply, hz]
  exact P202.CompactSupport.fundamentalClass_compatible R M A o hJK

end P202.CompactSupportMV


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV
open P202Specs.SingularChains P202Specs.CohomologyPairs P202Specs.CapProducts P202Specs.CupProduct

/-- The explicit primitive in the signed connecting cap square. It lies in the
space containing the input chain, so this identity may be applied inside U∩V. -/
lemma cap_connecting_primitive (R : Type u) [CommRing R] (X : TopCat.{v})
    (p : ℕ) (j : ℤ) (a : Cochain R X p)
    (c : (ordinaryComplex R R X).X j) :
    (-1 : ℤ)^(p+1) •
        castOrdinary R (by omega : (j-1)-(p : ℤ)=j-p-1)
          (cap R X p (j-1) a ((ordinaryComplex R R X).d j (j-1) c)) -
      (-1 : ℤ)^(p+1) •
        castOrdinary R (by push_cast; omega : j-((p+1:ℕ):ℤ)=j-p-1)
          (cap R X (p+1) j (delta R X p a) c) =
    (ordinaryComplex R R X).d (j-p) (j-p-1) (-(cap R X p j a c)) := by
  rw [map_neg, P202.CapProducts.ordinaryBoundary, ← smul_sub, pow_succ]
  simp only [mul_neg, mul_one, neg_smul]

/-- The chain-level primitive gives equality of the two classes in the actual
space X, including degree zero. -/
lemma cap_connecting_homology (R : Type u) [CommRing R] (X : TopCat.{v})
    (p : ℕ) (j : ℤ) (a : Cochain R X p)
    (c : (ordinaryComplex R R X).X j)
    (z w : (ordinaryComplex R R X).cycles (j-p-1))
    (hz : (ordinaryComplex R R X).iCycles (j-p-1) z =
      (-1 : ℤ)^(p+1) •
        castOrdinary R (by omega : (j-1)-(p : ℤ)=j-p-1)
          (cap R X p (j-1) a ((ordinaryComplex R R X).d j (j-1) c)))
    (hw : (ordinaryComplex R R X).iCycles (j-p-1) w =
      castOrdinary R (by push_cast; omega : j-((p+1:ℕ):ℤ)=j-p-1)
        (cap R X (p+1) j (delta R X p a) c)) :
    (ordinaryComplex R R X).homologyπ (j-p-1) z =
      (-1 : ℤ)^(p+1) • (ordinaryComplex R R X).homologyπ (j-p-1) w := by
  apply sub_eq_zero.mp
  rw [← map_zsmul, ← map_sub]
  apply (P202.CapProducts.chain_class_zero_iff (R := R) _ (j-p-1) _).mpr
  refine ⟨castOrdinary R (by omega : j-p=(j-p-1)+1) (-(cap R X p j a c)), ?_⟩
  rw [← P202.CapProducts.castOrdinary_d R
    (by omega : j-p=(j-p-1)+1) (show j-p-1=j-p-1 from rfl)]
  change (ordinaryComplex R R X).d (j-p) (j-p-1) (-(cap R X p j a c)) = _
  rw [← cap_connecting_primitive, map_sub, map_zsmul, hz, hw]

end P202.CompactSupportMV


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.CompactSupportMV
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CapProducts P202Specs.CohomologyPairs P202Specs.CupProduct

lemma cap_connecting_boundary (R : Type u) [CommRing R] (X : TopCat.{v})
    (P Q : Set X) (p : ℕ) (j : ℤ) (a aP aQ : Cochain R X p)
    (hsplit : a = aP + aQ) (ha : delta R X p a = 0)
    (hP : aP ∈ vanishingCochains R R ⟨X,P⟩ p)
    (hQ : aQ ∈ vanishingCochains R R ⟨X,Q⟩ p)
    (cU cW : (ordinaryComplex R R X).X j)
    (hcU : cU ∈ ordinarySubspaceRange R X Q j)
    (hdUW : (ordinaryComplex R R X).d j (j-1) (cU+cW) ∈
      ordinarySubspaceRange R X P (j-1)) :
    (ordinaryComplex R R X).d (j-p) (j-p-1) (cap R X p j a cU) =
      (-1 : ℤ)^(p+1) •
        castOrdinary R (by omega : (j-1)-(p : ℤ)=j-p-1)
          (cap R X p (j-1) aP ((ordinaryComplex R R X).d j (j-1) cW)) := by
  have hQzero : cap R X p (j-1) aQ ((ordinaryComplex R R X).d j (j-1) cU) = 0 :=
    P202.CapProducts.cap_annihilates_subspace R ⟨X,Q⟩ p (j-1) aQ hQ _
      (ordinarySubspaceRange_d R X cU hcU)
  have hPzero : cap R X p (j-1) aP ((ordinaryComplex R R X).d j (j-1) (cU+cW)) = 0 :=
    P202.CapProducts.cap_annihilates_subspace R ⟨X,P⟩ p (j-1) aP hP _ hdUW
  have hneg : cap R X p (j-1) aP ((ordinaryComplex R R X).d j (j-1) cU) =
      -(cap R X p (j-1) aP ((ordinaryComplex R R X).d j (j-1) cW)) := by
    rw [map_add, map_add] at hPzero
    exact eq_neg_of_add_eq_zero_left hPzero
  rw [P202.CapProducts.ordinaryBoundary, ha, map_zero, LinearMap.zero_apply, map_zero, sub_zero]
  rw [hsplit, map_add, LinearMap.add_apply, hQzero, add_zero, hneg, map_neg, pow_succ]
  simp only [mul_neg, mul_one, neg_smul, smul_neg]

end P202.CompactSupportMV


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.CompactSupportMayerVietoris
open P202Specs.CompactSupportMayerVietoris P202Specs.CompactSupport
open P202Specs.SingularChains P202Specs.LocalOrientation

lemma cap_connecting_of_negative (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    {n : ℕ} {M : Type v} [TopologicalSpace M] [T2Space M]
    (A : Manifold n M) (o : Orientation R A) (C : Cover M)
    (δ : Connecting R M C)
    (hδ : P202Specs.MayerVietoris.Connecting.{u,v,0} (ordinaryChains R))
    (AW : Manifold n C.intersection) (oW : Orientation R AW)
    (p : ℤ) (hp : p < 0) (a : CompactCohomology R M p) :
    hδ C.ordinary ((n : ℤ)-p-1)
      (degreeTransport R (TopCat.of M) ((n : ℤ)-p) (((n : ℤ)-p-1)+1)
        (by omega) (d.D n M A o p a)) =
      ((p+1).negOnePow : ℤ) •
        degreeTransport R (TopCat.of C.intersection) ((n : ℤ)-(p+1)) ((n : ℤ)-p-1)
          (by omega) (d.D n C.intersection AW oW (p+1) (δ p a)) := by
  haveI : Subsingleton (CompactCohomology R M p) := P202.CompactSupport.negative R M p hp
  have ha : a = 0 := Subsingleton.elim a 0
  subst a
  simp

lemma cap_connecting_of_above (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    {n : ℕ} {M : Type v} [TopologicalSpace M] [T2Space M]
    (A : Manifold n M) (o : Orientation R A) (C : Cover M)
    (δ : Connecting R M C)
    (hδ : P202Specs.MayerVietoris.Connecting.{u,v,0} (ordinaryChains R))
    (AW : Manifold n C.intersection) (oW : Orientation R AW)
    (p : ℤ) (hp : (n : ℤ) ≤ p) (a : CompactCohomology R M p) :
    hδ C.ordinary ((n : ℤ)-p-1)
      (degreeTransport R (TopCat.of M) ((n : ℤ)-p) (((n : ℤ)-p-1)+1)
        (by omega) (d.D n M A o p a)) =
      ((p+1).negOnePow : ℤ) •
        degreeTransport R (TopCat.of C.intersection) ((n : ℤ)-(p+1)) ((n : ℤ)-p-1)
          (by omega) (d.D n C.intersection AW oW (p+1) (δ p a)) := by
  haveI : Subsingleton (homology R R (TopCat.of C.intersection) ((n : ℤ)-p-1)) :=
    ModuleCat.subsingleton_of_isZero
      (P202.SingularChains.ordinary_negative_homology R R (TopCat.of C.intersection)
        ((n : ℤ)-p-1) (by omega))
  exact @Subsingleton.elim (homology R R (TopCat.of C.intersection) ((n : ℤ)-p-1))
    inferInstance _ _

end P202.CompactSupportMayerVietoris

/-! Exact representative bridges and cofinal directed-limit identifications. -/



namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.CompactSupport P202Specs.CohomologyPairs
open P202Specs.RelativeSingularChains P202Specs.RelativeCupProduct
open P202Specs.CompactSupportMayerVietoris P202Specs.LocalOrientation
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

lemma cochainInclusion_cast {K L : Support M} (h : K = L) :
    eqToHom (congrArg (supportedCochains R M) h) ≫ cochainInclusion R M L =
      cochainInclusion R M K := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

lemma intersectionCochainRestriction_absolute (C : Cover M)
    (K : Support C.left) (L : Support C.right) :
    intersectionCochainRestriction R M C K L ≫
        cochainInclusion R C.intersection (intersectionIn M C.left C.right (K,L)) =
      cochainInclusion R M (ambientSupport M C.left K ⊓ ambientSupport M C.right L) ≫
        (ordinaryCochainFunctor R R).map
          (P202Specs.RelativeSingularChains.Pair.inclusion ⟨TopCat.of M, C.intersection⟩).op := by
  let J := intersectionIn M C.left C.right (K,L)
  have h := (cochainSequenceMap R R (openPairInclusion M C.intersection J)).comm₁₂
  change (relativeCochainFunctor R R).map (openPairInclusion M C.intersection J).op ≫
      cochainInclusion R C.intersection J =
    cochainInclusion R M (ambientSupport M C.intersection J) ≫ _ at h
  unfold intersectionCochainRestriction
  rw [Category.assoc, h, ← Category.assoc,
    cochainInclusion_cast R M (ambient_intersectionIn M C.left C.right (K,L)).symm]
  rfl

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris

/-- Every compact-support cohomology class has an actual cocycle representative
at a union of compact supports in the two named open pieces. -/
lemma exists_union_cocycle (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] [T2Space M] (C : Cover M)
    (p : ℤ) (a : CompactCohomology R M p) :
    ∃ (K : Support C.left) (L : Support C.right)
      (z : (supportedCochains R M
        (ambientSupport M C.left K ⊔ ambientSupport M C.right L)).cycles p),
      a = ofSupport R M p (ambientSupport M C.left K ⊔ ambientSupport M C.right L)
        ((supportedCochains R M
          (ambientSupport M C.left K ⊔ ambientSupport M C.right L)).homologyπ p z) := by
  obtain ⟨N, b, hb⟩ := P202.CompactSupport.representatives R M p a
  obtain ⟨⟨K,L⟩, hKL⟩ := compactUnionCofinal M C.left C.right
    C.left_open C.right_open C.covers N
  change ambientSupport M C.left K ⊔ ambientSupport M C.right L = N at hKL
  subst N
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((supportedCochains R M
      (ambientSupport M C.left K ⊔ ambientSupport M C.right L)).homologyπ p)).mp inferInstance b
  exact ⟨K, L, z, hb.symm⟩

end P202.CompactSupportMV


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV
open P202Specs.CompactSupportMayerVietoris P202Specs.CompactSupport
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

lemma extendSubset_openPullback_transition {B E : Set M} (h : B ⊆ E) (hB : IsOpen B)
    (p : ℤ) (J : Support B) (K : Support E) (hJK : supportInSubset h J ≤ K)
    (b : supportedCohomology R M p (ambientSupport M B J)) :
    extendSubset R M h hB p (ofSupport R B p J (openPullback R M B J p b)) =
      ofSupport R E p K (openPullback R M E K p
        (transition R M p (ambientSupport M B J) (ambientSupport M E K)
          ((le_of_eq (ambientSupport_supportInSubset M h J).symm).trans
            (ambientSupport_mono M E hJK)) b)) := by
  let S := supportInSubset h J
  have hS : ambientSupport M E S = ambientSupport M B J := ambientSupport_supportInSubset M h J
  let hto : ambientSupport M B J ≤ ambientSupport M E S := le_of_eq hS.symm
  let hfrom : ambientSupport M E S ≤ ambientSupport M B J := le_of_eq hS
  let bES := transition R M p (ambientSupport M B J) (ambientSupport M E S) hto b
  have hretract : transition R M p (ambientSupport M E S) (ambientSupport M B J) hfrom bES = b := by
    exact (DirectedSystem.map_map' (transition R M p) hto hfrom b).trans
      (DirectedSystem.map_self' (transition R M p) b)
  have hs : openPairInclusion M B J ≫ supportPairMap M hfrom =
      subsetPairInclusion h J ≫ openPairInclusion M E S := by
    apply PairMap.ext
    rfl
  have H := congrArg ((relativeCohomologyFunctor R R p).map) (congrArg Quiver.Hom.op hs)
  rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp] at H
  have hbB := congrArg (fun f => f bES) H
  change openPullback R M B J p
      (transition R M p (ambientSupport M E S) (ambientSupport M B J) hfrom bES) =
    subsetPullback R h J p (openPullback R M E S p bES) at hbB
  rw [hretract] at hbB
  rw [hbB, extendSubset_represents]
  calc
    ofSupport R E p S (openPullback R M E S p bES) =
        ofSupport R E p K (openPullback R M E K p
          (transition R M p (ambientSupport M E S) (ambientSupport M E K)
            (ambientSupport_mono M E hJK) bES)) :=
      (ofSupport_openPullback_transition R M E p hJK bES).symm
    _ = _ := by
      have hm := DirectedSystem.map_map' (transition R M p) hto
        (ambientSupport_mono M E hJK) b
      rw [hm]

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open P202Specs.CompactSupportMayerVietoris P202Specs.CompactSupport
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

lemma supportInSubset_intersectionIn_left (C : Cover M)
    (s : SupportPair M C.left C.right) :
    supportInSubset (show C.intersection ⊆ C.left from Set.inter_subset_left)
      (intersectionIn M C.left C.right s) ≤ s.1 := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨z, hz, he⟩ := hy.1
  have he' : z = subsetInclusion (show C.intersection ⊆ C.left from Set.inter_subset_left) y :=
    Subtype.ext he
  exact he' ▸ hz

lemma supportInSubset_intersectionIn_right (C : Cover M)
    (s : SupportPair M C.left C.right) :
    supportInSubset (show C.intersection ⊆ C.right from Set.inter_subset_right)
      (intersectionIn M C.left C.right s) ≤ s.2 := by
  rintro x ⟨y, hy, rfl⟩
  obtain ⟨z, hz, he⟩ := hy.2
  have he' : z = subsetInclusion (show C.intersection ⊆ C.right from Set.inter_subset_right) y :=
    Subtype.ext he
  exact he' ▸ hz

lemma intersectionExtendLeft_atSupports (C : Cover M) (p : ℤ)
    (s : SupportPair M C.left C.right)
    (b : supportedCohomology R M p (intersectionSupport M C.left C.right s)) :
    intersectionExtendLeft R M C p
      (ofSupport R C.intersection p (intersectionIn M C.left C.right s)
        (openPullback R M C.intersection (intersectionIn M C.left C.right s) p
          ((eqToHom (congrArg (supportedCohomology R M p)
            (ambient_intersectionIn M C.left C.right s).symm)) b))) =
      ofSupport R C.left p s.1 (openPullback R M C.left s.1 p
        (transition R M p (intersectionSupport M C.left C.right s)
          (ambientSupport M C.left s.1) inf_le_left b)) := by
  have H := extendSubset_openPullback_transition R M Set.inter_subset_left
    (C.left_open.inter C.right_open) p (intersectionIn M C.left C.right s) s.1
    (supportInSubset_intersectionIn_left M C s)
    ((eqToHom (congrArg (supportedCohomology R M p)
      (ambient_intersectionIn M C.left C.right s).symm)) b)
  change intersectionExtendLeft R M C p _ = _ at H
  rw [H]
  have ht := congrArg (fun f => f b) (transition_eqToHom R M p
    (ambient_intersectionIn M C.left C.right s).symm rfl inf_le_left
    ((le_of_eq (ambientSupport_supportInSubset M Set.inter_subset_left
      (intersectionIn M C.left C.right s)).symm).trans
        (ambientSupport_mono M C.left (supportInSubset_intersectionIn_left M C s))))
  simp only [eqToHom_refl, Category.comp_id, ModuleCat.comp_apply] at ht
  exact congrArg (fun x => ofSupport R C.left p s.1 (openPullback R M C.left s.1 p x)) ht.symm

lemma intersectionExtendRight_atSupports (C : Cover M) (p : ℤ)
    (s : SupportPair M C.left C.right)
    (b : supportedCohomology R M p (intersectionSupport M C.left C.right s)) :
    intersectionExtendRight R M C p
      (ofSupport R C.intersection p (intersectionIn M C.left C.right s)
        (openPullback R M C.intersection (intersectionIn M C.left C.right s) p
          ((eqToHom (congrArg (supportedCohomology R M p)
            (ambient_intersectionIn M C.left C.right s).symm)) b))) =
      ofSupport R C.right p s.2 (openPullback R M C.right s.2 p
        (transition R M p (intersectionSupport M C.left C.right s)
          (ambientSupport M C.right s.2) inf_le_right b)) := by
  have H := extendSubset_openPullback_transition R M Set.inter_subset_right
    (C.left_open.inter C.right_open) p (intersectionIn M C.left C.right s) s.2
    (supportInSubset_intersectionIn_right M C s)
    ((eqToHom (congrArg (supportedCohomology R M p)
      (ambient_intersectionIn M C.left C.right s).symm)) b)
  change intersectionExtendRight R M C p _ = _ at H
  rw [H]
  have ht := congrArg (fun f => f b) (transition_eqToHom R M p
    (ambient_intersectionIn M C.left C.right s).symm rfl inf_le_right
    ((le_of_eq (ambientSupport_supportInSubset M Set.inter_subset_right
      (intersectionIn M C.left C.right s)).symm).trans
        (ambientSupport_mono M C.right (supportInSubset_intersectionIn_right M C s))))
  simp only [eqToHom_refl, Category.comp_id, ModuleCat.comp_apply] at ht
  exact congrArg (fun x => ofSupport R C.right p s.2 (openPullback R M C.right s.2 p x)) ht.symm

end P202.CompactSupportMV

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

/-- The global sum map agrees on genuine excision representatives with the
finite-support sum, followed by the canonical map into the filtered limit. -/
lemma compact_sum_ofSupports (d : DualityData.{u,v} R) (C : Cover M) (p : ℤ)
    (K : Support C.left) (L : Support C.right)
    (bK : supportedCohomology R M p (ambientSupport M C.left K))
    (bL : supportedCohomology R M p (ambientSupport M C.right L)) :
    (sum R M d C p)
      ((biprod.inl : ModuleCat.of R (CompactCohomology R C.left p) ⟶ CompactMiddle R M C p)
          (ofSupport R C.left p K (openPullback R M C.left K p bK)) +
        (biprod.inr : ModuleCat.of R (CompactCohomology R C.right p) ⟶ CompactMiddle R M C p)
          (ofSupport R C.right p L (openPullback R M C.right L p bL))) =
      ofSupport R M p (ambientSupport M C.left K ⊔ ambientSupport M C.right L)
        (transition R M p (ambientSupport M C.left K)
            (ambientSupport M C.left K ⊔ ambientSupport M C.right L) le_sup_left bK +
          transition R M p (ambientSupport M C.right L)
            (ambientSupport M C.left K ⊔ ambientSupport M C.right L) le_sup_right bL) := by
  change (biprod.desc (ModuleCat.ofHom (d.extend M C.left C.left_open p))
    (ModuleCat.ofHom (d.extend M C.right C.right_open p))) _ = _
  rw [map_add, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
    biprod.inl_desc, biprod.inr_desc]
  change d.extend M C.left C.left_open p
      (ofSupport R C.left p K (openPullback R M C.left K p bK)) +
    d.extend M C.right C.right_open p
      (ofSupport R C.right p L (openPullback R M C.right L p bL)) = _
  rw [d.extension_represents, d.extension_represents, map_add,
    P202.CompactSupport.ofSupport_transition, P202.CompactSupport.ofSupport_transition]

end P202.CompactSupportMV


namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris
open P202Specs.SmallChainHomology P202Specs.CompactOrientation

/-- The finite fundamental class can be split into the three source open sets.
The middle piece is a fundamental lift on the actual intersection, and the
boundary of the first two pieces misses the left compact support. -/
lemma fundamental_cover_split (R : Type u) [CommRing R]
    {n : ℕ} {M : Type v} [TopologicalSpace M] [T2Space M]
    (A : Manifold n M) (o : Orientation R A) (C : Cover M)
    (AW : Manifold n C.intersection) (oW : Orientation R AW)
    (hoW : OpenOrientationCompatible R M o.val oW.val)
    (K : Support C.left) (L : Support C.right) :
    let K₀ := ambientSupport M C.left K
    let L₀ := ambientSupport M C.right L
    let J := intersectionIn M C.left C.right (K,L)
    let iW : ordinaryComplex R R (TopCat.of C.intersection) ⟶
        ordinaryComplex R R (TopCat.of M) :=
      inclusion (ordinaryFunctor R R) ⟨TopCat.of M,C.intersection⟩
    ∃ (cU cV : (ordinaryComplex R R (TopCat.of M)).X (n : ℤ))
      (cW : (ordinaryComplex R R (TopCat.of C.intersection)).X (n : ℤ))
      (z : (ordinary R R (supportedPair M (K₀ ⊔ L₀))).cycles (n : ℤ))
      (zW : (ordinary R R (supportedPair C.intersection J)).cycles (n : ℤ)),
      (projection (ordinaryFunctor R R) (supportedPair M (K₀ ⊔ L₀))).f (n : ℤ)
        (cU+iW.f (n : ℤ) cW+cV) =
          (ordinary R R (supportedPair M (K₀ ⊔ L₀))).iCycles (n : ℤ) z ∧
      (ordinary R R (supportedPair M (K₀ ⊔ L₀))).homologyπ (n : ℤ) z =
        P202.CompactSupport.fundamentalClass R M A o (K₀ ⊔ L₀) ∧
      cU ∈ ordinarySubspaceRange R (TopCat.of M) (C.left ∩ (L₀ : Set M)ᶜ) (n : ℤ) ∧
      cV ∈ ordinarySubspaceRange R (TopCat.of M) (C.right ∩ (K₀ : Set M)ᶜ) (n : ℤ) ∧
      (ordinaryComplex R R (TopCat.of M)).d (n : ℤ) ((n : ℤ)-1)
        (cU+iW.f (n : ℤ) cW) ∈
        ordinarySubspaceRange R (TopCat.of M) (K₀ : Set M)ᶜ ((n : ℤ)-1) ∧
      (projection (ordinaryFunctor R R) (supportedPair C.intersection J)).f (n : ℤ) cW =
        (ordinary R R (supportedPair C.intersection J)).iCycles (n : ℤ) zW ∧
      (ordinary R R (supportedPair C.intersection J)).homologyπ (n : ℤ) zW =
        P202.CompactSupport.fundamentalClass R C.intersection AW oW J := by
  dsimp only
  let X := TopCat.of M
  let K₀ := ambientSupport M C.left K
  let L₀ := ambientSupport M C.right L
  let J := intersectionIn M C.left C.right (K,L)
  let iW : ordinaryComplex R R (TopCat.of C.intersection) ⟶ ordinaryComplex R R X :=
    inclusion (ordinaryFunctor R R) ⟨X,C.intersection⟩
  obtain ⟨cU,cW₀,cV,z,hproj,hclass,hU,hW,hV⟩ :=
    small_relative_three_split R X (capSmallCover M C K L)
      (K₀ ⊔ L₀ : Set M)ᶜ n (P202.CompactSupport.fundamentalClass R M A o (K₀ ⊔ L₀))
  change cU ∈ ordinarySubspaceRange R X (C.left ∩ (L₀ : Set M)ᶜ) (n : ℤ) at hU
  change cW₀ ∈ ordinarySubspaceRange R X C.intersection (n : ℤ) at hW
  change cV ∈ ordinarySubspaceRange R X (C.right ∩ (K₀ : Set M)ᶜ) (n : ℤ) at hV
  obtain ⟨cW, hcW⟩ := hW
  change iW.f (n : ℤ) cW = cW₀ at hcW
  have hJ : ambientSupport M C.intersection J = K₀ ⊓ L₀ :=
    ambient_intersectionIn M C.left C.right (K,L)
  have hJK : ambientSupport M C.intersection J ≤ K₀ ⊔ L₀ := by
    rw [hJ]
    exact inf_le_left.trans le_sup_left
  have hUJ : C.left ∩ (L₀ : Set M)ᶜ ⊆ (ambientSupport M C.intersection J : Set M)ᶜ := by
    intro x hx hxJ
    change x ∈ (ambientSupport M C.intersection J : Set M) at hxJ
    rw [hJ] at hxJ
    exact hx.2 hxJ.2
  have hVJ : C.right ∩ (K₀ : Set M)ᶜ ⊆ (ambientSupport M C.intersection J : Set M)ᶜ := by
    intro x hx hxJ
    change x ∈ (ambientSupport M C.intersection J : Set M) at hxJ
    rw [hJ] at hxJ
    exact hx.2 hxJ.1
  have hremove : cU+cW₀+cV-iW.f (n : ℤ) cW ∈
      ordinarySubspaceRange R X (ambientSupport M C.intersection J : Set M)ᶜ (n : ℤ) := by
    rw [hcW]
    have he : cU+cW₀+cV-cW₀=cU+cV := by abel
    rw [he]
    exact (ordinarySubspaceRange R X _ _).add_mem
      (ordinarySubspaceRange_mono R X hUJ _ hU)
      (ordinarySubspaceRange_mono R X hVJ _ hV)
  obtain ⟨zW,hprojW,hclassW⟩ := fundamental_piece_class R A o C.intersection
    (C.left_open.inter C.right_open) AW oW hoW (K₀ ⊔ L₀) J hJK
    (cU+cW₀+cV) z hproj hclass cW hremove
  have hbound : (ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) (cU+cW₀) ∈
      ordinarySubspaceRange R X (K₀ : Set M)ᶜ ((n : ℤ)-1) := by
    have hdtotal : (ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) (cU+cW₀+cV) ∈
        ordinarySubspaceRange R X (K₀ ⊔ L₀ : Set M)ᶜ ((n : ℤ)-1) := by
      apply (P202.CapProducts.projection_kernel R (supportedPair M (K₀ ⊔ L₀)) _ _).mp
      let p : ordinaryComplex R R X ⟶ ordinary R R (supportedPair M (K₀ ⊔ L₀)) :=
        projection (ordinaryFunctor R R) (supportedPair M (K₀ ⊔ L₀))
      change p.f ((n : ℤ)-1) ((ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) (cU+cW₀+cV)) = 0
      rw [← ModuleCat.comp_apply, ← p.comm, ModuleCat.comp_apply]
      change (ordinary R R (supportedPair M (K₀ ⊔ L₀))).d (n : ℤ) ((n : ℤ)-1)
        ((projection (ordinaryFunctor R R) (supportedPair M (K₀ ⊔ L₀))).f (n : ℤ) (cU+cW₀+cV)) = 0
      erw [hproj]
      exact P202.CapProducts.chain_cycle_closed _ _ z
    have hdtotal' := ordinarySubspaceRange_mono R X
      (Set.compl_subset_compl.mpr (show (K₀ : Set M) ⊆ (K₀ ⊔ L₀ : Set M) from le_sup_left))
      _ hdtotal
    have hdV := ordinarySubspaceRange_d R X (j := (n : ℤ)-1) cV
      (ordinarySubspaceRange_mono R X (Set.inter_subset_right :
        C.right ∩ (K₀ : Set M)ᶜ ⊆ (K₀ : Set M)ᶜ) _ hV)
    have he : (ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) (cU+cW₀) =
        (ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) (cU+cW₀+cV) -
          (ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) cV := by simp only [map_add]; abel
    rw [he]
    exact (ordinarySubspaceRange R X _ _).sub_mem hdtotal' hdV
  refine ⟨cU,cV,cW,z,zW,?_,hclass,hU,hV,?_,hprojW,hclassW⟩
  · change (projection (ordinaryFunctor R R) (supportedPair M (K₀ ⊔ L₀))).f (n : ℤ)
      (cU+iW.f (n : ℤ) cW+cV) = _
    rw [hcW]
    exact hproj
  · change (ordinaryComplex R R X).d (n : ℤ) ((n : ℤ)-1) (cU+iW.f (n : ℤ) cW) ∈ _
    rw [hcW]
    exact hbound

end P202.CompactSupportMV


namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris

lemma classOf_eq_homologyπ (R : Type u) [CommRing R]
    (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (k : ℤ)
    (x : K.X k) (hx : K.d k (k-1) x = 0) (z : K.cycles k)
    (h : x = K.iCycles k z) :
    P202Specs.MayerVietoris.classOf K k x hx = K.homologyπ k z := by
  subst x
  exact P202.MayerVietoris.classOf_iCycles K k z hx

/-- Boundary normalization identifies a connecting value in the actual
intersection group whenever the left boundary differs from a given cycle by
an explicit boundary in the intersection. -/
lemma ordinary_connecting_boundary_homology (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] (C : Cover M)
    (δ : P202Specs.MayerVietoris.Connecting.{u,v,0} (ordinaryChains R))
    (hδ : P202Specs.MayerVietoris.BoundaryFormula (ordinaryChains R) δ)
    (k : ℤ)
    (c : (P202Specs.MayerVietoris.middle (ordinaryChains R) C.ordinary).X (k+1))
    (z : (ordinaryComplex R R (TopCat.of M)).cycles (k+1))
    (hsum : (P202Specs.MayerVietoris.chainSum (ordinaryChains R) C.ordinary).f (k+1) c =
      (ordinaryComplex R R (TopCat.of M)).iCycles (k+1) z)
    (t : ℤ) (w : (ordinaryComplex R R (TopCat.of C.intersection)).cycles k)
    (b : (ordinaryComplex R R (TopCat.of C.intersection)).X (k+1))
    (hleft : (ordinaryComplex R R (TopCat.of M)).d (k+1) k
      (((biprod.fst : P202Specs.MayerVietoris.middle (ordinaryChains R) C.ordinary ⟶
          (ordinaryChains R).obj C.ordinary.leftPair) ≫
        (ordinaryChains R).map C.ordinary.leftInclusion).f (k+1) c) =
      (show ordinaryComplex R R (TopCat.of C.intersection) ⟶ ordinaryComplex R R (TopCat.of M)
        from inclusion (ordinaryFunctor R R) ⟨TopCat.of M,C.intersection⟩).f k
        (t • (ordinaryComplex R R (TopCat.of C.intersection)).iCycles k w +
          (ordinaryComplex R R (TopCat.of C.intersection)).d (k+1) k b)) :
    δ C.ordinary k ((ordinaryComplex R R (TopCat.of M)).homologyπ (k+1) z) =
      t • (ordinaryComplex R R (TopCat.of C.intersection)).homologyπ k w := by
  let F := ordinaryChains R
  let S := P202Specs.MayerVietoris.middle F C.ordinary
  let g : S ⟶ ordinaryComplex R R (TopCat.of M) :=
    (biprod.fst : S ⟶ F.obj C.ordinary.leftPair) ≫ F.map C.ordinary.leftInclusion
  let iW : ordinaryComplex R R (TopCat.of C.intersection) ⟶ ordinaryComplex R R (TopCat.of M) :=
    inclusion (ordinaryFunctor R R) ⟨TopCat.of M,C.intersection⟩
  have hc : (F.obj C.ordinary.pair).d (k+1) k
      ((P202Specs.MayerVietoris.chainSum F C.ordinary).f (k+1) c) = 0 := by
    rw [hsum]
    exact congrArg (fun f => f z) ((ordinaryComplex R R (TopCat.of M)).iCycles_d (k+1) k)
  obtain ⟨x, ⟨hx,hxc⟩, _⟩ :=
    (P202.MayerVietoris.mayerVietoris R .ordinary).2.2.1 C.ordinary k c hc
  have hfac : P202Specs.MayerVietoris.chainFirst F C.ordinary ≫ g = iW := by
    dsimp only [g, P202Specs.MayerVietoris.chainFirst]
    rw [biprod.lift_fst_assoc, ← F.map_comp]
    rfl
  have hxambient : iW.f k x = (ordinaryComplex R R (TopCat.of M)).d (k+1) k (g.f (k+1) c) := by
    have H := congrArg (fun f => f.f k x) hfac
    simp only [HomologicalComplex.comp_f, ModuleCat.comp_apply] at H
    rw [hx] at H
    have Hg := congrArg (fun f => f c) (g.comm (k+1) k)
    simp only [ModuleCat.comp_apply] at Hg
    exact H.symm.trans Hg.symm
  have hxchain : x = t • (ordinaryComplex R R (TopCat.of C.intersection)).iCycles k w +
      (ordinaryComplex R R (TopCat.of C.intersection)).d (k+1) k b := by
    apply ordinary_subspace_injective R (TopCat.of M) C.intersection k
    exact hxambient.trans hleft
  let xcycle := P202.CapProducts.chainCycle (ordinaryComplex R R (TopCat.of C.intersection)) k x hxc
  have hxcycle : (ordinaryComplex R R (TopCat.of C.intersection)).iCycles k xcycle = x :=
    P202.CapProducts.chainCycle_i _ _ _ _
  have hclass : (ordinaryComplex R R (TopCat.of C.intersection)).homologyπ k xcycle =
      t • (ordinaryComplex R R (TopCat.of C.intersection)).homologyπ k w := by
    apply sub_eq_zero.mp
    rw [← map_zsmul, ← map_sub]
    apply (P202.CapProducts.chain_class_zero_iff (ordinaryComplex R R (TopCat.of C.intersection)) k _).mpr
    refine ⟨b, ?_⟩
    rw [map_sub, map_zsmul, hxcycle, hxchain]
    abel
  have hzclass : P202Specs.MayerVietoris.classOf (F.obj C.ordinary.pair) (k+1)
      ((P202Specs.MayerVietoris.chainSum F C.ordinary).f (k+1) c)
      (by rw [add_sub_cancel_right]; exact hc) =
      (ordinaryComplex R R (TopCat.of M)).homologyπ (k+1) z := by
    exact classOf_eq_homologyπ R _ _ _ _ z hsum
  have hvalue := hδ C.ordinary k c hc x hx hxc
  rw [hzclass] at hvalue
  have hxclass : P202Specs.MayerVietoris.classOf (F.obj C.ordinary.intersectionPair) k x hxc =
      (ordinaryComplex R R (TopCat.of C.intersection)).homologyπ k xcycle := by
    exact classOf_eq_homologyπ R _ _ _ _ xcycle hxcycle.symm
  exact hvalue.trans (hxclass.trans hclass)

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open P202Specs.SingularChains P202Specs.CapProducts
open P202Specs.CompactSupportMayerVietoris

lemma ordinarySubspaceRange_cast (R : Type u) [CommRing R] (X : TopCat.{v})
    (B : Set X) {i j : ℤ} (h : i = j)
    (c : (ordinaryComplex R R X).X i)
    (hc : c ∈ ordinarySubspaceRange R X B i) :
    castOrdinary R h c ∈ ordinarySubspaceRange R X B j := by
  subst j
  exact hc

/-- Change only the integer index of an actual chain cycle. -/
def castChainCycles {R : Type u} [CommRing R]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) {i j : ℤ} (h : i = j) :
    K.cycles i →ₗ[R] K.cycles j := by
  subst j
  exact LinearMap.id

lemma castChainCycles_i (R : Type u) [CommRing R] (X : TopCat.{v})
    {i j : ℤ} (h : i = j) (z : (ordinaryComplex R R X).cycles i) :
    (ordinaryComplex R R X).iCycles j (castChainCycles (ordinaryComplex R R X) h z) =
      castOrdinary R h ((ordinaryComplex R R X).iCycles i z) := by
  subst j
  rfl

lemma castChainCycles_homologyπ (R : Type u) [CommRing R] (X : TopCat.{v})
    {i j : ℤ} (h : i = j) (z : (ordinaryComplex R R X).cycles i) :
    (ordinaryComplex R R X).homologyπ j (castChainCycles (ordinaryComplex R R X) h z) =
      degreeTransport R X i j h ((ordinaryComplex R R X).homologyπ i z) := by
  subst j
  rfl

end P202.CompactSupportMV

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Classical
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV.DirectLimitProduct
variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι]
variable (F G : ι → Type w) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
  [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (f : ∀ i j, i ≤ j → F i →ₗ[R] F j)
  (g : ∀ i j, i ≤ j → G i →ₗ[R] G j)
  [DirectedSystem F (fun i j h => (f i j h).toFun)]
  [DirectedSystem G (fun i j h => (g i j h).toFun)]

def productTransition (i j : ι) (h : i ≤ j) : F i × G i →ₗ[R] F j × G j :=
  LinearMap.prodMap (f i j h) (g i j h)

instance : DirectedSystem (fun i => F i × G i)
    (fun i j h => (productTransition F G f g i j h).toFun) where
  map_self := by intro i x; ext <;> simp [productTransition, DirectedSystem.map_self']
  map_map := by intro i j k h h' x; ext <;> simp [productTransition, DirectedSystem.map_map']

def toProductLimit : Module.DirectLimit (fun i => F i × G i) (productTransition F G f g) →ₗ[R]
    Module.DirectLimit F f × Module.DirectLimit G g :=
  Module.DirectLimit.lift R ι _ _
    (fun i => (Module.DirectLimit.of R ι F f i).prodMap (Module.DirectLimit.of R ι G g i))
    (by intro i j h x; ext <;> exact Module.DirectLimit.of_f)

def inlLimit : Module.DirectLimit F f →ₗ[R]
    Module.DirectLimit (fun i => F i × G i) (productTransition F G f g) :=
  Module.DirectLimit.lift R ι F f
    (fun i => (Module.DirectLimit.of R ι _ (productTransition F G f g) i).comp
      (LinearMap.inl R (F i) (G i)))
    (by intro i j h x; simpa [productTransition] using
      (Module.DirectLimit.of_f (R:=R) (f:=productTransition F G f g) (hij:=h) (x:=(x,0))))

def inrLimit : Module.DirectLimit G g →ₗ[R]
    Module.DirectLimit (fun i => F i × G i) (productTransition F G f g) :=
  Module.DirectLimit.lift R ι G g
    (fun i => (Module.DirectLimit.of R ι _ (productTransition F G f g) i).comp
      (LinearMap.inr R (F i) (G i)))
    (by intro i j h x; simpa [productTransition] using
      (Module.DirectLimit.of_f (R:=R) (f:=productTransition F G f g) (hij:=h) (x:=(0,x))))

def fromProductLimit : Module.DirectLimit F f × Module.DirectLimit G g →ₗ[R]
    Module.DirectLimit (fun i => F i × G i) (productTransition F G f g) :=
  (inlLimit F G f g).comp (LinearMap.fst R _ _) +
    (inrLimit F G f g).comp (LinearMap.snd R _ _)

lemma fromProductLimit_toProductLimit :
    (fromProductLimit F G f g).comp (toProductLimit F G f g) = LinearMap.id := by
  apply Module.DirectLimit.hom_ext
  intro i
  apply LinearMap.ext
  rintro ⟨x,y⟩
  simp [fromProductLimit, toProductLimit, inlLimit, inrLimit, Module.DirectLimit.lift_of, ← map_add]

lemma toProductLimit_fromProductLimit [Nonempty ι] [IsDirectedOrder ι] :
    (toProductLimit F G f g).comp (fromProductLimit F G f g) = LinearMap.id := by
  apply LinearMap.ext
  rintro ⟨x,y⟩
  obtain ⟨i, a, rfl⟩ := Module.DirectLimit.exists_of x
  obtain ⟨j, b, rfl⟩ := Module.DirectLimit.exists_of y
  simp [fromProductLimit, toProductLimit, inlLimit, inrLimit, Module.DirectLimit.lift_of]

def productLimitEquiv [Nonempty ι] [IsDirectedOrder ι] :
    Module.DirectLimit (fun i => F i × G i) (productTransition F G f g) ≃ₗ[R]
      Module.DirectLimit F f × Module.DirectLimit G g :=
  LinearEquiv.ofLinearMap (toProductLimit F G f g) (fromProductLimit F G f g)
    (toProductLimit_fromProductLimit F G f g) (fromProductLimit_toProductLimit F G f g)

end P202.CompactSupportMV.DirectLimitProduct

namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CohomologyPairs
open P202Specs.CompactSupportMayerVietoris
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

namespace ModuleSystem
variable {S : Type*} [CommRing S] {ι : Type*} [Preorder ι]
def congr (F G : ModuleSystem S ι) (e : ∀ i, F.obj i ≃ₗ[S] G.obj i)
    (he : ∀ i j h, (e j).toLinearMap.comp (F.transition i j h) =
      (G.transition i j h).comp (e i).toLinearMap) : F.Limit ≃ₗ[S] G.Limit :=
  Module.DirectLimit.congr e he
@[simp] lemma congr_of (F G : ModuleSystem S ι) (e : ∀ i, F.obj i ≃ₗ[S] G.obj i)
    (he : ∀ i j h, (e j).toLinearMap.comp (F.transition i j h) =
      (G.transition i j h).comp (e i).toLinearMap) (i : ι) (a : F.obj i) :
    congr F G e he (F.of i a) = G.of i (e i a) :=
  Module.DirectLimit.congr_apply_of e he a
end ModuleSystem

/-- Excision at an intersection support, preserving the actual intersection
subtype and the original supported cohomology groups. -/
def intersectionStageEquiv (C : Cover M) (p : ℤ) (s : SupportPair M C.left C.right) :
    supportedCohomology R M p (intersectionSupport M C.left C.right s) ≃ₗ[R]
      supportedCohomology R C.intersection p (intersectionIn M C.left C.right s) := by
  haveI := P202.CompactSupport.openExcision R M C.intersection
    (C.left_open.inter C.right_open) (intersectionIn M C.left C.right s) p
  exact ((eqToIso (congrArg (supportedCohomology R M p)
    (ambient_intersectionIn M C.left C.right s).symm)) ≪≫
      asIso (openPullback R M C.intersection (intersectionIn M C.left C.right s) p)).toLinearEquiv

lemma intersectionStageEquiv_natural (C : Cover M) (p : ℤ)
    (s t : SupportPair M C.left C.right) (h : s ≤ t) :
    (intersectionStageEquiv R M C p t).toLinearMap.comp
      (transition R M p _ _ (intersectionSupport_mono M C.left C.right h)) =
    (transition R C.intersection p _ _ (intersectionIn_mono M C.left C.right h)).comp
      (intersectionStageEquiv R M C p s).toLinearMap := by
  ext a
  have he := ambient_intersectionIn M C.left C.right s
  have he' := ambient_intersectionIn M C.left C.right t
  have H := congrArg (fun f => f a) (transition_eqToHom R M p he.symm he'.symm
    (intersectionSupport_mono M C.left C.right h)
    (ambientSupport_mono M C.intersection (intersectionIn_mono M C.left C.right h)))
  change (eqToHom (congrArg (supportedCohomology R M p) he'.symm))
      (transition R M p _ _ _ a) =
    transition R M p _ _ (ambientSupport_mono M C.intersection (intersectionIn_mono M C.left C.right h))
      ((eqToHom (congrArg (supportedCohomology R M p) he.symm)) a) at H
  change openPullback R M C.intersection (intersectionIn M C.left C.right t) p
      ((eqToHom (congrArg (supportedCohomology R M p) he'.symm))
        (transition R M p _ _ _ a)) =
    transition R C.intersection p _ _ _
      (openPullback R M C.intersection (intersectionIn M C.left C.right s) p
        ((eqToHom (congrArg (supportedCohomology R M p) he.symm)) a))
  rw [H, openPullback_transition]

/-- The genuine intersection direct limit is compact cohomology of the actual
intersection subspace, by natural excision and the proved cofinality. -/
def intersectionColimitEquiv (C : Cover M) (p : ℤ) :
    ((cohomologySystem R M p).reindex (intersectionSupport M C.left C.right)
      (intersectionSupport_mono M C.left C.right)).Limit ≃ₗ[R]
        CompactCohomology R C.intersection p := by
  let F := (cohomologySystem R M p).reindex (intersectionSupport M C.left C.right)
    (intersectionSupport_mono M C.left C.right)
  let G := (cohomologySystem R C.intersection p).reindex (intersectionIn M C.left C.right)
    (intersectionIn_mono M C.left C.right)
  let e₁ : F.Limit ≃ₗ[R] G.Limit := ModuleSystem.congr F G (intersectionStageEquiv R M C p)
    (intersectionStageEquiv_natural R M C p)
  let e₂ : G.Limit ≃ₗ[R] CompactCohomology R C.intersection p :=
    LinearEquiv.ofBijective ((cohomologySystem R C.intersection p).reindexMap
      (intersectionIn M C.left C.right) (intersectionIn_mono M C.left C.right))
      (intersectionColimit R M C.left C.right p)
  exact e₁.trans e₂

@[simp] lemma intersectionColimitEquiv_of (C : Cover M) (p : ℤ)
    (s : SupportPair M C.left C.right)
    (a : supportedCohomology R M p (intersectionSupport M C.left C.right s)) :
    intersectionColimitEquiv R M C p
      (((cohomologySystem R M p).reindex (intersectionSupport M C.left C.right)
        (intersectionSupport_mono M C.left C.right)).of s a) =
      ofSupport R C.intersection p (intersectionIn M C.left C.right s)
        (intersectionStageEquiv R M C p s a) := by
  simp only [intersectionColimitEquiv, LinearEquiv.trans_apply, ModuleSystem.congr_of]
  change ((cohomologySystem R C.intersection p).reindexMap
    (intersectionIn M C.left C.right) (intersectionIn_mono M C.left C.right)) _ = _
  exact ModuleSystem.reindexMap_of_system (cohomologySystem R C.intersection p)
    (intersectionIn M C.left C.right) (intersectionIn_mono M C.left C.right) s _
end P202.CompactSupportMV

namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CohomologyPairs
open P202Specs.CompactSupportMayerVietoris
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]



def leftSupportSystem (C : Cover M) (p : ℤ) : ModuleSystem R (SupportPair M C.left C.right) :=
  (cohomologySystem R M p).reindex (fun s => ambientSupport M C.left s.1)
    (fun _ _ h => ambientSupport_mono M C.left h.1)

def rightSupportSystem (C : Cover M) (p : ℤ) : ModuleSystem R (SupportPair M C.left C.right) :=
  (cohomologySystem R M p).reindex (fun s => ambientSupport M C.right s.2)
    (fun _ _ h => ambientSupport_mono M C.right h.2)

def leftStageEquiv (C : Cover M) (p : ℤ) (s : SupportPair M C.left C.right) :
    (leftSupportSystem R M C p).obj s ≃ₗ[R] supportedCohomology R C.left p s.1 := by
  haveI := P202.CompactSupport.openExcision R M C.left C.left_open s.1 p
  exact (asIso (openPullback R M C.left s.1 p)).toLinearEquiv

def rightStageEquiv (C : Cover M) (p : ℤ) (s : SupportPair M C.left C.right) :
    (rightSupportSystem R M C p).obj s ≃ₗ[R] supportedCohomology R C.right p s.2 := by
  haveI := P202.CompactSupport.openExcision R M C.right C.right_open s.2 p
  exact (asIso (openPullback R M C.right s.2 p)).toLinearEquiv

lemma leftStageEquiv_natural (C : Cover M) (p : ℤ)
    (s t : SupportPair M C.left C.right) (h : s ≤ t) :
    (leftStageEquiv R M C p t).toLinearMap.comp ((leftSupportSystem R M C p).transition s t h) =
    (transition R C.left p _ _ h.1).comp (leftStageEquiv R M C p s).toLinearMap := by
  ext a
  exact openPullback_transition R M C.left p h.1 a

lemma rightStageEquiv_natural (C : Cover M) (p : ℤ)
    (s t : SupportPair M C.left C.right) (h : s ≤ t) :
    (rightStageEquiv R M C p t).toLinearMap.comp ((rightSupportSystem R M C p).transition s t h) =
    (transition R C.right p _ _ h.2).comp (rightStageEquiv R M C p s).toLinearMap := by
  ext a
  exact openPullback_transition R M C.right p h.2 a

lemma supportPair_fst_mono (C : Cover M) :
    Monotone (Prod.fst : SupportPair M C.left C.right → Support C.left) :=
  fun _ _ h => h.1

lemma supportPair_snd_mono (C : Cover M) :
    Monotone (Prod.snd : SupportPair M C.left C.right → Support C.right) :=
  fun _ _ h => h.2

def leftColimitEquiv (C : Cover M) (p : ℤ) :
    (leftSupportSystem R M C p).Limit ≃ₗ[R] CompactCohomology R C.left p := by
  let G := (cohomologySystem R C.left p).reindex
    (Prod.fst : SupportPair M C.left C.right → Support C.left) (supportPair_fst_mono M C)
  let e₁ : (leftSupportSystem R M C p).Limit ≃ₗ[R] G.Limit :=
    ModuleSystem.congr (leftSupportSystem R M C p) G (leftStageEquiv R M C p) (leftStageEquiv_natural R M C p)
  let e₂ : G.Limit ≃ₗ[R] CompactCohomology R C.left p :=
    LinearEquiv.ofBijective ((cohomologySystem R C.left p).reindexMap
      (Prod.fst : SupportPair M C.left C.right → Support C.left) (supportPair_fst_mono M C))
      (cofinalReindex R (Support C.left) (SupportPair M C.left C.right)
        (cohomologySystem R C.left p) Prod.fst (supportPair_fst_mono M C)
        (fun K => ⟨(K,⊥), le_rfl⟩))
  exact e₁.trans e₂

def rightColimitEquiv (C : Cover M) (p : ℤ) :
    (rightSupportSystem R M C p).Limit ≃ₗ[R] CompactCohomology R C.right p := by
  let G := (cohomologySystem R C.right p).reindex
    (Prod.snd : SupportPair M C.left C.right → Support C.right) (supportPair_snd_mono M C)
  let e₁ : (rightSupportSystem R M C p).Limit ≃ₗ[R] G.Limit :=
    ModuleSystem.congr (rightSupportSystem R M C p) G (rightStageEquiv R M C p) (rightStageEquiv_natural R M C p)
  let e₂ : G.Limit ≃ₗ[R] CompactCohomology R C.right p :=
    LinearEquiv.ofBijective ((cohomologySystem R C.right p).reindexMap
      (Prod.snd : SupportPair M C.left C.right → Support C.right) (supportPair_snd_mono M C))
      (cofinalReindex R (Support C.right) (SupportPair M C.left C.right)
        (cohomologySystem R C.right p) Prod.snd (supportPair_snd_mono M C)
        (fun L => ⟨(⊥,L), le_rfl⟩))
  exact e₁.trans e₂

@[simp] lemma leftColimitEquiv_of (C : Cover M) (p : ℤ)
    (s : SupportPair M C.left C.right) (a : (leftSupportSystem R M C p).obj s) :
    leftColimitEquiv R M C p ((leftSupportSystem R M C p).of s a) =
      ofSupport R C.left p s.1 (openPullback R M C.left s.1 p a) := by
  simp only [leftColimitEquiv, LinearEquiv.trans_apply, ModuleSystem.congr_of]
  change ((cohomologySystem R C.left p).reindexMap
    (Prod.fst : SupportPair M C.left C.right → Support C.left) (supportPair_fst_mono M C)) _ = _
  exact ModuleSystem.reindexMap_of_system (cohomologySystem R C.left p)
    Prod.fst (supportPair_fst_mono M C) s _

@[simp] lemma rightColimitEquiv_of (C : Cover M) (p : ℤ)
    (s : SupportPair M C.left C.right) (a : (rightSupportSystem R M C p).obj s) :
    rightColimitEquiv R M C p ((rightSupportSystem R M C p).of s a) =
      ofSupport R C.right p s.2 (openPullback R M C.right s.2 p a) := by
  simp only [rightColimitEquiv, LinearEquiv.trans_apply, ModuleSystem.congr_of]
  change ((cohomologySystem R C.right p).reindexMap
    (Prod.snd : SupportPair M C.left C.right → Support C.right) (supportPair_snd_mono M C)) _ = _
  exact ModuleSystem.reindexMap_of_system (cohomologySystem R C.right p)
    Prod.snd (supportPair_snd_mono M C) s _
end P202.CompactSupportMV

/-! Exact finite-support rows, their compatible directed systems, and the finite signed cap square. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Classical
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts
namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CohomologyPairs
open P202Specs.RelativeSingularChains P202Specs.RelativeCupProduct
open P202Specs.CompactSupportMayerVietoris P202Specs.LocalOrientation
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

lemma supportComparison_toLeft (K L : Support M) :
    supportComparison R M K L ≫ sumToLeft R (supportComplements M K L) =
      cochainTransition R M (show K ⊓ L ≤ K from inf_le_left) := by
  apply HomologicalComplex.Hom.ext
  funext p
  haveI : Mono ((cochainInclusion R M K).f p) :=
    (ModuleCat.mono_iff_injective _).mpr (P202.CompactSupport.cochainInclusion_injective R M K p)
  apply (cancel_mono ((cochainInclusion R M K).f p)).mp
  change ((supportComparison R M K L ≫ sumToLeft R (supportComplements M K L)) ≫
    cochainInclusion R M K).f p =
      (cochainTransition R M (show K ⊓ L ≤ K from inf_le_left) ≫ cochainInclusion R M K).f p
  rw [cochainInclusion_transition, Category.assoc]
  change (supportComparison R M K L ≫ sumToLeft R (supportComplements M K L) ≫
    relativeToAbsolute R R (supportComplements M K L).leftPair).f p = _
  rw [sumToLeft_absolute]
  unfold supportComparison
  rw [Category.assoc, P202.RelativeCupProduct.comparison_absolute]
  have h := (cochainSequenceMap R R (eqToHom (supportComplements_union M K L))).comm₁₂
  change (relativeCochainFunctor R R).map (eqToHom (supportComplements_union M K L)).op ≫
    relativeToAbsolute R R (supportComplements M K L).unionPair =
      cochainInclusion R M (K ⊓ L) ≫
        (ordinaryCochainFunctor R R).map (eqToHom (supportComplements_union M K L)).map.op at h
  rw [relativeCochain_eqToHom] at h
  change (eqToHom (congrArg (relativeCochains R R) (supportComplements_union M K L).symm) ≫
    relativeToAbsolute R R (supportComplements M K L).unionPair).f p = _
  have hm : (eqToHom (supportComplements_union M K L)).map = 𝟙 (TopCat.of M) :=
    pair_sameSpace_eqToHom_map _ _ _ _
  rw [hm] at h
  have hi : (ordinaryCochainFunctor R R).map (𝟙 (op (TopCat.of M))) =
      𝟙 (ordinaryCochains R R (TopCat.of M)) := (ordinaryCochainFunctor R R).map_id _
  change (eqToHom (congrArg (relativeCochains R R) (supportComplements_union M K L).symm) ≫
    relativeToAbsolute R R (supportComplements M K L).unionPair) =
      cochainInclusion R M (K ⊓ L) ≫ (ordinaryCochainFunctor R R).map (𝟙 (op (TopCat.of M))) at h
  rw [hi, Category.comp_id] at h
  exact congrArg (fun f => f.f p) h

lemma supportComparison_toRight (K L : Support M) :
    supportComparison R M K L ≫ sumToRight R (supportComplements M K L) =
      cochainTransition R M (show K ⊓ L ≤ L from inf_le_right) := by
  apply HomologicalComplex.Hom.ext
  funext p
  haveI : Mono ((cochainInclusion R M L).f p) :=
    (ModuleCat.mono_iff_injective _).mpr (P202.CompactSupport.cochainInclusion_injective R M L p)
  apply (cancel_mono ((cochainInclusion R M L).f p)).mp
  change ((supportComparison R M K L ≫ sumToRight R (supportComplements M K L)) ≫
    cochainInclusion R M L).f p =
      (cochainTransition R M (show K ⊓ L ≤ L from inf_le_right) ≫ cochainInclusion R M L).f p
  rw [cochainInclusion_transition, Category.assoc]
  change (supportComparison R M K L ≫ sumToRight R (supportComplements M K L) ≫
    relativeToAbsolute R R (supportComplements M K L).rightPair).f p = _
  rw [sumToRight_absolute]
  unfold supportComparison
  rw [Category.assoc, P202.RelativeCupProduct.comparison_absolute]
  have h := (cochainSequenceMap R R (eqToHom (supportComplements_union M K L))).comm₁₂
  change (relativeCochainFunctor R R).map (eqToHom (supportComplements_union M K L)).op ≫
    relativeToAbsolute R R (supportComplements M K L).unionPair =
      cochainInclusion R M (K ⊓ L) ≫
        (ordinaryCochainFunctor R R).map (eqToHom (supportComplements_union M K L)).map.op at h
  rw [relativeCochain_eqToHom] at h
  change (eqToHom (congrArg (relativeCochains R R) (supportComplements_union M K L).symm) ≫
    relativeToAbsolute R R (supportComplements M K L).unionPair).f p = _
  have hm : (eqToHom (supportComplements_union M K L)).map = 𝟙 (TopCat.of M) :=
    pair_sameSpace_eqToHom_map _ _ _ _
  rw [hm] at h
  have hi : (ordinaryCochainFunctor R R).map (𝟙 (op (TopCat.of M))) =
      𝟙 (ordinaryCochains R R (TopCat.of M)) := (ordinaryCochainFunctor R R).map_id _
  change (eqToHom (congrArg (relativeCochains R R) (supportComplements_union M K L).symm) ≫
    relativeToAbsolute R R (supportComplements M K L).unionPair) =
      cochainInclusion R M (K ⊓ L) ≫ (ordinaryCochainFunctor R R).map (𝟙 (op (TopCat.of M))) at h
  rw [hi, Category.comp_id] at h
  exact congrArg (fun f => f.f p) h


lemma supportToUnion_left (K L : Support M) :
    cochainTransition R M (show K ≤ K ⊔ L from le_sup_left) ≫
      unionSupportComparison R M K L = leftToIntersection R (supportComplements M K L) := by
  apply HomologicalComplex.Hom.ext
  funext p
  haveI : Mono ((relativeToAbsolute R R (intersectionPair (supportComplements M K L))).f p) :=
    (ModuleCat.mono_iff_injective _).mpr
      (relativeToAbsolute_injective R (intersectionPair (supportComplements M K L)) p)
  apply (cancel_mono ((relativeToAbsolute R R (intersectionPair (supportComplements M K L))).f p)).mp
  change ((cochainTransition R M (show K ≤ K ⊔ L from le_sup_left) ≫
    unionSupportComparison R M K L) ≫ relativeToAbsolute R R (intersectionPair (supportComplements M K L))).f p =
    (leftToIntersection R (supportComplements M K L) ≫
      relativeToAbsolute R R (intersectionPair (supportComplements M K L))).f p
  rw [Category.assoc, unionSupportComparison_absolute, cochainInclusion_transition,
    leftToIntersection_absolute]
  rfl

lemma supportToUnion_right (K L : Support M) :
    cochainTransition R M (show L ≤ K ⊔ L from le_sup_right) ≫
      unionSupportComparison R M K L = rightToIntersection R (supportComplements M K L) := by
  apply HomologicalComplex.Hom.ext
  funext p
  haveI : Mono ((relativeToAbsolute R R (intersectionPair (supportComplements M K L))).f p) :=
    (ModuleCat.mono_iff_injective _).mpr
      (relativeToAbsolute_injective R (intersectionPair (supportComplements M K L)) p)
  apply (cancel_mono ((relativeToAbsolute R R (intersectionPair (supportComplements M K L))).f p)).mp
  change ((cochainTransition R M (show L ≤ K ⊔ L from le_sup_right) ≫
    unionSupportComparison R M K L) ≫ relativeToAbsolute R R (intersectionPair (supportComplements M K L))).f p =
    (rightToIntersection R (supportComplements M K L) ≫
      relativeToAbsolute R R (intersectionPair (supportComplements M K L))).f p
  rw [Category.assoc, unionSupportComparison_absolute, cochainInclusion_transition,
    rightToIntersection_absolute]
  rfl

abbrev supportMiddle (K L : Support M) (p : ℤ) :=
  supportedCohomology R M p K ⊞ supportedCohomology R M p L

def supportFirst (K L : Support M) (p : ℤ) :
    supportedCohomology R M p (K ⊓ L) ⟶ supportMiddle R M K L p :=
  biprod.lift (ModuleCat.ofHom (transition R M p _ _ inf_le_left))
    (-ModuleCat.ofHom (transition R M p _ _ inf_le_right))

def supportSum (K L : Support M) (p : ℤ) :
    supportMiddle R M K L p ⟶ supportedCohomology R M p (K ⊔ L) :=
  biprod.desc (ModuleCat.ofHom (transition R M p _ _ le_sup_left))
    (ModuleCat.ofHom (transition R M p _ _ le_sup_right))

def supportMiddleIso (K L : Support M) (p : ℤ) :
    supportMiddle R M K L p ≅ (finiteSequence R (supportComplements M K L)).X₂.homology p :=
  ((homologyFunctor (ModuleCat.{max u v} R) (.up ℤ) p).mapBiprod
    (supportedCochains R M K) (supportedCochains R M L)).symm

lemma supportFirst_comparison (K L : Support M) (p : ℤ) :
    supportFirst R M K L p ≫ (supportMiddleIso R M K L p).hom =
      homologyMap (supportComparison R M K L) p ≫
        homologyMap (finiteSequence R (supportComplements M K L)).f p := by
  apply (cancel_mono (supportMiddleIso R M K L p).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hmid : homologyMap (finiteSequence R (supportComplements M K L)).f p ≫
      (supportMiddleIso R M K L p).inv =
      biprod.lift (homologyMap (sumToLeft R (supportComplements M K L)) p)
        (-homologyMap (sumToRight R (supportComplements M K L)) p) := by
    dsimp only [supportMiddle, supportMiddleIso, Iso.symm_inv]
    apply biprod.hom_ext
    · change (homologyMap (finiteSequence R (supportComplements M K L)).f p ≫
        biprod.lift (homologyMap (biprod.fst :
          supportedCochains R M K ⊞ supportedCochains R M L ⟶ supportedCochains R M K) p)
          (homologyMap (biprod.snd :
          supportedCochains R M K ⊞ supportedCochains R M L ⟶ supportedCochains R M L) p)) ≫
          biprod.fst = _
      rw [Category.assoc, biprod.lift_fst, ← homologyMap_comp]
      change homologyMap ((biprod.lift (sumToLeft R (supportComplements M K L))
        (-sumToRight R (supportComplements M K L))) ≫ biprod.fst) p = _
      simp only [biprod.lift_fst]
      erw [biprod.lift_fst]
    · change (homologyMap (finiteSequence R (supportComplements M K L)).f p ≫
        biprod.lift (homologyMap (biprod.fst :
          supportedCochains R M K ⊞ supportedCochains R M L ⟶ supportedCochains R M K) p)
          (homologyMap (biprod.snd :
          supportedCochains R M K ⊞ supportedCochains R M L ⟶ supportedCochains R M L) p)) ≫
          biprod.snd = _
      rw [Category.assoc, biprod.lift_snd, ← homologyMap_comp]
      change homologyMap ((biprod.lift (sumToLeft R (supportComplements M K L))
        (-sumToRight R (supportComplements M K L))) ≫ biprod.snd) p = _
      simp only [biprod.lift_snd, homologyMap_neg]
      erw [biprod.lift_snd]
  rw [Category.assoc, hmid]
  apply biprod.hom_ext
  · dsimp only [supportMiddle] at *
    simp only [supportFirst, Category.assoc, biprod.lift_fst]
    erw [biprod.lift_fst]
    change homologyMap (cochainTransition R M (show K ⊓ L ≤ K from inf_le_left)) p = _
    erw [← homologyMap_comp, supportComparison_toLeft]
  · dsimp only [supportMiddle] at *
    simp only [supportFirst, Category.assoc, biprod.lift_snd]
    erw [biprod.lift_snd, Preadditive.comp_neg]
    congr 1
    change homologyMap (cochainTransition R M (show K ⊓ L ≤ L from inf_le_right)) p = _
    erw [← homologyMap_comp, supportComparison_toRight]

lemma supportSum_comparison (K L : Support M) (p : ℤ) :
    supportSum R M K L p ≫ homologyMap (unionSupportComparison R M K L) p =
      (supportMiddleIso R M K L p).hom ≫
        homologyMap (finiteSequence R (supportComplements M K L)).g p := by
  have hmid : (supportMiddleIso R M K L p).hom ≫
      homologyMap (finiteSequence R (supportComplements M K L)).g p =
      biprod.desc (homologyMap (leftToIntersection R (supportComplements M K L)) p)
        (homologyMap (rightToIntersection R (supportComplements M K L)) p) := by
    exact biprod.mapBiprod_inv_map_desc (homologyFunctor (ModuleCat.{max u v} R) (.up ℤ) p)
      (supportedCochains R M K) (supportedCochains R M L) _ _
  rw [hmid]
  apply biprod.hom_ext'
  · simp only [supportSum, ← Category.assoc, biprod.inl_desc]
    change homologyMap (cochainTransition R M (show K ≤ K ⊔ L from le_sup_left)) p ≫ _ = _
    rw [← homologyMap_comp, supportToUnion_left]
  · simp only [supportSum, ← Category.assoc, biprod.inr_desc]
    change homologyMap (cochainTransition R M (show L ≤ K ⊔ L from le_sup_right)) p ≫ _ = _
    rw [← homologyMap_comp, supportToUnion_right]

/-- The complete finite-support sequence on the original supported cohomology
modules, before excision into the open pieces or passage to the filtered limit. -/
theorem supportLongExact (K L : Support M) (p : ℤ) :
    (ComposableArrows.mk₅ (supportFirst R M K L p) (supportSum R M K L p)
      (supportConnecting R M K L p) (supportFirst R M K L (p+1))
      (supportSum R M K L (p+1))).Exact := by
  haveI := finiteSupportComparison R M K L p
  haveI := finiteSupportComparison R M K L (p+1)
  haveI : IsIso (unionSupportComparison R M K L) := by
    dsimp only [unionSupportComparison]
    infer_instance
  let S := finiteSequence R (supportComplements M K L)
  let e := ComposableArrows.isoMk₅
    (f := ComposableArrows.mk₅ (supportFirst R M K L p) (supportSum R M K L p)
      (supportConnecting R M K L p) (supportFirst R M K L (p+1)) (supportSum R M K L (p+1)))
    (g := P202Specs.ChainLES.segment (finiteShortExact R (supportComplements M K L)) p (p+1) (by simp))
    (asIso (homologyMap (supportComparison R M K L) p))
    (supportMiddleIso R M K L p)
    (asIso (homologyMap (unionSupportComparison R M K L) p))
    (asIso (homologyMap (supportComparison R M K L) (p+1)))
    (supportMiddleIso R M K L (p+1))
    (asIso (homologyMap (unionSupportComparison R M K L) (p+1)))
    (supportFirst_comparison R M K L p) (supportSum_comparison R M K L p)
    (supportConnecting_comparison R M K L p)
    (supportFirst_comparison R M K L (p+1)) (supportSum_comparison R M K L (p+1))
  exact ComposableArrows.exact_of_iso e.symm
    ((P202.ChainLES.exactness S (finiteShortExact R (supportComplements M K L))).2 p (p+1) (by simp))

end P202.CompactSupportMV

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Classical
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV
variable {R : Type u} [CommRing R]

lemma biprodIsoProd_inv_apply (B D : ModuleCat.{max u v} R) (x : B × D) :
    (ModuleCat.biprodIsoProd B D).inv x =
      (biprod.inl : B ⟶ B ⊞ D) x.1 + (biprod.inr : D ⟶ B ⊞ D) x.2 := by
  apply P202.MayerVietoris.biprod_element_ext
  · rw [map_add, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      ModuleCat.biprodIsoProd_inv_comp_fst, biprod.inl_fst, biprod.inr_fst]
    simp
  · rw [map_add, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      ModuleCat.biprodIsoProd_inv_comp_snd, biprod.inl_snd, biprod.inr_snd]
    simp

lemma biprodIsoProd_hom_apply (B D : ModuleCat.{max u v} R) (x : (B ⊞ D : ModuleCat R)) :
    (ModuleCat.biprodIsoProd B D).hom x =
      ((biprod.fst : B ⊞ D ⟶ B) x, (biprod.snd : B ⊞ D ⟶ D) x) := by
  apply (ModuleCat.biprodIsoProd B D).toLinearEquiv.symm.injective
  change (ModuleCat.biprodIsoProd B D).inv ((ModuleCat.biprodIsoProd B D).hom x) =
    (ModuleCat.biprodIsoProd B D).inv _
  rw [← ModuleCat.comp_apply, Iso.hom_inv_id, ModuleCat.id_apply, biprodIsoProd_inv_apply]
  have H := congrArg (fun f : B ⊞ D ⟶ B ⊞ D => f x) (biprod.total (X:=B) (Y:=D))
  simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply, ModuleCat.id_apply] using H.symm

end P202.CompactSupportMV

namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open P202Specs.CompactSupport
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

def supportMiddleProdEquiv (K L : Support M) (p : ℤ) :
    supportMiddle R M K L p ≃ₗ[R]
      (supportedCohomology R M p K × supportedCohomology R M p L) :=
  (ModuleCat.biprodIsoProd (supportedCohomology R M p K)
    (supportedCohomology R M p L)).toLinearEquiv

lemma supportFirst_prod (K L : Support M) (p : ℤ) :
    (supportMiddleProdEquiv R M K L p).toLinearMap.comp (supportFirst R M K L p).hom =
      (transition R M p (K ⊓ L) K inf_le_left).prod (-transition R M p (K ⊓ L) L inf_le_right) := by
  apply LinearMap.ext
  intro x
  change (ModuleCat.biprodIsoProd (supportedCohomology R M p K)
    (supportedCohomology R M p L)).hom ((supportFirst R M K L p) x) = _
  rw [biprodIsoProd_hom_apply]
  apply Prod.ext
  · change (biprod.fst : supportMiddle R M K L p ⟶ _)
      ((biprod.lift (ModuleCat.ofHom (transition R M p (K ⊓ L) K inf_le_left))
        (-ModuleCat.ofHom (transition R M p (K ⊓ L) L inf_le_right))) x) = _
    rw [← ModuleCat.comp_apply, biprod.lift_fst]
    rfl
  · change (biprod.snd : supportMiddle R M K L p ⟶ _)
      ((biprod.lift (ModuleCat.ofHom (transition R M p (K ⊓ L) K inf_le_left))
        (-ModuleCat.ofHom (transition R M p (K ⊓ L) L inf_le_right))) x) = _
    rw [← ModuleCat.comp_apply, biprod.lift_snd]
    rfl

lemma supportSum_prod (K L : Support M) (p : ℤ) :
    ((transition R M p K (K ⊔ L) le_sup_left).comp (LinearMap.fst R (supportedCohomology R M p K) (supportedCohomology R M p L)) +
      (transition R M p L (K ⊔ L) le_sup_right).comp (LinearMap.snd R (supportedCohomology R M p K) (supportedCohomology R M p L))).comp
        (supportMiddleProdEquiv R M K L p).toLinearMap =
      (supportSum R M K L p).hom := by
  apply LinearMap.ext
  intro x
  change transition R M p K (K ⊔ L) le_sup_left
      ((ModuleCat.biprodIsoProd (supportedCohomology R M p K)
        (supportedCohomology R M p L)).hom x).1 +
    transition R M p L (K ⊔ L) le_sup_right
      ((ModuleCat.biprodIsoProd (supportedCohomology R M p K)
        (supportedCohomology R M p L)).hom x).2 = _
  rw [biprodIsoProd_hom_apply]
  change _ = (biprod.desc (ModuleCat.ofHom (transition R M p K (K ⊔ L) le_sup_left))
    (ModuleCat.ofHom (transition R M p L (K ⊔ L) le_sup_right))) x
  rw [biprod.desc_eq]
  rfl

lemma supportProduct_exact_first_sum (K L : Support M) (p : ℤ) :
    Function.Exact
      ((transition R M p (K ⊓ L) K inf_le_left).prod (-transition R M p (K ⊓ L) L inf_le_right))
      ((transition R M p K (K ⊔ L) le_sup_left).comp (LinearMap.fst R (supportedCohomology R M p K) (supportedCohomology R M p L)) +
        (transition R M p L (K ⊔ L) le_sup_right).comp (LinearMap.snd R (supportedCohomology R M p K) (supportedCohomology R M p L))) := by
  have h := supportLongExact R M K L p
  have H : Function.Exact (supportFirst R M K L p).hom (supportSum R M K L p).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (h.exact 0 (by omega))
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := LinearEquiv.refl R _) (e₂ := supportMiddleProdEquiv R M K L p)
    (e₃ := LinearEquiv.refl R _) _ _ H
  · simpa using (supportFirst_prod R M K L p).symm
  · simpa using supportSum_prod R M K L p

lemma supportProduct_exact_sum_connecting (K L : Support M) (p : ℤ) :
    Function.Exact
      ((transition R M p K (K ⊔ L) le_sup_left).comp (LinearMap.fst R (supportedCohomology R M p K) (supportedCohomology R M p L)) +
        (transition R M p L (K ⊔ L) le_sup_right).comp (LinearMap.snd R (supportedCohomology R M p K) (supportedCohomology R M p L)))
      (supportConnecting R M K L p).hom := by
  have h := supportLongExact R M K L p
  have H : Function.Exact (supportSum R M K L p).hom (supportConnecting R M K L p).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (h.exact 1 (by omega))
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := supportMiddleProdEquiv R M K L p) (e₂ := LinearEquiv.refl R _)
    (e₃ := LinearEquiv.refl R _) _ _ H
  · simpa using supportSum_prod R M K L p
  · rfl

lemma supportProduct_exact_connecting_first (K L : Support M) (p : ℤ) :
    Function.Exact (supportConnecting R M K L p).hom
      ((transition R M (p+1) (K ⊓ L) K inf_le_left).prod
        (-transition R M (p+1) (K ⊓ L) L inf_le_right)) := by
  have h := supportLongExact R M K L p
  have H : Function.Exact (supportConnecting R M K L p).hom (supportFirst R M K L (p+1)).hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (h.exact 2 (by omega))
  apply Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := LinearEquiv.refl R _) (e₂ := LinearEquiv.refl R _)
    (e₃ := supportMiddleProdEquiv R M K L (p+1)) _ _ H
  · rfl
  · simpa using (supportFirst_prod R M K L (p+1)).symm

end P202.CompactSupportMV

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Classical
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV.DirectLimitProduct
variable {R : Type*} [CommRing R] {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable (F G : ι → Type w) [∀ i, AddCommGroup (F i)] [∀ i, Module R (F i)]
  [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (f : ∀ i j, i ≤ j → F i →ₗ[R] F j)
  (g : ∀ i j, i ≤ j → G i →ₗ[R] G j)
  [DirectedSystem F (fun i j h => (f i j h).toFun)]
  [DirectedSystem G (fun i j h => (g i j h).toFun)]
@[simp] lemma productLimitEquiv_of (i : ι) (x : F i × G i) :
    productLimitEquiv F G f g (Module.DirectLimit.of R ι _ (productTransition F G f g) i x) =
      (Module.DirectLimit.of R ι F f i x.1, Module.DirectLimit.of R ι G g i x.2) :=
by
  change toProductLimit F G f g _ = _
  unfold toProductLimit
  exact Module.DirectLimit.lift_of _ _ _
end P202.CompactSupportMV.DirectLimitProduct

namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CohomologyPairs
open P202Specs.CompactSupportMayerVietoris
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

abbrev intersectionSystem (C : Cover M) (p : ℤ) :=
  (cohomologySystem R M p).reindex (intersectionSupport M C.left C.right)
    (intersectionSupport_mono M C.left C.right)

abbrev unionSystem (C : Cover M) (p : ℤ) :=
  (cohomologySystem R M p).reindex (unionSupport M C.left C.right)
    (unionSupport_mono M C.left C.right)

def middleProductSystem (C : Cover M) (p : ℤ) : ModuleSystem R (SupportPair M C.left C.right) where
  obj s := ModuleCat.of R ((leftSupportSystem R M C p).obj s × (rightSupportSystem R M C p).obj s)
  transition := DirectLimitProduct.productTransition
    (fun i => (leftSupportSystem R M C p).obj i) (fun i => (rightSupportSystem R M C p).obj i)
    (leftSupportSystem R M C p).transition (rightSupportSystem R M C p).transition
  self s x := by ext <;> exact DirectedSystem.map_self' (transition R M p) _
  trans s t q hst htq x := by ext <;> exact DirectedSystem.map_map' (transition R M p) _ _ _

def supportProductFirst (C : Cover M) (p : ℤ) (s : SupportPair M C.left C.right) :
    (intersectionSystem R M C p).obj s →ₗ[R] (middleProductSystem R M C p).obj s :=
  (transition R M p _ _ inf_le_left).prod (-transition R M p _ _ inf_le_right)

def supportProductSum (C : Cover M) (p : ℤ) (s : SupportPair M C.left C.right) :
    (middleProductSystem R M C p).obj s →ₗ[R] (unionSystem R M C p).obj s :=
  (transition R M p _ _ le_sup_left).comp (LinearMap.fst R _ _) +
    (transition R M p _ _ le_sup_right).comp (LinearMap.snd R _ _)

def firstSystemMap (C : Cover M) (p : ℤ) :
    (intersectionSystem R M C p).Map (middleProductSystem R M C p) where
  component := supportProductFirst R M C p
  comm s t h := by
    apply LinearMap.ext
    intro a
    apply Prod.ext
    · change transition R M p _ _ _ (transition R M p _ _ _ a) =
        transition R M p _ _ _ (transition R M p _ _ _ a)
      rw [DirectedSystem.map_map', DirectedSystem.map_map']
    · change -(transition R M p _ _ _ (transition R M p _ _ _ a)) =
        transition R M p _ _ _ (-(transition R M p _ _ _ a))
      rw [map_neg, DirectedSystem.map_map', DirectedSystem.map_map']

def sumSystemMap (C : Cover M) (p : ℤ) :
    (middleProductSystem R M C p).Map (unionSystem R M C p) where
  component := supportProductSum R M C p
  comm s t h := by
    apply LinearMap.ext
    rintro ⟨a,b⟩
    let K := ambientSupport M C.left s.1
    let L := ambientSupport M C.right s.2
    let K' := ambientSupport M C.left t.1
    let L' := ambientSupport M C.right t.2
    let hK : K ≤ K' := ambientSupport_mono M C.left h.1
    let hL : L ≤ L' := ambientSupport_mono M C.right h.2
    change transition R M p K' (K' ⊔ L') le_sup_left (transition R M p K K' hK a) +
      transition R M p L' (K' ⊔ L') le_sup_right (transition R M p L L' hL b) =
      transition R M p (K ⊔ L) (K' ⊔ L') (sup_le_sup hK hL)
        (transition R M p K (K ⊔ L) le_sup_left a + transition R M p L (K ⊔ L) le_sup_right b)
    have h₁ := DirectedSystem.map_map' (transition R M p) hK (show K' ≤ K' ⊔ L' from le_sup_left) a
    have h₂ := DirectedSystem.map_map' (transition R M p) hL (show L' ≤ K' ⊔ L' from le_sup_right) b
    have h₃ := DirectedSystem.map_map' (transition R M p) (show K ≤ K ⊔ L from le_sup_left)
      (sup_le_sup hK hL) a
    have h₄ := DirectedSystem.map_map' (transition R M p) (show L ≤ K ⊔ L from le_sup_right)
      (sup_le_sup hK hL) b
    exact (congrArg₂ (fun x y => x+y) (h₁.trans h₃.symm) (h₂.trans h₄.symm)).trans
      ((transition R M p (K ⊔ L) (K' ⊔ L') (sup_le_sup hK hL)).map_add _ _).symm

def connectingSystemMap (C : Cover M) (p : ℤ) :
    (unionSystem R M C p).Map (intersectionSystem R M C (p+1)) where
  component s := (supportConnecting R M (ambientSupport M C.left s.1)
    (ambientSupport M C.right s.2) p).hom
  comm s t h := by
    ext a
    exact supportConnecting_transition R M
      (ambientSupport_mono M C.left h.1) (ambientSupport_mono M C.right h.2) p a

def middleProductColimitEquiv (C : Cover M) (p : ℤ) :
    (middleProductSystem R M C p).Limit ≃ₗ[R]
      (CompactCohomology R C.left p × CompactCohomology R C.right p) := by
  let F := leftSupportSystem R M C p
  let G := rightSupportSystem R M C p
  let e₁ : (middleProductSystem R M C p).Limit ≃ₗ[R] F.Limit × G.Limit :=
    DirectLimitProduct.productLimitEquiv (fun i => F.obj i) (fun i => G.obj i) F.transition G.transition
  exact e₁.trans ((leftColimitEquiv R M C p).prodCongr (rightColimitEquiv R M C p))

set_option maxHeartbeats 400000 in
@[simp] lemma middleProductColimitEquiv_of (C : Cover M) (p : ℤ)
    (s : SupportPair M C.left C.right) (a : (middleProductSystem R M C p).obj s) :
    middleProductColimitEquiv R M C p ((middleProductSystem R M C p).of s a) =
      (ofSupport R C.left p s.1 (openPullback R M C.left s.1 p a.1),
        ofSupport R C.right p s.2 (openPullback R M C.right s.2 p a.2)) := by
  let F := leftSupportSystem R M C p
  let G := rightSupportSystem R M C p
  have hprod := DirectLimitProduct.productLimitEquiv_of
    (fun i => F.obj i) (fun i => G.obj i) F.transition G.transition s
    (show F.obj s × G.obj s from a)
  have H := congrArg ((leftColimitEquiv R M C p).prodCongr (rightColimitEquiv R M C p)) hprod
  exact H.trans (Prod.ext (leftColimitEquiv_of R M C p s a.1)
    (rightColimitEquiv_of R M C p s a.2))

end P202.CompactSupportMV


namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris
open P202Specs.CapProducts P202Specs.CupProduct

/-- Finite-chain cap comparison for the normalized ordinary connecting map.
All cap chains and the primitive on the right live on the actual intersection. -/
lemma cap_connecting_at_chains (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] (C : Cover M)
    (δ : P202Specs.MayerVietoris.Connecting.{u,v,0} (ordinaryChains R))
    (hδ : P202Specs.MayerVietoris.BoundaryFormula (ordinaryChains R) δ)
    (P Q : Set M) (p : ℕ) (j k : ℤ) (hk : j-(p : ℤ)=k+1)
    (a aP aQ : Cochain R (TopCat.of M) p)
    (hsplit : a = aP+aQ) (ha : delta R (TopCat.of M) p a = 0)
    (hP : aP ∈ vanishingCochains R R ⟨TopCat.of M,P⟩ p)
    (hQ : aQ ∈ vanishingCochains R R ⟨TopCat.of M,Q⟩ p)
    (cU cV : (ordinaryComplex R R (TopCat.of M)).X j)
    (cW : (ordinaryComplex R R (TopCat.of C.intersection)).X j)
    (hcU : cU ∈ ordinarySubspaceRange R (TopCat.of M) (C.left ∩ Q) j)
    (hcV : cV ∈ ordinarySubspaceRange R (TopCat.of M) C.right j)
    (hdUW : (ordinaryComplex R R (TopCat.of M)).d j (j-1)
      (cU+(show ordinaryComplex R R (TopCat.of C.intersection) ⟶ ordinaryComplex R R (TopCat.of M)
        from inclusion (ordinaryFunctor R R) ⟨TopCat.of M,C.intersection⟩).f j cW) ∈
      ordinarySubspaceRange R (TopCat.of M) P (j-1))
    (z : (ordinaryComplex R R (TopCat.of M)).cycles (k+1))
    (hz : (ordinaryComplex R R (TopCat.of M)).iCycles (k+1) z =
      castOrdinary R hk (cap R (TopCat.of M) p j a
        (cU+(show ordinaryComplex R R (TopCat.of C.intersection) ⟶ ordinaryComplex R R (TopCat.of M)
          from inclusion (ordinaryFunctor R R) ⟨TopCat.of M,C.intersection⟩).f j cW+cV)))
    (w : (ordinaryComplex R R (TopCat.of C.intersection)).cycles k)
    (hw : (ordinaryComplex R R (TopCat.of C.intersection)).iCycles k w =
      castOrdinary R (by push_cast; omega : j-((p+1:ℕ):ℤ)=k)
        (cap R (TopCat.of C.intersection) (p+1) j
          (delta R (TopCat.of C.intersection) p
            (pullback R (Pair.inclusion ⟨TopCat.of M,C.intersection⟩) p aP)) cW)) :
    δ C.ordinary k ((ordinaryComplex R R (TopCat.of M)).homologyπ (k+1) z) =
      (-1 : ℤ)^(p+1) •
        (ordinaryComplex R R (TopCat.of C.intersection)).homologyπ k w := by
  let X := TopCat.of M
  let W := TopCat.of C.intersection
  let iW : ordinaryComplex R R W ⟶ ordinaryComplex R R X :=
    inclusion (ordinaryFunctor R R) ⟨X,C.intersection⟩
  let aW := pullback R (Pair.inclusion ⟨X,C.intersection⟩) p aP
  let F := ordinaryChains R
  let S := P202Specs.MayerVietoris.middle F C.ordinary
  let g : S ⟶ ordinaryComplex R R X :=
    (biprod.fst : S ⟶ F.obj C.ordinary.leftPair) ≫ F.map C.ordinary.leftInclusion
  have hcUL : cU ∈ ordinarySubspaceRange R X C.left j :=
    ordinarySubspaceRange_mono R X Set.inter_subset_left _ hcU
  have hcUQ : cU ∈ ordinarySubspaceRange R X Q j :=
    ordinarySubspaceRange_mono R X Set.inter_subset_right _ hcU
  have hcWR : iW.f j cW ∈ ordinarySubspaceRange R X C.right j :=
    ordinarySubspaceRange_mono R X Set.inter_subset_right _ ⟨cW,rfl⟩
  have hcapL : castOrdinary R hk (cap R X p j a cU) ∈
      ordinarySubspaceRange R X C.left (k+1) := by
    apply ordinarySubspaceRange_cast R X C.left hk
    exact P202.CapProducts.cap_preserves_subspace R ⟨X,C.left⟩ p j a cU hcUL
  have hcapR : castOrdinary R hk (cap R X p j a (iW.f j cW+cV)) ∈
      ordinarySubspaceRange R X C.right (k+1) := by
    apply ordinarySubspaceRange_cast R X C.right hk
    exact P202.CapProducts.cap_preserves_subspace R ⟨X,C.right⟩ p j a _
      ((ordinarySubspaceRange R X C.right j).add_mem hcWR hcV)
  obtain ⟨l,hl⟩ := hcapL
  obtain ⟨r,hr⟩ := hcapR
  change (F.obj C.ordinary.leftPair).X (k+1) at l
  change (F.obj C.ordinary.rightPair).X (k+1) at r
  change (F.map C.ordinary.leftInclusion).f (k+1) l = castOrdinary R hk (cap R X p j a cU) at hl
  change (F.map C.ordinary.rightInclusion).f (k+1) r = castOrdinary R hk (cap R X p j a (iW.f j cW+cV)) at hr
  let cs : S.X (k+1) :=
    (biprod.inl : F.obj C.ordinary.leftPair ⟶ S).f (k+1) l +
    (biprod.inr : F.obj C.ordinary.rightPair ⟶ S).f (k+1) r
  have hsum : (P202Specs.MayerVietoris.chainSum F C.ordinary).f (k+1) cs =
      (ordinaryComplex R R X).iCycles (k+1) z := by
    have HL := congrArg (fun f => f l) (biprod_inl_desc_f
      (F.map C.ordinary.leftInclusion) (F.map C.ordinary.rightInclusion) (k+1))
    have HR := congrArg (fun f => f r) (biprod_inr_desc_f
      (F.map C.ordinary.leftInclusion) (F.map C.ordinary.rightInclusion) (k+1))
    simp only [ModuleCat.comp_apply] at HL HR
    dsimp only [cs]
    rw [map_add]
    change (biprod.desc (F.map C.ordinary.leftInclusion) (F.map C.ordinary.rightInclusion)).f (k+1)
      ((biprod.inl : F.obj C.ordinary.leftPair ⟶ S).f (k+1) l) +
      (biprod.desc (F.map C.ordinary.leftInclusion) (F.map C.ordinary.rightInclusion)).f (k+1)
        ((biprod.inr : F.obj C.ordinary.rightPair ⟶ S).f (k+1) r) = _
    erw [HL, HR, hl, hr]
    change (castOrdinary R hk (cap R X p j a cU) +
      castOrdinary R hk (cap R X p j a (iW.f j cW+cV)) :
        (ordinaryComplex R R X).X (k+1)) = _
    rw [← map_add, ← map_add]
    simpa only [add_assoc] using hz.symm
  have hfst : (biprod.fst : S ⟶ F.obj C.ordinary.leftPair).f (k+1) cs = l := by
    dsimp only [cs]
    rw [map_add, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      biprod_inl_fst_f, biprod_inr_fst_f]
    simp
  have hg : g.f (k+1) cs = castOrdinary R hk (cap R X p j a cU) := by
    change (F.map C.ordinary.leftInclusion).f (k+1)
      ((biprod.fst : S ⟶ F.obj C.ordinary.leftPair).f (k+1) cs) = _
    rw [hfst, hl]
  let b : (ordinaryComplex R R W).X (k+1) :=
    castOrdinary R hk (-(cap R W p j aW cW))
  have hprim : (-1 : ℤ)^(p+1) •
      castOrdinary R (by omega : (j-1)-(p : ℤ)=k)
        (cap R W p (j-1) aW ((ordinaryComplex R R W).d j (j-1) cW)) =
      (-1 : ℤ)^(p+1) • (ordinaryComplex R R W).iCycles k w +
        (ordinaryComplex R R W).d (k+1) k b := by
    have Hb := P202.CapProducts.cap_boundary_degrees R W p j (k+1) k hk (by omega) aW cW
    dsimp only [b]
    rw [map_neg, map_neg]
    erw [Hb]
    rw [hw, pow_succ]
    simp only [mul_neg, mul_one, neg_smul, smul_sub]
    abel
  have hboundary : (ordinaryComplex R R X).d (k+1) k
      (castOrdinary R hk (cap R X p j a cU)) =
      (-1 : ℤ)^(p+1) • castOrdinary R (by omega : (j-1)-(p : ℤ)=k)
        (cap R X p (j-1) aP ((ordinaryComplex R R X).d j (j-1) (iW.f j cW))) := by
    have H := congrArg (castOrdinary R (by omega : j-(p : ℤ)-1=k))
      (cap_connecting_boundary R X P Q p j a aP aQ hsplit ha hP hQ cU (iW.f j cW) hcUQ hdUW)
    rw [P202.CapProducts.castOrdinary_d R hk (by omega)] at H
    simpa only [map_zsmul, P202.CapProducts.castOrdinary_comp] using H
  have hnatural : cap R X p (j-1) aP ((ordinaryComplex R R X).d j (j-1) (iW.f j cW)) =
      iW.f ((j-1)-(p : ℤ))
        (cap R W p (j-1) aW ((ordinaryComplex R R W).d j (j-1) cW)) := by
    have Hi := congrArg (fun f => f cW) (iW.comm j (j-1))
    simp only [ModuleCat.comp_apply] at Hi
    rw [Hi]
    exact (P202.CapProducts.ordinaryNatural R (Pair.inclusion ⟨X,C.intersection⟩)
      p (j-1) aP _).symm
  have hleft : (ordinaryComplex R R X).d (k+1) k (g.f (k+1) cs) =
      iW.f k ((-1 : ℤ)^(p+1) • (ordinaryComplex R R W).iCycles k w +
        (ordinaryComplex R R W).d (k+1) k b) := by
    rw [hg, hboundary, hnatural]
    erw [P202.CapProducts.castOrdinary_map R (Pair.inclusion ⟨X,C.intersection⟩)]
    change (-1 : ℤ)^(p+1) • iW.f k
      (castOrdinary R (by omega : (j-1)-(p : ℤ)=k)
        (cap R W p (j-1) aW ((ordinaryComplex R R W).d j (j-1) cW))) = _
    rw [← map_zsmul]
    exact congrArg (iW.f k) hprim
  exact ordinary_connecting_boundary_homology R M C δ hδ k cs z hsum
    ((-1 : ℤ)^(p+1)) w b hleft

end P202.CompactSupportMV


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris
open P202Specs.CapProducts P202Specs.CupProduct
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

lemma intersection_connecting_cochain_value (C : Cover M)
    (K : Support C.left) (L : Support C.right) (p : ℕ)
    (aP : (supportedCochains R M (ambientSupport M C.left K)).X (p : ℤ))
    (b : (supportedCochains R M
      (ambientSupport M C.left K ⊓ ambientSupport M C.right L)).cycles ((p : ℤ)+1))
    (hb : (cochainInclusion R M
        (ambientSupport M C.left K ⊓ ambientSupport M C.right L)).f ((p : ℤ)+1)
          ((supportedCochains R M
            (ambientSupport M C.left K ⊓ ambientSupport M C.right L)).iCycles ((p : ℤ)+1) b) =
      (ordinaryCochains R R (TopCat.of M)).d (p : ℤ) ((p : ℤ)+1)
        ((cochainInclusion R M (ambientSupport M C.left K)).f (p : ℤ) aP)) :
    P202.CapProducts.relativeValue R
      (supportedPair C.intersection (intersectionIn M C.left C.right (K,L))) (p+1)
      ((supportedCochains R C.intersection (intersectionIn M C.left C.right (K,L))).iCycles
        ((p+1 : ℕ) : ℤ) (cyclesMap (intersectionCochainRestriction R M C K L) ((p : ℤ)+1) b)) =
    delta R (TopCat.of C.intersection) p
      (pullback R (Pair.inclusion ⟨TopCat.of M,C.intersection⟩) p
        (P202.CapProducts.relativeValue R (supportedPair M (ambientSupport M C.left K)) p aP)) := by
  let W := TopCat.of C.intersection
  let f := intersectionCochainRestriction R M C K L
  let g : ordinaryCochains R R (TopCat.of M) ⟶ ordinaryCochains R R W :=
    (ordinaryCochainFunctor R R).map (Pair.inclusion ⟨TopCat.of M,C.intersection⟩).op
  have hi := congrArg (fun t => t b) (cyclesMap_i f ((p : ℤ)+1))
  simp only [ModuleCat.comp_apply] at hi
  have hf := congrArg (fun t => t.f ((p : ℤ)+1)
    ((supportedCochains R M
      (ambientSupport M C.left K ⊓ ambientSupport M C.right L)).iCycles ((p : ℤ)+1) b))
    (intersectionCochainRestriction_absolute R M C K L)
  change (cochainInclusion R C.intersection (intersectionIn M C.left C.right (K,L))).f ((p : ℤ)+1)
      (f.f ((p : ℤ)+1)
        ((supportedCochains R M
          (ambientSupport M C.left K ⊓ ambientSupport M C.right L)).iCycles ((p : ℤ)+1) b)) =
    g.f ((p : ℤ)+1)
      ((cochainInclusion R M
        (ambientSupport M C.left K ⊓ ambientSupport M C.right L)).f ((p : ℤ)+1)
          ((supportedCochains R M
            (ambientSupport M C.left K ⊓ ambientSupport M C.right L)).iCycles ((p : ℤ)+1) b)) at hf
  have hd := congrArg (fun t => t ((cochainInclusion R M (ambientSupport M C.left K)).f (p : ℤ) aP))
    (g.comm (p : ℤ) ((p : ℤ)+1))
  simp only [ModuleCat.comp_apply] at hd
  change ordinaryCochainsEquiv R R W (p+1)
    ((cochainInclusion R C.intersection (intersectionIn M C.left C.right (K,L))).f ((p : ℤ)+1)
      ((supportedCochains R C.intersection (intersectionIn M C.left C.right (K,L))).iCycles ((p : ℤ)+1)
        (cyclesMap f ((p : ℤ)+1) b))) =
      delta R W p (pullback R (Pair.inclusion ⟨TopCat.of M,C.intersection⟩) p
        (ordinaryCochainsEquiv R R (TopCat.of M) p
          ((cochainInclusion R M (ambientSupport M C.left K)).f (p : ℤ) aP)))
  rw [hi, hf, hb, ← hd]
  exact (P202.CupProduct.ordinaryCochainsEquiv_d R W p _).trans
    (congrArg (delta R W p) (P202.CupProduct.ordinaryCochainsEquiv_pullback R
      (Pair.inclusion ⟨TopCat.of M,C.intersection⟩) p _))

end P202.CompactSupportMV


namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation
open P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris
open P202Specs.CapProducts P202Specs.CupProduct P202Specs.CompactOrientation

/-- Signed cap comparison at a genuine union-supported cocycle, with no duality
isomorphism assumptions and no restriction on the complementary degree. -/
lemma cap_connecting_of_support (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    {n : ℕ} {M : Type v} [TopologicalSpace M] [T2Space M]
    (A : Manifold n M) (o : Orientation R A) (C : Cover M)
    (AW : Manifold n C.intersection) (oW : Orientation R AW)
    (hoW : OpenOrientationCompatible R M o.val oW.val)
    (δ : P202Specs.MayerVietoris.Connecting.{u,v,0} (ordinaryChains R))
    (hδ : P202Specs.MayerVietoris.BoundaryFormula (ordinaryChains R) δ)
    (p : ℕ) (K : Support C.left) (L : Support C.right)
    (a : (supportedCochains R M
      (ambientSupport M C.left K ⊔ ambientSupport M C.right L)).cycles (p : ℤ)) :
    δ C.ordinary ((n : ℤ)-(p : ℤ)-1)
      (degreeTransport R (TopCat.of M) ((n : ℤ)-(p : ℤ)) (((n : ℤ)-(p : ℤ)-1)+1)
        (by omega) (d.D n M A o (p : ℤ)
          (ofSupport R M (p : ℤ)
            (ambientSupport M C.left K ⊔ ambientSupport M C.right L)
            ((supportedCochains R M
              (ambientSupport M C.left K ⊔ ambientSupport M C.right L)).homologyπ (p : ℤ) a)))) =
      (-1 : ℤ)^(p+1) •
        degreeTransport R (TopCat.of C.intersection)
          ((n : ℤ)-((p : ℤ)+1)) ((n : ℤ)-(p : ℤ)-1) (by omega)
          (d.D n C.intersection AW oW ((p : ℤ)+1)
            (compactConnecting R M C (p : ℤ)
              (ofSupport R M (p : ℤ)
                (ambientSupport M C.left K ⊔ ambientSupport M C.right L)
                ((supportedCochains R M
                  (ambientSupport M C.left K ⊔ ambientSupport M C.right L)).homologyπ (p : ℤ) a)))) := by
  let X := TopCat.of M
  let W := TopCat.of C.intersection
  let K₀ := ambientSupport M C.left K
  let L₀ := ambientSupport M C.right L
  let J := intersectionIn M C.left C.right (K,L)
  let q : ℤ := (n : ℤ)-(p : ℤ)-1
  have hk : (n : ℤ)-(p : ℤ)=q+1 := by dsimp [q]; omega
  have hvk : (n : ℤ)-((p+1:ℕ):ℤ)=q := by dsimp [q]; push_cast; omega
  let iW : ordinaryComplex R R W ⟶ ordinaryComplex R R X :=
    inclusion (ordinaryFunctor R R) ⟨X,C.intersection⟩
  obtain ⟨aP,aQ,b,hsplit,hdb,hb⟩ := supportCycleSplitting R M K₀ L₀ (p : ℤ) a
  let bW := cyclesMap (intersectionCochainRestriction R M C K L) ((p : ℤ)+1) b
  obtain ⟨cU,cV,cW,z,zW,hproj,hclass,hU,hV,hbound,hprojW,hclassW⟩ :=
    fundamental_cover_split R A o C AW oW hoW K L
  have hvalues : HasLocalValues R o.val (K₀ ⊔ L₀)
      ((ordinary R R (supportedPair M (K₀ ⊔ L₀))).homologyπ (n : ℤ) z) := by
    rw [hclass]
    exact P202.CompactSupport.fundamentalClass_values R M A o (K₀ ⊔ L₀)
  have hvaluesW : HasLocalValues R oW.val J
      ((ordinary R R (supportedPair C.intersection J)).homologyπ (n : ℤ) zW) := by
    rw [hclassW]
    exact P202.CompactSupport.fundamentalClass_values R C.intersection AW oW J
  obtain ⟨u,hu,hDu⟩ := d.represents n M A o p (K₀ ⊔ L₀) a z
    (cU+iW.f (n : ℤ) cW+cV) hproj hvalues
  obtain ⟨v,hv,hDv⟩ := d.represents n C.intersection AW oW (p+1) J bW zW cW hprojW hvaluesW
  let a₀ : Cochain R X p := P202.CapProducts.relativeValue R (supportedPair M (K₀ ⊔ L₀)) p
    ((supportedCochains R M (K₀ ⊔ L₀)).iCycles (p : ℤ) a)
  let aP₀ : Cochain R X p := P202.CapProducts.relativeValue R (supportedPair M K₀) p aP
  let aQ₀ : Cochain R X p := P202.CapProducts.relativeValue R (supportedPair M L₀) p aQ
  have hsplit₀ : a₀ = aP₀+aQ₀ := by
    change ordinaryCochainsEquiv R R X p
      ((cochainInclusion R M (K₀ ⊔ L₀)).f (p : ℤ)
        ((supportedCochains R M (K₀ ⊔ L₀)).iCycles (p : ℤ) a)) =
      ordinaryCochainsEquiv R R X p ((cochainInclusion R M K₀).f (p : ℤ) aP) +
        ordinaryCochainsEquiv R R X p ((cochainInclusion R M L₀).f (p : ℤ) aQ)
    have H := congrArg (ordinaryCochainsEquiv R R X p) hsplit
    simpa only [map_add] using H.symm
  have ha₀ : delta R X p a₀ = 0 := by
    change delta R X p (P202.CapProducts.relativeValue R (supportedPair M (K₀ ⊔ L₀)) p
      ((supportedCochains R M (K₀ ⊔ L₀)).iCycles (p : ℤ) a)) = 0
    have H := P202.CapProducts.relativeValue_d R (supportedPair M (K₀ ⊔ L₀)) p
      ((supportedCochains R M (K₀ ⊔ L₀)).iCycles (p : ℤ) a)
    erw [P202.CapProducts.cochain_cycle_closed _ p a, map_zero] at H
    exact H.symm
  have hbW : P202.CapProducts.relativeValue R (supportedPair C.intersection J) (p+1)
      ((supportedCochains R C.intersection J).iCycles ((p+1:ℕ):ℤ) bW) =
      delta R W p (pullback R (Pair.inclusion ⟨X,C.intersection⟩) p aP₀) := by
    exact intersection_connecting_cochain_value R M C K L p aP b hdb
  let u' := castChainCycles (ordinaryComplex R R X) hk u
  let v' := castChainCycles (ordinaryComplex R R W) hvk v
  have hu' : (ordinaryComplex R R X).iCycles (q+1) u' =
      castOrdinary R hk (cap R X p (n : ℤ) a₀ (cU+iW.f (n : ℤ) cW+cV)) := by
    rw [castChainCycles_i, hu]
    rfl
  have hv' : (ordinaryComplex R R W).iCycles q v' =
      castOrdinary R hvk (cap R W (p+1) (n : ℤ)
        (delta R W p (pullback R (Pair.inclusion ⟨X,C.intersection⟩) p aP₀)) cW) := by
    rw [castChainCycles_i, hv]
    exact congrArg (fun t => castOrdinary R hvk (cap R W (p+1) (n : ℤ) t cW)) hbW
  have H := cap_connecting_at_chains R M C δ hδ (K₀ : Set M)ᶜ (L₀ : Set M)ᶜ p
    (n : ℤ) q hk a₀ aP₀ aQ₀ hsplit₀ ha₀
    (P202.CapProducts.relativeValue_vanishing R (supportedPair M K₀) p aP)
    (P202.CapProducts.relativeValue_vanishing R (supportedPair M L₀) p aQ)
    cU cV cW hU (ordinarySubspaceRange_mono R X Set.inter_subset_left _ hV)
    hbound u' hu' v' hv'
  rw [castChainCycles_homologyπ, castChainCycles_homologyπ, ← hDu, ← hDv] at H
  have hconn := compactConnecting_ofCycle R M C K L (p : ℤ)
    ((supportedCochains R M (K₀ ⊔ L₀)).homologyπ (p : ℤ) a) b hb
  rw [hconn]
  exact H

end P202.CompactSupportMV

/-! Global exactness, the all-degree cap comparison, and the complete bound gluing theorem. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Classical
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CohomologyPairs
open P202Specs.CompactSupportMayerVietoris
namespace ModuleSystem
variable {R : Type*} [CommRing R] {ι : Type*} [Preorder ι]
@[simp] lemma Map.limit_of {F G : ModuleSystem R ι} (f : F.Map G) (i : ι) (a : F.obj i) :
    f.limit (F.of i a) = G.of i (f.component i a) :=
  Module.DirectLimit.map_apply_of _ _ _
lemma hom_ext (F : ModuleSystem R ι) {V : Type*} [AddCommGroup V] [Module R V]
    {f g : F.Limit →ₗ[R] V} (h : ∀ i, f.comp (F.of i) = g.comp (F.of i)) : f = g :=
  Module.DirectLimit.hom_ext h
end ModuleSystem
variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

def middleColimitEquiv (C : Cover M) (p : ℤ) :
    (middleProductSystem R M C p).Limit ≃ₗ[R] CompactMiddle R M C p :=
  (middleProductColimitEquiv R M C p).trans
    (ModuleCat.biprodIsoProd (ModuleCat.of R (CompactCohomology R C.left p))
      (ModuleCat.of R (CompactCohomology R C.right p))).symm.toLinearEquiv

@[simp] lemma middleColimitEquiv_of (C : Cover M) (p : ℤ)
    (s : SupportPair M C.left C.right) (a : (middleProductSystem R M C p).obj s) :
    middleColimitEquiv R M C p ((middleProductSystem R M C p).of s a) =
      (biprod.inl : ModuleCat.of R (CompactCohomology R C.left p) ⟶ CompactMiddle R M C p)
        (ofSupport R C.left p s.1 (openPullback R M C.left s.1 p a.1)) +
      (biprod.inr : ModuleCat.of R (CompactCohomology R C.right p) ⟶ CompactMiddle R M C p)
        (ofSupport R C.right p s.2 (openPullback R M C.right s.2 p a.2)) := by
  change (ModuleCat.biprodIsoProd (ModuleCat.of R (CompactCohomology R C.left p))
      (ModuleCat.of R (CompactCohomology R C.right p))).inv
        (middleProductColimitEquiv R M C p _) = _
  rw [middleProductColimitEquiv_of, biprodIsoProd_inv_apply]

lemma first_apply (C : Cover M)
    (eL : IntersectionExtension R M C C.left) (eR : IntersectionExtension R M C C.right)
    (p : ℤ) (a : CompactCohomology R C.intersection p) :
    first R M C eL eR p a =
      (biprod.inl : ModuleCat.of R (CompactCohomology R C.left p) ⟶ CompactMiddle R M C p) (eL p a) +
      (biprod.inr : ModuleCat.of R (CompactCohomology R C.right p) ⟶ CompactMiddle R M C p) (-(eR p a)) := by
  apply P202.MayerVietoris.biprod_element_ext
  · change (biprod.fst : CompactMiddle R M C p ⟶ ModuleCat.of R (CompactCohomology R C.left p))
      ((biprod.lift (ModuleCat.ofHom (eL p)) (-ModuleCat.ofHom (eR p))) a) = _
    erw [← ModuleCat.comp_apply, biprod.lift_fst, map_add,
      ← ModuleCat.comp_apply, biprod.inl_fst, ← ModuleCat.comp_apply, biprod.inr_fst]
    simp
  · change (biprod.snd : CompactMiddle R M C p ⟶ ModuleCat.of R (CompactCohomology R C.right p))
      ((biprod.lift (ModuleCat.ofHom (eL p)) (-ModuleCat.ofHom (eR p))) a) = _
    erw [← ModuleCat.comp_apply, biprod.lift_snd, map_add,
      ← ModuleCat.comp_apply, biprod.inl_snd, ← ModuleCat.comp_apply, biprod.inr_snd]
    simp

lemma first_colimit_square (C : Cover M) (p : ℤ) :
    (first R M C (intersectionExtendLeft R M C) (intersectionExtendRight R M C) p).hom.comp
      (intersectionColimitEquiv R M C p).toLinearMap =
    (middleColimitEquiv R M C p).toLinearMap.comp (firstSystemMap R M C p).limit := by
  apply ModuleSystem.hom_ext (intersectionSystem R M C p)
  intro s
  apply LinearMap.ext
  intro a
  change first R M C (intersectionExtendLeft R M C) (intersectionExtendRight R M C) p
      (intersectionColimitEquiv R M C p ((intersectionSystem R M C p).of s a)) =
    middleColimitEquiv R M C p ((firstSystemMap R M C p).limit ((intersectionSystem R M C p).of s a))
  rw [ModuleSystem.Map.limit_of, intersectionColimitEquiv_of, middleColimitEquiv_of, first_apply]
  have hL := intersectionExtendLeft_atSupports R M C p s a
  have hR := intersectionExtendRight_atSupports R M C p s a
  change intersectionExtendLeft R M C p
    (ofSupport R C.intersection p _ (intersectionStageEquiv R M C p s a)) = _ at hL
  change intersectionExtendRight R M C p
    (ofSupport R C.intersection p _ (intersectionStageEquiv R M C p s a)) = _ at hR
  rw [hL,hR]
  change (biprod.inl : ModuleCat.of R (CompactCohomology R C.left p) ⟶ CompactMiddle R M C p)
      (ofSupport R C.left p s.1 (openPullback R M C.left s.1 p
        (transition R M p _ _ inf_le_left a))) +
    (biprod.inr : ModuleCat.of R (CompactCohomology R C.right p) ⟶ CompactMiddle R M C p)
      (-(ofSupport R C.right p s.2 (openPullback R M C.right s.2 p
        (transition R M p _ _ inf_le_right a)))) =
    (biprod.inl : ModuleCat.of R (CompactCohomology R C.left p) ⟶ CompactMiddle R M C p)
      (ofSupport R C.left p s.1 (openPullback R M C.left s.1 p
        (transition R M p _ _ inf_le_left a))) +
    (biprod.inr : ModuleCat.of R (CompactCohomology R C.right p) ⟶ CompactMiddle R M C p)
      (ofSupport R C.right p s.2 (openPullback R M C.right s.2 p
        (-(transition R M p _ _ inf_le_right a))))
  rw [map_neg, map_neg, map_neg, map_neg]

lemma sum_colimit_square (d : DualityData.{u,v} R) (C : Cover M) (p : ℤ) :
    (sum R M d C p).hom.comp (middleColimitEquiv R M C p).toLinearMap =
      (unionColimitEquiv R M C p).toLinearMap.comp (sumSystemMap R M C p).limit := by
  apply ModuleSystem.hom_ext (middleProductSystem R M C p)
  intro s
  apply LinearMap.ext
  intro a
  change sum R M d C p (middleColimitEquiv R M C p ((middleProductSystem R M C p).of s a)) =
    unionColimitEquiv R M C p ((sumSystemMap R M C p).limit ((middleProductSystem R M C p).of s a))
  rw [ModuleSystem.Map.limit_of, middleColimitEquiv_of, unionColimitEquiv_of]
  exact compact_sum_ofSupports R M d C p s.1 s.2 a.1 a.2

lemma connecting_colimit_square (C : Cover M) (p : ℤ) :
    (compactConnecting R M C p).comp (unionColimitEquiv R M C p).toLinearMap =
      (intersectionColimitEquiv R M C (p+1)).toLinearMap.comp (connectingSystemMap R M C p).limit := by
  apply ModuleSystem.hom_ext (unionSystem R M C p)
  intro s
  apply LinearMap.ext
  intro a
  change compactConnecting R M C p (unionColimitEquiv R M C p ((unionSystem R M C p).of s a)) =
    intersectionColimitEquiv R M C (p+1) ((connectingSystemMap R M C p).limit ((unionSystem R M C p).of s a))
  rw [ModuleSystem.Map.limit_of, unionColimitEquiv_of, intersectionColimitEquiv_of]
  exact compactConnecting_ofSupport R M C p s.1 s.2 a

end P202.CompactSupportMV

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Classical
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
namespace P202.CompactSupportMV
open P202Specs.CompactSupport P202Specs.CohomologyPairs
open P202Specs.CompactSupportMayerVietoris

lemma module_exact₂_of_function {R : Type u} [CommRing R] {X Y Z : ModuleCat.{v} R}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Function.Exact f.hom g.hom) :
    (ComposableArrows.mk₂ f g).Exact := by
  have w : f ≫ g = 0 := ModuleCat.hom_ext h.linearMap_comp_eq_zero
  apply ComposableArrows.exact₂_mk _ w
  exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr h

variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] [T2Space M]

lemma compact_three_exact (d : DualityData.{u,v} R) (C : Cover M) (p : ℤ) :
    Function.Exact
      (first R M C (intersectionExtendLeft R M C) (intersectionExtendRight R M C) p).hom
      (sum R M d C p).hom ∧
    Function.Exact (sum R M d C p).hom (compactConnecting R M C p) ∧
    Function.Exact (compactConnecting R M C p)
      (first R M C (intersectionExtendLeft R M C) (intersectionExtendRight R M C) (p+1)).hom := by
  have h₁ : Function.Exact (firstSystemMap R M C p).limit (sumSystemMap R M C p).limit := by
    apply filteredExactness R (SupportPair M C.left C.right)
      (intersectionSystem R M C p) (middleProductSystem R M C p) (unionSystem R M C p)
      (firstSystemMap R M C p) (sumSystemMap R M C p)
    intro s
    exact supportProduct_exact_first_sum R M (ambientSupport M C.left s.1)
      (ambientSupport M C.right s.2) p
  have h₂ : Function.Exact (sumSystemMap R M C p).limit (connectingSystemMap R M C p).limit := by
    apply filteredExactness R (SupportPair M C.left C.right)
      (middleProductSystem R M C p) (unionSystem R M C p) (intersectionSystem R M C (p+1))
      (sumSystemMap R M C p) (connectingSystemMap R M C p)
    intro s
    exact supportProduct_exact_sum_connecting R M (ambientSupport M C.left s.1)
      (ambientSupport M C.right s.2) p
  have h₃ : Function.Exact (connectingSystemMap R M C p).limit (firstSystemMap R M C (p+1)).limit := by
    apply filteredExactness R (SupportPair M C.left C.right)
      (unionSystem R M C p) (intersectionSystem R M C (p+1)) (middleProductSystem R M C (p+1))
      (connectingSystemMap R M C p) (firstSystemMap R M C (p+1))
    intro s
    exact supportProduct_exact_connecting_first R M (ambientSupport M C.left s.1)
      (ambientSupport M C.right s.2) p
  refine ⟨?_, ?_, ?_⟩
  · exact Function.Exact.of_ladder_linearEquiv_of_exact
      (e₁ := intersectionColimitEquiv R M C p) (e₂ := middleColimitEquiv R M C p)
      (e₃ := unionColimitEquiv R M C p)
      (first_colimit_square R M C p) (sum_colimit_square R M d C p) h₁
  · exact Function.Exact.of_ladder_linearEquiv_of_exact
      (e₁ := middleColimitEquiv R M C p) (e₂ := unionColimitEquiv R M C p)
      (e₃ := intersectionColimitEquiv R M C (p+1))
      (sum_colimit_square R M d C p) (connecting_colimit_square R M C p) h₂
  · exact Function.Exact.of_ladder_linearEquiv_of_exact
      (e₁ := unionColimitEquiv R M C p) (e₂ := intersectionColimitEquiv R M C (p+1))
      (e₃ := middleColimitEquiv R M C (p+1))
      (connecting_colimit_square R M C p) (first_colimit_square R M C (p+1)) h₃

/-- The all-degree compact-support Mayer--Vietoris sequence is exact for the
actual intersection extensions, supplied ambient extensions, and the constructed
positive connecting homomorphism. -/
theorem compact_exact (d : DualityData.{u,v} R) (C : Cover M) :
    Exact R M d C (intersectionExtendLeft R M C) (intersectionExtendRight R M C)
      (compactConnecting R M C) := by
  constructor
  · intro p
    obtain ⟨h₁,h₂,h₃⟩ := compact_three_exact R M d C p
    have h₄ := (compact_three_exact R M d C (p+1)).1
    exact ComposableArrows.exact_of_δ₀ (module_exact₂_of_function _ _ h₁)
      (ComposableArrows.exact_of_δ₀ (module_exact₂_of_function _ _ h₂)
        (ComposableArrows.exact_of_δ₀ (module_exact₂_of_function _ _ h₃)
          (module_exact₂_of_function _ _ h₄)))
  · intro p
    exact module_exact₂_of_function _ _ (compact_three_exact R M d C p).1

end P202.CompactSupportMV


namespace P202.CompactSupportMV
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactSupport P202Specs.CompactSupportMayerVietoris

/-- The signed connecting square for compact-support duality in every integer
degree, on the original homology groups and the same duality maps. -/
theorem cap_connecting (R : Type u) [CommRing R] (d : DualityData.{u,v} R)
    {n : ℕ} {M : Type v} [TopologicalSpace M] [T2Space M]
    (A : Manifold n M) (o : Orientation R A) (C : Cover M)
    (AW : Manifold n C.intersection) (oW : Orientation R AW)
    (hoW : OpenOrientationCompatible R M o.val oW.val)
    (δ : P202Specs.MayerVietoris.Connecting.{u,v,0} (ordinaryChains R))
    (hδ : P202Specs.MayerVietoris.BoundaryFormula (ordinaryChains R) δ)
    (p : ℤ) (a : CompactCohomology R M p) :
    δ C.ordinary ((n : ℤ)-p-1)
      (degreeTransport R (TopCat.of M) ((n : ℤ)-p) (((n : ℤ)-p-1)+1)
        (by omega) (d.D n M A o p a)) =
      ((p+1).negOnePow : ℤ) •
        degreeTransport R (TopCat.of C.intersection) ((n : ℤ)-(p+1)) ((n : ℤ)-p-1)
          (by omega) (d.D n C.intersection AW oW (p+1) (compactConnecting R M C p a)) := by
  by_cases hp : p < 0
  · exact P202.CompactSupportMayerVietoris.cap_connecting_of_negative R d A o C
      (compactConnecting R M C) δ AW oW p hp a
  · obtain ⟨p,rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ p)
    obtain ⟨K,L,z,rfl⟩ := exists_union_cocycle R M C (p : ℤ) a
    have H := cap_connecting_of_support R d A o C AW oW hoW δ hδ p K L z
    have hsign : (((p : ℤ)+1).negOnePow : ℤ) = (-1 : ℤ)^(p+1) := by
      have he : (p : ℤ)+1 = ((p+1 : ℕ) : ℤ) := by omega
      rw [he, Int.coe_negOnePow_natCast]
    rw [hsign]
    exact H

end P202.CompactSupportMV

namespace P202.CompactSupportMayerVietoris
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.LocalOrientation P202Specs.CompactSupport
open P202Specs.CompactSupportMayerVietoris P202.CompactSupportMV

/-- Compact-support Mayer–Vietoris and its full signed comparison with ordinary
finite-chain homology, for the original duality data and every open cover. -/
theorem gluing : P202Specs.CompactSupportMayerVietoris.Expected.gluing.{u,v} := by
  intro R _ d n M _ A o
  letI : T2Space M := A.hausdorff
  intro C
  let O := orientedCoverData R M A o C
  obtain ⟨δ, hExact, hNatural, hBoundary⟩ := ordinary_sequence R
  refine ⟨{
    union_cofinal := union_cofinal M C
    intersection_cofinal := intersection_cofinal M C
    extendLeft := intersectionExtendLeft R M C
    extendRight := intersectionExtendRight R M C
    left_represents := intersectionExtendLeft_represents R M C
    right_represents := intersectionExtendRight_represents R M C
    connecting := compactConnecting R M C
    exact := compact_exact R M d C
    connecting_formula := compactConnecting_formula R M C
    homologyConnecting := δ
    homology_exact := hExact
    homology_natural := hNatural
    homology_boundary := hBoundary
    leftManifold := O.leftManifold
    rightManifold := O.rightManifold
    intersectionManifold := O.intersectionManifold
    leftOrientation := O.leftOrientation
    rightOrientation := O.rightOrientation
    intersectionOrientation := O.intersectionOrientation
    left_compatible := O.left_compatible
    right_compatible := O.right_compatible
    intersection_compatible := O.intersection_compatible
    cap_first := fun p => P202.CompactSupportMV.cap_first R M d n C
      O.leftManifold O.rightManifold O.intersectionManifold
      O.leftOrientation O.rightOrientation O.intersectionOrientation o.val
      O.left_compatible O.right_compatible O.intersection_compatible p
    cap_sum := fun p => cap_sum R M d n A o C O.leftManifold O.rightManifold
      O.leftOrientation O.rightOrientation O.left_compatible O.right_compatible p
    cap_connecting := fun p a => P202.CompactSupportMV.cap_connecting R d A o C
      O.intersectionManifold O.intersectionOrientation O.intersection_compatible
      δ hBoundary p a }⟩

end P202.CompactSupportMayerVietoris
