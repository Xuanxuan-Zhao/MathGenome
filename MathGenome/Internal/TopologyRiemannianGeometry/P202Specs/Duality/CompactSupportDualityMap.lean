import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Cohomology.Pairs
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CompactOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CapProducts
import Mathlib.Algebra.Colimit.Module
import Mathlib.Topology.Sets.Compacts

/-!
Compact supports and the duality map, paper.tex 2194–2205 and 2220–2229.
The directed system uses all compact subsets, including the empty compact.
The cohomology and homology are the existing ordinary singular theories.
No duality isomorphism is assumed here.
-/
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
universe u v
namespace P202Specs.CompactSupport
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation

variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]

abbrev Support := TopologicalSpace.Compacts M
abbrev supportedCochains (K : Support M) := relativeCochains R R (supportedPair M K)
abbrev supportedCohomology (p : ℤ) (K : Support M) :=
  relativeCohomology R R (supportedPair M K) p

/-- The map of pairs for compact-set inclusion, with its carrier coercion explicit. -/
def supportPairMap {K L : Support M} (h : K ≤ L) :
    supportedPair M L ⟶ supportedPair M K := supportMap (fun _ hx => h hx)

/-- Increasing compact supports, with the contravariant pair map. -/
def cochainTransition {K L : Support M} (h : K ≤ L) :
    supportedCochains R M K ⟶ supportedCochains R M L :=
  (relativeCochainFunctor R R).map (supportPairMap M h).op

def transition (p : ℤ) (K L : Support M) (h : K ≤ L) :
    supportedCohomology R M p K →ₗ[R] supportedCohomology R M p L :=
  ((relativeCohomologyFunctor R R p).map (supportPairMap M h).op).hom

instance supportSystem (p : ℤ) :
    DirectedSystem (fun K => ↥(supportedCohomology R M p K))
      (fun K L h => (transition R M p K L h).toFun) where
  map_self K x := by
    have h : supportPairMap M (le_refl K) = 𝟙 (supportedPair M K) := by
      apply PairMap.ext; rfl
    simp [transition, h]
  map_map K L N hKL hLN x := by
    have h : supportPairMap M (hKL.trans hLN) = supportPairMap M hLN ≫ supportPairMap M hKL := by
      apply PairMap.ext; rfl
    change ((relativeCohomologyFunctor R R p).map (supportPairMap M hLN).op)
      (((relativeCohomologyFunctor R R p).map (supportPairMap M hKL).op) x) =
      ((relativeCohomologyFunctor R R p).map (supportPairMap M (hKL.trans hLN)).op) x
    rw [h, op_comp, Functor.map_comp, ModuleCat.comp_apply]

/-- The actual filtered colimit of relative cohomology groups, in every degree. -/
abbrev CompactCohomology (p : ℤ) :=
  Module.DirectLimit (fun K => ↥(supportedCohomology R M p K)) (transition R M p)

def ofSupport (p : ℤ) (K : Support M) :
    supportedCohomology R M p K →ₗ[R] CompactCohomology R M p :=
  Module.DirectLimit.of R (Support M) (fun K => ↥(supportedCohomology R M p K))
    (transition R M p) K

/-- Universal descent from compatible linear maps on supports. -/
def descend (p : ℤ) {V : Type*} [AddCommGroup V] [Module R V]
    (f : ∀ K : Support M, supportedCohomology R M p K →ₗ[R] V)
    (hf : ∀ K L h a, f L (transition R M p K L h a) = f K a) :
    CompactCohomology R M p →ₗ[R] V :=
  Module.DirectLimit.lift R (Support M) (fun K => ↥(supportedCohomology R M p K))
    (transition R M p) f hf

/-- Embedding of supported cochains into ordinary cochains. -/
abbrev cochainInclusion (K : Support M) :
    supportedCochains R M K ⟶ ordinaryCochains R R (TopCat.of M) :=
  relativeToAbsolute R R (supportedPair M K)

lemma cochainInclusion_transition {K L : Support M} (h : K ≤ L) :
    cochainTransition R M h ≫ cochainInclusion R M L = cochainInclusion R M K := by
  have H := (cochainSequenceMap R R (supportPairMap M h)).comm₁₂
  have HI : (ordinaryCochainFunctor R R).map (𝟙 (TopCat.of M)).op =
      𝟙 ((ordinaryCochains R R (TopCat.of M))) :=
    (ordinaryCochainFunctor R R).map_id (op (TopCat.of M))
  change cochainTransition R M h ≫ cochainInclusion R M L =
    cochainInclusion R M K ≫ (ordinaryCochainFunctor R R).map (𝟙 (TopCat.of M)).op at H
  exact H.trans (by rw [HI, Category.comp_id])

/-- Degreewise union of the relative cochain submodules, inside ordinary cochains.
The existential support condition is closed under addition by taking K ∪ L. -/
def unionCochains (p : ℤ) : Submodule R ((ordinaryCochains R R (TopCat.of M)).X p) where
  carrier := {a | ∃ (K : Support M) (b : (supportedCochains R M K).X p),
    (cochainInclusion R M K).f p b = a}
  zero_mem' := ⟨⊥, 0, map_zero _⟩
  add_mem' := by
    rintro a b ⟨K, x, rfl⟩ ⟨L, y, rfl⟩
    refine ⟨K ⊔ L, (cochainTransition R M le_sup_left).f p x +
      (cochainTransition R M le_sup_right).f p y, ?_⟩
    rw [map_add]
    exact congrArg₂ (· + ·)
      (congrArg (fun f => f.f p x) (cochainInclusion_transition R M (K := K) (L := K ⊔ L) le_sup_left))
      (congrArg (fun f => f.f p y) (cochainInclusion_transition R M (K := L) (L := K ⊔ L) le_sup_right))
  smul_mem' := by
    rintro r a ⟨K, x, rfl⟩
    exact ⟨K, r • x, map_smul _ _ _⟩

lemma unionCochains_d (p q : ℤ) (a : (ordinaryCochains R R (TopCat.of M)).X p)
    (ha : a ∈ unionCochains R M p) :
    (ordinaryCochains R R (TopCat.of M)).d p q a ∈ unionCochains R M q := by
  obtain ⟨K, b, rfl⟩ := ha
  exact ⟨K, (supportedCochains R M K).d p q b,
    congrArg (fun f => f b) ((cochainInclusion R M K).comm p q).symm⟩

/-- The union with its actual restricted singular coboundary. -/
def unionComplex : CochainComplex (ModuleCat.{max u v} R) ℤ where
  X p := ModuleCat.of R (unionCochains R M p)
  d p q := ModuleCat.ofHom
    (((ordinaryCochains R R (TopCat.of M)).d p q).hom.restrict
      (unionCochains_d R M p q))
  shape p q h := by
    apply ModuleCat.hom_ext
    ext a
    change (ordinaryCochains R R (TopCat.of M)).d p q a.val = 0
    rw [(ordinaryCochains R R (TopCat.of M)).shape p q h]
    rfl
  d_comp_d' p q k _ _ := by
    apply ModuleCat.hom_ext
    ext a
    change (ordinaryCochains R R (TopCat.of M)).d q k
      ((ordinaryCochains R R (TopCat.of M)).d p q a.val) = 0
    rw [← ModuleCat.comp_apply, d_comp_d]
    rfl

/-- The canonical map from a relative complex into the union. -/
def intoUnion (K : Support M) : supportedCochains R M K ⟶ unionComplex R M where
  f p := ModuleCat.ofHom
    { toFun := fun a => ⟨(cochainInclusion R M K).f p a, K, a, rfl⟩
      map_add' := by intros; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intros; apply Subtype.ext; exact map_smul _ _ _ }
  comm' p q _ := by
    apply ModuleCat.hom_ext
    ext a
    apply Subtype.ext
    exact congrArg (fun f => f a) ((cochainInclusion R M K).comm p q)

lemma intoUnion_transition {K L : Support M} (h : K ≤ L) :
    cochainTransition R M h ≫ intoUnion R M L = intoUnion R M K := by
  ext p a
  apply Subtype.ext
  exact congrArg (fun f => f.f p a) (cochainInclusion_transition R M h)

/-- The canonical comparison with the cohomology of the actual union complex. -/
def unionComparison (p : ℤ) :
    CompactCohomology R M p →ₗ[R] (unionComplex R M).homology p :=
  descend R M p (fun K => (homologyMap (intoUnion R M K) p).hom)
    (by
      intro K L h a
      change homologyMap (intoUnion R M L) p
        (homologyMap (cochainTransition R M h) p a) = _
      rw [← ModuleCat.comp_apply, ← homologyMap_comp, intoUnion_transition])

/-- Image of a compact of an open subspace, with its actual ambient compactness. -/
def ambientSupport (U : Set M) (K : Support U) : Support M :=
  K.map Subtype.val continuous_subtype_val

lemma ambientSupport_mono (U : Set M) {K L : Support U} (h : K ≤ L) :
    ambientSupport M U K ≤ ambientSupport M U L := Set.image_mono h

/-- The actual inclusion of pairs near a compact in an open subspace. -/
def openPairInclusion (U : Set M) (K : Support U) :
    supportedPair U K ⟶ supportedPair M (ambientSupport M U K) where
  map := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  mapsTo := by
    rintro x hx ⟨y, hy, he⟩
    exact hx (Subtype.val_injective he ▸ hy)

/-- Excision restriction; extension at a compact is its inverse. -/
def openPullback (U : Set M) (K : Support U) (p : ℤ) :
    supportedCohomology R M p (ambientSupport M U K) ⟶
      supportedCohomology R U p K :=
  (relativeCohomologyFunctor R R p).map (openPairInclusion M U K).op

/-- Compatibility with the orientation inherited by an open submanifold,
stated on the original local singular homology groups. -/
def OpenOrientationCompatible {n : ℕ} {U : Set M}
    (oM : LocalChoice R n M) (oU : LocalChoice R n U) : Prop :=
  ∀ x : U, ((relativeHomologyFunctor R R (n : ℤ)).map
    (P202Specs.LocalOrientation.openLocalInclusion U x)) (oU x) = oM x.val

/-- The usual covariant map on ordinary finite-chain homology for an open inclusion. -/
def openHomology (U : Set M) (q : ℤ) :
    homology R R (TopCat.of U) q →ₗ[R] homology R R (TopCat.of M) q :=
  (homologyMap (show ordinaryComplex R R (TopCat.of U) ⟶ ordinaryComplex R R (TopCat.of M) from
    (ordinaryFunctor R R).map (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)) q).hom

/-- Complete data for compact-support duality before proving any isomorphism.
The representative law fixes the front/back cap convention and the actual
fundamental class by its local values. Extension is fixed by excision restriction.
-/
structure DualityData where
  D : ∀ (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A) (p : ℤ),
    CompactCohomology R M p →ₗ[R] homology R R (TopCat.of M) ((n : ℤ)-p)
  extend : ∀ (M : Type v) [TopologicalSpace M] [T2Space M]
    (U : Set M), IsOpen U → ∀ p : ℤ,
      CompactCohomology R U p →ₗ[R] CompactCohomology R M p
  represents : ∀ (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A) (p : ℕ) (K : Support M)
    (a : (supportedCochains R M K).cycles (p : ℤ))
    (z : (ordinary R R (supportedPair M K)).cycles (n : ℤ))
    (c : (ordinaryComplex R R (TopCat.of M)).X (n : ℤ)),
    (projection (ordinaryFunctor R R) (supportedPair M K)).f (n : ℤ) c =
      (ordinary R R (supportedPair M K)).iCycles (n : ℤ) z →
    P202Specs.CompactOrientation.HasLocalValues R o.val K
      ((ordinary R R (supportedPair M K)).homologyπ (n : ℤ) z) →
    ∃ v : (ordinaryComplex R R (TopCat.of M)).cycles ((n : ℤ)-p),
      (ordinaryComplex R R (TopCat.of M)).iCycles ((n : ℤ)-p) v =
        P202Specs.CapProducts.cap R (TopCat.of M) p (n : ℤ)
          (ordinaryCochainsEquiv R R (TopCat.of M) p
            ((cochainInclusion R M K).f (p : ℤ)
              ((supportedCochains R M K).iCycles (p : ℤ) a))) c ∧
      D n M A o (p : ℤ)
        (ofSupport R M (p : ℤ) K ((supportedCochains R M K).homologyπ (p : ℤ) a)) =
        (ordinaryComplex R R (TopCat.of M)).homologyπ ((n : ℤ)-p) v
  extension_represents : ∀ (M : Type v) [TopologicalSpace M] [T2Space M]
    (U : Set M) (hU : IsOpen U) (p : ℤ) (K : Support U)
    (b : supportedCohomology R M p (ambientSupport M U K)),
    extend M U hU p (ofSupport R U p K (openPullback R M U K p b)) =
      ofSupport R M p (ambientSupport M U K) b
  negative : ∀ (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A) (p : ℤ), p < 0 → D n M A o p = 0
  above : ∀ (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A) (p : ℕ), n < p → D n M A o (p : ℤ) = 0
  naturality : ∀ (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (oM : Orientation R A)
    (U : Set M) (hU : IsOpen U) (AU : Manifold n U) (oU : Orientation R AU),
    OpenOrientationCompatible R M oM.val oU.val → ∀ (p : ℤ) (a : CompactCohomology R U p),
    letI : T2Space M := A.hausdorff
    openHomology R M U ((n : ℤ)-p) (D n U AU oU p a) =
      D n M A oM p (extend M U hU p a)

/-- The canonical compact-support module, exposed as a reusable definition. -/
def compactCohomology_type := ∀ (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] (p : ℤ), Type (max u v)
def compactCohomology_value : compactCohomology_type.{u,v} := @CompactCohomology

namespace Expected

def construction : Prop := ∀ (R : Type u) [CommRing R], Nonempty (DualityData.{u,v} R)

def openExcision : Prop := ∀ (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] [T2Space M] (U : Set M), IsOpen U →
  ∀ (K : Support U) (p : ℤ), IsIso (openPullback R M U K p)

def unionEquivalence : Prop := ∀ (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] (p : ℤ),
  Function.Bijective (unionComparison R M p)

def representatives : Prop := ∀ (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] (p : ℤ) (a : CompactCohomology R M p),
  ∃ (K : Support M) (b : supportedCohomology R M p K), ofSupport R M p K b = a

/-- Equal classes from possibly different supports agree on a single larger compact. -/
def equalityWitness : Prop := ∀ (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] (p : ℤ) (K L : Support M)
    (a : supportedCohomology R M p K) (b : supportedCohomology R M p L),
  ofSupport R M p K a = ofSupport R M p L b ↔
    ∃ (N : Support M) (hKN : K ≤ N) (hLN : L ≤ N),
      transition R M p K N hKN a = transition R M p L N hLN b

/-- The zero source in negative cohomological degrees, without a restriction
on the degree of the target homology. -/
def negative : Prop := ∀ (R : Type u) [CommRing R]
    (M : Type v) [TopologicalSpace M] (p : ℤ), p < 0 →
  Subsingleton (CompactCohomology R M p)

end Expected
end P202Specs.CompactSupport
