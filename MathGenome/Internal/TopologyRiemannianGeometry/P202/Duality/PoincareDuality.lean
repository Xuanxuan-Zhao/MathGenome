import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.PoincareDuality
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.CompactSupportDualityMap
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Cohomology.FreeChainDual
import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Topology.Bases
import Mathlib.Order.SetAccumulate
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.CompactSupportMayerVietoris
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w

namespace P202.PoincareDuality
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation P202Specs.CompactSupport
open P202Specs.PoincareDuality

variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]

/-- The five lemma with a unit in the connecting square. Multiplying the
last two vertical arrows by that unit makes all four squares commute. -/
lemma signed_five_lemma
    {X₁ X₂ X₃ X₄ X₅ Y₁ Y₂ Y₃ Y₄ Y₅ : ModuleCat.{v} R}
    (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅)
    (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) (g₃ : Y₃ ⟶ Y₄) (g₄ : Y₄ ⟶ Y₅)
    (i₁ : X₁ ⟶ Y₁) (i₂ : X₂ ⟶ Y₂) (i₃ : X₃ ⟶ Y₃)
    (i₄ : X₄ ⟶ Y₄) (i₅ : X₅ ⟶ Y₅) (s : ℤˣ)
    (hc₁ : f₁ ≫ i₂ = i₁ ≫ g₁) (hc₂ : f₂ ≫ i₃ = i₂ ≫ g₂)
    (hc₃ : ∀ x, g₃ (i₃ x) = (s : ℤ) • i₄ (f₃ x))
    (hc₄ : f₄ ≫ i₅ = i₄ ≫ g₄)
    (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃)
    (hf₃ : Function.Exact f₃ f₄) (hg₁ : Function.Exact g₁ g₂)
    (hg₂ : Function.Exact g₂ g₃) (hg₃ : Function.Exact g₃ g₄)
    (hi₁ : Function.Surjective i₁) (hi₂ : Function.Bijective i₂)
    (hi₄ : Function.Bijective i₄) (hi₅ : Function.Injective i₅) :
    Function.Bijective i₃ := by
  have h₁ : g₁.hom.comp i₁.hom = i₂.hom.comp f₁.hom :=
    congrArg ModuleCat.Hom.hom hc₁.symm
  have h₂ : g₂.hom.comp i₂.hom = i₃.hom.comp f₂.hom :=
    congrArg ModuleCat.Hom.hom hc₂.symm
  have h₃ : g₃.hom.comp i₃.hom = ((s : ℤ) • i₄.hom).comp f₃.hom := by
    ext x
    exact hc₃ x
  have h₄ : g₄.hom.comp ((s : ℤ) • i₄.hom) =
      ((s : ℤ) • i₅.hom).comp f₄.hom := by
    ext x
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply, map_zsmul,
      ModuleCat.comp_apply] using
      congrArg (fun y => (s : ℤ) • y) (congrArg (fun f => f x) hc₄.symm)
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    f₁.hom f₂.hom f₃.hom f₄.hom g₁.hom g₂.hom g₃.hom g₄.hom
    i₁.hom i₂.hom i₃.hom ((s : ℤ) • i₄.hom) ((s : ℤ) • i₅.hom)
    h₁ h₂ h₃ h₄ hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hi₁ hi₂
    (s.isUnit.smul_bijective.comp hi₄) (s.isUnit.smul_bijective.1.comp hi₅)

lemma exact_functions {k : ℕ} (S : ComposableArrows (ModuleCat.{v} R) k)
    (hS : S.Exact) (i : ℕ) (hi : i+2 ≤ k) :
    Function.Exact (S.map' i (i+1)) (S.map' (i+1) (i+2)) :=
  (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS.exact i hi)

lemma biprod_bijective {X Y X' Y' : ModuleCat.{v} R} (f : X ⟶ X') (g : Y ⟶ Y')
    (hf : Function.Bijective f) (hg : Function.Bijective g) :
    Function.Bijective (biprod.map f g) := by
  haveI := (ConcreteCategory.isIso_iff_bijective f).mpr hf
  haveI := (ConcreteCategory.isIso_iff_bijective g).mpr hg
  exact (biprod.mapIso (asIso f) (asIso g)).toLinearEquiv.bijective

open P202Specs.CompactSupportMayerVietoris

/-- Degree transport as a morphism between the original bundled homology
objects, avoiding a second bundling of their underlying modules. -/
def homologyTransport (X : TopCat.{v}) (i j : ℤ) (h : i = j) :
    homology R R X i ⟶ homology R R X j := by
  subst j
  exact 𝟙 _

lemma homologyTransport_bijective (X : TopCat.{v}) (i j : ℤ) (h : i = j) :
    Function.Bijective (homologyTransport R X i j h) := by
  subst j
  exact Function.bijective_id

lemma homologyTransport_apply (X : TopCat.{v}) (i j : ℤ) (h : i = j)
    (a : homology R R X i) :
    homologyTransport R X i j h a = degreeTransport R X i j h a := by
  subst j
  rfl

lemma biprod_map_id (X Y : ModuleCat.{v} R) :
    biprod.map (𝟙 X) (𝟙 Y) = 𝟙 (X ⊞ Y) := by
  apply biprod.hom_ext <;> simp

lemma degreeTransport_bijective (X : TopCat.{v}) (i j : ℤ) (h : i = j) :
    Function.Bijective (degreeTransport R X i j h) := by
  subst j
  exact Function.bijective_id

lemma first_degreeTransport [T2Space M] (C : Cover M) (i j : ℤ) (h : i = j) :
    P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary i ≫
      biprod.map (homologyTransport R (TopCat.of C.left) i j h)
        (homologyTransport R (TopCat.of C.right) i j h) =
      homologyTransport R (TopCat.of C.intersection) i j h ≫
        P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary j := by
  subst j
  change P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary i ≫
    biprod.map (𝟙 _) (𝟙 _) = 𝟙 _ ≫
      P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary i
  rw [biprod_map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

lemma sum_connecting_exact [T2Space M] (C : Cover M)
    (δ : P202Specs.MayerVietoris.Connecting.{u,v,0} (ordinaryChains R))
    (hδ : P202Specs.MayerVietoris.Exact (ordinaryChains R) δ)
    (k q : ℤ) (h : k = q+1) :
    Function.Exact (P202Specs.MayerVietoris.sum (ordinaryChains R) C.ordinary k)
      (homologyTransport R (TopCat.of M) k (q+1) h ≫ δ C.ordinary q) := by
  subst k
  change Function.Exact (P202Specs.MayerVietoris.sum (ordinaryChains R) C.ordinary (q+1))
    (δ C.ordinary q)
  exact exact_functions R _ (hδ.1 C.ordinary q) 1 (by omega)

lemma connecting_first_exact [T2Space M] (C : Cover M)
    (δ : P202Specs.MayerVietoris.Connecting.{u,v,0} (ordinaryChains R))
    (hδ : P202Specs.MayerVietoris.Exact (ordinaryChains R) δ)
    (k q : ℤ) (h : k = q+1) :
    Function.Exact
      (homologyTransport R (TopCat.of M) k (q+1) h ≫ δ C.ordinary q)
      (P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary q) := by
  subst k
  change Function.Exact (δ C.ordinary q)
    (P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary q)
  exact exact_functions R _ (hδ.1 C.ordinary q) 2 (by omega)

/-- The finite gluing step for the actual compact-support cap maps. The
orientations in the hypotheses are precisely the inherited ones in G. -/
theorem twoSet (d : DualityData.{u,v} R) {n : ℕ} (A : Manifold n M)
    (o : Orientation R A) [T2Space M] (C : Cover M)
    (G : GluingData R M d n A o C)
    (hL : Holds R C.left d G.leftManifold G.leftOrientation)
    (hR : Holds R C.right d G.rightManifold G.rightOrientation)
    (hI : Holds R C.intersection d G.intersectionManifold G.intersectionOrientation) :
    Holds R M d A o := by
  intro p
  let k : ℤ := (n : ℤ)-p
  let q : ℤ := (n : ℤ)-p-1
  have hk : k = q+1 := by dsimp [k, q]; omega
  have hq : (n : ℤ)-(p+1) = q := by dsimp [q]; omega
  let eI := homologyTransport R (TopCat.of C.intersection) ((n : ℤ)-(p+1)) q hq
  let eL := homologyTransport R (TopCat.of C.left) ((n : ℤ)-(p+1)) q hq
  let eR := homologyTransport R (TopCat.of C.right) ((n : ℤ)-(p+1)) q hq
  let DL (i : ℤ) : ModuleCat.of R (CompactCohomology R C.left i) ⟶
      homology R R (TopCat.of C.left) ((n : ℤ)-i) :=
    ModuleCat.ofHom (d.D n C.left G.leftManifold G.leftOrientation i)
  let DR (i : ℤ) : ModuleCat.of R (CompactCohomology R C.right i) ⟶
      homology R R (TopCat.of C.right) ((n : ℤ)-i) :=
    ModuleCat.ofHom (d.D n C.right G.rightManifold G.rightOrientation i)
  let DI (i : ℤ) : ModuleCat.of R (CompactCohomology R C.intersection i) ⟶
      homology R R (TopCat.of C.intersection) ((n : ℤ)-i) :=
    ModuleCat.ofHom (d.D n C.intersection G.intersectionManifold G.intersectionOrientation i)
  let DM : ModuleCat.of R (CompactCohomology R M p) ⟶
      homology R R (TopCat.of M) ((n : ℤ)-p) := ModuleCat.ofHom (d.D n M A o p)
  let δ := homologyTransport R (TopCat.of M) k (q+1) hk ≫
    G.homologyConnecting C.ordinary q
  have hi₂ := biprod_bijective R (DL p) (DR p) (hL p) (hR p)
  have hi₄ : Function.Bijective (DI (p+1) ≫ eI) :=
    (homologyTransport_bijective R _ _ _ hq).comp (hI (p+1))
  have hi₅ : Function.Bijective (biprod.map (DL (p+1)) (DR (p+1)) ≫ biprod.map eL eR) :=
    (biprod_bijective R eL eR (homologyTransport_bijective R _ _ _ hq)
      (homologyTransport_bijective R _ _ _ hq)).comp
      (biprod_bijective R _ _ (hL (p+1)) (hR (p+1)))
  apply signed_five_lemma R
    (first R M C G.extendLeft G.extendRight p) (sum R M d C p)
    (ModuleCat.ofHom (G.connecting p)) (first R M C G.extendLeft G.extendRight (p+1))
    (P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary k)
    (P202Specs.MayerVietoris.sum (ordinaryChains R) C.ordinary k)
    δ (P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary q)
    (DI p) (biprod.map (DL p) (DR p)) DM (DI (p+1) ≫ eI)
    (biprod.map (DL (p+1)) (DR (p+1)) ≫ biprod.map eL eR) (p+1).negOnePow
  · exact G.cap_first p
  · exact G.cap_sum p
  · intro a
    change G.homologyConnecting C.ordinary q
        (homologyTransport R (TopCat.of M) k (q+1) hk (d.D n M A o p a)) =
      ((p+1).negOnePow : ℤ) •
        homologyTransport R (TopCat.of C.intersection) ((n : ℤ)-(p+1)) q hq
          (d.D n C.intersection G.intersectionManifold G.intersectionOrientation (p+1)
            (G.connecting p a))
    rw [homologyTransport_apply, homologyTransport_apply]
    exact G.cap_connecting p a
  · have hc : first R M C G.extendLeft G.extendRight (p+1) ≫
        biprod.map (DL (p+1)) (DR (p+1)) =
        DI (p+1) ≫ P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary ((n : ℤ)-(p+1)) :=
      G.cap_first (p+1)
    rw [← Category.assoc, hc, Category.assoc]
    have ht : P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary ((n : ℤ)-(p+1)) ≫
        biprod.map eL eR = eI ≫ P202Specs.MayerVietoris.first (ordinaryChains R) C.ordinary q :=
      first_degreeTransport R M C _ _ hq
    exact (congrArg (fun f => DI (p+1) ≫ f) ht).trans (Category.assoc _ _ _).symm
  · exact exact_functions R _ (G.exact.1 p) 0 (by omega)
  · exact exact_functions R _ (G.exact.1 p) 1 (by omega)
  · exact exact_functions R _ (G.exact.1 p) 2 (by omega)
  · exact exact_functions R _ (G.homology_exact.2 C.ordinary k) 0 (by omega)
  · exact sum_connecting_exact R M C G.homologyConnecting G.homology_exact k q hk
  · exact connecting_first_exact R M C G.homologyConnecting G.homology_exact k q hk
  · exact (hI p).2
  · exact hi₂
  · exact hi₄
  · exact hi₅.1

/-- A compact support contained in a subspace remains compact in that
subspace, with no extra closedness condition on the subspace. -/
def restrictSupport (K : Support M) (U : Set M) (h : (K : Set M) ⊆ U) : Support U :=
  ⟨Subtype.val ⁻¹' (K : Set M),
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' K.isCompact
      (fun x hx => ⟨⟨x, h hx⟩, rfl⟩)⟩

lemma ambient_restrictSupport (K : Support M) (U : Set M) (h : (K : Set M) ⊆ U) :
    ambientSupport M U (restrictSupport M K U h) = K := by
  apply TopologicalSpace.Compacts.ext
  exact Set.image_preimage_eq_of_subset (fun x hx => ⟨⟨x, h hx⟩, rfl⟩)

/-- Every compact lies in one member of an increasing open cover. This
includes the empty compact, with no nonemptiness hypothesis on M. -/
lemma compact_in_increasing_cover (U : ℕ → Set M) (hU : ∀ i, IsOpen (U i))
    (hmono : Monotone U) (hcover : ⋃ i, U i = Set.univ) (K : Support M) :
    ∃ i, (K : Set M) ⊆ U i := by
  apply K.isCompact.elim_directed_cover U hU
  · rw [hcover]
    exact Set.subset_univ _
  · exact fun i j => ⟨max i j, hmono (le_max_left _ _), hmono (le_max_right _ _)⟩

lemma supported_class_from_open (d : DualityData.{u,v} R) [T2Space M]
    (U : Set M) (hU : IsOpen U) (K : Support M) (L : Support U)
    (hL : ambientSupport M U L = K) (p : ℤ) (a : supportedCohomology R M p K) :
    ∃ b : CompactCohomology R U p, d.extend M U hU p b = ofSupport R M p K a := by
  subst K
  exact ⟨ofSupport R U p L (openPullback R M U L p a),
    d.extension_represents M U hU p L a⟩

/-- Compact-support cohomology classes on an increasing union already
come from one open member through the actual prescribed extension. -/
theorem compact_class_from_increasing_cover (d : DualityData.{u,v} R) [T2Space M]
    (U : ℕ → Set M) (hU : ∀ i, IsOpen (U i))
    (hmono : Monotone U) (hcover : ⋃ i, U i = Set.univ)
    (p : ℤ) (a : CompactCohomology R M p) :
    ∃ (i : ℕ) (b : CompactCohomology R (U i) p), d.extend M (U i) (hU i) p b = a := by
  obtain ⟨K, b, rfl⟩ := P202.CompactSupport.representatives R M p a
  obtain ⟨i, hi⟩ := compact_in_increasing_cover M U hU hmono hcover K
  obtain ⟨c, hc⟩ := supported_class_from_open R M d (U i) (hU i) K
    (restrictSupport M K (U i) hi) (ambient_restrictSupport M K (U i) hi) p b
  exact ⟨i, c, hc⟩

/-- The image of any ordinary finite singular chain is compact. This uses
the accepted chain-support factorization and the canonical full-subspace
homeomorphism; negative chain degrees are included. -/
lemma ordinary_chain_compact (i : ℤ) (b : (ordinaryComplex R R (TopCat.of M)).X i) :
    ∃ K : Support M, ∀ U : Set M, (K : Set M) ⊆ U →
      ∃ c : (ordinaryComplex R R (TopCat.of U)).X i,
        (inclusion (ordinaryFunctor R R) ⟨TopCat.of M, U⟩).f i c = b := by
  let e := (ordinaryFunctor R R).mapIso (TopCat.isoOfHomeo
    (X := TopCat.of (Set.univ : Set M)) (Y := TopCat.of M) (Homeomorph.Set.univ M))
  let b' := (HomologicalComplex.Hom.isoApp e i).inv b
  have hb : (inclusion (ordinaryFunctor R R) ⟨TopCat.of M, Set.univ⟩).f i b' = b :=
    (HomologicalComplex.Hom.isoApp e i).inv_hom_id_apply b
  obtain ⟨K, hK, _, hfactor⟩ := P202.CompactOrientation.ordinary_chain_compact_factor R
    (X := TopCat.of M) Set.univ i b'
  refine ⟨⟨K, hK⟩, ?_⟩
  intro U hKU
  obtain ⟨c, hc⟩ := hfactor U hKU
  exact ⟨c, hc.trans hb⟩

lemma ordinary_chain_from_increasing_cover (U : ℕ → Set M) (hU : ∀ i, IsOpen (U i))
    (hmono : Monotone U) (hcover : ⋃ i, U i = Set.univ)
    (q : ℤ) (b : (ordinaryComplex R R (TopCat.of M)).X q) :
    ∃ (i : ℕ) (c : (ordinaryComplex R R (TopCat.of (U i))).X q),
      (inclusion (ordinaryFunctor R R) ⟨TopCat.of M, U i⟩).f q c = b := by
  obtain ⟨K, hK⟩ := ordinary_chain_compact R M q b
  obtain ⟨i, hi⟩ := compact_in_increasing_cover M U hU hmono hcover K
  obtain ⟨c, hc⟩ := hK (U i) hi
  exact ⟨i, c, hc⟩

/-- Every ordinary homology class on an increasing open union comes from a
member, through its original finite-singular-chain inclusion. -/
theorem homology_class_from_increasing_cover (U : ℕ → Set M) (hU : ∀ i, IsOpen (U i))
    (hmono : Monotone U) (hcover : ⋃ i, U i = Set.univ)
    (q : ℤ) (a : homology R R (TopCat.of M) q) :
    ∃ (i : ℕ) (b : homology R R (TopCat.of (U i)) q), openHomology R M (U i) q b = a := by
  let B := ordinaryComplex R R (TopCat.of M)
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (B.homologyπ q)).mp inferInstance a
  obtain ⟨i, c, hc⟩ := ordinary_chain_from_increasing_cover R M U hU hmono hcover q (B.iCycles q z)
  let C := ordinaryComplex R R (TopCat.of (U i))
  let f := inclusion (ordinaryFunctor R R) ⟨TopCat.of M, U i⟩
  have hz₀ : B.d q (q-1) (B.iCycles q z) = 0 :=
    congrArg (fun f => f z) (B.iCycles_d q (q-1))
  have hc₀ : C.d q (q-1) c = 0 := by
    apply (ModuleCat.mono_iff_injective (f.f (q-1))).mp inferInstance
    have he := congrArg (fun f => f c) (f.comm q (q-1))
    simp only [ModuleCat.comp_apply] at he
    change B.d q (q-1) (f.f q c) = f.f (q-1) (C.d q (q-1) c) at he
    rw [hc, hz₀] at he
    exact he.symm.trans (map_zero _).symm
  have hnext : (ComplexShape.down ℤ).next q = q-1 :=
    (ComplexShape.down ℤ).next_eq' (by simp [ComplexShape.down_Rel])
  let w := C.cyclesMk c (q-1) hnext hc₀
  have hw : C.iCycles q w = c := C.i_cyclesMk c (q-1) hnext hc₀
  have hfz : cyclesMap f q w = z := by
    apply (ModuleCat.mono_iff_injective (B.iCycles q)).mp inferInstance
    have he := congrArg (fun f => f w) (cyclesMap_i f q)
    simp only [ModuleCat.comp_apply] at he
    change B.iCycles q (cyclesMap f q w) = f.f q (C.iCycles q w) at he
    exact he.trans ((congrArg (fun x => f.f q x) hw).trans hc)
  refine ⟨i, C.homologyπ q w, ?_⟩
  have he := congrArg (fun f => f w) (homologyπ_naturality f q)
  simp only [ModuleCat.comp_apply] at he
  change homologyMap f q (C.homologyπ q w) = B.homologyπ q (cyclesMap f q w) at he
  change homologyMap f q (C.homologyπ q w) = a
  exact he.trans ((congrArg (fun x => B.homologyπ q x) hfz).trans hz)

@[simp] lemma forgetSupport_ofSupport (p : ℤ) (K : Support M)
    (a : supportedCohomology R M p K) :
    forgetSupport R M p (ofSupport R M p K a) =
      homologyMap (cochainInclusion R M K) p a := by
  simp only [forgetSupport, descend, ofSupport, Module.DirectLimit.lift_of]

/-- At the full support the relative-to-ordinary cochain map is the dual
of the quotient by the chains of the empty space. -/
lemma fullSupport_cochain_iso (hM : IsCompact (Set.univ : Set M)) :
    IsIso (cochainInclusion R M ⟨Set.univ, hM⟩) := by
  let P := supportedPair M (Set.univ : Set M)
  letI : IsEmpty P.sub := ⟨fun x => x.property (Set.mem_univ _)⟩
  haveI : ∀ i : ℤ, IsIso ((projection (ordinaryFunctor R R) P).f i) := by
    intro i
    exact ((P202.RelativeSingularChains.sequence_shortExact (ordinaryFunctor R R) P i).isIso_g_iff).mpr
      (P202.SingularDegreeZero.emptyOrdinaryX R R P.sub i)
  haveI : IsIso (projection (ordinaryFunctor R R) P) :=
    HomologicalComplex.Hom.isIso_of_components _
  change IsIso ((dualComplexFunctor R R (ComplexShape.down ℤ)).map
    (projection (ordinaryFunctor R R) P).op)
  infer_instance

/-- A compact whole space is a terminal support, so its structure map to
the direct limit is bijective, in every integer degree. -/
lemma fullSupport_bijective (hM : IsCompact (Set.univ : Set M)) (p : ℤ) :
    Function.Bijective (ofSupport R M p ⟨Set.univ, hM⟩) := by
  classical
  let T : Support M := ⟨Set.univ, hM⟩
  have hT : ∀ K : Support M, K ≤ T := fun _ _ _ => Set.mem_univ _
  constructor
  · intro a b hab
    obtain ⟨N, hTN, _, hN⟩ := (P202.CompactSupport.equalityWitness R M p T T a b).mp hab
    have he : N = T := le_antisymm (hT N) hTN
    subst N
    have ha : transition R M p T T hTN a = a :=
      DirectedSystem.map_self (f := fun {K L} h => (transition R M p K L h).toFun) a
    have hb : transition R M p T T hTN b = b :=
      DirectedSystem.map_self (f := fun {K L} h => (transition R M p K L h).toFun) b
    exact ha.symm.trans (hN.trans hb)
  · intro a
    obtain ⟨K, b, rfl⟩ := P202.CompactSupport.representatives R M p a
    exact ⟨transition R M p K T (hT K) b, Module.DirectLimit.of_f⟩

/-- The compact-support identification is the canonical forget-support map,
not just an unspecified equivalence of the two modules. -/
theorem forgetSupport_bijective (hM : IsCompact (Set.univ : Set M)) (p : ℤ) :
    Function.Bijective (forgetSupport R M p) := by
  haveI := fullSupport_cochain_iso R M hM
  have hcomp : (forgetSupport R M p).comp (ofSupport R M p ⟨Set.univ, hM⟩) =
      (homologyMap (cochainInclusion R M ⟨Set.univ, hM⟩) p).hom := by
    ext a
    exact forgetSupport_ofSupport R M p ⟨Set.univ, hM⟩ a
  have hb : Function.Bijective
      ((forgetSupport R M p).comp (ofSupport R M p ⟨Set.univ, hM⟩)) := by
    rw [hcomp]
    exact (asIso (homologyMap (cochainInclusion R M ⟨Set.univ, hM⟩) p)).toLinearEquiv.bijective
  exact ⟨fun a b hab => by
    obtain ⟨a', rfl⟩ := (fullSupport_bijective R M hM p).2 a
    obtain ⟨b', rfl⟩ := (fullSupport_bijective R M hM p).2 b
    exact congrArg (ofSupport R M p ⟨Set.univ, hM⟩) (hb.1 hab),
    fun a => by
      obtain ⟨b, hb⟩ := hb.2 a
      exact ⟨ofSupport R M p ⟨Set.univ, hM⟩ b, hb⟩⟩

/-- On compact manifolds the representative law for D gives precisely cap
with the ordinary fundamental class under the canonical identification. -/
theorem compactIdentification_conditional
    (_ : P202Specs.CompactSupportMayerVietoris.Expected.gluing.{u,v}) :
    P202Specs.PoincareDuality.Expected.compactIdentification.{u,v} := by
  intro R _ d n M _ A o hM
  let T : Support M := ⟨Set.univ, hM⟩
  let C := ordinaryCochains R R (TopCat.of M)
  let B := ordinaryComplex R R (TopCat.of M)
  let Q := supportedCochains R M T
  let H := ordinary R R (supportedPair M T)
  let f := cochainInclusion R M T
  let q := projection (ordinaryFunctor R R) (supportedPair M T)
  haveI : IsIso f := fullSupport_cochain_iso R M hM
  obtain ⟨_, μ, hμ, _⟩ :=
    P202.CompactOrientation.ordinaryFundamentalClass R n M A o hM
  let hf := forgetSupport_bijective R M hM
  refine ⟨hf, μ, hμ, ?_⟩
  intro p a z hz
  obtain ⟨b, hb⟩ := (asIso (cyclesMap f (p : ℤ))).toLinearEquiv.surjective a
  let t := cyclesMap q (n : ℤ) z
  have ht : q.f (n : ℤ) (B.iCycles (n : ℤ) z) = H.iCycles (n : ℤ) t := by
    exact (congrArg (fun f => f z) (cyclesMap_i q (n : ℤ))).symm
  have htμ : P202Specs.CompactOrientation.HasLocalValues R o.val T
      (H.homologyπ (n : ℤ) t) := by
    have he := (congrArg (fun f => f z) (homologyπ_naturality q (n : ℤ))).symm
    simp only [ModuleCat.comp_apply] at he
    change H.homologyπ (n : ℤ) t = homologyMap q (n : ℤ) (B.homologyπ (n : ℤ) z) at he
    rw [he, hz]
    exact hμ
  obtain ⟨w, hw, hD⟩ := d.represents n M A o p T b t (B.iCycles (n : ℤ) z) ht htμ
  have hbval : f.f (p : ℤ) (Q.iCycles (p : ℤ) b) = C.iCycles (p : ℤ) a := by
    have he := (congrArg (fun f => f b) (cyclesMap_i f (p : ℤ))).symm
    change f.f (p : ℤ) (Q.iCycles (p : ℤ) b) =
      C.iCycles (p : ℤ) (cyclesMap f (p : ℤ) b) at he
    exact he.trans (congrArg (fun x => C.iCycles (p : ℤ) x) hb)
  have hbclass : forgetSupport R M (p : ℤ)
      (ofSupport R M (p : ℤ) T (Q.homologyπ (p : ℤ) b)) = C.homologyπ (p : ℤ) a := by
    rw [forgetSupport_ofSupport]
    have he := congrArg (fun f => f b) (homologyπ_naturality f (p : ℤ))
    simp only [ModuleCat.comp_apply] at he
    change homologyMap f (p : ℤ) (Q.homologyπ (p : ℤ) b) =
      C.homologyπ (p : ℤ) (cyclesMap f (p : ℤ) b) at he
    exact he.trans (congrArg (fun x => C.homologyπ (p : ℤ) x) hb)
  have ha : ((LinearEquiv.ofBijective (forgetSupport R M (p : ℤ)) (hf (p : ℤ))).symm
      (C.homologyπ (p : ℤ) a)) = ofSupport R M (p : ℤ) T (Q.homologyπ (p : ℤ) b) := by
    apply (LinearEquiv.ofBijective (forgetSupport R M (p : ℤ)) (hf (p : ℤ))).injective
    rw [LinearEquiv.apply_symm_apply]
    exact hbclass.symm
  refine ⟨w, ?_, ?_⟩
  · change B.iCycles ((n : ℤ)-p) w =
      P202Specs.CapProducts.cap R (TopCat.of M) p (n : ℤ)
        (P202Specs.CupProduct.cocycleValue R (TopCat.of M) p a) (B.iCycles (n : ℤ) z)
    change B.iCycles ((n : ℤ)-p) w =
      P202Specs.CapProducts.cap R (TopCat.of M) p (n : ℤ)
        (ordinaryCochainsEquiv R R (TopCat.of M) p (f.f (p : ℤ) (Q.iCycles (p : ℤ) b)))
        (B.iCycles (n : ℤ) z) at hw
    rw [hbval] at hw
    exact hw
  · rw [ha]
    exact hD

/-- Dimension vanishing follows from all-degree duality and the genuine
negative-degree convention, without a compactness or finite type hypothesis. -/
lemma aboveDimension_of_duality (d : DualityData.{u,v} R) {n : ℕ}
    (A : Manifold n M) (o : Orientation R A) (h : Holds R M d A o)
    (i : ℤ) (hi : (n : ℤ) < i) : IsZero (homology R R (TopCat.of M) i) := by
  have hp : (n : ℤ) - i < 0 := by omega
  haveI := P202.CompactSupport.negative R M ((n : ℤ)-i) hp
  have he : (n : ℤ) - ((n : ℤ)-i) = i := by omega
  have hs := (h ((n : ℤ)-i)).2
  have hz : IsZero (homology R R (TopCat.of M) ((n : ℤ) - ((n : ℤ)-i))) :=
    ModuleCat.isZero_iff_subsingleton.mpr (Function.Surjective.subsingleton hs)
  simpa only [he] using hz

/-- The representative law determines the duality map uniquely, in all
integer degrees, independently of choices in its construction. -/
lemma dualityMap_unique (d e : DualityData.{u,v} R) {n : ℕ}
    (A : Manifold n M) (o : Orientation R A) (p : ℤ) :
    d.D n M A o p = e.D n M A o p := by
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    apply LinearMap.ext
    intro a
    obtain ⟨K, b, rfl⟩ := P202.CompactSupport.representatives R M (p : ℤ) a
    let Q := supportedCochains R M K
    let B := ordinary R R (supportedPair M K)
    obtain ⟨a, rfl⟩ := (ModuleCat.epi_iff_surjective (Q.homologyπ (p : ℤ))).mp
      inferInstance b
    obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (B.homologyπ (n : ℤ))).mp
      inferInstance (P202.CompactSupport.fundamentalClass R M A o K)
    have hlocal : P202Specs.CompactOrientation.HasLocalValues R o.val K
        (B.homologyπ (n : ℤ) z) := by
      rw [hz]
      exact P202.CompactSupport.fundamentalClass_values R M A o K
    obtain ⟨c, hc⟩ := P202.CapProducts.projection_surjective R (supportedPair M K)
      (n : ℤ) (B.iCycles (n : ℤ) z)
    obtain ⟨w, hw, hd⟩ := d.represents n M A o p K a z c hc hlocal
    obtain ⟨w', hw', he⟩ := e.represents n M A o p K a z c hc hlocal
    have hww : w = w' :=
      (ModuleCat.mono_iff_injective ((ordinaryComplex R R (TopCat.of M)).iCycles
        ((n : ℤ)-p))).mp inferInstance (hw.trans hw'.symm)
    exact hd.trans ((congrArg (fun w =>
      (ordinaryComplex R R (TopCat.of M)).homologyπ ((n : ℤ)-p) w) hww).trans he.symm)
  · rw [d.negative n M A o p (by omega), e.negative n M A o p (by omega)]

/-- Surjectivity passes to an increasing open union through finite-chain
representatives and the actual cap naturality law. -/
theorem duality_surjective_increasing_cover (d : DualityData.{u,v} R) {n : ℕ}
    (A : Manifold n M) (o : Orientation R A)
    (U : ℕ → Set M) (hU : ∀ i, IsOpen (U i))
    (hmono : Monotone U) (hcover : ⋃ i, U i = Set.univ)
    (AU : ∀ i, Manifold n (U i)) (oU : ∀ i, Orientation R (AU i))
    (ho : ∀ i, OpenOrientationCompatible R M o.val (oU i).val)
    (p : ℤ) (hs : ∀ i, Function.Surjective (d.D n (U i) (AU i) (oU i) p)) :
    Function.Surjective (d.D n M A o p) := by
  letI : T2Space M := A.hausdorff
  intro a
  obtain ⟨i, b, hb⟩ := homology_class_from_increasing_cover R M U hU hmono hcover
    ((n : ℤ)-p) a
  obtain ⟨c, hc⟩ := hs i b
  refine ⟨d.extend M (U i) (hU i) p c, ?_⟩
  rw [← d.naturality n M A o (U i) (hU i) (AU i) (oU i) (ho i) p c, hc, hb]


lemma homologyπ_eq_zero_iff_boundary
    (B : ChainComplex (ModuleCat.{v} R) ℤ) (q : ℤ) (z : B.cycles q) :
    B.homologyπ q z = 0 ↔ ∃ c : B.X (q+1), B.d (q+1) q c = B.iCycles q z := by
  have hp : (ComplexShape.down ℤ).prev q = q+1 :=
    (ComplexShape.down ℤ).prev_eq' (by simp [ComplexShape.down_Rel])
  have hπ (z : B.cycles q) :
      B.pOpcycles q (B.iCycles q z) = B.homologyι q (B.homologyπ q z) :=
    (congrArg (fun f => f z) (B.homology_π_ι q)).symm
  constructor
  · intro hz
    have hz' : (B.sc q).pOpcycles (B.iCycles q z) = 0 := by
      change B.pOpcycles q (B.iCycles q z) = 0
      rw [hπ, hz, map_zero]
    obtain ⟨c, hc⟩ := ((B.sc q).moduleCat_pOpcycles_eq_zero_iff _).mp hz'
    change ∃ c : B.X (q+1), B.d (q+1) q c = B.iCycles q z
    have hh : ∃ c : B.X ((ComplexShape.down ℤ).prev q),
      B.d ((ComplexShape.down ℤ).prev q) q c = B.iCycles q z := ⟨c, hc⟩
    rw [hp] at hh
    exact hh
  · rintro ⟨c, hc⟩
    apply (ModuleCat.mono_iff_injective (B.homologyι q)).mp inferInstance
    rw [map_zero, ← hπ, ← hc]
    exact congrArg (fun f => f c) (B.d_pOpcycles (q+1) q)

open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202Specs.CohomologyPairs P202Specs.LocalOrientation P202Specs.CompactSupport
open P202Specs.PoincareDuality P202Specs.CompactSupportMayerVietoris

variable (M : Type v) [TopologicalSpace M]

/-- A class on one member of an increasing open cover that vanishes in the
union vanishes after inclusion into a larger member. The bounding chain is an
ordinary finite singular chain, also in negative integer degrees. -/
theorem homology_zero_in_increasing_cover
    (U : ℕ → Set M) (hU : ∀ i, IsOpen (U i))
    (hmono : Monotone U) (hcover : ⋃ i, U i = Set.univ)
    (q : ℤ) (i : ℕ) (a : homology R R (TopCat.of (U i)) q)
    (ha : openHomology R M (U i) q a = 0) :
    ∃ (k : ℕ) (hik : i ≤ k),
      homologyMap ((ordinaryFunctor R R).map
        (TopCat.ofHom (subsetInclusion (hmono hik)))) q a = 0 := by
  let B := ordinaryComplex R R (TopCat.of M)
  let Ci := ordinaryComplex R R (TopCat.of (U i))
  let fi := inclusion (ordinaryFunctor R R) ⟨TopCat.of M, U i⟩
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (Ci.homologyπ q)).mp inferInstance a
  have hzB : B.homologyπ q (cyclesMap fi q z) = 0 := by
    have he := congrArg (fun f => f z) (homologyπ_naturality fi q)
    change homologyMap fi q (Ci.homologyπ q z) =
      B.homologyπ q (cyclesMap fi q z) at he
    exact he.symm.trans ha
  obtain ⟨c, hc⟩ := (homologyπ_eq_zero_iff_boundary R B q (cyclesMap fi q z)).mp hzB
  obtain ⟨j, cj, hcj⟩ := ordinary_chain_from_increasing_cover R M U hU hmono hcover (q+1) c
  let k := max i j
  have hik : i ≤ k := le_max_left _ _
  have hjk : j ≤ k := le_max_right _ _
  let Ck := ordinaryComplex R R (TopCat.of (U k))
  let fk := inclusion (ordinaryFunctor R R) ⟨TopCat.of M, U k⟩
  let fj := inclusion (ordinaryFunctor R R) ⟨TopCat.of M, U j⟩
  let eik := (ordinaryFunctor R R).map
    (TopCat.ofHom (subsetInclusion (hmono hik)))
  let ejk := (ordinaryFunctor R R).map
    (TopCat.ofHom (subsetInclusion (hmono hjk)))
  have heik : eik ≫ fk = fi := by
    change (ordinaryFunctor R R).map _ ≫ (ordinaryFunctor R R).map _ = _
    rw [← (ordinaryFunctor R R).map_comp]
    rfl
  have hejk : ejk ≫ fk = fj := by
    change (ordinaryFunctor R R).map _ ≫ (ordinaryFunctor R R).map _ = _
    rw [← (ordinaryFunctor R R).map_comp]
    rfl
  let ck := ejk.f (q+1) cj
  let zk := cyclesMap eik q z
  have hckval : fk.f (q+1) ck = c := by
    exact (congrArg (fun f => f.f (q+1) cj) hejk).trans hcj
  have hck : Ck.d (q+1) q ck = Ck.iCycles q zk := by
    apply (ModuleCat.mono_iff_injective (fk.f q)).mp inferInstance
    have he₁ := congrArg (fun f => f ck) (fk.comm (q+1) q)
    change B.d (q+1) q (fk.f (q+1) ck) = fk.f q (Ck.d (q+1) q ck) at he₁
    have he₂ := congrArg (fun f => f z) (cyclesMap_i eik q)
    change Ck.iCycles q zk = eik.f q (Ci.iCycles q z) at he₂
    have he₃ := congrArg (fun f => f z) (cyclesMap_i fi q)
    change B.iCycles q (cyclesMap fi q z) = fi.f q (Ci.iCycles q z) at he₃
    calc
      fk.f q (Ck.d (q+1) q ck) = B.d (q+1) q c := by rw [← he₁, hckval]
      _ = B.iCycles q (cyclesMap fi q z) := hc
      _ = fi.f q (Ci.iCycles q z) := he₃
      _ = fk.f q (eik.f q (Ci.iCycles q z)) :=
        (congrArg (fun f => f.f q (Ci.iCycles q z)) heik).symm
      _ = fk.f q (Ck.iCycles q zk) := congrArg (fun x => fk.f q x) he₂.symm
  refine ⟨k, hik, ?_⟩
  change homologyMap eik q (Ci.homologyπ q z) = 0
  have he := congrArg (fun f => f z) (homologyπ_naturality eik q)
  change homologyMap eik q (Ci.homologyπ q z) = Ck.homologyπ q zk at he
  exact he.trans ((homologyπ_eq_zero_iff_boundary R Ck q zk).mpr ⟨ck, hck⟩)

/-- Equality in the union is witnessed after inclusion into a single larger
member; the index is allowed to depend on the classes. -/
theorem homology_eq_in_increasing_cover
    (U : ℕ → Set M) (hU : ∀ i, IsOpen (U i))
    (hmono : Monotone U) (hcover : ⋃ i, U i = Set.univ)
    (q : ℤ) (i : ℕ) (a b : homology R R (TopCat.of (U i)) q)
    (hab : openHomology R M (U i) q a = openHomology R M (U i) q b) :
    ∃ (k : ℕ) (hik : i ≤ k),
      homologyMap ((ordinaryFunctor R R).map
        (TopCat.ofHom (subsetInclusion (hmono hik)))) q a =
      homologyMap ((ordinaryFunctor R R).map
        (TopCat.ofHom (subsetInclusion (hmono hik)))) q b := by
  have hab₀ : openHomology R M (U i) q (a-b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨k, hik, hk⟩ := homology_zero_in_increasing_cover R M U hU hmono hcover q i (a-b) hab₀
  exact ⟨k, hik, sub_eq_zero.mp (by simpa only [map_sub] using hk)⟩


/-- The pair inclusion, with a fixed compact of the ambient space. -/
def containedPairInclusion (K : Support M) (U : Set M) (hKU : (K : Set M) ⊆ U) :
    supportedPair U (restrictSupport M K U hKU) ⟶ supportedPair M K where
  map := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  mapsTo := by intro x hx; exact hx

def containedPullback (K : Support M) (U : Set M) (hKU : (K : Set M) ⊆ U) (p : ℤ) :
    supportedCohomology R M p K ⟶
      supportedCohomology R U p (restrictSupport M K U hKU) :=
  (relativeCohomologyFunctor R R p).map (containedPairInclusion M K U hKU).op

lemma supportedPair_eqToHom_map (K L : Support M) (e : K = L) :
    (eqToHom (congrArg (fun K : Support M => supportedPair M (K : Set M)) e)).map =
      𝟙 (TopCat.of M) := by
  subst L
  rfl

lemma extension_contained_represents (d : DualityData.{u,v} R) [T2Space M]
    (K : Support M) (U : Set M) (hU : IsOpen U) (hKU : (K : Set M) ⊆ U)
    (p : ℤ) (a : supportedCohomology R M p K) :
    d.extend M U hU p (ofSupport R U p (restrictSupport M K U hKU)
      (containedPullback R M K U hKU p a)) = ofSupport R M p K a := by
  have hgen : ∀ (L : Support U) (K : Support M) (e : ambientSupport M U L = K)
      (a : supportedCohomology R M p K),
      d.extend M U hU p (ofSupport R U p L
        (((relativeCohomologyFunctor R R p).map
          (openPairInclusion M U L ≫ eqToHom (congrArg (fun K : Support M =>
            supportedPair M (K : Set M)) e)).op) a)) = ofSupport R M p K a := by
    intro L K e a
    subst K
    simp only [eqToHom_refl, Category.comp_id]
    change d.extend M U hU p (ofSupport R U p L (openPullback R M U L p a)) = _
    exact d.extension_represents M U hU p L a
  have e := ambient_restrictSupport M K U hKU
  have hf : containedPairInclusion M K U hKU =
      openPairInclusion M U (restrictSupport M K U hKU) ≫
        eqToHom (congrArg (fun K : Support M => supportedPair M (K : Set M)) e) := by
    apply PairMap.ext
    change _ = (openPairInclusion M U (restrictSupport M K U hKU)).map ≫ _
    rw [supportedPair_eqToHom_map M _ _ e]
    rfl
  change d.extend M U hU p (ofSupport R U p (restrictSupport M K U hKU)
    (((relativeCohomologyFunctor R R p).map (containedPairInclusion M K U hKU).op) a)) = _
  rw [hf]
  exact hgen (restrictSupport M K U hKU) K e a

/-- The direct inclusion between two subspaces of one ambient space. -/
def subsetMap (U V : Set M) (hUV : U ⊆ V) : TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x => ⟨x.val, hUV x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

def containedBetweenPair (K : Support M) (U V : Set M)
    (hKU : (K : Set M) ⊆ U) (hKV : (K : Set M) ⊆ V) (hUV : U ⊆ V) :
    supportedPair U (restrictSupport M K U hKU) ⟶
      supportedPair V (restrictSupport M K V hKV) where
  map := subsetMap M U V hUV
  mapsTo := by intro x hx; exact hx

lemma containedBetweenPair_ambient (K : Support M) (U V : Set M)
    (hKU : (K : Set M) ⊆ U) (hKV : (K : Set M) ⊆ V) (hUV : U ⊆ V) :
    containedBetweenPair M K U V hKU hKV hUV ≫ containedPairInclusion M K V hKV =
      containedPairInclusion M K U hKU := by
  apply PairMap.ext; rfl

lemma containedBetweenPair_pullback (K : Support M) (U V : Set M)
    (hKU : (K : Set M) ⊆ U) (hKV : (K : Set M) ⊆ V) (hUV : U ⊆ V)
    (p : ℤ) (a : supportedCohomology R M p K) :
    ((relativeCohomologyFunctor R R p).map
      (containedBetweenPair M K U V hKU hKV hUV).op)
      (containedPullback R M K V hKV p a) = containedPullback R M K U hKU p a := by
  have h := congrArg (fun f => (relativeCohomologyFunctor R R p).map f.op)
    (containedBetweenPair_ambient M K U V hKU hKV hUV)
  rw [op_comp, CategoryTheory.Functor.map_comp] at h
  exact congrArg (fun f => f a) h

def localBetweenPair (U V : Set M) (hUV : U ⊆ V) (x : U) :
    localPair U x ⟶ localPair V ⟨x.val, hUV x.property⟩ where
  map := subsetMap M U V hUV
  mapsTo := by
    intro y hy hxy
    apply hy
    apply Subtype.ext
    exact congrArg (fun z : V => z.val) hxy

lemma localBetweenPair_ambient (U V : Set M) (hUV : U ⊆ V) (x : U) :
    localBetweenPair M U V hUV x ≫
        P202Specs.LocalOrientation.openLocalInclusion V ⟨x.val, hUV x.property⟩ =
      P202Specs.LocalOrientation.openLocalInclusion U x := by
  apply PairMap.ext; rfl

lemma containedBetweenPair_point (K : Support M) (U V : Set M)
    (hKU : (K : Set M) ⊆ U) (hKV : (K : Set M) ⊆ V) (hUV : U ⊆ V)
    (x : U) (hx : x.val ∈ K) :
    containedBetweenPair M K U V hKU hKV hUV ≫
        pointMap (show (⟨x.val, hUV x.property⟩ : V) ∈ restrictSupport M K V hKV from hx) =
      pointMap (show x ∈ restrictSupport M K U hKU from hx) ≫
        localBetweenPair M U V hUV x := by
  apply PairMap.ext; rfl

lemma containedPairInclusion_point (K : Support M) (U : Set M)
    (hKU : (K : Set M) ⊆ U) (x : U) (hx : x.val ∈ K) :
    containedPairInclusion M K U hKU ≫ pointMap hx =
      pointMap (show x ∈ restrictSupport M K U hKU from hx) ≫
        P202Specs.LocalOrientation.openLocalInclusion U x := by
  apply PairMap.ext; rfl

lemma containedPullback_iso [T2Space M] (K : Support M) (U : Set M) (hU : IsOpen U)
    (hKU : (K : Set M) ⊆ U) (p : ℤ) : IsIso (containedPullback R M K U hKU p) := by
  let D := P202.LocalOrientation.openSupportExcisionData U hU (K : Set M)
    K.isCompact.isClosed hKU
  haveI := P202.CohomologyExcisionMV.excision R R D p
  have he : containedPairInclusion M K U hKU =
      (P202.LocalOrientation.openSupportExcisionIso U hU (K : Set M)
        K.isCompact.isClosed hKU).hom ≫ D.inclusion := by
    apply PairMap.ext; rfl
  rw [containedPullback, he, op_comp, CategoryTheory.Functor.map_comp]
  infer_instance

lemma containedPairInclusion_homology_isIso [T2Space M] (K : Support M)
    (U : Set M) (hU : IsOpen U) (hKU : (K : Set M) ⊆ U) (q : ℤ) :
    IsIso ((relativeHomologyFunctor R R q).map (containedPairInclusion M K U hKU)) := by
  cases q with
  | ofNat q =>
    exact P202.LocalOrientation.openSupportInclusion_isIso R U hU (K : Set M)
      K.isCompact.isClosed hKU q
  | negSucc q =>
    apply isIso_of_source_target_iso_zero
    · exact (P202.RelativeSingularChains.ordinary_negative R R
        (supportedPair U (restrictSupport M K U hKU)) _ (by omega)).2.isoZero
    · exact (P202.RelativeSingularChains.ordinary_negative R R
        (supportedPair M K) _ (by omega)).2.isoZero

lemma contained_local_values {n : ℕ} (K : Support M) (U : Set M)
    (hKU : (K : Set M) ⊆ U) (oM : LocalChoice R n M) (oU : LocalChoice R n U)
    (ho : OpenOrientationCompatible R M oM oU)
    (z : SupportedGroup R U (restrictSupport M K U hKU) n)
    (hz : P202Specs.CompactOrientation.HasLocalValues R oU (restrictSupport M K U hKU) z) :
    P202Specs.CompactOrientation.HasLocalValues R oM K
      (((relativeHomologyFunctor R R (n : ℤ)).map (containedPairInclusion M K U hKU)) z) := by
  intro x hx
  let y : U := ⟨x, hKU hx⟩
  have H := congrArg (fun f => ((relativeHomologyFunctor R R (n : ℤ)).map f) z)
    (containedPairInclusion_point M K U hKU y hx)
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at H
  change restrictPoint R hx n
    (((relativeHomologyFunctor R R (n : ℤ)).map (containedPairInclusion M K U hKU)) z) =
      ((relativeHomologyFunctor R R (n : ℤ)).map
        (P202Specs.LocalOrientation.openLocalInclusion U y))
        (restrictPoint R (show y ∈ restrictSupport M K U hKU from hx) n z) at H
  rw [H, hz y hx]
  exact ho y

lemma fundamentalClass_contained {n : ℕ} (A : Manifold n M) (oM : Orientation R A)
    (K : Support M) (U : Set M) (hKU : (K : Set M) ⊆ U)
    (AU : Manifold n U) (oU : Orientation R AU)
    (ho : OpenOrientationCompatible R M oM.val oU.val) :
    ((relativeHomologyFunctor R R (n : ℤ)).map (containedPairInclusion M K U hKU))
      (P202.CompactSupport.fundamentalClass R U AU oU (restrictSupport M K U hKU)) =
        P202.CompactSupport.fundamentalClass R M A oM K := by
  apply P202.CompactOrientation.hasLocalValues_unique R
    (P202.CompactOrientation.localDetection R n M A K K.isCompact)
  · exact contained_local_values R M K U hKU oM.val oU.val ho _
      (P202.CompactSupport.fundamentalClass_values R U AU oU _)
  · exact P202.CompactSupport.fundamentalClass_values R M A oM K

lemma fundamentalClass_between {n : ℕ} (A : Manifold n M) (oM : Orientation R A)
    (K : Support M) (U V : Set M) (hV : IsOpen V)
    (hKU : (K : Set M) ⊆ U) (hKV : (K : Set M) ⊆ V) (hUV : U ⊆ V)
    (AU : Manifold n U) (oU : Orientation R AU)
    (AV : Manifold n V) (oV : Orientation R AV)
    (hoU : OpenOrientationCompatible R M oM.val oU.val)
    (hoV : OpenOrientationCompatible R M oM.val oV.val) :
    ((relativeHomologyFunctor R R (n : ℤ)).map
      (containedBetweenPair M K U V hKU hKV hUV))
        (P202.CompactSupport.fundamentalClass R U AU oU (restrictSupport M K U hKU)) =
      P202.CompactSupport.fundamentalClass R V AV oV (restrictSupport M K V hKV) := by
  letI : T2Space M := A.hausdorff
  haveI := containedPairInclusion_homology_isIso R M K V hV hKV (n : ℤ)
  apply (ModuleCat.mono_iff_injective ((relativeHomologyFunctor R R (n : ℤ)).map
    (containedPairInclusion M K V hKV))).mp inferInstance
  change ((relativeHomologyFunctor R R (n : ℤ)).map (containedPairInclusion M K V hKV))
    (((relativeHomologyFunctor R R (n : ℤ)).map (containedBetweenPair M K U V hKU hKV hUV)) _) = _
  rw [← ModuleCat.comp_apply, ← CategoryTheory.Functor.map_comp,
    containedBetweenPair_ambient, fundamentalClass_contained R M A oM K U hKU AU oU hoU,
    fundamentalClass_contained R M A oM K V hKV AV oV hoV]

lemma extend_eq_canonical (d : DualityData.{u,v} R) [T2Space M]
    (U : Set M) (hU : IsOpen U) (p : ℤ) :
    d.extend M U hU p = P202.CompactSupport.extendOpen R M U hU p := by
  apply LinearMap.ext
  intro a
  obtain ⟨K, b, rfl⟩ := P202.CompactSupport.representatives R U p a
  have h := d.extension_represents M U hU p K
    (P202.CompactSupport.extendAt R M U hU K p b)
  rw [P202.CompactSupport.openPullback_extendAt] at h
  exact h.trans (P202.CompactSupport.extendOpen_ofSupport R M U hU p K b).symm

lemma extend_eq (d e : DualityData.{u,v} R) [T2Space M]
    (U : Set M) (hU : IsOpen U) (p : ℤ) : d.extend M U hU p = e.extend M U hU p := by
  rw [extend_eq_canonical R M d U hU p, extend_eq_canonical R M e U hU p]


/-- It is enough to calculate cap on a cofinal collection of compact supports.
The comparison maps are the original structure maps of compact cohomology. -/
theorem duality_of_cofinal_supports (d : DualityData.{u,v} R) {n : ℕ}
    (A : Manifold n M) (o : Orientation R A) (p : ℤ)
    (h : ∀ K : Support M, ∃ (L : Support M), K ≤ L ∧
      Function.Bijective ((d.D n M A o p).comp (ofSupport R M p L))) :
    Function.Bijective (d.D n M A o p) := by
  constructor
  · intro a b hab
    obtain ⟨K, c, hc⟩ := P202.CompactSupport.representatives R M p (a-b)
    obtain ⟨L, hKL, hL⟩ := h K
    have he := P202.CompactSupport.ofSupport_transition R M p K L hKL c
    have hc₀ : transition R M p K L hKL c = 0 := by
      apply hL.1
      change d.D n M A o p (ofSupport R M p L (transition R M p K L hKL c)) =
        d.D n M A o p (ofSupport R M p L 0)
      rw [he, hc, map_sub, hab, sub_self, map_zero, map_zero]
    apply sub_eq_zero.mp
    rw [← hc, ← he, hc₀, map_zero]
  · obtain ⟨L, _, hL⟩ := h ⊥
    intro a
    obtain ⟨b, hb⟩ := hL.2 a
    exact ⟨ofSupport R M p L b, hb⟩

/-- The empty manifold satisfies the all-degree theorem for every formal
orientation, without any dimension or coefficient restriction. -/
lemma empty_duality (d : DualityData.{u,v} R) {n : ℕ}
    (A : Manifold n M) (o : Orientation R A) [IsEmpty M] : Holds R M d A o := by
  intro p
  have hM : IsCompact (Set.univ : Set M) := by
    have he : (Set.univ : Set M) = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun x _ => isEmptyElim x)
    rw [he]
    exact isCompact_empty
  haveI : Subsingleton ((ordinaryComplex R R (TopCat.of M)).X p) :=
    ModuleCat.subsingleton_of_isZero (P202.SingularDegreeZero.emptyOrdinaryX R R (TopCat.of M) p)
  have hC : IsZero ((ordinaryCochains R R (TopCat.of M)).X p) :=
    P202.CohomologyPairs.dual_isZero R R _
      (P202.SingularDegreeZero.emptyOrdinaryX R R (TopCat.of M) p)
  haveI : Subsingleton (ordinaryCohomology R R (TopCat.of M) p) :=
    ModuleCat.subsingleton_of_isZero ((HomologicalComplex.ExactAt.of_isZero hC).isZero_homology)
  haveI : Subsingleton (CompactCohomology R M p) :=
    (forgetSupport_bijective R M hM p).1.subsingleton
  haveI : Subsingleton (homology R R (TopCat.of M) ((n : ℤ)-p)) :=
    ModuleCat.subsingleton_of_isZero
      (P202.SingularDegreeZero.emptyOrdinary R R (TopCat.of M) ((n : ℤ)-p))
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun a => ⟨0, Subsingleton.elim _ _⟩⟩


/-- Naturality for two ambient open subsets with a common compact support.
Both maps use the original subtypes, so no nested-subtype identification is
hidden in the statement. -/
lemma duality_contained_natural (d : DualityData.{u,v} R) {n : ℕ}
    (A : Manifold n M) (o : Orientation R A)
    (K : Support M) (U V : Set M) (hV : IsOpen V)
    (hKU : (K : Set M) ⊆ U) (hKV : (K : Set M) ⊆ V) (hUV : U ⊆ V)
    (AU : Manifold n U) (oU : Orientation R AU)
    (AV : Manifold n V) (oV : Orientation R AV)
    (hoU : OpenOrientationCompatible R M o.val oU.val)
    (hoV : OpenOrientationCompatible R M o.val oV.val)
    (p : ℕ) (a : supportedCohomology R M (p : ℤ) K) :
    homologyMap ((ordinaryFunctor R R).map (TopCat.ofHom (subsetInclusion hUV))) ((n : ℤ)-p)
      (d.D n U AU oU (p : ℤ) (ofSupport R U (p : ℤ) (restrictSupport M K U hKU)
        (containedPullback R M K U hKU (p : ℤ) a))) =
    d.D n V AV oV (p : ℤ) (ofSupport R V (p : ℤ) (restrictSupport M K V hKV)
      (containedPullback R M K V hKV (p : ℤ) a)) := by
  rw [dualityMap_unique R U d (P202.CompactSupport.dualityData R) AU oU (p : ℤ),
    dualityMap_unique R V d (P202.CompactSupport.dualityData R) AV oV (p : ℤ)]
  change homologyMap ((ordinaryFunctor R R).map
    (TopCat.ofHom (subsetInclusion hUV))) ((n : ℤ)-p)
    (P202.CompactSupport.dualityInt R U AU oU (p : ℤ) _) =
    P202.CompactSupport.dualityInt R V AV oV (p : ℤ) _
  rw [P202.CompactSupport.dualityInt_nat, P202.CompactSupport.dualityInt_nat,
    P202.CompactSupport.duality_ofSupport, P202.CompactSupport.duality_ofSupport]
  let f := containedBetweenPair M K U V hKU hKV hUV
  change homologyMap (P202.CompactSupport.ordinaryMap R f.map) ((n : ℤ)-p)
    ((P202.CapProducts.relativeSystem R (supportedPair U (restrictSupport M K U hKU))).homologyOp
      p (n : ℤ) (containedPullback R M K U hKU (p : ℤ) a)
        (P202.CompactSupport.fundamentalClass R U AU oU _)) =
    (P202.CapProducts.relativeSystem R (supportedPair V (restrictSupport M K V hKV))).homologyOp
      p (n : ℤ) (containedPullback R M K V hKV (p : ℤ) a)
        (P202.CompactSupport.fundamentalClass R V AV oV _)
  rw [← containedBetweenPair_pullback R M K U V hKU hKV hUV,
    P202.CompactSupport.homologyCap_natural,
    fundamentalClass_between R M A o K U V hV hKU hKV hUV AU oU AV oV hoU hoV]

/-- Injectivity passes to increasing open unions. A vanishing class is
represented at a compact support, and a finite bounding chain witnesses its
vanishing in a larger member. -/
theorem duality_injective_increasing_cover (d : DualityData.{u,v} R) {n : ℕ}
    (A : Manifold n M) (o : Orientation R A)
    (U : ℕ → Set M) (hU : ∀ i, IsOpen (U i))
    (hmono : Monotone U) (hcover : ⋃ i, U i = Set.univ)
    (AU : ∀ i, Manifold n (U i)) (oU : ∀ i, Orientation R (AU i))
    (ho : ∀ i, OpenOrientationCompatible R M o.val (oU i).val)
    (p : ℤ) (hinj : ∀ i, Function.Injective (d.D n (U i) (AU i) (oU i) p)) :
    Function.Injective (d.D n M A o p) := by
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    letI : T2Space M := A.hausdorff
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro a ha
    obtain ⟨K, b, rfl⟩ := P202.CompactSupport.representatives R M (p : ℤ) a
    obtain ⟨i, hi⟩ := compact_in_increasing_cover M U hU hmono hcover K
    let bi := ofSupport R (U i) (p : ℤ) (restrictSupport M K (U i) hi)
      (containedPullback R M K (U i) hi (p : ℤ) b)
    have hbi : d.extend M (U i) (hU i) (p : ℤ) bi = ofSupport R M (p : ℤ) K b :=
      extension_contained_represents R M d K (U i) (hU i) hi (p : ℤ) b
    have hz : openHomology R M (U i) ((n : ℤ)-p)
        (d.D n (U i) (AU i) (oU i) (p : ℤ) bi) = 0 := by
      rw [d.naturality n M A o (U i) (hU i) (AU i) (oU i) (ho i), hbi]
      exact ha
    obtain ⟨k, hik, hk⟩ := homology_zero_in_increasing_cover R M U hU hmono hcover
      ((n : ℤ)-p) i (d.D n (U i) (AU i) (oU i) (p : ℤ) bi) hz
    have hKk : (K : Set M) ⊆ U k := hi.trans (hmono hik)
    let bk := ofSupport R (U k) (p : ℤ) (restrictSupport M K (U k) hKk)
      (containedPullback R M K (U k) hKk (p : ℤ) b)
    have hDk : d.D n (U k) (AU k) (oU k) (p : ℤ) bk = 0 := by
      have he := duality_contained_natural R M d A o K (U i) (U k) (hU k)
        hi hKk (hmono hik) (AU i) (oU i) (AU k) (oU k) (ho i) (ho k) p b
      exact he.symm.trans hk
    have hbk : bk = 0 := (hinj k) (hDk.trans (map_zero _).symm)
    have he := extension_contained_represents R M d K (U k) (hU k) hKk (p : ℤ) b
    change d.extend M (U k) (hU k) (p : ℤ) bk = _ at he
    rw [hbk, map_zero] at he
    exact he.symm
  · haveI := P202.CompactSupport.negative R M p (by omega)
    exact fun _ _ _ => Subsingleton.elim _ _

/-- The complete increasing-union passage for the specified cap maps, with
ordinary finite singular homology in all integer degrees. -/
theorem increasingUnion (d : DualityData.{u,v} R) {n : ℕ}
    (A : Manifold n M) (o : Orientation R A)
    (U : ℕ → Set M) (hU : ∀ i, IsOpen (U i))
    (hmono : Monotone U) (hcover : ⋃ i, U i = Set.univ)
    (AU : ∀ i, Manifold n (U i)) (oU : ∀ i, Orientation R (AU i))
    (ho : ∀ i, OpenOrientationCompatible R M o.val (oU i).val)
    (h : ∀ i, Holds R (U i) d (AU i) (oU i)) : Holds R M d A o := by
  intro p
  exact ⟨duality_injective_increasing_cover R M d A o U hU hmono hcover AU oU ho p
      (fun i => (h i p).1),
    duality_surjective_increasing_cover R M d A o U hU hmono hcover AU oU ho p
      (fun i => (h i p).2)⟩


namespace ConcentratedChains
open Opposite
set_option maxHeartbeats 1000000
variable {R : Type u} [CommRing R]

def fromSingleCycles (K : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    {A : ModuleCat.{v} R} (c : A ⟶ K.cycles n) :
    (single (ModuleCat.{v} R) (.down ℤ) n).obj A ⟶ K :=
  mkHomFromSingle (c ≫ K.iCycles n)
    (by intro k hk; rw [Category.assoc, K.iCycles_d, comp_zero])

lemma fromSingleCycles_homologyMap (K : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    {A : ModuleCat.{v} R} (c : A ⟶ K.cycles n) :
    homologyMap (fromSingleCycles K n c) n =
      (singleObjHomologySelfIso (.down ℤ) n A).hom ≫ c ≫ K.homologyπ n := by
  apply (cancel_epi (((single (ModuleCat.{v} R) (.down ℤ) n).obj A).homologyπ n)).mp
  rw [homologyπ_naturality, homologyπ_singleObjHomologySelfIso_hom_assoc]
  have heq : cyclesMap (fromSingleCycles K n c) n =
      (singleObjCyclesSelfIso (.down ℤ) n A).hom ≫ c := by
    apply (cancel_mono (K.iCycles n)).mp
    rw [cyclesMap_i]
    simp only [fromSingleCycles, mkHomFromSingle_f, Category.assoc,
      singleObjCyclesSelfIso_hom]
  rw [heq, Category.assoc]

lemma fromSingleCycles_quasiIso (K : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    {A : ModuleCat.{v} R} (c : A ⟶ K.cycles n) [IsIso (c ≫ K.homologyπ n)]
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) :
    QuasiIso (fromSingleCycles K n c) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  by_cases hi : i = n
  · subst i
    rw [fromSingleCycles_homologyMap]
    infer_instance
  · exact (isZero_single_obj_homology (.down ℤ) n A i hi).isIso (h i hi) _

/-- This dual map is literally evaluation on c at degree n. -/
lemma dualFromSingleCycles_quasiIso
    (B : Type w) [AddCommGroup B] [Module R B]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    {A : ModuleCat.{v} R} [Module.Free R A]
    [∀ i, Module.Free R (K.X i)]
    (hK : P202Specs.FreeChainDual.BoundedBelow K)
    (c : A ⟶ K.cycles n) [IsIso (c ≫ K.homologyπ n)]
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) :
    QuasiIso ((P202Specs.CohomologyPairs.dualComplexFunctor R B (.down ℤ)).map
      (fromSingleCycles K n c).op) := by
  let S := (single (ModuleCat.{v} R) (.down ℤ) n).obj A
  haveI : ∀ i, Module.Free R (S.X i) := by
    intro i
    by_cases hi : i = n
    · subst i
      exact Module.Free.of_equiv (singleObjXSelf (.down ℤ) n A).symm.toLinearEquiv
    · haveI : Subsingleton (S.X i) :=
        ModuleCat.subsingleton_of_isZero (isZero_single_obj_X (.down ℤ) n A i hi)
      infer_instance
  have hS : P202Specs.FreeChainDual.BoundedBelow S :=
    ⟨n, fun i hi => isZero_single_obj_X (.down ℤ) n A i (by omega)⟩
  haveI := fromSingleCycles_quasiIso K n c h
  obtain ⟨e, he⟩ := P202.FreeChainDual.homotopy_equivalence S K hS hK
    (fromSingleCycles K n c)
  let ed := (P202Specs.CohomologyPairs.dualFunctor R B).mapHomotopyEquiv
    { hom := (opFunctor _ (.down ℤ)).map e.hom.op
      inv := (opFunctor _ (.down ℤ)).map e.inv.op
      homotopyHomInvId := by simpa using e.homotopyInvHomId.op
      homotopyInvHomId := by simpa using e.homotopyHomInvId.op }
  have hd := ed.quasiIso_hom
  change QuasiIso ((P202Specs.CohomologyPairs.dualComplexFunctor R B (.down ℤ)).map
    e.hom.op) at hd
  rw [he] at hd
  exact hd

open P202Specs.CohomologyPairs

abbrev dualSingle (B : Type w) [AddCommGroup B] [Module R B]
    (n : ℤ) (A : ModuleCat.{v} R) :=
  (dualComplexFunctor R B (.down ℤ)).obj
    (op ((single (ModuleCat.{v} R) (.down ℤ) n).obj A))

lemma dualSingle_d_zero (B : Type w) [AddCommGroup B] [Module R B]
    (n : ℤ) (A : ModuleCat.{v} R) (i j : ℤ) :
    (dualSingle B n A).d i j = 0 := by
  change (dualFunctor R B).map (Quiver.Hom.op
    (((single (ModuleCat.{v} R) (.down ℤ) n).obj A).d j i)) = 0
  rw [single_obj_d, op_zero, Functor.map_zero]

/-- Cohomology of the dual of a single chain object is the literal linear dual. -/
def dualSingleHomologyIso (B : Type w) [AddCommGroup B] [Module R B]
    (n : ℤ) (A : ModuleCat.{v} R) :
    (dualSingle B n A).homology n ≅ ModuleCat.of R (A →ₗ[R] B) := by
  let S := dualSingle B n A
  haveI : IsIso (S.iCycles n) :=
    S.isIso_iCycles n (n+1) (((ComplexShape.down ℤ).symm).next_eq' (by change n+1=n+1; rfl)) (dualSingle_d_zero B n A n (n+1))
  haveI : IsIso (S.homologyπ n) :=
    S.isIso_homologyπ (n-1) n (((ComplexShape.down ℤ).symm).prev_eq' (by change (n-1)+1=n; omega)) (dualSingle_d_zero B n A (n-1) n)
  exact (asIso (S.homologyπ n)).symm ≪≫ asIso (S.iCycles n) ≪≫
    (LinearEquiv.arrowCongr (singleObjXSelf (.down ℤ) n A).toLinearEquiv
      (LinearEquiv.refl R B)).toModuleIso

lemma dualSingleHomology_isZero (B : Type w) [AddCommGroup B] [Module R B]
    (n : ℤ) (A : ModuleCat.{v} R) (i : ℤ) (hi : i ≠ n) :
    IsZero ((dualSingle B n A).homology i) := by
  have hz : IsZero ((dualSingle B n A).X i) :=
    P202.CohomologyPairs.dual_isZero R B _ (isZero_single_obj_X (.down ℤ) n A i hi)
  exact ((dualSingle B n A).sc i).isZero_homology_of_isZero_X₂ hz

lemma dualSingleHomologyIso_class (B : Type w) [AddCommGroup B] [Module R B]
    (n : ℤ) (A : ModuleCat.{v} R) (a : (dualSingle B n A).cycles n) :
    (dualSingleHomologyIso B n A).hom ((dualSingle B n A).homologyπ n a) =
      LinearEquiv.arrowCongr (singleObjXSelf (.down ℤ) n A).toLinearEquiv
        (LinearEquiv.refl R B) ((dualSingle B n A).iCycles n a) := by
  haveI : IsIso ((dualSingle B n A).homologyπ n) :=
    (dualSingle B n A).isIso_homologyπ (n-1) n
      (((ComplexShape.down ℤ).symm).prev_eq' (by change (n-1)+1=n; omega))
      (dualSingle_d_zero B n A (n-1) n)
  change LinearEquiv.arrowCongr (singleObjXSelf (.down ℤ) n A).toLinearEquiv
    (LinearEquiv.refl R B) ((dualSingle B n A).iCycles n
      ((asIso ((dualSingle B n A).homologyπ n)).inv
        ((asIso ((dualSingle B n A).homologyπ n)).hom a))) = _
  rw [Iso.hom_inv_id_apply]

def cohomologyEvaluation (B : Type w) [AddCommGroup B] [Module R B]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    {A : ModuleCat.{v} R} (c : A ⟶ K.cycles n) :
    ((dualComplexFunctor R B (.down ℤ)).obj (op K)).homology n →ₗ[R] (A →ₗ[R] B) :=
  (homologyMap ((dualComplexFunctor R B (.down ℤ)).map (fromSingleCycles K n c).op) n ≫
    (dualSingleHomologyIso B n A).hom).hom

lemma cohomologyEvaluation_bijective
    (B : Type w) [AddCommGroup B] [Module R B]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    {A : ModuleCat.{v} R} [Module.Free R A]
    [∀ i, Module.Free R (K.X i)]
    (hK : P202Specs.FreeChainDual.BoundedBelow K)
    (c : A ⟶ K.cycles n) [IsIso (c ≫ K.homologyπ n)]
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) :
    Function.Bijective (cohomologyEvaluation B K n c) := by
  haveI := dualFromSingleCycles_quasiIso B K n hK c h
  exact (asIso (homologyMap ((dualComplexFunctor R B (.down ℤ)).map
    (fromSingleCycles K n c).op) n ≫ (dualSingleHomologyIso B n A).hom)).toLinearEquiv.bijective

lemma cohomologyEvaluation_class
    (B : Type w) [AddCommGroup B] [Module R B]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    {A : ModuleCat.{v} R} (c : A ⟶ K.cycles n)
    (a : ((dualComplexFunctor R B (.down ℤ)).obj (op K)).cycles n) :
    cohomologyEvaluation B K n c
      (((dualComplexFunctor R B (.down ℤ)).obj (op K)).homologyπ n a) =
      (((dualComplexFunctor R B (.down ℤ)).obj (op K)).iCycles n a).comp
        (c ≫ K.iCycles n).hom := by
  let f := (dualComplexFunctor R B (.down ℤ)).map (fromSingleCycles K n c).op
  change (dualSingleHomologyIso B n A).hom
    (homologyMap f n (((dualComplexFunctor R B (.down ℤ)).obj (op K)).homologyπ n a)) = _
  have hn := congrArg (fun g => g a) (homologyπ_naturality f n)
  change homologyMap f n
    (((dualComplexFunctor R B (.down ℤ)).obj (op K)).homologyπ n a) =
      (dualSingle B n A).homologyπ n (cyclesMap f n a) at hn
  rw [hn, dualSingleHomologyIso_class]
  have he := congrArg (fun g => g a) (cyclesMap_i f n)
  change (dualSingle B n A).iCycles n (cyclesMap f n a) =
    f.f n (((dualComplexFunctor R B (.down ℤ)).obj (op K)).iCycles n a) at he
  rw [he]
  ext x
  change (show K.X n →ₗ[R] B from
      ((dualComplexFunctor R B (.down ℤ)).obj (op K)).iCycles n a)
    ((fromSingleCycles K n c).f n ((singleObjXSelf (.down ℤ) n A).inv x)) = _
  rw [fromSingleCycles, mkHomFromSingle_f]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply]
  rfl

def scalarCycle (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ)
    (z : K.cycles n) : ModuleCat.of R (ULift.{v} R) ⟶ K.cycles n :=
  ModuleCat.ofHom ((LinearMap.toSpanSingleton R _ z).comp
    (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R).toLinearMap)

def liftedScalarDualEquiv : (ULift.{v} R →ₗ[R] R) ≃ₗ[R] R :=
  (LinearEquiv.arrowCongr (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R)
    (LinearEquiv.refl R R)).trans (LinearMap.ringLmapEquivSelf R R R)

def scalarCohomologyEvaluation (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ)
    (z : K.cycles n) :
    ((dualComplexFunctor R R (.down ℤ)).obj (op K)).homology n →ₗ[R] R :=
  (liftedScalarDualEquiv (R := R)).toLinearMap.comp
    (cohomologyEvaluation R K n (scalarCycle K n z))

lemma scalarCohomologyEvaluation_bijective
    (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ)
    [∀ i, Module.Free R (K.X i)]
    (hK : P202Specs.FreeChainDual.BoundedBelow K) (z : K.cycles n)
    (hz : Function.Bijective (fun r : R => r • K.homologyπ n z))
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i)) :
    Function.Bijective (scalarCohomologyEvaluation K n z) := by
  have he : scalarCycle K n z ≫ K.homologyπ n =
      ModuleCat.ofHom ((LinearMap.toSpanSingleton R _ (K.homologyπ n z)).comp
        (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R).toLinearMap) := by
    apply ModuleCat.hom_ext
    ext r
    exact map_smul (K.homologyπ n).hom r.down z
  haveI : IsIso (scalarCycle K n z ≫ K.homologyπ n) := by
    rw [he]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr
      (hz.comp (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R).bijective)
  exact (liftedScalarDualEquiv (R := R)).bijective.comp
    (cohomologyEvaluation_bijective R K n hK (scalarCycle K n z) h)

lemma scalarCohomologyEvaluation_class
    (K : ChainComplex (ModuleCat.{max u v} R) ℤ) (n : ℤ)
    (z : K.cycles n)
    (a : ((dualComplexFunctor R R (.down ℤ)).obj (op K)).cycles n) :
    scalarCohomologyEvaluation K n z
      (((dualComplexFunctor R R (.down ℤ)).obj (op K)).homologyπ n a) =
      (show K.X n →ₗ[R] R from
        ((dualComplexFunctor R R (.down ℤ)).obj (op K)).iCycles n a)
        (K.iCycles n z) := by
  change liftedScalarDualEquiv
    (cohomologyEvaluation R K n (scalarCycle K n z)
      (((dualComplexFunctor R R (.down ℤ)).obj (op K)).homologyπ n a)) = _
  rw [cohomologyEvaluation_class]
  simp [liftedScalarDualEquiv, scalarCycle, LinearEquiv.arrowCongr_apply]

lemma dualCohomology_isZero
    (B : Type w) [AddCommGroup B] [Module R B]
    (K : ChainComplex (ModuleCat.{v} R) ℤ) (n : ℤ)
    {A : ModuleCat.{v} R} [Module.Free R A]
    [∀ i, Module.Free R (K.X i)]
    (hK : P202Specs.FreeChainDual.BoundedBelow K)
    (c : A ⟶ K.cycles n) [IsIso (c ≫ K.homologyπ n)]
    (h : ∀ i : ℤ, i ≠ n → IsZero (K.homology i))
    (i : ℤ) (hi : i ≠ n) :
    IsZero (((dualComplexFunctor R B (.down ℤ)).obj (op K)).homology i) := by
  haveI := dualFromSingleCycles_quasiIso B K n hK c h
  exact (asIso (homologyMap ((dualComplexFunctor R B (.down ℤ)).map
    (fromSingleCycles K n c).op) i)).isZero_iff.mpr
      (dualSingleHomology_isZero B n A i hi)

end ConcentratedChains

section OpenInduction
open Set TopologicalSpace
/-- A local-to-global principle using a countable basis closed under
intersections, finite Mayer--Vietoris gluing, and increasing open unions.
Neither the space nor the open set is assumed nonempty. -/
theorem open_of_countable_inter_basis
    {X : Type u} [TopologicalSpace X]
    (P : Set X → Prop) (B : Set (Set X))
    (hB : IsTopologicalBasis B) (hBc : B.Countable)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B)
    (hempty : P ∅) (hbasis : ∀ U ∈ B, P U)
    (hunion : ∀ U V, IsOpen U → IsOpen V →
      P U → P V → P (U ∩ V) → P (U ∪ V))
    (hincreasing : ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) →
      Monotone U → (∀ n, P (U n)) → P (⋃ n, U n))
    {s : Set X} (hs : IsOpen s) : P s := by
  classical
  have basic_open (U : Set X) (hU : U = ∅ ∨ U ∈ B) : IsOpen U := by
    rcases hU with rfl | hU
    · exact isOpen_empty
    · exact hB.isOpen hU
  have basic_good (U : Set X) (hU : U = ∅ ∨ U ∈ B) : P U := by
    rcases hU with rfl | hU
    · exact hempty
    · exact hbasis U hU
  have finite_good : ∀ (n : ℕ) (F : Fin n → Set X),
      (∀ i, F i = ∅ ∨ F i ∈ B) → P (⋃ i, F i) := by
    intro n
    induction n with
    | zero =>
      intro F _
      simpa only [iUnion_of_empty] using hempty
    | succ n ih =>
      intro F hF
      have ht : P (⋃ i : Fin n, F i.succ) := ih _ (fun i => hF i.succ)
      have hi : P (F 0 ∩ ⋃ i : Fin n, F i.succ) := by
        rw [inter_iUnion]
        apply ih
        intro i
        rcases hF 0 with hzero | hzero
        · exact Or.inl (by rw [hzero, empty_inter])
        rcases hF i.succ with hi | hi
        · exact Or.inl (by rw [hi, inter_empty])
        · exact Or.inr (hinter _ hzero _ hi)
      have he : (⋃ i : Fin (n+1), F i) = F 0 ∪ ⋃ i : Fin n, F i.succ := by
        ext x
        simp only [mem_iUnion, mem_union, Fin.exists_fin_succ]
      rw [he]
      exact hunion _ _ (basic_open _ (hF 0))
        (isOpen_iUnion (fun i => basic_open _ (hF i.succ)))
        (basic_good _ (hF 0)) ht hi
  let S : Set (Set X) := {U ∈ B | U ⊆ s}
  have hSc : S.Countable := hBc.mono (fun _ h => h.1)
  let e : ℕ → Set X := enumerateCountable hSc ∅
  have he (n : ℕ) : e n = ∅ ∨ e n ∈ B := by
    have h := range_enumerateCountable_subset hSc ∅ ⟨n, rfl⟩
    exact (mem_insert_iff.mp h).imp_right (fun h => h.1)
  have hcover : (⋃ n, e n) = s := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      have h := range_enumerateCountable_subset hSc ∅ ⟨n, rfl⟩
      rcases mem_insert_iff.mp h with he | he
      · change x ∈ enumerateCountable hSc ∅ n at hn
        rw [he] at hn
        exact hn.elim
      · exact he.2 hn
    · intro x hx
      obtain ⟨U, hUB, hxU, hUs⟩ := hB.exists_subset_of_mem_open hx hs
      obtain ⟨n, hn⟩ := subset_range_enumerate hSc ∅ (show U ∈ S from ⟨hUB, hUs⟩)
      exact mem_iUnion.mpr ⟨n, (show e n = U from hn).symm ▸ hxU⟩
  have hacc (n : ℕ) : accumulate e n = ⋃ i : Fin (n+1), e i := by
    ext x
    simp only [mem_accumulate, mem_iUnion]
    constructor
    · rintro ⟨i, hi, hxi⟩
      exact ⟨⟨i, by omega⟩, hxi⟩
    · rintro ⟨i, hxi⟩
      exact ⟨i, by omega, hxi⟩
  have hgood : P (⋃ n, accumulate e n) := by
    apply hincreasing
    · intro n
      exact isOpen_iUnion (fun i => isOpen_iUnion (fun _ => basic_open _ (he i)))
    · exact monotone_accumulate (s := e)
    · intro n
      rw [hacc]
      exact finite_good _ _ (fun i => he i)
  rw [iUnion_accumulate, hcover] at hgood
  exact hgood

end OpenInduction

namespace DegreeZero
set_option maxHeartbeats 1000000
open P202Specs.SingularChains P202Specs.SingularDegreeZero
variable (R : Type u) [CommRing R]

def componentSumEquiv (X : TopCat.{v}) [PathConnectedSpace X] :
    ComponentSums R X ≃ₗ[R] R := by
  let i : ZerothHomotopy X := Classical.choice inferInstance
  letI : Unique (ZerothHomotopy X) := ⟨⟨i⟩, fun j => Subsingleton.elim _ _⟩
  exact Finsupp.uniqueLinearEquiv R R i

lemma componentSumEquiv_apply (X : TopCat.{v}) [PathConnectedSpace X]
    (c : ComponentSums R X) : componentSumEquiv R X c = componentSum R R X c := by
  dsimp [componentSumEquiv]
  symm
  exact P202.SingularDegreeZero.sumCoefficients_eq_eval R R (ZerothHomotopy X) c _

def nonnegativeHomologyZeroIso (X : TopCat.{v}) :
    (complex R R X).homology 0 ≅ ModuleCat.of R (ComponentSums R X) :=
  (complex R R X).isoHomologyι₀ ≪≫
    ((complex R R X).opcyclesIsCokernel 1 0 ((ComplexShape.down ℕ).prev_eq' (by simp))).coconePointUniqueUpToIso
      (P202.SingularDegreeZero.componentProjectionIsCokernel R R X)

lemma nonnegativeHomologyZeroIso_class (X : TopCat.{v})
    (z : (complex R R X).cycles 0) :
    (nonnegativeHomologyZeroIso R X).hom ((complex R R X).homologyπ 0 z) =
      P202.SingularDegreeZero.componentProjection R R X ((complex R R X).iCycles 0 z) := by
  let K := complex R R X
  have hπ : K.homologyπ 0 ≫ (nonnegativeHomologyZeroIso R X).hom =
      K.iCycles 0 ≫ P202.SingularDegreeZero.componentProjection R R X := by
    dsimp only [nonnegativeHomologyZeroIso, Iso.trans_hom]
    rw [← Category.assoc]
    change (K.homologyπ 0 ≫ K.homologyι 0) ≫ _ = _
    rw [HomologicalComplex.homology_π_ι, Category.assoc]
    congr 1
    exact IsColimit.comp_coconePointUniqueUpToIso_hom
      (K.opcyclesIsCokernel 1 0 ((ComplexShape.down ℕ).prev_eq' (by simp)))
      (P202.SingularDegreeZero.componentProjectionIsCokernel R R X) WalkingParallelPair.one
  exact congrArg (fun f => f z) hπ

def augmentationH0Equiv (X : TopCat.{v}) [PathConnectedSpace X] :
    homology R R X 0 ≃ₗ[R] R :=
  ((complex R R X).extendHomologyIso (degreeEmbedding 0) (j := 0) rfl).toLinearEquiv.trans
    ((nonnegativeHomologyZeroIso R X).toLinearEquiv.trans (componentSumEquiv R X))

lemma augmentationH0Equiv_class (X : TopCat.{v}) [PathConnectedSpace X]
    (z : (ordinaryComplex R R X).cycles 0) :
    augmentationH0Equiv R X ((ordinaryComplex R R X).homologyπ 0 z) =
      augmentationLinear R R X
        ((ordinaryNonnegativeIso R R X 0).hom ((ordinaryComplex R R X).iCycles 0 z)) := by
  let K := complex R R X
  let e := K.extendCyclesIso (degreeEmbedding 0) (j := 0) (by rfl)
  have hn := congrArg (fun f => f z)
    (K.homologyπ_extendHomologyIso_hom (degreeEmbedding 0) (j := 0) (by rfl))
  change (K.extendHomologyIso (degreeEmbedding 0) (j := 0) (by rfl)).hom
      ((ordinaryComplex R R X).homologyπ 0 z) = K.homologyπ 0 (e.hom z) at hn
  change componentSumEquiv R X
    ((nonnegativeHomologyZeroIso R X).hom
      ((K.extendHomologyIso (degreeEmbedding 0) (j := 0) (by rfl)).hom
        ((ordinaryComplex R R X).homologyπ 0 z))) = _
  rw [hn, nonnegativeHomologyZeroIso_class, componentSumEquiv_apply]
  have hs := congrArg (fun f => ULift.down (f (K.iCycles 0 (e.hom z))))
    (P202.SingularDegreeZero.componentProjection_sum R R X)
  change componentSum R R X
    (P202.SingularDegreeZero.componentProjection R R X (K.iCycles 0 (e.hom z))) =
      augmentationLinear R R X (K.iCycles 0 (e.hom z)) at hs
  rw [hs]
  congr 1
  have hc := congrArg (fun f => f z)
    (K.extendCyclesIso_hom_iCycles (degreeEmbedding 0) (j := 0) (by rfl))
  exact hc

lemma augmentation_capAt (X : TopCat.{v}) (n : ℕ)
    (a : P202Specs.CupProduct.Cochain R X n) (c : Chains R X n) :
    augmentationLinear R R X
      (P202Specs.CapProducts.capAt R X n n 0 (by omega) a c) = a c := by
  have he : (augmentationLinear R R X).comp
      (P202Specs.CapProducts.capAt R X n n 0 (by omega) a) = a := by
    apply (Finsupp.basisSingleOne : Module.Basis _ R (Chains R X n)).ext
    intro s
    simp [LinearMap.comp_apply, P202.CapProducts.capAt_single,
      P202.SingularChains.augmentationLinear_single, P202.AlexanderWhitney.interval_self]
  exact LinearMap.congr_fun he c

lemma augmentation_cap (X : TopCat.{v}) (n : ℕ)
    (a : P202Specs.CupProduct.Cochain R X n)
    (c : (ordinaryComplex R R X).X (n : ℤ)) :
    augmentationLinear R R X ((ordinaryNonnegativeIso R R X 0).hom
      (P202Specs.CapProducts.castOrdinary R (by omega : (n : ℤ)-n=0)
        (P202Specs.CapProducts.cap R X n (n : ℤ) a c))) =
      a ((ordinaryNonnegativeIso R R X n).hom c) := by
  erw [P202.CapProducts.cap_nonnegative R X n n 0 (by omega)]
  rw [Iso.inv_hom_id_apply]
  exact augmentation_capAt R X n a _

def homologyCast (X : TopCat.{v}) (i j : ℤ) (h : i=j) :
    homology R R X i →ₗ[R] homology R R X j := by
  subst j
  exact LinearMap.id

lemma augmentationH0Equiv_cast_class (X : TopCat.{v}) [PathConnectedSpace X]
    (i : ℤ) (hi : i=0) (z : (ordinaryComplex R R X).cycles i) :
    augmentationH0Equiv R X
      (homologyCast R X i 0 hi ((ordinaryComplex R R X).homologyπ i z)) =
      augmentationLinear R R X ((ordinaryNonnegativeIso R R X 0).hom
        (P202Specs.CapProducts.castOrdinary R hi ((ordinaryComplex R R X).iCycles i z))) := by
  subst i
  exact augmentationH0Equiv_class R X z

open P202Specs.RelativeSingularChains P202Specs.LocalOrientation
open P202Specs.CohomologyPairs P202Specs.CompactSupport

lemma duality_supported_top_augmentation
    (d : DualityData.{u,v} R) (n : ℕ) (M : Type v) [TopologicalSpace M]
    [PathConnectedSpace M] (A : Manifold n M) (o : Orientation R A)
    (K : Support M) (a : (supportedCochains R M K).cycles (n : ℤ))
    (z : (ordinary R R (supportedPair M K)).cycles (n : ℤ))
    (c : (ordinaryComplex R R (TopCat.of M)).X (n : ℤ))
    (hc : (projection (ordinaryFunctor R R) (supportedPair M K)).f (n : ℤ) c =
      (ordinary R R (supportedPair M K)).iCycles (n : ℤ) z)
    (hμ : P202Specs.CompactOrientation.HasLocalValues R o.val K
      ((ordinary R R (supportedPair M K)).homologyπ (n : ℤ) z)) :
    augmentationH0Equiv R (TopCat.of M)
      (homologyCast R (TopCat.of M) ((n : ℤ)-n) 0 (by omega)
        (d.D n M A o (n : ℤ)
          (ofSupport R M (n : ℤ) K ((supportedCochains R M K).homologyπ (n : ℤ) a)))) =
      (show (ordinary R R (supportedPair M K)).X (n : ℤ) →ₗ[R] R from
        (supportedCochains R M K).iCycles (n : ℤ) a)
        ((ordinary R R (supportedPair M K)).iCycles (n : ℤ) z) := by
  obtain ⟨w, hw, hD⟩ := d.represents n M A o n K a z c hc hμ
  rw [hD, augmentationH0Equiv_cast_class]
  rw [hw]
  rw [augmentation_cap]
  change (show (ordinaryComplex R R (TopCat.of M)).X (n : ℤ) →ₗ[R] R from
    (cochainInclusion R M K).f (n : ℤ) ((supportedCochains R M K).iCycles (n : ℤ) a))
      ((ordinaryNonnegativeIso R R (TopCat.of M) n).inv
        ((ordinaryNonnegativeIso R R (TopCat.of M) n).hom c)) = _
  rw [Iso.hom_inv_id_apply]
  change (show (ordinary R R (supportedPair M K)).X (n : ℤ) →ₗ[R] R from
    (supportedCochains R M K).iCycles (n : ℤ) a)
      ((projection (ordinaryFunctor R R) (supportedPair M K)).f (n : ℤ) c) = _
  rw [hc]

end DegreeZero

namespace BallCalculation
section GeneralSupport
variable (M : Type v) [TopologicalSpace M]

/-- Concentration near any compact that restricts isomorphically to one
local point. The premise refers to the original relative pair maps. -/
lemma supported_homology_concentrated {n : ℕ} (A : Manifold n M)
    (K : Support M) (x : M) (hx : x ∈ K)
    (hpoint : ∀ q : ℤ, IsIso ((relativeHomologyFunctor R R q).map (pointMap hx)))
    (q : ℤ) (hq : q ≠ (n : ℤ)) :
    IsZero (relativeHomology R R (supportedPair M K) q) := by
  cases q with
  | ofNat q =>
    haveI := hpoint (q : ℤ)
    exact ((P202.LocalOrientation.localHomology R n M A x q).2
      (by intro heq; exact hq (congrArg (fun k : ℕ => (k : ℤ)) heq))).of_iso
        (asIso ((relativeHomologyFunctor R R (q : ℤ)).map (pointMap hx)))
  | negSucc q =>
    exact (P202.RelativeSingularChains.ordinary_negative R R (supportedPair M K) _ (by omega)).2

/-- The compact fundamental class is a generator whenever its restriction
to one point is an isomorphism. -/
lemma fundamentalClass_generator {n : ℕ} (A : Manifold n M) (o : Orientation R A)
    (K : Support M) (x : M) (hx : x ∈ K)
    (hpoint : IsIso ((relativeHomologyFunctor R R (n : ℤ)).map (pointMap hx))) :
    IsGenerator R (P202.CompactSupport.fundamentalClass R M A o K) := by
  haveI := hpoint
  let e := (asIso ((relativeHomologyFunctor R R (n : ℤ)).map (pointMap hx))).toLinearEquiv
  apply (P202.LocalOrientation.generator_map_iff R e _).mp
  change IsGenerator R (restrictPoint R hx n (P202.CompactSupport.fundamentalClass R M A o K))
  rw [P202.CompactSupport.fundamentalClass_values R M A o K x hx]
  exact o.property.1 x

end GeneralSupport

/-- Every chain module of the actual integer-graded relative singular
complex is free, including its zero modules in negative degrees. -/
lemma ordinaryPair_free (P : Pair.{v}) (q : ℤ) : Module.Free R ((ordinary R R P).X q) := by
  cases q with
  | ofNat q =>
    obtain ⟨b, _⟩ := P202.RelativeSingularChains.quotient_basis R P q
    haveI := Module.Free.of_basis b
    exact Module.Free.of_equiv (ordinaryDegreeIso R R P q).symm.toLinearEquiv
  | negSucc q =>
    haveI : Subsingleton ((ordinary R R P).X (Int.negSucc q)) :=
      ModuleCat.subsingleton_of_isZero
        (P202.RelativeSingularChains.ordinary_negative R R P _ (by omega)).1
    infer_instance

/-- The same relative complex vanishes in all negative chain degrees. -/
lemma ordinaryPair_boundedBelow (P : Pair.{v}) :
    P202Specs.FreeChainDual.BoundedBelow (ordinary R R P) := by
  exact ⟨0, fun q hq => (P202.RelativeSingularChains.ordinary_negative R R P q hq).1⟩

end BallCalculation

/-- Ordinary finite-chain homology of a nonempty contractible space vanishes
away from degree zero, including every negative integer degree. -/
lemma ordinary_contractible_other
    (X : Type v) [TopologicalSpace X] [Nonempty X] [ContractibleSpace X]
    (q : ℤ) (hq : q ≠ 0) : IsZero (homology R R (TopCat.of X) q) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  let p : TopCat.of X ⟶ P202Specs.SingularDegreeZero.point.{v} :=
    TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let g : P202Specs.SingularDegreeZero.point.{v} ⟶ TopCat.of X :=
    TopCat.ofHom (ContinuousMap.const _ x)
  have hpg : TopCat.Homotopy (p ≫ g) (𝟙 (TopCat.of X)) := H.symm
  have hgp : TopCat.Homotopy (g ≫ p) (𝟙 _) := ContinuousMap.Homotopy.refl _
  haveI := (P202.PrismHomotopy.homologyIso R R p g hpg hgp q).1
  exact (asIso ((homologyFunctor R R q).map p)).isZero_iff.mpr
    (P202.SingularDegreeZero.pointOrdinaryOther R R q hq)

/-- A homeomorphism preserving the support transports the actual point
restriction isomorphism, with the original maps of pairs. -/
lemma pointMap_isIso_of_homeomorph
    {X E : Type v} [TopologicalSpace X] [TopologicalSpace E]
    (e : X ≃ₜ E) (K : Set X) (L : Set E)
    (h : ∀ x, x ∈ K ↔ e x ∈ L) {x : X} (hx : x ∈ K) (q : ℤ)
    (hpoint : IsIso ((relativeHomologyFunctor R R q).map
      (pointMap ((h x).mp hx)))) :
    IsIso ((relativeHomologyFunctor R R q).map (pointMap hx)) := by
  let F := relativeHomologyFunctor R R q
  let a := P202.LocalOrientation.supportedPairIsoOfHomeomorph e K L h
  let b := P202.LocalOrientation.localPairIsoOfHomeomorph e x
  have he := congrArg F.map
    (P202.LocalOrientation.supportedPairIso_point_square e K L h hx)
  simp only [Functor.map_comp] at he
  haveI := hpoint
  haveI : IsIso (F.map (pointMap hx) ≫ F.map b.hom) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (F.map b.hom)

/-- Compact supports in a space homeomorphic to a proper real normed space
have cofinally many nonempty supports on which every point restriction is an
isomorphism in every integer degree. They are preimages of closed balls. -/
theorem cofinal_supports_pointMap_isIso
    (X : Type v) [TopologicalSpace X]
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (e : X ≃ₜ E) (K : Support X) :
    ∃ L : Support X, K ≤ L ∧ (L : Set X).Nonempty ∧
      ∀ (x : X) (hx : x ∈ (L : Set X)) (q : ℤ),
        IsIso ((relativeHomologyFunctor R R q).map (pointMap hx)) := by
  have hb : Bornology.IsBounded (e '' (K : Set X)) :=
    (K.isCompact.image e.continuous).isBounded
  obtain ⟨r, hr, hKr⟩ := hb.subset_closedBall_lt 0 (0 : E)
  let L : Support X := ⟨e ⁻¹' Metric.closedBall (0 : E) r,
    e.isCompact_preimage.mpr (isCompact_closedBall _ _)⟩
  have hKL : K ≤ L := fun x hx => hKr ⟨x, hx, rfl⟩
  have hx₀ : e.symm 0 ∈ (L : Set X) := by
    change e (e.symm 0) ∈ Metric.closedBall (0 : E) r
    rw [e.apply_symm_apply]
    exact Metric.mem_closedBall_self hr.le
  refine ⟨L, hKL, ⟨e.symm 0, hx₀⟩, ?_⟩
  intro x hx q
  apply pointMap_isIso_of_homeomorph R e (L : Set X)
    (Metric.closedBall (0 : E) r) (fun _ => Iff.rfl) hx q
  exact P202.LocalOrientation.closedBall_pointMap_isIso R R hx q

/-- The universe-lifted finite Euclidean model has the cofinal support
property used in the local compact-support calculation, including n=0. -/
lemma euclidean_cofinal_supports_pointMap_isIso
    {n : ℕ} (X : Type v) [TopologicalSpace X]
    (e : X ≃ₜ ULift.{v} (Fin n → ℝ)) (K : Support X) :
    ∃ L : Support X, K ≤ L ∧ (L : Set X).Nonempty ∧
      ∀ (x : X) (hx : x ∈ (L : Set X)) (q : ℤ),
        IsIso ((relativeHomologyFunctor R R q).map (pointMap hx)) :=
  cofinal_supports_pointMap_isIso R X (ULift.{v} (Fin n → ℝ)) e K


section LocalCalculation
set_option maxHeartbeats 1000000
lemma supported_duality_of_pointMap_iso
    (d : DualityData.{u,v} R) {n : ℕ} (M : Type v) [TopologicalSpace M]
    [Nonempty M] [ContractibleSpace M]
    (A : Manifold n M) (o : Orientation R A) (K : Support M)
    (x : M) (hx : x ∈ K)
    (hpoint : ∀ q : ℤ, IsIso ((relativeHomologyFunctor R R q).map (pointMap hx)))
    (p : ℤ) :
    Function.Bijective ((d.D n M A o p).comp (ofSupport R M p K)) := by
  let C := ordinary R R (supportedPair M K)
  let μ := P202.CompactSupport.fundamentalClass R M A o K
  obtain ⟨z, hz⟩ : ∃ z : C.cycles (n : ℤ), C.homologyπ (n : ℤ) z = μ :=
    (ModuleCat.epi_iff_surjective (C.homologyπ (n : ℤ))).mp inferInstance μ
  have hgen : Function.Bijective (fun r : R => r • C.homologyπ (n : ℤ) z) := by
    rw [hz]
    exact BallCalculation.fundamentalClass_generator R M A o K x hx (hpoint (n : ℤ))
  have hcon : ∀ q : ℤ, q ≠ (n : ℤ) → IsZero (C.homology q) :=
    BallCalculation.supported_homology_concentrated R M A K x hx hpoint
  haveI : ∀ q, Module.Free R (C.X q) :=
    BallCalculation.ordinaryPair_free R (supportedPair M K)
  have hbound : P202Specs.FreeChainDual.BoundedBelow C :=
    BallCalculation.ordinaryPair_boundedBelow R (supportedPair M K)
  by_cases hp : p = (n : ℤ)
  · subst p
    have hcast : Function.Bijective
        (DegreeZero.homologyCast R (TopCat.of M) ((n : ℤ)-n) 0 (by omega)) := by
      have hc : ∀ (q : ℤ) (he : q=0),
          Function.Bijective (DegreeZero.homologyCast R (TopCat.of M) q 0 he) := by
        intro q he
        subst q
        exact Function.bijective_id
      exact hc _ _
    have hnorm : Function.Bijective
        (fun a : supportedCohomology R M (n : ℤ) K =>
          DegreeZero.augmentationH0Equiv R (TopCat.of M)
            (DegreeZero.homologyCast R (TopCat.of M) ((n : ℤ)-n) 0 (by omega)
              (d.D n M A o (n : ℤ) (ofSupport R M (n : ℤ) K a)))) := by
      have he : (fun a : supportedCohomology R M (n : ℤ) K =>
          DegreeZero.augmentationH0Equiv R (TopCat.of M)
            (DegreeZero.homologyCast R (TopCat.of M) ((n : ℤ)-n) 0 (by omega)
              (d.D n M A o (n : ℤ) (ofSupport R M (n : ℤ) K a)))) =
          ConcentratedChains.scalarCohomologyEvaluation C (n : ℤ) z := by
        funext a₀
        obtain ⟨a, rfl⟩ :=
          (ModuleCat.epi_iff_surjective ((supportedCochains R M K).homologyπ (n : ℤ))).mp
            inferInstance a₀
        obtain ⟨c, hc⟩ := P202.CapProducts.projection_surjective R (supportedPair M K)
          (n : ℤ) (C.iCycles (n : ℤ) z)
        have hμ : P202Specs.CompactOrientation.HasLocalValues R o.val K
            (C.homologyπ (n : ℤ) z) := by
          rw [hz]
          exact P202.CompactSupport.fundamentalClass_values R M A o K
        rw [DegreeZero.duality_supported_top_augmentation R d n M A o K a z c hc hμ]
        exact (ConcentratedChains.scalarCohomologyEvaluation_class C (n : ℤ) z a).symm
      rw [he]
      exact ConcentratedChains.scalarCohomologyEvaluation_bijective C (n : ℤ) hbound z hgen hcon
    have hpost : Function.Bijective (fun b : homology R R (TopCat.of M) ((n : ℤ)-n) =>
      DegreeZero.augmentationH0Equiv R (TopCat.of M)
        (DegreeZero.homologyCast R (TopCat.of M) ((n : ℤ)-n) 0 (by omega) b)) :=
      (DegreeZero.augmentationH0Equiv R (TopCat.of M)).bijective.comp hcast
    exact (Function.Bijective.of_comp_iff' hpost _).mp hnorm
  · let c₀ := ConcentratedChains.scalarCycle C (n : ℤ) z
    have hc₀ : c₀ ≫ C.homologyπ (n : ℤ) =
        ModuleCat.ofHom ((LinearMap.toSpanSingleton R _ (C.homologyπ (n : ℤ) z)).comp
          (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R).toLinearMap) := by
      apply ModuleCat.hom_ext
      ext r
      exact map_smul (C.homologyπ (n : ℤ)).hom r.down z
    haveI : IsIso (c₀ ≫ C.homologyπ (n : ℤ)) := by
      rw [hc₀]
      exact (ConcreteCategory.isIso_iff_bijective _).mpr
        (hgen.comp (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R).bijective)
    have hsource : IsZero (supportedCohomology R M p K) :=
      ConcentratedChains.dualCohomology_isZero R C (n : ℤ) hbound c₀ hcon p hp
    have htarget : IsZero (homology R R (TopCat.of M) ((n : ℤ)-p)) :=
      ordinary_contractible_other R M _ (by omega)
    haveI := ModuleCat.subsingleton_of_isZero hsource
    haveI := ModuleCat.subsingleton_of_isZero htarget
    constructor
    · intro a b _; exact Subsingleton.elim _ _
    · intro b; exact ⟨0, Subsingleton.elim _ _⟩

lemma duality_of_homeomorphic_proper_normed
    (d : DualityData.{u,v} R) {n : ℕ} (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A)
    (E : Type v) [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (e : M ≃ₜ E) : Holds R M d A o := by
  letI : Nonempty M := ⟨e.symm 0⟩
  letI : ContractibleSpace M := e.contractibleSpace
  intro p
  apply duality_of_cofinal_supports R M d A o p
  intro K
  obtain ⟨L, hKL, ⟨x, hx⟩, hL⟩ := cofinal_supports_pointMap_isIso R M E e K
  exact ⟨L, hKL, supported_duality_of_pointMap_iso R d M A o L x hx (hL x hx) p⟩

lemma euclidean_duality
    (d : DualityData.{u,v} R) {n : ℕ} (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (o : Orientation R A)
    (e : M ≃ₜ ULift.{v} (Fin n → ℝ)) : Holds R M d A o :=
  duality_of_homeomorphic_proper_normed R d M A o (ULift.{v} (Fin n → ℝ)) e

end LocalCalculation

section OpenInductionGeneral
open Set TopologicalSpace
/-- A local-to-global principle in a second-countable space using a basis closed under
intersections, finite Mayer--Vietoris gluing, and increasing open unions.
Neither the space nor the open set is assumed nonempty. -/
theorem open_of_inter_basis
    {X : Type u} [TopologicalSpace X] [SecondCountableTopology X]
    (P : Set X → Prop) (B : Set (Set X))
    (hB : IsTopologicalBasis B)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B)
    (hempty : P ∅) (hbasis : ∀ U ∈ B, P U)
    (hunion : ∀ U V, IsOpen U → IsOpen V →
      P U → P V → P (U ∩ V) → P (U ∪ V))
    (hincreasing : ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) →
      Monotone U → (∀ n, P (U n)) → P (⋃ n, U n))
    {s : Set X} (hs : IsOpen s) : P s := by
  classical
  have basic_open (U : Set X) (hU : U = ∅ ∨ U ∈ B) : IsOpen U := by
    rcases hU with rfl | hU
    · exact isOpen_empty
    · exact hB.isOpen hU
  have basic_good (U : Set X) (hU : U = ∅ ∨ U ∈ B) : P U := by
    rcases hU with rfl | hU
    · exact hempty
    · exact hbasis U hU
  have finite_good : ∀ (n : ℕ) (F : Fin n → Set X),
      (∀ i, F i = ∅ ∨ F i ∈ B) → P (⋃ i, F i) := by
    intro n
    induction n with
    | zero =>
      intro F _
      simpa only [iUnion_of_empty] using hempty
    | succ n ih =>
      intro F hF
      have ht : P (⋃ i : Fin n, F i.succ) := ih _ (fun i => hF i.succ)
      have hi : P (F 0 ∩ ⋃ i : Fin n, F i.succ) := by
        rw [inter_iUnion]
        apply ih
        intro i
        rcases hF 0 with hzero | hzero
        · exact Or.inl (by rw [hzero, empty_inter])
        rcases hF i.succ with hi | hi
        · exact Or.inl (by rw [hi, inter_empty])
        · exact Or.inr (hinter _ hzero _ hi)
      have he : (⋃ i : Fin (n+1), F i) = F 0 ∪ ⋃ i : Fin n, F i.succ := by
        ext x
        simp only [mem_iUnion, mem_union, Fin.exists_fin_succ]
      rw [he]
      exact hunion _ _ (basic_open _ (hF 0))
        (isOpen_iUnion (fun i => basic_open _ (hF i.succ)))
        (basic_good _ (hF 0)) ht hi
  obtain ⟨S, hSB, hSc, hsS⟩ := hB.exists_countable_biUnion_of_isOpen hs
  let e : ℕ → Set X := enumerateCountable hSc ∅
  have he (n : ℕ) : e n = ∅ ∨ e n ∈ B := by
    have h := range_enumerateCountable_subset hSc ∅ ⟨n, rfl⟩
    exact (mem_insert_iff.mp h).imp_right (fun h => hSB h)
  have hcover : (⋃ n, e n) = s := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      have h := range_enumerateCountable_subset hSc ∅ ⟨n, rfl⟩
      rcases mem_insert_iff.mp h with he | he
      · change x ∈ enumerateCountable hSc ∅ n at hn
        rw [he] at hn
        exact hn.elim
      · rw [hsS]
        exact mem_iUnion.mpr ⟨e n, mem_iUnion.mpr ⟨he, hn⟩⟩
    · intro x hx
      rw [hsS] at hx
      obtain ⟨U, hxU⟩ := mem_iUnion.mp hx
      obtain ⟨hUS, hxU⟩ := mem_iUnion.mp hxU
      obtain ⟨n, hn⟩ := subset_range_enumerate hSc ∅ hUS
      exact mem_iUnion.mpr ⟨n, (show e n = U from hn).symm ▸ hxU⟩
  have hacc (n : ℕ) : accumulate e n = ⋃ i : Fin (n+1), e i := by
    ext x
    simp only [mem_accumulate, mem_iUnion]
    constructor
    · rintro ⟨i, hi, hxi⟩
      exact ⟨⟨i, by omega⟩, hxi⟩
    · rintro ⟨i, hxi⟩
      exact ⟨i, by omega, hxi⟩
  have hgood : P (⋃ n, accumulate e n) := by
    apply hincreasing
    · intro n
      exact isOpen_iUnion (fun i => isOpen_iUnion (fun _ => basic_open _ (he i)))
    · exact monotone_accumulate (s := e)
    · intro n
      rw [hacc]
      exact finite_good _ _ (fun i => he i)
  rw [iUnion_accumulate, hcover] at hgood
  exact hgood

/-- The bounded convex open subsets form an intersection-stable basis in
any real normed space. No finite-dimensional or nonemptiness assumption is needed. -/
lemma isTopologicalBasis_bounded_convex_open
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    IsTopologicalBasis {U : Set E | IsOpen U ∧ Convex ℝ U ∧ Bornology.IsBounded U} := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro U hU
    exact hU.1
  · intro x U hx hU
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
    exact ⟨Metric.ball x r, ⟨Metric.isOpen_ball, convex_ball _ _, Metric.isBounded_ball⟩,
      Metric.mem_ball_self hr, hball⟩

lemma bounded_convex_open_inter
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U V : Set E}
    (hU : IsOpen U ∧ Convex ℝ U ∧ Bornology.IsBounded U)
    (hV : IsOpen V ∧ Convex ℝ V ∧ Bornology.IsBounded V) :
    IsOpen (U ∩ V) ∧ Convex ℝ (U ∩ V) ∧ Bornology.IsBounded (U ∩ V) :=
  ⟨hU.1.inter hV.1, hU.2.1.inter hV.2.1, hU.2.2.subset inter_subset_left⟩

end OpenInductionGeneral

namespace Geometry
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonempty bounded convex open set is homeomorphic to its ambient real
normed space, including when that space has dimension zero. -/
lemma convexOpen_homeomorphic_space (U : Set E) (hU : IsOpen U)
    (hconvex : Convex ℝ U) (hbounded : Bornology.IsBounded U) (hne : U.Nonempty) :
    Nonempty (U ≃ₜ E) := by
  obtain ⟨e, he, _, _⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    hconvex (by simpa only [hU.interior_eq] using hne) hbounded
  have heU : e '' U = Metric.ball (0 : E) 1 := by
    simpa only [hU.interior_eq] using he
  exact ⟨((e.image U).trans (Homeomorph.setCongr heU)).trans
    (Homeomorph.unitBall : E ≃ₜ Metric.ball (0 : E) 1).symm⟩

end Geometry

section GlobalCalculation
set_option maxHeartbeats 1000000
/-- A subset of the target of a homeomorphism to a subspace is itself
homeomorphic to the corresponding preimage, with its original subtype. -/
def preimageSubsetHomeomorph
    {X : Type u} {M : Type v} [TopologicalSpace X] [TopologicalSpace M]
    {W U : Set M} (e : X ≃ₜ W) (h : U ⊆ W) :
    {x : X // (e x).val ∈ U} ≃ₜ U where
  toFun x := ⟨(e x.val).val, x.property⟩
  invFun y := ⟨e.symm ⟨y.val, h y.property⟩, by
    simpa only [e.apply_symm_apply] using y.property⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.val
  right_inv y := by
    apply Subtype.ext
    change (e (e.symm ⟨y.val, h y.property⟩)).val = y.val
    rw [e.apply_symm_apply]
  continuous_toFun :=
    (continuous_subtype_val.comp (e.continuous.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _


variable (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M]

/-- Duality on an open set, phrased invariantly so all inherited manifold
structures and orientations can be used without transporting their proof data. -/
def Good (d : DualityData.{u,v} R) (n : ℕ) (U : Set M) : Prop :=
  ∀ (X : Type v) [TopologicalSpace X] (A : Manifold n X) (o : Orientation R A),
    Nonempty (X ≃ₜ U) → Holds R X d A o

lemma good_empty (d : DualityData.{u,v} R) (n : ℕ) : Good R M d n ∅ := by
  intro X _ A o ⟨e⟩
  letI : IsEmpty X := ⟨fun x => (e x).property⟩
  exact empty_duality R X d A o

lemma good_homeomorph (d : DualityData.{u,v} R) (n : ℕ)
    {N : Type v} [TopologicalSpace N] (U : Set M) (V : Set N)
    (e : U ≃ₜ V) : Good R M d n U ↔ Good R N d n V := by
  constructor
  · intro h X _ A o ⟨f⟩
    exact h X A o ⟨f.trans e.symm⟩
  · intro h X _ A o ⟨f⟩
    exact h X A o ⟨f.trans e⟩

lemma good_union (hg : P202Specs.CompactSupportMayerVietoris.Expected.gluing.{u,v})
    (d : DualityData.{u,v} R) (n : ℕ) (U V : Set M) (hU : IsOpen U) (hV : IsOpen V)
    (hDU : Good R M d n U) (hDV : Good R M d n V)
    (hDI : Good R M d n (U ∩ V)) : Good R M d n (U ∪ V) := by
  intro X _ A o ⟨e⟩
  letI : T2Space X := A.hausdorff
  let C : Cover X :=
    { left := {x : X | (e x).val ∈ U}
      right := {x : X | (e x).val ∈ V}
      left_open := hU.preimage (continuous_subtype_val.comp e.continuous)
      right_open := hV.preimage (continuous_subtype_val.comp e.continuous)
      covers := Set.eq_univ_of_forall (fun x => (e x).property) }
  obtain ⟨G⟩ := hg R d n X A o C
  apply twoSet R X d A o C G
  · exact hDU C.left G.leftManifold G.leftOrientation
      ⟨preimageSubsetHomeomorph e Set.subset_union_left⟩
  · exact hDV C.right G.rightManifold G.rightOrientation
      ⟨preimageSubsetHomeomorph e Set.subset_union_right⟩
  · exact hDI C.intersection G.intersectionManifold G.intersectionOrientation
      ⟨preimageSubsetHomeomorph e (Set.inter_subset_left.trans Set.subset_union_left)⟩

lemma good_increasing_union
    (hg : P202Specs.CompactSupportMayerVietoris.Expected.gluing.{u,v})
    (d : DualityData.{u,v} R) (n : ℕ) (U : ℕ → Set M)
    (hU : ∀ i, IsOpen (U i)) (hmono : Monotone U)
    (hD : ∀ i, Good R M d n (U i)) : Good R M d n (⋃ i, U i) := by
  intro X _ A o ⟨e⟩
  letI : T2Space X := A.hausdorff
  let W (i : ℕ) : Set X := {x : X | (e x).val ∈ U i}
  have hW : ∀ i, IsOpen (W i) := fun i =>
    (hU i).preimage (continuous_subtype_val.comp e.continuous)
  have hWmono : Monotone W := fun _ _ hij _ hx => hmono hij hx
  have hWcover : ⋃ i, W i = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (e x).property
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  let C (i : ℕ) : Cover X :=
    { left := W i
      right := Set.univ
      left_open := hW i
      right_open := isOpen_univ
      covers := Set.union_univ _ }
  let G (i : ℕ) := Classical.choice (hg R d n X A o (C i))
  apply increasingUnion R X d A o W hW hWmono hWcover
    (fun i => (G i).leftManifold) (fun i => (G i).leftOrientation)
    (fun i => (G i).left_compatible)
  intro i
  exact hD i (W i) (G i).leftManifold (G i).leftOrientation
    ⟨preimageSubsetHomeomorph e (Set.subset_iUnion U i)⟩

namespace Geometry
open Set TopologicalSpace
open P202Specs.LocalOrientation

variable {M : Type v} [TopologicalSpace M]

/-- Any open set contained in a chart is homeomorphic to an open set in
the Euclidean coordinate model, in the original carrier's universe. -/
lemma chartOpen_homeomorphic_euclideanOpen {n : ℕ} (c : Chart n M)
    (U : Set M) (hU : IsOpen U) (hUc : U ⊆ c.source) :
    ∃ W : Set (ULift.{v} (Fin n → ℝ)), IsOpen W ∧ Nonempty (U ≃ₜ W) := by
  let e := c.transHomeomorph (P202.LocalOrientation.coordinateLiftHomeomorph.{v} n)
  have hUe : U ⊆ e.source := hUc
  refine ⟨e '' U, e.isOpen_image_of_subset_source hU hUe, ?_⟩
  exact ⟨e.homeomorphOfImageSubsetSource hUe rfl⟩

/-- The open sets contained in one chart of the fixed atlas. -/
def chartOpenBasis {n : ℕ} (A : Manifold n M) : Set (Set M) :=
  {U | IsOpen U ∧ ∃ c ∈ A.atlas, U ⊆ c.source}

lemma chartOpenBasis_inter {n : ℕ} (A : Manifold n M)
    (U : Set M) (hU : U ∈ chartOpenBasis A)
    (V : Set M) (hV : V ∈ chartOpenBasis A) : U ∩ V ∈ chartOpenBasis A := by
  obtain ⟨hUo, c, hc, hUc⟩ := hU
  exact ⟨hUo.inter hV.1, c, hc, inter_subset_left.trans hUc⟩

lemma chartOpenBasis_isTopologicalBasis {n : ℕ} (A : Manifold n M) :
    IsTopologicalBasis (chartOpenBasis A) := by
  apply isTopologicalBasis_of_isOpen_of_nhds (fun U hU => hU.1)
  intro x U hx hU
  obtain ⟨c, hc, hxc⟩ := A.covers x
  exact ⟨U ∩ c.source, ⟨hU.inter c.open_source, c, hc, inter_subset_right⟩,
    ⟨hx, hxc⟩, inter_subset_left⟩

end Geometry

/-- Every open subset of Euclidean space satisfies duality, with all
orientations and manifold structures that occur in the gluing process. -/
lemma good_euclidean_open
    (hg : P202Specs.CompactSupportMayerVietoris.Expected.gluing.{u,v})
    (d : DualityData.{u,v} R) (n : ℕ)
    (U : Set (ULift.{v} (Fin n → ℝ))) (hU : IsOpen U) :
    Good R (ULift.{v} (Fin n → ℝ)) d n U := by
  let E := ULift.{v} (Fin n → ℝ)
  apply open_of_inter_basis (Good R E d n)
    {V : Set E | IsOpen V ∧ Convex ℝ V ∧ Bornology.IsBounded V}
    (isTopologicalBasis_bounded_convex_open E)
    (fun _ hV _ hW => bounded_convex_open_inter hV hW)
    (good_empty R E d n) ?_ ?_ ?_ hU
  · intro V hV
    by_cases hne : V.Nonempty
    · obtain ⟨f⟩ := Geometry.convexOpen_homeomorphic_space V hV.1 hV.2.1 hV.2.2 hne
      intro X _ A o ⟨e⟩
      exact euclidean_duality R d X A o (e.trans f)
    · have he : V = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [he]
      exact good_empty R E d n
  · exact good_union R E hg d n
  · exact good_increasing_union R E hg d n

/-- Full compact-support duality derived from the single ordered gluing
premise. The independent specification retains its original unconditional type. -/
theorem duality_conditional
    (hg : P202Specs.CompactSupportMayerVietoris.Expected.gluing.{u,v}) :
    P202Specs.PoincareDuality.Expected.duality.{u,v} := by
  intro R _ d n M _ A o
  letI : SecondCountableTopology M := A.secondCountable
  have hgood : Good R M d n (Set.univ : Set M) := by
    apply open_of_inter_basis (Good R M d n) (Geometry.chartOpenBasis A)
      (Geometry.chartOpenBasis_isTopologicalBasis A) (Geometry.chartOpenBasis_inter A)
      (good_empty R M d n) ?_ (good_union R M hg d n)
      (good_increasing_union R M hg d n) isOpen_univ
    intro U hU
    obtain ⟨hUo, c, hc, hUc⟩ := hU
    obtain ⟨W, hW, ⟨e⟩⟩ := Geometry.chartOpen_homeomorphic_euclideanOpen c U hUo hUc
    exact (good_homeomorph R M d n U W e).mpr (good_euclidean_open R hg d n W hW)
  exact hgood M A o ⟨(Homeomorph.Set.univ M).symm⟩

/-- The dimension-vanishing consequence uses genuine finite singular homology
and the negative compact-cohomology convention. -/
theorem aboveDimension_conditional
    (hg : P202Specs.CompactSupportMayerVietoris.Expected.gluing.{u,v}) :
    P202Specs.PoincareDuality.Expected.aboveDimension.{u,v} := by
  intro R _ n M _ A o i hi
  let d := P202.CompactSupport.dualityData R
  exact aboveDimension_of_duality R M d A o
    (duality_conditional hg R d n M A o) i hi

end GlobalCalculation

end P202.PoincareDuality

universe v8_closure_89345daa138ea016_u0 v8_closure_89345daa138ea016_u1
theorem _root_.«P202».«PoincareDuality».«aboveDimension» : _root_.«P202Specs».«PoincareDuality».«Expected».«aboveDimension».{v8_closure_89345daa138ea016_u0, v8_closure_89345daa138ea016_u1} :=
  @_root_.«P202».«PoincareDuality».«aboveDimension_conditional».{v8_closure_89345daa138ea016_u0, v8_closure_89345daa138ea016_u1} (@_root_.«P202».«CompactSupportMayerVietoris».«gluing».{v8_closure_89345daa138ea016_u0, v8_closure_89345daa138ea016_u1})
theorem _root_.«P202».«PoincareDuality».«compactIdentification» : _root_.«P202Specs».«PoincareDuality».«Expected».«compactIdentification».{v8_closure_89345daa138ea016_u0, v8_closure_89345daa138ea016_u1} :=
  @_root_.«P202».«PoincareDuality».«compactIdentification_conditional».{v8_closure_89345daa138ea016_u0, v8_closure_89345daa138ea016_u1} (@_root_.«P202».«CompactSupportMayerVietoris».«gluing».{v8_closure_89345daa138ea016_u0, v8_closure_89345daa138ea016_u1})
theorem _root_.«P202».«PoincareDuality».«duality» : _root_.«P202Specs».«PoincareDuality».«Expected».«duality».{v8_closure_89345daa138ea016_u0, v8_closure_89345daa138ea016_u1} :=
  @_root_.«P202».«PoincareDuality».«duality_conditional».{v8_closure_89345daa138ea016_u0, v8_closure_89345daa138ea016_u1} (@_root_.«P202».«CompactSupportMayerVietoris».«gluing».{v8_closure_89345daa138ea016_u0, v8_closure_89345daa138ea016_u1})
