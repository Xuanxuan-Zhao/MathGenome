import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SimplicialComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SpheresDisks
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SpheresDisks
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.Excision
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SimplicialChains
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellTopology
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SubcomplexNeighborhoods
import Mathlib.LinearAlgebra.Projection
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.ContinuousMap.Sigma
import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Homology.Homotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.GoodPairQuotient
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! Proof of the simplicial–singular comparison for arbitrary weak
realizations, module coefficients, and subcomplex pairs. The characteristic
quotient comparison preserves the specified affine generators. Skeletal exact
sequences and finite chain support give the global comparison; carrier
homotopies give naturality under vertex collapse and signed order independence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped Simplicial
open P202.Cellular P202Specs.RelativeParametrizations P202Specs.SingularChains
open P202Specs.SimplicialComparison
universe u v w z
namespace P202.SimplicialComparison
attribute [local instance] P202Specs.OrientedSimplicialAlgebra.vertexOrder
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- Existence of precisely the two canonical affine maps; no isomorphism is assumed. -/
theorem simplicialComparisonData_nonempty {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K) :
    Nonempty (SimplicialComparisonData R A K B) := by
  obtain ⟨F, hF⟩ := P202.SimplicialChains.Simplicial.affineChainMap R A K
  obtain ⟨G, hG⟩ := P202.SimplicialChains.Simplicial.relativeAffineChainMap R A K B
  exact ⟨⟨F, hF, G, hG⟩⟩

theorem deltaComparisonData_nonempty (D : DeltaComplex.{w}) (B : DeltaSubcomplex D) :
    Nonempty (DeltaComparisonData R A D B) := by
  obtain ⟨F, hF⟩ := P202.SimplicialChains.deltaAffineChainMap R A D
  obtain ⟨G, hG⟩ := P202.SimplicialChains.deltaRelativeAffineChainMap R A D B
  exact ⟨⟨F, hF, G, hG⟩⟩

/-- Canonical affine formulas determine the absolute comparison uniquely. -/
theorem deltaComparison_absolute_unique (D : DeltaComplex.{w}) (B : DeltaSubcomplex D)
    (F G : DeltaComparisonData R A D B) : F.absolute = G.absolute := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  rw [F.absolute_formula, G.absolute_formula]

/-- Quotient surjectivity determines the relative comparison uniquely as well. -/
theorem deltaComparison_relative_unique (D : DeltaComplex.{w}) (B : DeltaSubcomplex D)
    (F G : DeltaComparisonData R A D B) : F.relative = G.relative := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := ((deltaSelection R A D B).module n).mkQ_surjective x
  rw [F.relative_formula, G.relative_formula]

theorem simplicialComparison_absolute_unique {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K)
    (F G : SimplicialComparisonData R A K B) : F.absolute = G.absolute := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  rw [F.absolute_formula, G.absolute_formula]

theorem simplicialComparison_relative_unique {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K)
    (F G : SimplicialComparisonData R A K B) : F.relative = G.relative := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := ((Simplicial.selection R A K B).module n).mkQ_surjective x
  rw [F.relative_formula, G.relative_formula]

/-- Descent of an ordered Δ-map through the actual weak realization quotient. -/
def deltaRealization {D E : DeltaComplex.{w}} (f : DeltaMap D E) :
    TopCat.of D.Realization ⟶ TopCat.of E.Realization := by
  let raw : D.SimplexSum → E.Realization :=
    fun p => E.simplexChart p.1 (f.simplex p.1 p.2.1) p.2.2
  have hraw : ∀ a b, (D.faceSetoid).r a b → raw a = raw b := by
    intro a b h
    induction h with
    | rel a b h =>
      cases h with
      | face a s t =>
        dsimp [raw]
        rw [f.face]
        exact Quotient.sound (Relation.EqvGen.rel _ _ (DeltaComplex.FaceRelation.face a _ t))
    | refl => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  exact TopCat.ofHom ⟨Quotient.lift raw hraw, Continuous.quotient_lift (by
    apply continuous_sigma
    intro n
    apply continuous_sigma
    intro s
    exact (deltaParametrization E n (f.simplex n s)).continuous) hraw⟩

@[simp] theorem deltaRealization_chart {D E : DeltaComplex.{w}} (f : DeltaMap D E)
    (n : ℕ) (s : D.Simplex n) (t : StandardSimplex n) :
    deltaRealization f (D.simplexChart n s t) = E.simplexChart n (f.simplex n s) t := rfl

/-- A map of Δ-subcomplexes realizes as a map of their actual carriers. -/
theorem deltaRealization_carrier {D E : DeltaComplex.{w}}
    (B : DeltaSubcomplex D) (H : DeltaSubcomplex E) (f : DeltaMap D E)
    (hf : ∀ n s, s ∈ B.selected n → f.simplex n s ∈ H.selected n)
    (x : D.Realization) (hx : x ∈ B.carrier) : deltaRealization f x ∈ H.carrier := by
  obtain ⟨n, s, hs, t, rfl⟩ := hx
  exact ⟨n, f.simplex n s, hf n s hs, t, rfl⟩

/-- Singular pushforward preserves the supported submodules of any map of pairs. -/
theorem singularMap_preserves {X Y : TopCat.{w}} (B : Set X) (E : Set Y)
    (g : X ⟶ Y) (hg : ∀ x ∈ B, g x ∈ E) (n : ℕ)
    (x : Chains A X n) (hx : x ∈ (singularSelection R A X B).module n) :
    ((chainMap R A g).f n).hom x ∈ (singularSelection R A Y E).module n := by
  apply map_supported R A _ _ ((chainMap R A g).f n).hom ?_ x hx
  intro s hs a
  erw [P202.SingularChains.chainMap_single]
  apply Finsupp.single_mem_supported
  intro t
  rw [P202.SingularChains.simplexEquiv_postcomp]
  exact hg _ (hs t)

/-- The canonical relative singular pushforward on these same supported quotients. -/
def singularPairMap {X Y : TopCat.{w}} (B : Set X) (E : Set Y)
    (g : X ⟶ Y) (hg : ∀ x ∈ B, g x ∈ E) :
    singularRelativeComplex R A X B ⟶ singularRelativeComplex R A Y E :=
  (singularSelection R A X B).quotientMap (singularSelection R A Y E)
    (chainMap R A g) (singularMap_preserves R A B E g hg)

@[simp] theorem singularPairMap_mk {X Y : TopCat.{w}} (B : Set X) (E : Set Y)
    (g : X ⟶ Y) (hg : ∀ x ∈ B, g x ∈ E) (n : ℕ) (x : Chains A X n) :
    ((singularPairMap R A B E g hg).f n).hom
        (((singularSelection R A X B).module n).mkQ x) =
      ((singularSelection R A Y E).module n).mkQ (((chainMap R A g).f n).hom x) := rfl

/-- Ordered parametrizations commute with realization pushforward on the nose. -/
theorem deltaAffine_natural {D E : DeltaComplex.{w}} (f : DeltaMap D E) (n : ℕ) :
    (deltaParametrizationLinear R A E n).comp (deltaPushforward R A f n) =
      (((chainMap R A (deltaRealization f)).f n).hom).comp
        (deltaParametrizationLinear R A D n) := by
  apply Finsupp.lhom_ext
  intro s a
  change Finsupp.mapDomain (deltaSingularSimplex E n)
      (Finsupp.mapDomain (f.simplex n) (Finsupp.single s a)) =
    Finsupp.mapDomain ((TopCat.toSSet.map (deltaRealization f)).app (Opposite.op ⦋n⦌))
      (Finsupp.mapDomain (deltaSingularSimplex D n) (Finsupp.single s a))
  simp only [Finsupp.mapDomain_single]
  congr 1

/-- Full absolute and relative Δ-naturality, independent of the homology
isomorphism proof. The source square already commutes at chain level. -/
theorem deltaNaturality_core : P202Specs.SimplicialComparison.deltaNaturality_type.{u,v,w} := by
  intro R _ A _ _ D E B H f hf
  obtain ⟨T, hT⟩ := P202.SimplicialChains.deltaPushforward_chainMap R A f
  obtain ⟨Trel, hTrel⟩ := P202.SimplicialChains.deltaRelativePushforward R A B H f hf
  let grel := singularPairMap R A B.carrier H.carrier (deltaRealization f)
    (deltaRealization_carrier B H f hf)
  refine ⟨deltaRealization f, deltaRealization_chart f, T, Trel, grel, hT, hTrel, ?_, ?_⟩
  · intro n x
    rfl
  · intro F G q
    have habs : T ≫ G.absolute = F.absolute ≫ chainMap R A (deltaRealization f) := by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      change ((G.absolute.f n).hom).comp (T.f n).hom =
        (((chainMap R A (deltaRealization f)).f n).hom).comp (F.absolute.f n).hom
      rw [G.absolute_formula, F.absolute_formula, hT]
      exact deltaAffine_natural R A f n
    have hrel : Trel ≫ G.relative = F.relative ≫ grel := by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := ((deltaSelection R A D B).module n).mkQ_surjective x
      change (G.relative.f n).hom ((Trel.f n).hom _) =
        (grel.f n).hom ((F.relative.f n).hom _)
      rw [hTrel, G.relative_formula, F.relative_formula]
      change ((singularSelection R A (TopCat.of E.Realization) H.carrier).module n).mkQ
          (deltaParametrizationLinear R A E n (deltaPushforward R A f n x)) =
        ((singularSelection R A (TopCat.of E.Realization) H.carrier).module n).mkQ
          (((chainMap R A (deltaRealization f)).f n).hom
            (deltaParametrizationLinear R A D n x))
      exact congrArg ((singularSelection R A (TopCat.of E.Realization) H.carrier).module n).mkQ
        (congrArg (fun L => L x) (deltaAffine_natural R A f n))
    exact ⟨by simpa only [homologyMap_comp] using congrArg (fun t => homologyMap t q) habs,
      by simpa only [homologyMap_comp] using congrArg (fun t => homologyMap t q) hrel⟩

/-- The ordered premise list is exactly the conditional-proof contract. These
premises are unused here because Δ-naturality is already a chain-level identity.
The original premise-free target is proved below. -/
theorem deltaNaturality_conditional
    (_hcontractible : P202Specs.SpheresDisks.contractible_type.{u,v,w})
    (_hdisk : P202Specs.SpheresDisks.diskHomology_type.{u,v})
    (_hendpoint : P202Specs.SpheresDisks.endpointDifference_type.{u,v})
    (_hconnecting : P202Specs.SpheresDisks.simplexConnecting_type.{u,v})
    (_hgenerator : P202Specs.SpheresDisks.simplexGenerator_type.{u,v})
    (_hvanishing : P202Specs.SpheresDisks.simplexVanishing_type.{u,v})
    (_hsphere : P202Specs.SpheresDisks.sphereHomology_type.{u,v}) :
    P202Specs.SimplicialComparison.deltaNaturality_type.{u,v,w} :=
  deltaNaturality_core


/-! Finite support in actual simplicial subcomplexes. The topology used here
is the weak realization topology, including when there are infinitely many
vertices or simplices. -/

/-- Restrict to the simplices whose vertices lie in a prescribed finite set. -/
def simplicialFiniteRestriction {V : Type w} (K : AbstractSimplicialComplex V)
    (F : Finset V) : Simplicial.Subcomplex K where
  complex := {
    simplices := {s | s ∈ K.simplices ∧ s ⊆ F}
    nonempty := fun s hs => K.nonempty s hs.1
    face := fun hs hts ht => ⟨K.face hs.1 hts ht, hts.trans hs.2⟩ }
  subset := fun _ hs => hs.1

theorem simplicialFiniteRestriction_finite {V : Type w}
    (K : AbstractSimplicialComplex V) (F : Finset V) :
    (simplicialFiniteRestriction K F).complex.simplices.Finite := by
  classical
  exact F.powerset.finite_toSet.subset (fun s hs => Finset.mem_powerset.mpr hs.2)

/-- The CW compact-support theorem gives a finite subcomplex in the SAME
abstract simplicial model, rather than just an unrelated CW cell selection. -/
theorem simplicialCompactSupport {V : Type w} (K : AbstractSimplicialComplex V)
    (S : Set K.Realization) (hS : IsCompact S) :
    ∃ B : Simplicial.Subcomplex K, B.complex.simplices.Finite ∧ S ⊆ B.carrier K := by
  classical
  obtain ⟨C, indices, hcharts⟩ := P202.Topology.simplicialRealizationCW K
  letI : CWStructure K.Realization := C
  obtain ⟨B, hBfinite, hB⟩ := P202.Topology.compactContainedInFiniteSubcomplex S hS
  let J := {d : Σ n, Cell K.Realization n // d.2 ∈ B.cells d.1}
  haveI : Finite J := hBfinite.to_subtype
  let F : Finset V := (Set.toFinite (Set.range (fun d : J => (indices d.1.1 d.1.2).1.1))).toFinset.biUnion
    (fun s => s)
  refine ⟨simplicialFiniteRestriction K F, simplicialFiniteRestriction_finite K F, ?_⟩
  intro x hx
  obtain ⟨n, c, hxc⟩ := Set.mem_iUnion₂.mp (hB hx)
  have hxi : x ∈ K.simplexChart (indices n c.1).1 '' K.simplexInterior (indices n c.1).1 := by
    rw [← (hcharts n c.1).1]
    exact hxc
  have hxSupport := (P202.Topology.simplicialChart_interior K _ x).mp hxi
  change x.1.weights.support ∈ K.simplices ∧ x.1.weights.support ⊆ F
  refine ⟨x.2, ?_⟩
  rw [hxSupport]
  intro v hv
  apply Finset.mem_biUnion.mpr
  refine ⟨(indices n c.1).1.1, ?_, hv⟩
  simpa only [Set.Finite.mem_toFinset] using
    (show (indices n c.1).1.1 ∈ Set.range (fun d : J => (indices d.1.1 d.1.2).1.1) from
      ⟨(⟨⟨n, c.1⟩, c.2⟩ : J), rfl⟩)

/-- Every finite family of actual singular chains, in possibly different
degrees, is supported in one finite simplicial subcomplex. This applies at
once to a cycle and a proposed bounding chain. -/
theorem simplicialChainsFiniteSupport {V : Type w} (K : AbstractSimplicialComplex V)
    {ι : Type*} [Finite ι] (degree : ι → ℕ)
    (c : ∀ i, Chains A (TopCat.of K.Realization) (degree i)) :
    ∃ B : Simplicial.Subcomplex K, B.complex.simplices.Finite ∧
      ∀ i, c i ∈ (singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module (degree i) := by
  classical
  let S : Set K.Realization := ⋃ i, ⋃ s : (c i).support,
    Set.range (simplexEquiv (TopCat.of K.Realization) (degree i) s.1)
  have hS : IsCompact S := isCompact_iUnion fun i => isCompact_iUnion fun s =>
    isCompact_range (simplexEquiv (TopCat.of K.Realization) (degree i) s.1).continuous
  obtain ⟨B, hBfinite, hB⟩ := simplicialCompactSupport K S hS
  refine ⟨B, hBfinite, ?_⟩
  intro i s hs t
  apply hB
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨t, rfl⟩⟩⟩


/-- All ordered faces of a finite collection of Δ-simplex labels. -/
def deltaFiniteClosure (D : DeltaComplex.{w}) (F : Finset (Σ n, D.Simplex n)) :
    DeltaSubcomplex D where
  selected m := {s | ∃ d ∈ F, ∃ a : Fin (m+1) ↪o Fin (d.1+1), D.face a d.2 = s}
  face_closed a s hs := by
    obtain ⟨d, hd, b, rfl⟩ := hs
    exact ⟨d, hd, a.comp b, (D.face_comp a b d.2).symm⟩

/-- Finiteness counts all labels in all dimensions, including repeated faces. -/
theorem deltaFiniteClosure_finite (D : DeltaComplex.{w})
    (F : Finset (Σ n, D.Simplex n)) :
    (Set.ofPred fun d : (Σ n, D.Simplex n) => d.2 ∈ (deltaFiniteClosure D F).selected d.1).Finite := by
  classical
  let T (d : Σ n, D.Simplex n) := Σ m : Fin (d.1+1), Fin (m.val+1) ↪o Fin (d.1+1)
  let label (d : Σ n, D.Simplex n) (a : T d) : Σ n, D.Simplex n :=
    ⟨a.1.val, D.face a.2 d.2⟩
  have hfinite : (⋃ d ∈ F, Set.range (label d)).Finite :=
    F.finite_toSet.biUnion (fun d _ => Set.finite_range (label d))
  apply hfinite.subset
  rintro ⟨m, s⟩ ⟨d, hd, a, ha⟩
  have hm : m ≤ d.1 := Nat.le_of_succ_le_succ (by
    simpa using Fintype.card_le_of_injective a a.injective)
  exact Set.mem_iUnion.mpr ⟨d, Set.mem_iUnion.mpr ⟨hd,
    ⟨⟨⟨m, Nat.lt_succ_of_le hm⟩, a⟩, congrArg (Sigma.mk m) ha⟩⟩⟩

/-- Each original chart lands in its face closure, including its boundary. -/
theorem deltaFiniteClosure_chart (D : DeltaComplex.{w})
    (F : Finset (Σ n, D.Simplex n)) (n : ℕ) (s : D.Simplex n)
    (hs : (⟨n, s⟩ : Σ n, D.Simplex n) ∈ F) (t : StandardSimplex n) :
    D.simplexChart n s t ∈ (deltaFiniteClosure D F).carrier := by
  exact ⟨n, s, ⟨⟨n, s⟩, hs, OrderEmbedding.id _, D.face_id n s⟩, t, rfl⟩

/-- Translate finite CW compact support back to finite face-closed Δ-labels. -/
theorem deltaCompactSupport (D : DeltaComplex.{w})
    (S : Set D.Realization) (hS : IsCompact S) :
    ∃ B : DeltaSubcomplex D,
      (Set.ofPred fun d : (Σ n, D.Simplex n) => d.2 ∈ B.selected d.1).Finite ∧ S ⊆ B.carrier := by
  classical
  obtain ⟨C, indices, hcharts⟩ := P202.Topology.deltaRealizationCW D
  letI : CWStructure D.Realization := C
  obtain ⟨B, hBfinite, hB⟩ := P202.Topology.compactContainedInFiniteSubcomplex S hS
  let J := {d : Σ n, Cell D.Realization n // d.2 ∈ B.cells d.1}
  haveI : Finite J := hBfinite.to_subtype
  let F : Finset (Σ n, D.Simplex n) :=
    (Set.finite_range (fun d : J => (⟨d.1.1, indices d.1.1 d.1.2⟩ : Σ n, D.Simplex n))).toFinset
  refine ⟨deltaFiniteClosure D F, deltaFiniteClosure_finite D F, ?_⟩
  intro x hx
  obtain ⟨n, c, hxc⟩ := Set.mem_iUnion₂.mp (hB hx)
  rw [(hcharts n c.1).1] at hxc
  obtain ⟨t, ht, rfl⟩ := hxc
  apply deltaFiniteClosure_chart D F n (indices n c.1)
  simpa only [F, Set.Finite.mem_toFinset] using
    (show (⟨n, indices n c.1⟩ : Σ n, D.Simplex n) ∈
      Set.range (fun d : J => (⟨d.1.1, indices d.1.1 d.1.2⟩ : Σ n, D.Simplex n)) from
        ⟨(⟨⟨n, c.1⟩, c.2⟩ : J), rfl⟩)

/-- Finite singular chains of arbitrary degrees have a simultaneous finite
Δ-subcomplex carrier. No local finiteness or dimension bound is imposed. -/
theorem deltaChainsFiniteSupport (D : DeltaComplex.{w})
    {ι : Type*} [Finite ι] (degree : ι → ℕ)
    (c : ∀ i, Chains A (TopCat.of D.Realization) (degree i)) :
    ∃ B : DeltaSubcomplex D,
      (Set.ofPred fun d : (Σ n, D.Simplex n) => d.2 ∈ B.selected d.1).Finite ∧
      ∀ i, c i ∈ (singularSelection R A (TopCat.of D.Realization) B.carrier).module (degree i) := by
  classical
  let S : Set D.Realization := ⋃ i, ⋃ s : (c i).support,
    Set.range (simplexEquiv (TopCat.of D.Realization) (degree i) s.1)
  have hS : IsCompact S := isCompact_iUnion fun i => isCompact_iUnion fun s =>
    isCompact_range (simplexEquiv (TopCat.of D.Realization) (degree i) s.1).continuous
  obtain ⟨B, hBfinite, hB⟩ := deltaCompactSupport D S hS
  refine ⟨B, hBfinite, ?_⟩
  intro i s hs t
  apply hB
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨⟨s, hs⟩, ⟨t, rfl⟩⟩⟩


/-- Pushforward along an injective continuous map is injective on the actual
singular chains, for arbitrary module coefficients. -/
theorem singularMap_injective {X Y : TopCat.{w}} (g : X ⟶ Y)
    (hg : Function.Injective g) (n : ℕ) :
    Function.Injective ((chainMap R A g).f n).hom := by
  apply Finsupp.mapDomain_injective
  intro s t h
  apply (simplexEquiv X n).injective
  ext p
  apply hg
  have hh := congrArg (fun z => simplexEquiv Y n z p) h
  simpa only [P202.SingularChains.simplexEquiv_postcomp, ContinuousMap.comp_apply] using hh

/-- A supported chain lifts to chains of the actual subspace with its subspace
topology. This uses the proved image identification of the upstream model. -/
theorem singularSubspaceLift {X : TopCat.{w}} (Y : Set X) (n : ℕ)
    (c : Chains A X n) (hc : c ∈ (singularSelection R A X Y).module n) :
    ∃ c' : Chains A (TopCat.of Y) n,
      ((chainMap R A (subspaceInclusion X Y)).f n).hom c' = c := by
  rw [← P202.SimplicialChains.singularSelection_range R A X Y n] at hc
  exact hc

/-- A differential equation between lifted chains holds in the subspace
whenever it holds after inclusion. Thus cycles and bounding-chain equations
survive the compact-support restriction. -/
theorem singularSubspace_boundary_iff {X : TopCat.{w}} (Y : Set X) (n : ℕ)
    (c : Chains A (TopCat.of Y) (n+1)) (b : Chains A (TopCat.of Y) n) :
    ((P202Specs.SingularChains.complex R A (TopCat.of Y)).d (n+1) n).hom c = b ↔
      ((P202Specs.SingularChains.complex R A X).d (n+1) n).hom
        (((chainMap R A (subspaceInclusion X Y)).f (n+1)).hom c) =
      ((chainMap R A (subspaceInclusion X Y)).f n).hom b := by
  let j := chainMap R A (subspaceInclusion X Y)
  have hj : Function.Injective (j.f n).hom :=
    singularMap_injective R A _ Subtype.val_injective n
  have hcomm := congrArg
    (fun f : (P202Specs.SingularChains.complex R A (TopCat.of Y)).X (n+1) ⟶
      (P202Specs.SingularChains.complex R A X).X n => f.hom c) (j.comm (n+1) n).symm
  change (j.f n).hom
    (((P202Specs.SingularChains.complex R A (TopCat.of Y)).d (n+1) n).hom c) =
    ((P202Specs.SingularChains.complex R A X).d (n+1) n).hom ((j.f (n+1)).hom c) at hcomm
  rw [← hcomm]
  exact hj.eq_iff.symm

/-- Simultaneous restriction of finitely many singular chains to the subspace
of a finite abstract simplicial subcomplex. -/
theorem simplicialChainsFiniteLift {V : Type w} (K : AbstractSimplicialComplex V)
    {ι : Type*} [Finite ι] (degree : ι → ℕ)
    (c : ∀ i, Chains A (TopCat.of K.Realization) (degree i)) :
    ∃ B : Simplicial.Subcomplex K, B.complex.simplices.Finite ∧
      ∀ i, ∃ c' : Chains A (TopCat.of (B.carrier K)) (degree i),
        ((chainMap R A (subspaceInclusion (TopCat.of K.Realization) (B.carrier K))).f
          (degree i)).hom c' = c i := by
  obtain ⟨B, hBfinite, hB⟩ := simplicialChainsFiniteSupport R A K degree c
  exact ⟨B, hBfinite, fun i => singularSubspaceLift R A _ _ _ (hB i)⟩

/-- Simultaneous restriction of finitely many singular chains to the subspace
of a finite face-closed Δ-subcomplex. -/
theorem deltaChainsFiniteLift (D : DeltaComplex.{w})
    {ι : Type*} [Finite ι] (degree : ι → ℕ)
    (c : ∀ i, Chains A (TopCat.of D.Realization) (degree i)) :
    ∃ B : DeltaSubcomplex D,
      (Set.ofPred fun d : (Σ n, D.Simplex n) => d.2 ∈ B.selected d.1).Finite ∧
      ∀ i, ∃ c' : Chains A (TopCat.of B.carrier) (degree i),
        ((chainMap R A (subspaceInclusion (TopCat.of D.Realization) B.carrier)).f
          (degree i)).hom c' = c i := by
  obtain ⟨B, hBfinite, hB⟩ := deltaChainsFiniteSupport R A D degree c
  exact ⟨B, hBfinite, fun i => singularSubspaceLift R A _ _ _ (hB i)⟩


/-- The barycentric realization map of an arbitrary simplicial map, permitting
vertex collapse. The weak topology is checked separately on each chart. -/
def simplicialRealization {V W : Type w} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) :
    TopCat.of K.Realization ⟶ TopCat.of L.Realization := by
  classical
  let g : K.Realization → L.Realization := fun x => ⟨x.1.map f.vertices,
    L.face (f.map_simplex _ x.2)
      (by intro v hv; exact Finsupp.mapDomain_support hv)
      (Convexity.StdSimplex.support_weights_nonempty _)⟩
  refine TopCat.ofHom ⟨g, ?_⟩
  rw [continuous_iSup_dom]
  intro s
  rw [continuous_coinduced_dom]
  let r : s.1 → s.1.image f.vertices :=
    fun v => ⟨f.vertices v.1, Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩
  have heq : g ∘ K.simplexChart s =
      L.simplexChart ⟨s.1.image f.vertices, f.map_simplex _ s.2⟩ ∘
        Convexity.StdSimplex.map r := by
    funext t
    apply Subtype.ext
    dsimp [g, AbstractSimplicialComplex.simplexChart]
    simp only [Convexity.StdSimplex.map_map]
    rfl
  rw [heq]
  exact (P202.Topology.simplicialChartContinuous L _).comp
    (Convexity.StdSimplex.continuous_map ℝ r)

@[simp] theorem simplicialRealization_value {V W : Type w}
    {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (x : K.Realization) :
    (simplicialRealization f x).val = x.val.map f.vertices := rfl

/-- A simplicial map of subcomplex pairs realizes to a map of their actual
carriers, including when its vertex map identifies vertices. -/
theorem simplicialRealization_carrier {V W : Type w}
    {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}
    (B : Simplicial.Subcomplex K) (E : Simplicial.Subcomplex L)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (hf : ∀ s ∈ B.complex.simplices, s.image f.vertices ∈ E.complex.simplices)
    (x : K.Realization) (hx : x ∈ B.carrier K) :
    simplicialRealization f x ∈ E.carrier L := by
  apply E.complex.face (hf _ hx) ?_ (Convexity.StdSimplex.support_weights_nonempty _)
  intro v hv
  exact Finsupp.mapDomain_support hv

/-- Construction of the three induced maps in simplicial naturality, with
the exact pushforward and relative quotient formulas required in its Spec.
The remaining homology-square assertion needs a carrier homotopy. -/
theorem simplicialNaturality_maps {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (B : Simplicial.Subcomplex K) (E : Simplicial.Subcomplex L)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (hf : ∀ s ∈ B.complex.simplices, s.image f.vertices ∈ E.complex.simplices) :
    ∃ (T : P202Specs.OrientedSimplicialAlgebra.complex R A (K := K) ⟶
          P202Specs.OrientedSimplicialAlgebra.complex R A (K := L))
      (Trel : Simplicial.relativeComplex R A K B ⟶ Simplicial.relativeComplex R A L E)
      (grel : singularRelativeComplex R A (TopCat.of K.Realization) (B.carrier K) ⟶
        singularRelativeComplex R A (TopCat.of L.Realization) (E.carrier L)),
      (∀ n, (T.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward R A f n) ∧
      (∀ n x, (Trel.f n).hom (((Simplicial.selection R A K B).module n).mkQ x) =
        ((Simplicial.selection R A L E).module n).mkQ
          (P202Specs.OrientedSimplicialAlgebra.pushforward R A f n x)) ∧
      (∀ n x, (grel.f n).hom
          (((singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module n).mkQ x) =
        ((singularSelection R A (TopCat.of L.Realization) (E.carrier L)).module n).mkQ
          (((chainMap R A (simplicialRealization f)).f n).hom x)) := by
  obtain ⟨T, hT⟩ := P202.SimplicialChains.Oriented.pushforward_chainMap R A f
  obtain ⟨Trel, hTrel⟩ := P202.SimplicialChains.Simplicial.relativePushforward R A K L B E f hf
  refine ⟨T, Trel, singularPairMap R A _ _ (simplicialRealization f)
    (simplicialRealization_carrier B E f hf), hT, hTrel, ?_⟩
  intro n x
  rfl


/-- For inclusions, the canonical affine square already commutes on chains.
This is the strict naturality needed in the finite-subcomplex comparison. -/
theorem simplicialAffine_inclusion {V : Type w}
    (K L : AbstractSimplicialComplex V) (h : K.simplices ⊆ L.simplices) (n : ℕ) :
    (Simplicial.affineLinear L R A n).comp
        (P202Specs.OrientedSimplicialAlgebra.pushforward R A
          (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion h) n) =
      (((chainMap R A (simplicialRealization
          (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion h))).f n).hom).comp
        (Simplicial.affineLinear K R A n) := by
  apply Finsupp.lhom_ext
  intro s a
  change Simplicial.affineLinear L R A n
      (P202Specs.OrientedSimplicialAlgebra.pushforward R A
        (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion h) n (Finsupp.single s a)) =
    ((chainMap R A (simplicialRealization
      (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion h))).f n).hom
        (Simplicial.affineLinear K R A n (Finsupp.single s a))
  erw [P202.SimplicialChains.Oriented.pushforward_inclusion_single,
    P202.SimplicialChains.Simplicial.affineLinear_single,
    P202.SimplicialChains.Simplicial.affineLinear_single,
    P202.SingularChains.chainMap_single]
  congr 1
  apply (simplexEquiv (TopCat.of L.Realization) n).injective
  rw [P202.SingularChains.simplexEquiv_postcomp]
  ext t
  apply Subtype.ext
  change (Simplicial.parametrization L n _ t).val =
    (simplicialRealization
      (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion h)
      (Simplicial.parametrization K n s t)).val
  rw [simplicialRealization_value,
    P202.SimplicialChains.Simplicial.parametrization_value,
    P202.SimplicialChains.Simplicial.parametrization_value]
  exact (Convexity.StdSimplex.map_id _).symm


/-- Absolute comparison commutes strictly with every subcomplex inclusion. -/
theorem simplicialInclusion_absolute_square {V : Type w}
    (K L : AbstractSimplicialComplex V) (h : K.simplices ⊆ L.simplices)
    (B : Simplicial.Subcomplex K) (E : Simplicial.Subcomplex L)
    (T : P202Specs.OrientedSimplicialAlgebra.complex R A (K := K) ⟶
      P202Specs.OrientedSimplicialAlgebra.complex R A (K := L))
    (hT : ∀ n, (T.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward R A
      (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion h) n)
    (F : SimplicialComparisonData R A K B) (G : SimplicialComparisonData R A L E) :
    T ≫ G.absolute = F.absolute ≫ chainMap R A
      (simplicialRealization (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion h)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  change ((G.absolute.f n).hom).comp (T.f n).hom =
    (((chainMap R A (simplicialRealization
      (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion h))).f n).hom).comp
      (F.absolute.f n).hom
  rw [G.absolute_formula, F.absolute_formula, hT]
  exact simplicialAffine_inclusion R A K L h n

/-- The same strict inclusion square descends to all relative quotients. -/
theorem simplicialInclusion_relative_square {V : Type w}
    (K L : AbstractSimplicialComplex V) (h : K.simplices ⊆ L.simplices)
    (B : Simplicial.Subcomplex K) (E : Simplicial.Subcomplex L)
    (Trel : Simplicial.relativeComplex R A K B ⟶ Simplicial.relativeComplex R A L E)
    (grel : singularRelativeComplex R A (TopCat.of K.Realization) (B.carrier K) ⟶
      singularRelativeComplex R A (TopCat.of L.Realization) (E.carrier L))
    (hTrel : ∀ n x, (Trel.f n).hom (((Simplicial.selection R A K B).module n).mkQ x) =
      ((Simplicial.selection R A L E).module n).mkQ
        (P202Specs.OrientedSimplicialAlgebra.pushforward R A
          (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion h) n x))
    (hgrel : ∀ n x, (grel.f n).hom
        (((singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module n).mkQ x) =
      ((singularSelection R A (TopCat.of L.Realization) (E.carrier L)).module n).mkQ
        (((chainMap R A (simplicialRealization
          (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion h))).f n).hom x))
    (F : SimplicialComparisonData R A K B) (G : SimplicialComparisonData R A L E) :
    Trel ≫ G.relative = F.relative ≫ grel := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := ((Simplicial.selection R A K B).module n).mkQ_surjective x
  change (G.relative.f n).hom ((Trel.f n).hom _) =
    (grel.f n).hom ((F.relative.f n).hom _)
  rw [hTrel, G.relative_formula, F.relative_formula, hgrel]
  exact congrArg ((singularSelection R A (TopCat.of L.Realization) (E.carrier L)).module n).mkQ
    (congrArg (fun M => M x) (simplicialAffine_inclusion R A K L h n))


/-! Relative chain groups retain exactly the unselected generators, with their
original coefficients. These identifications do not compute singular homology. -/

/-- Quotienting finite chains by a selected set removes precisely that set
from the direct-sum indexing type. -/
def supportedQuotientEquiv {I : Type w} (S : Set I) :
    ((I →₀ A) ⧸ Finsupp.supported A R S) ≃ₗ[R] (↥(Sᶜ) →₀ A) :=
  (Finsupp.supported A R S).quotientEquivOfIsCompl (Finsupp.supported A R Sᶜ)
    ⟨Finsupp.disjoint_supported_supported (M := A) (R := R) isCompl_compl.disjoint,
      Finsupp.codisjoint_supported_supported (M := A) (R := R) isCompl_compl.codisjoint⟩ ≪≫ₗ
    Finsupp.supportedEquivFinsupp (R := R) Sᶜ

/-- The inverse identifies each coefficient with exactly its quotient
simplex class; no arbitrary basis or sign is chosen. -/
@[simp] theorem supportedQuotientEquiv_symm_single {I : Type w} (S : Set I)
    (i : ↥(Sᶜ)) (a : A) :
    (supportedQuotientEquiv R A S).symm (Finsupp.single i a) =
      (Finsupp.supported A R S).mkQ (Finsupp.single i.1 a) := by
  simp [supportedQuotientEquiv, Submodule.quotientEquivOfIsCompl_symm_apply]

/-- Actual relative Δ-chain groups are direct sums over the remaining labels. -/
def deltaRelativeDegreeEquiv (D : DeltaComplex.{w}) (B : DeltaSubcomplex D) (n : ℕ) :
    (deltaRelativeComplex R A D B).X n ≃ₗ[R] (↥((B.selected n)ᶜ) →₀ A) :=
  supportedQuotientEquiv R A (B.selected n)

@[simp] theorem deltaRelativeDegreeEquiv_symm_single (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) (n : ℕ) (s : ↥((B.selected n)ᶜ)) (a : A) :
    (deltaRelativeDegreeEquiv R A D B n).symm (Finsupp.single s a) =
      ((deltaSelection R A D B).module n).mkQ (Finsupp.single s.1 a) :=
  supportedQuotientEquiv_symm_single R A _ s a

/-- The same direct-sum description for the oriented simplicial model. -/
def simplicialRelativeDegreeEquiv {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (n : ℕ) :
    (Simplicial.relativeComplex R A K B).X n ≃ₗ[R] (↥((B.selected K n)ᶜ) →₀ A) :=
  supportedQuotientEquiv R A (B.selected K n)

@[simp] theorem simplicialRelativeDegreeEquiv_symm_single {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K) (n : ℕ)
    (s : ↥((B.selected K n)ᶜ)) (a : A) :
    (simplicialRelativeDegreeEquiv R A K B n).symm (Finsupp.single s a) =
      ((Simplicial.selection R A K B).module n).mkQ (Finsupp.single s.1 a) :=
  supportedQuotientEquiv_symm_single R A _ s a


/-- The face-closed subcomplex containing precisely the labels below degree N. -/
def deltaSkeletonLT (D : DeltaComplex.{w}) (N : ℕ) : DeltaSubcomplex D where
  selected m := {s | m < N}
  face_closed {m n} a s hs := by
    have hmn : m ≤ n := Nat.le_of_succ_le_succ (by
      simpa using Fintype.card_le_of_injective a a.injective)
    exact lt_of_le_of_lt hmn hs

/-- The actual relative complex of consecutive Δ-skeleta, including the
zero skeleton relative to the empty subcomplex. -/
def deltaSkeletalRelative (D : DeltaComplex.{w}) (n : ℕ) :=
  deltaRelativeComplex R A (deltaSkeletonLT D (n+1)).asComplex
    (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n)

/-- No coefficient survives in any degree other than the skeletal degree. -/
theorem deltaSkeletalRelative_eq_zero (D : DeltaComplex.{w}) (n q : ℕ) (hq : q ≠ n)
    (c : (deltaSkeletalRelative R A D n).X q) : c = 0 := by
  let e := deltaRelativeDegreeEquiv R A (deltaSkeletonLT D (n+1)).asComplex
    (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n) q
  apply e.injective
  rw [map_zero]
  ext s
  have hs : q < n+1 := s.1.2
  have hsn : ¬ q < n := s.2
  exact False.elim (hq (by omega))

/-- Categorical form of concentration in the skeletal degree. -/
theorem deltaSkeletalRelative_isZero (D : DeltaComplex.{w}) (n q : ℕ) (hq : q ≠ n) :
    CategoryTheory.Limits.IsZero ((deltaSkeletalRelative R A D n).X q) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => (deltaSkeletalRelative_eq_zero R A D n q hq x).trans
    (deltaSkeletalRelative_eq_zero R A D n q hq y).symm⟩

/-- The remaining labels in degree n are exactly the original n-simplex
labels, with no identifications of distinct cells. -/
def deltaSkeletalLabels (D : DeltaComplex.{w}) (n : ℕ) :
    ↥((deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n).selected n)ᶜ ≃
      D.Simplex n where
  toFun s := s.1.1
  invFun s := ⟨⟨s, Nat.lt_succ_self n⟩, Nat.lt_irrefl n⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The only nonzero skeletal chain group is the direct sum of A indexed by
all n-simplices, also when that indexing set is infinite. -/
def deltaSkeletalTopEquiv (D : DeltaComplex.{w}) (n : ℕ) :
    (deltaSkeletalRelative R A D n).X n ≃ₗ[R] (D.Simplex n →₀ A) :=
  deltaRelativeDegreeEquiv R A (deltaSkeletonLT D (n+1)).asComplex
    (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n) n ≪≫ₗ
    Finsupp.domLCongr (deltaSkeletalLabels D n)

/-- The direct-sum coordinate a in the s summand is its original relative
chain generator, exactly as required before applying simplexGenerator. -/
@[simp] theorem deltaSkeletalTopEquiv_symm_single (D : DeltaComplex.{w}) (n : ℕ)
    (s : D.Simplex n) (a : A) :
    (deltaSkeletalTopEquiv R A D n).symm (Finsupp.single s a) =
      ((deltaSelection R A (deltaSkeletonLT D (n+1)).asComplex
        (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n)).module n).mkQ
          (Finsupp.single ⟨s, Nat.lt_succ_self n⟩ a) := by
  simp [deltaSkeletalTopEquiv, Finsupp.domLCongr, deltaSkeletalLabels]
  exact supportedQuotientEquiv_symm_single R A _ _ a


/-- Every differential of a consecutive-skeleta relative complex vanishes. -/
theorem deltaSkeletalRelative_d_zero (D : DeltaComplex.{w}) (n i j : ℕ) :
    (deltaSkeletalRelative R A D n).d i j = 0 := by
  by_cases hi : i = n
  · subst i
    by_cases hj : j = n
    · subst j
      exact (deltaSkeletalRelative R A D n).shape n n (by simp)
    · exact (deltaSkeletalRelative_isZero R A D n j hj).eq_of_tgt _ _
  · exact (deltaSkeletalRelative_isZero R A D n i hi).eq_of_src _ _

/-- The skeletal relative homology vanishes off the skeletal degree. -/
theorem deltaSkeletalRelative_homology_isZero (D : DeltaComplex.{w}) (n q : ℕ)
    (hq : q ≠ n) :
    CategoryTheory.Limits.IsZero ((deltaSkeletalRelative R A D n).homology q) :=
  (HomologicalComplex.ExactAt.of_isZero (deltaSkeletalRelative_isZero R A D n q hq)).isZero_homology

/-- Skeletal Δ-homology in its sole possible degree is the direct sum of A
over the n-simplex labels. This is the combinatorial side of the comparison. -/
def deltaSkeletalHomologyIso (D : DeltaComplex.{w}) (n : ℕ) :
    (deltaSkeletalRelative R A D n).homology n ≅ ModuleCat.of R (D.Simplex n →₀ A) :=
  (ShortComplex.HomologyData.ofZeros ((deltaSkeletalRelative R A D n).sc n)
    (deltaSkeletalRelative_d_zero R A D n _ _)
    (deltaSkeletalRelative_d_zero R A D n _ _)).left.homologyIso ≪≫
    (deltaSkeletalTopEquiv R A D n).toModuleIso


/-- The canonical increasing-order Δ-model reuses the oriented chain complex
itself: both its labels and its signed face differential are definitionally
identical. This does not assert a realization or comparison isomorphism. -/
theorem canonicalOrderedComplex_eq {V : Type w} (K : AbstractSimplicialComplex V) :
    deltaComplex R A (orderedDelta K (P202Specs.OrientedSimplicialAlgebra.vertexOrder V)) =
      P202Specs.OrientedSimplicialAlgebra.complex R A (K := K) := rfl

theorem canonicalOrderedRelativeComplex_eq {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) :
    deltaRelativeComplex R A (orderedDelta K (P202Specs.OrientedSimplicialAlgebra.vertexOrder V))
      (orderedSubcomplex K B (P202Specs.OrientedSimplicialAlgebra.vertexOrder V)) =
      Simplicial.relativeComplex R A K B := rfl

theorem canonicalOrderedAffine_eq {V : Type w} (K : AbstractSimplicialComplex V) (n : ℕ) :
    orderedAffineLinear R A K (P202Specs.OrientedSimplicialAlgebra.vertexOrder V) n =
      Simplicial.affineLinear K R A n := rfl



/-! Canonical bridge to the upstream categorical relative singular complexes. -/

def singularRelativeDegreeEquiv (X : TopCat.{w}) (Y : Set X) (n : ℕ) :
    (P202Specs.RelativeSingularChains.nonnegative R A ⟨X, Y⟩).X n ≃ₗ[R]
      (singularRelativeComplex R A X Y).X n :=
  P202Specs.RelativeSingularChains.chainQuotientEquiv R A ⟨X, Y⟩ n ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (P202.SimplicialChains.singularSelection_range R A X Y n)

@[simp] theorem singularRelativeDegreeEquiv_projection (X : TopCat.{w}) (Y : Set X)
    (n : ℕ) (c : Chains A X n) :
    singularRelativeDegreeEquiv R A X Y n
      ((P202Specs.RelativeSingularChains.projection (chainFunctor R A) ⟨X, Y⟩).f n c) =
      ((singularSelection R A X Y).module n).mkQ c := by
  have h := congrArg (fun f => f c)
    (PreservesCokernel.π_iso_hom (HomologicalComplex.eval (ModuleCat R) _ n)
      (P202Specs.RelativeSingularChains.inclusion (chainFunctor R A) ⟨X, Y⟩))
  change ((P202Specs.RelativeSingularChains.degreeQuotientIso (chainFunctor R A) ⟨X, Y⟩ n).hom)
    ((P202Specs.RelativeSingularChains.projection (chainFunctor R A) ⟨X, Y⟩).f n c) =
      cokernel.π ((P202Specs.RelativeSingularChains.inclusion (chainFunctor R A) ⟨X, Y⟩).f n) c at h
  change (Submodule.quotEquivOfEq _ _
      (P202.SimplicialChains.singularSelection_range R A X Y n))
    ((ModuleCat.cokernelIsoRangeQuotient _).hom
      ((P202Specs.RelativeSingularChains.degreeQuotientIso (chainFunctor R A) ⟨X,Y⟩ n).hom
        ((P202Specs.RelativeSingularChains.projection (chainFunctor R A) ⟨X,Y⟩).f n c))) = _
  rw [h]
  have hπ := congrArg (fun f : (complex R A X).X n ⟶ _ => f c)
    (ModuleCat.cokernel_π_cokernelIsoRangeQuotient_hom
      ((P202Specs.RelativeSingularChains.inclusion (chainFunctor R A) ⟨X,Y⟩).f n))
  dsimp only [ModuleCat.comp_apply] at hπ
  erw [hπ]
  rfl

def singularRelativeIso (X : TopCat.{w}) (Y : Set X) :
    P202Specs.RelativeSingularChains.nonnegative R A ⟨X, Y⟩ ≅
      singularRelativeComplex R A X Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (singularRelativeDegreeEquiv R A X Y n).toModuleIso) (by
      intro i j hij
      symm
      apply (cancel_epi ((P202Specs.RelativeSingularChains.projection
        (chainFunctor R A) ⟨X,Y⟩).f i)).mp
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change singularRelativeDegreeEquiv R A X Y j
        (((P202Specs.RelativeSingularChains.nonnegative R A ⟨X,Y⟩).d i j).hom
          ((P202Specs.RelativeSingularChains.projection (chainFunctor R A) ⟨X,Y⟩).f i c)) =
        ((singularRelativeComplex R A X Y).d i j).hom
          (singularRelativeDegreeEquiv R A X Y i
            ((P202Specs.RelativeSingularChains.projection (chainFunctor R A) ⟨X,Y⟩).f i c))
      have hc := congrArg (fun f => f c)
        ((P202Specs.RelativeSingularChains.projection (chainFunctor R A) ⟨X,Y⟩).comm i j).symm
      change (P202Specs.RelativeSingularChains.projection (chainFunctor R A) ⟨X,Y⟩).f j
        ((complex R A X).d i j c) =
        (P202Specs.RelativeSingularChains.nonnegative R A ⟨X,Y⟩).d i j
          ((P202Specs.RelativeSingularChains.projection (chainFunctor R A) ⟨X,Y⟩).f i c) at hc
      rw [← hc, singularRelativeDegreeEquiv_projection, singularRelativeDegreeEquiv_projection]
      obtain rfl : i = j+1 := by simpa using hij.symm
      exact congrArg (fun f : (complex R A X).X (j+1) ⟶ _ => f c)
        (((singularSelection R A X Y).projection).comm (j+1) j).symm)

@[reassoc (attr := simp)] theorem singularRelativeIso_projection (X : TopCat.{w}) (Y : Set X) :
    P202Specs.RelativeSingularChains.projection (chainFunctor R A) ⟨X,Y⟩ ≫
      (singularRelativeIso R A X Y).hom = (singularSelection R A X Y).projection := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact singularRelativeDegreeEquiv_projection R A X Y n

/-- The bridge intertwines the same continuous map of pairs on both models. -/
theorem singularRelativeIso_natural {X Z : TopCat.{w}} (Y : Set X) (W : Set Z)
    (g : X ⟶ Z) (hg : ∀ x ∈ Y, g x ∈ W) :
    P202Specs.RelativeSingularChains.relativeMap (chainFunctor R A)
        (⟨g, fun x hx => hg x hx⟩ :
          (⟨X,Y⟩ : P202Specs.RelativeSingularChains.Pair) ⟶ ⟨Z,W⟩) ≫
      (singularRelativeIso R A Z W).hom =
    (singularRelativeIso R A X Y).hom ≫ singularPairMap R A Y W g hg := by
  apply (cancel_epi (P202Specs.RelativeSingularChains.projection (chainFunctor R A) ⟨X,Y⟩)).mp
  rw [← Category.assoc, P202Specs.RelativeSingularChains.projection_map,
    Category.assoc, singularRelativeIso_projection, ← Category.assoc,
    singularRelativeIso_projection]
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  rfl


/-! Strict naturality for simplicial maps preserving the chosen vertex orders. -/

def imageSimplexOfStrictMono {V W : Type w} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (hf : StrictMono f.vertices) {n : ℕ}
    (s : P202Specs.OrientedSimplicialAlgebra.Simplex K n) :
    P202Specs.OrientedSimplicialAlgebra.Simplex L n :=
  ⟨s.1.trans (OrderEmbedding.ofStrictMono f.vertices hf), by
    change Finset.univ.image (f.vertices ∘ s.1) ∈ L.simplices
    simpa only [Finset.image_image] using f.map_simplex _ s.2⟩

theorem pushforward_strictMono_single {V W : Type w} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (hf : StrictMono f.vertices) (n : ℕ)
    (s : P202Specs.OrientedSimplicialAlgebra.Simplex K n) (a : A) :
    P202Specs.OrientedSimplicialAlgebra.pushforward R A f n (Finsupp.single s a) =
      Finsupp.single (imageSimplexOfStrictMono f hf s) a := by
  rw [P202.SimplicialChains.Oriented.pushforward_single]
  exact P202.SimplicialChains.Oriented.oriented_increasing A
    (imageSimplexOfStrictMono f hf s) a

theorem simplicialAffine_natural_of_strictMono {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (hf : StrictMono f.vertices)
    (g : TopCat.of K.Realization ⟶ TopCat.of L.Realization)
    (hg : ∀ x, (g x).val = x.val.map f.vertices) (n : ℕ) :
    (Simplicial.affineLinear L R A n).comp
        (P202Specs.OrientedSimplicialAlgebra.pushforward R A f n) =
      (((chainMap R A g).f n).hom).comp (Simplicial.affineLinear K R A n) := by
  apply Finsupp.lhom_ext
  intro s a
  change Simplicial.affineLinear L R A n
      (P202Specs.OrientedSimplicialAlgebra.pushforward R A f n (Finsupp.single s a)) =
    ((chainMap R A g).f n).hom (Simplicial.affineLinear K R A n (Finsupp.single s a))
  erw [pushforward_strictMono_single R A f hf,
    P202.SimplicialChains.Simplicial.affineLinear_single,
    P202.SimplicialChains.Simplicial.affineLinear_single,
    P202.SingularChains.chainMap_single]
  congr 1
  apply (simplexEquiv (TopCat.of L.Realization) n).injective
  rw [P202.SingularChains.simplexEquiv_postcomp]
  ext t
  apply Subtype.ext
  change (Simplicial.parametrization L n _ t).val =
    (g (Simplicial.parametrization K n s t)).val
  rw [hg, P202.SimplicialChains.Simplicial.parametrization_value,
    P202.SimplicialChains.Simplicial.parametrization_value,
    Convexity.StdSimplex.map_map]
  rfl

/-- Strict absolute naturality when the vertex map preserves the chosen orders. -/
theorem simplicialStrictMono_absolute_square {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (B : Simplicial.Subcomplex K) (E : Simplicial.Subcomplex L)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (hf : StrictMono f.vertices)
    (g : TopCat.of K.Realization ⟶ TopCat.of L.Realization)
    (hg : ∀ x, (g x).val = x.val.map f.vertices)
    (T : P202Specs.OrientedSimplicialAlgebra.complex R A (K := K) ⟶
      P202Specs.OrientedSimplicialAlgebra.complex R A (K := L))
    (hT : ∀ n, (T.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward R A f n)
    (F : SimplicialComparisonData R A K B) (G : SimplicialComparisonData R A L E) :
    T ≫ G.absolute = F.absolute ≫ chainMap R A g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  change ((G.absolute.f n).hom).comp (T.f n).hom =
    (((chainMap R A g).f n).hom).comp (F.absolute.f n).hom
  rw [G.absolute_formula, F.absolute_formula, hT]
  exact simplicialAffine_natural_of_strictMono R A K L f hf g hg n

/-- The same strict square descends to every pair preserved by the map. -/
theorem simplicialStrictMono_relative_square {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (B : Simplicial.Subcomplex K) (E : Simplicial.Subcomplex L)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (hf : StrictMono f.vertices)
    (g : TopCat.of K.Realization ⟶ TopCat.of L.Realization)
    (hg : ∀ x, (g x).val = x.val.map f.vertices)
    (Trel : Simplicial.relativeComplex R A K B ⟶ Simplicial.relativeComplex R A L E)
    (grel : singularRelativeComplex R A (TopCat.of K.Realization) (B.carrier K) ⟶
      singularRelativeComplex R A (TopCat.of L.Realization) (E.carrier L))
    (hTrel : ∀ n x, (Trel.f n).hom (((Simplicial.selection R A K B).module n).mkQ x) =
      ((Simplicial.selection R A L E).module n).mkQ
        (P202Specs.OrientedSimplicialAlgebra.pushforward R A f n x))
    (hgrel : ∀ n x, (grel.f n).hom
        (((singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module n).mkQ x) =
      ((singularSelection R A (TopCat.of L.Realization) (E.carrier L)).module n).mkQ
        (((chainMap R A g).f n).hom x))
    (F : SimplicialComparisonData R A K B) (G : SimplicialComparisonData R A L E) :
    Trel ≫ G.relative = F.relative ≫ grel := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := ((Simplicial.selection R A K B).module n).mkQ_surjective x
  change (G.relative.f n).hom ((Trel.f n).hom _) =
    (grel.f n).hom ((F.relative.f n).hom _)
  rw [hTrel, G.relative_formula, F.relative_formula, hgrel]
  exact congrArg ((singularSelection R A (TopCat.of L.Realization) (E.carrier L)).module n).mkQ
    (congrArg (fun M => M x) (simplicialAffine_natural_of_strictMono R A K L f hf g hg n))




/-! Intrinsic Δ-subcomplex realizations and their carriers have the same topology. -/
open _root_.Topology P202.Topology.DeltaSupport

theorem deltaSubcomplexRealization_injective (D : DeltaComplex.{w}) (B : DeltaSubcomplex D) :
    Function.Injective (deltaRealization B.inclusion) := by
  intro x y h
  obtain ⟨n, s, t, ht, rfl⟩ := P202.Topology.deltaInteriorCover B.asComplex x
  obtain ⟨m, r, z, hz, rfl⟩ := P202.Topology.deltaInteriorCover B.asComplex y
  have he := P202.Topology.DeltaSupport.interior_quotient_unique D ht hz h
  have hnm : n = m := congrArg Sigma.fst he
  subst m
  have hsr : s.1 = r.1 := by
    exact (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).1
  have htz : t = z := by
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
  have hsr' : s = r := Subtype.ext hsr
  subst r
  subst z
  rfl

theorem deltaSubcomplexRealization_range (D : DeltaComplex.{w}) (B : DeltaSubcomplex D) :
    Set.range (deltaRealization B.inclusion) = B.carrier := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨n,s,t⟩, rfl⟩ := Quotient.mk_surjective y
    exact ⟨n,s.1,s.2,t,rfl⟩
  · rintro ⟨n,s,hs,t,rfl⟩
    exact ⟨B.asComplex.simplexChart n ⟨s,hs⟩ t, rfl⟩

/-- A point of a face-closed realization that lands on an ambient simplex
already lies on one of its selected ordered faces. -/
theorem deltaSubcomplexRealization_over_chart (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) (n : ℕ) (s : D.Simplex n)
    (x : B.asComplex.Realization) (t : StandardSimplex n)
    (h : deltaRealization B.inclusion x = D.simplexChart n s t) :
    ∃ (m : ℕ) (a : Fin (m+1) ↪o Fin (n+1))
      (ha : D.face a s ∈ B.selected m) (u : StandardSimplex m),
      B.asComplex.simplexChart m ⟨D.face a s,ha⟩ u = x ∧ orderedAffineFace a u = t := by
  obtain ⟨m,r,u,hu,rfl⟩ := P202.Topology.deltaInteriorCover B.asComplex x
  obtain ⟨k,_,a,z,hz,hzt⟩ := exists_interior_face t
  have hface : D.simplexChart k (D.face a s) z = D.simplexChart n s t :=
    (Quotient.sound (Relation.EqvGen.rel _ _
      (DeltaComplex.FaceRelation.face a s z))).trans (congrArg (D.simplexChart n s) hzt)
  have he := interior_quotient_unique D hu hz (h.trans hface.symm)
  have hmk : m = k := congrArg Sigma.fst he
  subst k
  have hlabel : r.1 = D.face a s := (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).1
  have hpoint : u = z := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).2
  have ha : D.face a s ∈ B.selected m := hlabel ▸ r.2
  refine ⟨m,a,ha,u,?_,hpoint ▸ hzt⟩
  congr 1
  exact Subtype.ext hlabel.symm


/-- The chart preimage of a selected realization is a finite union of
selected closed face images. This retains repeated face labels. -/
theorem deltaSubcomplexRealization_chart_preimage (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) (n : ℕ) (s : D.Simplex n)
    (C : Set B.asComplex.Realization) :
    D.simplexChart n s ⁻¹' (deltaRealization B.inclusion '' C) =
      ⋃ (m : Fin (n+1)) (a : Fin (m.1+1) ↪o Fin (n+1))
        (ha : D.face a s ∈ B.selected m.1),
        orderedAffineFace a '' ((B.asComplex.simplexChart m.1 ⟨D.face a s,ha⟩) ⁻¹' C) := by
  ext t
  constructor
  · rintro ⟨x,hx,hxt⟩
    obtain ⟨m,a,ha,u,rfl,htu⟩ := deltaSubcomplexRealization_over_chart D B n s x t hxt
    have hm : m < n+1 := Nat.lt_succ_of_le (Nat.le_of_succ_le_succ (by
      simpa using Fintype.card_le_of_injective a a.injective))
    exact Set.mem_iUnion.mpr ⟨⟨m,hm⟩, Set.mem_iUnion.mpr ⟨a,
      Set.mem_iUnion.mpr ⟨ha, ⟨u,hx,htu⟩⟩⟩⟩
  · intro ht
    obtain ⟨m,ht⟩ := Set.mem_iUnion.mp ht
    obtain ⟨a,ht⟩ := Set.mem_iUnion.mp ht
    obtain ⟨ha,u,hu,rfl⟩ := Set.mem_iUnion.mp ht
    exact ⟨B.asComplex.simplexChart m.1 ⟨D.face a s,ha⟩ u, hu,
      Quotient.sound (Relation.EqvGen.rel _ _ (DeltaComplex.FaceRelation.face a s u))⟩

/-- Every face-closed Δ-subcomplex has precisely its intrinsic weak topology
inside the ambient weak realization, without a finiteness assumption. -/
theorem deltaSubcomplexRealization_isClosedMap (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) : IsClosedMap (deltaRealization B.inclusion) := by
  intro C hC
  apply (P202.Topology.deltaProjectionQuotient D).isCoinducing.isClosed_preimage.mp
  apply isClosed_sigma_iff.mpr
  intro n
  apply isClosed_sigma_iff.mpr
  intro s
  change IsClosed (D.simplexChart n s ⁻¹' (deltaRealization B.inclusion '' C))
  letI : T2Space (StandardSimplex n) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n+1))).t2Space
  rw [deltaSubcomplexRealization_chart_preimage]
  apply isClosed_iUnion_of_finite
  intro m
  apply isClosed_iUnion_of_finite
  intro a
  apply isClosed_iUnion_of_finite
  intro ha
  exact ((hC.preimage (P202.Topology.deltaChartContinuous B.asComplex m.1
    ⟨D.face a s,ha⟩)).isCompact.image
      (Convexity.StdSimplex.continuous_map ℝ a)).isClosed

/-- The canonical inclusion of any Δ-subcomplex is a closed embedding. -/
theorem deltaSubcomplexRealization_isClosedEmbedding (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) : IsClosedEmbedding (deltaRealization B.inclusion) := by
  exact IsClosedEmbedding.of_continuous_injective_isClosedMap
    (deltaRealization B.inclusion).hom.continuous
    (deltaSubcomplexRealization_injective D B)
    (deltaSubcomplexRealization_isClosedMap D B)

/-- Intrinsic realization and actual carrier agree homeomorphically through
the canonical realization map. -/
def deltaSubcomplexRealizationHomeomorph (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) : B.asComplex.Realization ≃ₜ B.carrier :=
  (deltaSubcomplexRealization_isClosedEmbedding D B).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (deltaSubcomplexRealization_range D B))




/-! Transport of the full simplex hypotheses to the comparison quotient model. -/

def ordinaryRelativeExtensionIso (X : TopCat.{w}) (Y : Set X) :
    P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩ ≅
      (P202Specs.RelativeSingularChains.nonnegative R A ⟨X,Y⟩).extend (degreeEmbedding 0) :=
  P202.GoodPairQuotient.nonnegativeExtensionIso _ _
    (P202Specs.RelativeSingularChains.ordinaryDegreeIso R A ⟨X,Y⟩)
    (fun i hi => (P202.RelativeSingularChains.ordinary_negative R A ⟨X,Y⟩ i hi).1)
    (P202.RelativeSingularChains.ordinary_boundary R A ⟨X,Y⟩)

/-- The integer-indexed relative homology used by the sphere premises is the
same homology as the supported nonnegative quotient used by the comparison. -/
def singularRelativeHomologyIso (X : TopCat.{w}) (Y : Set X) (n : ℕ) :
    P202Specs.RelativeSingularChains.relativeHomology R A ⟨X,Y⟩ (n : ℤ) ≅
      (singularRelativeComplex R A X Y).homology n :=
  HomologicalComplex.homologyMapIso (ordinaryRelativeExtensionIso R A X Y) (n : ℤ) ≪≫
    (P202Specs.RelativeSingularChains.nonnegative R A ⟨X,Y⟩).extendHomologyIso
      (degreeEmbedding 0) (by change (0 : ℤ) + n = n; omega) ≪≫
    HomologicalComplex.homologyMapIso (singularRelativeIso R A X Y) n

theorem simplexRelativeHomology_vanish
    (hvanishing : P202Specs.SpheresDisks.simplexVanishing_type.{u,v})
    (n j : ℕ) (hj : j ≠ n) :
    IsZero ((singularRelativeComplex R A (P202Specs.SpheresDisks.simplex n)
      (P202Specs.SpheresDisks.simplexPair n).subspace).homology j) :=
  (singularRelativeHomologyIso R A _ _ j).isZero_iff.mp (hvanishing R A n j hj)



/-- Formal affine tuples, indexed by their number of vertices. Index zero is
augmentation degree -1. Entries may repeat and coefficients form any module. -/
abbrev TupleChains (Y : Type w) (n : ℕ) := (Fin n → Y) →₀ A

def tupleBoundary (Y : Type w) (n : ℕ) :
    TupleChains A Y (n+1) →ₗ[R] TupleChains A Y n :=
  ∑ i : Fin (n+1), (-1 : ℤ)^i.val •
    Finsupp.lmapDomain A R (fun t => t ∘ i.succAbove)

def tupleCone {Y : Type w} (b : Y) (n : ℕ) :
    TupleChains A Y n →ₗ[R] TupleChains A Y (n+1) :=
  Finsupp.lmapDomain A R (fun t => Fin.cons b t)

@[simp] theorem tupleBoundary_single {Y : Type w} (n : ℕ)
    (t : Fin (n+1) → Y) (a : A) :
    tupleBoundary R A Y n (Finsupp.single t a) =
      ∑ i : Fin (n+1), (-1 : ℤ)^i.val • Finsupp.single (t ∘ i.succAbove) a := by
  simp [tupleBoundary, LinearMap.sum_apply, LinearMap.smul_apply]

@[simp] theorem tupleCone_single {Y : Type w} (b : Y) (n : ℕ)
    (t : Fin n → Y) (a : A) :
    tupleCone R A b n (Finsupp.single t a) = Finsupp.single (Fin.cons b t) a := by
  simp [tupleCone]

/-- Cone contraction in augmentation degree -1. -/
theorem tupleBoundary_cone_zero {Y : Type w} (b : Y) (c : TupleChains A Y 0) :
    tupleBoundary R A Y 0 (tupleCone R A b 0 c) = c := by
  have h : (tupleBoundary R A Y 0).comp (tupleCone R A b 0) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro t a
    change tupleBoundary R A Y 0 (tupleCone R A b 0 (Finsupp.single t a)) = Finsupp.single t a
    rw [tupleCone_single, tupleBoundary_single, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul]
    congr 1
  exact LinearMap.congr_fun h c

/-- The signed cone identity, including repeated tuple entries and all module
coefficients. It is the local filling operation used in carrier homotopies. -/
theorem tupleBoundary_cone {Y : Type w} (b : Y) (n : ℕ)
    (c : TupleChains A Y (n+1)) :
    tupleBoundary R A Y (n+1) (tupleCone R A b (n+1) c) =
      c - tupleCone R A b n (tupleBoundary R A Y n c) := by
  have h : (tupleBoundary R A Y (n+1)).comp (tupleCone R A b (n+1)) =
      LinearMap.id - (tupleCone R A b n).comp (tupleBoundary R A Y n) := by
    apply Finsupp.lhom_ext
    intro t a
    change tupleBoundary R A Y (n+1) (tupleCone R A b (n+1) (Finsupp.single t a)) =
      Finsupp.single t a - tupleCone R A b n (tupleBoundary R A Y n (Finsupp.single t a))
    rw [tupleCone_single, tupleBoundary_single, Fin.sum_univ_succ,
      tupleBoundary_single, map_sum]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.succAbove_zero,
      Fin.cons_comp_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul,
      map_zsmul, tupleCone_single, Fin.cons_comp_succ_succAbove,
      ← Finset.sum_neg_distrib, sub_eq_add_neg]
    rfl
  exact LinearMap.congr_fun h c

theorem tupleBoundary_squared {Y : Type w} (n : ℕ)
    (c : TupleChains A Y (n+2)) :
    tupleBoundary R A Y n (tupleBoundary R A Y (n+1) c) = 0 := by
  induction n with
  | zero =>
    have h : (tupleBoundary R A Y 0).comp (tupleBoundary R A Y 1) = 0 := by
      apply Finsupp.lhom_ext
      intro t a
      have ht : t = Fin.cons (t 0) (fun i => t i.succ) := (Fin.cons_self_tail t).symm
      rw [ht, ← tupleCone_single R A (t 0) 1]
      rw [LinearMap.comp_apply, tupleBoundary_cone, map_sub, tupleBoundary_cone_zero]
      simp
    exact LinearMap.congr_fun h c
  | succ n ih =>
    have h : (tupleBoundary R A Y (n+1)).comp (tupleBoundary R A Y (n+2)) = 0 := by
      apply Finsupp.lhom_ext
      intro t a
      have ht : t = Fin.cons (t 0) (fun i => t i.succ) := (Fin.cons_self_tail t).symm
      rw [ht, ← tupleCone_single R A (t 0) (n+2)]
      rw [LinearMap.comp_apply, tupleBoundary_cone, map_sub, tupleBoundary_cone, ih]
      simp
    exact LinearMap.congr_fun h c

/-- A recursive cone homotopy from a tuple chain endomorphism to the identity.
No geometric structure on Y is needed: all operations are formal affine tuples. -/
def tupleHomotopy {Y : Type w}
    (N : ∀ n, TupleChains A Y n →ₗ[R] TupleChains A Y n) :
    ∀ n, TupleChains A Y n →ₗ[R] TupleChains A Y (n+1) :=
  Nat.rec (motive := fun n => TupleChains A Y n →ₗ[R] TupleChains A Y (n+1)) 0
    (fun n H => Finsupp.lsum R fun t =>
      (tupleCone R A (t 0) (n+1)).comp
        (((N (n+1) - LinearMap.id) -
          H.comp (tupleBoundary R A Y n)).comp (Finsupp.lsingle t)))

@[simp] theorem tupleHomotopy_single {Y : Type w}
    (N : ∀ n, TupleChains A Y n →ₗ[R] TupleChains A Y n)
    (n : ℕ) (t : Fin (n+1) → Y) (a : A) :
    tupleHomotopy R A N (n+1) (Finsupp.single t a) =
      tupleCone R A (t 0) (n+1)
        (N (n+1) (Finsupp.single t a) - Finsupp.single t a -
          tupleHomotopy R A N n (tupleBoundary R A Y n (Finsupp.single t a))) := by
  simp [tupleHomotopy, Finsupp.lsum_single]


/-- Every tuple chain endomorphism inducing the identity on the augmentation is
chain homotopic to the identity through the explicit recursive cone operator. -/
theorem tupleHomotopy_identity {Y : Type w}
    (N : ∀ n, TupleChains A Y n →ₗ[R] TupleChains A Y n)
    (hzero : N 0 = LinearMap.id)
    (hN : ∀ n c, tupleBoundary R A Y n (N (n+1) c) =
      N n (tupleBoundary R A Y n c)) (n : ℕ) (c : TupleChains A Y (n+1)) :
    tupleBoundary R A Y (n+1) (tupleHomotopy R A N (n+1) c) +
      tupleHomotopy R A N n (tupleBoundary R A Y n c) = N (n+1) c - c := by
  induction n with
  | zero =>
    have h : (tupleBoundary R A Y 1).comp (tupleHomotopy R A N 1) +
        (tupleHomotopy R A N 0).comp (tupleBoundary R A Y 0) = N 1 - LinearMap.id := by
      apply Finsupp.lhom_ext
      intro t a
      change tupleBoundary R A Y 1 (tupleHomotopy R A N 1 (Finsupp.single t a)) +
        tupleHomotopy R A N 0 (tupleBoundary R A Y 0 (Finsupp.single t a)) = _
      rw [tupleHomotopy_single, tupleBoundary_cone]
      have hcycle : tupleBoundary R A Y 0
          (N 1 (Finsupp.single t a) - Finsupp.single t a -
            tupleHomotopy R A N 0 (tupleBoundary R A Y 0 (Finsupp.single t a))) = 0 := by
        simp only [tupleHomotopy, Nat.rec_zero, LinearMap.zero_apply, sub_zero, map_sub, hN, hzero,
          LinearMap.id_apply, sub_self]
      rw [hcycle, map_zero]
      simp [tupleHomotopy]
    exact LinearMap.congr_fun h c
  | succ n ih =>
    have h : (tupleBoundary R A Y (n+2)).comp (tupleHomotopy R A N (n+2)) +
        (tupleHomotopy R A N (n+1)).comp (tupleBoundary R A Y (n+1)) =
          N (n+2) - LinearMap.id := by
      apply Finsupp.lhom_ext
      intro t a
      change tupleBoundary R A Y (n+2) (tupleHomotopy R A N (n+2) (Finsupp.single t a)) +
        tupleHomotopy R A N (n+1) (tupleBoundary R A Y (n+1) (Finsupp.single t a)) = _
      rw [tupleHomotopy_single, tupleBoundary_cone]
      have hcycle : tupleBoundary R A Y (n+1)
          (N (n+2) (Finsupp.single t a) - Finsupp.single t a -
            tupleHomotopy R A N (n+1)
              (tupleBoundary R A Y (n+1) (Finsupp.single t a))) = 0 := by
        rw [map_sub, map_sub, hN]
        have hi := ih (tupleBoundary R A Y (n+1) (Finsupp.single t a))
        rw [tupleBoundary_squared, map_zero, add_zero] at hi
        rw [hi, sub_self]
      rw [hcycle, map_zero]
      simp only [LinearMap.sub_apply, LinearMap.id_apply]
      abel
    exact LinearMap.congr_fun h c


/-- Tuples supported in a fixed set of vertices. -/
def tupleSupported (Y : Type w) (S : Set Y) (n : ℕ) : Submodule R (TupleChains A Y n) :=
  Finsupp.supported A R {t | ∀ i, t i ∈ S}

theorem tupleBoundary_preserves {Y : Type w} (S : Set Y) (n : ℕ)
    (c : TupleChains A Y (n+1)) (hc : c ∈ tupleSupported R A Y S (n+1)) :
    tupleBoundary R A Y n c ∈ tupleSupported R A Y S n := by
  apply P202Specs.RelativeParametrizations.map_supported R A _ _ (tupleBoundary R A Y n) ?_ c hc
  intro t ht a
  rw [tupleBoundary_single]
  apply Submodule.sum_mem
  intro i _
  exact (tupleSupported R A Y S n).toAddSubgroup.zsmul_mem (Finsupp.single_mem_supported (M := A) R a (fun j => ht (i.succAbove j))) _

theorem tupleCone_preserves {Y : Type w} (S : Set Y) (b : Y) (hb : b ∈ S)
    (n : ℕ) (c : TupleChains A Y n) (hc : c ∈ tupleSupported R A Y S n) :
    tupleCone R A b n c ∈ tupleSupported R A Y S (n+1) := by
  apply P202Specs.RelativeParametrizations.map_supported R A _ _ (tupleCone R A b n) ?_ c hc
  intro t ht a
  rw [tupleCone_single]
  apply Finsupp.single_mem_supported
  intro i
  exact Fin.cases hb (fun j => ht j) i

/-- The recursive homotopy stays inside every carrier preserved by N. -/
theorem tupleHomotopy_preserves {Y : Type w}
    (N : ∀ n, TupleChains A Y n →ₗ[R] TupleChains A Y n) (S : Set Y)
    (hN : ∀ n c, c ∈ tupleSupported R A Y S n → N n c ∈ tupleSupported R A Y S n)
    (n : ℕ) (c : TupleChains A Y n) (hc : c ∈ tupleSupported R A Y S n) :
    tupleHomotopy R A N n c ∈ tupleSupported R A Y S (n+1) := by
  induction n with
  | zero => exact Submodule.zero_mem _
  | succ n ih =>
    apply P202Specs.RelativeParametrizations.map_supported R A _ _
      (tupleHomotopy R A N (n+1)) ?_ c hc
    intro t ht a
    rw [tupleHomotopy_single]
    apply tupleCone_preserves R A S (t 0) (ht 0)
    have hs : Finsupp.single t a ∈ tupleSupported R A Y S (n+1) :=
      Finsupp.single_mem_supported (M := A) R a ht
    exact Submodule.sub_mem _ (Submodule.sub_mem _ (hN _ _ hs) hs)
      (ih _ (tupleBoundary_preserves R A S n _ hs))




section
open P202Specs.OrientedSimplicialAlgebra
def orderedTuple {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) {n : ℕ} (s : (orderedDelta K o).Simplex n) : VertexTuple K n :=
  ⟨s.1, by
    convert s.2 using 1
    ext x
    simp only [Finset.mem_image]⟩

def orderReturnLinear {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) : DeltaChains A (orderedDelta K o) n →ₗ[R] Chains K A n :=
  Finsupp.lsum R fun s => {
    toFun := fun a => oriented A (orderedTuple K o s) a
    map_add' := by
      classical
      intros; simp only [oriented]; split <;> simp [Finsupp.single_add, smul_add]
    map_smul' := by
      classical
      intro r a; simp only [oriented]; split <;> simp [Finsupp.single_smul, smul_comm r] }

@[simp] theorem orderReturnLinear_single {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) (s : (orderedDelta K o).Simplex n) (a : A) :
    orderReturnLinear R A K o n (Finsupp.single s a) = oriented A (orderedTuple K o s) a := by
  rw [orderReturnLinear, Finsupp.lsum_single]; rfl

@[simp] theorem orderTransitionLinear_single {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) (s : Simplex K n) (a : A) :
    orderTransitionLinear R A K o n (Finsupp.single s a) =
      (Equiv.Perm.sign (sortingPermutation o s.1) : ℤ) • Finsupp.single (reorderedSimplex o s) a := by
  rw [orderTransitionLinear, Finsupp.lsum_single]; rfl

theorem orderReturn_boundary {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) :
    (boundary R A n).comp (orderReturnLinear R A K o (n+1)) =
      (orderReturnLinear R A K o n).comp (deltaBoundary R A (orderedDelta K o) n) := by
  classical
  apply Finsupp.lhom_ext
  intro s a
  simp only [LinearMap.comp_apply, orderReturnLinear_single]
  rw [P202.OrientedSimplicialAlgebra.boundary_oriented]
  simp only [deltaBoundary, LinearMap.sum_apply, LinearMap.smul_apply,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, map_sum, map_zsmul,
    orderReturnLinear_single]
  rfl

def orderReturnChainMap {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) : deltaComplex R A (orderedDelta K o) ⟶ complex R A (K := K) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (orderReturnLinear R A K o n)) (by
    intro n
    apply ModuleCat.hom_ext
    change (((complex R A (K := K)).d (n+1) n).hom).comp (orderReturnLinear R A K o (n+1)) =
      (orderReturnLinear R A K o n).comp (((deltaComplex R A (orderedDelta K o)).d (n+1) n).hom)
    rw [P202.OrientedSimplicialAlgebra.boundary_eq]
    rw [P202.RelativeParametrizations.deltaBoundary_eq]
    exact orderReturn_boundary R A K o n)

theorem orderReturn_transition {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) :
    (orderReturnLinear R A K o n).comp (orderTransitionLinear R A K o n) = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext
  intro s a
  simp only [LinearMap.comp_apply, orderTransitionLinear_single, map_zsmul, orderReturnLinear_single,
    LinearMap.id_apply]
  have h : orderedTuple K o (reorderedSimplex o s) =
      permute ⟨s.1,s.2⟩ (sortingPermutation o s.1) := rfl
  rw [h, P202.OrientedSimplicialAlgebra.oriented_permute,
    P202.OrientedSimplicialAlgebra.oriented_increasing]
  rw [← mul_smul]
  simp

theorem ordered_sort_inverse {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) {n : ℕ} (s : (orderedDelta K o).Simplex n) :
    sortingPermutation o (sorted (orderedTuple K o s) s.1.injective).1 =
      (@Tuple.sort (n+1) V (vertexOrder V) (orderedTuple K o s).1).symm := by
  let σ := @Tuple.sort (n+1) V (vertexOrder V) (orderedTuple K o s).1
  have ht : ((sorted (orderedTuple K o s) s.1.injective).1 : Fin (n+1) → V) =
      (s.1 : Fin (n+1) → V) ∘ σ := by
    dsimp only [sorted, orderedTuple, OrderEmbedding.coe_ofStrictMono]
    rfl
  letI := o
  change @Tuple.sort (n+1) V o _ = σ.symm
  rw [ht]
  have ho : @Tuple.sort (n+1) V o (s.1 : Fin (n+1) → V) = Equiv.refl _ :=
    Tuple.sort_eq_refl_iff_monotone.mpr s.1.monotone
  have h : σ * @Tuple.sort (n+1) V o ((s.1 : Fin (n+1) → V) ∘ σ) = Equiv.refl _ := by
    apply Equiv.ext
    intro i
    apply s.1.injective
    have hi := congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort
      (f := (s.1 : Fin (n+1) → V)) (σ := σ)) i
    simpa only [ho, Equiv.refl_apply, Function.comp_apply, Equiv.Perm.mul_apply] using hi
  calc
    @Tuple.sort (n+1) V o ((s.1 : Fin (n+1) → V) ∘ σ) =
        σ⁻¹ * (σ * @Tuple.sort (n+1) V o ((s.1 : Fin (n+1) → V) ∘ σ)) := by group
    _ = σ.symm := by rw [h]; exact mul_one σ⁻¹

theorem reordered_sorted {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) {n : ℕ} (s : (orderedDelta K o).Simplex n) :
    reorderedSimplex o (sorted (orderedTuple K o s) s.1.injective) = s := by
  apply Subtype.ext
  apply DFunLike.ext
  intro i
  change (sorted (orderedTuple K o s) s.1.injective).1
    (sortingPermutation o (sorted (orderedTuple K o s) s.1.injective).1 i) = s.1 i
  rw [ordered_sort_inverse K o s]
  dsimp only [sorted, orderedTuple, OrderEmbedding.coe_ofStrictMono]
  change s.1 ((@Tuple.sort (n+1) V (vertexOrder V) (orderedTuple K o s).1)
    ((@Tuple.sort (n+1) V (vertexOrder V) (orderedTuple K o s).1).symm i)) = s.1 i
  rw [Equiv.apply_symm_apply]

theorem orderTransition_return {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) :
    (orderTransitionLinear R A K o n).comp (orderReturnLinear R A K o n) = LinearMap.id := by
  classical
  apply Finsupp.lhom_ext
  intro s a
  simp only [LinearMap.comp_apply, orderReturnLinear_single, LinearMap.id_apply]
  have hs : Function.Injective (orderedTuple K o s).1 := s.1.injective
  rw [oriented, dif_pos hs, map_zsmul, orderTransitionLinear_single,
    ordered_sort_inverse K o s, reordered_sorted K o s]
  rw [Equiv.Perm.sign_symm, ← mul_smul]
  have hsign : (Equiv.Perm.sign (@Tuple.sort (n+1) V (vertexOrder V) (orderedTuple K o s).1) : ℤ) *
      (Equiv.Perm.sign (@Tuple.sort (n+1) V (vertexOrder V) (orderedTuple K o s).1) : ℤ) = 1 := by simp
  rw [hsign, one_smul]


theorem orderReturn_injective {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) : Function.Injective (orderReturnLinear R A K o n) := by
  intro x y h
  have ht := congrArg (orderTransitionLinear R A K o n) h
  simpa only [← LinearMap.comp_apply, orderTransition_return, LinearMap.id_apply] using ht

theorem orderTransition_boundary {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) :
    (deltaBoundary R A (orderedDelta K o) n).comp (orderTransitionLinear R A K o (n+1)) =
      (orderTransitionLinear R A K o n).comp (boundary R A n) := by
  apply LinearMap.ext
  intro x
  apply orderReturn_injective R A K o n
  have hb := LinearMap.congr_fun (orderReturn_boundary R A K o n)
    (orderTransitionLinear R A K o (n+1) x)
  change orderReturnLinear R A K o n
      (deltaBoundary R A (orderedDelta K o) n (orderTransitionLinear R A K o (n+1) x)) =
    orderReturnLinear R A K o n (orderTransitionLinear R A K o n (boundary R A n x))
  have hl := LinearMap.congr_fun (orderReturn_transition R A K o (n+1)) x
  have hr := LinearMap.congr_fun (orderReturn_transition R A K o n) (boundary R A n x)
  simp only [LinearMap.comp_apply, LinearMap.id_apply] at hb hl hr
  exact hb.symm.trans ((congrArg (boundary R A n) hl).trans hr.symm)

def orderTransitionChainMap {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) : complex R A (K := K) ⟶ deltaComplex R A (orderedDelta K o) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (orderTransitionLinear R A K o n)) (by
    intro n
    apply ModuleCat.hom_ext
    change (((deltaComplex R A (orderedDelta K o)).d (n+1) n).hom).comp
        (orderTransitionLinear R A K o (n+1)) =
      (orderTransitionLinear R A K o n).comp (((complex R A (K := K)).d (n+1) n).hom)
    rw [P202.OrientedSimplicialAlgebra.boundary_eq, P202.RelativeParametrizations.deltaBoundary_eq]
    exact orderTransition_boundary R A K o n)

def orderTransitionIso {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) : complex R A (K := K) ≅ deltaComplex R A (orderedDelta K o) where
  hom := orderTransitionChainMap R A K o
  inv := orderReturnChainMap R A K o
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact orderReturn_transition R A K o n
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    exact orderTransition_return R A K o n


theorem orderTransition_selected {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) (n : ℕ)
    (x : Chains K A n) (hx : x ∈ (Simplicial.selection R A K B).module n) :
    orderTransitionLinear R A K o n x ∈
      (deltaSelection R A (orderedDelta K o) (orderedSubcomplex K B o)).module n := by
  apply map_supported R A (B.selected K n) _ (orderTransitionLinear R A K o n) ?_ x hx
  intro s hs a
  rw [orderTransitionLinear_single]
  apply zsmul_mem
  apply Finsupp.single_mem_supported
  change Finset.univ.image (reorderedSimplex o s).1 ∈ B.complex.simplices
  change @Finset.image _ V (vertexOrder V).toDecidableEq s.1 Finset.univ ∈ B.complex.simplices at hs
  convert hs using 1
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => ⟨sortingPermutation o s.1 i, hi⟩,
    fun ⟨i, hi⟩ => ⟨(sortingPermutation o s.1).symm i, by
      change s.1 ((sortingPermutation o s.1) ((sortingPermutation o s.1).symm i)) = x
      simpa only [Equiv.apply_symm_apply] using hi⟩⟩

theorem orderReturn_selected {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) (n : ℕ)
    (x : DeltaChains A (orderedDelta K o) n)
    (hx : x ∈ (deltaSelection R A (orderedDelta K o) (orderedSubcomplex K B o)).module n) :
    orderReturnLinear R A K o n x ∈ (Simplicial.selection R A K B).module n := by
  classical
  apply map_supported R A ((orderedSubcomplex K B o).selected n) _
    (orderReturnLinear R A K o n) ?_ x hx
  intro s hs a
  rw [orderReturnLinear_single]
  have hinj : Function.Injective (orderedTuple K o s).1 := s.1.injective
  rw [oriented, dite_eq_left hinj]
  apply zsmul_mem
  apply Finsupp.single_mem_supported
  change @Finset.image _ V (vertexOrder V).toDecidableEq (sorted (orderedTuple K o s) hinj).1 Finset.univ ∈ B.complex.simplices
  change Finset.univ.image s.1 ∈ B.complex.simplices at hs
  convert hs using 1
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  let σ := @Tuple.sort (n+1) V (vertexOrder V) (orderedTuple K o s).1
  exact ⟨fun ⟨i, hi⟩ => ⟨σ i, hi⟩,
    fun ⟨i, hi⟩ => ⟨σ.symm i, by simpa only [sorted, orderedTuple,
      OrderEmbedding.coe_ofStrictMono, Function.comp_apply, σ, Equiv.apply_symm_apply] using hi⟩⟩

def orderTransitionRelativeChainMap {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) :
    Simplicial.relativeComplex R A K B ⟶
      deltaRelativeComplex R A (orderedDelta K o) (orderedSubcomplex K B o) :=
  (Simplicial.selection R A K B).quotientMap
    (deltaSelection R A (orderedDelta K o) (orderedSubcomplex K B o))
    (orderTransitionChainMap R A K o) (orderTransition_selected R A K B o)

def orderReturnRelativeChainMap {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) :
    deltaRelativeComplex R A (orderedDelta K o) (orderedSubcomplex K B o) ⟶
      Simplicial.relativeComplex R A K B :=
  (deltaSelection R A (orderedDelta K o) (orderedSubcomplex K B o)).quotientMap
    (Simplicial.selection R A K B) (orderReturnChainMap R A K o)
    (orderReturn_selected R A K B o)

def orderTransitionRelativeIso {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) :
    Simplicial.relativeComplex R A K B ≅
      deltaRelativeComplex R A (orderedDelta K o) (orderedSubcomplex K B o) where
  hom := orderTransitionRelativeChainMap R A K B o
  inv := orderReturnRelativeChainMap R A K B o
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := ((Simplicial.selection R A K B).module n).mkQ_surjective x
    change ((orderReturnRelativeChainMap R A K B o).f n).hom
      (((orderTransitionRelativeChainMap R A K B o).f n).hom
        (((Simplicial.selection R A K B).module n).mkQ x)) = _
    change ((Simplicial.selection R A K B).module n).mkQ
      ((orderReturnLinear R A K o n).comp (orderTransitionLinear R A K o n) x) = _
    rw [orderReturn_transition]
    rfl
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := ((deltaSelection R A (orderedDelta K o)
      (orderedSubcomplex K B o)).module n).mkQ_surjective x
    change ((orderTransitionRelativeChainMap R A K B o).f n).hom
      (((orderReturnRelativeChainMap R A K B o).f n).hom
        (((deltaSelection R A (orderedDelta K o)
          (orderedSubcomplex K B o)).module n).mkQ x)) = _
    change ((deltaSelection R A (orderedDelta K o) (orderedSubcomplex K B o)).module n).mkQ
      ((orderTransitionLinear R A K o n).comp (orderReturnLinear R A K o n) x) = _
    rw [orderTransition_return]
    rfl


theorem orderedParametrization_value {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) (s : (orderedDelta K o).Simplex n) (x : StandardSimplex n) :
    (orderedParametrization K o n s x).1 = x.map s.1 := by
  classical
  exact Convexity.StdSimplex.map_map _ _ _

def orderedSingularSimplex {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) (s : (orderedDelta K o).Simplex n) :=
  (P202Specs.SingularChains.simplexEquiv (TopCat.of K.Realization) n).symm
    (orderedParametrization K o n s)

theorem orderedSingularSimplex_face {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) (i : Fin (n+2)) (s : (orderedDelta K o).Simplex (n+1)) :
    orderedSingularSimplex K o n (deltaFace (orderedDelta K o) i s) =
      P202Specs.SingularChains.face i (orderedSingularSimplex K o (n+1) s) := by
  apply (P202Specs.SingularChains.simplexEquiv _ n).injective
  rw [P202.SingularChains.simplexEquiv_face]
  change orderedParametrization K o n (deltaFace (orderedDelta K o) i s) =
    (orderedParametrization K o (n+1) s).comp (P202Specs.SingularChains.faceInclusion i)
  ext x
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, orderedParametrization_value, orderedParametrization_value]
  apply Convexity.StdSimplex.ext
  change x.weights.mapDomain (deltaFace (orderedDelta K o) i s).1 =
    ((P202Specs.SingularChains.faceInclusion i x).weights).mapDomain s.1
  rw [P202.SingularChains.faceInclusion_weights, ← Finsupp.mapDomain_comp]
  rfl

@[simp] theorem orderedAffineLinear_single {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) (s : (orderedDelta K o).Simplex n) (a : A) :
    orderedAffineLinear R A K o n (Finsupp.single s a) =
      Finsupp.single (orderedSingularSimplex K o n s) a := by
  simp [orderedAffineLinear, orderedSingularSimplex]

def orderedAffineChainMap {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) : deltaComplex R A (orderedDelta K o) ⟶
      P202Specs.SingularChains.complex R A (TopCat.of K.Realization) :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom (orderedAffineLinear R A K o n)) (by
    intro n
    apply ModuleCat.hom_ext
    change (P202Specs.SingularChains.boundary R A _ n).comp
        (orderedAffineLinear R A K o (n+1)) =
      (orderedAffineLinear R A K o n).comp
        (((deltaComplex R A (orderedDelta K o)).d (n+1) n).hom)
    rw [P202.RelativeParametrizations.deltaBoundary_eq]
    apply Finsupp.lhom_ext
    intro s a
    change P202Specs.SingularChains.boundary R A _ n
        (orderedAffineLinear R A K o (n+1) (Finsupp.single s a)) =
      orderedAffineLinear R A K o n
        (deltaBoundary R A (orderedDelta K o) n (Finsupp.single s a))
    rw [orderedAffineLinear_single, P202.SingularChains.boundary_single R A,
      P202.RelativeParametrizations.deltaBoundary_single R A]
    simp only [map_sum, map_zsmul, orderedAffineLinear_single, orderedSingularSimplex_face])

theorem orderedParametrization_lands {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) (n : ℕ)
    (s : (orderedDelta K o).Simplex n) (hs : s ∈ (orderedSubcomplex K B o).selected n)
    (t : StandardSimplex n) : orderedParametrization K o n s t ∈ B.carrier K := by
  change (orderedParametrization K o n s t).1.weights.support ∈ B.complex.simplices
  rw [orderedParametrization_value]
  apply B.complex.face hs _ (Convexity.StdSimplex.support_weights_nonempty _)
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem orderedAffine_preserves {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) (n : ℕ)
    (x : DeltaChains A (orderedDelta K o) n)
    (hx : x ∈ (deltaSelection R A (orderedDelta K o) (orderedSubcomplex K B o)).module n) :
    orderedAffineLinear R A K o n x ∈
      (singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module n := by
  apply map_supported R A _ _ (orderedAffineLinear R A K o n) ?_ x hx
  intro s hs a
  rw [orderedAffineLinear_single]
  apply Finsupp.single_mem_supported
  intro t
  simpa [orderedSingularSimplex] using orderedParametrization_lands K B o n s hs t

def orderedRelativeAffineChainMap {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) :
    deltaRelativeComplex R A (orderedDelta K o) (orderedSubcomplex K B o) ⟶
      singularRelativeComplex R A (TopCat.of K.Realization) (B.carrier K) :=
  (deltaSelection R A (orderedDelta K o) (orderedSubcomplex K B o)).quotientMap
    (singularSelection R A (TopCat.of K.Realization) (B.carrier K))
    (orderedAffineChainMap R A K o) (orderedAffine_preserves R A K B o)


end


section
open P202Specs.OrientedSimplicialAlgebra
def tupleFullComplex (V : Type w) : AbstractSimplicialComplex V where
  simplices := {s | s.Nonempty}
  nonempty _ hs := hs
  face _ _ hn := hn

def fullVertexTuple {V : Type w} {n : ℕ} (t : Fin (n+1) → V) :
    VertexTuple (tupleFullComplex V) n :=
  ⟨t, Finset.image_nonempty.mpr Finset.univ_nonempty⟩

def tupleOrientedLinear (V : Type w) (n : ℕ) :
    TupleChains A V (n+1) →ₗ[R] Chains (tupleFullComplex V) A n :=
  Finsupp.lsum R fun t => {
    toFun := fun a => oriented A (fullVertexTuple t) a
    map_add' := by
      classical
      intros; simp only [oriented]; split <;> simp [Finsupp.single_add, smul_add]
    map_smul' := by
      classical
      intro r a; simp only [oriented]; split <;> simp [smul_comm r] }

@[simp] theorem tupleOrientedLinear_single (V : Type w) (n : ℕ) (t : Fin (n+1) → V) (a : A) :
    tupleOrientedLinear R A V n (Finsupp.single t a) = oriented A (fullVertexTuple t) a := by
  rw [tupleOrientedLinear, Finsupp.lsum_single]; rfl

def tupleIncreasingLinear (V : Type w) (n : ℕ) :
    Chains (tupleFullComplex V) A n →ₗ[R] TupleChains A V (n+1) :=
  Finsupp.lmapDomain A R (fun s => (s.1 : Fin (n+1) → V))

@[simp] theorem tupleIncreasingLinear_single (V : Type w) (n : ℕ)
    (s : Simplex (tupleFullComplex V) n) (a : A) :
    tupleIncreasingLinear R A V n (Finsupp.single s a) = Finsupp.single (s.1 : Fin (n+1) → V) a := by
  simp [tupleIncreasingLinear]

def tupleNormalize (V : Type w) : ∀ n, TupleChains A V n →ₗ[R] TupleChains A V n :=
  fun n => Nat.casesOn (motive := fun n => TupleChains A V n →ₗ[R] TupleChains A V n) n
    LinearMap.id (fun n => (tupleIncreasingLinear R A V n).comp (tupleOrientedLinear R A V n))

@[simp] theorem tupleNormalize_zero (V : Type w) : tupleNormalize R A V 0 = LinearMap.id := rfl

theorem tupleNormalize_single (V : Type w) (n : ℕ) (t : Fin (n+1) → V) (a : A) :
    tupleNormalize R A V (n+1) (Finsupp.single t a) =
      if ht : Function.Injective t then
        (Equiv.Perm.sign (@Tuple.sort (n+1) V (vertexOrder V) t) : ℤ) •
          Finsupp.single (t ∘ @Tuple.sort (n+1) V (vertexOrder V) t) a
      else 0 := by
  classical
  simp only [tupleNormalize, Nat.casesOn, LinearMap.comp_apply, tupleOrientedLinear_single, oriented]
  dsimp only [fullVertexTuple]
  split <;> simp only [map_zsmul, tupleIncreasingLinear_single, map_zero]
  rfl

@[simp] theorem tupleNormalize_one (V : Type w) : tupleNormalize R A V 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro t a
  have ht : Function.Injective t := by intro i j _; exact Subsingleton.elim i j
  have hs : @Tuple.sort 1 V (vertexOrder V) t = Equiv.refl _ := Subsingleton.elim _ _
  rw [tupleNormalize_single, dite_eq_left ht, hs]
  simp

theorem tupleOriented_boundary (V : Type w) (n : ℕ) :
    (boundary R A n).comp (tupleOrientedLinear R A V (n+1)) =
      (tupleOrientedLinear R A V n).comp (tupleBoundary R A V (n+1)) := by
  classical
  apply Finsupp.lhom_ext
  intro t a
  simp only [LinearMap.comp_apply, tupleOrientedLinear_single]
  rw [P202.OrientedSimplicialAlgebra.boundary_oriented, tupleBoundary_single]
  simp only [map_sum, map_zsmul, tupleOrientedLinear_single]
  rfl

theorem tupleIncreasing_boundary (V : Type w) (n : ℕ) :
    (tupleBoundary R A V (n+1)).comp (tupleIncreasingLinear R A V (n+1)) =
      (tupleIncreasingLinear R A V n).comp (boundary R A n) := by
  classical
  apply Finsupp.lhom_ext
  intro t a
  simp only [LinearMap.comp_apply, tupleIncreasingLinear_single]
  rw [P202.OrientedSimplicialAlgebra.boundary_single, tupleBoundary_single]
  simp only [map_sum, map_zsmul, tupleIncreasingLinear_single]
  rfl

theorem tupleNormalize_boundary (V : Type w) (n : ℕ) (c : TupleChains A V (n+1)) :
    tupleBoundary R A V n (tupleNormalize R A V (n+1) c) =
      tupleNormalize R A V n (tupleBoundary R A V n c) := by
  cases n with
  | zero => rw [tupleNormalize_one, tupleNormalize_zero]; rfl
  | succ n =>
    have hi := LinearMap.congr_fun (tupleIncreasing_boundary R A V n)
      (tupleOrientedLinear R A V (n+1) c)
    have ho := LinearMap.congr_fun (tupleOriented_boundary R A V n) c
    simp only [LinearMap.comp_apply] at hi ho
    change tupleBoundary R A V (n+1)
      (tupleIncreasingLinear R A V (n+1) (tupleOrientedLinear R A V (n+1) c)) =
      tupleIncreasingLinear R A V n (tupleOrientedLinear R A V n (tupleBoundary R A V (n+1) c))
    rw [hi, ho]

theorem tupleNormalize_preserves (V : Type w) (S : Set V) (n : ℕ)
    (c : TupleChains A V n) (hc : c ∈ tupleSupported R A V S n) :
    tupleNormalize R A V n c ∈ tupleSupported R A V S n := by
  cases n with
  | zero => exact hc
  | succ n =>
    apply P202Specs.RelativeParametrizations.map_supported R A _ _
      (tupleNormalize R A V (n+1)) ?_ c hc
    intro t ht a
    rw [tupleNormalize_single]
    split
    · apply zsmul_mem
      apply Finsupp.single_mem_supported
      intro i
      exact ht _
    · exact Submodule.zero_mem _


end


section
open P202Specs.OrientedSimplicialAlgebra
/-- Affine parametrization for every tuple spanning a simplex. Repeated entries
are allowed, so collapsed simplicial images have this same geometric meaning. -/
def tupleParametrization {V : Type w} (K : AbstractSimplicialComplex V)
    (n : ℕ) (s : VertexTuple K n) : C(StandardSimplex n, K.Realization) := by
  classical
  let r : Fin (n+1) → (Finset.univ.image s.1 : Finset V) :=
    fun i => ⟨s.1 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  exact ⟨K.simplexChart ⟨_, s.2⟩ ∘ Convexity.StdSimplex.map r,
    (continuous_iSup_rng (i := (⟨_, s.2⟩ : K.Simplex)) continuous_coinduced_rng).comp
      (Convexity.StdSimplex.continuous_map ℝ r)⟩

theorem tupleParametrization_value {V : Type w} (K : AbstractSimplicialComplex V)
    (n : ℕ) (s : VertexTuple K n) (x : StandardSimplex n) :
    (tupleParametrization K n s x).1 = x.map s.1 := by
  classical
  exact Convexity.StdSimplex.map_map _ _ _

theorem tupleParametrization_face {V : Type w} (K : AbstractSimplicialComplex V)
    (n : ℕ) (i : Fin (n+2)) (s : VertexTuple K (n+1)) :
    tupleParametrization K n (tupleFace i s) =
      (tupleParametrization K (n+1) s).comp (faceInclusion i) := by
  ext t
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, tupleParametrization_value, tupleParametrization_value]
  change t.map (s.1 ∘ i.succAbove) = (t.map i.succAbove).map s.1
  exact (Convexity.StdSimplex.map_map t i.succAbove s.1).symm

def tupleSingularSimplex {V : Type w} (K : AbstractSimplicialComplex V)
    (n : ℕ) (s : VertexTuple K n) :
    P202Specs.SingularChains.Simplex (TopCat.of K.Realization) n :=
  (P202Specs.SingularChains.simplexEquiv _ n).symm (tupleParametrization K n s)

theorem tupleSingularSimplex_face {V : Type w} (K : AbstractSimplicialComplex V)
    (n : ℕ) (i : Fin (n+2)) (s : VertexTuple K (n+1)) :
    tupleSingularSimplex K n (tupleFace i s) =
      P202Specs.SingularChains.face i (tupleSingularSimplex K (n+1) s) := by
  apply (P202Specs.SingularChains.simplexEquiv _ n).injective
  rw [P202.SingularChains.simplexEquiv_face]
  simp only [tupleSingularSimplex, Equiv.apply_symm_apply]
  exact tupleParametrization_face K n i s

def validTupleBoundary {V : Type w} (K : AbstractSimplicialComplex V) (n : ℕ) :
    (VertexTuple K (n+1) →₀ A) →ₗ[R] (VertexTuple K n →₀ A) :=
  ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.lmapDomain A R (tupleFace i)

def tupleEvaluation {V : Type w} (K : AbstractSimplicialComplex V) (n : ℕ) :
    (VertexTuple K n →₀ A) →ₗ[R] Chains A (TopCat.of K.Realization) n :=
  Finsupp.lmapDomain A R (tupleSingularSimplex K n)

@[simp] theorem validTupleBoundary_single {V : Type w}
    (K : AbstractSimplicialComplex V) (n : ℕ) (s : VertexTuple K (n+1)) (a : A) :
    validTupleBoundary R A K n (Finsupp.single s a) =
      ∑ i : Fin (n+2), (-1 : ℤ)^i.val • Finsupp.single (tupleFace i s) a := by
  simp [validTupleBoundary, LinearMap.sum_apply, LinearMap.smul_apply]

@[simp] theorem tupleEvaluation_single {V : Type w}
    (K : AbstractSimplicialComplex V) (n : ℕ) (s : VertexTuple K n) (a : A) :
    tupleEvaluation R A K n (Finsupp.single s a) =
      Finsupp.single (tupleSingularSimplex K n s) a := by
  simp [tupleEvaluation]

/-- Affine tuple evaluation respects the signed face boundary even for tuples
with repeated vertices. No orientation normalization is applied in this map. -/
theorem tupleEvaluation_boundary {V : Type w} (K : AbstractSimplicialComplex V)
    (n : ℕ) :
    (P202Specs.SingularChains.boundary R A (TopCat.of K.Realization) n).comp
        (tupleEvaluation R A K (n+1)) =
      (tupleEvaluation R A K n).comp (validTupleBoundary R A K n) := by
  apply Finsupp.lhom_ext
  intro s a
  change P202Specs.SingularChains.boundary R A _ n
    (tupleEvaluation R A K (n+1) (Finsupp.single s a)) =
      tupleEvaluation R A K n (validTupleBoundary R A K n (Finsupp.single s a))
  rw [tupleEvaluation_single, P202.SingularChains.boundary_single,
    validTupleBoundary_single, map_sum]
  simp only [map_zsmul, tupleEvaluation_single, tupleSingularSimplex_face]

/-- Every simplex in a selected subcomplex evaluates wholly in its carrier. -/
theorem tupleEvaluation_preserves {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (n : ℕ) (c : VertexTuple K n →₀ A)
    (hc : c ∈ Finsupp.supported A R {s | Finset.univ.image s.1 ∈ B.complex.simplices}) :
    tupleEvaluation R A K n c ∈
      (singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module n := by
  apply map_supported R A _ _ (tupleEvaluation R A K n) ?_ c hc
  intro s hs a
  rw [tupleEvaluation_single]
  apply Finsupp.single_mem_supported
  intro t
  simp only [tupleSingularSimplex, Equiv.apply_symm_apply]
  change (tupleParametrization K n s t).val.weights.support ∈ B.complex.simplices
  rw [tupleParametrization_value]
  apply B.complex.face hs ?_ (Convexity.StdSimplex.support_weights_nonempty _)
  intro v hv
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩


/-- Before orientation normalization, every simplicial vertex map commutes with
affine tuple evaluation, including all vertex collapses. -/
theorem tupleParametrization_natural {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f : SimplicialMap (K := K) L)
    (g : TopCat.of K.Realization ⟶ TopCat.of L.Realization)
    (hg : ∀ x, (g x).val = x.val.map f.vertices)
    (n : ℕ) (s : VertexTuple K n) :
    tupleParametrization L n (f.imageTuple s) =
      g.hom.comp (tupleParametrization K n s) := by
  ext t
  apply Subtype.ext
  rw [ContinuousMap.comp_apply, hg, tupleParametrization_value, tupleParametrization_value,
    Convexity.StdSimplex.map_map]
  rfl

def validTuplePushforward {V W : Type w}
    {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}
    (f : SimplicialMap (K := K) L) (n : ℕ) :
    (VertexTuple K n →₀ A) →ₗ[R] (VertexTuple L n →₀ A) :=
  Finsupp.lmapDomain A R f.imageTuple

theorem tupleEvaluation_natural {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f : SimplicialMap (K := K) L)
    (g : TopCat.of K.Realization ⟶ TopCat.of L.Realization)
    (hg : ∀ x, (g x).val = x.val.map f.vertices) (n : ℕ) :
    (tupleEvaluation R A L n).comp (validTuplePushforward R A f n) =
      (((chainMap R A g).f n).hom).comp (tupleEvaluation R A K n) := by
  apply Finsupp.lhom_ext
  intro s a
  change tupleEvaluation R A L n
      (validTuplePushforward R A f n (Finsupp.single s a)) =
    ((chainMap R A g).f n).hom (tupleEvaluation R A K n (Finsupp.single s a))
  simp only [validTuplePushforward, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    tupleEvaluation_single]
  erw [P202.SingularChains.chainMap_single]
  congr 1
  apply (P202Specs.SingularChains.simplexEquiv _ n).injective
  rw [P202.SingularChains.simplexEquiv_postcomp]
  simp only [tupleSingularSimplex, Equiv.apply_symm_apply]
  exact tupleParametrization_natural K L f g hg n s

/-- Forgetting that a tuple is increasing, then evaluating, recovers exactly the
original canonical comparison map. -/
theorem tupleEvaluation_increasing {V : Type w} (K : AbstractSimplicialComplex V)
    (n : ℕ) :
    (tupleEvaluation R A K n).comp
        (Finsupp.lmapDomain A R (fun s : P202Specs.OrientedSimplicialAlgebra.Simplex K n =>
          (⟨s.1, s.2⟩ : VertexTuple K n))) =
      Simplicial.affineLinear K R A n := by
  apply Finsupp.lhom_ext
  intro s a
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    tupleEvaluation_single]
  erw [P202.SimplicialChains.Simplicial.affineLinear_single]
  rfl


end


section
open P202Specs.OrientedSimplicialAlgebra
/-- Total linear evaluation sends invalid vertex tuples to zero. On tuples
supported in any simplex it is the actual affine evaluation and respects d. -/
def totalTupleEvaluation {V : Type w} (K : AbstractSimplicialComplex V) (n : ℕ) :
    TupleChains A V (n+1) →ₗ[R] P202Specs.SingularChains.Chains A (TopCat.of K.Realization) n := by
  classical
  exact Finsupp.lsum R fun t => if ht : Finset.univ.image t ∈ K.simplices then
    Finsupp.lsingle (tupleSingularSimplex K n ⟨t, ht⟩) else 0

@[simp] theorem totalTupleEvaluation_single_valid {V : Type w}
    (K : AbstractSimplicialComplex V) (n : ℕ) (t : Fin (n+1) → V)
    (ht : Finset.univ.image t ∈ K.simplices) (a : A) :
    totalTupleEvaluation R A K n (Finsupp.single t a) =
      Finsupp.single (tupleSingularSimplex K n ⟨t, ht⟩) a := by
  classical
  simp [totalTupleEvaluation, Finsupp.lsum_single, ht]

theorem totalTupleEvaluation_increasing {V : Type w} (K : AbstractSimplicialComplex V)
    (n : ℕ) :
    (totalTupleEvaluation R A K n).comp
        (Finsupp.lmapDomain A R (fun s : P202Specs.OrientedSimplicialAlgebra.Simplex K n =>
          (s.1 : Fin (n+1) → V))) =
      Simplicial.affineLinear K R A n := by
  apply Finsupp.lhom_ext
  intro s a
  simp only [LinearMap.comp_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rw [totalTupleEvaluation_single_valid R A K n _ s.2]
  erw [P202.SimplicialChains.Simplicial.affineLinear_single]
  rfl

/-- Boundary compatibility is asserted precisely on valid tuples, and therefore
on every formal tuple chain contained in an actual simplex carrier. -/
theorem totalTupleEvaluation_boundary {V : Type w}
    (K : AbstractSimplicialComplex V) (n : ℕ) (c : TupleChains A V (n+2))
    (hc : c ∈ Finsupp.supported A R {t | Finset.univ.image t ∈ K.simplices}) :
    P202Specs.SingularChains.boundary R A (TopCat.of K.Realization) n
        (totalTupleEvaluation R A K (n+1) c) =
      totalTupleEvaluation R A K n (tupleBoundary R A V (n+1) c) := by
  let d : P202Specs.SingularChains.Chains A (TopCat.of K.Realization) (n+1) →ₗ[R]
      P202Specs.SingularChains.Chains A (TopCat.of K.Realization) n :=
    P202Specs.SingularChains.boundary R A (TopCat.of K.Realization) n
  let D := d.comp (totalTupleEvaluation R A K (n+1)) -
    (totalTupleEvaluation R A K n).comp (tupleBoundary R A V (n+1))
  have hz : D c ∈ (⊥ : Submodule R _) := by
    apply map_supported R A _ _ D ?_ c hc
    intro t ht a
    change _ ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot]
    change d (totalTupleEvaluation R A K (n+1) (Finsupp.single t a)) -
        totalTupleEvaluation R A K n (tupleBoundary R A V (n+1) (Finsupp.single t a)) = 0
    rw [sub_eq_zero]
    change P202Specs.SingularChains.boundary R A _ n
      (totalTupleEvaluation R A K (n+1) (Finsupp.single t a)) =
        totalTupleEvaluation R A K n (tupleBoundary R A V (n+1) (Finsupp.single t a))
    rw [totalTupleEvaluation_single_valid R A K (n+1) t ht,
      P202.SingularChains.boundary_single, tupleBoundary_single, map_sum]
    simp only [map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    have hface : Finset.univ.image (t ∘ i.succAbove) ∈ K.simplices :=
      (tupleFace i (⟨t, ht⟩ : VertexTuple K (n+1))).2
    rw [totalTupleEvaluation_single_valid R A K n _ hface]
    rw [← tupleSingularSimplex_face]
    rfl
  exact sub_eq_zero.mp ((Submodule.mem_bot R).mp hz)

/-- Evaluation takes every tuple chain whose vertices lie in a selected simplex
into the actual singular chain submodule of its subcomplex carrier. -/
theorem totalTupleEvaluation_preserves {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K)
    (n : ℕ) (c : TupleChains A V (n+1))
    (hc : c ∈ Finsupp.supported A R {t | Finset.univ.image t ∈ B.complex.simplices}) :
    totalTupleEvaluation R A K n c ∈
      (singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module n := by
  apply map_supported R A _ _ (totalTupleEvaluation R A K n) ?_ c hc
  intro t ht a
  rw [totalTupleEvaluation_single_valid R A K n t (B.subset ht)]
  apply Finsupp.single_mem_supported
  intro x
  simp only [tupleSingularSimplex, Equiv.apply_symm_apply]
  change (tupleParametrization K n ⟨t, B.subset ht⟩ x).val.weights.support ∈ B.complex.simplices
  rw [tupleParametrization_value]
  apply B.complex.face ht ?_ (Convexity.StdSimplex.support_weights_nonempty _)
  intro v hv
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hv)
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩


end


section

def deltaSkeletalChart (D : DeltaComplex.{w}) (n : ℕ) (s : D.Simplex n) :
    C(StandardSimplex n, (deltaSkeletonLT D (n+1)).asComplex.Realization) :=
  deltaParametrization _ n ⟨s, Nat.lt_succ_self n⟩

theorem deltaSkeletalChart_boundary (D : DeltaComplex.{w}) (n : ℕ) (s : D.Simplex n)
    (t : StandardSimplex n) (ht : ∃ i, t.weights i = 0) :
    deltaSkeletalChart D n s t ∈
      (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n).carrier := by
  have hnot : t ∉ standardSimplexInterior n := by
    obtain ⟨i,hi⟩ := ht
    intro h
    exact (h i).ne' hi
  obtain ⟨m,hm,a,z,hz,hzt⟩ := P202.Topology.exists_proper_interior_face t hnot
  refine ⟨m, ((deltaSkeletonLT D (n+1)).asComplex).face a ⟨s, Nat.lt_succ_self n⟩,
    hm, z, ?_⟩
  exact (P202.Topology.deltaFaceCompatibility _ a _ z).trans
    (congrArg ((deltaSkeletonLT D (n+1)).asComplex.simplexChart n _) hzt)

/-- The characteristic simplex of each n-cell is a map of pairs to the actual
consecutive skeletal pair, including the point/empty pair when n=0. -/
def deltaSkeletalPair (D : DeltaComplex.{w}) (n : ℕ) : P202Specs.RelativeSingularChains.Pair.{w} :=
  ⟨TopCat.of (deltaSkeletonLT D (n+1)).asComplex.Realization,
    (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n).carrier⟩

-- Test same-universe morphism from geometric simplex pair:
-- def deltaSkeletalPairMap (D : DeltaComplex.{w}) (n : ℕ) (s : D.Simplex n) :
--     P202Specs.SpheresDisks.simplexPair n ⟶ deltaSkeletalPair D n :=
--   ⟨deltaSkeletalChart D n s, fun t ht => deltaSkeletalChart_boundary D n s t ht⟩


variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- Singular pushforward as a linear map permits source and target spaces in
different universes. It uses the same continuous simplex equivalences as the
canonical singular functor, without choosing any new chain model. -/
def singularContinuousMapLinear {X : TopCat.{w}} {Y : TopCat.{t}}
    (f : C(X,Y)) (q : ℕ) : Chains A X q →ₗ[R] Chains A Y q :=
  Finsupp.lmapDomain A R fun z => (simplexEquiv Y q).symm (f.comp (simplexEquiv X q z))

@[simp] theorem singularContinuousMapLinear_single {X : TopCat.{w}} {Y : TopCat.{t}}
    (f : C(X,Y)) (q : ℕ) (z : Simplex X q) (a : A) :
    singularContinuousMapLinear R A f q (Finsupp.single z a) =
      Finsupp.single ((simplexEquiv Y q).symm (f.comp (simplexEquiv X q z))) a := by
  exact Finsupp.mapDomain_single

/-- Face compatibility for the same pushforward, with arbitrary geometric universes. -/
theorem singularContinuousMapLinear_face {X : TopCat.{w}} {Y : TopCat.{t}}
    (f : C(X,Y)) (q : ℕ) (i : Fin (q+2)) (z : Simplex X (q+1)) :
    (simplexEquiv Y q).symm (f.comp (simplexEquiv X q (face i z))) =
      face i ((simplexEquiv Y (q+1)).symm (f.comp (simplexEquiv X (q+1) z))) := by
  apply (simplexEquiv Y q).injective
  simp only [Equiv.apply_symm_apply, P202.SingularChains.simplexEquiv_face]
  ext t
  rfl

/-- Boundary naturality holds before any categorical universe lifting. -/
theorem singularContinuousMapLinear_boundary {X : TopCat.{w}} {Y : TopCat.{t}}
    (f : C(X,Y)) (q : ℕ) :
    (singularContinuousMapLinear R A f q).comp (boundary R A X q) =
      (boundary R A Y q).comp (singularContinuousMapLinear R A f (q+1)) := by
  apply Finsupp.lhom_ext
  intro z a
  change singularContinuousMapLinear R A f q (boundary R A X q (Finsupp.single z a)) =
    boundary R A Y q (singularContinuousMapLinear R A f (q+1) (Finsupp.single z a))
  erw [P202.SingularChains.boundary_single]
  rw [singularContinuousMapLinear_single]
  erw [P202.SingularChains.boundary_single]
  simp only [map_sum, map_zsmul, singularContinuousMapLinear_single,
    singularContinuousMapLinear_face]

/-- Subspace support is preserved for arbitrary maps of actual pairs. -/
theorem singularContinuousMapLinear_preserves {X : TopCat.{w}} {Y : TopCat.{t}}
    (B : Set X) (E : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f B E) (q : ℕ)
    (c : Chains A X q) (hc : c ∈ (singularSelection R A X B).module q) :
    singularContinuousMapLinear R A f q c ∈ (singularSelection R A Y E).module q := by
  apply map_supported R A _ _ (singularContinuousMapLinear R A f q) ?_ c hc
  intro z hz a
  rw [singularContinuousMapLinear_single]
  apply Finsupp.single_mem_supported
  intro t
  simp only [Equiv.apply_symm_apply, ContinuousMap.comp_apply]
  exact hf (hz t)

/-- The induced map on the original supported relative chain quotients; no
common universe of the geometric spaces is needed for this linear operation. -/
def singularContinuousMapRelativeLinear {X : TopCat.{w}} {Y : TopCat.{t}}
    (B : Set X) (E : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f B E) (q : ℕ) :
    (singularRelativeComplex R A X B).X q →ₗ[R]
      (singularRelativeComplex R A Y E).X q :=
  ((singularSelection R A X B).module q).mapQ
    ((singularSelection R A Y E).module q) (singularContinuousMapLinear R A f q)
      (singularContinuousMapLinear_preserves R A B E f hf q)


@[simp] theorem singularContinuousMapRelativeLinear_mk {X : TopCat.{w}} {Y : TopCat.{t}}
    (B : Set X) (E : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f B E) (q : ℕ)
    (c : Chains A X q) :
    singularContinuousMapRelativeLinear R A B E f hf q
      (((singularSelection R A X B).module q).mkQ c) =
    ((singularSelection R A Y E).module q).mkQ (singularContinuousMapLinear R A f q c) := rfl

/-- These relative quotient maps commute with the actual differentials. -/
theorem singularContinuousMapRelativeLinear_boundary {X : TopCat.{w}} {Y : TopCat.{t}}
    (B : Set X) (E : Set Y) (f : C(X,Y)) (hf : Set.MapsTo f B E) (q : ℕ) :
    (singularContinuousMapRelativeLinear R A B E f hf q).comp
        ((singularRelativeComplex R A X B).d (q+1) q).hom =
      (((singularRelativeComplex R A Y E).d (q+1) q).hom).comp
        (singularContinuousMapRelativeLinear R A B E f hf (q+1)) := by
  apply LinearMap.ext
  intro x
  obtain ⟨c,rfl⟩ := ((singularSelection R A X B).module (q+1)).mkQ_surjective x
  simp only [singularRelativeComplex, ChainSelection.quotient, ChainComplex.of_d,
    ModuleCat.hom_ofHom, LinearMap.comp_apply]
  change ((singularSelection R A Y E).module q).mkQ
      (singularContinuousMapLinear R A f q (boundary R A X q c)) =
    ((singularSelection R A Y E).module q).mkQ
      (boundary R A Y q (singularContinuousMapLinear R A f (q+1) c))
  exact congrArg ((singularSelection R A Y E).module q).mkQ
    (LinearMap.congr_fun (singularContinuousMapLinear_boundary R A f q) c)

/-- Relative characteristic-simplex chain map, stated linearly so the geometric
standard simplex and the cell labels may occupy different universes. -/
def deltaSkeletalChartRelativeLinear (D : DeltaComplex.{w}) (n : ℕ) (s : D.Simplex n)
    (q : ℕ) :
    (singularRelativeComplex R A (P202Specs.SpheresDisks.simplex n)
      (P202Specs.SpheresDisks.simplexPair n).subspace).X q →ₗ[R]
    (singularRelativeComplex R A (deltaSkeletalPair D n).space
      (deltaSkeletalPair D n).subspace).X q :=
  singularContinuousMapRelativeLinear R A _ _ (deltaSkeletalChart D n s)
    (fun t ht => deltaSkeletalChart_boundary D n s t ht) q

/-- The map sends the oriented relative simplex to exactly the canonical affine
relative n-cell generator, with its original coefficient and sign. -/
@[simp] theorem deltaSkeletalChartRelativeLinear_generator (D : DeltaComplex.{w})
    (n : ℕ) (s : D.Simplex n) (a : A) :
    deltaSkeletalChartRelativeLinear R A D n s n
      (((singularSelection R A (P202Specs.SpheresDisks.simplex n)
        (P202Specs.SpheresDisks.simplexPair n).subspace).module n).mkQ
          (P202Specs.SpheresDisks.affineChain A n a)) =
      ((singularSelection R A (deltaSkeletalPair D n).space
        (deltaSkeletalPair D n).subspace).module n).mkQ
          (deltaParametrizationLinear R A (deltaSkeletonLT D (n+1)).asComplex n
            (Finsupp.single ⟨s,Nat.lt_succ_self n⟩ a)) := by
  change ((singularSelection R A (deltaSkeletalPair D n).space
    (deltaSkeletalPair D n).subspace).module n).mkQ
      (singularContinuousMapLinear R A (deltaSkeletalChart D n s) n
        (Finsupp.single (P202Specs.SpheresDisks.affineSimplex n) a)) = _
  rw [singularContinuousMapLinear_single]
  congr 1
  simp only [P202Specs.SpheresDisks.affineSimplex, Equiv.apply_symm_apply,
    ContinuousMap.comp_id]
  simp only [deltaParametrizationLinear, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  rfl


end


section
variable {R : Type u} [CommRing R]
def moduleCycleClass (S : ShortComplex (ModuleCat.{v} R)) (x : S.X₂)
    (hx : S.g x = 0) : S.homology :=
  S.moduleCatHomologyIso.inv
    (S.moduleCatToCycles.range.mkQ ⟨x,hx⟩)

theorem moduleCycleClass_eq_pi (S : ShortComplex (ModuleCat.{v} R))
    (x : S.X₂) (hx : S.g x = 0) :
    moduleCycleClass S x hx = S.homologyπ (S.moduleCatCyclesIso.inv ⟨x,hx⟩) := by
  exact (congrArg (fun f => f ⟨x,hx⟩) S.moduleCatCyclesIso_inv_π).symm

theorem moduleCycleClass_surjective (S : ShortComplex (ModuleCat.{v} R)) (z : S.homology) :
    ∃ (x : S.X₂) (hx : S.g x = 0), moduleCycleClass S x hx = z := by
  obtain ⟨x,hx⟩ := S.moduleCatToCycles.range.mkQ_surjective (S.moduleCatHomologyIso.hom z)
  exact ⟨x.1, x.2, by simp [moduleCycleClass, hx]⟩

@[simp] theorem moduleCycleClass_eq_zero_iff (S : ShortComplex (ModuleCat.{v} R))
    (x : S.X₂) (hx : S.g x = 0) :
    moduleCycleClass S x hx = 0 ↔ ∃ y : S.X₁, S.f y = x := by
  change S.moduleCatHomologyIso.inv.hom (S.moduleCatToCycles.range.mkQ ⟨x,hx⟩) = 0 ↔ _
  rw [← map_zero S.moduleCatHomologyIso.inv.hom]
  rw [(ModuleCat.mono_iff_injective S.moduleCatHomologyIso.inv).mp inferInstance |>.eq_iff]
  erw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨y,hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y,hy⟩
    exact ⟨y, Subtype.ext hy⟩

theorem moduleCycleClass_natural {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)
    (x : S.X₂) (hx : S.g x = 0) :
    ShortComplex.homologyMap f (moduleCycleClass S x hx) =
      moduleCycleClass T (f.τ₂ x) (by
        have h := congrArg (fun g => g x) f.comm₂₃
        simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h) := by
  rw [moduleCycleClass_eq_pi, moduleCycleClass_eq_pi]
  have hn := congrArg (fun g => g (S.moduleCatCyclesIso.inv ⟨x,hx⟩))
    (ShortComplex.homologyπ_naturality f)
  simp only [ConcreteCategory.comp_apply] at hn
  rw [hn]
  congr 1
  apply (ModuleCat.mono_iff_injective T.iCycles).mp inferInstance
  have hcy := congrArg (fun g => g (S.moduleCatCyclesIso.inv ⟨x,hx⟩))
    (ShortComplex.cyclesMap_i f)
  simp only [ConcreteCategory.comp_apply] at hcy
  rw [hcy]
  simp only [← ConcreteCategory.comp_apply, ShortComplex.moduleCatCyclesIso_inv_iCycles]
  rfl


/-- Equality of the actual categorical homology classes is precisely the
existence of a bounding chain for their difference. -/
theorem moduleCycleClass_eq_iff (S : ShortComplex (ModuleCat.{v} R))
    (x y : S.X₂) (hx : S.g x = 0) (hy : S.g y = 0) :
    moduleCycleClass S x hx = moduleCycleClass S y hy ↔
      ∃ z : S.X₁, S.f z = x-y := by
  have hsub : moduleCycleClass S x hx - moduleCycleClass S y hy =
      moduleCycleClass S (x-y) (by simp [map_sub, hx, hy]) := by
    unfold moduleCycleClass
    rw [← map_sub]
    congr 1
  rw [← sub_eq_zero, hsub, moduleCycleClass_eq_zero_iff]

/-- A concrete isomorphism criterion for a map of module short complexes.
The two hypotheses are the cycle-lifting and bounding-chain reflection
conditions used to pass finite-subcomplex comparisons to an infinite complex. -/
theorem homologyMap_isIso_of_cycle_conditions
    {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)
    (hsurj : ∀ y : T.X₂, T.g y = 0 →
      ∃ (x : S.X₂) (_ : S.g x = 0) (z : T.X₁), T.f z = f.τ₂ x-y)
    (hinj : ∀ x : S.X₂, S.g x = 0 →
      (∃ z : T.X₁, T.f z = f.τ₂ x) → ∃ z : S.X₁, S.f z = x) :
    IsIso (ShortComplex.homologyMap f) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · apply (injective_iff_map_eq_zero (ShortComplex.homologyMap f).hom).mpr
    intro z hz
    obtain ⟨x,hx,rfl⟩ := moduleCycleClass_surjective S z
    rw [moduleCycleClass_natural] at hz
    apply (moduleCycleClass_eq_zero_iff S x hx).mpr
    apply hinj x hx
    exact (moduleCycleClass_eq_zero_iff T _ _).mp hz
  · intro z
    obtain ⟨y,hy,rfl⟩ := moduleCycleClass_surjective T z
    obtain ⟨x,hx,w,hw⟩ := hsurj y hy
    refine ⟨moduleCycleClass S x hx, ?_⟩
    rw [moduleCycleClass_natural]
    exact (moduleCycleClass_eq_iff T _ _ _ _).mpr ⟨w,hw⟩


end


section

def singularRelativeCyclesIso (X : TopCat.{w}) (Y : Set X) (n : ℕ) :
    (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).cycles (n : ℤ) ≅
      (singularRelativeComplex R A X Y).cycles n :=
  asIso (cyclesMap (ordinaryRelativeExtensionIso R A X Y).hom (n : ℤ)) ≪≫
    (P202Specs.RelativeSingularChains.nonnegative R A ⟨X,Y⟩).extendCyclesIso
      (degreeEmbedding 0) (by change (0 : ℤ) + n = n; omega) ≪≫
    asIso (cyclesMap (singularRelativeIso R A X Y).hom n)

@[reassoc] theorem singularRelativeHomologyIso_homologyπ (X : TopCat.{w}) (Y : Set X) (n : ℕ) :
    (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).homologyπ (n : ℤ) ≫
      (singularRelativeHomologyIso R A X Y n).hom =
    (singularRelativeCyclesIso R A X Y n).hom ≫
      (singularRelativeComplex R A X Y).homologyπ n := by
  simp only [singularRelativeHomologyIso, singularRelativeCyclesIso, Iso.trans_hom,
    homologyMapIso_hom, asIso_hom, Category.assoc, homologyπ_naturality_assoc,
    homologyπ_extendHomologyIso_hom_assoc, homologyπ_naturality]

@[reassoc] theorem singularRelativeCyclesIso_iCycles (X : TopCat.{w}) (Y : Set X) (n : ℕ) :
    (singularRelativeCyclesIso R A X Y n).hom ≫ (singularRelativeComplex R A X Y).iCycles n =
    (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).iCycles (n : ℤ) ≫
      (P202Specs.RelativeSingularChains.ordinaryDegreeIso R A ⟨X,Y⟩ n).hom ≫
      (singularRelativeDegreeEquiv R A X Y n).toModuleIso.hom := by
  simp only [singularRelativeCyclesIso, Iso.trans_hom, asIso_hom,
    Category.assoc, cyclesMap_i, extendCyclesIso_hom_iCycles_assoc]
  rw [← Category.assoc, cyclesMap_i]
  simp only [ordinaryRelativeExtensionIso, P202.GoodPairQuotient.nonnegativeExtensionIso_hom_f,
    Category.assoc, Iso.inv_hom_id_assoc]
  rfl


/-- Under the canonical bridge, the homology class has exactly the expected
quotient-chain representative; this statement also covers degree zero. -/
theorem singularRelativeHomologyIso_cycle (X : TopCat.{w}) (Y : Set X) (n : ℕ)
    (z : (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).X (n : ℤ))
    (hz : (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).d (n : ℤ) ((n : ℤ)-1) z = 0)
    (c : (singularRelativeComplex R A X Y).X n)
    (hc : (singularRelativeComplex R A X Y).d n ((ComplexShape.down ℕ).next n) c = 0)
    (he : singularRelativeDegreeEquiv R A X Y n
      ((P202Specs.RelativeSingularChains.ordinaryDegreeIso R A ⟨X,Y⟩ n).hom z) = c) :
    (singularRelativeHomologyIso R A X Y n).hom
      (P202Specs.SpheresDisks.classOf R _ (n : ℤ) z hz) =
    (singularRelativeComplex R A X Y).homologyπ n
      ((singularRelativeComplex R A X Y).cyclesMk c ((ComplexShape.down ℕ).next n) rfl hc) := by
  let zcy := (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).cyclesMk z
    ((n : ℤ)-1) (by simp) hz
  have hcy : (singularRelativeCyclesIso R A X Y n).hom zcy =
      (singularRelativeComplex R A X Y).cyclesMk c ((ComplexShape.down ℕ).next n) rfl hc := by
    apply ((ModuleCat.mono_iff_injective ((singularRelativeComplex R A X Y).iCycles n)).mp
      inferInstance)
    have h := congrArg (fun f => f zcy) (singularRelativeCyclesIso_iCycles R A X Y n)
    change (singularRelativeComplex R A X Y).iCycles n
      ((singularRelativeCyclesIso R A X Y n).hom zcy) =
      singularRelativeDegreeEquiv R A X Y n
        ((P202Specs.RelativeSingularChains.ordinaryDegreeIso R A ⟨X,Y⟩ n).hom
          ((P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).iCycles (n : ℤ) zcy)) at h
    erw [h]
    change singularRelativeDegreeEquiv R A X Y n
      ((P202Specs.RelativeSingularChains.ordinaryDegreeIso R A ⟨X,Y⟩ n).hom
        ((P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).iCycles (n : ℤ) zcy)) = _
    have hzcy : (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).iCycles (n : ℤ) zcy = z :=
      HomologicalComplex.i_cyclesMk (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩)
        z ((n : ℤ)-1) (by simp) hz
    rw [hzcy, he]
    exact (HomologicalComplex.i_cyclesMk (singularRelativeComplex R A X Y)
      c ((ComplexShape.down ℕ).next n) rfl hc).symm
  have h := congrArg (fun f => f zcy) (singularRelativeHomologyIso_homologyπ R A X Y n)
  change (singularRelativeHomologyIso R A X Y n).hom
      ((P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).homologyπ (n : ℤ) zcy) =
    (singularRelativeComplex R A X Y).homologyπ n
      ((singularRelativeCyclesIso R A X Y n).hom zcy) at h
  erw [hcy] at h
  exact h

end



section
open P202Specs.OrientedSimplicialAlgebra
/-- A chain supported on tuples whose vertices lie in one simplex is valid. -/
theorem tupleSupported_le_valid {V : Type w} (K : AbstractSimplicialComplex V)
    {k : ℕ} (t : Fin (k+1) → V) (ht : Finset.univ.image t ∈ K.simplices) (n : ℕ) :
    tupleSupported R A V (Set.range t) (n+1) ≤
      Finsupp.supported A R {s | Finset.univ.image s ∈ K.simplices} := by
  apply Finsupp.supported_mono
  intro s hs
  apply K.face ht ?_ (Finset.image_nonempty.mpr Finset.univ_nonempty)
  intro v hv
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨j, hj⟩ := hs i
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩

/-- Preservation of every vertex carrier makes the tuple homotopy evaluable in
the original complex, without extending invalid tuples to geometric maps. -/
theorem tupleHomotopy_valid {V : Type w} (K : AbstractSimplicialComplex V)
    (N : ∀ n, TupleChains A V n →ₗ[R] TupleChains A V n)
    (hN : ∀ (S : Set V) n c, c ∈ tupleSupported R A V S n →
      N n c ∈ tupleSupported R A V S n)
    (n : ℕ) (c : TupleChains A V (n+1))
    (hc : c ∈ Finsupp.supported A R {t | Finset.univ.image t ∈ K.simplices}) :
    tupleHomotopy R A N (n+1) c ∈
      Finsupp.supported A R {t | Finset.univ.image t ∈ K.simplices} := by
  apply map_supported R A _ _ (tupleHomotopy R A N (n+1)) ?_ c hc
  intro t ht a
  apply tupleSupported_le_valid R A K t ht (n+1)
  apply tupleHomotopy_preserves R A N (Set.range t) (hN (Set.range t))
  exact Finsupp.single_mem_supported R a (fun i => Set.mem_range_self i)

/-- Singular boundary with its finite-support source and target made explicit. -/
def singularTupleBoundary {V : Type w} (K : AbstractSimplicialComplex V) (n : ℕ) :
    P202Specs.SingularChains.Chains A (TopCat.of K.Realization) (n+1) →ₗ[R]
      P202Specs.SingularChains.Chains A (TopCat.of K.Realization) n :=
  P202Specs.SingularChains.boundary R A (TopCat.of K.Realization) n

/-- The formal cone homotopy evaluates to a genuine singular boundary equation
on all valid tuples. This is the carrier step needed for both naturality and
change of vertex order. -/
theorem totalTupleEvaluation_homotopy_identity {V : Type w}
    (K : AbstractSimplicialComplex V)
    (N : ∀ n, TupleChains A V n →ₗ[R] TupleChains A V n)
    (hzero : N 0 = LinearMap.id)
    (hchain : ∀ n c, tupleBoundary R A V n (N (n+1) c) =
      N n (tupleBoundary R A V n c))
    (hcarrier : ∀ (S : Set V) n c, c ∈ tupleSupported R A V S n →
      N n c ∈ tupleSupported R A V S n)
    (n : ℕ) (c : TupleChains A V (n+1))
    (hc : c ∈ Finsupp.supported A R {t | Finset.univ.image t ∈ K.simplices}) :
    singularTupleBoundary R A K n
        (totalTupleEvaluation R A K (n+1) (tupleHomotopy R A N (n+1) c)) +
      totalTupleEvaluation R A K n
        (tupleHomotopy R A N n (tupleBoundary R A V n c)) =
      totalTupleEvaluation R A K n (N (n+1) c) - totalTupleEvaluation R A K n c := by
  unfold singularTupleBoundary
  erw [totalTupleEvaluation_boundary R A K n _ (tupleHomotopy_valid R A K N hcarrier n c hc)]
  rw [← map_add, tupleHomotopy_identity R A N hzero hchain, map_sub]

/-- For an ordinary cycle, the carrier equation supplies an actual singular
bounding chain for normalized evaluation minus the original evaluation. -/
theorem totalTupleEvaluation_cycle_difference {V : Type w}
    (K : AbstractSimplicialComplex V)
    (N : ∀ n, TupleChains A V n →ₗ[R] TupleChains A V n)
    (hzero : N 0 = LinearMap.id)
    (hchain : ∀ n c, tupleBoundary R A V n (N (n+1) c) =
      N n (tupleBoundary R A V n c))
    (hcarrier : ∀ (S : Set V) n c, c ∈ tupleSupported R A V S n →
      N n c ∈ tupleSupported R A V S n)
    (n : ℕ) (c : TupleChains A V (n+1))
    (hc : c ∈ Finsupp.supported A R {t | Finset.univ.image t ∈ K.simplices})
    (hcycle : n = 0 ∨ tupleBoundary R A V n c = 0) :
    singularTupleBoundary R A K n
        (totalTupleEvaluation R A K (n+1) (tupleHomotopy R A N (n+1) c)) =
      totalTupleEvaluation R A K n (N (n+1) c) - totalTupleEvaluation R A K n c := by
  have h := totalTupleEvaluation_homotopy_identity R A K N hzero hchain hcarrier n c hc
  have hz : tupleHomotopy R A N n (tupleBoundary R A V n c) = 0 := by
    rcases hcycle with rfl | hcycle
    · rfl
    · rw [hcycle, map_zero]
  rwa [hz, map_zero, add_zero] at h


end


section
open P202Specs.OrientedSimplicialAlgebra
def tupleOrderedIncreasingLinear (V : Type w) (o : LinearOrder V) (n : ℕ) :
    P202Specs.RelativeParametrizations.DeltaChains A (orderedDelta (tupleFullComplex V) o) n →ₗ[R]
      TupleChains A V (n+1) :=
  Finsupp.lmapDomain A R (fun s => (s.1 : Fin (n+1) → V))

@[simp] theorem tupleOrderedIncreasingLinear_single (V : Type w) (o : LinearOrder V) (n : ℕ)
    (s : (orderedDelta (tupleFullComplex V) o).Simplex n) (a : A) :
    tupleOrderedIncreasingLinear R A V o n (Finsupp.single s a) =
      Finsupp.single (s.1 : Fin (n+1) → V) a := by
  simp [tupleOrderedIncreasingLinear]

def tupleNormalizeOrdered (V : Type w) (o : LinearOrder V) :
    ∀ n, TupleChains A V n →ₗ[R] TupleChains A V n :=
  fun n => Nat.casesOn (motive := fun n => TupleChains A V n →ₗ[R] TupleChains A V n) n
    LinearMap.id (fun n => (tupleOrderedIncreasingLinear R A V o n).comp
      ((orderTransitionLinear R A (tupleFullComplex V) o n).comp (tupleOrientedLinear R A V n)))

@[simp] theorem tupleNormalizeOrdered_zero (V : Type w) (o : LinearOrder V) :
    tupleNormalizeOrdered R A V o 0 = LinearMap.id := rfl

theorem tupleNormalizeOrdered_single (V : Type w) (o : LinearOrder V) (n : ℕ)
    (t : Fin (n+1) → V) (a : A) :
    tupleNormalizeOrdered R A V o (n+1) (Finsupp.single t a) =
      if ht : Function.Injective t then
        (Equiv.Perm.sign (@Tuple.sort (n+1) V (vertexOrder V) t) : ℤ) •
          (Equiv.Perm.sign (sortingPermutation o (sorted (fullVertexTuple t) ht).1) : ℤ) •
            Finsupp.single ((reorderedSimplex o (sorted (fullVertexTuple t) ht)).1 : Fin (n+1) → V) a
      else 0 := by
  classical
  simp only [tupleNormalizeOrdered, LinearMap.comp_apply, tupleOrientedLinear_single, oriented]
  dsimp only [fullVertexTuple]
  split <;> simp only [map_zsmul, orderTransitionLinear_single,
    tupleOrderedIncreasingLinear_single, map_zero]

@[simp] theorem tupleNormalizeOrdered_one (V : Type w) (o : LinearOrder V) :
    tupleNormalizeOrdered R A V o 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro t a
  have ht : Function.Injective t := by intro i j _; exact Subsingleton.elim i j
  have hs : @Tuple.sort 1 V (vertexOrder V) t = Equiv.refl _ := Subsingleton.elim _ _
  have ho : sortingPermutation o (sorted (fullVertexTuple t) ht).1 = Equiv.refl _ := by
    apply Equiv.ext
    intro i
    apply Fin.ext
    omega
  rw [tupleNormalizeOrdered_single, dite_eq_left ht, hs, ho]
  simp only [Equiv.Perm.sign_refl, Units.val_one, one_smul, LinearMap.id_apply]
  congr 1
  funext i
  change t ((@Tuple.sort 1 V (vertexOrder V) t)
    ((sortingPermutation o (sorted (fullVertexTuple t) ht).1) i)) = t i
  rw [hs, ho]
  rfl

theorem tupleOrderedIncreasing_boundary (V : Type w) (o : LinearOrder V) (n : ℕ) :
    (tupleBoundary R A V (n+1)).comp (tupleOrderedIncreasingLinear R A V o (n+1)) =
      (tupleOrderedIncreasingLinear R A V o n).comp
        (P202Specs.RelativeParametrizations.deltaBoundary R A (orderedDelta (tupleFullComplex V) o) n) := by
  classical
  apply Finsupp.lhom_ext
  intro t a
  simp only [LinearMap.comp_apply, tupleOrderedIncreasingLinear_single]
  rw [P202.RelativeParametrizations.deltaBoundary_single, tupleBoundary_single]
  simp only [map_sum, map_zsmul, tupleOrderedIncreasingLinear_single]
  rfl

theorem tupleNormalizeOrdered_boundary (V : Type w) (o : LinearOrder V) (n : ℕ)
    (c : TupleChains A V (n+1)) :
    tupleBoundary R A V n (tupleNormalizeOrdered R A V o (n+1) c) =
      tupleNormalizeOrdered R A V o n (tupleBoundary R A V n c) := by
  cases n with
  | zero => rw [tupleNormalizeOrdered_one, tupleNormalizeOrdered_zero]; rfl
  | succ n =>
    have hi := LinearMap.congr_fun (tupleOrderedIncreasing_boundary R A V o n)
      (orderTransitionLinear R A (tupleFullComplex V) o (n+1) (tupleOrientedLinear R A V (n+1) c))
    have ho := LinearMap.congr_fun (tupleOriented_boundary R A V n) c
    have hT := LinearMap.congr_fun (orderTransition_boundary R A (tupleFullComplex V) o n)
      (tupleOrientedLinear R A V (n+1) c)
    simp only [LinearMap.comp_apply] at hi ho hT
    change tupleBoundary R A V (n+1)
      (tupleOrderedIncreasingLinear R A V o (n+1)
        (orderTransitionLinear R A (tupleFullComplex V) o (n+1) (tupleOrientedLinear R A V (n+1) c))) =
      tupleOrderedIncreasingLinear R A V o n
        (orderTransitionLinear R A (tupleFullComplex V) o n
          (tupleOrientedLinear R A V n (tupleBoundary R A V (n+1) c)))
    rw [hi, hT, ho]

theorem tupleNormalizeOrdered_preserves (V : Type w) (o : LinearOrder V) (S : Set V) (n : ℕ)
    (c : TupleChains A V n) (hc : c ∈ tupleSupported R A V S n) :
    tupleNormalizeOrdered R A V o n c ∈ tupleSupported R A V S n := by
  cases n with
  | zero => exact hc
  | succ n =>
    apply P202Specs.RelativeParametrizations.map_supported R A _ _
      (tupleNormalizeOrdered R A V o (n+1)) ?_ c hc
    intro t ht a
    rw [tupleNormalizeOrdered_single]
    split
    · apply zsmul_mem
      apply zsmul_mem
      apply Finsupp.single_mem_supported
      intro i
      exact ht _
    · exact Submodule.zero_mem _

theorem tupleNormalizeOrdered_increasing (V : Type w) (o : LinearOrder V)
    (n : ℕ) (s : Simplex (tupleFullComplex V) n) (a : A) :
    tupleNormalizeOrdered R A V o (n+1) (Finsupp.single (s.1 : Fin (n+1) → V) a) =
      (Equiv.Perm.sign (sortingPermutation o s.1) : ℤ) •
        Finsupp.single ((reorderedSimplex o s).1 : Fin (n+1) → V) a := by
  change tupleOrderedIncreasingLinear R A V o n
    (orderTransitionLinear R A (tupleFullComplex V) o n
      (tupleOrientedLinear R A V n (Finsupp.single (s.1 : Fin (n+1) → V) a))) = _
  rw [tupleOrientedLinear_single]
  have hs : fullVertexTuple (s.1 : Fin (n+1) → V) = (⟨s.1,s.2⟩ : VertexTuple (tupleFullComplex V) n) := rfl
  rw [hs, P202.OrientedSimplicialAlgebra.oriented_increasing,
    orderTransitionLinear_single, map_zsmul, tupleOrderedIncreasingLinear_single]


theorem tupleNormalizeOrdered_simplex {V : Type w} {K : AbstractSimplicialComplex V}
    (o : LinearOrder V) (n : ℕ) (s : Simplex K n) (a : A) :
    tupleNormalizeOrdered R A V o (n+1) (Finsupp.single (s.1 : Fin (n+1) → V) a) =
      (Equiv.Perm.sign (sortingPermutation o s.1) : ℤ) •
        Finsupp.single ((reorderedSimplex o s).1 : Fin (n+1) → V) a := by
  letI : LinearOrder V := vertexOrder V
  let s' : Simplex (tupleFullComplex V) n :=
    ⟨s.1, Finset.image_nonempty.mpr Finset.univ_nonempty⟩
  exact tupleNormalizeOrdered_increasing R A V o n s' a


end


section
open P202Specs.OrientedSimplicialAlgebra
def rawTupleImage {V W : Type w} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) (n : ℕ) :
    P202Specs.OrientedSimplicialAlgebra.Chains K A n →ₗ[R] TupleChains A W (n+1) :=
  Finsupp.lmapDomain A R (fun s => f.vertices ∘ s.1)

@[simp] theorem rawTupleImage_single {V W : Type w} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) (n : ℕ)
    (s : P202Specs.OrientedSimplicialAlgebra.Simplex K n) (a : A) :
    rawTupleImage R A f n (Finsupp.single s a) = Finsupp.single (f.vertices ∘ s.1) a := by
  simp [rawTupleImage]

theorem rawTupleImage_valid {V W : Type w} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (n : ℕ) (c : P202Specs.OrientedSimplicialAlgebra.Chains K A n) :
    rawTupleImage R A f n c ∈
      Finsupp.supported A R {t | Finset.univ.image t ∈ L.simplices} := by
  apply map_supported R A Set.univ _ (rawTupleImage R A f n) ?_ c
    (by exact Finsupp.supported_mono (by intro _ _; trivial) (Finsupp.mem_supported_support R c))
  intro s _ a
  rw [rawTupleImage_single]
  apply Finsupp.single_mem_supported
  exact (f.imageTuple (⟨s.1, s.2⟩ : P202Specs.OrientedSimplicialAlgebra.VertexTuple K n)).2

theorem rawTupleImage_boundary {V W : Type w} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) (n : ℕ) :
    (tupleBoundary R A W (n+1)).comp (rawTupleImage R A f (n+1)) =
      (rawTupleImage R A f n).comp (P202Specs.OrientedSimplicialAlgebra.boundary R A n) := by
  apply Finsupp.lhom_ext
  intro s a
  simp only [LinearMap.comp_apply, rawTupleImage_single]
  rw [tupleBoundary_single, P202.SimplicialChains.Oriented.boundary_single]
  simp only [map_sum, map_zsmul, rawTupleImage_single]
  rfl

theorem rawTupleImage_normalize {V W : Type w} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) (n : ℕ) :
    (tupleNormalize R A W (n+1)).comp (rawTupleImage R A f n) =
      (Finsupp.lmapDomain A R (fun s : P202Specs.OrientedSimplicialAlgebra.Simplex L n =>
        (s.1 : Fin (n+1) → W))).comp
          (P202Specs.OrientedSimplicialAlgebra.pushforward R A f n) := by
  classical
  apply Finsupp.lhom_ext
  intro s a
  change tupleNormalize R A W (n+1) (rawTupleImage R A f n (Finsupp.single s a)) =
    (Finsupp.lmapDomain A R (fun s : P202Specs.OrientedSimplicialAlgebra.Simplex L n =>
      (s.1 : Fin (n+1) → W)))
        (P202Specs.OrientedSimplicialAlgebra.pushforward R A f n (Finsupp.single s a))
  rw [rawTupleImage_single, tupleNormalize_single]
  erw [P202.SimplicialChains.Oriented.pushforward_single]
  simp only [P202Specs.OrientedSimplicialAlgebra.oriented,
    P202Specs.OrientedSimplicialAlgebra.SimplicialMap.imageTuple]
  split
  · simp only [map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
    rfl
  · simp only [map_zero]

theorem totalTupleEvaluation_rawImage {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (g : TopCat.of K.Realization ⟶ TopCat.of L.Realization)
    (hg : ∀ x, (g x).val = x.val.map f.vertices) (n : ℕ) :
    (totalTupleEvaluation R A L n).comp (rawTupleImage R A f n) =
      (((chainMap R A g).f n).hom).comp (Simplicial.affineLinear K R A n) := by
  apply Finsupp.lhom_ext
  intro s a
  change totalTupleEvaluation R A L n (rawTupleImage R A f n (Finsupp.single s a)) =
    ((chainMap R A g).f n).hom (Simplicial.affineLinear K R A n (Finsupp.single s a))
  rw [rawTupleImage_single]
  have hs := (f.imageTuple (⟨s.1, s.2⟩ : P202Specs.OrientedSimplicialAlgebra.VertexTuple K n)).2
  erw [totalTupleEvaluation_single_valid R A L n _ hs]
  erw [P202.SimplicialChains.Simplicial.affineLinear_single,
    P202.SingularChains.chainMap_single]
  congr 1
  apply (P202Specs.SingularChains.simplexEquiv _ n).injective
  rw [P202.SingularChains.simplexEquiv_postcomp]
  simp only [tupleSingularSimplex, Equiv.apply_symm_apply]
  exact tupleParametrization_natural K L f g hg n ⟨s.1, s.2⟩

theorem totalTupleEvaluation_normalize_rawImage {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) (n : ℕ) :
    (totalTupleEvaluation R A L n).comp
        ((tupleNormalize R A W (n+1)).comp (rawTupleImage R A f n)) =
      (Simplicial.affineLinear L R A n).comp
        (P202Specs.OrientedSimplicialAlgebra.pushforward R A f n) := by
  rw [rawTupleImage_normalize, ← LinearMap.comp_assoc, totalTupleEvaluation_increasing]


end


/-- Transporting an ordinary relative cycle yields a cycle in the supported
nonnegative model, including its ordinary degree-zero convention. -/
theorem singularRelativeDegreeEquiv_cycle (X : TopCat.{w}) (Y : Set X) (n : ℕ)
    (z : (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).X (n : ℤ))
    (hz : (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).d (n : ℤ) ((n : ℤ)-1) z = 0) :
    (singularRelativeComplex R A X Y).d n ((ComplexShape.down ℕ).next n)
      (singularRelativeDegreeEquiv R A X Y n
        ((P202Specs.RelativeSingularChains.ordinaryDegreeIso R A ⟨X,Y⟩ n).hom z)) = 0 := by
  let zcy := (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).cyclesMk z
    ((n : ℤ)-1) (by simp) hz
  have h := congrArg (fun f => f zcy) (singularRelativeCyclesIso_iCycles R A X Y n)
  change (singularRelativeComplex R A X Y).iCycles n
      ((singularRelativeCyclesIso R A X Y n).hom zcy) =
    singularRelativeDegreeEquiv R A X Y n
      ((P202Specs.RelativeSingularChains.ordinaryDegreeIso R A ⟨X,Y⟩ n).hom
        ((P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).iCycles (n : ℤ) zcy)) at h
  have hzcy : (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩).iCycles (n : ℤ) zcy = z :=
    HomologicalComplex.i_cyclesMk (P202Specs.RelativeSingularChains.ordinary R A ⟨X,Y⟩)
      z ((n : ℤ)-1) (by simp) hz
  rw [hzcy] at h
  rw [← h]
  exact congrArg (fun f => f ((singularRelativeCyclesIso R A X Y n).hom zcy))
    ((singularRelativeComplex R A X Y).iCycles_d n ((ComplexShape.down ℕ).next n))

@[simp] theorem singularRelativeDegreeEquiv_affine (n : ℕ) (a : A) :
    singularRelativeDegreeEquiv R A (P202Specs.SpheresDisks.simplex n)
      (P202Specs.SpheresDisks.simplexPair n).subspace n
      ((P202Specs.RelativeSingularChains.ordinaryDegreeIso R A
        (P202Specs.SpheresDisks.simplexPair n) n).hom
        (P202Specs.SpheresDisks.relativeAffineChain R A n a)) =
      ((singularSelection R A (P202Specs.SpheresDisks.simplex n)
        (P202Specs.SpheresDisks.simplexPair n).subspace).module n).mkQ
          (P202Specs.SpheresDisks.affineChain A n a) := by
  have h := congrArg (fun f => f (P202Specs.SpheresDisks.affineChainZ R A n a))
    (P202.RelativeSingularChains.ordinary_degree R A (P202Specs.SpheresDisks.simplexPair n) n)
  change (P202Specs.RelativeSingularChains.ordinaryDegreeIso R A
      (P202Specs.SpheresDisks.simplexPair n) n).hom
      (P202Specs.SpheresDisks.relativeAffineChain R A n a) =
    (P202Specs.RelativeSingularChains.projection (chainFunctor R A)
      (P202Specs.SpheresDisks.simplexPair n)).f n
      ((ordinaryNonnegativeIso R A (P202Specs.SpheresDisks.simplex n) n).hom
        (P202Specs.SpheresDisks.affineChainZ R A n a)) at h
  rw [h]
  have hz : (ordinaryNonnegativeIso R A (P202Specs.SpheresDisks.simplex n) n).hom
      (P202Specs.SpheresDisks.affineChainZ R A n a) =
      P202Specs.SpheresDisks.affineChain A n a := by
    exact (ordinaryNonnegativeIso R A (P202Specs.SpheresDisks.simplex n) n).inv_hom_id_apply _
  rw [hz]
  exact singularRelativeDegreeEquiv_projection R A _ _ n _


/-- The full generator premise gives the exact affine-chain generator in the
supported quotient model, with arbitrary module coefficients. -/
theorem simplexRelativeHomology_generator
    (hgenerator : P202Specs.SpheresDisks.simplexGenerator_type.{u,v}) (n : ℕ) :
    ∃ hz : ∀ a : A,
      (singularRelativeComplex R A (P202Specs.SpheresDisks.simplex n)
        (P202Specs.SpheresDisks.simplexPair n).subspace).d n ((ComplexShape.down ℕ).next n)
          (((singularSelection R A (P202Specs.SpheresDisks.simplex n)
            (P202Specs.SpheresDisks.simplexPair n).subspace).module n).mkQ
              (P202Specs.SpheresDisks.affineChain A n a)) = 0,
      ∃ e : (singularRelativeComplex R A (P202Specs.SpheresDisks.simplex n)
          (P202Specs.SpheresDisks.simplexPair n).subspace).homology n ≃ₗ[R] A,
        ∀ a, e (P202Specs.ChainLES.cycleClass
          (singularRelativeComplex R A (P202Specs.SpheresDisks.simplex n)
            (P202Specs.SpheresDisks.simplexPair n).subspace)
          ((ComplexShape.down ℕ).next n) rfl
          (((singularSelection R A (P202Specs.SpheresDisks.simplex n)
            (P202Specs.SpheresDisks.simplexPair n).subspace).module n).mkQ
              (P202Specs.SpheresDisks.affineChain A n a)) (hz a)) = a := by
  obtain ⟨hz, e, he⟩ := hgenerator R A n
  have hc (a : A) :
      (singularRelativeComplex R A (P202Specs.SpheresDisks.simplex n)
        (P202Specs.SpheresDisks.simplexPair n).subspace).d n ((ComplexShape.down ℕ).next n)
          (((singularSelection R A (P202Specs.SpheresDisks.simplex n)
            (P202Specs.SpheresDisks.simplexPair n).subspace).module n).mkQ
              (P202Specs.SpheresDisks.affineChain A n a)) = 0 := by
    have h := singularRelativeDegreeEquiv_cycle R A
      (P202Specs.SpheresDisks.simplex n) (P202Specs.SpheresDisks.simplexPair n).subspace n
      (P202Specs.SpheresDisks.relativeAffineChain R A n a) (hz a)
    erw [singularRelativeDegreeEquiv_affine] at h
    exact h
  let E := singularRelativeHomologyIso R A (P202Specs.SpheresDisks.simplex n)
    (P202Specs.SpheresDisks.simplexPair n).subspace n
  refine ⟨hc, E.toLinearEquiv.symm.trans e, ?_⟩
  intro a
  have h := singularRelativeHomologyIso_cycle R A (P202Specs.SpheresDisks.simplex n)
    (P202Specs.SpheresDisks.simplexPair n).subspace n
    (P202Specs.SpheresDisks.relativeAffineChain R A n a) (hz a) _ (hc a)
    (singularRelativeDegreeEquiv_affine R A n a)
  have eh := congrArg (fun z => e (E.toLinearEquiv.symm z)) h
  change e (E.toLinearEquiv.symm (E.toLinearEquiv _)) = _ at eh
  rw [LinearEquiv.symm_apply_apply] at eh
  exact eh.symm.trans (he a)



section
variable {R : Type u} [CommRing R]
def homotopyOfDegreewise {C D : ChainComplex (ModuleCat.{v} R) ℕ}
    (f g : C ⟶ D) (H : ∀ n, C.X n ⟶ D.X (n+1))
    (hzero : f.f 0 = H 0 ≫ D.d 1 0 + g.f 0)
    (hsucc : ∀ n, f.f (n+1) = C.d (n+1) n ≫ H n +
      H (n+1) ≫ D.d (n+2) (n+1) + g.f (n+1)) : Homotopy f g where
  hom i j := if h : j = i+1 then H i ≫ eqToHom (congrArg D.X h.symm) else 0
  zero i j hij := by
    have h : j ≠ i+1 := by
      intro h
      apply hij
      exact h.symm
    simp only [h, ↓reduceDIte]
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex]
      simpa only [dite_true, eqToHom_refl, Category.comp_id, zero_add] using hzero
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex]
      simpa only [dite_true, eqToHom_refl, Category.comp_id] using hsucc n

end


section
open P202Specs.OrientedSimplicialAlgebra
def simplicialTupleLinear {V : Type w} (K : AbstractSimplicialComplex V) (n : ℕ) :
    Chains K A n →ₗ[R] TupleChains A V (n+1) :=
  Finsupp.lmapDomain A R (fun s => (s.1 : Fin (n+1) → V))

@[simp] theorem simplicialTupleLinear_single {V : Type w} (K : AbstractSimplicialComplex V)
    (n : ℕ) (s : Simplex K n) (a : A) :
    simplicialTupleLinear R A K n (Finsupp.single s a) = Finsupp.single (s.1 : Fin (n+1) → V) a := by
  simp [simplicialTupleLinear]

theorem simplicialTupleLinear_boundary {V : Type w} (K : AbstractSimplicialComplex V) (n : ℕ) :
    (tupleBoundary R A V (n+1)).comp (simplicialTupleLinear R A K (n+1)) =
      (simplicialTupleLinear R A K n).comp (boundary R A n) := by
  classical
  apply Finsupp.lhom_ext
  intro s a
  simp only [LinearMap.comp_apply, simplicialTupleLinear_single]
  rw [tupleBoundary_single, P202.OrientedSimplicialAlgebra.boundary_single]
  simp only [map_sum, map_zsmul, simplicialTupleLinear_single]
  rfl

theorem simplicialTupleLinear_valid {V : Type w} (K : AbstractSimplicialComplex V) (n : ℕ)
    (c : Chains K A n) :
    simplicialTupleLinear R A K n c ∈
      Finsupp.supported A R {t | Finset.univ.image t ∈ K.simplices} := by
  classical
  apply map_supported R A Set.univ _ (simplicialTupleLinear R A K n) ?_ c
    ((Finsupp.mem_supported R c).mpr (Set.subset_univ _))
  intro s _ a
  rw [simplicialTupleLinear_single]
  exact Finsupp.single_mem_supported R a s.2

theorem simplicialTupleLinear_selected {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (n : ℕ) (c : Chains K A n)
    (hc : c ∈ (Simplicial.selection R A K B).module n) :
    simplicialTupleLinear R A K n c ∈
      Finsupp.supported A R {t | Finset.univ.image t ∈ B.complex.simplices} := by
  apply map_supported R A _ _ (simplicialTupleLinear R A K n) ?_ c hc
  intro s hs a
  rw [simplicialTupleLinear_single]
  exact Finsupp.single_mem_supported R a hs

theorem totalTupleEvaluation_ordered_single {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) (s : (orderedDelta K o).Simplex n) (a : A) :
    totalTupleEvaluation R A K n (Finsupp.single (s.1 : Fin (n+1) → V) a) =
      Finsupp.single (orderedSingularSimplex K o n s) a := by
  change totalTupleEvaluation R A K n (Finsupp.single (orderedTuple K o s).1 a) = _
  rw [totalTupleEvaluation_single_valid R A K n _ (orderedTuple K o s).2]
  congr 1
  apply (P202Specs.SingularChains.simplexEquiv _ n).injective
  simp only [tupleSingularSimplex, orderedSingularSimplex, Equiv.apply_symm_apply]
  ext t
  apply Subtype.ext
  rw [tupleParametrization_value, orderedParametrization_value]
  rfl

theorem totalTupleEvaluation_normalized_order {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) :
    (totalTupleEvaluation R A K n).comp
      ((tupleNormalizeOrdered R A V o (n+1)).comp (simplicialTupleLinear R A K n)) =
      (orderedAffineLinear R A K o n).comp (orderTransitionLinear R A K o n) := by
  apply Finsupp.lhom_ext
  intro s a
  simp only [LinearMap.comp_apply, simplicialTupleLinear_single,
    tupleNormalizeOrdered_simplex, map_zsmul, totalTupleEvaluation_ordered_single,
    orderTransitionLinear_single, orderedAffineLinear_single]

def orderComparisonHomotopyLinear {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) : Chains K A n →ₗ[R]
      P202Specs.SingularChains.Chains A (TopCat.of K.Realization) (n+1) :=
  (totalTupleEvaluation R A K (n+1)).comp
    ((tupleHomotopy R A (tupleNormalizeOrdered R A V o) (n+1)).comp
      (simplicialTupleLinear R A K n))

theorem orderComparisonHomotopyLinear_selected {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) (n : ℕ)
    (c : Chains K A n) (hc : c ∈ (Simplicial.selection R A K B).module n) :
    orderComparisonHomotopyLinear R A K o n c ∈
      (singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module (n+1) := by
  apply totalTupleEvaluation_preserves R A K B (n+1)
  apply tupleHomotopy_valid R A B.complex (tupleNormalizeOrdered R A V o)
    (tupleNormalizeOrdered_preserves R A V o) n
  exact simplicialTupleLinear_selected R A K B n c hc

theorem orderComparisonHomotopyLinear_zero {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (c : Chains K A 0) :
    singularTupleBoundary R A K 0
      (orderComparisonHomotopyLinear R A K o 0 c) =
      orderedAffineLinear R A K o 0 (orderTransitionLinear R A K o 0 c) -
        Simplicial.affineLinear K R A 0 c := by
  have h := totalTupleEvaluation_homotopy_identity R A K (tupleNormalizeOrdered R A V o)
    (tupleNormalizeOrdered_zero R A V o) (tupleNormalizeOrdered_boundary R A V o)
    (tupleNormalizeOrdered_preserves R A V o) 0 (simplicialTupleLinear R A K 0 c)
    (simplicialTupleLinear_valid R A K 0 c)
  have hn := LinearMap.congr_fun (totalTupleEvaluation_normalized_order R A K o 0) c
  have he := LinearMap.congr_fun (totalTupleEvaluation_increasing R A K 0) c
  simp only [LinearMap.comp_apply] at hn he
  change totalTupleEvaluation R A K 0 (simplicialTupleLinear R A K 0 c) = _ at he
  simp only [tupleHomotopy, Nat.rec_zero, LinearMap.zero_apply, map_zero, add_zero] at h
  rw [hn, he] at h
  exact h

theorem orderComparisonHomotopyLinear_succ {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) (c : Chains K A (n+1)) :
    singularTupleBoundary R A K (n+1)
        (orderComparisonHomotopyLinear R A K o (n+1) c) +
      orderComparisonHomotopyLinear R A K o n (boundary R A n c) =
      orderedAffineLinear R A K o (n+1) (orderTransitionLinear R A K o (n+1) c) -
        Simplicial.affineLinear K R A (n+1) c := by
  have h := totalTupleEvaluation_homotopy_identity R A K (tupleNormalizeOrdered R A V o)
    (tupleNormalizeOrdered_zero R A V o) (tupleNormalizeOrdered_boundary R A V o)
    (tupleNormalizeOrdered_preserves R A V o) (n+1) (simplicialTupleLinear R A K (n+1) c)
    (simplicialTupleLinear_valid R A K (n+1) c)
  have hn := LinearMap.congr_fun (totalTupleEvaluation_normalized_order R A K o (n+1)) c
  have he := LinearMap.congr_fun (totalTupleEvaluation_increasing R A K (n+1)) c
  have hb := LinearMap.congr_fun (simplicialTupleLinear_boundary R A K n) c
  simp only [LinearMap.comp_apply] at hn he hb
  change totalTupleEvaluation R A K (n+1) (simplicialTupleLinear R A K (n+1) c) = _ at he
  rw [hn, he, hb] at h
  exact h


end


section
theorem homologyMap_eq_of_cycle_boundaries
    {C D : ChainComplex (ModuleCat.{v} R) ℕ} (f g : C ⟶ D) (q : ℕ)
    (h : ∀ (x : (C.sc q).X₂), (C.sc q).g x = 0 →
      ∃ z : (D.sc q).X₁, (D.sc q).f z = (f.f q) x - (g.f q) x) :
    homologyMap f q = homologyMap g q := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨x,hx,rfl⟩ := moduleCycleClass_surjective (C.sc q) z
  change ShortComplex.homologyMap ((shortComplexFunctor _ _ q).map f) _ =
    ShortComplex.homologyMap ((shortComplexFunctor _ _ q).map g) _
  rw [moduleCycleClass_natural, moduleCycleClass_natural]
  apply (moduleCycleClass_eq_iff (D.sc q) _ _ _ _).mpr
  exact h x hx

theorem simplicialNaturality_absolute_square {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (B : Simplicial.Subcomplex K) (E : Simplicial.Subcomplex L)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (g : TopCat.of K.Realization ⟶ TopCat.of L.Realization)
    (hg : ∀ x, (g x).val = x.val.map f.vertices)
    (T : P202Specs.OrientedSimplicialAlgebra.complex R A (K := K) ⟶
      P202Specs.OrientedSimplicialAlgebra.complex R A (K := L))
    (hT : ∀ n, (T.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward R A f n)
    (F : SimplicialComparisonData R A K B) (G : SimplicialComparisonData R A L E)
    (q : ℕ) :
    homologyMap T q ≫ homologyMap G.absolute q =
      homologyMap F.absolute q ≫ homologyMap (chainMap R A g) q := by
  rw [← homologyMap_comp, ← homologyMap_comp]
  apply homologyMap_eq_of_cycle_boundaries R
  intro x hx
  have hcycle : q = 0 ∨ tupleBoundary R A W q (rawTupleImage R A f q x) = 0 := by
    cases q with
    | zero => exact Or.inl rfl
    | succ n =>
      right
      have hb : P202Specs.OrientedSimplicialAlgebra.boundary R A n x = 0 := by
        change (P202Specs.OrientedSimplicialAlgebra.complex R A (K := K)).d
          (n+1) ((ComplexShape.down ℕ).next (n+1)) x = 0 at hx
        rw [ChainComplex.next_nat_succ] at hx
        change ((P202Specs.OrientedSimplicialAlgebra.complex R A (K := K)).d (n+1) n).hom x = 0 at hx
        erw [P202.SimplicialChains.Oriented.boundary_eq] at hx
        exact hx
      have h := LinearMap.congr_fun (rawTupleImage_boundary R A f n) x
      simpa only [LinearMap.comp_apply, hb, map_zero] using h
  have hh := totalTupleEvaluation_cycle_difference R A L (tupleNormalize R A W)
    (tupleNormalize_zero R A W) (tupleNormalize_boundary R A W)
    (tupleNormalize_preserves R A W) q (rawTupleImage R A f q x)
    (rawTupleImage_valid R A f q x) hcycle
  have hn := LinearMap.congr_fun (totalTupleEvaluation_normalize_rawImage R A K L f q) x
  have hr := LinearMap.congr_fun (totalTupleEvaluation_rawImage R A K L f g hg q) x
  simp only [LinearMap.comp_apply] at hn hr
  rw [hn, hr] at hh
  change ∃ z : (P202Specs.SingularChains.complex R A (TopCat.of L.Realization)).X
      ((ComplexShape.down ℕ).prev q),
    (P202Specs.SingularChains.complex R A (TopCat.of L.Realization)).d
      ((ComplexShape.down ℕ).prev q) q z =
        (G.absolute.f q) ((T.f q) x) - ((chainMap R A g).f q) ((F.absolute.f q) x)
  rw [ChainComplex.prev]
  refine ⟨totalTupleEvaluation R A L (q+1)
    (tupleHomotopy R A (tupleNormalize R A W) (q+1) (rawTupleImage R A f q x)), ?_⟩
  change singularTupleBoundary R A L q _ =
    (G.absolute.f q).hom ((T.f q).hom x) - ((chainMap R A g).f q).hom ((F.absolute.f q).hom x)
  rw [G.absolute_formula, F.absolute_formula, hT]
  exact hh


end


section
variable {R : Type u} [CommRing R]
variable {C D : ChainComplex (ModuleCat.{v} R) ℕ}
def selectionSubcomplexMap (S : ChainSelection R C) (T : ChainSelection R D)
    (f : C ⟶ D) (hf : ∀ n x, x ∈ S.module n → (f.f n).hom x ∈ T.module n) :
    S.subcomplex ⟶ T.subcomplex :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    (((f.f n).hom.comp (S.module n).subtype).codRestrict (T.module n)
      (fun x => hf n x.1 x.2))) (by
    intro n
    simp only [ChainSelection.subcomplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (D.d (n+1) n).hom ((f.f (n+1)).hom x.1) =
      (f.f n).hom ((C.d (n+1) n).hom x.1)
    exact congrArg (fun g : C.X (n+1) ⟶ D.X n => g.hom x.1) (f.comm (n+1) n))

def selectionSequence (S : ChainSelection R C) : ShortComplex (ChainComplex (ModuleCat.{v} R) ℕ) :=
  ShortComplex.mk S.inclusion S.projection (by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (S.module n).mkQ x.1 = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr x.2)

theorem selectionSequence_shortExact (S : ChainSelection R C) :
    (selectionSequence S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    change (S.module n).mkQ x = 0 at hx
    refine ⟨⟨x, (Submodule.Quotient.mk_eq_zero _).mp hx⟩, rfl⟩
  · exact (ModuleCat.mono_iff_injective _).mpr Subtype.val_injective
  · exact (ModuleCat.epi_iff_surjective _).mpr (S.module n).mkQ_surjective

def selectionSequenceMap (S : ChainSelection R C) (T : ChainSelection R D)
    (f : C ⟶ D) (hf : ∀ n x, x ∈ S.module n → (f.f n).hom x ∈ T.module n) :
    selectionSequence S ⟶ selectionSequence T :=
  ShortComplex.Hom.mk (selectionSubcomplexMap S T f hf) f (S.quotientMap T f hf)
    (by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      rfl)
    (by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      rfl)

/-- The exact sequence of supported chains transfers absolute comparison on
both the ambient complex and its subcomplex to every relative quotient. -/
theorem selectionQuotientComparison_isIso (S : ChainSelection R C) (T : ChainSelection R D)
    (f : C ⟶ D) (hf : ∀ n x, x ∈ S.module n → (f.f n).hom x ∈ T.module n)
    (hsub : ∀ q, IsIso (homologyMap (selectionSubcomplexMap S T f hf) q))
    (habs : ∀ q, IsIso (homologyMap f q)) (q : ℕ) :
    IsIso (homologyMap (S.quotientMap T f hf) q) := by
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃
    (selectionSequenceMap S T f hf) (selectionSequence_shortExact S) (selectionSequence_shortExact T) q
  · change Epi (homologyMap (selectionSubcomplexMap S T f hf) q)
    haveI := hsub q
    infer_instance
  · exact habs q
  · intro j hj
    exact hsub j
  · intro j hj
    change Mono (homologyMap f j)
    haveI := habs j
    infer_instance

end


section
variable {R : Type u} [CommRing R]
/-- A finite abstract simplicial complex has compact weak realization. -/
theorem finiteSimplicialRealization_compact {V : Type w}
    (K : AbstractSimplicialComplex V) (hK : K.simplices.Finite) :
    CompactSpace K.Realization := by
  letI : Finite K.Simplex := hK.to_subtype
  have hc : IsCompact (⋃ s : K.Simplex, Set.range (K.simplexChart s)) :=
    isCompact_iUnion fun s => isCompact_range (P202.Topology.simplicialChartContinuous K s)
  have he : (⋃ s : K.Simplex, Set.range (K.simplexChart s)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨s,⟨t,ht,rfl⟩,_⟩ := P202.Topology.simplicialInteriorPartition K x
    exact Set.mem_iUnion.mpr ⟨s, ⟨t,rfl⟩⟩
  rw [he] at hc
  exact isCompact_univ_iff.mp hc

/-- Finite subcomplex inclusion has its actual subspace topology. -/
def finiteSimplicialSubcomplexHomeomorph {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K)
    (hB : B.complex.simplices.Finite) : B.complex.Realization ≃ₜ B.carrier K := by
  let g := simplicialRealization
    (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset)
  have hg : ∀ x, (g x).1 = x.1 := by
    intro x
    rw [simplicialRealization_value]
    exact Convexity.StdSimplex.map_id x.1
  have hi : Function.Injective g := by
    intro x y h
    apply Subtype.ext
    simpa only [hg] using congrArg Subtype.val h
  have hr : Set.range g = B.carrier K := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      change (g y).1.weights.support ∈ B.complex.simplices
      rw [hg]
      exact y.2
    · intro hx
      refine ⟨⟨x.1,hx⟩, ?_⟩
      apply Subtype.ext
      exact hg _
  letI := finiteSimplicialRealization_compact B.complex hB
  letI := P202.Topology.simplicialHausdorff K
  exact (g.hom.continuous.isClosedEmbedding hi).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hr)

/-- Finite unions remain subcomplexes on the same ambient vertex type. -/
def simplicialSubcomplexUnion {V : Type w} (K : AbstractSimplicialComplex V)
    (B C : Simplicial.Subcomplex K) : Simplicial.Subcomplex K where
  complex := {
    simplices := B.complex.simplices ∪ C.complex.simplices
    nonempty := fun s hs => hs.elim (B.complex.nonempty s) (C.complex.nonempty s)
    face := by
      intro s t hs hts ht
      exact hs.elim (fun h => Or.inl (B.complex.face h hts ht))
        (fun h => Or.inr (C.complex.face h hts ht)) }
  subset := fun s hs => hs.elim (fun h => B.subset h) (fun h => C.subset h)


variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- A supported singular chain of a finite subcomplex lifts to its intrinsic
weak realization, through the actual subspace homeomorphism. -/
theorem singularFiniteSimplicialLift {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (hB : B.complex.simplices.Finite) (q : ℕ)
    (c : Chains A (TopCat.of K.Realization) q)
    (hc : c ∈ (singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module q) :
    ∃ c' : Chains A (TopCat.of B.complex.Realization) q,
      ((chainMap R A (simplicialRealization
        (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset))).f q).hom c' = c := by
  let h := finiteSimplicialSubcomplexHomeomorph K B hB
  let hinv : TopCat.of (B.carrier K) ⟶ TopCat.of B.complex.Realization :=
    TopCat.ofHom ⟨h.symm,h.symm.continuous⟩
  let g := simplicialRealization
    (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset)
  have hcomp : hinv ≫ g = subspaceInclusion (TopCat.of K.Realization) (B.carrier K) := by
    ext x
    have hh := congrArg Subtype.val (h.apply_symm_apply x)
    change g (h.symm x) = x.1
    exact hh
  obtain ⟨c₀,hc₀⟩ := singularSubspaceLift R A _ _ _ hc
  refine ⟨((chainMap R A hinv).f q).hom c₀, ?_⟩
  have hmap : chainMap R A hinv ≫ chainMap R A g =
      chainMap R A (subspaceInclusion (TopCat.of K.Realization) (B.carrier K)) := by
    rw [← P202.SingularChains.chainMap_comp, hcomp]
  have hh := congrArg (fun f => (f.f q).hom c₀) hmap
  exact hh.trans hc₀


/-- A simplicial chain and two singular chains in successive degrees lift
simultaneously to one finite subcomplex, with the original canonical maps. -/
theorem simplicialMixedFiniteLift {V : Type w} (K : AbstractSimplicialComplex V) (q r : ℕ)
    (x : P202Specs.OrientedSimplicialAlgebra.Chains K A q)
    (y : Chains A (TopCat.of K.Realization) q)
    (z : Chains A (TopCat.of K.Realization) r) :
    ∃ (B : Simplicial.Subcomplex K) (_ : B.complex.simplices.Finite)
      (x₀ : P202Specs.OrientedSimplicialAlgebra.Chains B.complex A q)
      (y₀ : Chains A (TopCat.of B.complex.Realization) q)
      (z₀ : Chains A (TopCat.of B.complex.Realization) r),
      P202Specs.OrientedSimplicialAlgebra.pushforward R A
        (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset) q x₀ = x ∧
      ((chainMap R A (simplicialRealization
        (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset))).f q).hom y₀ = y ∧
      ((chainMap R A (simplicialRealization
        (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset))).f r).hom z₀ = z := by
  classical
  let F := x.support.biUnion (fun s => Finset.univ.image s.1)
  let C := simplicialFiniteRestriction K F
  let degree : Bool → ℕ := fun b => cond b r q
  let cs : ∀ b, Chains A (TopCat.of K.Realization) (degree b) := fun b => Bool.rec y z b
  obtain ⟨B,hB,hc⟩ := simplicialChainsFiniteSupport R A K degree cs
  let E := simplicialSubcomplexUnion K C B
  have hE : E.complex.simplices.Finite := (simplicialFiniteRestriction_finite K F).union hB
  have hx : x ∈ (Simplicial.selection R A K E).module q := by
    intro s hs
    apply Or.inl
    refine ⟨s.2, ?_⟩
    intro v hv
    exact Finset.mem_biUnion.mpr ⟨s,hs,hv⟩
  have hy : y ∈ (singularSelection R A (TopCat.of K.Realization) (E.carrier K)).module q := by
    intro s hs t
    exact Or.inr (hc false hs t)
  have hz : z ∈ (singularSelection R A (TopCat.of K.Realization) (E.carrier K)).module r := by
    intro s hs t
    exact Or.inr (hc true hs t)
  rw [← P202.SimplicialChains.Simplicial.inclusion_range R A K E q] at hx
  obtain ⟨x₀,hx₀⟩ := hx
  obtain ⟨y₀,hy₀⟩ := singularFiniteSimplicialLift R A K E hE q y hy
  obtain ⟨z₀,hz₀⟩ := singularFiniteSimplicialLift R A K E hE r z hz
  exact ⟨E,hE,x₀,y₀,z₀,hx₀,hy₀,hz₀⟩


/-- Homology isomorphisms pass through simultaneous finite-support
factorizations. The inclusions need only reflect the displayed chain equations. -/
theorem homologyMap_isIso_of_local_factorizations
    {S T : ShortComplex (ModuleCat.{v} R)} (f : S ⟶ T)
    (hlocal : ∀ (x : S.X₂) (y : T.X₂) (z : T.X₁),
      ∃ (S₀ T₀ : ShortComplex (ModuleCat.{v} R)) (f₀ : S₀ ⟶ T₀)
        (i : S₀ ⟶ S) (j : T₀ ⟶ T),
        IsIso (ShortComplex.homologyMap f₀) ∧
        Function.Injective i.τ₃ ∧ Function.Injective j.τ₂ ∧ Function.Injective j.τ₃ ∧
        i ≫ f = f₀ ≫ j ∧
        ∃ (x₀ : S₀.X₂) (y₀ : T₀.X₂) (z₀ : T₀.X₁),
          i.τ₂ x₀ = x ∧ j.τ₂ y₀ = y ∧ j.τ₁ z₀ = z) :
    IsIso (ShortComplex.homologyMap f) := by
  apply homologyMap_isIso_of_cycle_conditions f
  · intro y hy
    obtain ⟨S₀,T₀,f₀,i,j,hiso,hi,hj,hj₃,hsq,x₀,y₀,z₀,hx₀,hy₀,hz₀⟩ := hlocal 0 y 0
    have hycycle : T₀.g y₀ = 0 := by
      apply hj₃
      have h := congrArg (fun k => k y₀) j.comm₂₃
      simpa only [ConcreteCategory.comp_apply, hy₀, hy, map_zero] using h.symm
    haveI := hiso
    obtain ⟨a,ha⟩ := (ModuleCat.epi_iff_surjective (ShortComplex.homologyMap f₀)).mp inferInstance
      (moduleCycleClass T₀ y₀ hycycle)
    obtain ⟨b,hb,rfl⟩ := moduleCycleClass_surjective S₀ a
    rw [moduleCycleClass_natural] at ha
    obtain ⟨c,hc⟩ := (moduleCycleClass_eq_iff T₀ _ _ _ _).mp ha
    refine ⟨i.τ₂ b, ?_, j.τ₁ c, ?_⟩
    · have h := congrArg (fun k => k b) i.comm₂₃
      simpa only [ConcreteCategory.comp_apply, hb, map_zero] using h
    · have hsq₂ := congrArg (fun k => k.τ₂ b) hsq
      have h := congrArg (fun k => k c) j.comm₁₂
      simp only [ConcreteCategory.comp_apply] at h
      change f.τ₂ (i.τ₂ b) = j.τ₂ (f₀.τ₂ b) at hsq₂
      rw [h, hc, map_sub, hy₀, hsq₂]
  · intro x hx hbound
    obtain ⟨z,hz⟩ := hbound
    obtain ⟨S₀,T₀,f₀,i,j,hiso,hi,hj,hj₃,hsq,x₀,y₀,z₀,hx₀,hy₀,hz₀⟩ := hlocal x 0 z
    have hxcycle : S₀.g x₀ = 0 := by
      apply hi
      have h := congrArg (fun k => k x₀) i.comm₂₃
      simpa only [ConcreteCategory.comp_apply, hx₀, hx, map_zero] using h.symm
    have hlocalbound : T₀.f z₀ = f₀.τ₂ x₀ := by
      apply hj
      have h := congrArg (fun k => k z₀) j.comm₁₂
      simp only [ConcreteCategory.comp_apply, hz₀, hz] at h
      have hsq₂ := congrArg (fun k => k.τ₂ x₀) hsq
      change f.τ₂ (i.τ₂ x₀) = j.τ₂ (f₀.τ₂ x₀) at hsq₂
      rw [hx₀] at hsq₂
      exact h.symm.trans hsq₂
    haveI := hiso
    have hzero : moduleCycleClass S₀ x₀ hxcycle = 0 := by
      apply (ModuleCat.mono_iff_injective (ShortComplex.homologyMap f₀)).mp inferInstance
      rw [map_zero]
      rw [moduleCycleClass_natural]
      exact (moduleCycleClass_eq_zero_iff T₀ _ _).mpr ⟨z₀,hlocalbound⟩
    obtain ⟨a,ha⟩ := (moduleCycleClass_eq_zero_iff S₀ x₀ hxcycle).mp hzero
    refine ⟨i.τ₁ a, ?_⟩
    have h := congrArg (fun k => k a) i.comm₁₂
    simpa only [ConcreteCategory.comp_apply, ha, hx₀] using h


/-- The canonical absolute comparison on every finite complex suffices for
arbitrary weak realizations. Both cycles and bounding chains are restricted
through the same actual finite-subcomplex inclusions. This is a reduction
lemma; it does not assume a finite-dimensional bound on the ambient complex. -/
theorem simplicialAbsoluteComparison_of_finite {V : Type w}
    (hfinite : ∀ (L : AbstractSimplicialComplex V), L.simplices.Finite →
      ∀ (G : SimplicialComparisonData R A L (Simplicial.Subcomplex.empty L)) (q : ℕ),
        IsIso (homologyMap G.absolute q))
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K)
    (F : SimplicialComparisonData R A K B) (q : ℕ) :
    IsIso (homologyMap F.absolute q) := by
  let sc := shortComplexFunctor (ModuleCat.{max v w} R) (ComplexShape.down ℕ) q
  change IsIso (ShortComplex.homologyMap (sc.map F.absolute))
  apply homologyMap_isIso_of_local_factorizations R (sc.map F.absolute)
  intro x y z
  obtain ⟨C,hC,x₀,y₀,z₀,hx₀,hy₀,hz₀⟩ :=
    simplicialMixedFiniteLift R A K q ((ComplexShape.down ℕ).prev q) x y z
  obtain ⟨G⟩ := simplicialComparisonData_nonempty R A C.complex (Simplicial.Subcomplex.empty _)
  obtain ⟨I,hI,hIinj,hIrange⟩ := P202.SimplicialChains.Simplicial.inclusion_chainMap R A K C
  let g := simplicialRealization
    (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion C.subset)
  let J := chainMap R A g
  have hginj : Function.Injective g := by
    intro a b hab
    apply (finiteSimplicialSubcomplexHomeomorph K C hC).injective
    exact Subtype.ext hab
  have hJinj : ∀ r, Function.Injective (J.f r).hom := singularMap_injective R A g hginj
  refine ⟨sc.obj (P202Specs.OrientedSimplicialAlgebra.complex R A (K := C.complex)),
    sc.obj (P202Specs.SingularChains.complex R A (TopCat.of C.complex.Realization)),
    sc.map G.absolute, sc.map I, sc.map J, hfinite C.complex hC G q,
    hIinj _, hJinj _, hJinj _, ?_, x₀, y₀, z₀, ?_, hy₀, hz₀⟩
  · have hs := simplicialInclusion_absolute_square R A C.complex K C.subset
      (Simplicial.Subcomplex.empty _) B I hI G F
    simpa only [Functor.map_comp] using congrArg sc.map hs
  · change (I.f q).hom x₀ = x
    rw [hI]
    exact hx₀



end


section
@[simp] theorem simplicialSubcomplexRealization_value {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K)
    (x : B.complex.Realization) :
    (simplicialRealization
      (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset) x).1 = x.1 := by
  rw [simplicialRealization_value]
  exact Convexity.StdSimplex.map_id x.1

/-- Every abstract simplicial subcomplex has precisely the intrinsic weak
realization topology on its ambient carrier. -/
theorem simplicialSubcomplexRealization_isClosedMap {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K) :
    IsClosedMap (simplicialRealization
      (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset)) := by
  let g := simplicialRealization
    (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset)
  have hgval : ∀ x, (g x).1 = x.1 := simplicialSubcomplexRealization_value K B
  intro C hC
  change IsClosed[⨆ s : K.Simplex,
    TopologicalSpace.coinduced (K.simplexChart s) inferInstance] (g '' C)
  rw [isClosed_iSup_iff]
  intro s
  rw [isClosed_coinduced]
  let P := simplicialFiniteRestriction B.complex s.1
  let i := simplicialRealization
    (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion P.subset)
  have hival : ∀ x, (i x).1 = x.1 := simplicialSubcomplexRealization_value B.complex P
  have hmem : ∀ x : P.complex.Realization, g (i x) ∈ Set.range (K.simplexChart s) := by
    intro x
    apply (P202.Topology.simplicialChart_range K s _).mpr
    rw [hgval,hival]
    exact x.2.2
  let e := (P202.Topology.simplicialChartEmbedding K s).toHomeomorph
  let lift : P.complex.Realization → K.GeometricSimplex s :=
    fun x => e.symm ⟨g (i x),hmem x⟩
  have hlift : Continuous lift :=
    e.symm.continuous.comp (((g.hom.continuous.comp i.hom.continuous)).subtype_mk hmem)
  have hliftvalue : ∀ x, K.simplexChart s (lift x) = g (i x) := by
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply ⟨g (i x),hmem x⟩)
  have hpre : K.simplexChart s ⁻¹' (g '' C) = lift '' (i ⁻¹' C) := by
    ext t
    constructor
    · rintro ⟨x,hx,hxt⟩
      have hs : x.1.weights.support ⊆ s.1 := by
        have h := (P202.Topology.simplicialChart_range K s (g x)).mp ⟨t,hxt.symm⟩
        rw [hgval] at h
        exact h
      let p : P.complex.Realization := ⟨x.1,x.2,hs⟩
      have hip : i p = x := by
        apply Subtype.ext
        exact simplicialSubcomplexRealization_value B.complex P p
      refine ⟨p, ?_, ?_⟩
      · change i p ∈ C
        rw [hip]
        exact hx
      ·
        apply (P202.Topology.simplicialChartEmbedding K s).injective
        rw [hliftvalue,hip,hxt]
    · rintro ⟨x,hx,rfl⟩
      exact ⟨i x,hx,(hliftvalue x).symm⟩
  letI := finiteSimplicialRealization_compact P.complex
    (simplicialFiniteRestriction_finite B.complex s.1)
  letI : T2Space (K.GeometricSimplex s) :=
    (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ s.1).t2Space
  rw [hpre]
  exact ((hC.preimage i.hom.continuous).isCompact.image hlift).isClosed


/-- The canonical realization map of any subcomplex is a closed embedding. -/
theorem simplicialSubcomplexRealization_isClosedEmbedding {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K) :
    IsClosedEmbedding (simplicialRealization
      (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset)) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
    (simplicialRealization _).hom.continuous ?_
    (simplicialSubcomplexRealization_isClosedMap K B)
  intro x y h
  apply Subtype.ext
  have hh := congrArg Subtype.val h
  exact (simplicialSubcomplexRealization_value K B x).symm.trans
    (hh.trans (simplicialSubcomplexRealization_value K B y))

/-- The range is the original support-defined carrier, not a chosen model. -/
theorem simplicialSubcomplexRealization_range {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K) :
    Set.range (simplicialRealization
      (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset)) = B.carrier K := by
  let g := simplicialRealization
    (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset)
  have hg : ∀ x, (g x).1 = x.1 := simplicialSubcomplexRealization_value K B
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change (g y).1.weights.support ∈ B.complex.simplices
    rw [hg]
    exact y.2
  · intro hx
    refine ⟨⟨x.1,hx⟩, ?_⟩
    apply Subtype.ext
    exact hg _

/-- Intrinsic weak realization and actual subcomplex carrier are canonically
homeomorphic for every abstract simplicial subcomplex, including infinite ones. -/
def simplicialSubcomplexRealizationHomeomorph {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K) :
    B.complex.Realization ≃ₜ B.carrier K :=
  (simplicialSubcomplexRealization_isClosedEmbedding K B).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (simplicialSubcomplexRealization_range K B))


end


section
open P202Specs.OrientedSimplicialAlgebra
def simplicialMapHomotopyLinear {V W : Type w} {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) (n : ℕ) :
    P202Specs.OrientedSimplicialAlgebra.Chains K A n →ₗ[R]
      P202Specs.SingularChains.Chains A (TopCat.of L.Realization) (n+1) :=
  (totalTupleEvaluation R A L (n+1)).comp
    ((tupleHomotopy R A (tupleNormalize R A W) (n+1)).comp (rawTupleImage R A f n))

theorem rawTupleImage_selected {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (B : Simplicial.Subcomplex K) (E : Simplicial.Subcomplex L)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (hf : ∀ s ∈ B.complex.simplices, s.image f.vertices ∈ E.complex.simplices)
    (n : ℕ) (c : P202Specs.OrientedSimplicialAlgebra.Chains K A n)
    (hc : c ∈ (Simplicial.selection R A K B).module n) :
    rawTupleImage R A f n c ∈
      Finsupp.supported A R {t | Finset.univ.image t ∈ E.complex.simplices} := by
  apply map_supported R A _ _ (rawTupleImage R A f n) ?_ c hc
  intro s hs a
  rw [rawTupleImage_single]
  apply Finsupp.single_mem_supported
  change Finset.univ.image (f.vertices ∘ s.1) ∈ E.complex.simplices
  simpa only [Finset.image_image] using hf _ hs

theorem simplicialMapHomotopyLinear_selected {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (B : Simplicial.Subcomplex K) (E : Simplicial.Subcomplex L)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (hf : ∀ s ∈ B.complex.simplices, s.image f.vertices ∈ E.complex.simplices)
    (n : ℕ) (c : P202Specs.OrientedSimplicialAlgebra.Chains K A n)
    (hc : c ∈ (Simplicial.selection R A K B).module n) :
    simplicialMapHomotopyLinear R A f n c ∈
      (singularSelection R A (TopCat.of L.Realization) (E.carrier L)).module (n+1) := by
  apply totalTupleEvaluation_preserves R A L E (n+1)
  apply tupleHomotopy_valid R A E.complex (tupleNormalize R A W)
    (tupleNormalize_preserves R A W) n
  exact rawTupleImage_selected R A K L B E f hf n c hc

def singularChainMapLinear {X Y : TopCat.{w}} (g : X ⟶ Y) (n : ℕ) :
    Chains A X n →ₗ[R] Chains A Y n := ((chainMap R A g).f n).hom

theorem simplicialMapHomotopyLinear_zero {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (g : TopCat.of K.Realization ⟶ TopCat.of L.Realization)
    (hg : ∀ x, (g x).val = x.val.map f.vertices)
    (c : P202Specs.OrientedSimplicialAlgebra.Chains K A 0) :
    singularTupleBoundary R A L 0 (simplicialMapHomotopyLinear R A f 0 c) =
      Simplicial.affineLinear L R A 0 (P202Specs.OrientedSimplicialAlgebra.pushforward R A f 0 c) -
        singularChainMapLinear R A g 0 (Simplicial.affineLinear K R A 0 c) := by
  have h := totalTupleEvaluation_homotopy_identity R A L (tupleNormalize R A W)
    (tupleNormalize_zero R A W) (tupleNormalize_boundary R A W)
    (tupleNormalize_preserves R A W) 0 (rawTupleImage R A f 0 c)
    (rawTupleImage_valid R A f 0 c)
  have hn := LinearMap.congr_fun (totalTupleEvaluation_normalize_rawImage R A K L f 0) c
  have hr := LinearMap.congr_fun (totalTupleEvaluation_rawImage R A K L f g hg 0) c
  simp only [LinearMap.comp_apply] at hn hr
  have hz : tupleHomotopy R A (tupleNormalize R A W) 0 = 0 := rfl
  rw [hz, LinearMap.zero_apply, map_zero, add_zero] at h
  rw [hn, hr] at h
  exact h

theorem simplicialMapHomotopyLinear_succ {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (g : TopCat.of K.Realization ⟶ TopCat.of L.Realization)
    (hg : ∀ x, (g x).val = x.val.map f.vertices)
    (n : ℕ) (c : P202Specs.OrientedSimplicialAlgebra.Chains K A (n+1)) :
    singularTupleBoundary R A L (n+1) (simplicialMapHomotopyLinear R A f (n+1) c) +
      simplicialMapHomotopyLinear R A f n (P202Specs.OrientedSimplicialAlgebra.boundary R A n c) =
      Simplicial.affineLinear L R A (n+1)
          (P202Specs.OrientedSimplicialAlgebra.pushforward R A f (n+1) c) -
        singularChainMapLinear R A g (n+1) (Simplicial.affineLinear K R A (n+1) c) := by
  have h := totalTupleEvaluation_homotopy_identity R A L (tupleNormalize R A W)
    (tupleNormalize_zero R A W) (tupleNormalize_boundary R A W)
    (tupleNormalize_preserves R A W) (n+1) (rawTupleImage R A f (n+1) c)
    (rawTupleImage_valid R A f (n+1) c)
  have hn := LinearMap.congr_fun (totalTupleEvaluation_normalize_rawImage R A K L f (n+1)) c
  have hr := LinearMap.congr_fun (totalTupleEvaluation_rawImage R A K L f g hg (n+1)) c
  have hb := LinearMap.congr_fun (rawTupleImage_boundary R A f n) c
  simp only [LinearMap.comp_apply] at hn hr hb
  rw [hn, hr, hb] at h
  exact h


def simplicialMapHomotopyComponent {V W : Type w}
    {K : AbstractSimplicialComplex V} {L : AbstractSimplicialComplex W}
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L) (n : ℕ) :
    (P202Specs.OrientedSimplicialAlgebra.complex R A (K := K)).X n ⟶
      (P202Specs.SingularChains.complex R A (TopCat.of L.Realization)).X (n+1) :=
  ModuleCat.ofHom (simplicialMapHomotopyLinear R A f n)

def simplicialNaturality_homotopy {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (B : Simplicial.Subcomplex K) (E : Simplicial.Subcomplex L)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (g : TopCat.of K.Realization ⟶ TopCat.of L.Realization)
    (hg : ∀ x, (g x).val = x.val.map f.vertices)
    (T : P202Specs.OrientedSimplicialAlgebra.complex R A (K := K) ⟶
      P202Specs.OrientedSimplicialAlgebra.complex R A (K := L))
    (hT : ∀ n, (T.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward R A f n)
    (F : SimplicialComparisonData R A K B) (G : SimplicialComparisonData R A L E) :
    Homotopy (T ≫ G.absolute) (F.absolute ≫ chainMap R A g) := by
  apply homotopyOfDegreewise _ _ (simplicialMapHomotopyComponent R A f)
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change (G.absolute.f 0).hom ((T.f 0).hom c) =
      singularTupleBoundary R A L 0 (simplicialMapHomotopyLinear R A f 0 c) +
        singularChainMapLinear R A g 0 ((F.absolute.f 0).hom c)
    rw [G.absolute_formula, F.absolute_formula, hT]
    exact sub_eq_iff_eq_add.mp (simplicialMapHomotopyLinear_zero R A K L f g hg c).symm
  · intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    change (G.absolute.f (n+1)).hom ((T.f (n+1)).hom c) =
      simplicialMapHomotopyLinear R A f n
          (((P202Specs.OrientedSimplicialAlgebra.complex R A (K := K)).d (n+1) n).hom c) +
        singularTupleBoundary R A L (n+1) (simplicialMapHomotopyLinear R A f (n+1) c) +
        singularChainMapLinear R A g (n+1) ((F.absolute.f (n+1)).hom c)
    rw [G.absolute_formula, F.absolute_formula, hT,
      P202.SimplicialChains.Oriented.boundary_eq]
    have h := sub_eq_iff_eq_add.mp (simplicialMapHomotopyLinear_succ R A K L f g hg n c).symm
    calc
      _ = _ := h
      _ = _ := by abel


end


section
variable {R : Type u} [CommRing R]
def quotientHomotopyOfDegreewise {C D : ChainComplex (ModuleCat.{v} R) ℕ}
    (S : ChainSelection R C) (T : ChainSelection R D)
    (f g : C ⟶ D)
    (hf : ∀ n x, x ∈ S.module n → (f.f n).hom x ∈ T.module n)
    (hg : ∀ n x, x ∈ S.module n → (g.f n).hom x ∈ T.module n)
    (H : ∀ n, C.X n ⟶ D.X (n+1))
    (hH : ∀ n x, x ∈ S.module n → (H n).hom x ∈ T.module (n+1))
    (hzero : f.f 0 = H 0 ≫ D.d 1 0 + g.f 0)
    (hsucc : ∀ n, f.f (n+1) = C.d (n+1) n ≫ H n +
      H (n+1) ≫ D.d (n+2) (n+1) + g.f (n+1)) :
    Homotopy (S.quotientMap T f hf) (S.quotientMap T g hg) :=
  homotopyOfDegreewise _ _ (fun n => ModuleCat.ofHom
    ((S.module n).mapQ (T.module (n+1)) (H n).hom (hH n)))
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := (S.module 0).mkQ_surjective x
      change (T.module 0).mkQ ((f.f 0).hom x) =
        (T.module 0).mkQ ((D.d 1 0).hom ((H 0).hom x)) + (T.module 0).mkQ ((g.f 0).hom x)
      rw [← map_add]
      apply congrArg (T.module 0).mkQ
      exact congrArg (fun k : C.X 0 ⟶ D.X 0 => k.hom x) hzero)
    (by
      intro n
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨x, rfl⟩ := (S.module (n+1)).mkQ_surjective x
      have hh := congrArg (T.module (n+1)).mkQ
        (congrArg (fun k : C.X (n+1) ⟶ D.X (n+1) => k.hom x) (hsucc n))
      have hd (k : ℕ) : T.quotient.d (k+1) k = ModuleCat.ofHom (T.quotientBoundary k) := by
        simp only [ChainSelection.quotient, ChainComplex.of_d]
      erw [hd (n+1)]
      simpa [ChainSelection.quotient, ChainSelection.quotientBoundary, ChainSelection.quotientMap,
        ModuleCat.hom_add, ModuleCat.hom_comp] using hh)


def quotientHomotopy {C D : ChainComplex (ModuleCat.{v} R) ℕ}
    (S : ChainSelection R C) (T : ChainSelection R D)
    (f g : C ⟶ D)
    (hf : ∀ n x, x ∈ S.module n → (f.f n).hom x ∈ T.module n)
    (hg : ∀ n x, x ∈ S.module n → (g.f n).hom x ∈ T.module n)
    (h : Homotopy f g)
    (hH : ∀ n x, x ∈ S.module n → (h.hom n (n+1)).hom x ∈ T.module (n+1)) :
    Homotopy (S.quotientMap T f hf) (S.quotientMap T g hg) :=
  quotientHomotopyOfDegreewise S T f g hf hg (fun n => h.hom n (n+1)) hH
    (by
      have hz := h.comm 0
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at hz
      exact hz)
    (by
      intro n
      have hs := h.comm (n+1)
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at hs
      exact hs)


end


section
open P202Specs.OrientedSimplicialAlgebra
def orderComparisonHomotopyComponent {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) : (complex R A (K := K)).X n ⟶
      (P202Specs.SingularChains.complex R A (TopCat.of K.Realization)).X (n+1) :=
  ModuleCat.ofHom (orderComparisonHomotopyLinear R A K o n)

theorem orderComparison_degree_zero {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) (F : SimplicialComparisonData R A K B) :
    ((orderTransitionChainMap R A K o) ≫ (orderedAffineChainMap R A K o)).f 0 =
      orderComparisonHomotopyComponent R A K o 0 ≫
        (P202Specs.SingularChains.complex R A (TopCat.of K.Realization)).d 1 0 + F.absolute.f 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rw [ModuleCat.hom_add, LinearMap.add_apply, F.absolute_formula]
  change orderedAffineLinear R A K o 0 (orderTransitionLinear R A K o 0 c) =
    singularTupleBoundary R A K 0 (orderComparisonHomotopyLinear R A K o 0 c) +
      Simplicial.affineLinear K R A 0 c
  exact (sub_eq_iff_eq_add.mp (orderComparisonHomotopyLinear_zero R A K o c).symm)

theorem orderComparison_degree_succ {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) (F : SimplicialComparisonData R A K B)
    (n : ℕ) :
    ((orderTransitionChainMap R A K o) ≫ (orderedAffineChainMap R A K o)).f (n+1) =
      ((complex R A (K := K)).d (n+1) n ≫ orderComparisonHomotopyComponent R A K o n) +
      (orderComparisonHomotopyComponent R A K o (n+1) ≫
        (P202Specs.SingularChains.complex R A (TopCat.of K.Realization)).d (n+2) (n+1)) + F.absolute.f (n+1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rw [ModuleCat.hom_add, LinearMap.add_apply, F.absolute_formula]
  change orderedAffineLinear R A K o (n+1) (orderTransitionLinear R A K o (n+1) c) =
    orderComparisonHomotopyLinear R A K o n (((complex R A (K := K)).d (n+1) n).hom c) +
      singularTupleBoundary R A K (n+1) (orderComparisonHomotopyLinear R A K o (n+1) c) +
        Simplicial.affineLinear K R A (n+1) c
  rw [P202.OrientedSimplicialAlgebra.boundary_eq]
  have h := sub_eq_iff_eq_add.mp (orderComparisonHomotopyLinear_succ R A K o n c).symm
  rw [add_comm (singularTupleBoundary R A K (n+1) _)] at h
  exact h

def orderComparisonHomotopy {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) (F : SimplicialComparisonData R A K B) :
    Homotopy ((orderTransitionChainMap R A K o) ≫ (orderedAffineChainMap R A K o)) F.absolute :=
  homotopyOfDegreewise _ _ (fun n => orderComparisonHomotopyComponent R A K o n)
    (orderComparison_degree_zero R A K B o F) (orderComparison_degree_succ R A K B o F)

theorem orderComparison_homology {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) (F : SimplicialComparisonData R A K B)
    (q : ℕ) :
    homologyMap (orderTransitionChainMap R A K o) q ≫ homologyMap (orderedAffineChainMap R A K o) q =
      homologyMap F.absolute q := by
  rw [← homologyMap_comp]
  exact (orderComparisonHomotopy R A K B o F).homologyMap_eq q


end


section
open P202Specs.OrientedSimplicialAlgebra
def orderComparisonRelativeHomotopy {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) (F : SimplicialComparisonData R A K B) :
    Homotopy ((orderTransitionRelativeChainMap R A K B o) ≫ (orderedRelativeAffineChainMap R A K B o))
      F.relative := by
  let S := Simplicial.selection R A K B
  let Q := singularSelection R A (TopCat.of K.Realization) (B.carrier K)
  let f := orderTransitionChainMap R A K o ≫ orderedAffineChainMap R A K o
  have hf : ∀ n x, x ∈ S.module n → (f.f n).hom x ∈ Q.module n := by
    intro n x hx
    change orderedAffineLinear R A K o n (orderTransitionLinear R A K o n x) ∈ Q.module n
    exact orderedAffine_preserves R A K B o n _ (orderTransition_selected R A K B o n x hx)
  have hg : ∀ n x, x ∈ S.module n → (F.absolute.f n).hom x ∈ Q.module n := by
    intro n x hx
    rw [F.absolute_formula]
    exact P202.RelativeParametrizations.Simplicial.affine_preserves R A K B n x hx
  have hH : ∀ n x, x ∈ S.module n →
      ((orderComparisonHomotopy R A K B o F).hom n (n+1)).hom x ∈ Q.module (n+1) := by
    intro n x hx
    have hcomponent : ((orderComparisonHomotopy R A K B o F).hom n (n+1)).hom =
        orderComparisonHomotopyLinear R A K o n := by
      simp [orderComparisonHomotopy, homotopyOfDegreewise, orderComparisonHomotopyComponent]
    rw [hcomponent]
    dsimp only [Q]
    exact orderComparisonHomotopyLinear_selected R A K B o n x hx
  have h := quotientHomotopy S Q f F.absolute hf hg (orderComparisonHomotopy R A K B o F) hH
  have hfrel : S.quotientMap Q f hf =
      orderTransitionRelativeChainMap R A K B o ≫ orderedRelativeAffineChainMap R A K B o := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (S.module n).mkQ_surjective x
    rfl
  have hgrel : S.quotientMap Q F.absolute hg = F.relative := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := (S.module n).mkQ_surjective x
    erw [F.relative_formula]
    change (Q.module n).mkQ ((F.absolute.f n).hom x) = _
    rw [F.absolute_formula]
    rfl
  rw [hfrel, hgrel] at h
  exact h

theorem orderComparison_relative_homology {V : Type w} (K : AbstractSimplicialComplex V)
    (B : Simplicial.Subcomplex K) (o : LinearOrder V) (F : SimplicialComparisonData R A K B)
    (q : ℕ) :
    homologyMap (orderTransitionRelativeChainMap R A K B o) q ≫
        homologyMap (orderedRelativeAffineChainMap R A K B o) q = homologyMap F.relative q := by
  rw [← homologyMap_comp]
  exact (orderComparisonRelativeHomotopy R A K B o F).homologyMap_eq q


end


section
open P202Specs.OrientedSimplicialAlgebra
theorem orderIndependence_of_comparison
    (hcomparison : P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w}) :
    P202Specs.SimplicialComparison.orderIndependence_type.{u,v,w} := by
  intro R _ A _ _ V K B o
  obtain ⟨F, hF, hFrel⟩ := hcomparison R A K B
  refine ⟨orderedAffineChainMap R A K o, orderedRelativeAffineChainMap R A K B o,
    orderTransitionChainMap R A K o, orderTransitionRelativeChainMap R A K B o,
    (fun _ => rfl), (fun _ _ => rfl), (fun _ => rfl), (fun _ _ => rfl), ?_, ?_⟩
  · intro q
    have hT : IsIso (homologyMap (orderTransitionChainMap R A K o) q) := by
      change IsIso (homologyMap (orderTransitionIso R A K o).hom q)
      infer_instance
    have hTrel : IsIso (homologyMap (orderTransitionRelativeChainMap R A K B o) q) := by
      change IsIso (homologyMap (orderTransitionRelativeIso R A K B o).hom q)
      infer_instance
    letI := hT
    letI := hTrel
    have hG : IsIso (homologyMap (orderedAffineChainMap R A K o) q) := by
      haveI : IsIso (homologyMap (orderTransitionChainMap R A K o) q ≫
          homologyMap (orderedAffineChainMap R A K o) q) := by
        rw [orderComparison_homology R A K B o F q]
        exact hF q
      exact IsIso.of_isIso_comp_left (homologyMap (orderTransitionChainMap R A K o) q)
        (homologyMap (orderedAffineChainMap R A K o) q)
    have hGrel : IsIso (homologyMap (orderedRelativeAffineChainMap R A K B o) q) := by
      haveI : IsIso (homologyMap (orderTransitionRelativeChainMap R A K B o) q ≫
          homologyMap (orderedRelativeAffineChainMap R A K B o) q) := by
        rw [orderComparison_relative_homology R A K B o F q]
        exact hFrel q
      exact IsIso.of_isIso_comp_left (homologyMap (orderTransitionRelativeChainMap R A K B o) q)
        (homologyMap (orderedRelativeAffineChainMap R A K B o) q)
    exact ⟨hG, hGrel, hT, hTrel⟩
  · intro G q
    exact ⟨orderComparison_homology R A K B o G q,
      orderComparison_relative_homology R A K B o G q⟩


end


section
variable {R : Type u} [CommRing R]
def selectionLift {C D : ChainComplex (ModuleCat.{v} R) ℕ}
    (S : ChainSelection R D) (f : C ⟶ D)
    (hf : ∀ n x, (f.f n).hom x ∈ S.module n) : C ⟶ S.subcomplex :=
  ChainComplex.ofHom (fun n => ModuleCat.ofHom
    ((f.f n).hom.codRestrict (S.module n) (hf n))) (by
    intro n
    simp only [ChainSelection.subcomplex, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun g => g.hom x) (f.comm (n+1) n))

/-- An injective chain map with exactly the selected image becomes an
isomorphism onto that subcomplex. -/
theorem selectionLift_isIso {C D : ChainComplex (ModuleCat.{v} R) ℕ}
    (S : ChainSelection R D) (f : C ⟶ D)
    (hf : ∀ n x, (f.f n).hom x ∈ S.module n)
    (hinj : ∀ n, Function.Injective (f.f n).hom)
    (hrange : ∀ n, (f.f n).hom.range = S.module n) :
    IsIso (selectionLift S f hf) := by
  haveI : ∀ n, IsIso ((selectionLift S f hf).f n) := by
    intro n
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    constructor
    · intro x y h
      apply hinj n
      exact congrArg Subtype.val h
    · intro x
      have hx : x.1 ∈ (f.f n).hom.range := (hrange n).symm ▸ x.2
      obtain ⟨y,hy⟩ := hx
      exact ⟨y,Subtype.ext hy⟩
  exact HomologicalComplex.Hom.isIso_of_components _

variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- The singular pushforward of a subcomplex realization has exactly the
supported-chain image, for arbitrary subcomplexes and arbitrary coefficients. -/
theorem simplicialSubcomplexSingular_range {V : Type w}
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K) (n : ℕ) :
    ((chainMap R A (simplicialRealization
      (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset))).f n).hom.range =
      (singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module n := by
  let e : TopCat.of B.complex.Realization ≅ TopCat.of (B.carrier K) :=
    TopCat.isoOfHomeo (simplicialSubcomplexRealizationHomeomorph K B)
  let i := subspaceInclusion (TopCat.of K.Realization) (B.carrier K)
  let g := simplicialRealization
    (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset)
  have hfac : e.hom ≫ i = g := rfl
  have hmap : ((chainMap R A g).f n).hom =
      (((chainMap R A i).f n).hom).comp (((chainMap R A e.hom).f n).hom) := by
    exact (congrArg (fun f => (f.f n).hom) (by
      rw [← P202.SingularChains.chainMap_comp, hfac] :
        chainMap R A e.hom ≫ chainMap R A i = chainMap R A g)).symm
  have hepi : Function.Surjective (((chainMap R A e.hom).f n).hom) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  change ((chainMap R A g).f n).hom.range = _
  rw [hmap, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hepi)]
  exact P202.SimplicialChains.singularSelection_range R A _ _ n


/-- Absolute canonical comparisons on all subcomplex realizations imply
comparison for every actual relative quotient. The proof identifies each
selected-chain complex with the intrinsic subcomplex chain model. -/
theorem simplicialRelativeComparison_of_absolute {V : Type w}
    (habsolute : ∀ (L : AbstractSimplicialComplex V) (C : Simplicial.Subcomplex L)
      (G : SimplicialComparisonData R A L C) (q : ℕ), IsIso (homologyMap G.absolute q))
    (K : AbstractSimplicialComplex V) (B : Simplicial.Subcomplex K)
    (F : SimplicialComparisonData R A K B) (q : ℕ) :
    IsIso (homologyMap F.relative q) := by
  let S := Simplicial.selection R A K B
  let T := singularSelection R A (TopCat.of K.Realization) (B.carrier K)
  have hpres : ∀ n x, x ∈ S.module n → (F.absolute.f n).hom x ∈ T.module n := by
    intro n x hx
    rw [F.absolute_formula]
    exact P202.SimplicialChains.Simplicial.affine_preserves R A K B n x hx
  obtain ⟨G⟩ := simplicialComparisonData_nonempty R A B.complex (Simplicial.Subcomplex.empty _)
  obtain ⟨I,hI,hIinj,hIrange⟩ := P202.SimplicialChains.Simplicial.inclusion_chainMap R A K B
  let g := simplicialRealization
    (P202Specs.OrientedSimplicialAlgebra.SimplicialMap.inclusion B.subset)
  let J := chainMap R A g
  have hIS : ∀ n x, (I.f n).hom x ∈ S.module n := by
    intro n x
    rw [← hIrange n]
    exact ⟨x,rfl⟩
  have hJrange : ∀ n, (J.f n).hom.range = T.module n :=
    simplicialSubcomplexSingular_range R A K B
  have hJT : ∀ n x, (J.f n).hom x ∈ T.module n := by
    intro n x
    rw [← hJrange n]
    exact ⟨x,rfl⟩
  have hJinj : ∀ n, Function.Injective (J.f n).hom :=
    singularMap_injective R A g (simplicialSubcomplexRealization_isClosedEmbedding K B).injective
  let L := selectionLift S I hIS
  let M := selectionLift T J hJT
  haveI hL : IsIso L := selectionLift_isIso S I hIS hIinj hIrange
  haveI hM : IsIso M := selectionLift_isIso T J hJT hJinj hJrange
  have hsquare : L ≫ selectionSubcomplexMap S T F.absolute hpres = G.absolute ≫ M := by
    have hs := simplicialInclusion_absolute_square R A B.complex K B.subset
      (Simplicial.Subcomplex.empty _) B I hI G F
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => (f.f n).hom x) hs
  have hsub : ∀ n, IsIso (homologyMap (selectionSubcomplexMap S T F.absolute hpres) n) := by
    intro n
    haveI := habsolute B.complex (Simplicial.Subcomplex.empty _) G n
    have heq : homologyMap (selectionSubcomplexMap S T F.absolute hpres) n =
        inv (homologyMap L n) ≫ homologyMap G.absolute n ≫ homologyMap M n := by
      apply (cancel_epi (homologyMap L n)).mp
      simpa only [homologyMap_comp, Category.assoc, IsIso.hom_inv_id_assoc]
        using congrArg (fun f => homologyMap f n) hsquare
    rw [heq]
    infer_instance
  have hrel : S.quotientMap T F.absolute hpres = F.relative := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x,rfl⟩ := (S.module n).mkQ_surjective x
    change (T.module n).mkQ ((F.absolute.f n).hom x) =
      (F.relative.f n).hom ((S.module n).mkQ x)
    rw [F.relative_formula,F.absolute_formula]
    rfl
  rw [← hrel]
  exact selectionQuotientComparison_isIso S T F.absolute hpres hsub (habsolute K B F) q


end


section
theorem quotientMap_eq_of_formula {C D : ChainComplex (ModuleCat.{v} R) ℕ}
    (S : ChainSelection R C) (T : ChainSelection R D) (f : C ⟶ D)
    (hf : ∀ n x, x ∈ S.module n → (f.f n).hom x ∈ T.module n)
    (g : S.quotient ⟶ T.quotient)
    (hg : ∀ n x, (g.f n).hom ((S.module n).mkQ x) =
      (T.module n).mkQ ((f.f n).hom x)) : g = S.quotientMap T f hf := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (S.module n).mkQ_surjective x
  exact hg n x

variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

theorem simplicialNaturality_relative_square {V W : Type w}
    (K : AbstractSimplicialComplex V) (L : AbstractSimplicialComplex W)
    (B : Simplicial.Subcomplex K) (E : Simplicial.Subcomplex L)
    (f : P202Specs.OrientedSimplicialAlgebra.SimplicialMap (K := K) L)
    (hf : ∀ s ∈ B.complex.simplices, s.image f.vertices ∈ E.complex.simplices)
    (g : TopCat.of K.Realization ⟶ TopCat.of L.Realization)
    (hg : ∀ x, (g x).val = x.val.map f.vertices)
    (hgpair : ∀ x ∈ B.carrier K, g x ∈ E.carrier L)
    (T : P202Specs.OrientedSimplicialAlgebra.complex R A (K := K) ⟶
      P202Specs.OrientedSimplicialAlgebra.complex R A (K := L))
    (Trel : Simplicial.relativeComplex R A K B ⟶ Simplicial.relativeComplex R A L E)
    (grel : singularRelativeComplex R A (TopCat.of K.Realization) (B.carrier K) ⟶
      singularRelativeComplex R A (TopCat.of L.Realization) (E.carrier L))
    (hT : ∀ n, (T.f n).hom = P202Specs.OrientedSimplicialAlgebra.pushforward R A f n)
    (hTrel : ∀ n x, (Trel.f n).hom (((Simplicial.selection R A K B).module n).mkQ x) =
      ((Simplicial.selection R A L E).module n).mkQ
        (P202Specs.OrientedSimplicialAlgebra.pushforward R A f n x))
    (hgrel : ∀ n x, (grel.f n).hom
        (((singularSelection R A (TopCat.of K.Realization) (B.carrier K)).module n).mkQ x) =
      ((singularSelection R A (TopCat.of L.Realization) (E.carrier L)).module n).mkQ
        (((chainMap R A g).f n).hom x))
    (F : SimplicialComparisonData R A K B) (G : SimplicialComparisonData R A L E)
    (q : ℕ) :
    homologyMap Trel q ≫ homologyMap G.relative q =
      homologyMap F.relative q ≫ homologyMap grel q := by
  let S := Simplicial.selection R A K B
  let U := singularSelection R A (TopCat.of L.Realization) (E.carrier L)
  let left := T ≫ G.absolute
  let right := F.absolute ≫ chainMap R A g
  have hleft : ∀ n x, x ∈ S.module n → (left.f n).hom x ∈ U.module n := by
    intro n x hx
    change (G.absolute.f n).hom ((T.f n).hom x) ∈ U.module n
    rw [G.absolute_formula, hT]
    exact P202.SimplicialChains.Simplicial.affine_preserves R A L E n _
      (P202.SimplicialChains.Simplicial.pushforward_preserves R A K L B E f hf n x hx)
  have hright : ∀ n x, x ∈ S.module n → (right.f n).hom x ∈ U.module n := by
    intro n x hx
    change ((chainMap R A g).f n).hom ((F.absolute.f n).hom x) ∈ U.module n
    rw [F.absolute_formula]
    apply singularMap_preserves R A _ _ g hgpair
    exact P202.SimplicialChains.Simplicial.affine_preserves R A K B n x hx
  let HA := simplicialNaturality_homotopy R A K L B E f g hg T hT F G
  have hH : ∀ n x, x ∈ S.module n → (HA.hom n (n+1)).hom x ∈ U.module (n+1) := by
    intro n x hx
    simp only [HA, U, simplicialNaturality_homotopy, homotopyOfDegreewise, dite_true,
      eqToHom_refl, Category.comp_id, simplicialMapHomotopyComponent, ModuleCat.hom_ofHom]
    change simplicialMapHomotopyLinear R A f n x ∈
      (singularSelection R A (TopCat.of L.Realization) (E.carrier L)).module (n+1)
    exact simplicialMapHomotopyLinear_selected R A K L B E f hf n x hx
  let HQ := quotientHomotopy S U left right hleft hright HA hH
  have hl : Trel ≫ G.relative = S.quotientMap U left hleft := by
    apply quotientMap_eq_of_formula R S U left hleft
    intro n x
    change (G.relative.f n).hom ((Trel.f n).hom _) =
      (U.module n).mkQ ((G.absolute.f n).hom ((T.f n).hom x))
    rw [hTrel, G.relative_formula, G.absolute_formula, hT]
    rfl
  have hr : F.relative ≫ grel = S.quotientMap U right hright := by
    apply quotientMap_eq_of_formula R S U right hright
    intro n x
    change (grel.f n).hom ((F.relative.f n).hom _) =
      (U.module n).mkQ (((chainMap R A g).f n).hom ((F.absolute.f n).hom x))
    rw [F.relative_formula, hgrel, F.absolute_formula]
    rfl
  rw [← homologyMap_comp, ← homologyMap_comp, hl, hr]
  exact HQ.homologyMap_eq q


theorem simplicialNaturality_core : P202Specs.SimplicialComparison.simplicialNaturality_type.{u,v,w} := by
  intro R _ A _ _ V W K L B E f hf
  obtain ⟨T,Trel,grel,hT,hTrel,hgrel⟩ := simplicialNaturality_maps R A K L B E f hf
  refine ⟨simplicialRealization f, simplicialRealization_value f,
    T,Trel,grel,hT,hTrel,hgrel,?_⟩
  intro F G q
  constructor
  · simpa only [homologyMap_comp] using
      (simplicialNaturality_homotopy R A K L B E f (simplicialRealization f)
        (simplicialRealization_value f) T hT F G).homologyMap_eq q
  · exact simplicialNaturality_relative_square R A K L B E f hf (simplicialRealization f)
      (simplicialRealization_value f) (simplicialRealization_carrier B E f hf)
      T Trel grel hT hTrel hgrel F G q

/-- The precise ordered conditional premises are retained; naturality itself is
already obtained from the affine cone homotopy and needs no disk computation. -/
theorem simplicialNaturality_conditional
    (_hcontractible : P202Specs.SpheresDisks.contractible_type.{u,v,w})
    (_hdisk : P202Specs.SpheresDisks.diskHomology_type.{u,v})
    (_hendpoint : P202Specs.SpheresDisks.endpointDifference_type.{u,v})
    (_hconnecting : P202Specs.SpheresDisks.simplexConnecting_type.{u,v})
    (_hgenerator : P202Specs.SpheresDisks.simplexGenerator_type.{u,v})
    (_hvanishing : P202Specs.SpheresDisks.simplexVanishing_type.{u,v})
    (_hsphere : P202Specs.SpheresDisks.sphereHomology_type.{u,v}) :
    P202Specs.SimplicialComparison.simplicialNaturality_type.{u,v,w} :=
  simplicialNaturality_core


end

/-- Naturality of the canonical simplicial comparison for every simplicial map
of subcomplex pairs, including vertex collapse. -/
theorem simplicialNaturality :
    P202Specs.SimplicialComparison.simplicialNaturality_type.{u,v,w} :=
  simplicialNaturality_core

/-- Naturality of the canonical ordered Δ-comparison for all subcomplex pairs. -/
theorem deltaNaturality :
    P202Specs.SimplicialComparison.deltaNaturality_type.{u,v,w} :=
  deltaNaturality_core


section
variable {R : Type u} [CommRing R]
variable {C D : ChainComplex (ModuleCat.{v} R) ℕ}
/-- The middle comparison of two short exact sequences is an isomorphism
when the subcomplex and quotient comparisons are isomorphisms. -/
theorem selectionAbsoluteComparison_isIso (S : ChainSelection R C) (T : ChainSelection R D)
    (f : C ⟶ D) (hf : ∀ n x, x ∈ S.module n → (f.f n).hom x ∈ T.module n)
    (hsub : ∀ q, IsIso (homologyMap (selectionSubcomplexMap S T f hf) q))
    (hquot : ∀ q, IsIso (homologyMap (S.quotientMap T f hf) q)) (q : ℕ) :
    IsIso (homologyMap f q) := by
  let φ := selectionSequenceMap S T f hf
  let hS := selectionSequence_shortExact S
  let hT := selectionSequence_shortExact T
  have hmono : Mono (homologyMap f q) := by
    apply CategoryTheory.Abelian.mono_of_epi_of_mono_of_mono
      ((CategoryTheory.ComposableArrows.δ₀Functor ⋙ CategoryTheory.ComposableArrows.δ₀Functor).map
        (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS hT (q+1) q (by simp)))
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS (q+1) q (by simp)).δ₀.δ₀
    · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hT (q+1) q (by simp)).δ₀.δ₀
    · change Epi (homologyMap (S.quotientMap T f hf) (q+1))
      haveI := hquot (q+1)
      infer_instance
    · change Mono (homologyMap (selectionSubcomplexMap S T f hf) q)
      haveI := hsub q
      infer_instance
    · change Mono (homologyMap (S.quotientMap T f hf) q)
      haveI := hquot q
      infer_instance
  have hepi : Epi (homologyMap f q) := by
    cases q with
    | zero =>
      apply CategoryTheory.Abelian.epi_of_epi_of_epi_of_epi
        (HomologicalComplex.HomologySequence.mapComposableArrows₂ φ 0)
      · exact HomologicalComplex.HomologySequence.composableArrows₂_exact hT 0
      · change Epi (homologyMap S.projection 0)
        haveI : Epi (S.projection.f 0) :=
          (ModuleCat.epi_iff_surjective _).mpr (S.module 0).mkQ_surjective
        exact HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.projection 0 (by simp)
      · change Epi (homologyMap (selectionSubcomplexMap S T f hf) 0)
        haveI := hsub 0
        infer_instance
      · change Epi (homologyMap (S.quotientMap T f hf) 0)
        haveI := hquot 0
        infer_instance
    | succ q =>
      apply CategoryTheory.Abelian.epi_of_epi_of_epi_of_mono
        ((CategoryTheory.ComposableArrows.δlastFunctor ⋙ CategoryTheory.ComposableArrows.δlastFunctor).map
          (HomologicalComplex.HomologySequence.mapComposableArrows₅ φ hS hT (q+1) q (by simp)))
      · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hS (q+1) q (by simp)).δlast.δlast
      · exact (HomologicalComplex.HomologySequence.composableArrows₅_exact hT (q+1) q (by simp)).δlast.δlast
      · change Epi (homologyMap (selectionSubcomplexMap S T f hf) (q+1))
        haveI := hsub (q+1)
        infer_instance
      · change Epi (homologyMap (S.quotientMap T f hf) (q+1))
        haveI := hquot (q+1)
        infer_instance
      · change Mono (homologyMap (selectionSubcomplexMap S T f hf) q)
        haveI := hsub q
        infer_instance
  exact CategoryTheory.isIso_of_mono_of_epi _
end

section
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- The canonical absolute affine comparison commutes with every ordered
Δ-map, in particular the inclusion of an actual subcomplex. -/
theorem deltaAbsolute_square {D E : DeltaComplex.{w}} (f : DeltaMap D E)
    (B : DeltaSubcomplex D) (C : DeltaSubcomplex E)
    (I : deltaComplex R A D ⟶ deltaComplex R A E)
    (hI : ∀ n, (I.f n).hom = deltaPushforward R A f n)
    (F : DeltaComparisonData R A D B) (G : DeltaComparisonData R A E C) :
    I ≫ G.absolute = F.absolute ≫ chainMap R A (deltaRealization f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  change ((G.absolute.f n).hom).comp (I.f n).hom =
    (((chainMap R A (deltaRealization f)).f n).hom).comp (F.absolute.f n).hom
  rw [G.absolute_formula, F.absolute_formula, hI]
  exact deltaAffine_natural R A f n

/-- The singular chains of the intrinsic Δ-subcomplex realization map onto
precisely the singular chains supported on its original ambient carrier. -/
theorem deltaSubcomplexSingular_range (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) (n : ℕ) :
    ((chainMap R A (deltaRealization B.inclusion)).f n).hom.range =
      (singularSelection R A (TopCat.of D.Realization) B.carrier).module n := by
  let e : TopCat.of B.asComplex.Realization ≅ TopCat.of B.carrier :=
    TopCat.isoOfHomeo (deltaSubcomplexRealizationHomeomorph D B)
  let i := subspaceInclusion (TopCat.of D.Realization) B.carrier
  let g := deltaRealization B.inclusion
  have hfac : e.hom ≫ i = g := rfl
  have hmap : ((chainMap R A g).f n).hom =
      (((chainMap R A i).f n).hom).comp (((chainMap R A e.hom).f n).hom) := by
    exact (congrArg (fun f => (f.f n).hom) (by
      rw [← P202.SingularChains.chainMap_comp, hfac] :
        chainMap R A e.hom ≫ chainMap R A i = chainMap R A g)).symm
  have hepi : Function.Surjective (((chainMap R A e.hom).f n).hom) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  change ((chainMap R A g).f n).hom.range = _
  rw [hmap, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hepi)]
  exact P202.SimplicialChains.singularSelection_range R A _ _ n

/-- The comparison on selected chains is transported from the intrinsic
Δ-subcomplex comparison through its canonical chain and realization inclusions. -/
theorem deltaSelectedComparison_isIso (D : DeltaComplex.{w}) (B : DeltaSubcomplex D)
    (F : DeltaComparisonData R A D B)
    (hpres : ∀ n x, x ∈ (deltaSelection R A D B).module n →
      (F.absolute.f n).hom x ∈
        (singularSelection R A (TopCat.of D.Realization) B.carrier).module n)
    (G : DeltaComparisonData R A B.asComplex (DeltaSubcomplex.empty _))
    (hG : ∀ q : ℕ, IsIso (homologyMap G.absolute q)) (q : ℕ) :
    IsIso (homologyMap (selectionSubcomplexMap (deltaSelection R A D B)
      (singularSelection R A (TopCat.of D.Realization) B.carrier) F.absolute hpres) q) := by
  let S := deltaSelection R A D B
  let T := singularSelection R A (TopCat.of D.Realization) B.carrier
  obtain ⟨I,hI,hIinj,hIrange⟩ := P202.SimplicialChains.deltaInclusion R A D B
  let g := deltaRealization B.inclusion
  let J := chainMap R A g
  have hIS : ∀ n x, (I.f n).hom x ∈ S.module n := by
    intro n x
    rw [← hIrange n]
    exact ⟨x,rfl⟩
  have hJrange : ∀ n, (J.f n).hom.range = T.module n :=
    deltaSubcomplexSingular_range R A D B
  have hJT : ∀ n x, (J.f n).hom x ∈ T.module n := by
    intro n x
    rw [← hJrange n]
    exact ⟨x,rfl⟩
  have hJinj : ∀ n, Function.Injective (J.f n).hom :=
    singularMap_injective R A g (deltaSubcomplexRealization_injective D B)
  let L := selectionLift S I hIS
  let M := selectionLift T J hJT
  haveI hL : IsIso L := selectionLift_isIso S I hIS hIinj hIrange
  haveI hM : IsIso M := selectionLift_isIso T J hJT hJinj hJrange
  have hsquare : L ≫ selectionSubcomplexMap S T F.absolute hpres = G.absolute ≫ M := by
    have hs := deltaAbsolute_square R A B.inclusion (DeltaSubcomplex.empty _) B I hI G F
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun f => (f.f n).hom x) hs
  haveI := hG q
  have heq : homologyMap (selectionSubcomplexMap S T F.absolute hpres) q =
      inv (homologyMap L q) ≫ homologyMap G.absolute q ≫ homologyMap M q := by
    apply (cancel_epi (homologyMap L q)).mp
    simpa only [homologyMap_comp, Category.assoc, IsIso.hom_inv_id_assoc]
      using congrArg (fun f => homologyMap f q) hsquare
  rw [heq]
  infer_instance

/-- Absolute comparison on all Δ-complexes implies comparison for every
subcomplex pair through the actual supported-chain quotients. -/
theorem deltaRelativeComparison_of_absolute
    (habsolute : ∀ (E : DeltaComplex.{w}) (C : DeltaSubcomplex E)
      (G : DeltaComparisonData R A E C) (q : ℕ), IsIso (homologyMap G.absolute q))
    (D : DeltaComplex.{w}) (B : DeltaSubcomplex D)
    (F : DeltaComparisonData R A D B) (q : ℕ) :
    IsIso (homologyMap F.relative q) := by
  let S := deltaSelection R A D B
  let T := singularSelection R A (TopCat.of D.Realization) B.carrier
  have hpres : ∀ n x, x ∈ S.module n → (F.absolute.f n).hom x ∈ T.module n := by
    intro n x hx
    rw [F.absolute_formula]
    exact P202.SimplicialChains.deltaAffine_preserves R A D B n x hx
  obtain ⟨G⟩ := deltaComparisonData_nonempty R A B.asComplex (DeltaSubcomplex.empty _)
  have hsub : ∀ n, IsIso (homologyMap (selectionSubcomplexMap S T F.absolute hpres) n) :=
    deltaSelectedComparison_isIso R A D B F hpres G
      (habsolute B.asComplex (DeltaSubcomplex.empty _) G)
  have hrel : S.quotientMap T F.absolute hpres = F.relative := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x,rfl⟩ := (S.module n).mkQ_surjective x
    change (T.module n).mkQ ((F.absolute.f n).hom x) =
      (F.relative.f n).hom ((S.module n).mkQ x)
    rw [F.relative_formula,F.absolute_formula]
    rfl
  rw [← hrel]
  exact selectionQuotientComparison_isIso S T F.absolute hpres hsub (habsolute D B F) q

/-- A selected singular chain lifts along the canonical inclusion of the
intrinsic weak realization of any Δ-subcomplex. -/
theorem singularDeltaSubcomplexLift (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) (q : ℕ) (c : Chains A (TopCat.of D.Realization) q)
    (hc : c ∈ (singularSelection R A (TopCat.of D.Realization) B.carrier).module q) :
    ∃ c' : Chains A (TopCat.of B.asComplex.Realization) q,
      ((chainMap R A (deltaRealization B.inclusion)).f q).hom c' = c := by
  rw [← deltaSubcomplexSingular_range R A D B q] at hc
  exact hc

/-- The union is formed on the original simplex labels, including repeated
faces and all their original face maps. -/
def deltaSubcomplexUnion (D : DeltaComplex.{w}) (B C : DeltaSubcomplex D) :
    DeltaSubcomplex D where
  selected n := B.selected n ∪ C.selected n
  face_closed a s hs := hs.elim
    (fun h => Or.inl (B.face_closed a s h)) (fun h => Or.inr (C.face_closed a s h))

/-- Finiteness of all selected labels gives finiteness of the intrinsic
Δ-complex, counting labels in all dimensions. -/
theorem deltaSubcomplex_finite (D : DeltaComplex.{w}) (B : DeltaSubcomplex D)
    (hB : (Set.ofPred fun d : (Σ n, D.Simplex n) => d.2 ∈ B.selected d.1).Finite) :
    Finite (Σ n, B.asComplex.Simplex n) := by
  let e : (Σ n, B.asComplex.Simplex n) →
      {d : (Σ n, D.Simplex n) // d.2 ∈ B.selected d.1} :=
    fun d => ⟨⟨d.1,d.2.1⟩,d.2.2⟩
  letI : Finite {d : (Σ n, D.Simplex n) // d.2 ∈ B.selected d.1} := hB.to_subtype
  apply Finite.of_injective e
  rintro ⟨n,s⟩ ⟨m,t⟩ h
  have h' : (⟨n,s.1⟩ : Σ k, D.Simplex k) = ⟨m,t.1⟩ := congrArg Subtype.val h
  have hnm : n = m := congrArg Sigma.fst h'
  subst m
  have hst : s = t := Subtype.ext (eq_of_heq (Sigma.mk.inj h').2)
  subst t
  rfl

/-- A Δ-chain and two singular chains lift simultaneously to one finite
face-closed Δ-subcomplex through the same canonical inclusion maps. -/
theorem deltaMixedFiniteLift (D : DeltaComplex.{w}) (q r : ℕ)
    (x : DeltaChains A D q) (y : Chains A (TopCat.of D.Realization) q)
    (z : Chains A (TopCat.of D.Realization) r) :
    ∃ (B : DeltaSubcomplex D) (_ : Finite (Σ n, B.asComplex.Simplex n))
      (x₀ : DeltaChains A B.asComplex q)
      (y₀ : Chains A (TopCat.of B.asComplex.Realization) q)
      (z₀ : Chains A (TopCat.of B.asComplex.Realization) r),
      deltaPushforward R A B.inclusion q x₀ = x ∧
      ((chainMap R A (deltaRealization B.inclusion)).f q).hom y₀ = y ∧
      ((chainMap R A (deltaRealization B.inclusion)).f r).hom z₀ = z := by
  classical
  let labels : Finset (Σ n, D.Simplex n) := x.support.image (Sigma.mk q)
  let C := deltaFiniteClosure D labels
  let degree : Bool → ℕ := fun b => cond b r q
  let cs : ∀ b, Chains A (TopCat.of D.Realization) (degree b) := fun b => Bool.rec y z b
  obtain ⟨B,hB,hc⟩ := deltaChainsFiniteSupport R A D degree cs
  let E := deltaSubcomplexUnion D C B
  have hEselected : (Set.ofPred fun d : (Σ n, D.Simplex n) => d.2 ∈ E.selected d.1).Finite :=
    (deltaFiniteClosure_finite D labels).union hB
  have hE : Finite (Σ n, E.asComplex.Simplex n) := deltaSubcomplex_finite D E hEselected
  have hx : x ∈ (deltaSelection R A D E).module q := by
    intro s hs
    apply Or.inl
    refine ⟨⟨q,s⟩,Finset.mem_image.mpr ⟨s,hs,rfl⟩,OrderEmbedding.id _,D.face_id q s⟩
  have hy : y ∈ (singularSelection R A (TopCat.of D.Realization) E.carrier).module q := by
    intro s hs t
    obtain ⟨n,a,ha,u,hu⟩ := hc false hs t
    exact ⟨n,a,Or.inr ha,u,hu⟩
  have hz : z ∈ (singularSelection R A (TopCat.of D.Realization) E.carrier).module r := by
    intro s hs t
    obtain ⟨n,a,ha,u,hu⟩ := hc true hs t
    exact ⟨n,a,Or.inr ha,u,hu⟩
  obtain ⟨I,hI,hIinj,hIrange⟩ := P202.SimplicialChains.deltaInclusion R A D E
  rw [← hIrange q] at hx
  obtain ⟨x₀,hx₀⟩ := hx
  obtain ⟨y₀,hy₀⟩ := singularDeltaSubcomplexLift R A D E q y hy
  obtain ⟨z₀,hz₀⟩ := singularDeltaSubcomplexLift R A D E r z hz
  rw [hI] at hx₀
  exact ⟨E,hE,x₀,y₀,z₀,hx₀,hy₀,hz₀⟩

/-- Canonical absolute comparison for finite Δ-complexes implies comparison
for every weak Δ-realization. A cycle and any proposed bounding chain are
restricted to the same finite face-closed subcomplex. -/
theorem deltaAbsoluteComparison_of_finite
    (hfinite : ∀ (E : DeltaComplex.{w}), Finite (Σ n, E.Simplex n) →
      ∀ (G : DeltaComparisonData R A E (DeltaSubcomplex.empty E)) (q : ℕ),
        IsIso (homologyMap G.absolute q))
    (D : DeltaComplex.{w}) (B : DeltaSubcomplex D)
    (F : DeltaComparisonData R A D B) (q : ℕ) :
    IsIso (homologyMap F.absolute q) := by
  let sc := shortComplexFunctor (ModuleCat.{max v w} R) (ComplexShape.down ℕ) q
  change IsIso (ShortComplex.homologyMap (sc.map F.absolute))
  apply homologyMap_isIso_of_local_factorizations R (sc.map F.absolute)
  intro x y z
  obtain ⟨C,hC,x₀,y₀,z₀,hx₀,hy₀,hz₀⟩ :=
    deltaMixedFiniteLift R A D q ((ComplexShape.down ℕ).prev q) x y z
  obtain ⟨G⟩ := deltaComparisonData_nonempty R A C.asComplex (DeltaSubcomplex.empty _)
  obtain ⟨I,hI,hIinj,hIrange⟩ := P202.SimplicialChains.deltaInclusion R A D C
  let g := deltaRealization C.inclusion
  let J := chainMap R A g
  have hJinj : ∀ r, Function.Injective (J.f r).hom :=
    singularMap_injective R A g (deltaSubcomplexRealization_injective D C)
  refine ⟨sc.obj (deltaComplex R A C.asComplex),
    sc.obj (P202Specs.SingularChains.complex R A (TopCat.of C.asComplex.Realization)),
    sc.map G.absolute, sc.map I, sc.map J, hfinite C.asComplex hC G q,
    hIinj _, hJinj _, hJinj _, ?_, x₀, y₀, z₀, ?_, hy₀, hz₀⟩
  · have hs := deltaAbsolute_square R A C.inclusion (DeltaSubcomplex.empty _) B I hI G F
    simpa only [Functor.map_comp] using congrArg sc.map hs
  · change (I.f q).hom x₀ = x
    rw [hI]
    exact hx₀


/-- The relative and intrinsic subcomplex comparisons together imply the
ambient absolute comparison, using the actual pair exact sequences. -/
theorem deltaAbsoluteComparison_of_subcomplex (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) (F : DeltaComparisonData R A D B)
    (G : DeltaComparisonData R A B.asComplex (DeltaSubcomplex.empty _))
    (hG : ∀ q : ℕ, IsIso (homologyMap G.absolute q))
    (hF : ∀ q : ℕ, IsIso (homologyMap F.relative q)) (q : ℕ) :
    IsIso (homologyMap F.absolute q) := by
  let S := deltaSelection R A D B
  let T := singularSelection R A (TopCat.of D.Realization) B.carrier
  have hpres : ∀ n x, x ∈ S.module n → (F.absolute.f n).hom x ∈ T.module n := by
    intro n x hx
    rw [F.absolute_formula]
    exact P202.SimplicialChains.deltaAffine_preserves R A D B n x hx
  have hquot : ∀ q, IsIso (homologyMap (S.quotientMap T F.absolute hpres) q) := by
    have heq : S.quotientMap T F.absolute hpres = F.relative := by
      symm
      apply quotientMap_eq_of_formula R S T F.absolute hpres
      intro n x
      change (F.relative.f n).hom
        (((deltaSelection R A D B).module n).mkQ x) =
        ((singularSelection R A (TopCat.of D.Realization) B.carrier).module n).mkQ
          ((F.absolute.f n).hom x)
      rw [F.relative_formula, F.absolute_formula]
      rfl
    rw [heq]
    exact hF
  exact selectionAbsoluteComparison_isIso S T F.absolute hpres
    (deltaSelectedComparison_isIso R A D B F hpres G hG) hquot q

/-- Empty Δ-complexes have the canonical comparison in every degree, with
ordinary homology in degree zero. -/
theorem deltaAbsoluteComparison_of_empty (D : DeltaComplex.{w})
    (hD : ∀ n, IsEmpty (D.Simplex n)) (B : DeltaSubcomplex D)
    (F : DeltaComparisonData R A D B) (q : ℕ) :
    IsIso (homologyMap F.absolute q) := by
  letI : IsEmpty D.Realization := ⟨fun x => by
    obtain ⟨⟨n,s,t⟩, rfl⟩ := Quotient.mk_surjective x
    exact (hD n).false s⟩
  letI : IsEmpty (D.Simplex q) := hD q
  letI : IsEmpty (P202Specs.SingularChains.Simplex (TopCat.of D.Realization) q) :=
    ⟨fun s => isEmptyElim (simplexEquiv (TopCat.of D.Realization) q s default)⟩
  have hs : IsZero ((deltaComplex R A D).X q) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun x y => ?_⟩
    change (x : DeltaChains A D q) = y
    apply Finsupp.ext
    intro s
    exact isEmptyElim s
  have ht : IsZero ((P202Specs.SingularChains.complex R A (TopCat.of D.Realization)).X q) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    refine ⟨fun x y => ?_⟩
    change (x : Chains A (TopCat.of D.Realization) q) = y
    apply Finsupp.ext
    intro s
    exact isEmptyElim s
  exact (HomologicalComplex.ExactAt.of_isZero hs).isZero_homology.isIso
    (HomologicalComplex.ExactAt.of_isZero ht).isZero_homology _

/-- Every finite set of Δ-simplex labels is bounded in dimension. -/
theorem deltaFinite_dimensionBound (D : DeltaComplex.{w})
    [Finite (Σ n, D.Simplex n)] :
    ∃ N : ℕ, ∀ n, N ≤ n → IsEmpty (D.Simplex n) := by
  classical
  letI := Fintype.ofFinite (Σ n, D.Simplex n)
  let N := (Finset.univ : Finset (Σ n, D.Simplex n)).sup Sigma.fst + 1
  refine ⟨N, fun n hn => ⟨fun s => ?_⟩⟩
  have hs : n ≤ (Finset.univ : Finset (Σ n, D.Simplex n)).sup Sigma.fst :=
    Finset.le_sup (f := Sigma.fst) (Finset.mem_univ (⟨n,s⟩ : Σ n, D.Simplex n))
  dsimp [N] at hn
  omega

/-- The finite-dimensional skeletal induction. The remaining hypothesis is
exactly the relative canonical comparison for a complex of dimension at most n
modulo its lower skeleton; no conclusion about this hypothesis is assumed. -/
theorem deltaAbsoluteComparison_of_skeletal
    (hskeletal : ∀ (E : DeltaComplex.{w}) (n : ℕ),
      (∀ k, n+1 ≤ k → IsEmpty (E.Simplex k)) →
      ∀ (H : DeltaComparisonData R A E (deltaSkeletonLT E n)) (q : ℕ),
        IsIso (homologyMap H.relative q))
    (N : ℕ) (D : DeltaComplex.{w})
    (hD : ∀ k, N ≤ k → IsEmpty (D.Simplex k))
    (B : DeltaSubcomplex D) (F : DeltaComparisonData R A D B) (q : ℕ) :
    IsIso (homologyMap F.absolute q) := by
  induction N generalizing D B q with
  | zero => exact deltaAbsoluteComparison_of_empty R A D (fun n => hD n (Nat.zero_le n)) B F q
  | succ N ih =>
    let C := deltaSkeletonLT D N
    obtain ⟨H⟩ := deltaComparisonData_nonempty R A D C
    obtain ⟨G⟩ := deltaComparisonData_nonempty R A C.asComplex (DeltaSubcomplex.empty _)
    have hC : ∀ k, N ≤ k → IsEmpty (C.asComplex.Simplex k) := by
      intro k hk
      exact ⟨fun s => (Nat.not_lt_of_ge hk) s.2⟩
    have hG : ∀ j, IsIso (homologyMap G.absolute j) :=
      fun j => ih C.asComplex hC (DeltaSubcomplex.empty _) G j
    have hH : ∀ j, IsIso (homologyMap H.relative j) := hskeletal D N hD H
    have hsame : F.absolute = H.absolute := by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      rw [F.absolute_formula, H.absolute_formula]
    rw [hsame]
    exact deltaAbsoluteComparison_of_subcomplex R A D C H G hG hH q


section OrderedRealization

/-- The ordered quotient realization maps to the original weak barycentric
realization by precisely the prescribed affine charts. -/
def orderedRealizationToSimplicial {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) :
    TopCat.of (orderedDelta K o).Realization ⟶ TopCat.of K.Realization := by
  let raw : (orderedDelta K o).SimplexSum → K.Realization :=
    fun p => orderedParametrization K o p.1 p.2.1 p.2.2
  have hraw : ∀ a b, ((orderedDelta K o).faceSetoid).r a b → raw a = raw b := by
    intro a b h
    induction h with
    | rel a b h =>
      cases h with
      | face a s t =>
        apply Subtype.ext
        change (orderedParametrization K o _ _ t).val =
          (orderedParametrization K o _ s (orderedAffineFace a t)).val
        rw [orderedParametrization_value, orderedParametrization_value]
        change t.map (fun i => s.1 (a i)) = (t.map a).map s.1
        rw [Convexity.StdSimplex.map_map]
    | refl => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  exact TopCat.ofHom ⟨Quotient.lift raw hraw, Continuous.quotient_lift (by
    apply continuous_sigma
    intro n
    apply continuous_sigma
    intro s
    exact (orderedParametrization K o n s).continuous) hraw⟩

@[simp] theorem orderedRealizationToSimplicial_chart {V : Type w}
    (K : AbstractSimplicialComplex V) (o : LinearOrder V) (n : ℕ)
    (s : (orderedDelta K o).Simplex n) (t : StandardSimplex n) :
    orderedRealizationToSimplicial K o ((orderedDelta K o).simplexChart n s t) =
      orderedParametrization K o n s t := rfl

/-- Positive barycentric representatives in the same order are unique. -/
theorem orderedParametrization_interior_unique {V : Type w}
    (K : AbstractSimplicialComplex V) (o : LinearOrder V)
    {n m : ℕ} (s : (orderedDelta K o).Simplex n) (r : (orderedDelta K o).Simplex m)
    (t : StandardSimplex n) (u : StandardSimplex m)
    (ht : t ∈ standardSimplexInterior n) (hu : u ∈ standardSimplexInterior m)
    (he : orderedParametrization K o n s t = orderedParametrization K o m r u) :
    (⟨n,s,t⟩ : (orderedDelta K o).SimplexSum) = ⟨m,r,u⟩ := by
  classical
  letI := o
  have hval : t.map s.1 = u.map r.1 := by
    simpa only [orderedParametrization_value] using congrArg Subtype.val he
  have hs : Finset.univ.image s.1 = Finset.univ.image r.1 := by
    have h := congrArg (fun x => x.weights.support) hval
    change (t.weights.mapDomain s.1).support = (u.weights.mapDomain r.1).support at h
    simpa only [Finsupp.mapDomain_support_of_injective s.1.injective,
      Finsupp.mapDomain_support_of_injective r.1.injective,
      P202.Topology.DeltaSupport.interior_support ht,
      P202.Topology.DeltaSupport.interior_support hu] using h
  have hnm : n = m := by
    have := congrArg Finset.card hs
    simpa only [Finset.card_image_of_injective _ s.1.injective,
      Finset.card_image_of_injective _ r.1.injective,
      Finset.card_univ, Fintype.card_fin, Nat.succ.injEq] using this
  subst m
  have hcard : (Finset.univ.image r.1).card = n+1 := by
    rw [Finset.card_image_of_injective _ r.1.injective]
    simp
  have hsr : s = r := by
    apply Subtype.ext
    exact (Finset.orderEmbOfFin_unique' hcard (fun i => by
      rw [← hs]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).trans
      (Finset.orderEmbOfFin_unique' hcard (fun i =>
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)).symm
  subst r
  have htu : t = u := by
    apply Convexity.StdSimplex.ext
    exact Finsupp.mapDomain_injective s.1.injective
      (congrArg Convexity.StdSimplex.weights hval)
  subst u
  rfl

theorem orderedRealizationToSimplicial_injective {V : Type w}
    (K : AbstractSimplicialComplex V) (o : LinearOrder V) :
    Function.Injective (orderedRealizationToSimplicial K o) := by
  intro x y h
  obtain ⟨n,s,t,ht,rfl⟩ := P202.Topology.deltaInteriorCover (orderedDelta K o) x
  obtain ⟨m,r,u,hu,rfl⟩ := P202.Topology.deltaInteriorCover (orderedDelta K o) y
  have he := orderedParametrization_interior_unique K o s r t u ht hu h
  exact congrArg (Quotient.mk (orderedDelta K o).faceSetoid) he

/-- Every original finite simplex has its unique increasing chart in any
specified vertex order. -/
theorem orderedRealization_chart_factorization {V : Type w}
    (K : AbstractSimplicialComplex V) (o : LinearOrder V) (s : K.Simplex) :
    ∃ (n : ℕ) (r : (orderedDelta K o).Simplex n)
      (e : s.1 ≃ Fin (n+1)),
      K.simplexChart s = orderedRealizationToSimplicial K o ∘
        (orderedDelta K o).simplexChart n r ∘ Convexity.StdSimplex.map e := by
  classical
  letI := o
  let n := s.1.card-1
  have hc : s.1.card = n+1 := (Nat.sub_add_cancel (K.nonempty s.1 s.2).card_pos).symm
  let e : Fin (n+1) ≃o s.1 := s.1.orderIsoOfFin hc
  let r : (orderedDelta K o).Simplex n := ⟨s.1.orderEmbOfFin hc, by
    simpa only [Finset.image_orderEmbOfFin_univ] using s.2⟩
  refine ⟨n,r,e.symm.toEquiv,?_⟩
  funext t
  apply Subtype.ext
  change (K.simplexChart s t).val = (orderedParametrization K o n r (t.map e.symm)).val
  rw [orderedParametrization_value]
  change t.map (Subtype.val : s.1 → V) = (t.map e.symm).map r.1
  rw [Convexity.StdSimplex.map_map]
  congr 1
  funext v
  change v.val = (e (e.symm v)).val
  rw [e.apply_symm_apply]

theorem orderedRealizationToSimplicial_surjective {V : Type w}
    (K : AbstractSimplicialComplex V) (o : LinearOrder V) :
    Function.Surjective (orderedRealizationToSimplicial K o) := by
  intro x
  obtain ⟨s,⟨t,ht,hs⟩,_⟩ := P202.Topology.simplicialInteriorPartition K x
  obtain ⟨n,r,e,he⟩ := orderedRealization_chart_factorization K o s
  refine ⟨(orderedDelta K o).simplexChart n r (t.map e), ?_⟩
  exact (congrFun he t).symm.trans hs

/-- The weak Δ-realization of increasing simplices is the original weak
simplicial realization, through the exact affine parametrizations. -/
def orderedRealizationHomeomorph {V : Type w}
    (K : AbstractSimplicialComplex V) (o : LinearOrder V) :
    (orderedDelta K o).Realization ≃ₜ K.Realization := by
  let f := orderedRealizationToSimplicial K o
  let e : (orderedDelta K o).Realization ≃ K.Realization :=
    Equiv.ofBijective f ⟨orderedRealizationToSimplicial_injective K o,
      orderedRealizationToSimplicial_surjective K o⟩
  refine { e with continuous_toFun := f.hom.continuous, continuous_invFun := ?_ }
  rw [continuous_iSup_dom]
  intro s
  rw [continuous_coinduced_dom]
  obtain ⟨n,r,a,ha⟩ := orderedRealization_chart_factorization K o s
  have he : e.symm ∘ K.simplexChart s =
      (orderedDelta K o).simplexChart n r ∘ Convexity.StdSimplex.map a := by
    funext t
    apply e.injective
    exact (e.apply_symm_apply _).trans (congrFun ha t)
  change Continuous (e.symm ∘ K.simplexChart s)
  rw [he]
  exact (deltaParametrization (orderedDelta K o) n r).continuous.comp
    (Convexity.StdSimplex.continuous_map ℝ a)

end OrderedRealization

section DeltaToSimplicial

/-- Postcomposition through the realization homeomorphism takes each specified
Δ-parametrization to exactly its original affine singular parametrization. -/
theorem orderedRealization_affine {V : Type w} (K : AbstractSimplicialComplex V)
    (o : LinearOrder V) (n : ℕ) :
    (((chainMap R A (orderedRealizationToSimplicial K o)).f n).hom).comp
        (deltaParametrizationLinear R A (orderedDelta K o) n) =
      orderedAffineLinear R A K o n := by
  apply Finsupp.lhom_ext
  intro s a
  change ((chainMap R A (orderedRealizationToSimplicial K o)).f n).hom
      (deltaParametrizationLinear R A (orderedDelta K o) n (Finsupp.single s a)) =
    orderedAffineLinear R A K o n (Finsupp.single s a)
  erw [P202.RelativeParametrizations.deltaParametrizationLinear_single,
    P202.SingularChains.chainMap_single, orderedAffineLinear_single]
  congr 1

/-- The general Δ-comparison implies the original absolute and relative
simplicial comparison through the canonical increasing-order Δ-model. -/
theorem simplicialComparison_of_deltaComparison
    (hdelta : P202Specs.SimplicialComparison.deltaComparison_type.{u,v,w}) :
    P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w} := by
  intro R _ A _ _ V K B
  have habs : ∀ (L : AbstractSimplicialComplex V) (C : Simplicial.Subcomplex L)
      (F : SimplicialComparisonData R A L C) (q : ℕ), IsIso (homologyMap F.absolute q) := by
    intro L C F q
    let o := P202Specs.OrientedSimplicialAlgebra.vertexOrder V
    obtain ⟨G,hG,_⟩ := hdelta R A (orderedDelta L o) (orderedSubcomplex L C o)
    have hsquare : G.absolute ≫ chainMap R A (orderedRealizationToSimplicial L o) =
        F.absolute := by
      apply HomologicalComplex.Hom.ext
      funext n
      apply ModuleCat.hom_ext
      change (((chainMap R A (orderedRealizationToSimplicial L o)).f n).hom).comp
        (G.absolute.f n).hom = (F.absolute.f n).hom
      rw [G.absolute_formula, F.absolute_formula]
      exact orderedRealization_affine R A L o n
    haveI : IsIso (orderedRealizationToSimplicial L o) := by
      change IsIso (TopCat.isoOfHomeo
        (X := TopCat.of (orderedDelta L o).Realization) (Y := TopCat.of L.Realization)
        (orderedRealizationHomeomorph L o)).hom
      infer_instance
    haveI := hG q
    rw [← hsquare, homologyMap_comp]
    infer_instance
  obtain ⟨F⟩ := simplicialComparisonData_nonempty R A K B
  exact ⟨F,habs K B F,fun q =>
    simplicialRelativeComparison_of_absolute R A habs K B F q⟩

end DeltaToSimplicial

end
/-- Completing the one remaining relative skeletal comparison gives the full
comparison for every Δ-complex and every subcomplex pair, including unbounded
and infinite weak realizations. This is an explicit reduction theorem. -/
theorem deltaComparison_of_skeletal
    (hskeletal : ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
      (E : DeltaComplex.{w}) (n : ℕ),
      (∀ k, n+1 ≤ k → IsEmpty (E.Simplex k)) →
      ∀ (H : DeltaComparisonData R A E (deltaSkeletonLT E n)) (q : ℕ),
        IsIso (homologyMap H.relative q)) :
    P202Specs.SimplicialComparison.deltaComparison_type.{u,v,w} := by
  intro R _ A _ _ D B
  have hfinite : ∀ (E : DeltaComplex.{w}), Finite (Σ n, E.Simplex n) →
      ∀ (G : DeltaComparisonData R A E (DeltaSubcomplex.empty E)) (q : ℕ),
        IsIso (homologyMap G.absolute q) := by
    intro E hE G q
    letI := hE
    obtain ⟨N,hN⟩ := deltaFinite_dimensionBound E
    exact deltaAbsoluteComparison_of_skeletal R A (hskeletal R A) N E hN
      (DeltaSubcomplex.empty _) G q
  have habsolute : ∀ (E : DeltaComplex.{w}) (C : DeltaSubcomplex E)
      (G : DeltaComparisonData R A E C) (q : ℕ), IsIso (homologyMap G.absolute q) :=
    deltaAbsoluteComparison_of_finite R A hfinite
  obtain ⟨F⟩ := deltaComparisonData_nonempty R A D B
  exact ⟨F,habsolute D B F,deltaRelativeComparison_of_absolute R A habsolute D B F⟩

/-- All remaining original comparison and order-independence conclusions
follow from the specified relative skeletal maps. No abstractly chosen
isomorphism is substituted for the canonical parametrization maps. -/
theorem comparisons_of_skeletal
    (hskeletal : ∀ (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
      (E : DeltaComplex.{w}) (n : ℕ),
      (∀ k, n+1 ≤ k → IsEmpty (E.Simplex k)) →
      ∀ (H : DeltaComparisonData R A E (deltaSkeletonLT E n)) (q : ℕ),
        IsIso (homologyMap H.relative q)) :
    P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w} ∧
      P202Specs.SimplicialComparison.deltaComparison_type.{u,v,w} ∧
      P202Specs.SimplicialComparison.orderIndependence_type.{u,v,w} := by
  have hd := deltaComparison_of_skeletal hskeletal
  have hs := simplicialComparison_of_deltaComparison hd
  exact ⟨hs,hd,orderIndependence_of_comparison hs⟩


section SelectionIso
variable {R : Type u} [CommRing R]
variable {C D : ChainComplex (ModuleCat.{v} R) ℕ}
/-- An isomorphism preserving the selected chains in both directions induces
an isomorphism of the actual relative quotient complexes. -/
def selectionQuotientIso (S : ChainSelection R C) (T : ChainSelection R D)
    (e : C ≅ D)
    (he : ∀ n x, x ∈ S.module n → (e.hom.f n).hom x ∈ T.module n)
    (hi : ∀ n x, x ∈ T.module n → (e.inv.f n).hom x ∈ S.module n) :
    S.quotient ≅ T.quotient where
  hom := S.quotientMap T e.hom he
  inv := T.quotientMap S e.inv hi
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x,rfl⟩ := (S.module n).mkQ_surjective x
    change (S.module n).mkQ ((e.inv.f n).hom ((e.hom.f n).hom x)) = (S.module n).mkQ x
    have h := congrArg (fun f => (f.f n).hom x) e.hom_inv_id
    exact congrArg (S.module n).mkQ h
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x,rfl⟩ := (T.module n).mkQ_surjective x
    change (T.module n).mkQ ((e.hom.f n).hom ((e.inv.f n).hom x)) = (T.module n).mkQ x
    have h := congrArg (fun f => (f.f n).hom x) e.inv_hom_id
    exact congrArg (T.module n).mkQ h
end SelectionIso

section
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- The weak realization of a Δ-complex with only vertex labels is discrete. -/
theorem deltaZeroDimensional_discrete (D : DeltaComplex.{w})
    (hD : ∀ n : ℕ, n ≠ 0 → IsEmpty (D.Simplex n)) :
    DiscreteTopology D.Realization := by
  apply discreteTopology_iff_forall_isOpen.mpr
  intro U
  apply (P202.Topology.deltaProjectionQuotient D).isCoinducing.isOpen_preimage.mp
  apply isOpen_sigma_iff.mpr
  intro n
  apply isOpen_sigma_iff.mpr
  intro s
  by_cases hn : n = 0
  · subst n
    exact isOpen_discrete _
  · exact (hD n hn).false s |>.elim

/-- Totally disconnected singular chains form the alternating constant
complex on the actual points, with the given module coefficients. -/
def singularTotallyDisconnectedIso (X : TopCat.{w}) [TotallyDisconnectedSpace X] :
    P202Specs.SingularChains.complex R A X ≅
      ChainComplex.alternatingConst.obj (ModuleCat.of R (X →₀ A)) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
    (Functor.isoWhiskerRight (TopCat.toSSetIsoConst X) (finsuppFunctor R A) ≪≫
      Functor.constComp _ _ _) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app _

/-- The ordinary first differential vanishes on every totally disconnected
space, including the empty space. -/
theorem singularTotallyDisconnected_boundary_one (X : TopCat.{w})
    [TotallyDisconnectedSpace X] :
    (P202Specs.SingularChains.complex R A X).d 1 0 = 0 := by
  let e := singularTotallyDisconnectedIso R A X
  apply (cancel_mono (e.hom.f 0)).mp
  rw [zero_comp, ← e.hom.comm 1 0]
  simp [e, ChainComplex.alternatingConst]

/-- Positive-degree singular homology vanishes for totally disconnected
spaces in precisely the chain model used by comparison. -/
theorem singularTotallyDisconnected_homology_isZero (X : TopCat.{w})
    [TotallyDisconnectedSpace X] (q : ℕ) (hq : q ≠ 0) :
    IsZero ((P202Specs.SingularChains.complex R A X).homology q) :=
  ((ChainComplex.alternatingConst_exactAt _ q hq).of_iso
    (singularTotallyDisconnectedIso R A X).symm).isZero_homology

/-- Vertex labels parametrize precisely the points of a zero-dimensional
Δ-realization; the weak quotient introduces no identifications of vertices. -/
theorem deltaZeroDimensional_vertices_bijective (D : DeltaComplex.{w})
    (hD : ∀ n : ℕ, n ≠ 0 → IsEmpty (D.Simplex n)) :
    Function.Bijective (fun s : D.Simplex 0 =>
      D.simplexChart 0 s (Convexity.StdSimplex.single 0)) := by
  constructor
  · intro s t h
    have ht : Convexity.StdSimplex.single (0 : Fin 1) ∈ standardSimplexInterior 0 := by
      intro i
      have hi : i = 0 := Fin.eq_zero i
      simp [hi]
    have he := P202.Topology.DeltaSupport.interior_quotient_unique D ht ht h
    exact (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj he).2)).1
  · intro x
    obtain ⟨⟨n,s,t⟩,rfl⟩ := Quotient.mk_surjective x
    by_cases hn : n = 0
    · subst n
      exact ⟨s,congrArg (D.simplexChart 0 s) (Subsingleton.elim _ _)⟩
    · exact (hD n hn).false s |>.elim

/-- The canonical affine vertex map is a bijection onto the actual singular
zero-simplices of a zero-dimensional Δ-realization. -/
theorem deltaZeroDimensional_singularSimplex_bijective (D : DeltaComplex.{w})
    (hD : ∀ n : ℕ, n ≠ 0 → IsEmpty (D.Simplex n)) :
    Function.Bijective (deltaSingularSimplex D 0) := by
  let v : StandardSimplex 0 := Convexity.StdSimplex.single 0
  have hv := deltaZeroDimensional_vertices_bijective D hD
  constructor
  · intro s t h
    apply hv.injective
    exact congrArg (fun z => simplexEquiv (TopCat.of D.Realization) 0 z v) h
  · intro s
    obtain ⟨t,ht⟩ := hv.surjective (simplexEquiv (TopCat.of D.Realization) 0 s v)
    refine ⟨t,?_⟩
    apply (simplexEquiv (TopCat.of D.Realization) 0).injective
    ext p
    change D.simplexChart 0 t p = simplexEquiv (TopCat.of D.Realization) 0 s p
    exact (congrArg (D.simplexChart 0 t) (Subsingleton.elim p v)).trans
      (ht.trans (congrArg (simplexEquiv (TopCat.of D.Realization) 0 s) (Subsingleton.elim v p)))

/-- The chain comparison is an isomorphism in degree zero for a
zero-dimensional Δ-complex, for arbitrary module coefficients. -/
theorem deltaZeroDimensional_affine_zero_bijective (D : DeltaComplex.{w})
    (hD : ∀ n : ℕ, n ≠ 0 → IsEmpty (D.Simplex n))
    (B : DeltaSubcomplex D) (F : DeltaComparisonData R A D B) :
    Function.Bijective (F.absolute.f 0).hom := by
  rw [F.absolute_formula]
  change Function.Bijective (Finsupp.mapDomain (deltaSingularSimplex D 0))
  have hv := deltaZeroDimensional_singularSimplex_bijective D hD
  exact ⟨Finsupp.mapDomain_injective hv.injective,
    Finsupp.mapDomain_surjective hv.surjective⟩

/-- The actual Δ-chain homology vanishes in every positive degree when
all positive-dimensional simplex-label types are empty. -/
theorem deltaZeroDimensional_homology_isZero (D : DeltaComplex.{w})
    (hD : ∀ n : ℕ, n ≠ 0 → IsEmpty (D.Simplex n)) (q : ℕ) (hq : q ≠ 0) :
    IsZero ((deltaComplex R A D).homology q) := by
  letI : IsEmpty (D.Simplex q) := hD q hq
  have hzero : IsZero ((deltaComplex R A D).X q) := by
    change IsZero (ModuleCat.of R (D.Simplex q →₀ A))
    exact ModuleCat.isZero_of_subsingleton _
  exact (HomologicalComplex.ExactAt.of_isZero hzero).isZero_homology

/-- Canonical absolute Δ–singular comparison in dimension zero. This applies
to every vertex-label set and every module, without any finiteness hypothesis. -/
theorem deltaZeroDimensional_absoluteComparison (D : DeltaComplex.{w})
    (hD : ∀ n : ℕ, n ≠ 0 → IsEmpty (D.Simplex n))
    (B : DeltaSubcomplex D) (F : DeltaComparisonData R A D B) (q : ℕ) :
    IsIso (homologyMap F.absolute q) := by
  letI := deltaZeroDimensional_discrete D hD
  by_cases hq : q = 0
  · subst q
    have hp : (ComplexShape.down ℕ).prev 0 = 1 :=
      (ComplexShape.down ℕ).prev_eq' (by simp)
    have hn : (ComplexShape.down ℕ).next 0 = 0 :=
      (ComplexShape.down ℕ).next_eq_self' 0 (by intro k; simp)
    change IsIso (ShortComplex.homologyMap
      ((shortComplexFunctor (ModuleCat.{max v w} R) (ComplexShape.down ℕ) 0).map F.absolute))
    have hfun : shortComplexFunctor (ModuleCat.{max v w} R) (ComplexShape.down ℕ) 0 =
        shortComplexFunctor' (ModuleCat.{max v w} R) (ComplexShape.down ℕ) 1 0 0 := by
      rw [shortComplexFunctor,hp,hn]
    rw [hfun]
    apply homologyMap_isIso_of_cycle_conditions
    · intro y hy
      dsimp only [shortComplexFunctor'] at *
      obtain ⟨x,hx⟩ := (deltaZeroDimensional_affine_zero_bijective R A D hD B F).surjective y
      refine ⟨x,?_,0,?_⟩
      · change ((deltaComplex R A D).d 0 0).hom x = 0
        rw [(deltaComplex R A D).shape 0 0 (by decide)]
        rfl
      · change (ConcreteCategory.hom (F.absolute.f 0)) x = y at hx
        rw [hx,sub_self]
        exact map_zero _
    · intro x hx hbound
      dsimp only [shortComplexFunctor'] at *
      obtain ⟨z,hz⟩ := hbound
      change ((P202Specs.SingularChains.complex R A (TopCat.of D.Realization)).d 1 0).hom z =
        (F.absolute.f 0).hom x at hz
      rw [singularTotallyDisconnected_boundary_one R A] at hz
      have hxzero : x = 0 :=
        (deltaZeroDimensional_affine_zero_bijective R A D hD B F).injective
          (hz.symm.trans (map_zero _).symm)
      refine ⟨0,?_⟩
      rw [hxzero]
      exact map_zero _
  · exact (deltaZeroDimensional_homology_isZero R A D hD q hq).isIso
      (singularTotallyDisconnected_homology_isZero R A (TopCat.of D.Realization) q hq)
      (homologyMap F.absolute q)


/-- Relative chains of a complex bounded in dimension n vanish off degree n
after quotienting by its lower skeleton. -/
theorem deltaBoundedRelative_eq_zero (D : DeltaComplex.{w}) (n : ℕ)
    (hD : ∀ k, n+1 ≤ k → IsEmpty (D.Simplex k)) (q : ℕ) (hq : q ≠ n)
    (c : (deltaRelativeComplex R A D (deltaSkeletonLT D n)).X q) : c = 0 := by
  let e := deltaRelativeDegreeEquiv R A D (deltaSkeletonLT D n) q
  apply e.injective
  rw [map_zero]
  apply Finsupp.ext
  intro s
  by_cases h : q < n
  · exact False.elim (s.2 h)
  · exact False.elim ((hD q (by omega)).false s.1)

/-- Categorical concentration of the actual bounded relative Δ-chain model. -/
theorem deltaBoundedRelative_isZero (D : DeltaComplex.{w}) (n : ℕ)
    (hD : ∀ k, n+1 ≤ k → IsEmpty (D.Simplex k)) (q : ℕ) (hq : q ≠ n) :
    IsZero ((deltaRelativeComplex R A D (deltaSkeletonLT D n)).X q) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact ⟨fun x y => (deltaBoundedRelative_eq_zero R A D n hD q hq x).trans
    (deltaBoundedRelative_eq_zero R A D n hD q hq y).symm⟩

/-- All its differentials vanish, including the ordinary outgoing vertex
boundary when n = 0. -/
theorem deltaBoundedRelative_d_zero (D : DeltaComplex.{w}) (n : ℕ)
    (hD : ∀ k, n+1 ≤ k → IsEmpty (D.Simplex k)) (i j : ℕ) :
    (deltaRelativeComplex R A D (deltaSkeletonLT D n)).d i j = 0 := by
  by_cases hi : i = n
  · subst i
    by_cases hj : j = n
    · subst j
      exact (deltaRelativeComplex R A D (deltaSkeletonLT D n)).shape n n (by simp)
    · exact (deltaBoundedRelative_isZero R A D n hD j hj).eq_of_tgt _ _
  · exact (deltaBoundedRelative_isZero R A D n hD i hi).eq_of_src _ _

def deltaBoundedRelativeLabels (D : DeltaComplex.{w}) (n : ℕ) :
    ↥((deltaSkeletonLT D n).selected n)ᶜ ≃ D.Simplex n where
  toFun s := s.1
  invFun s := ⟨s,Nat.lt_irrefl n⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The top relative group retains every original simplex label. -/
def deltaBoundedRelativeTopEquiv (D : DeltaComplex.{w}) (n : ℕ) :
    (deltaRelativeComplex R A D (deltaSkeletonLT D n)).X n ≃ₗ[R]
      (D.Simplex n →₀ A) :=
  deltaRelativeDegreeEquiv R A D (deltaSkeletonLT D n) n ≪≫ₗ
    Finsupp.domLCongr (deltaBoundedRelativeLabels D n)

@[simp] theorem deltaBoundedRelativeTopEquiv_symm_single (D : DeltaComplex.{w}) (n : ℕ)
    (s : D.Simplex n) (a : A) :
    (deltaBoundedRelativeTopEquiv R A D n).symm (Finsupp.single s a) =
      ((deltaSelection R A D (deltaSkeletonLT D n)).module n).mkQ
        (Finsupp.single s a) := by
  simp [deltaBoundedRelativeTopEquiv, Finsupp.domLCongr, deltaBoundedRelativeLabels]

/-- The combinatorial bounded relative homology has its canonical simplex
coordinates, ready for the characteristic-map comparison. -/
def deltaBoundedRelativeHomologyIso (D : DeltaComplex.{w}) (n : ℕ)
    (hD : ∀ k, n+1 ≤ k → IsEmpty (D.Simplex k)) :
    (deltaRelativeComplex R A D (deltaSkeletonLT D n)).homology n ≅
      ModuleCat.of R (D.Simplex n →₀ A) :=
  (ShortComplex.HomologyData.ofZeros
    ((deltaRelativeComplex R A D (deltaSkeletonLT D n)).sc n)
    (deltaBoundedRelative_d_zero R A D n hD _ _)
    (deltaBoundedRelative_d_zero R A D n hD _ _)).left.homologyIso ≪≫
      (deltaBoundedRelativeTopEquiv R A D n).toModuleIso

theorem deltaBoundedRelative_homology_isZero (D : DeltaComplex.{w}) (n : ℕ)
    (hD : ∀ k, n+1 ≤ k → IsEmpty (D.Simplex k)) (q : ℕ) (hq : q ≠ n) :
    IsZero ((deltaRelativeComplex R A D (deltaSkeletonLT D n)).homology q) :=
  (HomologicalComplex.ExactAt.of_isZero
    (deltaBoundedRelative_isZero R A D n hD q hq)).isZero_homology


section SingularSigma

variable {ι : Type w} (X : ι → TopCat.{w})

/-- Inclusion of a summand in the topological disjoint union. -/
def singularSigmaInclusion (i : ι) : X i ⟶ TopCat.of (Σ j, X j) :=
  TopCat.ofHom (ContinuousMap.sigmaMk (X := fun j => X j) i)

/-- A singular simplex lies in one and only one topological summand. The
connectedness of the standard simplex supplies this decomposition. -/
def singularSimplexSigmaEquiv (n : ℕ) :
    Simplex (TopCat.of (Σ i, X i)) n ≃ Σ i, Simplex (X i) n :=
  (simplexEquiv (TopCat.of (Σ i, X i)) n).trans
    ((ContinuousMap.sigmaCodHomeomorph (StandardSimplex n) (fun i => X i)).toEquiv.trans
      (Equiv.sigmaCongrRight (fun i => (simplexEquiv (X i) n).symm)))

@[simp] theorem singularSimplexSigmaEquiv_symm_apply (n : ℕ) (i : ι)
    (s : Simplex (X i) n) :
    (singularSimplexSigmaEquiv X n).symm ⟨i,s⟩ =
      (TopCat.toSSet.map (singularSigmaInclusion X i)).app (Opposite.op ⦋n⦌) s := by
  apply (simplexEquiv (TopCat.of (Σ i, X i)) n).injective
  rw [P202.SingularChains.simplexEquiv_postcomp]
  simp [singularSimplexSigmaEquiv, singularSigmaInclusion,
    Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight]

/-- The underlying labels of chains split by their unique summand. -/
def singularChainsSigmaEquiv (n : ℕ) :
    Chains A (TopCat.of (Σ i, X i)) n ≃ₗ[R] (Σ i, Simplex (X i) n) →₀ A :=
  Finsupp.mapDomain.linearEquiv A R (singularSimplexSigmaEquiv X n)

/-- The differential on the disjoint union of singular-simplex bases is the
ordinary signed face differential within the same summand. -/
def singularSigmaBoundary (n : ℕ) :
    ((Σ i, Simplex (X i) (n+1)) →₀ A) →ₗ[R] ((Σ i, Simplex (X i) n) →₀ A) :=
  ∑ j : Fin (n+2), (-1 : ℤ)^j.val •
    Finsupp.lmapDomain A R (fun s => ⟨s.1, face j s.2⟩)

@[simp] theorem singularSigmaBoundary_single (n : ℕ) (i : ι)
    (s : Simplex (X i) (n+1)) (a : A) :
    singularSigmaBoundary R A X n (Finsupp.single ⟨i,s⟩ a) =
      ∑ j : Fin (n+2), (-1 : ℤ)^j.val • Finsupp.single ⟨i,face j s⟩ a := by
  classical
  simp [singularSigmaBoundary, LinearMap.sum_apply, LinearMap.smul_apply]

/-- Joining the summands commutes with every signed face boundary. -/
theorem singularSigmaBoundary_join (n : ℕ) :
    ((singularChainsSigmaEquiv R A X n).symm.toLinearMap).comp
        (singularSigmaBoundary R A X n) =
      (boundary R A (TopCat.of (Σ i, X i)) n).comp
        ((singularChainsSigmaEquiv R A X (n+1)).symm.toLinearMap) := by
  apply Finsupp.lhom_ext
  rintro ⟨i,s⟩ a
  change (singularChainsSigmaEquiv R A X n).symm
      (singularSigmaBoundary R A X n (Finsupp.single ⟨i,s⟩ a)) =
    boundary R A (TopCat.of (Σ i, X i)) n
      ((singularChainsSigmaEquiv R A X (n+1)).symm (Finsupp.single ⟨i,s⟩ a))
  have hsingle (m : ℕ) (s : Simplex (X i) m) :
      (singularChainsSigmaEquiv R A X m).symm (Finsupp.single ⟨i,s⟩ a) =
      ((chainMap R A (singularSigmaInclusion X i)).f m).hom (Finsupp.single s a) := by
    change Finsupp.mapDomain (singularSimplexSigmaEquiv X m).symm (Finsupp.single ⟨i,s⟩ a) = _
    rw [Finsupp.mapDomain_single, singularSimplexSigmaEquiv_symm_apply,
      P202.SingularChains.chainMap_single]
  rw [singularSigmaBoundary_single, map_sum]
  simp only [map_zsmul, hsingle]
  have h := congrArg (fun f => f.hom (Finsupp.single s a))
    (P202.SingularChains.chainMap_boundary R A (singularSigmaInclusion X i) n)
  change boundary R A (TopCat.of (Σ i, X i)) n
      (((chainMap R A (singularSigmaInclusion X i)).f (n+1)).hom (Finsupp.single s a)) =
    ((chainMap R A (singularSigmaInclusion X i)).f n).hom
      (boundary R A (X i) n (Finsupp.single s a)) at h
  rw [h, P202.SingularChains.boundary_single]
  simp only [map_sum, map_zsmul]

 theorem singularSigmaBoundary_join_apply (n : ℕ)
    (c : (Σ i, Simplex (X i) (n+1)) →₀ A) :
    (singularChainsSigmaEquiv R A X n).symm (singularSigmaBoundary R A X n c) =
      boundary R A (TopCat.of (Σ i, X i)) n
        ((singularChainsSigmaEquiv R A X (n+1)).symm c) :=
  LinearMap.congr_fun (singularSigmaBoundary_join R A X n) c

/-- Splitting also commutes with the boundary. -/
theorem singularChainsSigmaEquiv_boundary (n : ℕ)
    (c : Chains A (TopCat.of (Σ i, X i)) (n+1)) :
    singularChainsSigmaEquiv R A X n (boundary R A (TopCat.of (Σ i, X i)) n c) =
      singularSigmaBoundary R A X n (singularChainsSigmaEquiv R A X (n+1) c) := by
  apply (singularChainsSigmaEquiv R A X n).symm.injective
  simpa only [LinearEquiv.symm_apply_apply] using
    (singularSigmaBoundary_join_apply R A X n
      (singularChainsSigmaEquiv R A X (n+1) c)).symm

/-- The summandwise differential squares to zero, without restrictions on
the number of summands or the coefficient module. -/
theorem singularSigmaBoundary_squared (n : ℕ) :
    (singularSigmaBoundary R A X n).comp (singularSigmaBoundary R A X (n+1)) = 0 := by
  apply LinearMap.ext
  intro c
  apply (singularChainsSigmaEquiv R A X n).symm.injective
  change (singularChainsSigmaEquiv R A X n).symm
    (singularSigmaBoundary R A X n (singularSigmaBoundary R A X (n+1) c)) =
      (singularChainsSigmaEquiv R A X n).symm 0
  rw [map_zero, singularSigmaBoundary_join_apply, singularSigmaBoundary_join_apply]
  exact congrArg (fun f => f.hom ((singularChainsSigmaEquiv R A X (n+2)).symm c))
    ((complex R A (TopCat.of (Σ i, X i))).d_comp_d (n+2) (n+1) n)

/-- The complex of finite chains on the disjoint union of the summand bases. -/
def singularSigmaComplex : ChainComplex (ModuleCat.{max v w} R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R ((Σ i, Simplex (X i) n) →₀ A))
    (fun n => ModuleCat.ofHom (singularSigmaBoundary R A X n)) (by
      intro n
      apply ModuleCat.hom_ext
      exact singularSigmaBoundary_squared R A X n)

/-- Singular chains carry arbitrary topological disjoint unions to the
summandwise direct sum complex, via the canonical basis decomposition. -/
def singularSigmaChainIso :
    complex R A (TopCat.of (Σ i, X i)) ≅ singularSigmaComplex R A X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (singularChainsSigmaEquiv R A X n).toModuleIso) (by
      intro m n hmn
      change n+1 = m at hmn
      subst m
      dsimp only [singularSigmaComplex]
      rw [ChainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change singularSigmaBoundary R A X n (singularChainsSigmaEquiv R A X (n+1) c) =
        singularChainsSigmaEquiv R A X n (boundary R A (TopCat.of (Σ i, X i)) n c)
      exact (singularChainsSigmaEquiv_boundary R A X n c).symm)

end SingularSigma

section ConstantSingularSigma

variable (I : Type w) (X : TopCat.{z})

/-- A simplex in a constant-family disjoint union, with its summand recorded. -/
def constantSigmaSimplex (n : ℕ) (i : I) (s : Simplex X n) :
    Simplex (TopCat.of (Σ _ : I, X)) n :=
  (simplexEquiv (TopCat.of (Σ _ : I, X)) n).symm
    ((ContinuousMap.sigmaMk i).comp (simplexEquiv X n s))

@[simp] theorem constantSigmaSimplex_value (n : ℕ) (i : I) (s : Simplex X n)
    (t : StandardSimplex n) :
    simplexEquiv (TopCat.of (Σ _ : I, X)) n (constantSigmaSimplex I X n i s) t =
      ⟨i,simplexEquiv X n s t⟩ := by
  simp [constantSigmaSimplex]

@[simp] theorem constantSigmaSimplex_face {n : ℕ} (j : Fin (n+2))
    (i : I) (s : Simplex X (n+1)) :
    face j (constantSigmaSimplex I X (n+1) i s) =
      constantSigmaSimplex I X n i (face j s) := by
  apply (simplexEquiv (TopCat.of (Σ _ : I, X)) n).injective
  rw [P202.SingularChains.simplexEquiv_face]
  simp only [constantSigmaSimplex, Equiv.apply_symm_apply,
    P202.SingularChains.simplexEquiv_face, ContinuousMap.comp_assoc]

/-- Decomposing the connected simplex into one summand, then placing that
summand index into the coefficient, uses independent geometric and index universes. -/
def constantSigmaLabelEquiv (n : ℕ) :
    Simplex (TopCat.of (Σ _ : I, X)) n ≃ Simplex X n × I :=
  (simplexEquiv (TopCat.of (Σ _ : I, X)) n).trans
    ((ContinuousMap.sigmaCodHomeomorph (StandardSimplex n) (fun _ : I => X)).toEquiv.trans
      ((Equiv.sigmaCongrRight (fun _ : I => (simplexEquiv X n).symm)).trans
        ((Equiv.sigmaEquivProd I (Simplex X n)).trans (Equiv.prodComm _ _))))

@[simp] theorem constantSigmaLabelEquiv_symm_apply (n : ℕ)
    (s : Simplex X n) (i : I) :
    (constantSigmaLabelEquiv I X n).symm (s,i) = constantSigmaSimplex I X n i s := by
  apply (simplexEquiv (TopCat.of (Σ _ : I, X)) n).injective
  simp [constantSigmaLabelEquiv, constantSigmaSimplex, Equiv.sigmaCongrRight]

/-- Absolute chains on the disjoint union are chains on one space with
finitely supported summand coefficients. This also handles an empty index set. -/
def constantSigmaChainsEquiv (n : ℕ) :
    Chains A (TopCat.of (Σ _ : I, X)) n ≃ₗ[R] Chains (I →₀ A) X n :=
  (Finsupp.mapDomain.linearEquiv A R (constantSigmaLabelEquiv I X n)).trans
    (Finsupp.curryLinearEquiv R)

@[simp] theorem constantSigmaChainsEquiv_symm_single (n : ℕ) (i : I)
    (s : Simplex X n) (a : A) :
    (constantSigmaChainsEquiv R A I X n).symm
        (Finsupp.single s (Finsupp.single i a)) =
      Finsupp.single (constantSigmaSimplex I X n i s) a := by
  change Finsupp.mapDomain (constantSigmaLabelEquiv I X n).symm
    ((Finsupp.single s (Finsupp.single i a)).uncurry) = _
  rw [Finsupp.uncurry_single, Finsupp.mapDomain_single,
    constantSigmaLabelEquiv_symm_apply]

/-- The coefficient conversion preserves every face and its orientation sign. -/
theorem constantSigmaChainsEquiv_boundary_join (n : ℕ) :
    ((constantSigmaChainsEquiv R A I X n).symm.toLinearMap).comp
        (boundary R (I →₀ A) X n) =
      (boundary R A (TopCat.of (Σ _ : I, X)) n).comp
        ((constantSigmaChainsEquiv R A I X (n+1)).symm.toLinearMap) := by
  apply Finsupp.lhom_ext
  intro s b
  change (constantSigmaChainsEquiv R A I X n).symm
      (boundary R (I →₀ A) X n (Finsupp.single s b)) =
    boundary R A (TopCat.of (Σ _ : I, X)) n
      ((constantSigmaChainsEquiv R A I X (n+1)).symm (Finsupp.single s b))
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [Finsupp.single_add, map_add, hb, hc]
  | single i a =>
    rw [constantSigmaChainsEquiv_symm_single, P202.SingularChains.boundary_single,
      P202.SingularChains.boundary_single, map_sum]
    simp only [map_zsmul, constantSigmaChainsEquiv_symm_single,
      constantSigmaSimplex_face]

 theorem constantSigmaChainsEquiv_boundary_join_apply (n : ℕ)
    (c : Chains (I →₀ A) X (n+1)) :
    (constantSigmaChainsEquiv R A I X n).symm (boundary R (I →₀ A) X n c) =
      boundary R A (TopCat.of (Σ _ : I, X)) n
        ((constantSigmaChainsEquiv R A I X (n+1)).symm c) :=
  LinearMap.congr_fun (constantSigmaChainsEquiv_boundary_join R A I X n) c

 theorem constantSigmaChainsEquiv_boundary (n : ℕ)
    (c : Chains A (TopCat.of (Σ _ : I, X)) (n+1)) :
    constantSigmaChainsEquiv R A I X n
        (boundary R A (TopCat.of (Σ _ : I, X)) n c) =
      boundary R (I →₀ A) X n (constantSigmaChainsEquiv R A I X (n+1) c) := by
  apply (constantSigmaChainsEquiv R A I X n).symm.injective
  simpa only [LinearEquiv.symm_apply_apply] using
    (constantSigmaChainsEquiv_boundary_join_apply R A I X n
      (constantSigmaChainsEquiv R A I X (n+1) c)).symm

/-- The nonnegative singular chain complex of copies of X is exactly the
singular chain complex of X with finitely supported summand coefficients. -/
def constantSigmaChainIso :
    complex R A (TopCat.of (Σ _ : I, X)) ≅ complex R (I →₀ A) X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (constantSigmaChainsEquiv R A I X n).toModuleIso) (by
      intro m n hmn
      change n+1 = m at hmn
      subst m
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro c
      change boundary R (I →₀ A) X n (constantSigmaChainsEquiv R A I X (n+1) c) =
        constantSigmaChainsEquiv R A I X n
          (boundary R A (TopCat.of (Σ _ : I, X)) n c)
      exact (constantSigmaChainsEquiv_boundary R A I X n c).symm)

end ConstantSingularSigma

section ConstantSingularSigmaSupport
variable (I : Type w) (X : TopCat.{z}) (B : Set X)

@[simp] theorem constantSigmaChainsEquiv_single (n : ℕ) (i : I)
    (s : Simplex X n) (a : A) :
    constantSigmaChainsEquiv R A I X n
        (Finsupp.single (constantSigmaSimplex I X n i s) a) =
      Finsupp.single s (Finsupp.single i a) := by
  apply (constantSigmaChainsEquiv R A I X n).symm.injective
  rw [LinearEquiv.symm_apply_apply, constantSigmaChainsEquiv_symm_single]

/-- Splitting into summand coefficients preserves exactly the chains supported
in copies of the chosen subspace. -/
theorem constantSigmaChainsEquiv_preserves (n : ℕ)
    (c : Chains A (TopCat.of (Σ _ : I, X)) n)
    (hc : c ∈ (singularSelection R A (TopCat.of (Σ _ : I, X)) {p | p.2 ∈ B}).module n) :
    constantSigmaChainsEquiv R A I X n c ∈
      (singularSelection R (I →₀ A) X B).module n := by
  apply map_supported R A _ _ (constantSigmaChainsEquiv R A I X n).toLinearMap ?_ c hc
  intro t ht a
  obtain ⟨⟨s,i⟩,rfl⟩ := (constantSigmaLabelEquiv I X n).symm.surjective t
  rw [constantSigmaLabelEquiv_symm_apply]
  change constantSigmaChainsEquiv R A I X n
    (Finsupp.single (constantSigmaSimplex I X n i s) a) ∈ _
  rw [constantSigmaChainsEquiv_single]
  apply Finsupp.single_mem_supported
  intro u
  have h := ht u
  change (simplexEquiv (TopCat.of (Σ _ : I, X)) n
    ((constantSigmaLabelEquiv I X n).symm (s,i)) u).2 ∈ B at h
  rw [constantSigmaLabelEquiv_symm_apply, constantSigmaSimplex_value] at h
  exact h

/-- Joining coefficient summands preserves subspace-supported chains as well. -/
theorem constantSigmaChainsEquiv_symm_preserves (n : ℕ)
    (c : Chains (I →₀ A) X n)
    (hc : c ∈ (singularSelection R (I →₀ A) X B).module n) :
    (constantSigmaChainsEquiv R A I X n).symm c ∈
      (singularSelection R A (TopCat.of (Σ _ : I, X)) {p | p.2 ∈ B}).module n := by
  apply map_supported R (I →₀ A) _ _ (constantSigmaChainsEquiv R A I X n).symm.toLinearMap
    ?_ c hc
  intro s hs b
  change (constantSigmaChainsEquiv R A I X n).symm (Finsupp.single s b) ∈ _
  induction b using Finsupp.induction_linear with
  | zero => simp
  | add b c hb hc =>
    rw [Finsupp.single_add, map_add]
    exact Submodule.add_mem _ hb hc
  | single i a =>
    rw [constantSigmaChainsEquiv_symm_single]
    apply Finsupp.single_mem_supported
    intro t
    change (simplexEquiv (TopCat.of (Σ _ : I, X)) n
      (constantSigmaSimplex I X n i s) t).2 ∈ B
    rw [constantSigmaSimplex_value]
    exact hs t

 theorem constantSigmaChainsEquiv_supported_iff (n : ℕ)
    (c : Chains A (TopCat.of (Σ _ : I, X)) n) :
    constantSigmaChainsEquiv R A I X n c ∈
        (singularSelection R (I →₀ A) X B).module n ↔
      c ∈ (singularSelection R A (TopCat.of (Σ _ : I, X)) {p | p.2 ∈ B}).module n := by
  constructor
  · intro hc
    simpa only [LinearEquiv.symm_apply_apply] using
      constantSigmaChainsEquiv_symm_preserves R A I X B n
        (constantSigmaChainsEquiv R A I X n c) hc
  · exact constantSigmaChainsEquiv_preserves R A I X B n c

end ConstantSingularSigmaSupport

end

end P202.SimplicialComparison

open scoped TensorProduct
namespace P202.SimplicialComparison.ModuleCoefficients
open P202Specs.SingularChains P202Specs.RelativeSingularChains
open P202.SpheresDisks.IntegralCoefficients
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

def relativeCoordinates (P : Pair.{w}) (n : ℕ) :
    (nonnegative R A P).X n ≃ₗ[R] (Outside P n →₀ A) :=
  Classical.choose (P202.RelativeSingularChains.quotient_coordinates R A P n)

lemma relativeCoordinates_projection (P : Pair.{w}) (n : ℕ) (c : Chains A P.space n) :
    relativeCoordinates R A P n ((projection (chainFunctor R A) P).f n c) =
      outsideProjection R A P n c :=
  Classical.choose_spec (P202.RelativeSingularChains.quotient_coordinates R A P n) c

/-- The relative coefficient change is valid for spaces in every universe. -/
def relativeCoefficientComponent (P : Pair.{w}) (n : ℕ) :
    (integralTensorFunctor R A).obj ((nonnegative ℤ ℤ P).X n) ≅
      (nonnegative R A P).X n := by
  classical
  exact (integralTensorFunctor R A).mapIso (relativeCoordinates ℤ ℤ P n).toModuleIso ≪≫
    (TensorProduct.finsuppScalarRight ℤ R A (Outside P n)).toModuleIso ≪≫
      (relativeCoordinates R A P n).symm.toModuleIso

lemma relativeCoefficientComponent_projection (P : Pair.{w}) (n : ℕ)
    (a : A) (c : Chains ℤ P.space n) :
    (relativeCoefficientComponent R A P n).hom
      (a ⊗ₜ[ℤ] ((projection (chainFunctor ℤ ℤ) P).f n c)) =
      (projection (chainFunctor R A) P).f n
        (integralTensorChainsEquiv R A P.space n (a ⊗ₜ[ℤ] c)) := by
  classical
  apply (relativeCoordinates R A P n).injective
  change (relativeCoordinates R A P n)
    ((relativeCoordinates R A P n).symm
      ((TensorProduct.finsuppScalarRight ℤ R A (Outside P n))
        (TensorProduct.AlgebraTensorModule.lTensor R A
          (relativeCoordinates ℤ ℤ P n).toLinearMap
            (a ⊗ₜ[ℤ] ((projection (chainFunctor ℤ ℤ) P).f n c))))) = _
  rw [LinearEquiv.apply_symm_apply, TensorProduct.AlgebraTensorModule.lTensor_tmul]
  rw [relativeCoordinates_projection R A P n]
  change (TensorProduct.finsuppScalarRight ℤ R A (Outside P n))
    (a ⊗ₜ[ℤ] (relativeCoordinates ℤ ℤ P n)
      ((projection (chainFunctor ℤ ℤ) P).f n c)) = _
  erw [relativeCoordinates_projection ℤ ℤ P n c]
  ext s
  rw [TensorProduct.finsuppScalarRight_apply_tmul_apply]
  change c s.val • a = (integralTensorChainsEquiv R A P.space n (a ⊗ₜ[ℤ] c)) s.val
  exact (TensorProduct.finsuppScalarRight_apply_tmul_apply (R := ℤ) (S := R) a c s.val).symm

lemma relativeCoefficientComponent_boundary (P : Pair.{w}) (n : ℕ)
    (z : A ⊗[ℤ] (nonnegative ℤ ℤ P).X (n+1)) :
    (relativeCoefficientComponent R A P n).hom
        (TensorProduct.AlgebraTensorModule.lTensor R A
          ((nonnegative ℤ ℤ P).d (n+1) n).hom z) =
      (nonnegative R A P).d (n+1) n
        ((relativeCoefficientComponent R A P (n+1)).hom z) := by
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul a q =>
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((projection (chainFunctor ℤ ℤ) P).f (n+1))).mp inferInstance q
    rw [TensorProduct.AlgebraTensorModule.lTensor_tmul,
      relativeCoefficientComponent_projection]
    have hpZ := congrArg (fun f => f c)
      ((projection (chainFunctor ℤ ℤ) P).comm (n+1) n)
    change (nonnegative ℤ ℤ P).d (n+1) n
        ((projection (chainFunctor ℤ ℤ) P).f (n+1) c) =
      (projection (chainFunctor ℤ ℤ) P).f n (boundary ℤ ℤ P.space n c) at hpZ
    rw [hpZ, relativeCoefficientComponent_projection]
    have hpA := congrArg (fun f => f
      (integralTensorChainsEquiv R A P.space (n+1) (a ⊗ₜ[ℤ] c)))
      ((projection (chainFunctor R A) P).comm (n+1) n)
    change (nonnegative R A P).d (n+1) n
        ((projection (chainFunctor R A) P).f (n+1)
          (integralTensorChainsEquiv R A P.space (n+1) (a ⊗ₜ[ℤ] c))) =
      (projection (chainFunctor R A) P).f n
        (boundary R A P.space n
          (integralTensorChainsEquiv R A P.space (n+1) (a ⊗ₜ[ℤ] c))) at hpA
    rw [hpA]
    apply congrArg ((projection (chainFunctor R A) P).f n)
    simpa only [TensorProduct.AlgebraTensorModule.lTensor_tmul] using
      integralTensorChainsEquiv_boundary R A P.space n (a ⊗ₜ[ℤ] c)

/-- This is an isomorphism of actual nonnegative relative chain complexes. -/
def relativeCoefficientIso (P : Pair.{w}) :
    ((integralTensorFunctor R A).mapHomologicalComplex (.down ℕ)).obj
      (nonnegative ℤ ℤ P) ≅ nonnegative R A P :=
  HomologicalComplex.Hom.isoOfComponents (relativeCoefficientComponent R A P)
    (by
      intro i j hij
      have hi : j+1=i := hij
      subst i
      apply ModuleCat.hom_ext
      ext z
      exact (relativeCoefficientComponent_boundary R A P j z).symm)

lemma integralTensorChainsEquiv_map {X Y : TopCat.{w}} (f : X ⟶ Y) (n : ℕ)
    (a : A) (c : Chains ℤ X n) :
    integralTensorChainsEquiv R A Y n
      (a ⊗ₜ[ℤ] (chainMap ℤ ℤ f).f n c) =
      (chainMap R A f).f n (integralTensorChainsEquiv R A X n (a ⊗ₜ[ℤ] c)) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hc hd
  | single s z =>
    simp only [P202.SingularChains.chainMap_single, integralTensorChainsEquiv_tmul_single]

lemma relativeCoefficientIso_natural {P Q : Pair.{w}} (f : P ⟶ Q) :
    ((integralTensorFunctor R A).mapHomologicalComplex (.down ℕ)).map
        (relativeMap (chainFunctor ℤ ℤ) f) ≫ (relativeCoefficientIso R A Q).hom =
      (relativeCoefficientIso R A P).hom ≫ relativeMap (chainFunctor R A) f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  ext z
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simpa only [map_add] using congrArg₂ (· + ·) hz hz'
  | tmul a q =>
    obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective
      ((projection (chainFunctor ℤ ℤ) P).f n)).mp inferInstance q
    change (relativeCoefficientComponent R A Q n).hom
        (a ⊗ₜ[ℤ] (relativeMap (chainFunctor ℤ ℤ) f).f n
          ((projection (chainFunctor ℤ ℤ) P).f n c)) =
      (relativeMap (chainFunctor R A) f).f n
        ((relativeCoefficientComponent R A P n).hom
          (a ⊗ₜ[ℤ] ((projection (chainFunctor ℤ ℤ) P).f n c)))
    have hpZ := congrArg (fun k => k.f n c) (projection_map (chainFunctor ℤ ℤ) f)
    have hpA := congrArg (fun k => k.f n (integralTensorChainsEquiv R A P.space n
        (a ⊗ₜ[ℤ] c))) (projection_map (chainFunctor R A) f)
    change (relativeMap (chainFunctor ℤ ℤ) f).f n
      ((projection (chainFunctor ℤ ℤ) P).f n c) =
      (projection (chainFunctor ℤ ℤ) Q).f n ((chainMap ℤ ℤ f.map).f n c) at hpZ
    change (relativeMap (chainFunctor R A) f).f n
      ((projection (chainFunctor R A) P).f n _) =
      (projection (chainFunctor R A) Q).f n ((chainMap R A f.map).f n _) at hpA
    rw [hpZ, relativeCoefficientComponent_projection,
      relativeCoefficientComponent_projection, hpA, integralTensorChainsEquiv_map]

lemma integralRelative_projective (P : Pair.{w}) (n : ℕ) :
    Projective ((nonnegative ℤ ℤ P).X n) := by
  obtain ⟨b, _⟩ := P202.RelativeSingularChains.quotient_basis ℤ P n
  exact ModuleCat.projective_of_free b

/-- The canonical relative map preserves quasi-isomorphisms under every
coefficient-module change; no flatness hypothesis is needed. -/
lemma relativeMap_quasiIso_of_integral {P Q : Pair.{w}} (f : P ⟶ Q)
    [QuasiIso (relativeMap (chainFunctor ℤ ℤ) f)] :
    QuasiIso (relativeMap (chainFunctor R A) f) := by
  letI : ∀ n, Projective ((nonnegative ℤ ℤ P).X n) := integralRelative_projective P
  letI : ∀ n, Projective ((nonnegative ℤ ℤ Q).X n) := integralRelative_projective Q
  haveI := P202.SpheresDisks.ConcentratedHomology.map_quasiIso_of_projective
    (integralTensorFunctor R A) (relativeMap (chainFunctor ℤ ℤ) f)
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have hn := congrArg (fun k => homologyMap k n) (relativeCoefficientIso_natural R A f)
  rw [homologyMap_comp, homologyMap_comp] at hn
  haveI : IsIso (homologyMap (relativeCoefficientIso R A P).hom n ≫
      homologyMap (relativeMap (chainFunctor R A) f) n) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (homologyMap (relativeCoefficientIso R A P).hom n) _

/-- Excision for arbitrary coefficient modules over a commutative ring. -/
theorem moduleExcision (D : P202Specs.Excision.Data.{w}) (n : ℕ) :
    IsIso (homologyMap (relativeMap (chainFunctor R A) D.inclusion) n) := by
  haveI : QuasiIso (relativeMap (chainFunctor ℤ ℤ) D.inclusion) := by
    rw [quasiIso_iff]
    intro j
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact P202.Excision.isomorphism ℤ D j
  haveI := relativeMap_quasiIso_of_integral R A D.inclusion
  infer_instance

end P202.SimplicialComparison.ModuleCoefficients

namespace P202.SimplicialComparison.ModuleCoefficients
open P202Specs.SingularChains P202Specs.RelativeSingularChains
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

/-- The quotient projection of a good pair is a relative homology isomorphism
with arbitrary module coefficients, including ordinary degree zero. -/
theorem moduleGoodPairQuotient (D : P202Specs.GoodPairQuotient.Data.{w}) (n : ℕ) :
    IsIso (homologyMap (relativeMap (chainFunctor R A)
      (P202Specs.GoodPairQuotient.quotientPairMap D.pair)) n) := by
  haveI : QuasiIso (relativeMap (chainFunctor ℤ ℤ)
      (P202Specs.GoodPairQuotient.quotientPairMap D.pair)) := by
    rw [quasiIso_iff]
    intro j
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact P202.GoodPairQuotient.relative_quotient_isIso_conditional
      P202.Excision.isomorphism P202.Excision.naturality ℤ D j
  haveI := relativeMap_quasiIso_of_integral R A
    (P202Specs.GoodPairQuotient.quotientPairMap D.pair)
  infer_instance

/-- A quotient-pair isomorphism detects the relative comparison for good pairs.
The square is required on the actual quotient projections. -/
theorem moduleRelativeMap_of_quotientPairIso
    (D E : P202Specs.GoodPairQuotient.Data.{w}) (f : D.pair ⟶ E.pair)
    (g : P202Specs.GoodPairQuotient.quotientPair D.pair ⟶
      P202Specs.GoodPairQuotient.quotientPair E.pair) [IsIso g]
    (hsq : f ≫ P202Specs.GoodPairQuotient.quotientPairMap E.pair =
      P202Specs.GoodPairQuotient.quotientPairMap D.pair ≫ g) (n : ℕ) :
    IsIso (homologyMap (relativeMap (chainFunctor R A) f) n) := by
  let F := relativeFunctor (chainFunctor R A) ⋙
    HomologicalComplex.homologyFunctor _ _ n
  haveI : IsIso (F.map (P202Specs.GoodPairQuotient.quotientPairMap D.pair)) :=
    moduleGoodPairQuotient R A D n
  haveI : IsIso (F.map (P202Specs.GoodPairQuotient.quotientPairMap E.pair)) :=
    moduleGoodPairQuotient R A E n
  haveI : IsIso (F.map f ≫
      F.map (P202Specs.GoodPairQuotient.quotientPairMap E.pair)) := by
    rw [← F.map_comp, hsq, F.map_comp]
    infer_instance
  exact IsIso.of_isIso_comp_right (F.map f)
    (F.map (P202Specs.GoodPairQuotient.quotientPairMap E.pair))

end P202.SimplicialComparison.ModuleCoefficients

namespace P202.SimplicialComparison
section ConcentratedComplex
variable {R : Type u} [CommRing R]
/-- A complex concentrated in one degree is canonically the single complex
on that chain group, with a specified coordinate isomorphism. -/
def concentratedComplexIso (C : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ)
    (M : ModuleCat.{v} R) (e : C.X n ≅ M)
    (hC : ∀ q, q ≠ n → IsZero (C.X q)) :
    C ≅ (HomologicalComplex.single (ModuleCat.{v} R) (.down ℕ) n).obj M := by
  let f := HomologicalComplex.mkHomToSingle e.hom (by
    intro i hi
    have hin : i ≠ n := by change n+1=i at hi; omega
    exact (hC i hin).eq_of_src _ _)
  haveI : ∀ q, IsIso (f.f q) := by
    intro q
    by_cases hq : q=n
    · subst q
      dsimp only [f]
      rw [HomologicalComplex.mkHomToSingle_f]
      infer_instance
    · exact (hC q hq).isIso (HomologicalComplex.isZero_single_obj_X
        (.down ℕ) n M q hq) _
  haveI : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

@[simp] theorem concentratedComplexIso_hom_self
    (C : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (M : ModuleCat.{v} R)
    (e : C.X n ≅ M) (hC : ∀ q, q ≠ n → IsZero (C.X q)) :
    ((concentratedComplexIso C n M e hC).hom.f n) =
      e.hom ≫ (HomologicalComplex.singleObjXSelf (.down ℕ) n M).inv := by
  simp only [concentratedComplexIso, asIso_hom, HomologicalComplex.mkHomToSingle_f]
end ConcentratedComplex

section SkeletalSingle
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
/-- Consecutive Δ-skeleta have the single complex on their original top
simplex labels; the coordinates are the actual quotient simplex classes. -/
def deltaSkeletalSingleIso (D : DeltaComplex.{w}) (n : ℕ) :
    deltaSkeletalRelative R A D n ≅
      (HomologicalComplex.single (ModuleCat.{max v w} R) (.down ℕ) n).obj
        (ModuleCat.of R (D.Simplex n →₀ A)) :=
  concentratedComplexIso (deltaSkeletalRelative R A D n) n _
    (deltaSkeletalTopEquiv R A D n).toModuleIso
    (deltaSkeletalRelative_isZero R A D n)

@[simp] theorem deltaSkeletalSingleIso_hom_generator (D : DeltaComplex.{w}) (n : ℕ)
    (s : D.Simplex n) (a : A) :
    (HomologicalComplex.singleObjXSelf (.down ℕ) n
      (ModuleCat.of R (D.Simplex n →₀ A))).hom
    (((deltaSkeletalSingleIso R A D n).hom.f n).hom
      (((deltaSelection R A (deltaSkeletonLT D (n+1)).asComplex
        (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n)).module n).mkQ
          (Finsupp.single ⟨s,Nat.lt_succ_self n⟩ a))) = Finsupp.single s a := by
  rw [deltaSkeletalSingleIso, concentratedComplexIso_hom_self]
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  change deltaSkeletalTopEquiv R A D n _ = Finsupp.single s a
  rw [← deltaSkeletalTopEquiv_symm_single, LinearEquiv.apply_symm_apply]
end SkeletalSingle

section
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
/-- Absolute comparison on the ambient Δ-complex and its intrinsic
subcomplex implies comparison for this particular subcomplex pair. -/
theorem deltaRelativeComparison_of_subcomplex (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) (F : DeltaComparisonData R A D B)
    (G : DeltaComparisonData R A B.asComplex (DeltaSubcomplex.empty _))
    (hG : ∀ q : ℕ, IsIso (homologyMap G.absolute q))
    (hFabs : ∀ q : ℕ, IsIso (homologyMap F.absolute q)) (q : ℕ) :
    IsIso (homologyMap F.relative q) := by
  let S := deltaSelection R A D B
  let T := singularSelection R A (TopCat.of D.Realization) B.carrier
  have hpres : ∀ n x, x ∈ S.module n → (F.absolute.f n).hom x ∈ T.module n := by
    intro n x hx
    rw [F.absolute_formula]
    exact P202.SimplicialChains.deltaAffine_preserves R A D B n x hx
  have hrel : S.quotientMap T F.absolute hpres = F.relative := by
    symm
    apply quotientMap_eq_of_formula R S T F.absolute hpres
    intro n x
    change (F.relative.f n).hom (((deltaSelection R A D B).module n).mkQ x) =
      ((singularSelection R A (TopCat.of D.Realization) B.carrier).module n).mkQ
        ((F.absolute.f n).hom x)
    rw [F.relative_formula,F.absolute_formula]
    rfl
  rw [← hrel]
  exact selectionQuotientComparison_isIso S T F.absolute hpres
    (deltaSelectedComparison_isIso R A D B F hpres G hG) hFabs q

/-- Every pair of zero-dimensional Δ-complexes has its canonical relative
comparison for arbitrary modules and arbitrary vertex-label sets. -/
theorem deltaZeroDimensional_relativeComparison (D : DeltaComplex.{w})
    (hD : ∀ n : ℕ, n ≠ 0 → IsEmpty (D.Simplex n))
    (B : DeltaSubcomplex D) (F : DeltaComparisonData R A D B) (q : ℕ) :
    IsIso (homologyMap F.relative q) := by
  obtain ⟨G⟩ := deltaComparisonData_nonempty R A B.asComplex (DeltaSubcomplex.empty _)
  have hB : ∀ n : ℕ, n ≠ 0 → IsEmpty (B.asComplex.Simplex n) := by
    intro n hn
    exact ⟨fun s => (hD n hn).false s.1⟩
  exact deltaRelativeComparison_of_subcomplex R A D B F G
    (deltaZeroDimensional_absoluteComparison R A B.asComplex hB (DeltaSubcomplex.empty _) G)
    (deltaZeroDimensional_absoluteComparison R A D hD B F) q

/-- Selecting every Δ-simplex gives the whole realization, including when
there are no simplex labels at all. -/
theorem deltaSubcomplex_carrier_eq_univ_of_all_selected (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) (hB : ∀ n (s : D.Simplex n), s ∈ B.selected n) :
    B.carrier = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨⟨n,s,t⟩,rfl⟩ := Quotient.mk_surjective x
  exact ⟨n,s,hB n s,t,rfl⟩

/-- The relative Δ-chain object vanishes degreewise when all labels have
been selected. -/
theorem deltaRelative_isZero_of_all_selected (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) (hB : ∀ n (s : D.Simplex n), s ∈ B.selected n) (q : ℕ) :
    IsZero ((deltaRelativeComplex R A D B).X q) := by
  have htop : (deltaSelection R A D B).module q = ⊤ := by
    change Finsupp.supported A R (B.selected q) = ⊤
    rw [Set.eq_univ_of_forall (hB q), Finsupp.supported_univ]
  change IsZero (ModuleCat.of R (DeltaChains A D q ⧸ (deltaSelection R A D B).module q))
  rw [htop]
  exact ModuleCat.isZero_of_subsingleton _

/-- The singular relative chain object vanishes degreewise when all labels
of the ambient Δ-complex have been selected. -/
theorem deltaSingularRelative_isZero_of_all_selected (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) (hB : ∀ n (s : D.Simplex n), s ∈ B.selected n) (q : ℕ) :
    IsZero ((singularRelativeComplex R A (TopCat.of D.Realization) B.carrier).X q) := by
  have htop : (singularSelection R A (TopCat.of D.Realization) B.carrier).module q = ⊤ := by
    change Finsupp.supported A R {s | ∀ t,
      simplexEquiv (TopCat.of D.Realization) q s t ∈ B.carrier} = ⊤
    rw [deltaSubcomplex_carrier_eq_univ_of_all_selected D B hB]
    simp only [Set.mem_univ, forall_const, Set.ofPred_true, Finsupp.supported_univ]
  change IsZero (ModuleCat.of R (Chains A (TopCat.of D.Realization) q ⧸
    (singularSelection R A (TopCat.of D.Realization) B.carrier).module q))
  rw [htop]
  exact ModuleCat.isZero_of_subsingleton _

/-- Canonical comparison for the full subcomplex pair, in every degree and
with every coefficient module. Both actual relative complexes vanish. -/
theorem deltaRelativeComparison_of_all_selected (D : DeltaComplex.{w})
    (B : DeltaSubcomplex D) (hB : ∀ n (s : D.Simplex n), s ∈ B.selected n)
    (F : DeltaComparisonData R A D B) (q : ℕ) :
    IsIso (homologyMap F.relative q) :=
  (HomologicalComplex.ExactAt.of_isZero
    (deltaRelative_isZero_of_all_selected R A D B hB q)).isZero_homology.isIso
    (HomologicalComplex.ExactAt.of_isZero
      (deltaSingularRelative_isZero_of_all_selected R A D B hB q)).isZero_homology
    (homologyMap F.relative q)

/-- If a complex has no simplex labels at or above n, its lower-skeleton
pair is the full pair and hence has the canonical relative comparison. -/
theorem deltaBoundedRelativeComparison_of_no_top_labels (D : DeltaComplex.{w})
    (n : ℕ) (hD : ∀ k, n ≤ k → IsEmpty (D.Simplex k))
    (F : DeltaComparisonData R A D (deltaSkeletonLT D n)) (q : ℕ) :
    IsIso (homologyMap F.relative q) := by
  apply deltaRelativeComparison_of_all_selected R A D (deltaSkeletonLT D n) ?_ F q
  intro k s
  change k < n
  by_contra hk
  exact (hD k (by omega)).false s

/-- The bounded skeletal pair needs no positive-dimensional cell computation
when the top simplex-label type is empty. -/
theorem deltaBoundedRelativeComparison_of_empty_top (D : DeltaComplex.{w})
    (n : ℕ) (hD : ∀ k, n+1 ≤ k → IsEmpty (D.Simplex k))
    (htop : IsEmpty (D.Simplex n))
    (F : DeltaComparisonData R A D (deltaSkeletonLT D n)) (q : ℕ) :
    IsIso (homologyMap F.relative q) := by
  apply deltaBoundedRelativeComparison_of_no_top_labels R A D n ?_ F q
  intro k hk
  by_cases hkn : k = n
  · exact hkn ▸ htop
  · exact hD k (by omega)

end
section
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
section ConstantSigmaRelative
universe z'
variable (I : Type w) (X : TopCat.{z'}) (B : Set X)

/-- Coefficient conversion identifies the actual supported relative quotient
complexes, for every subspace and every index set. -/
def constantSigmaRelativeIso :
    singularRelativeComplex R A (TopCat.of (Σ _ : I, X)) {p | p.2 ∈ B} ≅
      singularRelativeComplex R (I →₀ A) X B :=
  selectionQuotientIso
    (singularSelection R A (TopCat.of (Σ _ : I, X)) {p | p.2 ∈ B})
    (singularSelection R (I →₀ A) X B)
    (constantSigmaChainIso R A I X)
    (constantSigmaChainsEquiv_preserves R A I X B)
    (constantSigmaChainsEquiv_symm_preserves R A I X B)

@[simp] theorem constantSigmaRelativeIso_hom_mk (q : ℕ)
    (c : Chains A (TopCat.of (Σ _ : I, X)) q) :
    ((constantSigmaRelativeIso R A I X B).hom.f q).hom
        (((singularSelection R A (TopCat.of (Σ _ : I, X)) {p | p.2 ∈ B}).module q).mkQ c) =
      ((singularSelection R (I →₀ A) X B).module q).mkQ
        (constantSigmaChainsEquiv R A I X q c) := rfl

@[simp] theorem constantSigmaRelativeIso_inv_mk (q : ℕ)
    (c : Chains (I →₀ A) X q) :
    ((constantSigmaRelativeIso R A I X B).inv.f q).hom
        (((singularSelection R (I →₀ A) X B).module q).mkQ c) =
      ((singularSelection R A (TopCat.of (Σ _ : I, X)) {p | p.2 ∈ B}).module q).mkQ
        ((constantSigmaChainsEquiv R A I X q).symm c) := rfl

end ConstantSigmaRelative

section ConstantSigmaAffine
open P202Specs.SpheresDisks P202.SpheresDisks
open P202.SpheresDisks.ConcentratedHomology P202.SpheresDisks.IntegralCoefficients
variable (I : Type w)

/-- The actual affine simplices in all disjoint copies of the standard simplex,
as a map out of the concentrated module of coefficients on the copies. -/
def constantSigmaAffineComparison (n : ℕ) :
    (single (ModuleCat.{max v w} R) (.down ℕ) n).obj (ModuleCat.of R (I →₀ A)) ⟶
      singularRelativeComplex R A (TopCat.of (Σ _ : I, simplex n))
        {p | p.2 ∈ (simplexPair n).subspace} :=
  fromSingleCycles (P202Specs.RelativeSingularChains.nonnegative R (I →₀ A) (simplexPair n)) n
      (nonnegativeAffineCycleMap R (I →₀ A) n) ≫
    (singularRelativeIso R (I →₀ A) (simplex n) (simplexPair n).subspace).hom ≫
    (constantSigmaRelativeIso R A I (simplex n) (simplexPair n).subspace).inv

/-- The genuine integral affine-generator calculation, transported to arbitrary
module coefficients, proves this is a quasi-isomorphism. -/
theorem constantSigmaAffineComparison_quasiIso (n : ℕ) :
    QuasiIso (constantSigmaAffineComparison R A I n) := by
  have hb : Function.Bijective (affineClassLinear R (I →₀ A) n) :=
    affineClassLinear_bijective_of_integral R (I →₀ A) n
      (P202.SpheresDisks.SimplexOrientation.affineClassLinear_ring_bijective ℤ n)
  haveI := nonnegativeAffine_quasiIso R (I →₀ A) n hb
  dsimp only [constantSigmaAffineComparison]
  infer_instance

/-- In its unique nonzero source degree the comparison takes precisely the
coefficient on one summand to that summand's oriented affine simplex. -/
theorem constantSigmaAffineComparison_generator (n : ℕ) (i : I) (a : A) :
    ((singleObjXSelf (.down ℕ) n (ModuleCat.of R (I →₀ A))).inv ≫
        (constantSigmaAffineComparison R A I n).f n).hom (Finsupp.single i a) =
      ((singularSelection R A (TopCat.of (Σ _ : I, simplex n))
        {p | p.2 ∈ (simplexPair n).subspace}).module n).mkQ
          (Finsupp.single (constantSigmaSimplex I (simplex n) n i (affineSimplex n)) a) := by
  have hf :
      (singleObjXSelf (.down ℕ) n (ModuleCat.of R (I →₀ A))).inv ≫
          (constantSigmaAffineComparison R A I n).f n =
        ModuleCat.ofHom (nonnegativeAffineLinear R (I →₀ A) n) ≫
          (singularRelativeIso R (I →₀ A) (simplex n) (simplexPair n).subspace).hom.f n ≫
          (constantSigmaRelativeIso R A I (simplex n) (simplexPair n).subspace).inv.f n := by
    dsimp only [constantSigmaAffineComparison]
    simp only [HomologicalComplex.comp_f, fromSingleCycles, mkHomFromSingle_f,
      Category.assoc, Iso.inv_hom_id_assoc, nonnegativeAffineCycleMap_i]
  rw [hf]
  change ((constantSigmaRelativeIso R A I (simplex n) (simplexPair n).subspace).inv.f n).hom
    (singularRelativeDegreeEquiv R (I →₀ A) (simplex n) (simplexPair n).subspace n
      (((P202Specs.RelativeSingularChains.projection (chainFunctor R (I →₀ A))
        (simplexPair n)).f n).hom (affineChain (I →₀ A) n (Finsupp.single i a)))) = _
  erw [singularRelativeDegreeEquiv_projection]
  rw [constantSigmaRelativeIso_inv_mk]
  change ((singularSelection R A (TopCat.of (Σ _ : I, simplex n))
    {p | p.2 ∈ (simplexPair n).subspace}).module n).mkQ
      ((constantSigmaChainsEquiv R A I (simplex n) n).symm
        (Finsupp.single (affineSimplex n) (Finsupp.single i a))) = _
  rw [constantSigmaChainsEquiv_symm_single]

end ConstantSigmaAffine
end

end P202.SimplicialComparison

open _root_.Topology
open P202Specs.RelativeSingularChains P202Specs.GoodPairQuotient
namespace P202.SimplicialComparison
namespace SkeletalQuotient

def sourcePair (D : DeltaComplex.{w}) (n : ℕ) : Pair.{w} :=
  ⟨TopCat.of (Σ _ : D.Simplex n, StandardSimplex n),
    {p | ∃ i, p.2.weights i = 0}⟩

def characteristicMap (D : DeltaComplex.{w}) (n : ℕ) :
    sourcePair D n ⟶ deltaSkeletalPair D n where
  map := TopCat.ofHom ⟨fun p => deltaSkeletalChart D n p.1 p.2, by
    apply continuous_sigma
    intro s
    exact (deltaSkeletalChart D n s).continuous⟩
  mapsTo := fun p hp => deltaSkeletalChart_boundary D n p.1 p.2 hp

lemma boundary_iff (n : ℕ) (t : StandardSimplex n) :
    (∃ i, t.weights i = 0) ↔ t ∉ standardSimplexInterior n := by
  constructor
  · rintro ⟨i,hi⟩ ht
    exact (ht i).ne' hi
  · intro ht
    classical
    change ¬ (∀ i, 0 < t.weights i) at ht
    push Not at ht
    obtain ⟨i,hi⟩ := ht
    exact ⟨i, le_antisymm hi (t.weights_nonneg i)⟩

lemma characteristic_preimage_lower (D : DeltaComplex.{w}) (n : ℕ)
    (p : (sourcePair D n).space) :
    (characteristicMap D n).map p ∈ (deltaSkeletalPair D n).subspace ↔
      p ∈ (sourcePair D n).subspace := by
  constructor
  · intro hp
    apply (boundary_iff n p.2).mpr
    intro hint
    obtain ⟨m,r,hr,t,he⟩ := hp
    obtain ⟨k,hkm,a,z,hz,hzt⟩ := P202.Topology.DeltaSupport.exists_interior_face t
    have he' : (deltaSkeletonLT D (n+1)).asComplex.simplexChart k
        ((deltaSkeletonLT D (n+1)).asComplex.face a r) z =
        (deltaSkeletonLT D (n+1)).asComplex.simplexChart n
          ⟨p.1,Nat.lt_succ_self n⟩ p.2 :=
      (P202.Topology.deltaFaceCompatibility _ a r z).trans
        ((congrArg ((deltaSkeletonLT D (n+1)).asComplex.simplexChart m r) hzt).trans he)
    have hh := P202.Topology.DeltaSupport.interior_quotient_unique _ hz hint he'
    have hkn : k=n := congrArg Sigma.fst hh
    change m<n at hr
    omega
  · intro hp
    exact deltaSkeletalChart_boundary D n p.1 p.2 hp

lemma characteristic_injective_off_lower (D : DeltaComplex.{w}) (n : ℕ)
    (p q : (sourcePair D n).space)
    (hp : p ∉ (sourcePair D n).subspace) (hq : q ∉ (sourcePair D n).subspace)
    (he : (characteristicMap D n).map p = (characteristicMap D n).map q) : p=q := by
  have hh := P202.Topology.DeltaSupport.interior_quotient_unique
    (deltaSkeletonLT D (n+1)).asComplex (by simpa using (boundary_iff n p.2).not.mp hp)
      (by simpa using (boundary_iff n q.2).not.mp hq) he
  have hs : p.1=q.1 := congrArg Subtype.val (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hh).2)).1
  have ht : p.2=q.2 := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj hh).2)).2
  exact Sigma.ext hs (heq_of_eq ht)

lemma source_boundary_nonempty (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] : (sourcePair D n).subspace.Nonempty := by
  classical
  let s : D.Simplex n := Classical.choice inferInstance
  refine ⟨⟨s,Convexity.StdSimplex.single (0 : Fin (n+1))⟩, ⟨⟨1, by omega⟩, ?_⟩⟩
  simp [Convexity.StdSimplex.weights_single, Finsupp.single_eq_of_ne]

lemma collapse_respects (D : DeltaComplex.{w}) (n : ℕ)
    (x y : (sourcePair D n).space) (h : (collapseSetoid (sourcePair D n)).r x y) :
    quotientProjection (deltaSkeletalPair D n) ((characteristicMap D n).map x) =
      quotientProjection (deltaSkeletalPair D n) ((characteristicMap D n).map y) := by
  apply Quotient.sound
  rcases h with rfl | ⟨hx,hy⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨(characteristicMap D n).mapsTo hx, (characteristicMap D n).mapsTo hy⟩

def quotientMap (D : DeltaComplex.{w}) (n : ℕ) :
    C(quotientSpace (sourcePair D n), quotientSpace (deltaSkeletalPair D n)) :=
  ⟨Quotient.lift
    (fun x => quotientProjection (deltaSkeletalPair D n) ((characteristicMap D n).map x))
    (collapse_respects D n),
    Continuous.quotient_lift
      ((quotientProjection (deltaSkeletalPair D n)).hom.continuous.comp
        (characteristicMap D n).map.hom.continuous) (collapse_respects D n)⟩

lemma quotientMap_injective (D : DeltaComplex.{w}) (n : ℕ) :
    Function.Injective (quotientMap D n) := by
  intro x y h
  induction x using Quotient.inductionOn with | h p =>
    induction y using Quotient.inductionOn with | h q =>
      apply Quotient.sound
      have h' := Quotient.exact h
      rcases h' with he | ⟨hp,hq⟩
      · by_cases hp : p ∈ (sourcePair D n).subspace
        · right
          refine ⟨hp, (characteristic_preimage_lower D n q).mp ?_⟩
          rw [← he]
          exact (characteristicMap D n).mapsTo hp
        · by_cases hq : q ∈ (sourcePair D n).subspace
          · have : p ∈ (sourcePair D n).subspace :=
              (characteristic_preimage_lower D n p).mp (he ▸ (characteristicMap D n).mapsTo hq)
            exact (hp this).elim
          · left
            exact characteristic_injective_off_lower D n p q hp hq he
      · exact Or.inr ⟨(characteristic_preimage_lower D n p).mp hp,
          (characteristic_preimage_lower D n q).mp hq⟩

lemma quotientMap_surjective (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] : Function.Surjective (quotientMap D n) := by
  obtain ⟨p0,hp0⟩ := source_boundary_nonempty D n hn
  intro y
  induction y using Quotient.inductionOn with | h y =>
    obtain ⟨⟨m,s,t⟩, rfl⟩ := Quotient.mk_surjective y
    have hm : m<n+1 := s.property
    by_cases hmn : m=n
    · subst m
      exact ⟨Quotient.mk _ ⟨s.val,t⟩, rfl⟩
    · refine ⟨Quotient.mk _ p0, ?_⟩
      apply Quotient.sound
      exact Or.inr ⟨(characteristicMap D n).mapsTo hp0, ⟨m,s,by change m<n; omega,t,rfl⟩⟩

lemma characteristicQuotient_isQuotientMap (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] :
    IsQuotientMap (fun p : (sourcePair D n).space =>
      quotientProjection (deltaSkeletalPair D n) ((characteristicMap D n).map p)) := by
  obtain ⟨p0,hp0⟩ := source_boundary_nonempty D n hn
  constructor
  · apply IsCoinducing.of_isOpen_preimage_iff_isOpen
    intro U
    constructor
    · intro hU
      apply (P202.GoodPairQuotient.quotientProjection_isQuotientMap
        (deltaSkeletalPair D n)).isOpen_preimage.mp
      apply (P202.Topology.deltaProjectionQuotient
        (deltaSkeletonLT D (n+1)).asComplex).isOpen_preimage.mp
      apply isOpen_sigma_iff.mpr
      intro m
      apply isOpen_sigma_iff.mpr
      intro s
      by_cases hm : m=n
      · subst m
        exact hU.preimage (continuous_sigmaMk (i := s.val))
      · have hmn : m<n := by have hh := s.property; change m<n+1 at hh; omega
        have hc : (fun t : StandardSimplex m =>
            quotientProjection (deltaSkeletalPair D n)
              ((deltaSkeletonLT D (n+1)).asComplex.simplexChart m s t)) =
            (fun _ => quotientProjection (deltaSkeletalPair D n)
              ((characteristicMap D n).map p0)) := by
          funext t
          apply Quotient.sound
          exact Or.inr ⟨⟨m,s,hmn,t,rfl⟩, (characteristicMap D n).mapsTo hp0⟩
        change IsOpen ((fun t : StandardSimplex m =>
          quotientProjection (deltaSkeletalPair D n)
            ((deltaSkeletonLT D (n+1)).asComplex.simplexChart m s t)) ⁻¹' U)
        rw [hc]
        by_cases hb : quotientProjection (deltaSkeletalPair D n)
            ((characteristicMap D n).map p0) ∈ U <;> simp [hb]
    · intro hU
      exact hU.preimage ((quotientProjection (deltaSkeletalPair D n)).hom.continuous.comp
        (characteristicMap D n).map.hom.continuous)
  · intro y
    obtain ⟨z,hz⟩ := quotientMap_surjective D n hn y
    obtain ⟨p,rfl⟩ := Quotient.mk_surjective z
    exact ⟨p,hz⟩

lemma quotientMap_isQuotientMap (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] : IsQuotientMap (quotientMap D n) := by
  exact IsQuotientMap.of_comp continuous_quot_mk (quotientMap D n).continuous
    (characteristicQuotient_isQuotientMap D n hn)

/-- Collapsing the lower skeleton retains exactly the top simplex quotients,
with every boundary point giving the same basepoint. -/
def quotientHomeomorph (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] :
    quotientSpace (sourcePair D n) ≃ₜ quotientSpace (deltaSkeletalPair D n) :=
  (Equiv.ofBijective (quotientMap D n)
    ⟨quotientMap_injective D n, quotientMap_surjective D n hn⟩).toHomeomorph
      (fun _ => (quotientMap_isQuotientMap D n hn).isOpen_preimage)

@[simp] lemma quotientHomeomorph_projection (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] (p : (sourcePair D n).space) :
    quotientHomeomorph D n hn (quotientProjection (sourcePair D n) p) =
      quotientProjection (deltaSkeletalPair D n) ((characteristicMap D n).map p) := rfl

lemma quotientHomeomorph_subspace (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)]
    (x : quotientSpace (sourcePair D n)) :
    x ∈ (quotientPair (sourcePair D n)).subspace ↔
      quotientHomeomorph D n hn x ∈ (quotientPair (deltaSkeletalPair D n)).subspace := by
  induction x using Quotient.inductionOn with | h p =>
    have hP := congrArg (fun S => p ∈ S)
      (P202.GoodPairQuotient.quotient_preimage_subspace (sourcePair D n))
    have hQ := congrArg (fun S => (characteristicMap D n).map p ∈ S)
      (P202.GoodPairQuotient.quotient_preimage_subspace (deltaSkeletalPair D n))
    change (quotientProjection (sourcePair D n) p ∈
      (quotientPair (sourcePair D n)).subspace) ↔
        quotientProjection (deltaSkeletalPair D n) ((characteristicMap D n).map p) ∈
          (quotientPair (deltaSkeletalPair D n)).subspace
    exact (Iff.of_eq hP).trans ((characteristic_preimage_lower D n p).symm.trans
      (Iff.of_eq hQ).symm)

def quotientPairIso (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] :
    quotientPair (sourcePair D n) ≅ quotientPair (deltaSkeletalPair D n) :=
  P202.GoodPairQuotient.pairIsoOfHomeomorph _ _ (quotientHomeomorph D n hn)
    (quotientHomeomorph_subspace D n hn)

lemma quotientPairIso_square (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] :
    characteristicMap D n ≫ quotientPairMap (deltaSkeletalPair D n) =
      quotientPairMap (sourcePair D n) ≫ (quotientPairIso D n hn).hom := by
  apply PairMap.ext
  rfl

/-- A face-closed Delta subcomplex is a cellular subcomplex of the checked
CW realization, with exactly its prescribed carrier. -/
lemma deltaCarrier_hasCWSubcomplex (D : DeltaComplex.{w}) (B : DeltaSubcomplex D) :
    ∃ C : CWStructure D.Realization, ∃ CB : @P202.Cellular.Subcomplex D.Realization
      D.realizationTopology C, @P202.Cellular.Subcomplex.carrier _ _ C CB = B.carrier := by
  classical
  obtain ⟨C,indices,hcharts⟩ := P202.Topology.deltaRealizationCW D
  letI : CWStructure D.Realization := C
  let cells : ∀ n, Set (Cell D.Realization n) := fun n => {c | indices n c ∈ B.selected n}
  have hc : (⋃ n, ⋃ c : cells n, openCell D.Realization n c.val) = B.carrier := by
    ext x
    constructor
    · intro hx
      obtain ⟨n,hx⟩ := Set.mem_iUnion.mp hx
      obtain ⟨c,hx⟩ := Set.mem_iUnion.mp hx
      rw [(hcharts n c.val).1] at hx
      obtain ⟨t,ht,rfl⟩ := hx
      exact ⟨n,indices n c.val,c.property,t,rfl⟩
    · rintro ⟨n,s,hs,t,rfl⟩
      obtain ⟨m,_,a,u,hu,htu⟩ := P202.Topology.DeltaSupport.exists_interior_face t
      let c : cells m := ⟨(indices m).symm (D.face a s), by
        change indices m ((indices m).symm (D.face a s)) ∈ B.selected m
        simpa using B.face_closed a s hs⟩
      apply Set.mem_iUnion.mpr
      refine ⟨m,Set.mem_iUnion.mpr ⟨c,?_⟩⟩
      rw [(hcharts m c.val).1]
      refine ⟨u,hu,?_⟩
      simp only [c, Equiv.apply_symm_apply]
      exact (P202.Topology.deltaFaceCompatibility D a s u).trans
        (congrArg (D.simplexChart n s) htu)
  have hclosed : IsClosed B.carrier := by
    rw [← deltaSubcomplexRealization_range D B]
    exact (deltaSubcomplexRealization_isClosedEmbedding D B).isClosed_range
  let CB : P202.Cellular.Subcomplex D.Realization := {
    cells := cells
    contains_closures := by
      intro n c hcsel
      rw [hc]
      apply closure_minimal _ hclosed
      intro x hx
      rw [← hc]
      exact Set.mem_iUnion.mpr ⟨n,Set.mem_iUnion.mpr ⟨⟨c,hcsel⟩,hx⟩⟩ }
  exact ⟨C,CB,hc⟩


lemma deltaCarrier_hasNeighborhood (D : DeltaComplex.{w}) (B : DeltaSubcomplex D) :
    ∃ W : Set D.Realization, IsOpen W ∧ StrongDeformationRetracts B.carrier W := by
  obtain ⟨C,CB,hCB⟩ := deltaCarrier_hasCWSubcomplex D B
  letI : CWStructure D.Realization := C
  obtain ⟨W,hW,hret⟩ := P202.Topology.subcomplexNeighborhood CB
  exact ⟨W,hW,hCB ▸ hret⟩

/-- The source's neighborhood theorem gives good-pair data for every nonempty
face-closed Delta carrier without a finiteness condition. -/
def deltaCarrierGoodData (D : DeltaComplex.{w}) (B : DeltaSubcomplex D)
    (hne : B.carrier.Nonempty) : P202Specs.GoodPairQuotient.Data.{w} := by
  classical
  let W := Classical.choose (deltaCarrier_hasNeighborhood D B)
  have hW : IsOpen W := (Classical.choose_spec (deltaCarrier_hasNeighborhood D B)).1
  have hret : StrongDeformationRetracts B.carrier W :=
    (Classical.choose_spec (deltaCarrier_hasNeighborhood D B)).2
  let H := Classical.choose hret.2
  have hH := Classical.choose_spec hret.2
  exact {
    pair := ⟨TopCat.of D.Realization,B.carrier⟩
    nonempty := hne
    closed := by
      rw [← deltaSubcomplexRealization_range D B]
      exact (deltaSubcomplexRealization_isClosedEmbedding D B).isClosed_range
    neighborhood := W
    open_neighborhood := hW
    subset_neighborhood := hret.1
    deformation := H.comp ⟨Prod.swap,continuous_swap⟩
    at_zero := hH.1
    at_one := hH.2.1
    fixes := by intro t x hx; exact hH.2.2 x t hx }

@[simp] lemma deltaCarrierGoodData_pair (D : DeltaComplex.{w}) (B : DeltaSubcomplex D)
    (hne : B.carrier.Nonempty) :
    (deltaCarrierGoodData D B hne).pair = ⟨TopCat.of D.Realization,B.carrier⟩ := rfl

/-- Good-pair data are preserved by a homeomorphism of the specified pairs. -/
def transportGoodData (d : P202Specs.GoodPairQuotient.Data.{w}) (Q : Pair.{w})
    (e : d.pair.space ≃ₜ Q.space)
    (he : ∀ x, x ∈ d.pair.subspace ↔ e x ∈ Q.subspace) :
    P202Specs.GoodPairQuotient.Data.{w} := by
  let ew := e.image d.neighborhood
  exact {
    pair := Q
    nonempty := by
      obtain ⟨a,ha⟩ := d.nonempty
      exact ⟨e a,(he a).mp ha⟩
    closed := by
      have hh : e '' d.pair.subspace = Q.subspace := by
        ext y
        constructor
        · rintro ⟨x,hx,rfl⟩; exact (he x).mp hx
        · intro hy; exact ⟨e.symm y,(he (e.symm y)).mpr (by simpa using hy),by simp⟩
      exact hh ▸ e.isClosedMap _ d.closed
    neighborhood := e '' d.neighborhood
    open_neighborhood := e.isOpenMap _ d.open_neighborhood
    subset_neighborhood := by
      intro y hy
      exact ⟨e.symm y,d.subset_neighborhood ((he (e.symm y)).mpr (by simpa using hy)),by simp⟩
    deformation := ⟨fun tx => ew (d.deformation (tx.1,ew.symm tx.2)), by fun_prop⟩
    at_zero := by intro x; change ew (d.deformation (0,ew.symm x)) = x; rw [d.at_zero]; simp
    at_one := by
      intro x
      exact (he _).mp (d.at_one (ew.symm x))
    fixes := by
      intro t x hx
      change ew (d.deformation (t,ew.symm x)) = x
      have hh : (ew.symm x).val ∈ d.pair.subspace := by
        apply (he _).mpr
        have hew : e (ew.symm x).val = x.val := congrArg Subtype.val (ew.apply_symm_apply x)
        rw [hew]
        exact hx
      rw [d.fixes t (ew.symm x) hh]
      simp }

@[simp] lemma transportGoodData_pair (d : P202Specs.GoodPairQuotient.Data.{w}) (Q : Pair.{w})
    (e : d.pair.space ≃ₜ Q.space)
    (he : ∀ x, x ∈ d.pair.subspace ↔ e x ∈ Q.subspace) :
    (transportGoodData d Q e he).pair = Q := rfl

def targetGoodData (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] : P202Specs.GoodPairQuotient.Data.{w} :=
  deltaCarrierGoodData (deltaSkeletonLT D (n+1)).asComplex
    (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n) (by
      obtain ⟨p,hp⟩ := source_boundary_nonempty D n hn
      exact ⟨(characteristicMap D n).map p,(characteristicMap D n).mapsTo hp⟩)

@[simp] lemma targetGoodData_pair (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] :
    (targetGoodData D n hn).pair = deltaSkeletalPair D n := rfl

/-- Disjoint full ordered simplices, retaining the top-cell labels. -/
def sourceDelta (I : Type w) (n : ℕ) : DeltaComplex.{w} where
  Simplex m := I × (Fin (m+1) ↪o Fin (n+1))
  face a s := (s.1,a.trans s.2)
  face_id := by intros; rfl
  face_comp := by intros; rfl

def sourceEvaluation (I : Type w) (n : ℕ) :
    C((sourceDelta I n).Realization, Σ _ : I, StandardSimplex n) := by
  let raw : (sourceDelta I n).SimplexSum → Σ _ : I, StandardSimplex n :=
    fun p => ⟨p.2.1.1,orderedAffineFace p.2.1.2 p.2.2⟩
  have hraw : ∀ x y, ((sourceDelta I n).faceSetoid).r x y → raw x = raw y := by
    intro x y h
    induction h with
    | rel x y h =>
      cases h with
      | face a s t =>
        change (⟨s.1,orderedAffineFace (a.trans s.2) t⟩ : Σ _ : I,StandardSimplex n) =
          ⟨s.1,orderedAffineFace s.2 (orderedAffineFace a t)⟩
        exact congrArg (fun z : StandardSimplex n => (⟨s.1,z⟩ : Σ _ : I,StandardSimplex n))
          (Convexity.StdSimplex.map_map t a s.2).symm
    | refl => rfl
    | symm x y h ih => exact ih.symm
    | trans x y z h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  exact ⟨Quotient.lift raw hraw,Continuous.quotient_lift (by
    apply continuous_sigma
    intro m
    apply continuous_sigma
    intro s
    change Continuous (fun t => (Sigma.mk s.1 (orderedAffineFace s.2 t) : Σ _ : I,StandardSimplex n))
    exact (continuous_sigmaMk (i := s.1)).comp (Convexity.StdSimplex.continuous_map ℝ s.2)) hraw⟩

def sourceTopChart (I : Type w) (n : ℕ) :
    C((Σ _ : I, StandardSimplex n),(sourceDelta I n).Realization) :=
  ⟨fun p => (sourceDelta I n).simplexChart n (p.1,OrderEmbedding.id _) p.2,
    by
      apply continuous_sigma
      intro i
      exact P202.Topology.deltaChartContinuous (sourceDelta I n) n (i,OrderEmbedding.id _)⟩

def sourceHomeomorph (I : Type w) (n : ℕ) :
    (sourceDelta I n).Realization ≃ₜ (Σ _ : I, StandardSimplex n) where
  toFun := sourceEvaluation I n
  invFun := sourceTopChart I n
  continuous_toFun := (sourceEvaluation I n).continuous
  continuous_invFun := (sourceTopChart I n).continuous
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with | h p =>
      obtain ⟨m,⟨i,a⟩,t⟩ := p
      change (sourceDelta I n).simplexChart n (i,OrderEmbedding.id _) (orderedAffineFace a t) =
        (sourceDelta I n).simplexChart m (i,a) t
      exact (P202.Topology.deltaFaceCompatibility (sourceDelta I n) a
        (i,OrderEmbedding.id _) t).symm
  right_inv := by
    rintro ⟨i,t⟩
    change (⟨i,orderedAffineFace (OrderEmbedding.id _) t⟩ : Σ _ : I,StandardSimplex n) = ⟨i,t⟩
    exact congrArg (fun z : StandardSimplex n => (⟨i,z⟩ : Σ _ : I,StandardSimplex n))
      (Convexity.StdSimplex.map_id t)

lemma sourceHomeomorph_chart (I : Type w) (n m : ℕ)
    (s : (sourceDelta I n).Simplex m) (t : StandardSimplex m) :
    sourceHomeomorph I n ((sourceDelta I n).simplexChart m s t) =
      ⟨s.1,orderedAffineFace s.2 t⟩ := rfl

lemma sourceHomeomorph_lower (D : DeltaComplex.{w}) (n : ℕ)
    (x : (sourceDelta (D.Simplex n) n).Realization) :
    x ∈ (deltaSkeletonLT (sourceDelta (D.Simplex n) n) n).carrier ↔
      sourceHomeomorph (D.Simplex n) n x ∈ (sourcePair D n).subspace := by
  constructor
  · rintro ⟨m,s,hs,t,rfl⟩
    change ∃ i, (orderedAffineFace s.2 t).weights i = 0
    exact (boundary_iff n _).mpr (P202.Topology.DeltaBoundary.properFace_mem_boundary hs s.2 t)
  · intro hx
    let p := sourceHomeomorph (D.Simplex n) n x
    have hp : p ∈ (sourcePair D n).subspace := hx
    obtain ⟨m,hm,a,t,ht,hat⟩ := P202.Topology.exists_proper_interior_face p.2
      ((boundary_iff n p.2).mp hp)
    refine ⟨m,(p.1,a),hm,t,?_⟩
    apply (sourceHomeomorph (D.Simplex n) n).injective
    change (⟨p.1,orderedAffineFace a t⟩ : Σ _ : D.Simplex n,StandardSimplex n) = p
    exact Sigma.ext rfl (heq_of_eq hat)

def sourceGoodData (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] : P202Specs.GoodPairQuotient.Data.{w} := by
  let B := deltaSkeletonLT (sourceDelta (D.Simplex n) n) n
  have hne : B.carrier.Nonempty := by
    obtain ⟨p,hp⟩ := source_boundary_nonempty D n hn
    refine ⟨(sourceHomeomorph (D.Simplex n) n).symm p,?_⟩
    exact (sourceHomeomorph_lower D n _).mpr (by simpa using hp)
  let d := deltaCarrierGoodData (sourceDelta (D.Simplex n) n) B hne
  exact transportGoodData d (sourcePair D n) (sourceHomeomorph (D.Simplex n) n)
    (sourceHomeomorph_lower D n)

@[simp] lemma sourceGoodData_pair (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] :
    (sourceGoodData D n hn).pair = sourcePair D n := rfl

/-- The characteristic coproduct map induces the required singular skeletal
isomorphism with arbitrary module coefficients. The affine summand generator
is sent by this very map, fixing all signs. -/
theorem characteristicMap_isIso
    (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
    (D : DeltaComplex.{w}) (n : ℕ) (hn : 0<n) [Nonempty (D.Simplex n)] (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (relativeMap (P202Specs.SingularChains.chainFunctor R A) (characteristicMap D n)) q) := by
  exact ModuleCoefficients.moduleRelativeMap_of_quotientPairIso R A
    (sourceGoodData D n hn) (targetGoodData D n hn) (characteristicMap D n)
      (quotientPairIso D n hn).hom (quotientPairIso_square D n hn) q

end SkeletalQuotient
end P202.SimplicialComparison

namespace P202.SimplicialComparison
section
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
section UpperSkeletalComparison
open P202Specs.SpheresDisks
open P202Specs.RelativeSingularChains

/-- The characteristic map on the very same supported relative quotients. -/
def upperSkeletalCharacteristicMap (D : DeltaComplex.{w}) (n : ℕ) :
    singularRelativeComplex R A (SkeletalQuotient.sourcePair D n).space
        (SkeletalQuotient.sourcePair D n).subspace ⟶
      singularRelativeComplex R A (deltaSkeletalPair D n).space
        (deltaSkeletalPair D n).subspace :=
  singularPairMap R A _ _ (SkeletalQuotient.characteristicMap D n).map
    (SkeletalQuotient.characteristicMap D n).mapsTo

/-- The quotient-space argument for the characteristic map transfers through
the canonical equivalence with supported relative chains. -/
theorem upperSkeletalCharacteristicMap_isIso (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)] (q : ℕ) :
    IsIso (homologyMap (upperSkeletalCharacteristicMap R A D n) q) := by
  let S := singularRelativeIso R A (SkeletalQuotient.sourcePair D n).space
    (SkeletalQuotient.sourcePair D n).subspace
  let T := singularRelativeIso R A (deltaSkeletalPair D n).space
    (deltaSkeletalPair D n).subspace
  have hs : relativeMap (chainFunctor R A) (SkeletalQuotient.characteristicMap D n) ≫ T.hom =
      S.hom ≫ upperSkeletalCharacteristicMap R A D n :=
    singularRelativeIso_natural R A _ _ (SkeletalQuotient.characteristicMap D n).map
      (SkeletalQuotient.characteristicMap D n).mapsTo
  haveI := SkeletalQuotient.characteristicMap_isIso R A D n hn q
  haveI : IsIso (homologyMap S.hom q ≫ homologyMap (upperSkeletalCharacteristicMap R A D n) q) := by
    rw [← homologyMap_comp, ← hs, homologyMap_comp]
    infer_instance
  exact IsIso.of_isIso_comp_left (homologyMap S.hom q)
    (homologyMap (upperSkeletalCharacteristicMap R A D n) q)

/-- On each source affine simplex the characteristic map is exactly the
specified Δ-parametrization, retaining the original label and orientation. -/
theorem upperSkeletalCharacteristicMap_simplex (D : DeltaComplex.{w}) (n : ℕ)
    (s : D.Simplex n) :
    (TopCat.toSSet.map (SkeletalQuotient.characteristicMap D n).map).app (Opposite.op ⦋n⦌)
        (constantSigmaSimplex (D.Simplex n) (simplex n) n s (affineSimplex n)) =
      deltaSingularSimplex (deltaSkeletonLT D (n+1)).asComplex n ⟨s,Nat.lt_succ_self n⟩ := by
  apply (simplexEquiv (deltaSkeletalPair D n).space n).injective
  rw [P202.SingularChains.simplexEquiv_postcomp]
  ext t
  simp only [ContinuousMap.comp_apply, constantSigmaSimplex_value,
    affineSimplex, Equiv.apply_symm_apply, ContinuousMap.id_apply]
  rfl

/-- The concentrated skeletal model, source affine generators, and the
characteristic map recover the original canonical relative comparison. -/
theorem upperSkeletalComparison_factorization (D : DeltaComplex.{w}) (n : ℕ)
    (F : DeltaComparisonData R A (deltaSkeletonLT D (n+1)).asComplex
      (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n)) :
    (deltaSkeletalSingleIso R A D n).hom ≫
      constantSigmaAffineComparison R A (D.Simplex n) n ≫
      upperSkeletalCharacteristicMap R A D n = F.relative := by
  apply HomologicalComplex.Hom.ext
  funext q
  by_cases hq : q=n
  · subst q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨c,rfl⟩ := ((deltaSelection R A (deltaSkeletonLT D (n+1)).asComplex
      (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n)).module n).mkQ_surjective x
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add c d hc hd => simp only [map_add, hc, hd]
    | single s a =>
      obtain ⟨s,hs⟩ := s
      let e := singleObjXSelf (.down ℕ) n (ModuleCat.of R (D.Simplex n →₀ A))
      have hsingle : ((deltaSkeletalSingleIso R A D n).hom.f n).hom
          (((deltaSelection R A (deltaSkeletonLT D (n+1)).asComplex
            (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n)).module n).mkQ
              (Finsupp.single ⟨s,hs⟩ a)) = e.inv (Finsupp.single s a) := by
        have h := congrArg (fun z => e.inv z) (deltaSkeletalSingleIso_hom_generator R A D n s a)
        simpa only [e, Iso.hom_inv_id_apply] using h
      change ((upperSkeletalCharacteristicMap R A D n).f n).hom
        (((constantSigmaAffineComparison R A (D.Simplex n) n).f n).hom
          (((deltaSkeletalSingleIso R A D n).hom.f n).hom _)) = _
      rw [hsingle]
      have ha := constantSigmaAffineComparison_generator R A (D.Simplex n) n s a
      change ((constantSigmaAffineComparison R A (D.Simplex n) n).f n).hom
        (e.inv (Finsupp.single s a)) = _ at ha
      rw [ha]
      change ((singularSelection R A (deltaSkeletalPair D n).space
        (deltaSkeletalPair D n).subspace).module n).mkQ
          (((chainMap R A (SkeletalQuotient.characteristicMap D n).map).f n).hom
            (Finsupp.single (constantSigmaSimplex (D.Simplex n) (simplex n) n s (affineSimplex n)) a)) = _
      rw [P202.SingularChains.chainMap_single, upperSkeletalCharacteristicMap_simplex]
      erw [F.relative_formula, P202.RelativeParametrizations.deltaParametrizationLinear_single]
      rfl
  · exact (deltaSkeletalRelative_isZero R A D n q hq).eq_of_src _ _

/-- Every canonical comparison between successive nonempty positive skeleta
is an isomorphism, in every degree and over every coefficient module. -/
theorem upperSkeletalComparison_isIso (D : DeltaComplex.{w}) (n : ℕ)
    (hn : 0<n) [Nonempty (D.Simplex n)]
    (F : DeltaComparisonData R A (deltaSkeletonLT D (n+1)).asComplex
      (deltaSkeletonLT (deltaSkeletonLT D (n+1)).asComplex n)) (q : ℕ) :
    IsIso (homologyMap F.relative q) := by
  haveI := constantSigmaAffineComparison_quasiIso R A (D.Simplex n) n
  haveI := upperSkeletalCharacteristicMap_isIso R A D n hn q
  rw [← upperSkeletalComparison_factorization R A D n F,
    homologyMap_comp, homologyMap_comp]
  infer_instance

end UpperSkeletalComparison

end

section
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]

def deltaBoundedInverse (E : DeltaComplex.{w}) (n : ℕ)
    (hE : ∀ k, n+1 ≤ k → IsEmpty (E.Simplex k)) :
    DeltaMap E (deltaSkeletonLT E (n+1)).asComplex where
  simplex k s := ⟨s,by
    by_contra hk
    haveI := hE k (Nat.le_of_not_gt hk)
    exact isEmptyElim s⟩
  face _ _ := Subtype.ext rfl

lemma deltaBoundedRealization_left (E : DeltaComplex.{w}) (n : ℕ)
    (hE : ∀ k, n+1 ≤ k → IsEmpty (E.Simplex k))
    (x : (deltaSkeletonLT E (n+1)).asComplex.Realization) :
    deltaRealization (deltaBoundedInverse E n hE)
      (deltaRealization (deltaSkeletonLT E (n+1)).inclusion x) = x := by
  induction x using Quotient.inductionOn with | h p =>
    obtain ⟨k,s,t⟩ := p
    change (deltaSkeletonLT E (n+1)).asComplex.simplexChart k _ t =
      (deltaSkeletonLT E (n+1)).asComplex.simplexChart k s t
    congr 1

lemma deltaBoundedRealization_right (E : DeltaComplex.{w}) (n : ℕ)
    (hE : ∀ k, n+1 ≤ k → IsEmpty (E.Simplex k)) (x : E.Realization) :
    deltaRealization (deltaSkeletonLT E (n+1)).inclusion
      (deltaRealization (deltaBoundedInverse E n hE) x) = x := by
  induction x using Quotient.inductionOn with | h p => rfl

def deltaBoundedRealizationHomeomorph (E : DeltaComplex.{w}) (n : ℕ)
    (hE : ∀ k, n+1 ≤ k → IsEmpty (E.Simplex k)) :
    (deltaSkeletonLT E (n+1)).asComplex.Realization ≃ₜ E.Realization where
  toFun := deltaRealization (deltaSkeletonLT E (n+1)).inclusion
  invFun := deltaRealization (deltaBoundedInverse E n hE)
  left_inv := deltaBoundedRealization_left E n hE
  right_inv := deltaBoundedRealization_right E n hE
  continuous_toFun := (deltaRealization (deltaSkeletonLT E (n+1)).inclusion).hom.continuous
  continuous_invFun := (deltaRealization (deltaBoundedInverse E n hE)).hom.continuous

lemma deltaBoundedRealization_carrier (E : DeltaComplex.{w}) (n : ℕ)
    (hE : ∀ k, n+1 ≤ k → IsEmpty (E.Simplex k))
    (x : (deltaSkeletonLT E (n+1)).asComplex.Realization) :
    x ∈ (deltaSkeletonLT (deltaSkeletonLT E (n+1)).asComplex n).carrier ↔
      deltaBoundedRealizationHomeomorph E n hE x ∈ (deltaSkeletonLT E n).carrier := by
  constructor
  · exact deltaRealization_carrier _ _ _ (fun _ _ hs => hs) x
  · intro hx
    have hh := deltaRealization_carrier (deltaSkeletonLT E n)
      (deltaSkeletonLT (deltaSkeletonLT E (n+1)).asComplex n)
      (deltaBoundedInverse E n hE) (fun _ _ hs => hs) _ hx
    change deltaRealization (deltaBoundedInverse E n hE)
      (deltaRealization (deltaSkeletonLT E (n+1)).inclusion x) ∈ _ at hh
    rw [deltaBoundedRealization_left] at hh
    exact hh

def deltaBoundedPairIso (E : DeltaComplex.{w}) (n : ℕ)
    (hE : ∀ k, n+1 ≤ k → IsEmpty (E.Simplex k)) :
    P202Specs.RelativeSingularChains.Pair.mk
      (TopCat.of (deltaSkeletonLT E (n+1)).asComplex.Realization)
      (deltaSkeletonLT (deltaSkeletonLT E (n+1)).asComplex n).carrier ≅
      ⟨TopCat.of E.Realization,(deltaSkeletonLT E n).carrier⟩ :=
  P202.GoodPairQuotient.pairIsoOfHomeomorph _ _
    (deltaBoundedRealizationHomeomorph E n hE) (deltaBoundedRealization_carrier E n hE)

lemma deltaRelativePushforward_isIso_of_inverse
    {D E : DeltaComplex.{w}} (B : DeltaSubcomplex D) (H : DeltaSubcomplex E)
    (f : DeltaMap D E) (g : DeltaMap E D)
    (hf : ∀ k s, s ∈ B.selected k → f.simplex k s ∈ H.selected k)
    (hg : ∀ k s, s ∈ H.selected k → g.simplex k s ∈ B.selected k)
    (hgf : ∀ k s, g.simplex k (f.simplex k s) = s)
    (hfg : ∀ k s, f.simplex k (g.simplex k s) = s)
    (T : deltaRelativeComplex R A D B ⟶ deltaRelativeComplex R A E H)
    (hT : ∀ k x, (T.f k).hom (((deltaSelection R A D B).module k).mkQ x) =
      ((deltaSelection R A E H).module k).mkQ (deltaPushforward R A f k x)) :
    IsIso T := by
  obtain ⟨S,hS⟩ := P202.SimplicialChains.deltaRelativePushforward R A H B g hg
  refine (⟨T,S,?_,?_⟩ : deltaRelativeComplex R A D B ≅ deltaRelativeComplex R A E H).isIso_hom
  · apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨x,rfl⟩ := ((deltaSelection R A D B).module k).mkQ_surjective x
    change (S.f k).hom ((T.f k).hom _) = _
    rw [hT,hS]
    change ((deltaSelection R A D B).module k).mkQ
      (Finsupp.mapDomain (g.simplex k) (Finsupp.mapDomain (f.simplex k) x)) = _
    rw [← Finsupp.mapDomain_comp]
    have hh : g.simplex k ∘ f.simplex k = id := funext (hgf k)
    rw [hh,Finsupp.mapDomain_id]
    rfl
  · apply HomologicalComplex.Hom.ext
    funext k
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨x,rfl⟩ := ((deltaSelection R A E H).module k).mkQ_surjective x
    change (T.f k).hom ((S.f k).hom _) = _
    rw [hS,hT]
    change ((deltaSelection R A E H).module k).mkQ
      (Finsupp.mapDomain (f.simplex k) (Finsupp.mapDomain (g.simplex k) x)) = _
    rw [← Finsupp.mapDomain_comp]
    have hh : f.simplex k ∘ g.simplex k = id := funext (hfg k)
    rw [hh,Finsupp.mapDomain_id]
    rfl

/-- Bounded Delta complexes identify with their full upper skeleton, and the
strict affine square transports the canonical relative comparison. -/
theorem deltaBoundedRelativeComparison_of_skeletal
    (E : DeltaComplex.{w}) (n : ℕ)
    (hE : ∀ k, n+1 ≤ k → IsEmpty (E.Simplex k))
    (hupper : ∀ (G : DeltaComparisonData R A (deltaSkeletonLT E (n+1)).asComplex
      (deltaSkeletonLT (deltaSkeletonLT E (n+1)).asComplex n)) (q : ℕ),
      IsIso (homologyMap G.relative q))
    (F : DeltaComparisonData R A E (deltaSkeletonLT E n)) (q : ℕ) :
    IsIso (homologyMap F.relative q) := by
  let U := (deltaSkeletonLT E (n+1)).asComplex
  let B := deltaSkeletonLT U n
  let H := deltaSkeletonLT E n
  let f := (deltaSkeletonLT E (n+1)).inclusion
  let g := deltaBoundedInverse E n hE
  have hf : ∀ k s, s ∈ B.selected k → f.simplex k s ∈ H.selected k := fun _ _ hs => hs
  have hg : ∀ k s, s ∈ H.selected k → g.simplex k s ∈ B.selected k := fun _ _ hs => hs
  obtain ⟨G⟩ := deltaComparisonData_nonempty R A U B
  obtain ⟨r,hr,T,Trel,grel,hT,hTrel,hgrel,hcomm⟩ :=
    deltaNaturality_core R A B H f hf
  have hr' : r = deltaRealization f := by
    apply TopCat.hom_ext
    ext x
    induction x using Quotient.inductionOn with | h p =>
      obtain ⟨k,s,t⟩ := p
      exact hr k s t
  subst r
  haveI := deltaRelativePushforward_isIso_of_inverse R A B H f g hf hg
    (by intro k s; exact Subtype.ext rfl) (by intros; rfl) Trel hTrel
  haveI : IsIso grel := by
    let e := deltaBoundedPairIso E n hE
    let absrel := P202Specs.RelativeSingularChains.relativeMap (chainFunctor R A) e.hom
    have heq : absrel ≫ (singularRelativeIso R A (TopCat.of E.Realization) H.carrier).hom =
        (singularRelativeIso R A (TopCat.of U.Realization) B.carrier).hom ≫ grel := by
      have habs : absrel = P202Specs.RelativeSingularChains.relativeMap (chainFunctor R A)
          (⟨deltaRealization f,fun x hx => deltaRealization_carrier B H f hf x hx⟩ :
            (⟨TopCat.of U.Realization,B.carrier⟩ : P202Specs.RelativeSingularChains.Pair) ⟶
              ⟨TopCat.of E.Realization,H.carrier⟩) := rfl
      rw [habs,singularRelativeIso_natural R A B.carrier H.carrier (deltaRealization f)
        (deltaRealization_carrier B H f hf)]
      congr 1
      apply HomologicalComplex.Hom.ext
      funext k
      apply ModuleCat.hom_ext
      ext x
      obtain ⟨x,rfl⟩ := ((singularSelection R A (TopCat.of U.Realization) B.carrier).module k).mkQ_surjective x
      exact (hgrel k x).symm
    haveI : IsIso absrel := (P202Specs.RelativeSingularChains.relativeFunctor (chainFunctor R A)).map_isIso e.hom
    haveI : IsIso ((singularRelativeIso R A (TopCat.of U.Realization) B.carrier).hom ≫ grel) := by
      rw [← heq]; infer_instance
    exact IsIso.of_isIso_comp_left
      (singularRelativeIso R A (TopCat.of U.Realization) B.carrier).hom grel
  haveI := hupper G q
  have hn := (hcomm G F q).2
  haveI : IsIso (homologyMap Trel q ≫ homologyMap F.relative q) := by
    rw [hn]; infer_instance
  exact IsIso.of_isIso_comp_left (homologyMap Trel q) (homologyMap F.relative q)


end
section BoundedSkeletalComparison
variable (R : Type u) [CommRing R] (A : Type v) [AddCommGroup A] [Module R A]
/-- The actual canonical comparison on each bounded skeletal pair. The
point/empty case uses ordinary degree zero, and no top cells gives the full pair. -/
theorem boundedSkeletalComparison_isIso (E : DeltaComplex.{w}) (n : ℕ)
    (hE : ∀ k, n+1 ≤ k → IsEmpty (E.Simplex k))
    (F : DeltaComparisonData R A E (deltaSkeletonLT E n)) (q : ℕ) :
    IsIso (homologyMap F.relative q) := by
  by_cases hn : n = 0
  · subst n
    exact deltaZeroDimensional_relativeComparison R A E
      (fun k hk => hE k (by omega)) (deltaSkeletonLT E 0) F q
  · by_cases ht : Nonempty (E.Simplex n)
    · letI := ht
      exact deltaBoundedRelativeComparison_of_skeletal R A E n hE
        (fun G j => upperSkeletalComparison_isIso R A E n (Nat.pos_of_ne_zero hn) G j) F q
    · exact deltaBoundedRelativeComparison_of_empty_top R A E n hE
        (not_nonempty_iff.mp ht) F q
end BoundedSkeletalComparison

/-- Canonical Δ–singular comparison for arbitrary weak realizations and all
subcomplex pairs, with arbitrary module coefficients. -/
theorem deltaComparison : P202Specs.SimplicialComparison.deltaComparison_type.{u,v,w} := by
  apply deltaComparison_of_skeletal
  intro R _ A _ _ E n hE F q
  exact boundedSkeletalComparison_isIso R A E n hE F q

/-- Canonical simplicial–singular comparison for arbitrary complexes and
subcomplex pairs through the original increasing affine parametrizations. -/
theorem simplicialComparison : P202Specs.SimplicialComparison.simplicialComparison_type.{u,v,w} :=
  simplicialComparison_of_deltaComparison deltaComparison

/-- Every choice of vertex order gives the same absolute and relative
comparison on homology after its signed orientation transport. -/
theorem orderIndependence : P202Specs.SimplicialComparison.orderIndependence_type.{u,v,w} :=
  orderIndependence_of_comparison simplicialComparison

end P202.SimplicialComparison
