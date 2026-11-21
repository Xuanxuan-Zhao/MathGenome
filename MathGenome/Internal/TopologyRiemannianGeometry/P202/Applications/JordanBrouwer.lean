import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Applications.JordanBrouwer
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.AlexanderDuality
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
Jordan–Brouwer separation, paper.tex 2854–2884.
Rational Alexander duality counts complementary components and proves that
embedded closed balls do not separate. Stereographic coordinates construct
small nonseparating patches, and a point-set argument proves the full common
boundary assertion. All dimensions n ≥ 1, including the two-point S⁰ case,
are covered without a local-flatness assumption.
-/
noncomputable section
open Set Topology CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite

namespace P202.JordanBrouwer
open P202Specs.JordanBrouwer

/-- Components are relatively closed even when their ambient subset is not closed. -/
theorem closure_component_inter_subset {X : Type*} [TopologicalSpace X]
    {U : Set X} {x : X} (hx : x ∈ U) :
    closure (connectedComponentIn U x) ∩ U ⊆ connectedComponentIn U x := by
  intro y hy
  rw [connectedComponentIn_eq_image hx] at hy ⊢
  have h : (⟨y, hy.2⟩ : U) ∈ closure (connectedComponent (⟨x, hx⟩ : U)) := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    exact hy.1
  rw [isClosed_connectedComponent.closure_eq] at h
  exact ⟨⟨y, hy.2⟩, h, rfl⟩

/-- No point of an open complement is on the frontier of one of its components. -/
theorem frontier_component_subset {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {K : Set X} (hK : IsClosed K)
    {x : X} (hx : x ∈ Kᶜ) : frontier (connectedComponentIn Kᶜ x) ⊆ K := by
  intro y hy
  by_contra hyK
  have hyC := closure_component_inter_subset hx ⟨frontier_subset_closure hy, hyK⟩
  have hopen : IsOpen (connectedComponentIn Kᶜ x) := hK.isOpen_compl.connectedComponentIn
  exact hy.2 (hopen.interior_eq.symm ▸ hyC)

/-- A connected enlargement meeting a component must meet its frontier, unless
it is contained in that component. This makes the common-boundary argument
independent of any collar or regularity of the embedded sphere. -/
theorem boundaryFromPatches : P202Specs.JordanBrouwer.Expected.boundaryFromPatches := by
  intro X _ _ K hK hpatch x hx
  apply Set.Subset.antisymm (frontier_component_subset hK hx)
  intro y hy
  have hopen : IsOpen (connectedComponentIn Kᶜ x) := hK.isOpen_compl.connectedComponentIn
  have hyclosure : y ∈ closure (connectedComponentIn Kᶜ x) := by
    rw [mem_closure_iff]
    intro O hO hyO
    by_contra hmiss
    obtain ⟨D, hyD, hD, hconn⟩ := hpatch y hy O hO hyO
    have hclosureD : Disjoint (closure (connectedComponentIn Kᶜ x)) D := by
      apply Set.disjoint_left.mpr
      intro z hzC hzD
      obtain ⟨w, hwO, hwC⟩ := mem_closure_iff.mp hzC O hO (hD hzD).2
      exact hmiss ⟨w, hwO, hwC⟩
    have hsub : Kᶜ ∪ D ⊆ connectedComponentIn Kᶜ x := by
      apply hconn.subset_of_closure_inter_subset hopen
      · exact ⟨x, Or.inl hx, mem_connectedComponentIn hx⟩
      · intro z hz
        rcases hz.2 with hzK | hzD
        · exact closure_component_inter_subset hx ⟨hz.1, hzK⟩
        · exact False.elim (Set.disjoint_left.mp hclosureD hz.1 hzD)
    exact (connectedComponentIn_subset Kᶜ x (hsub (Or.inr hyD))) hy
  rw [hopen.frontier_eq]
  exact ⟨hyclosure, fun hyC => (connectedComponentIn_subset Kᶜ x hyC) hy⟩

/-- Stereographic coordinates construct the patches from connected complements
of embedded closed balls. The zero-dimensional coordinate space is allowed. -/
theorem patches_of_closedBall_complements
    {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace Y] [NormedAddCommGroup E]
    (e : Y → X) (he : Topology.IsEmbedding e)
    (puncture : ∀ p : Y, {y : Y | y ≠ p} ≃ₜ E)
    (hball : ∀ r : ℝ, 0 < r → ∀ f : Metric.closedBall (0 : E) r → X,
      Topology.IsEmbedding f → IsPreconnected (range f)ᶜ) :
    HasNonseparatingPatches (range e) := by
  rintro _ ⟨p, rfl⟩ O hO hpO
  let A : Set Y := e ⁻¹' Oᶜ
  have hA : IsCompact A := (hO.isClosed_compl.preimage he.continuous).isCompact
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA
  let q : A → {y : Y | y ≠ p} := fun y => ⟨y.val, by
    intro h
    have hy := y.property
    change e y.val ∉ O at hy
    exact hy (h ▸ hpO)⟩
  have hq : Continuous q := continuous_subtype_val.subtype_mk _
  let s := puncture p
  have hbounded : Bornology.IsBounded (range (s ∘ q)) :=
    (isCompact_range (s.continuous.comp hq)).isBounded
  obtain ⟨r, hr, hbound⟩ := hbounded.subset_closedBall_lt 0 (0 : E)
  let f : Metric.closedBall (0 : E) r → X := fun w => e (s.symm w.val).val
  have hf : Topology.IsEmbedding f :=
    he.comp (Topology.IsEmbedding.subtypeVal.comp
      (s.symm.isEmbedding.comp Topology.IsEmbedding.subtypeVal))
  have hfsub : range f ⊆ range e := by
    rintro _ ⟨w, rfl⟩
    exact ⟨(s.symm w.val).val, rfl⟩
  have hpf : e p ∉ range f := by
    rintro ⟨w, hw⟩
    exact (s.symm w.val).property (he.injective hw)
  have hcover : range e ∩ Oᶜ ⊆ range f := by
    rintro _ ⟨⟨y, rfl⟩, hyO⟩
    have hyA : y ∈ A := hyO
    let v : A := ⟨y, hyA⟩
    have hvball : s (q v) ∈ Metric.closedBall (0 : E) r :=
      hbound (mem_range_self v)
    refine ⟨⟨s (q v), hvball⟩, ?_⟩
    change e (s.symm (s (q v))).val = e y
    rw [s.symm_apply_apply]
  refine ⟨range e \ range f, ⟨mem_range_self p, hpf⟩, ?_, ?_⟩
  · intro y hy
    refine ⟨hy.1, ?_⟩
    by_contra hyO
    exact hy.2 (hcover ⟨hy.1, hyO⟩)
  · have hset : (range e)ᶜ ∪ (range e \ range f) = (range f)ᶜ := by
      ext y
      constructor
      · rintro (hy | hy)
        · exact fun h => hy (hfsub h)
        · exact hy.2
      · intro hy
        by_cases he : y ∈ range e
        · exact Or.inr ⟨he, hy⟩
        · exact Or.inl he
    rw [hset]
    exact hball r hr f hf

/-- The sphere has the local connectedness needed by the boundary argument,
including the zero-dimensional sphere. -/
theorem sphere_locallyConnected (n : ℕ) :
    LocallyConnectedSpace (P202.Duality.NeighborhoodCohomology.Sphere n) :=
  ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) _

/-- An embedded sphere is closed by compactness, without a local-flatness assumption. -/
theorem sphere_range_closed {n m : ℕ}
    {e : P202.Duality.NeighborhoodCohomology.Sphere m →
      P202.Duality.NeighborhoodCohomology.Sphere n}
    (he : Topology.IsEmbedding e) : IsClosed (range e) :=
  (isCompact_range he.continuous).isClosed

open P202.Duality.NeighborhoodCohomology
open P202Specs.SingularChains P202Specs.SingularDegreeZero
open P202Specs.AlexanderDuality P202Specs.SpheresDisks
open P202.PoincareDuality.ConcentratedChains
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem convex_stronglyLocallyContractible {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hC : Convex ℝ C) : StronglyLocallyContractibleSpace C := by
  refine StronglyLocallyContractibleSpace.of_bases (fun x : C => Metric.nhds_basis_ball) ?_
  intro x r hr
  let e : ↥(C ∩ Metric.ball x.val r) ≃ₜ Metric.ball x r :=
    { toFun := fun y => ⟨⟨y.val, y.property.1⟩, y.property.2⟩
      invFun := fun y => ⟨y.val.val, y.val.property, y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  haveI : ContractibleSpace ↥(C ∩ Metric.ball x.val r) :=
    (hC.inter (convex_ball x.val r)).contractibleSpace
      ⟨x.val, x.property, Metric.mem_ball_self hr⟩
  exact e.symm.contractibleSpace

theorem local_stronglyLocallyContractible {X : Type*} [TopologicalSpace X]
    (h : ∀ x : X, ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ StronglyLocallyContractibleSpace W) :
    StronglyLocallyContractibleSpace X := by
  constructor
  intro x
  rw [Filter.hasBasis_self]
  intro U hU
  obtain ⟨W, hW, hxW, hWc⟩ := h x
  letI := hWc
  have hU' : (Subtype.val ⁻¹' U : Set W) ∈ 𝓝 (⟨x, hxW⟩ : W) :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds hU
  obtain ⟨V, ⟨hV, hVc⟩, hVU⟩ := (contractible_basis (⟨x, hxW⟩ : W)).mem_iff.mp hU'
  refine ⟨Subtype.val '' V, hW.isOpenEmbedding_subtypeVal.image_mem_nhds.mpr hV, ?_, ?_⟩
  · letI : ContractibleSpace V := hVc
    exact (Topology.IsEmbedding.subtypeVal.homeomorphImage V).symm.contractibleSpace
  · rintro _ ⟨y, hy, rfl⟩
    exact hVU hy

/-- Euclidean spaces have a basis of contractible balls. -/
theorem euclidean_stronglyLocallyContractible (n : ℕ) :
    StronglyLocallyContractibleSpace (EuclideanSpace ℝ (Fin n)) := by
  haveI : StronglyLocallyContractibleSpace (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
    convex_stronglyLocallyContractible convex_univ
  exact (Homeomorph.Set.univ _).symm.isOpenEmbedding.stronglyLocallyContractibleSpace

theorem sphere_stronglyLocallyContractible (n : ℕ) :
    StronglyLocallyContractibleSpace (Sphere n) := by
  haveI := euclidean_stronglyLocallyContractible n
  apply local_stronglyLocallyContractible
  intro x
  refine ⟨{y : Sphere n | y ≠ -x}, isOpen_ne,
    ne_neg_of_mem_unit_sphere ℝ x, ?_⟩
  exact (P202.AlexanderDuality.spherePuncturedHomeomorph n (-x)).isOpenEmbedding.stronglyLocallyContractibleSpace

theorem sphere_nonempty (n : ℕ) : Nonempty (Sphere n) :=
  (NormedSpace.sphere_nonempty.mpr (show (0 : ℝ) ≤ 1 by norm_num)).to_subtype

/-- Rational rank detects the finite number of path components without a
prior finiteness assumption on the set of components. -/
theorem pathComponents_of_reduced_rank (X : TopCat.{0}) [Nonempty X] (k : ℕ)
    (h : Module.rank ℚ (reducedHomology ℚ ℚ X 0) = k) :
    Nonempty (ZerothHomotopy X ≃ Fin (k + 1)) := by
  classical
  obtain ⟨e⟩ := P202.SingularDegreeZero.reducedDegreeZero ℚ ℚ X
  let i : ZerothHomotopy X := ZerothHomotopy.mk (Classical.choice inferInstance)
  have hs : Function.Surjective (componentSum ℚ ℚ X) := by
    intro q
    exact ⟨Finsupp.single i q, by simp [componentSum, sumCoefficients]⟩
  have hr := (componentSum ℚ ℚ X).rank_eq_of_surjective hs
  rw [← e.rank_eq, h, Module.rank_self] at hr
  apply Cardinal.mk_eq_nat_iff.mp
  simpa only [rank_finsupp_self', Nat.cast_add, Nat.cast_one, add_comm] using hr

/-- Transport cohomology along the actual homeomorphism, with its usual
contravariant direction. -/
def reducedCohomologyHomeomorph {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (q : ℤ) :
    reducedCohomology ℚ (TopCat.of Y) q ≃ₗ[ℚ]
      reducedCohomology ℚ (TopCat.of X) q :=
  ((HomologicalComplex.homologyFunctor _ _ q).mapIso
    ((P202Specs.CohomologyPairs.dualComplexFunctor ℚ ℚ (.down ℤ)).mapIso
      (((reducedFunctor ℚ ℚ).mapIso (TopCat.isoOfHomeo e)).op))).toLinearEquiv

/-- The top cohomology computation includes degree zero of the two-point sphere. -/
def sphereTopCohomology (m : ℕ) :
    reducedCohomology ℚ (sphere m) (m : ℤ) ≃ₗ[ℚ] ℚ := by
  let K := reducedComplex ℚ ℚ (sphere m)
  let e := Classical.choice ((P202.SpheresDisks.sphereHomology ℚ ℚ m m).1 rfl)
  haveI : ∀ q : ℤ, Module.Free ℚ (K.X q) := fun q => inferInstance
  let c : K.homology (m : ℤ) ⟶ K.cycles (m : ℤ) :=
    Projective.factorThru (𝟙 _) (K.homologyπ (m : ℤ))
  have hc : c ≫ K.homologyπ (m : ℤ) = 𝟙 _ := Projective.factorThru_comp _ _
  haveI : IsIso (c ≫ K.homologyπ (m : ℤ)) := by rw [hc]; infer_instance
  let a := LinearEquiv.ofBijective (cohomologyEvaluation ℚ K (m : ℤ) c)
    (cohomologyEvaluation_bijective ℚ K (m : ℤ)
      (P202.AlexanderDuality.reducedComplex_boundedBelow ℚ _) c
      (P202.AlexanderDuality.sphere_reducedHomology_concentrated ℚ m))
  exact a.trans ((LinearEquiv.arrowCongr e (LinearEquiv.refl ℚ ℚ)).trans
    (LinearMap.ringLmapEquivSelf ℚ ℚ ℚ))

/-- A contractible space has zero reduced cohomology for the same algebraic
singular cochains used by the Alexander-duality interface. -/
theorem contractible_reducedCohomology (X : TopCat.{0}) [Nonempty X]
    [ContractibleSpace X] (q : ℤ) : IsZero (reducedCohomology ℚ X q) := by
  let K := reducedComplex ℚ ℚ X
  have hz : ∀ i : ℤ, IsZero (K.homology i) :=
    (P202.SpheresDisks.contractible ℚ ℚ).2 X
  haveI : ∀ i : ℤ, Module.Free ℚ (K.X i) := fun i => inferInstance
  let c : K.homology (q-1) ⟶ K.cycles (q-1) :=
    Projective.factorThru (𝟙 _) (K.homologyπ (q-1))
  have hc : c ≫ K.homologyπ (q-1) = 𝟙 _ := Projective.factorThru_comp _ _
  haveI : IsIso (c ≫ K.homologyπ (q-1)) := by rw [hc]; infer_instance
  exact dualCohomology_isZero ℚ K (q-1)
    (P202.AlexanderDuality.reducedComplex_boundedBelow ℚ X) c
    (fun i _ => hz i) q (by omega)

/-- A zero homology group prevents a compact embedding from filling a sphere
whose homology group in that degree is nonzero. -/
theorem embedding_not_surjective_of_zero_homology
    {Y : Type} [TopologicalSpace Y] {n : ℕ} (e : Y → Sphere n)
    (he : Topology.IsEmbedding e)
    (hY : IsZero (reducedHomology ℚ ℚ (TopCat.of Y) (n : ℤ))) :
    range e ≠ univ := by
  intro hfull
  let a := he.toHomeomorphOfSurjective (Set.range_eq_univ.mp hfull)
  let i := (reducedHomologyFunctor ℚ ℚ (n : ℤ)).mapIso (TopCat.isoOfHomeo (X := TopCat.of Y) (Y := TopCat.of (Sphere n)) a)
  haveI : Subsingleton (reducedHomology ℚ ℚ (TopCat.of (Sphere n)) (n : ℤ)) :=
    ModuleCat.subsingleton_of_isZero (hY.of_iso i.symm)
  obtain ⟨b⟩ := (P202.SpheresDisks.sphereHomology ℚ ℚ n n).1 rfl
  haveI : Subsingleton ℚ := b.symm.injective.subsingleton
  exact zero_ne_one (Subsingleton.elim (0 : ℚ) 1)

/-- The component count, retaining all original embedding hypotheses. -/
theorem componentCount (n : ℕ) (hn : 1 ≤ n)
    (e : Sphere (n-1) → Sphere n) (he : Topology.IsEmbedding e) :
    Nonempty (ConnectedComponents ((range e)ᶜ : Set (Sphere n)) ≃ Fin 2) := by
  haveI := sphere_nonempty (n-1)
  haveI := sphere_stronglyLocallyContractible (n-1)
  haveI : StronglyLocallyContractibleSpace (range e) :=
    he.toHomeomorph.symm.isOpenEmbedding.stronglyLocallyContractibleSpace
  have hp : range e ≠ univ := embedding_not_surjective_of_zero_homology e he
    ((P202.SpheresDisks.sphereHomology ℚ ℚ (n-1) n).2 (by omega))
  haveI : Nonempty (complement n (range e)) := P202.AlexanderDuality.complement_nonempty n _ hp
  obtain ⟨a⟩ := P202.AlexanderDuality.field ℚ n (range e) hn (Set.range_nonempty e)
    hp (isCompact_range he.continuous) StronglyLocallyContractibleSpace.locallyContractible 0
  have hq : (n : ℤ) - (0 : ℕ) - 1 = ((n-1 : ℕ) : ℤ) := by omega
  rw [hq] at a
  let b := a.trans ((reducedCohomologyHomeomorph he.toHomeomorph _).trans
    (sphereTopCohomology (n-1)))
  obtain ⟨c⟩ := pathComponents_of_reduced_rank (complement n (range e)) 1
    (b.rank_eq.trans (Module.rank_self ℚ))
  haveI : LocallyPathConnectedSpace (Sphere n) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin n)) _
  haveI : LocallyPathConnectedSpace ((range e)ᶜ : Set (Sphere n)) :=
    (sphere_range_closed he).isOpen_compl.locallyPathConnectedSpace
  exact ⟨connectedComponentsEquivZerothHomotopy.trans c⟩

/-- Every embedded closed ball has a connected complement. Its source is
compact, contractible, and locally contractible, as required by duality. -/
theorem closedBallComplement (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (r : ℝ) (hr : 0 < r)
    (e : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r → Sphere n)
    (he : Topology.IsEmbedding e) : IsConnected (range e)ᶜ := by
  let B := Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) r
  haveI : Nonempty B := ⟨⟨0, Metric.mem_closedBall_self hr.le⟩⟩
  haveI : ContractibleSpace B :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin m)) r).contractibleSpace
      ⟨0, Metric.mem_closedBall_self hr.le⟩
  haveI : StronglyLocallyContractibleSpace B :=
    convex_stronglyLocallyContractible (convex_closedBall _ _)
  haveI : StronglyLocallyContractibleSpace (range e) :=
    he.toHomeomorph.symm.isOpenEmbedding.stronglyLocallyContractibleSpace
  have hp : range e ≠ univ := embedding_not_surjective_of_zero_homology e he
    ((P202.SpheresDisks.contractible ℚ ℚ).2 (TopCat.of B) (n : ℤ))
  haveI : Nonempty (complement n (range e)) := P202.AlexanderDuality.complement_nonempty n _ hp
  obtain ⟨a⟩ := P202.AlexanderDuality.field ℚ n (range e) hn (Set.range_nonempty e)
    hp (isCompact_range he.continuous) StronglyLocallyContractibleSpace.locallyContractible 0
  let b := a.trans (reducedCohomologyHomeomorph he.toHomeomorph _)
  haveI : Subsingleton (reducedCohomology ℚ (TopCat.of B) ((n : ℤ) - (0 : ℕ) - 1)) :=
    ModuleCat.subsingleton_of_isZero (contractible_reducedCohomology (TopCat.of B) _)
  haveI : Subsingleton (reducedHomology ℚ ℚ (complement n (range e)) 0) :=
    b.injective.subsingleton
  obtain ⟨c⟩ := pathComponents_of_reduced_rank (complement n (range e)) 0 (by simp)
  change ZerothHomotopy (complement n (range e)) ≃ Fin 1 at c
  haveI : Subsingleton (ZerothHomotopy (complement n (range e))) := c.injective.subsingleton
  haveI : PathConnectedSpace (complement n (range e)) :=
    pathConnectedSpace_iff_zerothHomotopy.mpr ⟨inferInstance, inferInstance⟩
  exact isConnected_iff_connectedSpace.mpr inferInstance

/-- Jordan–Brouwer separation and the complete common-boundary conclusion. -/
theorem separation : P202Specs.JordanBrouwer.Expected.separation := by
  intro n hn e he
  refine ⟨componentCount n hn e he, ?_⟩
  haveI := sphere_locallyConnected n
  apply boundaryFromPatches _ (range e) (sphere_range_closed he)
  exact patches_of_closedBall_complements e he
    (P202.AlexanderDuality.spherePuncturedHomeomorph (n-1))
    (fun r hr f hf => (closedBallComplement n hn (n-1) r hr f hf).isPreconnected)


end P202.JordanBrouwer
