import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.PrismHomotopy
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.LocalOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.MayerVietoris
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.SingularDegreeZero
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.Excision
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Homology.SpheresDisks
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Convex.Contractible
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CoveringLifting

/-! Local homology, orientations, and the integral orientation double cover
for paper.tex T29. All groups and restriction maps are the shared singular
homology objects. The independent Specs retain the full source statements. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
universe u v w t
namespace P202.LocalOrientation
open P202Specs.LocalOrientation P202Specs.SingularChains P202Specs.RelativeSingularChains

/-- R-orientations in the shared singular local homology groups, with the
local supported-ball compatibility required by T29. -/
def orientation : Expected.orientation_type.{u,v} := @Orientation

section Generators
variable (R : Type u) [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
  {W : Type w} [AddCommGroup W] [Module R W]

/-- A generator determines the coefficient parametrization of its module. -/
def generatorEquiv (g : V) (hg : IsGenerator R g) : R ≃ₗ[R] V :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton R V g) hg

@[simp] lemma generatorEquiv_apply (g : V) (hg : IsGenerator R g) (r : R) :
    generatorEquiv R g hg r = r • g := rfl

lemma generator_map_iff (e : V ≃ₗ[R] W) (g : V) :
    IsGenerator R (e g) ↔ IsGenerator R g := by
  change Function.Bijective (fun r => r • e g) ↔ _
  have h : (fun r : R => r • e g) = e ∘ (fun r : R => r • g) := by
    funext r
    exact (e.map_smul r g).symm
  rw [h]
  exact Function.Bijective.of_comp_iff' e.bijective _

lemma generator_one : IsGenerator R (1 : R) := by
  constructor
  · intro a b h
    simpa only [smul_eq_mul, mul_one] using h
  · intro a
    exact ⟨a, by simp⟩

lemma generator_iff_isUnit (r : R) : IsGenerator R r ↔ IsUnit r :=
  IsUnit.isUnit_iff_mulRight_bijective.symm

lemma exists_generator (e : V ≃ₗ[R] R) : ∃ g : V, IsGenerator R g := by
  refine ⟨e.symm 1, ?_⟩
  exact (generator_map_iff R e.symm 1).mpr (generator_one R)

/-- Any two rank-one generators differ by a unique unit, with no domain or
nonzero-ring assumption. -/
lemma generator_change (g h : V) (hg : IsGenerator R g) (hh : IsGenerator R h) :
    ∃! a : Rˣ, a.val • h = g := by
  let e := generatorEquiv R h hh
  have hr : IsUnit (e.symm g) := by
    apply (generator_iff_isUnit R _).mp
    exact (generator_map_iff R e.symm g).mpr hg
  obtain ⟨a, ha⟩ := hr
  refine ⟨a, ?_, ?_⟩
  · change e a.val = g
    rw [ha]
    exact e.apply_symm_apply g
  · intro b hb
    apply Units.ext
    apply e.injective
    change b.val • h = a.val • h
    rw [hb, ha]
    exact (e.apply_symm_apply g).symm

/-- Generator fibers transport along a linear isomorphism. -/
def generatorsEquiv (e : V ≃ₗ[R] W) : Generators R V ≃ Generators R W where
  toFun g := ⟨e g.val, (generator_map_iff R e g.val).mpr g.property⟩
  invFun h := ⟨e.symm h.val, (generator_map_iff R e.symm h.val).mpr h.property⟩
  left_inv g := Subtype.ext (e.symm_apply_apply g.val)
  right_inv h := Subtype.ext (e.apply_symm_apply h.val)

/-- The generator convention agrees exactly with the units of the coefficient ring. -/
def ringGeneratorsEquiv : Generators R R ≃ Rˣ where
  toFun g := (generator_iff_isUnit R g.val).mp g.property |>.unit
  invFun a := ⟨a.val, (generator_iff_isUnit R a.val).mpr a.isUnit⟩
  left_inv g := Subtype.ext (((generator_iff_isUnit R g.val).mp g.property).unit_spec)
  right_inv a := Units.ext (((generator_iff_isUnit R a.val).mp
    ((generator_iff_isUnit R a.val).mpr a.isUnit)).unit_spec)

end Generators

/-- Exactly two integral generators, without choosing a sign in the module. -/
lemma integral_generators (V : Type v) [AddCommGroup V] [Module ℤ V]
    (e : V ≃ₗ[ℤ] ℤ) : Nonempty (Generators ℤ V ≃ Bool) := by
  let f : ℤˣ ≃ Bool := {
    toFun := fun a => decide (a = -1)
    invFun := fun b => if b then -1 else 1
    left_inv := by
      intro a
      rcases Int.units_eq_one_or a with rfl | rfl <;> decide
    right_inv := by intro b; cases b <;> decide }
  exact ⟨(generatorsEquiv ℤ e).trans ((ringGeneratorsEquiv ℤ).trans f)⟩

/-- Over F_2 the generator is unique. This is the coefficient algebra part of
the canonical orientation assertion; no manifold computation is assumed here. -/
lemma modTwo_generator_unique (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] ZMod 2) : ∃! g : V, IsGenerator (ZMod 2) g := by
  obtain ⟨g, hg⟩ := exists_generator (ZMod 2) e
  refine ⟨g, hg, ?_⟩
  intro h hh
  obtain ⟨a, ha, _⟩ := generator_change (ZMod 2) h g hh hg
  have ha1 : a.val = (1 : ZMod 2) := by
    have hne := a.ne_zero
    have hal : a.val.val < 2 := (a.val).val_lt
    have hz : a.val.val ≠ 0 := by
      intro hz
      exact hne ((ZMod.val_eq_zero _).mp hz)
    have hone : a.val.val = 1 := by omega
    exact (ZMod.val_injective 2) (by change a.val.val = 1; exact hone)
  simpa [ha1] using ha.symm

/-- Forget smooth compatibility while keeping P104's exact chart model. -/
def forgetSmoothModel : Expected.forgetSmooth_type.{v} := @forgetSmooth

/-- The smooth bridge retains the exact topological atlas and topology. -/
lemma forgetSmooth_atlas {n : ℕ} {M : Type v} [TopologicalSpace M]
    (S : SmoothManifolds.AtlasData.SmoothManifold n .euclidean M) :
    (forgetSmooth S).atlas = S.topologicalManifold.atlas := rfl

/-- Closed and open coordinate balls use the original subspace topology. -/
lemma ball_interior_open {n : ℕ} {M : Type v} [TopologicalSpace M]
    {A : Manifold n M} (B : CoordinateBall A) : IsOpen B.interior := by
  exact B.chart.continuousOn.isOpen_inter_preimage B.chart.open_source Metric.isOpen_ball

/-- Coordinate closed balls are compact in the original manifold topology. -/
lemma ball_closed_compact {n : ℕ} {M : Type v} [TopologicalSpace M]
    {A : Manifold n M} (B : CoordinateBall A) : IsCompact B.closed := by
  letI : ProperSpace (Coordinate n) := by
    change ProperSpace (↥(Set.univ : Set (Fin n → ℝ)))
    exact ProperSpace.of_isClosed isClosed_univ
  have himage : B.chart.symm '' Metric.closedBall B.center B.radius = B.closed := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨B.chart.map_target (B.closedBall_subset hy), ?_⟩
      change B.chart (B.chart.symm y) ∈ Metric.closedBall B.center B.radius
      rw [B.chart.right_inv (B.closedBall_subset hy)]
      exact hy
    · intro hx
      exact ⟨B.chart x, hx.2, B.chart.left_inv hx.1⟩
  rw [← himage]
  exact (isCompact_closedBall B.center B.radius).image_of_continuousOn
    (B.chart.symm.continuousOn.mono B.closedBall_subset)

lemma ball_closed_closed {n : ℕ} {M : Type v} [TopologicalSpace M]
    {A : Manifold n M} (B : CoordinateBall A) : IsClosed B.closed := by
  letI := A.hausdorff
  exact (ball_closed_compact B).isClosed

/-- Restriction of support is functorial, with the paper's direction. -/
lemma supportMap_comp {M : Type v} [TopologicalSpace M] {J K L : Set M}
    (hJK : J ⊆ K) (hKL : K ⊆ L) :
    supportMap hKL ≫ supportMap hJK = supportMap (hJK.trans hKL) :=
  PairMap.ext _ _ rfl

lemma supportMap_pointMap {M : Type v} [TopologicalSpace M] {K L : Set M}
    (hKL : K ⊆ L) {x : M} (hx : x ∈ K) :
    supportMap hKL ≫ pointMap hx = pointMap (hKL hx) :=
  PairMap.ext _ _ rfl

lemma restrictPoint_support {R : Type u} [CommRing R] {M : Type v} [TopologicalSpace M]
    {K L : Set M} (hKL : K ⊆ L) {x : M} (hx : x ∈ K) (j : ℕ)
    (g : SupportedGroup R M L j) :
    restrictPoint R hx j (((relativeHomologyFunctor R R (j : ℤ)).map (supportMap hKL)) g) =
      restrictPoint R (hKL hx) j g := by
  have h := (relativeHomologyFunctor R R (j : ℤ)).map_comp (supportMap hKL) (pointMap hx)
  rw [supportMap_pointMap] at h
  exact congrArg (fun f => f g) h.symm

/-- Coordinate balls form a neighborhood basis, without local finiteness or
connectedness hypotheses on the manifold. -/
lemma coordinateBall_basis {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : Manifold n M) (x : M) {U : Set M} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ B : CoordinateBall A, x ∈ B.interior ∧ B.closed ⊆ U := by
  obtain ⟨c, hc, hxc⟩ := A.covers x
  have hV : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.symm.isOpen_inter_preimage hU
  have hxV : c x ∈ c.target ∩ c.symm ⁻¹' U :=
    ⟨c.map_source hxc, by simpa only [Set.mem_preimage, c.left_inv hxc] using hx⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hxV)
  let B : CoordinateBall A := ⟨c, hc, c x, r, hr, fun y hy => (hball hy).1⟩
  refine ⟨B, ⟨hxc, ?_⟩, ?_⟩
  · exact Metric.mem_ball_self hr
  · intro y hy
    change y ∈ c.source ∩ c ⁻¹' Metric.closedBall (c x) r at hy
    have h := (hball hy.2).2
    simpa only [Set.mem_preimage, c.left_inv hy.1] using h

/-- In dimension zero every singleton is a chart domain. -/
lemma zero_manifold_singleton_open {M : Type v} [TopologicalSpace M]
    (A : Manifold 0 M) (x : M) : IsOpen ({x} : Set M) := by
  obtain ⟨c, _, hx⟩ := A.covers x
  have hc : c.source = {x} := by
    ext y
    constructor
    · intro hy
      exact c.injOn hy hx (Subsingleton.elim _ _)
    · intro hy
      simpa only [Set.mem_singleton_iff.mp hy] using hx
  rw [← hc]
  exact c.open_source

section Extension
variable (R : Type u) [CommRing R]

lemma relativeExtensionCokernel (P : Pair.{v}) :
    ((sequence (chainFunctor R R) P).map
      ((degreeEmbedding 0).extendFunctor (ModuleCat.{max u v} R))).ShortExact :=
  P202.MayerVietoris.extend_shortExact (degreeEmbedding 0)
    (sequence (chainFunctor R R) P)
    (HomologicalComplex.shortExact_of_degreewise_shortExact _
      (P202.RelativeSingularChains.sequence_shortExact (chainFunctor R R) P))

/-- Universe-polymorphic extension of the relative complex. The upstream
sphere helper fixes universe zero; chart domains in this task need arbitrary v. -/
def relativeExtensionIso (P : Pair.{v}) :
    ordinary R R P ≅ (nonnegative R R P).extend (degreeEmbedding 0) :=
  IsColimit.coconePointUniqueUpToIso
    (cokernelIsCokernel (inclusion (ordinaryFunctor R R) P))
    (relativeExtensionCokernel R P).gIsCokernel

lemma relativeExtensionIso_projection (P : Pair.{v}) :
    projection (ordinaryFunctor R R) P ≫ (relativeExtensionIso R P).hom =
      extendMap (projection (chainFunctor R R) P) (degreeEmbedding 0) := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (cokernelIsCokernel (inclusion (ordinaryFunctor R R) P))
    (relativeExtensionCokernel R P).gIsCokernel WalkingParallelPair.one

lemma relativeExtensionIso_naturality {P Q : Pair.{v}} (f : P ⟶ Q) :
    relativeMap (ordinaryFunctor R R) f ≫ (relativeExtensionIso R Q).hom =
      (relativeExtensionIso R P).hom ≫
        extendMap (relativeMap (chainFunctor R R) f) (degreeEmbedding 0) := by
  apply (cancel_epi (projection (ordinaryFunctor R R) P)).mp
  calc
    _ = (ordinaryFunctor R R).map f.map ≫
        (projection (ordinaryFunctor R R) Q ≫ (relativeExtensionIso R Q).hom) := by
      rw [← Category.assoc, projection_map, Category.assoc]
    _ = (ordinaryFunctor R R).map f.map ≫
        extendMap (projection (chainFunctor R R) Q) (degreeEmbedding 0) := by
      rw [relativeExtensionIso_projection]
    _ = extendMap ((chainFunctor R R).map f.map ≫ projection (chainFunctor R R) Q)
        (degreeEmbedding 0) := by rw [extendMap_comp]; rfl
    _ = extendMap (projection (chainFunctor R R) P ≫ relativeMap (chainFunctor R R) f)
        (degreeEmbedding 0) := by rw [projection_map]
    _ = _ := by
      rw [← Category.assoc, relativeExtensionIso_projection, ← extendMap_comp]


/-- Nonnegative excision transports to the shared integer-indexed homology
through its actual inclusion maps, rather than just an abstract equivalence. -/
lemma excision_integer (D : P202Specs.Excision.Data.{v}) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map D.inclusion) := by
  let f := relativeMap (chainFunctor R R) D.inclusion
  haveI : QuasiIso f := by
    rw [quasiIso_iff]
    intro k
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact P202.Excision.isomorphism R D k
  haveI : IsIso (homologyMap (extendMap f (degreeEmbedding 0)) (j : ℤ)) := inferInstance
  have h := congrArg (fun g => homologyMap g (j : ℤ))
    (relativeExtensionIso_naturality R D.inclusion)
  simp only [homologyMap_comp] at h
  haveI : IsIso (homologyMap (relativeMap (ordinaryFunctor R R) D.inclusion) (j : ℤ) ≫
      homologyMap (relativeExtensionIso R D.pair).hom (j : ℤ)) := by
    rw [h]
    infer_instance
  change IsIso (homologyMap (relativeMap (ordinaryFunctor R R) D.inclusion) (j : ℤ))
  exact IsIso.of_isIso_comp_right _ (homologyMap (relativeExtensionIso R D.pair).hom (j : ℤ))

end Extension

/-- Excision data for a neighborhood of a point. Hausdorffness is used only
to make the removed closed set lie in the open punctured manifold. -/
def chartExcisionData {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : Manifold n M) (c : Chart n M) (x : c.source) : P202Specs.Excision.Data.{v} where
  pair := localPair M x.val
  removed := c.sourceᶜ
  subset := by
    intro y hy he
    change y = x.val at he
    exact hy (he ▸ x.property)
  closure_subset := by
    letI := A.hausdorff
    have hclosed : IsClosed c.sourceᶜ := c.open_source.isClosed_compl
    have hopen : IsOpen {y : M | y ≠ x.val} := isClosed_singleton.isOpen_compl
    change closure c.sourceᶜ ⊆ interior {y : M | y ≠ x.val}
    rw [hclosed.closure_eq, hopen.interior_eq]
    intro y hy he
    exact hy (he ▸ x.property)

/-- The excised subspace has precisely the original chart-domain topology. -/
def chartExcisionIso {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : Manifold n M) (c : Chart n M) (x : c.source) :
    chartLocalPair c x ≅ (chartExcisionData A c x).excised where
  hom := ⟨TopCat.ofHom ⟨fun y => ⟨y.val, by
      change ¬ y.val ∈ c.sourceᶜ
      simpa only [Set.mem_compl_iff, not_not] using y.property⟩,
    continuous_subtype_val.subtype_mk _⟩, fun _ h => h⟩
  inv := ⟨TopCat.ofHom ⟨fun y => ⟨y.val, by
      have hy := y.property
      change ¬ y.val ∈ c.sourceᶜ at hy
      simpa only [Set.mem_compl_iff, not_not] using hy⟩,
    continuous_subtype_val.subtype_mk _⟩, fun _ h => h⟩
  hom_inv_id := PairMap.ext _ _ rfl
  inv_hom_id := PairMap.ext _ _ rfl

/-- Chart excision in the actual shared relative homology theory. -/
theorem chartExcision : Expected.chartExcision.{u,v} := by
  intro R _ n M _ A c x j
  let D := chartExcisionData A c x
  haveI := excision_integer R D j
  have he : (chartExcisionIso A c x).hom ≫ D.inclusion = chartInclusion c x :=
    PairMap.ext _ _ rfl
  rw [← he, Functor.map_comp]
  infer_instance

/-- For an empty second term, the quotient projection is an isomorphism of
ordinary complexes, in all integer degrees. -/
def emptySubspaceHomologyIso (R : Type u) [CommRing R] (P : Pair.{v}) [IsEmpty P.sub]
    (j : ℤ) : homology R R P.space j ≅ relativeHomology R R P j := by
  have hinc : inclusion (ordinaryFunctor R R) P = 0 := by
    apply HomologicalComplex.Hom.ext
    funext i
    exact (P202.SingularDegreeZero.emptyOrdinaryX R R P.sub i).eq_of_src _ _
  haveI : IsIso (projection (ordinaryFunctor R R) P) := by
    change IsIso (cokernel.π (inclusion (ordinaryFunctor R R) P))
    rw [hinc]
    infer_instance
  exact (HomologicalComplex.homologyFunctor _ _ j).mapIso
    (asIso (projection (ordinaryFunctor R R) P))

/-- A zero-chart has one point, and its punctured subspace is genuinely empty. -/
lemma zero_chart_subsingleton {M : Type v} [TopologicalSpace M] (c : Chart 0 M) :
    Subsingleton c.source := by
  constructor
  intro y z
  exact Subtype.ext (c.injOn y.property z.property (Subsingleton.elim _ _))

lemma zero_chart_punctured_empty {M : Type v} [TopologicalSpace M]
    (c : Chart 0 M) (x : c.source) : IsEmpty (chartLocalPair c x).sub := by
  refine ⟨fun y => y.property ?_⟩
  exact c.injOn y.val.property x.property (Subsingleton.elim _ _)

/-- Full local computation in dimension zero, including disconnected and empty
zero-manifolds. The chart pair is the one-point/empty pair, as in the source. -/
theorem zeroLocalHomology : Expected.zeroLocalHomology.{u,v} := by
  intro R _ M _ A x j
  obtain ⟨c, _, hx⟩ := A.covers x
  let cx : c.source := ⟨x, hx⟩
  let P := chartLocalPair c cx
  letI : Subsingleton P.space := zero_chart_subsingleton c
  letI : IsEmpty P.sub := zero_chart_punctured_empty c cx
  haveI := chartExcision R 0 M A c cx j
  let e : LocalGroup R M x j ≅ homology R R P.space (j : ℤ) :=
    (asIso ((relativeHomologyFunctor R R (j : ℤ)).map (chartInclusion c cx))).symm ≪≫
      (emptySubspaceHomologyIso R P (j : ℤ)).symm
  constructor
  · intro hj
    subst j
    exact ⟨e.toLinearEquiv.trans
      ((P202.SingularDegreeZero.totallyDisconnectedZero R R P.space).trans
        (Finsupp.uniqueLinearEquiv R R cx))⟩
  · intro hj
    exact e.isZero_iff.mpr (P202.SingularDegreeZero.totallyDisconnectedHomology R R
      P.space (j : ℤ) (by exact_mod_cast hj))

/-- Assembly of the F₂ assertion from local computation and ball restriction.
Both geometric inputs are proved below, independently of orientation choices. -/
theorem modTwoOrientation_of_local_and_ball
    (hLocal : Expected.localHomology.{0,v}) (hBall : Expected.ballRestriction.{0,v}) :
    Expected.modTwoOrientation.{v} := by
  intro n M _ A
  have hUnique (x : M) : ∃! g : LocalGroup (ZMod 2) M x n, IsGenerator (ZMod 2) g := by
    obtain ⟨e⟩ := (hLocal (ZMod 2) n M A x n).1 rfl
    exact modTwo_generator_unique _ e
  let o : LocalChoice (ZMod 2) n M := fun x => Classical.choose (hUnique x)
  have ho (x : M) : IsGenerator (ZMod 2) (o x) := (Classical.choose_spec (hUnique x)).1
  have heq (x : M) (g : LocalGroup (ZMod 2) M x n) (hg : IsGenerator (ZMod 2) g) :
      g = o x := (Classical.choose_spec (hUnique x)).2 g hg
  have horient : IsOrientation (ZMod 2) A o := by
    refine ⟨ho, ?_⟩
    intro x
    obtain ⟨B, hx, _⟩ := coordinateBall_basis A x isOpen_univ (Set.mem_univ x)
    obtain ⟨e⟩ := (hBall (ZMod 2) n M A B).1
    obtain ⟨g, hg⟩ := exists_generator (ZMod 2) e
    refine ⟨B, hx, g, hg, ?_⟩
    intro y hy
    let f := LinearEquiv.ofBijective (restrictPoint (ZMod 2) (B.interior_subset_closed hy) n)
      ((hBall (ZMod 2) n M A B).2 y hy)
    exact heq y _ ((generator_map_iff (ZMod 2) f g).mpr hg)
  refine ⟨hUnique, o, horient, ?_⟩
  intro o' ho'
  funext x
  exact heq x (o' x) (ho'.1 x)

/-- The local computation gives the integral two-generator fiber count.
The covering topology is established separately using ball compatibility. -/
lemma integralFibers_of_localHomology (hLocal : Expected.localHomology.{0,v})
    (n : ℕ) (M : Type v) [TopologicalSpace M] (A : Manifold n M) (x : M) :
    Nonempty (IntegralFiber A x ≃ Bool) := by
  obtain ⟨e⟩ := (hLocal ℤ n M A x n).1 rfl
  exact integral_generators _ e

section BallComparison
variable (hBall : Expected.ballRestriction.{u,v})
  (R : Type u) [CommRing R] {n : ℕ} {M : Type v} [TopologicalSpace M]

/-- Restriction to an interior point, once the geometric ball comparison is known. -/
def ballPointEquiv {A : Manifold n M} (B : CoordinateBall A)
    {x : M} (hx : x ∈ B.interior) :
    SupportedGroup R M B.closed n ≃ₗ[R] LocalGroup R M x n :=
  LinearEquiv.ofBijective (restrictPoint R (B.interior_subset_closed hx) n)
    ((hBall R n M A B).2 x hx)

/-- Actual restriction of a supported homology class to a smaller support. -/
def supportLinear {K L : Set M} (hKL : K ⊆ L) (j : ℕ) :
    SupportedGroup R M L j →ₗ[R] SupportedGroup R M K j :=
  ((relativeHomologyFunctor R R (j : ℤ)).map (supportMap hKL)).hom

lemma restrictPoint_supportLinear {K L : Set M} (hKL : K ⊆ L)
    {x : M} (hx : x ∈ K) (j : ℕ) (g : SupportedGroup R M L j) :
    restrictPoint R hx j (supportLinear R hKL j g) = restrictPoint R (hKL hx) j g :=
  restrictPoint_support hKL hx j g

include hBall

/-- Equality at one point propagates throughout any smaller ball in the overlap.
This uses naturality and injectivity of the actual point restriction. -/
lemma ball_sections_eq_on {A A' A'' : Manifold n M}
    (B : CoordinateBall A) (C : CoordinateBall A') (D : CoordinateBall A'')
    (hDB : D.closed ⊆ B.closed) (hDC : D.closed ⊆ C.closed)
    (g : SupportedGroup R M B.closed n) (h : SupportedGroup R M C.closed n)
    {x : M} (hx : x ∈ D.interior) (hxB : x ∈ B.interior) (hxC : x ∈ C.interior)
    (he : restrictPoint R (B.interior_subset_closed hxB) n g =
      restrictPoint R (C.interior_subset_closed hxC) n h) :
    ∀ (y : M) (hyD : y ∈ D.interior) (hyB : y ∈ B.interior) (hyC : y ∈ C.interior),
      restrictPoint R (B.interior_subset_closed hyB) n g =
        restrictPoint R (C.interior_subset_closed hyC) n h := by
  have heD : supportLinear R hDB n g = supportLinear R hDC n h := by
    apply ((hBall R n M A'' D).2 x hx).1
    simpa only [restrictPoint_supportLinear] using he
  intro y hyD hyB hyC
  have heY := congrArg (restrictPoint R (D.interior_subset_closed hyD) n) heD
  simpa only [restrictPoint_supportLinear] using heY

/-- Ball compatibility forces the unit comparing any two chart generators to
be locally constant, including when the two balls use different atlases. -/
theorem transitionUnits_of_ballRestriction :
    ∀ (n : ℕ) (M : Type v) [TopologicalSpace M]
      (A A' : Manifold n M) (B : CoordinateBall A) (C : CoordinateBall A')
      (g : SupportedGroup R M B.closed n) (h : SupportedGroup R M C.closed n),
      IsGenerator R g → IsGenerator R h →
        ∃ a : ↥(B.interior ∩ C.interior) → Rˣ, IsLocallyConstant a ∧
          ∀ x : ↥(B.interior ∩ C.interior),
            restrictPoint R (B.interior_subset_closed x.property.1) n g =
              (a x).val • restrictPoint R (C.interior_subset_closed x.property.2) n h := by
  intro n M _ A A' B C g h hg hh
  have hg' (x : ↥(B.interior ∩ C.interior)) :
      IsGenerator R (restrictPoint R (B.interior_subset_closed x.property.1) n g) :=
    (generator_map_iff R (ballPointEquiv hBall R B x.property.1) g).mpr hg
  have hh' (x : ↥(B.interior ∩ C.interior)) :
      IsGenerator R (restrictPoint R (C.interior_subset_closed x.property.2) n h) :=
    (generator_map_iff R (ballPointEquiv hBall R C x.property.2) h).mpr hh
  choose a ha hau using fun x => generator_change R _ _ (hg' x) (hh' x)
  refine ⟨a, ?_, fun x => (ha x).symm⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨D, hxD, hD⟩ := coordinateBall_basis A x.val
    ((ball_interior_open B).inter (ball_interior_open C)) x.property
  have he := ball_sections_eq_on hBall R B C D
    (fun y hy => B.interior_subset_closed (hD hy).1)
    (fun y hy => C.interior_subset_closed (hD hy).2)
    g ((a x).val • h) hxD x.property.1 x.property.2 (by
      rw [map_smul]
      exact (ha x).symm)
  have hn : ∀ᶠ y : ↥(B.interior ∩ C.interior) in nhds x, y.val ∈ D.interior :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((ball_interior_open D).mem_nhds hxD)
  filter_upwards [hn] with y hy
  symm
  apply (hau y (a x))
  have hey := he y.val hy y.property.1 y.property.2
  rw [map_smul] at hey
  exact hey.symm

/-- An orientation can be transferred to a smaller ball in any covering atlas. -/
lemma orientation_transfer {A A' : Manifold n M} {o : LocalChoice R n M}
    (ho : IsOrientation R A o) : IsOrientation R A' o := by
  refine ⟨ho.1, ?_⟩
  intro x
  obtain ⟨B, hxB, g, hg, hgo⟩ := ho.2 x
  obtain ⟨D, hxD, hDB⟩ := coordinateBall_basis A' x (ball_interior_open B) hxB
  let f := supportLinear R (hDB.trans B.interior_subset_closed) n
  refine ⟨D, hxD, f g, ?_, ?_⟩
  · apply (generator_map_iff R (ballPointEquiv hBall R D hxD) (f g)).mp
    change IsGenerator R (restrictPoint R (D.interior_subset_closed hxD) n (f g))
    rw [show restrictPoint R (D.interior_subset_closed hxD) n (f g) =
      restrictPoint R (B.interior_subset_closed hxB) n g from
        restrictPoint_supportLinear R _ _ _ _]
    rw [hgo x hxB]
    exact ho.1 x
  · intro y hy
    change restrictPoint R (D.interior_subset_closed hy) n (supportLinear R _ n g) = o y
    rw [restrictPoint_supportLinear]
    exact hgo y (hDB (D.interior_subset_closed hy))

/-- Atlas independence is a consequence of the ball comparison, with no smooth
compatibility condition on either of the topological atlases. -/
theorem atlasIndependence_of_ballRestriction :
    ∀ (n : ℕ) (M : Type v) [TopologicalSpace M]
      (A A' : Manifold n M) (o : LocalChoice R n M),
      IsOrientation R A o ↔ IsOrientation R A' o := by
  intro n M _ A A' o
  exact ⟨orientation_transfer hBall R, orientation_transfer hBall R⟩

/-- For an orientation, coordinates relative to any supported ball generator
are units and vary locally constantly. -/
lemma orientation_units_on_ball {A : Manifold n M} {o : LocalChoice R n M}
    (ho : IsOrientation R A o) (B : CoordinateBall A)
    (g : SupportedGroup R M B.closed n) (hg : IsGenerator R g) :
    ∃ a : B.interior → Rˣ, IsLocallyConstant a ∧ ∀ x : B.interior,
      o x.val = (a x).val • restrictPoint R (B.interior_subset_closed x.property) n g := by
  have hg' (x : B.interior) :
      IsGenerator R (restrictPoint R (B.interior_subset_closed x.property) n g) :=
    (generator_map_iff R (ballPointEquiv hBall R B x.property) g).mpr hg
  choose a ha hau using fun x : B.interior => generator_change R _ _ (ho.1 x.val) (hg' x)
  refine ⟨a, ?_, fun x => (ha x).symm⟩
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  obtain ⟨C, hxC, h, hh, hho⟩ := ho.2 x.val
  obtain ⟨D, hxD, hD⟩ := coordinateBall_basis A x.val
    ((ball_interior_open B).inter (ball_interior_open C)) ⟨x.property, hxC⟩
  have he := ball_sections_eq_on hBall R B C D
    (fun y hy => B.interior_subset_closed (hD hy).1)
    (fun y hy => C.interior_subset_closed (hD hy).2)
    ((a x).val • g) h hxD x.property hxC (by
      rw [map_smul, ha x, hho x.val hxC])
  have hn : ∀ᶠ y : B.interior in nhds x, y.val ∈ D.interior :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((ball_interior_open D).mem_nhds hxD)
  filter_upwards [hn] with y hy
  symm
  apply hau y (a x)
  have hey := he y.val hy y.property (hD (D.interior_subset_closed hy)).2
  rw [map_smul, hho y.val (hD (D.interior_subset_closed hy)).2] at hey
  exact hey

end BallComparison

/-- Unit multiplication preserves the precise rank-one generator convention. -/
lemma generator_smul_unit (R : Type u) [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V] (a : Rˣ) (g : V) :
    IsGenerator R (a.val • g) ↔ IsGenerator R g :=
  generator_map_iff R (LinearEquiv.smulOfUnit a) g

section BallComparison
variable (hBall : Expected.ballRestriction.{u,v})
  (R : Type u) [CommRing R] {n : ℕ} {M : Type v} [TopologicalSpace M]
include hBall

omit hBall in
/-- A locally constant unit on a ball is constant on a smaller closed ball.
The statement retains the ambient topology rather than imposing a discrete
manifold model. -/
lemma coordinateBall_constant {A : Manifold n M} (B : CoordinateBall A)
    (a : B.interior → Rˣ) (ha : IsLocallyConstant a) (x : B.interior) :
    ∃ (D : CoordinateBall A) (hxD : x.val ∈ D.interior)
      (hDB : D.closed ⊆ B.interior),
      ∀ y : D.closed, a ⟨y.val, hDB y.property⟩ = a x := by
  obtain ⟨U, hU, hxU, haU⟩ := ha.exists_open x
  have hV : IsOpen (Subtype.val '' U : Set M) :=
    (ball_interior_open B).isOpenMap_subtype_val U hU
  obtain ⟨D, hxD, hD⟩ := coordinateBall_basis A x.val hV ⟨x, hxU, rfl⟩
  have hDB : D.closed ⊆ B.interior := by
    intro y hy
    obtain ⟨z, _, rfl⟩ := hD hy
    exact z.property
  refine ⟨D, hxD, hDB, ?_⟩
  intro y
  obtain ⟨z, hz, hzy⟩ := hD y.property
  have he : (⟨y.val, hDB y.property⟩ : B.interior) = z := Subtype.ext hzy.symm
  rw [he]
  exact haU z hz

/-- The ball-class and locally constant unit definitions of orientation agree,
provided the geometric restriction maps for balls are isomorphisms. -/
theorem orientationIndependence_of_ballRestriction :
    ∀ (n : ℕ) (M : Type v) [TopologicalSpace M]
      (A : Manifold n M) (o : LocalChoice R n M), IsOrientation R A o ↔
        ∀ B : CoordinateBall A, ∃ g : SupportedGroup R M B.closed n,
          IsGenerator R g ∧ ∃ a : B.interior → Rˣ, IsLocallyConstant a ∧
            ∀ x : B.interior, o x.val = (a x).val •
              restrictPoint R (B.interior_subset_closed x.property) n g := by
  intro n M _ A o
  constructor
  · intro ho B
    obtain ⟨e⟩ := (hBall R n M A B).1
    obtain ⟨g, hg⟩ := exists_generator R e
    exact ⟨g, hg, orientation_units_on_ball hBall R ho B g hg⟩
  · intro ho
    have hgen (x : M) : IsGenerator R (o x) := by
      obtain ⟨B, hxB, _⟩ := coordinateBall_basis A x isOpen_univ (Set.mem_univ x)
      obtain ⟨g, hg, a, ha, hoa⟩ := ho B
      rw [hoa ⟨x, hxB⟩]
      apply (generator_smul_unit R _ _).mpr
      exact (generator_map_iff R (ballPointEquiv hBall R B hxB) g).mpr hg
    refine ⟨hgen, ?_⟩
    intro x
    obtain ⟨B, hxB, _⟩ := coordinateBall_basis A x isOpen_univ (Set.mem_univ x)
    obtain ⟨g, hg, a, ha, hoa⟩ := ho B
    obtain ⟨D, hxD, hDB, haD⟩ := coordinateBall_constant R B a ha ⟨x, hxB⟩
    let k := (a ⟨x, hxB⟩).val • supportLinear R (hDB.trans B.interior_subset_closed) n g
    have hk (y : M) (hy : y ∈ D.interior) :
        restrictPoint R (D.interior_subset_closed hy) n k = o y := by
      change restrictPoint R (D.interior_subset_closed hy) n
        ((a ⟨x, hxB⟩).val • supportLinear R _ n g) = o y
      rw [map_smul, restrictPoint_supportLinear, hoa ⟨y, hDB (D.interior_subset_closed hy)⟩,
        haD ⟨y, D.interior_subset_closed hy⟩]
    refine ⟨D, hxD, k, ?_, hk⟩
    apply (generator_map_iff R (ballPointEquiv hBall R D hxD) k).mp
    change IsGenerator R (restrictPoint R (D.interior_subset_closed hxD) n k)
    rw [hk x hxD]
    exact hgen x

end BallComparison

/-- Every coordinate ball contains its chart center. -/
def ballCenter {n : ℕ} {M : Type v} [TopologicalSpace M]
    {A : Manifold n M} (B : CoordinateBall A) : M := B.chart.symm B.center

lemma ballCenter_mem {n : ℕ} {M : Type v} [TopologicalSpace M]
    {A : Manifold n M} (B : CoordinateBall A) : ballCenter B ∈ B.interior := by
  have hc : B.center ∈ B.chart.target :=
    B.closedBall_subset (Metric.mem_closedBall_self B.radius_pos.le)
  exact ⟨B.chart.map_target hc, by
    change B.chart (B.chart.symm B.center) ∈ Metric.ball B.center B.radius
    rw [B.chart.right_inv hc]
    exact Metric.mem_ball_self B.radius_pos⟩

/-- The support of a zero-dimensional coordinate ball is a singleton. -/
lemma zero_ball_subsingleton {M : Type v} [TopologicalSpace M]
    {A : Manifold 0 M} (B : CoordinateBall A) : B.closed.Subsingleton := by
  intro y hy z hz
  exact B.chart.injOn hy.1 hz.1 (Subsingleton.elim _ _)

/-- In dimension zero the supported pair and the local pair are isomorphic
by the actual restriction map. -/
def zeroBallPointIso {M : Type v} [TopologicalSpace M]
    {A : Manifold 0 M} (B : CoordinateBall A) {x : M} (hx : x ∈ B.interior) :
    supportedPair M B.closed ≅ localPair M x where
  hom := pointMap (B.interior_subset_closed hx)
  inv := ⟨𝟙 _, by
    intro y hy hyB
    exact hy (zero_ball_subsingleton B hyB (B.interior_subset_closed hx))⟩
  hom_inv_id := PairMap.ext _ _ rfl
  inv_hom_id := PairMap.ext _ _ rfl

/-- The full ball restriction assertion is unconditional in dimension zero. -/
theorem zeroBallRestriction (R : Type u) [CommRing R] (M : Type v)
    [TopologicalSpace M] (A : Manifold 0 M) (B : CoordinateBall A) :
    Nonempty (SupportedGroup R M B.closed 0 ≃ₗ[R] R) ∧
      ∀ (x : M) (hx : x ∈ B.interior),
        Function.Bijective (restrictPoint R (B.interior_subset_closed hx) 0) := by
  have he (x : M) (hx : x ∈ B.interior) :
      SupportedGroup R M B.closed 0 ≃ₗ[R] LocalGroup R M x 0 :=
    ((relativeHomologyFunctor R R 0).mapIso (zeroBallPointIso B hx)).toLinearEquiv
  constructor
  · obtain ⟨e⟩ := (zeroLocalHomology R M A (ballCenter B) 0).1 rfl
    exact ⟨(he (ballCenter B) (ballCenter_mem B)).trans e⟩
  · intro x hx
    exact (((relativeHomologyFunctor R R 0).mapIso (zeroBallPointIso B hx)).toLinearEquiv).bijective

/-- Only the top-degree ball computation is needed to identify the local
orientation module; the other local homology degrees are separate. -/
lemma topLocalEquiv_of_ballRestriction (hBall : Expected.ballRestriction.{u,v})
    (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
    (A : Manifold n M) (x : M) : Nonempty (LocalGroup R M x n ≃ₗ[R] R) := by
  obtain ⟨B, hx, _⟩ := coordinateBall_basis A x isOpen_univ (Set.mem_univ x)
  obtain ⟨e⟩ := (hBall R n M A B).1
  exact ⟨(ballPointEquiv hBall R B hx).symm.trans e⟩

/-- An actual homeomorphism induces the corresponding isomorphism of punctured pairs. -/
def localPairIsoOfHomeomorph {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) : localPair X x ≅ localPair Y (e x) where
  hom := ⟨TopCat.ofHom ⟨e, e.continuous⟩, fun y hy h => hy (e.injective h)⟩
  inv := ⟨TopCat.ofHom ⟨e.symm, e.symm.continuous⟩, fun y hy h => hy (by
    change e.symm y = x at h
    have hh := congrArg e h
    simpa only [e.apply_symm_apply] using hh)⟩
  hom_inv_id := PairMap.ext _ _ (by ext y; exact e.symm_apply_apply y)
  inv_hom_id := PairMap.ext _ _ (by ext y; exact e.apply_symm_apply y)

/-- Excision for any open neighborhood, in the original punctured pair. -/
def openLocalExcisionData {X : Type v} [TopologicalSpace X] [T2Space X]
    (U : Set X) (hU : IsOpen U) (x : U) : P202Specs.Excision.Data.{v} where
  pair := localPair X x.val
  removed := Uᶜ
  subset := fun _ hy he => hy (he ▸ x.property)
  closure_subset := by
    have hclosed : IsClosed Uᶜ := hU.isClosed_compl
    have hopen : IsOpen {y : X | y ≠ x.val} := isClosed_singleton.isOpen_compl
    change closure Uᶜ ⊆ interior {y : X | y ≠ x.val}
    rw [hclosed.closure_eq, hopen.interior_eq]
    exact fun _ hy he => hy (he ▸ x.property)

/-- The excised pair is the punctured neighborhood with its subtype topology. -/
def openLocalExcisionIso {X : Type v} [TopologicalSpace X] [T2Space X]
    (U : Set X) (hU : IsOpen U) (x : U) :
    localPair U x ≅ (openLocalExcisionData U hU x).excised where
  hom := ⟨TopCat.ofHom ⟨fun y => ⟨y.val, by simpa [openLocalExcisionData] using y.property⟩,
    continuous_subtype_val.subtype_mk _⟩, fun y hy he => hy (Subtype.ext he)⟩
  inv := ⟨TopCat.ofHom ⟨fun y => ⟨y.val, by simpa [openLocalExcisionData] using y.property⟩,
    continuous_subtype_val.subtype_mk _⟩, fun y hy he => hy (congrArg Subtype.val he)⟩
  hom_inv_id := PairMap.ext _ _ rfl
  inv_hom_id := PairMap.ext _ _ rfl

/-- Open neighborhoods have the same local homology in every nonnegative degree. -/
def openLocalHomologyIso (R : Type u) [CommRing R]
    {X : Type v} [TopologicalSpace X] [T2Space X]
    (U : Set X) (hU : IsOpen U) (x : U) (j : ℕ) :
    LocalGroup R U x j ≅ LocalGroup R X x.val j := by
  let D := openLocalExcisionData U hU x
  haveI := excision_integer R D j
  exact (relativeHomologyFunctor R R (j : ℤ)).mapIso (openLocalExcisionIso U hU x) ≪≫
    asIso ((relativeHomologyFunctor R R (j : ℤ)).map D.inclusion)

/-- Local homology is invariant under open partial homeomorphisms at source points. -/
def partialHomeomorphLocalHomologyIso (R : Type u) [CommRing R]
    {X Y : Type v} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    (c : OpenPartialHomeomorph X Y) (x : c.source) (j : ℕ) :
    LocalGroup R X x.val j ≅ LocalGroup R Y (c x.val) j :=
  (openLocalHomologyIso R c.source c.open_source x j).symm ≪≫
    (relativeHomologyFunctor R R (j : ℤ)).mapIso
      (localPairIsoOfHomeomorph c.toHomeomorphSourceTarget x) ≪≫
    openLocalHomologyIso R c.target c.open_target (c.toHomeomorphSourceTarget x) j

/-- Translation of the full Euclidean coordinate model takes any center to the origin. -/
def coordinateTranslation (n : ℕ) (a : Coordinate n) : Coordinate n ≃ₜ Coordinate n where
  toFun x := ⟨x.val - a.val, Set.mem_univ _⟩
  invFun x := ⟨x.val + a.val, Set.mem_univ _⟩
  left_inv x := Subtype.ext (sub_add_cancel _ _)
  right_inv x := Subtype.ext (add_sub_cancel_right _ _)
  continuous_toFun := (continuous_subtype_val.sub continuous_const).subtype_mk _
  continuous_invFun := (continuous_subtype_val.add continuous_const).subtype_mk _

@[simp] lemma coordinateTranslation_center (n : ℕ) (a : Coordinate n) :
    coordinateTranslation n a a = coordinateOrigin n := by
  apply Subtype.ext
  exact sub_self _

/-- The chart comparison for manifolds whose carrier is in the Euclidean universe. -/
theorem euclideanComparison_small : Expected.euclideanComparison.{u,0} := by
  intro R _ n M _ A x j
  letI := A.hausdorff
  obtain ⟨c, _, hx⟩ := A.covers x
  let e := partialHomeomorphLocalHomologyIso R c ⟨x, hx⟩ j
  let t := (relativeHomologyFunctor R R (j : ℤ)).mapIso
    (localPairIsoOfHomeomorph (coordinateTranslation n (c x)) (c x))
  have ht : coordinateTranslation n (c x) (c x) = coordinateOrigin n :=
    coordinateTranslation_center n (c x)
  have te := t.toLinearEquiv
  change LocalGroup R (Coordinate n) (c x) j ≃ₗ[R]
    LocalGroup R (Coordinate n) (coordinateTranslation n (c x) (c x)) j at te
  rw [ht] at te
  exact ⟨e.toLinearEquiv.trans te⟩


/-- The P104 full Euclidean subtype has the same topology as the standard Euclidean space. -/
def coordinateEuclideanHomeomorph (n : ℕ) :
    Coordinate n ≃ₜ EuclideanSpace ℝ (Fin n) :=
  ({ toFun := Subtype.val
     invFun := fun x => ⟨x, Set.mem_univ _⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl
     continuous_toFun := continuous_subtype_val
     continuous_invFun := continuous_id.subtype_mk _ } :
    Coordinate n ≃ₜ (Fin n → ℝ)).trans (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).symm

@[simp] lemma coordinateEuclideanHomeomorph_origin (n : ℕ) :
    coordinateEuclideanHomeomorph n (coordinateOrigin n) = 0 := rfl

/-- The radial coordinate is contractible. -/
lemma positiveRay_contractible : ContractibleSpace (Set.Ioi (0 : ℝ)) :=
  (convex_Ioi (0 : ℝ)).contractibleSpace ⟨1, by norm_num⟩

/-- Product with a nonempty contractible factor does not change homotopy type. -/
def contractibleProductEquiv (X : Type v) [TopologicalSpace X]
    (Y : Type v) [TopologicalSpace Y] [ContractibleSpace Y] :
    ContinuousMap.HomotopyEquiv (X × Y) X :=
  ((ContinuousMap.HomotopyEquiv.refl X).prodCongr
    (Classical.choice (ContractibleSpace.hequiv_unit Y))).trans
      (Homeomorph.prodUnique X Unit).toHomotopyEquiv

/-- Polar coordinates give a homotopy equivalence of punctured Euclidean space with its sphere. -/
def puncturedEuclideanSphereEquiv (n : ℕ) :
    ContinuousMap.HomotopyEquiv ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n+1))))
      (P202.Cellular.Sphere (n+1)) := by
  letI := positiveRay_contractible
  exact (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin (n+1)))).toHomotopyEquiv.trans
    (contractibleProductEquiv (P202.Cellular.Sphere (n+1)) (Set.Ioi (0 : ℝ)))



/-- The punctured local-pair subspace is the ordinary nonzero vector subspace. -/
def puncturedEuclideanHomeomorph (n : ℕ) :
    (localPair (EuclideanSpace ℝ (Fin (n+1))) 0).sub ≃ₜ
      ({0}ᶜ : Set (EuclideanSpace ℝ (Fin (n+1)))) :=
  Homeomorph.setCongr (by ext x; simp [localPair])

/-- The local Euclidean group is the sphere's reduced group one degree below. -/
def localEuclideanSphereIso (R : Type u) [CommRing R] (n j : ℕ) :
    LocalGroup R (Coordinate (n+1)) (coordinateOrigin (n+1)) j ≅
      reducedHomology R R (P202Specs.SpheresDisks.sphere n) ((j : ℤ)-1) := by
  let P := localPair (EuclideanSpace ℝ (Fin (n+1))) 0
  letI : Nonempty P.space := ⟨(0 : EuclideanSpace ℝ (Fin (n+1)))⟩
  letI : ContractibleSpace P.space :=
    inferInstanceAs (ContractibleSpace (EuclideanSpace ℝ (Fin (n+1))))
  let h := (relativeHomologyFunctor R R (j : ℤ)).mapIso
    (localPairIsoOfHomeomorph (coordinateEuclideanHomeomorph (n+1))
      (coordinateOrigin (n+1)))
  let e := (puncturedEuclideanHomeomorph n).toHomotopyEquiv.trans
    (puncturedEuclideanSphereEquiv n)
  exact h ≪≫ P202.SpheresDisks.contractiblePairIso R R P (j : ℤ) ≪≫
    P202.SpheresDisks.reducedHomologyIsoOfHomotopyEquiv R R e ((j : ℤ)-1)

/-- Complete local group computation for positive-dimensional full coordinate models. -/
lemma localEuclideanPositive (R : Type u) [CommRing R] (n j : ℕ) :
    (j = n+1 → Nonempty
      (LocalGroup R (Coordinate (n+1)) (coordinateOrigin (n+1)) j ≃ₗ[R] R)) ∧
    (j ≠ n+1 → IsZero
      (LocalGroup R (Coordinate (n+1)) (coordinateOrigin (n+1)) j)) := by
  let e := localEuclideanSphereIso R n j
  cases j with
  | zero =>
    haveI : Nonempty (P202Specs.SpheresDisks.sphere n) :=
      (NormedSpace.sphere_nonempty.mpr (by norm_num : (0 : ℝ) ≤ 1)).to_subtype
    constructor
    · intro hj; omega
    · intro _
      exact e.isZero_iff.mpr (P202.SingularDegreeZero.nonemptyReducedMinusOne R R
        (P202Specs.SpheresDisks.sphere n))
  | succ j =>
    have hd : (((j+1 : ℕ) : ℤ)-1) = (j : ℤ) := by omega
    have e' : LocalGroup R (Coordinate (n+1)) (coordinateOrigin (n+1)) (j+1) ≅
        reducedHomology R R (P202Specs.SpheresDisks.sphere n) (j : ℤ) := by
      simpa only [hd] using e
    constructor
    · intro hj
      obtain ⟨f⟩ := (P202.SpheresDisks.sphereHomology R R n j).1 (by omega)
      exact ⟨e'.toLinearEquiv.trans f⟩
    · intro hj
      exact e'.isZero_iff.mpr ((P202.SpheresDisks.sphereHomology R R n j).2 (by omega))

/-- Every ordinary-universe manifold has the required complete local homology. -/
theorem localHomology_small : Expected.localHomology.{u,0} := by
  intro R _ n M _ A x j
  cases n with
  | zero => exact zeroLocalHomology R M A x j
  | succ n =>
    obtain ⟨e⟩ := euclideanComparison_small R (n+1) M A x j
    constructor
    · intro hj
      obtain ⟨f⟩ := (localEuclideanPositive R n j).1 hj
      exact ⟨e.trans f⟩
    · intro hj
      exact (LinearEquiv.toModuleIso e).isZero_iff.mpr ((localEuclideanPositive R n j).2 hj)


/-- The local specialization of a cross-universe pair-homeomorphism bridge. -/
def localHomologyEquivOfHomeomorph_from_bridge
    (R : Type u) [CommRing R]
    (bridge : ∀ (P : Pair.{v}) (Q : Pair.{w}) (e : P.space ≃ₜ Q.space),
      (∀ x, e x ∈ Q.subspace ↔ x ∈ P.subspace) → (j : ℕ) →
      relativeHomology R R P (j : ℤ) ≃ₗ[R] relativeHomology R R Q (j : ℤ))
    {X : Type v} [TopologicalSpace X] {Y : Type w} [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) (j : ℕ) :
    LocalGroup R X x j ≃ₗ[R] LocalGroup R Y (e x) j :=
  bridge (localPair X x) (localPair Y (e x)) e (by
    intro y
    change e y ≠ e x ↔ y ≠ x
    exact e.injective.ne_iff) j

/-- Chart comparison uses neighborhood excision on both sides of the chart homeomorphism. -/
def partialHomeomorphLocalHomologyEquiv_from_bridge
    (R : Type u) [CommRing R]
    (bridge : ∀ (P : Pair.{v}) (Q : Pair.{w}) (e : P.space ≃ₜ Q.space),
      (∀ x, e x ∈ Q.subspace ↔ x ∈ P.subspace) → (j : ℕ) →
      relativeHomology R R P (j : ℤ) ≃ₗ[R] relativeHomology R R Q (j : ℤ))
    {X : Type v} [TopologicalSpace X] [T2Space X]
    {Y : Type w} [TopologicalSpace Y] [T2Space Y]
    (c : OpenPartialHomeomorph X Y) (x : c.source) (j : ℕ) :
    LocalGroup R X x.val j ≃ₗ[R] LocalGroup R Y (c x.val) j :=
  (openLocalHomologyIso R c.source c.open_source x j).symm.toLinearEquiv |>.trans
    (localHomologyEquivOfHomeomorph_from_bridge R bridge c.toHomeomorphSourceTarget x j) |>.trans
      (openLocalHomologyIso R c.target c.open_target (c.toHomeomorphSourceTarget x) j).toLinearEquiv

/-- Full-universe Euclidean comparison follows from the generic universe bridge. -/
theorem euclideanComparison_from_bridge
    (bridge : ∀ (R : Type u) [CommRing R] (P : Pair.{v}) (Q : Pair.{0})
      (e : P.space ≃ₜ Q.space),
      (∀ x, e x ∈ Q.subspace ↔ x ∈ P.subspace) → (j : ℕ) →
      relativeHomology R R P (j : ℤ) ≃ₗ[R] relativeHomology R R Q (j : ℤ)) :
    Expected.euclideanComparison.{u,v} := by
  intro R _ n M _ A x j
  letI := A.hausdorff
  obtain ⟨c, _, hx⟩ := A.covers x
  let e := partialHomeomorphLocalHomologyEquiv_from_bridge R (bridge R) c ⟨x, hx⟩ j
  let t := (relativeHomologyFunctor R R (j : ℤ)).mapIso
    (localPairIsoOfHomeomorph (coordinateTranslation n (c x)) (c x))
  have te := t.toLinearEquiv
  change LocalGroup R (Coordinate n) (c x) j ≃ₗ[R]
    LocalGroup R (Coordinate n) (coordinateTranslation n (c x) (c x)) j at te
  rw [coordinateTranslation_center] at te
  exact ⟨e.trans te⟩

/-- All dimensions and all nonnegative degrees follow from Euclidean comparison. -/
theorem localHomology_from_euclideanComparison
    (hEuclidean : Expected.euclideanComparison.{u,v}) : Expected.localHomology.{u,v} := by
  intro R _ n M _ A x j
  cases n with
  | zero => exact zeroLocalHomology R M A x j
  | succ n =>
    obtain ⟨e⟩ := hEuclidean R (n+1) M A x j
    constructor
    · intro hj
      obtain ⟨f⟩ := (localEuclideanPositive R n j).1 hj
      exact ⟨e.trans f⟩
    · intro hj
      apply ModuleCat.isZero_iff_subsingleton.mpr
      haveI : Subsingleton (LocalGroup R (Coordinate (n+1)) (coordinateOrigin (n+1)) j) :=
        ModuleCat.isZero_iff_subsingleton.mp ((localEuclideanPositive R n j).2 hj)
      exact e.injective.subsingleton

lemma basicSheet_open {n : ℕ} {M : Type v} [TopologicalSpace M]
    {A : Manifold n M} (B : CoordinateBall A)
    (g : SupportedGroup ℤ M B.closed n) (hg : IsGenerator ℤ g) :
    IsOpen (basicSheet B g) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨B, g, hg, rfl⟩

/-- Continuous sections coincide with the original ball-class orientation condition. -/
theorem sections_of_ballRestriction (hBall : Expected.ballRestriction.{0,v}) :
    Expected.sections.{v} := by
  intro n M _ A s
  constructor
  · intro hs
    refine ⟨fun x => (s x).property, ?_⟩
    intro x
    obtain ⟨B, hxB, _⟩ := coordinateBall_basis A x isOpen_univ (Set.mem_univ x)
    let e := ballPointEquiv hBall ℤ B hxB
    let g := e.symm (s x).val
    have hg : IsGenerator ℤ g := (generator_map_iff ℤ e.symm (s x).val).mpr (s x).property
    have hxg : (⟨x, s x⟩ : IntegralCover A) ∈ basicSheet B g := by
      refine ⟨hxB, ?_⟩
      exact (e.apply_symm_apply (s x).val).symm
    have hU : IsOpen ((fun x => (⟨x, s x⟩ : IntegralCover A)) ⁻¹' basicSheet B g) :=
      (basicSheet_open B g hg).preimage hs
    obtain ⟨D, hxD, hD⟩ := coordinateBall_basis A x (hU.inter (ball_interior_open B))
      ⟨hxg, hxB⟩
    have hDB : D.closed ⊆ B.closed := fun y hy => B.interior_subset_closed (hD hy).2
    let k := supportLinear ℤ hDB n g
    have hk (y : M) (hy : y ∈ D.interior) :
        restrictPoint ℤ (D.interior_subset_closed hy) n k = (s y).val := by
      obtain ⟨hyB, he⟩ := (hD (D.interior_subset_closed hy)).1
      change restrictPoint ℤ (D.interior_subset_closed hy) n (supportLinear ℤ hDB n g) = _
      rw [restrictPoint_supportLinear]
      exact he.symm
    refine ⟨D, hxD, k, ?_, hk⟩
    apply (generator_map_iff ℤ (ballPointEquiv hBall ℤ D hxD) k).mp
    change IsGenerator ℤ (restrictPoint ℤ (D.interior_subset_closed hxD) n k)
    rw [hk x hxD]
    exact (s x).property
  · intro ho
    apply continuous_generateFrom_iff.mpr
    rintro U ⟨B, g, hg, rfl⟩
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨hxB, he⟩ := hx
    obtain ⟨C, hxC, h, hh, hho⟩ := ho.2 x
    obtain ⟨D, hxD, hD⟩ := coordinateBall_basis A x
      ((ball_interior_open B).inter (ball_interior_open C)) ⟨hxB, hxC⟩
    have hDB : D.closed ⊆ B.closed := fun y hy => B.interior_subset_closed (hD hy).1
    have hDC : D.closed ⊆ C.closed := fun y hy => C.interior_subset_closed (hD hy).2
    have he' : restrictPoint ℤ (B.interior_subset_closed hxB) n g =
        restrictPoint ℤ (C.interior_subset_closed hxC) n h := by
      rw [hho x hxC]
      exact he.symm
    have hcomp := ball_sections_eq_on hBall ℤ B C D hDB hDC g h hxD hxB hxC he'
    apply Filter.mem_of_superset ((ball_interior_open D).mem_nhds hxD)
    intro y hy
    have hyB := (hD (D.interior_subset_closed hy)).1
    have hyC := (hD (D.interior_subset_closed hy)).2
    refine ⟨hyB, ?_⟩
    change (s y).val = restrictPoint ℤ (B.interior_subset_closed hyB) n g
    exact (hho y hyC).symm.trans (hcomp y hy hyB hyC).symm

/-- The two signs of a generator give all integral generators. -/
def integralUnitsBoolEquiv : ℤˣ ≃ Bool where
  toFun a := decide (a = -1)
  invFun b := if b then -1 else 1
  left_inv a := by rcases Int.units_eq_one_or a with rfl | rfl <;> decide
  right_inv b := by cases b <;> decide

def signedFiberEquiv {V : Type*} [AddCommGroup V] [Module ℤ V]
    (g : V) (hg : IsGenerator ℤ g) : Generators ℤ V ≃ Bool :=
  (generatorsEquiv ℤ (generatorEquiv ℤ g hg).symm).trans
    ((ringGeneratorsEquiv ℤ).trans integralUnitsBoolEquiv)

lemma signedFiberEquiv_symm_val {V : Type*} [AddCommGroup V] [Module ℤ V]
    (g : V) (hg : IsGenerator ℤ g) (b : Bool) :
    ((signedFiberEquiv g hg).symm b).val = if b then -g else g := by
  cases b <;> simp [signedFiberEquiv, integralUnitsBoolEquiv,
    ringGeneratorsEquiv, generatorsEquiv, generatorEquiv_apply]

section Cover
variable (hBall : Expected.ballRestriction.{0,v})
  {n : ℕ} {M : Type v} [TopologicalSpace M] {A : Manifold n M}

def ballLift (B : CoordinateBall A) (g : SupportedGroup ℤ M B.closed n)
    (hg : IsGenerator ℤ g) (x : B.interior) : IntegralCover A :=
  ⟨x.val, ⟨restrictPoint ℤ (B.interior_subset_closed x.property) n g,
    (generator_map_iff ℤ (ballPointEquiv hBall ℤ B x.property) g).mpr hg⟩⟩

lemma ballLift_continuous (B : CoordinateBall A) (g : SupportedGroup ℤ M B.closed n)
    (hg : IsGenerator ℤ g) : Continuous (ballLift hBall B g hg) := by
  apply continuous_generateFrom_iff.mpr
  rintro U ⟨C, h, hh, rfl⟩
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨hxC, he⟩ := hx
  obtain ⟨D, hxD, hD⟩ := coordinateBall_basis A x.val
    ((ball_interior_open B).inter (ball_interior_open C)) ⟨x.property, hxC⟩
  have hDB : D.closed ⊆ B.closed := fun y hy => B.interior_subset_closed (hD hy).1
  have hDC : D.closed ⊆ C.closed := fun y hy => C.interior_subset_closed (hD hy).2
  have hcomp := ball_sections_eq_on hBall ℤ B C D hDB hDC g h hxD x.property hxC he
  have hn : ∀ᶠ y : B.interior in nhds x, y.val ∈ D.interior :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((ball_interior_open D).mem_nhds hxD)
  apply Filter.mem_of_superset hn
  intro y hy
  have hyC := (hD (D.interior_subset_closed hy)).2
  exact ⟨hyC, hcomp y.val hy y.property hyC⟩

include hBall

lemma coverProjection_continuous : Continuous (fun z : IntegralCover A => z.1) := by
  apply continuous_def.mpr
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  obtain ⟨B, hxB, hB⟩ := coordinateBall_basis A z.1 hU hz
  let e := ballPointEquiv hBall ℤ B hxB
  let g := e.symm z.2.val
  have hg : IsGenerator ℤ g := (generator_map_iff ℤ e.symm z.2.val).mpr z.2.property
  have hzB : z ∈ basicSheet B g := ⟨hxB, (e.apply_symm_apply z.2.val).symm⟩
  apply Filter.mem_of_superset ((basicSheet_open B g hg).mem_nhds hzB)
  rintro y ⟨hy, _⟩
  exact hB (B.interior_subset_closed hy)

def signedCoverEquiv (B : CoordinateBall A) (g : SupportedGroup ℤ M B.closed n)
    (hg : IsGenerator ℤ g) :
    {z : IntegralCover A // z.1 ∈ B.interior} ≃ (B.interior × Bool) where
  toFun z := (⟨z.val.1, z.property⟩,
    signedFiberEquiv _ ((generator_map_iff ℤ (ballPointEquiv hBall ℤ B z.property) g).mpr hg) z.val.2)
  invFun p := ⟨⟨p.1.val, (signedFiberEquiv _
    ((generator_map_iff ℤ (ballPointEquiv hBall ℤ B p.1.property) g).mpr hg)).symm p.2⟩,
    p.1.property⟩
  left_inv z := by rcases z with ⟨⟨x, k⟩, hx⟩; simp
  right_inv p := by rcases p with ⟨⟨x, hx⟩, b⟩; simp

lemma signedCoverEquiv_symm_val (B : CoordinateBall A) (g : SupportedGroup ℤ M B.closed n)
    (hg : IsGenerator ℤ g) (x : B.interior) (b : Bool) :
    ((signedCoverEquiv hBall B g hg).symm (x,b)).val.2.val =
      if b then -(restrictPoint ℤ (B.interior_subset_closed x.property) n g)
      else restrictPoint ℤ (B.interior_subset_closed x.property) n g :=
  signedFiberEquiv_symm_val _ _ b

omit hBall in
lemma signedFiberEquiv_eq_iff {V : Type*} [AddCommGroup V] [Module ℤ V]
    (g : V) (hg : IsGenerator ℤ g) (k : Generators ℤ V) (b : Bool) :
    signedFiberEquiv g hg k = b ↔ k.val = if b then -g else g := by
  constructor
  · intro h
    have h' := congrArg (fun b => ((signedFiberEquiv g hg).symm b).val) h
    simpa only [Equiv.symm_apply_apply, signedFiberEquiv_symm_val] using h'
  · intro h
    apply (signedFiberEquiv g hg).symm.injective
    apply Subtype.ext
    simpa only [Equiv.symm_apply_apply] using
      h.trans (signedFiberEquiv_symm_val g hg b).symm

lemma signedCoverEquiv_preimage_sign (B : CoordinateBall A)
    (g : SupportedGroup ℤ M B.closed n) (hg : IsGenerator ℤ g) (b : Bool) :
    (fun z => (signedCoverEquiv hBall B g hg z).2) ⁻¹' {b} =
      Subtype.val ⁻¹' basicSheet B (if b then -g else g) := by
  ext z
  change signedFiberEquiv _ _ z.val.2 = b ↔ _
  rw [signedFiberEquiv_eq_iff]
  cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true,
    Set.mem_preimage, basicSheet, Set.mem_ofPred_eq, map_neg]
  · exact ⟨fun h => ⟨z.property, h⟩, fun ⟨_, h⟩ => h⟩
  · exact ⟨fun h => ⟨z.property, h⟩, fun ⟨_, h⟩ => h⟩

lemma signedCoverEquiv_continuous (B : CoordinateBall A)
    (g : SupportedGroup ℤ M B.closed n) (hg : IsGenerator ℤ g) :
    Continuous (signedCoverEquiv hBall B g hg) := by
  apply Continuous.prodMk
  · exact ((coverProjection_continuous hBall).comp continuous_subtype_val).subtype_mk _
  · apply continuous_discrete_rng.mpr
    intro b
    change IsOpen ((fun z => (signedCoverEquiv hBall B g hg z).2) ⁻¹' {b})
    rw [signedCoverEquiv_preimage_sign]
    have hsign : IsGenerator ℤ (if b then -g else g) := by
      cases b
      · exact hg
      · simpa only [ite_true, Units.val_neg, Units.val_one, neg_smul, one_smul]
          using (generator_smul_unit ℤ (-1) g).mpr hg
    exact (basicSheet_open B _ hsign).preimage continuous_subtype_val

lemma signedCoverEquiv_symm_continuous (B : CoordinateBall A)
    (g : SupportedGroup ℤ M B.closed n) (hg : IsGenerator ℤ g) :
    Continuous (signedCoverEquiv hBall B g hg).symm := by
  apply continuous_prod_of_discrete_right.mpr
  intro b
  apply Continuous.subtype_mk
  cases b
  · exact (ballLift_continuous hBall B g hg).congr fun x => by
      apply Sigma.ext (show x.val = x.val from rfl)
      apply heq_of_eq
      apply Subtype.ext
      exact (signedCoverEquiv_symm_val hBall B g hg x false).symm
  · have hg' : IsGenerator ℤ (-g) := by
      simpa only [Units.val_neg, Units.val_one, neg_smul, one_smul]
        using (generator_smul_unit ℤ (-1) g).mpr hg
    exact (ballLift_continuous hBall B (-g) hg').congr fun x => by
      apply Sigma.ext (show x.val = x.val from rfl)
      apply heq_of_eq
      apply Subtype.ext
      change restrictPoint ℤ (B.interior_subset_closed x.property) n (-g) = _
      rw [map_neg]
      exact (signedFiberEquiv_symm_val _ _ true).symm

def signedCoverHomeomorph (B : CoordinateBall A)
    (g : SupportedGroup ℤ M B.closed n) (hg : IsGenerator ℤ g) :
    {z : IntegralCover A // z.1 ∈ B.interior} ≃ₜ (B.interior × Bool) where
  toEquiv := signedCoverEquiv hBall B g hg
  continuous_toFun := signedCoverEquiv_continuous hBall B g hg
  continuous_invFun := signedCoverEquiv_symm_continuous hBall B g hg

end Cover

/-- Signed generators give the specified local product homeomorphisms. -/
theorem signedTrivializations_of_ballRestriction (hBall : Expected.ballRestriction.{0,v}) :
    Expected.signedTrivializations.{v} := by
  intro n M _ A B g hg
  refine ⟨signedCoverHomeomorph hBall B g hg, fun z => rfl, ?_⟩
  intro x b
  exact heq_of_eq (signedCoverEquiv_symm_val hBall B g hg x b)

/-- The actual generated topology is a surjective double covering. -/
theorem orientationCover_of_ballRestriction (hBall : Expected.ballRestriction.{0,v}) :
    Expected.orientationCover.{v} := by
  intro n M _ A
  have he (x : M) : Nonempty (IntegralFiber A x ≃ Bool) := by
    obtain ⟨e⟩ := topLocalEquiv_of_ballRestriction hBall ℤ n M A x
    exact integral_generators _ e
  refine ⟨?_, he⟩
  have hsurj : Function.Surjective (fun z : IntegralCover A => z.1) := by
    intro x
    obtain ⟨e⟩ := he x
    exact ⟨⟨x, e.symm false⟩, rfl⟩
  apply (P202.Topology.coveringBridge (IntegralCover A) M _).mpr
  refine ⟨?_, hsurj⟩
  intro x
  obtain ⟨B, hxB, _⟩ := coordinateBall_basis A x isOpen_univ (Set.mem_univ x)
  obtain ⟨e⟩ := (hBall ℤ n M A B).1
  obtain ⟨g, hg⟩ := exists_generator ℤ e
  have hx : IsEvenlyCovered (fun z : IntegralCover A => z.1) x Bool :=
    ⟨inferInstance, B.interior, hxB, ball_interior_open B,
      (ball_interior_open B).preimage (coverProjection_continuous hBall),
      signedCoverHomeomorph hBall B g hg, fun z => rfl⟩
  exact hx.to_isEvenlyCovered_preimage

/-- Homology is invariant under linear equivalences of short complexes, even
when the underlying modules lie in different universes. -/
def shortComplexHomologyLinearEquiv (R : Type u) [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (T : ShortComplex (ModuleCat.{w} R))
    (e₁ : S.X₁ ≃ₗ[R] T.X₁) (e₂ : S.X₂ ≃ₗ[R] T.X₂) (e₃ : S.X₃ ≃ₗ[R] T.X₃)
    (hf : ∀ x, e₂ (S.f x) = T.f (e₁ x))
    (hg : ∀ x, e₃ (S.g x) = T.g (e₂ x)) : S.homology ≃ₗ[R] T.homology := by
  let eK : LinearMap.ker S.g.hom ≃ₗ[R] LinearMap.ker T.g.hom := {
    toFun := fun x => ⟨e₂ x, by
      change T.g (e₂ x) = 0
      rw [← hg, x.property, map_zero]⟩
    invFun := fun x => ⟨e₂.symm x, by
      apply e₃.injective
      rw [map_zero, hg, e₂.apply_symm_apply]
      exact x.property⟩
    left_inv := fun x => Subtype.ext (e₂.symm_apply_apply x)
    right_inv := fun x => Subtype.ext (e₂.apply_symm_apply x)
    map_add' := fun x y => Subtype.ext (e₂.map_add x y)
    map_smul' := fun r x => Subtype.ext (e₂.map_smul r x) }
  have heK : S.moduleCatToCycles.range.map eK.toLinearMap = T.moduleCatToCycles.range := by
    ext y
    constructor
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨e₁ x, Subtype.ext (hf x).symm⟩
    · rintro ⟨x, rfl⟩
      refine ⟨S.moduleCatToCycles (e₁.symm x), ⟨e₁.symm x, rfl⟩, ?_⟩
      apply Subtype.ext
      change e₂ (S.f (e₁.symm x)) = T.f x
      rw [hf, e₁.apply_symm_apply]
  exact (S.moduleCatHomologyIso.toLinearEquiv).trans
    ((Submodule.Quotient.equiv _ _ eK heK).trans T.moduleCatHomologyIso.toLinearEquiv.symm)

/-- A change of chain coordinates can cross universes without identifying
incompatible categories of modules. -/
def homologyLinearEquiv (R : Type u) [CommRing R] {ι : Type t} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{v} R) c)
    (L : HomologicalComplex (ModuleCat.{w} R) c)
    (e : ∀ i, K.X i ≃ₗ[R] L.X i)
    (he : ∀ i j x, e j (K.d i j x) = L.d i j (e i x)) (i : ι) :
    K.homology i ≃ₗ[R] L.homology i :=
  shortComplexHomologyLinearEquiv R (K.sc i) (L.sc i)
    (e (c.prev i)) (e i) (e (c.next i)) (he _ _) (he _ _)

/-- A homeomorphism transports singular simplices across arbitrary universes. -/
def simplexHomeomorphEquiv {X : TopCat.{v}} {Y : TopCat.{w}}
    (e : X ≃ₜ Y) (n : ℕ) : Simplex X n ≃ Simplex Y n :=
  (simplexEquiv X n).trans (({
    toFun := fun s => (⟨e, e.continuous⟩ : C(X,Y)).comp s
    invFun := fun s => (⟨e.symm, e.symm.continuous⟩ : C(Y,X)).comp s
    left_inv := by intro s; ext x; exact e.symm_apply_apply (s x)
    right_inv := by intro s; ext x; exact e.apply_symm_apply (s x) } :
      C(Convexity.StdSimplex ℝ (Fin (n+1)), X) ≃
      C(Convexity.StdSimplex ℝ (Fin (n+1)), Y)).trans (simplexEquiv Y n).symm)

lemma simplexHomeomorphEquiv_apply {X : TopCat.{v}} {Y : TopCat.{w}}
    (e : X ≃ₜ Y) (n : ℕ) (s : Simplex X n) (x) :
    simplexEquiv Y n (simplexHomeomorphEquiv e n s) x = e (simplexEquiv X n s x) := by
  simp [simplexHomeomorphEquiv]

lemma simplexHomeomorphEquiv_face {X : TopCat.{v}} {Y : TopCat.{w}}
    (e : X ≃ₜ Y) (n : ℕ) (i : Fin (n+2)) (s : Simplex X (n+1)) :
    simplexHomeomorphEquiv e n (face i s) = face i (simplexHomeomorphEquiv e (n+1) s) := by
  apply (simplexEquiv Y n).injective
  ext x
  simp only [simplexHomeomorphEquiv_apply, P202.SingularChains.simplexEquiv_face,
    ContinuousMap.comp_apply]

/-- Chain transport uses the same coefficients and the original simplex bases. -/
def chainsHomeomorphEquiv (R : Type u) [CommRing R]
    {X : TopCat.{v}} {Y : TopCat.{w}} (e : X ≃ₜ Y) (n : ℕ) :
    Chains R X n ≃ₗ[R] Chains R Y n :=
  Finsupp.mapDomain.linearEquiv R R (simplexHomeomorphEquiv e n)

@[simp] lemma chainsHomeomorphEquiv_single (R : Type u) [CommRing R]
    {X : TopCat.{v}} {Y : TopCat.{w}} (e : X ≃ₜ Y) (n : ℕ) (s : Simplex X n) (r : R) :
    chainsHomeomorphEquiv R e n (Finsupp.single s r) =
      Finsupp.single (simplexHomeomorphEquiv e n s) r := by
  simp [chainsHomeomorphEquiv]

lemma chainsHomeomorphEquiv_boundary (R : Type u) [CommRing R]
    {X : TopCat.{v}} {Y : TopCat.{w}} (e : X ≃ₜ Y) (n : ℕ) (x : Chains R X (n+1)) :
    chainsHomeomorphEquiv R e n (boundary R R X n x) =
      boundary R R Y n (chainsHomeomorphEquiv R e (n+1) x) := by
  have h : (chainsHomeomorphEquiv R e n).toLinearMap.comp (boundary R R X n) =
      (boundary R R Y n).comp (chainsHomeomorphEquiv R e (n+1)).toLinearMap := by
    apply Finsupp.lhom_ext
    intro s r
    change chainsHomeomorphEquiv R e n (boundary R R X n (Finsupp.single s r)) =
      boundary R R Y n (chainsHomeomorphEquiv R e (n+1) (Finsupp.single s r))
    simp only [P202.SingularChains.boundary_single, map_sum, map_zsmul,
      chainsHomeomorphEquiv_single, simplexHomeomorphEquiv_face]
  exact congrArg (fun f => f x) h

lemma inSubspace_homeomorph {P : Pair.{v}} {Q : Pair.{w}}
    (e : P.space ≃ₜ Q.space) (h : ∀ x, e x ∈ Q.subspace ↔ x ∈ P.subspace)
    (n : ℕ) (s : Simplex P.space n) :
    InSubspace Q n (simplexHomeomorphEquiv e n s) ↔ InSubspace P n s := by
  simp only [InSubspace, simplexHomeomorphEquiv_apply, h]

/-- The homeomorphism also identifies the bases surviving the relative quotient. -/
def outsideHomeomorphEquiv {P : Pair.{v}} {Q : Pair.{w}}
    (e : P.space ≃ₜ Q.space) (h : ∀ x, e x ∈ Q.subspace ↔ x ∈ P.subspace)
    (n : ℕ) : Outside P n ≃ Outside Q n :=
  Equiv.subtypeEquiv (simplexHomeomorphEquiv e n)
    (fun s => not_congr (inSubspace_homeomorph e h n s).symm)

def relativeOutsideEquiv (R : Type u) [CommRing R] (P : Pair.{v}) (n : ℕ) :
    (nonnegative R R P).X n ≃ₗ[R] (Outside P n →₀ R) :=
  Classical.choose (P202.RelativeSingularChains.quotient_coordinates R R P n)

lemma relativeOutsideEquiv_projection (R : Type u) [CommRing R]
    (P : Pair.{v}) (n : ℕ) (c : Chains R P.space n) :
    relativeOutsideEquiv R P n ((projection (chainFunctor R R) P).f n c) =
      outsideProjection R R P n c :=
  Classical.choose_spec (P202.RelativeSingularChains.quotient_coordinates R R P n) c

def relativeChainsHomeomorphEquiv (R : Type u) [CommRing R]
    {P : Pair.{v}} {Q : Pair.{w}} (e : P.space ≃ₜ Q.space)
    (h : ∀ x, e x ∈ Q.subspace ↔ x ∈ P.subspace) (n : ℕ) :
    (nonnegative R R P).X n ≃ₗ[R] (nonnegative R R Q).X n :=
  (relativeOutsideEquiv R P n).trans
    ((Finsupp.mapDomain.linearEquiv R R (outsideHomeomorphEquiv e h n)).trans
      (relativeOutsideEquiv R Q n).symm)

lemma outsideHomeomorphEquiv_projection (R : Type u) [CommRing R]
    {P : Pair.{v}} {Q : Pair.{w}} (e : P.space ≃ₜ Q.space)
    (h : ∀ x, e x ∈ Q.subspace ↔ x ∈ P.subspace) (n : ℕ) (c : Chains R P.space n) :
    Finsupp.mapDomain.linearEquiv R R (outsideHomeomorphEquiv e h n)
      (outsideProjection R R P n c) =
      outsideProjection R R Q n (chainsHomeomorphEquiv R e n c) := by
  ext s
  change Finsupp.mapDomain (outsideHomeomorphEquiv e h n)
    (Finsupp.subtypeDomain _ c) s =
    (Finsupp.mapDomain (simplexHomeomorphEquiv e n) c) s.val
  rw [Finsupp.mapDomain_equiv_apply, Finsupp.mapDomain_equiv_apply]
  rfl

lemma relativeChainsHomeomorphEquiv_projection (R : Type u) [CommRing R]
    {P : Pair.{v}} {Q : Pair.{w}} (e : P.space ≃ₜ Q.space)
    (h : ∀ x, e x ∈ Q.subspace ↔ x ∈ P.subspace) (n : ℕ) (c : Chains R P.space n) :
    relativeChainsHomeomorphEquiv R e h n ((projection (chainFunctor R R) P).f n c) =
      (projection (chainFunctor R R) Q).f n (chainsHomeomorphEquiv R e n c) := by
  apply (relativeOutsideEquiv R Q n).injective
  simp only [relativeChainsHomeomorphEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, relativeOutsideEquiv_projection]
  exact outsideHomeomorphEquiv_projection R e h n c

lemma relativeBoundary_projection (R : Type u) [CommRing R] (P : Pair.{v})
    (n : ℕ) (c : Chains R P.space (n+1)) :
    (nonnegative R R P).d (n+1) n ((projection (chainFunctor R R) P).f (n+1) c) =
      (projection (chainFunctor R R) P).f n (boundary R R P.space n c) :=
  congrArg (fun f => f c) ((projection (chainFunctor R R) P).comm (n+1) n)

lemma relativeChainsHomeomorphEquiv_boundary (R : Type u) [CommRing R]
    {P : Pair.{v}} {Q : Pair.{w}} (e : P.space ≃ₜ Q.space)
    (h : ∀ x, e x ∈ Q.subspace ↔ x ∈ P.subspace) (n : ℕ)
    (x : (nonnegative R R P).X (n+1)) :
    relativeChainsHomeomorphEquiv R e h n ((nonnegative R R P).d (n+1) n x) =
      (nonnegative R R Q).d (n+1) n (relativeChainsHomeomorphEquiv R e h (n+1) x) := by
  have hs : Function.Surjective ((projection (chainFunctor R R) P).f (n+1)) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨c, rfl⟩ := hs x
  rw [relativeBoundary_projection, relativeChainsHomeomorphEquiv_projection,
    relativeChainsHomeomorphEquiv_projection, relativeBoundary_projection,
    chainsHomeomorphEquiv_boundary]

lemma relativeChainsHomeomorphEquiv_d (R : Type u) [CommRing R]
    {P : Pair.{v}} {Q : Pair.{w}} (e : P.space ≃ₜ Q.space)
    (h : ∀ x, e x ∈ Q.subspace ↔ x ∈ P.subspace) (i j : ℕ)
    (x : (nonnegative R R P).X i) :
    relativeChainsHomeomorphEquiv R e h j ((nonnegative R R P).d i j x) =
      (nonnegative R R Q).d i j (relativeChainsHomeomorphEquiv R e h i x) := by
  by_cases hij : (ComplexShape.down ℕ).Rel i j
  · change j + 1 = i at hij
    subst i
    exact relativeChainsHomeomorphEquiv_boundary R e h j x
  · rw [(nonnegative R R P).shape i j hij, (nonnegative R R Q).shape i j hij]
    simp

/-- Relative homology depends on the homeomorphism type of the actual pair,
without imposing a universe bound on the ambient space. -/
def relativeHomologyEquivOfHomeomorph (R : Type u) [CommRing R]
    (P : Pair.{v}) (Q : Pair.{w}) (e : P.space ≃ₜ Q.space)
    (h : ∀ x, e x ∈ Q.subspace ↔ x ∈ P.subspace) (j : ℕ) :
    relativeHomology R R P (j : ℤ) ≃ₗ[R] relativeHomology R R Q (j : ℤ) := by
  let eP := ((HomologicalComplex.homologyFunctor _ _ (j : ℤ)).mapIso
    (relativeExtensionIso R P)).toLinearEquiv.trans
      ((nonnegative R R P).extendHomologyIso (degreeEmbedding 0)
        (show (degreeEmbedding 0).f j = (j : ℤ) by change (0 : ℤ) + j = j; omega)).toLinearEquiv
  let eQ := ((HomologicalComplex.homologyFunctor _ _ (j : ℤ)).mapIso
    (relativeExtensionIso R Q)).toLinearEquiv.trans
      ((nonnegative R R Q).extendHomologyIso (degreeEmbedding 0)
        (show (degreeEmbedding 0).f j = (j : ℤ) by change (0 : ℤ) + j = j; omega)).toLinearEquiv
  exact eP.trans ((homologyLinearEquiv R (nonnegative R R P) (nonnegative R R Q)
    (relativeChainsHomeomorphEquiv R e h) (relativeChainsHomeomorphEquiv_d R e h) j).trans eQ.symm)

lemma relative_isIso_of_homology_isIso
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {P Q : Pair.{w}} (f : P ⟶ Q)
    (h₁ : ∀ j : ℤ, IsIso ((homologyFunctor R M j).map f.restrict))
    (h₂ : ∀ j : ℤ, IsIso ((homologyFunctor R M j).map f.map)) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R M j).map f) := by
  let φ := sequenceMap (ordinaryFunctor R M) f
  have hp := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.RelativeSingularChains.ordinary_short_exact R M P)
  have hq := HomologicalComplex.shortExact_of_degreewise_shortExact _
    (P202.RelativeSingularChains.ordinary_short_exact R M Q)
  apply HomologicalComplex.HomologySequence.isIso_homologyMap_τ₃ φ hp hq j
  · exact (h₁ j).epi_of_iso _
  · exact h₂ j
  · intro k _; exact h₁ k
  · intro k _; exact (h₂ k).mono_of_iso _

section Normed
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma outward_closedBall {c x y : E} {r a : ℝ}
    (hx : x ∈ Metric.closedBall c r) (hy : y ∉ Metric.closedBall c r)
    (ha : 1 ≤ a) : x + a • (y-x) ∉ Metric.closedBall c r := by
  intro hz
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hi : a⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr ha0.le, inv_le_one_of_one_le₀ ha⟩
  have hm := (convex_closedBall c r).add_smul_sub_mem hx hz hi
  have he : x + a⁻¹ • (x + a • (y-x) - x) = y := by
    simp [smul_smul, inv_mul_cancel₀ ha0.ne', sub_add_cancel]
  rw [he] at hm
  exact hy hm

/-- A continuous outward dilation taking the complement of x outside a fixed ball. -/
def escapeFactor (c x : E) (r : ℝ) (y : {y : E // y ≠ x}) : ℝ :=
  max 1 ((r + dist x c + 1) / ‖y.val-x‖)

lemma escapeFactor_ge_one (c x : E) (r : ℝ) (y : {y : E // y ≠ x}) :
    1 ≤ escapeFactor c x r y := le_max_left _ _

lemma escapeFactor_continuous (c x : E) (r : ℝ) : Continuous (escapeFactor c x r) := by
  apply continuous_const.max
  exact continuous_const.div ((continuous_subtype_val.sub continuous_const).norm)
    (fun y => norm_ne_zero_iff.mpr (sub_ne_zero.mpr y.property))

lemma escapeFactor_outside {c x : E} {r : ℝ} (y : {y : E // y ≠ x}) :
    x + escapeFactor c x r y • (y.val-x) ∉ Metric.closedBall c r := by
  have hn : 0 < ‖y.val-x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr y.property)
  have ha : 0 ≤ escapeFactor c x r y := le_trans zero_le_one (escapeFactor_ge_one c x r y)
  have hh : r + dist x c + 1 ≤ escapeFactor c x r y * ‖y.val-x‖ := by
    exact (div_le_iff₀ hn).mp (le_max_right _ _)
  have ht := norm_sub_le (x + escapeFactor c x r y • (y.val-x) - c) (x-c)
  simp [norm_smul, abs_of_nonneg ha] at ht
  intro hz
  have hz' : ‖x + escapeFactor c x r y • (y.val-x) - c‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
  rw [dist_eq_norm] at hh
  linarith

def exteriorInclusion {c x : E} {r : ℝ} (hx : x ∈ Metric.closedBall c r) :
    C(↥((Metric.closedBall c r)ᶜ), {y : E // y ≠ x}) where
  toFun y := ⟨y.val, fun hy => y.property (hy.symm ▸ hx)⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def escapeMap (c x : E) (r : ℝ) :
    C({y : E // y ≠ x}, ↥((Metric.closedBall c r)ᶜ)) where
  toFun y := ⟨x + escapeFactor c x r y • (y.val-x), escapeFactor_outside y⟩
  continuous_toFun := (continuous_const.add ((escapeFactor_continuous c x r).smul
    (continuous_subtype_val.sub continuous_const))).subtype_mk _

def escapeScale (c x : E) (r : ℝ)
    (t : unitInterval) (y : {y : E // y ≠ x}) : ℝ :=
  (1-(t : ℝ)) * escapeFactor c x r y + t

lemma escapeScale_ge_one (c x : E) (r : ℝ)
    (t : unitInterval) (y : {y : E // y ≠ x}) :
    1 ≤ escapeScale c x r t y := by
  have := escapeFactor_ge_one c x r y
  have := unitInterval.nonneg t
  have := unitInterval.le_one t
  dsimp [escapeScale]
  nlinarith

lemma escapeScale_continuous (c x : E) (r : ℝ) :
    Continuous (fun ty : unitInterval × {y : E // y ≠ x} => escapeScale c x r ty.1 ty.2) := by
  dsimp [escapeScale]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
    ((escapeFactor_continuous c x r).comp continuous_snd)).add
      (continuous_subtype_val.comp continuous_fst)

lemma escapeScale_ne_center (c x : E) (r : ℝ)
    (t : unitInterval) (y : {y : E // y ≠ x}) :
    x + escapeScale c x r t y • (y.val-x) ≠ x := by
  have ha : escapeScale c x r t y ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one (escapeScale_ge_one c x r t y)).ne'
  intro hh
  have hh' : escapeScale c x r t y • (y.val-x) = 0 := by
    exact add_left_cancel (hh.trans (add_zero x).symm)
  exact (smul_ne_zero ha (sub_ne_zero.mpr y.property)) hh'

def escapePunctureHomotopy {c x : E} {r : ℝ} (hx : x ∈ Metric.closedBall c r) :
    ContinuousMap.Homotopy ((exteriorInclusion hx).comp (escapeMap c x r))
      (ContinuousMap.id {y : E // y ≠ x}) where
  toFun ty := ⟨x + escapeScale c x r ty.1 ty.2 • (ty.2.val-x),
    escapeScale_ne_center c x r ty.1 ty.2⟩
  continuous_toFun := (continuous_const.add ((escapeScale_continuous c x r).smul
    ((continuous_subtype_val.comp continuous_snd).sub continuous_const))).subtype_mk _
  map_zero_left y := by ext; simp [escapeScale, exteriorInclusion, escapeMap]
  map_one_left y := by ext; simp [escapeScale]

def escapeExteriorHomotopy {c x : E} {r : ℝ} (hx : x ∈ Metric.closedBall c r) :
    ContinuousMap.Homotopy ((escapeMap c x r).comp (exteriorInclusion hx))
      (ContinuousMap.id ↥((Metric.closedBall c r)ᶜ)) where
  toFun ty := ⟨x + escapeScale c x r ty.1 (exteriorInclusion hx ty.2) • (ty.2.val-x),
    outward_closedBall hx ty.2.property
      (escapeScale_ge_one c x r ty.1 (exteriorInclusion hx ty.2))⟩
  continuous_toFun := (continuous_const.add
    (((escapeScale_continuous c x r).comp
      (continuous_fst.prodMk ((exteriorInclusion hx).continuous.comp continuous_snd))).smul
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const))).subtype_mk _
  map_zero_left y := by ext; simp [escapeScale, exteriorInclusion, escapeMap]
  map_one_left y := by ext; simp [escapeScale]

/-- Inclusion of the complement of a ball into the complement of any point of
its interior is a homotopy equivalence. The proof also works for boundary points. -/
def exteriorPunctureHomotopyEquiv {c x : E} {r : ℝ}
    (hx : x ∈ Metric.closedBall c r) :
    ContinuousMap.HomotopyEquiv ↥((Metric.closedBall c r)ᶜ) {y : E // y ≠ x} where
  toFun := exteriorInclusion hx
  invFun := escapeMap c x r
  left_inv := ⟨escapeExteriorHomotopy hx⟩
  right_inv := ⟨escapePunctureHomotopy hx⟩


open P202Specs.LocalOrientation

/-- The actual support restriction from a closed normed-space ball to any of
its points is an isomorphism, in every homological degree. -/
lemma closedBall_pointMap_isIso
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
    {c x : E} {r : ℝ} (hx : x ∈ Metric.closedBall c r) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R M j).map (pointMap hx)) := by
  apply relative_isIso_of_homology_isIso R M (pointMap hx)
  · intro k
    change IsIso ((homologyFunctor R M k).map (TopCat.ofHom (exteriorInclusion hx)))
    exact (P202.PrismHomotopy.homologyIso R M
      (TopCat.ofHom (exteriorInclusion hx)) (TopCat.ofHom (escapeMap c x r))
      (escapeExteriorHomotopy hx) (escapePunctureHomotopy hx) k).1
  · intro k
    change IsIso ((homologyFunctor R M k).map (𝟙 (TopCat.of E)))
    infer_instance

lemma closedBall_restrictPoint_bijective
    (R : Type u) [CommRing R] {c x : E} {r : ℝ}
    (hx : x ∈ Metric.closedBall c r) (j : ℕ) :
    Function.Bijective (restrictPoint R hx j) := by
  haveI := closedBall_pointMap_isIso R R hx (j : ℤ)
  exact (asIso ((relativeHomologyFunctor R R (j : ℤ)).map (pointMap hx))).toLinearEquiv.bijective

end Normed

/-- Inclusion of a neighborhood in the pair with support K. -/
def openSupportInclusion {X : Type v} [TopologicalSpace X] (U K : Set X) :
    supportedPair U (Subtype.val ⁻¹' K) ⟶ supportedPair X K :=
  ⟨TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩, fun _ hy => hy⟩

/-- Excision is valid for a closed support contained in an open neighborhood. -/
def openSupportExcisionData {X : Type v} [TopologicalSpace X]
    (U : Set X) (hU : IsOpen U) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U) :
    P202Specs.Excision.Data.{v} where
  pair := supportedPair X K
  removed := Uᶜ
  subset := fun _ hy hk => hy (hKU hk)
  closure_subset := by
    change closure Uᶜ ⊆ interior Kᶜ
    rw [hU.isClosed_compl.closure_eq, hK.isOpen_compl.interior_eq]
    exact fun _ hy hk => hy (hKU hk)

def openSupportExcisionIso {X : Type v} [TopologicalSpace X]
    (U : Set X) (hU : IsOpen U) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U) :
    supportedPair U (Subtype.val ⁻¹' K) ≅
      (openSupportExcisionData U hU K hK hKU).excised where
  hom := ⟨TopCat.ofHom ⟨fun y => ⟨y.val, by simpa [openSupportExcisionData] using y.property⟩,
    continuous_subtype_val.subtype_mk _⟩, fun _ hy => hy⟩
  inv := ⟨TopCat.ofHom ⟨fun y => ⟨y.val, by simpa [openSupportExcisionData] using y.property⟩,
    continuous_subtype_val.subtype_mk _⟩, fun _ hy => hy⟩
  hom_inv_id := PairMap.ext _ _ rfl
  inv_hom_id := PairMap.ext _ _ rfl

lemma openSupportInclusion_isIso (R : Type u) [CommRing R]
    {X : Type v} [TopologicalSpace X]
    (U : Set X) (hU : IsOpen U) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (j : ℕ) : IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (openSupportInclusion U K)) := by
  let D := openSupportExcisionData U hU K hK hKU
  haveI := excision_integer R D j
  have he : openSupportInclusion U K =
      (openSupportExcisionIso U hU K hK hKU).hom ≫ D.inclusion :=
    PairMap.ext _ _ rfl
  rw [he, Functor.map_comp]
  infer_instance

/-- Homeomorphisms preserving a support induce isomorphisms of supported pairs. -/
def supportedPairIsoOfHomeomorph {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (K : Set X) (L : Set Y) (h : ∀ x, x ∈ K ↔ e x ∈ L) :
    supportedPair X K ≅ supportedPair Y L where
  hom := ⟨TopCat.ofHom ⟨e, e.continuous⟩, fun x hx hL => hx ((h x).mpr hL)⟩
  inv := ⟨TopCat.ofHom ⟨e.symm, e.symm.continuous⟩, fun y hy hK => hy (by
    have hh := (h (e.symm y)).mp hK
    simpa only [e.apply_symm_apply] using hh)⟩
  hom_inv_id := PairMap.ext _ _ (by ext x; exact e.symm_apply_apply x)
  inv_hom_id := PairMap.ext _ _ (by ext x; exact e.apply_symm_apply x)

/-- Under a support-preserving homeomorphism, point restriction commutes with
exactly the corresponding maps of the supported and punctured pairs. -/
lemma supportedPairIso_point_square {X Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (K : Set X) (L : Set Y) (h : ∀ x, x ∈ K ↔ e x ∈ L)
    {x : X} (hx : x ∈ K) :
    (supportedPairIsoOfHomeomorph e K L h).hom ≫ pointMap ((h x).mp hx) =
      pointMap hx ≫ (localPairIsoOfHomeomorph e x).hom :=
  PairMap.ext _ _ rfl


/-- Reuse the shared inclusion of local pairs, retaining the implementation
name for clients that already use it. -/
abbrev openLocalInclusion {X : Type v} [TopologicalSpace X]
    (U : Set X) (x : U) : localPair U x ⟶ localPair X x.val :=
  P202Specs.LocalOrientation.openLocalInclusion U x

lemma openLocalInclusion_isIso (R : Type u) [CommRing R]
    {X : Type v} [TopologicalSpace X] [T2Space X]
    (U : Set X) (hU : IsOpen U) (x : U) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (openLocalInclusion U x)) := by
  let D := openLocalExcisionData U hU x
  haveI := excision_integer R D j
  have he : openLocalInclusion U x = (openLocalExcisionIso U hU x).hom ≫ D.inclusion :=
    PairMap.ext _ _ rfl
  rw [he, Functor.map_comp]
  infer_instance

lemma openSupportInclusion_point_square {X : Type v} [TopologicalSpace X]
    (U K : Set X) (x : U) (hx : x.val ∈ K) :
    openSupportInclusion U K ≫ pointMap hx =
      pointMap (show x ∈ Subtype.val ⁻¹' K from hx) ≫ openLocalInclusion U x :=
  PairMap.ext _ _ rfl

lemma open_pointMap_isIso_iff (R : Type u) [CommRing R]
    {X : Type v} [TopologicalSpace X] [T2Space X]
    (U : Set X) (hU : IsOpen U) (K : Set X) (hK : IsClosed K) (hKU : K ⊆ U)
    (x : U) (hx : x.val ∈ K) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (pointMap hx)) ↔
      IsIso ((relativeHomologyFunctor R R (j : ℤ)).map
        (pointMap (show x ∈ Subtype.val ⁻¹' K from hx))) := by
  let F := relativeHomologyFunctor R R (j : ℤ)
  haveI := openSupportInclusion_isIso R U hU K hK hKU j
  haveI := openLocalInclusion_isIso R U hU x j
  have hs := congrArg F.map (openSupportInclusion_point_square U K x hx)
  simp only [Functor.map_comp] at hs
  constructor
  · intro h
    haveI := h
    haveI : IsIso (F.map (pointMap (show x ∈ Subtype.val ⁻¹' K from hx)) ≫
        F.map (openLocalInclusion U x)) := by rw [← hs]; infer_instance
    exact IsIso.of_isIso_comp_right _ (F.map (openLocalInclusion U x))
  · intro h
    haveI := h
    haveI : IsIso (F.map (openSupportInclusion U K) ≫ F.map (pointMap hx)) := by
      rw [hs]; infer_instance
    exact IsIso.of_isIso_comp_left (F.map (openSupportInclusion U K)) _

/-- Transport of the actual point restriction through an open partial
homeomorphism, for closed supports contained in its source and target. -/
lemma partialHomeomorph_pointMap_isIso_iff (R : Type u) [CommRing R]
    {X Y : Type v} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    (c : OpenPartialHomeomorph X Y)
    (K : Set X) (hK : IsClosed K) (hKs : K ⊆ c.source)
    (L : Set Y) (hL : IsClosed L) (hLt : L ⊆ c.target)
    (h : ∀ x ∈ c.source, x ∈ K ↔ c x ∈ L)
    {x : X} (hx : x ∈ K) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (pointMap hx)) ↔
      IsIso ((relativeHomologyFunctor R R (j : ℤ)).map
        (pointMap ((h x (hKs hx)).mp hx))) := by
  let x' : c.source := ⟨x, hKs hx⟩
  let e := c.toHomeomorphSourceTarget
  let F := relativeHomologyFunctor R R (j : ℤ)
  let s := supportedPairIsoOfHomeomorph e (Subtype.val ⁻¹' K) (Subtype.val ⁻¹' L)
    (fun z => h z.val z.property)
  let l := localPairIsoOfHomeomorph e x'
  have hs := congrArg F.map
    (supportedPairIso_point_square e (Subtype.val ⁻¹' K) (Subtype.val ⁻¹' L)
      (fun z => h z.val z.property) (show x' ∈ Subtype.val ⁻¹' K from hx))
  simp only [Functor.map_comp] at hs
  rw [open_pointMap_isIso_iff R c.source c.open_source K hK hKs x' hx j,
    open_pointMap_isIso_iff R c.target c.open_target L hL hLt (e x')
      ((h x (hKs hx)).mp hx) j]
  constructor
  · intro hh
    haveI := hh
    haveI : IsIso (F.map s.hom ≫ F.map
        (pointMap (show e x' ∈ Subtype.val ⁻¹' L from (h x (hKs hx)).mp hx))) := by
      rw [hs]; infer_instance
    exact IsIso.of_isIso_comp_left (F.map s.hom) _
  · intro hh
    haveI := hh
    haveI : IsIso (F.map (pointMap (show x' ∈ Subtype.val ⁻¹' K from hx)) ≫
        F.map l.hom) := by rw [← hs]; infer_instance
    exact IsIso.of_isIso_comp_right _ (F.map l.hom)

/-- Lift the raw coordinate sup-norm model into the carrier's universe. -/
def coordinateLiftHomeomorph (n : ℕ) : Coordinate n ≃ₜ ULift.{v} (Fin n → ℝ) where
  toFun x := ⟨x.val⟩
  invFun x := ⟨x.down, Set.mem_univ _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := Homeomorph.ulift.symm.continuous.comp continuous_subtype_val
  continuous_invFun := Homeomorph.ulift.continuous.subtype_mk _

/-- Actual point restriction for a coordinate-ball support is an isomorphism
in every nonnegative degree, irrespective of carrier universe or dimension. -/
lemma coordinateBall_pointMap_isIso (R : Type u) [CommRing R]
    {n : ℕ} {M : Type v} [TopologicalSpace M] {A : Manifold n M}
    (B : CoordinateBall A) (x : M) (hx : x ∈ B.closed) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (pointMap hx)) := by
  letI := A.hausdorff
  let e := coordinateLiftHomeomorph.{v} n
  let c := B.chart.transHomeomorph e
  let z : ULift.{v} (Fin n → ℝ) := ⟨B.center.val⟩
  let L := Metric.closedBall z B.radius
  have hKt : B.closed ⊆ c.source := fun y hy => hy.1
  have hLt : L ⊆ c.target := by
    intro y hy
    change (e.symm y) ∈ B.chart.target
    apply B.closedBall_subset
    exact hy
  have hsup : ∀ y ∈ c.source, y ∈ B.closed ↔ c y ∈ L := by
    intro y hy
    change (y ∈ B.chart.source ∧ B.chart y ∈ Metric.closedBall B.center B.radius) ↔
      c y ∈ L
    exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  apply (partialHomeomorph_pointMap_isIso_iff R c B.closed (ball_closed_closed B) hKt
    L Metric.isClosed_closedBall hLt hsup hx j).mpr
  exact closedBall_pointMap_isIso R R ((hsup x (hKt hx)).mp hx) (j : ℤ)

lemma coordinateBall_restrictPoint_bijective (R : Type u) [CommRing R]
    {n : ℕ} {M : Type v} [TopologicalSpace M] {A : Manifold n M}
    (B : CoordinateBall A) (x : M) (hx : x ∈ B.interior) (j : ℕ) :
    Function.Bijective (restrictPoint R (B.interior_subset_closed hx) j) := by
  haveI := coordinateBall_pointMap_isIso R B x (B.interior_subset_closed hx) j
  exact (asIso ((relativeHomologyFunctor R R (j : ℤ)).map
    (pointMap (B.interior_subset_closed hx)))).toLinearEquiv.bijective

/-- The local homology computation supplies the rank-one value after the
actual coordinate-ball restriction has been shown to be an isomorphism. -/
theorem ballRestriction_of_localHomology (hLocal : Expected.localHomology.{u,v}) :
    Expected.ballRestriction.{u,v} := by
  intro R _ n M _ A B
  constructor
  · let x := ballCenter B
    have hx := ballCenter_mem B
    haveI := coordinateBall_pointMap_isIso R B x (B.interior_subset_closed hx) n
    obtain ⟨e⟩ := (hLocal R n M A x n).1 rfl
    exact ⟨(asIso ((relativeHomologyFunctor R R (n : ℤ)).map
      (pointMap (B.interior_subset_closed hx)))).toLinearEquiv.trans e⟩
  · intro x hx
    exact coordinateBall_restrictPoint_bijective R B x hx n

/-- Chart excision identifies every manifold local group with its Euclidean model. -/
theorem euclideanComparison : Expected.euclideanComparison.{u,v} :=
  euclideanComparison_from_bridge (fun R _ P Q e h j =>
    relativeHomologyEquivOfHomeomorph R P Q e h j)

/-- Complete local homology in all dimensions, degrees, and coefficient rings. -/
theorem localHomology : Expected.localHomology.{u,v} :=
  localHomology_from_euclideanComparison euclideanComparison

/-- Closed coordinate-ball classes restrict isomorphically to every interior point. -/
theorem ballRestriction : Expected.ballRestriction.{u,v} :=
  ballRestriction_of_localHomology localHomology

/-- Ball-class compatibility is exactly the locally constant unit condition. -/
theorem orientationIndependence : Expected.orientationIndependence.{u,v} := by
  intro R _
  exact orientationIndependence_of_ballRestriction ballRestriction R

/-- Orientations depend only on the given topological manifold. -/
theorem atlasIndependence : Expected.atlasIndependence.{u,v} := by
  intro R _
  exact atlasIndependence_of_ballRestriction ballRestriction R

/-- Changes between local generators are locally constant units. -/
theorem transitionUnits : Expected.transitionUnits.{u,v} := by
  intro R _
  exact transitionUnits_of_ballRestriction ballRestriction R

/-- The integral local generators form a surjective double covering. -/
theorem orientationCover : Expected.orientationCover.{v} :=
  orientationCover_of_ballRestriction ballRestriction

/-- Signed chart generators give the stipulated local product homeomorphisms. -/
theorem signedTrivializations : Expected.signedTrivializations.{v} :=
  signedTrivializations_of_ballRestriction ballRestriction

/-- Continuous sections of the generator cover are exactly integral orientations. -/
theorem sections : Expected.sections.{v} :=
  sections_of_ballRestriction ballRestriction

/-- The unique local generators over F₂ give the unique compatible orientation. -/
theorem modTwoOrientation : Expected.modTwoOrientation.{v} :=
  modTwoOrientation_of_local_and_ball localHomology ballRestriction

end P202.LocalOrientation
