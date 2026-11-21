import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Duality.CompactOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Duality.LocalOrientation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.MayerVietoris

/-! Work on paper.tex, thm:p202-compact-orientation.
The proof uses the closed-support exact sequence, convex chart supports,
finite chain boundary carriers, and compact finite-union induction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v w
namespace P202.CompactOrientation
open P202Specs.CompactOrientation P202Specs.LocalOrientation
open P202Specs.SingularChains P202Specs.RelativeSingularChains

variable (R : Type u) [CommRing R] {n : ℕ} {M : Type v} [TopologicalSpace M]

/-- Naturality of the prescribed point values under restriction of support. -/
lemma hasLocalValues_restrict {o : LocalChoice R n M} {K L : Set M}
    (hKL : K ⊆ L) {g : SupportedGroup R M L n} (hg : HasLocalValues R o L g) :
    HasLocalValues R o K
      (((relativeHomologyFunctor R R (n : ℤ)).map (supportMap hKL)) g) := by
  intro x hx
  rw [P202.LocalOrientation.restrictPoint_support hKL hx n g]
  exact hg x (hKL hx)

/-- Injectivity into the product gives uniqueness for any prescribed local values. -/
lemma hasLocalValues_unique {o : LocalChoice R n M} {K : Set M}
    (hK : Function.Injective (localRestrictions R K n))
    {g h : SupportedGroup R M K n}
    (hg : HasLocalValues R o K g) (hh : HasLocalValues R o K h) : g = h := by
  apply hK
  funext x
  exact (hg x.val x.property).trans (hh x.val x.property).symm

/-- The compatibility conclusion needs only detection at the smaller support. -/
lemma compatible_of_detection {o : LocalChoice R n M} {K L : Set M}
    (hK : Function.Injective (localRestrictions R K n)) (hKL : K ⊆ L)
    {gK : SupportedGroup R M K n} {gL : SupportedGroup R M L n}
    (hgK : HasLocalValues R o K gK) (hgL : HasLocalValues R o L gL) :
    ((relativeHomologyFunctor R R (n : ℤ)).map (supportMap hKL)) gL = gK :=
  hasLocalValues_unique R hK (hasLocalValues_restrict R hKL hgL) hgK

/-- Compatibility is a consequence of the independently stated detection theorem. -/
theorem compatibility_of_localDetection (h : Expected.localDetection.{u,v}) :
    Expected.compatibility.{u,v} := by
  intro R _ n M _ A o K L hK _ hKL gK gL hgK hgL
  exact compatible_of_detection R (h R n M A K hK) hKL hgK hgL

/-- For an empty support the relative complex is the cokernel of the identity. -/
lemma emptySupport_isZero (j : ℕ) : IsZero (SupportedGroup R M ∅ j) := by
  let P := supportedPair M (∅ : Set M)
  have : IsIso P.inclusion := by
    let e : P.sub ≅ P.space := TopCat.isoOfHomeo {
      toFun := Subtype.val
      invFun := fun x => ⟨x, by simp [P, supportedPair]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk (fun x : P.space =>
        show x ∈ P.subspace from by simp [P, supportedPair]) }
    change IsIso e.hom
    infer_instance
  have : IsIso (inclusion (ordinaryFunctor R R) P) := by
    change IsIso ((ordinaryFunctor R R).map P.inclusion)
    infer_instance
  have hC : IsZero (ordinary R R P) := isZero_cokernel_of_epi _
  exact ((ordinary R R P).sc (j : ℤ)).isZero_homology_of_isZero_X₂
    ((HomologicalComplex.eval _ _ (j : ℤ)).map_isZero hC)

/-- The empty compact has exactly one class with the vacuous point values. -/
lemma emptySupport_unique (o : LocalChoice R n M) :
    ∃! g : SupportedGroup R M ∅ n, HasLocalValues R o ∅ g := by
  refine ⟨0, ?_, ?_⟩
  · intro x hx
    exact False.elim hx
  · intro g _
    exact (ModuleCat.isZero_iff_subsingleton.mp (emptySupport_isZero R n)).elim g 0

/-- Ball supports are detected by any one point, even at the boundary. -/
lemma ball_localDetection (A : Manifold n M) (B : CoordinateBall A) :
    Function.Injective (localRestrictions R B.closed n) := by
  intro g h he
  let x := P202.LocalOrientation.ballCenter B
  have hx : x ∈ B.closed :=
    B.interior_subset_closed (P202.LocalOrientation.ballCenter_mem B)
  have := P202.LocalOrientation.coordinateBall_pointMap_isIso R B x hx n
  apply (asIso ((relativeHomologyFunctor R R (n : ℤ)).map
    (pointMap hx))).toLinearEquiv.injective
  exact congrFun he ⟨x, hx⟩

/-- The upstream ball-to-point comparison is in every degree, hence gives
vanishing above n on balls without any orientation assumption. -/
lemma ball_aboveDimension (A : Manifold n M) (B : CoordinateBall A)
    (j : ℕ) (hj : n < j) : IsZero (SupportedGroup R M B.closed j) := by
  let x := P202.LocalOrientation.ballCenter B
  have hx := B.interior_subset_closed (P202.LocalOrientation.ballCenter_mem B)
  have := P202.LocalOrientation.coordinateBall_pointMap_isIso R B x hx j
  exact (asIso ((relativeHomologyFunctor R R (j : ℤ)).map
    (pointMap hx))).isZero_iff.mpr
      ((P202.LocalOrientation.localHomology R n M A x j).2 (by omega))

/-- Orientation compatibility itself supplies supported classes locally. This
is only a neighborhood result; no compact gluing theorem is assumed. -/
lemma neighborhood_class (A : Manifold n M) (o : Orientation R A) (x : M) :
    ∃ B : CoordinateBall A, x ∈ B.interior ∧
      ∀ K : Set M, K ⊆ B.interior →
        ∃ g : SupportedGroup R M K n, HasLocalValues R o.val K g := by
  obtain ⟨B, hxB, g, _, hg⟩ := o.property.2 x
  refine ⟨B, hxB, fun K hK => ?_⟩
  refine ⟨((relativeHomologyFunctor R R (n : ℤ)).map
    (supportMap (hK.trans B.interior_subset_closed))) g, ?_⟩
  intro y hy
  rw [P202.LocalOrientation.restrictPoint_support]
  exact hg y (hK hy)

/-- The projection for the whole support is the actual ordinary homology
comparison and is bijective, without compactness or manifold hypotheses. -/
lemma absoluteToSupported_bijective (j : ℕ) :
    Function.Bijective (absoluteToSupported R M j) := by
  let P := supportedPair M (Set.univ : Set M)
  let : IsEmpty P.sub := ⟨fun x => x.property (Set.mem_univ _)⟩
  exact (P202.LocalOrientation.emptySubspaceHomologyIso R P (j : ℤ)).toLinearEquiv.bijective

/-- Once compact-supported existence and uniqueness is proved, the ordinary
fundamental class follows by the canonical empty-subspace comparison. -/
theorem ordinaryFundamentalClass_of_compactClass (h : Expected.compactClass.{u,v}) :
    Expected.ordinaryFundamentalClass.{u,v} := by
  intro R _ n M _ A o hM
  have hb := absoluteToSupported_bijective (M := M) R n
  refine ⟨hb, ?_⟩
  obtain ⟨g, hg, huniq⟩ := h R n M A o Set.univ hM
  obtain ⟨a, ha⟩ := hb.2 g
  refine ⟨a, ?_, ?_⟩
  · change HasLocalValues R o.val Set.univ (absoluteToSupported R M n a)
    rw [ha]
    exact hg
  · intro b hb'
    apply hb.1
    exact (huniq _ hb').trans ha.symm

/-- The compact finite-union induction used twice in the source. The local
hypothesis covers every compact subset of each piece, so that intersections
in the induction satisfy the same hypothesis. -/
lemma finite_compact_union [T2Space M] (P : Set M → Prop)
    (h0 : P ∅)
    (hu : ∀ K L : Set M, IsCompact K → IsCompact L →
      P K → P L → P (K ∩ L) → P (K ∪ L))
    {ι : Type*} (s : Finset ι) (C : ι → Set M)
    (hc : ∀ i ∈ s, IsCompact (C i))
    (hp : ∀ i ∈ s, ∀ K : Set M, IsCompact K → K ⊆ C i → P K) :
    P (⋃ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty => simpa using h0
  | @insert a s ha ih =>
    have hsc : IsCompact (⋃ i ∈ s, C i) :=
      s.isCompact_biUnion (fun i hi => hc i (Finset.mem_insert_of_mem hi))
    have hca := hc a (Finset.mem_insert_self a s)
    have he : (⋃ i ∈ s, C i) ∩ C a = ⋃ i ∈ s, C i ∩ C a := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iUnion]
      aesop
    have hci : P ((⋃ i ∈ s, C i) ∩ C a) := by
      rw [he]
      apply ih (fun i => C i ∩ C a)
      · intro i hi
        exact (hc i (Finset.mem_insert_of_mem hi)).inter_right hca.isClosed
      · intro i hi K hK hKi
        exact hp i (Finset.mem_insert_of_mem hi) K hK (hKi.trans Set.inter_subset_left)
    have hm : P ((⋃ i ∈ s, C i) ∪ C a) := hu _ _ hsc hca
      (ih C (fun i hi => hc i (Finset.mem_insert_of_mem hi))
        (fun i hi => hp i (Finset.mem_insert_of_mem hi)))
      (hp a (Finset.mem_insert_self a s) (C a) hca Set.Subset.rfl) hci
    simpa only [Finset.set_biUnion_insert, Set.union_comm] using hm

/-- Compact sets admit finite compact chart pieces lying inside coordinate
balls, with no assumptions on connectedness or dimension. -/
lemma compact_ball_pieces (A : Manifold n M) (K : Set M) (hK : IsCompact K) :
    ∃ (s : Finset (CoordinateBall A)) (C : CoordinateBall A → Set M),
      K = ⋃ B ∈ s, C B ∧
      (∀ B ∈ s, IsCompact (C B)) ∧
      ∀ B ∈ s, ∃ D : CoordinateBall A, C B ⊆ D.interior := by
  classical
  let := A.hausdorff
  have hsmall (x : M) : ∃ B D : CoordinateBall A,
      x ∈ B.interior ∧ B.closed ⊆ D.interior := by
    obtain ⟨D, hxD, _⟩ := P202.LocalOrientation.coordinateBall_basis A x
      isOpen_univ (Set.mem_univ x)
    obtain ⟨B, hxB, hBD⟩ := P202.LocalOrientation.coordinateBall_basis A x
      (P202.LocalOrientation.ball_interior_open D) hxD
    exact ⟨B, D, hxB, hBD⟩
  let good : Set (CoordinateBall A) := {B | ∃ D : CoordinateBall A, B.closed ⊆ D.interior}
  have hcover : K ⊆ ⋃ B : good, B.val.interior := by
    intro x _
    obtain ⟨B, D, hxB, hBD⟩ := hsmall x
    exact Set.mem_iUnion.mpr ⟨⟨B, D, hBD⟩, hxB⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun B : good => B.val.interior)
    (fun B => P202.LocalOrientation.ball_interior_open B.val) hcover
  let t : Finset (CoordinateBall A) := s.image Subtype.val
  let C : CoordinateBall A → Set M := fun B => K ∩ B.closed
  refine ⟨t, C, ?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨B, hBs, hxB⟩ := Set.mem_iUnion₂.mp (hs hx)
      exact Set.mem_iUnion₂.mpr ⟨B.val, Finset.mem_image.mpr ⟨B, hBs, rfl⟩,
        hx, B.val.interior_subset_closed hxB⟩
    · intro x hx
      obtain ⟨B, _, hxB⟩ := Set.mem_iUnion₂.mp hx
      exact hxB.1
  · intro B _
    exact hK.inter_right (P202.LocalOrientation.ball_closed_closed B)
  · intro B hB
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨D, hD⟩ := b.property
    exact ⟨D, Set.inter_subset_right.trans hD⟩

/-- Reduction of an arbitrary compact support to the ball-local theorem and
binary compact gluing. This is the full geometric assembly, rather than a
local-finiteness assumption on M or on the compact support. -/
lemma compact_induction (A : Manifold n M) (P : Set M → Prop)
    (h0 : P ∅)
    (hl : ∀ (B : CoordinateBall A) (K : Set M), IsCompact K → K ⊆ B.interior → P K)
    (hu : ∀ K L : Set M, IsCompact K → IsCompact L →
      P K → P L → P (K ∩ L) → P (K ∪ L))
    (K : Set M) (hK : IsCompact K) : P K := by
  let := A.hausdorff
  obtain ⟨s, C, he, hc, hp⟩ := compact_ball_pieces A K hK
  rw [he]
  apply finite_compact_union P h0 hu s C hc
  intro B hB J hJ hJC
  obtain ⟨D, hD⟩ := hp B hB
  exact hl D J hJ (hJC.trans hD)

/-- Binary compact-support gluing, in the exact form needed by the source's
induction. The closed-support exact sequence below proves this input without manifold
hypotheses. -/
def SupportGluing (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M] : Prop :=
  ∀ K L : Set M, IsCompact K → IsCompact L →
    (∀ j : ℕ, IsZero (SupportedGroup R M (K ∩ L) (j+1)) →
      ∀ a b : SupportedGroup R M (K ∪ L) j,
        P202.LocalOrientation.supportLinear R Set.subset_union_left j a =
          P202.LocalOrientation.supportLinear R Set.subset_union_left j b →
        P202.LocalOrientation.supportLinear R Set.subset_union_right j a =
          P202.LocalOrientation.supportLinear R Set.subset_union_right j b → a = b) ∧
    (∀ (j : ℕ) (a : SupportedGroup R M K j) (b : SupportedGroup R M L j),
      P202.LocalOrientation.supportLinear R Set.inter_subset_left j a =
        P202.LocalOrientation.supportLinear R Set.inter_subset_right j b →
      ∃ c : SupportedGroup R M (K ∪ L) j,
        P202.LocalOrientation.supportLinear R Set.subset_union_left j c = a ∧
        P202.LocalOrientation.supportLinear R Set.subset_union_right j c = b)

/-- The three simultaneous assertions at a support. Existence is quantified
over all actual orientations, and no compactness is hidden in the definition. -/
def SupportAssertions (A : Manifold n M) (K : Set M) : Prop :=
  (∀ j : ℕ, n < j → IsZero (SupportedGroup R M K j)) ∧
    Function.Injective (localRestrictions R K n) ∧
    ∀ o : Orientation R A, ∃ g : SupportedGroup R M K n, HasLocalValues R o.val K g

lemma emptySupport_assertions (A : Manifold n M) : SupportAssertions R A ∅ := by
  refine ⟨fun j _ => emptySupport_isZero R j, ?_, ?_⟩
  · intro a b _
    exact (ModuleCat.isZero_iff_subsingleton.mp (emptySupport_isZero R n)).elim a b
  · intro o
    obtain ⟨g, hg, _⟩ := emptySupport_unique R o.val
    exact ⟨g, hg⟩

/-- Complete algebraic induction step. In particular existence on K and L
uses detection on their intersection to obtain the equality needed for gluing. -/
lemma union_assertions (A : Manifold n M) (hglue : SupportGluing R M)
    (K L : Set M) (hcK : IsCompact K) (hcL : IsCompact L)
    (hK : SupportAssertions R A K) (hL : SupportAssertions R A L)
    (hI : SupportAssertions R A (K ∩ L)) : SupportAssertions R A (K ∪ L) := by
  obtain ⟨hinj, hlift⟩ := hglue K L hcK hcL
  refine ⟨?_, ?_, ?_⟩
  · intro j hj
    apply ModuleCat.isZero_iff_subsingleton.mpr
    have hKs := ModuleCat.isZero_iff_subsingleton.mp (hK.1 j hj)
    have hLs := ModuleCat.isZero_iff_subsingleton.mp (hL.1 j hj)
    exact ⟨fun a b => hinj j (hI.1 (j+1) (by omega)) a b
      (hKs.elim _ _) (hLs.elim _ _)⟩
  · intro a b hab
    apply hinj n (hI.1 (n+1) (by omega)) a b
    · apply hK.2.1
      funext x
      change restrictPoint R x.property n
        (P202.LocalOrientation.supportLinear R Set.subset_union_left n a) =
        restrictPoint R x.property n
          (P202.LocalOrientation.supportLinear R Set.subset_union_left n b)
      rw [P202.LocalOrientation.restrictPoint_supportLinear,
        P202.LocalOrientation.restrictPoint_supportLinear]
      exact congrFun hab ⟨x.val, Or.inl x.property⟩
    · apply hL.2.1
      funext x
      change restrictPoint R x.property n
        (P202.LocalOrientation.supportLinear R Set.subset_union_right n a) =
        restrictPoint R x.property n
          (P202.LocalOrientation.supportLinear R Set.subset_union_right n b)
      rw [P202.LocalOrientation.restrictPoint_supportLinear,
        P202.LocalOrientation.restrictPoint_supportLinear]
      exact congrFun hab ⟨x.val, Or.inr x.property⟩
  · intro o
    obtain ⟨a, ha⟩ := hK.2.2 o
    obtain ⟨b, hb⟩ := hL.2.2 o
    have hi : P202.LocalOrientation.supportLinear R Set.inter_subset_left n a =
        P202.LocalOrientation.supportLinear R Set.inter_subset_right n b :=
      hasLocalValues_unique R hI.2.1
        (hasLocalValues_restrict R Set.inter_subset_left ha)
        (hasLocalValues_restrict R Set.inter_subset_right hb)
    obtain ⟨c, hca, hcb⟩ := hlift n a b hi
    refine ⟨c, ?_⟩
    intro x hx
    rcases hx with hx | hx
    · rw [← P202.LocalOrientation.restrictPoint_supportLinear R
        Set.subset_union_left hx n c, hca]
      exact ha x hx
    · rw [← P202.LocalOrientation.restrictPoint_supportLinear R
        Set.subset_union_right hx n c, hcb]
      exact hb x hx

/-- The entire compact-to-global assembly is proved here. Its premises are supplied below by closed-support gluing and the chart-local
compact-support argument. -/
lemma compact_assertions_of_ballLocal_and_gluing (A : Manifold n M)
    (hg : SupportGluing R M)
    (hl : ∀ (B : CoordinateBall A) (K : Set M), IsCompact K → K ⊆ B.interior →
      SupportAssertions R A K)
    (K : Set M) (hK : IsCompact K) : SupportAssertions R A K :=
  compact_induction A (SupportAssertions R A) (emptySupport_assertions R A)
    hl (fun K L hcK hcL => union_assertions R A hg K L hcK hcL) K hK

/-- Assembly of all five independent source conclusions from its two
local inputs. Both inputs are proved below. -/
theorem compactTheorem_of_ballLocal_and_gluing
    (hg : ∀ (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M],
      T2Space M → SupportGluing R M)
    (hl : ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
      (A : Manifold n M) (B : CoordinateBall A) (K : Set M),
      IsCompact K → K ⊆ B.interior → SupportAssertions R A K) :
    Expected.compactClass.{u,v} ∧ Expected.aboveDimension.{u,v} ∧
      Expected.localDetection.{u,v} ∧ Expected.compatibility.{u,v} ∧
      Expected.ordinaryFundamentalClass.{u,v} := by
  have hall (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
      (A : Manifold n M) (K : Set M) (hK : IsCompact K) : SupportAssertions R A K :=
    compact_assertions_of_ballLocal_and_gluing R A (hg R M A.hausdorff)
      (hl R n M A) K hK
  have hclass : Expected.compactClass.{u,v} := by
    intro R _ n M _ A o K hK
    have h := hall R n M A K hK
    obtain ⟨g, hg⟩ := h.2.2 o
    exact ⟨g, hg, fun g' hg' => hasLocalValues_unique R h.2.1 hg' hg⟩
  have hdetect : Expected.localDetection.{u,v} := by
    intro R _ n M _ A K hK
    exact (hall R n M A K hK).2.1
  exact ⟨hclass, fun R _ n M _ A K hK => (hall R n M A K hK).1, hdetect,
    compatibility_of_localDetection hdetect, ordinaryFundamentalClass_of_compactClass hclass⟩

/-- Coordinate-ball interiors are connected in the actual manifold topology.
We use the raw coordinate sup-norm ball; no smooth structure is required. -/
lemma ball_interior_isPreconnected (A : Manifold n M) (B : CoordinateBall A) :
    IsPreconnected B.interior := by
  let f : (Fin n → ℝ) → M := fun z => B.chart.symm ⟨z, Set.mem_univ _⟩
  have hf : ContinuousOn f (Metric.ball B.center.val B.radius) := by
    apply B.chart.symm.continuousOn.comp (continuous_id.subtype_mk
      (fun z : Fin n → ℝ => Set.mem_univ z)).continuousOn
    intro z hz
    exact B.closedBall_subset (Metric.ball_subset_closedBall hz)
  have he : f '' Metric.ball B.center.val B.radius = B.interior := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hz' : (⟨z, Set.mem_univ _⟩ : Coordinate n) ∈
          Metric.ball B.center B.radius := hz
      have hzt := B.closedBall_subset (Metric.ball_subset_closedBall hz')
      refine ⟨B.chart.map_target hzt, ?_⟩
      change B.chart (B.chart.symm ⟨z, Set.mem_univ _⟩) ∈ Metric.ball B.center B.radius
      rw [B.chart.right_inv hzt]
      exact hz
    · intro hx
      refine ⟨(B.chart x).val, hx.2, ?_⟩
      exact B.chart.left_inv hx.1
  rw [← he]
  exact (convex_ball B.center.val B.radius).isPreconnected.image f hf

/-- Every orientation has a ball class with all its prescribed interior values.
This extends the defining local compatibility to each coordinate ball. -/
lemma oriented_ball_class (A : Manifold n M) (o : Orientation R A)
    (B : CoordinateBall A) :
    ∃ g : SupportedGroup R M B.closed n,
      ∀ (x : M) (hx : x ∈ B.interior),
        restrictPoint R (B.interior_subset_closed hx) n g = o.val x := by
  let : PreconnectedSpace B.interior :=
    isPreconnected_iff_preconnectedSpace.mp (ball_interior_isPreconnected A B)
  obtain ⟨g, _, a, ha, hoa⟩ :=
    (P202.LocalOrientation.orientationIndependence R n M A o.val).mp o.property B
  let x : B.interior := ⟨P202.LocalOrientation.ballCenter B,
    P202.LocalOrientation.ballCenter_mem B⟩
  refine ⟨(a x).val • g, ?_⟩
  intro y hy
  rw [map_smul, hoa ⟨y, hy⟩, ha.apply_eq_of_preconnectedSpace x ⟨y, hy⟩]

/-- Existence on every subset of a coordinate ball's interior. Compactness is
needed for detection and vanishing, but not for this existence assertion. -/
lemma ball_subset_class (A : Manifold n M) (o : Orientation R A)
    (B : CoordinateBall A) (K : Set M) (hK : K ⊆ B.interior) :
    ∃ g : SupportedGroup R M K n, HasLocalValues R o.val K g := by
  obtain ⟨g, hg⟩ := oriented_ball_class R A o B
  refine ⟨P202.LocalOrientation.supportLinear R (hK.trans B.interior_subset_closed) n g, ?_⟩
  intro x hx
  rw [P202.LocalOrientation.restrictPoint_supportLinear]
  exact hg x (hK hx)

/-- The final reduction has the gluing and local detection inputs. Ball-local
existence is supplied by the unconditional proof above. -/
theorem compactTheorem_of_ballDetection_and_gluing
    (hg : ∀ (R : Type u) [CommRing R] (M : Type v) [TopologicalSpace M],
      T2Space M → SupportGluing R M)
    (hl : ∀ (R : Type u) [CommRing R] (n : ℕ) (M : Type v) [TopologicalSpace M]
      (A : Manifold n M) (B : CoordinateBall A) (K : Set M),
      IsCompact K → K ⊆ B.interior →
      (∀ j : ℕ, n < j → IsZero (SupportedGroup R M K j)) ∧
        Function.Injective (localRestrictions R K n)) :
    Expected.compactClass.{u,v} ∧ Expected.aboveDimension.{u,v} ∧
      Expected.localDetection.{u,v} ∧ Expected.compatibility.{u,v} ∧
      Expected.ordinaryFundamentalClass.{u,v} := by
  apply compactTheorem_of_ballLocal_and_gluing hg
  intro R _ n M _ A B K hK hKB
  have h := hl R n M A B K hK hKB
  exact ⟨h.1, h.2, fun o => ball_subset_class R A o B K hKB⟩

namespace CompactGluing
open P202Specs.MayerVietoris P202Specs.SmallChainHomology
open P202.MayerVietoris
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryProducts

/-- The open complement of the intersection, covered by the two complements. -/
def complementCover {K L : Set M} (hK : IsClosed K) (hL : IsClosed L) :
    CoverPair.{v,0} :=
  CoverPair.ofSets ⟨TopCat.of ↥((K ∩ L)ᶜ), ∅⟩
    {x | x.val ∉ K} {x | x.val ∉ L}
    (hK.isOpen_compl.preimage continuous_subtype_val)
    (hL.isOpen_compl.preimage continuous_subtype_val)
    (by ext x; simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true];
        exact not_and_or.mp x.property)

variable {K L : Set M} (hK : IsClosed K) (hL : IsClosed L)

/-- Flattening the nested subtypes identifies the cover pieces with the
original complements; all topologies are the given subspace topologies. -/
def leftHomeo : (complementCover hK hL).leftPair.space ≃ₜ (supportedPair M K).sub where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, fun h => x.property h.1⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def rightHomeo : (complementCover hK hL).rightPair.space ≃ₜ (supportedPair M L).sub where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, fun h => x.property h.2⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def intersectionHomeo : (complementCover hK hL).intersectionPair.space ≃ₜ
    (supportedPair M (K ∪ L)).sub where
  toFun x := ⟨x.val.val, fun h => h.elim x.property.1 x.property.2⟩
  invFun x := ⟨⟨x.val, fun h => x.property (Or.inl h.1)⟩,
    fun h => x.property (Or.inl h), fun h => x.property (Or.inr h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

abbrev ambient := (ordinaryFunctor R R).obj (TopCat.of M)
abbrev rel (K : Set M) := ordinary R R (supportedPair M K)

/-- Diagonal with a negative second component, before taking quotients. -/
def diagonal : ambient R (M := M) ⟶ ambient R (M := M) ⊞ ambient R (M := M) :=
  biprod.lift (𝟙 _) (-𝟙 _)

def addition : ambient R (M := M) ⊞ ambient R (M := M) ⟶ ambient R (M := M) :=
  biprod.desc (𝟙 _) (𝟙 _)

lemma diagonal_addition : diagonal R (M := M) ≫ addition R = 0 := by
  simp [diagonal, addition]

lemma diagonal_shortExact :
    (ShortComplex.mk (diagonal R (M := M)) (addition R) (diagonal_addition R)).ShortExact := by
  let s : (ShortComplex.mk (diagonal R (M := M)) (addition R)
      (diagonal_addition R)).Splitting := {
    r := biprod.fst
    s := biprod.inr
    f_r := by simp [diagonal]
    s_g := by simp [addition]
    id := by
      apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
        simp [diagonal, addition] }
  exact s.shortExact

abbrev leftIso := (ordinaryFunctor R R).mapIso (TopCat.isoOfHomeo (leftHomeo hK hL))
abbrev rightIso := (ordinaryFunctor R R).mapIso (TopCat.isoOfHomeo (rightHomeo hK hL))
abbrev intersectionIso := (ordinaryFunctor R R).mapIso
  (TopCat.isoOfHomeo (intersectionHomeo hK hL))

abbrev small := ordinarySmallComplex R (complementCover hK hL)

abbrev into (J : Set M) := inclusion (ordinaryFunctor R R) (supportedPair M J)
abbrev proj (J : Set M) := projection (ordinaryFunctor R R) (supportedPair M J)
abbrev restrict {J T : Set M} (h : J ⊆ T) :=
  relativeMap (ordinaryFunctor R R) (supportMap h)
abbrev subrestrict {J T : Set M} (h : J ⊆ T) :=
  (ordinaryFunctor R R).map (supportMap h).restrict

lemma subrestrict_into {J T : Set M} (h : J ⊆ T) :
    subrestrict R h ≫ into R J = into R T := by
  rw [← Functor.map_comp]
  rfl

/-- The first and middle terms of the small-chain sequence, flattened to
subspaces of M before taking the supported quotients. -/
def firstSub :
    (ordinaryFunctor R R).obj (supportedPair M (K ∪ L)).sub ⟶
      (ordinaryFunctor R R).obj (supportedPair M K).sub ⊞
        (ordinaryFunctor R R).obj (supportedPair M L).sub :=
  biprod.lift (subrestrict R Set.subset_union_left) (-subrestrict R Set.subset_union_right)

def smallSum :
    (ordinaryFunctor R R).obj (supportedPair M K).sub ⊞
      (ordinaryFunctor R R).obj (supportedPair M L).sub ⟶ small R hK hL :=
  biprod.map (leftIso R hK hL).inv (rightIso R hK hL).inv ≫
    ordinarySmallSum R (complementCover hK hL)

lemma firstSub_iso :
    (intersectionIso R hK hL).hom ≫ firstSub R (K := K) (L := L) =
      chainFirst (theoryFunctor R .ordinary) (complementCover hK hL) ≫
        biprod.map (leftIso R hK hL).hom (rightIso R hK hL).hom := by
  apply biprod.hom_ext <;>
    simp only [firstSub, chainFirst, Category.assoc, biprod.lift_fst,
      biprod.lift_snd, biprod.map_fst, biprod.map_snd,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      Preadditive.comp_neg, Preadditive.neg_comp]
  · change (ordinaryFunctor R R).map _ ≫ (ordinaryFunctor R R).map _ =
      (ordinaryFunctor R R).map _ ≫ (ordinaryFunctor R R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · congr 1
    change (ordinaryFunctor R R).map _ ≫ (ordinaryFunctor R R).map _ =
      (ordinaryFunctor R R).map _ ≫ (ordinaryFunctor R R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl

lemma firstSub_smallSum : firstSub R (K := K) (L := L) ≫ smallSum R hK hL = 0 := by
  apply (cancel_epi (intersectionIso R hK hL).hom).mp
  rw [← Category.assoc, firstSub_iso]
  rw [Category.assoc]
  unfold smallSum
  change chainFirst (theoryFunctor R .ordinary) (complementCover hK hL) ≫
    (biprod.mapIso (leftIso R hK hL) (rightIso R hK hL)).hom ≫
    (biprod.mapIso (leftIso R hK hL) (rightIso R hK hL)).inv ≫ _ = _
  rw [Iso.hom_inv_id_assoc, ordinaryFirst_smallSum, comp_zero]

lemma sub_small_shortExact :
    (ShortComplex.mk (firstSub R (K := K) (L := L))
      (smallSum R hK hL) (firstSub_smallSum R hK hL)).ShortExact := by
  let e : ShortComplex.mk
      (chainFirst (theoryFunctor R .ordinary) (complementCover hK hL))
      (ordinarySmallSum R (complementCover hK hL)) (ordinaryFirst_smallSum R _) ≅
      ShortComplex.mk (firstSub R (K := K) (L := L))
        (smallSum R hK hL) (firstSub_smallSum R hK hL) :=
    ShortComplex.isoMk (intersectionIso R hK hL)
    (biprod.mapIso (leftIso R hK hL) (rightIso R hK hL)) (Iso.refl (small R hK hL))
    (firstSub_iso R hK hL)
    (show biprod.map (leftIso R hK hL).hom (rightIso R hK hL).hom ≫
        smallSum R hK hL = ordinarySmallSum R (complementCover hK hL) ≫ 𝟙 _ by
      change (biprod.mapIso (leftIso R hK hL) (rightIso R hK hL)).hom ≫
        (biprod.mapIso (leftIso R hK hL) (rightIso R hK hL)).inv ≫ _ = _
      simp only [Iso.hom_inv_id_assoc, Category.comp_id])
  exact (ShortComplex.shortExact_iff_of_iso e).mp
    (ordinarySmall_shortExact R (complementCover hK hL))

/-- Embed the small chains in the ambient ordinary singular complex. -/
def smallInto : small R hK hL ⟶ ambient R (M := M) :=
  ordinarySmallInclusion R (complementCover hK hL) ≫ into R (K ∩ L)

lemma smallInto_mono : Mono (smallInto R hK hL) := by
  haveI := ordinarySmallInclusion_mono R (complementCover hK hL)
  dsimp [smallInto]
  infer_instance

lemma smallSum_into : smallSum R hK hL ≫ smallInto R hK hL =
    biprod.desc (into R K) (into R L) := by
  unfold smallSum smallInto
  rw [Category.assoc, ← Category.assoc (ordinarySmallSum R _), ordinarySmallSum_inclusion]
  apply biprod.hom_ext'
  · simp only [Category.assoc, biprod.inl_map_assoc, chainSum, biprod.inl_desc_assoc,
      biprod.inl_desc]
    change (ordinaryFunctor R R).map _ ≫ (ordinaryFunctor R R).map _ ≫
      (ordinaryFunctor R R).map _ = (ordinaryFunctor R R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl
  · simp only [Category.assoc, biprod.inr_map_assoc, chainSum, biprod.inr_desc_assoc,
      biprod.inr_desc]
    change (ordinaryFunctor R R).map _ ≫ (ordinaryFunctor R R).map _ ≫
      (ordinaryFunctor R R).map _ = (ordinaryFunctor R R).map _
    rw [← Functor.map_comp, ← Functor.map_comp]
    rfl

abbrev middleInto := biprod.map (into R K) (into R L)

/-- Map of the small-chain row to the split diagonal/addition row. -/
def rowInclusion :
    ShortComplex.mk (firstSub R (K := K) (L := L))
      (smallSum R hK hL) (firstSub_smallSum R hK hL) ⟶
    ShortComplex.mk (diagonal R (M := M)) (addition R) (diagonal_addition R) :=
  ShortComplex.Hom.mk (into R (K ∪ L)) (middleInto R (K := K) (L := L))
    (smallInto R hK hL)
    (by
      dsimp only [diagonal, firstSub, middleInto, subrestrict, into, inclusion,
        supportedPair, supportMap, PairMap.restrict]
      apply biprod.hom_ext <;>
        simp only [Category.assoc, biprod.lift_fst, biprod.lift_snd,
          biprod.map_fst, biprod.map_snd, biprod.lift_fst_assoc,
          biprod.lift_snd_assoc, Preadditive.comp_neg, Preadditive.neg_comp,
          Category.comp_id]
      all_goals rw [← Functor.map_comp]
      all_goals rfl)
    (by
      rw [smallSum_into]
      apply biprod.hom_ext' <;>
        simp only [middleInto, addition, biprod.inl_map_assoc, biprod.inr_map_assoc,
          biprod.inl_desc, biprod.inr_desc, Category.comp_id]
      all_goals exact Category.comp_id _)

abbrev middleProj := biprod.map (proj R K) (proj R L)

/-- The direct sum of the two canonical quotient projections. -/
def middleProjColimit : IsColimit (CokernelCofork.ofπ
    (middleProj R (K := K) (L := L))
    (show middleInto R (K := K) (L := L) ≫ middleProj R = 0 by
      apply biprod.hom_ext' <;> simp [middleInto, middleProj, proj, into])) :=
  RelativeBridge.biprodCokernelIsColimit _ _

/-- The signed restriction from the union to the two compact supports. -/
def firstRel : rel R (K ∪ L) ⟶ rel R K ⊞ rel R L :=
  biprod.lift (restrict R Set.subset_union_left) (-restrict R Set.subset_union_right)

lemma restrict_proj {J T : Set M} (h : J ⊆ T) :
    proj R T ≫ restrict R h = proj R J := by
  dsimp only [proj, restrict]
  rw [projection_map]
  change (ordinaryFunctor R R).map (𝟙 _) ≫ _ = _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

lemma firstRel_proj : proj R (K ∪ L) ≫ firstRel R (K := K) (L := L) =
    diagonal R ≫ middleProj R := by
  apply biprod.hom_ext
  · calc
      _ = proj R K := by
        change (proj R (K ∪ L) ≫ firstRel R) ≫ biprod.fst = proj R K
        rw [Category.assoc, firstRel, biprod.lift_fst, restrict_proj]
      _ = _ := by
        change proj R K = (diagonal R ≫ middleProj R) ≫ biprod.fst
        rw [Category.assoc, middleProj, biprod.map_fst, ← Category.assoc]
        change proj R K = (biprod.lift (𝟙 (ambient R (M:=M))) (-𝟙 _) ≫ biprod.fst) ≫ proj R K
        rw [biprod.lift_fst, Category.id_comp]
  · calc
      _ = -proj R L := by
        change (proj R (K ∪ L) ≫ firstRel R) ≫ biprod.snd = -proj R L
        rw [Category.assoc, firstRel, biprod.lift_snd, Preadditive.comp_neg, restrict_proj]
      _ = _ := by
        change -proj R L = (diagonal R ≫ middleProj R) ≫ biprod.snd
        rw [Category.assoc, middleProj, biprod.map_snd, ← Category.assoc]
        change -proj R L = (biprod.lift (𝟙 (ambient R (M:=M))) (-𝟙 _) ≫ biprod.snd) ≫ proj R L
        rw [biprod.lift_snd, Preadditive.neg_comp, Category.id_comp]

/-- Addition descends to the quotient by small chains in the complement. -/
def lastRel : rel R K ⊞ rel R L ⟶ cokernel (smallInto R hK hL) :=
  (middleProjColimit R (K := K) (L := L)).desc (CokernelCofork.ofπ
    (addition R ≫ cokernel.π (smallInto R hK hL)) (by
      rw [← Category.assoc]
      have he : middleInto R (K := K) (L := L) ≫ addition R =
          biprod.desc (into R K) (into R L) := by
        apply biprod.hom_ext' <;>
        simp only [middleInto, addition, biprod.inl_map_assoc, biprod.inr_map_assoc,
          biprod.inl_desc, biprod.inr_desc, Category.comp_id]
        all_goals exact Category.comp_id _
      rw [he, ← smallSum_into R hK hL, Category.assoc, cokernel.condition, comp_zero]))

@[reassoc (attr := simp)]
lemma lastRel_proj : middleProj R (K := K) (L := L) ≫ lastRel R hK hL =
    addition R ≫ cokernel.π (smallInto R hK hL) :=
  Cofork.IsColimit.π_desc (middleProjColimit R)

lemma firstRel_lastRel : firstRel R (K := K) (L := L) ≫ lastRel R hK hL = 0 := by
  apply (cancel_epi (proj R (K ∪ L))).mp
  rw [← Category.assoc, firstRel_proj, Category.assoc, lastRel_proj,
    ← Category.assoc, diagonal_addition, zero_comp, comp_zero]

abbrev quotientRow := ShortComplex.mk (firstRel R (K := K) (L := L))
  (lastRel R hK hL) (firstRel_lastRel R hK hL)

def rowProjection :
    ShortComplex.mk (diagonal R (M := M)) (addition R) (diagonal_addition R) ⟶
      quotientRow R hK hL :=
  ShortComplex.Hom.mk (proj R (K ∪ L)) (middleProj R)
    (cokernel.π (smallInto R hK hL)) (firstRel_proj R) (lastRel_proj R hK hL)

/-- The short exact quotient sequence underlying compact-support gluing. -/
lemma quotient_shortExact : (quotientRow R hK hL).ShortExact := by
  haveI : Mono (rowInclusion R hK hL).τ₃ := smallInto_mono R hK hL
  apply RelativeBridge.quotient_row_shortExact (rowInclusion R hK hL)
    (rowProjection R hK hL)
    (show rowInclusion R hK hL ≫ rowProjection R hK hL = 0 by
      apply ShortComplex.hom_ext
      · exact cokernel.condition _
      · change middleInto R ≫ middleProj R = 0
        apply biprod.hom_ext' <;> simp [middleInto, middleProj, proj, into]
      · exact cokernel.condition _)
    (sub_small_shortExact R hK hL) (diagonal_shortExact R)
  · exact cokernelIsCokernel _
  · exact middleProjColimit R
  · exact cokernelIsCokernel _

/-- Comparison of the last quotient with the actual pair for K ∩ L. -/
def comparison : cokernel (smallInto R hK hL) ⟶ rel R (K ∩ L) :=
  cokernel.map _ _ (ordinarySmallInclusion R (complementCover hK hL)) (𝟙 _)
    (by simp [smallInto])

lemma comparison_quasiIso : QuasiIso (comparison R hK hL) := by
  let φ : ShortComplex.cokernelSequence (smallInto R hK hL) ⟶
      sequence (ordinaryFunctor R R) (supportedPair M (K ∩ L)) :=
    ShortComplex.Hom.mk (ordinarySmallInclusion R (complementCover hK hL)) (𝟙 _)
      (comparison R hK hL) (by simp [smallInto]) (by simp [comparison, projection])
  have hs : (ShortComplex.cokernelSequence (smallInto R hK hL)).ShortExact := by
    haveI := smallInto_mono R hK hL
    exact { exact := ShortComplex.cokernelSequence_exact _
            mono_f := smallInto_mono R hK hL
            epi_g := inferInstance }
  have ht : (sequence (ordinaryFunctor R R) (supportedPair M (K ∩ L))).ShortExact :=
    HomologicalComplex.shortExact_of_degreewise_shortExact _
      (P202.RelativeSingularChains.sequence_shortExact _ _)
  exact HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hs ht
    (ordinarySmallInclusion_quasiIso R (complementCover hK hL)) (by infer_instance)

lemma lastRel_comparison : lastRel R hK hL ≫ comparison R hK hL =
    biprod.desc (restrict R Set.inter_subset_left) (restrict R Set.inter_subset_right) := by
  apply (cancel_epi (middleProj R (K := K) (L := L))).mp
  rw [← Category.assoc, lastRel_proj, Category.assoc]
  apply biprod.hom_ext' <;>
    simp [comparison, addition, middleProj, proj, restrict, projection_map, supportMap, supportedPair,
      Category.id_comp]
  all_goals exact Category.id_comp _

/-- Homology commutes with the binary direct sum in the quotient sequence. -/
def homologyMiddleIso (j : ℕ) :
    (rel R K ⊞ rel R L).homology (j : ℤ) ≅
      SupportedGroup R M K j ⊞ SupportedGroup R M L j :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R)
    (ComplexShape.down ℤ) (j : ℤ)).mapBiprod _ _

lemma firstRel_homology (j : ℕ) :
    homologyMap (firstRel R (K := K) (L := L)) (j : ℤ) ≫
      (homologyMiddleIso R (K := K) (L := L) j).hom =
      biprod.lift (homologyMap (restrict R Set.subset_union_left) (j : ℤ))
        (-homologyMap (restrict R Set.subset_union_right) (j : ℤ)) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R)
    (ComplexShape.down ℤ) (j : ℤ)
  change H.map (biprod.lift (restrict R Set.subset_union_left)
      (-restrict R Set.subset_union_right)) ≫ (H.mapBiprod (rel R K) (rel R L)).hom =
        biprod.lift (H.map (restrict R Set.subset_union_left))
          (-H.map (restrict R Set.subset_union_right))
  rw [← Functor.map_neg]
  exact biprod.map_lift_mapBiprod H (rel R K) (rel R L) _ _

lemma lastRel_homology (j : ℕ) :
    (homologyMiddleIso R (K := K) (L := L) j).hom ≫
      biprod.desc (homologyMap (restrict R Set.inter_subset_left) (j : ℤ))
        (homologyMap (restrict R Set.inter_subset_right) (j : ℤ)) =
      homologyMap (lastRel R hK hL) (j : ℤ) ≫
        homologyMap (comparison R hK hL) (j : ℤ) := by
  rw [← homologyMap_comp, lastRel_comparison]
  exact biprod.mapBiprod_hom_desc
    (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R)
      (ComplexShape.down ℤ) (j : ℤ)) (rel R K) (rel R L) _ _

include hK hL in
/-- Compact-support gluing is valid for any two closed supports. Compactness
is only needed elsewhere in the fundamental class theorem. -/
theorem closed_support_gluing :
    (∀ j : ℕ, IsZero (SupportedGroup R M (K ∩ L) (j+1)) →
      ∀ a b : SupportedGroup R M (K ∪ L) j,
        P202.LocalOrientation.supportLinear R Set.subset_union_left j a =
          P202.LocalOrientation.supportLinear R Set.subset_union_left j b →
        P202.LocalOrientation.supportLinear R Set.subset_union_right j a =
          P202.LocalOrientation.supportLinear R Set.subset_union_right j b → a = b) ∧
    (∀ (j : ℕ) (a : SupportedGroup R M K j) (b : SupportedGroup R M L j),
      P202.LocalOrientation.supportLinear R Set.inter_subset_left j a =
        P202.LocalOrientation.supportLinear R Set.inter_subset_right j b →
      ∃ c : SupportedGroup R M (K ∪ L) j,
        P202.LocalOrientation.supportLinear R Set.subset_union_left j c = a ∧
        P202.LocalOrientation.supportLinear R Set.subset_union_right j c = b) := by
  have hq := quotient_shortExact R hK hL
  haveI := comparison_quasiIso R hK hL
  constructor
  · intro j hz a b hleft hright
    change homologyMap (restrict R Set.subset_union_left) (j : ℤ) a =
      homologyMap (restrict R Set.subset_union_left) (j : ℤ) b at hleft
    change homologyMap (restrict R Set.subset_union_right) (j : ℤ) a =
      homologyMap (restrict R Set.subset_union_right) (j : ℤ) b at hright
    have hz' : IsZero ((cokernel (smallInto R hK hL)).homology ((j : ℤ)+1)) := by
      have hi := (asIso (homologyMap (comparison R hK hL) ((j : ℤ)+1))).isZero_iff
      apply hi.mpr
      change IsZero (relativeHomology R R (supportedPair M (K ∩ L)) ((j : ℤ)+1))
      have he : ((j+1 : ℕ) : ℤ) = (j : ℤ)+1 := by simp
      rw [← he]
      exact hz
    have hm : Mono (homologyMap (firstRel R (K := K) (L := L)) (j : ℤ)) :=
      (hq.homology_exact₁ ((j : ℤ)+1) (j : ℤ) (by simp)).mono_g
        (hz'.eq_of_src _ _)
    apply (ModuleCat.mono_iff_injective _).mp hm
    apply (homologyMiddleIso R (K := K) (L := L) j).toLinearEquiv.injective
    have h₁ := congrArg (fun f => f a) (firstRel_homology R (K := K) (L := L) j)
    have h₂ := congrArg (fun f => f b) (firstRel_homology R (K := K) (L := L) j)
    rw [ModuleCat.comp_apply] at h₁ h₂
    change (homologyMiddleIso R (K := K) (L := L) j).hom _ =
      (homologyMiddleIso R (K := K) (L := L) j).hom _
    rw [h₁, h₂]
    apply biprod_element_ext
    · simpa only [← ModuleCat.comp_apply, biprod.lift_fst] using hleft
    · simpa only [← ModuleCat.comp_apply, biprod.lift_snd, ModuleCat.hom_neg,
        LinearMap.neg_apply] using congrArg Neg.neg hright
  · intro j a b hab
    let e := homologyMiddleIso R (K := K) (L := L) j
    let y : ↥(SupportedGroup R M K j ⊞ SupportedGroup R M L j) :=
      (biprod.inl : SupportedGroup R M K j ⟶
        SupportedGroup R M K j ⊞ SupportedGroup R M L j) a -
        (biprod.inr : SupportedGroup R M L j ⟶
          SupportedGroup R M K j ⊞ SupportedGroup R M L j) b
    have hy : (biprod.desc
        (homologyMap (restrict R Set.inter_subset_left) (j : ℤ))
        (homologyMap (restrict R Set.inter_subset_right) (j : ℤ))) y = 0 := by
      dsimp [y]
      rw [map_sub]
      simp only [← ModuleCat.comp_apply, biprod.inl_desc, biprod.inr_desc]
      exact sub_eq_zero.mpr hab
    have hy' : homologyMap (lastRel R hK hL) (j : ℤ) (e.inv y) = 0 := by
      apply (asIso (homologyMap (comparison R hK hL) (j : ℤ))).toLinearEquiv.injective
      rw [map_zero]
      change homologyMap (comparison R hK hL) (j : ℤ)
        (homologyMap (lastRel R hK hL) (j : ℤ) (e.inv y)) = 0
      have hh := congrArg (fun f => f (e.inv y)) (lastRel_homology R hK hL j)
      simp only [ModuleCat.comp_apply] at hh
      have hcancel : e.hom (e.inv y) = y := by
        rw [← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply]
      exact hh.symm.trans ((congrArg (fun z =>
        (biprod.desc (homologyMap (restrict R Set.inter_subset_left) (j : ℤ))
          (homologyMap (restrict R Set.inter_subset_right) (j : ℤ))) z) hcancel).trans hy)
    obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp
      (hq.homology_exact₂ (j : ℤ)) (e.inv y) hy'
    change homologyMap (firstRel R (K := K) (L := L)) (j : ℤ) c = e.inv y at hc
    have he : (biprod.lift
        (homologyMap (restrict R Set.subset_union_left) (j : ℤ))
        (-(homologyMap (restrict R Set.subset_union_right) (j : ℤ)))) c = y := by
      rw [← firstRel_homology R (K := K) (L := L) j, ModuleCat.comp_apply, hc]
      change e.hom (e.inv y) = y
      rw [← ModuleCat.comp_apply, e.inv_hom_id, ModuleCat.id_apply]
    refine ⟨c, ?_, ?_⟩
    · change homologyMap (restrict R Set.subset_union_left) (j : ℤ) c = a
      have hh := congrArg (fun z => (biprod.fst :
          SupportedGroup R M K j ⊞ SupportedGroup R M L j ⟶ _) z) he
      simpa only [y, map_sub, ← ModuleCat.comp_apply, biprod.lift_fst,
        biprod.inl_fst, biprod.inr_fst, ModuleCat.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
        sub_zero] using hh
    · have hh := congrArg (fun z => (biprod.snd :
          SupportedGroup R M K j ⊞ SupportedGroup R M L j ⟶ _) z) he
      have hh' : -(homologyMap (restrict R Set.subset_union_right) (j : ℤ)) c = -b := by
        simpa only [y, map_sub, ← ModuleCat.comp_apply, biprod.lift_snd,
          biprod.inl_snd, biprod.inr_snd, ModuleCat.id_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
          zero_sub, ModuleCat.hom_neg, LinearMap.neg_apply] using hh
      change homologyMap (restrict R Set.subset_union_right) (j : ℤ) c = b
      exact neg_injective hh' 

end CompactGluing

/-- The compact gluing input follows from the closed-support exact sequence. -/
theorem supportGluing [T2Space M] : SupportGluing R M := by
  intro K L hK hL
  exact CompactGluing.closed_support_gluing R hK.isClosed hL.isClosed

open P202.LocalOrientation

section ConvexSupports
variable {E : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An outward ray from a point in a convex support remains in its complement. -/
lemma outward_convex {K : Set E} (hK : Convex ℝ K) {x y : E} {a : ℝ}
    (hx : x ∈ K) (hy : y ∉ K) (ha : 1 ≤ a) : x + a • (y-x) ∉ K := by
  intro hz
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hi : a⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨inv_nonneg.mpr ha0.le, inv_le_one_of_one_le₀ ha⟩
  have hm := hK.add_smul_sub_mem hx hz hi
  have he : x + a⁻¹ • (x + a • (y-x) - x) = y := by
    simp [smul_smul, inv_mul_cancel₀ ha0.ne', sub_add_cancel]
  rw [he] at hm
  exact hy hm

def convexExteriorInclusion {K : Set E} {x : E} (hx : x ∈ K) :
    C(↥(Kᶜ), {y : E // y ≠ x}) where
  toFun y := ⟨y.val, fun hy => y.property (hy.symm ▸ hx)⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def convexEscapeMap {K : Set E} {c x : E} {r : ℝ}
    (hKb : K ⊆ Metric.closedBall c r) :
    C({y : E // y ≠ x}, ↥(Kᶜ)) where
  toFun y := ⟨x + escapeFactor c x r y • (y.val-x), fun hy => escapeFactor_outside y (hKb hy)⟩
  continuous_toFun := (continuous_const.add ((escapeFactor_continuous c x r).smul
    (continuous_subtype_val.sub continuous_const))).subtype_mk _

def convexEscapePunctureHomotopy {K : Set E} {c x : E} {r : ℝ}
    (hKb : K ⊆ Metric.closedBall c r) (hx : x ∈ K) :
    ContinuousMap.Homotopy ((convexExteriorInclusion hx).comp (convexEscapeMap hKb))
      (ContinuousMap.id {y : E // y ≠ x}) where
  toFun ty := ⟨x + escapeScale c x r ty.1 ty.2 • (ty.2.val-x),
    escapeScale_ne_center c x r ty.1 ty.2⟩
  continuous_toFun := (continuous_const.add ((escapeScale_continuous c x r).smul
    ((continuous_subtype_val.comp continuous_snd).sub continuous_const))).subtype_mk _
  map_zero_left y := by ext; simp [escapeScale, convexExteriorInclusion, convexEscapeMap]
  map_one_left y := by ext; simp [escapeScale]

def convexEscapeExteriorHomotopy {K : Set E} (hK : Convex ℝ K)
    {c x : E} {r : ℝ} (hKb : K ⊆ Metric.closedBall c r) (hx : x ∈ K) :
    ContinuousMap.Homotopy ((convexEscapeMap hKb).comp (convexExteriorInclusion hx))
      (ContinuousMap.id ↥(Kᶜ)) where
  toFun ty := ⟨x + escapeScale c x r ty.1 (convexExteriorInclusion hx ty.2) • (ty.2.val-x),
    outward_convex hK hx ty.2.property
      (escapeScale_ge_one c x r ty.1 (convexExteriorInclusion hx ty.2))⟩
  continuous_toFun := (continuous_const.add
    (((escapeScale_continuous c x r).comp
      (continuous_fst.prodMk ((convexExteriorInclusion hx).continuous.comp continuous_snd))).smul
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const))).subtype_mk _
  map_zero_left y := by ext; simp [escapeScale, convexExteriorInclusion, convexEscapeMap]
  map_one_left y := by ext; simp [escapeScale]

/-- Point restriction for a bounded convex support is an isomorphism in every degree. -/
lemma boundedConvex_pointMap_isIso
    (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    {K : Set E} (hK : Convex ℝ K) {c x : E} {r : ℝ}
    (hKb : K ⊆ Metric.closedBall c r) (hx : x ∈ K) (j : ℤ) :
    IsIso ((relativeHomologyFunctor R V j).map (pointMap hx)) := by
  apply relative_isIso_of_homology_isIso R V (pointMap hx)
  · intro k
    change IsIso ((homologyFunctor R V k).map (TopCat.ofHom (convexExteriorInclusion hx)))
    exact (P202.PrismHomotopy.homologyIso R V
      (TopCat.ofHom (convexExteriorInclusion hx)) (TopCat.ofHom (convexEscapeMap hKb))
      (convexEscapeExteriorHomotopy hK hKb hx) (convexEscapePunctureHomotopy hKb hx) k).1
  · intro k
    change IsIso ((homologyFunctor R V k).map (𝟙 (TopCat.of E)))
    infer_instance

end ConvexSupports

/-- Compact convex coordinate images have the same supported homology as any
one of their points, by excision and the radial complement comparison. -/
lemma chartConvex_pointMap_isIso
    (R : Type u) [CommRing R] {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : Manifold n M) (c : Chart n M) (K : Set M) (hK : IsCompact K)
    (hKs : K ⊆ c.source)
    (hconvex : Convex ℝ ((fun x : M => coordinateLiftHomeomorph.{v} n (c x)) '' K))
    {x : M} (hx : x ∈ K) (j : ℕ) :
    IsIso ((relativeHomologyFunctor R R (j : ℤ)).map (pointMap hx)) := by
  letI := A.hausdorff
  let e := coordinateLiftHomeomorph.{v} n
  let c' := c.transHomeomorph e
  let L := c' '' K
  have hc : ContinuousOn c' K := c'.continuousOn.mono hKs
  have hLc : IsCompact L := hK.image_of_continuousOn hc
  have hLt : L ⊆ c'.target := by
    rintro y ⟨z, hz, rfl⟩
    exact c'.map_source (hKs hz)
  have hsup : ∀ y ∈ c'.source, y ∈ K ↔ c' y ∈ L := by
    intro y hy
    constructor
    · intro hyK
      exact ⟨y, hyK, rfl⟩
    · rintro ⟨z, hz, he⟩
      have he' := congrArg c'.symm he
      rw [c'.left_inv (hKs hz), c'.left_inv hy] at he'
      exact he' ▸ hz
  apply (partialHomeomorph_pointMap_isIso_iff R c' K hK.isClosed hKs
    L hLc.isClosed hLt hsup hx j).mpr
  obtain ⟨r, hr⟩ := hLc.isBounded.subset_closedBall (0 : ULift.{v} (Fin n → ℝ))
  exact boundedConvex_pointMap_isIso R R hconvex hr ((hsup x (hKs hx)).mp hx) (j : ℤ)

/-- A fixed chart supplies arbitrarily small balls centered at the given point. -/
lemma fixedChart_ball_basis {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : Manifold n M) (c : Chart n M) (hc : c ∈ A.atlas)
    (x : M) (hxc : x ∈ c.source) {U : Set M} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ B : CoordinateBall A, B.chart = c ∧ ballCenter B = x ∧
      x ∈ B.interior ∧ B.closed ⊆ U := by
  have hV : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.symm.isOpen_inter_preimage hU
  have hxV : c x ∈ c.target ∩ c.symm ⁻¹' U :=
    ⟨c.map_source hxc, by simpa only [Set.mem_preimage, c.left_inv hxc] using hx⟩
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hxV)
  let B : CoordinateBall A := ⟨c, hc, c x, r, hr, fun y hy => (hball hy).1⟩
  refine ⟨B, rfl, c.left_inv hxc, ⟨hxc, Metric.mem_ball_self hr⟩, ?_⟩
  intro y hy
  change y ∈ c.source ∩ c ⁻¹' Metric.closedBall (c x) r at hy
  have h := (hball hy.2).2
  simpa only [Set.mem_preimage, c.left_inv hy.1] using h

/-- A compact set in a chart has a finite cover by closed coordinate balls
centered in the set, with closures in any prescribed open neighborhood. -/
lemma compact_buffer_balls {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : Manifold n M) (c : Chart n M) (hc : c ∈ A.atlas)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ c.source)
    {U : Set M} (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ s : Finset (CoordinateBall A),
      K ⊆ ⋃ B ∈ s, B.closed ∧
      ∀ B ∈ s, B.chart = c ∧ ballCenter B ∈ K ∧ B.closed ⊆ U := by
  classical
  let good : Set (CoordinateBall A) :=
    {B | B.chart = c ∧ ballCenter B ∈ K ∧ B.closed ⊆ U}
  have hcover : K ⊆ ⋃ B : good, B.val.interior := by
    intro x hx
    obtain ⟨B, hBc, hBx, hxB, hBU⟩ :=
      fixedChart_ball_basis A c hc x (hKs hx) hU (hKU hx)
    exact Set.mem_iUnion.mpr ⟨⟨B, hBc, hBx ▸ hx, hBU⟩, hxB⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover (fun B : good => B.val.interior)
    (fun B => ball_interior_open B.val) hcover
  refine ⟨s.image Subtype.val, ?_, ?_⟩
  · intro x hx
    obtain ⟨B, hBs, hxB⟩ := Set.mem_iUnion₂.mp (hs hx)
    exact Set.mem_iUnion₂.mpr ⟨B.val, Finset.mem_image.mpr ⟨B, hBs, rfl⟩,
      B.val.interior_subset_closed hxB⟩
  · intro B hB
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hB
    exact b.property

/-- In its own chart, a closed coordinate ball has precisely the usual
closed-ball image in the lifted normed model. -/
lemma coordinateBall_chart_image {n : ℕ} {M : Type v} [TopologicalSpace M]
    {A : Manifold n M} (B : CoordinateBall A) :
    (fun x : M => coordinateLiftHomeomorph.{v} n (B.chart x)) '' B.closed =
      Metric.closedBall (coordinateLiftHomeomorph.{v} n B.center) B.radius := by
  let e := coordinateLiftHomeomorph.{v} n
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact hx.2
  · intro y hy
    have hz : e.symm y ∈ Metric.closedBall B.center B.radius := hy
    have hzt := B.closedBall_subset hz
    refine ⟨B.chart.symm (e.symm y), ⟨B.chart.map_target hzt, ?_⟩, ?_⟩
    · change B.chart (B.chart.symm (e.symm y)) ∈ Metric.closedBall B.center B.radius
      rw [B.chart.right_inv hzt]
      exact hz
    · change e (B.chart (B.chart.symm (e.symm y))) = y
      rw [B.chart.right_inv hzt, e.apply_symm_apply]

lemma coordinateBall_chart_convex {n : ℕ} {M : Type v} [TopologicalSpace M]
    {A : Manifold n M} (B : CoordinateBall A) :
    Convex ℝ ((fun x : M => coordinateLiftHomeomorph.{v} n (B.chart x)) '' B.closed) := by
  rw [coordinateBall_chart_image]
  exact convex_closedBall _ _


/-- A version of finite compact induction in which the family, rather than all
compact subsets of a piece, is assumed stable under binary intersection. -/
lemma finite_compact_union_interstable {M : Type v} [TopologicalSpace M] [T2Space M]
    (P : Set M → Prop) (F : Set (Set M))
    (h0 : P ∅)
    (hbase : ∀ C ∈ F, IsCompact C → P C)
    (hinter : ∀ C ∈ F, ∀ D ∈ F, C ∩ D ∈ F)
    (hu : ∀ K L : Set M, IsCompact K → IsCompact L →
      P K → P L → P (K ∩ L) → P (K ∪ L))
    {ι : Type*} (s : Finset ι) (C : ι → Set M)
    (hc : ∀ i ∈ s, IsCompact (C i)) (hf : ∀ i ∈ s, C i ∈ F) :
    P (⋃ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty => simpa using h0
  | @insert a s ha ih =>
    have hsc : IsCompact (⋃ i ∈ s, C i) :=
      s.isCompact_biUnion (fun i hi => hc i (Finset.mem_insert_of_mem hi))
    have hca := hc a (Finset.mem_insert_self a s)
    have hfa := hf a (Finset.mem_insert_self a s)
    have he : (⋃ i ∈ s, C i) ∩ C a = ⋃ i ∈ s, C i ∩ C a := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_iUnion]
      aesop
    have hci : P ((⋃ i ∈ s, C i) ∩ C a) := by
      rw [he]
      apply ih (fun i => C i ∩ C a)
      · intro i hi
        exact (hc i (Finset.mem_insert_of_mem hi)).inter_right hca.isClosed
      · intro i hi
        exact hinter _ (hf i (Finset.mem_insert_of_mem hi)) _ hfa
    have hm : P ((⋃ i ∈ s, C i) ∪ C a) := hu _ _ hsc hca
      (ih C (fun i hi => hc i (Finset.mem_insert_of_mem hi))
        (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
      (hbase _ hfa hca) hci
    simpa only [Finset.set_biUnion_insert, Set.union_comm] using hm

/-- Vanishing and detection, without any orientation existence premise. -/
def SupportDetection (R : Type u) [CommRing R] (n : ℕ)
    (M : Type v) [TopologicalSpace M] (K : Set M) : Prop :=
  (∀ j : ℕ, n < j → IsZero (SupportedGroup R M K j)) ∧
    Function.Injective (localRestrictions R K n)

variable (R : Type u) [CommRing R] {n : ℕ} {M : Type v} [TopologicalSpace M]

lemma emptySupport_detection : SupportDetection R n M ∅ := by
  refine ⟨fun j _ => emptySupport_isZero R j, ?_⟩
  intro a b _
  exact (ModuleCat.isZero_iff_subsingleton.mp (emptySupport_isZero R n)).elim a b

lemma union_detection (hglue : SupportGluing R M)
    (K L : Set M) (hcK : IsCompact K) (hcL : IsCompact L)
    (hK : SupportDetection R n M K) (hL : SupportDetection R n M L)
    (hI : SupportDetection R n M (K ∩ L)) : SupportDetection R n M (K ∪ L) := by
  obtain ⟨hinj, _⟩ := hglue K L hcK hcL
  refine ⟨?_, ?_⟩
  · intro j hj
    apply ModuleCat.isZero_iff_subsingleton.mpr
    have hKs := ModuleCat.isZero_iff_subsingleton.mp (hK.1 j hj)
    have hLs := ModuleCat.isZero_iff_subsingleton.mp (hL.1 j hj)
    exact ⟨fun a b => hinj j (hI.1 (j+1) (by omega)) a b
      (hKs.elim _ _) (hLs.elim _ _)⟩
  · intro a b hab
    apply hinj n (hI.1 (n+1) (by omega)) a b
    · apply hK.2
      funext x
      change restrictPoint R x.property n
        (P202.LocalOrientation.supportLinear R Set.subset_union_left n a) =
        restrictPoint R x.property n
          (P202.LocalOrientation.supportLinear R Set.subset_union_left n b)
      rw [P202.LocalOrientation.restrictPoint_supportLinear,
        P202.LocalOrientation.restrictPoint_supportLinear]
      exact congrFun hab ⟨x.val, Or.inl x.property⟩
    · apply hL.2
      funext x
      change restrictPoint R x.property n
        (P202.LocalOrientation.supportLinear R Set.subset_union_right n a) =
        restrictPoint R x.property n
          (P202.LocalOrientation.supportLinear R Set.subset_union_right n b)
      rw [P202.LocalOrientation.restrictPoint_supportLinear,
        P202.LocalOrientation.restrictPoint_supportLinear]
      exact congrFun hab ⟨x.val, Or.inr x.property⟩

lemma finite_convex_union_detection {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hglue : SupportGluing R E)
    (hbase : ∀ C : Set E, IsCompact C → Convex ℝ C → SupportDetection R n E C)
    {ι : Type*} (s : Finset ι) (C : ι → Set E)
    (hc : ∀ i ∈ s, IsCompact (C i)) (hf : ∀ i ∈ s, Convex ℝ (C i)) :
    SupportDetection R n E (⋃ i ∈ s, C i) := by
  apply finite_compact_union_interstable (SupportDetection R n E) {C | Convex ℝ C}
    (emptySupport_detection R) (fun C hC hc => hbase C hc hC)
    (fun C hC D hD => hC.inter hD)
    (fun K L hcK hcL hK hL hI => union_detection R hglue K L hcK hcL hK hL hI)
    s C hc hf


/-- The compact convex base case includes lower-dimensional convex supports
and the empty set. -/
lemma chartConvex_detection (A : Manifold n M) (c : Chart n M)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ c.source)
    (hconvex : Convex ℝ ((fun x : M =>
      P202.LocalOrientation.coordinateLiftHomeomorph.{v} n (c x)) '' K)) :
    SupportDetection R n M K := by
  rcases K.eq_empty_or_nonempty with he | ⟨x, hx⟩
  · subst K
    exact emptySupport_detection R
  · refine ⟨?_, ?_⟩
    · intro j hj
      haveI := chartConvex_pointMap_isIso R A c K hK hKs hconvex hx j
      exact (asIso ((relativeHomologyFunctor R R (j : ℤ)).map
        (pointMap hx))).isZero_iff.mpr
          ((P202.LocalOrientation.localHomology R n M A x j).2 (by omega))
    · intro g h he
      haveI := chartConvex_pointMap_isIso R A c K hK hKs hconvex hx n
      apply (asIso ((relativeHomologyFunctor R R (n : ℤ)).map
        (pointMap hx))).toLinearEquiv.injective
      exact congrFun he ⟨x, hx⟩

/-- Finite unions of compact supports convex in one chart satisfy vanishing
and detection. Pairwise intersections remain convex in that same chart. -/
lemma finite_chartConvex_union_detection (A : Manifold n M) (c : Chart n M)
    (hglue : SupportGluing R M) {ι : Type*} (s : Finset ι) (C : ι → Set M)
    (hc : ∀ i ∈ s, IsCompact (C i)) (hs : ∀ i ∈ s, C i ⊆ c.source)
    (hf : ∀ i ∈ s, Convex ℝ ((fun x : M =>
      P202.LocalOrientation.coordinateLiftHomeomorph.{v} n (c x)) '' C i)) :
    SupportDetection R n M (⋃ i ∈ s, C i) := by
  letI := A.hausdorff
  let f := fun x : M => P202.LocalOrientation.coordinateLiftHomeomorph.{v} n (c x)
  let F : Set (Set M) := {K | K ⊆ c.source ∧ Convex ℝ (f '' K)}
  have hinj : Set.InjOn f c.source := by
    intro x hx y hy he
    apply c.injOn hx hy
    exact (P202.LocalOrientation.coordinateLiftHomeomorph.{v} n).injective he
  apply finite_compact_union_interstable (SupportDetection R n M) F
    (emptySupport_detection R)
    (fun K hK hcK => chartConvex_detection R A c K hcK hK.1 hK.2)
    (fun K hK L hL => ?_)
    (fun K L hcK hcL hK hL hI => union_detection R hglue K L hcK hcL hK hL hI)
    s C hc (fun i hi => ⟨hs i hi, hf i hi⟩)
  refine ⟨Set.inter_subset_left.trans hK.1, ?_⟩
  change Convex ℝ (f '' (K ∩ L))
  rw [hinj.image_inter hK.1 hL.1]
  exact hK.2.inter hL.2


/-- A class on a finite union vanishes when each piece restriction vanishes,
provided local values detect the union. -/
lemma finite_union_class_zero {ι : Type*} (s : Finset ι) (C : ι → Set M)
    (j : ℕ) (hdet : Function.Injective (localRestrictions R (⋃ i ∈ s, C i) j))
    (g : SupportedGroup R M (⋃ i ∈ s, C i) j)
    (hg : ∀ (i : ι) (hi : i ∈ s),
      P202.LocalOrientation.supportLinear R
        (show C i ⊆ ⋃ k ∈ s, C k from fun y hy =>
          Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hy⟩⟩) j g = 0) : g = 0 := by
  apply hdet
  funext x
  have hx := x.property
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  change restrictPoint R x.property j g = _
  rw [show (localRestrictions R (⋃ i ∈ s, C i) j) 0 x = 0 from by
    change restrictPoint R x.property j 0 = 0
    exact map_zero _]
  rw [← P202.LocalOrientation.restrictPoint_supportLinear R
    (show C i ⊆ ⋃ k ∈ s, C k from fun y hy =>
      Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hy⟩⟩) hxi j g,
    hg i hi, map_zero]


section BoundaryBuffer
open Opposite
open scoped Simplicial
variable {X : TopCat.{v}}

lemma chain_compact_factor (A : Set X) (k : ℕ) (b : Chains R (TopCat.of A) k) :
    ∃ B : Set X, IsCompact B ∧ B ⊆ A ∧
      ∀ C : Set X, B ⊆ C → ∃ c : Chains R (TopCat.of C) k,
        (chainMap R R (Pair.inclusion ⟨X, C⟩)).f k c =
          (chainMap R R (Pair.inclusion ⟨X, A⟩)).f k b := by
  classical
  let f : Simplex (TopCat.of A) k → Simplex X k :=
    (TopCat.toSSet.map (Pair.inclusion ⟨X, A⟩)).app (op ⦋k⦌)
  let B : Set X := ⋃ s ∈ b.support, Set.range (fun x => (simplexEquiv (TopCat.of A) k s x).val)
  refine ⟨B, ?_, ?_, ?_⟩
  · exact b.support.isCompact_biUnion (fun s _ =>
      isCompact_range (continuous_subtype_val.comp (simplexEquiv (TopCat.of A) k s).continuous))
  · intro x hx
    obtain ⟨s, _, t, rfl⟩ := Set.mem_iUnion₂.mp hx
    exact (simplexEquiv (TopCat.of A) k s t).property
  · intro C hBC
    apply (Finsupp.mem_range_mapDomain_iff _
      (P202.RelativeSingularChains.simplex_injective ⟨X, C⟩ k) _).mpr
    intro s hs
    by_contra hz
    have hsupport : s ∈ (Finsupp.mapDomain f b).support := Finsupp.mem_support_iff.mpr hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hsupport)
    apply hs
    apply (P202.RelativeSingularChains.simplex_image ⟨X, C⟩ k (f t)).mpr
    intro x
    exact hBC (Set.mem_iUnion₂.mpr ⟨t, ht, ⟨x, rfl⟩⟩)

lemma ordinary_chain_compact_factor (A : Set X) (i : ℤ)
    (b : (ordinaryComplex R R (TopCat.of A)).X i) :
    ∃ B : Set X, IsCompact B ∧ B ⊆ A ∧
      ∀ C : Set X, B ⊆ C → ∃ c : (ordinaryComplex R R (TopCat.of C)).X i,
        (inclusion (ordinaryFunctor R R) ⟨X, C⟩).f i c =
          (inclusion (ordinaryFunctor R R) ⟨X, A⟩).f i b := by
  cases i with
  | ofNat k =>
    obtain ⟨B, hB, hBA, hBC⟩ := chain_compact_factor R A k
      ((ordinaryNonnegativeIso R R (TopCat.of A) k).hom b)
    refine ⟨B, hB, hBA, fun C hC => ?_⟩
    obtain ⟨c, hc⟩ := hBC C hC
    refine ⟨(ordinaryNonnegativeIso R R (TopCat.of C) k).inv c, ?_⟩
    apply (ordinaryNonnegativeIso R R X k).toLinearEquiv.injective
    have hA := congrArg (fun f => f b) (ordinary_inclusion_degree R R ⟨X, A⟩ k)
    have hC := congrArg (fun f => f ((ordinaryNonnegativeIso R R (TopCat.of C) k).inv c))
      (ordinary_inclusion_degree R R ⟨X, C⟩ k)
    simp only [ModuleCat.comp_apply] at hA hC
    change (ordinaryNonnegativeIso R R X k).hom
      ((inclusion (ordinaryFunctor R R) ⟨X, C⟩).f (k : ℤ)
        ((ordinaryNonnegativeIso R R (TopCat.of C) k).inv c)) =
      (chainMap R R (Pair.inclusion ⟨X, C⟩)).f k
        ((ordinaryNonnegativeIso R R (TopCat.of C) k).hom
          ((ordinaryNonnegativeIso R R (TopCat.of C) k).inv c)) at hC
    rw [Iso.inv_hom_id_apply] at hC
    exact hC.trans (hc.trans hA.symm)
  | negSucc k =>
    have hb : b = 0 := (ModuleCat.isZero_iff_subsingleton.mp
      (P202.SingularChains.ordinary_negative_chains R R (TopCat.of A) _ (by omega))).elim b 0
    refine ⟨∅, isCompact_empty, Set.empty_subset A, fun C _ => ⟨0, ?_⟩⟩
    simp [hb]

lemma class_boundary_buffer {M : Type v} [TopologicalSpace M]
    (K : Set M) (j : ℕ) (g : SupportedGroup R M K j) :
    ∃ B : Set M, IsCompact B ∧ Disjoint B K ∧
      ∀ (L : Set M) (hKL : K ⊆ L), Disjoint B L →
        ∃ h : SupportedGroup R M L j,
          ((relativeHomologyFunctor R R (j : ℤ)).map (supportMap hKL)) h = g := by
  let PK := supportedPair M K
  let QK := ordinary R R PK
  let T := ordinaryComplex R R (TopCat.of M)
  let i : ℤ := j
  let qK := projection (ordinaryFunctor R R) PK
  obtain ⟨z, hz⟩ := (ModuleCat.epi_iff_surjective (QK.homologyπ i)).mp inferInstance g
  let zc := QK.iCycles i z
  have hzc : QK.d i (i-1) zc = 0 := by
    exact congrArg (fun f => f z) (QK.iCycles_d i (i-1))
  obtain ⟨c, hc, b, ⟨hb, _⟩, _⟩ :=
    P202.ChainLES.lifts_exist (sequence (ordinaryFunctor R R) PK)
      (P202.RelativeSingularChains.sequence_shortExact (ordinaryFunctor R R) PK)
      i (i-1) (by simp [ComplexShape.down_Rel]) zc hzc
  change T.X i at c
  change (ordinaryComplex R R (TopCat.of (Kᶜ : Set M))).X (i-1) at b
  change qK.f i c = zc at hc
  change (inclusion (ordinaryFunctor R R) PK).f (i-1) b = T.d i (i-1) c at hb
  obtain ⟨B, hB, hBK, hfactor⟩ := ordinary_chain_compact_factor R
    (X := TopCat.of M) Kᶜ (i-1) b
  refine ⟨B, hB, Set.disjoint_left.mpr (fun x hxB hxK => hBK hxB hxK), ?_⟩
  intro L hKL hBL
  let PL := supportedPair M L
  let QL := ordinary R R PL
  let qL := projection (ordinaryFunctor R R) PL
  obtain ⟨bL, hbL⟩ := hfactor Lᶜ (fun x hxB hxL => Set.disjoint_left.mp hBL hxB hxL)
  change (inclusion (ordinaryFunctor R R) PL).f (i-1) bL =
    (inclusion (ordinaryFunctor R R) PK).f (i-1) b at hbL
  have hboundary : qL.f (i-1) (T.d i (i-1) c) = 0 := by
    rw [← hb, ← hbL]
    exact congrArg (fun f => f bL) (congrArg (fun f => f.f (i-1))
      (cokernel.condition (inclusion (ordinaryFunctor R R) PL)))
  let zL := qL.f i c
  have hzL : QL.d i (i-1) zL = 0 := by
    have hcomm := congrArg (fun f => f c) (qL.comm i (i-1))
    simp only [ModuleCat.comp_apply] at hcomm
    exact hcomm.trans hboundary
  have hnext : (ComplexShape.down ℤ).next i = i-1 :=
    (ComplexShape.down ℤ).next_eq' (by simp [ComplexShape.down_Rel])
  let w := QL.cyclesMk zL (i-1) hnext hzL
  refine ⟨QL.homologyπ i w, ?_⟩
  let t := relativeMap (ordinaryFunctor R R) (supportMap hKL)
  change homologyMap t i (QL.homologyπ i w) = g
  have hcyc : cyclesMap t i w = z := by
    apply (ModuleCat.mono_iff_injective (QK.iCycles i)).mp inferInstance
    have hcomm := congrArg (fun f => f w) (cyclesMap_i t i)
    simp only [ModuleCat.comp_apply] at hcomm
    rw [hcomm]
    have hw : QL.iCycles i w = zL := QL.i_cyclesMk zL (i-1) hnext hzL
    rw [hw]
    have hp' : qL ≫ t = qK := by
      have H := projection_map (ordinaryFunctor R R) (supportMap hKL)
      have hid : (supportMap hKL).map = 𝟙 (TopCat.of M) := rfl
      rw [hid] at H
      change qL ≫ t = (ordinaryFunctor R R).map (𝟙 (TopCat.of M)) ≫ qK at H
      rw [CategoryTheory.Functor.map_id, Category.id_comp] at H
      exact H
    have hp := congrArg (fun f => f.f i c) hp' 
    change t.f i zL = zc
    exact hp.trans hc
  have hn := congrArg (fun f => f w) (homologyπ_naturality t i)
  simp only [ModuleCat.comp_apply] at hn
  rw [hn, hcyc]
  exact hz


end BoundaryBuffer

lemma compact_ball_detection (R : Type u) [CommRing R]
    {n : ℕ} {M : Type v} [TopologicalSpace M]
    (A : Manifold n M) (B : CoordinateBall A) (hglue : SupportGluing R M)
    (K : Set M) (hK : IsCompact K) (hKB : K ⊆ B.interior) :
    SupportDetection R n M K := by
  letI := A.hausdorff
  have hbuffer (j : ℕ) (g : SupportedGroup R M K j) :
      ∃ (s : Finset (CoordinateBall A))
        (hKL : K ⊆ ⋃ C ∈ s, C.closed)
        (h : SupportedGroup R M (⋃ C ∈ s, C.closed) j),
        P202.LocalOrientation.supportLinear R hKL j h = g ∧
        (∀ C ∈ s, C.chart = B.chart ∧ P202.LocalOrientation.ballCenter C ∈ K) := by
    obtain ⟨D, hD, hDK, hfactor⟩ := class_boundary_buffer R K j g
    let U := B.chart.source ∩ Dᶜ
    have hKU : K ⊆ U := by
      intro x hx
      exact ⟨(hKB hx).1, fun hxD => Set.disjoint_left.mp hDK hxD hx⟩
    obtain ⟨s, hKs, hs⟩ := compact_buffer_balls A B.chart B.chart_mem K hK
      (fun x hx => (hKB hx).1) (B.chart.open_source.inter hD.isClosed.isOpen_compl) hKU
    have hDL : Disjoint D (⋃ C ∈ s, C.closed) := by
      apply Set.disjoint_left.mpr
      intro x hxD hxL
      obtain ⟨C, hCs, hxC⟩ := Set.mem_iUnion₂.mp hxL
      exact (hs C hCs).2.2 hxC |>.2 hxD
    obtain ⟨h, hh⟩ := hfactor (⋃ C ∈ s, C.closed) hKs hDL
    exact ⟨s, hKs, h, hh, fun C hC => ⟨(hs C hC).1, (hs C hC).2.1⟩⟩
  have hfinite (s : Finset (CoordinateBall A))
      (hs : ∀ C ∈ s, C.chart = B.chart) :
      SupportDetection R n M (⋃ C ∈ s, C.closed) := by
    apply finite_chartConvex_union_detection R A B.chart hglue s
      (fun C => C.closed)
      (fun C _ => P202.LocalOrientation.ball_closed_compact C)
    · intro C hC x hx
      rw [← hs C hC]
      exact hx.1
    · intro C hC
      rw [← hs C hC]
      exact coordinateBall_chart_convex C
  constructor
  · intro j hj
    apply ModuleCat.isZero_iff_subsingleton.mpr
    suffices hz : ∀ g : SupportedGroup R M K j, g = 0 from
      ⟨fun a b => (hz a).trans (hz b).symm⟩
    intro g
    obtain ⟨s, hKL, h, hh, hs⟩ := hbuffer j g
    have hhzero : h = 0 := (ModuleCat.isZero_iff_subsingleton.mp
      ((hfinite s (fun C hC => (hs C hC).1)).1 j hj)).elim h 0
    rw [← hh, hhzero, map_zero]
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro g hg
    obtain ⟨s, hKL, h, hh, hs⟩ := hbuffer n g
    have hhzero : h = 0 := by
      apply finite_union_class_zero R s (fun C => C.closed) n
        (hfinite s (fun C hC => (hs C hC).1)).2 h
      intro C hCs
      let x := P202.LocalOrientation.ballCenter C
      have hxC : x ∈ C.closed :=
        C.interior_subset_closed (P202.LocalOrientation.ballCenter_mem C)
      have hxK : x ∈ K := (hs C hCs).2
      haveI := P202.LocalOrientation.coordinateBall_pointMap_isIso R C x hxC n
      apply (asIso ((relativeHomologyFunctor R R (n : ℤ)).map
        (pointMap hxC))).toLinearEquiv.injective
      change restrictPoint R hxC n _ = restrictPoint R hxC n 0
      rw [P202.LocalOrientation.restrictPoint_supportLinear, map_zero]
      have hgx := congrFun hg ⟨x, hxK⟩
      change restrictPoint R hxK n g = 0 at hgx
      rw [← hh, P202.LocalOrientation.restrictPoint_supportLinear] at hgx
      exact hgx
    rw [← hh, hhzero, map_zero]

/-- The five conclusions of the compact orientation theorem, assembled from
closed-support gluing and the chart-local compact-support argument. -/
private theorem compactOrientationTheorem :
    Expected.compactClass.{u,v} ∧ Expected.aboveDimension.{u,v} ∧
      Expected.localDetection.{u,v} ∧ Expected.compatibility.{u,v} ∧
      Expected.ordinaryFundamentalClass.{u,v} := by
  apply compactTheorem_of_ballDetection_and_gluing
  · intro R _ M _ hT
    letI := hT
    exact supportGluing R
  · intro R _ n M _ A B K hK hKB
    letI := A.hausdorff
    exact compact_ball_detection R A B (supportGluing R) K hK hKB

/-- Existence and uniqueness of the orientation class near any compact set. -/
theorem compactClass : Expected.compactClass.{u,v} :=
  compactOrientationTheorem.1

/-- Classes for nested compact supports agree under the canonical restriction. -/
theorem compatibility : Expected.compatibility.{u,v} :=
  compactOrientationTheorem.2.2.2.1

/-- Supported homology vanishes above the manifold dimension. -/
theorem aboveDimension : Expected.aboveDimension.{u,v} :=
  compactOrientationTheorem.2.1

/-- Top-dimensional supported classes are detected by their local restrictions. -/
theorem localDetection : Expected.localDetection.{u,v} :=
  compactOrientationTheorem.2.2.1

/-- On a compact whole manifold the class is the unique ordinary fundamental class. -/
theorem ordinaryFundamentalClass : Expected.ordinaryFundamentalClass.{u,v} :=
  compactOrientationTheorem.2.2.2.2

end P202.CompactOrientation
