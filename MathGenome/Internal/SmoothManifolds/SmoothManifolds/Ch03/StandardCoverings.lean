import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.CoveringStructure
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Examples.RealProjectiveSpace
import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.StandardCoverings
import Mathlib.Topology.Covering.Quotient

namespace SmoothManifolds.StandardCoverings
open Set Filter Topology SphereTorusData ProjectiveData StandardCoveringData
open scoped ContDiff

lemma euclideanAtlas_isContDiffAtlas (k : ℕ) :
    IsContDiffAtlas (⊤ : ℕ∞) (euclideanAtlas k) := by
  let c := (Homeomorph.Set.univ (Euclidean k)).symm.toOpenPartialHomeomorph
  constructor
  · intro x
    exact ⟨c, rfl, mem_univ _⟩
  · intro e he d hd
    have he' : e = c := he
    have hd' : d = c := hd
    subst e; subst d
    apply contDiffCompatible_of_germs <;> intro x hx hy <;>
      exact LocalCoordinateExtension.self _ _ _

theorem euclideanManifold :
    Specs.SmoothManifolds.Ch03.StandardCoverings.euclideanManifoldType := by
  intro k
  have hA := euclideanAtlas_isContDiffAtlas k
  exact ⟨⟨⟨inferInstance, inferInstance, _, hA.1⟩,
    ⟨_, maximalExtension_isMaximal hA⟩⟩, rfl⟩

/-- Identify any explicitly verified smooth covering with the canonical
maximal lifted atlas, using the uniqueness result on the fixed total space. -/
lemma canonical_atlas_eq {n : ℕ} {E M : Type*} [TopologicalSpace E] [TopologicalSpace M]
    (T : SmoothManifold n .euclidean E) (S : SmoothManifold n .euclidean M)
    (p : E → M) (hp : CoveringData.IsSmoothCovering T S p) :
    T.smoothStructure.val = maximalExtension (⊤ : ℕ∞)
      (CoveringData.liftedAtlas S.smoothStructure.val p) := by
  have hL := CoveringStructure.liftedAtlas_isContDiffAtlas _ _
    S.smoothStructure.property.1 hp.1.isLocalHomeomorph
  let T' : SmoothManifold n .euclidean E :=
    ⟨T.topologicalManifold, ⟨_, maximalExtension_isMaximal hL⟩⟩
  have hT' := CoveringStructure.smooth_covering_of_liftedAtlas T' S p hp.1 rfl
  exact congrArg Subtype.val (CoveringStructure.smooth_covering_unique T T' S p hp hT')

/-- Small coordinate boxes isolate every point of the lattice kernel.
The quotient-covering theorem then constructs actual evenly covered open
neighborhoods from these discrete translation neighborhoods. -/
lemma quotient_isCoveringMap (k : ℕ) : IsCoveringMap (quotientProjection k) := by
  let q : Euclidean k →+ FlatTorus k :=
    { toFun := quotientProjection k
      map_zero' := rfl
      map_add' := by intro x y; rfl }
  have hdisc : IsDiscrete (q.ker : Set (Euclidean k)) := by
    apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    intro x hx
    refine ⟨angleBox x (1 / 8), SphereTorus.isOpen_angleBox _ _, ?_⟩
    ext y
    constructor
    · rintro ⟨hy, hky⟩
      apply mem_singleton_iff.mpr
      apply SphereTorus.quotientProjection_injOn_box x (by norm_num : (1 : ℝ) / 8 < 1 / 2)
        hy (SphereTorus.mem_angleBox_center x (by norm_num))
      exact hky.trans hx.symm
    · intro hy
      have h := mem_singleton_iff.mp hy
      subst y
      exact ⟨SphereTorus.mem_angleBox_center x (by norm_num), hx⟩
  have hq : IsQuotientMap q :=
    (SphereTorus.quotientProjection_isOpenQuotientMap k).isQuotientMap
  exact (hq.isAddQuotientCoveringMap_of_isDiscrete_ker_addMonoidHom hdisc).isCoveringMap


lemma quotient_smooth_covering (k : ℕ)
    (E : SmoothManifold k .euclidean (Euclidean k))
    (Q : SmoothManifold k .euclidean (FlatTorus k))
    (hE : E.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (euclideanAtlas k))
    (hQ : Q.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (angleAtlas k)) :
    CoveringData.IsSmoothCovering E Q (quotientProjection k) := by
  let c := (Homeomorph.Set.univ (Euclidean k)).symm.toOpenPartialHomeomorph
  have hc : c ∈ E.smoothStructure.val := by
    rw [hE]
    exact subset_maximalExtension (euclideanAtlas_isContDiffAtlas k) rfl
  have hQsub : angleAtlas k ⊆ Q.smoothStructure.val := by
    rw [hQ]
    exact subset_maximalExtension (SphereTorus.angleAtlas_isContDiffAtlas k)
  have htop := quotient_isCoveringMap k
  refine ⟨htop, ?_, ?_⟩
  · intro x
    let d := SphereTorus.angleChart x (1 / 8) (by norm_num)
    have hd := SphereTorus.angleChart_spec x (1 / 8) (by norm_num)
    have hxd : quotientProjection k x ∈ d.source := by
      rw [hd.1]
      exact ⟨x, SphereTorus.mem_angleBox_center x (by norm_num), rfl⟩
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      E.smoothStructure.property.1 Q.smoothStructure.property.1 _ x).mpr
    refine ⟨htop.continuous.continuousAt, c, hc, d,
      hQsub ⟨x, 1 / 8, by norm_num, by norm_num, hd⟩, mem_univ _, hxd, ?_⟩
    refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
    filter_upwards [(SphereTorus.isOpen_angleBox x (1 / 8)).mem_nhds
      (SphereTorus.mem_angleBox_center x (by norm_num))] with z hz
    exact (hd.2.2.1 z hz).symm
  · intro q hq y hy
    let a := q.symm y
    let d := SphereTorus.angleChart a (1 / 8) (by norm_num)
    have hd := SphereTorus.angleChart_spec a (1 / 8) (by norm_num)
    have ha : quotientProjection k a = y := by
      rw [← hq (q.map_target hy)]
      exact q.right_inv hy
    have hyd : y ∈ d.source := by
      rw [hd.1]
      exact ⟨a, SphereTorus.mem_angleBox_center a (by norm_num), ha⟩
    apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
      Q.smoothStructure.property.1 E.smoothStructure.property.1 _ y).mpr
    refine ⟨q.symm.continuousAt hy, d,
      hQsub ⟨a, 1 / 8, by norm_num, by norm_num, hd⟩, c, hc, hyd, mem_univ _, ?_⟩
    refine ⟨univ, isOpen_univ, mem_univ _, id, contDiffOn_id, ?_⟩
    have hbox := (q.symm.continuousAt hy).preimage_mem_nhds
      ((SphereTorus.isOpen_angleBox a (1 / 8)).mem_nhds
        (SphereTorus.mem_angleBox_center a (by norm_num)))
    filter_upwards [hbox, q.open_target.mem_nhds hy] with z hza hz
    change (d z).val = q.symm z
    have he : quotientProjection k (q.symm z) = z := by
      rw [← hq (q.map_target hz)]
      exact q.right_inv hz
    exact (congrArg (fun w => (d w).val) he.symm).trans (hd.2.2.1 _ hza)

theorem quotientSmoothCovering :
    Specs.SmoothManifolds.Ch03.StandardCoverings.quotientSmoothCoveringType := by
  intro k E Q hE hQ
  have h := quotient_smooth_covering k E Q hE hQ
  exact ⟨h, canonical_atlas_eq E Q _ h⟩

/-- The local form of smooth lifting, with agreement as germs. This also
handles branches whose identities hold only on their open target. -/
lemma smooth_lift_germ {n m : ℕ} {E M X : Type*}
    [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace X]
    (T : SmoothManifold n .euclidean E) (S : SmoothManifold n .euclidean M)
    (R : SmoothManifold m .euclidean X) (p : E → M)
    (hp : CoveringData.IsSmoothCovering T S p)
    {f : X → M} {g : X → E} {x : X}
    (hf : ManifoldSmoothAt R.smoothStructure.val S.smoothStructure.val f x)
    (hg : ContinuousAt g x) (heq : (p ∘ g) =ᶠ[𝓝 x] f) :
    ManifoldSmoothAt R.smoothStructure.val T.smoothStructure.val g x := by
  obtain ⟨q, hxq, hpq⟩ := hp.1.isLocalHomeomorph (g x)
  have hfx : f x ∈ q.target := by
    rw [← heq.eq_of_nhds]
    change p (g x) ∈ q.target
    rw [hpq]
    exact q.map_source hxq
  have hq : EqOn q p q.source := fun z _ => congrFun hpq.symm z
  have hi := hp.2.2 q hq (f x) hfx
  have hc := manifoldContDiffAt_comp S.smoothStructure.property.1.1 hf hi
  apply manifoldContDiffAt_congr hc
  filter_upwards [hg.preimage_mem_nhds (q.open_source.mem_nhds hxq), heq] with z hz he
  change q.symm (f z) = g z
  rw [← he]
  change q.symm (p (g z)) = g z
  rw [hpq, q.left_inv hz]

theorem angleSmoothCovering :
    Specs.SmoothManifolds.Ch03.StandardCoverings.angleSmoothCoveringType := by
  intro k E T hE hT
  obtain ⟨Q, _, hQ⟩ := (SphereTorus.angleManifold k).2.2
  obtain ⟨h, hh, hf, hg, _⟩ := SphereTorus.angleProductCompatibility k T Q hT hQ
  have hp := quotient_smooth_covering k E Q hE hQ
  have heq : h ∘ quotientProjection k = angleMap k := funext hh
  have hcov : CoveringData.IsSmoothCovering E T (angleMap k) := by
    refine ⟨heq ▸ hp.1.homeomorph_comp h, ?_, ?_⟩
    · rw [← heq]
      exact fun x => manifoldContDiffAt_comp Q.smoothStructure.property.1.1 (hp.2.1 x) (hf _)
    · intro q hq y hy
      apply smooth_lift_germ E Q T (quotientProjection k) hp (hg y)
        (q.symm.continuousAt hy)
      filter_upwards [q.open_target.mem_nhds hy] with z hz
      apply h.injective
      rw [Homeomorph.apply_symm_apply]
      change h (quotientProjection k (q.symm z)) = z
      rw [hh]
      exact (hq (q.map_target hz)).symm.trans (q.right_inv hz)
  exact ⟨hcov, canonical_atlas_eq E T _ hcov⟩


lemma projection_injOn_hemisphere {n : ℕ} (i : Fin (n + 1)) (s : Bool) :
    InjOn (@projectiveProjection n) (hemisphere i s) := by
  intro x hx y hy he
  rcases (Projective.projection_fiber x y).mp he with h | h
  · exact h
  · have hi := congrArg (fun z : Sphere n => z.val i) h
    simp only [antipode, Pi.neg_apply] at hi
    cases s <;> simp only [hemisphere, Bool.false_eq_true, ↓reduceIte,
      mem_ofPred_eq] at hx hy <;> linarith

/-- A sheet above the i-th projective coordinate locus: the positive or
negative open hemisphere. Its forward map is the actual quotient map. -/
noncomputable def hemisphereProjection {n : ℕ} (i : Fin (n + 1)) (s : Bool) :
    OpenPartialHomeomorph (Sphere n) (RealProjectiveSpace n) :=
  letI : Nonempty (Sphere n) := ⟨SphereTorus.sphereBase n⟩
  OpenPartialHomeomorph.ofContinuousOpen
    ((projection_injOn_hemisphere i s).toPartialEquiv projectiveProjection (hemisphere i s))
    (Projective.projection_isOpenQuotientMap n).continuous.continuousOn
    (Projective.projection_isOpenQuotientMap n).isOpenMap (SphereTorus.isOpen_hemisphere i s)

lemma projection_isLocalHomeomorph (n : ℕ) : IsLocalHomeomorph (@projectiveProjection n) := by
  apply IsLocalHomeomorph.mk
  intro x
  obtain ⟨i, s, hx⟩ := SphereTorus.hemisphere_cover n x
  exact ⟨hemisphereProjection i s, hx, fun _ _ => rfl⟩

lemma projection_finite_fiber {n : ℕ} (p : RealProjectiveSpace n) :
    (projectiveProjection ⁻¹' {p}).Finite := by
  induction p using Quotient.inductionOn with | _ x =>
  apply (Set.toFinite {x, antipode x}).subset
  intro y hy
  rcases (Projective.projection_fiber y x).mp hy with h | h <;> simp [h]

lemma projection_isClosedMap (n : ℕ) : IsClosedMap (@projectiveProjection n) := by
  intro U hU
  apply (Projective.projection_isOpenQuotientMap n).isQuotientMap.isClosed_preimage.mp
  rw [Projective.projection_saturation]
  exact hU.union (hU.preimage (Projective.continuous_antipode n))

/-- Closedness, exactly two possible representatives per fiber, and the
actual hemisphere homeomorphisms give genuine evenly covered neighborhoods. -/
lemma projection_isCoveringMap (n : ℕ) : IsCoveringMap (@projectiveProjection n) := by
  apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
  exact (projection_isClosedMap n).isCoveringMapOn_of_isLocalHomeomorphOn
    (fun p _ => projection_finite_fiber p) (projection_isLocalHomeomorph n).isLocalHomeomorphOn


/-- Choose the normalized representative in the specified signed hemisphere. -/
noncomputable def signedRepresentative {n : ℕ} (i : Fin (n + 1)) (s : Bool)
    (y : Euclidean n) : Sphere n :=
  if s then normalizedRepresentative i y else antipode (normalizedRepresentative i y)

lemma signedRepresentative_mem {n : ℕ} (i : Fin (n + 1)) (s : Bool) (y : Euclidean n) :
    signedRepresentative i s y ∈ hemisphere i s := by
  have h := Projective.sqrt_normalizer_pos y
  cases s <;> simp [signedRepresentative, hemisphere, normalizedRepresentative,
    antipode, insertOne, h]

lemma projection_signedRepresentative {n : ℕ} (i : Fin (n + 1)) (s : Bool)
    (y : Euclidean n) :
    projectiveProjection (signedRepresentative i s y) = projectiveInverse i y := by
  cases s
  · exact (Projective.projection_fiber _ _).mpr (Or.inr rfl)
  · rfl

lemma signedRepresentative_ratios {n : ℕ} (i : Fin (n + 1)) (s : Bool)
    (x : Sphere n) (hx : x ∈ hemisphere i s) :
    signedRepresentative i s (projectiveRatios i (projectiveProjection x)) = x := by
  apply projection_injOn_hemisphere i s (signedRepresentative_mem i s _) hx
  rw [projection_signedRepresentative]
  apply Projective.inverse_ratios
  apply (Projective.projection_mem_locus i x).mpr
  cases s <;> simp only [hemisphere, Bool.false_eq_true, ↓reduceIte,
    mem_ofPred_eq] at hx
  · exact ne_of_lt hx
  · exact ne_of_gt hx

lemma contDiff_signedRepresentative_val {n : ℕ} (i : Fin (n + 1)) (s : Bool) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (signedRepresentative i s y).val) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun y => (normalizedRepresentative i y).val) := by
    apply contDiff_pi.mpr
    intro j
    exact (contDiff_pi.mp (Projective.contDiff_insertOne i) j).div
      ((contDiff_const.add (SphereTorus.contDiff_squareSum n)).sqrt
        (fun y => ne_of_gt (by have := SphereTorus.squareSum_nonneg y; positivity)))
      (fun y => (Projective.sqrt_normalizer_pos y).ne')
  cases s
  · exact h.neg
  · exact h

lemma projection_smooth {n : ℕ}
    (S : SmoothManifold n .euclidean (Sphere n))
    (P : SmoothManifold n .euclidean (RealProjectiveSpace n))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas n))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (projectiveAtlas n)) :
    IsSmoothMap S P (@projectiveProjection n) := by
  have hSsub : hemisphereAtlas n ⊆ S.smoothStructure.val := by
    rw [hS]; exact subset_maximalExtension (SphereTorus.hemisphereAtlas_isContDiffAtlas n)
  have hPsub : projectiveAtlas n ⊆ P.smoothStructure.val := by
    rw [hP]; exact subset_maximalExtension (Projective.projectiveAtlas_isContDiffAtlas n)
  intro x
  obtain ⟨i, s, hx⟩ := SphereTorus.hemisphere_cover n x
  let c := SphereTorus.hemisphereChart i s
  let d := Projective.projectiveChart i
  have hc := SphereTorus.hemisphereChart_spec i s
  have hd := Projective.projectiveChart_spec i
  have hxc : x ∈ c.source := hx
  have hxd : projectiveProjection x ∈ d.source := by
    apply (Projective.projection_mem_locus i x).mpr
    cases s <;> simp only [hemisphere, Bool.false_eq_true, ↓reduceIte, mem_ofPred_eq] at hx
    · exact ne_of_lt hx
    · exact ne_of_gt hx
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    S.smoothStructure.property.1 P.smoothStructure.property.1 _ x).mpr
  refine ⟨(Projective.projection_isOpenQuotientMap n).continuous.continuousAt,
    c, hSsub ⟨i, s, hc⟩, d, hPsub ⟨i, hd⟩, hxc, hxd, ?_⟩
  let U : Set (Euclidean n) := {y | squareSum y < 1}
  refine ⟨U, isOpen_lt (SphereTorus.continuous_squareSum n) continuous_const,
    ?_, fun y j => insertRoot i s y (i.succAbove j) / insertRoot i s y i, ?_, ?_⟩
  · have h := c.map_source hxc
    rwa [hc.2.1] at h
  · apply contDiffOn_pi.mpr
    intro j
    exact (contDiffOn_pi.mp (SphereTorus.contDiffOn_insertRoot i s) _).div
      (contDiffOn_pi.mp (SphereTorus.contDiffOn_insertRoot i s) _) (fun y hy => by
        have hr : 0 < Real.sqrt (1 - squareSum y) := Real.sqrt_pos.mpr (sub_pos.mpr hy)
        cases s <;> simp [insertRoot, signedRoot, hr.ne'])
  · filter_upwards [c.open_source.mem_nhds hxc,
      (Projective.projection_isOpenQuotientMap n).continuous.continuousAt.preimage_mem_nhds
        (d.open_source.mem_nhds hxd)] with z hzc hzd
    have he : insertRoot i s (c z).val = z.val := by
      rw [← hc.2.2.2 (c z) (c.map_source hzc), c.left_inv hzc]
    change (fun j => insertRoot i s (c z).val (i.succAbove j) /
      insertRoot i s (c z).val i) = (d (projectiveProjection z)).val
    rw [he, hd.2.2.1 _ hzd]
    rfl

lemma projection_inverse_smooth {n : ℕ}
    (S : SmoothManifold n .euclidean (Sphere n))
    (P : SmoothManifold n .euclidean (RealProjectiveSpace n))
    (hS : S.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (hemisphereAtlas n))
    (hP : P.smoothStructure.val = maximalExtension (⊤ : ℕ∞) (projectiveAtlas n))
    (q : OpenPartialHomeomorph (Sphere n) (RealProjectiveSpace n))
    (hq : EqOn q projectiveProjection q.source) :
    ManifoldSmoothOn P.smoothStructure.val S.smoothStructure.val q.symm q.target := by
  have hSsub : hemisphereAtlas n ⊆ S.smoothStructure.val := by
    rw [hS]; exact subset_maximalExtension (SphereTorus.hemisphereAtlas_isContDiffAtlas n)
  have hPsub : projectiveAtlas n ⊆ P.smoothStructure.val := by
    rw [hP]; exact subset_maximalExtension (Projective.projectiveAtlas_isContDiffAtlas n)
  intro y hy
  obtain ⟨i, s, hx⟩ := SphereTorus.hemisphere_cover n (q.symm y)
  let c := SphereTorus.hemisphereChart i s
  let d := Projective.projectiveChart i
  have hc := SphereTorus.hemisphereChart_spec i s
  have hd := Projective.projectiveChart_spec i
  have hxc : q.symm y ∈ c.source := hx
  have hproj {z : RealProjectiveSpace n} (hz : z ∈ q.target) :
      projectiveProjection (q.symm z) = z :=
    (hq (q.map_target hz)).symm.trans (q.right_inv hz)
  have hyd : y ∈ d.source := by
    rw [← hproj hy]
    apply (Projective.projection_mem_locus i _).mpr
    cases s <;> simp only [hemisphere, Bool.false_eq_true, ↓reduceIte, mem_ofPred_eq] at hx
    · exact ne_of_lt hx
    · exact ne_of_gt hx
  apply (manifoldContDiffAt_iff_oneChart (⊤ : ℕ∞) _ _
    P.smoothStructure.property.1 S.smoothStructure.property.1 _ y).mpr
  refine ⟨q.symm.continuousAt hy, d, hPsub ⟨i, hd⟩, c, hSsub ⟨i, s, hc⟩,
    hyd, hxc, ?_⟩
  refine ⟨univ, isOpen_univ, mem_univ _,
    fun z => omitCoordinate i (signedRepresentative i s z).val, ?_, ?_⟩
  · apply ContDiff.contDiffOn
    apply contDiff_pi.mpr
    intro j
    exact contDiff_pi.mp (contDiff_signedRepresentative_val i s) (i.succAbove j)
  · filter_upwards [q.open_target.mem_nhds hy, d.open_source.mem_nhds hyd,
      (q.symm.continuousAt hy).preimage_mem_nhds (c.open_source.mem_nhds hxc)]
      with z hz hzd hzc
    change omitCoordinate i (signedRepresentative i s (d z).val).val = (c (q.symm z)).val
    rw [hd.2.2.1 _ hzd]
    have he := signedRepresentative_ratios i s (q.symm z) hzc
    rw [hproj hz] at he
    rw [he]
    exact (hc.2.2.1 _ hzc).symm

theorem antipodalSmoothCovering :
    Specs.SmoothManifolds.Ch03.StandardCoverings.antipodalSmoothCoveringType := by
  intro n S P hS hP
  have h : CoveringData.IsSmoothCovering S P (@projectiveProjection n) :=
    ⟨projection_isCoveringMap n, projection_smooth S P hS hP,
      projection_inverse_smooth S P hS hP⟩
  exact ⟨h, canonical_atlas_eq S P _ h⟩

end SmoothManifolds.StandardCoverings
