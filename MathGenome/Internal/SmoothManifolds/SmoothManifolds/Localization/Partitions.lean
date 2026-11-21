import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Localization.Partitions
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.SmoothMaps
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Foundations.CompactExhaustion
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace SmoothManifolds
open Set Filter
open scoped Topology
universe u v w

abbrev ScalarContDiffAt := @PartitionData.ScalarContDiffAt
abbrev ScalarContDiff := @PartitionData.ScalarContDiff
abbrev ScalarSmooth := @PartitionData.ScalarSmooth
abbrev IsSmoothPartition := @PartitionData.IsSmoothPartition
abbrev IsSubordinate := @PartitionData.IsSubordinate
noncomputable abbrev groupWeights := @PartitionData.groupWeights
abbrev IsCutoff := @PartitionData.IsCutoff

variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]

/-- The scalar definition is exactly the canonical one-dimensional vector test,
with the coordinate embedding/evaluation made explicit. -/
theorem scalarContDiffAt_iff (r : ℕ∞) (A : Set (ModelChart n a M)) (f : M → ℝ) (x : M) :
    ScalarContDiffAt r A f x ↔
      ContinuousAt f x ∧ ∀ e ∈ A, x ∈ e.source →
        ∃ U : Set (Euclidean n), IsOpen U ∧ (e x).val ∈ U ∧
          ∃ F : Euclidean n → ℝ, ContDiffOn ℝ r F U ∧
            (fun y => F (e y).val) =ᶠ[𝓝 x] f := by
  constructor
  · rintro ⟨hc, he⟩
    refine ⟨(continuous_apply (0 : Fin 1)).continuousAt.comp hc, ?_⟩
    intro e heA hxe
    obtain ⟨U, hU, hxU, F, hF, heq⟩ := he e heA hxe
    exact ⟨U, hU, hxU, fun z => F z 0, (contDiffOn_pi.mp hF) 0, heq.mono (fun _ h => congrFun h 0)⟩
  · rintro ⟨hc, he⟩
    refine ⟨continuousAt_pi.mpr (fun _ => hc), ?_⟩
    intro e heA hxe
    obtain ⟨U, hU, hxU, F, hF, heq⟩ := he e heA hxe
    exact ⟨U, hU, hxU, fun z (_ : Fin 1) => F z,
      contDiffOn_pi.mpr (fun _ => hF), heq.mono (fun _ h => funext (fun _ => h))⟩

namespace ScalarContDiffAt
variable {r : ℕ∞} {A : Set (ModelChart n a M)} {f g : M → ℝ} {x : M}

protected theorem const (r : ℕ∞) (A : Set (ModelChart n a M)) (c : ℝ) (x : M) :
    ScalarContDiffAt r A (fun _ => c) x := by
  apply (scalarContDiffAt_iff r A _ x).mpr
  exact ⟨continuousAt_const, fun _ _ _ =>
    ⟨univ, isOpen_univ, mem_univ _, fun _ => c, contDiffOn_const,
      Eventually.of_forall (fun _ => rfl)⟩⟩

protected theorem congr (hf : ScalarContDiffAt r A f x) (heq : f =ᶠ[𝓝 x] g) :
    ScalarContDiffAt r A g x := by
  obtain ⟨hc, he⟩ := (scalarContDiffAt_iff r A f x).mp hf
  refine (scalarContDiffAt_iff r A g x).mpr ⟨hc.congr_of_eventuallyEq heq.symm, ?_⟩
  intro e heA hxe
  obtain ⟨U, hU, hxU, F, hF, hFf⟩ := he e heA hxe
  exact ⟨U, hU, hxU, F, hF, hFf.trans heq⟩

protected theorem add (hf : ScalarContDiffAt r A f x) (hg : ScalarContDiffAt r A g x) :
    ScalarContDiffAt r A (fun y => f y + g y) x := by
  obtain ⟨hc, he⟩ := (scalarContDiffAt_iff r A f x).mp hf
  obtain ⟨hd, hd'⟩ := (scalarContDiffAt_iff r A g x).mp hg
  refine (scalarContDiffAt_iff r A _ x).mpr ⟨hc.add hd, ?_⟩
  intro e heA hxe
  obtain ⟨U, hU, hxU, F, hF, hFf⟩ := he e heA hxe
  obtain ⟨V, hV, hxV, G, hG, hGg⟩ := hd' e heA hxe
  exact ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun z => F z + G z,
    (hF.mono inter_subset_left).add (hG.mono inter_subset_right), hFf.add hGg⟩

protected theorem mul (hf : ScalarContDiffAt r A f x) (hg : ScalarContDiffAt r A g x) :
    ScalarContDiffAt r A (fun y => f y * g y) x := by
  obtain ⟨hc, he⟩ := (scalarContDiffAt_iff r A f x).mp hf
  obtain ⟨hd, hd'⟩ := (scalarContDiffAt_iff r A g x).mp hg
  refine (scalarContDiffAt_iff r A _ x).mpr ⟨hc.mul hd, ?_⟩
  intro e heA hxe
  obtain ⟨U, hU, hxU, F, hF, hFf⟩ := he e heA hxe
  obtain ⟨V, hV, hxV, G, hG, hGg⟩ := hd' e heA hxe
  exact ⟨U ∩ V, hU.inter hV, ⟨hxU, hxV⟩, fun z => F z * G z,
    (hF.mono inter_subset_left).mul (hG.mono inter_subset_right), hFf.mul hGg⟩

protected theorem neg (hf : ScalarContDiffAt r A f x) :
    ScalarContDiffAt r A (fun y => -f y) x := by
  obtain ⟨hc, he⟩ := (scalarContDiffAt_iff r A f x).mp hf
  refine (scalarContDiffAt_iff r A _ x).mpr ⟨hc.neg, ?_⟩
  intro e heA hxe
  obtain ⟨U, hU, hxU, F, hF, hFf⟩ := he e heA hxe
  exact ⟨U, hU, hxU, fun z => -F z, hF.neg, hFf.neg⟩

protected theorem inv (hf : ScalarContDiffAt r A f x) (hx : f x ≠ 0) :
    ScalarContDiffAt r A (fun y => (f y)⁻¹) x := by
  obtain ⟨hc, he⟩ := (scalarContDiffAt_iff r A f x).mp hf
  refine (scalarContDiffAt_iff r A _ x).mpr ⟨hc.inv₀ hx, ?_⟩
  intro e heA hxe
  obtain ⟨U, hU, hxU, F, hF, hFf⟩ := he e heA hxe
  have hFx : F (e x).val ≠ 0 := by rwa [hFf.eq_of_nhds]
  refine ⟨U ∩ F ⁻¹' ({0}ᶜ), hF.continuousOn.isOpen_inter_preimage hU
    isClosed_singleton.isOpen_compl, ⟨hxU, hFx⟩, fun z => (F z)⁻¹,
    (hF.mono inter_subset_left).inv ?_, hFf.inv⟩
  intro z hz
  exact hz.2

protected theorem sum {ι : Type v} (s : Finset ι) {f : ι → M → ℝ}
    (hf : ∀ i ∈ s, ScalarContDiffAt r A (f i) x) :
    ScalarContDiffAt r A (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using ScalarContDiffAt.const r A 0 x
  | @insert i s hi ih =>
    simpa [hi] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end ScalarContDiffAt

theorem scalarContDiff_const (r : ℕ∞) (A : Set (ModelChart n a M)) (c : ℝ) :
    ScalarContDiff r A (fun _ => c) := fun x => ScalarContDiffAt.const r A c x

theorem scalarContDiff_add {r : ℕ∞} {A : Set (ModelChart n a M)} {f g : M → ℝ}
    (hf : ScalarContDiff r A f) (hg : ScalarContDiff r A g) :
    ScalarContDiff r A (fun x => f x + g x) := fun x => ScalarContDiffAt.add (hf x) (hg x)

theorem scalarContDiff_mul {r : ℕ∞} {A : Set (ModelChart n a M)} {f g : M → ℝ}
    (hf : ScalarContDiff r A f) (hg : ScalarContDiff r A g) :
    ScalarContDiff r A (fun x => f x * g x) := fun x => ScalarContDiffAt.mul (hf x) (hg x)

theorem scalarContDiff_inv {r : ℕ∞} {A : Set (ModelChart n a M)} {f : M → ℝ}
    (hf : ScalarContDiff r A f) (h : ∀ x, f x ≠ 0) :
    ScalarContDiff r A (fun x => (f x)⁻¹) := fun x => ScalarContDiffAt.inv (hf x) (h x)

/-- A locally finite sum is a fixed finite sum on a neighborhood of each point. -/
theorem locallyFinite_eventuallyEq_finsum {ι : Type v} {f : ι → M → ℝ}
    (hf : LocallyFinite (fun i => sectionSupport (f i))) (x : M) :
    ∃ s : Finset ι, (fun y => ∑ᶠ i, f i y) =ᶠ[𝓝 x] (fun y => ∑ i ∈ s, f i y) := by
  classical
  obtain ⟨V, hV, hfin⟩ := hf x
  refine ⟨hfin.toFinset, Filter.mem_of_superset hV (fun y hy => ?_)⟩
  apply finsum_eq_sum_of_support_subset
  intro i hi
  exact hfin.mem_toFinset.mpr ⟨y, subset_closure hi, hy⟩

theorem scalarContDiff_finsum {r : ℕ∞} {A : Set (ModelChart n a M)}
    {ι : Type v} {f : ι → M → ℝ} (hf : ∀ i, ScalarContDiff r A (f i))
    (hlf : LocallyFinite (fun i => sectionSupport (f i))) :
    ScalarContDiff r A (fun x => ∑ᶠ i, f i x) := by
  intro x
  obtain ⟨s, hs⟩ := locallyFinite_eventuallyEq_finsum hlf x
  exact ScalarContDiffAt.congr (ScalarContDiffAt.sum s (fun i _ => hf i x)) hs.symm

/-- Restrict an ambient smooth bump to the closed model. No positive dimension
or interior-point assumption is needed. -/
theorem exists_model_bump (n : ℕ) (a : ModelKind) (x : ModelSpace n a)
    (U : Set (ModelSpace n a)) (hU : IsOpen U) (hx : x ∈ U) :
    ∃ f : ModelSpace n a → ℝ,
      ModelSmoothOn univ (fun y => f y.val) ∧
      (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
      f =ᶠ[𝓝 x] (fun _ => 1) ∧
      sectionSupport f ⊆ U ∧ IsCompact (sectionSupport f) := by
  obtain ⟨V, hV, hVU⟩ := isOpen_induced_iff.mp hU
  have hxV : x.val ∈ V := by change x ∈ Subtype.val ⁻¹' V; rwa [hVU]
  obtain ⟨d, hd, hdV⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hV.mem_nhds hxV)
  let b : ContDiffBump x.val :=
    ⟨d / 2, d, half_pos hd, half_lt_self hd⟩
  let f : ModelSpace n a → ℝ := fun y => b y.val
  have hsupp : sectionSupport f ⊆ Subtype.val ⁻¹' Metric.closedBall x.val d := by
    apply closure_minimal
    · intro y hy
      have hyb : y.val ∈ Function.support b := hy
      rw [b.support_eq] at hyb
      exact Metric.ball_subset_closedBall hyb
    · exact Metric.isClosed_closedBall.preimage continuous_subtype_val
  refine ⟨f, ?_, fun y => ⟨b.nonneg, b.le_one⟩, ?_, ?_, ?_⟩
  · intro y
    exact ⟨univ, isOpen_univ, mem_univ _, b, b.contDiff.contDiffOn, fun _ _ => rfl⟩
  · exact b.eventuallyEq_one.comp_tendsto continuous_subtype_val.continuousAt
  · intro y hy
    rw [← hVU]
    exact hdV (hsupp hy)
  · exact ((isClosed_modelSet n a).isClosedEmbedding_subtypeVal.isCompact_preimage
      (isCompact_closedBall x.val d)).of_isClosed_subset isClosed_closure hsupp

/-- A scalar ambient germ in one compatible chart determines all chart germs. -/
theorem scalarContDiffAt_of_chart {r : ℕ∞} {A : Set (ModelChart n a M)}
    (hA : IsContDiffAtlas r A) {e : ModelChart n a M} (he : e ∈ A)
    {f : M → ℝ} {x : M} (hx : x ∈ e.source)
    (h : ∃ U : Set (Euclidean n), IsOpen U ∧ (e x).val ∈ U ∧
      ∃ F : Euclidean n → ℝ, ContDiffOn ℝ r F U ∧
        (fun y => F (e y).val) =ᶠ[𝓝 x] f) : ScalarContDiffAt r A f x := by
  obtain ⟨U, hU, hxU, F, hF, heq⟩ := h
  have hcoord : ContinuousAt (fun y => (e y).val) x :=
    continuous_subtype_val.continuousAt.comp (e.continuousAt hx)
  have hFc : ContinuousAt F ((e x).val) :=
    hF.continuousOn.continuousAt (hU.mem_nhds hxU)
  have hcomp : ContinuousAt (fun y : M => F (e y).val) x :=
    ContinuousAt.comp (f := fun y : M => (e y).val) hFc hcoord
  have hc : ContinuousAt f x := hcomp.congr_of_eventuallyEq heq.symm
  refine ⟨continuousAt_pi.mpr (fun _ => hc), ?_⟩
  intro d hd hxd
  have hfe : LocalCoordinateExtension r (fun y => (e y).val)
      (fun y (_ : Fin 1) => f y) x :=
    ⟨U, hU, hxU, fun z _ => F z, contDiffOn_pi.mpr (fun _ => hF),
      heq.mono (fun _ h => funext (fun _ => h))⟩
  exact LocalCoordinateExtension.comp hfe
    (chartContDiffAt_of_compatible (hA.2 d hd e he) hxd hx)

/-- A model bump whose closed support lies inside a chart can be extended by zero. -/
theorem exists_local_bump (S : SmoothManifold n a M) (x : M) (U : Set M)
    (hU : IsOpen U) (hx : x ∈ U) :
    ∃ f : M → ℝ, PartitionData.ScalarSmooth S.smoothStructure.val f ∧
      (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
      f =ᶠ[𝓝 x] (fun _ => 1) ∧
      sectionSupport f ⊆ U ∧ IsCompact (sectionSupport f) := by
  classical
  let A := S.smoothStructure.val
  have hA : IsContDiffAtlas (⊤ : ℕ∞) A := S.smoothStructure.property.1
  obtain ⟨e, he, hxe⟩ := hA.1 x
  let V := e.symm ⁻¹' U ∩ e.target
  have hV : IsOpen V := by
    simpa [V, inter_comm] using e.symm.isOpen_inter_preimage hU
  have hxV : e x ∈ V := ⟨by simpa [e.left_inv hxe] using hx, e.map_source hxe⟩
  obtain ⟨b, hb, hb01, hb1, hbV, hbcp⟩ := exists_model_bump n a (e x) V hV hxV
  let C : Set M := e.symm '' sectionSupport b
  have hbt : sectionSupport b ⊆ e.target := fun y hy => (hbV hy).2
  have hCcp : IsCompact C := hbcp.image_of_continuousOn (e.symm.continuousOn.mono hbt)
  let : T2Space M := S.topologicalManifold.hausdorff
  have hCs : C ⊆ e.source := by
    rintro y ⟨z, hz, rfl⟩
    exact e.map_target (hbt hz)
  have hCU : C ⊆ U := by
    rintro y ⟨z, hz, rfl⟩
    exact (hbV hz).1
  let f : M → ℝ := e.source.indicator (fun y => b (e y))
  have hfC : Function.support f ⊆ C := by
    intro y hy
    have hys : y ∈ e.source := by
      by_contra hys
      exact hy (by simp [f, hys])
    have hby : b (e y) ≠ 0 := by simpa [f, hys] using hy
    exact ⟨e y, subset_closure hby, e.left_inv hys⟩
  have hfsupp : sectionSupport f ⊆ C := closure_minimal hfC hCcp.isClosed
  have heq (y : M) (hy : y ∈ e.source) : f =ᶠ[𝓝 y] (fun z => b (e z)) := by
    filter_upwards [e.open_source.mem_nhds hy] with z hz
    simp [f, hz]
  refine ⟨f, ?_, ?_, ?_, hfsupp.trans hCU,
    hCcp.of_isClosed_subset isClosed_closure hfsupp⟩
  · intro y
    by_cases hy : y ∈ e.source
    · obtain ⟨W, hW, hyW, F, hF, hFb⟩ := hb ⟨e y, mem_univ _⟩
      apply scalarContDiffAt_of_chart hA he hy
      refine ⟨W, hW, hyW, F, hF, ?_⟩
      have hcoord := continuous_subtype_val.continuousAt.comp (e.continuousAt hy)
      filter_upwards [hcoord.preimage_mem_nhds (hW.mem_nhds hyW), heq y hy] with z hzW hzf
      exact (hFb ⟨e z, mem_univ _⟩ hzW).trans hzf.symm
    · have hyC : y ∉ C := fun hyC => hy (hCs hyC)
      apply ScalarContDiffAt.congr (ScalarContDiffAt.const (⊤ : ℕ∞) A 0 y)
      filter_upwards [hCcp.isClosed.compl_mem_nhds hyC] with z hz
      exact (Function.notMem_support.mp (fun hzf => hz (hfC hzf))).symm
  · intro y
    by_cases hy : y ∈ e.source
    · simpa [f, hy] using hb01 (e y)
    · simp [f, hy]
  · exact (heq x hxe).trans (hb1.comp_tendsto (e.continuousAt hxe))

/-- Unions over arbitrary fibers preserve local finiteness. -/
theorem locallyFinite_fiber_union {ι : Type v} {κ : Type w}
    {F : ι → Set M} (hF : LocallyFinite F) (q : ι → κ) :
    LocallyFinite (fun k => ⋃ i : {i // q i = k}, F i.val) := by
  intro x
  obtain ⟨V, hV, hfin⟩ := hF x
  refine ⟨V, hV, (hfin.image q).subset ?_⟩
  rintro k ⟨y, hy, hyV⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  exact ⟨i.val, ⟨y, hi, hyV⟩, i.property⟩

theorem support_groupWeights_subset {ι : Type v} {κ : Type w}
    (q : ι → κ) (ρ : ι → M → ℝ)
    (hlf : LocallyFinite (fun i => sectionSupport (ρ i))) (k : κ) :
    sectionSupport (groupWeights q ρ k) ⊆ ⋃ i : {i // q i = k}, sectionSupport (ρ i.val) := by
  apply closure_minimal
  · intro x hx
    by_contra h
    have hz : ∀ i : {i // q i = k}, ρ i.val x = 0 := by
      intro i
      by_contra hi
      exact h (mem_iUnion.mpr ⟨i, subset_closure hi⟩)
    exact hx (by simp [groupWeights, PartitionData.groupWeights, hz])
  · exact (hlf.comp_injective Subtype.val_injective).isClosed_iUnion
      (fun _ => isClosed_closure)

omit [TopologicalSpace M] in
/-- A finite point support suffices to group an arbitrary family of scalar weights. -/
theorem finsum_groupWeights {ι : Type v} {κ : Type w}
    (q : ι → κ) (ρ : ι → M → ℝ) (x : M)
    (hfin : (Function.support (fun i => ρ i x)).Finite) :
    ∑ᶠ k, groupWeights q ρ k x = ∑ᶠ i, ρ i x := by
  classical
  have heq (k : κ) : groupWeights q ρ k x =
      ∑ i ∈ hfin.toFinset with q i = k, ρ i x := by
    unfold groupWeights PartitionData.groupWeights
    rw [finsum_subtype_eq_finsum_cond (f := fun i => ρ i x) (fun i => q i = k)]
    apply finsum_cond_eq_sum_of_cond_iff
    intro i hi
    simp [hfin.mem_toFinset.mpr hi]
  simp_rw [heq]
  rw [finsum_sum_filter q hfin.toFinset (fun i => ρ i x)]
  exact (finsum_eq_sum _ hfin).symm

theorem group_smooth_partition {A : Set (ModelChart n a M)}
    {ι : Type v} {κ : Type w} {ρ : ι → M → ℝ} (q : ι → κ) (U : κ → Set M)
    (hρ : IsSmoothPartition A ρ) (hU : ∀ i, sectionSupport (ρ i) ⊆ U (q i)) :
    IsSmoothPartition A (groupWeights q ρ) ∧ IsSubordinate U (groupWeights q ρ) := by
  obtain ⟨hs, hpos, hlf, hsum⟩ := hρ
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k
    exact scalarContDiff_finsum (fun i => hs i.val)
      (hlf.comp_injective Subtype.val_injective)
  · intro k x
    exact finsum_nonneg (fun i : {i // q i = k} => hpos i.val x)
  · exact (locallyFinite_fiber_union hlf q).subset (support_groupWeights_subset q ρ hlf)
  · intro x
    rw [finsum_groupWeights q ρ x ((hlf.point_finite x).subset (fun _ hi => subset_closure hi))]
    exact hsum x
  · intro k x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (support_groupWeights_subset q ρ hlf k hx)
    simpa [i.property] using hU i.val hi

/-- Refine the basis of positive loci of compactly supported smooth bumps,
normalize its locally finite sum, then group by the original cover index. -/
theorem exists_smooth_partition (S : SmoothManifold n a M) {ι : Type v}
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ ρ : ι → M → ℝ,
      IsSmoothPartition S.smoothStructure.val ρ ∧ IsSubordinate U ρ := by
  classical
  let A := S.smoothStructure.val
  choose q hq using hcover
  let p : M → (M → ℝ) → Prop := fun x f =>
    PartitionData.ScalarSmooth A f ∧ (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
      f =ᶠ[𝓝 x] (fun _ => 1) ∧ sectionSupport f ⊆ U (q x)
  have hB (x : M) : (𝓝 x).HasBasis (p x) (fun f => Function.support f) := by
    apply hasBasis_iff.mpr
    intro t
    constructor
    · intro ht
      obtain ⟨V, hVt, hV, hxV⟩ := mem_nhds_iff.mp ht
      obtain ⟨f, hfs, hf01, hf1, hfsupp, _⟩ :=
        exists_local_bump S x (V ∩ U (q x)) (hV.inter (hU _)) ⟨hxV, hq x⟩
      exact ⟨f, ⟨hfs, hf01, hf1, fun y hy => (hfsupp hy).2⟩,
        fun y hy => hVt (hfsupp (subset_closure hy)).1⟩
    · rintro ⟨f, hfp, hft⟩
      apply Filter.mem_of_superset (hfp.2.2.1.mono (fun y hy => ?_)) hft
      rw [hy]
      exact one_ne_zero
  let : T2Space M := S.topologicalManifold.hausdorff
  let : SecondCountableTopology M := S.topologicalManifold.secondCountable
  let : LocallyCompactSpace M := TopologicalManifold.locallyCompactSpace S.topologicalManifold
  obtain ⟨J, c, f, hp, hcov, hlf⟩ :=
    refinement_of_locallyCompact_sigmaCompact_of_nhds_basis hB
  have hclosed : LocallyFinite (fun j => sectionSupport (f j)) := hlf.closure
  let b : M → ℝ := fun x => ∑ᶠ j, f j x
  have hb : ScalarContDiff (⊤ : ℕ∞) A b := scalarContDiff_finsum (fun j => (hp j).1) hclosed
  have hbpos (x : M) : 0 < b x := by
    apply finsum_pos (fun j => ((hp j).2.1 x).1)
    · have hx : x ∈ ⋃ j, Function.support (f j) := by rw [hcov]; trivial
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact ⟨j, lt_of_le_of_ne ((hp j).2.1 x).1 (Ne.symm hj)⟩
    · exact hlf.point_finite x
  let ρ : J → M → ℝ := fun j x => f j x * (b x)⁻¹
  have hρsupp (j : J) : sectionSupport (ρ j) ⊆ sectionSupport (f j) := by
    apply closure_mono
    intro x hx
    exact left_ne_zero_of_mul hx
  have hρ : IsSmoothPartition A ρ := by
    refine ⟨?_, ?_, hclosed.subset hρsupp, ?_⟩
    · intro j
      exact scalarContDiff_mul (hp j).1 (scalarContDiff_inv hb (fun x => (hbpos x).ne'))
    · intro j x
      exact mul_nonneg ((hp j).2.1 x).1 (inv_nonneg.mpr (hbpos x).le)
    · intro x
      change (∑ᶠ j, f j x * (b x)⁻¹) = 1
      rw [← finsum_mul]
      exact mul_inv_cancel₀ (hbpos x).ne'
  have hsub (j : J) : sectionSupport (ρ j) ⊆ U (q (c j)) :=
    (hρsupp j).trans (hp j).2.2.2
  exact ⟨groupWeights (q ∘ c) ρ, group_smooth_partition (q ∘ c) U hρ hsub⟩

/-- A two-member partition gives a cutoff equal to one off the closed support
of the weight assigned to the complement of A. -/
theorem exists_smooth_cutoff (S : SmoothManifold n a M) (A U : Set M)
    (hA : IsClosed A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ χ : M → ℝ, IsCutoff S A U χ := by
  let V : Bool → Set M := fun i => if i then U else Aᶜ
  have hV : ∀ i, IsOpen (V i) := by
    intro i
    cases i <;> simp [V, hU, hA.isOpen_compl]
  have hcover : ∀ x, ∃ i, x ∈ V i := by
    intro x
    by_cases hx : x ∈ A
    · exact ⟨true, hAU hx⟩
    · exact ⟨false, hx⟩
  obtain ⟨ρ, hs, hsub⟩ := exists_smooth_partition S V hV hcover
  obtain ⟨hsmooth, hpos, hlf, hsum⟩ := hs
  have hsum' (x : M) : ρ false x + ρ true x = 1 := by
    simpa [finsum_eq_sum_of_fintype, Fintype.sum_bool, add_comm] using hsum x
  refine ⟨ρ true, hsmooth true, ?_, ?_, hsub true⟩
  · intro x
    exact ⟨hpos true x, by linarith [hpos false x, hsum' x]⟩
  · refine ⟨(sectionSupport (ρ false))ᶜ, isClosed_closure.isOpen_compl, ?_, ?_⟩
    · intro x hx hxρ
      exact hsub false hxρ hx
    · intro x hx
      have hzero : ρ false x = 0 := Function.notMem_support.mp
        (fun h => hx (subset_closure h))
      linarith [hsum' x]

theorem exists_compactly_supported_smooth_cutoff (S : SmoothManifold n a M) (A U : Set M)
    (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) :
    ∃ χ : M → ℝ, IsCutoff S A U χ ∧ IsCompact (sectionSupport χ) := by
  let : T2Space M := S.topologicalManifold.hausdorff
  let : LocallyCompactSpace M := TopologicalManifold.locallyCompactSpace S.topologicalManifold
  obtain ⟨K, hKcp, hAK, hKU⟩ := exists_compact_between hA hU hAU
  obtain ⟨χ, hsmooth, h01, h1, hsupp⟩ := exists_smooth_cutoff S A (interior K)
    hA.isClosed isOpen_interior hAK
  exact ⟨χ, ⟨hsmooth, h01, h1, hsupp.trans (interior_subset.trans hKU)⟩,
    hKcp.of_isClosed_subset isClosed_closure (hsupp.trans interior_subset)⟩

end SmoothManifolds
