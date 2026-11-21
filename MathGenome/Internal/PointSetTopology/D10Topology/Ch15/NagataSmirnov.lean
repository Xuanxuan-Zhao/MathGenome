import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.NagataSmirnov
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.MetricSigmaRefinement
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.PerfectNormal
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.FunctionTopologies
import Mathlib.Topology.MetricSpace.PiNat

/-!
Nagata--Smirnov, with no countability restriction on a basis layer.
The forward proof refines the covers by small balls and flattens the two
natural-number layer indices. In the converse each locally finite layer
maps continuously into its supremum-metric function space. The countable
product of these spaces has a compatible metric. The cozero coordinates
recover all basis neighborhoods, so the map is an embedding; we pull back
the product metric. Empty spaces and empty layers need no separate choices
of points.
-/

noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
universe u v w

namespace D10Topology.Ch15

variable {X : Type u} [TopologicalSpace X]

/-- Restricting to an injective family of indices preserves sigma local finiteness. -/
theorem SigmaLocallyFinite.comp_injective {I : Type v} {J : Type w}
    {A : I → Set X} (hA : SigmaLocallyFinite A)
    {e : J → I} (he : Function.Injective e) : SigmaLocallyFinite (A ∘ e) := by
  obtain ⟨L, hL, hfin⟩ := hA
  refine ⟨fun n => e ⁻¹' L n, ?_, fun n => ?_⟩
  · exact iUnion_eq_univ_iff.mpr fun j => iUnion_eq_univ_iff.mp hL (e j)
  · let e' : (e ⁻¹' L n) → L n := fun j => ⟨e j, j.property⟩
    exact (hfin n).comp_injective (show Function.Injective e' from
      fun a b hab => Subtype.ext (he (congrArg Subtype.val hab)))

/-- Passing from indexed sets to their range only removes repetitions. -/
theorem SigmaLocallyFinite.on_range {I : Type v} {A : I → Set X}
    (hA : SigmaLocallyFinite A) :
    SigmaLocallyFinite (fun b : range A => (b : Set X)) := by
  classical
  let e : range A → I := fun b => b.property.choose
  have heq (b : range A) : A (e b) = b := b.property.choose_spec
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    rw [← heq a, ← heq b, hab]
  simpa only [Function.comp_def, heq] using hA.comp_injective he

/-- A sequence of sigma locally finite families is still sigma locally finite. -/
theorem SigmaLocallyFinite.sigma_nat {I : Type v} {A : ℕ → I → Set X}
    (hA : ∀ n, SigmaLocallyFinite (A n)) :
    SigmaLocallyFinite (fun j : ℕ × I => A j.1 j.2) := by
  classical
  choose L hL hfin using hA
  let K (n : ℕ) : Set (ℕ × I) :=
    {j | j.1 = n.unpair.1 ∧ j.2 ∈ L n.unpair.1 n.unpair.2}
  refine ⟨K, ?_, fun n => ?_⟩
  · apply iUnion_eq_univ_iff.mpr
    intro ⟨m, i⟩
    obtain ⟨k, hk⟩ := iUnion_eq_univ_iff.mp (hL m) i
    exact ⟨Nat.pair m k, by simpa [K] using hk⟩
  · let e : K n → L n.unpair.1 n.unpair.2 := fun j => ⟨j.val.2, j.property.2⟩
    have he : Function.Injective e := by
      intro a b hab
      apply Subtype.ext
      exact Prod.ext (a.property.1.trans b.property.1.symm) (congrArg Subtype.val hab)
    have hf := (hfin n.unpair.1 n.unpair.2).comp_injective he
    convert hf using 1
    funext j
    exact congrArg (fun m => A m j.val.2) j.property.1

theorem metric_sigmaLocallyFinite_basis (X : Type u) [MetricSpace X] :
    ∃ B : Set (Set X), IsTopologicalBasis B ∧
      SigmaLocallyFinite (fun b : B => (b : Set X)) := by
  classical
  let r : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hr (m : ℕ) : 0 < r m := div_pos zero_lt_one (Nat.cast_add_one_pos m)
  have hex (m : ℕ) := metric_sigma_refinement (fun x : X => Metric.ball x (r m))
    (fun _ => Metric.isOpen_ball) (iUnion_eq_univ_iff.mpr fun x =>
      ⟨x, Metric.mem_ball_self (hr m)⟩)
  choose V hVo hVr hVd hVs using hex
  let A : ℕ × (ℕ × X) → Set X := fun j => V j.1 j.2
  have hAb : IsTopologicalBasis (range A) := by
    apply isTopologicalBasis_of_isOpen_of_nhds
    · rintro _ ⟨j, rfl⟩
      exact hVo j.1 j.2
    · intro x U hx hU
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU x hx
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (half_pos hε)
      obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp (hVr m).1 x
      refine ⟨V m j, ⟨(m, j), rfl⟩, hj, ?_⟩
      intro y hy
      apply hball
      have hxj := hVs m j hj
      have hyj := hVs m j hy
      have ht := dist_triangle y j.2 x
      have hxy : dist y x < ε := by
        change dist x j.2 < r m at hxj
        change dist y j.2 < r m at hyj
        rw [dist_comm j.2 x] at ht
        dsimp only [r] at hxj hyj
        linarith
      exact hxy
  exact ⟨range A, hAb, (SigmaLocallyFinite.sigma_nat
    (fun m => sigmaLocallyDiscrete_sigmaLocallyFinite _ (hVd m))).on_range⟩

/-- A locally finite family of cozero coordinates is continuous for the
supremum metric, although its index set can be arbitrarily large. -/
theorem continuous_cozero_layer {I : Type v} (A : I → Set X)
    (hA : LocallyFinite A) (f : I → X → unitInterval)
    (hf : ∀ i, Continuous (f i))
    (hz : ∀ i x, x ∉ A i → f i x = 0) :
    @Continuous X (I → unitInterval) _
      Ch13.uniformMetric.toUniformSpace.toTopologicalSpace (fun x i => f i x) := by
  letI : TopologicalSpace (I → unitInterval) :=
    Ch13.uniformMetric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (I → unitInterval) := Ch13.uniformMetric
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨N, hN, hfin⟩ := hA x
  have hclose : ∀ᶠ y in 𝓝 x, ∀ i ∈ {i | (A i ∩ N).Nonempty},
      dist (f i y) (f i x) < ε / 2 := by
    apply (eventually_all_finite hfin).mpr
    intro i _
    exact (Metric.continuousAt_iff'.mp (hf i).continuousAt (ε / 2) (half_pos hε))
  filter_upwards [hN, hclose] with y hy hclose
  have hbound : Ch13.uniformDistance (fun i => f i y) (fun i => f i x) ≤ ε / 2 := by
    apply (Ch13.uniformDistance_le _ _ _ (half_pos hε).le).mpr
    intro i
    by_cases hi : (A i ∩ N).Nonempty
    · exact (min_le_right _ _).trans (hclose i hi).le
    · have hyA : y ∉ A i := fun h => hi ⟨y, h, hy⟩
      have hxA : x ∉ A i := fun h => hi ⟨x, h, mem_of_mem_nhds hN⟩
      rw [hz i y hyA, hz i x hxA, Ch13.boundedDistance_self]
      exact (half_pos hε).le
  exact hbound.trans_lt (half_lt_self hε)

/-- Evaluating one coordinate is continuous in the supremum metric. -/
theorem continuous_uniformMetric_eval {I : Type v} (i : I) :
    @Continuous (I → unitInterval) ℝ
      Ch13.uniformMetric.toUniformSpace.toTopologicalSpace _ (fun g => (g i : ℝ)) := by
  letI : TopologicalSpace (I → unitInterval) :=
    Ch13.uniformMetric.toUniformSpace.toTopologicalSpace
  letI : MetricSpace (I → unitInterval) := Ch13.uniformMetric
  apply continuous_iff_continuousAt.mpr
  intro g
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  refine ⟨min 1 ε, lt_min zero_lt_one hε, ?_⟩
  intro h hh
  have hmin : min 1 (dist (h i) (g i)) < min 1 ε :=
    (Ch13.boundedDistance_le_uniformDistance h g i).trans_lt hh
  have hdist : dist (h i) (g i) < ε := by
    rcases min_lt_iff.mp hmin with h | h
    · exact (not_lt_of_ge (min_le_left _ _) h).elim
    · exact h.trans_le (min_le_right _ _)
  exact hdist

theorem exists_compatibleMetric_of_sigmaLocallyFinite_basis
    (X : Type u) [t : TopologicalSpace X] [RegularSpace X] [T1Space X]
    (B : Set (Set X)) (hB : IsTopologicalBasis B)
    (hσ : SigmaLocallyFinite (fun b : B => (b : Set X))) :
    ∃ d : MetricSpace X, Ch09.metricTopology d.toPseudoMetricSpace = t := by
  classical
  have hcozero (b : B) := sigmaLocallyFinite_basis_cozero X B hB hσ b (hB.isOpen b.property)
  choose f hf hfpos using hcozero
  have hpos (b : B) (x : X) : x ∈ (b : Set X) ↔ 0 < (f b x : ℝ) := by
    rw [hfpos b]
    rfl
  have hz (b : B) (x : X) (hx : x ∉ (b : Set X)) : f b x = 0 := by
    apply Subtype.ext
    apply le_antisymm
    · exact le_of_not_gt (fun hp => hx ((hpos b x).mpr hp))
    · exact (f b x).property.1
  obtain ⟨L, hL, hfin⟩ := hσ
  letI : ∀ n, TopologicalSpace (L n → unitInterval) := fun _ =>
    Ch13.uniformMetric.toUniformSpace.toTopologicalSpace
  letI : ∀ n, MetricSpace (L n → unitInterval) := fun _ => Ch13.uniformMetric
  let E := ∀ n, L n → unitInterval
  let F : X → E := fun x _ b => f b.val x
  have hFc : Continuous F := by
    apply continuous_pi
    intro n
    exact continuous_cozero_layer (fun b : L n => (b.val : Set X)) (hfin n)
      (fun b => f b.val) (fun b => hf b.val) (fun b => hz b.val)
  have hFi : Function.Injective F := by
    intro x y hxy
    by_contra hne
    obtain ⟨b, hb, hxb, hby⟩ := hB.exists_subset_of_mem_open
      (show x ∈ ({y} : Set X)ᶜ from hne) isClosed_singleton.isOpen_compl
    obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp hL (⟨b, hb⟩ : B)
    have heq : f ⟨b, hb⟩ x = f ⟨b, hb⟩ y :=
      congrArg (fun g : E => g n ⟨⟨b, hb⟩, hn⟩) hxy
    have hp : 0 < (f ⟨b, hb⟩ x : ℝ) := (hpos ⟨b, hb⟩ x).mp hxb
    rw [heq, hz ⟨b, hb⟩ y (fun hy => hby hy rfl)] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  have hFind : Topology.IsInducing F := by
    apply Topology.isInducing_iff_nhds.mpr
    intro x
    apply le_antisymm hFc.continuousAt.le_comap
    intro U hU
    obtain ⟨b, hb, hxb, hbU⟩ := hB.mem_nhds_iff.mp hU
    obtain ⟨n, hn⟩ := iUnion_eq_univ_iff.mp hL (⟨b, hb⟩ : B)
    let b' : L n := ⟨⟨b, hb⟩, hn⟩
    let T : Set E := {g | 0 < (g n b' : ℝ)}
    have hT : IsOpen T := isOpen_lt continuous_const
      ((continuous_uniformMetric_eval b').comp (continuous_apply n))
    have hxT : F x ∈ T := by
      change 0 < (f ⟨b, hb⟩ x : ℝ)
      exact (hpos ⟨b, hb⟩ x).mp hxb
    apply mem_comap.mpr
    refine ⟨T, hT.mem_nhds hxT, ?_⟩
    intro y hy
    apply hbU
    change 0 < (f ⟨b, hb⟩ y : ℝ) at hy
    exact (hpos ⟨b, hb⟩ y).mpr hy
  have hFe : Topology.IsEmbedding F := ⟨hFind, hFi⟩
  letI : MetricSpace E := PiCountable.metricSpace
  exact ⟨hFe.comapMetricSpace F, rfl⟩

/-- Nagata--Smirnov with regularity and T1 explicitly separated. -/
theorem nagata_smirnov (X : Type u) (t : TopologicalSpace X) :
    Ch09.Metrizable t ↔ @RegularSpace X t ∧ @T1Space X t ∧
      ∃ B : Set (Set X), @IsTopologicalBasis X t B ∧
        @SigmaLocallyFinite X B t (fun b => (b : Set X)) := by
  letI := t
  constructor
  · rintro ⟨d, hd⟩
    letI : MetricSpace X := d.replaceTopology hd.symm
    exact ⟨inferInstance, inferInstance, metric_sigmaLocallyFinite_basis X⟩
  · rintro ⟨hr, hT1, B, hB, hσ⟩
    letI := hr
    letI := hT1
    exact exists_compatibleMetric_of_sigmaLocallyFinite_basis X B hB hσ

end D10Topology.Ch15
