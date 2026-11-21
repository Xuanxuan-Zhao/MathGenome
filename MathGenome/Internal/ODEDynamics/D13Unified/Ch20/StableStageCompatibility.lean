import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.StableStageCompatibility
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Flow
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

noncomputable section
open Set Function Filter
open scoped ContDiff Topology
namespace D13Unified.Ch20.StableStageCompatibility
open Ch06.StateDerivative Ch11.Flow
open Specs.D13Unified.Ch11.Flow
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : AutonomousODE E} {k : ℕ∞} {G : S → E} {P : E → S} {V : Set S}

lemma timeMap_regular (hk : 1 ≤ k) (hF : ContDiffOn ℝ (k : ℕ∞ω) F.eval F.domain)
    (t : ℝ) : ContDiffOn ℝ (k : ℕ∞ω) (flow F t) (timeDomainValue F t) := by
  rw [contDiffOn_iff_forall_nat_le]
  intro j hj
  by_cases hj0 : j = 0
  · subst j
    exact (contDiffOn_timeMap 1 (by omega) F
      (hF.of_le (by exact_mod_cast hk)) t).of_le (by norm_num)
  · exact contDiffOn_timeMap j (by omega) F (hF.of_le (by exact_mod_cast hj)) t

variable (H : Hypotheses F k G P V)
include H
lemma Hypotheses.field_c1 : ContDiffOn ℝ 1 F.eval F.domain :=
  H.field_regular.of_le (by exact_mod_cast H.one_le)

lemma Hypotheses.order_ne_zero : (k : ℕ∞ω) ≠ 0 := by
  exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ∞) < 1) H.one_le))

lemma Hypotheses.stageDomain_open (m : ℕ) : IsOpen (stageDomain F G V m) :=
  H.open_portion.inter ((isOpen_timeDomain F H.field_c1 _).preimage H.graph_regular.continuous)

lemma Hypotheses.stageMap_regular (m : ℕ) :
    ContDiffOn ℝ (k : ℕ∞ω) (stageMap F G m) (stageDomain F G V m) :=
  (timeMap_regular H.one_le H.field_regular _).comp H.graph_regular.contDiffOn
    (fun _ hξ => hξ.2)

lemma Hypotheses.stageMap_injective (m : ℕ) : InjOn (stageMap F G m) (stageDomain F G V m) := by
  intro ξ hξ η hη heq
  apply H.left_inverse.injective
  have hrξ := (reverse_flow F H.field_c1 hξ.2).2
  have hrη := (reverse_flow F H.field_c1 hη.2).2
  exact hrξ.symm.trans ((congrArg (fun x => flow F (-(-(m : ℝ))) x) heq).trans hrη)

lemma Hypotheses.stageMap_differential (m : ℕ) {ξ : S} (hξ : ξ ∈ stageDomain F G V m) :
    Injective (fderiv ℝ (stageMap F G m) ξ) := by
  have hc := H.stageMap_regular m
  have hd := (hc.differentiableOn H.order_ne_zero).differentiableAt
    ((H.stageDomain_open m).mem_nhds hξ)
  have hr := reverse_flow F H.field_c1 hξ.2
  have hb := (timeMap_regular H.one_le H.field_regular (-(-(m : ℝ)))).differentiableOn
    H.order_ne_zero
  have hdb := hb.differentiableAt ((isOpen_timeDomain F H.field_c1 _).mem_nhds hr.1)
  have hid : (fun η => flow F (-(-(m : ℝ))) (stageMap F G m η)) =ᶠ[𝓝 ξ] G := by
    filter_upwards [(H.stageDomain_open m).mem_nhds hξ] with η hη
    exact (reverse_flow F H.field_c1 hη.2).2
  have he : (fderiv ℝ (flow F (-(-(m : ℝ)))) (stageMap F G m ξ)).comp
      (fderiv ℝ (stageMap F G m) ξ) = fderiv ℝ G ξ := by
    exact ((hdb.hasFDerivAt.comp ξ hd.hasFDerivAt).congr_of_eventuallyEq hid.symm).fderiv.symm
  intro a b hab
  apply H.graph_differential ξ
  rw [← he]
  simpa only [ContinuousLinearMap.comp_apply] using congrArg (fderiv ℝ (flow F (-(-(m : ℝ)))) (stageMap F G m ξ)) hab

/-- Composition with exact maximal-domain membership, not an unrestricted group law. -/
lemma Hypotheses.compose_flow {x : E} {s t : ℝ} (hs : x ∈ timeDomainValue F s)
    (hts : x ∈ timeDomainValue F (t+s)) :
    flow F s x ∈ timeDomainValue F t ∧ flow F t (flow F s x) = flow F (t+s) x := by
  have htr := flow_translation F H.field_c1 x hs.1 s hs.2
  refine ⟨⟨(reverse_flow F H.field_c1 hs).1.1, ?_⟩, htr.2 t hts.2⟩
  rw [htr.1]
  exact hts.2

lemma Hypotheses.forward_from_stage {m n : ℕ} (hmn : m ≤ n) {ξ : S}
    (hξ : ξ ∈ stageDomain F G V m) :
    stageMap F G m ξ ∈ timeDomainValue F (n : ℝ) ∧
      flow F (n : ℝ) (stageMap F G m ξ) = flow F ((n : ℝ) - m) (G ξ) := by
  exact H.compose_flow hξ.2 (by
    simpa only [sub_eq_add_neg] using
      H.forward_exists ξ hξ.1 ((n : ℝ) - m) (sub_nonneg.mpr (by exact_mod_cast hmn)))

lemma Hypotheses.transition_graph {m n : ℕ} (hmn : m ≤ n) {ξ : S}
    (hξ : ξ ∈ stageDomain F G V m) :
    transition F G P m n ξ ∈ V ∧
      G (transition F G P m n ξ) = flow F (n : ℝ) (stageMap F G m ξ) := by
  have hf := H.forward_from_stage hmn hξ
  obtain ⟨η, hη, he⟩ := H.forward_invariant ξ hξ.1 ((n : ℝ) - m)
    (sub_nonneg.mpr (by exact_mod_cast hmn))
  have ht : transition F G P m n ξ = η := by
    simp only [transition, hf.2, ← he, H.left_inverse η]
  exact ⟨ht.symm ▸ hη, by rw [ht, hf.2, he]⟩

lemma Hypotheses.transition_mem {m n : ℕ} (hmn : m ≤ n) {ξ : S}
    (hξ : ξ ∈ stageDomain F G V m) :
    transition F G P m n ξ ∈ stageDomain F G V n ∧
      stageMap F G n (transition F G P m n ξ) = stageMap F G m ξ := by
  have hf := H.forward_from_stage hmn hξ
  have hg := H.transition_graph hmn hξ
  have hr := reverse_flow F H.field_c1 hf.1
  refine ⟨⟨hg.1, ?_⟩, ?_⟩
  · change G (transition F G P m n ξ) ∈ timeDomainValue F (-(n : ℝ))
    rw [hg.2]
    exact hr.1
  · exact (congrArg (flow F (-(n : ℝ))) hg.2).trans hr.2

lemma Hypotheses.transition_regular {m n : ℕ} (hmn : m ≤ n) :
    ContDiffOn ℝ (k : ℕ∞ω) (transition F G P m n) (stageDomain F G V m) := by
  exact H.projection_regular.comp_contDiffOn
    ((timeMap_regular H.one_le H.field_regular (n : ℝ)).comp (H.stageMap_regular m)
      (fun ξ hξ => (H.forward_from_stage hmn hξ).1))

lemma Hypotheses.transition_injective {m n : ℕ} (hmn : m ≤ n) :
    InjOn (transition F G P m n) (stageDomain F G V m) := by
  intro ξ hξ η hη he
  apply H.stageMap_injective m hξ hη
  rw [← (H.transition_mem hmn hξ).2, ← (H.transition_mem hmn hη).2, he]

lemma Hypotheses.transition_differential {m n : ℕ} (hmn : m ≤ n) {ξ : S}
    (hξ : ξ ∈ stageDomain F G V m) :
    Bijective (fderiv ℝ (transition F G P m n) ξ) := by
  have ht := H.transition_mem hmn hξ
  have hc := H.transition_regular hmn
  have hd := (hc.differentiableOn H.order_ne_zero).differentiableAt
    ((H.stageDomain_open m).mem_nhds hξ)
  have hn := ((H.stageMap_regular n).differentiableOn H.order_ne_zero).differentiableAt
    ((H.stageDomain_open n).mem_nhds ht.1)
  have hid : (fun η => stageMap F G n (transition F G P m n η)) =ᶠ[𝓝 ξ]
      stageMap F G m := by
    filter_upwards [(H.stageDomain_open m).mem_nhds hξ] with η hη
    exact (H.transition_mem hmn hη).2
  have he : (fderiv ℝ (stageMap F G n) (transition F G P m n ξ)).comp
      (fderiv ℝ (transition F G P m n) ξ) = fderiv ℝ (stageMap F G m) ξ := by
    exact ((hn.hasFDerivAt.comp ξ hd.hasFDerivAt).congr_of_eventuallyEq hid.symm).fderiv.symm
  have hi : Injective (fderiv ℝ (transition F G P m n) ξ) := by
    intro a b hab
    apply H.stageMap_differential m hξ
    rw [← he]
    simpa only [ContinuousLinearMap.comp_apply] using congrArg (fderiv ℝ (stageMap F G n) (transition F G P m n ξ)) hab
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

/-- The inverse formula also has its own actual time-domain membership. -/
lemma Hypotheses.transition_inverse {m n : ℕ} (hmn : m ≤ n) {ξ : S}
    (hξ : ξ ∈ stageDomain F G V m) :
    G (transition F G P m n ξ) ∈ timeDomainValue F ((m : ℝ) - n) ∧
      P (flow F ((m : ℝ) - n) (G (transition F G P m n ξ))) = ξ := by
  have hpos : 0 ≤ (n : ℝ) - m := sub_nonneg.mpr (by exact_mod_cast hmn)
  have hr := reverse_flow F H.field_c1 (H.forward_exists ξ hξ.1 _ hpos)
  have hg : G (transition F G P m n ξ) = flow F ((n : ℝ) - m) (G ξ) :=
    (H.transition_graph hmn hξ).2.trans (H.forward_from_stage hmn hξ).2
  have hneg : -((n : ℝ) - m) = (m : ℝ) - n := by ring
  rw [hneg] at hr
  rw [hg]
  exact ⟨hr.1, by rw [hr.2, H.left_inverse ξ]⟩

omit H in
/-- In equal finite dimensions an injective differential makes the image of an
open set open. This also covers the zero-dimensional parameter space. -/
lemma image_open_of_injective_differential {u : Set S} {f : S → S}
    (hu : IsOpen u) (hk : 1 ≤ k) (hc : ContDiffOn ℝ (k : ℕ∞ω) f u)
    (hi : ∀ x ∈ u, Injective (fderiv ℝ f x)) : IsOpen (f '' u) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro y ⟨x, hx, rfl⟩
  have hca := hc.contDiffAt (hu.mem_nhds hx)
  let L : S ≃L[ℝ] S :=
    (LinearEquiv.ofInjectiveEndo (fderiv ℝ f x).toLinearMap (hi x hx)).toContinuousLinearEquiv
  have hL : (L : S →L[ℝ] S) = fderiv ℝ f x := by ext v; rfl
  have hd : HasFDerivAt f (L : S →L[ℝ] S) x := by
    rw [hL]
    exact ((hc.differentiableOn (by
      exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℕ∞) < 1) hk)))).differentiableAt
      (hu.mem_nhds hx)).hasFDerivAt
  have hk0 : (k : ℕ∞ω) ≠ 0 := by
    have hk' : (1 : ℕ∞ω) ≤ k := by exact_mod_cast hk
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) hk')
  let e := hca.toOpenPartialHomeomorph f hd hk0
  have hxe : x ∈ e.source := hca.mem_toOpenPartialHomeomorph_source hd hk0
  have ho : IsOpen (e '' (u ∩ e.source)) :=
    e.isOpen_image_of_subset_source (hu.inter e.open_source) inter_subset_right
  have hym : f x ∈ e '' (u ∩ e.source) := ⟨x, ⟨hx, hxe⟩, rfl⟩
  apply mem_of_superset (ho.mem_nhds hym)
  rintro z ⟨a, ha, rfl⟩
  exact ⟨a, ha.1, rfl⟩

lemma Hypotheses.transition_image_open {m n : ℕ} (hmn : m ≤ n) :
    IsOpen (transition F G P m n '' stageDomain F G V m) :=
  image_open_of_injective_differential (H.stageDomain_open m) H.one_le
    (H.transition_regular hmn) (fun _ hξ => (H.transition_differential hmn hξ).1)

lemma Hypotheses.transition_inverse_regular {m n : ℕ} (hmn : m ≤ n) :
    ContDiffOn ℝ (k : ℕ∞ω) (fun η => P (flow F ((m : ℝ) - n) (G η)))
      (transition F G P m n '' stageDomain F G V m) := by
  apply H.projection_regular.comp_contDiffOn
  apply (timeMap_regular H.one_le H.field_regular _).comp H.graph_regular.contDiffOn
  rintro η ⟨ξ, hξ, rfl⟩
  exact (H.transition_inverse hmn hξ).1

/-- A single open partial homeomorphism on the entire stage source. Its total
inverse uses the original backward flow only on its proven target domain. -/
def Hypotheses.stageChange (m n : ℕ) (hmn : m ≤ n) : OpenPartialHomeomorph S S where
  toFun := transition F G P m n
  invFun := fun η => P (flow F ((m : ℝ) - n) (G η))
  source := stageDomain F G V m
  target := transition F G P m n '' stageDomain F G V m
  map_source' := fun ξ hξ => ⟨ξ, hξ, rfl⟩
  map_target' := by
    rintro η ⟨ξ, hξ, rfl⟩
    rw [(H.transition_inverse hmn hξ).2]
    exact hξ
  left_inv' := fun ξ hξ => (H.transition_inverse hmn hξ).2
  right_inv' := by
    rintro η ⟨ξ, hξ, rfl⟩
    rw [(H.transition_inverse hmn hξ).2]
  open_source := H.stageDomain_open m
  open_target := H.transition_image_open hmn
  continuousOn_toFun := (H.transition_regular hmn).continuousOn
  continuousOn_invFun := (H.transition_inverse_regular hmn).continuousOn

omit H in
theorem compatibility : Specs.D13Unified.Ch20.StableStageCompatibility.compatibilityExpected := by
  intro S E _ _ _ _ _ _ F k G P V H
  refine ⟨{
    open_domain := H.stageDomain_open
    regular := H.stageMap_regular
    injective := H.stageMap_injective
    differential := fun m ξ hξ => H.stageMap_differential m hξ
    change := H.stageChange
    change_source := fun _ _ _ => rfl
    change_target := ?_
    change_regular := fun _ _ h => H.transition_regular h
    change_symm_regular := fun _ _ h => H.transition_inverse_regular h
    change_formula := fun _ _ _ _ _ => rfl
    change_symm_formula := fun _ _ _ _ _ => rfl
    change_differential := fun _ _ h _ hξ => H.transition_differential h hξ
    forward_domain := fun _ _ h _ hξ => (H.forward_from_stage h hξ).1
    backward_domain := ?_
    forward_graph := fun _ _ h _ hξ => (H.transition_graph h hξ).2
    intertwine := fun _ _ h _ hξ => (H.transition_mem h hξ).2 }⟩
  · rintro m n h η ⟨ξ, hξ, rfl⟩
    exact (H.transition_mem h hξ).1
  · rintro m n h η ⟨ξ, hξ, rfl⟩
    exact (H.transition_inverse h hξ).1

omit H in
/-- The compatibility theorem supplies exactly the fields required by the
upstream gluing theorem, whenever the local portion is nonempty. -/
theorem atlas_package : Specs.D13Unified.Ch20.StableStageCompatibility.atlasPackageExpected := by
  intro S E _ _ _ _ _ _ F k G P V H hV
  obtain ⟨C⟩ := compatibility S E F k G P V H
  let D : CountableImmersedAtlas.Data S E k := {
    one_le := H.one_le
    U := stageDomain F G V
    open_U := C.open_domain
    f := stageMap F G
    regular := C.regular
    injective := C.injective
    differential := C.differential
    change := C.change
    change_source := C.change_source
    change_target := C.change_target
    change_regular := C.change_regular
    change_symm_regular := C.change_symm_regular
    intertwine := C.intertwine
    nonempty := by
      obtain ⟨ξ, hξ⟩ := hV
      exact ⟨stageMap F G 0 ξ, 0, ξ,
        ⟨hξ, by simpa using H.forward_exists ξ hξ 0 le_rfl⟩, rfl⟩ }
  exact ⟨D, rfl, rfl⟩

end D13Unified.Ch20.StableStageCompatibility
