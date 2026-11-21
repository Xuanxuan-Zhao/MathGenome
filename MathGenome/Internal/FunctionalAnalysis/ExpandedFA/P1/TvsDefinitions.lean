import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.TvsDefinitions

/-! Native interfaces for the definitions in `fa2:p1:tvs-definitions`.
The canonical definitions live in the independent Specs so later independent
statements may use them without importing this implementation. -/

open Set Filter
open scoped Topology Pointwise

universe u

namespace ExpandedFA.P1

def tvs : TvsDefinitionsSpec.tvsType := fun 𝕜 E _ _ _ _ => TVS 𝕜 E

def lcs : TvsDefinitionsSpec.lcsType := fun 𝕜 E _ _ _ _ _ _ => LCS 𝕜 E

def balanced : TvsDefinitionsSpec.balancedType := fun 𝕜 _ _ _ _ A => Balanced 𝕜 A

def absorbing : TvsDefinitionsSpec.absorbingType := fun _ _ _ A => Absorbing A

def bounded : TvsDefinitionsSpec.boundedType := fun _ _ _ _ A => Bounded A

def cauchyNet : TvsDefinitionsSpec.cauchyNetType := fun _ _ _ _ _ x => CauchyNet x

def translationComplete : TvsDefinitionsSpec.completeType := fun E _ _ _ => TranslationComplete E

def fSpace : TvsDefinitionsSpec.fSpaceType := fun 𝕜 E _ _ _ _ => FSpace 𝕜 E

def frechetSpace : TvsDefinitionsSpec.frechetSpaceType :=
  fun 𝕜 E _ _ _ _ _ _ => FrechetSpace 𝕜 E

/-- No separation axiom is needed to obtain the native TVS interface. -/
theorem tvs_iff_joint_continuity : TvsDefinitionsSpec.JointContinuity := by
  intro 𝕜 E _ _ _ _
  constructor
  · rintro ⟨hadd, hsmul⟩
    let := hadd
    let := hsmul
    exact ⟨continuous_add, continuous_smul⟩
  · rintro ⟨hadd, hsmul⟩
    let : ContinuousAdd E := ⟨hadd⟩
    let : ContinuousSMul 𝕜 E := ⟨hsmul⟩
    let : ContinuousNeg E := ContinuousNeg.of_continuousConstSMul 𝕜 E
    exact ⟨{ continuous_add := hadd, continuous_neg := continuous_neg }, inferInstance⟩

theorem lcs_iff_convex_zero_basis : TvsDefinitionsSpec.LocalConvexity := by
  intro 𝕜 E _ _ _ _ _ _ h
  let := h.1
  exact ⟨fun h => (locallyConvexSpace_iff_exists_convex_subset_zero ℝ E).mp h.2,
    fun hconv => ⟨h, (locallyConvexSpace_iff_exists_convex_subset_zero ℝ E).mpr hconv⟩⟩

theorem translation_uniformity : TvsDefinitionsSpec.TranslationUniformity := by
  intro E _ _ _
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  exact uniformity_eq_comap_nhds_zero E

theorem cauchy_filter_iff_differences : TvsDefinitionsSpec.CauchyFilters := by
  intro E _ _ _
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  intro f
  rw [IsUniformAddGroup.cauchy_iff_tendsto]
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun U hU => ?_⟩
    rcases Filter.mem_prod_iff.mp (h hU) with ⟨V, hV, W, hW, hVW⟩
    exact ⟨V ∩ W, inter_mem hV hW, fun x hx y hy => hVW (show (x, y) ∈ V ×ˢ W from ⟨hx.1, hy.2⟩)⟩
  · rintro ⟨hne, h⟩
    refine ⟨hne, fun U hU => ?_⟩
    rcases h U hU with ⟨V, hV, hVV⟩
    exact Filter.mem_prod_iff.mpr ⟨V, hV, V, hV, fun p hp => hVV p.1 hp.1 p.2 hp.2⟩

theorem cauchy_net_iff_differences : TvsDefinitionsSpec.CauchyNets := by
  intro E ι _ _ _ _ _ _
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  intro x
  rw [IsUniformAddGroup.cauchy_map_iff_tendsto]
  simp only [show (atTop : Filter ι).NeBot from inferInstance, true_and]
  change (∀ U ∈ 𝓝 (0 : E), ∀ᶠ p : ι × ι in atTop ×ˢ atTop,
    x p.1 - x p.2 ∈ U) ↔ CauchyNet x
  rw [Filter.prod_atTop_atTop_eq]
  simp only [Filter.eventually_atTop_prod_self', CauchyNet]

theorem complete_iff_cauchy_filters : TvsDefinitionsSpec.CompleteFilters := by
  intro E _ _ _
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  constructor
  · intro h f hne hc
    exact h.complete ((cauchy_filter_iff_differences E f).mpr ⟨hne, hc⟩)
  · intro h
    exact ⟨fun hc => h _ ((cauchy_filter_iff_differences E _).mp hc).1
      ((cauchy_filter_iff_differences E _).mp hc).2⟩

theorem complete_cauchy_nets_converge : TvsDefinitionsSpec.CompleteNets := by
  intro E ι _ _ _ _ _ _ h x hx
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  exact h.complete ((cauchy_net_iff_differences E ι x).mpr hx)

/-- Every proper filter is the tail filter of a net: use pairs `(V, x)` with
`V` in the filter and `x ∈ V`, ordered by reverse inclusion of `V`. Including
all points of each `V`, rather than choosing just one, gives equality of filters. -/
private theorem exists_net_of_filter {E : Type u} (f : Filter E) [f.NeBot] :
    ∃ (ι : Type u) (_ : Preorder ι) (_ : IsDirectedOrder ι) (_ : Nonempty ι)
      (x : ι → E), Filter.map x atTop = f := by
  classical
  let ι := {p : Set E × E // p.1 ∈ f ∧ p.2 ∈ p.1}
  let : Preorder ι := Preorder.lift (fun i => OrderDual.toDual i.val.1)
  have hindex (V : Set E) (hV : V ∈ f) : ∃ i : ι, i.val.1 = V := by
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hV
    exact ⟨⟨(V, x), hV, hx⟩, rfl⟩
  let : Nonempty ι := ⟨(hindex univ univ_mem).choose⟩
  let : IsDirectedOrder ι := ⟨fun i j => by
    obtain ⟨k, hk⟩ := hindex (i.val.1 ∩ j.val.1) (inter_mem i.property.1 j.property.1)
    exact ⟨k, show k.val.1 ⊆ i.val.1 from hk ▸ inter_subset_left,
      show k.val.1 ⊆ j.val.1 from hk ▸ inter_subset_right⟩⟩
  let x : ι → E := fun i => i.val.2
  refine ⟨ι, inferInstance, inferInstance, inferInstance, x, ?_⟩
  apply Filter.ext
  intro V
  change (∀ᶠ i : ι in atTop, x i ∈ V) ↔ V ∈ f
  rw [Filter.eventually_atTop]
  constructor
  · rintro ⟨i, hi⟩
    refine mem_of_superset i.property.1 fun y hy => ?_
    exact hi ⟨(i.val.1, y), i.property.1, hy⟩ (show i.val.1 ⊆ i.val.1 from subset_rfl)
  · intro hV
    obtain ⟨i, hi⟩ := hindex V hV
    exact ⟨i, fun j hj => hi ▸ (show j.val.1 ⊆ i.val.1 from hj) j.property.2⟩

theorem complete_iff_cauchy_nets : TvsDefinitionsSpec.CompleteNetsIff := by
  intro E _ _ _
  constructor
  · intro h ι _ _ _ x hx
    exact complete_cauchy_nets_converge E ι h x hx
  · intro h
    let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    refine ⟨fun {f} hf => ?_⟩
    let : f.NeBot := hf.1
    obtain ⟨ι, hi, hd, hn, x, hx⟩ := exists_net_of_filter f
    let := hi
    let := hd
    let := hn
    have hc : CauchyNet x := (cauchy_net_iff_differences E ι x).mp (hx.symm ▸ hf)
    obtain ⟨a, ha⟩ := h ι x hc
    exact ⟨a, hx ▸ ha⟩

end ExpandedFA.P1
