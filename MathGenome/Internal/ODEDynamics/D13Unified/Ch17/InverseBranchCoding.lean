import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch17.InverseBranchCoding
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.InverseCodingConstruction
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.FullShiftChaos
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Complete disjoint inverse-branch coding theorem. The upstream construction
supplies the homeomorphism onto the exact finite-level intersection. This module
proves its topological properties and identifies the actual local forward map
with the chaotic conjugate of the shift. Sensitivity uses Heine--Cantor for the
inverse coding map on its compact domain, with strict separation. -/
namespace D13Unified.Ch17.InverseBranchCoding
open Set Topology
open D13Unified.Ch17.ShiftSpaces
open D13Unified.Ch17.InverseCodingConstruction
open D13Unified.Ch17.ChaosDefinitions
noncomputable section

/-- Conjugacy transports open-set transitivity without a metric assumption. -/
lemma transitive_of_conjugacy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y)
    (hh : Function.Semiconj h F G) (ht : TopologicallyTransitive F) :
    TopologicallyTransitive G := by
  rw [topologicallyTransitive_iff_exists_mem] at ht ⊢
  intro U V hU hnU hV hnV
  obtain ⟨x, hx, n, hn⟩ := ht (h ⁻¹' U) (h ⁻¹' V)
    (hU.preimage h.continuous) (h.surjective.nonempty_preimage.mpr hnU)
    (hV.preimage h.continuous) (h.surjective.nonempty_preimage.mpr hnV)
  exact ⟨h x, hx, n, (hh.iterate_right n x) ▸ hn⟩

/-- Positive periodic points transport with their actual positive periods. -/
lemma dense_periodic_of_conjugacy {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (F : X → X) (G : Y → Y) (h : X ≃ₜ Y)
    (hh : Function.Semiconj h F G) (hp : DensePeriodicPoints F) :
    DensePeriodicPoints G := by
  rw [densePeriodicPoints_iff_open] at hp ⊢
  intro U hU hnU
  obtain ⟨x, hx, n, hn, hnx⟩ := hp (h ⁻¹' U)
    (hU.preimage h.continuous) (h.surjective.nonempty_preimage.mpr hnU)
  refine ⟨h x, hx, n, hn, ?_⟩
  rw [← hh.iterate_right n x, hnx]

/-- Compactness of the target makes the inverse coordinate change uniformly
continuous. Halving its modulus gives the strict sensitivity convention. -/
lemma sensitive_of_conjugacy {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [CompactSpace Y] (F : X → X) (G : Y → Y) (h : X ≃ₜ Y)
    (hh : Function.Semiconj h F G) (hs : SensitiveDependence F) :
    SensitiveDependence G := by
  obtain ⟨δ, hδ, hs⟩ := hs
  obtain ⟨ε, hε, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous h.symm.continuous) δ hδ
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro y U hU
  obtain ⟨x, hx, n, hn⟩ := hs (h.symm y) (h ⁻¹' U)
    (h.continuous.continuousAt.preimage_mem_nhds (by simpa using hU))
  refine ⟨h x, hx, n, ?_⟩
  have hsep : ε ≤ dist (G^[n] y) (G^[n] (h x)) := by
    by_contra! hlt
    have hm := hmod hlt
    rw [← h.apply_symm_apply y, ← hh.iterate_right n (h.symm y),
      ← hh.iterate_right n x, h.symm_apply_apply, h.symm_apply_apply] at hm
    exact (not_lt_of_ge hn.le) hm
  exact (half_lt_self hε).trans_le hsep

/-- A conjugate of the one-sided shift is chaotic for its given metric.
Only the symbolic metric is installed locally; its topology is the product
one used by the canonical coding homeomorphism. -/
lemma chaotic_of_shift_conjugacy {Y : Type} [MetricSpace Y]
    (π : OneSided ≃ₜ Y) (f : Y → Y)
    (hh : Function.Semiconj π shiftPlus f) : Chaotic f := by
  let : CompactSpace Y := π.compactSpace
  let : MetricSpace OneSided := PiNat.metricSpace (E := fun _ => Binary)
  refine ⟨transitive_of_conjugacy shiftPlus f π hh FullShiftChaos.shiftPlus_transitive,
    dense_periodic_of_conjugacy shiftPlus f π hh FullShiftChaos.shiftPlus_dense_periodic,
    sensitive_of_conjugacy shiftPlus f π hh ?_⟩
  exact ⟨1 / 2, by norm_num, FullShiftChaos.shiftPlus_sensitive⟩

/-- No point becomes isolated under a homeomorphism. -/
lemma no_isolated_of_shift {Y : Type*} [TopologicalSpace Y] (π : OneSided ≃ₜ Y) :
    ∀ x : Y, ∀ V ∈ 𝓝 x, ∃ y ∈ V, y ≠ x := by
  intro x V hV
  obtain ⟨s, hs, hne⟩ := ShiftCompactness.noIsolatedPointsPlus (π.symm x) (π ⁻¹' V)
    (π.continuous.continuousAt.preimage_mem_nhds (by simpa using hV))
  refine ⟨π s, hs, ?_⟩
  intro heq
  exact hne (π.injective (heq.trans (π.apply_symm_apply x).symm))

theorem limitSet_topology :
    Specs.D13Unified.Ch17.InverseBranchCoding.limitSet_topologyStatement := by
  intro K _ _ _ b q hq hb hi hd
  obtain ⟨π, _, _⟩ := coding_exists b q hq hb hi hd
  let : CompactSpace (limitSet b) := π.compactSpace
  exact ⟨isCompact_iff_compactSpace.mpr inferInstance,
    no_isolated_of_shift π, π.totallyDisconnectedSpace⟩

/-- Construct the restriction from the proved local intertwining equation.
The self-map is a conjugate of the shift, and its equality to F is proved
pointwise; it is not an assumed extension of F. -/
lemma restriction_from_coding {K Y : Type} [MetricSpace K] [TopologicalSpace Y]
    (b : Binary → K → K) (ι : K → Y) (U : Set K) (F : U → Y)
    (π : OneSided ≃ₜ limitSet b)
    (hc : ∀ s, ∃ hs : (π s : K) ∈ U,
      F ⟨(π s : K), hs⟩ = ι (π (shiftPlus s) : K)) :
    ∃ (hΛ : limitSet b ⊆ U) (f : limitSet b → limitSet b),
      (∀ x, ι (f x : K) = F ⟨(x : K), hΛ x.property⟩) ∧
      Continuous f ∧ Function.Surjective f ∧
      Set.range (fun x : limitSet b => F ⟨(x : K), hΛ x.property⟩) = ι '' limitSet b ∧
      Function.Semiconj π shiftPlus f := by
  let f : limitSet b → limitSet b := fun x => π (shiftPlus (π.symm x))
  have hΛ : limitSet b ⊆ U := by
    intro x hx
    obtain ⟨hs, _⟩ := hc (π.symm ⟨x, hx⟩)
    simpa only [π.apply_symm_apply] using hs
  have hv : ∀ x : limitSet b, ι (f x : K) = F ⟨(x : K), hΛ x.property⟩ := by
    intro x
    obtain ⟨hs, he⟩ := hc (π.symm x)
    simpa only [π.apply_symm_apply] using he.symm
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨s, hs⟩ := shiftPlus_surjective (π.symm y)
    refine ⟨π s, ?_⟩
    simp only [f, π.symm_apply_apply, hs, π.apply_symm_apply]
  refine ⟨hΛ, f, hv,
    π.continuous.comp (shiftPlus_continuous.comp π.symm.continuous), hf, ?_, ?_⟩
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨f x, (f x).property, hv x⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz⟩ := hf ⟨x, hx⟩
      exact ⟨z, (hv z).symm.trans (congrArg (fun t : limitSet b => ι (t : K)) hz)⟩
  · intro s
    simp only [f, π.symm_apply_apply]

theorem inverse_branch_coding :
    Specs.D13Unified.Ch17.InverseBranchCoding.inverse_branch_codingStatement := by
  intro K _ _ _ b q hq hb hi hd U hU F hFc hbU hF
  obtain ⟨π, hπ, hc⟩ := local_conjugacy b q hq hb hi hd id U hU F hFc hbU hF
  obtain ⟨hΛ, f, hv, hf, hsurj, hrange, hh⟩ :=
    restriction_from_coding b id U F π hc
  obtain ⟨hcompact, hnoisol, htot⟩ := limitSet_topology b q hq hb hi hd
  refine ⟨hcompact, hnoisol, htot, hΛ, f, π, hv, hf, hsurj, ?_,
    fun s => (hh s).symm, hπ, chaotic_of_shift_conjugacy π f hh⟩
  simpa only [Set.image_id] using hrange

theorem ambient_inverse_branch_coding :
    Specs.D13Unified.Ch17.InverseBranchCoding.ambient_inverse_branch_codingStatement := by
  intro X _ K hK hn b q hq hb hi hd U hU F hFc hbU hF
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := hn.to_subtype
  obtain ⟨π, hπ, hc⟩ := ambient_conjugacy K hK hn b q hq hb hi hd U hU F hFc hbU hF
  let V : Set K := Subtype.val ⁻¹' U
  let j : V → U := fun x => ⟨(x.val : X), x.property⟩
  obtain ⟨hΛ, f, hv, hf, hsurj, hrange, hh⟩ :=
    restriction_from_coding b (Subtype.val : K → X) V (F ∘ j) π hc
  obtain ⟨hcompact, hnoisol, htot⟩ := limitSet_topology b q hq hb hi hd
  refine ⟨hcompact.image continuous_subtype_val, hnoisol, htot,
    (fun x => hΛ x.property), f, π, hv, hf, hsurj, hrange,
    fun s => (hh s).symm, hπ, chaotic_of_shift_conjugacy π f hh⟩

end
end D13Unified.Ch17.InverseBranchCoding
