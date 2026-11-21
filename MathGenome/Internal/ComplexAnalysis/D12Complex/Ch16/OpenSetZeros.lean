import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.OpenSetZeros
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.EntireZeros
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.BoundaryFactorProduct
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SingularityGrowth
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Connected.LocallyConnected

/-!
D12.16.05. Finite divisors use the accepted polynomial construction. For an
infinite divisor, enumerate its multiplicity slots and invert about a divisor-free
disk. The transformed sequence satisfies every hypothesis of the accepted
boundary-factor theorem. Its full product tends to one at infinity, so the
pullback extends holomorphically at the center with value one. Inversion has
nonzero derivative away from that center and therefore preserves zero orders.

The construction works on the whole open set, even when disconnected: no
connectedness assumption enters the transformed-product theorem. Finite orders
at every point give nontriviality on each open connected component.
-/

noncomputable section
open Set Metric Filter
open scoped Topology

namespace D12Complex.OpenSetZeros

abbrev Realizes := Specs.D12Complex.Ch16.OpenSetZeros.Realizes_value

/-- Compact subsets meet the support of a divisor in finitely many points. -/
lemma finite_support_on_compact {Ω : Set ℂ} (d : Function.locallyFinsuppWithin Ω ℕ)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) : (K ∩ d.support).Finite := by
  have h : {z : ℂ | d z = 0} ∈ codiscreteWithin K :=
    (codiscreteWithin_mono hKΩ) d.eq_zero_codiscreteWithin
  have heq : K ∩ d.support = K \ {z : ℂ | d z = 0} := by ext z; simp
  rw [heq]
  exact hK.finite_sdiff_of_mem_codiscreteWithin h

/-- A divisor-free disk can be found in any nonempty open set. -/
lemma exists_divisor_free_disk {Ω : Set ℂ} (hΩ : IsOpen Ω) (hne : Ω.Nonempty)
    (d : Function.locallyFinsuppWithin Ω ℕ) :
    ∃ a : ℂ, ∃ r : ℝ, 0 < r ∧ ball a r ⊆ Ω ∧ ∀ z ∈ ball a r, d z = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨t, ht, hfin⟩ := d.supportLocallyFiniteWithinDomain x hx
  have hnh : interior t ∩ Ω ∈ 𝓝 x := inter_mem (interior_mem_nhds.mpr ht) (hΩ.mem_nhds hx)
  have hinf := infinite_of_mem_nhds x hnh
  obtain ⟨a, ha, hnot⟩ := hinf.exists_notMem_finite hfin
  have hn : interior t ∩ Ω ∩ (t ∩ d.support)ᶜ ∈ 𝓝 a := by
    exact inter_mem (inter_mem (isOpen_interior.mem_nhds ha.1) (hΩ.mem_nhds ha.2))
      (hfin.isClosed.isOpen_compl.mem_nhds hnot)
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨a, r, hr, fun z hz => (hball hz).1.2, ?_⟩
  intro z hz
  by_contra hh
  exact (hball hz).2 ⟨interior_subset (hball hz).1.1, hh⟩

lemma realizes_of_order {Ω : Set ℂ} (d : Function.locallyFinsuppWithin Ω ℕ)
    (f : ℂ → ℂ) (hf : HolomorphicOn Ω f)
    (ho : ∀ z ∈ Ω, analyticOrderAt f z = (d z : ℕ∞)) : Realizes Ω d f := by
  refine ⟨hf, ho, ?_, ?_⟩
  · intro z hz
    have han := HolomorphicProducts.analyticAt_of_holomorphic hf hz
    rw [← han.analyticOrderAt_ne_zero, ho z hz]
    simp
  · intro a ha
    by_contra h
    have he : ∀ᶠ z in 𝓝 a, f z = 0 := by
      filter_upwards [connectedComponentIn_mem_nhds (hf.1.mem_nhds ha)] with z hz
      exact Classical.not_not.mp (fun hh => h ⟨z, hz, hh⟩)
    exact ENat.natCast_ne_top (d a) ((ho a ha).symm.trans (analyticOrderAt_eq_top.mpr he))

/-- Finite divisors use the finite polynomial product in the original coordinate. -/
lemma finite_divisor {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (d : Function.locallyFinsuppWithin Ω ℕ) (hd : d.support.Finite) :
    ∃ f : ℂ → ℂ, Realizes Ω d f := by
  obtain ⟨hf, _, ho, _⟩ := EntireZeros.finite_divisor d hd.toFinset
    (fun z hz => hd.mem_toFinset.mpr hz)
  exact ⟨_, realizes_of_order d _ ⟨hΩ, fun z _ => hf.2 z (mem_univ z)⟩ (fun z _ => ho z)⟩

/-- One slot for every unit of positive multiplicity, including a slot at zero
when the original divisor prescribes one there. -/
abbrev Occurrences {Ω : Set ℂ} (d : Function.locallyFinsuppWithin Ω ℕ) :=
  Σ z : d.support, Fin (d z)

lemma occurrence_count {Ω : Set ℂ} (d : Function.locallyFinsuppWithin Ω ℕ)
    (e : ℕ ≃ Occurrences d) (z : ℂ) :
    (∑' n, (if (e n).1.1 = z then 1 else 0 : ℕ∞)) = (d z : ℕ∞) := by
  classical
  rw [e.tsum_eq (fun i => (if i.1.1 = z then 1 else 0 : ℕ∞))]
  by_cases hd : d z = 0
  · have hne : ∀ i : Occurrences d, i.1.1 ≠ z := by
      intro i hi
      exact i.1.2 (hi ▸ hd)
    simp [hne, hd]
  · let q : ↥{i : Occurrences d | i.1.1 = z} ≃ Fin (d z) :=
      { toFun := fun i => Fin.cast (congrArg d i.2) i.1.2
        invFun := fun k => ⟨⟨⟨z, hd⟩, k⟩, rfl⟩
        left_inv := by
          rintro ⟨⟨⟨w, hw⟩, k⟩, hi⟩
          simp only [Set.mem_ofPred_eq] at hi
          subst w
          rfl
        right_inv := by intro k; rfl }
    calc
      (∑' i : Occurrences d, (if i.1.1 = z then 1 else 0 : ℕ∞)) =
          ∑' i : ↥{i : Occurrences d | i.1.1 = z}, (1 : ℕ∞) := by
        simpa only [Set.indicator, mem_ofPred_eq] using
          (tsum_subtype {i : Occurrences d | i.1.1 = z} (fun _ => (1 : ℕ∞))).symm
      _ = ∑' _ : Fin (d z), (1 : ℕ∞) := q.tsum_eq (fun _ => 1)
      _ = (d z : ℕ∞) := by simp [tsum_fintype]

lemma enumerate_divisor {Ω : Set ℂ} (d : Function.locallyFinsuppWithin Ω ℕ)
    (hinf : d.support.Infinite) : Nonempty (ℕ ≃ Occurrences d) := by
  have hc := (HereditarilyLindelofSpace.isLindelof d.support).countable_of_isDiscrete d.discreteSupport
  have := hc.to_subtype
  have : Infinite d.support := hinf.to_subtype
  have : Infinite (Occurrences d) := Infinite.of_surjective
    (fun i : Occurrences d => i.1)
    (fun z => ⟨⟨z, ⟨0, Nat.pos_of_ne_zero z.2⟩⟩, rfl⟩)
  exact inferInstance

lemma finite_occurrences_on_compact {Ω : Set ℂ} (d : Function.locallyFinsuppWithin Ω ℕ)
    {K : Set ℂ} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    {i : Occurrences d | i.1.1 ∈ K}.Finite := by
  have hbase : {z : d.support | z.1 ∈ K}.Finite := by
    apply ((finite_support_on_compact d hK hKΩ).preimage Subtype.val_injective.injOn).subset
    intro z hz
    exact ⟨hz, z.2⟩
  have h := hbase.sigma (fun z _ => Set.toFinite (univ : Set (Fin (d z))))
  exact h.subset (fun i hi => ⟨hi, mem_univ _⟩)

/-- The punctured open set in the reciprocal coordinate. Zero is excluded even
when the original open set is the whole plane. -/
def transformedDomain (Ω : Set ℂ) (a : ℂ) : Set ℂ :=
  {w | w ≠ 0 ∧ a + w⁻¹ ∈ Ω}

lemma transformedDomain_open {Ω : Set ℂ} (hΩ : IsOpen Ω) (a : ℂ) :
    IsOpen (transformedDomain Ω a) := by
  change IsOpen ({0}ᶜ ∩ (fun w : ℂ => a + w⁻¹) ⁻¹' Ω)
  exact (continuousOn_const.add continuousOn_inv₀).isOpen_inter_preimage
    isClosed_singleton.isOpen_compl hΩ

lemma inversion_mem {Ω : Set ℂ} {a z : ℂ} (hz : z ∈ Ω) (hne : z ≠ a) :
    (z-a)⁻¹ ∈ transformedDomain Ω a := by
  exact ⟨inv_ne_zero (sub_ne_zero.mpr hne), by simpa using hz⟩

lemma transformed_contains_exterior {Ω : Set ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hball : ball a r ⊆ Ω) :
    ∃ R : ℝ, 0 < R ∧ ∀ w : ℂ, R < ‖w‖ → w ∈ transformedDomain Ω a := by
  refine ⟨r⁻¹ + 1, by positivity, fun w hw => ?_⟩
  have hwpos : 0 < ‖w‖ := by have := inv_pos.mpr hr; linarith
  refine ⟨norm_pos_iff.mp hwpos, hball ?_⟩
  rw [mem_ball, dist_eq_norm]
  simp only [add_sub_cancel_left, norm_inv]
  exact inv_lt_of_inv_lt₀ hr (by linarith)

lemma transformed_complement_compact {Ω : Set ℂ} (hΩ : IsOpen Ω)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball a r ⊆ Ω) :
    IsCompact (transformedDomain Ω a)ᶜ := by
  obtain ⟨R, _, hR⟩ := transformed_contains_exterior hr hball
  apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    (transformedDomain_open hΩ a).isClosed_compl
  intro w hw
  simp only [mem_closedBall, dist_zero_right]
  exact le_of_not_gt (fun hh => hw (hR w hh))

/-- Inversion sends an arbitrary enumeration of all multiplicity slots to an
admissible bounded, compactly locally finite sequence for the accepted product. -/
lemma transformed_admissible {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (d : Function.locallyFinsuppWithin Ω ℕ) (e : ℕ ≃ Occurrences d)
    {a : ℂ} {r : ℝ} (hr : 0 < r) (hball : ball a r ⊆ Ω)
    (hfree : ∀ z ∈ ball a r, d z = 0) :
    BoundaryFactorProduct.Admissible (transformedDomain Ω a)
      (fun n => ((e n).1.1 - a)⁻¹) := by
  have hza : ∀ n, (e n).1.1 ≠ a := by
    intro n he
    exact (e n).1.2 (he ▸ hfree a (mem_ball_self hr))
  refine ⟨transformedDomain_open hΩ a, transformed_contains_exterior hr hball,
    transformed_complement_compact hΩ hr hball, ⟨0, by simp [transformedDomain]⟩,
    ?_, (fun n => inversion_mem (d.supportWithinDomain (e n).1.2) (hza n)), ?_⟩
  · apply (isBounded_closedBall (x := (0 : ℂ)) (r := r⁻¹)).subset
    rintro w ⟨n, rfl⟩
    simp only [mem_closedBall, dist_zero_right, norm_inv]
    have hrad : r ≤ ‖(e n).1.1 - a‖ := by
      apply le_of_not_gt
      intro hh
      exact (e n).1.2 (hfree _ (by simpa [mem_ball, dist_eq_norm] using hh))
    exact (inv_le_inv₀ (lt_of_lt_of_le hr hrad) hr).mpr hrad
  · intro K hK hKG
    let S := (fun w : ℂ => a + w⁻¹) '' K
    have hS : IsCompact S := hK.image_of_continuousOn
      (continuousOn_const.add (continuousOn_inv₀.mono (fun w hw => (hKG hw).1)))
    have hSΩ : S ⊆ Ω := by
      rintro z ⟨w, hw, rfl⟩
      exact (hKG hw).2
    apply ((finite_occurrences_on_compact d hS hSΩ).preimage e.injective.injOn).subset
    intro n hn
    change (e n).1.1 ∈ S
    exact ⟨((e n).1.1-a)⁻¹, hn, by simp⟩

lemma inversion_deriv (a z : ℂ) (hz : z ≠ a) :
    HasDerivAt (fun w : ℂ => (w-a)⁻¹) (-((z-a)^2)⁻¹) z := by
  convert ((hasDerivAt_id z).sub_const a).inv (sub_ne_zero.mpr hz) using 1 <;>
    simp [Pi.inv_def, neg_div, one_div]

lemma inversion_deriv_ne_zero (a z : ℂ) (hz : z ≠ a) :
    deriv (fun w : ℂ => (w-a)⁻¹) z ≠ 0 := by
  rw [(inversion_deriv a z hz).deriv]
  exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hz)))

lemma update_eq_near (q : ℂ → ℂ) (a z c : ℂ) (hz : z ≠ a) :
    Function.update q a c =ᶠ[𝓝 z] q := by
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact Function.update_of_ne hw c q

/-- The exterior normalization of the *whole* product gives the punctured
limit one after inversion, not merely limits of its individual factors. -/
lemma pullback_tendsto_one (a : ℂ) (F : ℂ → ℂ)
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ w : ℂ, R < ‖w‖ → ‖F w - 1‖ < ε) :
    Tendsto (fun z : ℂ => F ((z-a)⁻¹)) (𝓝[≠] a) (𝓝 1) := by
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨R, hR, hbound⟩ := hlim ε hε
  refine ⟨(R+1)⁻¹, by positivity, fun z hza hz => ?_⟩
  rw [dist_eq_norm] at hz ⊢
  have hpos : 0 < ‖z-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hza)
  have hlarge : R+1 < ‖z-a‖⁻¹ := (lt_inv_comm₀ hpos (by positivity)).mp hz
  exact hbound _ (by rw [norm_inv]; linarith)

/-- The normalized pullback is holomorphic even at the center, with value one.
Only the ordinary removable-singularity theorem is used at that point. -/
lemma normalized_pullback_holomorphic {Ω : Set ℂ} (hΩ : IsOpen Ω) {a : ℂ}
    (ha : a ∈ Ω) (F : ℂ → ℂ) (hF : HolomorphicOn (transformedDomain Ω a) F)
    (hlim : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ w : ℂ, R < ‖w‖ → ‖F w - 1‖ < ε) :
    HolomorphicOn Ω (Function.update (fun z => F ((z-a)⁻¹)) a 1) := by
  classical
  let q : ℂ → ℂ := fun z => F ((z-a)⁻¹)
  let f : ℂ → ℂ := Function.update q a 1
  have hd : ∀ z ∈ Ω, z ≠ a → DifferentiableAt ℂ f z := by
    intro z hz hza
    exact ((hF.2 _ (inversion_mem hz hza)).comp z
      (inversion_deriv a z hza).differentiableAt).congr_of_eventuallyEq
      (update_eq_near q a z 1 hza)
  refine ⟨hΩ, fun z hz => ?_⟩
  by_cases hza : z = a
  · subst z
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ?_
      (continuousAt_update_same.mpr (pullback_tendsto_one a F hlim)) |>.differentiableAt
    filter_upwards [nhdsWithin_le_nhds (hΩ.mem_nhds ha), self_mem_nhdsWithin] with z hz hza
    exact hd z hz hza
  · exact hd z hz hza

lemma normalized_pullback_order (a z : ℂ) (F : ℂ → ℂ) (hz : z ≠ a) :
    analyticOrderAt (Function.update (fun w => F ((w-a)⁻¹)) a 1) z =
      analyticOrderAt F ((z-a)⁻¹) := by
  rw [analyticOrderAt_congr (update_eq_near _ a z 1 hz)]
  exact analyticOrderAt_comp_of_deriv_ne_zero
    ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr hz))
    (inversion_deriv_ne_zero a z hz)

/-- The infinite construction is normalized at a genuine divisor-free point.
The admissibility and extension are proved for the whole open set, so this
also handles finite and empty divisors on individual disconnected components. -/
lemma infinite_divisor_normalized {Ω : Set ℂ} (hΩ : IsOpen Ω)
    (d : Function.locallyFinsuppWithin Ω ℕ) (hd : d.support.Infinite) :
    ∃ (a : ℂ) (f : ℂ → ℂ), a ∈ Ω ∧ d a = 0 ∧ f a = 1 ∧ Realizes Ω d f := by
  classical
  have hne : Ω.Nonempty := hd.nonempty.mono d.supportWithinDomain
  obtain ⟨a, r, hr, hball, hfree⟩ := exists_divisor_free_disk hΩ hne d
  have ha : a ∈ Ω := hball (mem_ball_self hr)
  have hda : d a = 0 := hfree a (mem_ball_self hr)
  let e : ℕ ≃ Occurrences d := Classical.choice (enumerate_divisor d hd)
  let G := transformedDomain Ω a
  let z : ℕ → ℂ := fun n => ((e n).1.1-a)⁻¹
  have hadm : BoundaryFactorProduct.Admissible G z :=
    transformed_admissible hΩ d e hr hball hfree
  obtain ⟨b, hb⟩ := BoundaryFactorProduct.exists_nearest G z hadm
  let F := BoundaryFactorProduct.product z b
  have hF : HolomorphicOn G F := (BoundaryFactorProduct.product_holomorphic G z b hadm hb).2
  have hlim : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
      ∀ w : ℂ, R < ‖w‖ → ‖F w - 1‖ < ε := by
    intro ε hε
    obtain ⟨R, hR, hbound⟩ := BoundaryFactorProduct.product_limit_at_infinity G z b hadm hb ε hε
    exact ⟨R, hR, fun w hw => (hbound w hw).2⟩
  let f : ℂ → ℂ := Function.update (fun w => F ((w-a)⁻¹)) a 1
  have hf : HolomorphicOn Ω f := normalized_pullback_holomorphic hΩ ha F hF hlim
  refine ⟨a, f, ha, hda, by simp [f], realizes_of_order d f hf ?_⟩
  intro w hw
  by_cases hwa : w = a
  · subst w
    rw [hda]
    exact (HolomorphicProducts.analyticAt_of_holomorphic hf ha).analyticOrderAt_eq_zero.mpr
      (by simp [f])
  · change analyticOrderAt (Function.update (fun w => F ((w-a)⁻¹)) a 1) w = _
    rw [normalized_pullback_order a w F hwa]
    rw [(BoundaryFactorProduct.product_multiplicity G z b hadm hb _ (inversion_mem hw hwa)).2.1]
    simpa only [z, inv_inj, sub_left_inj] using occurrence_count d e w

/-- D12.16.05: every locally finite effective divisor on any open plane set
is the exact zero divisor of a holomorphic function nontrivial on each component. -/
theorem open_set_prescribed_zeros :
    Specs.D12Complex.Ch16.OpenSetZeros.open_set_prescribed_zeros_type := by
  classical
  intro Ω hΩ d
  by_cases hd : d.support.Finite
  · exact finite_divisor hΩ d hd
  · obtain ⟨a, f, _, _, _, hf⟩ := infinite_divisor_normalized hΩ d (Set.not_finite.mp hd)
    exact ⟨f, hf⟩

end D12Complex.OpenSetZeros
