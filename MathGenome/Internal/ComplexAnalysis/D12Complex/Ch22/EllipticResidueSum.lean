import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.EllipticResidueSum
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.TorusSurface
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.ResidueCycle
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.WeakGoursat
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.SetTheory.Cardinal.Continuum
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set Filter
open scoped Topology BigOperators Pointwise

namespace D12Complex.EllipticResidueSum
open TorusSurface
open private periodBasis periodBasis_zero periodBasis_one lattice_eq_span_basis from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.LatticeGeometry

/-- Signed orders are unchanged by a lattice translation. -/
lemma order_translation {ω₁ ω₂ : ℂ} {f : ℂ → ℂ} (hf : Periodic ω₁ ω₂ f)
    (a l : ℂ) (hl : l ∈ lattice ω₁ ω₂) :
    meromorphicOrderAt f (a + l) = meromorphicOrderAt f a := by
  rw [← meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt]
  congr 1
  funext z
  exact hf z l hl

lemma pole_translation {ω₁ ω₂ : ℂ} {f : ℂ → ℂ} (hf : Periodic ω₁ ω₂ f)
    (a l : ℂ) (hl : l ∈ lattice ω₁ ω₂) :
    a + l ∈ poleSet f ↔ a ∈ poleSet f := by
  simp only [poleSet, mem_ofPred_eq, order_translation hf a l hl]

/-- Translation invariance holds directly for the defining circle integrals. -/
theorem residue_translation : Specs.D12Complex.Ch22.EllipticResidueSum.residue_translation_type := by
  intro ω₁ ω₂ f hf a l hl
  unfold Residue.residue
  congr 1
  funext r
  congr 1
  unfold circleIntegral
  congr 1
  funext t
  simp only [circleMap, deriv_circleMap]
  have heq : a + l + (r : ℂ) * Complex.exp (↑t * Complex.I) =
      (a + (r : ℂ) * Complex.exp (↑t * Complex.I)) + l := by ring
  rw [heq, hf _ l hl]

theorem residue_representative_independent :
    Specs.D12Complex.Ch22.EllipticResidueSum.residue_representative_independent_type := by
  intro ω₁ ω₂ f hf a b hab
  have hl := (projection_eq_iff a b).mp hab
  simpa using residue_translation ω₁ ω₂ f hf b (a - b) hl

/-- Compact sets contain finitely many genuine poles, also for the zero function. -/
lemma finite_poles_on_compact {f : ℂ → ℂ} (hm : ∀ z, MeromorphicAt f z)
    {K : Set ℂ} (hK : IsCompact K) : (K ∩ poleSet f).Finite := by
  have hd := (MeromorphicOn.divisor f K).finiteSupport hK
  apply hd.subset
  intro z hz
  rw [Function.mem_support, MeromorphicOn.divisor_apply (fun z _ => hm z) hz.1]
  intro hzero
  have hh := WithTop.untop₀_eq_zero.mp hzero
  rcases hh with hh | hh
  · exact (ne_of_lt hz.2) hh
  · have hp : meromorphicOrderAt f z < 0 := hz.2
    rw [hh] at hp
    exact (not_lt_of_ge (by simp : (0 : WithTop ℤ) ≤ ⊤)) hp

/-- Finite pole classes follow by reducing to a bounded fundamental domain. -/
theorem finite_poleClasses : Specs.D12Complex.Ch22.EllipticResidueSum.finite_poleClasses_type := by
  intro ω₁ ω₂ h₁ h₂ f hm hf
  let b := periodBasis h₁ h₂
  let K := Metric.closedBall (0 : ℂ) (∑ i, ‖b i‖)
  have hfin := (finite_poles_on_compact hm (isCompact_closedBall (0 : ℂ)
    (∑ i, ‖b i‖))).image (projection ω₁ ω₂)
  apply hfin.subset
  rintro x ⟨z, hz, rfl⟩
  let w := ZSpan.fract b z
  have hl : z - w ∈ lattice ω₁ ω₂ := by
    change z - w ∈ Ch22.LatticeGeometry.lattice ω₁ ω₂
    rw [lattice_eq_span_basis h₁ h₂]
    simpa [w, ZSpan.fract, b] using (ZSpan.floor b z).property
  have hw : w ∈ poleSet f := by
    have heq : w + (z - w) = z := by ring
    exact (pole_translation hf w (z - w) hl).mp (heq.symm ▸ hz)
  refine ⟨w, ⟨?_, hw⟩, ?_⟩
  · simpa only [Metric.mem_closedBall, dist_zero_right] using ZSpan.norm_fract_le b z
  · exact (projection_eq_iff w z).mpr (by simpa using neg_mem hl)

theorem exists_complete_representatives :
    Specs.D12Complex.Ch22.EllipticResidueSum.exists_complete_representatives_type := by
  classical
  intro ω₁ ω₂ h₁ h₂ f hm hf
  have hfin := finite_poleClasses ω₁ ω₂ h₁ h₂ f hm hf
  obtain ⟨s, hs, hinj, himg⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (poleSet f) hfin.toFinset (by
      intro x hx
      exact (hfin.mem_toFinset.mp hx))
  refine ⟨s, hs, hinj, ?_⟩
  simpa only [← Finset.coe_image, himg, hfin.coe_toFinset]

/-- The empty pole set has the empty complete representative set. -/
lemma empty_representatives {ω₁ ω₂ : ℂ} {f : ℂ → ℂ} (hf : poleSet f = ∅) :
    CompletePoleRepresentatives ω₁ ω₂ f ∅ := by
  simp [CompletePoleRepresentatives, poleClasses, hf]

/-- The zero-pole case of the residue conclusion, without any nonconstancy premise. -/
lemma residue_sum_of_no_poles {ω₁ ω₂ : ℂ} {f : ℂ → ℂ} {s : Finset ℂ}
    (hf : poleSet f = ∅) (hs : CompletePoleRepresentatives ω₁ ω₂ f s) :
    ∑ a ∈ s, Residue.residue f a = 0 := by
  have he : s = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have := hs.1 hz
    simpa [hf] using this
  simp [he]

/-- A local factor with exponent -1 gives its nonzero numerator as residue. -/
lemma residue_simple_pole {f : ℂ → ℂ} {a : ℂ} (hm : MeromorphicAt f a)
    (ho : meromorphicOrderAt f a = (-1 : ℤ)) : Residue.residue f a ≠ 0 := by
  obtain ⟨g, hg, hga, heq⟩ := (meromorphicOrderAt_eq_int_iff hm).mp ho
  obtain ⟨r, hr, hgr⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨s, hs, hfs⟩ := Metric.mem_nhdsWithin_iff.mp heq
  have hev : ∀ᶠ ρ in 𝓝[>] (0 : ℝ),
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * circleIntegral f a ρ = g a := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hr),
      nhdsWithin_le_nhds (Iio_mem_nhds hs)] with ρ hρ hρr hρs
    have hc : circleIntegral f a ρ =
        circleIntegral (fun z => (z - a)⁻¹ • g z) a ρ := by
      apply circleIntegral.integral_congr hρ.le
      intro z hz
      have hza : z ≠ a := by
        intro h
        subst z
        have ht : (0 : ℝ) = ρ := by simpa [Metric.mem_sphere] using hz
        exact hρ.ne' ht.symm
      have he := hfs ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hz).trans_lt hρs),
        by simpa using hza⟩
      change f z = (z - a) ^ (-1 : ℤ) • g z at he
      simpa only [zpow_neg_one] using he
    rw [hc]
    exact Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      countable_empty (Metric.mem_ball_self hρ)
      ((hgr.mono (Metric.closedBall_subset_ball hρr)).continuousOn)
      (fun z hz => (hgr z (Metric.ball_subset_ball hρr.le hz.1)).differentiableAt)
  have hres : Residue.residue f a = g a := Tendsto.limUnder_eq
    (tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm))
  rw [hres]
  exact hga

/-- Residues depend on the punctured germ, with no regularity assumption. -/
lemma residue_congr_germ {f g : ℂ → ℂ} {a : ℂ} (hfg : f =ᶠ[𝓝[≠] a] g) :
    Residue.residue f a = Residue.residue g a := by
  obtain ⟨r, hr, heq⟩ := Metric.mem_nhdsWithin_iff.mp hfg
  unfold Residue.residue Filter.limUnder
  congr 1
  apply Filter.map_congr
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds hr)] with ρ hρ hρr
  congr 1
  apply circleIntegral.integral_congr hρ.le
  intro z hz
  have hza : z ≠ a := by
    intro h
    subst z
    have ht : (0 : ℝ) = ρ := by simpa [Metric.mem_sphere] using hz
    exact hρ.ne' ht.symm
  exact heq ⟨Metric.mem_ball.mpr ((Metric.mem_sphere.mp hz).trans_lt hρr),
    by simpa using hza⟩

lemma poleSet_subset_divisor_support {f : ℂ → ℂ} (hm : ∀ z, MeromorphicAt f z) :
    poleSet f ⊆ (MeromorphicOn.divisor f univ).support := by
  intro z hz
  rw [Function.mem_support, MeromorphicOn.divisor_apply (fun z _ => hm z) (mem_univ z)]
  intro hzero
  rcases WithTop.untop₀_eq_zero.mp hzero with hzero | htop
  · exact (ne_of_lt hz) hzero
  · have hp : meromorphicOrderAt f z < 0 := hz
    simpa [htop] using hp

lemma poleSet_closed_discrete {f : ℂ → ℂ} (hm : ∀ z, MeromorphicAt f z) :
    IsClosed (poleSet f) ∧ IsDiscrete (poleSet f) := by
  have hd := (MeromorphicOn.divisor f univ).discreteSupport
  have hc := (MeromorphicOn.divisor f univ).closedSupport isClosed_univ
  exact ⟨isClosed_of_subset_discrete_closed (poleSet_subset_divisor_support hm) hd hc,
    hd.mono (poleSet_subset_divisor_support hm)⟩

/-- Correct the irrelevant isolated assigned values. The punctured germs,
orders, residues and lattice periodicity are all preserved. -/
lemma normalized_representative {ω₁ ω₂ : ℂ} {f : ℂ → ℂ}
    (hm : ∀ z, MeromorphicAt f z) (hf : Periodic ω₁ ω₂ f) :
    ∃ g : ℂ → ℂ, Periodic ω₁ ω₂ g ∧ HolomorphicOn (univ \ poleSet f) g ∧
      (∀ z, MeromorphicAt g z) ∧
      (∀ z, meromorphicOrderAt g z = meromorphicOrderAt f z) ∧
      (∀ z, Residue.residue g z = Residue.residue f z) := by
  let g := toMeromorphicNFOn f univ
  have hmOn : MeromorphicOn f univ := fun z _ => hm z
  have hnf (z : ℂ) : MeromorphicNFAt g z :=
    meromorphicNFOn_toMeromorphicNFOn f univ (mem_univ z)
  have hgf (z : ℂ) : g =ᶠ[𝓝[≠] z] f :=
    hmOn.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z)
  have horder (z : ℂ) : meromorphicOrderAt g z = meromorphicOrderAt f z :=
    meromorphicOrderAt_congr (hgf z)
  have hper : Periodic ω₁ ω₂ g := by
    intro z l hl
    have hshift : Tendsto (fun w : ℂ => w + l) (𝓝[≠] z) (𝓝[≠] (z + l)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (continuous_id.add_const l).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w hw
        simpa only [mem_compl_iff, mem_singleton_iff, add_left_inj] using hw
    have heq : (g ∘ (fun w => w + l)) =ᶠ[𝓝[≠] z] g := by
      filter_upwards [(hgf (z + l)).comp_tendsto hshift, hgf z] with w hw hw'
      exact hw.trans ((hf w l hl).trans hw'.symm)
    have hnfShift : MeromorphicNFAt (g ∘ (fun w => w + l)) z :=
      meromorphicNFAt_comp_add_const_iff_meromorphicNFAt.mpr (hnf (z + l))
    exact ((hnfShift.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds (hnf z)).mp heq).eq_of_nhds
  refine ⟨g, hper, ⟨isOpen_univ.sdiff (poleSet_closed_discrete hm).1, ?_⟩,
    (fun z => (hnf z).meromorphicAt), horder, fun z => residue_congr_germ (hgf z)⟩
  intro z hz
  apply ((hnf z).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_).differentiableAt
  rw [horder z]
  exact le_of_not_gt hz.2

/-- Replacing a complete representative set leaves its residue sum unchanged. -/
lemma sum_representatives_eq {ω₁ ω₂ : ℂ} {f : ℂ → ℂ}
    (hf : Periodic ω₁ ω₂ f) {s t : Finset ℂ}
    (hs : CompletePoleRepresentatives ω₁ ω₂ f s)
    (ht : CompletePoleRepresentatives ω₁ ω₂ f t) :
    ∑ a ∈ s, Residue.residue f a = ∑ b ∈ t, Residue.residue f b := by
  classical
  have hex : ∀ a ∈ s, ∃ b ∈ t, projection ω₁ ω₂ a = projection ω₁ ω₂ b := by
    intro a ha
    have hp : projection ω₁ ω₂ a ∈ poleClasses ω₁ ω₂ f := ⟨a, hs.1 ha, rfl⟩
    rw [← ht.2.2] at hp
    obtain ⟨b, hb, hba⟩ := hp
    exact ⟨b, hb, hba.symm⟩
  choose g hgm hge using hex
  apply Finset.sum_bij g hgm
  · intro a ha b hb hab
    apply hs.2.1 ha hb
    rw [hge a ha, hge b hb, hab]
  · intro b hb
    have hp : projection ω₁ ω₂ b ∈ poleClasses ω₁ ω₂ f := ⟨b, ht.1 hb, rfl⟩
    rw [← hs.2.2] at hp
    obtain ⟨a, ha, hab⟩ := hp
    refine ⟨a, ha, ht.2.1 (hgm a ha) hb ?_⟩
    exact (hge a ha).symm.trans hab
  · intro a ha
    exact residue_representative_independent ω₁ ω₂ f hf a (g a ha) (hge a ha)

/-- The analytic part of the proof, for a fundamental contour supplied by geometry.
The hypotheses describe only its index, boundary avoidance and cancellation of
periodic integrals; they contain no residue-sum conclusion. -/
lemma residue_sum_from_periodic_cycle {ω₁ ω₂ : ℂ} {f : ℂ → ℂ}
    (hm : ∀ z, MeromorphicAt f z) (hf : Periodic ω₁ ω₂ f)
    (s : Finset ℂ) (hs : CompletePoleRepresentatives ω₁ ω₂ f s)
    (Γ : IntegralCycle) (havoid : Disjoint Γ.trace (poleSet f))
    (hindex : ∀ z ∈ poleSet f, Γ.index z = if z ∈ s then 1 else 0)
    (hcancel : ∀ g : ℂ → ℂ, Periodic ω₁ ω₂ g →
      ContinuousOn g Γ.trace → Γ.integral g = 0) :
    ∑ a ∈ s, Residue.residue f a = 0 := by
  classical
  obtain ⟨g, hgper, hghol, _, _, hgres⟩ := normalized_representative hm hf
  have hclosed := (poleSet_closed_discrete hm).1
  have hdisc := (poleSet_closed_discrete hm).2
  have htrace : Γ.trace ⊆ univ \ poleSet f := by
    intro z hz
    exact ⟨mem_univ z, fun hp => (Set.disjoint_left.mp havoid hz hp)⟩
  obtain ⟨t, ht, hInt⟩ := ResidueCycle.residue_theorem univ (poleSet f) g Γ
    isOpen_univ (subset_univ _) (hclosed.preimage continuous_subtype_val) hdisc
    hghol (subset_univ _) havoid (by simp)
  have hts : t = s := by
    ext z
    rw [ht]
    by_cases hp : z ∈ poleSet f
    · rw [hindex z hp]
      by_cases hz : z ∈ s <;> simp [hp, hz]
    · have hz : z ∉ s := fun hz => hp (hs.1 hz)
      simp [hp, hz]
  have hzero : Γ.integral g = 0 :=
    hcancel g hgper (fun z hz => (hghol.2 z (htrace hz)).continuousAt.continuousWithinAt)
  rw [hzero, hts] at hInt
  have hsum : ∑ a ∈ s, Γ.index a * Residue.residue g a =
      ∑ a ∈ s, Residue.residue f a := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hindex a (hs.1 ha), ite_eq_left ha, one_mul, hgres a]
  rw [hsum] at hInt
  exact (mul_eq_zero.mp hInt.symm).resolve_left (mul_ne_zero
    (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero)

/-- Final algebraic deduction once the residue sum theorem is available. -/
lemma no_single_simple_pole_of_residue_sum
    (hSum : Specs.D12Complex.Ch22.EllipticResidueSum.residue_sum_type) :
    Specs.D12Complex.Ch22.EllipticResidueSum.no_single_simple_pole_type := by
  classical
  intro ω₁ ω₂ h₁ h₂ f hm hf h
  obtain ⟨a, ha, hclasses⟩ := h
  have hap : a ∈ poleSet f := by
    change meromorphicOrderAt f a < 0
    rw [ha]
    exact WithTop.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by decide)
  have hs : CompletePoleRepresentatives ω₁ ω₂ f {a} := by
    refine ⟨by simpa, ?_, ?_⟩
    · simpa only [Finset.coe_singleton] using
        (subsingleton_singleton : ({a} : Set ℂ).Subsingleton).injOn (projection ω₁ ω₂)
    · ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hz' : z = a := by simpa using hz
        exact ⟨z, hz' ▸ hap, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨a, by simp, (hclasses z hz).symm⟩
  have hz := hSum ω₁ ω₂ h₁ h₂ f hm hf {a} hs
  have hr := residue_simple_pole (hm a) ha
  exact hr (by simpa using hz)

lemma parallelogram_basis (b : Module.Basis (Fin 2) ℝ ℂ) (a : ℂ) :
    Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a (b 0) (b 1) =
      (Homeomorph.addLeft a) '' parallelepiped b := by
  rw [parallelepiped_eq_convexHull]
  have he : (∑ i : Fin 2, ({(0 : ℂ), b i} : Set ℂ)) = {0, b 0, b 0 + b 1, b 1} := by
    simp only [Fin.sum_univ_two]
    ext z
    simp only [Set.mem_add, Set.mem_insert_iff, Set.mem_singleton_iff]
    aesop
  rw [he]
  change _ = (AffineEquiv.constVAdd ℝ ℂ a).toAffineMap '' _
  rw [AffineMap.image_convexHull]
  simp [Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value, add_assoc]

lemma parallelogram_coordinates (b : Module.Basis (Fin 2) ℝ ℂ) (a : ℂ) :
    Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a (b 0) (b 1) =
      (fun z => b.equivFunL (z - a)) ⁻¹' Set.pi univ (fun _ => Icc (0 : ℝ) 1) := by
  rw [parallelogram_basis, parallelepiped_basis_eq]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change ∀ i, i ∈ univ → b.repr (a + x - a) i ∈ Icc 0 1
    intro i _
    simpa only [add_sub_cancel_left] using hx i
  · intro hz
    refine ⟨z - a, ?_, by simp⟩
    exact fun i => hz i (mem_univ i)

lemma parallelogram_interior (b : Module.Basis (Fin 2) ℝ ℂ) (a z : ℂ) :
    z ∈ interior (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a (b 0) (b 1)) ↔
      ∀ i, 0 < b.repr (z - a) i ∧ b.repr (z - a) i < 1 := by
  rw [parallelogram_coordinates]
  let e := (Homeomorph.addRight (-a)).trans b.equivFunL.toHomeomorph
  have he : (fun z => b.equivFunL (z - a)) = e := by ext z i; simp [e, sub_eq_add_neg]
  rw [he, ← e.preimage_interior, interior_pi_set (finite_univ), interior_Icc]
  simp [Set.mem_pi, e, sub_eq_add_neg]

lemma parallelogram_closed (b : Module.Basis (Fin 2) ℝ ℂ) (a : ℂ) :
    IsClosed (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a (b 0) (b 1)) := by
  rw [parallelogram_coordinates]
  exact (isClosed_set_pi (fun _ _ => isClosed_Icc)).preimage
    (b.equivFunL.continuous.comp (continuous_id.sub continuous_const))

/-- Avoid both endpoint levels of each coordinate. -/
lemma exists_avoiding_cell (b : Module.Basis (Fin 2) ℝ ℂ)
    (A : Set ℂ) (hA : A.Countable) :
    ∃ a : ℂ, Disjoint (frontier
      (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a (b 0) (b 1))) A := by
  classical
  have hex (i : Fin 2) : ∃ c : ℝ, ∀ z ∈ A,
      b.repr z i ≠ c ∧ b.repr z i ≠ c + 1 := by
    let S := (fun z => b.repr z i) '' A ∪ (fun z => b.repr z i - 1) '' A
    have hS : S.Countable := (hA.image _).union (hA.image _)
    have hn : S ≠ univ := fun h => Set.not_countable_univ (h ▸ hS)
    obtain ⟨c, hc⟩ := Set.nonempty_compl.mpr hn
    refine ⟨c, fun z hz => ⟨?_, ?_⟩⟩
    · intro heq
      exact hc (Or.inl ⟨z, hz, heq⟩)
    · intro heq
      exact hc (Or.inr ⟨z, hz, by linarith⟩)
  choose c hc using hex
  let a := b.equivFunL.symm c
  have ha (i : Fin 2) : b.repr a i = c i := by
    change b.equivFunL (b.equivFunL.symm c) i = c i
    exact congrArg (fun d : Fin 2 → ℝ => d i) (b.equivFunL.apply_symm_apply c)
  refine ⟨a, Set.disjoint_left.mpr ?_⟩
  intro z hz hzA
  have hzP : z ∈ Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a (b 0) (b 1) :=
    (parallelogram_closed b a).closure_eq ▸ frontier_subset_closure hz
  have hzC : ∀ i, 0 ≤ b.repr (z - a) i ∧ b.repr (z - a) i ≤ 1 := by
    rw [parallelogram_coordinates] at hzP
    exact fun i => hzP i (mem_univ i)
  have hzI : z ∈ interior
      (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a (b 0) (b 1)) := by
    rw [parallelogram_interior]
    intro i
    have hzi := hzC i
    have hne := hc i z hzA
    simp only [map_sub, Finsupp.sub_apply, ha] at hzi ⊢
    constructor
    · exact lt_of_le_of_ne hzi.1 (by intro h; exact hne.1 (by linarith))
    · exact lt_of_le_of_ne hzi.2 (by intro h; exact hne.2 (by linarith))
  exact hz.2 hzI

open D12Complex.TorusSurface
lemma representatives_in_avoiding_cell {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (A : Set ℂ) (a : ℂ)
    (hper : ∀ z l : ℂ, l ∈ lattice ω₁ ω₂ → (z + l ∈ A ↔ z ∈ A))
    (havoid : Disjoint (frontier
      (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂)) A) :
    ∀ z ∈ A, ∃! w : ℂ,
      w ∈ interior (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂) ∧
      projection ω₁ ω₂ w = projection ω₁ ω₂ z := by
  let b := periodBasis h₁ h₂
  have hb₀ : b 0 = ω₁ := periodBasis_zero h₁ h₂
  have hb₁ : b 1 = ω₂ := periodBasis_one h₁ h₂
  have hlat : lattice ω₁ ω₂ = Submodule.span ℤ (Set.range b) := lattice_eq_span_basis h₁ h₂
  intro z hz
  let w := a + ZSpan.fract b (z - a)
  have hdiff : w - z ∈ lattice ω₁ ω₂ := by
    rw [hlat]
    convert neg_mem (ZSpan.floor b (z - a)).property using 1
    dsimp [w, ZSpan.fract]
    abel
  have hwA : w ∈ A := by
    have := (hper z (w - z) hdiff).mpr hz
    simpa using this
  have hwP : w ∈ Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂ := by
    rw [← hb₀, ← hb₁, parallelogram_coordinates]
    intro i _
    change b.repr (w - a) i ∈ Icc 0 1
    have heq : w - a = ZSpan.fract b (z - a) := by dsimp [w]; abel
    rw [heq, ZSpan.repr_fract_apply]
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hwI : w ∈ interior (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂) := by
    by_contra hn
    exact Set.disjoint_left.mp havoid ((mem_frontier_iff_notMem_interior hwP).mpr hn) hwA
  refine ⟨w, ⟨hwI, (D12Complex.TorusSurface.projection_eq_iff w z).mpr hdiff⟩, ?_⟩
  intro y hy
  have hyw : y - w ∈ lattice ω₁ ω₂ :=
    (D12Complex.TorusSurface.projection_eq_iff y w).mp (hy.2.trans
      ((D12Complex.TorusSurface.projection_eq_iff w z).mpr hdiff).symm)
  have hfrac : ZSpan.fract b (y - a) = ZSpan.fract b (w - a) := by
    apply (ZSpan.fract_eq_fract b _ _).mpr
    rw [← hlat]
    convert neg_mem hyw using 1; abel
  have hmem {x : ℂ}
      (hx : x ∈ interior (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂)) :
      x - a ∈ ZSpan.fundamentalDomain b := by
    rw [← hb₀, ← hb₁, parallelogram_interior] at hx
    exact fun i => ⟨(hx i).1.le, (hx i).2⟩
  rw [ZSpan.fract_eq_self.mpr (hmem hy.1), ZSpan.fract_eq_self.mpr (hmem hwI)] at hfrac
  exact sub_left_injective hfrac

/-- A translate with no poles on its boundary, with one interior point per pole class. -/
theorem allowed_parallelogram :
    Specs.D12Complex.Ch22.EllipticResidueSum.allowed_parallelogram_type := by
  intro ω₁ ω₂ h₁ h₂ f hm hf
  let b := periodBasis h₁ h₂
  have hc := poleSet_closed_discrete hm
  have hcount : (poleSet f).Countable := hc.1.isLindelof.countable_of_isDiscrete hc.2
  obtain ⟨a, ha⟩ := exists_avoiding_cell b (poleSet f) hcount
  have hb₀ : b 0 = ω₁ := periodBasis_zero h₁ h₂
  have hb₁ : b 1 = ω₂ := periodBasis_one h₁ h₂
  rw [hb₀, hb₁] at ha
  exact ⟨a, ha, representatives_in_avoiding_cell h₁ h₂ (poleSet f) a
    (fun z l hl => pole_translation hf z l hl) ha⟩

open WeakGoursat

lemma segment_integral_formula (a b : ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (segmentPath a b).trace) :
    (segmentPath a b).integral f = ∫ t in (0 : ℝ)..1,
      f (a + t • (b - a)) * (b - a) := by
  rw [PiecewiseC1Path.integral_congr_representative (segmentPath a b)
    (segmentPath a b) f hf (fun _ _ => rfl)]
  simp_rw [(segmentPath_hasDerivAt a b _).deriv]
  rfl

lemma segment_trace_reverse (a b : ℂ) :
    (segmentPath b a).trace = (segmentPath a b).trace := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    change t ∈ Icc (0 : ℝ) 1 at ht
    refine ⟨1 - t, (show 1 - t ∈ Icc (0 : ℝ) 1 from ⟨by linarith [ht.2], by linarith [ht.1]⟩), ?_⟩
    change a + (1 - t) • (b - a) = b + t • (a - b)
    simp only [sub_smul, one_smul, smul_sub]
    abel
  · rintro ⟨t, ht, rfl⟩
    change t ∈ Icc (0 : ℝ) 1 at ht
    refine ⟨1 - t, (show 1 - t ∈ Icc (0 : ℝ) 1 from ⟨by linarith [ht.2], by linarith [ht.1]⟩), ?_⟩
    change b + (1 - t) • (a - b) = a + t • (b - a)
    simp only [sub_smul, one_smul, smul_sub]
    abel

lemma segment_reverse_integral (a b : ℂ) (f : ℂ → ℂ)
    (hf : ContinuousOn f (segmentPath a b).trace) :
    (segmentPath b a).integral f = -(segmentPath a b).integral f := by
  apply PiecewiseC1Path.integral_reversal (segmentPath a b) (segmentPath b a) f rfl rfl
  · intro t ht
    change b + t • (a - b) = a + (0 + 1 - t) • (b - a)
    simp only [zero_add, sub_smul, one_smul, smul_sub]
    abel
  · exact hf

lemma segment_translate_integral {ω₁ ω₂ : ℂ} {f : ℂ → ℂ}
    (hf : Periodic ω₁ ω₂ f) (a b l : ℂ) (hl : l ∈ lattice ω₁ ω₂)
    (hab : ContinuousOn f (segmentPath a b).trace)
    (hshift : ContinuousOn f (segmentPath (a + l) (b + l)).trace) :
    (segmentPath (a + l) (b + l)).integral f = (segmentPath a b).integral f := by
  rw [segment_integral_formula _ _ _ hshift, segment_integral_formula _ _ _ hab]
  apply intervalIntegral.integral_congr
  intro t _
  have heq : a + l + t • (b - a) = (a + t • (b - a)) + l := by abel
  simp only [add_sub_add_right_eq_sub, heq, hf _ l hl]

lemma parallelogram_periodic_integral {ω₁ ω₂ : ℂ} {f : ℂ → ℂ}
    (hf : Periodic ω₁ ω₂ f) (a : ℂ)
    (hbottom : ContinuousOn f (segmentPath a (a + ω₁)).trace)
    (hright : ContinuousOn f (segmentPath (a + ω₁) (a + ω₁ + ω₂)).trace)
    (htop : ContinuousOn f (segmentPath (a + ω₁ + ω₂) (a + ω₂)).trace)
    (hleft : ContinuousOn f (segmentPath (a + ω₂) a).trace) :
    parallelogramBoundaryIntegral a ω₁ ω₂ f = 0 := by
  have hω₁ : ω₁ ∈ lattice ω₁ ω₂ := Submodule.subset_span (by simp)
  have hω₂ : ω₂ ∈ lattice ω₁ ω₂ := Submodule.subset_span (by simp)
  have hleft' : ContinuousOn f (segmentPath a (a + ω₂)).trace := by
    rwa [segment_trace_reverse] at hleft
  have htop' : ContinuousOn f (segmentPath (a + ω₂) (a + ω₁ + ω₂)).trace := by
    rwa [segment_trace_reverse] at htop
  have heq : a + ω₂ + ω₁ = a + ω₁ + ω₂ := by abel
  have hright' := segment_translate_integral hf a (a + ω₂) ω₁ hω₁ hleft'
    (by simpa only [heq] using hright)
  rw [heq] at hright'
  have htop'' := segment_translate_integral hf a (a + ω₁) ω₂ hω₂ hbottom htop'
  have htoprev := segment_reverse_integral (a + ω₂) (a + ω₁ + ω₂) f htop'
  have hleftrev := segment_reverse_integral a (a + ω₂) f hleft'
  unfold parallelogramBoundaryIntegral
  rw [htoprev, hleftrev, hright', htop'']
  ring

lemma segment_reciprocal_log (a b c k : ℂ) (hk : k ≠ 0)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, (a + t • (b - a) - c) * k ∈ Complex.slitPlane) :
    (segmentPath a b).integral (fun z => 1 / (z - c)) =
      Complex.log ((b - c) * k) - Complex.log ((a - c) * k) := by
  have hs' : ∀ z ∈ segment ℝ a b, (z - c) * k ∈ Complex.slitPlane := by
    rw [segment_eq_image']
    rintro z ⟨t, ht, rfl⟩
    exact hs t ht
  have hne : ∀ z ∈ segment ℝ a b, z - c ≠ 0 := by
    intro z hz h
    have := Complex.slitPlane_ne_zero (hs' z hz)
    exact this (by rw [h, zero_mul])
  apply segment_integral_eq_sub (convex_segment a b) (f := fun z => 1 / (z - c))
    (F := fun z => Complex.log ((z - c) * k)) ?_ ?_ (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
  · intro z hz
    apply HasDerivAt.hasDerivWithinAt
    convert (Complex.hasDerivAt_log (hs' z hz)).comp z
      (((hasDerivAt_id z).sub_const c).mul_const k) using 1
    · funext w
      simp only [Function.comp_apply, id_eq]
    · field_simp [hk, hne z hz]
  · exact continuousOn_const.div (continuousOn_id.sub continuousOn_const) hne

lemma real_affine_mem_slit {τ : ℂ} (hτ : 0 < τ.im) (p q : ℝ)
    (hpq : 0 < p ∨ q ≠ 0) : (p : ℂ) + (q : ℂ) * τ ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hq : q = 0
  · left
    rcases hpq with hp | hq'
    · simpa [hq] using hp
    · exact (hq' hq).elim
  · right
    simpa using mul_ne_zero hq (ne_of_gt hτ)

lemma log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_sub_pi_of_im_pos hz]

lemma log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, Complex.arg_neg_eq_arg_add_pi_of_im_neg hz]

lemma parallelogram_reciprocal_integral (a u v : ℂ) (hu : u ≠ 0)
    (hv : 0 < (v / u).im) (x y : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hy : y ∈ Ioo (0 : ℝ) 1) :
    parallelogramBoundaryIntegral a u v (fun z => 1 / (z - (a + x • u + y • v))) =
      2 * Real.pi * Complex.I := by
  let c := a + x • u + y • v
  let τ := v / u
  have hbottom (t : ℝ) : (a + t • (a + u - a) - c) * u⁻¹ =
      ((t - x : ℝ) : ℂ) + (-y : ℂ) * τ := by
    dsimp [c, τ]
    simp only [Complex.real_smul, Complex.ofReal_sub]
    field_simp
    ring
  have hright (t : ℝ) : (a + u + t • (a + u + v - (a + u)) - c) * u⁻¹ =
      ((1 - x : ℝ) : ℂ) + ((t - y : ℝ) : ℂ) * τ := by
    dsimp [c, τ]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    field_simp
    ring
  have htop (t : ℝ) : (a + u + v + t • (a + v - (a + u + v)) - c) * u⁻¹ =
      ((1 - t - x : ℝ) : ℂ) + ((1 - y : ℝ) : ℂ) * τ := by
    dsimp [c, τ]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    field_simp
    ring
  have hleft (t : ℝ) : (a + v + t • (a - (a + v)) - c) * (-u⁻¹) =
      (x : ℂ) + ((t + y - 1 : ℝ) : ℂ) * τ := by
    dsimp [c, τ]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_one]
    field_simp
    ring
  have hb := segment_reciprocal_log a (a + u) c u⁻¹ (inv_ne_zero hu) (fun t ht => by
    rw [hbottom]
    simpa only [Complex.ofReal_neg] using real_affine_mem_slit hv (t - x) (-y)
      (Or.inr (neg_ne_zero.mpr (ne_of_gt hy.1))))
  have hr := segment_reciprocal_log (a + u) (a + u + v) c u⁻¹ (inv_ne_zero hu) (fun t ht => by
    rw [hright]
    exact real_affine_mem_slit hv _ _ (Or.inl (sub_pos.mpr hx.2)))
  have ht := segment_reciprocal_log (a + u + v) (a + v) c u⁻¹ (inv_ne_zero hu) (fun t ht => by
    rw [htop]
    exact real_affine_mem_slit hv _ _ (Or.inr (ne_of_gt (sub_pos.mpr hy.2))))
  have hl := segment_reciprocal_log (a + v) a c (-u⁻¹) (neg_ne_zero.mpr (inv_ne_zero hu)) (fun t ht => by
    rw [hleft]
    exact real_affine_mem_slit hv _ _ (Or.inl hx.1))
  have ha_im : ((a - c) * u⁻¹).im < 0 := by
    have heq := hbottom 0
    simp only [zero_smul, add_zero] at heq
    rw [heq]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.neg_im, Complex.mul_im,
      Complex.ofReal_re, zero_mul, add_zero, zero_add]
    simpa only [Complex.neg_re, Complex.ofReal_re, neg_zero, zero_mul, add_zero]
      using mul_neg_of_neg_of_pos (neg_neg_of_pos hy.1) hv
  have hav_im : 0 < ((a + v - c) * u⁻¹).im := by
    have heq := htop 1
    simp only [one_smul] at heq
    have heq' : a + u + v + (a + v - (a + u + v)) = a + v := by abel
    rw [heq'] at heq
    rw [heq]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, zero_mul, add_zero, zero_add]
    exact mul_pos (sub_pos.mpr hy.2) hv
  unfold parallelogramBoundaryIntegral
  change _ = 2 * Real.pi * Complex.I
  rw [hb, hr, ht, hl]
  simp only [mul_neg] -- normalize the two left-side logarithm arguments
  rw [log_neg_of_im_neg ha_im, log_neg_of_im_pos hav_im]
  ring

lemma concatenate_with_trace (γ₁ γ₂ : PiecewiseC1Path)
    (h₁ : γ₁.path.a < γ₁.path.b) (h₂ : γ₂.path.a < γ₂.path.b)
    (hcompat : γ₁.path.target = γ₂.path.source) :
    ∃ η : PiecewiseC1Path, η.path.a = 0 ∧ η.path.b = 2 ∧
      η.path.source = γ₁.path.source ∧ η.path.target = γ₂.path.target ∧
      η.trace = γ₁.trace ∪ γ₂.trace ∧
      ∀ f : ℂ → ℂ, ContinuousOn f η.trace → η.integral f = γ₁.integral f + γ₂.integral f := by
  obtain ⟨η, ha, hb, he₁, he₂⟩ := PiecewiseC1Path.exists_concatenation γ₁ γ₂ hcompat
  have hsource : η.path.source = γ₁.path.source := by
    change η η.path.a = γ₁ γ₁.path.a
    rw [ha, he₁ (by norm_num)]
    simp
  have htarget : η.path.target = γ₂.path.target := by
    change η η.path.b = γ₂ γ₂.path.b
    rw [hb, he₂ (by norm_num)]
    congr 1
    ring
  have htrace : η.trace = γ₁.trace ∪ γ₂.trace := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      rw [ha, hb] at ht
      by_cases ht₁ : t ≤ 1
      · left
        refine ⟨γ₁.path.a + (γ₁.path.b - γ₁.path.a) * t, ⟨?_, ?_⟩,
          (he₁ ⟨ht.1, ht₁⟩).symm⟩
        · nlinarith [mul_nonneg (sub_pos.mpr h₁).le ht.1]
        · nlinarith [mul_nonneg (sub_pos.mpr h₁).le (sub_nonneg.mpr ht₁)]
      · right
        refine ⟨γ₂.path.a + (γ₂.path.b - γ₂.path.a) * (t - 1), ⟨?_, ?_⟩,
          (he₂ ⟨(not_le.mp ht₁).le, ht.2⟩).symm⟩
        · nlinarith [mul_nonneg (sub_pos.mpr h₂).le (show 0 ≤ t - 1 by linarith)]
        · nlinarith [mul_nonneg (sub_pos.mpr h₂).le (show 0 ≤ 2 - t by linarith [ht.2])]
    · rintro (⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩)
      · let t := (s - γ₁.path.a) / (γ₁.path.b - γ₁.path.a)
        have ht : t ∈ Icc (0 : ℝ) 1 :=
          ⟨div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr h₁).le,
            (div_le_one (sub_pos.mpr h₁)).mpr (by linarith [hs.2])⟩
        refine ⟨t, by rw [ha, hb]; exact ⟨ht.1, ht.2.trans (by norm_num)⟩, ?_⟩
        rw [he₁ ht]
        congr 1
        dsimp [t]
        field_simp [ne_of_gt (sub_pos.mpr h₁)]
        <;> ring
      · let t := (s - γ₂.path.a) / (γ₂.path.b - γ₂.path.a) + 1
        have ht : t ∈ Icc (1 : ℝ) 2 := by
          have hl := div_nonneg (sub_nonneg.mpr hs.1) (sub_pos.mpr h₂).le
          have hu := (div_le_one (sub_pos.mpr h₂)).mpr (show s - γ₂.path.a ≤ γ₂.path.b - γ₂.path.a by linarith [hs.2])
          exact ⟨by dsimp [t]; linarith, by dsimp [t]; linarith⟩
        refine ⟨t, by rw [ha, hb]; exact ⟨(by norm_num : (0 : ℝ) ≤ 1).trans ht.1, ht.2⟩, ?_⟩
        rw [he₂ ht]
        congr 1
        dsimp [t]
        field_simp [ne_of_gt (sub_pos.mpr h₂)]
        <;> ring
  refine ⟨η, ha, hb, hsource, htarget, htrace, ?_⟩
  intro f hf
  apply PiecewiseC1Path.integral_concatenation γ₁ γ₂ η 1
    γ₁.path.a (γ₁.path.b - γ₁.path.a)
    (γ₂.path.a - (γ₂.path.b - γ₂.path.a)) (γ₂.path.b - γ₂.path.a) f
  · rw [ha, hb]; norm_num
  · exact sub_nonneg.mpr h₁.le
  · exact sub_nonneg.mpr h₂.le
  · exact hcompat
  · rw [ha]; ring
  · ring
  · ring
  · rw [hb]; ring
  · rw [ha]; exact he₁
  · intro t ht
    rw [hb] at ht
    rw [he₂ ht]
    congr 1
    ring
  · exact hf.mono (by rw [htrace]; exact subset_union_left)
  · exact hf.mono (by rw [htrace]; exact subset_union_right)

/-- The four sides as one closed piecewise C1 path, then as a singleton cycle. -/
lemma parallelogram_cycle (a u v : ℂ) :
    ∃ Γ : IntegralCycle,
      Γ.trace = ((segmentPath a (a + u)).trace ∪
        (segmentPath (a + u) (a + u + v)).trace) ∪
        ((segmentPath (a + u + v) (a + v)).trace ∪ (segmentPath (a + v) a).trace) ∧
      ∀ f : ℂ → ℂ, ContinuousOn f Γ.trace →
        Γ.integral f = parallelogramBoundaryIntegral a u v f := by
  classical
  obtain ⟨γ₁, ha₁, hb₁, hs₁, ht₁, htr₁, hi₁⟩ := concatenate_with_trace
    (segmentPath a (a + u)) (segmentPath (a + u) (a + u + v))
    (by norm_num [segmentPath, PiecewiseC1Path.path])
    (by norm_num [segmentPath, PiecewiseC1Path.path]) (by
      simp [ComplexPath.target, ComplexPath.source, segmentPath, PiecewiseC1Path.path] <;> abel)
  obtain ⟨γ₂, ha₂, hb₂, hs₂, ht₂, htr₂, hi₂⟩ := concatenate_with_trace
    (segmentPath (a + u + v) (a + v)) (segmentPath (a + v) a)
    (by norm_num [segmentPath, PiecewiseC1Path.path])
    (by norm_num [segmentPath, PiecewiseC1Path.path]) (by
      simp [ComplexPath.target, ComplexPath.source, segmentPath, PiecewiseC1Path.path] <;> abel)
  have hjoin : γ₁.path.target = γ₂.path.source := by
    rw [ht₁, hs₂]
    simp [ComplexPath.target, ComplexPath.source, segmentPath, PiecewiseC1Path.path] <;> abel
  obtain ⟨γ, ha, hb, hs, ht, htr, hi⟩ := concatenate_with_trace γ₁ γ₂
    (by rw [ha₁, hb₁]; norm_num) (by rw [ha₂, hb₂]; norm_num) hjoin
  have hclosed : γ.IsClosed := by
    change γ.path.target = γ.path.source
    rw [ht, hs, ht₂, hs₁]
    simp [ComplexPath.target, ComplexPath.source, segmentPath, PiecewiseC1Path.path] <;> abel
  let Γ : IntegralCycle := ⟨Finsupp.single γ 1, by
    intro δ hδ
    have heq : δ = γ := by simpa using hδ
    subst δ
    exact hclosed⟩
  have hΓtr : Γ.trace = γ.trace := by
    ext z
    simp [Γ, IntegralCycle.trace, IntegralCycle.chain, IntegralChain.trace]
  have hΓint (f : ℂ → ℂ) : Γ.integral f = γ.integral f := by
    simp [Γ, IntegralCycle.integral, IntegralCycle.chain, IntegralChain.integral]
  refine ⟨Γ, by rw [hΓtr, htr, htr₁, htr₂], ?_⟩
  intro f hf
  rw [hΓtr] at hf
  rw [hΓint, hi f hf, hi₁ f (hf.mono (by rw [htr]; exact subset_union_left)),
    hi₂ f (hf.mono (by rw [htr]; exact subset_union_right))]
  unfold parallelogramBoundaryIntegral
  ring
lemma parallelogram_boundary_point (b : Module.Basis (Fin 2) ℝ ℂ) (a : ℂ)
    (r s : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (hs : s ∈ Icc (0 : ℝ) 1)
    (hboundary : r = 0 ∨ r = 1 ∨ s = 0 ∨ s = 1) :
    a + r • b 0 + s • b 1 ∈ frontier
      (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a (b 0) (b 1)) := by
  have hc₀ : b.repr (a + r • b 0 + s • b 1 - a) 0 = r := by
    have heq : a + r • b 0 + s • b 1 - a = r • b 0 + s • b 1 := by abel
    rw [heq, map_add, map_smul, map_smul]
    simp
  have hc₁ : b.repr (a + r • b 0 + s • b 1 - a) 1 = s := by
    have heq : a + r • b 0 + s • b 1 - a = r • b 0 + s • b 1 := by abel
    rw [heq, map_add, map_smul, map_smul]
    simp
  rw [(parallelogram_closed b a).frontier_eq]
  constructor
  · rw [parallelogram_coordinates]
    intro i _
    fin_cases i
    · change b.repr (a + r • b 0 + s • b 1 - a) 0 ∈ Icc 0 1
      rwa [hc₀]
    · change b.repr (a + r • b 0 + s • b 1 - a) 1 ∈ Icc 0 1
      rwa [hc₁]
  · rw [parallelogram_interior]
    intro h
    have h₀ := h 0
    have h₁ := h 1
    rw [hc₀] at h₀
    rw [hc₁] at h₁
    rcases hboundary with h | h | h | h <;> simp_all

lemma parallelogram_cycle_on_frontier {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (a : ℂ) :
    ∃ Γ : IntegralCycle,
      Γ.trace ⊆ frontier (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂) ∧
      (∀ f : ℂ → ℂ, ContinuousOn f Γ.trace →
        Γ.integral f = parallelogramBoundaryIntegral a ω₁ ω₂ f) ∧
      (∀ f : ℂ → ℂ, Periodic ω₁ ω₂ f → ContinuousOn f Γ.trace → Γ.integral f = 0) := by
  obtain ⟨Γ, htr, hi⟩ := parallelogram_cycle a ω₁ ω₂
  let b := periodBasis h₁ h₂
  have hb₀ : b 0 = ω₁ := periodBasis_zero h₁ h₂
  have hb₁ : b 1 = ω₂ := periodBasis_one h₁ h₂
  have hsubset : Γ.trace ⊆ frontier
      (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂) := by
    rw [htr, ← hb₀, ← hb₁]
    rintro z ((⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩) | (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩))
    · change t ∈ Icc (0 : ℝ) 1 at ht
      convert parallelogram_boundary_point b a t 0 ht (by simp) (Or.inr (Or.inr (Or.inl rfl))) using 1
      simp [segmentPath, PiecewiseC1Path.path]
    · change t ∈ Icc (0 : ℝ) 1 at ht
      convert parallelogram_boundary_point b a 1 t (by simp) ht (Or.inr (Or.inl rfl)) using 1
      simp [segmentPath, PiecewiseC1Path.path]
    · change t ∈ Icc (0 : ℝ) 1 at ht
      have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      convert parallelogram_boundary_point b a (1 - t) 1 ht' (by simp) (Or.inr (Or.inr (Or.inr rfl))) using 1
      simp only [segmentPath, PiecewiseC1Path.path, one_smul, sub_smul, smul_sub, smul_add]
      abel
    · change t ∈ Icc (0 : ℝ) 1 at ht
      have ht' : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
      convert parallelogram_boundary_point b a 0 (1 - t) (by simp) ht' (Or.inl rfl) using 1
      simp only [segmentPath, PiecewiseC1Path.path, zero_smul, add_zero, sub_smul, one_smul, smul_sub, smul_add]
      abel
  refine ⟨Γ, hsubset, hi, ?_⟩
  intro f hf hc
  rw [hi f hc]
  rw [htr] at hc
  apply parallelogram_periodic_integral hf a
  · exact hc.mono (by intro z hz; exact Or.inl (Or.inl hz))
  · exact hc.mono (by intro z hz; exact Or.inl (Or.inr hz))
  · exact hc.mono (by intro z hz; exact Or.inr (Or.inl hz))
  · exact hc.mono (by intro z hz; exact Or.inr (Or.inr hz))

lemma parallelogram_reciprocal_integral_of_mem_interior {ω₁ ω₂ : ℂ}
    (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) (a z : ℂ)
    (hz : z ∈ interior (Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂)) :
    parallelogramBoundaryIntegral a ω₁ ω₂ (fun w => 1 / (w - z)) = 2 * Real.pi * Complex.I := by
  let b := periodBasis h₁ h₂
  have hb₀ : b 0 = ω₁ := periodBasis_zero h₁ h₂
  have hb₁ : b 1 = ω₂ := periodBasis_one h₁ h₂
  rw [← hb₀, ← hb₁, parallelogram_interior] at hz
  have heq : z = a + b.repr (z - a) 0 • ω₁ + b.repr (z - a) 1 • ω₂ := by
    have heq := b.sum_repr (z - a)
    simp only [Fin.sum_univ_two, hb₀, hb₁] at heq
    have hh := congrArg (fun w : ℂ => a + w) heq
    have hz' : a + (z - a) = z := by abel
    rw [hz'] at hh
    calc z = a + (b.repr (z - a) 0 • ω₁ + b.repr (z - a) 1 • ω₂) := hh.symm
         _ = _ := by abel
  conv_lhs => arg 4; intro w; rw [heq]
  exact parallelogram_reciprocal_integral a ω₁ ω₂ h₁ h₂ _ _ (hz 0) (hz 1)

lemma parallelogram_reciprocal_integral_of_notMem {a u v z : ℂ}
    (hz : z ∉ Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a u v) :
    parallelogramBoundaryIntegral a u v (fun w => 1 / (w - z)) = 0 := by
  apply goursat_parallelogram a u v ({z}ᶜ) (fun w => 1 / (w - z))
  · refine ⟨isClosed_singleton.isOpen_compl, ?_⟩
    intro w hw
    exact (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const z)
      (sub_ne_zero.mpr hw)
  · intro w hw hwz
    exact hz ((mem_singleton_iff.mp hwz) ▸ hw)

/-- The sum for every complete representative set, including the empty set. -/
theorem residue_sum : Specs.D12Complex.Ch22.EllipticResidueSum.residue_sum_type := by
  classical
  intro ω₁ ω₂ h₁ h₂ f hm hf s hs
  obtain ⟨a, havoid, hreps⟩ := allowed_parallelogram ω₁ ω₂ h₁ h₂ f hm hf
  let P := Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂
  have hP : IsCompact P := by
    exact (by simp : ({a, a + ω₁, a + ω₁ + ω₂, a + ω₂} : Set ℂ).Finite).isCompact_convexHull ℝ
  have hfinite : (poleSet f ∩ interior P).Finite := (finite_poles_on_compact hm hP).subset (by
    intro z hz
    exact ⟨interior_subset hz.2, hz.1⟩)
  let t : Finset ℂ := hfinite.toFinset
  have hmem (z : ℂ) : z ∈ t ↔ z ∈ poleSet f ∧ z ∈ interior P := hfinite.mem_toFinset
  have htcomplete : CompletePoleRepresentatives ω₁ ω₂ f t := by
    refine ⟨fun z hz => ((hmem z).mp hz).1, ?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨w, _, huniq⟩ := hreps x ((hmem x).mp hx).1
      exact (huniq x ⟨((hmem x).mp hx).2, rfl⟩).trans
        (huniq y ⟨((hmem y).mp hy).2, hxy.symm⟩).symm
    · ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, ((hmem z).mp hz).1, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨w, hw, _⟩ := hreps z hz
        have hl := (projection_eq_iff w z).mp hw.2
        have hwp : w ∈ poleSet f := by
          simpa using (pole_translation hf z (w - z) hl).mpr hz
        exact ⟨w, (hmem w).mpr ⟨hwp, hw.1⟩, hw.2⟩
  obtain ⟨Γ, htrace, hInt, hcancel⟩ := parallelogram_cycle_on_frontier h₁ h₂ a
  have havoid' : Disjoint Γ.trace (poleSet f) := havoid.mono_left htrace
  have hindex : ∀ z ∈ poleSet f, Γ.index z = if z ∈ t then 1 else 0 := by
    intro z hz
    have hztr : z ∉ Γ.trace := fun hztr => Set.disjoint_left.mp havoid' hztr hz
    have hcont : ContinuousOn (fun w => 1 / (w - z)) Γ.trace :=
      Γ.chain.reciprocal_continuousOn_trace z hztr
    rw [show Γ.index z = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        Γ.integral (fun w => 1 / (w - z)) from Γ.index_eq_integral z hztr]
    rw [hInt _ hcont]
    by_cases hzI : z ∈ interior P
    · rw [parallelogram_reciprocal_integral_of_mem_interior h₁ h₂ a z hzI]
      have hzt : z ∈ t := (hmem z).mpr ⟨hz, hzI⟩
      rw [ite_eq_left hzt, inv_mul_cancel₀]
      exact mul_ne_zero (mul_ne_zero (by norm_num)
        (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    · have hzP : z ∉ P := by
        intro hzP
        exact Set.disjoint_left.mp havoid ((mem_frontier_iff_notMem_interior hzP).mpr hzI) hz
      rw [parallelogram_reciprocal_integral_of_notMem hzP, mul_zero]
      simp [hmem, hzI]
  have hsum := residue_sum_from_periodic_cycle hm hf t htcomplete Γ havoid' hindex hcancel
  exact (sum_representatives_eq hf hs htcomplete).trans hsum

/-- A genuine simple pole has nonzero residue, contradicting the sum theorem. -/
theorem no_single_simple_pole :
    Specs.D12Complex.Ch22.EllipticResidueSum.no_single_simple_pole_type :=
  no_single_simple_pole_of_residue_sum residue_sum

/-- Reduction of the full sum theorem to the purely geometric contour lemma. -/
lemma residue_sum_of_contour_geometry (hgeo : FundamentalContourGeometry) :
    Specs.D12Complex.Ch22.EllipticResidueSum.residue_sum_type := by
  classical
  intro ω₁ ω₂ h₁ h₂ f hm hf s hs
  obtain ⟨a, havoid, hreps, t, Γ, ht, htrace, hindex, hcancel⟩ := hgeo ω₁ ω₂ h₁ h₂
    (poleSet f) (poleSet_closed_discrete hm).1 (poleSet_closed_discrete hm).2
    (fun z l hl => pole_translation hf z l hl)
  let P := Specs.D12Complex.Ch04.WeakGoursat.closedParallelogram_value a ω₁ ω₂
  have hmem (z : ℂ) : z ∈ t ↔ z ∈ poleSet f ∧ z ∈ interior P := by
    change z ∈ (t : Set ℂ) ↔ _
    rw [ht]
    rfl
  have htcomplete : CompletePoleRepresentatives ω₁ ω₂ f t := by
    refine ⟨fun z hz => ((hmem z).mp hz).1, ?_, ?_⟩
    · intro x hx y hy hxy
      obtain ⟨w, _, huniq⟩ := hreps x ((hmem x).mp hx).1
      exact (huniq x ⟨((hmem x).mp hx).2, rfl⟩).trans
        (huniq y ⟨((hmem y).mp hy).2, hxy.symm⟩).symm
    · ext q
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, ((hmem z).mp hz).1, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨w, hw, _⟩ := hreps z hz
        have hl := (projection_eq_iff w z).mp hw.2
        have hwp : w ∈ poleSet f := by
          simpa using (pole_translation hf z (w - z) hl).mpr hz
        exact ⟨w, (hmem w).mpr ⟨hwp, hw.1⟩, hw.2⟩
  have havoid' : Disjoint Γ.trace (poleSet f) := htrace.symm ▸ havoid
  have hsum := residue_sum_from_periodic_cycle hm hf t htcomplete Γ havoid' ?_ hcancel
  · exact (sum_representatives_eq hf hs htcomplete).trans hsum
  · intro z hz
    have hzt : z ∉ Γ.trace := fun hztr => Set.disjoint_left.mp havoid' hztr hz
    have hmiff : z ∈ t ↔ z ∈ interior P := by rw [hmem]; simp [hz]
    rw [hindex z hzt]
    simp only [hmiff, P]

lemma allowed_parallelogram_of_contour_geometry (hgeo : FundamentalContourGeometry) :
    Specs.D12Complex.Ch22.EllipticResidueSum.allowed_parallelogram_type := by
  intro ω₁ ω₂ h₁ h₂ f hm hf
  obtain ⟨a, havoid, hreps, _⟩ := hgeo ω₁ ω₂ h₁ h₂ (poleSet f)
    (poleSet_closed_discrete hm).1 (poleSet_closed_discrete hm).2
    (fun z l hl => pole_translation hf z l hl)
  exact ⟨a, havoid, hreps⟩

end D12Complex.EllipticResidueSum

namespace D12Complex.EllipticResidueSum.Definitions
abbrev poleSet : Specs.D12Complex.Ch22.EllipticResidueSum.poleSet_type :=
  D12Complex.EllipticResidueSum.poleSet
abbrev poleClasses : Specs.D12Complex.Ch22.EllipticResidueSum.poleClasses_type :=
  D12Complex.EllipticResidueSum.poleClasses
abbrev CompletePoleRepresentatives :
    Specs.D12Complex.Ch22.EllipticResidueSum.CompletePoleRepresentatives_type :=
  D12Complex.EllipticResidueSum.CompletePoleRepresentatives
end D12Complex.EllipticResidueSum.Definitions
