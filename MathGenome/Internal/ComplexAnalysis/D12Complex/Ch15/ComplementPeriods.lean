import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch15.ComplementPeriods
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch15.OpenRunge
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereTopology

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.ComplementPeriods

/-- The complement always contains infinity, including when Ω is the plane. -/
theorem infty_mem_complement (Ω : Set ℂ) :
    sphereInfty ∈ (sphereFinite '' Ω)ᶜ := by
  rintro ⟨z, _, hz⟩
  exact OnePoint.coe_ne_infty z hz

/-- Separate a disconnected closed spherical set into two compact pieces,
with infinity in the second piece. The first piece therefore has a compact
finite-coordinate preimage. This is ordinary connectedness, with no planar
separation theorem. -/
theorem complement_compact_partition (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hdisc : ¬ IsConnected (sphereFinite '' Ω)ᶜ) :
    ∃ A B : Set RiemannSphere,
      IsClosed A ∧ IsClosed B ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint A B ∧ A ∪ B = (sphereFinite '' Ω)ᶜ ∧ sphereInfty ∈ B := by
  classical
  let C := (sphereFinite '' Ω)ᶜ
  have hC : IsClosed C := (OnePoint.isOpen_image_coe.mpr hΩ).isClosed_compl
  have hi : sphereInfty ∈ C := infty_mem_complement Ω
  have hnp : ¬ IsPreconnected C := fun hp => hdisc ⟨⟨sphereInfty, hi⟩, hp⟩
  rw [isPreconnected_closed_iff] at hnp
  push Not at hnp
  obtain ⟨u, v, hu, hv, hcover, hune, hvne, hdis⟩ := hnp
  have hd : Disjoint (C ∩ u) (C ∩ v) := by
    apply disjoint_left.mpr
    intro p hp hq
    have hm : p ∈ C ∩ (u ∩ v) := ⟨hp.1, hp.2, hq.2⟩
    rw [hdis] at hm
    exact hm
  have heq : (C ∩ u) ∪ (C ∩ v) = C := by
    ext p
    constructor
    · rintro (hp | hp) <;> exact hp.1
    · intro hp
      rcases hcover hp with hpu | hpv
      · exact Or.inl ⟨hp, hpu⟩
      · exact Or.inr ⟨hp, hpv⟩
  rcases hcover hi with hiu | hiv
  · refine ⟨C ∩ v, C ∩ u, hC.inter hv, hC.inter hu, hvne, hune,
      hd.symm, ?_, ⟨hi, hiu⟩⟩
    rwa [union_comm]
  · exact ⟨C ∩ u, C ∩ v, hC.inter hu, hC.inter hv, hune, hvne,
      hd, heq, ⟨hi, hiv⟩⟩

theorem disconnected_complement_cycle :
    Specs.D12Complex.Ch15.ComplementPeriods.disconnected_complement_cycle_type := by
  intro Ω hΩ hdisc
  obtain ⟨A, B, hA, hB, hAne, _, hd, hcover, hiB⟩ :=
    complement_compact_partition Ω hΩ hdisc
  have hiA : sphereInfty ∉ A := fun hi => disjoint_left.mp hd hi hiB
  let K := sphereFinite ⁻¹' A
  let U := (sphereFinite ⁻¹' B)ᶜ
  have hK : IsCompact K := (OnePoint.isClosed_iff_of_notMem hiA).mp hA |>.2
  have hU : IsOpen U := (hB.preimage continuous_sphereFinite).isOpen_compl
  have hKU : K ⊆ U := fun _ hz => fun hb => disjoint_left.mp hd hz hb
  obtain ⟨p, hp⟩ := hAne
  obtain hpinf | ⟨a, rfl⟩ := sphere_eq_infty_or_finite p
  · exact (hiA (hpinf ▸ hp)).elim
  have haK : a ∈ K := hp
  have haΩ : a ∉ Ω := by
    intro ha
    have hc : sphereFinite a ∈ (sphereFinite '' Ω)ᶜ := by
      rw [← hcover]
      exact Or.inl hp
    exact hc ⟨a, ha, rfl⟩
  obtain ⟨Γ, hpoly, htrace, _, hone, _⟩ :=
    PolygonRepresentation.exists_polygonal_cycle K U hK hU hKU
  have hΓΩ : Γ.trace ⊆ Ω := by
    intro z hz
    by_contra hzΩ
    have hc : sphereFinite z ∈ (sphereFinite '' Ω)ᶜ := by
      rintro ⟨w, hw, he⟩
      exact hzΩ (sphereFinite_injective he ▸ hw)
    rw [← hcover] at hc
    rcases hc with hza | hzb
    · exact (htrace hz).2 hza
    · exact (htrace hz).1 hzb
  have haΓ : a ∉ Γ.trace := fun hz => haΩ (hΓΩ hz)
  have hindex : Γ.index a = 1 := hone a haK
  have hint : Γ.integral (fun z => 1 / (z - a)) =
      2 * (Real.pi : ℂ) * Complex.I := by
    have he := IntegralCycle.index_eq_integral Γ a haΓ
    rw [hindex] at he
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    simpa only [mul_one] using (inv_mul_eq_iff_eq_mul₀ hne).mp he.symm
  exact ⟨a, Γ, haΩ, hpoly, hΓΩ, haΓ, hindex, hint⟩

/-- A polynomial has a global primitive, hence zero period on every closed
piecewise C1 path, including constant and degenerate ones. -/
theorem polynomial_period_zero (P : Polynomial ℂ) (γ : PiecewiseC1Path)
    (hγ : γ.IsClosed) : γ.integral (fun z => P.eval z) = 0 := by
  have hf : HolomorphicOn univ (fun z => P.eval z) :=
    ⟨isOpen_univ, fun z _ => P.differentiableAt⟩
  obtain ⟨F, hF⟩ := DiskPrimitives.entire_exists_primitive _ hf
  rw [Primitives.piecewise_endpoint univ _ F P.continuous.continuousOn hF γ
    (subset_univ _), hγ, sub_self]

/-- Locally uniform polynomial approximation passes through the integral on
the compact trace of each individual path. -/
theorem zero_periods_of_connected_complement (Ω : Set ℂ) (hΩ : IsOpen Ω)
    (hc : IsConnected (sphereFinite '' Ω)ᶜ) (f : ℂ → ℂ)
    (hf : HolomorphicOn Ω f) (γ : PiecewiseC1Path)
    (htrace : γ.trace ⊆ Ω) (hclosed : γ.IsClosed) : γ.integral f = 0 := by
  obtain ⟨P, hP⟩ := OpenRunge.polynomial_runge Ω f hΩ hc hf
  have ht := PiecewiseC1Length.integral_tendsto_uniform γ
    (fun n z => (P n).eval z) f (fun n => (P n).continuous.continuousOn)
    (hP γ.trace γ.path.trace_compact htrace)
  have hz : Tendsto (fun n => γ.integral (fun z => (P n).eval z)) atTop (𝓝 0) := by
    simpa only [polynomial_period_zero _ γ hclosed] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht hz

theorem connected_complement_iff_zero_periods :
    Specs.D12Complex.Ch15.ComplementPeriods.connected_complement_iff_zero_periods_type := by
  intro Ω hΩ
  constructor
  · intro hc f hf γ htrace hclosed
    exact zero_periods_of_connected_complement Ω hΩ.2.1 hc f hf γ htrace hclosed
  · intro hzero
    by_contra hc
    obtain ⟨a, Γ, ha, _, htrace, _, _, hint⟩ :=
      disconnected_complement_cycle Ω hΩ.2.1 hc
    have hf : HolomorphicOn Ω (fun z => 1 / (z - a)) := by
      refine ⟨hΩ.2.1, fun z hz => ?_⟩
      exact (differentiableAt_const (1 : ℂ)).div (differentiableAt_id.sub_const a)
        (sub_ne_zero.mpr (fun he => ha (he ▸ hz)))
    have hΓzero : Γ.integral (fun z => 1 / (z - a)) = 0 := by
      unfold IntegralCycle.integral IntegralChain.integral Finsupp.sum
      apply Finset.sum_eq_zero
      intro γ hγ
      dsimp only
      rw [hzero _ hf γ (fun z hz => htrace ⟨γ, hγ, hz⟩) (Γ.property γ hγ), mul_zero]
    have hne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero
    exact hne (hint.symm.trans hΓzero)

end D12Complex.ComplementPeriods
