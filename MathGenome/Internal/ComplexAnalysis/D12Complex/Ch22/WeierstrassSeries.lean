import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.WeierstrassSeries
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.LatticeGeometry
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.Ch22.WeierstrassSeries
abbrev lattice := Specs.D12Complex.Ch22.LatticeGeometry.lattice
abbrev weierstrassP := Specs.D12Complex.Ch22.WeierstrassSeries.weierstrassP

/-- The library period pair uses the actual given periods and their integer span. -/
def periodPair {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) : PeriodPair :=
  ⟨ω₁, ω₂, LatticeGeometry.periods_linearIndependent h₁ h₂⟩

@[simp] theorem periodPair_lattice {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) : (periodPair h₁ h₂).lattice = lattice ω₁ ω₂ := rfl

@[simp] theorem periodPair_weierstrassP {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) :
    (periodPair h₁ h₂).weierstrassP = weierstrassP ω₁ ω₂ := rfl

theorem series_representation :
    Specs.D12Complex.Ch22.WeierstrassSeries.series_representation_type := by
  intro ω₁ ω₂ h₁ h₂ z
  have h := ((periodPair h₁ h₂).hasSum_weierstrassP z).summable.sum_add_tsum_compl
    (s := ({0} : Finset (lattice ω₁ ω₂)))
  have he : (({0} : Finset (lattice ω₁ ω₂)) : Set (lattice ω₁ ω₂))ᶜ =
      {l | l ≠ 0} := by ext l; simp
  rw [he] at h
  simp only [Finset.sum_singleton, Submodule.coe_zero, sub_zero,
    zero_pow (by decide : 2 ≠ 0), div_zero, sub_zero] at h
  change weierstrassP ω₁ ω₂ z = _
  exact h.symm

theorem series_locallyUniform :
    Specs.D12Complex.Ch22.WeierstrassSeries.series_locallyUniform_type := by
  intro ω₁ ω₂ h₁ h₂
  exact (periodPair h₁ h₂).hasSumLocallyUniformly_weierstrassP.hasSumLocallyUniformlyOn

theorem holomorphic : Specs.D12Complex.Ch22.WeierstrassSeries.holomorphic_type := by
  intro ω₁ ω₂ h₁ h₂
  let L := periodPair h₁ h₂
  exact ⟨L.isClosed_lattice.isOpen_compl, fun z hz =>
    L.differentiableOn_weierstrassP.differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)⟩

theorem meromorphic : Specs.D12Complex.Ch22.WeierstrassSeries.meromorphic_type := by
  intro ω₁ ω₂ h₁ h₂
  exact (periodPair h₁ h₂).meromorphic_weierstrassP

theorem principal_part : Specs.D12Complex.Ch22.WeierstrassSeries.principal_part_type := by
  intro ω₁ ω₂ h₁ h₂ a ha
  let L := periodPair h₁ h₂
  refine ⟨fun z => L.weierstrassPExcept a z - 1 / a ^ 2, ?_, ?_⟩
  · exact (L.analyticAt_weierstrassPExcept a).sub analyticAt_const
  · exact Filter.Eventually.of_forall fun z => by
      change L.weierstrassP z = _
      rw [← L.weierstrassPExcept_add ⟨a, ha⟩]
      ring

theorem pole_order : Specs.D12Complex.Ch22.WeierstrassSeries.pole_order_type := by
  intro ω₁ ω₂ h₁ h₂ a ha
  exact (periodPair h₁ h₂).order_weierstrassP a ha

theorem derivative : Specs.D12Complex.Ch22.WeierstrassSeries.derivative_type := by
  intro ω₁ ω₂ h₁ h₂ z hz
  let L := periodPair h₁ h₂
  have hd := (holomorphic ω₁ ω₂ h₁ h₂).2 z hz |>.hasDerivAt
  convert hd using 1
  change _ = deriv L.weierstrassP z
  rw [L.deriv_weierstrassP]
  simp [PeriodPair.derivWeierstrassP, div_eq_mul_inv, tsum_mul_left, neg_mul]
  rfl

theorem derivative_locallyUniform :
    Specs.D12Complex.Ch22.WeierstrassSeries.derivative_locallyUniform_type := by
  intro ω₁ ω₂ h₁ h₂
  change HasSumLocallyUniformlyOn _ (deriv (periodPair h₁ h₂).weierstrassP) _
  rw [(periodPair h₁ h₂).deriv_weierstrassP]
  exact (periodPair h₁ h₂).hasSumLocallyUniformly_derivWeierstrassP.hasSumLocallyUniformlyOn

/-- Turn a cofinite summable bound into an everywhere bound on a compact set.
The finitely many exceptional terms are bounded by compactness. -/
theorem compact_majorant {ι : Type*} {f : ι → ℂ → ℂ} {K : Set ℂ}
    (hK : IsCompact K) (hc : ∀ i, ContinuousOn (f i) K) {u : ι → ℝ}
    (hu : Summable u) (hu0 : ∀ i, 0 ≤ u i)
    (hbound : ∀ᶠ i in cofinite, ∀ z ∈ K, ‖f i z‖ ≤ u i) :
    ∃ v : ι → ℝ, Summable v ∧ ∀ i, ∀ z ∈ K, ‖f i z‖ ≤ v i := by
  classical
  let v : ι → ℝ := fun i => sSup (insert 0 ((fun z => ‖f i z‖) '' K))
  have hb (i : ι) : BddAbove (insert 0 ((fun z => ‖f i z‖) '' K)) :=
    BddAbove.insert 0 (hK.bddAbove_image (hc i).norm)
  have hv0 (i : ι) : 0 ≤ v i := le_csSup (hb i) (mem_insert _ _)
  refine ⟨v, hu.of_norm_bounded_eventually ?_, ?_⟩
  · filter_upwards [hbound] with i hi
    rw [Real.norm_eq_abs, abs_of_nonneg (hv0 i)]
    apply csSup_le (Set.insert_nonempty _ _)
    rintro y (rfl | ⟨z, hz, rfl⟩)
    · exact hu0 i
    · exact hi z hz
  · intro i z hz
    exact le_csSup (hb i) (mem_insert_of_mem _ (mem_image_of_mem _ hz))

/-- Outside a finite set, lattice vectors have arbitrarily large norm. -/
theorem cofinite_norm_ge (L : PeriodPair) (R : ℝ) :
    ∀ᶠ l : L.lattice in cofinite, R ≤ ‖(l : ℂ)‖ := by
  apply Filter.eventually_cofinite.mpr
  apply (isCompact_iff_finite.mp (isCompact_closedBall (0 : L.lattice) R)).subset
  intro l hl
  have hl' : ‖(l : ℂ)‖ < R := not_le.mp hl
  simpa using hl'.le

theorem series_normal : Specs.D12Complex.Ch22.WeierstrassSeries.series_normal_type := by
  intro ω₁ ω₂ h₁ h₂ K hK hsub
  let L := periodPair h₁ h₂
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.exists_pos_norm_lt
  have hc (l : L.lattice) :
      ContinuousOn (fun z : ℂ => 1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2) K := by
    apply ContinuousOn.sub _ continuousOn_const
    apply continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
    intro z hz
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro he
    have he' : z = (l : ℂ) := he
    exact hsub hz (he' ▸ l.2)
  apply compact_majorant hK hc
    ((ZLattice.summable_norm_rpow L.lattice (-3) (by simp; norm_num)).mul_left (10 * r))
    (fun l => by positivity)
  filter_upwards [cofinite_norm_ge L (2 * r)] with l hl
  intro z hz
  exact PeriodPair.weierstrassP_bound r hr z (hKr z hz) l hl

/-- Uniform inverse-cube estimate for the far lattice tail. -/
theorem inverse_cube_bound (r : ℝ) (hr : 0 < r) (z l : ℂ)
    (hz : ‖z‖ < r) (hl : 2 * r ≤ ‖l‖) :
    ‖1 / (z - l) ^ 3‖ ≤ 8 * ‖l‖ ^ (-3 : ℝ) := by
  have hl0 : 0 < ‖l‖ := by linarith
  have hd : ‖l‖ / 2 ≤ ‖z - l‖ := by
    have := norm_sub_norm_le l z
    rw [norm_sub_rev] at this
    linarith
  calc
    _ = 1 / ‖z - l‖ ^ 3 := by simp
    _ ≤ 1 / (‖l‖ / 2) ^ 3 := by
      apply one_div_le_one_div_of_le (pow_pos (by positivity) _) (pow_le_pow_left₀ (by positivity) hd _)
    _ = 8 * ‖l‖ ^ (-3 : ℝ) := by
      rw [show (-3 : ℝ) = -(3 : ℝ) by norm_num, Real.rpow_neg (norm_nonneg l), Real.rpow_ofNat]
      field_simp
      ring

theorem derivative_normal : Specs.D12Complex.Ch22.WeierstrassSeries.derivative_normal_type := by
  intro ω₁ ω₂ h₁ h₂ K hK hsub
  let L := periodPair h₁ h₂
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.exists_pos_norm_lt
  have hc (l : L.lattice) : ContinuousOn (fun z : ℂ => 1 / (z - (l : ℂ)) ^ 3) K := by
    apply continuousOn_const.div ((continuousOn_id.sub continuousOn_const).pow _)
    intro z hz
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro he
    have he' : z = (l : ℂ) := he
    exact hsub hz (he' ▸ l.2)
  apply compact_majorant hK hc
    ((ZLattice.summable_norm_rpow L.lattice (-3) (by simp; norm_num)).mul_left 8)
    (fun l => by positivity)
  filter_upwards [cofinite_norm_ge L (2 * r)] with l hl
  intro z hz
  exact inverse_cube_bound r hr z l (hKr z hz) hl

theorem absolute_convergence :
    Specs.D12Complex.Ch22.WeierstrassSeries.absolute_convergence_type := by
  intro ω₁ ω₂ h₁ h₂ z hz
  have hs : ({z} : Set ℂ) ⊆ (lattice ω₁ ω₂ : Set ℂ)ᶜ := by
    exact singleton_subset_iff.mpr hz
  obtain ⟨u, hu, hbu⟩ := series_normal ω₁ ω₂ h₁ h₂ {z} isCompact_singleton hs
  obtain ⟨v, hv, hbv⟩ := derivative_normal ω₁ ω₂ h₁ h₂ {z} isCompact_singleton hs
  have hu' : Summable (fun l : lattice ω₁ ω₂ =>
      ‖1 / (z - (l : ℂ)) ^ 2 - 1 / (l : ℂ) ^ 2‖) :=
    hu.of_norm_bounded (fun l => by simpa only [norm_norm] using hbu l z (by simp))
  exact ⟨hu'.subtype (· ≠ 0),
    hv.of_norm_bounded (fun l => by simpa only [norm_norm] using hbv l z (by simp))⟩

theorem termwise_differentiation :
    Specs.D12Complex.Ch22.WeierstrassSeries.termwise_differentiation_type := by
  intro ω₁ ω₂ h₁ h₂
  let L := periodPair h₁ h₂
  apply (series_locallyUniform ω₁ ω₂ h₁ h₂).deriv _ L.isClosed_lattice.isOpen_compl
  apply Filter.Eventually.of_forall
  intro s
  apply DifferentiableOn.fun_sum
  intro l hl
  apply DifferentiableOn.sub _ (differentiableOn_const _)
  apply DifferentiableOn.div (differentiableOn_const _) (by fun_prop)
  intro z hz
  exact pow_ne_zero _ (sub_ne_zero.mpr fun h => hz (h.symm ▸ l.2))

end D12Complex.Ch22.WeierstrassSeries
