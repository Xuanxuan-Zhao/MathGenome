import Specs.LinearAlgebraicGroups.Arithmetic.LocalRescaling
import LinearAlgebraicGroups.Arithmetic.AdelicGroups
import LinearAlgebraicGroups.Arithmetic.LocalAlgebraicTransport
import LinearAlgebraicGroups.Arithmetic.LocalQuotientTransport
import LinearAlgebraicGroups.Arithmetic.SteinbergFundamentalTraces
import LinearAlgebraicGroups.Arithmetic.RationalStronglyRegularElements
import LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
import LinearAlgebraicGroups.Relative.RelativeWeylScheme
import LinearAlgebraicGroups.Relative.RationalDensity
import LinearAlgebraicGroups.Reductive.CentralDerived
import LinearAlgebraicGroups.Solvable.FiniteWordClosure
import LinearAlgebraicGroups.Solvable.WordDomainGeometry
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Support

import LinearAlgebraicGroups.Arithmetic.LocalQuotientMixing
open Filter MeasureTheory Set
open Topology
open scoped InnerProductSpace Topology

namespace LinearAlgebraicGroups.Arithmetic.LocalRescaling

open LocalQuotientTransport (RightCosets RightInvariant L2 coset rightTranslate rightOperator
  quotient_action)

private def QuotientMixing {G : Type*} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {ν : Measure (RightCosets H)} (hν : RightInvariant ν) (a : G) : Prop :=
  ∀ f g : L2 ν, Tendsto (fun m : ℕ => ⟪g, rightOperator hν (a ^ m) f⟫_ℂ) atTop
    (𝓝 (((∫ x, f x ∂ν) * (∫ x, star (g x) ∂ν)) / ((ν univ).toReal : ℂ)))

private theorem quotientMixing_inv {G : Type*} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {ν : Measure (RightCosets H)} {hν : RightInvariant ν}
    {a : G} (hmix : QuotientMixing hν a) : QuotientMixing hν a⁻¹ := by
  intro f g
  have hh := Complex.continuous_conj.continuousAt.tendsto.comp (hmix g f)
  have hconj : starRingEnd ℂ (((∫ x, g x ∂ν) * (∫ x, star (f x) ∂ν)) / ((ν univ).toReal : ℂ)) =
      ((∫ x, f x ∂ν) * (∫ x, star (g x) ∂ν)) / ((ν univ).toReal : ℂ) := by
    have hf := integral_conj (μ := ν) (f := fun x => star (f x))
    change (∫ x, star (star (f x)) ∂ν) = star (∫ x, star (f x) ∂ν) at hf
    have hg := integral_conj (μ := ν) (f := fun x => g x)
    change (∫ x, star (g x) ∂ν) = star (∫ x, g x ∂ν) at hg
    change star (((∫ x, g x ∂ν) * (∫ x, star (f x) ∂ν)) / ((ν univ).toReal : ℂ)) = _
    rw [star_div₀, star_mul, ← hf, ← hg]
    simp
  change Tendsto (fun n : ℕ => star ⟪f, rightOperator hν (a ^ n) g⟫_ℂ) atTop (𝓝 _) at hh
  rw [hconj] at hh
  refine hh.congr fun n => ?_
  have h := (rightOperator hν (a ^ n)).inner_map_map g (rightOperator hν (a⁻¹ ^ n) f)
  rw [← (LocalQuotientTransport.representation_law hν).2, inv_pow, mul_inv_cancel,
    (LocalQuotientTransport.representation_law hν).1] at h
  rw [inv_pow]
  exact (inner_conj_symm _ _).trans h

private theorem integral_indicatorOne {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsFiniteMeasure ν] {U : Set X} (hU : MeasurableSet U) :
    ∫ x, indicatorConstLp 2 hU (measure_ne_top ν U) (1 : ℂ) x ∂ν = (ν.real U : ℂ) := by
  rw [integral_congr_ae (indicatorConstLp_coeFn (μ := ν)), integral_indicator hU]
  simp

private theorem integral_star_indicatorOne {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsFiniteMeasure ν] {U : Set X} (hU : MeasurableSet U) :
    ∫ x, star (indicatorConstLp 2 hU (measure_ne_top ν U) (1 : ℂ) x) ∂ν =
      (ν.real U : ℂ) := by
  have h : (fun x => star (indicatorConstLp 2 hU (measure_ne_top ν U) (1 : ℂ) x)) =ᵐ[ν]
      U.indicator (fun _ => (1 : ℂ)) := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := ν) (s := U) (c := (1 : ℂ))
      (hs := hU) (hμs := measure_ne_top ν U)] with x hx
    rw [hx]
    by_cases hmem : x ∈ U <;> simp [hmem]
  rw [integral_congr_ae h, integral_indicator hU]
  simp

private theorem eventually_intersects_of_mixing {G : Type*} [Group G] [TopologicalSpace G]
    {H : Subgroup G} {ν : Measure (RightCosets H)} [IsFiniteMeasure ν]
    {hν : RightInvariant ν} {a : G} (hmix : QuotientMixing hν a)
    {U V : Set (RightCosets H)} (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hUpos : 0 < ν U) (hVpos : 0 < ν V) :
    ∀ᶠ n : ℕ in atTop, ∃ q ∈ U, rightTranslate (a ^ n) q ∈ V := by
  let f : L2 ν := indicatorConstLp 2 hV (measure_ne_top ν V) (1 : ℂ)
  let g : L2 ν := indicatorConstLp 2 hU (measure_ne_top ν U) (1 : ℂ)
  have h := hmix f g
  rw [show (∫ x, f x ∂ν) = (ν.real V : ℂ) from integral_indicatorOne ν hV,
    show (∫ x, star (g x) ∂ν) = (ν.real U : ℂ) from integral_star_indicatorOne ν hU] at h
  have hpos (s : Set (RightCosets H)) (hs : 0 < ν s) : (ν.real s : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hs.ne' (measure_ne_top _ _)).ne'
  have hlimit : (ν.real V : ℂ) * (ν.real U : ℂ) / ((ν univ).toReal : ℂ) ≠ 0 :=
    div_ne_zero (mul_ne_zero (hpos _ hVpos) (hpos _ hUpos))
      (hpos _ (hUpos.trans_le (measure_mono (subset_univ U))))
  filter_upwards [h.eventually_ne hlimit] with n hn
  by_contra hdisjoint
  apply hn
  rw [MeasureTheory.L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  have hf : (fun q => rightOperator hν (a ^ n) f q) =ᵐ[ν]
      (fun q => f (rightTranslate (a ^ n) q)) :=
    Lp.coeFn_compMeasurePreserving f (hν (a ^ n))
  have hf' : (fun q => f (rightTranslate (a ^ n) q)) =ᵐ[ν]
      fun q => V.indicator (fun _ => (1 : ℂ)) (rightTranslate (a ^ n) q) :=
    (hν (a ^ n)).quasiMeasurePreserving.ae_eq_comp indicatorConstLp_coeFn
  have hg : (fun q => g q) =ᵐ[ν] U.indicator (fun _ => (1 : ℂ)) :=
    indicatorConstLp_coeFn
  filter_upwards [hf.trans hf', hg] with q hq hq'
  rw [hq, hq']
  by_cases hqU : q ∈ U
  · have hqV : rightTranslate (a ^ n) q ∉ V := fun hv => hdisjoint ⟨q, hqU, hv⟩
    simp [hqV]
  · simp [hqU]

private theorem measure_pos_of_open {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G]
    {H : Subgroup G} {ν : Measure (RightCosets H)}
    (hν : RightInvariant ν) (hν₀ : ν ≠ 0)
    {U : Set (RightCosets H)} (hU : IsOpen U) (hUn : U.Nonempty) : 0 < ν U := by
  have hquot := (quotient_action H).1
  let : SecondCountableTopology (RightCosets H) := hquot.secondCountableTopology
  obtain ⟨q, hq⟩ := (Measure.nonempty_inter_support_of_pos (s := univ)
    (pos_iff_ne_zero.mpr (Measure.measure_univ_eq_zero.not.mpr hν₀))).mono inter_subset_right
  obtain ⟨p, hp⟩ := hUn
  obtain ⟨z, rfl⟩ := hquot.surjective q
  obtain ⟨y, rfl⟩ := hquot.surjective p
  let b := z⁻¹ * y
  have hzy : rightTranslate b (coset H z) = coset H y := by
    change coset H (z * (z⁻¹ * y)) = coset H y
    simp
  have hc : Continuous (rightTranslate (H := H) b) :=
    (quotient_action H).2.2.comp (continuous_id.prodMk continuous_const)
  have hpre : rightTranslate b ⁻¹' U ∈ 𝓝 (coset H z) :=
    (hU.preimage hc).mem_nhds (show rightTranslate b (coset H z) ∈ U from hzy ▸ hp)
  have hpos := (Measure.mem_support_iff_forall _).mp hq _ hpre
  rw [← Measure.map_apply (hν b).measurable hU.measurableSet, (hν b).map_eq] at hpos
  exact hpos

private theorem eventually_coset_intersects {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G]
    {H : Subgroup G} {ν : Measure (RightCosets H)} [IsFiniteMeasure ν]
    {hν : RightInvariant ν} (hν₀ : ν ≠ 0) {a : G} (hmix : QuotientMixing hν a)
    {U V : Set G} (hU : IsOpen U) (hV : IsOpen V) (hUn : U.Nonempty) (hVn : V.Nonempty)
    (g : G) :
    ∀ᶠ n : ℕ in atTop, ∃ y ∈ U, ∃ z ∈ V, ∃ b ∈ H, y * a ^ n = b * (z * g) := by
  obtain ⟨hq, heq, _⟩ := quotient_action H
  have hVg : IsOpen ((fun z : G => z * g) '' V) := (Homeomorph.mulRight g).isOpenMap _ hV
  have hU' := hq.isOpenMap _ hU
  have hV' := hq.isOpenMap _ hVg
  filter_upwards [eventually_intersects_of_mixing hmix hU'.measurableSet hV'.measurableSet
    (measure_pos_of_open hν hν₀ hU' (hUn.image _))
    (measure_pos_of_open hν hν₀ hV' ((hVn.image _).image _))] with n hn
  obtain ⟨_, ⟨y, hy, rfl⟩, ⟨_, ⟨z, hz, rfl⟩, he⟩⟩ := hn
  obtain ⟨b, hb, h⟩ := (heq (y * a ^ n) (z * g)).mp he.symm
  exact ⟨y, hy, z, hz, b, hb, h⟩

private theorem subgroup_eq_top_of_periodic_mixing
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] {H : Subgroup G} (hH : IsClosed (H : Set G))
    {ν : Measure (RightCosets H)} [IsFiniteMeasure ν]
    {hν : RightInvariant ν} (hν₀ : ν ≠ 0) {a : G} (hmix : QuotientMixing hν a)
    {p : ℕ} (hp : 0 < p) (ha : a ^ p = 1) : H = ⊤ := by
  apply top_unique
  intro x _
  by_contra hx
  have hevent : {q : G × G | q.1 * q.2⁻¹ ∉ H} ∈ 𝓝 x ×ˢ 𝓝 (1 : G) := by
    rw [← nhds_prod_eq]
    exact (hH.isOpen_compl.preimage (continuous_fst.mul continuous_snd.inv)).mem_nhds (by simpa)
  obtain ⟨S, hS, T, hT, hST⟩ := mem_prod_iff.mp hevent
  obtain ⟨U, hUsub, hU, hxU⟩ := mem_nhds_iff.mp hS
  obtain ⟨V, hVsub, hV, h1V⟩ := mem_nhds_iff.mp hT
  have hh : Tendsto (fun n : ℕ => p * n) atTop atTop :=
    tendsto_atTop.2 fun n => eventually_atTop.2 ⟨n, fun j hj =>
      hj.trans (Nat.le_mul_of_pos_left _ hp)⟩
  obtain ⟨n, y, hy, z, hz, b, hb, hab⟩ :=
    (hh.eventually (eventually_coset_intersects hν₀ hmix hU hV ⟨x, hxU⟩ ⟨1, h1V⟩ 1)).exists
  have hz' : y * z⁻¹ = b := by
    have h := hab
    rw [pow_mul, ha, one_pow, mul_one, mul_one] at h
    exact mul_inv_eq_iff_eq_mul.mpr h
  have hpair : (y, z) ∈ S ×ˢ T := ⟨hUsub hy, hVsub hz⟩
  have hbad : y * z⁻¹ ∉ H := hST hpair
  exact hbad (hz'.symm ▸ hb)

/-- Stability in the base point and mixing put the entire conjugacy class
of the rescaled limit in the same conjugate of the subgroup. -/
private theorem conjugates_mem_of_rescaled_limit {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [SecondCountableTopology G]
    {H : Subgroup G} (hH : IsClosed (H : Set G))
    {ν : Measure (RightCosets H)} [IsFiniteMeasure ν]
    {hν : RightInvariant ν} (hν₀ : ν ≠ 0) {a : G} (hmix : QuotientMixing hν a)
    {h : ℕ → G} (hh : ∀ n, h n ∈ H) {m : ℕ → ℕ} (hm : Tendsto m atTop atTop)
    {x u : G}
    (hlim : Tendsto (fun p : ℕ × G => (a ^ m p.1)⁻¹ * (p.2⁻¹ * h p.1 * p.2) * a ^ m p.1)
      (atTop ×ˢ 𝓝 x) (𝓝 u)) (g : G) :
    x * (g * u * g⁻¹) * x⁻¹ ∈ H := by
  let l : Filter ((ℕ × G) × G) := (atTop ×ˢ 𝓝 x) ×ˢ 𝓝 x
  let r (p : (ℕ × G) × G) := (a ^ m p.1.1)⁻¹ * (p.1.2⁻¹ * h p.1.1 * p.1.2) * a ^ m p.1.1
  have hr : Tendsto r l (𝓝 u) := hlim.comp tendsto_fst
  have hz : Tendsto (fun p : (ℕ × G) × G => p.2) l (𝓝 x) := tendsto_snd
  have ht : Tendsto (fun p => p.2 * (g * r p * g⁻¹) * p.2⁻¹) l
      (𝓝 (x * (g * u * g⁻¹) * x⁻¹)) :=
    (hz.mul ((tendsto_const_nhds.mul hr).mul tendsto_const_nhds)).mul hz.inv
  by_contra hnot
  have he := ht.eventually (hH.isOpen_compl.mem_nhds hnot)
  obtain ⟨S, hS, V, hV, hSV⟩ := mem_prod_iff.mp he
  obtain ⟨I, hI, U, hU, hIU⟩ := mem_prod_iff.mp hS
  obtain ⟨U', hU'U, hU'o, hxU'⟩ := mem_nhds_iff.mp hU
  obtain ⟨V', hV'V, hV'o, hxV'⟩ := mem_nhds_iff.mp hV
  have hex := hm.eventually (eventually_coset_intersects hν₀ hmix hU'o hV'o ⟨x, hxU'⟩ ⟨x, hxV'⟩ g)
  have hI' : ∀ᶠ n in atTop, n ∈ I := hI
  obtain ⟨n, hn, y, hy, z, hz', b, hb, hrel⟩ := (hI'.and hex).exists
  have hmem := hSV (show ((n, y), z) ∈ S ×ˢ V from
    ⟨hIU ⟨hn, hU'U hy⟩, hV'V hz'⟩)
  have eqn : z * (g * r ((n, y), z) * g⁻¹) * z⁻¹ = b⁻¹ * h n * b := by
    have heq : y * a ^ m n = b * z * g := by simpa only [mul_assoc] using hrel
    change z * (g * ((a ^ m n)⁻¹ * (y⁻¹ * h n * y) * a ^ m n) * g⁻¹) * z⁻¹ = _
    calc
      _ = (z * g) * ((y * a ^ m n)⁻¹ * h n * (y * a ^ m n)) * (z * g)⁻¹ := by group
      _ = _ := by rw [heq]; group
  exact hmem (eqn.symm ▸ H.mul_mem (H.mul_mem (H.inv_mem hb) (hh n)) hb)

private theorem exists_small_sequence_avoiding_finite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T1Space G] [FirstCountableTopology G]
    (H : Subgroup G) (hnd : ¬ DiscreteTopology H) {S : Set G} (hS : S.Finite) :
    ∃ h : ℕ → G, (∀ n, h n ∈ H ∧ h n ∉ S) ∧ Tendsto h atTop (𝓝 1) := by
  have hone : (1 : G) ∈ closure ((H : Set G) \ S) := by
    by_contra hc
    let U := (closure ((H : Set G) \ S))ᶜ ∩ (S \ {1})ᶜ
    have hU : IsOpen U := isClosed_closure.isOpen_compl.inter
      (hS.subset Set.sdiff_subset).isClosed.isOpen_compl
    have hpre : ((↑) : H → G) ⁻¹' U = ({1} : Set H) := by
      ext y
      constructor
      · intro hy
        have hys : (y : G) ∈ S := by
          by_contra hyn
          exact hy.1 (subset_closure ⟨y.property, hyn⟩)
        exact Set.mem_singleton_iff.mpr (Subtype.ext
          ((not_not.mp (fun hn => hy.2 ⟨hys, hn⟩)) : (↑y : G) ∈ ({1} : Set G)))
      · rintro (rfl : y = 1)
        exact ⟨hc, fun hn => hn.2 (mem_singleton _)⟩
    exact hnd (discreteTopology_of_isOpen_singleton_one (hpre ▸ hU.preimage continuous_subtype_val))
  exact mem_closure_iff_seq_limit.mp hone

private theorem exists_rescaled_coordinates {F ι : Type*} [NormedField F] [ProperSpace F]
    [Fintype ι] (w : ι → F) (d : ℕ → ι → F) (hd : Tendsto d atTop (𝓝 0))
    (hexpand : ∀ n, ∃ i, 1 < ‖w i‖ ∧ d n i ≠ 0) {r : ℝ} (hr : 0 < r) :
    ∃ (m φ : ℕ → ℕ) (b : ι → F), Tendsto m atTop atTop ∧ StrictMono φ ∧
      Tendsto (fun n i => w i ^ m (φ n) * d (φ n) i) atTop (𝓝 b) ∧
      r ≤ ‖b‖ ∧ ‖b‖ ≤ ‖w‖ * r ∧ ∃ i, 1 < ‖w i‖ ∧ b i ≠ 0 := by
  classical
  let c (n k : ℕ) : ι → F := fun i => w i ^ k * d n i
  have hstep (n k : ℕ) : ‖c n (k + 1)‖ ≤ ‖w‖ * ‖c n k‖ := by
    refine (pi_norm_le_iff_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr ?_
    intro i
    have heq : c n (k + 1) i = w i * c n k i := by simp [c, pow_succ', mul_assoc]
    rw [heq, norm_mul]
    exact mul_le_mul (norm_le_pi_norm w i) (norm_le_pi_norm (c n k) i)
      (norm_nonneg _) (norm_nonneg _)
  have hbig (n : ℕ) : ∃ k : ℕ, r ≤ ‖c n k‖ := by
    obtain ⟨i, hi, hdi⟩ := hexpand n
    have hpow : Tendsto (fun k : ℕ => ‖w i‖ ^ k * ‖d n i‖) atTop atTop :=
      Tendsto.atTop_mul_const (norm_pos_iff.mpr hdi) (tendsto_pow_atTop_atTop_of_one_lt hi)
    obtain ⟨k, hk⟩ := (tendsto_atTop.mp hpow r).exists
    exact ⟨k, (hk.trans_eq (by simp [c, norm_mul, norm_pow])).trans (norm_le_pi_norm (c n k) i)⟩
  let m (n : ℕ) := Nat.find (hbig n)
  have hm_lo (n : ℕ) : r ≤ ‖c n (m n)‖ := Nat.find_spec (hbig n)
  have hm_hi : ∀ᶠ n in atTop, ‖c n (m n)‖ ≤ ‖w‖ * r := by
    filter_upwards [hd.norm.eventually_lt_const (by simpa using hr)] with n hn
    have hm0 : m n ≠ 0 := by
      intro hm0
      apply hn.not_ge
      simpa [hm0, c] using hm_lo n
    have hprec : ‖c n (m n - 1)‖ < r :=
      lt_of_not_ge (Nat.find_min (hbig n) (show m n - 1 < m n by omega))
    have hsucc : m n - 1 + 1 = m n := by omega
    rw [← hsucc]
    exact (hstep n (m n - 1)).trans (mul_le_mul_of_nonneg_left hprec.le (norm_nonneg _))
  have hck (k : ℕ) : Tendsto (fun n => c n k) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.mpr fun i => ?_
    have hi := (continuous_apply i).continuousAt.tendsto.comp hd
    simpa [c, Function.comp_def] using tendsto_const_nhds.mul hi
  have hm : Tendsto m atTop atTop := by
    refine tendsto_atTop.mpr fun k => ?_
    have hlt (j : ℕ) : ∀ᶠ n in atTop, ‖c n j‖ < r := by
      have hnorm := (hck j).norm
      exact hnorm.eventually_lt_const (by simpa using hr)
    have hfinite := (eventually_all_finset (Finset.range k)).mpr (fun j _ => hlt j)
    filter_upwards [hfinite] with n hn
    by_contra! hnk
    exact (hn _ (Finset.mem_range.mpr hnk)).not_ge (hm_lo n)
  let C := Metric.closedBall (0 : ι → F) (‖w‖ * r) ∩ {z : ι → F | r ≤ ‖z‖}
  have hC : IsCompact C := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const continuous_norm)
  have hcC : ∀ᶠ n in atTop, c n (m n) ∈ C := by
    filter_upwards [hm_hi] with n hn
    exact ⟨by simpa [Metric.mem_closedBall, dist_zero_right] using hn, hm_lo n⟩
  obtain ⟨b, hb, φ, hφ, hlim⟩ := hC.tendsto_subseq' hcC.frequently
  refine ⟨m, φ, b, hm, hφ, hlim, hb.2, ?_, ?_⟩
  · simpa [Metric.mem_closedBall, dist_zero_right] using hb.1
  · by_contra! hn
    have hbzero : b = 0 := by
      funext i
      by_cases hwi : 1 < ‖w i‖
      · exact hn i hwi
      · have hnorm (n : ℕ) : ‖c n (m n) i‖ ≤ ‖d n i‖ := by
          simp only [c, norm_mul, norm_pow]
          exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (le_of_not_gt hwi))
        have h0 : Tendsto (fun n => c n (m n) i) atTop (𝓝 0) :=
          squeeze_zero_norm hnorm (((continuous_apply i).continuousAt.tendsto.comp hd).norm.trans
            (by simp))
        exact tendsto_nhds_unique ((continuous_apply i).continuousAt.tendsto.comp hlim)
          (h0.comp hφ.tendsto_atTop)
    exact hr.not_ge (by simpa [hbzero] using hb.2)

/-- The conjugated coordinates lie in finitely many spaces of continuous
functions. Simultaneous convergence of their coefficients gives convergence
as the base point varies. -/
private theorem exists_stable_rescaled_coordinates
    {F G ι : Type*} [NontriviallyNormedField F] [ProperSpace F] [TopologicalSpace G] [Fintype ι]
    (w : ι → F) (D : ι → G → ι → F) (hD : ∀ i j, Continuous (fun y => D i y j))
    (d : ℕ → ι → F) (hd : Tendsto d atTop (𝓝 0))
    (hexpand : ∀ n : ℕ, ∃ i y, 1 < ‖w i‖ ∧ ∑ j, d n j * D i y j ≠ 0) :
    ∃ (m φ : ℕ → ℕ) (x : G) (v : ι → F), Tendsto m atTop atTop ∧ StrictMono φ ∧
      Tendsto (fun p : ℕ × G => fun i => w i ^ m (φ p.1) * ∑ j, d (φ p.1) j * D i p.2 j)
        (atTop ×ˢ 𝓝 x) (𝓝 v) ∧ ∃ i, 1 < ‖w i‖ ∧ v i ≠ 0 := by
  classical
  let E (i : ι) : (ι → F) →ₗ[F] (G → F) :=
    { toFun := fun z y => ∑ j, z j * D i y j
      map_add' := by
        intro z z'
        ext y
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro t z
        ext y
        simp [mul_assoc, Finset.mul_sum] }
  let κ (i : ι) := Fin (Module.finrank F (LinearMap.range (E i)))
  let B (i : ι) : Module.Basis (κ i) F (LinearMap.range (E i)) := Module.finBasis F _
  let e : (ι → F) → (i : ι) × κ i → F := fun z k =>
    (B k.1).equivFun ((E k.1).rangeRestrict z) k.2
  have he (i : ι) (z : ι → F) (y : G) :
      ∑ j : κ i, e z ⟨i, j⟩ * ((B i j).val y) = ∑ j, z j * D i y j := by
    have h := congrArg (fun q : LinearMap.range (E i) => q.val y)
      ((B i).sum_equivFun ((E i).rangeRestrict z))
    change _ = ((E i).rangeRestrict z).val y
    simpa only [e, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using h
  have hc (i : ι) (j : κ i) : Continuous (fun y => (B i j).val y) := by
    obtain ⟨z, hz⟩ := (B i j).property
    rw [← hz]
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (hD i k)
  have hecont : Continuous e := by
    refine continuous_pi fun k => ?_
    let L : (ι → F) →ₗ[F] F :=
      (LinearMap.proj k.2).comp ((B k.1).equivFun.toLinearMap.comp (E k.1).rangeRestrict)
    exact L.continuous_of_finiteDimensional
  have hde : Tendsto (e ∘ d) atTop (𝓝 0) := by
    have ht := hecont.continuousAt.tendsto.comp hd
    have hzero : e 0 = 0 := by ext k; simp [e]
    rwa [hzero] at ht
  have hex : ∀ n, ∃ k : (i : ι) × κ i, 1 < ‖w k.1‖ ∧ (e ∘ d) n k ≠ 0 := by
    intro n
    obtain ⟨i, y, hi, hiy⟩ := hexpand n
    by_contra! h
    apply hiy
    rw [← he i (d n) y]
    exact Finset.sum_eq_zero fun j _ => mul_eq_zero.mpr (Or.inl (h ⟨i, j⟩ hi))
  obtain ⟨m, φ, b, hm, hφ, hb, _, _, k, hk, hbk⟩ :=
    exists_rescaled_coordinates (fun k : (i : ι) × κ i => w k.1) (e ∘ d) hde hex zero_lt_one
  let v (y : G) (i : ι) : F := ∑ j : κ i, b ⟨i, j⟩ * (B i j).val y
  have hv : ∃ x, v x k.1 ≠ 0 := by
    by_contra! h
    let z : LinearMap.range (E k.1) := ∑ j : κ k.1, b ⟨k.1, j⟩ • B k.1 j
    have hz : z = 0 := by
      apply Subtype.ext
      funext y
      simpa [z, v, Submodule.coe_sum] using h y
    have hrepr := congrFun ((B k.1).repr_sum_self (fun j => b ⟨k.1, j⟩)) k.2
    change (B k.1).repr z k.2 = b k at hrepr
    exact hbk (hrepr.symm.trans (by simp [hz]))
  obtain ⟨x, hx⟩ := hv
  refine ⟨m, φ, x, v x, hm, hφ, ?_, ⟨k.1, hk, hx⟩⟩
  refine tendsto_pi_nhds.mpr fun i => ?_
  have hconv :
      Tendsto (fun p : ℕ × G =>
        ∑ j : κ i, (w i ^ m (φ p.1) * e (d (φ p.1)) ⟨i, j⟩) * (B i j).val p.2)
        (atTop ×ˢ 𝓝 x) (𝓝 (v x i)) := by
    apply tendsto_finsetSum
    intro j _
    exact (((continuous_apply (⟨i, j⟩ : (i : ι) × κ i)).continuousAt.tendsto.comp hb).comp
      tendsto_fst).mul ((hc i j).continuousAt.tendsto.comp tendsto_snd)
  refine hconv.congr fun p => ?_
  simp only [mul_assoc, ← Finset.mul_sum, he]

/-- A closed matrix coordinate embedding, its conjugation action, and an
expansion direction for a small subgroup sequence suffice for rescaling. -/
private theorem conjugates_mem_of_expanding_coordinates
    {F G ι : Type*} [NontriviallyNormedField F] [ProperSpace F]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Fintype ι]
    {H : Subgroup G} (hH : IsClosed (H : Set G))
    {ν : Measure (RightCosets H)} [IsFiniteMeasure ν]
    {hν : RightInvariant ν} (hν₀ : ν ≠ 0) {a : G} (hmix : QuotientMixing hν a)
    (q : G → ι → F) (hq : IsClosedEmbedding q) (hq1 : q 1 = 0)
    (w : ι → F) (hw : ∀ g i, q (a⁻¹ * g * a) i = w i * q g i)
    (D : ι → G → ι → F) (hD : ∀ i j, Continuous (fun y => D i y j))
    (hconj : ∀ y g i, q (y⁻¹ * g * y) i = ∑ j, q g j * D i y j)
    (h : ℕ → G) (hh : ∀ n, h n ∈ H) (ht : Tendsto h atTop (𝓝 1))
    (hexpand : ∀ n, ∃ i y, 1 < ‖w i‖ ∧ q (y⁻¹ * h n * y) i ≠ 0) :
    ∃ x u : G, u ∉ Subgroup.center G ∧ ∀ g : G, x * (g * u * g⁻¹) * x⁻¹ ∈ H := by
  have : SecondCountableTopology G := hq.isEmbedding.secondCountableTopology
  have hpow (m : ℕ) (g : G) (i : ι) : q ((a ^ m)⁻¹ * g * a ^ m) i = w i ^ m * q g i := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ a]
      have heq : (a ^ m * a)⁻¹ * g * (a ^ m * a) =
          a⁻¹ * ((a ^ m)⁻¹ * g * a ^ m) * a := by group
      rw [heq, hw, ih, pow_succ']
      exact (mul_assoc _ _ _).symm
  have hq0 : Tendsto (q ∘ h) atTop (𝓝 0) :=
    hq1 ▸ hq.continuous.continuousAt.tendsto.comp ht
  obtain ⟨m, φ, x, v, hm, hφ, hlim, i, hwi, hvi⟩ :=
    exists_stable_rescaled_coordinates w D hD (q ∘ h) hq0 (by simpa [hconj] using hexpand)
  let r (p : ℕ × G) :=
    (a ^ m (φ p.1))⁻¹ * (p.2⁻¹ * h (φ p.1) * p.2) * a ^ m (φ p.1)
  have hl : Tendsto (q ∘ r) (atTop ×ˢ 𝓝 x) (𝓝 v) := by
    exact hlim.congr (fun p => funext fun j => by simp only [Function.comp_apply, r, hpow, hconj])
  obtain ⟨u, rfl⟩ := hq.isClosed_range.mem_of_tendsto hl
    (Eventually.of_forall fun p => mem_range_self (r p))
  refine ⟨x, u, ?_, fun g => conjugates_mem_of_rescaled_limit hH hν₀ hmix
    (fun n => hh (φ n)) (hm.comp hφ.tendsto_atTop) (hq.isEmbedding.tendsto_nhds_iff.mpr hl) g⟩
  intro huc
  have hcomm := Subgroup.mem_center_iff.mp huc a
  have heq : a⁻¹ * u * a = u := by
    rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hwui := hw u i
  rw [heq, ← one_mul (q u i)] at hwui
  have hwi' : (1 : F) = w i := by
    apply mul_right_cancel₀ hvi
    simpa only [one_mul] using hwui
  exact (not_lt_of_ge (by simp [← hwi'])) hwi

section MatrixCoordinates

open Matrix

variable {F I : Type*} [NontriviallyNormedField F] [Fintype I] [DecidableEq I]

/-- Coordinates of a matrix and its inverse, both shifted to vanish at the identity. -/
private def matrixPairCoordinates :
    (Matrix I I F × (Matrix I I F)ᵐᵒᵖ) ≃ₜ (Bool × (I × I) → F) where
  toFun p k := (if k.1 then MulOpposite.unop p.2 else p.1) k.2.1 k.2.2 -
    (1 : Matrix I I F) k.2.1 k.2.2
  invFun z := (fun i j => z (false, i, j) + (1 : Matrix I I F) i j,
    MulOpposite.op fun i j => z (true, i, j) + (1 : Matrix I I F) i j)
  left_inv p := by
    apply Prod.ext
    · ext i j
      simp
    · apply MulOpposite.unop_injective
      ext i j
      simp
  right_inv z := by
    funext k
    rcases k with ⟨b, i, j⟩
    cases b <;> exact add_sub_cancel_right _ _
  continuous_toFun := by
    apply continuous_pi
    rintro ⟨b, i, j⟩
    cases b
    · exact (continuous_fst.matrix_elem i j).sub continuous_const
    · exact ((MulOpposite.continuous_unop.comp continuous_snd).matrix_elem i j).sub continuous_const
  continuous_invFun := by
    refine (continuous_matrix fun i j => (continuous_apply (false, i, j)).add continuous_const).prodMk
      (MulOpposite.continuous_op.comp (continuous_matrix fun i j =>
        (continuous_apply (true, i, j)).add continuous_const))

private theorem conjugates_mem_of_diagonal
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ProperSpace F]
    {H : Subgroup G} (hH : IsClosed (H : Set G))
    {ν : Measure (RightCosets H)} [IsFiniteMeasure ν]
    {hν : RightInvariant ν} (hν₀ : ν ≠ 0) {a : G} (hmix : QuotientMixing hν a)
    (ρ : G →* Matrix.GeneralLinearGroup I F) (hρ : IsClosedEmbedding ρ)
    (d : I → Fˣ) (ha : (ρ a).val = diagonal fun i => (d i : F))
    (h : ℕ → G) (hh : ∀ n, h n ∈ H) (ht : Tendsto h atTop (𝓝 1))
    (hexpand : ∀ n, ∃ (i j : I) (y : G), 1 < ‖(d i : F)⁻¹ * (d j : F)‖ ∧
      (ρ (y⁻¹ * h n * y)).val i j ≠ 0) :
    ∃ x u : G, u ∉ Subgroup.center G ∧ ∀ g : G, x * (g * u * g⁻¹) * x⁻¹ ∈ H := by
  let q : G → Bool × (I × I) → F :=
    matrixPairCoordinates ∘ Units.embedProduct (Matrix I I F) ∘ ρ
  let M (g : G) (b : Bool) : Matrix I I F := if b then (ρ g⁻¹).val else (ρ g).val
  have hq (g : G) (b : Bool) (i j : I) : q g (b, i, j) = (M g b - 1) i j := by
    cases b <;> simp [q, matrixPairCoordinates, M, Units.embedProduct_apply, map_inv]
  have hqemb : IsClosedEmbedding q := matrixPairCoordinates.isClosedEmbedding.comp
    (Units.isClosedEmbedding_embedProduct.comp hρ)
  have hM (y g : G) (b : Bool) : M (y⁻¹ * g * y) b =
      (ρ y⁻¹).val * M g b * (ρ y).val := by
    have hinv : (y⁻¹ * g * y)⁻¹ = y⁻¹ * g⁻¹ * y := by group
    cases b <;> simp only [M, Bool.false_eq_true, ite_false, ite_true, hinv, map_mul, Units.val_mul]
  have hI (y : G) : (ρ y⁻¹).val * 1 * (ρ y).val = 1 := by
    rw [mul_one, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
  have hconj (y g : G) (b : Bool) : M (y⁻¹ * g * y) b - 1 =
      (ρ y⁻¹).val * (M g b - 1) * (ρ y).val := by
    rw [hM, mul_sub, sub_mul, hI]
  let w (k : Bool × (I × I)) : F := (d k.2.1 : F)⁻¹ * (d k.2.2 : F)
  let A (k : Bool × (I × I)) (y : G) (l : Bool × (I × I)) : F :=
    if l.1 = k.1 then (ρ y⁻¹).val k.2.1 l.2.1 * (ρ y).val l.2.2 k.2.2 else 0
  have hA (k l : Bool × (I × I)) : Continuous (fun y => A k y l) := by
    by_cases hkl : l.1 = k.1
    · have h₁ := (continuous_apply l.2.1).comp
        (Matrix.GeneralLinearGroup.continuous_apply (fun y => ρ y⁻¹)
          (hρ.continuous.comp continuous_inv) k.2.1)
      have h₂ := (continuous_apply k.2.2).comp
        (Matrix.GeneralLinearGroup.continuous_apply ρ hρ.continuous l.2.2)
      simp only [A, hkl, ite_true]
      exact continuous_mul.comp (h₁.prodMk h₂)
    · simpa [A, hkl] using (continuous_const : Continuous (fun _ : G => (0 : F)))
  refine conjugates_mem_of_expanding_coordinates hH hν₀ hmix q hqemb ?_ w ?_ A hA ?_ h hh ht ?_
  · funext k
    rcases k with ⟨b, i, j⟩
    rw [hq]
    cases b <;> simp [M]
  · intro g k
    rcases k with ⟨b, i, j⟩
    let diag := Units.map (Matrix.diagonalRingHom (n := I) (α := F)).toMonoidHom
    let dd : (I → F)ˣ := MulEquiv.piUnits.symm d
    have hd : ρ a = diag dd := Units.ext ha
    have hai : (ρ a⁻¹).val = diagonal fun z => (d z : F)⁻¹ := by
      rw [map_inv, hd, ← map_inv]
      change diagonal (fun z => (↑((d z)⁻¹) : F)) = _
      simp only [Units.val_inv_eq_inv_val]
    rw [hq, hq, hconj, ha, hai, mul_diagonal, diagonal_mul]
    change (d i : F)⁻¹ * (M g b - 1) i j * (d j : F) =
      ((d i : F)⁻¹ * (d j : F)) * (M g b - 1) i j
    ac_rfl
  · intro y g k
    rcases k with ⟨b, i, j⟩
    rw [hq, hconj]
    simp only [Fintype.sum_prod_type, A]
    cases b <;> simp [hq, Matrix.mul_apply, Finset.sum_mul] <;>
      rw [Finset.sum_comm] <;> exact Finset.sum_congr rfl (fun _ _ =>
        Finset.sum_congr rfl fun _ _ => by ac_rfl)
  · intro n
    obtain ⟨i, j, y, hw, hv⟩ := hexpand n
    have hne : i ≠ j := by
      rintro rfl
      simp [Units.ne_zero] at hw
    exact ⟨(false, i, j), y, hw, by
      rw [hq]
      simpa [M, Matrix.one_apply_ne hne] using hv⟩

/-- It suffices that the common centralizer of the conjugates of the diagonal
element be finite, and that unequal diagonal eigenvalues have distinct norms. -/
private theorem conjugates_mem_of_finite_common_centralizer
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ProperSpace F]
    {H : Subgroup G} (hH : IsClosed (H : Set G)) (hnd : ¬ DiscreteTopology H)
    {ν : Measure (RightCosets H)} [IsFiniteMeasure ν]
    {hν : RightInvariant ν} (hν₀ : ν ≠ 0) {a : G} (hmix : QuotientMixing hν a)
    (ρ : G →* Matrix.GeneralLinearGroup I F) (hρ : IsClosedEmbedding ρ)
    (d : I → Fˣ) (ha : (ρ a).val = diagonal fun i => (d i : F))
    (hd : ∀ i j, ‖(d i : F)‖ = ‖(d j : F)‖ → d i = d j)
    (hfin : {z : G | ∀ y : G, Commute a (y⁻¹ * z * y)}.Finite) :
    ∃ x u : G, u ∉ Subgroup.center G ∧ ∀ g : G, x * (g * u * g⁻¹) * x⁻¹ ∈ H := by
  have hE := matrixPairCoordinates.isClosedEmbedding.comp (Units.isClosedEmbedding_embedProduct.comp hρ)
  have : SecondCountableTopology G := hE.isEmbedding.secondCountableTopology
  have : T2Space G := hρ.isEmbedding.t2Space
  obtain ⟨h, hh, ht⟩ := exists_small_sequence_avoiding_finite H hnd hfin
  let P (n : ℕ) := ∃ (i j : I) (y : G), ‖(d i : F)‖ < ‖(d j : F)‖ ∧
    (ρ (y⁻¹ * h n * y)).val i j ≠ 0
  let Q (n : ℕ) := ∃ (i j : I) (y : G), ‖(d j : F)‖ < ‖(d i : F)‖ ∧
    (ρ (y⁻¹ * h n * y)).val i j ≠ 0
  have hPQ (n : ℕ) : P n ∨ Q n := by
    obtain ⟨y, hy⟩ : ∃ y : G, ¬ Commute a (y⁻¹ * h n * y) := not_forall.mp (hh n).2
    let g := y⁻¹ * h n * y
    have he : ∃ i j : I, d i ≠ d j ∧ (ρ g).val i j ≠ 0 := by
      by_contra! hzero
      apply hy
      change a * g = g * a
      apply hρ.injective
      rw [map_mul ρ a g, map_mul ρ g a]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, ha]
      ext i j
      rw [diagonal_mul, mul_diagonal]
      by_cases hval : d i = d j
      · rw [hval, mul_comm]
      · rw [hzero i j hval, mul_zero, zero_mul]
    obtain ⟨i, j, hij, hm⟩ := he
    rcases lt_or_gt_of_ne (fun hn => hij (hd i j hn)) with hlt | hgt
    · exact Or.inl ⟨i, j, y, hlt, hm⟩
    · exact Or.inr ⟨i, j, y, hgt, hm⟩
  have hnorm (i j : I) (hij : ‖(d i : F)‖ < ‖(d j : F)‖) :
      1 < ‖(d i : F)⁻¹ * (d j : F)‖ := by
    rw [norm_mul, norm_inv, ← div_eq_inv_mul]
    exact (one_lt_div₀ (norm_pos_iff.mpr (d i).ne_zero)).mpr hij
  by_cases hp : ∃ᶠ n in atTop, P n
  · obtain ⟨φ, hφ, hP⟩ := extraction_of_frequently_atTop hp
    refine conjugates_mem_of_diagonal hH hν₀ hmix ρ hρ d ha (h ∘ φ)
      (fun n => (hh (φ n)).1) (ht.comp hφ.tendsto_atTop) fun n => ?_
    obtain ⟨i, j, y, hij, hne⟩ := hP n
    exact ⟨i, j, y, hnorm i j hij, hne⟩
  · have hq : ∀ᶠ n in atTop, Q n := by
      filter_upwards [not_frequently.mp hp] with n hn
      exact (hPQ n).resolve_left hn
    obtain ⟨φ, hφ, hQ⟩ := extraction_of_frequently_atTop hq.frequently
    let dinv (i : I) := (d i)⁻¹
    have ha' : (ρ a⁻¹).val = diagonal fun i => (dinv i : F) := by
      let diag := Units.map (Matrix.diagonalRingHom (n := I) (α := F)).toMonoidHom
      let dd : (I → F)ˣ := MulEquiv.piUnits.symm d
      have heq : ρ a = diag dd := Units.ext ha
      rw [map_inv, heq, ← map_inv]
      rfl
    refine conjugates_mem_of_diagonal hH hν₀ (quotientMixing_inv hmix) ρ hρ dinv ha' (h ∘ φ)
      (fun n => (hh (φ n)).1) (ht.comp hφ.tendsto_atTop) fun n => ?_
    obtain ⟨i, j, y, hij, hne⟩ := hQ n
    refine ⟨i, j, y, ?_, hne⟩
    simpa [dinv, Units.val_inv_eq_inv_val, mul_comm] using hnorm j i hij

end MatrixCoordinates

section MixingAndCentralizers

private theorem rescaling_of_diagonal_mixing
    {F I G : Type*} [NontriviallyNormedField F] [ProperSpace F] [Fintype I] [DecidableEq I]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsClosed (H : Set G)) (hnd : ¬ DiscreteTopology H)
    {ν : Measure (RightCosets H)} [IsFiniteMeasure ν]
    {hν : RightInvariant ν} (hν₀ : ν ≠ 0) {a : G} (hmix : QuotientMixing hν a)
    (ρ : G →* Matrix.GeneralLinearGroup I F) (hρ : IsClosedEmbedding ρ)
    (d : I → Fˣ) (hd : (ρ a).val = Matrix.diagonal fun i => (d i : F))
    (hnorm : ∀ i j, ‖(d i : F)‖ = ‖(d j : F)‖ → d i = d j)
    (hcentre : (Subgroup.center G : Set G).Finite)
    (hfin : a ∉ Subgroup.center G → {z : G | ∀ y : G, Commute a (y⁻¹ * z * y)}.Finite) :
    ∃ x u : G, u ∉ Subgroup.center G ∧ ∀ g : G, x * (g * u * g⁻¹) * x⁻¹ ∈ H := by
  by_cases ha : a ∈ Subgroup.center G
  · have hE := matrixPairCoordinates.isClosedEmbedding.comp
      (Units.isClosedEmbedding_embedProduct.comp hρ)
    have : SecondCountableTopology G := hE.isEmbedding.secondCountableTopology
    have : T2Space G := hE.isEmbedding.t2Space
    have : Finite (Subgroup.center G) := hcentre
    let b : Subgroup.center G := ⟨a, ha⟩
    have hpow : a ^ orderOf b = 1 := congrArg Subtype.val (pow_orderOf_eq_one b)
    have htop := subgroup_eq_top_of_periodic_mixing hH hν₀ hmix (orderOf_pos b) hpow
    obtain ⟨s, hs, _⟩ := exists_small_sequence_avoiding_finite H hnd hcentre
    exact ⟨1, s 0, (hs 0).2, fun g => htop.symm ▸ Subgroup.mem_top _⟩
  · exact conjugates_mem_of_finite_common_centralizer hH hnd hν₀ hmix ρ hρ d hd hnorm (hfin ha)

private theorem finite_centralizers_of_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (hcentre : (Subgroup.center G' : Set G').Finite)
    (hcore : ∀ a : G', a ∉ Subgroup.center G' →
      {z : G' | ∀ y : G', Commute a (y⁻¹ * z * y)}.Finite) :
    (Subgroup.center G : Set G).Finite ∧
      ∀ a : G, a ∉ Subgroup.center G →
        {z : G | ∀ y : G, Commute a (y⁻¹ * z * y)}.Finite := by
  have he (g : G) : e g ∈ Subgroup.center G' ↔ g ∈ Subgroup.center G := by
    constructor
    · intro h
      exact Subgroup.mem_center_iff.mpr fun z => e.injective (by
        simpa only [map_mul] using Subgroup.mem_center_iff.mp h (e z))
    · intro h
      apply Subgroup.mem_center_iff.mpr
      intro z
      obtain ⟨y, rfl⟩ := e.surjective z
      simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp h y)
  refine ⟨(hcentre.preimage e.injective.injOn).subset (fun g hg => (he g).mpr hg), ?_⟩
  intro a ha
  have ha' : e a ∉ Subgroup.center G' := fun h => ha ((he a).mp h)
  refine ((hcore (e a) ha').preimage e.injective.injOn).subset ?_
  intro z hz
  change ∀ y, Commute (e a) (y⁻¹ * e z * y)
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom] using (hz x).map e.toMonoidHom

end MixingAndCentralizers

section RationalPoints

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization)
open Specs.StandardGroups (GLCoordinates universalMatrix)
open Specs.Unipotent (Index)
open AdelicGroups (asMatrix PointsIn)
open LocalAlgebraicTransport (RationalPoints pointTopology rationalPointTopologicalGroup)

open private asMatrix_isClosedEmbedding matrixPresentation continuous_glEvaluation
  from LinearAlgebraicGroups.Arithmetic.AdelicGroups
open private glEvaluation glEvaluation_entry from LinearAlgebraicGroups.Affine.StandardGroups
open private coordinateMap coordinateMap_spec from LinearAlgebraicGroups.Arithmetic.IntegralModels

universe u

set_option backward.isDefEq.respectTransparency false in
private theorem matrixTopology_eq_pointTopology
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    {J : AffineAlgebraicGroup F} (i : MatrixRealization J) :
    TopologicalSpace.induced (i.onPoints : RationalPoints J.val.X → _)
      inferInstance = pointTopology J.val.X := by
  let P := RationalPoints J.val.X
  let r : P →* Matrix.GeneralLinearGroup (Index.{u} i.size) F := i.onPoints
  obtain ⟨A, ⟨e⟩⟩ := essImage_algSpec.mpr J.property.1
  obtain ⟨a, ha, hmat⟩ := matrixPresentation A.unop e i
  let f := e.hom.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of A.unop)).hom
  have hf : Function.Surjective f := (ConcreteCategory.bijective_of_isIso f).2
  have heval (p : P) (b : Γ(J.val.X.left, ⊤)) :
      LocalAlgebraicTransport.evaluation p b =
        (coordinateMap (k := F) (p ≫ e.inv)).hom (f b) := by
    let cp := coordinateMap (k := F) (p ≫ e.inv)
    have hp : p.left = Spec.map (CommRingCat.ofHom cp.hom.toRingHom) ≫ e.hom.left := by
      have hh := congrArg (fun p => p.left) (coordinateMap_spec (p ≫ e.inv))
      change Spec.map (CommRingCat.ofHom cp.hom.toRingHom) = p.left ≫ e.inv.left at hh
      rw [hh, Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.comp_id]
    unfold LocalAlgebraicTransport.evaluation
    rw [hp, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]
    rfl
  have hcoord (p : P) (v : GLCoordinates F (Index.{u} i.size)) (b : Γ(J.val.X.left, ⊤))
      (hb : a.hom v = f b) :
      glEvaluation (r p) v = LocalAlgebraicTransport.evaluation p b := by
    rw [heval, ← hb]
    exact DFunLike.congr_fun (hmat F (show PointsIn i F from p)) v
  change TopologicalSpace.induced r inferInstance = pointTopology J.val.X
  apply le_antisymm
  · let : TopologicalSpace P := TopologicalSpace.induced r inferInstance
    change _ ≤ TopologicalSpace.induced _ inferInstance
    apply continuous_iff_le_induced.mp
    apply continuous_pi
    intro b
    obtain ⟨v, hv⟩ := ha (f b)
    exact ((continuous_glEvaluation v).comp continuous_induced_dom).congr
      fun p => hcoord p v b hv
  · let := pointTopology J.val.X
    have : IsTopologicalGroup P := rationalPointTopologicalGroup J
    have hcont : Continuous (fun p : P => (r p).val) := by
      apply continuous_matrix
      intro j k
      let v := universalMatrix F (Index.{u} i.size) j k
      obtain ⟨b, hb⟩ := hf (a.hom v)
      have hcont' : Continuous (fun p : P => LocalAlgebraicTransport.evaluation p b) :=
        (continuous_apply b).comp continuous_induced_dom
      exact hcont'.congr fun p => (hcoord p v b hb.symm).symm.trans (glEvaluation_entry _ j k)
    apply continuous_iff_le_induced.mp
    exact Units.continuous_iff.mpr ⟨hcont, (hcont.comp continuous_inv).congr fun p => map_inv r p ▸ rfl⟩

private theorem rationalMatrixClosedEmbedding
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    {J : AffineAlgebraicGroup F} (i : MatrixRealization J) :
    @IsClosedEmbedding (RationalPoints J.val.X) _ (pointTopology J.val.X) _
      (fun p => i.onPoints p) := by
  rw [← matrixTopology_eq_pointTopology i]
  exact asMatrix_isClosedEmbedding i F

open Specs.GeometricRadicals (IsSplitTorus)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (pairing characterValue)
open Specs.RootWeightAction (Representation mem_weightSpace extendVector act)
open Specs.AdjointRepresentation (GroupPoints)
open CocharacterDynamics (cocharacterPoint)
open private exists_weightBasis basisMatrix matrixInBasis matrixInBasis_entry
  from LinearAlgebraicGroups.Arithmetic.SteinbergFundamentalTraces

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalizes_cocharacter
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    {J : AffineAlgebraicGroup F} (i : MatrixRealization J)
    (S : Specs.ClosedSubgroup J.val) (hS : IsSplitTorus S.group)
    (c : Cocharacter S.group) (t : Fˣ) :
    letI := pointTopology J.val.X
    let a : RationalPoints J.val.X := cocharacterPoint (c ≫ S.inclusion) (CommAlgCat.of F F) t
    ∃ (r : RationalPoints J.val.X →* Matrix.GeneralLinearGroup (Index.{u} i.size) F)
      (d : Index.{u} i.size → ℤ), IsClosedEmbedding (fun p => r p) ∧
      (r a).val = Matrix.diagonal (fun j => ((t ^ d j : Fˣ) : F)) := by
  classical
  let T := pointTopology J.val.X
  let I := Index.{u} i.size
  let R := CommAlgCat.of F F
  let P := RationalPoints J.val.X
  let ρ : Representation J.val I := (groupPointsFunctor F).map i.embedding ≫ i.matrix.hom
  obtain ⟨b, χ, hb, _⟩ := exists_weightBasis ρ S hS
  let B := basisMatrix b
  let r : P →* Matrix.GeneralLinearGroup I F :=
    (MulAut.conj B⁻¹).toMonoidHom.comp i.onPoints
  let U : Matrix.GeneralLinearGroup I F ≃ₜ Matrix.GeneralLinearGroup I F :=
    (Homeomorph.mulLeft B⁻¹).trans (Homeomorph.mulRight B)
  let d (j : I) : ℤ := pairing S.group (χ j) c
  refine ⟨r, d, ?_, ?_⟩
  · have he : (fun p : P => r p) = U ∘ (fun p => i.onPoints p) := by
      funext p
      change B⁻¹ * i.onPoints p * (B⁻¹)⁻¹ = B⁻¹ * i.onPoints p * B
      rw [inv_inv]
    rw [he]
    exact U.isClosedEmbedding.comp (rationalMatrixClosedEmbedding i)
  · let a : GroupPoints J.val R := cocharacterPoint (c ≫ S.inclusion) R t
    have hact (j : I) : act ρ R a (extendVector R (b j)) =
        ((t ^ d j : Fˣ) : F) • (b j) := by
      have h := mem_weightSpace.mp (hb j) R (cocharacterPoint c R t)
      have hR (v : I → F) : extendVector R v = v := by
        funext k
        simp [extendVector, R]
      have he := (RootData.CharacterPairing.characterPairingComposition S.group (χ j) c).2 R t
      rw [hR, he] at h
      exact h
    ext p q
    change matrixInBasis b ρ R a p q = _
    rw [matrixInBasis_entry, hact]
    have hsum : ∑ l : I, b.repr ((Pi.basisFun F I) l) p * b q l =
        b.repr (b q) p := by
      have h := congrArg (fun v => b.coord p v) ((Pi.basisFun F I).sum_equivFun (b q))
      simpa only [Pi.basisFun_equivFun, LinearEquiv.refl_apply, map_sum, map_smul,
        Finset.sum_apply, Module.Basis.coord_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using h
    simp only [R, CommAlgCat.coe_of, Algebra.algebraMap_self, RingHom.id_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [show (∑ l : I, b.repr ((Pi.basisFun F I) l) p * (((t ^ d q : Fˣ) : F) * b q l)) =
        ((t ^ d q : Fˣ) : F) * ∑ l : I, b.repr ((Pi.basisFun F I) l) p * b q l by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ac_rfl]
    rw [hsum, Module.Basis.repr_self_apply]
    by_cases h : p = q <;> simp [h, eq_comm]

end RationalPoints

section AlgebraicCentralizers

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.GrpObj
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme ClosedSubgroup)
open Specs.GeometricRadicals (IsSemisimple IsReductive GeometricGroup IsSmoothConnectedNormal)
open Specs.Arithmetic.RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open Specs.Relative.RationalDensity (rationalPointOver)
open Specs.FiniteWordClosure (ConjugationStable power wordDomain)
open Specs.CentralTorus (IsSchemeCentre)

open private reductive_of_semisimple from LinearAlgebraicGroups.Classification.CentralIsogenies
open private isReduced_of_smooth_over_field from LinearAlgebraicGroups.Affine.SmoothnessCriteria
open private finite_rationalSections from LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private dense_rationalSectionValues from LinearAlgebraicGroups.Relative.RationalDensity
open private pointCentralizerExists scalarExtendedRationalPoint_value
  from LinearAlgebraicGroups.Arithmetic.RationalStronglyRegularElements
open private scalarPointHom from LinearAlgebraicGroups.Arithmetic.QuasiSplitFixedWeyl
open private scalarExtended_point_injective from LinearAlgebraicGroups.RootData.RankOneFlag
open private affine_tensor affine_power from LinearAlgebraicGroups.Solvable.FiniteWordClosure
open private power_geometry from LinearAlgebraicGroups.Solvable.SchemeDerivedGroup
open private geometricallyIrreducible_of_connected smooth_geometricallyIrreducible_tensor
  geometry_of_smooth_geometricallyIrreducible from LinearAlgebraicGroups.Solvable.WordDomainGeometry

private theorem eq_of_dense_section_values {k : Type u} [Field k] {X Y : SchemeOver k}
    [IsReduced X.left] [IsSeparated Y.hom] {idx : Type*} (s : idx → (𝟙_ (SchemeOver k) ⟶ X))
    (hs : Dense (Set.range fun i => (s i).left (IsLocalRing.closedPoint k)))
    {f g : X ⟶ Y} (h : ∀ i, s i ≫ f = s i ≫ g) : f = g := by
  let e := equalizer.ι f.left g.left
  have hcomp (i : idx) : (s i).left ≫ f.left = (s i).left ≫ g.left :=
    congrArg (fun a => a.left) (h i)
  have hd : IsDominant e := ⟨hs.mono (by
    rintro _ ⟨i, rfl⟩
    refine ⟨equalizer.lift (s i).left (hcomp i) (IsLocalRing.closedPoint k), ?_⟩
    change (equalizer.lift (s i).left (hcomp i) ≫ e) (IsLocalRing.closedPoint k) = _
    rw [equalizer.lift_ι])⟩
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated Y.hom (by rw [Over.w f, Over.w g]) e
    (equalizer.condition _ _)

private abbrev SectionGroup {k : Type u} [Field k] (G : GroupScheme k) :=
  (𝟙_ (SchemeOver k)) ⟶ G.X

private theorem toUnit_unit (k : Type u) [Field k] :
    toUnit (𝟙_ (SchemeOver k)) = 𝟙 (𝟙_ (SchemeOver k)) := toUnit_unique _ _

private theorem finite_center_sections {k : Type u} [Field k] [IsAlgClosed k] [Infinite k]
    (J : AffineAlgebraicGroup k) (hJ : IsSemisimple J) :
    (Subgroup.center (SectionGroup J.val) : Set (SectionGroup J.val)).Finite := by
  letI := J.property.1
  letI := hJ.1
  have : IsReduced J.val.X.left := isReduced_of_smooth_over_field J.val.X.hom
  let whole : ClosedSubgroup J.val := ⟨J.val, 𝟙 _, by change IsClosedImmersion (𝟙 _); infer_instance⟩
  obtain ⟨Z, hZ⟩ := LinearAlgebraicGroups.centralizerScheme k J whole
  have hcentre : IsSchemeCentre Z := hZ
  have hred := reductive_of_semisimple J hJ
  have : IsFinite Z.group.X.hom :=
    (Reductive.CentralDerived.semisimpleIffFiniteCentre J hred Z hcentre).mp hJ
  have : Finite (SectionGroup Z.group) := finite_rationalSections Z.group.X
  refine (Set.finite_range (fun z : SectionGroup Z.group => z ≫ Z.inclusion.hom.hom)).subset ?_
  intro z hz
  apply (hcentre _ z).mp
  have hd := dense_rationalSectionValues (X := J.val.X) id
    (Relative.RationalDensity.reductiveRationalPointsDense k J hred)
  have he : Commute (toUnit J.val.X ≫ z) (𝟙 J.val.X) := by
    apply eq_of_dense_section_values id hd
    intro g
    simpa only [MonObj.comp_mul, ← Category.assoc, comp_toUnit, toUnit_unit, Category.comp_id,
      Category.id_comp, id_eq] using
      ((Subgroup.mem_center_iff.mp hz g).symm : z * g = g * z)
  apply (centralizes_iff (𝟙 J.val) z).mpr
  intro U t q
  have hq := congrArg (fun f => q ≫ f) he.eq
  have ht : t = toUnit U := toUnit_unique t _
  change (t ≫ z) * (q ≫ 𝟙 J.val.X) = (q ≫ 𝟙 J.val.X) * (t ≫ z)
  simpa only [ht, MonObj.comp_mul, ← Category.assoc, comp_toUnit, Category.comp_id] using hq

private noncomputable def conjugacyMap {k : Type u} [Field k] {G : GroupScheme k} (a : SectionGroup G) :
    G.X ⟶ G.X := (𝟙 G.X) * (toUnit G.X ≫ a) * (𝟙 G.X)⁻¹

private theorem comp_conjugacyMap {k : Type u} [Field k] {G : GroupScheme k} {X : SchemeOver k}
    (a : SectionGroup G) (x : X ⟶ G.X) :
    x ≫ conjugacyMap a = x * (toUnit X ≫ a) * x⁻¹ := by
  simp only [conjugacyMap, MonObj.comp_mul, GrpObj.comp_inv, Category.comp_id,
    ← Category.assoc, comp_toUnit]

private theorem center_of_commuting_with_geometric_conjugates
    {k : Type u} [Field k] [IsAlgClosed k] (J : AffineAlgebraicGroup k)
    (hJ : IsSemisimple J) (hsimple : ∀ N : ClosedSubgroup J.val,
      IsSmoothConnectedNormal N → Specs.GeometricRadicals.IsTrivialSubgroup N ∨ IsIso N.inclusion)
    (a z : SectionGroup J.val) (ha : a ∉ Subgroup.center (SectionGroup J.val))
    (hc : ∀ (Y : SchemeOver k) (y : Y ⟶ J.val.X),
      Commute (y ≫ conjugacyMap a) (toUnit Y ≫ z)) :
    z ∈ Subgroup.center (SectionGroup J.val) := by
  letI := J.property.1
  letI := J.property.2.1
  letI := J.property.2.2
  letI := hJ.1
  letI : GeometricallyConnected J.val.X.hom := hJ.2.1
  have : ConnectedSpace J.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton J.val.X.hom
  have := geometricallyIrreducible_of_connected J
  let X := J.val.X ⊗ J.val.X
  let f : X ⟶ J.val.X :=
    (fst _ _ ≫ conjugacyMap a) * (snd _ _ ≫ conjugacyMap a)⁻¹
  let x₀ : 𝟙_ (SchemeOver k) ⟶ X := lift 1 1
  have hform {T : SchemeOver k} (p : T ⟶ X) :
      p ≫ f = ((p ≫ fst _ _) ≫ conjugacyMap a) * ((p ≫ snd _ _) ≫ conjugacyMap a)⁻¹ := by
    simp only [f, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
  have hx₀ : x₀ ≫ f = 1 := by
    rw [hform]
    simp only [x₀, lift_fst, lift_snd, mul_inv_cancel]
  have hf : ConjugationStable f := by
    intro T g p
    refine ⟨lift (g * (p ≫ fst _ _)) (g * (p ≫ snd _ _)), ?_⟩
    simp only [hform, lift_fst, lift_snd, comp_conjugacyMap]
    group
  obtain ⟨hXs, hXi⟩ := smooth_geometricallyIrreducible_tensor J.val.X J.val.X
  have hX : IsAffine X.left := affine_tensor (A := J.val.X) (B := J.val.X)
  have hpow (m : ℕ) : IsIntegral (power X m).left := by
    obtain ⟨hs, hi⟩ := power_geometry X m
    exact (geometry_of_smooth_geometricallyIrreducible (power X m)).2.2
  obtain ⟨N, n, w, _, hn, hdom, hfac, hmin, _⟩ :=
    FiniteWordClosure.existsFiniteWordClosure J X f x₀ hX inferInstance inferInstance hx₀ hpow hf
  have : IsIntegral (wordDomain X n).left := hpow (2 * n)
  have : IsAffine (wordDomain X n).left := affine_power (2 * n)
  have : IsAffine N.group.X.left := (Specs.Unipotent.closedSubgroupAlgebraicGroup N).property.1
  have : QuasiCompact w.left := inferInstance
  have := hdom
  have hN : IsReduced N.group.X.left := IsSchemeTheoreticallyDominant.isReduced w.left
  have : LocallyOfFiniteType N.group.X.hom :=
    (Specs.Unipotent.closedSubgroupAlgebraicGroup N).property.2.1
  have hNs := smoothOfReducedOverPerfectField k N.group hN
  have hNc : ConnectedSpace N.group.X.left := by
    apply connectedSpace_iff_univ.mpr
    rw [← w.left.denseRange.closure_eq]
    exact (isConnected_range w.left.continuous).closure
  have hNI : IsIso N.inclusion := by
    rcases hsimple N ⟨hNs, hNc, hn⟩ with ht | h
    · obtain ⟨e⟩ := ht
      exfalso
      apply ha
      apply Subgroup.mem_center_iff.mpr
      intro y
      obtain ⟨i, hi⟩ := hfac
      let p : 𝟙_ (SchemeOver k) ⟶ X := lift y 1
      let e' := (Grp.forget (SchemeOver k)).mapIso e
      have hp : p ≫ i = 1 := (cancel_mono e'.hom).mp (toUnit_unique _ _)
      have hp' : p ≫ f = 1 := by
        rw [← hi, ← Category.assoc, hp, MonObj.one_comp]
      rw [hform, show p ≫ fst _ _ = y from lift_fst _ _,
        show p ≫ snd _ _ = 1 from lift_snd _ _, comp_conjugacyMap, comp_conjugacyMap] at hp'
      have he : (toUnit (𝟙_ (SchemeOver k)) ≫ a) = a := by simp
      rw [he, inv_one, one_mul, mul_one, mul_inv_eq_iff_eq_mul, one_mul,
        mul_inv_eq_iff_eq_mul] at hp'
      exact hp'
    · exact h
  obtain ⟨C, hC⟩ := pointCentralizerExists J z
  have hfC := (hC X f).mp
    ((hc X (fst _ _)).mul_left ((hc X (snd _ _)).inv_left))
  obtain ⟨j, hj⟩ := hmin C hfC
  apply Subgroup.mem_center_iff.mpr
  intro g
  let r := inv N.inclusion ≫ j
  have hr : r ≫ C.inclusion = 𝟙 J.val := by simp [r, Category.assoc, hj]
  have hr' : r.hom.hom ≫ C.inclusion.hom.hom = 𝟙 J.val.X :=
    congrArg (fun v => v.hom.hom) hr
  have hg := (hC _ g).mpr ⟨g ≫ r.hom.hom, by simp [Category.assoc, hr']⟩
  simpa using hg.eq

private theorem commutes_of_dense_sections {k : Type u} [Field k]
    (J : AffineAlgebraicGroup k) (hs : Smooth J.val.X.hom)
    {idx : Type*} (s : idx → SectionGroup J.val)
    (hd : Dense (Set.range fun i => (s i).left (IsLocalRing.closedPoint k)))
    (f : J.val.X ⟶ J.val.X) (z : SectionGroup J.val)
    (hz : ∀ i, Commute (s i ≫ f) z) :
    ∀ (Y : SchemeOver k) (y : Y ⟶ J.val.X), Commute (y ≫ f) (toUnit Y ≫ z) := by
  letI := J.property.1
  letI := hs
  have : IsReduced J.val.X.left := isReduced_of_smooth_over_field J.val.X.hom
  have h : Commute f (toUnit J.val.X ≫ z) := by
    apply eq_of_dense_section_values s hd
    intro i
    simpa only [MonObj.comp_mul, ← Category.assoc, comp_toUnit, toUnit_unit,
      Category.id_comp] using (hz i).eq
  intro Y y
  show (y ≫ f) * (toUnit Y ≫ z) = (toUnit Y ≫ z) * (y ≫ f)
  simpa only [MonObj.comp_mul, ← Category.assoc, comp_toUnit] using
    congrArg (fun v => y ≫ v) h.eq

private theorem finite_common_centralizer_sections {k : Type u} [Field k] [Infinite k]
    (J : AffineAlgebraicGroup k) (hJ : IsAbsolutelyAlmostSimple J)
    (a : SectionGroup J.val) (ha : a ∉ Subgroup.center (SectionGroup J.val)) :
    {z : SectionGroup J.val | ∀ y : SectionGroup J.val, Commute a (y⁻¹ * z * y)}.Finite := by
  let K := AlgebraicClosure k
  let Jg := GeometricGroup J
  let E : SectionGroup J.val →* SectionGroup Jg.val := scalarPointHom (K := K) J.val
  have hi : Function.Injective E := scalarExtended_point_injective K J.val.X
  have hs : IsSemisimple Jg :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) J hJ.1.1 hJ.1.2.1).mpr hJ.1
  have hd : Dense (Set.range fun y => (E y).left (IsLocalRing.closedPoint K)) := by
    simp_rw [show ∀ y : SectionGroup J.val,
      (E y).left (IsLocalRing.closedPoint K) = rationalPointOver K y from
        fun y => scalarExtendedRationalPoint_value K y]
    exact Relative.RationalDensity.reductiveRationalPointsDense k J (reductive_of_semisimple J hJ.1)
  refine ((finite_center_sections Jg hs).preimage hi.injOn).subset ?_
  intro z hz
  change E z ∈ Subgroup.center (SectionGroup Jg.val)
  have ha' : E a ∉ Subgroup.center (SectionGroup Jg.val) := by
    intro hac
    exact ha (Subgroup.mem_center_iff.mpr fun g => hi (by
      simpa only [map_mul] using Subgroup.mem_center_iff.mp hac (E g)))
  refine center_of_commuting_with_geometric_conjugates Jg hs hJ.2.2 (E a) (E z) ha' ?_
  apply commutes_of_dense_sections Jg hs.1 E hd
  intro y
  have hcomm : Commute (y * a * y⁻¹) z := by
    change (y * a * y⁻¹) * z = z * (y * a * y⁻¹)
    calc
      _ = y * (a * (y⁻¹ * z * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * z * y) * a) * y⁻¹ := by rw [(hz y).eq]
      _ = _ := by group
  simpa only [comp_conjugacyMap, toUnit_unit, Category.id_comp, map_mul, map_inv] using
    hcomm.map E

private theorem finite_center_of_absolute_simplicity {k : Type u} [Field k] [Infinite k]
    (J : AffineAlgebraicGroup k) (hJ : IsAbsolutelyAlmostSimple J) :
    (Subgroup.center (SectionGroup J.val) : Set (SectionGroup J.val)).Finite := by
  let K := AlgebraicClosure k
  let Jg := GeometricGroup J
  let E : SectionGroup J.val →* SectionGroup Jg.val := scalarPointHom (K := K) J.val
  have hi : Function.Injective E := scalarExtended_point_injective K J.val.X
  have hs : IsSemisimple Jg :=
    (Reductive.RadicalBaseChange.semisimpleFieldExtension (K := K) J hJ.1.1 hJ.1.2.1).mpr hJ.1
  have hd : Dense (Set.range fun y => (E y).left (IsLocalRing.closedPoint K)) := by
    simp_rw [show ∀ y : SectionGroup J.val,
      (E y).left (IsLocalRing.closedPoint K) = rationalPointOver K y from
        fun y => scalarExtendedRationalPoint_value K y]
    exact Relative.RationalDensity.reductiveRationalPointsDense k J (reductive_of_semisimple J hJ.1)
  refine ((finite_center_sections Jg hs).preimage hi.injOn).subset ?_
  intro z hz
  apply Subgroup.mem_center_iff.mpr
  intro g
  have h : ∀ y, Commute (E y ≫ 𝟙 Jg.val.X) (E z) := by
    intro y
    simpa only [Category.comp_id] using
      (show Commute y z from Subgroup.mem_center_iff.mp hz y).map E
  simpa only [Category.comp_id, toUnit_unit, Category.id_comp] using
    (commutes_of_dense_sections Jg hs.1 E hd (𝟙 Jg.val.X) (E z) h _ g).eq

end AlgebraicCentralizers

section LocalField

open AlgebraicGeometry CategoryTheory Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ValuativeRel
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup GroupScheme)
open Specs.GeometricRadicals (identitySubgroup)
open LocalAlgebraicTransport
  (IsUniformizingUnit RationalPoints pointTopology rationalPointTopologicalGroup)
open CocharacterDynamics (cocharacterPoint)

open private maximalSplitTorusAbove from LinearAlgebraicGroups.Relative.RelativeWeylScheme
open private exists_regular_cocharacter from LinearAlgebraicGroups.RootData.BorelsAndChambers
open private trivial_isSplitTorus testUnitIso precompSections
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags

private noncomputable def rationalSectionEquiv {F : Type u} [Field F] (J : GroupScheme F) :
    RationalPoints J.X ≃* SectionGroup J :=
  precompSections (testUnitIso F).symm J

private theorem finite_rational_centers {F : Type u} [Field F] [Infinite F]
    (J : AffineAlgebraicGroup F)
    (hJ : Specs.Arithmetic.RelativeRootIrreducibility.IsAbsolutelyAlmostSimple J) :
    let P := RationalPoints J.val.X
    (Subgroup.center P : Set P).Finite ∧
      ∀ a : P, a ∉ Subgroup.center P → {z : P | ∀ y : P, Commute a (y⁻¹ * z * y)}.Finite :=
  finite_centralizers_of_mulEquiv (rationalSectionEquiv J.val)
    (finite_center_of_absolute_simplicity J hJ) (finite_common_centralizer_sections J hJ)

private theorem int_value_le_uniformizer (x : WithZero (Multiplicative ℤ)) (hx : x < 1) :
    x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h : x = 0
  · rw [h]
    exact zero_le
  · apply (WithZero.log_le_iff_le_exp h).mp
    have hl : WithZero.log x < (0 : ℤ) := (WithZero.log_lt_iff_lt_exp h).mpr
      (by rw [WithZero.exp_zero]; exact hx)
    exact (zero_sub (1 : ℤ)) ▸ Int.le_sub_one_of_lt hl

private theorem exists_maximal_value_below_one {F : Type*} [Field F]
    (f : F → WithZero (Multiplicative ℤ)) (hs : Function.Surjective f) (h0 : f 0 = 0) :
    ∃ π : Fˣ, f (π : F) < 1 ∧ ∀ x : F, f x < 1 → f x ≤ f (π : F) := by
  obtain ⟨p, hp⟩ := hs (WithZero.exp (-1 : ℤ))
  have hp₀ : p ≠ 0 := by
    intro h
    exact (WithZero.exp_pos (a := (-1 : ℤ))).ne' (hp.symm.trans ((congrArg f h).trans h0))
  have hlt : WithZero.exp (-1 : ℤ) < 1 :=
    WithZero.exp_lt_one_iff.mpr (Int.negSucc_lt_zero 0)
  exact ⟨Units.mk0 p hp₀, hp.symm ▸ hlt, fun x hx => hp.symm ▸ int_value_le_uniformizer (f x) hx⟩

private theorem exists_uniformizingUnit (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    ∃ π : Fˣ, IsUniformizingUnit π := by
  let w := LocalDivisionRamification.normalizedValuation F
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hlt (x : F) : w x < 1 ↔ x <ᵥ (1 : F) := by
    rw [(valuation F).vlt_iff_lt, map_one (valuation F)]
    change e (valuation F x) < 1 ↔ _
    rw [← map_one e]
    exact e.toOrderIso.lt_iff_lt
  have hle (x y : F) : w x ≤ w y ↔ x ≤ᵥ y :=
    e.toOrderIso.le_iff_le.trans (valuation F).vle_iff_le.symm
  have hs : Function.Surjective w :=
    e.surjective.comp (ValuativeRel.valuation_surjective (K := F))
  obtain ⟨π, hp, hmax⟩ := exists_maximal_value_below_one w hs (map_zero w)
  exact ⟨π, (hlt _).mp hp, fun x hx => (hle _ _).mp (hmax x ((hlt _).mpr hx))⟩

private theorem rescaling_at_uniformizer {F I G : Type*}
    [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Fintype I] [DecidableEq I] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Subgroup G} (hH : IsClosed (H : Set G)) (hnd : ¬ DiscreteTopology H)
    {ν : Measure (RightCosets H)} [IsFiniteMeasure ν]
    {hν : RightInvariant ν} (hν₀ : ν ≠ 0) {a : G} (hmix : QuotientMixing hν a)
    (ρ : G →* Matrix.GeneralLinearGroup I F) (hρ : IsClosedEmbedding ρ)
    (π : Fˣ) (hπ : IsUniformizingUnit π) (d : I → ℤ)
    (hd : (ρ a).val = Matrix.diagonal (fun i => ((π ^ d i : Fˣ) : F)))
    (hcentre : (Subgroup.center G : Set G).Finite)
    (hfin : a ∉ Subgroup.center G → {z : G | ∀ y : G, Commute a (y⁻¹ * z * y)}.Finite) :
    ∃ x u : G, u ∉ Subgroup.center G ∧ ∀ g : G, x * (g * u * g⁻¹) * x⁻¹ ∈ H := by
  let := IsTopologicalAddGroup.rightUniformSpace F
  let := isUniformAddGroup_of_addCommGroup (G := F)
  let rank := (IsRankLeOne.nonempty (R := F)).some
  let : (Valued.v (R := F) (Γ₀ := ValueGroupWithZero F)).RankOne :=
    { hom' := rank.emb.comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := rank.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  let : NontriviallyNormedField F := Valued.toNontriviallyNormedField F (ValueGroupWithZero F)
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have hnorm : ‖(π : F)‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mpr ((valuation F).vlt_iff_lt.mp hπ.1)
  have hd' (i j : I) (h : ‖((π ^ d i : Fˣ) : F)‖ = ‖((π ^ d j : Fˣ) : F)‖) :
      π ^ d i = π ^ d j := by
    have e := (zpow_right_strictAnti₀ (norm_pos_iff.mpr π.ne_zero) hnorm).injective
      (by simpa only [Units.val_zpow_eq_zpow_val, norm_zpow] using h :
        ‖(π : F)‖ ^ d i = ‖(π : F)‖ ^ d j)
    rw [e]
  exact rescaling_of_diagonal_mixing hH hnd hν₀ hmix ρ hρ (fun i => π ^ d i) hd hd' hcentre hfin

/-- Rescaling on the original measured local quotient, conditional on the
ordered local-mixing obligations. -/
theorem localRescaling_conditional.{u}
    (_exceptional : Specs.Arithmetic.LocalQuotientMixing.ExceptionalAndTrialitarianRankOne.{u})
    (mixing : Specs.Arithmetic.LocalQuotientMixing.Statement.{u})
    (_longRoot : Specs.Arithmetic.LocalQuotientMixing.LongRootRankOne.{u})
    (_fixedVector : Specs.Arithmetic.LocalQuotientMixing.UpperRootFixedVector.{u,u}) :
    Specs.Arithmetic.LocalRescaling.Statement.{u} := by
  intro F _ _ _ _ J hJ hcases
  have : Infinite (WithZero (Multiplicative ℤ)) :=
    Infinite.of_injective WithZero.exp WithZero.exp_injective
  have : Infinite F := Infinite.of_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F) ∘ ValuativeRel.valuation F)
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).surjective.comp
      (ValuativeRel.valuation_surjective (K := F)))
  let T := pointTopology J.val.X
  let P := RationalPoints J.val.X
  have : IsTopologicalGroup P := rationalPointTopologicalGroup J
  intro H hH hnd ν _ hν₀ hν
  obtain ⟨S, hS, _⟩ := maximalSplitTorusAbove J (identitySubgroup J) trivial_isSplitTorus
  obtain ⟨c, hc⟩ := exists_regular_cocharacter J S hS.1
  obtain ⟨π, hπ⟩ := exists_uniformizingUnit F
  let a : P := cocharacterPoint (c ≫ S.inclusion) (CommAlgCat.of F F) π
  have hmix : QuotientMixing hν a := mixing F J hJ hcases S hS c hc π hπ H hH ν hν₀ hν
  obtain ⟨n, L, ⟨m⟩, f, hf⟩ := LinearAlgebraicGroups.faithfulLinearization F J
  let M : Specs.IntegralModels.MatrixRealization J := ⟨n, L, m, f, hf⟩
  obtain ⟨ρ, d, hρ, hd⟩ := diagonalizes_cocharacter M S hS.1 c π
  obtain ⟨hcentre, hfin⟩ := finite_rational_centers J hJ
  exact rescaling_at_uniformizer hH hnd hν₀ hmix ρ hρ π hπ d hd hcentre (hfin a)

end LocalField

end LinearAlgebraicGroups.Arithmetic.LocalRescaling

universe v8_closure_b75a4065e922ae3d_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«LocalRescaling».«localRescaling» : _root_.«LinearAlgebraicGroups».«Specs».«Arithmetic».«LocalRescaling».«Statement».{v8_closure_b75a4065e922ae3d_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalRescaling».«localRescaling_conditional».{v8_closure_b75a4065e922ae3d_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«exceptionalAndTrialitarianRankOne».{v8_closure_b75a4065e922ae3d_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«localQuotientMixing».{v8_closure_b75a4065e922ae3d_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«longRootRankOne».{v8_closure_b75a4065e922ae3d_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«LocalQuotientMixing».«upperRootFixedVector».{v8_closure_b75a4065e922ae3d_u0, v8_closure_b75a4065e922ae3d_u0})
