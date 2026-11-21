import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch16.EntireFactorization
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.EntireZeros
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.GlobalLogarithmCriterion
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.DiskPrimitives
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalZeroFactorization

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.EntireFactorization

private lemma analytic_entire {f : ℂ → ℂ} (hf : HolomorphicOn univ f) (z : ℂ) :
    AnalyticAt ℂ f z :=
  HolomorphicProducts.analyticAt_of_holomorphic hf (mem_univ z)

/-- Units in local factorizations with a common power. -/
private lemma local_unit (f : ℂ → ℂ) (d : ℂ → ℕ) (hf : HolomorphicOn univ f)
    (ho : ∀ z, analyticOrderAt f z = (d z : ℕ∞)) (a : ℂ) :
    ∃ u : ℂ → ℂ, AnalyticAt ℂ u a ∧ u a ≠ 0 ∧
      ∀ᶠ z in 𝓝 a, f z = (z - a) ^ d a * u z := by
  simpa only [smul_eq_mul] using
    (analytic_entire hf a).analyticOrderAt_eq_natCast.mp (ho a)

theorem quotient_extension :
    Specs.D12Complex.Ch16.EntireFactorization.quotient_extension_type := by
  classical
  intro f P d hf hP hof hoP
  choose u hu hu0 hfu using local_unit f d hf hof
  choose v hv hv0 hPv using local_unit P d hP hoP
  let q : ℂ → ℂ := fun z => u z z / v z z
  have hq0 : ∀ z, q z ≠ 0 := fun z => div_ne_zero (hu0 z) (hv0 z)
  have hoff : ∀ z, P z ≠ 0 → q z = f z / P z := by
    intro z hz
    have hzord : (d z : ℕ∞) = 0 := (hoP z).symm.trans
      ((analytic_entire hP z).analyticOrderAt_eq_zero.mpr hz)
    have hd : d z = 0 := by exact_mod_cast hzord
    have hfz := (hfu z).self_of_nhds
    have hPz := (hPv z).self_of_nhds
    simp only [hd, pow_zero, one_mul] at hfz hPz
    simp only [q, ← hfz, ← hPz]
  have hlocal : ∀ a, q =ᶠ[𝓝 a] fun z => u a z / v a z := by
    intro a
    filter_upwards [hfu a, hPv a, (hv a).continuousAt.eventually_ne (hv0 a)] with z hfz hPz hvz
    by_cases hza : z = a
    · subst z; rfl
    · have hp : (z - a) ^ d a ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hza)
      rw [hoff z (by rw [hPz]; exact mul_ne_zero hp hvz), hfz, hPz]
      exact mul_div_mul_left _ _ hp
  refine ⟨q, ⟨isOpen_univ, fun a _ => ?_⟩, hq0, hoff, ?_⟩
  · exact (((hu a).differentiableAt).div (hv a).differentiableAt (hv0 a)).congr_of_eventuallyEq
      (hlocal a)
  · intro z
    by_cases hz : P z ≠ 0
    · rw [hoff z hz, div_mul_cancel₀ _ hz]
    · have hfz : f z = 0 := by
        have hzero := (analytic_entire hP z).analyticOrderAt_ne_zero.mpr (not_ne_iff.mp hz)
        rw [hoP z, ← hof z] at hzero
        exact (analytic_entire hf z).analyticOrderAt_ne_zero.mp hzero
      simp [not_ne_iff.mp hz, hfz]

theorem entire_logarithm :
    Specs.D12Complex.Ch16.EntireFactorization.entire_logarithm_type := by
  intro q hq hn
  have hd := GlobalLogarithmCriterion.holomorphicOn_logarithmicDerivative univ q hq
    (fun z _ => hn z)
  obtain ⟨H, hH⟩ := DiskPrimitives.entire_exists_primitive _ hd
  have hdom : IsDomain (univ : Set ℂ) :=
    ⟨univ_nonempty, isOpen_univ, isPreconnected_univ⟩
  obtain ⟨g, hg, he⟩ := (GlobalLogarithmCriterion.global_logarithm_criterion
    univ q hdom hq (fun z _ => hn z)).mpr (by
      intro γ hγ hc
      rw [Primitives.piecewise_endpoint univ _ H
        (fun z hz => (hd.2 z hz).continuousAt.continuousWithinAt) hH γ hγ,
        hc, sub_self])
  exact ⟨g, hg, fun z => by rw [← Exponential.E_eq_exp]; exact he z (mem_univ z)⟩

theorem zero_divisor : Specs.D12Complex.Ch16.EntireFactorization.zero_divisor_type := by
  classical
  intro f hf hnon
  have ha : AnalyticOnNhd ℂ f univ := fun z _ => analytic_entire hf z
  obtain ⟨w, hw⟩ := hnon
  have hfin : ∀ z, analyticOrderAt f z ≠ ⊤ := fun z =>
    ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ w) (mem_univ z)
      (by rw [(analytic_entire hf w).analyticOrderAt_eq_zero.mpr hw]; simp)
  let d : ℂ → ℕ := fun z => (analyticOrderAt f z).toNat
  have ho : ∀ z, analyticOrderAt f z = (d z : ℕ∞) := fun z =>
    (ENat.natCast_toNat (hfin z)).symm
  refine ⟨d, ?_, ho⟩
  intro a
  obtain ⟨u, hu, hu0, he⟩ := local_unit f d hf ho a
  have hev : ∀ᶠ z in 𝓝 a, z ≠ a → d z = 0 := by
    filter_upwards [he, hu.continuousAt.eventually_ne hu0] with z hz hzu hza
    have hfz : f z ≠ 0 := by
      rw [hz]
      exact mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr hza)) hzu
    have hd0 := (ho z).symm.trans ((analytic_entire hf z).analyticOrderAt_eq_zero.mpr hfz)
    exact_mod_cast hd0
  obtain ⟨U, hU, hprop⟩ := eventually_iff_exists_mem.mp hev
  refine ⟨U, hU, (finite_singleton a).subset ?_⟩
  intro z hz
  by_contra hza
  exact hz.2 (hprop z hz.1 (by simpa using hza))


/-- The finite canonical product has exactly the prescribed local orders. -/
private lemma finite_product_order (d : ℂ → ℕ) (s : Finset ℂ)
    (hs : ∀ z, z ∈ s ↔ z ≠ 0 ∧ d z ≠ 0) :
    let P := fun z : ℂ => z ^ d 0 *
      ∏ a ∈ s, CanonicalFactors.factor 0 (z / a) ^ d a
    HolomorphicOn univ P ∧ ∀ z, analyticOrderAt P z = (d z : ℕ∞) := by
  classical
  let v := fun a z : ℂ => CanonicalFactors.factor 0 (z / a) ^ d a
  have hv : ∀ a z, AnalyticAt ℂ (v a) z := by
    intro a z
    exact (analytic_entire (EntireZeros.rescaled_factor_entire (fun _ => a) 0) z).pow _
  have ho : ∀ a ∈ s, ∀ z, analyticOrderAt (v a) z =
      if a = z then (d a : ℕ∞) else 0 := by
    intro a ha z
    change analyticOrderAt ((fun w : ℂ => CanonicalFactors.factor 0 (w / a)) ^ d a) z = _
    rw [analyticOrderAt_pow (analytic_entire
      (EntireZeros.rescaled_factor_entire (fun _ => a) 0) z),
      EntireZeros.order_rescaled_factor 0 ((hs a).mp ha).1 z]
    split_ifs <;> simp_all
  refine ⟨⟨isOpen_univ, fun z _ => differentiableAt_id.pow _ |>.mul
    (s.analyticAt_fun_prod (fun a _ => hv a z)).differentiableAt⟩, ?_⟩
  intro z
  change analyticOrderAt ((fun z : ℂ => z ^ d 0) * (fun z => ∏ a ∈ s, v a z)) z = _
  rw [analyticOrderAt_mul (by fun_prop) (s.analyticAt_fun_prod (fun a _ => hv a z)),
    EntireZeros.order_finset_product s v z (fun a _ => hv a z)]
  have hsum : (∑ a ∈ s, analyticOrderAt (v a) z) =
      if z ∈ s then (d z : ℕ∞) else 0 := by
    simp_rw [Finset.sum_congr rfl (fun a ha => ho a ha z)]
    simp
  rw [hsum]
  have hid : analyticOrderAt (fun w : ℂ => w ^ d 0) z =
      if z = 0 then (d 0 : ℕ∞) else 0 := by
    by_cases hz : z = 0
    · subst z
      have heq : ((· - (0 : ℂ)) ^ d 0 : ℂ → ℂ) = fun w => w ^ d 0 := by
        funext w
        simp
      rw [ite_eq_left rfl, ← heq]
      exact analyticOrderAt_centeredMonomial
    · rw [ite_eq_right hz]
      exact (show AnalyticAt ℂ (fun w : ℂ => w ^ d 0) z by fun_prop).analyticOrderAt_eq_zero.mpr
        (pow_ne_zero _ hz)
  rw [hid]
  by_cases hz : z = 0
  · subst z
    simp [hs]
  · by_cases hd : d z = 0
    · simp [hz, hd, hs]
    · simp [hz, hd, hs]

theorem finite_factorization :
    Specs.D12Complex.Ch16.EntireFactorization.finite_factorization_type := by
  intro f d s hf ho hs
  let P := fun z : ℂ => z ^ d 0 *
    ∏ a ∈ s, CanonicalFactors.factor 0 (z / a) ^ d a
  obtain ⟨hP, hPo⟩ := finite_product_order d s hs
  obtain ⟨q, hq, hq0, _, heq⟩ := quotient_extension f P d hf hP ho hPo
  obtain ⟨g, hg, heg⟩ := entire_logarithm q hq hq0
  refine ⟨g, hg, fun z => ?_⟩
  rw [heq z, ← heg z]
  change Complex.exp (g z) * (z ^ d 0 * _) = _
  simp only [CanonicalFactors.factor]
  ring

theorem infinite_factorization :
    Specs.D12Complex.Ch16.EntireFactorization.infinite_factorization_type := by
  intro f d hf ho hd hi
  obtain ⟨e, he, hP⟩ := EntireZeros.infinite_divisor_product d hd hi
  obtain ⟨q, hq, hq0, _, heq⟩ := quotient_extension f
    (EntireZeros.canonicalProduct (fun n => (e n).1.1) (d 0)) d hf hP.1 ho hP.2.2.1
  obtain ⟨g, hg, heg⟩ := entire_logarithm q hq hq0
  refine ⟨e, g, he, hg, fun z => ?_⟩
  rw [heq z, ← heg z]
  change Complex.exp (g z) * (z ^ d 0 * _) = _
  ring

theorem entire_factorization :
    Specs.D12Complex.Ch16.EntireFactorization.entire_factorization_type := by
  classical
  intro f hf hn
  obtain ⟨d, hd, ho⟩ := zero_divisor f hf hn
  refine ⟨d, hd, ho, ?_⟩
  by_cases hfinite : {z : ℂ | z ≠ 0 ∧ d z ≠ 0}.Finite
  · let s := hfinite.toFinset
    have hs : ∀ z, z ∈ s ↔ z ≠ 0 ∧ d z ≠ 0 := fun z => hfinite.mem_toFinset
    obtain ⟨g, hg, he⟩ := finite_factorization f d s hf ho hs
    exact Or.inl ⟨s, g, hs, hg, he⟩
  · exact Or.inr (infinite_factorization f d hf ho hd (Set.not_finite.mp hfinite))

end D12Complex.EntireFactorization
