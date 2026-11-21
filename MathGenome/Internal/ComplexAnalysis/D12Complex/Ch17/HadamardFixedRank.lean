import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.HadamardFixedRank
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.FiniteOrderDivisorGrowth
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.CanonicalLowerCircles
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.RealPartPolynomial
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.GlobalLogarithmCriterion
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Complex.HasPrimitives

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.HadamardFixedRank
open OrderDivisorDefinitions ExponentCountingRank CanonicalLowerCircles CanonicalFactors

lemma analyticAt_entire {g : ℂ → ℂ} (hg : HolomorphicOn univ g) (z : ℂ) :
    AnalyticAt ℂ g z :=
  (LocalZeroFactorization.holomorphicNear_iff_analyticAt g z).mp ⟨univ, mem_univ _, hg⟩

lemma counting_growth (f : NonzeroEntireFunction) (hfin : order f ≠ ⊤) :
    CountingGrowth (zeroLocation f) (order f).toReal := by
  intro s hs
  obtain ⟨C, _, R, _, hR⟩ := FiniteOrderDivisorGrowth.counting_growth f hfin s hs
  exact ⟨C, (eventually_ge_atTop R).mono (fun r hr => hR r hr)⟩

/-- Restricting the repeated divisor to a subset preserves local finiteness. -/
lemma locallyFinite_subtype {ι : Type} (a : ι → ℂ) (ha : LocallyFiniteDivisor a)
    (S : Set ι) : LocallyFiniteDivisor (fun i : S => a i.val) := by
  intro R
  exact (ha R).preimage Subtype.val_injective.injOn

/-- A finite subproduct splits from the actual convergent product, including
at zeros of the finite part. -/
lemma product_split {ι : Type} (a : ι → ℂ) (p : ℕ) (ha : LocallyFiniteDivisor a)
    (hs : Summable (fun i => ‖a i‖ ^ (-((p : ℝ) + 1)))) (S : Finset ι) (z : ℂ) :
    canonicalProduct p a z = (∏ i ∈ S, factor p (z / a i)) *
      canonicalProduct p (fun i : {i // i ∉ S} => a i.val) z := by
  have ht := hasProdLocallyUniformlyOn_of_summable
    (fun i : {i // i ∉ S} => a i.val) p (locallyFinite_subtype a ha _)
    (hs.subtype _)
  exact ((S.hasProd (fun i => factor p (z / a i))).mul_compl
    (ht.hasProd (mem_univ z))).tprod_eq

lemma scaled_factor_order (p : ℕ) (a : ℂ) (ha : a ≠ 0) :
    analyticOrderAt (fun z => factor p (z / a)) a = 1 := by
  have hd : deriv (fun z : ℂ => z / a) a ≠ 0 := by
    change deriv (fun z : ℂ => id z / a) a ≠ 0
    rw [(hasDerivAt_id a |>.div_const a).deriv]
    exact div_ne_zero one_ne_zero ha
  have h := analyticOrderAt_comp_of_deriv_ne_zero
    (f := factor p) (g := fun z : ℂ => z / a)
    (analyticAt_id.div_const) hd
  simpa only [Function.comp_def, div_self ha, factor_simple_zero] using h

/-- Multiplicity of a canonical product at a nonzero point, for arbitrary
finite or infinite index types. -/
lemma product_order {ι : Type} (a : ι → ℂ) (p : ℕ) (ha : LocallyFiniteDivisor a)
    (hne : ∀ i, a i ≠ 0)
    (hs : Summable (fun i => ‖a i‖ ^ (-((p : ℝ) + 1)))) (z : ℂ) :
    analyticOrderAt (canonicalProduct p a) z = (Nat.card {i // a i = z} : ℕ∞) := by
  classical
  have hf : Set.Finite {i | a i = z} := (ha ‖z‖).subset (by intro i hi; change a i = z at hi; simp [hi])
  let S := hf.toFinset
  have hS : ∀ i, i ∈ S ↔ a i = z := by simp [S]
  have ht := product_entire_of_summable
    (fun i : {i // i ∉ S} => a i.val) p (locallyFinite_subtype a ha _) (hs.subtype _)
  have htz : canonicalProduct p (fun i : {i // i ∉ S} => a i.val) z ≠ 0 := by
    intro hzero
    have hzero' := (product_eq_zero_iff_of_summable
      (fun i : {i // i ∉ S} => a i.val) p (locallyFinite_subtype a ha _)
      (fun i => hne i.val) (hs.subtype _) z).mp hzero
    obtain ⟨i, hi⟩ := hzero'
    exact i.property ((hS i.val).mpr hi.symm)
  have he : canonicalProduct p a =
      (fun w => (∏ i ∈ S, factor p (w / a i))) *
        canonicalProduct p (fun i : {i // i ∉ S} => a i.val) := by
    funext w
    exact product_split a p ha hs S w
  rw [he, analyticOrderAt_mul
    (S.analyticAt_fun_prod (fun i _ => analyticAt_entire
      ⟨isOpen_univ, fun w _ => factor_differentiable a p i w⟩ z))
    (analyticAt_entire ht z), (analyticAt_entire ht z).analyticOrderAt_eq_zero.mpr htz,
    add_zero]
  have hfinite : analyticOrderAt (fun w => ∏ i ∈ S, factor p (w / a i)) z =
      (S.card : ℕ∞) := by
    by_cases hz : z = 0
    · have hS0 : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        exact hne i ((hS i).mp hi |>.trans hz)
      simp [hS0, analyticOrderAt_eq_zero]
    · have heq : (fun w => ∏ i ∈ S, factor p (w / a i)) =
          (fun w => factor p (w / z)) ^ S.card := by
        funext w
        simp only [Pi.pow_apply]
        calc
          _ = ∏ i ∈ S, factor p (w / z) :=
            Finset.prod_congr rfl (fun i hi => by rw [(hS i).mp hi])
          _ = _ := by simp
      have hA : AnalyticAt ℂ (fun w => factor p (w / z)) z := by
        exact analyticAt_entire ⟨isOpen_univ, fun w _ =>
          ((factor_entire p).2 _ (mem_univ _)).comp w (differentiableAt_id.div_const z)⟩ z
      rw [heq, analyticOrderAt_pow hA, scaled_factor_order p z hz]
      simp
  rw [hfinite]
  congr 1
  exact (Nat.card_eq_card_finite_toFinset hf).symm

/-- The intrinsic divisor cardinality includes the full multiplicity. -/
lemma intrinsic_product_order (f : NonzeroEntireFunction) (p : ℕ)
    (hs : Summable (fun i => ‖zeroLocation f i‖ ^ (-((p : ℝ) + 1))))
    {z : ℂ} (hz : z ≠ 0) :
    analyticOrderAt (canonicalProduct p (zeroLocation f)) z = analyticOrderAt f.toFun z := by
  rw [product_order _ p (zeros_locallyFinite f) (zeroLocation_nonzero f) hs]
  have hc : Nat.card {i : RepeatedZero f // zeroLocation f i = z} =
      (analyticOrderAt f.toFun z).toNat := by
    simpa [zeroLocation] using Nat.card_congr (repeatedZero_fiber f z hz).some
  rw [hc, ENat.natCast_toNat (zero_multiplicity_finite f z)]

theorem canonical_product_exact :
    Specs.D12Complex.Ch17.HadamardFixedRank.canonical_product_exact_type := by
  intro f hfin
  dsimp only
  let p := ⌊(order f).toReal⌋₊
  let m := (analyticOrderAt f.toFun 0).toNat
  have hs := FiniteOrderDivisorGrowth.floor_sum f hfin
  have hloc := zeros_locallyFinite f
  have hP := product_entire_of_summable (zeroLocation f) p hloc hs
  refine ⟨hasProdLocallyUniformlyOn_of_summable _ p hloc hs, hP, fun z => ?_⟩
  have hpA : AnalyticAt ℂ (fun w : ℂ => w ^ m) z := analyticAt_id.pow m
  have hmul : (fun w : ℂ => w ^ m * canonicalProduct p (zeroLocation f) w) =
      (fun w : ℂ => w ^ m) * canonicalProduct p (zeroLocation f) := rfl
  change analyticOrderAt (fun w : ℂ => w ^ m * canonicalProduct p (zeroLocation f) w) z = _
  rw [hmul, analyticOrderAt_mul hpA (analyticAt_entire hP z)]
  by_cases hz : z = 0
  · subst z
    have hP0 : canonicalProduct p (zeroLocation f) 0 ≠ 0 := by
      intro he
      obtain ⟨i, hi⟩ := (product_eq_zero_iff_of_summable _ p hloc
        (zeroLocation_nonzero f) hs 0).mp he
      exact zeroLocation_nonzero f i hi.symm
    rw [(analyticAt_entire hP 0).analyticOrderAt_eq_zero.mpr hP0, add_zero]
    have he : (fun w : ℂ => w ^ m) = (fun w : ℂ => w - 0) ^ m := by funext w; simp
    rw [he, analyticOrderAt_centeredMonomial, ENat.natCast_toNat (zero_multiplicity_finite f 0)]
  · rw [hpA.analyticOrderAt_eq_zero.mpr (pow_ne_zero m hz), zero_add,
      intrinsic_product_order f p hs hz]

/-- Equal finite local orders give an everywhere nonzero entire quotient,
by the library's continuous meromorphic extension. -/
lemma entire_quotient_of_equal_orders (f : NonzeroEntireFunction) (F : ℂ → ℂ)
    (hF : HolomorphicOn univ F)
    (horder : ∀ z, analyticOrderAt F z = analyticOrderAt f.toFun z) :
    ∃ g : ℂ → ℂ, HolomorphicOn univ g ∧ (∀ z, g z ≠ 0) ∧
      ∀ z, f.toFun z = g z * F z := by
  let v := f.toFun / F
  have hv : MeromorphicOn v univ := fun z _ =>
    (analyticAt_entire f.holomorphic z).meromorphicAt.div
      (analyticAt_entire hF z).meromorphicAt
  have hvorder (z : ℂ) : meromorphicOrderAt v z = 0 := by
    rw [meromorphicOrderAt_div (analyticAt_entire f.holomorphic z).meromorphicAt
      (analyticAt_entire hF z).meromorphicAt,
      (analyticAt_entire f.holomorphic z).meromorphicOrderAt_eq,
      (analyticAt_entire hF z).meromorphicOrderAt_eq, horder z]
    rw [← ENat.natCast_toNat (zero_multiplicity_finite f z), ENat.map_natCast]
    simp
  let g := toMeromorphicNFOn v univ
  have hgNF (z : ℂ) : MeromorphicNFAt g z :=
    meromorphicNFOn_toMeromorphicNFOn v univ (mem_univ z)
  have hgorder (z : ℂ) : meromorphicOrderAt g z = 0 :=
    (meromorphicOrderAt_toMeromorphicNFOn hv (mem_univ z)).trans (hvorder z)
  have hgA (z : ℂ) : AnalyticAt ℂ g z :=
    (hgNF z).meromorphicOrderAt_nonneg_iff_analyticAt.mp (by rw [hgorder])
  refine ⟨g, ⟨isOpen_univ, fun z _ => (hgA z).differentiableAt⟩,
    fun z => (hgNF z).meromorphicOrderAt_eq_zero_iff.mp (hgorder z), fun z => ?_⟩
  have hFne : ∀ᶠ w in 𝓝[≠] z, F w ≠ 0 := by
    apply (analyticAt_entire hF z).eventually_eq_zero_or_eventually_ne_zero.resolve_left
    intro he
    exact zero_multiplicity_finite f z ((horder z).symm.trans (analyticOrderAt_eq_top.mpr he))
  have heq : f.toFun =ᶠ[𝓝[≠] z] fun w => g w * F w := by
    filter_upwards [hv.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ z), hFne] with w hw hwne
    change g w = f.toFun w / F w at hw
    rw [hw, div_mul_cancel₀ _ hwne]
  exact ((analyticAt_entire f.holomorphic z).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    ((hgA z).continuousAt.mul (analyticAt_entire hF z).continuousAt)).mp heq |>.self_of_nhds

/-- The global logarithm criterion applies on the plane: an entire primitive
of the logarithmic derivative supplies its zero periods. -/
lemma entire_logarithm (g : ℂ → ℂ) (hg : HolomorphicOn univ g) (hne : ∀ z, g z ≠ 0) :
    ∃ h : ℂ → ℂ, HolomorphicOn univ h ∧ ∀ z, Complex.exp (h z) = g z := by
  have hD : IsDomain (univ : Set ℂ) := ⟨univ_nonempty, isOpen_univ, isPreconnected_univ⟩
  have hld := GlobalLogarithmCriterion.holomorphicOn_logarithmicDerivative univ g hg
    (fun z _ => hne z)
  obtain ⟨H, hH⟩ := (show Differentiable ℂ (fun z => deriv g z / g z) from
    fun z => hld.2 z (mem_univ _)).isExactOn_univ
  have hHp : Primitives.IsPrimitive univ (fun z => deriv g z / g z) H :=
    ⟨⟨isOpen_univ, fun z hz => (hH z hz).differentiableAt⟩, fun z hz => (hH z hz).deriv⟩
  obtain ⟨h, hh, he⟩ := (GlobalLogarithmCriterion.global_logarithm_criterion
    univ g hD hg (fun z _ => hne z)).mpr (by
      intro γ hγ hclosed
      rw [Primitives.piecewise_endpoint univ _ H
        (fun z hz => (hld.2 z hz).continuousAt.continuousWithinAt) hHp γ hγ,
        hclosed, sub_self])
  have hE : E = Complex.exp := Exponential.E_eq_exp
  exact ⟨h, hh, fun z => by rw [← hE]; exact he z (mem_univ _)⟩

theorem entire_quotient_log :
    Specs.D12Complex.Ch17.HadamardFixedRank.entire_quotient_log_type := by
  intro f hfin
  dsimp only
  let p := ⌊(order f).toReal⌋₊
  let m := (analyticOrderAt f.toFun 0).toNat
  obtain ⟨_, hP, horder⟩ := canonical_product_exact f hfin
  have hF : HolomorphicOn univ (fun z : ℂ => z ^ m * canonicalProduct p (zeroLocation f) z) :=
    ⟨isOpen_univ, fun z hz => (differentiableAt_id.pow m).mul (hP.2 z hz)⟩
  obtain ⟨g, hg, hgne, hfg⟩ := entire_quotient_of_equal_orders f _ hF horder
  obtain ⟨h, hh, he⟩ := entire_logarithm g hg hgne
  refine ⟨g, h, hg, hgne, hh, he, fun z => ?_⟩
  rw [hfg z]
  ring

/-- The logarithmic identity on a divisor-free circle converts the lower
product bound and the upper maximum-modulus bound to a one-sided bound on
an actual logarithm. All logarithms here have positive arguments. -/
lemma real_part_bound (f : NonzeroEntireFunction) (m p : ℕ) (h : ℂ → ℂ)
    (he : ∀ z, f.toFun z = z ^ m * Complex.exp (h z) *
      canonicalProduct p (zeroLocation f) z)
    {r s t C : ℝ} (hr : 1 ≤ r) (hst : s ≤ t)
    (hupper : Real.log (max (Real.exp 1) (maximumModulus f.toFun r)) ≤ r ^ s)
    (hlower : ∀ z, ‖z‖ = r → canonicalProduct p (zeroLocation f) z ≠ 0 ∧
      -C * r ^ t ≤ Real.log ‖canonicalProduct p (zeroLocation f) z‖) :
    ∀ z ∈ Metric.sphere (0 : ℂ) r, (h z).re ≤ (1 + C) * r ^ t := by
  intro z hz
  have hzR : ‖z‖ = r := by simpa using hz
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hz0 : z ≠ 0 := norm_pos_iff.mp (hzR ▸ hr0)
  have hp := hlower z hzR
  have hpow0 : ‖z‖ ^ m ≠ 0 := pow_ne_zero m (norm_ne_zero_iff.mpr hz0)
  have hlog : Real.log ‖f.toFun z‖ =
      (m : ℝ) * Real.log r + (h z).re +
        Real.log ‖canonicalProduct p (zeroLocation f) z‖ := by
    rw [he z, norm_mul, norm_mul, norm_pow, Complex.norm_exp,
      Real.log_mul (mul_ne_zero hpow0 (Real.exp_ne_zero _)) (norm_ne_zero_iff.mpr hp.1),
      Real.log_mul hpow0 (Real.exp_ne_zero _), Real.log_exp, Real.log_pow, hzR]
  have hfn : f.toFun z ≠ 0 := by
    rw [he z]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero m hz0) (Complex.exp_ne_zero _)) hp.1
  obtain ⟨_, _, _, hmax⟩ := maximumModulus_attained f.toFun
    (show Differentiable ℂ f.toFun from fun w => f.holomorphic.2 w (mem_univ _)).continuous r hr0
  have hlmax : Real.log ‖f.toFun z‖ ≤
      Real.log (max (Real.exp 1) (maximumModulus f.toFun r)) :=
    Real.log_le_log (norm_pos_iff.mpr hfn) ((hmax z hz).trans (le_max_right _ _))
  have hmp : 0 ≤ (m : ℝ) * Real.log r :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hr)
  have hpow := Real.rpow_le_rpow_of_exponent_le hr hst
  nlinarith [hp.2]

/-- Bounds on selected lower-product circles force the entire logarithm
to be a polynomial of degree at most floor(order). The selected sequence
is shifted past the finite initial range where the growth bound need not hold. -/
lemma logarithm_polynomial (f : NonzeroEntireFunction) (hfin : order f ≠ ⊤)
    (h : ℂ → ℂ) (hh : HolomorphicOn univ h)
    (he : ∀ z, f.toFun z = z ^ (analyticOrderAt f.toFun 0).toNat *
      Complex.exp (h z) * canonicalProduct ⌊(order f).toReal⌋₊ (zeroLocation f) z) :
    ∃ Q : Polynomial ℂ, Q.natDegree ≤ ⌊(order f).toReal⌋₊ ∧ ∀ z, h z = Q.eval z := by
  let ρ := (order f).toReal
  let p := ⌊ρ⌋₊
  obtain ⟨t, hρt, htp⟩ := exists_between (Nat.lt_floor_add_one ρ)
  obtain ⟨s, hρs, hst⟩ := exists_between hρt
  obtain ⟨r, C, _, hrTop, hr⟩ := lower_circles (zeroLocation f) ρ
    ENNReal.toReal_nonneg (zeros_locallyFinite f) (zeroLocation_nonzero f)
    (counting_growth f hfin) t hρt htp
  have hev : ∀ᶠ k : ℕ in atTop, 1 ≤ r k ∧
      Real.log (max (Real.exp 1) (maximumModulus f.toFun (r k))) ≤ (r k) ^ s := by
    filter_upwards [hrTop.eventually_ge_atTop 1,
      hrTop.eventually (FiniteOrderDivisorGrowth.log_maximum_eventually_le f hfin hρs)]
      with k hk1 hku
    exact ⟨hk1, hku⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hbound : ∀ k, ∀ z ∈ Metric.sphere (0 : ℂ) (r (k + N)),
      (h z).re ≤ (1 + C) * (r (k + N)) ^ t := by
    intro k
    have hk := hN (k + N) (Nat.le_add_left N k)
    exact real_part_bound f (analyticOrderAt f.toFun 0).toNat p h he hk.1 hst.le hk.2
      (hr (k + N)).2.2
  exact RealPartPolynomial.polynomial_of_finite_order_real_part_growth h hh
    ρ t (1 + C) (fun k => r (k + N)) ENNReal.toReal_nonneg hρt htp
    (hrTop.comp (tendsto_add_atTop_nat N)) hbound

theorem hadamard_fixed_rank :
    Specs.D12Complex.Ch17.HadamardFixedRank.hadamard_fixed_rank_type := by
  intro f hfin
  dsimp only
  obtain ⟨g, h, _, _, hh, hexp, he⟩ := entire_quotient_log f hfin
  have heh : ∀ z, f.toFun z = z ^ (analyticOrderAt f.toFun 0).toNat *
      Complex.exp (h z) * canonicalProduct ⌊(order f).toReal⌋₊ (zeroLocation f) z := by
    intro z
    rw [hexp z]
    exact he z
  obtain ⟨Q, hQ, hhQ⟩ := logarithm_polynomial f hfin h hh heh
  obtain ⟨hconv, hP, horder⟩ := canonical_product_exact f hfin
  refine ⟨Q, hQ, hconv, hP, horder, fun z => ?_⟩
  rw [← hhQ z]
  exact heh z

end D12Complex.HadamardFixedRank
