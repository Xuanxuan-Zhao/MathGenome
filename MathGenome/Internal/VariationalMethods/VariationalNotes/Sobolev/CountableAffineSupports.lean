import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Sobolev.CountableAffineSupports
import MathGenome.Internal.VariationalMethods.VariationalNotes.ConvexAnalysis.ProximalCharacterization
import MathGenome.Internal.VariationalMethods.VariationalNotes.Sobolev.CaratheodoryIntegrands
import Mathlib.Topology.Order.IsLUB
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Data.Nat.Pairing

noncomputable section
open MeasureTheory Filter Set
open scoped InnerProductSpace Topology
universe u v
namespace VariationalNotes.Sobolev.AffineSupports

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def finiteProx (g : H → ℝ) (ε : ℝ) (b : H) : H :=
  AffineSupportSpecs.finiteProx g ε b

def supportSlope (g : H → ℝ) (ε : ℝ) (b : H) : H :=
  AffineSupportSpecs.supportSlope g ε b

def supportConstant (g : H → ℝ) (ε : ℝ) (b : H) : ℝ :=
  AffineSupportSpecs.supportConstant g ε b

def supportValue (g : H → ℝ) (ε : ℝ) (b y : H) : ℝ :=
  AffineSupportSpecs.supportValue g ε b y

/-- Finite continuous convex functions satisfy exactly the upstream extended
hypotheses. No nonnegativity is needed for this bridge. -/
lemma finite_fiber_hypotheses (g : H → ℝ) (hg : Continuous g)
    (hc : ConvexOn ℝ univ g) :
    ConvexAnalysis.Proper (fun y => (g y : WithTop ℝ)) ∧
    ConvexAnalysis.IsConvex (fun y => (g y : WithTop ℝ)) ∧
    ConvexAnalysis.IsLowerSemicontinuous (fun y => (g y : WithTop ℝ)) := by
  refine ⟨⟨0, WithTop.coe_lt_top _⟩, ?_, ?_⟩
  · apply (ConvexAnalysis.convex_iff_twoPoint _).mpr
    intro x y r s hr hs a b ha hb hab
    have hr' : g x = r := WithTop.coe_inj.mp hr
    have hs' : g y = s := WithTop.coe_inj.mp hs
    apply WithTop.coe_le_coe.mpr
    simpa only [hr', hs', smul_eq_mul] using hc.2 (mem_univ x) (mem_univ y) ha hb hab
  · intro a
    change IsOpen {x | (a : WithTop ℝ) < (g x : WithTop ℝ)}
    simpa only [WithTop.coe_lt_coe] using isOpen_lt continuous_const hg

variable [CompleteSpace H]

theorem finiteProx_minimizes : AffineSupportSpecs.finiteProx_minimizes.{v} := by
  intro H _ _ _ g hg hc ε hε b
  obtain ⟨hp, hc', hl⟩ := finite_fiber_hypotheses g hg hc
  have hmin := ConvexAnalysis.proximalMap_minimizes _ hp hc' hl ε hε b
  constructor
  · intro y
    have h := hmin.2 y
    change ((g (finiteProx g ε b) : WithTop ℝ) + _) ≤ ((g y : WithTop ℝ) + _) at h
    exact WithTop.coe_le_coe.mp h
  · intro w hw
    apply (ConvexAnalysis.minimizer_iff_eq_proximalMap _ hp hc' hl ε hε b w).mp
    refine ⟨WithTop.coe_lt_top _, ?_⟩
    intro y
    exact WithTop.coe_le_coe.mpr (hw y)

omit [CompleteSpace H] in
lemma supportValue_eq (g : H → ℝ) (ε : ℝ) (b y : H) :
    supportValue g ε b y =
      g (finiteProx g ε b) + ⟪ε⁻¹ • (b - finiteProx g ε b), y - finiteProx g ε b⟫_ℝ := by
  change g (finiteProx g ε b) - ⟪ε⁻¹ • (b - finiteProx g ε b), finiteProx g ε b⟫_ℝ +
    ⟪ε⁻¹ • (b - finiteProx g ε b), y⟫_ℝ = _
  rw [inner_sub_right]
  ring

theorem supportValue_le : AffineSupportSpecs.supportValue_le.{v} := by
  intro H _ _ _ g hg hc ε hε b y
  obtain ⟨hp, hc', hl⟩ := finite_fiber_hypotheses g hg hc
  have hs := (ConvexAnalysis.proximalMap_characterization _ hp hc' hl ε hε b
    (finiteProx g ε b)).mp rfl
  obtain ⟨r, hr, hs⟩ := hs
  have hr' : g (finiteProx g ε b) = r := WithTop.coe_inj.mp hr
  change supportValue g ε b y ≤ g y
  rw [supportValue_eq, hr']
  exact WithTop.coe_le_coe.mp (hs y)

/-- Comparison with the center supplies the uniform localization used in the
parameter-continuity argument. -/
lemma finiteProx_norm_sq_le (g : H → ℝ) (hg : Continuous g)
    (hc : ConvexOn ℝ univ g) (hn : ∀ y, 0 ≤ g y)
    (ε : ℝ) (hε : 0 < ε) (b : H) :
    ‖finiteProx g ε b - b‖ ^ 2 ≤ 2 * ε * g b := by
  have hm := (finiteProx_minimizes g hg hc ε hε b).1 b
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, add_zero] at hm
  have hh : ‖finiteProx g ε b - b‖ ^ 2 / (2 * ε) ≤ g b :=
    le_trans (le_add_of_nonneg_left (hn _)) hm
  have := (div_le_iff₀ (by positivity : 0 < 2 * ε)).mp hh
  nlinarith

/-- Quantitative strict minimality, with a stronger constant than the source's
midpoint estimate. This forces measurable approximate minimizers to converge. -/
lemma finiteProx_gap (g : H → ℝ) (hg : Continuous g)
    (hc : ConvexOn ℝ univ g) (ε : ℝ) (hε : 0 < ε) (b y : H) :
    ‖y - finiteProx g ε b‖ ^ 2 / (2 * ε) ≤
      (g y + ‖y - b‖ ^ 2 / (2 * ε)) -
      (g (finiteProx g ε b) + ‖finiteProx g ε b - b‖ ^ 2 / (2 * ε)) := by
  let w := finiteProx g ε b
  have hs := supportValue_le g hg hc ε hε b y
  change supportValue g ε b y ≤ g y at hs
  rw [supportValue_eq, real_inner_smul_left, inv_mul_eq_div] at hs
  have hi : ⟪b - w, y - w⟫_ℝ ≤ (g y - g w) * ε :=
    (div_le_iff₀ hε).mp (by linarith)
  have he := norm_add_sq_real (y - w) (w - b)
  have heq : y - w + (w - b) = y - b := by abel
  rw [heq, real_inner_comm] at he
  have heq' : b - w = -(w - b) := by abel
  rw [heq', inner_neg_left] at hi
  apply (div_le_iff₀ (by positivity : 0 < 2 * ε)).mpr
  have hε0 : ε ≠ 0 := ne_of_gt hε
  field_simp
  nlinarith

lemma continuous_finiteProx_center (g : H → ℝ) (hg : Continuous g)
    (hc : ConvexOn ℝ univ g) (ε : ℝ) (hε : 0 < ε) :
    Continuous (finiteProx g ε) := by
  obtain ⟨hp, hc', hl⟩ := finite_fiber_hypotheses g hg hc
  apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
  intro x y
  simpa only [NNReal.coe_one, one_mul, dist_eq_norm_sub, finiteProx,
    AffineSupportSpecs.finiteProx, ConvexAnalysis.proximalMap] using
    (ConvexAnalysis.proximalMap_nonexpansive _ hp hc' hl ε hε x y)

lemma continuous_supportValue_center (g : H → ℝ) (hg : Continuous g)
    (hc : ConvexOn ℝ univ g) (ε : ℝ) (hε : 0 < ε) (y : H) :
    Continuous (fun b => supportValue g ε b y) := by
  have hw := continuous_finiteProx_center g hg hc ε hε
  simp only [supportValue_eq]
  exact (hg.comp hw).add ((continuous_const.smul (continuous_id.sub hw)).inner
    (continuous_const.sub hw))

omit [CompleteSpace H] in
/-- At its own center the support is at least the fiber value at the proximal point. -/
lemma fiberValue_le_support_at_center (g : H → ℝ) (ε : ℝ) (hε : 0 < ε) (y : H) :
    g (finiteProx g ε y) ≤ supportValue g ε y y := by
  rw [supportValue_eq, real_inner_smul_left, real_inner_self_eq_norm_sq]
  exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hε.le) (sq_nonneg _))

/-- The source's positive sequence of parameters tends to zero. -/
lemma finiteProx_small_parameter (g : H → ℝ) (hg : Continuous g)
    (hc : ConvexOn ℝ univ g) (hn : ∀ y, 0 ≤ g y) (y : H) :
    Tendsto (fun n : ℕ => finiteProx g ((n : ℝ) + 1)⁻¹ y) atTop (𝓝 y) := by
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  have hlim : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)⁻¹ * g y) atTop (𝓝 0) := by
    simpa only [one_div, mul_zero, zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2 |>.mul_const (g y)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (sq_pos_of_pos hδ))
  refine ⟨N, fun n hnN => ?_⟩
  have hh := finiteProx_norm_sq_le g hg hc hn ((n : ℝ) + 1)⁻¹ (by positivity) y
  rw [dist_eq_norm]
  have hsq : ‖finiteProx g ((n : ℝ) + 1)⁻¹ y - y‖ ^ 2 < δ ^ 2 := hh.trans_lt (hN n hnN)
  nlinarith [norm_nonneg (finiteProx g ((n : ℝ) + 1)⁻¹ y - y)]

/-- Any dense sequence of centers suffices; rational coordinates are one option.
This is the full deterministic supremum assertion. -/
lemma dense_supports_isLUB (g : H → ℝ) (hg : Continuous g)
    (hc : ConvexOn ℝ univ g) (hn : ∀ y, 0 ≤ g y)
    (d : ℕ → H) (hd : DenseRange d) (y : H) :
    IsLUB ({0} ∪ Set.range (fun p : ℕ × ℕ =>
      supportValue g ((p.2 : ℝ) + 1)⁻¹ (d p.1) y)) (g y) := by
  refine ⟨?_, ?_⟩
  · rintro t (ht | ⟨⟨i,j⟩, rfl⟩)
    · simpa only [mem_singleton_iff.mp ht] using hn y
    · exact supportValue_le g hg hc _ (by positivity) _ _
  · intro t ht
    have hd' (j : ℕ) (b : H) : supportValue g ((j : ℝ) + 1)⁻¹ b y ≤ t := by
      have hclosed : IsClosed {b : H | supportValue g ((j : ℝ) + 1)⁻¹ b y ≤ t} :=
        isClosed_le (continuous_supportValue_center g hg hc _ (by positivity) y) continuous_const
      have hsub : Set.range d ⊆ {b : H | supportValue g ((j : ℝ) + 1)⁻¹ b y ≤ t} := by
        rintro _ ⟨i, rfl⟩
        exact ht (Or.inr ⟨(i,j), rfl⟩)
      exact (closure_minimal hsub hclosed) (hd b)
    have hg_lim := hg.continuousAt.tendsto.comp (finiteProx_small_parameter g hg hc hn y)
    apply le_of_tendsto hg_lim
    exact Eventually.of_forall fun j =>
      (fiberValue_le_support_at_center g _ (by positivity) y).trans (hd' j y)

/-- Measurable minimization by first approximate minimizers in a countable
 dense set. No measurable-selection certificate is used. -/
lemma measurable_finiteProx {S : Type u} [MeasurableSpace S]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (F : S → H → ℝ) (hF : ∀ y, Measurable (fun x => F x y))
    (hC : ∀ x, Continuous (F x)) (hV : ∀ x, ConvexOn ℝ univ (F x))
    (ε : ℝ) (hε : 0 < ε) (b : H) :
    Measurable (fun x => finiteProx (F x) ε b) := by
  classical
  let d := TopologicalSpace.denseSeq H
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq H
  let Q (x : S) (y : H) : ℝ := F x y + ‖y - b‖ ^ 2 / (2 * ε)
  let w (x : S) : H := finiteProx (F x) ε b
  have hQ (x : S) : Continuous (Q x) :=
    (hC x).add ((continuous_id.sub continuous_const).norm.pow 2 |>.div_const _)
  have hmin (x : S) (y : H) : Q x (w x) ≤ Q x y :=
    (finiteProx_minimizes (F x) (hC x) (hV x) ε hε b).1 y
  let M (x : S) : ℝ := ⨅ k : ℕ, Q x (d k)
  have hbd (x : S) : BddBelow (range (fun k => Q x (d k))) :=
    ⟨Q x (w x), by rintro _ ⟨k,rfl⟩; exact hmin x (d k)⟩
  have hM : Measurable M := Measurable.iInf fun k => (hF (d k)).add_const _
  have hMw (x : S) : M x = Q x (w x) := by
    apply le_antisymm
    · have hs : IsClosed {y | M x ≤ Q x y} := isClosed_le continuous_const (hQ x)
      have hsub : range d ⊆ {y | M x ≤ Q x y} := by
        rintro _ ⟨k,rfl⟩
        exact ciInf_le (hbd x) k
      exact closure_minimal hsub hs (hd (w x))
    · exact le_ciInf (fun k => hmin x (d k))
  have hex (n : ℕ) (x : S) : ∃ k, Q x (d k) < M x + ((n : ℝ) + 1)⁻¹ := by
    apply (ciInf_lt_iff (hbd x)).mp
    change M x < M x + ((n : ℝ) + 1)⁻¹
    have : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    linarith
  let a (n : ℕ) (x : S) : H := d (Nat.find (hex n x))
  have ha (n : ℕ) : Measurable (a n) := by
    apply Measurable.find (fun k => measurable_const)
      (fun k => measurableSet_lt ((hF (d k)).add_const _) (hM.add_const _)) (hex n)
  have haQ (n : ℕ) (x : S) : Q x (a n x) < Q x (w x) + ((n : ℝ) + 1)⁻¹ := by
    simpa only [a, hMw x] using Nat.find_spec (hex n x)
  apply measurable_of_tendsto_metrizable ha
  apply tendsto_pi_nhds.mpr
  intro x
  apply Metric.tendsto_atTop.mpr
  intro δ hδ
  have hlim : Tendsto (fun n : ℕ => 2 * ε * ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * ε)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually_lt_const (sq_pos_of_pos hδ))
  refine ⟨N, fun n hn => ?_⟩
  have hgap := finiteProx_gap (F x) (hC x) (hV x) ε hε b (a n x)
  change ‖a n x - w x‖ ^ 2 / (2 * ε) ≤ Q x (a n x) - Q x (w x) at hgap
  have hgap' := (div_le_iff₀ (by positivity : 0 < 2 * ε)).mp hgap
  have hbound := mul_lt_mul_of_pos_left (haQ n x) (by positivity : 0 < 2 * ε)
  rw [dist_eq_norm]
  nlinarith [hN n hn, norm_nonneg (a n x - w x)]

/-- Continuous dependence on a state parameter. Nonnegativity localizes the
minimizers in a compact ball; every subsequential limit is the unique minimizer
of the limiting objective. -/
lemma continuous_finiteProx_parameter {A : Type*} [TopologicalSpace A] [SequentialSpace A]
    [ProperSpace H] (G : A → H → ℝ)
    (hG : Continuous (fun p : A × H => G p.1 p.2))
    (hV : ∀ s, ConvexOn ℝ univ (G s)) (hN : ∀ s y, 0 ≤ G s y)
    (ε : ℝ) (hε : 0 < ε) (b : H) :
    Continuous (fun s => finiteProx (G s) ε b) := by
  have hC (s : A) : Continuous (G s) :=
    hG.comp (continuous_const.prodMk continuous_id)
  let Q (s : A) (y : H) := G s y + ‖y - b‖ ^ 2 / (2 * ε)
  have hQ : Continuous (fun p : A × H => Q p.1 p.2) :=
    hG.add ((continuous_snd.sub continuous_const).norm.pow 2 |>.div_const _)
  apply continuous_iff_seqContinuous.mpr
  intro u s hus
  apply tendsto_of_subseq_tendsto
  intro ns hns
  let t (n : ℕ) := u (ns n)
  have ht : Tendsto t atTop (𝓝 s) := hus.comp hns
  have hGb : Tendsto (fun n => G (t n) b) atTop (𝓝 (G s b)) :=
    (hG.tendsto (s,b)).comp (ht.prodMk_nhds tendsto_const_nhds)
  obtain ⟨M, hM⟩ := hGb.bddAbove_range
  have hM0 : 0 ≤ M := (hN (t 0) b).trans (hM (mem_range_self 0))
  let R := 2 * ε * M + 1
  let w (n : ℕ) := finiteProx (G (t n)) ε b
  have hw (n : ℕ) : w n ∈ Metric.closedBall b R := by
    have hsq := finiteProx_norm_sq_le (G (t n)) (hC (t n)) (hV (t n)) (hN (t n)) ε hε b
    have hMb := hM (mem_range_self n)
    rw [Metric.mem_closedBall, dist_eq_norm]
    change ‖w n - b‖ ≤ 2 * ε * M + 1
    change ‖w n - b‖ ^ 2 ≤ 2 * ε * G (t n) b at hsq
    have hbound : ‖w n - b‖ ^ 2 ≤ 2 * ε * M :=
      hsq.trans (mul_le_mul_of_nonneg_left hMb (by positivity))
    nlinarith [sq_nonneg (‖w n - b‖ - 1)]
  obtain ⟨v, _, φ, hφ, hv⟩ := (isCompact_closedBall b R).tendsto_subseq hw
  have htφ := ht.comp hφ.tendsto_atTop
  have hpair : Tendsto (fun n => (t (φ n), w (φ n))) atTop (𝓝 (s,v)) :=
    htφ.prodMk_nhds hv
  have hleft : Tendsto (fun n => Q (t (φ n)) (w (φ n))) atTop (𝓝 (Q s v)) :=
    (hQ.tendsto (s,v)).comp hpair
  have hvmin (y : H) : Q s v ≤ Q s y := by
    have hright : Tendsto (fun n => Q (t (φ n)) y) atTop (𝓝 (Q s y)) :=
      (hQ.tendsto (s,y)).comp (htφ.prodMk_nhds tendsto_const_nhds)
    apply le_of_tendsto_of_tendsto hleft hright
    exact Eventually.of_forall fun n =>
      (finiteProx_minimizes (G (t (φ n))) (hC _) (hV _) ε hε b).1 y
  have heq : v = finiteProx (G s) ε b :=
    (finiteProx_minimizes (G s) (hC s) (hV s) ε hε b).2 v hvmin
  exact ⟨φ, by simpa only [heq, Function.comp_def, w, t] using hv⟩

omit [CompleteSpace H] in
/-- One common measurable null set repairs continuity, convexity and
nonnegativity simultaneously, on an arbitrary measure space. -/
lemma regularize_convex_integrand {S A : Type*} [MeasurableSpace S]
    [TopologicalSpace A] (μ : Measure S) (G : S → A → H → ℝ)
    (hG : Caratheodory μ (fun x (p : A × H) => G x p.1 p.2))
    (hV : ∀ᵐ x ∂μ, ∀ s, ConvexOn ℝ univ (G x s))
    (hN : ∀ᵐ x ∂μ, ∀ s y, 0 ≤ G x s y) :
    ∃ (N : Set S) (G₀ : S → A → H → ℝ),
      MeasurableSet N ∧ μ N = 0 ∧
      (∀ x ∉ N, ∀ s y, G₀ x s y = G x s y) ∧
      (∀ x ∈ N, ∀ s y, G₀ x s y = 0) ∧
      (∀ s y, Measurable (fun x => G₀ x s y)) ∧
      (∀ x, Continuous (fun p : A × H => G₀ x p.1 p.2)) ∧
      (∀ x s, ConvexOn ℝ univ (G₀ x s)) ∧
      (∀ x s y, 0 ≤ G₀ x s y) := by
  classical
  let P (x : S) := Continuous (fun p : A × H => G x p.1 p.2) ∧
    (∀ s, ConvexOn ℝ univ (G x s)) ∧ (∀ s y, 0 ≤ G x s y)
  have hP : ∀ᵐ x ∂μ, P x := hG.2.and (hV.and hN)
  let N := toMeasurable μ {x | ¬ P x}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : μ N = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hP
  have hgood (x : S) (hx : x ∉ N) : P x := by
    by_contra hh
    exact hx (subset_toMeasurable μ _ hh)
  let G₀ (x : S) (s : A) (y : H) := if x ∈ N then 0 else G x s y
  refine ⟨N, G₀, hNm, hN0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx s y
    exact ite_eq_right hx
  · intro x hx s y
    exact ite_eq_left hx
  · intro s y
    exact measurable_const.piecewise hNm (hG.1 (s,y))
  · intro x
    by_cases hx : x ∈ N
    · simpa only [G₀, ite_eq_left hx] using
        (continuous_const : Continuous (fun _ : A × H => (0 : ℝ)))
    · simpa only [G₀, ite_eq_right hx] using (hgood x hx).1
  · intro x s
    by_cases hx : x ∈ N
    · simpa only [G₀, ite_eq_left hx] using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (univ : Set H)))
    · simpa only [G₀, ite_eq_right hx] using (hgood x hx).2.1 s
  · intro x s y
    by_cases hx : x ∈ N
    · simp only [G₀, ite_eq_left hx, le_refl]
    · simpa only [G₀, ite_eq_right hx] using (hgood x hx).2.2 s y

lemma continuous_support_coefficients_parameter {A : Type*} [TopologicalSpace A]
    [SequentialSpace A] [ProperSpace H] (G : A → H → ℝ)
    (hG : Continuous (fun p : A × H => G p.1 p.2))
    (hV : ∀ s, ConvexOn ℝ univ (G s)) (hN : ∀ s y, 0 ≤ G s y)
    (ε : ℝ) (hε : 0 < ε) (b : H) :
    Continuous (fun s => supportConstant (G s) ε b) ∧
    Continuous (fun s => supportSlope (G s) ε b) := by
  have hw := continuous_finiteProx_parameter G hG hV hN ε hε b
  have hs : Continuous (fun s => ε⁻¹ • (b - finiteProx (G s) ε b)) :=
    continuous_const.smul (continuous_const.sub hw)
  constructor
  · exact (hG.comp (continuous_id.prodMk hw)).sub (hs.inner hw)
  · exact hs

lemma measurable_support_coefficients_substitution {S A : Type*} [MeasurableSpace S]
    [MeasurableSpace A] [PseudoMetricSpace A] [BorelSpace A] [SecondCountableTopology A]
    [Nonempty A] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (G : S → A → H → ℝ)
    (hG : ∀ s y, Measurable (fun x => G x s y))
    (hC : ∀ x, Continuous (fun p : A × H => G x p.1 p.2))
    (hV : ∀ x s, ConvexOn ℝ univ (G x s))
    (ε : ℝ) (hε : 0 < ε) (b : H) (s : S → A) (hs : Measurable s) :
    Measurable (fun x => supportConstant (G x (s x)) ε b) ∧
    Measurable (fun x => supportSlope (G x (s x)) ε b) := by
  have hF (y : H) : Measurable (fun x => G x (s x) y) :=
    measurable_substitution (fun a => hG a y)
      (fun x => (hC x).comp (continuous_id.prodMk continuous_const)) hs
  have hw := measurable_finiteProx (fun x => G x (s x)) hF
    (fun x => (hC x).comp (continuous_const.prodMk continuous_id))
    (fun x => hV x (s x)) ε hε b
  have hb : Measurable (fun x => ε⁻¹ • (b - finiteProx (G x (s x)) ε b)) :=
    measurable_const.smul (measurable_const.sub hw)
  have hval : Measurable (fun x => G x (s x) (finiteProx (G x (s x)) ε b)) :=
    measurable_substitution (fun p => hG p.1 p.2) hC (hs.prodMk hw)
  exact ⟨hval.sub (hb.inner hw), hb⟩

/-- The full source conclusion: one countable family of affine minorants, with
continuous state coefficients and measurable substitution, on one common conull
set. Zero redefinition gives everywhere measurable coefficients. -/
theorem countable_affine_supports : AffineSupportSpecs.countable_affine_supports.{u} := by
  intro S _ μ m D G hG hV hN
  classical
  let A := EuclideanSpace ℝ (Fin m)
  let E := EuclideanSpace ℝ (Fin D)
  obtain ⟨N, G₀, hNm, hN0, hGeq, _, hGm, hGc, hGv, hGn⟩ :=
    regularize_convex_integrand μ G hG hV hN
  let d := TopologicalSpace.denseSeq E
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq E
  let ε (n : ℕ) : ℝ := ((Nat.unpair n).2 + 1 : ℝ)⁻¹
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let c (n : ℕ) (x : S) (s : A) : ℝ :=
    if x ∈ N then 0 else supportConstant (G₀ x s) (ε n) (d (Nat.unpair n).1)
  let b (n : ℕ) (x : S) (s : A) : E :=
    if x ∈ N then 0 else supportSlope (G₀ x s) (ε n) (d (Nat.unpair n).1)
  refine ⟨N, c, b, hNm, hN0, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx n s
    simp only [c, b, ite_eq_left hx, and_self]
  · intro x hx n s y
    have hh := supportValue_le (G₀ x s)
      ((hGc x).comp (continuous_const.prodMk continuous_id)) (hGv x s)
      (ε n) (hε n) (d (Nat.unpair n).1) y
    change supportValue (G₀ x s) (ε n) (d (Nat.unpair n).1) y ≤ G₀ x s y at hh
    simpa only [c, b, ite_eq_right hx, supportValue, AffineSupportSpecs.supportValue,
      supportConstant, supportSlope, hGeq x hx s y] using hh
  · intro x hx s y
    have hh := dense_supports_isLUB (G₀ x s)
      ((hGc x).comp (continuous_const.prodMk continuous_id)) (hGv x s) (hGn x s) d hd y
    have hrange : Set.range (fun n => c n x s + ⟪b n x s, y⟫_ℝ) =
        Set.range (fun p : ℕ × ℕ => supportValue (G₀ x s)
          ((p.2 : ℝ) + 1)⁻¹ (d p.1) y) := by
      ext r
      constructor
      · rintro ⟨n, rfl⟩
        refine ⟨Nat.unpair n, ?_⟩
        simp only [c, b, ite_eq_right hx, ε, supportValue, AffineSupportSpecs.supportValue,
          supportConstant, supportSlope]
      · rintro ⟨⟨i,j⟩, rfl⟩
        refine ⟨Nat.pair i j, ?_⟩
        simp only [c, b, ite_eq_right hx, ε, Nat.unpair_pair, supportValue,
          AffineSupportSpecs.supportValue, supportConstant, supportSlope]
    rw [hrange, ← hGeq x hx s y]
    exact hh
  · intro n x
    by_cases hx : x ∈ N
    · simp only [c, b, ite_eq_left hx]
      exact ⟨continuous_const, continuous_const⟩
    · simpa only [c, b, ite_eq_right hx] using
        continuous_support_coefficients_parameter (G₀ x) (hGc x) (hGv x) (hGn x)
          (ε n) (hε n) (d (Nat.unpair n).1)
  · intro n s hs
    have hh := measurable_support_coefficients_substitution G₀ hGm hGc hGv
      (ε n) (hε n) (d (Nat.unpair n).1) s hs
    exact ⟨measurable_const.piecewise hNm hh.1, measurable_const.piecewise hNm hh.2⟩

end VariationalNotes.Sobolev.AffineSupports
