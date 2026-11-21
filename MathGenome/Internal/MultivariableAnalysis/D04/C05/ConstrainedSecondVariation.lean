import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ConstrainedSecondVariation
import MathGenome.Internal.MultivariableAnalysis.D04.C05.ConstrainedHessianBridge
import MathGenome.Internal.MultivariableAnalysis.D04.C05.SecondOrderTests
import MathGenome.Internal.MultivariableAnalysis.D04.C02.LipschitzConstancy

noncomputable section
open Set Filter Topology
namespace D04.ConstrainedSecondVariation
open Specs.D04.C04.RegularLevel.Model
open Specs.D04.C05.ExtremaInterfaces.Model
open ConstrainedHessianBridge

private theorem exists_chart {n q : ℕ} {U : Set (E n)} {g : E n → E q}
    {c : E q} {a : E n} (hU : IsOpen U) (hg : ContDiffOn ℝ 2 g U)
    (ha : a ∈ level U g c) (hs : Function.Surjective (fderiv ℝ g a)) :
    ∃ (d : LevelGraph 2 U g c) (u : E (n-q)), u ∈ d.A ∧ d.θ u = a := by
  obtain ⟨_,d,had,_⟩ := RegularLevel.regular_level_local 2 U g c a
    (by constructor <;> norm_num [Specs.D04.C14.EmbeddedManifoldCharts.Model.ManifoldRegularity])
    hU hg ha hs
  exact ⟨d,d.projection a,RegularLevel.LevelGraph.inverse_mem d a ⟨ha,had⟩⟩

private theorem chart_twice {n q : ℕ} {U : Set (E n)} {f : E n → ℝ}
    {g : E n → E q} {c : E q} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (d : LevelGraph 2 U g c) {u : E (n-q)} (hu : u ∈ d.A) :
    TimesDifferentiableAt 2 d.A (f ∘ d.θ) u := by
  have hF := hf.comp (RegularLevel.LevelGraph.theta_regular d)
    (fun v hv => (RegularLevel.LevelGraph.theta_mem d v hv).1.1)
  exact crOn_timesDifferentiableAt 2 d.A _ d.open_A
    ((crOn_iff_contDiffOn 2 d.A _ d.open_A).mpr hF) u hu

private theorem diagonal_pair {k : ℕ} (T : Differential (E k) ℝ 2) (v : E k) :
    differentialDiagonal T v = T ![v,v] := by
  change T (fun _ => v) = T ![v,v]
  apply congrArg T
  funext i
  fin_cases i <;> rfl

private theorem chart_minimum {n q : ℕ} {U : Set (E n)} {f : E n → ℝ}
    {g : E n → E q} {c : E q} (d : LevelGraph 2 U g c) {u : E (n-q)}
    (hu : u ∈ d.A) (hm : LocalMinimumOn (level U g c) f (d.θ u)) :
    LocalMinimumOn d.A (f ∘ d.θ) u := by
  apply (localMinimumOn_iff _ _ _).mpr
  refine ⟨hu, ?_⟩
  exact ((localMinimumOn_iff _ _ _).mp hm).2.comp_continuousOn
    (fun v hv => (RegularLevel.LevelGraph.theta_mem d v hv).1)
    (RegularLevel.LevelGraph.theta_regular d).continuousOn hu

private theorem chart_maximum {n q : ℕ} {U : Set (E n)} {f : E n → ℝ}
    {g : E n → E q} {c : E q} (d : LevelGraph 2 U g c) {u : E (n-q)}
    (hu : u ∈ d.A) (hm : LocalMaximumOn (level U g c) f (d.θ u)) :
    LocalMaximumOn d.A (f ∘ d.θ) u := by
  apply (localMaximumOn_iff _ _ _).mpr
  refine ⟨hu, ?_⟩
  exact ((localMaximumOn_iff _ _ _).mp hm).2.comp_continuousOn
    (fun v hv => (RegularLevel.LevelGraph.theta_mem d v hv).1)
    (RegularLevel.LevelGraph.theta_regular d).continuousOn hu

theorem constrained_minimum :
    Specs.D04.C05.ConstrainedSecondVariation.constrained_minimumType := by
  intro n q U f g c a lam hU hf hg ha hs hstat hm v hv
  obtain ⟨d,u,hu,hea⟩ := exists_chart hU hg ha hs
  obtain ⟨e,he⟩ := chart_tangent_isomorphism hU hg d u hu
  obtain ⟨w,hw⟩ := e.surjective ⟨v,by change fderiv ℝ g (d.θ u) v = 0; rwa [hea]⟩
  have hew : fderiv ℝ d.θ u w = v := (he w).symm.trans (congrArg Subtype.val hw)
  have hm' : LocalMinimumOn (level U g c) f (d.θ u) := hea.symm ▸ hm
  have hsecond := (secondOrder_minimum d.A (f ∘ d.θ) u (chart_twice hU hf d hu)
    (chart_minimum d hu hm')).2 w
  change 0 ≤ differentialDiagonal (higherDifferential 2 (f ∘ d.θ) u) w at hsecond
  rw [diagonal_pair, (chart_second_variation hU hf hg lam d u a hu hea hs hstat).2.2 w,
    hew] at hsecond
  exact hsecond

theorem constrained_maximum :
    Specs.D04.C05.ConstrainedSecondVariation.constrained_maximumType := by
  intro n q U f g c a lam hU hf hg ha hs hstat hm v hv
  obtain ⟨d,u,hu,hea⟩ := exists_chart hU hg ha hs
  obtain ⟨e,he⟩ := chart_tangent_isomorphism hU hg d u hu
  obtain ⟨w,hw⟩ := e.surjective ⟨v,by change fderiv ℝ g (d.θ u) v = 0; rwa [hea]⟩
  have hew : fderiv ℝ d.θ u w = v := (he w).symm.trans (congrArg Subtype.val hw)
  have hm' : LocalMaximumOn (level U g c) f (d.θ u) := hea.symm ▸ hm
  have hsecond := (secondOrder_maximum d.A (f ∘ d.θ) u (chart_twice hU hf d hu)
    (chart_maximum d hu hm')).2 w
  change differentialDiagonal (higherDifferential 2 (f ∘ d.θ) u) w ≤ 0 at hsecond
  rw [diagonal_pair, (chart_second_variation hU hf hg lam d u a hu hea hs hstat).2.2 w,
    hew] at hsecond
  exact hsecond

/-- A local graph's Lipschitz bound converts coordinate growth into growth
in the original Euclidean distance, including a zero-dimensional source. -/
private theorem chart_growth {n q : ℕ} {U : Set (E n)} {f : E n → ℝ}
    {g : E n → E q} {c : E q} (d : LevelGraph 2 U g c) {u : E (n-q)}
    (hu : u ∈ d.A) {b : ℝ} (hb : 0 < b)
    (hgrowth : ∀ᶠ w in 𝓝 u, f (d.θ u) + b * ‖w-u‖^2 ≤ f (d.θ w)) :
    ∃ c₀ > 0, ∃ ρ > 0, ∀ x ∈ level U g c, ‖x-d.θ u‖ < ρ →
      f (d.θ u) + c₀ * ‖x-d.θ u‖^2 ≤ f x := by
  have ht : CrOn 1 d.A d.θ := (crOn_iff_contDiffOn 1 d.A d.θ d.open_A).mpr
    ((RegularLevel.LevelGraph.theta_regular d).of_le (by norm_num))
  obtain ⟨r,hr,_,M,hM,hLip⟩ := locally_lipschitz_of_crOn_one d.A d.θ d.open_A ht u hu
  let C := M+1
  have hC : 0 < C := by dsimp [C]; linarith
  have hC2 : 0 < C^2 := sq_pos_of_pos hC
  have hevent : ∀ᶠ w in 𝓝 u,
      f (d.θ u) + (b/C^2) * ‖d.θ w-d.θ u‖^2 ≤ f (d.θ w) := by
    filter_upwards [hgrowth, Metric.ball_mem_nhds u hr] with w hw hwr
    have hL := hLip u (Metric.mem_ball_self hr) w hwr
    have hL' : ‖d.θ w-d.θ u‖ ≤ C * ‖w-u‖ := by
      have hnon := norm_nonneg (w-u)
      dsimp [C]
      nlinarith
    have hsq : ‖d.θ w-d.θ u‖^2 ≤ C^2 * ‖w-u‖^2 := by
      nlinarith only [mul_self_le_mul_self (norm_nonneg _) hL']
    have hmul : (b/C^2)*‖d.θ w-d.θ u‖^2 ≤ b*‖w-u‖^2 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hC2).mpr
      nlinarith
    linarith
  have hp : Tendsto d.projection (𝓝 (d.θ u)) (𝓝 u) := by
    simpa only [RegularLevel.LevelGraph.projection_theta] using
      (d.projection.continuous.continuousAt (x := d.θ u)).tendsto
  have hlocal : ∀ᶠ x in 𝓝 (d.θ u), x ∈ level U g c →
      f (d.θ u) + (b/C^2) * ‖x-d.θ u‖^2 ≤ f x := by
    filter_upwards [hp.eventually hevent,
      (RegularLevel.LevelGraph.ambient_open d).mem_nhds
        (RegularLevel.LevelGraph.theta_mem d u hu).2] with x hx hxD hxM
    rwa [(RegularLevel.LevelGraph.inverse_mem d x ⟨hxM,hxD⟩).2] at hx
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp hlocal
  exact ⟨b/C^2,div_pos hb hC2,ρ,hρ,fun x hx hxρ => hball
    (by simpa only [Metric.mem_ball, dist_eq_norm] using hxρ) hx⟩

private theorem strict_of_growth {n : ℕ} {S : Set (E n)} {f : E n → ℝ}
    {a : E n} (ha : a ∈ S) {b ρ : ℝ} (hb : 0 < b) (hρ : 0 < ρ)
    (h : ∀ x ∈ S, ‖x-a‖ < ρ → f a + b*‖x-a‖^2 ≤ f x) :
    StrictLocalMinimumOn S f a := by
  refine ⟨ha,ρ,hρ,fun x hx hxρ hxa => ?_⟩
  have hpos := mul_pos hb (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxa)))
  linarith [h x hx hxρ]

theorem constrained_positive :
    Specs.D04.C05.ConstrainedSecondVariation.constrained_positiveType := by
  intro n q U f g c a lam hU hf hg ha hs hstat hpos
  obtain ⟨d,u,hu,hea⟩ := exists_chart hU hg ha hs
  have hvariation := chart_second_variation hU hf hg lam d u a hu hea hs hstat
  have hinj := RegularLevel.LevelGraph.derivative_injective d (by norm_num) u hu
  obtain ⟨e,he⟩ := chart_tangent_isomorphism hU hg d u hu
  have hpositive : ∀ w, w ≠ 0 →
      0 < differentialDiagonal (higherDifferential 2 (f ∘ d.θ) u) w := by
    intro w hw
    rw [diagonal_pair, hvariation.2.2 w]
    apply hpos
    · have hv := (e w).property
      rwa [he w,hea] at hv
    · exact fun hz => hw (hinj (by simpa using hz))
  obtain ⟨_,b,hb,ρ,hρ,hgrow⟩ := secondOrder_positive d.A (f ∘ d.θ) u
    (chart_twice hU hf d hu) hvariation.2.1 hpositive
  have hevent : ∀ᶠ w in 𝓝 u,
      f (d.θ u)+b*‖w-u‖^2 ≤ f (d.θ w) := by
    filter_upwards [Metric.ball_mem_nhds u hρ] with w hw
    simpa only [Function.comp_apply, add_sub_cancel] using
      (hgrow (w-u) (by simpa only [Metric.mem_ball,dist_eq_norm] using hw)).2
  obtain ⟨c₀,hc₀,r,hr,h⟩ := chart_growth d hu hb hevent
  rw [hea] at h
  exact ⟨strict_of_growth ha hc₀ hr h,c₀,hc₀,r,hr,h⟩

theorem constrained_negative :
    Specs.D04.C05.ConstrainedSecondVariation.constrained_negativeType := by
  intro n q U f g c a lam hU hf hg ha hs hstat hneg
  obtain ⟨d,u,hu,hea⟩ := exists_chart hU hg ha hs
  have hvariation := chart_second_variation hU hf hg lam d u a hu hea hs hstat
  have hinj := RegularLevel.LevelGraph.derivative_injective d (by norm_num) u hu
  obtain ⟨e,he⟩ := chart_tangent_isomorphism hU hg d u hu
  have hnegative : ∀ w, w ≠ 0 →
      differentialDiagonal (higherDifferential 2 (f ∘ d.θ) u) w < 0 := by
    intro w hw
    rw [diagonal_pair, hvariation.2.2 w]
    apply hneg
    · have hv := (e w).property
      rwa [he w,hea] at hv
    · exact fun hz => hw (hinj (by simpa using hz))
  obtain ⟨_,b,hb,ρ,hρ,hgrow⟩ := secondOrder_negative d.A (f ∘ d.θ) u
    (chart_twice hU hf d hu) hvariation.2.1 hnegative
  have hevent : ∀ᶠ w in 𝓝 u,
      (-f) (d.θ u)+b*‖w-u‖^2 ≤ (-f) (d.θ w) := by
    filter_upwards [Metric.ball_mem_nhds u hρ] with w hw
    have h := (hgrow (w-u) (by simpa only [Metric.mem_ball,dist_eq_norm] using hw)).2
    simp only [Function.comp_apply, add_sub_cancel] at h
    change -f (d.θ u)+b*‖w-u‖^2 ≤ -f (d.θ w)
    linarith
  obtain ⟨c₀,hc₀,r,hr,h⟩ := chart_growth (f := -f) d hu hb hevent
  rw [hea] at h
  have hstrict := strict_of_growth ha hc₀ hr h
  refine ⟨?_,c₀,hc₀,r,hr,?_⟩
  · obtain ⟨_,ε,hε,hh⟩ := hstrict
    exact ⟨ha,ε,hε,fun x hx hxε hxa => neg_lt_neg_iff.mp (hh x hx hxε hxa)⟩
  · intro x hx hxr
    have hh := h x hx hxr
    change -f a + c₀*‖x-a‖^2 ≤ -f x at hh
    linarith

private theorem chart_saddle {n q : ℕ} {U : Set (E n)} {f : E n → ℝ}
    {g : E n → E q} {c : E q} (d : LevelGraph 2 U g c) {u : E (n-q)}
    (hu : u ∈ d.A) (hsaddle : SaddlePoint d.A (f ∘ d.θ) u) :
    SaddlePoint (level U g c) f (d.θ u) := by
  refine ⟨(RegularLevel.LevelGraph.theta_mem d u hu).1, fun r hr => ?_⟩
  have hc := (RegularLevel.LevelGraph.theta_regular d).continuousOn.continuousAt
    (d.open_A.mem_nhds hu)
  have he : ∀ᶠ w in 𝓝 u, ‖d.θ w-d.θ u‖ < r := by
    change d.θ ⁻¹' Metric.ball (d.θ u) r ∈ 𝓝 u
    exact hc.preimage_mem_nhds (Metric.ball_mem_nhds (d.θ u) hr)
  obtain ⟨δ,hδ,hδball⟩ := Metric.mem_nhds_iff.mp he
  obtain ⟨⟨v,hv,hvδ,hfv⟩,⟨w,hw,hwδ,hfw⟩⟩ := hsaddle.2 δ hδ
  exact ⟨⟨d.θ v,(RegularLevel.LevelGraph.theta_mem d v hv).1,
      hδball (by simpa only [Metric.mem_ball,dist_eq_norm] using hvδ),hfv⟩,
    ⟨d.θ w,(RegularLevel.LevelGraph.theta_mem d w hw).1,
      hδball (by simpa only [Metric.mem_ball,dist_eq_norm] using hwδ),hfw⟩⟩

theorem constrained_indefinite :
    Specs.D04.C05.ConstrainedSecondVariation.constrained_indefiniteType := by
  intro n q U f g c a lam hU hf hg ha hs hstat hpos hneg
  obtain ⟨d,u,hu,hea⟩ := exists_chart hU hg ha hs
  obtain ⟨e,he⟩ := chart_tangent_isomorphism hU hg d u hu
  have hvariation := (chart_second_variation hU hf hg lam d u a hu hea hs hstat).2.2
  have hpositive : ∃ w, 0 < differentialDiagonal (higherDifferential 2 (f ∘ d.θ) u) w := by
    obtain ⟨v,hv,hpv⟩ := hpos
    obtain ⟨w,hw⟩ := e.surjective ⟨v,by change fderiv ℝ g (d.θ u) v = 0; rwa [hea]⟩
    refine ⟨w,?_⟩
    rw [diagonal_pair,hvariation w,← he w,congrArg Subtype.val hw]
    exact hpv
  have hnegative : ∃ w, differentialDiagonal (higherDifferential 2 (f ∘ d.θ) u) w < 0 := by
    obtain ⟨v,hv,hnv⟩ := hneg
    obtain ⟨w,hw⟩ := e.surjective ⟨v,by change fderiv ℝ g (d.θ u) v = 0; rwa [hea]⟩
    refine ⟨w,?_⟩
    rw [diagonal_pair,hvariation w,← he w,congrArg Subtype.val hw]
    exact hnv
  have h := chart_saddle d hu (secondOrder_indefinite d.A (f ∘ d.θ) u
    (chart_twice hU hf d hu) hpositive hnegative)
  rwa [hea] at h

theorem constrained_zero_kernel :
    Specs.D04.C05.ConstrainedSecondVariation.constrained_zero_kernelType := by
  intro n q U f g c a hU hg ha hs hker
  obtain ⟨d,u,hu,hea⟩ := exists_chart hU hg ha hs
  obtain ⟨e,he⟩ := chart_tangent_isomorphism hU hg d u hu
  have htzero (w : E (n-q)) : fderiv ℝ d.θ u w = 0 := by
    have hv := (e w).property
    rw [he w] at hv
    rw [hea,hker] at hv
    exact hv
  have hinj := RegularLevel.LevelGraph.derivative_injective d (by norm_num) u hu
  have hcoord (w : E (n-q)) : w = u := hinj ((htzero w).trans (htzero u).symm)
  have had : a ∈ d.ambient := hea ▸ (RegularLevel.LevelGraph.theta_mem d u hu).2
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp
    ((RegularLevel.LevelGraph.ambient_open d).mem_nhds had)
  have hsingle : ∀ x ∈ level U g c, ‖x-a‖ < ρ → x = a := by
    intro x hx hxr
    have hxD := hball (by simpa only [Metric.mem_ball,dist_eq_norm] using hxr)
    have heq := (RegularLevel.LevelGraph.inverse_mem d x ⟨hx,hxD⟩).2
    rw [hcoord (d.projection x),hea] at heq
    exact heq.symm
  refine ⟨⟨ρ,hρ,hsingle⟩,⟨ha,ρ,hρ,?_⟩,⟨ha,ρ,hρ,?_⟩⟩ <;>
    intro x hx hxr hxa <;> exact (hxa (hsingle x hx hxr)).elim

end D04.ConstrainedSecondVariation
