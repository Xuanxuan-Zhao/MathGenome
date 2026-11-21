import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinRealSpectralModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SelfAdjointRangeCriterion
import Mathlib.Tactic.Module
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.VonNeumann.MultiplicityExistence
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ExpandedFA.PartIV.KreinRealSpectralModel
open Unbounded KreinSpectralKernel

/-- The zero measure realizes every operator on the zero Hilbert space. -/
theorem zero_model : Spec.ZeroModel := by
  intro H _ _ _ _ S
  let : Subsingleton (Lp FiberSpace 2 (0 : Measure ℝ)) := ⟨fun f g => by
    apply Lp.ext
    rw [Filter.EventuallyEq, ae_zero]
    exact Filter.eventually_bot⟩
  let U : H →ₗᵢ[ℂ] Lp FiberSpace 2 (0 : Measure ℝ) :=
    { (0 : H →ₗ[ℂ] Lp FiberSpace 2 (0 : Measure ℝ)) with
      norm_map' := fun x => by simp [Subsingleton.elim x 0] }
  let M : RealSpectralModel S :=
    { μ := 0
      finite := inferInstance
      multiplicity := fun _ => 1
      measurable_multiplicity := measurable_const
      positive_multiplicity := by simp
      U := U
      range_eq := by
        ext f
        constructor
        · intro _; simp
        · intro _; exact ⟨0, Subsingleton.elim _ _⟩
      graph_iff := by
        intro x y
        constructor
        · intro _
          rw [Filter.EventuallyEq, ae_zero]
          exact Filter.eventually_bot
        · intro _
          have hx : x ∈ S.domain := by
            rw [Subsingleton.elim x 0]
            exact S.domain.zero_mem
          exact ⟨hx, Subsingleton.elim _ _⟩ }
  exact ⟨M, rfl⟩

/-- A self-adjoint operator is closed and symmetric, with no extra domain
hypothesis beyond the density already contained in self-adjointness. -/
private theorem closed_symmetric {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : Operator ℂ H H)
    (hS : SymmetryAndDeficienciesSpec.selfAdjointValue S) :
    IsClosed S ∧ IsSymmetric S := by
  have hs : Unbounded.IsSelfAdjoint S := hS
  refine ⟨?_, hs.1, hs.2.le⟩
  rw [hs.2]
  exact hilbertAdjoint_isClosed S hs.1

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem sub_shift_bijective (S : Operator ℂ H H)
    (hS : SymmetryAndDeficienciesSpec.selfAdjointValue S) (z : ℂ) (hz : z.im ≠ 0) :
    Function.Bijective (S.toFun - z • S.domain.subtype) := by
  have hsa : Unbounded.IsSelfAdjoint S := hS
  obtain ⟨hc, hs⟩ := closed_symmetric S hS
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    have h := hs.nonreal_lower_bound z x
    change S x - z • (x : H) = 0 at hx
    rw [hx, norm_zero] at h
    have hp : 0 < |z.im| := abs_pos.mpr hz
    have hn : ‖(x : H)‖ = 0 := by nlinarith [norm_nonneg (x : H)]
    exact Subtype.ext (norm_eq_zero.mp hn)
  · apply LinearMap.range_eq_top.mp
    rw [← range_shift_eq_range_sub, closed_symmetric_shift_range S hc hs z hz,
      hsa.deficiencySpace_eq_bot _ (by simpa using hz), Submodule.bot_orthogonal_eq_top]

/-- The unitary Cayley transform and its full inverse graph. -/
theorem cayley_exists : Spec.CayleyExistence := by
  intro H _ _ _ S hS
  have hs := (closed_symmetric S hS).2
  let P : S.domain →ₗ[ℂ] H := S.toFun + Complex.I • S.domain.subtype
  let Q : S.domain →ₗ[ℂ] H := S.toFun - Complex.I • S.domain.subtype
  have hp : Function.Bijective P := by
    simpa only [sub_neg_eq_add, neg_smul] using
      sub_shift_bijective S hS (-Complex.I) (by simp)
  have hq : Function.Bijective Q := sub_shift_bijective S hS Complex.I (by simp)
  let eP : S.domain ≃ₗ[ℂ] H := LinearEquiv.ofBijective P hp
  let eQ : S.domain ≃ₗ[ℂ] H := LinearEquiv.ofBijective Q hq
  have hnorm (x : S.domain) : ‖Q x‖ = ‖P x‖ := by
    have h1 := hs.norm_sub_sq Complex.I x
    have h2 := hs.norm_sub_sq (-Complex.I) x
    simp only [Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im,
      neg_zero, Complex.ofReal_zero, zero_smul, sub_zero, abs_one, abs_neg,
      one_pow, one_mul, neg_smul, sub_neg_eq_add] at h1 h2
    change ‖S x - Complex.I • (x : H)‖ = ‖S x + Complex.I • (x : H)‖
    nlinarith [norm_nonneg (S x - Complex.I • (x : H)),
      norm_nonneg (S x + Complex.I • (x : H))]
  let V : H ≃ₗᵢ[ℂ] H :=
    { eP.symm.trans eQ with
      norm_map' := fun x => by
        change ‖Q (eP.symm x)‖ = ‖x‖
        rw [hnorm]
        exact congrArg norm (eP.apply_symm_apply x) }
  have hv (x : S.domain) : V (S x + Complex.I • (x : H)) =
      S x - Complex.I • (x : H) := by
    change eQ (eP.symm (eP x)) = Q x
    rw [eP.symm_apply_apply]
    rfl
  have graph (x y : H) :
      (∃ hx : x ∈ S.domain, S ⟨x, hx⟩ = y) ↔
      V (y + Complex.I • x) = y - Complex.I • x := by
    constructor
    · rintro ⟨hx, rfl⟩
      exact hv ⟨x, hx⟩
    · intro h
      let a := eP.symm (y + Complex.I • x)
      have ha : S a + Complex.I • (a : H) = y + Complex.I • x :=
        eP.apply_symm_apply _
      have hb : S a - Complex.I • (a : H) = y - Complex.I • x := by
        rw [← hv, ha, h]
      have hdiff : (2 * Complex.I) • (a : H) = (2 * Complex.I) • x := by
        calc
          _ = (S a + Complex.I • (a : H)) -
              (S a - Complex.I • (a : H)) := by module
          _ = (y + Complex.I • x) - (y - Complex.I • x) := by rw [ha, hb]
          _ = _ := by module
      have hax : (a : H) = x :=
        (smul_right_injective H (by norm_num : (2 : ℂ) * Complex.I ≠ 0)) hdiff
      refine ⟨hax ▸ a.prop, ?_⟩
      have haction : S a = y := by rw [hax] at ha; exact add_right_cancel ha
      simpa only [← hax] using haction
  refine ⟨V, hv, ?_, graph⟩
  intro x hx
  have hgraph := (graph 0 x).mpr (by simpa using hx)
  obtain ⟨h0, h0x⟩ := hgraph
  have : S ⟨0, h0⟩ = 0 := by exact S.map_zero
  exact h0x.symm.trans this

/-- The Borel real coordinate inverse to the Cayley coordinate off its pole. -/
def realCoordinate (z : ℂ) : ℝ := -z.im / (1 - z.re)
/-- The Cayley embedding of the entire real line. -/
def cayleyCoordinate (t : ℝ) : ℂ := ((t : ℂ) - Complex.I) / ((t : ℂ) + Complex.I)
lemma realCoordinate_measurable : Measurable realCoordinate := by
  unfold realCoordinate
  fun_prop
lemma cayleyCoordinate_measurable : Measurable cayleyCoordinate := by
  unfold cayleyCoordinate
  fun_prop
lemma cayley_denominator_ne (t : ℝ) : (t : ℂ) + Complex.I ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
lemma cayleyCoordinate_ne_one (t : ℝ) : cayleyCoordinate t ≠ 1 := by
  rw [cayleyCoordinate, ne_eq, div_eq_one_iff_eq (cayley_denominator_ne t)]
  intro h
  have := congrArg Complex.im h
  norm_num at this
lemma cayleyCoordinate_norm (t : ℝ) : ‖cayleyCoordinate t‖ = 1 := by
  rw [cayleyCoordinate, norm_div]
  have h : ‖(t : ℂ) - Complex.I‖ = ‖(t : ℂ) + Complex.I‖ := by
    simp [Complex.norm_def, Complex.normSq_apply]
  rw [h]
  exact div_self (norm_ne_zero_iff.mpr (cayley_denominator_ne t))
lemma realCoordinate_cayleyCoordinate (t : ℝ) :
    realCoordinate (cayleyCoordinate t) = t := by
  have ht : t ^ 2 + 1 ≠ 0 := by positivity
  simp [realCoordinate, cayleyCoordinate, Complex.div_re, Complex.div_im,
    Complex.normSq_apply]
  field_simp
  ring

lemma realCoordinate_identity {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) :
    (realCoordinate z : ℂ) * (1 - z) = Complex.I * (1 + z) := by
  have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by
    have hn := Complex.normSq_eq_norm_sq z
    rw [hz, Complex.normSq_apply] at hn
    nlinarith [hn]
  have hre : 1 - z.re ≠ 0 := by
    intro he
    have hr : z.re = 1 := by linarith
    have hi : z.im = 0 := by nlinarith [sq_nonneg z.im]
    exact h1 (Complex.ext (by simpa using hr) (by simpa using hi))
  apply Complex.ext
  · change realCoordinate z * (1 - z.re) - 0 * (0 - z.im) =
      0 * (1 + z.re) - 1 * (0 + z.im)
    simp only [realCoordinate, zero_mul, one_mul, zero_add, sub_zero, zero_sub]
    field_simp
  · change realCoordinate z * (0 - z.im) + 0 * (1 - z.re) =
      0 * (0 + z.im) + 1 * (1 + z.re)
    simp only [realCoordinate, zero_mul, one_mul, zero_add, add_zero, zero_sub]
    field_simp
    nlinarith

lemma cayleyCoordinate_realCoordinate {z : ℂ} (hz : ‖z‖ = 1) (h1 : z ≠ 1) :
    cayleyCoordinate (realCoordinate z) = z := by
  have h := realCoordinate_identity hz h1
  rw [cayleyCoordinate, div_eq_iff (cayley_denominator_ne _)]
  linear_combination h

section Transport
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} {r : α → β} {s : β → α}
/-- Pullback along maps inverse almost everywhere is onto the entire L² space. -/
def lpCoordinateEquiv (hr : MeasurePreserving r μ ν) (hs : MeasurePreserving s ν μ)
    (hrs : ∀ᵐ x ∂μ, s (r x) = x) (hsr : ∀ᵐ y ∂ν, r (s y) = y) :
    Lp KreinSpectralKernel.FiberSpace 2 μ ≃ₗᵢ[ℂ] Lp KreinSpectralKernel.FiberSpace 2 ν where
  __ := Lp.compMeasurePreservingₗᵢ ℂ s hs
  invFun := Lp.compMeasurePreserving r hr
  left_inv f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving s hs f) hr,
      hr.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving f hs), hrs] with x h1 h2 h3
    exact h1.trans (h2.trans (congrArg f h3))
  right_inv g := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (Lp.compMeasurePreserving r hr g) hs,
      hs.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving g hr), hsr] with y h1 h2 h3
    exact h1.trans (h2.trans (congrArg g h3))
end Transport
lemma cayley_smul_iff {E : Type*} [AddCommGroup E] [Module ℂ E]
    (t : ℝ) (a b : E) :
    cayleyCoordinate t • (b + Complex.I • a) = b - Complex.I • a ↔
      b = (t : ℂ) • a := by
  have hden := cayley_denominator_ne t
  constructor
  · intro h
    have h' := congrArg (fun x : E => ((t : ℂ) + Complex.I) • x) h
    rw [cayleyCoordinate, smul_smul, mul_div_cancel₀ _ hden] at h'
    have hzero : (2 * Complex.I) • (b - (t : ℂ) • a) = 0 := by
      linear_combination (norm := module) -h'
    have : b - (t : ℂ) • a = 0 := (smul_eq_zero.mp hzero).resolve_left (by norm_num)
    exact sub_eq_zero.mp this
  · rintro rfl
    rw [← add_smul, smul_smul, cayleyCoordinate,
      div_mul_cancel₀ _ hden, sub_smul]

lemma cayley_measurePreserving (μ : Measure ℂ)
    (hμ : ∀ᵐ z ∂μ, ‖z‖ = 1 ∧ z ≠ 1) :
    MeasurePreserving cayleyCoordinate (μ.map realCoordinate) μ := by
  refine ⟨cayleyCoordinate_measurable, ?_⟩
  rw [Measure.map_map cayleyCoordinate_measurable realCoordinate_measurable]
  have hid : cayleyCoordinate ∘ realCoordinate =ᵐ[μ] id := by
    filter_upwards [hμ] with z hz
    exact cayleyCoordinate_realCoordinate hz.1 hz.2
  rw [Measure.map_congr hid, Measure.map_id]

/-- A coordinate change induces an equivalence of the full vector-valued L² spaces. -/
def realLpEquiv (μ : Measure ℂ) (hμ : ∀ᵐ z ∂μ, ‖z‖ = 1 ∧ z ≠ 1) :
    Lp KreinSpectralKernel.FiberSpace 2 μ ≃ₗᵢ[ℂ]
      Lp KreinSpectralKernel.FiberSpace 2 (μ.map realCoordinate) :=
  lpCoordinateEquiv (realCoordinate_measurable.measurePreserving μ)
    (cayley_measurePreserving μ hμ)
    (hμ.mono fun _ hz => cayleyCoordinate_realCoordinate hz.1 hz.2)
    (Filter.Eventually.of_forall realCoordinate_cayleyCoordinate)

lemma realLpEquiv_ae (μ : Measure ℂ) (hμ : ∀ᵐ z ∂μ, ‖z‖ = 1 ∧ z ≠ 1)
    (f : Lp KreinSpectralKernel.FiberSpace 2 μ) :
    realLpEquiv μ hμ f =ᵐ[μ.map realCoordinate] f ∘ cayleyCoordinate :=
  Lp.coeFn_compMeasurePreserving f (cayley_measurePreserving μ hμ)

lemma realLpEquiv_symm_ae (μ : Measure ℂ) (hμ : ∀ᵐ z ∂μ, ‖z‖ = 1 ∧ z ≠ 1)
    (f : Lp KreinSpectralKernel.FiberSpace 2 (μ.map realCoordinate)) :
    (realLpEquiv μ hμ).symm f =ᵐ[μ] f ∘ realCoordinate :=
  Lp.coeFn_compMeasurePreserving f (realCoordinate_measurable.measurePreserving μ)

open VonNeumann.MultiplicityModel.Spec
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
/-- A finite coordinate model cannot charge 1 when the original unitary has
no fixed vectors: a singleton-supported first-coordinate section would be fixed. -/
lemma coordinate_model_no_atom_one (V : H ≃ₗᵢ[ℂ] H)
    (hV : ∀ x, V x = x → x = 0) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (m : Multiplicity μ) (hb : BoundedCoordinate μ) (U : DirectIntegral μ m ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, U (coordinateOperatorValue μ m hb f) = V (U f)) :
    μ {1} = 0 := by
  classical
  let e : FiberSpace := lp.single 2 0 (1 : ℂ)
  have he : e ≠ 0 := by
    intro h
    have := congrArg (fun x : FiberSpace => x 0) h
    simp [e] at this
  have hmem {d : ℕ∞} (hd : 0 < d) : e ∈ fiber d := by
    intro k hk
    by_cases h : k = 0
    · subst k
      exact (hk (by simpa using hd)).elim
    · simp [e, lp.single_apply, h]
  let g : Lp FiberSpace 2 μ :=
    indicatorConstLp 2 (measurableSet_singleton (1 : ℂ)) (measure_lt_top μ _).ne e
  have hg : g =ᵐ[μ] ({1} : Set ℂ).indicator (fun _ => e) := indicatorConstLp_coeFn
  have hgmem : g ∈ directIntegralSubmodule μ m := by
    filter_upwards [hg, m.positive] with z hz hm
    rw [hz]
    by_cases h : z ∈ ({1} : Set ℂ)
    · rw [Set.indicator_of_mem h]
      exact hmem hm
    · rw [Set.indicator_of_notMem h]
      exact (fiber _).zero_mem
  let f : DirectIntegral μ m := ⟨g, hgmem⟩
  have hf : coordinateOperatorValue μ m hb f = f := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [coordinateLpValue_ae hb g, hg] with z hz hgz
    change coordinateLpValue hb g z = g z
    rw [hz, hgz]
    by_cases h : z = 1
    · simp [h]
    · simp [h]
  have hz : (g : Lp FiberSpace 2 μ) = 0 := by
    have hu : U f = 0 := hV _ (by rw [← hU, hf])
    have hfzero : f = 0 := U.injective (by simpa using hu)
    exact congrArg Subtype.val hfzero
  have hne : ∀ᵐ z ∂μ, z ≠ (1 : ℂ) := by
    rw [hz] at hg
    filter_upwards [hg, Lp.coeFn_zero FiberSpace 2 μ] with z hz hzero
    intro h
    subst z
    apply he
    simpa using hz.symm.trans hzero
  simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using hne

omit [CompleteSpace H] in
/-- Transport a bounded Cayley model to the real line, retaining every section
and the exact original graph. The circle and pole conditions are used only
for the Borel change of coordinates. -/
theorem real_model_of_cayley_model (S : Operator ℂ H H) (V : H ≃ₗᵢ[ℂ] H)
    (hgraph : ∀ x y : H, (∃ hx : x ∈ S.domain, S ⟨x, hx⟩ = y) ↔
      V (y + Complex.I • x) = y - Complex.I • x)
    (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, ‖z‖ = 1 ∧ z ≠ 1)
    (m : Multiplicity μ) (hb : BoundedCoordinate μ)
    (U : DirectIntegral μ m ≃ₗᵢ[ℂ] H)
    (hU : ∀ f, U (coordinateOperatorValue μ m hb f) = V (U f)) :
    Nonempty (RealSpectralModel S) := by
  let ν := μ.map realCoordinate
  let er := realLpEquiv μ hμ
  let w : H →ₗᵢ[ℂ] Lp FiberSpace 2 μ :=
    (directIntegralSubmodule μ m).subtypeₗᵢ.comp U.symm.toLinearIsometry
  let W : H →ₗᵢ[ℂ] Lp FiberSpace 2 ν := er.toLinearIsometry.comp w
  have hs := cayley_measurePreserving μ hμ
  have hr := realCoordinate_measurable.measurePreserving μ
  have hw (x : H) : w (V x) =ᵐ[μ] fun z => z • w x z := by
    have hu : coordinateOperatorValue μ m hb (U.symm x) = U.symm (V x) := by
      apply U.injective
      rw [hU, U.apply_symm_apply, U.apply_symm_apply]
    have heq : coordinateLpValue hb (w x) = w (V x) := congrArg Subtype.val hu
    rw [← heq]
    exact coordinateLpValue_ae hb (w x)
  have hW (x : H) : W (V x) =ᵐ[ν] fun t => cayleyCoordinate t • W x t := by
    filter_upwards [realLpEquiv_ae μ hμ (w (V x)),
      realLpEquiv_ae μ hμ (w x), hs.quasiMeasurePreserving.ae (hw x)] with t h1 h2 h3
    change W (V x) t = w (V x) (cayleyCoordinate t) at h1
    change W x t = w x (cayleyCoordinate t) at h2
    rw [h1, h2]
    exact h3
  have hplus (x y : H) : W (y + Complex.I • x) =ᵐ[ν]
      fun t => W y t + Complex.I • W x t := by
    rw [map_add, map_smul]
    filter_upwards [Lp.coeFn_add (W y) (Complex.I • W x),
      Lp.coeFn_smul Complex.I (W x)] with t h1 h2
    simp only [h1, h2, Pi.add_apply, Pi.smul_apply]
  have hminus (x y : H) : W (y - Complex.I • x) =ᵐ[ν]
      fun t => W y t - Complex.I • W x t := by
    rw [map_sub, map_smul]
    filter_upwards [Lp.coeFn_sub (W y) (Complex.I • W x),
      Lp.coeFn_smul Complex.I (W x)] with t h1 h2
    simp only [h1, h2, Pi.sub_apply, Pi.smul_apply]
  refine ⟨{
    μ := ν
    finite := by dsimp [ν]; infer_instance
    multiplicity := fun t => m (cayleyCoordinate t)
    measurable_multiplicity := m.measurable_toFun.comp cayleyCoordinate_measurable
    positive_multiplicity := hs.quasiMeasurePreserving.ae m.positive
    U := W
    range_eq := ?_
    graph_iff := ?_ }⟩
  · ext g
    constructor
    · rintro ⟨x, rfl⟩
      filter_upwards [realLpEquiv_ae μ hμ (w x),
        hs.quasiMeasurePreserving.ae (U.symm x).property] with t h1 h2
      change W x t ∈ _
      change W x t = w x (cayleyCoordinate t) at h1
      rw [h1]
      exact h2
    · intro hg
      let f := er.symm g
      have hf : f ∈ directIntegralSubmodule μ m := by
        filter_upwards [realLpEquiv_symm_ae μ hμ g, hμ,
          hr.quasiMeasurePreserving.ae hg] with z h1 h2 h3
        change f z ∈ _
        change f z = g (realCoordinate z) at h1
        rw [h1]
        simpa only [cayleyCoordinate_realCoordinate h2.1 h2.2] using h3
      refine ⟨U ⟨f, hf⟩, ?_⟩
      change er ((U.symm (U ⟨f, hf⟩) : DirectIntegral μ m) : Lp FiberSpace 2 μ) = g
      rw [U.symm_apply_apply]
      exact er.apply_symm_apply g
  · intro x y
    rw [hgraph]
    constructor
    · intro h
      have heq : W (V (y + Complex.I • x)) = W (y - Complex.I • x) := congrArg W h
      have hc := hW (y + Complex.I • x)
      rw [heq] at hc
      filter_upwards [hc, hplus x y, hminus x y] with t hc hp hm
      exact (cayley_smul_iff t (W x t) (W y t)).mp (by rw [← hp, ← hm]; exact hc.symm)
    · intro h
      apply W.injective
      apply Lp.ext
      filter_upwards [hW (y + Complex.I • x), hplus x y, hminus x y, h] with t hc hp hm ht
      rw [hc, hp, hm]
      exact (cayley_smul_iff t (W x t) (W y t)).mpr ht

/-- The full unbounded real spectral model, including zero Hilbert spaces. -/
theorem exists_model : KreinSpectralKernel.Spec.RealModelExistence := by
  intro H _ _ _ _ S hS
  obtain ⟨V, _, hfix, hgraph⟩ := cayley_exists H S hS
  let N : H →L[ℂ] H := V
  have hunit : N ∈ unitary (H →L[ℂ] H) :=
    (Unitary.linearIsometryEquiv.symm V).property
  have hnormal : IsStarNormal N := isStarNormal_of_mem_unitary hunit
  obtain ⟨E, μ, _, hfinite, hsupport, _, m, hb, U, hU⟩ :=
    VonNeumann.MultiplicityExistence.multiplicity_existence H N hnormal
  let := hfinite
  have hcircle : ∀ᵐ z ∂μ, ‖z‖ = 1 := by
    have hmem : ∀ᵐ z ∂μ, z ∈ spectrum ℂ N := by
      exact ae_iff.mpr hsupport
    exact hmem.mono fun z hz => spectrum.norm_eq_one_of_unitary hunit hz
  have hzero : μ {1} = 0 := coordinate_model_no_atom_one V hfix μ m hb U hU
  have hne : ∀ᵐ z ∂μ, z ≠ (1 : ℂ) := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using hzero
  exact real_model_of_cayley_model S V hgraph μ (hcircle.and hne) m hb U hU

end ExpandedFA.PartIV.KreinRealSpectralModel
