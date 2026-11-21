import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Models.EventuallyZeroNoncompactResolvent
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.LaplaceResolvent
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal

namespace ExpandedFA.Models.EventuallyZeroNoncompactResolvent
open ExpandedFA.Semigroups ExpandedFA.Unbounded
universe u
variable {𝕜 : Type*} [RCLike 𝕜]
variable {M : Type u} [NormedAddCommGroup M] [InnerProductSpace 𝕜 M] [CompleteSpace M]

abbrev FullState (M : Type u) [NormedAddCommGroup M] := Lp M 2 (volume : Measure ℝ)

private theorem memLp_extend (f : State M) :
    MemLp ((Ioo (0 : ℝ) 1).indicator (f : ℝ → M)) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Ioo.nullMeasurableSet).2 (Lp.memLp f)

/-- Extension by zero from the actual interval L² space. -/
def extend : State M →L[𝕜] FullState M :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_extend f).toLp _
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_extend (f + g)),
          Lp.coeFn_add ((memLp_extend f).toLp _) ((memLp_extend g).toLp _),
          MemLp.coeFn_toLp (memLp_extend f), MemLp.coeFn_toLp (memLp_extend g),
          (ae_restrict_iff' measurableSet_Ioo).1 (Lp.coeFn_add f g)] with s h1 h2 h3 h4 h5
        rw [h1, h2]
        simp only [Pi.add_apply]
        rw [h3, h4]
        by_cases hs : s ∈ Ioo (0 : ℝ) 1
        · simpa only [indicator_of_mem hs, Pi.add_apply] using h5 hs
        · simp only [indicator_of_notMem hs, add_zero]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_extend (c • f)),
          Lp.coeFn_smul c ((memLp_extend f).toLp _),
          MemLp.coeFn_toLp (memLp_extend f),
          (ae_restrict_iff' measurableSet_Ioo).1 (Lp.coeFn_smul c f)] with s h1 h2 h3 h4
        by_cases hs : s ∈ Ioo (0 : ℝ) 1
        · simpa [h1, h2, h3, hs] using h4 hs
        · simp [h1, h2, h3, hs] }
    1 (by
      intro f
      change ‖(memLp_extend f).toLp _‖ ≤ 1 * ‖f‖
      rw [one_mul, Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict
        measurableSet_Ioo.nullMeasurableSet]
      exact le_of_eq (Lp.norm_def f).symm)

theorem extend_rep (f : State M) :
    (extend (𝕜 := 𝕜) f : ℝ → M) =ᵐ[volume] (Ioo (0 : ℝ) 1).indicator (f : ℝ → M) :=
  MemLp.coeFn_toLp (memLp_extend f)

def restrict : FullState M →L[𝕜] State M :=
  LpToLpRestrictCLM ℝ M 𝕜 volume 2 (Ioo 0 1)

theorem restrict_rep (f : FullState M) :
    (restrict (𝕜 := 𝕜) f : ℝ → M) =ᵐ[intervalMeasure] f :=
  LpToLpRestrictCLM_coeFn 𝕜 (Ioo 0 1) f

@[simp] theorem restrict_extend (f : State M) :
    restrict (𝕜 := 𝕜) (extend (𝕜 := 𝕜) f) = f := by
  apply Lp.ext
  filter_upwards [restrict_rep (𝕜 := 𝕜) (extend (𝕜 := 𝕜) f),
    ae_restrict_of_ae (extend_rep (𝕜 := 𝕜) f),
    ae_restrict_mem measurableSet_Ioo] with s h1 h2 hs
  simp [h1, h2, hs]

theorem norm_extend (f : State M) : ‖extend (𝕜 := 𝕜) f‖ = ‖f‖ := by
  change ‖(memLp_extend f).toLp _‖ = _
  rw [Lp.norm_toLp, eLpNorm_indicator_eq_eLpNorm_restrict
    measurableSet_Ioo.nullMeasurableSet, Lp.norm_def]

def fullTranslate (t : ℝ) : FullState M →ₗᵢ[𝕜] FullState M :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (fun s : ℝ => s + t)
    (measurePreserving_add_right (volume : Measure ℝ) t)

theorem fullTranslate_rep (t : ℝ) (f : FullState M) :
    (fullTranslate (𝕜 := 𝕜) t f : ℝ → M) =ᵐ[volume] fun s => f (s + t) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume t)

theorem continuous_fullTranslate (f : FullState M) :
    Continuous (fun t => fullTranslate (𝕜 := 𝕜) t f) := by
  let g : ℝ → C(ℝ, ℝ) := fun t => ⟨fun s => s + t, continuous_id.add continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun t => measurePreserving_add_right volume t) (by norm_num)

/-- Compress the full-line translation by extension and restriction. -/
def shift (t : ℝ≥0) : State M →L[𝕜] State M :=
  (restrict (𝕜 := 𝕜)).comp
    ((fullTranslate (𝕜 := 𝕜) t).toContinuousLinearMap.comp (extend (𝕜 := 𝕜)))

theorem shift_rep (t : ℝ≥0) (f : State M) :
    (shift (𝕜 := 𝕜) t f : ℝ → M) =ᵐ[intervalMeasure]
      fun s => if s + (t : ℝ) < 1 then f (s + t) else 0 := by
  have he := (measurePreserving_add_right volume (t : ℝ)).quasiMeasurePreserving.ae
    (extend_rep (𝕜 := 𝕜) f)
  filter_upwards [restrict_rep (𝕜 := 𝕜) (fullTranslate (𝕜 := 𝕜) t (extend (𝕜 := 𝕜) f)),
    ae_restrict_of_ae (fullTranslate_rep (𝕜 := 𝕜) t (extend (𝕜 := 𝕜) f)),
    ae_restrict_of_ae he, ae_restrict_mem measurableSet_Ioo] with x h1 h2 h3 hx
  change (restrict (𝕜 := 𝕜) (fullTranslate (𝕜 := 𝕜) t (extend (𝕜 := 𝕜) f)) : ℝ → M) x = _
  rw [h1, h2, h3]
  by_cases h : x + (t : ℝ) < 1
  · rw [ite_eq_left h, indicator_of_mem (show x + (t : ℝ) ∈ Ioo (0 : ℝ) 1 from
      ⟨by linarith [hx.1, t.coe_nonneg], h⟩)]
  · rw [ite_eq_right h, indicator_of_notMem (by simpa only [mem_Ioo, not_and] using fun _ => h)]

@[simp] theorem shift_zero : shift (𝕜 := 𝕜) (M := M) 0 = ContinuousLinearMap.id 𝕜 _ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [shift_rep (𝕜 := 𝕜) 0 f, ae_restrict_mem measurableSet_Ioo] with x h hx
  simpa [hx.2] using h

theorem shift_add (t s : ℝ≥0) :
    shift (𝕜 := 𝕜) (M := M) (t + s) = (shift t).comp (shift s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  have hh := (measurePreserving_add_right volume (t : ℝ)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ioo).1 (shift_rep (𝕜 := 𝕜) s f))
  filter_upwards [shift_rep (𝕜 := 𝕜) (t + s) f,
    shift_rep (𝕜 := 𝕜) t (shift (𝕜 := 𝕜) s f), ae_restrict_of_ae hh,
    ae_restrict_mem measurableSet_Ioo] with x h1 h2 h3 hx
  change (shift (𝕜 := 𝕜) (t + s) f : ℝ → M) x =
    (shift (𝕜 := 𝕜) t (shift (𝕜 := 𝕜) s f) : ℝ → M) x
  rw [h1, h2]
  simp only [NNReal.coe_add]
  by_cases h : x + (t : ℝ) < 1
  · rw [ite_eq_left h, h3 ⟨by linarith [hx.1, t.coe_nonneg], h⟩]
    simp only [add_assoc]
  · rw [ite_eq_right h]
    exact ite_eq_right (by linarith [s.coe_nonneg])

theorem norm_shift_le (t : ℝ≥0) (f : State M) :
    ‖shift (𝕜 := 𝕜) t f‖ ≤ ‖f‖ := by
  calc
    _ ≤ ‖fullTranslate (𝕜 := 𝕜) t (extend (𝕜 := 𝕜) f)‖ :=
      norm_Lp_toLp_restrict_le (Ioo 0 1) _
    _ = ‖extend (𝕜 := 𝕜) f‖ := (fullTranslate (𝕜 := 𝕜) t).norm_map _
    _ = ‖f‖ := norm_extend f

theorem continuous_shift (f : State M) :
    Continuous (fun t : ℝ => shift (𝕜 := 𝕜) t.toNNReal f) := by
  exact (restrict (𝕜 := 𝕜)).continuous.comp
    ((continuous_fullTranslate (𝕜 := 𝕜) (extend (𝕜 := 𝕜) f)).comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal))

/-- The killed left translation semigroup, with only the C₀ axioms as data. -/
def translationSemigroup : C0Semigroup 𝕜 (State M) where
  operators := shift
  at_zero := shift_zero
  add_time := shift_add
  strong_zero f := by
    have h := (continuous_shift (𝕜 := 𝕜) f).continuousAt.tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
    simpa using h

theorem translation_formula : ShiftFormula (translationSemigroup (𝕜 := 𝕜) (M := M)) :=
  shift_rep

theorem translation_contractive : Contractive (translationSemigroup (𝕜 := 𝕜) (M := M)) := by
  intro t
  change ‖shift (𝕜 := 𝕜) (M := M) t‖ ≤ 1
  exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
    simpa only [one_mul] using norm_shift_le (𝕜 := 𝕜) t f)

theorem translation_eventuallyZero : EventuallyZero (translationSemigroup (𝕜 := 𝕜) (M := M)) := by
  intro t ht
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [shift_rep (𝕜 := 𝕜) t f, ae_restrict_mem measurableSet_Ioo,
    Lp.coeFn_zero M 2 intervalMeasure] with x h hx hz
  change (shift (𝕜 := 𝕜) t f : ℝ → M) x = (0 : State M) x
  rw [h, hz]
  exact ite_eq_right (by have hle : (1 : ℝ) ≤ t := ht; linarith [hx.1])

theorem eventuallyCompact_of_eventuallyZero (T : C0Semigroup 𝕜 (State M))
    (h : EventuallyZero T) : EventuallyCompact T := by
  intro t ht
  rw [h t ht]
  exact isCompactOperator_zero

theorem construction :
  ∀ (𝕜 : Type*) [RCLike 𝕜] (M : Type u) [NormedAddCommGroup M]
    [InnerProductSpace 𝕜 M] [CompleteSpace M],
    ∃ T : C0Semigroup 𝕜 (State M),
      ShiftFormula T ∧ Contractive T ∧ EventuallyZero T := by
  intro 𝕜 _ M _ _ _
  exact ⟨translationSemigroup, translation_formula, translation_contractive, translation_eventuallyZero⟩

instance intervalMeasure_finite : IsFiniteMeasure intervalMeasure := by
  constructor
  simp [intervalMeasure, Real.volume_Ioo]

/-- Constant multiplicity vectors, as genuine interval L² functions. -/
def constants : M →L[𝕜] State M := Lp.constL 2 intervalMeasure 𝕜

/-- The adjoint of constants is the bounded spatial averaging map. -/
def average : State M →L[𝕜] M := (constants (𝕜 := 𝕜) (M := M)).adjoint

theorem shift_constants (t : ℝ≥0) (m : M) :
    shift (𝕜 := 𝕜) t (constants (𝕜 := 𝕜) m) =
      indicatorConstLp (s := Ioo (0 : ℝ) (1 - (t : ℝ))) 2 measurableSet_Ioo
        (measure_ne_top intervalMeasure _) m := by
  apply Lp.ext
  have hc := (measurePreserving_add_right volume (t : ℝ)).quasiMeasurePreserving.ae
    ((ae_restrict_iff' measurableSet_Ioo).1 (Lp.coeFn_const 2 intervalMeasure m))
  filter_upwards [shift_rep (𝕜 := 𝕜) t (constants (𝕜 := 𝕜) m),
    indicatorConstLp_coeFn (p := 2) (μ := intervalMeasure)
      (s := Ioo 0 (1 - (t : ℝ))) (hs := measurableSet_Ioo)
      (hμs := measure_ne_top _ _) (c := m),
    ae_restrict_of_ae hc, ae_restrict_mem measurableSet_Ioo] with x h1 h2 h3 hx
  rw [h1, h2]
  by_cases h : x + (t : ℝ) < 1
  · rw [ite_eq_left h]
    change Lp.const 2 intervalMeasure m (x + t) = _
    rw [h3 ⟨by linarith [hx.1, t.coe_nonneg], h⟩]
    rw [indicator_of_mem (show x ∈ Ioo (0 : ℝ) (1 - t) from ⟨hx.1, by linarith⟩)]
    rfl
  · rw [ite_eq_right h, indicator_of_notMem (show x ∉ Ioo (0 : ℝ) (1 - t) by
      intro hh; linarith [hh.2])]

local instance : NormedSpace ℝ M := NormedSpace.restrictScalars ℝ 𝕜 M
local instance : IsScalarTower ℝ 𝕜 M := IsScalarTower.restrictScalars ℝ 𝕜 M
local instance : NormedSpace ℝ (State M) := NormedSpace.restrictScalars ℝ 𝕜 (State M)
local instance : IsScalarTower ℝ 𝕜 (State M) := IsScalarTower.restrictScalars ℝ 𝕜 (State M)

local instance : NormedSpace ℝ 𝕜 := RCLike.toInnerProductSpaceReal.toNormedSpace
local instance : NormedSpace ℝ ℝ := RCLike.toInnerProductSpaceReal.toNormedSpace

/-- Spatial averaging of a translated constant records the surviving length. -/
theorem average_shift_constants (t : ℝ≥0) (ht : t ≤ 1) (m : M) :
    average (𝕜 := 𝕜) (shift (𝕜 := 𝕜) t (constants (𝕜 := 𝕜) m)) = (1 - (t : ℝ)) • m := by
  apply ext_inner_left 𝕜
  intro v
  rw [average, ContinuousLinearMap.adjoint_inner_right, shift_constants]
  rw [L2.inner_def]
  have heq :
      (fun x => inner 𝕜 (constants (𝕜 := 𝕜) v x)
        (indicatorConstLp (s := Ioo (0 : ℝ) (1 - (t : ℝ))) 2 measurableSet_Ioo
          (measure_ne_top intervalMeasure _) m x))
        =ᵐ[intervalMeasure]
        (Ioo (0 : ℝ) (1 - (t : ℝ))).indicator (fun _ => inner 𝕜 v m) := by
    filter_upwards [Lp.coeFn_const 2 intervalMeasure v,
      indicatorConstLp_coeFn (p := 2) (μ := intervalMeasure)
        (s := Ioo 0 (1 - (t : ℝ))) (hs := measurableSet_Ioo)
        (hμs := measure_ne_top _ _) (c := m)] with x h1 h2
    change inner 𝕜 (Lp.const 2 intervalMeasure v x) _ = _
    rw [h1, h2]
    by_cases hx : x ∈ Ioo (0 : ℝ) (1 - t) <;> simp [hx]
  calc
    _ = ∫ x, (Ioo (0 : ℝ) (1 - (t : ℝ))).indicator
        (fun _ => inner 𝕜 v m) x ∂intervalMeasure := integral_congr_ae heq
    _ = _ := ?_
  rw [integral_indicator measurableSet_Ioo, setIntegral_const]
  have hμ : intervalMeasure.real (Ioo 0 (1 - (t : ℝ))) = 1 - (t : ℝ) := by
    have hs : Ioo (0 : ℝ) (1 - (t : ℝ)) ⊆ Ioo 0 1 := by
      intro x hx
      exact ⟨hx.1, lt_of_lt_of_le hx.2 (by linarith [t.coe_nonneg])⟩
    rw [measureReal_def, intervalMeasure, Measure.restrict_apply measurableSet_Ioo,
      inter_eq_self_of_subset_left hs, Real.volume_Ioo]
    rw [ENNReal.toReal_ofReal (by have ht' : (t : ℝ) ≤ 1 := ht; linarith)]
    ring
  rw [hμ]
  change (1 - (t : ℝ)) • inner 𝕜 v m = inner 𝕜 v (((1 - (t : ℝ) : ℝ) : 𝕜) • m)
  rw [inner_smul_real_right]

/-- The unweighted integrated orbit of a constant has mean one half. -/
theorem average_integrated_constants (m : M) :
    average (𝕜 := 𝕜) ((translationSemigroup (𝕜 := 𝕜)).integratedOperator 1 (constants (𝕜 := 𝕜) m)) =
      (1 / 2 : ℝ) • m := by
  rw [C0Semigroup.integratedOperator_apply]
  change average (𝕜 := 𝕜) (∫ s : ℝ in (0 : ℝ)..1,
    (translationSemigroup (𝕜 := 𝕜)).operators s.toNNReal (constants (𝕜 := 𝕜) m)) = _
  calc
    _ = ∫ s : ℝ in (0 : ℝ)..1, average (𝕜 := 𝕜)
        ((translationSemigroup (𝕜 := 𝕜)).operators s.toNNReal (constants (𝕜 := 𝕜) m)) :=
      ((average (𝕜 := 𝕜) (M := M)).intervalIntegral_comp_comm
        (((translationSemigroup (𝕜 := 𝕜)).continuous_real_orbit
          (constants (𝕜 := 𝕜) m)).intervalIntegrable 0 1)).symm
    _ = ∫ s : ℝ in (0 : ℝ)..1, (1 - s) • m := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
      change average (𝕜 := 𝕜) (shift (𝕜 := 𝕜) s.toNNReal (constants (𝕜 := 𝕜) m)) = _
      rw [average_shift_constants s.toNNReal (by
        simpa using Real.toNNReal_le_toNNReal hs.2), Real.coe_toNNReal s hs.1]
    _ = (∫ s : ℝ in (0 : ℝ)..1, (1 - s)) • m := intervalIntegral.integral_smul_const (fun s : ℝ => 1 - s) m
    _ = (1 / 2 : ℝ) • m := by
      congr 1
      calc
        _ = (∫ _ : ℝ in (0 : ℝ)..1, (1 : ℝ)) - ∫ s : ℝ in (0 : ℝ)..1, s :=
          intervalIntegral.integral_sub
            ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).intervalIntegrable 0 1)
            (continuous_id.intervalIntegrable 0 1)
        _ = 1 / 2 := by norm_num [intervalIntegral.integral_const, integral_id]

/-- Factoring the identity through a compact operator forces finite dimension. -/
theorem finiteDimensional_of_compact_factor
    {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (R : X →L[𝕜] X) (B : M →L[𝕜] X) (E : X →L[𝕜] M)
    (hR : IsCompactOperator R) (h : ∀ m, E (R (B m)) = m) :
    FiniteDimensional 𝕜 M := by
  apply FiniteDimensional.of_isCompactOperator_id (𝕜 := 𝕜)
  have hc := (hR.comp_clm B).clm_comp E
  convert hc using 1
  funext m
  exact (h m).symm

/-- Integrated constants lie in the exact generator domain, with generator
value minus the original constant. This uses the proved integrated-orbit
identity and the vanishing of the time-one operator. -/
theorem generator_integrated_constants (m : M) :
    C0SemigroupSpec.generatorValue (translationSemigroup (𝕜 := 𝕜))
      ⟨(translationSemigroup (𝕜 := 𝕜)).integratedOperator 1 (constants (𝕜 := 𝕜) m),
        (translationSemigroup (𝕜 := 𝕜)).integratedOperator_mem_domain 1
          (constants (𝕜 := 𝕜) m)⟩ = -constants (𝕜 := 𝕜) m := by
  let T := translationSemigroup (𝕜 := 𝕜) (M := M)
  have hlim := T.integratedOperator_hasGeneratorLimit 1 (constants (𝕜 := 𝕜) m)
  have hz : T.operators 1 = 0 := translation_eventuallyZero 1 le_rfl
  rw [hz, zero_apply, zero_sub] at hlim
  exact generator_limit_unique T _ _ _
    (generator_has_limit T ⟨_, T.integratedOperator_mem_domain 1 (constants (𝕜 := 𝕜) m)⟩)
    hlim

/-- Every resolvent of the killed translation generator is noncompact when
its multiplicity space is infinite dimensional. -/
theorem resolvent_noncompact (hM : ¬ FiniteDimensional 𝕜 M) (ζ : 𝕜)
    (R : ResolventInverse
      (C0SemigroupSpec.generatorValue (translationSemigroup (𝕜 := 𝕜) (M := M))) ζ) :
    ¬ IsCompactOperator R.inverse := by
  intro hR
  let T := translationSemigroup (𝕜 := 𝕜) (M := M)
  let J : M →L[𝕜] State M := (T.integratedOperator 1).comp (constants (𝕜 := 𝕜))
  let B : M →L[𝕜] State M := ζ • J + constants (𝕜 := 𝕜)
  let E : State M →L[𝕜] M := (2 : 𝕜) • average (𝕜 := 𝕜)
  apply hM
  apply finiteDimensional_of_compact_factor R.inverse B E hR
  intro m
  have hr : R.inverse (B m) = J m := by
    have h := R.left_inverse
      ⟨T.integratedOperator 1 (constants (𝕜 := 𝕜) m),
        T.integratedOperator_mem_domain 1 (constants (𝕜 := 𝕜) m)⟩
    rw [generator_integrated_constants] at h
    simpa only [B, J, _root_.add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, sub_neg_eq_add] using h
  rw [hr]
  change (2 : 𝕜) • average (𝕜 := 𝕜)
    (T.integratedOperator 1 (constants (𝕜 := 𝕜) m)) = m
  rw [average_integrated_constants]
  change (2 : 𝕜) • (((1 / 2 : ℝ) : 𝕜) • m) = m
  rw [smul_smul]
  norm_num [map_ofNat]

/-- The contraction bound supplies a genuine resolvent at the positive
parameter 1 through the upstream Laplace-resolvent theorem. -/
theorem resolvent_at_one :
    Nonempty (ResolventInverse
      (C0SemigroupSpec.generatorValue (translationSemigroup (𝕜 := 𝕜) (M := M))) (1 : 𝕜)) := by
  have hb : C0SemigroupSpec.exponentialBoundValue
      (translationSemigroup (𝕜 := 𝕜) (M := M)) 1 0 := by
    refine ⟨le_rfl, ?_⟩
    intro t
    simpa using translation_contractive (𝕜 := 𝕜) (M := M) t
  obtain ⟨R, _⟩ := LaplaceResolvent.laplace_inverse
    (translationSemigroup (𝕜 := 𝕜) (M := M)) 1 0 1 hb (by simp)
  exact ⟨R⟩

theorem counterexample :
  ∀ (𝕜 : Type*) [RCLike 𝕜] (M : Type u) [NormedAddCommGroup M]
    [InnerProductSpace 𝕜 M] [CompleteSpace M],
    ¬ FiniteDimensional 𝕜 M →
    ∃ T : C0Semigroup 𝕜 (State M),
      ShiftFormula T ∧ Contractive T ∧ EventuallyZero T ∧ EventuallyCompact T ∧
      ∃ R : ResolventInverse (C0SemigroupSpec.generatorValue T) (1 : 𝕜),
        ¬ IsCompactOperator R.inverse ∧ NoCompactResolvent T := by
  intro 𝕜 _ M _ _ _ hM
  refine ⟨translationSemigroup, translation_formula, translation_contractive,
    translation_eventuallyZero,
    eventuallyCompact_of_eventuallyZero _ translation_eventuallyZero, ?_⟩
  exact ⟨resolvent_at_one.some, resolvent_noncompact hM 1 resolvent_at_one.some,
    resolvent_noncompact hM⟩

end ExpandedFA.Models.EventuallyZeroNoncompactResolvent
