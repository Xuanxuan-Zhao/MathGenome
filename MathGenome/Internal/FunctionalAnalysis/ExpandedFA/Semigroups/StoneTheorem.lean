import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.StoneTheorem
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.GeneratorDeterminesSemigroup
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.UnboundedNormalSpectralTheorem
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SymmetryAndDeficiencies
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open Filter Topology Set
open scoped NNReal
namespace ExpandedFA.Semigroups.Stone
open Unbounded
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace UnitaryGroup

def positive (U : UnitaryGroup H) : C0Semigroup ℂ H where
  operators t := (U.operators t).toLinearIsometry.toContinuousLinearMap
  at_zero := by ext x; exact U.at_zero x
  add_time t s := by ext x; exact U.add_time t s x
  strong_zero x := by
    change Tendsto (fun h : ℝ => U.operators (h.toNNReal : ℝ) x) (𝓝[>] 0) (𝓝 x)
    have hc : Continuous (fun h : ℝ => U.operators (h.toNNReal : ℝ) x) :=
      (U.continuous_orbit x).comp (continuous_subtype_val.comp continuous_real_toNNReal)
    simpa only [Real.toNNReal_zero, NNReal.coe_zero, U.at_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds

@[simp] theorem positive_apply (U : UnitaryGroup H) (t : ℝ≥0) (x : H) :
    U.positive.operators t x = U.operators t x := rfl

@[simp] theorem neg_apply_cancel (U : UnitaryGroup H) (t : ℝ) (x : H) :
    U.operators (-t) (U.operators t x) = x := by
  rw [← U.add_time, neg_add_cancel, U.at_zero]

@[simp] theorem apply_neg_cancel (U : UnitaryGroup H) (t : ℝ) (x : H) :
    U.operators t (U.operators (-t) x) = x := by
  rw [← U.add_time, add_neg_cancel, U.at_zero]

/-- Both time directions are again groups with the original strong continuity. -/
def reverse (U : UnitaryGroup H) : UnitaryGroup H where
  operators t := U.operators (-t)
  at_zero x := by simpa using U.at_zero x
  add_time t s x := by simpa only [neg_add] using U.add_time (-t) (-s) x
  continuous_orbit x := (U.continuous_orbit x).comp continuous_neg

/-- The usual positive-time generator. -/
def infinitesimalGenerator (U : UnitaryGroup H) : Operator ℂ H H :=
  C0SemigroupSpec.generatorValue U.positive

/-- The candidate Stone operator has exactly the derivative generator's domain. -/
def stoneOperator (U : UnitaryGroup H) : Operator ℂ H H :=
  (-Complex.I) • U.infinitesimalGenerator

/-- Strong continuity remains valid with a varying initial vector, since
all the operators are isometries. -/
theorem tendsto_apply (U : UnitaryGroup H) {ι : Type*} {l : Filter ι}
    {t : ι → ℝ} {v : ι → H} {a : ℝ} {x : H}
    (ht : Tendsto t l (𝓝 a)) (hv : Tendsto v l (𝓝 x)) :
    Tendsto (fun i => U.operators (t i) (v i)) l (𝓝 (U.operators a x)) := by
  have hz : Tendsto (fun i => U.operators (t i) (v i - x)) l (𝓝 0) := by
    apply squeeze_zero_norm
    · intro i
      exact le_of_eq ((U.operators (t i)).norm_map (v i - x))
    · simpa only [sub_self, norm_zero] using (hv.sub_const x).norm
  have hx := ((U.continuous_orbit x).tendsto a).comp ht
  simpa only [Function.comp_def, map_sub, sub_add_cancel, zero_add] using hz.add hx

/-- Positive-time generator limits are the restrictions of full-time limits. -/
theorem has_positive_limit_iff (U : UnitaryGroup H) (x y : H) :
    C0SemigroupSpec.hasGeneratorLimitValue U.positive x y ↔
      Tendsto (fun h => differenceQuotient U h x) (𝓝[>] (0 : ℝ)) (𝓝 y) := by
  apply tendsto_congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [C0SemigroupSpec.differenceQuotientValue, differenceQuotient,
    smul_apply, sub_apply,
    ContinuousLinearMap.id_apply, positive_apply]
  rw [Real.coe_toNNReal h (le_of_lt hh)]
  rfl

/-- Negating time changes the quotient by a unitary operator tending to I. -/
theorem differenceQuotient_neg (U : UnitaryGroup H) (h : ℝ) (x : H) :
    differenceQuotient U (-h) x = U.operators (-h) (differenceQuotient U h x) := by
  simp only [differenceQuotient, map_smul, map_sub, neg_apply_cancel,
    Complex.ofReal_neg, inv_neg, neg_smul]
  rw [← smul_neg, neg_sub]

/-- Every right generator limit extends to the two-sided derivative. -/
theorem hasDerivative_iff_positive_limit (U : UnitaryGroup H) (x y : H) :
    HasDerivative U x y ↔ C0SemigroupSpec.hasGeneratorLimitValue U.positive x y := by
  rw [U.has_positive_limit_iff]
  constructor
  · intro h
    exact h.mono_left (nhdsGT_le_nhdsNE 0)
  · intro h
    have hn : Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa only [neg_zero] using
          (continuous_neg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
            Tendsto (fun h : ℝ => -h) (𝓝[<] 0) (𝓝 (- (0 : ℝ))))
      · filter_upwards [self_mem_nhdsWithin] with h hh
        exact neg_pos.mpr (show h < 0 from hh)
    have hh := h.comp hn
    have ht : Tendsto (fun h : ℝ => -(-h)) (𝓝[<] 0) (𝓝 0) := by
      simpa only [neg_zero] using (hn.mono_right nhdsWithin_le_nhds).neg
    have hl := U.tendsto_apply ht hh
    simp only [Function.comp_def, neg_neg, U.at_zero] at hl
    have hl' : Tendsto (fun h => differenceQuotient U h x) (𝓝[<] 0) (𝓝 y) := by
      convert hl using 1
      funext h
      simpa only [neg_neg] using U.differenceQuotient_neg (-h) x
    change Tendsto _ _ _
    rw [← nhdsLT_sup_nhdsGT]
    exact hl'.sup h

/-- Exact graph identification for the two-sided derivative. -/
theorem hasDerivative_iff_mem_graph (U : UnitaryGroup H) (x y : H) :
    HasDerivative U x y ↔ (x, y) ∈ U.infinitesimalGenerator.graph := by
  rw [U.hasDerivative_iff_positive_limit]
  exact (mem_generator_graph_iff U.positive x y).symm

/-- Equality here contains the exact derivative domain as well as its value. -/
theorem derivativeGraph_stoneOperator (U : UnitaryGroup H) :
    DerivativeGraph U U.stoneOperator := by
  have heq : Complex.I • U.stoneOperator = U.infinitesimalGenerator := by
    change Complex.I • ((-Complex.I) • U.infinitesimalGenerator) = _
    rw [smul_smul]
    simp
  intro x y
  rw [heq]
  exact U.hasDerivative_iff_mem_graph x y

theorem generator_dense (U : UnitaryGroup H) :
    Dense (U.infinitesimalGenerator.domain : Set H) :=
  U.positive.generator_domain_dense

theorem generator_closed (U : UnitaryGroup H) : U.infinitesimalGenerator.IsClosed :=
  U.positive.generator_graph_closed

theorem stoneOperator_dense (U : UnitaryGroup H) :
    Dense (U.stoneOperator.domain : Set H) := U.generator_dense

local instance : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
local instance : IsScalarTower ℝ ℂ H := IsScalarTower.restrictScalars ℝ ℂ H

/-- The norm difference-quotient convention agrees with the native real derivative. -/
theorem hasDerivative_iff_hasDerivAt (U : UnitaryGroup H) (x y : H) :
    HasDerivative U x y ↔ HasDerivAt (fun t : ℝ => U.operators t x) y 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  apply tendsto_congr'
  filter_upwards [] with h
  simp only [zero_add, U.at_zero, differenceQuotient]
  rw [← Complex.ofReal_inv]
  rfl

/-- The full derivative at zero, on exactly the positive generator's domain. -/
theorem hasDerivAt_zero (U : UnitaryGroup H) (x : U.infinitesimalGenerator.domain) :
    HasDerivAt (fun t : ℝ => U.operators t x) (U.infinitesimalGenerator x) 0 := by
  apply (U.hasDerivative_iff_hasDerivAt _ _).mp
  apply (U.hasDerivative_iff_positive_limit _ _).mpr
  exact generator_has_limit U.positive x

/-- Translating time gives the usual orbit derivative at every real time. -/
theorem hasDerivAt_orbit (U : UnitaryGroup H) (x : U.infinitesimalGenerator.domain)
    (t : ℝ) :
    HasDerivAt (fun s : ℝ => U.operators s x)
      (U.operators t (U.infinitesimalGenerator x)) t := by
  have hd := ((U.operators t).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (U.hasDerivAt_zero x)
  change HasDerivAt (fun h : ℝ => U.operators t (U.operators h x))
    (U.operators t (U.infinitesimalGenerator x)) 0 at hd
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have hh := hd.tendsto_slope_zero
  apply hh.congr'
  filter_upwards [] with h
  simp only [zero_add, U.at_zero, ← U.add_time]


/-- The unitary identity makes the derivative generator skew symmetric. -/
theorem generator_inner (U : UnitaryGroup H)
    (x y : U.infinitesimalGenerator.domain) :
    inner ℂ (U.infinitesimalGenerator x) (y : H) =
      -inner ℂ (x : H) (U.infinitesimalGenerator y) := by
  have hd := (U.hasDerivAt_zero x).inner ℂ (U.hasDerivAt_zero y)
  have hc : (fun t : ℝ => inner ℂ (U.operators t x) (U.operators t y)) =
      (fun _ : ℝ => inner ℂ (x : H) (y : H)) := by
    funext t
    exact (U.operators t).inner_map_map x y
  rw [hc] at hd
  have he := hd.unique (hasDerivAt_const 0 (inner ℂ (x : H) (y : H)))
  simp only [U.at_zero] at he
  exact eq_neg_of_add_eq_zero_right he

/-- Multiplication by −i converts skew symmetry into the manuscript's symmetry. -/
theorem stoneOperator_symmetric (U : UnitaryGroup H) : IsSymmetric U.stoneOperator := by
  refine ⟨U.stoneOperator_dense, ?_⟩
  apply LinearPMap.IsFormalAdjoint.le_adjoint U.stoneOperator_dense
  intro x y
  change U.infinitesimalGenerator.domain at x y
  change inner ℂ ((-Complex.I) • U.infinitesimalGenerator x) (y : H) =
    inner ℂ (x : H) ((-Complex.I) • U.infinitesimalGenerator y)
  rw [inner_smul_left, inner_smul_right, U.generator_inner]
  simp

/-- A unitary can be transferred to the other slot by reversing time. -/
theorem inner_move (U : UnitaryGroup H) (t : ℝ) (x y : H) :
    inner ℂ (U.operators (-t) x) y = inner ℂ x (U.operators t y) := by
  simpa only [U.apply_neg_cancel] using
    ((U.operators t).inner_map_map (U.operators (-t) x) y).symm

/-- The full generator graph is invariant under every real group time. -/
theorem generator_graph_orbit (U : UnitaryGroup H)
    (x : U.infinitesimalGenerator.domain) (t : ℝ) :
    (U.operators t x, U.operators t (U.infinitesimalGenerator x)) ∈
      U.infinitesimalGenerator.graph := by
  apply (U.hasDerivative_iff_mem_graph _ _).mp
  apply (U.hasDerivative_iff_hasDerivAt _ _).mpr
  have hd := ((U.operators t).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (U.hasDerivAt_zero x)
  change HasDerivAt (fun h : ℝ => U.operators t (U.operators h x))
    (U.operators t (U.infinitesimalGenerator x)) 0 at hd
  convert hd using 1
  funext h
  rw [← U.add_time, ← U.add_time, add_comm]

theorem orbit_mem_generator_domain (U : UnitaryGroup H)
    (x : U.infinitesimalGenerator.domain) (t : ℝ) :
    U.operators t x ∈ U.infinitesimalGenerator.domain := by
  obtain ⟨hx, _⟩ := (Unbounded.mem_graph_iff _ _).mp (U.generator_graph_orbit x t)
  exact hx

theorem generator_orbit (U : UnitaryGroup H)
    (x : U.infinitesimalGenerator.domain) (t : ℝ)
    (hx : U.operators t x ∈ U.infinitesimalGenerator.domain) :
    U.infinitesimalGenerator ⟨U.operators t x, hx⟩ =
      U.operators t (U.infinitesimalGenerator x) := by
  obtain ⟨_, he⟩ := (Unbounded.mem_graph_iff _ _).mp (U.generator_graph_orbit x t)
  exact he

/-- On an adjoint-domain vector, testing against a generator-domain vector
identifies a weak derivative without assuming strong differentiability. -/
theorem weak_hasDerivAt (U : UnitaryGroup H)
    (y : (hilbertAdjoint U.stoneOperator).domain)
    (x : U.infinitesimalGenerator.domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => inner ℂ (x : H) (U.operators s y))
      (inner ℂ (x : H) (U.operators t (Complex.I • hilbertAdjoint U.stoneOperator y))) t := by
  have hd := ((U.hasDerivAt_orbit x (-t)).scomp t (hasDerivAt_neg t)).inner ℂ
    (hasDerivAt_const t (y : H))
  have hf : (fun s : ℝ => inner ℂ (U.operators (-s) x) (y : H)) =
      (fun s : ℝ => inner ℂ (x : H) (U.operators s y)) := by
    funext s
    exact U.inner_move s x y
  simp only [Function.comp_def, inner_zero_right, zero_add,
    neg_one_smul] at hd
  rw [hf] at hd
  convert hd using 1
  rw [← U.inner_move t x]
  let z : U.infinitesimalGenerator.domain :=
    ⟨U.operators (-t) x, U.orbit_mem_generator_domain x (-t)⟩
  have he := hilbertAdjoint_inner U.stoneOperator U.stoneOperator_dense y ⟨z, z.2⟩
  change inner ℂ ((-Complex.I) • U.infinitesimalGenerator z) (y : H) =
    inner ℂ (U.operators (-t) x) (hilbertAdjoint U.stoneOperator y) at he
  have hgz : U.infinitesimalGenerator z = U.operators (-t) (U.infinitesimalGenerator x) :=
    U.generator_orbit x (-t) z.2
  rw [hgz, inner_smul_left] at he
  rw [inner_smul_right, ← he]
  simp only [inner_neg_left, map_neg, Complex.conj_I, neg_neg]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/-- The weak derivative integrates to a vector identity, by density. -/
theorem adjoint_orbit_integral (U : UnitaryGroup H)
    (y : (hilbertAdjoint U.stoneOperator).domain) (t : ℝ) :
    U.operators t y - (y : H) =
      ∫ s in (0 : ℝ)..t, U.operators s (Complex.I • hilbertAdjoint U.stoneOperator y) := by
  apply Dense.eq_of_inner_right (𝕜 := ℂ) U.generator_dense
  intro x hx
  have hc := U.continuous_orbit (Complex.I • hilbertAdjoint U.stoneOperator y)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => U.weak_hasDerivAt y ⟨x, hx⟩ s)
    (((innerSL ℂ x).continuous.comp hc).intervalIntegrable 0 t)
  rw [inner_sub_right]
  change _ = (innerSL ℂ x) (∫ s in (0 : ℝ)..t,
    U.operators s (Complex.I • hilbertAdjoint U.stoneOperator y))
  rw [← (innerSL ℂ x).intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
  simpa only [U.at_zero, innerSL_apply_apply] using hi.symm

/-- The integrated identity upgrades the weak derivative to a norm derivative. -/
theorem adjoint_hasDerivative (U : UnitaryGroup H)
    (y : (hilbertAdjoint U.stoneOperator).domain) :
    HasDerivative U y (Complex.I • hilbertAdjoint U.stoneOperator y) := by
  have hc := U.continuous_orbit (Complex.I • hilbertAdjoint U.stoneOperator y)
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 0) hc.aestronglyMeasurable.stronglyMeasurableAtFilter
      hc.continuousAt).add_const (y : H)
  apply (U.hasDerivative_iff_hasDerivAt _ _).mpr
  have he : (fun t : ℝ =>
      (∫ s in (0 : ℝ)..t, U.operators s (Complex.I • hilbertAdjoint U.stoneOperator y)) + y) =
      (fun t : ℝ => U.operators t y) := by
    funext t
    rw [← U.adjoint_orbit_integral y t, sub_add_cancel]
  rw [he] at hd
  simpa only [U.at_zero, add_zero] using hd

/-- Self-adjointness follows by recovering every adjoint-domain vector from
its strong derivative. This proves equality of the entire domains. -/
theorem stoneOperator_selfAdjoint (U : UnitaryGroup H) : Unbounded.IsSelfAdjoint U.stoneOperator := by
  refine ⟨U.stoneOperator_dense, le_antisymm U.stoneOperator_symmetric.2 ?_⟩
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨hy, hval⟩ := (Unbounded.mem_graph_iff _ _).mp hp
  have hd := U.adjoint_hasDerivative ⟨p.1, hy⟩
  rw [U.derivativeGraph_stoneOperator] at hd
  obtain ⟨hz, he⟩ := (Unbounded.mem_graph_iff _ _).mp hd
  apply (Unbounded.mem_graph_iff _ _).mpr
  refine ⟨hz, ?_⟩
  change Complex.I • U.stoneOperator ⟨p.1, hz⟩ =
    Complex.I • hilbertAdjoint U.stoneOperator ⟨p.1, hy⟩ at he
  exact ((smul_right_injective _ Complex.I_ne_zero) he).trans hval

end UnitaryGroup

/-- The derivative graph determines a partial operator, including its domain. -/
theorem operator_eq_of_derivativeGraph (U : UnitaryGroup H) (A B : Operator ℂ H H)
    (hA : DerivativeGraph U A) (hB : DerivativeGraph U B) : A = B := by
  have he : Complex.I • A = Complex.I • B := by
    apply LinearPMap.eq_of_eq_graph
    ext p
    exact (hA p.1 p.2).symm.trans (hB p.1 p.2)
  have he' := congrArg (fun T : Operator ℂ H H => (-Complex.I) • T) he
  simpa only [smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul] using he'

def exponentialSymbol (t : ℝ) (r : ℝ) : ℂ :=
  Complex.exp (Complex.I * (t : ℂ) * (r : ℂ))

theorem norm_exponentialSymbol (t r : ℝ) : ‖exponentialSymbol t r‖ = 1 := by
  simp [exponentialSymbol, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem continuous_exponentialSymbol (t : ℝ) : Continuous (exponentialSymbol t) := by
  exact Complex.continuous_exp.comp ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal)

def derivativeMultiplier (h : ℝ) (r : ℝ) : ℂ :=
  dslope Complex.exp 0 (Complex.I * (h : ℂ) * (r : ℂ))

theorem continuous_exp_dslope : Continuous (dslope Complex.exp 0) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = 0
  · subst z
    exact continuousAt_dslope_same.mpr (Complex.differentiable_exp 0)
  · exact (continuousAt_dslope_of_ne hz).mpr Complex.continuous_exp.continuousAt

theorem continuous_derivativeMultiplier (h : ℝ) : Continuous (derivativeMultiplier h) :=
  continuous_exp_dslope.comp ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal)

theorem derivativeMultiplier_zero (r : ℝ) : derivativeMultiplier 0 r = 1 := by
  simp [derivativeMultiplier, dslope_same, Complex.deriv_exp]

theorem derivativeMultiplier_tendsto (r : ℝ) :
    Tendsto (fun h => derivativeMultiplier h r) (𝓝 0) (𝓝 1) := by
  have hc : Continuous (fun h : ℝ => derivativeMultiplier h r) :=
    continuous_exp_dslope.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  simpa only [derivativeMultiplier_zero] using hc.tendsto 0

theorem derivativeMultiplier_bound (h r : ℝ) : ‖derivativeMultiplier h r‖ ≤ 1 := by
  let z : ℂ := Complex.I * (h : ℂ) * (r : ℂ)
  by_cases hz : z = 0
  · change ‖dslope Complex.exp 0 z‖ ≤ 1
    rw [hz]
    simp [dslope_same, Complex.deriv_exp]
  · rw [derivativeMultiplier, dslope_of_ne _ hz, slope_def_field]
    simp only [sub_zero, Complex.exp_zero, norm_div]
    apply (div_le_one (norm_pos_iff.mpr hz)).mpr
    have he : Complex.I * (h : ℂ) * (r : ℂ) = Complex.I * ((h * r : ℝ) : ℂ) := by
      push_cast; ring
    dsimp only [z]
    rw [he]
    simpa using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := h * r))

theorem derivativeMultiplier_identity (h r : ℝ) :
    (Complex.I * (h : ℂ) * (r : ℂ)) * derivativeMultiplier h r = exponentialSymbol h r - 1 := by
  simpa only [sub_zero, smul_eq_mul, Complex.exp_zero, derivativeMultiplier, exponentialSymbol]
    using sub_smul_dslope Complex.exp 0 (Complex.I * (h : ℂ) * (r : ℂ))

theorem coordinate_mul_derivativeMultiplier (h : ℝ) (hh : h ≠ 0) :
    (fun r : ℝ => (r : ℂ) * derivativeMultiplier h r) =
      (Complex.I * (h : ℂ))⁻¹ • (exponentialSymbol h - fun _ => 1) := by
  funext r
  change (r : ℂ) * derivativeMultiplier h r =
    (Complex.I * (h : ℂ))⁻¹ * (exponentialSymbol h r - 1)
  apply mul_left_cancel₀ (show Complex.I * (h : ℂ) ≠ 0 by simp [hh])
  rw [← mul_assoc, derivativeMultiplier_identity, mul_inv_cancel_left₀ (by simp [hh])]

open Unbounded.MeasurableSpectralCalculus
open Unbounded.UnboundedNormalSpectralTheorem.SpectralRepresentation

private theorem bounded_one : SpectralMeasure.Spec.IsBoundedMeasurable (fun _ : ℝ => (1 : ℂ)) :=
  ⟨measurable_const, 1, by simp⟩

theorem bounded_exponentialSymbol (t : ℝ) :
    SpectralMeasure.Spec.IsBoundedMeasurable (exponentialSymbol t) :=
  ⟨(continuous_exponentialSymbol t).measurable, 1, fun r => (norm_exponentialSymbol t r).le⟩

theorem bounded_derivativeMultiplier (h : ℝ) :
    SpectralMeasure.Spec.IsBoundedMeasurable (derivativeMultiplier h) :=
  ⟨(continuous_derivativeMultiplier h).measurable, 1, derivativeMultiplier_bound h⟩

@[simp] theorem exponentialSymbol_zero : exponentialSymbol 0 = fun _ => 1 := by
  funext r
  simp [exponentialSymbol]

theorem exponentialSymbol_add (t s : ℝ) :
    exponentialSymbol (t + s) = exponentialSymbol t * exponentialSymbol s := by
  funext r
  simp only [exponentialSymbol, Pi.mul_apply, Complex.ofReal_add]
  rw [← Complex.exp_add]
  congr 1
  ring

variable {E : SpectralMeasure.ProjectionValuedMeasure ℝ H}

/-- The bounded PVM exponential, before packaging it as a unitary. -/
def spectralOperator (C : BoundedRealization E) (t : ℝ) : H →L[ℂ] H :=
  C.integral (exponentialSymbol t)

@[simp] theorem spectralOperator_zero (C : BoundedRealization E) : spectralOperator C 0 = 1 := by
  rw [spectralOperator, exponentialSymbol_zero, C.one]

theorem spectralOperator_add (C : BoundedRealization E) (t s : ℝ) :
    spectralOperator C (t + s) = spectralOperator C t * spectralOperator C s := by
  rw [spectralOperator, exponentialSymbol_add,
    C.mul _ _ (bounded_exponentialSymbol t) (bounded_exponentialSymbol s)]
  rfl

theorem spectralOperator_norm (C : BoundedRealization E) (t : ℝ) (x : H) :
    ‖spectralOperator C t x‖ = ‖x‖ := by
  have ht := C.norm_sq _ (bounded_exponentialSymbol t) x
  have h1 := C.norm_sq _ bounded_one x
  simp only [norm_exponentialSymbol, one_pow] at ht
  simp only [C.one, one_apply_eq_self, norm_one, one_pow] at h1
  change ‖spectralOperator C t x‖ ^ 2 = _ at ht
  nlinarith [norm_nonneg (spectralOperator C t x), norm_nonneg x]

/-- The inverse time gives the explicit inverse linear map. -/
def spectralUnitary (C : BoundedRealization E) (t : ℝ) : H ≃ₗᵢ[ℂ] H where
  toLinearEquiv :=
    { (spectralOperator C t).toLinearMap with
      invFun := spectralOperator C (-t)
      left_inv := by
        intro x
        change (spectralOperator C (-t) * spectralOperator C t) x = x
        rw [← spectralOperator_add, neg_add_cancel, spectralOperator_zero, one_apply_eq_self]
      right_inv := by
        intro x
        change (spectralOperator C t * spectralOperator C (-t)) x = x
        rw [← spectralOperator_add, add_neg_cancel, spectralOperator_zero, one_apply_eq_self] }
  norm_map' := spectralOperator_norm C t

@[simp] theorem spectralUnitary_apply (C : BoundedRealization E) (t : ℝ) (x : H) :
    spectralUnitary C t x = spectralOperator C t x := rfl

/-- Bounded convergence against each finite scalar spectral measure gives
strong continuity, with no common scalar control measure. -/
theorem continuous_spectralOperator (C : BoundedRealization E) (x : H) :
    Continuous (fun t : ℝ => spectralOperator C t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro a ha
  apply strong_convergence C (exponentialSymbol t) (fun n => exponentialSymbol (a n))
    (bounded_exponentialSymbol t) (fun n => bounded_exponentialSymbol (a n))
    ⟨1, fun n r => (norm_exponentialSymbol (a n) r).le⟩
  intro r
  have hc : Continuous (fun t : ℝ => exponentialSymbol t r) :=
    Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  exact (hc.tendsto t).comp ha

/-- The PVM construction of a strongly continuous unitary group. -/
def spectralGroup (C : BoundedRealization E) : UnitaryGroup H where
  operators := spectralUnitary C
  at_zero x := by simp
  add_time t s x := by
    simp only [spectralUnitary_apply, spectralOperator_add]
    rfl
  continuous_orbit := continuous_spectralOperator C

/-- The bounded multiplier tends strongly to I, including at zero spectral value. -/
theorem tendsto_derivativeMultiplier (C : BoundedRealization E) (x : H) :
    Tendsto (fun h : ℝ => C.integral (derivativeMultiplier h) x) (𝓝 0) (𝓝 x) := by
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro a ha
  have ht := strong_convergence C (fun _ : ℝ => (1 : ℂ))
    (fun n => derivativeMultiplier (a n)) bounded_one
    (fun n => bounded_derivativeMultiplier (a n))
    ⟨1, fun n r => derivativeMultiplier_bound (a n) r⟩
    (fun r => (derivativeMultiplier_tendsto r).comp ha) x
  simpa only [C.one, one_apply_eq_self, Function.comp_def] using ht

/-- The quotient is a bounded multiplier applied to Ax. This avoids imposing
boundedness of the coordinate symbol or of the original operator. -/
theorem spectral_differenceQuotient (C : BoundedRealization E)
    (x : (measurableIntegral C (fun r : ℝ => (r : ℂ))).domain)
    (h : ℝ) (hh : h ≠ 0) :
    differenceQuotient (spectralGroup C) h x =
      Complex.I • C.integral (derivativeMultiplier h)
        (measurableIntegral C (fun r : ℝ => (r : ℂ)) x) := by
  have hprod : SpectralMeasure.Spec.IsBoundedMeasurable
      ((fun r : ℝ => (r : ℂ)) * derivativeMultiplier h) := by
    change SpectralMeasure.Spec.IsBoundedMeasurable
      (fun r : ℝ => (r : ℂ) * derivativeMultiplier h r)
    rw [coordinate_mul_derivativeMultiplier h hh]
    simpa only [neg_one_smul, sub_eq_add_neg] using
      (bounded_exponentialSymbol h |>.add (bounded_one.smul (-1)) |>.smul
        (Complex.I * (h : ℂ))⁻¹)
  rw [bounded_product_commutes C Complex.measurable_ofReal (bounded_derivativeMultiplier h) hprod x]
  have hsym : Complex.I • ((fun r : ℝ => (r : ℂ)) * derivativeMultiplier h) =
      (h : ℂ)⁻¹ • (exponentialSymbol h - fun _ => 1) := by
    funext r
    change Complex.I * ((r : ℂ) * derivativeMultiplier h r) =
      (h : ℂ)⁻¹ * (exponentialSymbol h r - 1)
    rw [← derivativeMultiplier_identity h r]
    field_simp [hh]
  change differenceQuotient (spectralGroup C) h x =
    (Complex.I • C.integral ((fun r : ℝ => (r : ℂ)) * derivativeMultiplier h)) x
  rw [← C.smul Complex.I _ hprod, hsym,
    C.smul _ _ (by simpa only [sub_eq_add_neg] using
      (bounded_exponentialSymbol h).add (by simpa using bounded_one.smul (-1))),
    C.sub _ _ (bounded_exponentialSymbol h) bounded_one, C.one]
  rfl

/-- On its given spectral domain, the norm derivative is iAx. -/
theorem spectral_hasDerivative (C : BoundedRealization E)
    (x : (measurableIntegral C (fun r : ℝ => (r : ℂ))).domain) :
    HasDerivative (spectralGroup C) x
      (Complex.I • measurableIntegral C (fun r : ℝ => (r : ℂ)) x) := by
  have ht := (tendsto_derivativeMultiplier C
    (measurableIntegral C (fun r : ℝ => (r : ℂ)) x)).const_smul Complex.I
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (spectral_differenceQuotient C x h (show h ≠ 0 from hh)).symm

/-- The differentiability assertion transfers to any group satisfying the
same PVM formula, without adding a derivative-domain hypothesis. -/
theorem hasDerivative_of_spectralExponential (A : Operator ℂ H H) (U : UnitaryGroup H)
    (h : SpectralExponential A U) (x : A.domain) :
    HasDerivative U x (Complex.I • A x) := by
  obtain ⟨E, C, hA, hU⟩ := h
  subst A
  have hd := spectral_hasDerivative C x
  apply hd.congr'
  filter_upwards [] with r
  unfold differenceQuotient
  congr 1
  congr 1
  exact (congrArg (fun T : H →L[ℂ] H => T x) (hU r)).symm

/-- The derivative on a proposed operator's domain gives actual inclusion
into the Stone operator, retaining the graph values. -/
theorem le_stoneOperator_of_hasDerivative (A : Operator ℂ H H) (U : UnitaryGroup H)
    (h : ∀ x : A.domain, HasDerivative U x (Complex.I • A x)) : A ≤ U.stoneOperator := by
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨hx, he⟩ := (Unbounded.mem_graph_iff _ _).mp hp
  have hd := (U.derivativeGraph_stoneOperator p.1 _).mp (h ⟨p.1, hx⟩)
  obtain ⟨hz, hv⟩ := (Unbounded.mem_graph_iff _ _).mp hd
  apply (Unbounded.mem_graph_iff _ _).mpr
  refine ⟨hz, ?_⟩
  change Complex.I • U.stoneOperator ⟨p.1, hz⟩ = Complex.I • A ⟨p.1, hx⟩ at hv
  exact ((smul_right_injective _ Complex.I_ne_zero) hv).trans he

/-- A self-adjoint operator admits no proper densely defined symmetric extension. -/
theorem selfAdjoint_eq_of_le_symmetric (A B : Operator ℂ H H)
    (hA : Unbounded.IsSelfAdjoint A) (hB : IsSymmetric B) (hle : A ≤ B) : A = B := by
  have hf : A.IsFormalAdjoint B := by
    intro x y
    have hx : (x : H) ∈ B.domain := hle.1 x.2
    have he : A x = B ⟨x, hx⟩ := hle.2 rfl
    rw [he]
    exact hB.inner_map ⟨x, hx⟩ y
  have hb : B ≤ A.adjoint := hf.le_adjoint hA.1
  have he : A = A.adjoint := hA.2
  rw [← he] at hb
  exact le_antisymm hle hb

/-- Exactness of the spectral derivative domain follows from maximality:
no additional norm-differentiable vectors can occur outside D(A). -/
theorem spectral_derivative : Spec.SpectralDerivative.{u} := by
  intro H _ _ _ A U hA hU
  have hi := le_stoneOperator_of_hasDerivative A U
    (hasDerivative_of_spectralExponential A U hU)
  have he := selfAdjoint_eq_of_le_symmetric A U.stoneOperator hA U.stoneOperator_symmetric hi
  rw [he]
  exact U.derivativeGraph_stoneOperator

/-- The converse construction for every self-adjoint operator. -/
theorem stone_converse : Spec.Converse.{u} := by
  intro H _ _ _ A hA
  have hc : A.IsClosed := by
    rw [hA.2]
    exact LinearPMap.adjoint_isClosed hA.1
  obtain ⟨E, ⟨C, hC, _⟩⟩ :=
    (Unbounded.UnboundedNormalSpectralTheorem.selfadjoint_spectral H A hA.1 hc hA.2.symm).1
  have hs : SpectralExponential A (spectralGroup C) := by
    refine ⟨E, C, hC, ?_⟩
    intro t
    rfl
  exact ⟨spectralGroup C, hs, spectral_derivative H A (spectralGroup C) hA hs⟩

/-- The positive-time generator is determined by the full derivative graph. -/
theorem generator_eq_of_derivativeGraph (U : UnitaryGroup H) (A : Operator ℂ H H)
    (h : DerivativeGraph U A) : U.infinitesimalGenerator = Complex.I • A := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  exact (U.hasDerivative_iff_mem_graph p.1 p.2).symm.trans (h p.1 p.2)

/-- Equality of the generators identifies the groups at positive and negative
times, using semigroup uniqueness and the group inverses. -/
theorem operators_eq_of_generator_eq (U V : UnitaryGroup H)
    (h : U.infinitesimalGenerator = V.infinitesimalGenerator) (t : ℝ) :
    U.operators t = V.operators t := by
  have hp (s : ℝ≥0) : U.operators s = V.operators s := by
    have he := GeneratorDeterminesSemigroup.generator_determines_semigroup U.positive V.positive h s
    apply LinearIsometryEquiv.ext
    intro x
    exact congrArg (fun T : H →L[ℂ] H => T x) he
  by_cases ht : 0 ≤ t
  · simpa only [Real.coe_toNNReal _ ht] using hp t.toNNReal
  · have hnt : 0 ≤ -t := (neg_nonneg.mpr (le_of_not_ge ht))
    have he : U.operators (-t) = V.operators (-t) := by
      simpa only [Real.coe_toNNReal _ hnt] using hp (-t).toNNReal
    apply LinearIsometryEquiv.ext
    intro x
    apply (U.operators (-t)).injective
    rw [U.neg_apply_cancel, he, V.neg_apply_cancel]

/-- Existence, exact-domain generation, and uniqueness for the given group. -/
theorem stone_forward : Spec.Forward.{u} := by
  intro H _ _ _ U
  let A := U.stoneOperator
  have hA : Unbounded.SymmetryAndDeficienciesSpec.selfAdjointValue A := U.stoneOperator_selfAdjoint
  obtain ⟨V, hV, hdV⟩ := stone_converse H A hA
  have he : U.infinitesimalGenerator = V.infinitesimalGenerator := by
    rw [generator_eq_of_derivativeGraph U A U.derivativeGraph_stoneOperator,
      generator_eq_of_derivativeGraph V A hdV]
  have hexp : SpectralExponential A U := by
    obtain ⟨E, C, hC, hform⟩ := hV
    refine ⟨E, C, hC, ?_⟩
    intro t
    rw [operators_eq_of_generator_eq U V he t]
    exact hform t
  refine ⟨A, hA, hexp, U.derivativeGraph_stoneOperator, ?_⟩
  intro B hB hBU
  exact operator_eq_of_derivativeGraph U B A
    (spectral_derivative H B U hB hBU) U.derivativeGraph_stoneOperator

/-- Stone's theorem with the PVM exponential and the exact derivative domain. -/
theorem stone_theorem : Spec.FullTheorem.{u} := ⟨stone_forward, stone_converse⟩

end ExpandedFA.Semigroups.Stone
