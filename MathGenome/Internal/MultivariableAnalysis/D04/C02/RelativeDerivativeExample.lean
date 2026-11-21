import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.RelativeDerivativeExample
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces

noncomputable section
open Set Filter Topology
namespace D04

def horizontalAxis : Set (E 2) :=
  Specs.D04.C02.RelativeDerivativeExample.Model.horizontalAxis

def axisFunction : E 2 → ℝ :=
  Specs.D04.C02.RelativeDerivativeExample.Model.axisFunction

def axisFirstMap : E 2 →L[ℝ] ℝ :=
  Specs.D04.C02.RelativeDerivativeExample.Model.axisFirstMap

def axisSecondMap : E 2 →L[ℝ] ℝ :=
  Specs.D04.C02.RelativeDerivativeExample.Model.axisSecondMap

theorem horizontalAxis_eq_range :
    horizontalAxis = Set.range (fun t : ℝ => WithLp.toLp 2 ![t, 0]) := by
  ext x
  constructor
  · intro hx
    refine ⟨x 0, ?_⟩
    ext i
    fin_cases i
    · rfl
    · exact hx.symm
  · rintro ⟨t, rfl⟩
    rfl

theorem axis_maps_apply :
    (∀ h : E 2, axisFirstMap h = h 0) ∧
    (∀ h : E 2, axisSecondMap h = h 0 + h 1) := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- Both remainders vanish identically on the available increments. -/
theorem axis_relative_approximations :
    RelativeApproximation horizontalAxis axisFunction axisFirstMap 0 ∧
    RelativeApproximation horizontalAxis axisFunction axisSecondMap 0 ∧
    axisFirstMap ≠ axisSecondMap := by
  have hfirst : RelativeApproximation horizontalAxis axisFunction axisFirstMap 0 := by
    change Tendsto (fun x : E 2 => ‖x 0 - (0 : ℝ) - axisFirstMap (x - 0)‖ /
      ‖x - 0‖) (𝓝[horizontalAxis \ {0}] 0) (𝓝 0)
    simpa only [sub_zero, axis_maps_apply.1, sub_self, norm_zero, zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : E 2 => (0 : ℝ))
        (𝓝[horizontalAxis \ {0}] 0) (𝓝 0))
  have hsecond : RelativeApproximation horizontalAxis axisFunction axisSecondMap 0 := by
    change Tendsto (fun x : E 2 => ‖x 0 - (0 : ℝ) - axisSecondMap (x - 0)‖ /
      ‖x - 0‖) (𝓝[horizontalAxis \ {0}] 0) (𝓝 0)
    apply (tendsto_const_nhds : Tendsto (fun _ : E 2 => (0 : ℝ))
      (𝓝[horizontalAxis \ {0}] 0) (𝓝 0)).congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : x 1 = 0 := hx.1
    simp only [sub_zero, axis_maps_apply.2, hx1, add_zero, sub_self, norm_zero, zero_div]
  refine ⟨hfirst, hsecond, ?_⟩
  intro he
  have hv := congrArg (fun A : E 2 →L[ℝ] ℝ => A (WithLp.toLp 2 ![0, 1])) he
  norm_num [axis_maps_apply.1, axis_maps_apply.2] at hv

theorem axis_relative_not_unique :
    ¬ (∀ A B : E 2 →L[ℝ] ℝ,
      RelativeApproximation horizontalAxis axisFunction A 0 →
      RelativeApproximation horizontalAxis axisFunction B 0 → A = B) := by
  intro h
  obtain ⟨hfirst, hsecond, hne⟩ := axis_relative_approximations
  exact hne (h axisFirstMap axisSecondMap hfirst hsecond)

theorem relativeApproximation_at_isolated {n : ℕ} {Y : Type}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set (E n)) (f : E n → Y) (a : U)
    (ha : IsolatedPoint U a) (A : E n →L[ℝ] Y) :
    RelativeApproximation U f A a := by
  apply (relativeApproximation_iff_hasFDerivWithinAt U f A a).mpr
  apply HasFDerivWithinAt.of_not_accPt
  intro h
  exact isolated_not_accumulation U a ha ((accumulationPoint_iff_accPt U a).mpr h)

theorem relativeApproximation_subtype_at_isolated {n m : ℕ}
    (U : Set (E n)) (f : U → E m) (a : U)
    (ha : IsolatedPoint U a) (A : E n →ₗ[ℝ] E m) :
    RelativeApproximation U (domainExtension U f) A.toContinuousLinearMap a :=
  relativeApproximation_at_isolated U (domainExtension U f) a ha A.toContinuousLinearMap

theorem relativeApproximation_singleton {n m : ℕ}
    (a : E n) (f : ({a} : Set (E n)) → E m) (A : E n →ₗ[ℝ] E m) :
    RelativeApproximation {a} (domainExtension {a} f) A.toContinuousLinearMap a := by
  apply relativeApproximation_subtype_at_isolated {a} f ⟨a, by simp⟩ _ A
  refine ⟨1, zero_lt_one, ?_⟩
  intro x hx _
  exact Set.mem_singleton_iff.mp hx

end D04
