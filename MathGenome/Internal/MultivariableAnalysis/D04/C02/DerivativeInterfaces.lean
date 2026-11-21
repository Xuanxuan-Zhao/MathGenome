import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import MathGenome.Internal.MultivariableAnalysis.D04.C01.OperatorEstimates

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04
def domainExtension : Specs.D04.C02.DerivativeInterfaces.domainExtensionType :=
  Specs.D04.C02.DerivativeInterfaces.domainExtensionValue

def HasDirectionalDerivative : Specs.D04.C02.DerivativeInterfaces.HasDirectionalDerivativeType :=
  Specs.D04.C02.DerivativeInterfaces.HasDirectionalDerivativeValue

def directionalDerivative : Specs.D04.C02.DerivativeInterfaces.directionalDerivativeType :=
  Specs.D04.C02.DerivativeInterfaces.directionalDerivativeValue

def HasPartialDerivative : Specs.D04.C02.DerivativeInterfaces.HasPartialDerivativeType :=
  Specs.D04.C02.DerivativeInterfaces.HasPartialDerivativeValue

def partialDerivative : Specs.D04.C02.DerivativeInterfaces.partialDerivativeType :=
  Specs.D04.C02.DerivativeInterfaces.partialDerivativeValue

def remainder : Specs.D04.C02.DerivativeInterfaces.remainderType :=
  Specs.D04.C02.DerivativeInterfaces.remainderValue

def RelativeApproximation : Specs.D04.C02.DerivativeInterfaces.RelativeApproximationType :=
  Specs.D04.C02.DerivativeInterfaces.RelativeApproximationValue

def HasTotalDerivative : Specs.D04.C02.DerivativeInterfaces.HasTotalDerivativeType :=
  Specs.D04.C02.DerivativeInterfaces.HasTotalDerivativeValue

def HasLinearDerivative : Specs.D04.C02.DerivativeInterfaces.HasLinearDerivativeType :=
  Specs.D04.C02.DerivativeInterfaces.HasLinearDerivativeValue

def totalDerivative : Specs.D04.C02.DerivativeInterfaces.totalDerivativeType :=
  Specs.D04.C02.DerivativeInterfaces.totalDerivativeValue

def TotalDifferentiableOn : Specs.D04.C02.DerivativeInterfaces.TotalDifferentiableOnType :=
  Specs.D04.C02.DerivativeInterfaces.TotalDifferentiableOnValue

def SmoothOn : Specs.D04.C02.DerivativeInterfaces.SmoothOnType :=
  Specs.D04.C02.DerivativeInterfaces.SmoothOnValue

def RealAnalyticOn : Specs.D04.C02.DerivativeInterfaces.RealAnalyticOnType :=
  Specs.D04.C02.DerivativeInterfaces.RealAnalyticOnValue

def CrOn : Specs.D04.C02.DerivativeInterfaces.CrOnType :=
  Specs.D04.C02.DerivativeInterfaces.CrOnValue

section Generic
variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable (U : Set X) (f : X → Y) (A : X →L[ℝ] Y) (a : X)

theorem relativeApproximation_iff_hasFDerivWithinAt :
    RelativeApproximation U f A a ↔ HasFDerivWithinAt f A U a := by
  rw [← hasFDerivWithinAt_sdiff_singleton_self, hasFDerivWithinAt_iff_tendsto]
  change Tendsto _ _ _ ↔ Tendsto _ _ _
  simp only [div_eq_inv_mul]

theorem hasTotalDerivative_iff_hasFDerivAt (hU : IsOpen U) (ha : a ∈ U) :
    HasTotalDerivative U f A a ↔ HasFDerivAt f A a := by
  change (IsOpen U ∧ a ∈ U ∧ RelativeApproximation U f A a) ↔ _
  rw [relativeApproximation_iff_hasFDerivWithinAt]
  exact ⟨fun h => h.2.2.hasFDerivAt (hU.mem_nhds ha), fun h => ⟨hU, ha, h.hasFDerivWithinAt⟩⟩

theorem totalDerivative_eq (h : HasTotalDerivative U f A a) :
    totalDerivative f a = A := by
  exact ((hasTotalDerivative_iff_hasFDerivAt U f A a h.1 h.2.1).mp h).fderiv

theorem totalDifferentiableOn_iff (hU : IsOpen U) :
    TotalDifferentiableOn U f ↔ DifferentiableOn ℝ f U := by
  change (∀ a ∈ U, ∃ A, HasTotalDerivative U f A a) ↔ _
  constructor
  · intro h a ha
    obtain ⟨A, hA⟩ := h a ha
    exact ((hasTotalDerivative_iff_hasFDerivAt U f A a hU ha).mp hA).differentiableAt.differentiableWithinAt
  · intro h a ha
    have hd := (h a ha).differentiableAt (hU.mem_nhds ha)
    exact ⟨fderiv ℝ f a, (hasTotalDerivative_iff_hasFDerivAt U f _ a hU ha).mpr hd.hasFDerivAt⟩

theorem remainder_zero : remainder f A a 0 = 0 := by
  simp [remainder, Specs.D04.C02.DerivativeInterfaces.remainderValue,
    Specs.D04.C02.DerivativeInterfaces.Model.remainder]

theorem remainder_expansion (h : X) :
    f (a + h) = f a + A h + remainder f A a h := by
  change f (a + h) = f a + A h + (f (a + h) - f a - A h)
  abel

theorem relativeApproximation_iff_remainder_limit :
    RelativeApproximation U f A a ↔
      Tendsto (fun h => ‖remainder f A a h‖ / ‖h‖)
        (𝓝[{h | a + h ∈ U} \ {0}] 0) (𝓝 0) := by
  have hadd : Tendsto (fun h : X => a + h)
      (𝓝[{h | a + h ∈ U} \ {0}] 0) (𝓝[U \ {a}] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · convert (continuous_const.add continuous_id : Continuous (fun h : X => a + h)).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[{h : X | a + h ∈ U} \ {0}] 0 ≤ 𝓝 0) using 1
      simp
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact ⟨hh.1, by simpa using hh.2⟩
  have hsub : Tendsto (fun x : X => x - a)
      (𝓝[U \ {a}] a) (𝓝[{h | a + h ∈ U} \ {0}] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · convert (continuous_id.sub continuous_const : Continuous (fun x : X => x - a)).continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[U \ {a}] a ≤ 𝓝 a) using 1 <;> first | rfl | simp
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact ⟨by simpa using hx.1, by simpa [sub_eq_zero] using hx.2⟩
  change Tendsto (fun x => ‖f x - f a - A (x - a)‖ / ‖x - a‖) _ _ ↔ _
  constructor
  · intro h
    simpa [Function.comp_def, remainder, Specs.D04.C02.DerivativeInterfaces.remainderValue,
      Specs.D04.C02.DerivativeInterfaces.Model.remainder] using h.comp hadd
  · intro h
    simpa [Function.comp_def, remainder, Specs.D04.C02.DerivativeInterfaces.remainderValue,
      Specs.D04.C02.DerivativeInterfaces.Model.remainder] using h.comp hsub

theorem hasDirectionalDerivative_iff_hasDerivAt (v : X) (d : Y) :
    HasDirectionalDerivative f a v d ↔ HasDerivAt (fun t : ℝ => f (a + t • v)) d 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  change Tendsto _ _ _ ↔ Tendsto _ _ _
  simp only [zero_add, zero_smul, add_zero]

theorem directionalDerivative_eq (v : X) (d : Y)
    (h : HasDirectionalDerivative f a v d) : directionalDerivative f a v = d :=
  ((hasDirectionalDerivative_iff_hasDerivAt f a v d).mp h).deriv

/-- Available increments determine the remainder on the domain, without a uniqueness claim for A. -/
theorem relativeApproximation_iff_exists_remainder :
    RelativeApproximation U f A a ↔ ∃ r : X → Y,
      r 0 = 0 ∧ (∀ h, a + h ∈ U → f (a + h) = f a + A h + r h) ∧
      Tendsto (fun h => ‖r h‖ / ‖h‖) (𝓝[{h | a + h ∈ U} \ {0}] 0) (𝓝 0) := by
  constructor
  · intro h
    exact ⟨remainder f A a, remainder_zero f A a,
      fun h _ => remainder_expansion f A a h,
      (relativeApproximation_iff_remainder_limit U f A a).mp h⟩
  · rintro ⟨r, _, hr, ht⟩
    apply (relativeApproximation_iff_remainder_limit U f A a).mpr
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have he : r h = remainder f A a h := by
      change r h = f (a + h) - f a - A h
      rw [hr h hh.1]
      abel
    rw [he]

/-- The original open-domain remainder formulation, with an explicit witness. -/
theorem hasTotalDerivative_iff_remainder (hU : IsOpen U) (ha : a ∈ U) :
    HasTotalDerivative U f A a ↔ ∃ r : X → Y,
      r 0 = 0 ∧ (∀ h, a + h ∈ U → f (a + h) = f a + A h + r h) ∧
      Tendsto (fun h => ‖r h‖ / ‖h‖) (𝓝[{h | a + h ∈ U} \ {0}] 0) (𝓝 0) := by
  change (IsOpen U ∧ a ∈ U ∧ RelativeApproximation U f A a) ↔ _
  simp only [hU, ha, true_and, relativeApproximation_iff_exists_remainder]

theorem hasTotalDerivative_congr (g : X → Y) (ha : a ∈ U) (hfg : EqOn f g U) :
    HasTotalDerivative U f A a ↔ HasTotalDerivative U g A a := by
  change (IsOpen U ∧ a ∈ U ∧ RelativeApproximation U f A a) ↔
    (IsOpen U ∧ a ∈ U ∧ RelativeApproximation U g A a)
  rw [relativeApproximation_iff_hasFDerivWithinAt, relativeApproximation_iff_hasFDerivWithinAt]
  exact and_congr_right fun _ => and_congr_right fun _ =>
    ⟨fun h => h.congr hfg.symm (hfg ha).symm, fun h => h.congr hfg (hfg ha)⟩

theorem totalDerivative_congr (g : X → Y) (hU : IsOpen U) (ha : a ∈ U)
    (hfg : EqOn f g U) : totalDerivative f a = totalDerivative g a := by
  have he : f =ᶠ[𝓝 a] g := Filter.eventuallyEq_of_mem (hU.mem_nhds ha) hfg
  exact he.fderiv_eq

end Generic

/-- The recursive definition uses the operator norm at every operator-valued stage. -/
theorem crOn_iff_contDiffOn (r : ℕ) {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (hU : IsOpen U) :
    CrOn r U f ↔ ContDiffOn ℝ (r : ℕ∞ω) f U := by
  induction r generalizing Y with
  | zero => exact contDiffOn_zero.symm
  | succ r ih =>
    change (TotalDifferentiableOn U f ∧ CrOn r U (totalDerivative f)) ↔ _
    rw [totalDifferentiableOn_iff U f hU, ih (totalDerivative f),
      Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_of_isOpen hU]
    change (DifferentiableOn ℝ f U ∧ ContDiffOn ℝ (r : ℕ∞ω) (fderiv ℝ f) U) ↔ _
    simp

theorem smoothOn_iff_contDiffOn {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (hU : IsOpen U) :
    SmoothOn U f ↔ ContDiffOn ℝ ∞ f U := by
  change (∀ r : ℕ, CrOn r U f) ↔ _
  simp only [crOn_iff_contDiffOn, hU, contDiffOn_infty]

theorem realAnalyticOn_iff {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) :
    RealAnalyticOn U f ↔ AnalyticOnNhd ℝ f U := Iff.rfl

/-- No continuity restriction on an algebraic map is added in finite dimensions. -/
theorem hasLinearDerivative_iff {n m : ℕ} (U : Set (E n)) (f : E n → E m)
    (A : E n →ₗ[ℝ] E m) (a : E n) (hU : IsOpen U) (ha : a ∈ U) :
    HasLinearDerivative U f A a ↔ HasFDerivAt f (LinearMap.toContinuousLinearMap A) a :=
  hasTotalDerivative_iff_hasFDerivAt U f _ a hU ha

theorem totalDerivative_operatorNorm {n m : ℕ} (f : E n → E m) (a : E n) :
    linearOperatorNorm (totalDerivative f a).toLinearMap = ‖fderiv ℝ f a‖ :=
  linearOperatorNorm_eq_standard _

theorem domainExtension_apply {n m : ℕ} (U : Set (E n)) (f : U → E m) (a : U) :
    domainExtension U f a = f a := by
  simp [domainExtension, Specs.D04.C02.DerivativeInterfaces.domainExtensionValue,
    Specs.D04.C02.DerivativeInterfaces.Model.domainExtension, a.property]

/-- Every open-domain function may be used through any ambient extension. -/
theorem domainExtension_eqOn {n m : ℕ} (U : Set (E n)) (f : U → E m)
    (g : E n → E m) (hg : ∀ x : U, g x = f x) : EqOn (domainExtension U f) g U := by
  intro x hx
  exact (domainExtension_apply U f ⟨x, hx⟩).trans (hg ⟨x, hx⟩).symm

theorem domainExtension_hasTotalDerivative_iff {n m : ℕ} (U : Set (E n)) (f : U → E m)
    (g : E n → E m) (hg : ∀ x : U, g x = f x) (a : U) (A : E n →L[ℝ] E m) :
    HasTotalDerivative U (domainExtension U f) A a ↔ HasTotalDerivative U g A a :=
  hasTotalDerivative_congr U _ A a g a.property (domainExtension_eqOn U f g hg)

theorem crOn_congr (r : ℕ) {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f g : X → Y)
    (hU : IsOpen U) (hfg : EqOn f g U) : CrOn r U f ↔ CrOn r U g := by
  rw [crOn_iff_contDiffOn r U f hU, crOn_iff_contDiffOn r U g hU]
  exact contDiffOn_congr hfg

theorem domainExtension_continuousOn_iff {n m : ℕ} (U : Set (E n)) (f : U → E m) :
    ContinuousOn (domainExtension U f) U ↔ Continuous f := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : U.domRestrict (domainExtension U f) = f := by
    funext x
    exact domainExtension_apply U f x
  rw [he]

end D04
