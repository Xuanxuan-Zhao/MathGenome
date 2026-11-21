import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.ClosedAndExactForms
import MathGenome.Internal.MultivariableAnalysis.D04.C13.ExteriorDerivative
import MathGenome.Internal.MultivariableAnalysis.D04.C01.Components
import MathGenome.Internal.MultivariableAnalysis.D04.C02.LipschitzConstancy

/-! Closed and exact forms, with the finite regularity of d04:13:closed-exact. -/
noncomputable section
open Set Filter Topology
namespace D04

abbrev IsClosedForm := @Specs.D04.C13.ClosedAndExactForms.Model.IsClosedForm
abbrev IsExactForm := @Specs.D04.C13.ClosedAndExactForms.Model.IsExactForm

theorem isClosedForm_iff {n k : ℕ} (U : Set (E n)) (ω : FormField n k)
    (hω : IsCrForm (some 1) U ω) :
    IsClosedForm U ω ↔ ∀ x ∈ U, exteriorDerivative ω x = 0 :=
  ⟨fun h => h.2, fun h => ⟨hω, h⟩⟩

theorem isExactForm_iff {n k : ℕ} (U : Set (E n)) (ω : FormField n (k + 1)) :
    IsExactForm U ω ↔ ∃ η : FormField n k, IsCrForm (some 1) U η ∧
      ∀ x ∈ U, ω x = exteriorDerivative η x := Iff.rfl

private theorem scalar_closed_iff_derivative_zero {n : ℕ} (U : Set (E n))
    (f : E n → ℝ) (hU : IsOpen U) (hf : CrOn 1 U f) :
    IsClosedForm U (fun x => scalarCovector (V := E n) (f x)) ↔
      ∀ x ∈ U, totalDerivative f x = 0 := by
  rw [isClosedForm_iff U _ ((isCrForm_zero_iff _ U f).mpr ⟨hU, hf⟩)]
  constructor
  · intro h x hx
    have hd := h x hx
    rw [exteriorDerivative_function U f hU hf x hx] at hd
    ext v
    exact congrArg (fun α : Covector (E n) 1 => α (fun _ => v)) hd
  · intro h x hx
    rw [exteriorDerivative_function U f hU hf x hx, h x hx]
    ext v
    rfl

private theorem scalar_derivative_zero_iff_locally_constant {n : ℕ}
    (U : Set (E n)) (f : E n → ℝ) (hU : IsOpen U) (hf : CrOn 1 U f) :
    (∀ x ∈ U, totalDerivative f x = 0) ↔
      ∀ x ∈ U, ∃ r > 0, Metric.ball x r ⊆ U ∧
        ∀ y ∈ Metric.ball x r, f y = f x := by
  constructor
  · intro hz x hx
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU x hx
    refine ⟨r, hr, hsub, ?_⟩
    intro y hy
    exact Metric.isOpen_ball.is_const_of_fderiv_eq_zero
      (convex_ball x r).isPreconnected
      (((totalDifferentiableOn_iff U f hU).mp hf.1).mono hsub)
      (fun z hz' => hz z (hsub hz')) hy (Metric.mem_ball_self hr)
  · intro h x hx
    obtain ⟨r, hr, _, heq⟩ := h x hx
    have he : f =ᶠ[𝓝 x] fun _ => f x :=
      Filter.eventually_of_mem (Metric.ball_mem_nhds x hr) heq
    exact he.fderiv_eq.trans (fderiv_const_apply (f x))

theorem isClosedForm_zero_iff_locally_constant {n : ℕ}
    (U : Set (E n)) (ω : FormField n 0) (hω : IsCrForm (some 1) U ω) :
    IsClosedForm U ω ↔ ∀ x ∈ U, ∃ r > 0,
      Metric.ball x r ⊆ U ∧ ∀ y ∈ Metric.ball x r, ω y = ω x := by
  let f : E n → ℝ := fun x => scalarCovector.symm (ω x)
  have hrepr : (fun x => scalarCovector (V := E n) (f x)) = ω := by
    funext x
    exact scalarCovector.apply_symm_apply (ω x)
  have hf : CrOn 1 U f := ((isCrForm_zero_iff _ U f).mp (hrepr ▸ hω)).2
  have hscalar := (scalar_closed_iff_derivative_zero U f hω.1 hf).trans
    (scalar_derivative_zero_iff_locally_constant U f hω.1 hf)
  rw [hrepr] at hscalar
  rw [hscalar]
  constructor
  · intro h x hx
    obtain ⟨r, hr, hsub, heq⟩ := h x hx
    refine ⟨r, hr, hsub, fun y hy => ?_⟩
    exact scalarCovector.symm.injective (heq y hy)
  · intro h x hx
    obtain ⟨r, hr, hsub, heq⟩ := h x hx
    exact ⟨r, hr, hsub, fun y hy => congrArg scalarCovector.symm (heq y hy)⟩

theorem isClosedForm_zero_iff_constant_on_components {n : ℕ}
    (U : Set (E n)) (ω : FormField n 0) (hω : IsCrForm (some 1) U ω) :
    IsClosedForm U ω ↔ ∀ a ∈ U,
      ∀ x ∈ componentWithin U a, ∀ y ∈ componentWithin U a, ω x = ω y := by
  let f : E n → ℝ := fun x => scalarCovector.symm (ω x)
  have hrepr : (fun x => scalarCovector (V := E n) (f x)) = ω := by
    funext x
    exact scalarCovector.apply_symm_apply (ω x)
  have hf : CrOn 1 U f := ((isCrForm_zero_iff _ U f).mp (hrepr ▸ hω)).2
  constructor
  · intro h a _ x hx y hy
    have hz := (scalar_closed_iff_derivative_zero U f hω.1 hf).mp (hrepr ▸ h)
    have hopen : IsOpen (componentWithin U a) :=
      (open_iff_isOpen _).mp (open_componentWithin U ((open_iff_isOpen U).mpr hω.1) a)
    have heq : f x = f y := hopen.is_const_of_fderiv_eq_zero
      (componentWithin_connected U a)
      (((totalDifferentiableOn_iff U f hω.1).mp hf.1).mono (componentWithin_subset U a))
      (fun z hz' => hz z (componentWithin_subset U a hz')) hx hy
    exact scalarCovector.symm.injective heq
  · intro h
    apply (isClosedForm_zero_iff_locally_constant U ω hω).mpr
    intro x hx
    have hopen : IsOpen (componentWithin U x) :=
      (open_iff_isOpen _).mp (open_componentWithin U ((open_iff_isOpen U).mpr hω.1) x)
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hopen x (mem_componentWithin U x hx)
    exact ⟨r, hr, hsub.trans (componentWithin_subset U x),
      fun y hy => h x hx y (hsub hy) x (mem_componentWithin U x hx)⟩

end D04
