import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch09.ContinuousPrimitive
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch09.FtcFirst
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch08.Continuous
import Mathlib.Topology.MetricSpace.Pseudo.Real

/-! A continuous scalar function on any real interval has a primitive.
All integrals below are the proper Darboux integrals of chapter 08.
The interval need not be compact or have included endpoints. Compact hulls
of finitely many of its points suffice for every integral and every splitting.
-/
namespace SingleVariableAnalysis.Riemann
open scoped Topology

/-- A bound on an ordered tagged integral gives a bound for increments in
either direction. -/
theorem norm_increment_le_of_tagged_limits {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f F : ℝ → E} {I : Set ℝ}
    (hF : ∀ a ∈ I, ∀ b ∈ I, a ≤ b → FineTaggedLimit f a b (F b - F a))
    {x y M : ℝ} (hx : x ∈ I) (hy : y ∈ I)
    (hb : ∀ t ∈ Set.uIcc x y, ‖f t‖ ≤ M) :
    ‖F y - F x‖ ≤ |y-x| * M := by
  rcases le_total x y with hxy | hyx
  · have h := (hF x hx y hy hxy).sub_const_bound (c := 0) hxy
      (by simpa only [Set.uIcc_of_le hxy, sub_zero] using hb)
    simpa only [smul_zero, sub_zero, abs_of_nonneg (sub_nonneg.mpr hxy)] using h
  · have h := (hF y hy x hx hyx).sub_const_bound (c := 0) hyx
      (by simpa only [Set.uIcc_of_ge hyx, sub_zero] using hb)
    simpa only [smul_zero, sub_zero, norm_sub_rev (F y),
      abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub] using h

/-- Local boundedness of a continuous integrand makes any function with its
tagged integral increments continuous relative to the whole interval. This
includes a one-sided neighborhood at an included endpoint. -/
theorem continuousOn_of_tagged_increments {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f F : ℝ → E} {I : Set ℝ} (hI : I.OrdConnected)
    (hf : ContinuousOn f I)
    (hF : ∀ a ∈ I, ∀ b ∈ I, a ≤ b → FineTaggedLimit f a b (F b - F a)) :
    ContinuousOn F I := by
  intro x hx
  apply Metric.continuousWithinAt_iff.mpr
  intro ε hε
  obtain ⟨r, hr, hfbound⟩ := Metric.continuousWithinAt_iff.mp (hf x hx) 1 zero_lt_one
  let M := ‖f x‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨min r (ε/M), lt_min hr (div_pos hε hM), fun y hy hxy => ?_⟩
  have hb (t : ℝ) (ht : t ∈ Set.uIcc x y) : ‖f t‖ ≤ M := by
    have htI := hI.uIcc_subset hx hy ht
    have htx : dist t x < r := by
      rw [dist_comm t x]
      exact (Real.dist_left_le_of_mem_uIcc ht).trans_lt
        ((by simpa only [dist_comm] using hxy : dist x y < min r (ε/M)).trans_le
          (min_le_left _ _))
    have h := hfbound htI htx
    rw [dist_eq_norm] at h
    exact (norm_le_norm_sub_add (f t) (f x)).trans (by dsimp [M]; linarith)
  have hb' := norm_increment_le_of_tagged_limits hF hx hy hb
  rw [dist_eq_norm]
  apply hb'.trans_lt
  apply (lt_div_iff₀ hM).mp
  simpa only [Real.dist_eq] using hxy.trans_le (min_le_right r (ε/M))

/-- FTC is local: an interior point has a compact neighborhood contained in
the interval, where the previously proved tagged-increment FTC applies. -/
theorem hasDerivAt_of_tagged_increments {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f F : ℝ → E} {I : Set ℝ} (hf : ContinuousOn f I)
    (hF : ∀ a ∈ I, ∀ b ∈ I, a ≤ b → FineTaggedLimit f a b (F b - F a))
    {x : ℝ} (hx : x ∈ interior I) : HasDerivAt F (f x) x := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let a := x-r/2
  let b := x+r/2
  have hxi : x ∈ Set.Ioo a b := by dsimp [a, b]; constructor <;> linarith
  have hsub : Set.Icc a b ⊆ I := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    dsimp [a, b] at ht
    constructor <;> linarith [ht.1, ht.2]
  apply (withinDerivative_interior_iff F (f x) (Set.Icc a b) x
    (by simpa only [interior_Icc] using hxi)).mp
  exact accumulation_hasRealIncrementDerivativeWithin f F ⟨hxi.1.le, hxi.2.le⟩
    ((hf.mono hsub) x ⟨hxi.1.le, hxi.2.le⟩)
    (fun u hu v hv huv => hF u (hsub hu) v (hsub hv) huv)

/-- Continuity on an arbitrary interval supplies every proper compact hull. -/
theorem real_continuous_integrable_between {f : ℝ → ℝ} {I : Set ℝ}
    (hI : I.OrdConnected) (hf : ContinuousOn f I) {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) : OrientedRealIntegrable f a b := by
  apply real_continuous_integrable f min_le_max
  intro x hx
  apply (relativeContinuousAt_within_iff _ _ _).mpr
  exact (hf.mono (hI.uIcc_subset ha hb)) x hx

theorem complex_continuous_integrable_between {f : ℝ → ℂ} {I : Set ℝ}
    (hI : I.OrdConnected) (hf : ContinuousOn f I) {a b : ℝ}
    (ha : a ∈ I) (hb : b ∈ I) : OrientedComplexIntegrable f a b := by
  apply complex_continuous_integrable f min_le_max
  intro x hx
  apply (relativeContinuousAt_within_iff _ _ _).mpr
  exact (hf.mono (hI.uIcc_subset ha hb)) x hx

/-- The base point may be any member of I, including an included endpoint. -/
theorem real_continuous_primitive_construction :
    Specs.SingleVariableAnalysis.Ch09.ContinuousPrimitive.realConstruction := by
  intro f I hI hf x₀ hx₀
  let H (x y : I) := real_continuous_integrable_between hI hf x.property y.property
  let J (x y : I) := orientedRealIntegral f (H x y)
  have hAdd (x y z : I) : J x y + J y z = J x z :=
    ordered_cocycle J (fun x y => oriented_real_symmetry f x y (H x y) (H y x))
      (fun x y z hxy hyz => oriented_real_ordered_add hxy hyz (H x y) (H y z) (H x z))
      x y z
  let p : I := ⟨x₀, hx₀⟩
  obtain ⟨F, hF⟩ := exists_ambientExtension I (J p)
  have hlim : ∀ u ∈ I, ∀ v ∈ I, u ≤ v → FineTaggedLimit f u v (F v - F u) := by
    intro u hu v hv huv
    let U : I := ⟨u, hu⟩
    let V : I := ⟨v, hv⟩
    have ho : RealIntegrable f u v := by
      simpa only [U, V, OrientedRealIntegrable, O.realIntegrableValue,
        min_eq_left huv, max_eq_right huv] using H U V
    have he : F v - F u = realIntegral f ho := by
      rw [hF V, hF U]
      have h := hAdd p U V
      change J p V - J p U = _
      rw [show J p V - J p U = J U V by exact sub_eq_of_eq_add (h.symm.trans (add_comm _ _))]
      exact oriented_real_agreement f huv (H U V) ho
    rw [he]
    exact (real_tagged_equivalence f huv ho.bounded _).mp ⟨ho, rfl⟩
  refine ⟨F, ?_, ?_, continuousOn_of_tagged_increments hI hf hlim,
    fun x hx => hasDerivAt_of_tagged_increments hf hlim hx⟩
  · intro x hx
    exact ⟨H p ⟨x, hx⟩, hF ⟨x, hx⟩⟩
  · rw [hF p]
    exact (oriented_real_degenerate f x₀).choose_spec

theorem complex_continuous_primitive_construction :
    Specs.SingleVariableAnalysis.Ch09.ContinuousPrimitive.complexConstruction := by
  intro f I hI hf x₀ hx₀
  let H (x y : I) := complex_continuous_integrable_between hI hf x.property y.property
  let J (x y : I) := orientedComplexIntegral f (H x y)
  have hAdd (x y z : I) : J x y + J y z = J x z :=
    ordered_cocycle J (fun x y => oriented_complex_symmetry f x y (H x y) (H y x))
      (fun x y z hxy hyz => oriented_complex_ordered_add hxy hyz (H x y) (H y z) (H x z))
      x y z
  let p : I := ⟨x₀, hx₀⟩
  obtain ⟨F, hF⟩ := exists_ambientExtension I (J p)
  have hlim : ∀ u ∈ I, ∀ v ∈ I, u ≤ v → FineTaggedLimit f u v (F v - F u) := by
    intro u hu v hv huv
    let U : I := ⟨u, hu⟩
    let V : I := ⟨v, hv⟩
    have ho : ComplexIntegrable f u v := by
      simpa only [U, V, OrientedComplexIntegrable, O.complexIntegrableValue,
        min_eq_left huv, max_eq_right huv] using H U V
    have he : F v - F u = complexIntegral f ho := by
      rw [hF V, hF U]
      have h := hAdd p U V
      change J p V - J p U = _
      rw [show J p V - J p U = J U V by exact sub_eq_of_eq_add (h.symm.trans (add_comm _ _))]
      exact oriented_complex_agreement f huv (H U V) ho
    rw [he]
    exact (complex_tagged_equivalence f huv ho.norm_bound _).mp ⟨ho, rfl⟩
  refine ⟨F, ?_, ?_, continuousOn_of_tagged_increments hI hf hlim,
    fun x hx => hasDerivAt_of_tagged_increments hf hlim hx⟩
  · intro x hx
    exact ⟨H p ⟨x, hx⟩, hF ⟨x, hx⟩⟩
  · rw [hF p]
    exact (oriented_complex_degenerate f x₀).choose_spec

/-- Existence also includes empty and singleton intervals. For the empty
interval all restrictions are vacuous; for a singleton the construction is
the zero degenerate integral and there are no interior derivative conditions. -/
theorem real_continuous_primitive :
    Specs.SingleVariableAnalysis.Ch09.ContinuousPrimitive.realExistence := by
  intro f I hI hf
  rcases I.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨fun _ => 0, continuousOn_const, by simp⟩
  · obtain ⟨F, _, _, hc, hd⟩ := real_continuous_primitive_construction f I hI hf x₀ hx₀
    exact ⟨F, hc, hd⟩

theorem complex_continuous_primitive :
    Specs.SingleVariableAnalysis.Ch09.ContinuousPrimitive.complexExistence := by
  intro f I hI hf
  rcases I.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · exact ⟨fun _ => 0, continuousOn_const, by simp⟩
  · obtain ⟨F, _, _, hc, hd⟩ := complex_continuous_primitive_construction f I hI hf x₀ hx₀
    exact ⟨F, hc, hd⟩

end SingleVariableAnalysis.Riemann
