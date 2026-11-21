import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Unbounded.SchrodingerFreeLaplacian
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.SchrodingerPotentialBounds
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.PositiveAdjointProduct
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Tactic.LinearCombination

/-! The free Laplacian on the shared native-real-line L² spaces.

The maximal weak first derivative is densely defined, closed and skew-adjoint.
Its exact adjoint product is the canonical free Laplacian, with both weak
derivatives in L². The adjoint-product theorem gives self-adjointness.

For the actual smooth compactly supported graph core, the shifted test range
is dense: an orthogonal vector solves u″ = u weakly, and convolution with real
tests gives bounded classical solutions, which vanish. The bounded inverse of
I plus the free Laplacian carries this range density to graph density.
-/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set TopologicalSpace Filter
open scoped ENNReal Topology

namespace ExpandedFA.Unbounded.SchrodingerFreeLaplacian
open SchrodingerPotential
variable {𝕜 : Type} [RCLike 𝕜]

/-- Smooth compactly supported native-real-line tests define actual L² classes. -/
def testL2 (φ : Tests 𝕜) : L2 𝕜 :=
  (φ.continuous.memLp_of_hasCompactSupport (p := 2) φ.hasCompactSupport).toLp φ

theorem testL2_coe (φ : Tests 𝕜) : (testL2 φ : ℝ → 𝕜) =ᵐ[volume] φ :=
  MemLp.coeFn_toLp _

theorem testL2_mem_smoothCompact (φ : Tests 𝕜) : testL2 φ ∈ smoothCompact 𝕜 :=
  ⟨φ, φ.contDiff, φ.hasCompactSupport, testL2_coe φ⟩

theorem test_lineDeriv (φ : Tests 𝕜) (x : ℝ) :
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ : Tests 𝕜) x = deriv φ x := by
  rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
  rw [(φ.contDiff.differentiable (by simp) x).lineDeriv_eq_fderiv]
  rfl

/-- Converse to the test identity, with precisely the shared weak derivative. -/
theorem weakDerivative_iff_test (u v : L2 𝕜) :
    WeakDerivative u v ↔ ∀ φ : Tests 𝕜,
      (∫ x, φ x * v x) = -(∫ x, deriv φ x * u x) := by
  constructor
  · exact fun h φ => weakDerivative_test_identity h φ
  · intro h
    apply ContinuousLinearMap.ext
    intro φ
    change regular v φ = -(regular u (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ))
    simpa only [regular_apply, test_lineDeriv] using h φ

/-- Classical smooth differentiation agrees with the actual distribution graph. -/
theorem testL2_weakDerivative (φ : Tests 𝕜) :
    WeakDerivative (testL2 φ)
      (testL2 (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ)) := by
  apply (weakDerivative_iff_test _ _).mpr
  intro ψ
  have hd : ContDiff ℝ 1 (φ : ℝ → 𝕜) := φ.contDiff.of_le (by simp)
  have he := Sobolev.OneDimensional.integral_test_mul_density φ.continuous
    (fun a b => hd.contDiffOn.absolutelyContinuousOnInterval)
    ((φ.contDiff.continuous_deriv (by simp)).locallyIntegrable)
    (ae_of_all _ (fun x => (φ.contDiff.differentiable (by simp) x).hasDerivAt))
    ψ.contDiff ψ.hasCompactSupport
  calc
    (∫ x, ψ x * testL2 (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ) x) =
        ∫ x, ψ x * deriv φ x := by
      apply integral_congr_ae
      filter_upwards [testL2_coe (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ)] with x hx
      rw [hx, test_lineDeriv]
    _ = -(∫ x, deriv ψ x * φ x) := he
    _ = -(∫ x, deriv ψ x * testL2 φ x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [testL2_coe φ] with x hx
      rw [hx]

theorem testL2_mem_domain (φ : Tests 𝕜) : testL2 φ ∈ (freeLaplacian 𝕜).domain := by
  rw [(free_graph 𝕜).2, mem_H2_iff]
  exact ⟨testL2 (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ),
    testL2 (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ)
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ)),
    testL2_weakDerivative φ,
    testL2_weakDerivative (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ)⟩

theorem smooth_domain : Spec.SmoothDomain := by
  intro 𝕜 _ u hu
  obtain ⟨f, hf, hfc, huf⟩ := hu
  let φ : Tests 𝕜 := ⟨f, hf, hfc, subset_univ _⟩
  have he : u = testL2 φ := Lp.ext (huf.trans (testL2_coe φ).symm)
  rw [he]
  exact testL2_mem_domain φ

theorem smooth_dense : Spec.SmoothDense := by
  intro 𝕜 _
  apply (Lp.dense_hasCompactSupport_contDiff (F := 𝕜)
    (μ := (volume : Measure ℝ)) (p := 2) (by norm_num)).mono
  rintro u ⟨f, huf, hfc, hf⟩
  exact ⟨f, hf, hfc, huf⟩

theorem dense_domain : Spec.DenseDomain := by
  intro 𝕜 _
  exact (smooth_dense 𝕜).mono (smooth_domain 𝕜)

/-- Two integrations by parts on the genuine H² weak derivatives. -/
theorem free_symmetry : Spec.FreeSymmetry := by
  intro 𝕜 _ u v
  have hu := (freeLaplacian 𝕜).mem_graph u
  have hv := (freeLaplacian 𝕜).mem_graph v
  rw [(free_graph 𝕜).1] at hu hv
  obtain ⟨u', huu, huA⟩ := hu
  obtain ⟨v', hvv, hvA⟩ := hv
  have h₁ := weakDerivative_inner huA hvv
  have h₂ := weakDerivative_inner huu hvA
  simp only [inner_neg_left, inner_neg_right, neg_neg] at h₁ h₂
  exact (neg_injective h₁).trans h₂

/-- Density and symmetry give the preliminary adjoint inclusion. -/
theorem free_le_adjoint : freeLaplacian 𝕜 ≤ HilbertAdjointSpec.adjointValue
    (freeLaplacian 𝕜) :=
  LinearPMap.IsFormalAdjoint.le_adjoint (hT := dense_domain 𝕜) (free_symmetry 𝕜)

/-- Conjugation preserves the actual native-real-line test space. -/
def conjugateTest (φ : Tests 𝕜) : Tests 𝕜 :=
  TestFunction.postcompCLM (RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap φ

theorem conjugateTest_apply (φ : Tests 𝕜) (x : ℝ) :
    conjugateTest φ x = starRingEnd 𝕜 (φ x) := rfl

theorem deriv_conjugateTest (φ : Tests 𝕜) (x : ℝ) :
    deriv (conjugateTest φ) x = starRingEnd 𝕜 (deriv φ x) := by
  exact ((RCLike.conjCLE : 𝕜 ≃L[ℝ] 𝕜).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt x
    (φ.contDiff.differentiable (by simp) x).hasDerivAt).deriv

/-- Test evaluation is an ordinary continuous L² inner product. -/
theorem regular_eq_inner (u : L2 𝕜) (φ : Tests 𝕜) :
    regular u φ = inner 𝕜 (testL2 (conjugateTest φ)) u := by
  rw [regular_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [testL2_coe (conjugateTest φ)] with x hx
  simp only [hx, RCLike.inner_apply', conjugateTest_apply, starRingEnd_apply, star_star]

/-- The maximal graph of the first weak derivative. -/
def derivativeGraph (𝕜 : Type) [RCLike 𝕜] : Submodule 𝕜 (L2 𝕜 × L2 𝕜) where
  carrier := {p | WeakDerivative p.1 p.2}
  zero_mem' := by simp [WeakDerivative, distributionDerivative]
  add_mem' := by
    rintro ⟨u, v⟩ ⟨w, z⟩ huv hwz
    simpa [WeakDerivative, distributionDerivative, map_add, ContinuousLinearMap.add_comp,
      neg_add, add_comm] using congrArg₂ (· + ·) huv hwz
  smul_mem' := by
    rintro c ⟨u, v⟩ huv
    simpa [WeakDerivative, distributionDerivative, map_smul,
      ContinuousLinearMap.smul_comp, smul_neg] using congrArg (c • ·) huv

/-- The actual maximal first-derivative operator on real or complex L²(ℝ). -/
def derivative (𝕜 : Type) [RCLike 𝕜] : Operator 𝕜 (L2 𝕜) (L2 𝕜) :=
  (derivativeGraph 𝕜).toLinearPMap

theorem derivative_graph : (derivative 𝕜).graph = derivativeGraph 𝕜 := by
  apply Submodule.toLinearPMap_graph_eq
  intro p hp hz
  exact weakDerivative_zero (hz ▸ hp)

theorem mem_derivative_graph (u v : L2 𝕜) :
    (u, v) ∈ (derivative 𝕜).graph ↔ WeakDerivative u v := by
  rw [derivative_graph]
  rfl

theorem derivative_weakDerivative (u : (derivative 𝕜).domain) :
    WeakDerivative u.val (derivative 𝕜 u) :=
  (mem_derivative_graph _ _).mp ((derivative 𝕜).mem_graph u)

theorem testL2_mem_derivative_domain (φ : Tests 𝕜) :
    testL2 φ ∈ (derivative 𝕜).domain := by
  apply ((derivative 𝕜).mem_domain_iff).mpr
  exact ⟨_, (mem_derivative_graph _ _).mpr (testL2_weakDerivative φ)⟩

theorem derivative_testL2 (φ : Tests 𝕜) :
    derivative 𝕜 ⟨testL2 φ, testL2_mem_derivative_domain φ⟩ =
      testL2 (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ) :=
  ((LinearPMap.image_iff _).mpr ((mem_derivative_graph _ _).mpr
    (testL2_weakDerivative φ))).symm

theorem derivative_dense : Dense ((derivative 𝕜).domain : Set (L2 𝕜)) := by
  apply (smooth_dense 𝕜).mono
  rintro u ⟨f, hf, hfc, huf⟩
  let φ : Tests 𝕜 := ⟨f, hf, hfc, subset_univ _⟩
  have he : u = testL2 φ := Lp.ext (huf.trans (testL2_coe φ).symm)
  rw [he]
  exact testL2_mem_derivative_domain φ

theorem derivative_closed : (derivative 𝕜).IsClosed := by
  change _root_.IsClosed ((derivative 𝕜).graph : Set (L2 𝕜 × L2 𝕜))
  rw [derivative_graph]
  have he : (derivativeGraph 𝕜 : Set (L2 𝕜 × L2 𝕜)) =
      ⋂ φ : Tests 𝕜, {p | regular p.2 φ =
        -(regular p.1 (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ))} := by
    ext p
    simp only [mem_iInter, mem_ofPred_eq]
    change WeakDerivative p.1 p.2 ↔ _
    constructor
    · intro h φ
      exact congrArg (fun T : Distribution 𝕜 => T φ) h
    · intro h
      exact ContinuousLinearMap.ext h
  rw [he]
  apply isClosed_iInter
  intro φ
  simp_rw [regular_eq_inner]
  exact isClosed_eq (continuous_const.inner continuous_snd)
    (continuous_const.inner continuous_fst).neg

/-- Testing the adjoint against conjugate tests identifies its full weak graph. -/
theorem derivative_adjoint_weakDerivative (y : (derivative 𝕜).adjoint.domain) :
    WeakDerivative y.val (-((derivative 𝕜).adjoint y)) := by
  apply (weakDerivative_iff_test _ _).mpr
  intro φ
  let ψ := conjugateTest φ
  let x : (derivative 𝕜).domain := ⟨testL2 ψ, testL2_mem_derivative_domain ψ⟩
  have hi := (LinearPMap.adjoint_isFormalAdjoint (derivative_dense (𝕜 := 𝕜))).symm x y
  change inner 𝕜 (derivative 𝕜 x) y.val = inner 𝕜 x.val ((derivative 𝕜).adjoint y) at hi
  have hx : derivative 𝕜 x = testL2 (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) ψ) :=
    derivative_testL2 ψ
  rw [hx, L2.inner_def, L2.inner_def] at hi
  have h₁ : (∫ t, inner 𝕜 (testL2 (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) ψ) t) (y.val t)) =
      ∫ t, deriv φ t * y.val t := by
    apply integral_congr_ae
    filter_upwards [testL2_coe (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) ψ)] with t ht
    rw [ht, test_lineDeriv]
    dsimp only [ψ]
    rw [deriv_conjugateTest]
    simp [mul_comm]
  have h₂ : (∫ t, inner 𝕜 (x.val t) ((derivative 𝕜).adjoint y t)) =
      ∫ t, φ t * (derivative 𝕜).adjoint y t := by
    apply integral_congr_ae
    filter_upwards [testL2_coe ψ] with t ht
    change inner 𝕜 (testL2 ψ t) _ = _
    rw [ht]
    simp [ψ, conjugateTest_apply, mul_comm]
  rw [h₁, h₂] at hi
  calc
    (∫ t, φ t * (-((derivative 𝕜).adjoint y) : L2 𝕜) t) =
        -(∫ t, φ t * (derivative 𝕜).adjoint y t) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_neg ((derivative 𝕜).adjoint y)] with t ht
      exact (congrArg (φ t * ·) ht).trans (mul_neg _ _)
    _ = -(∫ t, deriv φ t * y.val t) := congrArg Neg.neg hi.symm

/-- The maximal first derivative is skew-adjoint on its exact weak domain. -/
theorem derivative_adjoint : (derivative 𝕜).adjoint = -(derivative 𝕜) := by
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro p hp
    obtain ⟨y, hy, hz⟩ := ((derivative 𝕜).adjoint).mem_graph_iff.mp hp
    have hw := derivative_adjoint_weakDerivative y
    have hm : (y.val, -((derivative 𝕜).adjoint y)) ∈ (derivative 𝕜).graph :=
      (mem_derivative_graph _ _).mpr hw
    obtain ⟨x, hx, hdx⟩ := ((derivative 𝕜).mem_graph_iff).mp hm
    refine (-(derivative 𝕜)).mem_graph_iff.mpr ⟨x, hx.trans hy, ?_⟩
    change -(derivative 𝕜 x) = p.2
    rw [hdx, neg_neg, hz]
  · apply LinearPMap.IsFormalAdjoint.le_adjoint (derivative_dense (𝕜 := 𝕜))
    intro x y
    change inner 𝕜 (derivative 𝕜 x) y.val = inner 𝕜 x.val (-(derivative 𝕜 y))
    rw [inner_neg_right]
    exact weakDerivative_inner (derivative_weakDerivative x) (derivative_weakDerivative y)

/-- Product graphs retain both intermediate domain conditions. -/
theorem mem_product_graph (A B : Operator 𝕜 (L2 𝕜) (L2 𝕜)) (u f : L2 𝕜) :
    (u, f) ∈ (OperatorDomainsSpec.productValue A B).graph ↔
      ∃ v, (u, v) ∈ B.graph ∧ (v, f) ∈ A.graph := by
  constructor
  · intro h
    obtain ⟨x, hx, hf⟩ := (OperatorDomainsSpec.productValue A B).mem_graph_iff.mp h
    let b : B.domain := ⟨x.val, x.prop.choose⟩
    let a : A.domain := ⟨B b, x.prop.choose_spec⟩
    exact ⟨B b, B.mem_graph_iff.mpr ⟨b, hx, rfl⟩,
      A.mem_graph_iff.mpr ⟨a, rfl, hf⟩⟩
  · rintro ⟨v, hb, ha⟩
    obtain ⟨b, hbu, hbv⟩ := B.mem_graph_iff.mp hb
    obtain ⟨a, hav, haf⟩ := A.mem_graph_iff.mp ha
    change b.val = u at hbu
    change B b = v at hbv
    change a.val = v at hav
    change A a = f at haf
    have hBa : B b ∈ A.domain := by rw [hbv, ← hav]; exact a.prop
    let x : (OperatorDomainsSpec.productValue A B).domain :=
      ⟨b.val, ⟨b.prop, hBa⟩⟩
    refine (OperatorDomainsSpec.productValue A B).mem_graph_iff.mpr ⟨x, hbu, ?_⟩
    change A ⟨B b, hBa⟩ = f
    have he : (⟨B b, hBa⟩ : A.domain) = a := Subtype.ext (hbv.trans hav.symm)
    rw [he, haf]

theorem mem_negative_derivative_graph (u f : L2 𝕜) :
    (u, f) ∈ (-(derivative 𝕜)).graph ↔ WeakDerivative u (-f) := by
  constructor
  · intro h
    obtain ⟨x, hx, hf⟩ := (-(derivative 𝕜)).mem_graph_iff.mp h
    change x.val = u at hx
    have hw := derivative_weakDerivative x
    change -(derivative 𝕜 x) = f at hf
    rwa [← hf, neg_neg, ← hx]
  · intro h
    obtain ⟨x, hx, hf⟩ := (derivative 𝕜).mem_graph_iff.mp
      ((mem_derivative_graph _ _).mpr h)
    refine (-(derivative 𝕜)).mem_graph_iff.mpr ⟨x, hx, ?_⟩
    change -(derivative 𝕜 x) = f
    rw [hf, neg_neg]

/-- Exact graph identification with D*D, including the intermediate L²
first derivative. This proves equality of operators, hence of their domains. -/
theorem free_eq_adjointProduct : freeLaplacian 𝕜 =
    PositiveAdjointProductSpec.adjointProduct (derivative 𝕜) := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  obtain ⟨u, f⟩ := p
  rw [(free_graph 𝕜).1]
  change (∃ v, WeakDerivative u v ∧ WeakDerivative v (-f)) ↔ _
  change (∃ v, WeakDerivative u v ∧ WeakDerivative v (-f)) ↔
    (u, f) ∈ (OperatorDomainsSpec.productValue (derivative 𝕜).adjoint (derivative 𝕜)).graph
  rw [derivative_adjoint, mem_product_graph]
  simp only [mem_derivative_graph, mem_negative_derivative_graph]

/-- Self-adjointness is proved on the canonical native-real-line H² domain,
uniformly for real and complex scalar-valued L². -/
theorem free_selfAdjoint : SelfAdjoint (freeLaplacian 𝕜) := by
  rw [free_eq_adjointProduct]
  exact ⟨PositiveAdjointProduct.product_dense (derivative 𝕜)
      derivative_dense derivative_closed,
    PositiveAdjointProduct.product_selfAdjoint (derivative 𝕜)
      derivative_dense derivative_closed⟩

theorem free_closed : Spec.FreeClosed := by
  intro 𝕜 _
  rw [(free_selfAdjoint (𝕜 := 𝕜)).2]
  exact LinearPMap.adjoint_isClosed (dense_domain 𝕜)

/-- A bounded solution of H′ = H on the whole real line is zero. -/
theorem bounded_solution_deriv_eq_self {H : ℝ → 𝕜}
    (hH : ∀ x, HasDerivAt H (H x) x) (B : ℝ) (hb : ∀ x, ‖H x‖ ≤ B) :
    ∀ x, H x = 0 := by
  let K : ℝ → 𝕜 := fun x => Real.exp (-x) • H x
  have hd (x : ℝ) : HasDerivAt K 0 x := by
    have he := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).smul (hH x)
    convert! he using 1
    simp [neg_smul]
  have hc (x y : ℝ) : K x = K y :=
    is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) x y
  have hlim : Tendsto (fun t : ℝ => ‖K t‖) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) (fun t => ?_)
      (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const B)
    change ‖Real.exp (-t) • H t‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (hb t) (Real.exp_pos _).le
  intro x
  have hz : ‖K x‖ = 0 := by
    have he : (fun t : ℝ => ‖K t‖) = fun _ => ‖K x‖ := funext (fun t => congrArg norm (hc t x))
    rw [he] at hlim
    exact tendsto_nhds_unique tendsto_const_nhds hlim
  have he := norm_eq_zero.mp hz
  exact (smul_eq_zero.mp he).resolve_left (ne_of_gt (Real.exp_pos _))

set_option backward.isDefEq.respectTransparency false in
/-- Bounded solutions of F″ = F vanish. Bounds on F and F′ are enough,
and are available directly from L² convolution estimates. -/
theorem bounded_solution_second_deriv_eq_self {F G : ℝ → 𝕜}
    (hF : ∀ x, HasDerivAt F (G x) x) (hG : ∀ x, HasDerivAt G (F x) x)
    (B C : ℝ) (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖G x‖ ≤ C) :
    ∀ x, F x = 0 := by
  have hplus : ∀ x, F x + G x = 0 := by
    apply bounded_solution_deriv_eq_self (B := B + C)
    · intro x
      convert! (hF x).add (hG x) using 1
      simp [add_comm]
    · exact fun x => (norm_add_le _ _).trans (add_le_add (hB x) (hC x))
  have hminus : ∀ x, F x - G x = 0 := by
    have h := bounded_solution_deriv_eq_self
      (H := fun x => F (-x) - G (-x))
      (fun x => by
        convert! ((hF (-x)).scomp x (hasDerivAt_neg x)).sub
          ((hG (-x)).scomp x (hasDerivAt_neg x)) using 1
        simp [sub_eq_add_neg, add_comm])
      (B + C) (fun x => (norm_sub_le _ _).trans (add_le_add (hB (-x)) (hC (-x))))
    intro x
    simpa using h (-x)
  intro x
  have h₂ : (2 : 𝕜) * F x = 0 := by
    linear_combination hplus x + hminus x
  exact (mul_eq_zero.mp h₂).resolve_left (by norm_num)

/-- Reflection and translation keep a native-real-line test compactly supported. -/
def reflectTest (φ : Tests ℝ) (x : ℝ) : Tests ℝ where
  toFun := fun t => φ (x - t)
  contDiff' := φ.contDiff.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.subLeft x)
  tsupport_subset' := subset_univ _

/-- Real kernels act on both actual scalar-valued L² spaces. -/
def convolveTest (u : L2 𝕜) (φ : Tests ℝ) : ℝ → 𝕜 :=
  convolution (u : ℝ → 𝕜) φ (ContinuousLinearMap.lsmul ℝ ℝ).flip volume

theorem convolveTest_hasDerivAt (u : L2 𝕜) (φ : Tests ℝ) (x : ℝ) :
    HasDerivAt (convolveTest u φ)
      (convolveTest u (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) φ) x) x := by
  have he := φ.hasCompactSupport.hasDerivAt_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ).flip
    ((Lp.memLp u).locallyIntegrable (by norm_num))
    (φ.contDiff.of_le (by simp) : ContDiff ℝ 1 (φ : ℝ → ℝ)) x
  have hφ : (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) φ : ℝ → ℝ) = deriv φ :=
    funext (test_lineDeriv φ)
  simpa only [convolveTest, hφ] using he

theorem convolveTest_bounded (u : L2 𝕜) (φ : Tests ℝ) :
    ∃ B : ℝ, ∀ x, ‖convolveTest u φ x‖ ≤ B := by
  have hm : MemLp (φ : ℝ → ℝ) 2 volume :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  let M : ℝ≥0∞ := ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] 𝕜 →L[ℝ] 𝕜).flip‖ₑ *
    eLpNorm (u : ℝ → 𝕜) 2 volume * eLpNorm (φ : ℝ → ℝ) 2 volume
  have hM : M ≠ ⊤ := by
    exact (ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp)
      (Lp.memLp u).eLpNorm_lt_top) hm.eLpNorm_lt_top).ne
  refine ⟨M.toReal, fun x => ?_⟩
  have he := enorm_convolution_le (p := 2) (q := 2)
    (ContinuousLinearMap.lsmul ℝ ℝ).flip (Lp.memLp u).aestronglyMeasurable
    hm.aestronglyMeasurable x
  exact (ENNReal.toReal_mono hM he).trans_eq (by simp)

theorem reflectTest_derivative (φ : Tests ℝ) (x : ℝ) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) (reflectTest φ x) =
      -reflectTest (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) φ) x := by
  ext t
  rw [test_lineDeriv]
  change deriv (fun s => φ (x - s)) t =
    -(TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) φ (x - t))
  rw [test_lineDeriv]
  exact deriv_comp_const_sub (φ : ℝ → ℝ) x t

theorem reflectTest_second_derivative (φ : Tests ℝ) (x : ℝ) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ)
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) (reflectTest φ x)) =
    reflectTest (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ)
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) φ)) x := by
  rw [reflectTest_derivative, map_neg, reflectTest_derivative, neg_neg]

/-- The homogeneous weak resolvent equation has no nonzero L² solutions.
Only real kernels are used; the unknown may be genuinely real or complex. -/
theorem weak_second_resolvent_unique (u : L2 𝕜)
    (h : ∀ φ : Tests ℝ,
      (∫ t, (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ)
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) φ)) t • u t) = ∫ t, φ t • u t) :
    u = 0 := by
  have hzero (φ : Tests ℝ) : ∀ x, convolveTest u φ x = 0 := by
    have he (x : ℝ) : convolveTest u (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ)
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) φ)) x = convolveTest u φ x := by
      have hi := h (reflectTest φ x)
      rw [reflectTest_second_derivative] at hi
      exact hi
    obtain ⟨B, hB⟩ := convolveTest_bounded u φ
    obtain ⟨C, hC⟩ := convolveTest_bounded u (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) φ)
    apply bounded_solution_second_deriv_eq_self (convolveTest_hasDerivAt u φ)
      (fun x => ?_) B C hB hC
    rw [← he x]
    exact convolveTest_hasDerivAt u (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) φ) x
  apply Lp.ext
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((Lp.memLp u).locallyIntegrable (by norm_num)) (fun g hg hgc => ?_)
  · filter_upwards [hz, Lp.coeFn_zero 𝕜 2 (volume : Measure ℝ)] with t ht hzt
    exact ht.trans hzt.symm
  · let φ : Tests ℝ := ⟨g, hg, hgc, subset_univ _⟩
    have hi := hzero (reflectTest φ 0) 0
    change (∫ t, φ (0 - (0 - t)) • u t) = 0 at hi
    convert! hi using 1
    congr 1
    funext t
    simp only [sub_sub_cancel]
    rfl

/-- Real tests, included pointwise into the chosen scalar field. -/
def realTest (φ : Tests ℝ) : Tests 𝕜 :=
  TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) φ

theorem realTest_apply (φ : Tests ℝ) (t : ℝ) :
    realTest (𝕜 := 𝕜) φ t = (φ t : 𝕜) := rfl

theorem realTest_derivative (φ : Tests ℝ) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) (realTest (𝕜 := 𝕜) φ) =
      realTest (𝕜 := 𝕜) (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) φ) := by
  ext t
  rw [test_lineDeriv]
  change deriv (fun x => (φ x : 𝕜)) t =
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ (1 : ℝ) φ t : 𝕜)
  rw [test_lineDeriv]
  exact ((RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).hasFDerivAt.comp_hasDerivAt t
    (φ.contDiff.differentiable (by simp) t).hasDerivAt).deriv

theorem inner_testL2_realTest (φ : Tests ℝ) (u : L2 𝕜) :
    inner 𝕜 (testL2 (realTest φ)) u = ∫ t, φ t • u t := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [testL2_coe (realTest (𝕜 := 𝕜) φ)] with t ht
  rw [ht, realTest_apply]
  simp [RCLike.real_smul_eq_coe_mul, mul_comm]

/-- The free operator is classical -φ″ on every actual test class. -/
theorem free_testL2 (φ : Tests 𝕜) :
    freeLaplacian 𝕜 ⟨testL2 φ, testL2_mem_domain φ⟩ =
      -testL2 (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ)
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ)) := by
  apply Eq.symm
  apply (LinearPMap.image_iff _).mpr
  rw [(free_graph 𝕜).1]
  refine ⟨testL2 (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ),
    testL2_weakDerivative φ, ?_⟩
  simpa only [neg_neg] using
    testL2_weakDerivative (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) 𝕜 (1 : ℝ) φ)

/-- I plus the free operator on the actual smooth compactly supported subspace. -/
def smoothShift (𝕜 : Type) [RCLike 𝕜] : smoothCompact 𝕜 →ₗ[𝕜] L2 𝕜 :=
  (smoothCompact 𝕜).subtype + (freeLaplacian 𝕜).toFun.comp
    (Submodule.inclusion (smooth_domain 𝕜))

theorem smoothShift_apply (u : smoothCompact 𝕜) :
    smoothShift 𝕜 u = u.val + freeLaplacian 𝕜 ⟨u.val, smooth_domain 𝕜 u.prop⟩ := rfl

/-- The shifted test range is dense. Orthogonality gives the homogeneous
weak resolvent equation, whose uniqueness was proved above. -/
theorem smoothShift_dense : Dense ((smoothShift 𝕜).range : Set (L2 𝕜)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  apply le_antisymm _ bot_le
  intro u hu
  change u = 0
  apply weak_second_resolvent_unique
  intro φ
  let ψ : Tests 𝕜 := realTest φ
  let x : smoothCompact 𝕜 := ⟨testL2 ψ, testL2_mem_smoothCompact ψ⟩
  have hi := hu _ (show smoothShift 𝕜 x ∈ (smoothShift 𝕜).range from ⟨x, rfl⟩)
  rw [smoothShift_apply] at hi
  change inner 𝕜 (testL2 ψ + freeLaplacian 𝕜 ⟨testL2 ψ, _⟩) u = 0 at hi
  rw [free_testL2, inner_add_left, inner_neg_left] at hi
  dsimp only [ψ] at hi
  rw [realTest_derivative, realTest_derivative, inner_testL2_realTest,
    inner_testL2_realTest] at hi
  exact (sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hi)).symm

/-- The bounded inverse of I minus the second derivative. It is obtained from
the closed first derivative, without using the desired core assertion. -/
def freeResolvent (𝕜 : Type) [RCLike 𝕜] : L2 𝕜 →L[𝕜] L2 𝕜 :=
  PositiveAdjointProduct.inverse (derivative 𝕜) derivative_dense derivative_closed

theorem freeResolvent_right (f : L2 𝕜) :
    ∃ hx : freeResolvent 𝕜 f ∈ (freeLaplacian 𝕜).domain,
      freeResolvent 𝕜 f + freeLaplacian 𝕜 ⟨freeResolvent 𝕜 f, hx⟩ = f := by
  rw [free_eq_adjointProduct]
  exact PositiveAdjointProduct.inverse_right (derivative 𝕜) derivative_dense derivative_closed f

theorem freeResolvent_left (u : (freeLaplacian 𝕜).domain) :
    freeResolvent 𝕜 (u.val + freeLaplacian 𝕜 u) = u.val := by
  revert u
  rw [free_eq_adjointProduct]
  exact PositiveAdjointProduct.inverse_left (derivative 𝕜) derivative_dense derivative_closed

/-- A continuous parametrization of the whole free graph. -/
def freeResolventGraph (𝕜 : Type) [RCLike 𝕜] : L2 𝕜 →L[𝕜] (L2 𝕜 × L2 𝕜) :=
  (freeResolvent 𝕜).prod (ContinuousLinearMap.id 𝕜 (L2 𝕜) - freeResolvent 𝕜)

theorem freeResolventGraph_left (u : (freeLaplacian 𝕜).domain) :
    freeResolventGraph 𝕜 (u.val + freeLaplacian 𝕜 u) = (u.val, freeLaplacian 𝕜 u) := by
  change (freeResolvent 𝕜 (u.val + freeLaplacian 𝕜 u),
    u.val + freeLaplacian 𝕜 u - freeResolvent 𝕜 (u.val + freeLaplacian 𝕜 u)) = _
  rw [freeResolvent_left]
  congr 1
  abel

/-- Graph density of the actual C∞ compactly supported subspace. The dense
shifted range is carried into its restricted graph by a bounded map. -/
theorem free_core : OperatorDomainsSpec.coreValue (freeLaplacian 𝕜) (smoothCompact 𝕜) := by
  refine ⟨smooth_domain 𝕜, ?_⟩
  apply le_antisymm
  · exact Submodule.topologicalClosure_mono
      (LinearPMap.le_graph_of_le (LinearPMap.domRestrict_le))
  · have hincl : (freeLaplacian 𝕜).graph ≤
        ((freeLaplacian 𝕜).domRestrict (smoothCompact 𝕜)).graph.topologicalClosure := by
      intro p hp
      obtain ⟨u, hu, hAu⟩ := (freeLaplacian 𝕜).mem_graph_iff.mp hp
      let f := u.val + freeLaplacian 𝕜 u
      have hf : f ∈ _root_.closure ((smoothShift 𝕜).range : Set (L2 𝕜)) := smoothShift_dense f
      have hm := mem_closure_image (freeResolventGraph 𝕜).continuous.continuousAt hf
      have himage : freeResolventGraph 𝕜 '' ((smoothShift 𝕜).range : Set (L2 𝕜)) ⊆
          (((freeLaplacian 𝕜).domRestrict (smoothCompact 𝕜)).graph :
            Set (L2 𝕜 × L2 𝕜)) := by
        rintro _ ⟨g, ⟨x, rfl⟩, rfl⟩
        rw [smoothShift_apply,
          freeResolventGraph_left ⟨x.val, smooth_domain 𝕜 x.prop⟩]
        exact ((freeLaplacian 𝕜).domRestrict (smoothCompact 𝕜)).mem_graph
          ⟨x.val, x.prop, smooth_domain 𝕜 x.prop⟩
      have he : freeResolventGraph 𝕜 f = p := by
        exact (freeResolventGraph_left u).trans (Prod.ext hu hAu)
      rw [he] at hm
      exact closure_mono himage hm
    exact (freeLaplacian 𝕜).graph.topologicalClosure_minimal hincl
      (((freeLaplacian 𝕜).domRestrict (smoothCompact 𝕜)).graph.isClosed_topologicalClosure)

/-- Both field clauses now contain actual self-adjointness, graph-core density,
and the previously proved energy identity on the actual weak derivative. -/
theorem free_facts (𝕜 : Type) [RCLike 𝕜] : SchrodingerPotential.Spec.FreeFacts 𝕜 :=
  ⟨free_selfAdjoint, free_core, free_energy 𝕜⟩

theorem free_real : Spec.FreeReal := free_facts ℝ

theorem free_complex : Spec.FreeComplex := free_facts ℂ

end ExpandedFA.Unbounded.SchrodingerFreeLaplacian
