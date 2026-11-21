import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.ContinuousDistributionPrimitives
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! Work towards paper.tex:17236. The cutoff lemmas below turn any proved finite
continuous-density representation into one supported in a prescribed open
neighborhood. They do not assume the continuous-primitives theorem itself. -/
open Set TopologicalSpace MeasureTheory
open scoped Distributions ContDiff Manifold

namespace ExpandedFA.Distributions
namespace ContinuousDistributionPrimitives

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

/-- Continuous densities have the stated, unconjugated distribution pairing. -/
theorem primitivePairing_eq_derivative (w : List (Fin d))
    (f : Domain d → 𝕜) (hf : Continuous f) (φ : Tests 𝕜 Ω) :
    continuousPrimitivePairing w f φ =
      distributionDerivative 𝕜 d Ω w (regularDistribution volume f) φ := by
  rw [distributionDerivative_apply,
    regularDistribution_apply volume f (hf.locallyIntegrable.locallyIntegrableOn Ω)]
  rfl

/-- A test derivative has no support outside that of the original test. -/
theorem tsupport_testPartial_subset (w : List (Fin d)) (φ : Tests 𝕜 Ω) :
    tsupport (testPartialCLM w φ) ⊆ tsupport φ := by
  induction w with
  | nil => exact Subset.rfl
  | cons i w ih =>
    rw [testPartial_formula 𝕜 d Ω (i :: w) φ]
    change tsupport (fun x => fderiv ℝ (partialFunction w φ) x (coordinateVector i)) ⊆ _
    exact (tsupport_fderiv_apply_subset ℝ (coordinateVector i)).trans
      ((by rw [testPartial_formula 𝕜 d Ω w φ] at ih; exact ih))

/-- Disjoint primitive and test supports make each actual derivative pairing zero. -/
theorem primitivePairing_eq_zero_of_disjoint (w : List (Fin d))
    (f : Domain d → 𝕜) (φ : Tests 𝕜 Ω) (h : Disjoint (tsupport f) (tsupport φ)) :
    continuousPrimitivePairing w f φ = 0 := by
  have hi : (fun x => f x * testPartialCLM w φ x) = 0 := by
    funext x
    by_cases hx : x ∈ tsupport f
    · have hxφ : x ∉ tsupport φ := fun hxφ => Set.disjoint_left.mp h hx hxφ
      have hxD : x ∉ tsupport (testPartialCLM w φ) :=
        fun hxD => hxφ (tsupport_testPartial_subset w φ hxD)
      simp [image_eq_zero_of_notMem_tsupport hxD]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  simp [continuousPrimitivePairing, hi]

/-- Zero is represented by the empty finite family, for all dimensions/domains. -/
theorem hasContinuousPrimitives_zero (S : Set (Domain d)) :
    HasContinuousPrimitives (0 : ScalarDistribution 𝕜 Ω) S := by
  refine ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, ?_, ?_⟩
  · exact fun j => PEmpty.elim j
  · intro φ
    simp

theorem hasContinuousPrimitives_add {u v : ScalarDistribution 𝕜 Ω}
    {S : Set (Domain d)} (hu : HasContinuousPrimitives u S)
    (hv : HasContinuousPrimitives v S) : HasContinuousPrimitives (u + v) S := by
  classical
  obtain ⟨ι, hι, w, f, hf, hu⟩ := hu
  obtain ⟨κ, hκ, z, g, hg, hv⟩ := hv
  let := hι
  let := hκ
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim w z, Sum.elim f g, ?_, ?_⟩
  · intro j
    cases j with
    | inl j => exact hf j
    | inr j => exact hg j
  · intro φ
    simp only [add_apply, hu, hv, Fintype.sum_sum_type]
    rfl

theorem hasContinuousPrimitives_smul (c : 𝕜) {u : ScalarDistribution 𝕜 Ω}
    {S : Set (Domain d)} (hu : HasContinuousPrimitives u S) :
    HasContinuousPrimitives (c • u) S := by
  classical
  obtain ⟨ι, hι, w, f, hf, hu⟩ := hu
  let := hι
  refine ⟨ι, inferInstance, w, fun j x => c * f j x, ?_, ?_⟩
  · intro j
    exact ⟨continuous_const.mul (hf j).1,
      (hf j).2.1.mul_left,
      tsupport_mul_subset_right.trans (hf j).2.2⟩
  · intro φ
    rw [smul_apply, hu, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [continuousPrimitivePairing, smul_eq_mul]
    rw [show (fun x => c * f j x * testPartialCLM (w j) φ x) =
        fun x => c * (f j x * testPartialCLM (w j) φ x) by
      funext x; ring, integral_const_mul]
    ring

theorem hasContinuousPrimitives_neg {u : ScalarDistribution 𝕜 Ω}
    {S : Set (Domain d)} (hu : HasContinuousPrimitives u S) :
    HasContinuousPrimitives (-u) S := by
  have h : (-1 : 𝕜) • u = -u := by
    ext φ
    simp
  rw [← h]
  exact hasContinuousPrimitives_smul (-1 : 𝕜) hu

theorem hasContinuousPrimitives_sum {ι : Type*} (s : Finset ι)
    (u : ι → ScalarDistribution 𝕜 Ω) {S : Set (Domain d)}
    (hu : ∀ j ∈ s, HasContinuousPrimitives (u j) S) :
    HasContinuousPrimitives (∑ j ∈ s, u j) S := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasContinuousPrimitives_zero (𝕜 := 𝕜) (Ω := Ω) S
  | @insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact hasContinuousPrimitives_add (hu j (Finset.mem_insert_self j s))
      (ih fun k hk => hu k (Finset.mem_insert_of_mem hk))

/-- The transpose reverses composition order. Appending a coordinate to a word
therefore differentiates the corresponding distribution once more. -/
theorem testPartial_append (v w : List (Fin d)) :
    (testPartialCLM (Ω := Ω) (𝕜 := 𝕜) (v ++ w)) =
      (testPartialCLM v).comp (testPartialCLM w) := by
  induction v with
  | nil => ext φ x; rfl
  | cons i v ih =>
    simp only [List.cons_append, testPartialCLM, ih, ContinuousLinearMap.comp_assoc]

theorem distributionDerivative_append (v w : List (Fin d))
    (u : ScalarDistribution 𝕜 Ω) :
    distributionDerivative 𝕜 d Ω (v ++ w) u =
      distributionDerivative 𝕜 d Ω w (distributionDerivative 𝕜 d Ω v u) := by
  ext φ
  simp only [distributionDerivative_apply, List.length_append, pow_add, testPartial_append,
    ContinuousLinearMap.comp_apply]
  ring

theorem hasContinuousPrimitives_derivative (w : List (Fin d))
    {u : ScalarDistribution 𝕜 Ω} {S : Set (Domain d)}
    (hu : HasContinuousPrimitives u S) :
    HasContinuousPrimitives (distributionDerivative 𝕜 d Ω w u) S := by
  classical
  obtain ⟨ι, hι, v, f, hf, hu⟩ := hu
  let := hι
  refine ⟨ι, inferInstance, fun j => v j ++ w, f, hf, ?_⟩
  intro φ
  rw [distributionDerivative_apply, hu]
  simp only [continuousPrimitivePairing, List.length_append, pow_add,
    testPartial_append, ContinuousLinearMap.comp_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A single globally continuous, compactly supported density is an order-zero
primitive. This lemma asserts its actual integral representation. -/
theorem hasContinuousPrimitives_regular (f : Domain d → 𝕜) (hf : Continuous f)
    (hc : HasCompactSupport f) {S : Set (Domain d)} (hs : tsupport f ⊆ S) :
    HasContinuousPrimitives (regularDistribution volume f : ScalarDistribution 𝕜 Ω) S := by
  refine ⟨Unit, inferInstance, fun _ => [], fun _ => f, fun _ => ⟨hf, hc, hs⟩, ?_⟩
  intro φ
  simp only [Fintype.sum_unique, primitivePairing_eq_derivative _ _ hf,
    distributionDerivative_nil]

/-- Multiplying a continuous density is the same operation before and after
passing to its integration distribution. -/
theorem multiply_regular (a : Domain d → 𝕜) (ha : ContDiff ℝ ∞ a)
    (f : Domain d → 𝕜) (hf : Continuous f) :
    multiplyDistribution ⟨a, ha.contDiffOn⟩
      (regularDistribution volume f : ScalarDistribution 𝕜 Ω) =
      regularDistribution volume (fun x => a x * f x) := by
  ext φ
  rw [multiplyDistribution_apply,
    regularDistribution_apply volume f (hf.locallyIntegrable.locallyIntegrableOn Ω),
    regularDistribution_apply volume (fun x => a x * f x)
      ((ha.continuous.mul hf).locallyIntegrable.locallyIntegrableOn Ω)]
  congr 1
  funext x
  simp only [multiplyTestCLM_apply]
  ring

/-- First-order integration by parts with a smooth coefficient, solved for the
product of that coefficient and a differentiated distribution. -/
theorem multiply_derivative (i : Fin d) (a : SmoothCoefficient 𝕜 Ω)
    (u : ScalarDistribution 𝕜 Ω) :
    multiplyDistribution a (distributionDerivative 𝕜 d Ω [i] u) =
      distributionDerivative 𝕜 d Ω [i] (multiplyDistribution a u) -
        multiplyDistribution (coefficientPartial i a) u := by
  have h := distribution_leibniz i a u
  have hd (v : ScalarDistribution 𝕜 Ω) :
      distributionDerivative 𝕜 d Ω [i] v = -v.comp (testPartialCLM [i]) := by
    ext φ
    simp only [distributionDerivative_apply, List.length_singleton, pow_one, neg_one_mul,
      neg_apply, ContinuousLinearMap.comp_apply]
  simp only [hd] at ⊢
  rw [h]
  abel

/-- Cutoffs convert any derivative of a continuous density into a finite sum
of derivatives of continuous densities supported in the cutoff's support.
The input density is not required to be compactly supported. -/
theorem cutoff_derivative_regular (w : List (Fin d))
    (f : Domain d → 𝕜) (hf : Continuous f) {S : Set (Domain d)} :
    ∀ (a : Domain d → 𝕜) (ha : ContDiff ℝ ∞ a), HasCompactSupport a →
      tsupport a ⊆ S →
      HasContinuousPrimitives
        (multiplyDistribution ⟨a, ha.contDiffOn⟩
          (distributionDerivative 𝕜 d Ω w (regularDistribution volume f))) S := by
  induction w using List.reverseRecOn with
  | nil =>
    intro a ha hc hs
    rw [distributionDerivative_nil, multiply_regular a ha f hf]
    exact hasContinuousPrimitives_regular _ (ha.continuous.mul hf)
      hc.mul_right (tsupport_mul_subset_left.trans hs)
  | @append_singleton w i ih =>
    intro a ha hc hs
    rw [distributionDerivative_append, multiply_derivative, sub_eq_add_neg]
    apply hasContinuousPrimitives_add
      (hasContinuousPrimitives_derivative [i] (ih a ha hc hs))
    apply hasContinuousPrimitives_neg
    let da : Domain d → 𝕜 := fun x => fderiv ℝ a x (coordinateVector i)
    have hda : ContDiff ℝ ∞ da :=
      (ha.fderiv_right (by simp)).clm_apply contDiff_const
    have hsda : tsupport da ⊆ tsupport a := tsupport_fderiv_apply_subset ℝ _
    exact ih da hda (hc.of_isClosed_subset isClosed_closure hsda) (hsda.trans hs)

/-- Cut off an arbitrary finite family of continuous primitives. No compact
support is assumed for the input densities or for their derivative terms. -/
theorem cutoff_finite_representation {ι : Type} [Fintype ι]
    (u : ScalarDistribution 𝕜 Ω) (w : ι → List (Fin d))
    (f : ι → Domain d → 𝕜) (hf : ∀ j, Continuous (f j))
    (hu : u = ∑ j, distributionDerivative 𝕜 d Ω (w j) (regularDistribution volume (f j)))
    (a : Domain d → 𝕜) (ha : ContDiff ℝ ∞ a)
    (hc : HasCompactSupport a) {S : Set (Domain d)} (hs : tsupport a ⊆ S) :
    HasContinuousPrimitives (multiplyDistribution ⟨a, ha.contDiffOn⟩ u) S := by
  classical
  have hmul : multiplyDistribution ⟨a, ha.contDiffOn⟩ u =
      ∑ j, multiplyDistribution ⟨a, ha.contDiffOn⟩
        (distributionDerivative 𝕜 d Ω (w j) (regularDistribution volume (f j))) := by
    ext φ
    simp only [multiplyDistribution_apply, hu, sum_apply]
  rw [hmul]
  exact hasContinuousPrimitives_sum Finset.univ _
    (fun j _ => cutoff_derivative_regular (w j) (f j) (hf j) a ha hc hs)

/-- The prescribed-support part of the structure theorem follows from any
unrestricted finite continuous-density representation. This result needs only
that V is open and contains the compact support; relative compactness of V is
unnecessary for this implication. -/
theorem compact_primitives_of_finite_representation {ι : Type} [Fintype ι]
    (V : Opens (Domain d)) (u : ScalarDistribution 𝕜 Ω)
    (hc : IsCompact (distributionSupport u)) (hs : distributionSupport u ⊆ V)
    (w : ι → List (Fin d)) (f : ι → Domain d → 𝕜)
    (hf : ∀ j, Continuous (f j))
    (hu : u = ∑ j, distributionDerivative 𝕜 d Ω (w j) (regularDistribution volume (f j))) :
    HasContinuousPrimitives u V := by
  obtain ⟨χ, W, hW, hSW, hχ⟩ := cutoff_existence d V (distributionSupport u) hc hs
  let a : Tests 𝕜 V := scalarCutoff 𝕜 χ
  have ha : ContDiff ℝ ∞ (a : Domain d → 𝕜) := a.contDiff
  have haW : EqOn (a : Domain d → 𝕜) 1 W := by
    intro x hx
    change (χ x : 𝕜) = 1
    rw [hχ hx]
    simp
  have hfix : multiplyDistribution ⟨a, ha.contDiffOn⟩ u = u := by
    ext φ
    have heq : multiplyTestCLM (Ω := Ω) ⟨a, ha.contDiffOn⟩ φ = multiplyTest a ha φ := by
      ext x
      change a x * φ x = φ x * a x
      exact mul_comm _ _
    change u (multiplyTestCLM ⟨a, ha.contDiffOn⟩ φ) = u φ
    rw [heq]
    exact cutoff_locality 𝕜 d Ω u a ha W hW hSW haW φ
  rw [← hfix]
  exact cutoff_finite_representation u w f hf hu a ha a.hasCompactSupport a.tsupport_subset

/-- Smooth multiplication cannot create distribution support away from the
coefficient's topological support. -/
theorem support_multiply_subset (a : SmoothCoefficient 𝕜 Ω)
    (u : ScalarDistribution 𝕜 Ω) :
    distributionSupport (multiplyDistribution a u) ⊆ tsupport a.val := by
  intro x hx
  by_contra hxa
  apply hx.2
  refine Set.mem_sUnion.mpr ⟨(Ω : Set (Domain d)) ∩ (tsupport a.val)ᶜ,
    ⟨Ω.isOpen.inter isClosed_closure.isOpen_compl, inter_subset_left, ?_⟩, hx.1, hxa⟩
  intro φ hφ
  have hz : multiplyTestCLM a φ = 0 := by
    ext y
    change a.val y * φ y = 0
    by_cases hy : y ∈ tsupport φ
    · rw [image_eq_zero_of_notMem_tsupport (hφ hy).2, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
  change u (multiplyTestCLM a φ) = 0
  rw [hz, map_zero]

/-- A compactly supported smooth multiplier produces an actually compactly
supported distribution, even though distributionSupport is defined relatively
to the open domain. -/
theorem compact_support_multiply (a : Tests 𝕜 Ω) (u : ScalarDistribution 𝕜 Ω) :
    IsCompact (distributionSupport (multiplyDistribution ⟨a, a.contDiff.contDiffOn⟩ u)) := by
  let v := multiplyDistribution ⟨a, a.contDiff.contDiffOn⟩ u
  have hs : distributionSupport v ⊆ tsupport a := support_multiply_subset _ u
  have heq : distributionSupport v = tsupport a \ vanishingRegion v := by
    ext x
    exact ⟨fun hx => ⟨hs hx, hx.2⟩,
      fun hx => ⟨a.tsupport_subset hx.1, hx.2⟩⟩
  rw [heq]
  exact a.hasCompactSupport.diff (support_vanishing 𝕜 d Ω v).1

/-- Changing only the open test domain leaves the signed integral unchanged. -/
theorem primitivePairing_inclusion {U : Opens (Domain d)} (hU : U ≤ Ω)
    (w : List (Fin d)) (f : Domain d → 𝕜) (φ : Tests 𝕜 U) :
    continuousPrimitivePairing w f (TestFunction.monoCLM 𝕜 φ : Tests 𝕜 Ω) =
      continuousPrimitivePairing w f φ := by
  have heq : ((TestFunction.monoCLM 𝕜 φ : Tests 𝕜 Ω) : Domain d → 𝕜) = φ :=
    funext fun x => inclusion_apply hU φ x
  have hD : ⇑(testPartialCLM w (TestFunction.monoCLM 𝕜 φ : Tests 𝕜 Ω)) =
      ⇑(testPartialCLM w φ) := by
    rw [testPartial_formula 𝕜 d Ω, testPartial_formula 𝕜 d U, heq]
  simp only [continuousPrimitivePairing, hD]

/-- Once the compact-support theorem is proved, no further analytic
representation theorem is needed for the local conclusion. -/
theorem local_primitives_of_compact
    (hcompact : Specs.ExpandedFA.Distributions.ContinuousDistributionPrimitives.compactPrimitivesType) :
    Specs.ExpandedFA.Distributions.ContinuousDistributionPrimitives.localPrimitivesType := by
  intro 𝕜 _ d Ω u x hx
  obtain ⟨χ, W, hW, hxW, hχW⟩ := cutoff_existence d Ω {x} (isCompact_singleton)
    (Set.singleton_subset_iff.mpr hx)
  let a : Tests 𝕜 Ω := scalarCutoff 𝕜 χ
  let v := multiplyDistribution ⟨a, a.contDiff.contDiffOn⟩ u
  obtain ⟨V, hV, hSV, hVO, hcV⟩ := exists_open_between_and_isCompact_closure
    a.hasCompactSupport Ω.isOpen a.tsupport_subset
  have hv : HasContinuousPrimitives v V := hcompact 𝕜 d Ω ⟨V, hV⟩ v
    (compact_support_multiply a u)
    ((support_multiply_subset _ u).trans hSV) hcV hVO
  obtain ⟨ι, hι, w, f, hf, hv⟩ := hv
  let := hι
  let U : Opens (Domain d) := ⟨W ∩ Ω, hW.inter Ω.isOpen⟩
  have hU : U ≤ Ω := inter_subset_right
  refine ⟨U, hU, ⟨hxW (by simp), hx⟩, ι, inferInstance, w, f,
    fun j => (hf j).1.continuousOn, ?_⟩
  intro φ
  have hfix : multiplyTestCLM ⟨a, a.contDiff.contDiffOn⟩
      (TestFunction.monoCLM 𝕜 φ : Tests 𝕜 Ω) = TestFunction.monoCLM 𝕜 φ := by
    ext y
    change a y * (TestFunction.monoCLM 𝕜 φ : Tests 𝕜 Ω) y =
      (TestFunction.monoCLM 𝕜 φ : Tests 𝕜 Ω) y
    rw [inclusion_apply hU]
    by_cases hy : y ∈ tsupport φ
    · have hyW : y ∈ W := (φ.tsupport_subset hy).1
      have haW : a y = 1 := by
        change (χ y : 𝕜) = 1
        rw [hχW hyW]
        simp
      rw [haW, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
  have heq : u (TestFunction.monoCLM 𝕜 φ) = v (TestFunction.monoCLM 𝕜 φ) := by
    change u _ = u (multiplyTestCLM _ _)
    rw [hfix]
  rw [heq, hv]
  apply Finset.sum_congr rfl
  intro j _
  exact primitivePairing_inclusion hU (w j) (f j) φ

/-- Refining a locally finite family by finitely many subsets in each member
preserves local finiteness. The number of subsets may vary with the member. -/
theorem locallyFinite_sigma_subsets {X κ : Type*} [TopologicalSpace X]
    {ι : κ → Type*} [∀ j, Finite (ι j)] (V : κ → Set X)
    (hV : LocallyFinite V) (F : (Σ j, ι j) → Set X)
    (hF : ∀ p, F p ⊆ V p.1) : LocallyFinite F := by
  intro x
  obtain ⟨N, hN, hfin⟩ := hV x
  refine ⟨N, hN, (hfin.biUnion (fun j _ => Set.finite_range (Sigma.mk j))).subset ?_⟩
  rintro ⟨j, k⟩ ⟨y, hyF, hyN⟩
  exact Set.mem_biUnion ⟨y, hF ⟨j, k⟩ hyF, hyN⟩ (Set.mem_range_self k)

/-- Assemble finite primitive representations of countably many pieces. The
hypotheses explicitly require a locally finite family of allowed supports;
local finiteness of the distribution pieces alone would not suffice to control
the supports of independently chosen primitives. -/
theorem global_primitives_of_locally_finite_pieces {κ : Type} [Countable κ]
    (u : ScalarDistribution 𝕜 Ω) (v : κ → ScalarDistribution 𝕜 Ω)
    (V : κ → Set (Domain d)) (hVΩ : ∀ j, V j ⊆ Ω)
    (hV : LocallyFinite (fun j => (Subtype.val : Ω → Domain d) ⁻¹' V j))
    (hrep : ∀ j, HasContinuousPrimitives (v j) (V j))
    (hu : ∀ φ : Tests 𝕜 Ω, u φ = ∑ᶠ j, v j φ) :
    ∃ (ι : Type) (_ : Countable ι) (w : ι → List (Fin d)) (f : ι → Domain d → 𝕜),
      (∀ j, Continuous (f j) ∧ HasCompactSupport (f j) ∧ tsupport (f j) ⊆ Ω) ∧
      LocallyFinite (fun j => (Subtype.val : Ω → Domain d) ⁻¹' tsupport (f j)) ∧
      ∀ φ : Tests 𝕜 Ω, u φ = ∑ᶠ j, continuousPrimitivePairing (w j) (f j) φ := by
  classical
  choose ι hι w f hf hv using hrep
  let (j : κ) : Fintype (ι j) := hι j
  let I := Σ j, ι j
  refine ⟨I, inferInstance, fun p => w p.1 p.2, fun p => f p.1 p.2,
    fun p => ⟨(hf p.1 p.2).1, (hf p.1 p.2).2.1,
      (hf p.1 p.2).2.2.trans (hVΩ p.1)⟩, ?_, ?_⟩
  · exact locallyFinite_sigma_subsets _ hV _ (fun p => Set.preimage_mono (hf p.1 p.2).2.2)
  · intro φ
    have hc : IsCompact ((Subtype.val : Ω → Domain d) ⁻¹' tsupport φ) :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' φ.hasCompactSupport
        (fun x hx => ⟨⟨x, φ.tsupport_subset hx⟩, rfl⟩)
    have hfin : {j | (V j ∩ tsupport φ).Nonempty}.Finite :=
      (hV.finite_nonempty_inter_compact hc).subset (by
        rintro j ⟨x, hxV, hxφ⟩
        exact ⟨⟨x, φ.tsupport_subset hxφ⟩, hxV, hxφ⟩)
    let s := hfin.toFinset
    have hz (j : κ) (hj : j ∉ s) (k : ι j) :
        continuousPrimitivePairing (w j k) (f j k) φ = 0 := by
      apply primitivePairing_eq_zero_of_disjoint
      apply Set.disjoint_left.mpr
      intro x hxf hxφ
      exact hj (hfin.mem_toFinset.mpr ⟨x, (hf j k).2.2 hxf, hxφ⟩)
    have hvz (j : κ) (hj : j ∉ s) : v j φ = 0 := by
      rw [hv]
      exact Finset.sum_eq_zero fun k _ => hz j hj k
    have hleft : (∑ᶠ j, v j φ) = ∑ j ∈ s, v j φ := by
      apply finsum_eq_sum_of_support_subset
      intro j hj
      by_contra hjs
      exact hj (hvz j hjs)
    let t : Finset I := s.sigma fun _ => Finset.univ
    have hright : (∑ᶠ p : I, continuousPrimitivePairing (w p.1 p.2) (f p.1 p.2) φ) =
        ∑ p ∈ t, continuousPrimitivePairing (w p.1 p.2) (f p.1 p.2) φ := by
      apply finsum_eq_sum_of_support_subset
      rintro ⟨j, k⟩ hp
      have hjs : j ∈ s := by
        by_contra hn
        exact hp (hz j hn k)
      exact Finset.mem_sigma.mpr ⟨hjs, Finset.mem_univ k⟩
    rw [hu, hleft, hright]
    dsimp only [t]
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro j _
    exact hv j φ

/-- An open Euclidean domain has a countable locally finite open cover whose
ambient closures are compact subsets of that domain. -/
theorem exists_locally_finite_precompact_cover (d : ℕ) (Ω : Opens (Domain d)) :
    ∃ (κ : Type) (_ : Countable κ) (V : κ → Opens (Domain d)),
      (∀ j, IsCompact (closure (V j : Set (Domain d))) ∧
        closure (V j : Set (Domain d)) ⊆ Ω) ∧
      (Ω : Set (Domain d)) ⊆ ⋃ j, (V j : Set (Domain d)) ∧
      LocallyFinite (fun j => (Subtype.val : Ω → Domain d) ⁻¹' V j) := by
  classical
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  have hB (x : Ω) : ∃ B : Set (Domain d), IsOpen B ∧ x.val ∈ B ∧
      closure B ⊆ Ω ∧ IsCompact (closure B) := by
    obtain ⟨B, ho, hxB, hBO, hc⟩ := exists_open_between_and_isCompact_closure
      (isCompact_singleton (x := x.val)) Ω.isOpen (Set.singleton_subset_iff.mpr x.property)
    exact ⟨B, ho, hxB (by simp), hBO, hc⟩
  choose B hBo hxB hBO hBc using hB
  obtain ⟨R, hRo, hRc, hRf, hRB⟩ := precise_refinement
    (fun x : Ω => (Subtype.val : Ω → Domain d) ⁻¹' B x)
    (fun x => (hBo x).preimage continuous_subtype_val) (by
      rw [Set.iUnion_eq_univ_iff]
      intro x
      exact ⟨x, hxB x⟩)
  let κ := {x : Ω // (R x).Nonempty}
  have hRκ : LocallyFinite (fun j : κ => R j.val) :=
    hRf.comp_injective Subtype.val_injective
  let : Encodable κ := hRκ.encodable (fun j => j.property)
  let V : κ → Opens (Domain d) := fun j =>
    ⟨Subtype.val '' R j.val, Ω.isOpen.isOpenMap_subtype_val _ (hRo j.val)⟩
  have hVB (j : κ) : (V j : Set (Domain d)) ⊆ B j.val := by
    rintro x ⟨y, hy, rfl⟩
    exact hRB j.val hy
  refine ⟨κ, inferInstance, V, ?_, ?_, ?_⟩
  · intro j
    exact ⟨(hBc j.val).of_isClosed_subset isClosed_closure (closure_mono (hVB j)),
      (closure_mono (hVB j)).trans (hBO j.val)⟩
  · intro x hx
    obtain ⟨j, hj⟩ := Set.iUnion_eq_univ_iff.mp hRc (⟨x, hx⟩ : Ω)
    exact Set.mem_iUnion.mpr ⟨⟨j, ⟨⟨x, hx⟩, hj⟩⟩, ⟨⟨x, hx⟩, hj, rfl⟩⟩
  · convert hRκ using 1
    funext j
    exact Set.preimage_image_eq _ Subtype.val_injective

/-- Choose the partition and the enlarged patches together. This controls the
supports of the primitives chosen later, including near the boundary of Ω. -/
theorem exists_partition_precompact_patches (d : ℕ) (Ω : Opens (Domain d)) :
    ∃ (κ : Type) (_ : Countable κ) (V : κ → Opens (Domain d)) (η : κ → Tests ℝ Ω),
      (∀ j, IsCompact (closure (V j : Set (Domain d))) ∧
        closure (V j : Set (Domain d)) ⊆ Ω) ∧
      LocallyFinite (fun j => (Subtype.val : Ω → Domain d) ⁻¹' V j) ∧
      (∀ j, tsupport (η j) ⊆ V j) ∧
      ∀ x ∈ Ω, ∑ᶠ j, η j x = 1 := by
  classical
  let : LocallyCompactSpace Ω := Ω.isOpen.locallyCompactSpace
  obtain ⟨κ, hκ, V, hVc, hcover, hVf⟩ := exists_locally_finite_precompact_cover d Ω
  let := hκ
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ, Domain d))
    (M := Ω) isClosed_univ
    (fun j => (Subtype.val : Ω → Domain d) ⁻¹' V j)
    (fun j => (V j).isOpen.preimage continuous_subtype_val) (by
      intro x _
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hcover x.property)
      exact Set.mem_iUnion.mpr ⟨j, hj⟩)
  have hc (j : κ) : HasCompactSupport (ρ j) := by
    have hcl : IsCompact ((Subtype.val : Ω → Domain d) ⁻¹' closure (V j : Set (Domain d))) :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' (hVc j).1
        (fun x hx => ⟨⟨x, (hVc j).2 hx⟩, rfl⟩)
    exact hcl.of_isClosed_subset isClosed_closure
      ((hρ j).trans (Set.preimage_mono subset_closure))
  let η : κ → Tests ℝ Ω := fun j => extendSmoothTest Ω (ρ j) (hc j)
  refine ⟨κ, inferInstance, V, η, hVc, hVf, ?_, ?_⟩
  · intro j x hx
    obtain ⟨y, hy, rfl⟩ := extendSmoothTest_tsupport_subset Ω (ρ j) (hc j) hx
    exact hρ j hy
  · intro x hx
    calc
      (∑ᶠ j, η j x) = ∑ᶠ j, ρ j (⟨x, hx⟩ : Ω) := by
        congr 1
        funext j
        exact extendSmoothTest_apply Ω (ρ j) (hc j) ⟨x, hx⟩
      _ = 1 := ρ.sum_eq_one (Set.mem_univ _)

/-- The compact-support theorem also suffices for the entire global locally
finite conclusion. No uniform derivative order on Ω is introduced. -/
theorem global_primitives_of_compact
    (hcompact : Specs.ExpandedFA.Distributions.ContinuousDistributionPrimitives.compactPrimitivesType) :
    Specs.ExpandedFA.Distributions.ContinuousDistributionPrimitives.globalPrimitivesType := by
  classical
  intro 𝕜 _ d Ω u
  obtain ⟨κ, hκ, V, η, hVc, hVf, hηV, hηsum⟩ := exists_partition_precompact_patches d Ω
  let := hκ
  let a (j : κ) : Tests 𝕜 Ω := scalarCutoff 𝕜 (η j)
  let v (j : κ) : ScalarDistribution 𝕜 Ω :=
    multiplyDistribution ⟨a j, (a j).contDiff.contDiffOn⟩ u
  have haV (j : κ) : tsupport (a j) ⊆ V j := by
    apply (tsupport_comp_subset (g := fun t : ℝ => (t : 𝕜)) (by simp) (η j)).trans
    exact hηV j
  have hrep (j : κ) : HasContinuousPrimitives (v j) (V j) :=
    hcompact 𝕜 d Ω (V j) (v j) (compact_support_multiply (a j) u)
      ((support_multiply_subset _ u).trans (haV j)) (hVc j).1 (hVc j).2
  apply global_primitives_of_locally_finite_pieces u v (fun j => (V j : Set (Domain d)))
    (fun j => subset_closure.trans (hVc j).2) hVf hrep
  have hηf : LocallyFinite (fun j => (Subtype.val : Ω → Domain d) ⁻¹' tsupport (η j)) :=
    hVf.subset fun j => Set.preimage_mono (hηV j)
  intro φ
  obtain ⟨s, hs0, hs⟩ := partition_reconstruct η hηf hηsum le_rfl φ
  have hm (j : κ) : multiplyTestCLM ⟨a j, (a j).contDiff.contDiffOn⟩ φ =
      realMultiplyTest (η j) (η j).contDiff φ := by
    ext x
    simp only [multiplyTestCLM_apply, realMultiplyTest_apply, a, scalarCutoff]
    exact (RCLike.real_smul_eq_coe_mul _ _).symm
  have hfin : (∑ᶠ j, v j φ) = ∑ j ∈ s, v j φ := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    by_contra hjs
    apply hj
    change u (multiplyTestCLM _ φ) = 0
    rw [hm, hs0 j hjs, map_zero]
  rw [hfin]
  calc
    u φ = u (∑ j ∈ s, realMultiplyTest (η j) (η j).contDiff φ) := congrArg u hs
    _ = ∑ j ∈ s, u (realMultiplyTest (η j) (η j).contDiff φ) := map_sum u _ _
    _ = ∑ j ∈ s, v j φ := by
      apply Finset.sum_congr rfl
      intro j _
      change u _ = u (multiplyTestCLM _ φ)
      rw [hm]

/-! ## Finite coordinate-jet factorization

The range of a jet restriction need not be closed or injective. Factoring
through its algebraic range first avoids either extra assumption. -/

/-- A scalar functional controlled by a linear map into a normed space factors
through a bounded functional on the whole space, by Hahn--Banach. -/
theorem exists_bounded_factor
    {E F : Type*} [AddCommGroup E] [Module 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (J : E →ₗ[𝕜] F) (L : E →ₗ[𝕜] 𝕜) (C : ℝ)
    (hC : ∀ x, ‖L x‖ ≤ C * ‖J x‖) :
    ∃ A : F →L[𝕜] 𝕜, ∀ x, A (J x) = L x := by
  have hk : LinearMap.ker J.rangeRestrict ≤ LinearMap.ker L := by
    intro x hx
    have hxJ : J x = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    exact LinearMap.mem_ker.mpr (norm_le_zero_iff.mp (by simpa [hxJ] using hC x))
  let l : J.range →ₗ[𝕜] 𝕜 :=
    J.rangeRestrict.liftOfSurjective J.surjective_rangeRestrict ⟨L, hk⟩
  have hl (x : E) : l (J.rangeRestrict x) = L x := by
    exact LinearMap.equivOfSurjective_apply J.surjective_rangeRestrict hk
  have hb (y : J.range) : ‖l y‖ ≤ C * ‖y‖ := by
    obtain ⟨x, rfl⟩ := J.surjective_rangeRestrict y
    change ‖l (J.rangeRestrict x)‖ ≤ C * ‖J x‖
    rw [hl]
    exact hC x
  let l' : J.range →L[𝕜] 𝕜 := l.mkContinuous C hb
  obtain ⟨A, hA, _⟩ := exists_extension_norm_eq J.range l'
  exact ⟨A, fun x => (hA (J.rangeRestrict x)).trans (hl x)⟩

/-- A compact-local coordinate jet, retaining the actual scalar function. -/
noncomputable def smoothCoordinateJetLM (a : SmoothCoordinateIndex Ω) :
    SmoothFunctions 𝕜 Ω →ₗ[𝕜] C(a.1.1.val, 𝕜) :=
  ((coordinateEvaluation 𝕜 a.2).compLeftContinuous 𝕜 a.1.1.val).toLinearMap.comp
    (smoothJetLM 𝕜 Ω a.1)

/-- A continuous smooth functional is a finite sum of bounded functionals on
compactly restricted coordinate derivatives. No injectivity or closed-range
assumption on the jet map is made. In particular, this includes zero-dimensional
and empty compact sets. -/
theorem smooth_functional_finite_coordinates
    (L : SmoothFunctions 𝕜 Ω →L[𝕜] 𝕜) :
    ∃ (s : Finset (SmoothCoordinateIndex Ω))
      (A : (a : s) → C(a.val.1.1.val, 𝕜) →L[𝕜] 𝕜),
      ∀ f, L f = ∑ a : s, A a (smoothCoordinateJetLM a.val f) := by
  classical
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous
    (smooth_coordinate_topology 𝕜 d Ω)
    ((normSeminorm 𝕜 𝕜).comp L.toLinearMap) L.continuous.norm
  let J : SmoothFunctions 𝕜 Ω →ₗ[𝕜] ((a : s) → C(a.val.1.1.val, 𝕜)) :=
    LinearMap.pi fun a => smoothCoordinateJetLM a.val
  have hJ (f : SmoothFunctions 𝕜 Ω) :
      (s.sup (smoothCoordinateSeminorm 𝕜 Ω)) f ≤ ‖J f‖ := by
    apply Seminorm.finset_sup_apply_le (norm_nonneg _)
    intro a ha
    exact norm_le_pi_norm (J f) ⟨a, ha⟩
  obtain ⟨B, hB⟩ := exists_bounded_factor J L.toLinearMap (C : ℝ) (fun f =>
    (hC f).trans (mul_le_mul_of_nonneg_left (hJ f) C.coe_nonneg))
  let A (a : s) : C(a.val.1.1.val, 𝕜) →L[𝕜] 𝕜 :=
    B.comp (ContinuousLinearMap.single 𝕜 (fun a : s => C(a.val.1.1.val, 𝕜)) a)
  refine ⟨s, A, fun f => ?_⟩
  have hBf : B (J f) = L f := hB f
  rw [← hBf]
  have hj : J f = ∑ a : s, Pi.single a (J f a) := by
    ext a
    simp
  conv_lhs => rw [hj, map_sum]
  rfl

/-- The compactly supported distribution case of finite jet factorization,
with the actual derivatives of its tests as the coordinates. -/
theorem compact_distribution_finite_coordinates
    (u : ScalarDistribution 𝕜 Ω) (hu : IsCompact (distributionSupport u)) :
    ∃ (s : Finset (SmoothCoordinateIndex Ω))
      (A : (a : s) → C(a.val.1.1.val, 𝕜) →L[𝕜] 𝕜),
      ∀ φ : Tests 𝕜 Ω, u φ =
        ∑ a : s, A a (smoothCoordinateJetLM a.val (testToSmoothLM 𝕜 Ω φ)) := by
  obtain ⟨L, hL, _⟩ := compact_dual_extension 𝕜 d Ω u hu
  obtain ⟨s, A, hA⟩ := smooth_functional_finite_coordinates L
  exact ⟨s, A, fun φ => (hL φ).symm.trans (hA _)⟩

/-- The coordinates in the factorization really are the ordered partials used
by the distribution calculus, with no inserted conjugation or sign. -/
theorem smoothCoordinateJetLM_test_apply (a : SmoothCoordinateIndex Ω)
    (φ : Tests 𝕜 Ω) (x : a.1.1.val) :
    smoothCoordinateJetLM a (testToSmoothLM 𝕜 Ω φ) x =
      testPartialCLM (List.ofFn a.2) φ x := by
  change iteratedFDeriv ℝ a.1.2 φ x (fun j => coordinateVector (a.2 j)) = _
  rw [testPartial_formula]
  exact (partialFunction_ofFn a.1.2 a.2 φ φ.contDiff x).symm

/-! ## A continuous fundamental kernel

The product of one-dimensional ramps recovers a test after two integrations
by parts in every coordinate. Applying a bounded functional on C(K) to the
continuous kernel sections constructs its continuous primitive directly;
Bochner integration commutes with that functional. -/

open Set TopologicalSpace MeasureTheory Topology

namespace ContinuousKernel

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]

/-- The kernel section as a continuous function of its parameter. -/
noncomputable def kernelMap (g : (Fin d → ℝ) × Y → 𝕜) (hg : Continuous g)
    (x : Fin d → ℝ) : C(Y, 𝕜) :=
  ⟨fun y => g (x, y), hg.comp (continuous_const.prodMk continuous_id)⟩

omit [CompactSpace Y] in
theorem continuous_kernelMap (g : (Fin d → ℝ) × Y → 𝕜) (hg : Continuous g) :
    Continuous (kernelMap g hg) := by
  exact ContinuousMap.continuous_of_continuous_uncurry _ hg

noncomputable def functionalPrimitive (g : (Fin d → ℝ) × Y → 𝕜) (hg : Continuous g)
    (A : C(Y, 𝕜) →L[𝕜] 𝕜) (x : Fin d → ℝ) := A (kernelMap g hg x)

omit [CompactSpace Y] in
theorem continuous_functionalPrimitive (g : (Fin d → ℝ) × Y → 𝕜) (hg : Continuous g)
    (A : C(Y, 𝕜) →L[𝕜] 𝕜) : Continuous (functionalPrimitive g hg A) :=
  A.continuous.comp (continuous_kernelMap g hg)

theorem integrable_weighted_kernelMap (g : (Fin d → ℝ) × Y → 𝕜) (hg : Continuous g)
    (ψ : (Fin d → ℝ) → 𝕜) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
    Integrable (fun x => ψ x • kernelMap g hg x) := by
  exact (hψ.smul (continuous_kernelMap g hg)).integrable_of_hasCompactSupport hcψ.smul_right

/-- A bounded scalar functional commutes with the compactly supported kernel integral. -/
theorem functionalPrimitive_pairing
    (g : (Fin d → ℝ) × Y → 𝕜) (hg : Continuous g)
    (A : C(Y, 𝕜) →L[𝕜] 𝕜)
    (ψ : (Fin d → ℝ) → 𝕜) (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ)
    (φ : C(Y, 𝕜)) (hidentity : ∀ y, ∫ x, g (x, y) * ψ x = φ y) :
    (∫ x, functionalPrimitive g hg A x * ψ x) = A φ := by
  have hi := integrable_weighted_kernelMap g hg ψ hψ hcψ
  have hf : (∫ x, ψ x • kernelMap g hg x) = φ := by
    ext y
    rw [ContinuousMap.integral_apply hi]
    simpa only [kernelMap, ContinuousMap.coe_mk, ContinuousMap.smul_apply,
      smul_eq_mul, mul_comm] using hidentity y
  calc
    (∫ x, functionalPrimitive g hg A x * ψ x) =
        ∫ x, A (ψ x • kernelMap g hg x) := by
      congr 1
      ext x
      simp [functionalPrimitive, mul_comm]
    _ = A (∫ x, ψ x • kernelMap g hg x) := A.integral_comp_comm hi
    _ = A φ := congrArg A hf

/-- The product of one-dimensional ramps, with values in the scalar field. -/
noncomputable def positiveKernel (x y : Fin d → ℝ) : 𝕜 :=
  ∏ i, (max (x i - y i) 0 : ℝ)

theorem continuous_positiveKernel :
    Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) => (positiveKernel p.1 p.2 : 𝕜)) := by
  unfold positiveKernel
  fun_prop

theorem continuous_compactKernel (K : Set (Fin d → ℝ)) :
    Continuous (fun p : (Fin d → ℝ) × K => (positiveKernel p.1 p.2 : 𝕜)) := by
  exact continuous_positiveKernel.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- Fubini with the first coordinate integrated before the remaining coordinates. -/
theorem integral_fin_cons (h : (Fin (d + 1) → ℝ) → 𝕜) (hh : Integrable h) :
    (∫ x, h x) = ∫ z : Fin d → ℝ, ∫ t : ℝ, h (Fin.cons t z) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm
  have he : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm
  have hhe : Integrable (h ∘ e) :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr hh
  calc
    (∫ x, h x) = ∫ p : ℝ × (Fin d → ℝ), h (e p) := (he.integral_comp' _).symm
    _ = ∫ z : Fin d → ℝ, ∫ t : ℝ, h (Fin.cons t z) := by
      simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.insertNth_zero, Measure.volume_eq_prod, Function.comp_def, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, cast_eq] using integral_prod_symm (h ∘ e) hhe

noncomputable def testRestriction {Ω : Opens (Domain d)}
    (K : Compacts (Domain d)) (φ : Tests 𝕜 Ω) : C(K, 𝕜) :=
  ⟨fun y => φ y, φ.continuous.comp continuous_subtype_val⟩

noncomputable def compactKernelPrimitive (K : Compacts (Domain d))
    (A : C(K, 𝕜) →L[𝕜] 𝕜) : Domain d → 𝕜 :=
  functionalPrimitive (fun p : Domain d × K => positiveKernel p.1 p.2)
    (continuous_compactKernel (𝕜 := 𝕜) (d := d) (K : Set (Domain d))) A

theorem continuous_compactKernelPrimitive (K : Compacts (Domain d))
    (A : C(K, 𝕜) →L[𝕜] 𝕜) : Continuous (compactKernelPrimitive K A) :=
  continuous_functionalPrimitive _ _ A

theorem compactKernelPrimitive_pairing {Ω : Opens (Domain d)}
    (K : Compacts (Domain d)) (A : C(K, 𝕜) →L[𝕜] 𝕜)
    (k : List (Fin d)) (heven : (-1 : 𝕜) ^ k.length = 1) (φ : Tests 𝕜 Ω)
    (hidentity : ∀ y : K,
      ∫ x, (positiveKernel x y : 𝕜) * testPartialCLM k φ x = φ y) :
    A (testRestriction K φ) =
      distributionDerivative 𝕜 d Ω k (regularDistribution volume (compactKernelPrimitive K A)) φ := by
  have hf := continuous_compactKernelPrimitive K A
  rw [distributionDerivative_apply,
    regularDistribution_apply volume _ (hf.locallyIntegrable.locallyIntegrableOn Ω),
    heven, one_mul]
  exact (functionalPrimitive_pairing
    (fun p : Domain d × K => positiveKernel p.1 p.2) (continuous_compactKernel (𝕜 := 𝕜) (d := d) (K : Set (Domain d))) A
    (testPartialCLM k φ) (testPartialCLM k φ).continuous
    (testPartialCLM k φ).hasCompactSupport (testRestriction K φ) hidentity).symm

end ContinuousKernel

open Set TopologicalSpace MeasureTheory
namespace CoordinateSlices
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

noncomputable def tailEmbedding (d : ℕ) : Domain d →L[ℝ] Domain (d+1) :=
  (0 : Domain d →L[ℝ] ℝ).finCons (ContinuousLinearMap.id ℝ _)

theorem contDiff_cons_tail (t : ℝ) : ContDiff ℝ ∞ (fun z : Domain d => (Fin.cons t z : Domain (d+1))) := by
  have h : (fun z : Domain d => Fin.cons t z) =
      fun z => Fin.cons t (0 : Domain d) + tailEmbedding d z := by
    funext z
    ext j
    exact Fin.cases (by simp [tailEmbedding]) (fun j => by simp [tailEmbedding]) j
  rw [h]
  exact contDiff_const.add (tailEmbedding d).contDiff

theorem contDiff_partialFunction (w : List (Fin d)) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (partialFunction w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem tailEmbedding_coordinate (i : Fin d) :
    tailEmbedding d (coordinateVector i) = coordinateVector i.succ := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [tailEmbedding, coordinateVector]
  · simp [tailEmbedding, coordinateVector, Pi.single_apply, Fin.succ_inj]

theorem partialFunction_cons_tail (w : List (Fin d)) (f : Domain (d+1) → 𝕜)
    (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    partialFunction (w.map Fin.succ) f ∘ (fun z : Domain d => Fin.cons t z) =
      partialFunction w (fun z : Domain d => f (Fin.cons t z)) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext z
    change fderiv ℝ (partialFunction (w.map Fin.succ) f) (Fin.cons t z)
      (coordinateVector i.succ) =
      fderiv ℝ (partialFunction w (fun z : Domain d => f (Fin.cons t z))) z
      (coordinateVector i)
    rw [← ih]
    have hcons : HasFDerivAt (fun z : Domain d => Fin.cons t z) (tailEmbedding d) z :=
      (hasFDerivAt_const t z).finCons (hasFDerivAt_id z)
    rw [((contDiff_partialFunction (w.map Fin.succ) f hf).differentiable (by simp)
      (Fin.cons t z)).hasFDerivAt.comp z hcons |>.fderiv]
    simp [tailEmbedding_coordinate]

theorem hasCompactSupport_cons_tail (f : Domain (d+1) → 𝕜)
    (hf : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (fun z : Domain d => f (Fin.cons t z)) := by
  have hc : Continuous (fun x : Domain (d+1) => Fin.tail x) :=
    continuous_pi fun i => continuous_apply i.succ
  apply (hf.image hc).of_isClosed_subset isClosed_closure
  intro z hz
  have hz' := tsupport_comp_subset_preimage f (contDiff_cons_tail t).continuous hz
  exact ⟨Fin.cons t z, hz', by simp⟩

theorem contDiff_cons_head (z : Domain d) :
    ContDiff ℝ ∞ (fun t : ℝ => (Fin.cons t z : Domain (d+1))) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change ContDiff ℝ ∞ (fun t : ℝ => t)
    exact contDiff_id
  · change ContDiff ℝ ∞ (fun _ : ℝ => z j)
    exact contDiff_const

theorem hasCompactSupport_cons_head (f : Domain (d+1) → 𝕜)
    (hf : HasCompactSupport f) (z : Domain d) :
    HasCompactSupport (fun t : ℝ => f (Fin.cons t z)) := by
  apply (hf.image (continuous_apply 0)).of_isClosed_subset isClosed_closure
  intro t ht
  have ht' := tsupport_comp_subset_preimage f (contDiff_cons_head z).continuous ht
  exact ⟨Fin.cons t z, ht', by simp⟩

theorem coordinateVector_zero : coordinateVector (0 : Fin (d+1)) =
    Fin.cons 1 (0 : Domain d) := by
  ext j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp [coordinateVector]
  · simp [coordinateVector]

theorem deriv_cons_head (f : Domain (d+1) → 𝕜) (hf : ContDiff ℝ ∞ f)
    (z : Domain d) (t : ℝ) :
    deriv (fun t : ℝ => f (Fin.cons t z)) t =
      partialFunction [0] f (Fin.cons t z) := by
  have hcons : HasDerivAt (fun t : ℝ => (Fin.cons t z : Domain (d+1)))
      (Fin.cons 1 (0 : Domain d)) t :=
    (hasDerivAt_id t).finCons (hasDerivAt_const t z)
  change _ = fderiv ℝ f (Fin.cons t z) (coordinateVector 0)
  rw [coordinateVector_zero]
  exact ((hf.differentiable (by simp) (Fin.cons t z)).hasFDerivAt.comp_hasDerivAt t hcons).deriv

theorem deriv_deriv_cons_head (f : Domain (d+1) → 𝕜) (hf : ContDiff ℝ ∞ f)
    (z : Domain d) (t : ℝ) :
    deriv (deriv (fun t : ℝ => f (Fin.cons t z))) t =
      partialFunction [0,0] f (Fin.cons t z) := by
  have heq : deriv (fun t : ℝ => f (Fin.cons t z)) =
      fun t => partialFunction [0] f (Fin.cons t z) :=
    funext fun t => deriv_cons_head f hf z t
  rw [heq]
  exact deriv_cons_head _ (contDiff_partialFunction [0] f hf) z t

theorem tsupport_partialFunction_subset (w : List (Fin d)) (f : Domain d → 𝕜) :
    tsupport (partialFunction w f) ⊆ tsupport f := by
  induction w with
  | nil => exact Subset.rfl
  | cons i w ih => exact (tsupport_fderiv_apply_subset ℝ _).trans ih

theorem hasCompactSupport_partialFunction (w : List (Fin d)) (f : Domain d → 𝕜)
    (hf : HasCompactSupport f) : HasCompactSupport (partialFunction w f) :=
  hf.of_isClosed_subset isClosed_closure (tsupport_partialFunction_subset w f)

end CoordinateSlices

namespace RampKernel
open MeasureTheory Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Two integrations by parts recover evaluation from the ramp kernel. -/
lemma ramp_identity (f : ℝ → E) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (y : ℝ) :
    ∫ x : ℝ, (max (x-y) 0) • deriv (deriv f) x = f y := by
  let g : ℝ → E := fun x => (x-y) • deriv f x
  have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hg : ContDiff ℝ ∞ g := (contDiff_id.sub contDiff_const).smul hdf
  have hcg : HasCompactSupport g := hc.deriv.smul_left
  have hderivg : deriv g = fun x => deriv f x + (x-y) • deriv (deriv f) x := by
    funext x
    have hh := ((hasDerivAt_id x).sub_const y |>.smul
      (hdf.differentiable (by simp) x).hasDerivAt).deriv
    convert hh using 1
    · congr 1
    · simp [add_comm]
  have hi1 := HasCompactSupport.integral_Ioi_deriv_eq (hg.of_le (by simp)) hcg y
  have hi2 := HasCompactSupport.integral_Ioi_deriv_eq (hf.of_le (by simp)) hc y
  have hid : Integrable (deriv f) := hdf.continuous.integrable_of_hasCompactSupport hc.deriv
  have hidd : Integrable (fun x => (x-y) • deriv (deriv f) x) :=
    ((continuous_id.sub continuous_const).smul
      ((contDiff_infty_iff_deriv.mp hdf).2).continuous).integrable_of_hasCompactSupport hc.deriv.deriv.smul_left
  rw [hderivg, integral_add hid.integrableOn hidd.integrableOn] at hi1
  have hir : ∫ x in Ioi y, (x-y) • deriv (deriv f) x = f y := by
    simp only [g, sub_self, zero_smul, neg_zero] at hi1
    rw [hi2] at hi1
    exact (neg_add_eq_zero.mp hi1).symm
  rw [← hir]
  calc
    (∫ x : ℝ, max (x-y) 0 • deriv (deriv f) x) =
      ∫ x in Ioi y, max (x-y) 0 • deriv (deriv f) x := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        simp only [mem_Ioi, not_lt] at hx
        rw [max_eq_right (sub_nonpos.mpr hx), zero_smul]
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [max_eq_left (sub_nonneg.mpr (le_of_lt hx))]

variable {𝕜 : Type} [RCLike 𝕜]

lemma ramp_identity_scalar_mul (f : ℝ → 𝕜) (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (y : ℝ) :
    ∫ x : ℝ, ((max (x-y) 0 : ℝ) : 𝕜) * deriv (deriv f) x = f y := by
  simpa only [RCLike.real_smul_eq_coe_mul] using ramp_identity f hf hc y

end RampKernel

namespace ContinuousKernel
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}

/-- Each coordinate is differentiated twice, in recursive coordinate order. -/
def twiceCoordinateWord : (d : ℕ) → List (Fin d)
  | 0 => []
  | n + 1 => 0 :: 0 :: (twiceCoordinateWord n).map Fin.succ

lemma positiveKernel_cons (t : ℝ) (z : Fin d → ℝ) (y : Fin (d+1) → ℝ) :
    positiveKernel (𝕜 := 𝕜) (Fin.cons t z) y =
      ((max (t-y 0) 0 : ℝ) : 𝕜) * positiveKernel z (Fin.tail y) := by
  simp only [positiveKernel, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.tail_def]

lemma positiveKernel_zero (x y : Fin 0 → ℝ) : positiveKernel (𝕜 := 𝕜) x y = 1 := by
  simp [positiveKernel]

lemma volume_univ_zero : volume (univ : Set (Fin 0 → ℝ)) = 1 := by
  simp [volume_pi]

lemma integral_zero_dim (f : (Fin 0 → ℝ) → 𝕜) (y : Fin 0 → ℝ) :
    ∫ x, f x = f y := by
  rw [integral_unique, Measure.real, volume_univ_zero]
  simp only [ENNReal.toReal_one, one_smul]
  congr 1
  exact Subsingleton.elim _ _

lemma zero_dim_identity (f : (Fin 0 → ℝ) → 𝕜) (y : Fin 0 → ℝ) :
    ∫ x, positiveKernel x y * f x = f y := by
  simpa only [positiveKernel_zero, one_mul] using integral_zero_dim f y

lemma twiceCoordinateWord_length (d : ℕ) : (twiceCoordinateWord d).length = 2*d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [twiceCoordinateWord, List.length_cons, List.length_map, ih]; omega

lemma twiceCoordinateWord_sign (d : ℕ) : (-1 : 𝕜) ^ (twiceCoordinateWord d).length = 1 := by
  rw [twiceCoordinateWord_length, pow_mul]
  simp

end ContinuousKernel

open Set TopologicalSpace MeasureTheory
namespace ContinuousKernel
open CoordinateSlices
variable {𝕜 : Type} [RCLike 𝕜]

/-- The ramp product is a fundamental kernel for two derivatives in each coordinate. -/
theorem positiveKernel_identity (d : ℕ) (f : Domain d → 𝕜)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (y : Domain d) :
    ∫ x, (positiveKernel x y : 𝕜) * partialFunction (twiceCoordinateWord d) f x = f y := by
  induction d with
  | zero => simpa only [twiceCoordinateWord, partialFunction] using zero_dim_identity f y
  | succ d ih =>
    let w : List (Fin (d+1)) := (twiceCoordinateWord d).map Fin.succ
    let q := partialFunction w f
    have hq : ContDiff ℝ ∞ q := contDiff_partialFunction w f hf
    have hcq : HasCompactSupport q := hasCompactSupport_partialFunction w f hc
    have hi : Integrable (fun x => (positiveKernel x y : 𝕜) * partialFunction (twiceCoordinateWord (d+1)) f x) :=
      ((continuous_positiveKernel.comp (continuous_id.prodMk continuous_const)).mul
        (contDiff_partialFunction _ f hf).continuous).integrable_of_hasCompactSupport
          (hasCompactSupport_partialFunction _ f hc).mul_left
    rw [integral_fin_cons _ hi]
    calc
      (∫ z : Domain d, ∫ t : ℝ, (positiveKernel (Fin.cons t z) y : 𝕜) *
          partialFunction (twiceCoordinateWord (d+1)) f (Fin.cons t z)) =
        ∫ z : Domain d, (positiveKernel z (Fin.tail y) : 𝕜) * q (Fin.cons (y 0) z) := by
          apply integral_congr_ae
          filter_upwards [] with z
          have hd : ∀ t : ℝ,
              partialFunction (twiceCoordinateWord (d+1)) f (Fin.cons t z) =
                deriv (deriv (fun t : ℝ => q (Fin.cons t z))) t := by
            intro t
            exact (deriv_deriv_cons_head q hq z t).symm
          calc
            (∫ t : ℝ, (positiveKernel (Fin.cons t z) y : 𝕜) *
                partialFunction (twiceCoordinateWord (d+1)) f (Fin.cons t z)) =
              ∫ t : ℝ, (positiveKernel z (Fin.tail y) : 𝕜) *
                (((max (t-y 0) 0 : ℝ) : 𝕜) *
                  deriv (deriv (fun t : ℝ => q (Fin.cons t z))) t) := by
                    apply integral_congr_ae
                    filter_upwards [] with t
                    rw [positiveKernel_cons, hd t]
                    ring
            _ = _ := by
              rw [integral_const_mul]
              congr 1
              exact RampKernel.ramp_identity_scalar_mul (fun t => q (Fin.cons t z))
                (hq.comp (contDiff_cons_head z)) (hasCompactSupport_cons_head q hcq z) (y 0)
      _ = f y := by
        have heq := partialFunction_cons_tail (twiceCoordinateWord d) f hf (y 0)
        simp_rw [show ∀ z : Domain d, q (Fin.cons (y 0) z) =
          partialFunction (twiceCoordinateWord d) (fun z => f (Fin.cons (y 0) z)) z from
          fun z => congrFun heq z]
        simpa only [Function.comp_def, Fin.cons_self_tail] using
          ih _ (hf.comp (contDiff_cons_tail (y 0)))
            (hasCompactSupport_cons_tail f hc (y 0)) (Fin.tail y)

end ContinuousKernel

lemma derivative_regular_sign (k w : List (Fin d)) (f : Domain d → 𝕜)
    (hf : Continuous f) (φ : Tests 𝕜 Ω) :
    distributionDerivative 𝕜 d Ω (k ++ w)
      (regularDistribution volume (fun x => (-1 : 𝕜)^w.length * f x)) φ =
      distributionDerivative 𝕜 d Ω k (regularDistribution volume f)
        (testPartialCLM w φ) := by
  rw [distributionDerivative_append]
  simp only [distributionDerivative_apply]
  rw [regularDistribution_apply volume (fun x => (-1 : 𝕜)^w.length * f x)
    ((continuous_const.mul hf).locallyIntegrable.locallyIntegrableOn Ω),
    regularDistribution_apply volume f (hf.locallyIntegrable.locallyIntegrableOn Ω)]
  rw [show (fun x => (-1 : 𝕜)^w.length * f x *
      testPartialCLM k (testPartialCLM w φ) x) =
      fun x => (-1 : 𝕜)^w.length * (f x * testPartialCLM k (testPartialCLM w φ) x) by
    funext x; ring, integral_const_mul]
  have hs : (-1 : 𝕜)^w.length * (-1 : 𝕜)^w.length = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  calc
    _ = ((-1 : 𝕜)^w.length * (-1 : 𝕜)^w.length) *
        ((-1 : 𝕜)^k.length * ∫ x, f x * testPartialCLM k (testPartialCLM w φ) x) := by ring
    _ = _ := by rw [hs, one_mul]

lemma compact_finite_continuous_representation_of_functional_primitives
    (k : List (Fin d))
    (hhelper : ∀ (K : Compacts (Domain d)) (A : C(K, 𝕜) →L[𝕜] 𝕜),
      ∃ f : Domain d → 𝕜, Continuous f ∧ ∀ φ : Tests 𝕜 Ω,
        A ⟨fun y => φ y, φ.continuous.comp continuous_subtype_val⟩ =
          distributionDerivative 𝕜 d Ω k (regularDistribution volume f) φ)
    (u : ScalarDistribution 𝕜 Ω) (hu : IsCompact (distributionSupport u)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → List (Fin d)) (f : ι → Domain d → 𝕜),
      (∀ j, Continuous (f j)) ∧
      u = ∑ j, distributionDerivative 𝕜 d Ω (w j) (regularDistribution volume (f j)) := by
  classical
  obtain ⟨s, A, hA⟩ := compact_distribution_finite_coordinates u hu
  choose f hf hrep using fun a : s => hhelper a.val.1.1.val (A a)
  refine ⟨s, inferInstance, fun a => k ++ List.ofFn a.val.2,
    fun a x => (-1 : 𝕜) ^ (List.ofFn a.val.2).length * f a x,
    fun a => continuous_const.mul (hf a), ?_⟩
  ext φ
  rw [hA]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [derivative_regular_sign k (List.ofFn a.val.2) (f a) (hf a)]
  rw [← hrep a (testPartialCLM (List.ofFn a.val.2) φ)]
  congr 1
  ext y
  exact smoothCoordinateJetLM_test_apply a.val φ y

/-- Compactly supported distributions admit a finite representation by actual
continuous densities. The finite coordinate functionals act directly on ramp
kernel sections, so the construction works uniformly over both scalar fields. -/
theorem compact_finite_continuous_representation
    (u : ScalarDistribution 𝕜 Ω) (hu : IsCompact (distributionSupport u)) :
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → List (Fin d)) (f : ι → Domain d → 𝕜),
      (∀ j, Continuous (f j)) ∧
      u = ∑ j, distributionDerivative 𝕜 d Ω (w j) (regularDistribution volume (f j)) := by
  apply compact_finite_continuous_representation_of_functional_primitives
    (ContinuousKernel.twiceCoordinateWord d) ?_ u hu
  intro K A
  refine ⟨ContinuousKernel.compactKernelPrimitive K A,
    ContinuousKernel.continuous_compactKernelPrimitive K A, ?_⟩
  intro φ
  apply ContinuousKernel.compactKernelPrimitive_pairing K A _
    (ContinuousKernel.twiceCoordinateWord_sign d) φ
  intro y
  rw [testPartial_formula]
  exact ContinuousKernel.positiveKernel_identity d φ φ.contDiff φ.hasCompactSupport y

/-- The compact-support conclusion, assembled from the analytic existence
statement and the already proved cutoff construction. -/
theorem compact_primitives :
    Specs.ExpandedFA.Distributions.ContinuousDistributionPrimitives.compactPrimitivesType := by
  intro 𝕜 _ d Ω V u hc hs _ _
  obtain ⟨ι, hι, w, f, hf, hu⟩ := compact_finite_continuous_representation u hc
  let := hι
  exact compact_primitives_of_finite_representation V u hc hs w f hf hu

theorem local_primitives :
    Specs.ExpandedFA.Distributions.ContinuousDistributionPrimitives.localPrimitivesType :=
  local_primitives_of_compact compact_primitives

theorem global_primitives :
    Specs.ExpandedFA.Distributions.ContinuousDistributionPrimitives.globalPrimitivesType :=
  global_primitives_of_compact compact_primitives

end ContinuousDistributionPrimitives
end ExpandedFA.Distributions
