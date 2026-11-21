import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DistributionConvolution
import MathGenome.Internal.FourierSobolev.P102.U4.CompactSupportExtension
import MathGenome.Internal.FourierSobolev.P102.U4.LocalConvolution
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions Pointwise Topology
namespace P102.U4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

theorem compact_sub_set {K A : Set (Space d)} (hK : IsCompact K) (hA : IsCompact A) :
    IsCompact (K - A) := by
  rw [← Set.sub_image_prod]
  exact (hK.prod hA).image (continuous_fst.sub continuous_snd)


abbrev convolutionAdditionTest : DistributionConvolutionExpected.AdditionTestType := @additionTest
abbrev distributionConvolutionInner : DistributionConvolutionExpected.InnerType := @convolutionInner

/-- Whole-space convolution has no inadmissible points. -/
theorem convolutionDomain_top (φ : WholeTests d 𝕜) : convolutionDomain ⊤ φ = univ := by
  ext x
  simp [convolutionDomain]

/-- Reflection turns the plus sign in the inner pairing into the already proved
smooth-kernel regularization formula. -/
theorem convolutionInner_eq_localConvolution
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (φ : WholeTests d 𝕜) (x : Space d) :
    convolutionInner S φ x = localConvolution S (translatedKernel φ 0) (-x) := by
  rw [localConvolution_pairing d 𝕜 ⊤ S _ _ (by simp [convolutionDomain])]
  apply congrArg S
  ext y
  change φ (x + y) = φ (0 - (-x - y))
  congr 1
  abel

/-- Smoothness does not require either distribution to have compact support. -/
theorem convolutionInner_smooth
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (φ : WholeTests d 𝕜) :
    ContDiff ℝ (⊤ : ℕ∞) (convolutionInner S φ) := by
  have h := localConvolution_smooth d 𝕜 ⊤ S (translatedKernel φ 0)
  rw [convolutionDomain_top] at h
  have heq : convolutionInner S φ = fun x =>
      localConvolution S (translatedKernel φ 0) (-x) :=
    funext (convolutionInner_eq_localConvolution S φ)
  rw [heq]
  exact (contDiffOn_univ.mp h).comp contDiff_id.neg

/-- Pointwise vanishing away from the difference of the two closed supports. -/
theorem convolutionInner_eq_zero
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (φ : WholeTests d 𝕜)
    (x : Space d) (hx : x ∉ tsupport φ - relativeSupport S) :
    convolutionInner S φ x = 0 := by
  let U : Set (Space d) := {y | x + y ∉ tsupport φ}
  have hU : IsOpen U := (isClosed_tsupport φ).isOpen_compl.preimage
    (continuous_const.add continuous_id)
  apply pairing_zero_of_eqOn_zero S (additionTest φ x) hU
  · intro y hy hxy
    exact hx (Set.mem_sub.mpr ⟨x + y, hxy, y, hy, by abel⟩)
  · intro y hy
    exact image_eq_zero_of_notMem_tsupport (f := φ) hy

/-- The source support bound is closed because both sets in the difference are compact. -/
theorem convolutionInner_tsupport_subset
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) (φ : WholeTests d 𝕜) :
    tsupport (convolutionInner S φ) ⊆ tsupport φ - relativeSupport S := by
  apply closure_minimal _ (compact_sub_set φ.hasCompactSupport hS).isClosed
  intro x hx
  by_contra hn
  exact hx (convolutionInner_eq_zero S φ x hn)

/-- All assertions about the inner x-test, with no compactness condition on T. -/
theorem distributionConvolution_innerTest : DistributionConvolutionExpected.InnerTest := by
  intro d 𝕜 _ S hS φ
  exact ⟨convolutionInner_smooth S φ, convolutionInner_tsupport_subset S hS φ,
    (compact_sub_set φ.hasCompactSupport hS).of_isClosed_subset (isClosed_tsupport _)
      (convolutionInner_tsupport_subset S hS φ)⟩

theorem distributionConvolution_extensionPairing :
    DistributionConvolutionExpected.ExtensionPairing := by
  intro d 𝕜 _ S E hE φ x
  exact (hE (additionTest φ x)).symm

/-- The inner pairing, now bundled as an actual compactly supported test. -/
def convolutionInnerTest (S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) (φ : WholeTests d 𝕜) : WholeTests d 𝕜 where
  toFun := convolutionInner S φ
  contDiff' := convolutionInner_smooth S φ
  hasCompactSupport' := (distributionConvolution_innerTest d 𝕜 S hS φ).2.2
  tsupport_subset' := subset_univ _

@[simp] theorem convolutionInnerTest_apply
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) (φ : WholeTests d 𝕜) (x : Space d) :
    convolutionInnerTest S hS φ x = S (additionTest φ x) := rfl

/-- Algebraic part of the transpose construction. Continuity is proved separately. -/
def convolutionInnerLM (S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) : WholeTests d 𝕜 →ₗ[𝕜] WholeTests d 𝕜 where
  toFun := convolutionInnerTest S hS
  map_add' φ ψ := by
    ext x
    change S (additionTest (φ + ψ) x) = S (additionTest φ x) + S (additionTest ψ x)
    rw [show additionTest (φ + ψ) x = additionTest φ x + additionTest ψ x from rfl,
      map_add]
  map_smul' c φ := by
    ext x
    change S (additionTest (c • φ) x) = c • S (additionTest φ x)
    rw [show additionTest (c • φ) x = c • additionTest φ x from rfl, map_smul]

/-- Differentiating a plus translate has no reflection sign. -/
theorem partialWord_const_add {f : Space d → 𝕜}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space d) (l : List (Fin d)) :
    partialWord (fun y => f (x + y)) l = fun y => partialWord f l (x + y) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    ext y
    change fderiv ℝ (partialWord (fun y => f (x + y)) l) y (coordinateVector d i) = _
    rw [ih]
    have h := (((partialWord_contDiff hf l).differentiable (by simp)) (x + y)).hasFDerivAt
    have hc := h.comp y ((hasFDerivAt_id y).const_add x)
    change fderiv ℝ (partialWord f l ∘ HAdd.hAdd x) y (coordinateVector d i) = _
    rw [hc.fderiv]
    rfl

/-- Ordinary derivatives in x pass through the inner S pairing. -/
theorem convolutionInner_partialWord
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (φ : WholeTests d 𝕜)
    (l : List (Fin d)) :
    partialWord (convolutionInner S φ) l = convolutionInner S (testPartialWord ⊤ l φ) := by
  let ρ := translatedKernel φ 0
  have hc : ContDiff ℝ (⊤ : ℕ∞) (localConvolution S ρ) := by
    have h := localConvolution_smooth d 𝕜 ⊤ S ρ
    rw [convolutionDomain_top] at h
    exact contDiffOn_univ.mp h
  have heq : convolutionInner S φ = fun x => localConvolution S ρ (0 - x) := by
    ext x
    simpa only [zero_sub] using convolutionInner_eq_localConvolution S φ x
  rw [heq, partialWord_const_sub hc 0 l]
  ext x
  rw [localConvolution_partialWord S ρ l (0 - x) (by simp [convolutionDomain]),
    localConvolution_pairing d 𝕜 ⊤ S _ _ (by simp [convolutionDomain])]
  have ht : convolutionTest (testPartialWord ⊤ l ρ) (0 - x)
      (by simp [convolutionDomain]) =
      (-1 : 𝕜) ^ l.length • additionTest (testPartialWord ⊤ l φ) x := by
    ext y
    change testPartialWord ⊤ l ρ (0 - x - y) = _
    rw [testPartialWord_coe]
    change partialWord (fun y => φ (0 - y)) l (0 - x - y) = _
    rw [partialWord_const_sub φ.contDiff 0 l]
    change (-1 : 𝕜) ^ l.length * partialWord φ l (0 - (0 - x - y)) =
      (-1 : 𝕜) ^ l.length * testPartialWord ⊤ l φ (x + y)
    rw [show 0 - (0 - x - y) = x + y by abel, testPartialWord_coe]
  rw [ht, map_smul]
  change (-1 : 𝕜) ^ l.length * ((-1 : 𝕜) ^ l.length * _) = _
  rw [← mul_assoc, ← mul_pow]
  simp [convolutionInner]

/-- In the inner variable, distribution derivatives produce precisely their
usual distributional sign. -/
theorem convolutionInner_distributionPartial
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (φ : WholeTests d 𝕜)
    (α : MultiIndex d) (x : Space d) :
    convolutionInner (distributionPartial α S) φ x =
      (-1 : 𝕜) ^ α.card * convolutionInner S (kernelPartial α φ) x := by
  change (-1 : 𝕜) ^ α.card * S (testPartialWord ⊤ (α.sort (· ≤ ·)) (additionTest φ x)) = _
  congr 1
  apply congrArg S
  ext y
  rw [testPartialWord_coe]
  change partialWord (fun y => φ (x + y)) (α.sort (· ≤ ·)) y = _
  rw [partialWord_const_add φ.contDiff]
  change partialWord φ (α.sort (· ≤ ·)) (x + y) = kernelPartial α φ (x + y)
  rw [kernelPartial, testPartialWord_coe]

/-- The coordinate seminorm controls derivatives everywhere, including off K. -/
theorem partialWord_stage_bound (K : Compacts (Space d)) (φ : FixedSupport d 𝕜 K)
    (m : ℕ) (l : List (Fin d)) (hl : l.length ≤ m) (x : Space d) :
    ‖partialWord φ l x‖ ≤ coordinateSupSeminorm 𝕜 K m φ := by
  have hp : partialWord φ l x = iteratedFDeriv ℝ l.length φ x
      (fun j => coordinateVector d (l.get j)) := by
    simpa only [List.ofFn_get] using partialWord_ofFn φ.contDiff l.get x
  rw [hp]
  by_cases hx : x ∈ K
  · exact (coordinateSeminormFormula d 𝕜 K m φ _ (apply_nonneg _ _)).mp
      le_rfl l.length hl l.get x hx
  · have hz : iteratedFDeriv ℝ l.length φ x = 0 :=
      image_eq_zero_of_notMem_tsupport
        (fun h => hx (φ.tsupport_subset (tsupport_iteratedFDeriv_subset _ h)))
    rw [hz]
    simp

/-- The finite order of S bounds every derivative of its inner pairing by a
single higher seminorm of φ. The constants do not depend on the input support K. -/
theorem convolutionInner_orderBound
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (hS : IsCompact (relativeSupport S)) :
    ∃ (n : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (K : Compacts (Space d)) (φ : FixedSupport d 𝕜 K)
        (l : List (Fin d)) (x : Space d),
        ‖partialWord (convolutionInner S (stageInclusion 𝕜 (by intro x _; trivial) φ)) l x‖ ≤
          C * coordinateSupSeminorm 𝕜 K (n + l.length) φ := by
  obtain ⟨χ, hχ⟩ := exists_supportCutoff S hS
  obtain ⟨n, C, hC, hb⟩ := extensionUsingCutoff_bound S χ
  refine ⟨n, C, hC, ?_⟩
  intro K φ l x
  rw [convolutionInner_partialWord]
  let ψ := testPartialWord ⊤ l (stageInclusion 𝕜 (by intro x _; trivial) φ)
  have heq : convolutionInner S ψ x =
      extensionUsingCutoff S χ (testToSmooth 𝕜 (additionTest ψ x)) := by
    rw [extensionUsingCutoff_apply, smoothCutoff_agrees S χ hχ]
    rfl
  rw [heq]
  apply (hb _).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply (smoothSeminorm_le_iff _ _ n _ _ (apply_nonneg _ _)).mpr
  intro k hk a y _
  change ‖iteratedFDeriv ℝ k (additionTest ψ x) y
    (fun j => coordinateVector d (a j))‖ ≤ _
  rw [← partialWord_ofFn (additionTest ψ x).contDiff a]
  change ‖partialWord (fun z => ψ (x + z)) (List.ofFn a) y‖ ≤ _
  rw [partialWord_const_add ψ.contDiff]
  change ‖partialWord (testPartialWord ⊤ l (stageInclusion 𝕜 (by intro x _; trivial) φ))
    (List.ofFn a) (x + y)‖ ≤ _
  rw [testPartialWord_coe, ← partialWord_append]
  exact partialWord_stage_bound K φ (n + l.length) ((List.ofFn a) ++ l)
    (by simp only [List.length_append, List.length_ofFn]; omega) (x + y)

/-- One fixed-support stage is mapped into the compact difference stage. -/
def convolutionInnerStage (S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) (K : Compacts (Space d)) :
    FixedSupport d 𝕜 K →ₗ[𝕜]
      FixedSupport d 𝕜 ⟨(K : Set (Space d)) - relativeSupport S,
        compact_sub_set K.isCompact hS⟩ where
  toFun φ :=
    { toFun := convolutionInner S (stageInclusion 𝕜 (by intro x _; trivial) φ)
      contDiff' := convolutionInner_smooth S _
      zero_on_compl' := by
        intro x hx
        apply convolutionInner_eq_zero
        intro h
        exact hx (Set.sub_subset_sub_right φ.tsupport_subset h) }
  map_add' φ ψ := by
    ext x
    exact congrArg (fun f : WholeTests d 𝕜 => f x)
      ((convolutionInnerLM S hS).map_add (stageInclusion 𝕜 (by intro x _; trivial) φ)
        (stageInclusion 𝕜 (by intro x _; trivial) ψ))
  map_smul' c φ := by
    ext x
    exact congrArg (fun f : WholeTests d 𝕜 => f x)
      ((convolutionInnerLM S hS).map_smul c (stageInclusion 𝕜 (by intro x _; trivial) φ))

/-- Quantitative stage estimate proves actual LF continuity of the test map. -/
theorem convolutionInnerStage_continuous
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) (K : Compacts (Space d)) :
    Continuous (convolutionInnerStage S hS K) := by
  classical
  obtain ⟨n, C, hC, hb⟩ := convolutionInner_orderBound S hS
  apply WithSeminorms.continuous_of_isBounded (coordinateStageTopology d 𝕜 K)
    (coordinateStageTopology d 𝕜 _)
  intro m
  refine ⟨{n + m}, ⟨C, hC⟩, ?_⟩
  intro φ
  rw [Finset.sup_singleton]
  apply (coordinateSeminormFormula d 𝕜 _ m _ _ (by positivity)).mpr
  intro k hk a x _
  rw [← partialWord_ofFn (convolutionInnerStage S hS K φ).contDiff a]
  exact (hb K φ (List.ofFn a) x).trans
    (mul_le_mul_of_nonneg_left
      (coordinateSupSeminorm_monotone 𝕜 K (by simp; omega) φ) hC)

/-- The continuous test map used to transpose convolution. -/
def convolutionInnerCLM (S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) : WholeTests d 𝕜 →L[𝕜] WholeTests d 𝕜 :=
  ⟨convolutionInnerLM S hS, by
    apply (finalTopology d 𝕜 ⊤ (WholeTests d 𝕜) (convolutionInnerLM S hS)).mpr
    intro K _
    exact ((stageInclusion 𝕜 (by intro x _; trivial)).continuous.comp
      (convolutionInnerStage_continuous S hS K))⟩

theorem distributionConvolution_innerOperator : DistributionConvolutionExpected.InnerOperator := by
  intro d 𝕜 _ S hS
  exact ⟨convolutionInnerCLM S hS, fun _ _ => rfl⟩

/-- Convolution when its right factor has compact support. -/
def rightCompactConvolution (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) : DistributionSpace 𝕜 (⊤ : Opens (Space d)) :=
  T.comp (convolutionInnerCLM S hS)

@[simp] theorem rightCompactConvolution_apply
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) (φ : WholeTests d 𝕜) :
    rightCompactConvolution T S hS φ = T (convolutionInnerTest S hS φ) := rfl

/-- Whole-space relative support is an ambient closed set. -/
theorem relativeSupport_top_isClosed
    (T : DistributionSpace 𝕜 (⊤ : Opens (Space d))) : IsClosed (relativeSupport T) := by
  rw [relativeSupport, Opens.coe_top, ← compl_eq_univ_sdiff]
  exact (vanishingRegion_isOpen T).isClosed_compl

/-- Differentiation preserves compact distribution support. -/
theorem distributionPartial_compactSupport
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (hS : IsCompact (relativeSupport S))
    (α : MultiIndex d) : IsCompact (relativeSupport (distributionPartial α S)) :=
  hS.of_isClosed_subset (relativeSupport_top_isClosed _)
    (derivativeSupport d 𝕜 ⊤ α S)

/-- The closed-support inclusion, without compactness of the left distribution. -/
theorem rightCompactConvolution_support
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) :
    relativeSupport (rightCompactConvolution T S hS) ⊆ relativeSupport T + relativeSupport S := by
  intro x hx
  by_contra hn
  have hclosed : IsClosed (relativeSupport T + relativeSupport S) :=
    (relativeSupport_top_isClosed T).add_right_of_isCompact hS
  apply notMem_relativeSupport_of_vanishes (rightCompactConvolution T S hS)
    hclosed.isOpen_compl (subset_univ _) _ hn hx
  intro φ hφ
  rw [rightCompactConvolution_apply]
  apply vanishingRegion_vanishes T
  intro z hz
  have hz' := convolutionInner_tsupport_subset S hS φ hz
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_sub.mp hz'
  by_contra hzT
  have hzT' : z ∈ relativeSupport T := ⟨by trivial, hzT⟩
  have hsum : a ∈ relativeSupport T + relativeSupport S := by
    apply Set.mem_add.mpr
    exact ⟨z, hzT', b, hb, by rw [← hab]; abel⟩
  exact hφ ha hsum

/-- Differentiation of the x-test agrees with differentiation of its input. -/
theorem convolutionInnerTest_partialWord
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) (φ : WholeTests d 𝕜) (l : List (Fin d)) :
    testPartialWord ⊤ l (convolutionInnerTest S hS φ) =
      convolutionInnerTest S hS (testPartialWord ⊤ l φ) := by
  ext x
  rw [testPartialWord_coe]
  exact congrFun (convolutionInner_partialWord S φ l) x

/-- The distribution derivative can be placed on the left factor. -/
theorem rightCompactConvolution_partial_left
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) (α : MultiIndex d) :
    distributionPartial α (rightCompactConvolution T S hS) =
      rightCompactConvolution (distributionPartial α T) S hS := by
  ext φ
  change (-1 : 𝕜) ^ α.card * T (convolutionInnerTest S hS
    (testPartialWord ⊤ (α.sort (· ≤ ·)) φ)) =
      (-1 : 𝕜) ^ α.card * T (testPartialWord ⊤ (α.sort (· ≤ ·))
        (convolutionInnerTest S hS φ))
  rw [convolutionInnerTest_partialWord]

/-- The distribution derivative can also be placed on the compact factor. -/
theorem rightCompactConvolution_partial_right
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) (α : MultiIndex d)
    (hα : IsCompact (relativeSupport (distributionPartial α S))) :
    distributionPartial α (rightCompactConvolution T S hS) =
      rightCompactConvolution T (distributionPartial α S) hα := by
  ext φ
  have heq : convolutionInnerTest (distributionPartial α S) hα φ =
      (-1 : 𝕜) ^ α.card • convolutionInnerTest S hS (kernelPartial α φ) := by
    ext x
    exact convolutionInner_distributionPartial S φ α x
  change (-1 : 𝕜) ^ α.card * T (convolutionInnerTest S hS
    (testPartialWord ⊤ (α.sort (· ≤ ·)) φ)) =
      T (convolutionInnerTest (distributionPartial α S) hα φ)
  rw [heq, map_smul]
  rfl

/-- The compact-left case is represented by the transposed right-compact
construction. On every right-compact pair the source's defining formula is used. -/
def compactDistributionConvolution
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (h : IsCompact (relativeSupport T) ∨ IsCompact (relativeSupport S)) :
    DistributionSpace 𝕜 (⊤ : Opens (Space d)) := by
  classical
  exact if hS : IsCompact (relativeSupport S) then rightCompactConvolution T S hS
    else rightCompactConvolution S T (h.resolve_right hS)

theorem compactDistributionConvolution_eq_right
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S))
    (h : IsCompact (relativeSupport T) ∨ IsCompact (relativeSupport S)) :
    compactDistributionConvolution T S h = rightCompactConvolution T S hS := by
  simp [compactDistributionConvolution, hS]

/-- Complete distribution-theoretic construction and differential calculus. -/
theorem distributionConvolution_construction : DistributionConvolutionExpected.Construction := by
  intro d 𝕜 _
  refine ⟨compactDistributionConvolution, ?_, ?_, ?_⟩
  · intro T S hS φ
    refine ⟨convolutionInnerTest S hS φ, fun _ => rfl, ?_⟩
    rw [compactDistributionConvolution_eq_right T S hS]
    rfl
  · intro T S h
    classical
    by_cases hS : IsCompact (relativeSupport S)
    · rw [compactDistributionConvolution_eq_right T S hS]
      exact rightCompactConvolution_support T S hS
    · simp only [compactDistributionConvolution, dite_eq_right hS]
      simpa only [add_comm] using rightCompactConvolution_support S T (h.resolve_right hS)
  · intro T S hS α
    have hα := distributionPartial_compactSupport S hS α
    constructor
    · refine ⟨hα, ?_⟩
      rw [compactDistributionConvolution_eq_right T S hS,
        compactDistributionConvolution_eq_right T (distributionPartial α S) hα]
      exact rightCompactConvolution_partial_right T S hS α hα
    · rw [compactDistributionConvolution_eq_right T S hS,
        compactDistributionConvolution_eq_right (distributionPartial α T) S hS]
      exact rightCompactConvolution_partial_left T S hS α

/-- Compact essential support is enough for compact distribution support;
values of the representative on null sets are irrelevant. -/
theorem regularDistribution_support_of_ae_zero
    (f : Space d → 𝕜) (hf : LocallyIntegrable f volume) (K : Compacts (Space d))
    (hK : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    relativeSupport (regularDistribution ⊤ f) ⊆ K := by
  intro x hx
  by_contra hn
  apply notMem_relativeSupport_of_vanishes (regularDistribution ⊤ f)
    K.isCompact.isClosed.isOpen_compl (subset_univ _) _ hn hx
  intro φ hφ
  rw [regular_pairing d 𝕜 ⊤ f (hf.locallyIntegrableOn _)]
  simp only [Opens.coe_top, Measure.restrict_univ]
  apply integral_eq_zero_of_ae
  filter_upwards [hK] with y hy
  by_cases hyK : y ∈ K
  · have hz : φ y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => hφ hs hyK)
    simp [hz]
  · simp [hy hyK]

theorem regularDistribution_compactSupport_of_essential
    (f : Space d → 𝕜) (hf : LocallyIntegrable f volume)
    (h : HasCompactEssentialSupport f) : IsCompact (relativeSupport (regularDistribution ⊤ f)) := by
  obtain ⟨K, hK⟩ := h
  exact K.isCompact.of_isClosed_subset (relativeSupport_top_isClosed _)
    (regularDistribution_support_of_ae_zero f hf K hK)

theorem regularDistribution_test_compactSupport (ρ : WholeTests d 𝕜) :
    IsCompact (relativeSupport (regularDistribution ⊤ ρ)) := by
  apply regularDistribution_compactSupport_of_essential ρ ρ.continuous.locallyIntegrable
  exact ⟨⟨tsupport ρ, ρ.hasCompactSupport⟩,
    Filter.Eventually.of_forall fun x hx => image_eq_zero_of_notMem_tsupport hx⟩

/-- For regular factors the inner pairing is exactly the ordinary integral;
this identity requires no compact support of g. -/
theorem distributionConvolution_regularInner : DistributionConvolutionExpected.RegularInner := by
  intro d 𝕜 _ g hg φ x
  change regularDistribution ⊤ g (additionTest φ x) = _
  rw [regular_pairing d 𝕜 ⊤ g (hg.locallyIntegrableOn _)]
  simp only [Opens.coe_top, Measure.restrict_univ]
  rfl

/-- Repeated integration by parts moves the inner test derivatives onto the
smooth compact kernel. This avoids any differentiation of an unevaluated integral. -/
theorem convolutionInner_regular_partialWord (ρ φ : WholeTests d 𝕜)
    (l : List (Fin d)) (y : Space d) :
    partialWord (convolutionInner (regularDistribution ⊤ ρ) φ) l y =
      (-1 : 𝕜) ^ l.length * ∫ z, partialWord ρ l z * φ (y + z) := by
  rw [convolutionInner_partialWord,
    distributionConvolution_regularInner d 𝕜 ρ ρ.continuous.locallyIntegrable]
  have hi := integral_test_mul_partialWord (⊤ : Opens (Space d)) l
    (ρ.contDiff.of_le (by simp)).contDiffOn (additionTest φ y)
  have heq : (fun z => testPartialWord ⊤ l (additionTest φ y) z * ρ z) =
      (fun z => ρ z * testPartialWord ⊤ l φ (y + z)) := by
    ext z
    rw [testPartialWord_coe]
    change partialWord (fun z => φ (y + z)) l z * ρ z = _
    rw [partialWord_const_add φ.contDiff, mul_comm, testPartialWord_coe]
  rw [heq] at hi
  change (∫ z, φ (y + z) * partialWord ρ l z) = _ at hi
  simp_rw [mul_comm (φ (y + _))] at hi
  have hi' := congrArg (fun t : 𝕜 => (-1 : 𝕜) ^ l.length * t) hi
  simpa only [← mul_assoc, ← mul_pow,
    neg_one_mul, neg_neg, one_pow, one_mul] using hi'.symm

/-- The jet-valued integrand has compact parameter support, hence is Bochner
integrable in a finite product of Banach spaces. -/
theorem integrable_weightedTranslationJet (K : Compacts (Space d)) (m : ℕ)
    (ρ φ : WholeTests d 𝕜) :
    Integrable (fun x => φ x • translationJet K m ρ x) volume := by
  exact (φ.continuous.smul (contDiff_translationJet K m ρ).continuous).integrable_of_hasCompactSupport (φ.hasCompactSupport.smul_right)

/-- The scalar change of variables in the manuscript, also for every jet. -/
theorem integral_translated_partial (ρ φ : WholeTests d 𝕜)
    (l : List (Fin d)) (y : Space d) :
    (∫ x, φ x * ((-1 : 𝕜) ^ l.length * partialWord ρ l (x - y))) =
      (-1 : 𝕜) ^ l.length * ∫ z, partialWord ρ l z * φ (y + z) := by
  rw [← integral_add_left_eq_self (fun x =>
    φ x * ((-1 : 𝕜) ^ l.length * partialWord ρ l (x - y))) y]
  simp_rw [add_sub_cancel_left]
  simp_rw [show ∀ z, φ (y + z) * ((-1 : 𝕜) ^ l.length * partialWord ρ l z) =
    (-1 : 𝕜) ^ l.length * (partialWord ρ l z * φ (y + z)) by intro z; ring]
  exact integral_const_mul _ _

/-- Pulling an arbitrary distribution through a smooth compact kernel integral.
Only finite jets are integrated; no completeness of the LF test space is used. -/
theorem distribution_smoothKernel_transpose
    (T : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (ρ φ : WholeTests d 𝕜) :
    T (convolutionInnerTest (regularDistribution ⊤ ρ)
      (regularDistribution_test_compactSupport ρ) φ) =
      ∫ x, localConvolution T ρ x * φ x := by
  let K : Compacts (Space d) :=
    ⟨tsupport φ - tsupport ρ, compact_sub_set φ.hasCompactSupport ρ.hasCompactSupport⟩
  have hρsupp : relativeSupport (regularDistribution ⊤ ρ) ⊆ tsupport ρ :=
    regularDistribution_support_of_ae_zero ρ ρ.continuous.locallyIntegrable
      ⟨tsupport ρ, ρ.hasCompactSupport⟩
      (Eventually.of_forall fun x hx => image_eq_zero_of_notMem_tsupport hx)
  let ψ : FixedSupport d 𝕜 K :=
    ContDiffMapSupportedIn.of_support_subset (convolutionInner_smooth
      (regularDistribution ⊤ ρ) φ) ((subset_tsupport _).trans
        ((convolutionInner_tsupport_subset _ (regularDistribution_test_compactSupport ρ) φ).trans
          (Set.sub_subset_sub_left hρsupp)))
  obtain ⟨m, L, hL⟩ := FiniteJets.distribution_factorization 𝕜 T K
    (by intro x _; trivial)
  let J := fun x => φ x • translationJet K m ρ x
  have hJ : Integrable J volume := integrable_weightedTranslationJet K m ρ φ
  have hjet : (∫ x, J x) = FiniteJets.jet 𝕜 K m ψ := by
    funext a
    ext y
    let ev : FiniteJets.Jets 𝕜 K m →L[𝕜] 𝕜 :=
      (ContinuousMap.evalCLM 𝕜 y).comp (ContinuousLinearMap.proj a)
    have he := ev.integral_comp_comm hJ
    change (∫ x, φ x * ((-1 : 𝕜) ^ a.1.val *
      partialWord ρ (List.ofFn a.2) (x - (y : Space d)))) = (∫ x, J x) a y at he
    rw [← he, FiniteJets.jet_apply, ← partialWord_ofFn ψ.contDiff a.2]
    change _ = partialWord (convolutionInner (regularDistribution ⊤ ρ) φ)
      (List.ofFn a.2) y
    rw [convolutionInner_regular_partialWord]
    simpa only [List.length_ofFn] using integral_translated_partial ρ φ (List.ofFn a.2) y
  have hpoint : ∀ x, L (J x) = localConvolution T ρ x * φ x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have hs : tsupport (translatedKernel ρ x) ⊆ K := by
        intro y hy
        have hy' : x - y ∈ tsupport ρ :=
          tsupport_comp_subset_preimage ρ (continuous_const.sub continuous_id) hy
        exact Set.mem_sub.mpr ⟨x, hx, x - y, hy', by abel⟩
      rw [show L (J x) = φ x * L (translationJet K m ρ x) from L.map_smul _ _]
      rw [← localConvolution_eq_jetPairing T ρ K (by intro x _; trivial) m L hL x
        (by simp [convolutionDomain]) hs, mul_comm]
    · have hz : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [J, hz]
  calc
    _ = L (FiniteJets.jet 𝕜 K m ψ) := (hL ψ).symm
    _ = L (∫ x, J x) := congrArg L hjet.symm
    _ = ∫ x, L (J x) := (L.integral_comp_comm hJ).symm
    _ = _ := integral_congr_ae (Eventually.of_forall hpoint)

/-- A smooth compact factor gives exactly the regular distribution of the
already constructed smooth regularization. -/
theorem rightCompactConvolution_smoothKernel
    (T : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (ρ : WholeTests d 𝕜) :
    rightCompactConvolution T (regularDistribution ⊤ ρ)
      (regularDistribution_test_compactSupport ρ) =
      regularDistribution ⊤ (localConvolution T ρ) := by
  ext φ
  rw [rightCompactConvolution_apply, distribution_smoothKernel_transpose,
    regular_pairing d 𝕜 ⊤ _]
  · simp only [Opens.coe_top, Measure.restrict_univ]
  · have hs := localConvolution_smooth d 𝕜 ⊤ T ρ
    rw [convolutionDomain_top] at hs
    exact (contDiffOn_univ.mp hs).continuous.locallyIntegrable.locallyIntegrableOn _

/-- The integral convention is symmetric even at points where the Bochner
integral takes its default value, by the measure-preserving reflection. -/
theorem functionConvolution_comm (f g : Space d → 𝕜) (x : Space d) :
    functionConvolution f g x = functionConvolution g f x := by
  unfold functionConvolution
  rw [← integral_sub_left_eq_self (fun y => f (x - y) * g y) volume x]
  simp only [sub_sub_cancel, mul_comm]

/-- Local integrability and compact essential support give global L¹. -/
theorem integrable_of_compactEssentialSupport (g : Space d → 𝕜)
    (hg : LocallyIntegrable g volume) (A : Compacts (Space d))
    (hA : ∀ᵐ y ∂volume, y ∉ A → g y = 0) : Integrable g volume := by
  apply ((hg.integrableOn_isCompact A.isCompact).integrable_indicator
    A.isCompact.measurableSet).congr
  filter_upwards [hA] with y hy
  by_cases hyA : y ∈ A
  · simp [hyA]
  · simp [hyA, hy hyA]

/-- On a compact output region the other factor can be cut down to a compact
set. The equality is on integrands, so it also transfers a.e. existence. -/
theorem convolution_localization_right (f g : Space d → 𝕜)
    (A B : Compacts (Space d)) (hA : ∀ᵐ y ∂volume, y ∉ A → g y = 0)
    (x : Space d) (hx : x ∈ B) :
    (fun y => f (x - y) * g y) =ᵐ[volume]
      (fun y => ((B : Set (Space d)) - (A : Set (Space d))).indicator f (x - y) * g y) := by
  filter_upwards [hA] with y hy
  by_cases hyA : y ∈ A
  · rw [indicator_of_mem (Set.mem_sub.mpr ⟨x, hx, y, hyA, rfl⟩)]
  · simp [hy hyA]

/-- The local L¹ convolution theorem with a compact essential right factor. -/
theorem functionConvolution_local_right (f g : Space d → 𝕜)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (A : Compacts (Space d)) (hA : ∀ᵐ y ∂volume, y ∉ A → g y = 0) :
    (∀ᵐ x ∂volume, Integrable (fun y => f (x - y) * g y) volume) ∧
      LocallyIntegrable (functionConvolution f g) volume := by
  have hgI := integrable_of_compactEssentialSupport g hg A hA
  have hlocal : ∀ B : Compacts (Space d),
      (∀ᵐ x ∂volume.restrict B, Integrable (fun y => f (x - y) * g y) volume) ∧
        IntegrableOn (functionConvolution f g) B volume := by
    intro B
    let F := ((B : Set (Space d)) - (A : Set (Space d))).indicator f
    have hF : Integrable F volume :=
      (hf.integrableOn_isCompact (compact_sub_set B.isCompact A.isCompact)).integrable_indicator
        (compact_sub_set B.isCompact A.isCompact).measurableSet
    have heq : ∀ x ∈ B, functionConvolution f g x =
        MeasureTheory.convolution g F (ContinuousLinearMap.mul 𝕜 𝕜).flip volume x := by
      intro x hx
      exact integral_congr_ae (convolution_localization_right f g A B hA x hx)
    constructor
    · filter_upwards [(hgI.ae_convolution_exists (ContinuousLinearMap.mul 𝕜 𝕜).flip hF).filter_mono (ae_mono Measure.restrict_le_self), ae_restrict_mem B.isCompact.measurableSet]
          with x hi hx
      exact hi.congr (convolution_localization_right f g A B hA x hx).symm
    · apply ((hgI.integrable_convolution (ContinuousLinearMap.mul 𝕜 𝕜).flip hF).integrableOn).congr
      exact (ae_restrict_mem B.isCompact.measurableSet).mono fun x hx => (heq x hx).symm
  constructor
  · have hcover := (ae_restrict_iUnion_iff
        (fun n : ℕ => Metric.closedBall (0 : Space d) (n : ℝ))
        (fun x => Integrable (fun y => f (x - y) * g y) volume)).mpr
        (fun n => (hlocal ⟨_, isCompact_closedBall _ _⟩).1)
    simpa only [Metric.iUnion_closedBall_nat, Measure.restrict_univ] using hcover
  · exact locallyIntegrable_iff.mpr fun B hB => (hlocal ⟨B, hB⟩).2

/-- Fubini for the weighted integral of two globally L¹ factors. -/
theorem functionConvolution_pairing_integrable (f g : Space d → 𝕜)
    (hf : Integrable f volume) (hg : Integrable g volume) (φ : WholeTests d 𝕜) :
    (∫ x, functionConvolution f g x * φ x) =
      ∫ z, f z * ∫ y, g y * φ (z + y) := by
  obtain ⟨M, hM⟩ := (φ.hasCompactSupport.isCompact_range φ.continuous).isBounded.exists_norm_le
  have hb : ∀ x, ‖φ x‖ ≤ M := fun x => hM _ ⟨x, rfl⟩
  have hp : Integrable (fun p : Space d × Space d =>
      f (p.1 - p.2) * g p.2 * φ p.1) (volume.prod volume) :=
    (hg.convolution_integrand (ContinuousLinearMap.mul 𝕜 𝕜).flip hf).mul_bdd
      (φ.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => hb p.1)
  have hq : Integrable (fun p : Space d × Space d =>
      f p.1 * g p.2 * φ (p.1 + p.2)) (volume.prod volume) :=
    (hf.mul_prod hg).mul_bdd
      (φ.continuous.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun p => hb (p.1 + p.2))
  calc
    _ = ∫ x, ∫ y, f (x - y) * g y * φ x := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => (integral_mul_const (φ x) _).symm
    _ = ∫ y, ∫ x, f (x - y) * g y * φ x := integral_integral_swap hp
    _ = ∫ y, ∫ z, f z * g y * φ (z + y) := by
      apply integral_congr_ae
      refine Eventually.of_forall fun y => ?_
      change (∫ x, f (x - y) * g y * φ x) = _
      rw [← integral_add_right_eq_self (fun x => f (x - y) * g y * φ x) y]
      simp only [add_sub_cancel_right]
    _ = ∫ z, ∫ y, f z * g y * φ (z + y) := (integral_integral_swap hq).symm
    _ = _ := by simp_rw [mul_assoc, integral_const_mul]

/-- A second scalar Fubini identity, used when the essential compact support is
on the left. -/
theorem integral_inner_swap_integrable (f g : Space d → 𝕜)
    (hf : Integrable f volume) (hg : Integrable g volume) (φ : WholeTests d 𝕜) :
    (∫ z, f z * ∫ y, g y * φ (z + y)) =
      ∫ y, g y * ∫ z, f z * φ (y + z) := by
  obtain ⟨M, hM⟩ := (φ.hasCompactSupport.isCompact_range φ.continuous).isBounded.exists_norm_le
  have hq : Integrable (fun p : Space d × Space d =>
      f p.1 * (g p.2 * φ (p.1 + p.2))) (volume.prod volume) := by
    simpa only [mul_assoc, Function.comp_apply, Pi.add_apply] using (hf.mul_prod hg).mul_bdd
      (φ.continuous.comp (continuous_fst.add continuous_snd)).aestronglyMeasurable
      (Eventually.of_forall fun p => hM _ ⟨p.1 + p.2, rfl⟩)
  simp_rw [← integral_const_mul]
  rw [integral_integral_swap hq]
  congr 1
  ext y
  congr 1
  ext z
  rw [add_comm y z]
  ring

/-- With g supported essentially in A, the weighted inner integral only sees
f on supp φ - A. The equality holds for every outer point. -/
theorem innerIntegral_localization (f g : Space d → 𝕜)
    (A : Compacts (Space d)) (hA : ∀ᵐ y ∂volume, y ∉ A → g y = 0)
    (φ : WholeTests d 𝕜) (z : Space d) :
    f z * (∫ y, g y * φ (z + y)) =
      (tsupport φ - (A : Set (Space d))).indicator f z *
        (∫ y, g y * φ (z + y)) := by
  by_cases hz : z ∈ tsupport φ - (A : Set (Space d))
  · rw [indicator_of_mem hz]
  · have hz0 : (∫ y, g y * φ (z + y)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hA] with y hy
      by_cases hyA : y ∈ A
      · have hφ : φ (z + y) = 0 := image_eq_zero_of_notMem_tsupport
          (fun hs => hz (Set.mem_sub.mpr ⟨z + y, hs, y, hyA, by abel⟩))
        simp [hφ]
      · simp [hy hyA]
    simp [hz0]

/-- Fubini's pairing for locally integrable representatives when the right
factor has compact essential support. -/
theorem functionConvolution_pairing_right (f g : Space d → 𝕜)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (A : Compacts (Space d)) (hA : ∀ᵐ y ∂volume, y ∉ A → g y = 0)
    (φ : WholeTests d 𝕜) :
    (∫ x, functionConvolution f g x * φ x) =
      ∫ z, f z * ∫ y, g y * φ (z + y) := by
  let B : Compacts (Space d) := ⟨tsupport φ, φ.hasCompactSupport⟩
  let F := ((B : Set (Space d)) - (A : Set (Space d))).indicator f
  have hF : Integrable F volume :=
    (hf.integrableOn_isCompact (compact_sub_set B.isCompact A.isCompact)).integrable_indicator
      (compact_sub_set B.isCompact A.isCompact).measurableSet
  have hgI := integrable_of_compactEssentialSupport g hg A hA
  calc
    _ = ∫ x, functionConvolution F g x * φ x := by
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      change functionConvolution f g x * φ x = functionConvolution F g x * φ x
      by_cases hx : x ∈ tsupport φ
      · rw [show functionConvolution f g x = functionConvolution F g x from
          integral_congr_ae (convolution_localization_right f g A B hA x hx)]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    _ = ∫ z, F z * ∫ y, g y * φ (z + y) :=
      functionConvolution_pairing_integrable F g hF hgI φ
    _ = _ := integral_congr_ae (Eventually.of_forall fun z =>
      (innerIntegral_localization f g A hA φ z).symm)

/-- The weighted Fubini interchange also holds with only one essential compact
support and local L¹ hypotheses. -/
theorem integral_inner_swap_local_left (f g : Space d → 𝕜)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (A : Compacts (Space d)) (hA : ∀ᵐ z ∂volume, z ∉ A → f z = 0)
    (φ : WholeTests d 𝕜) :
    (∫ z, f z * ∫ y, g y * φ (z + y)) =
      ∫ y, g y * ∫ z, f z * φ (y + z) := by
  let G := (tsupport φ - (A : Set (Space d))).indicator g
  have hG : Integrable G volume :=
    (hg.integrableOn_isCompact (compact_sub_set φ.hasCompactSupport A.isCompact)).integrable_indicator (compact_sub_set φ.hasCompactSupport A.isCompact).measurableSet
  have hfI := integrable_of_compactEssentialSupport f hf A hA
  calc
    _ = ∫ z, f z * ∫ y, G y * φ (z + y) := by
      apply integral_congr_ae
      filter_upwards [hA] with z hz
      rw [← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      refine Eventually.of_forall fun y => ?_
      change f z * (g y * φ (z + y)) = f z * (G y * φ (z + y))
      by_cases hzA : z ∈ A
      · by_cases hy : y ∈ tsupport φ - (A : Set (Space d))
        · simp [G, indicator_of_mem hy]
        · have hφ : φ (z + y) = 0 := image_eq_zero_of_notMem_tsupport
            (fun hs => hy (Set.mem_sub.mpr ⟨z + y, hs, z, hzA, by abel⟩))
          simp [hφ]
      · simp [hz hzA]
    _ = ∫ y, G y * ∫ z, f z * φ (y + z) :=
      integral_inner_swap_integrable f G hfI hG φ
    _ = _ := integral_congr_ae (Eventually.of_forall fun y =>
      (innerIntegral_localization g f A hA φ y).symm)

/-- Ordinary convolution is a.e. defined and locally integrable for either
compact essential factor. -/
theorem functionConvolution_locallyIntegrable (f g : Space d → 𝕜)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (h : HasCompactEssentialSupport f ∨ HasCompactEssentialSupport g) :
    (∀ᵐ x ∂volume, Integrable (fun y => f (x - y) * g y) volume) ∧
      LocallyIntegrable (functionConvolution f g) volume := by
  rcases h with ⟨A, hA⟩ | ⟨A, hA⟩
  · obtain ⟨he, hi⟩ := functionConvolution_local_right g f hg hf A hA
    constructor
    · filter_upwards [he] with x hx
      simpa only [sub_sub_cancel, mul_comm] using hx.comp_sub_left x
    · have heq : functionConvolution g f = functionConvolution f g :=
        funext (functionConvolution_comm g f)
      rwa [heq] at hi
  · exact functionConvolution_local_right f g hf hg A hA

/-- The full scalar pairing formula, with the compact support on either factor. -/
theorem functionConvolution_pairing (f g : Space d → 𝕜)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (h : HasCompactEssentialSupport f ∨ HasCompactEssentialSupport g)
    (φ : WholeTests d 𝕜) :
    (∫ x, functionConvolution f g x * φ x) =
      ∫ z, f z * ∫ y, g y * φ (z + y) := by
  rcases h with ⟨A, hA⟩ | ⟨A, hA⟩
  · calc
      _ = ∫ x, functionConvolution g f x * φ x :=
        integral_congr_ae (Eventually.of_forall fun x =>
          congrArg (fun t : 𝕜 => t * φ x) (functionConvolution_comm f g x))
      _ = ∫ y, g y * ∫ z, f z * φ (y + z) :=
        functionConvolution_pairing_right g f hg hf A hA φ
      _ = _ := (integral_inner_swap_local_left f g hf hg A hA φ).symm
  · exact functionConvolution_pairing_right f g hf hg A hA φ

/-- The canonical right-compact distribution pairing is the regular
distribution of the usual convolution of locally integrable representatives. -/
theorem rightCompactConvolution_regular (f g : Space d → 𝕜)
    (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    (h : HasCompactEssentialSupport f ∨ HasCompactEssentialSupport g)
    (hS : IsCompact (relativeSupport (regularDistribution ⊤ g))) :
    rightCompactConvolution (regularDistribution ⊤ f) (regularDistribution ⊤ g) hS =
      regularDistribution ⊤ (functionConvolution f g) := by
  have hi := (functionConvolution_locallyIntegrable f g hf hg h).2
  ext φ
  rw [rightCompactConvolution_apply,
    regular_pairing d 𝕜 ⊤ f (hf.locallyIntegrableOn _),
    regular_pairing d 𝕜 ⊤ _ (hi.locallyIntegrableOn _)]
  simp only [Opens.coe_top, Measure.restrict_univ]
  change (∫ z, f z * convolutionInner (regularDistribution ⊤ g) φ z) = _
  simp_rw [distributionConvolution_regularInner d 𝕜 g hg]
  exact (functionConvolution_pairing f g hf hg h φ).symm

/-- Complete convolution theorem: construction, support, differentiation,
smooth regularization, and locally integrable compatibility with either
compact essential factor. -/
theorem distributionConvolution : DistributionConvolutionExpected.Convolution := by
  intro d 𝕜 _
  refine ⟨compactDistributionConvolution, ?_, ?_, ?_, ?_, ?_⟩
  · intro T S hS φ
    refine ⟨convolutionInnerTest S hS φ, fun _ => rfl, ?_⟩
    rw [compactDistributionConvolution_eq_right T S hS]
    rfl
  · intro T S h
    classical
    by_cases hS : IsCompact (relativeSupport S)
    · rw [compactDistributionConvolution_eq_right T S hS]
      exact rightCompactConvolution_support T S hS
    · simp only [compactDistributionConvolution, dite_eq_right hS]
      simpa only [add_comm] using rightCompactConvolution_support S T (h.resolve_right hS)
  · intro T S hS α
    have hα := distributionPartial_compactSupport S hS α
    constructor
    · refine ⟨hα, ?_⟩
      rw [compactDistributionConvolution_eq_right T S hS,
        compactDistributionConvolution_eq_right T (distributionPartial α S) hα]
      exact rightCompactConvolution_partial_right T S hS α hα
    · rw [compactDistributionConvolution_eq_right T S hS,
        compactDistributionConvolution_eq_right (distributionPartial α T) S hS]
      exact rightCompactConvolution_partial_left T S hS α
  · intro T ρ
    refine ⟨regularDistribution_test_compactSupport ρ, ?_⟩
    rw [compactDistributionConvolution_eq_right T _ (regularDistribution_test_compactSupport ρ)]
    exact rightCompactConvolution_smoothKernel T ρ
  · intro f g hf hg he
    obtain ⟨hex, hi⟩ := functionConvolution_locallyIntegrable f g hf hg he
    have h : IsCompact (relativeSupport (regularDistribution ⊤ f)) ∨
        IsCompact (relativeSupport (regularDistribution ⊤ g)) :=
      he.imp (regularDistribution_compactSupport_of_essential f hf)
        (regularDistribution_compactSupport_of_essential g hg)
    refine ⟨hex, hi, h, ?_⟩
    classical
    by_cases hS : IsCompact (relativeSupport (regularDistribution ⊤ g))
    · rw [compactDistributionConvolution_eq_right _ _ hS]
      exact rightCompactConvolution_regular f g hf hg he hS
    · simp only [compactDistributionConvolution, dite_eq_right hS]
      rw [rightCompactConvolution_regular g f hg hf he.symm (h.resolve_right hS)]
      congr 1
      exact funext (functionConvolution_comm g f)

end P102.U4
