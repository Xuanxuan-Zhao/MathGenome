import MathGenome.Internal.FourierSobolev.Specs.P102.U4.CompactSupportExtension
import MathGenome.Internal.FourierSobolev.P102.U4.DistributionSupport
import MathGenome.Internal.FourierSobolev.P102.U4.LocalOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds

noncomputable section
open Set TopologicalSpace
open scoped ContDiff Distributions Topology
namespace P102.U4

variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}

/-- The defining family generates exactly the declared compact-smooth topology. -/
theorem smoothFunctions_withSeminorms : WithSeminorms (smoothSeminormFamily 𝕜 Ω) := ⟨rfl⟩

/-- The finite-maximum seminorm is precisely the maximum of the coordinate suprema. -/
theorem smoothSeminorm_le_iff (K : Compacts (Space d))
    (hK : (K : Set (Space d)) ⊆ Ω) (m : ℕ) (f : SmoothFunctions 𝕜 Ω)
    (C : ℝ) (hC : 0 ≤ C) :
    smoothSeminorm 𝕜 K hK m f ≤ C ↔
      ∀ k ≤ m, ∀ a : Fin k → Fin d, ∀ x ∈ K,
        ‖iteratedFDeriv ℝ k f.val x (fun j => coordinateVector d (a j))‖ ≤ C := by
  constructor
  · intro h k hk a x hx
    have hw : smoothWordSeminorm 𝕜 K hK a f ≤ C :=
      (Seminorm.le_finset_sup_apply (Finset.mem_univ a)).trans
        ((Seminorm.le_finset_sup_apply
          (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))).trans h)
    exact ((ContinuousMap.norm_le _ hC).mp hw) ⟨x, hx⟩
  · intro h
    apply Seminorm.finset_sup_apply_le hC
    intro k hk
    apply Seminorm.finset_sup_apply_le hC
    intro a _
    apply (ContinuousMap.norm_le _ hC).mpr
    intro x
    exact h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) a x x.property

/-- Operator derivatives are bounded by coordinate seminorms on the same compact. -/
theorem smooth_iteratedFDeriv_bound (K : Compacts (Space d))
    (hK : (K : Set (Space d)) ⊆ Ω) (m k : ℕ) (hk : k ≤ m)
    (f : SmoothFunctions 𝕜 Ω) (x : Space d) (hx : x ∈ K) :
    ‖iteratedFDeriv ℝ k f.val x‖ ≤
      (max (d : ℝ) 1) ^ m * smoothSeminorm 𝕜 K hK m f := by
  have hq := (smoothSeminorm_le_iff K hK m f _ (apply_nonneg _ _)).mp le_rfl
  have h := operatorNormBound d k 𝕜 (iteratedFDeriv ℝ k f.val x)
    (smoothSeminorm 𝕜 K hK m f) (apply_nonneg _ _) (fun a => hq k hk a x hx)
  exact h.trans (mul_le_mul_of_nonneg_right
    ((pow_le_pow_left₀ (by positivity) (le_max_left _ _) _).trans
      (pow_le_pow_right₀ (le_max_right _ _) hk)) (apply_nonneg _ _))

/-- Ambient compactness of the relative support gives a real or complex cutoff,
without a nonemptiness assumption. -/
theorem exists_supportCutoff (S : DistributionSpace 𝕜 Ω)
    (hS : IsCompact (relativeSupport S)) :
    ∃ χ : TestSpace 𝕜 Ω, IsSupportCutoff S χ := by
  obtain ⟨χ, _, U, hU, _, hχ⟩ := cutoff d Ω ⟨relativeSupport S, hS⟩ sdiff_subset
  let χk : TestSpace 𝕜 Ω := TestFunction.postcompCLM
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) χ
  refine ⟨χk, U, hU, ?_⟩
  intro x hx
  change (χ x : 𝕜) = 1
  rw [hχ x hx]
  simp

/-- Support locality proves independence even for a noncompactly supported f. -/
theorem smoothCutoff_independent (S : DistributionSpace 𝕜 Ω)
    (χ ψ : TestSpace 𝕜 Ω) (hχ : IsSupportCutoff S χ) (hψ : IsSupportCutoff S ψ)
    (f : SmoothFunctions 𝕜 Ω) :
    S (smoothCutoffProduct χ f) = S (smoothCutoffProduct ψ f) := by
  obtain ⟨U, hU, hχ⟩ := hχ
  obtain ⟨V, hV, hψ⟩ := hψ
  apply supportLocality d 𝕜 Ω S _ _ (U ∩ V) (U.isOpen.inter V.isOpen)
    (subset_inter hU hV)
  intro x hx
  change f.val x * χ x = f.val x * ψ x
  rw [hχ x hx.1, hψ x hx.2]

/-- On tests the extension agrees with the original distribution. -/
theorem smoothCutoff_agrees (S : DistributionSpace 𝕜 Ω)
    (χ : TestSpace 𝕜 Ω) (hχ : IsSupportCutoff S χ) (φ : TestSpace 𝕜 Ω) :
    S (smoothCutoffProduct χ (testToSmooth 𝕜 φ)) = S φ := by
  obtain ⟨U, hU, hχ⟩ := hχ
  apply supportLocality d 𝕜 Ω S _ _ U U.isOpen hU
  intro x hx
  change φ x * χ x = φ x
  rw [hχ x hx, mul_one]

/-- Multiplication by a fixed test takes all smooth functions into one fixed stage. -/
def smoothCutoffStage (χ : TestSpace 𝕜 Ω) :
    SmoothFunctions 𝕜 Ω →ₗ[𝕜] FixedSupport d 𝕜 ⟨tsupport χ, χ.hasCompactSupport⟩ where
  toFun f := ⟨smoothCutoffProduct χ f, (smoothCutoffProduct χ f).contDiff,
    fun x hx => by
      change f.val x * χ x = 0
      rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]⟩
  map_add' f g := by ext x; change (f.val x + g.val x) * χ x = _; exact add_mul _ _ _
  map_smul' c f := by ext x; change (c * f.val x) * χ x = _; exact mul_assoc _ _ _

@[simp] theorem smoothCutoffStage_apply (χ : TestSpace 𝕜 Ω)
    (f : SmoothFunctions 𝕜 Ω) (x : Space d) :
    smoothCutoffStage χ f x = f.val x * χ x := rfl

/-- A uniform Leibniz estimate on the fixed cutoff support. -/
theorem smoothCutoffStage_bound (χ : TestSpace 𝕜 Ω) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : SmoothFunctions 𝕜 Ω,
      coordinateSupSeminorm 𝕜 ⟨tsupport χ, χ.hasCompactSupport⟩ m
        (smoothCutoffStage χ f) ≤
      C * smoothSeminorm 𝕜 ⟨tsupport χ, χ.hasCompactSupport⟩ χ.tsupport_subset m f := by
  obtain ⟨M, hM, hχ⟩ := χ.hasCompactSupport.exists_bound_iteratedFDeriv χ.contDiff m
  refine ⟨2 ^ m * M * (max (d : ℝ) 1) ^ m, by positivity, fun f => ?_⟩
  apply (coordinateSeminormFormula d 𝕜 ⟨tsupport χ, χ.hasCompactSupport⟩ m
    (smoothCutoffStage χ f) _ (by positivity)).mpr
  intro k hk a x hx
  apply (coordinateEvaluationBound d k 𝕜 _ a).trans
  have hb := norm_iteratedFDerivWithin_mul_le f.property.1 χ.contDiff.contDiffOn
    Ω.isOpen.uniqueDiffOn (χ.tsupport_subset hx) (n := k) (by simp)
  simp only [iteratedFDerivWithin_of_isOpen _ Ω.isOpen (χ.tsupport_subset hx)] at hb
  change ‖iteratedFDeriv ℝ k (fun x => f.val x * χ x) x‖ ≤ _
  calc
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f.val x‖ * ‖iteratedFDeriv ℝ (k - i) χ x‖ := hb
    _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ((max (d : ℝ) 1) ^ m *
          smoothSeminorm 𝕜 ⟨tsupport χ, χ.hasCompactSupport⟩ χ.tsupport_subset m f) * M := by
      apply Finset.sum_le_sum
      intro i hi
      gcongr
      · exact smooth_iteratedFDeriv_bound _ χ.tsupport_subset m i
          ((Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans hk) f x hx
      · exact hχ _ ((Nat.sub_le _ _).trans hk) x
    _ = 2 ^ k * M * (max (d : ℝ) 1) ^ m *
        smoothSeminorm 𝕜 ⟨tsupport χ, χ.hasCompactSupport⟩ χ.tsupport_subset m f := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
      push_cast
      ring
    _ ≤ _ := by gcongr; norm_num

/-- Cutoff multiplication is continuous from the compact-smooth topology to a
single fixed-support Fréchet stage. -/
theorem smoothCutoffStage_continuous (χ : TestSpace 𝕜 Ω) :
    Continuous (smoothCutoffStage χ) := by
  apply WithSeminorms.continuous_of_isBounded smoothFunctions_withSeminorms
    (coordinateStageTopology d 𝕜 ⟨tsupport χ, χ.hasCompactSupport⟩)
  intro m
  obtain ⟨C, hC, hb⟩ := smoothCutoffStage_bound χ m
  refine ⟨{(⟨⟨tsupport χ, χ.hasCompactSupport⟩, χ.tsupport_subset⟩, m)}, ⟨C, hC⟩, ?_⟩
  intro f
  rw [Finset.sup_singleton]
  exact hb f

/-- The linear map defined by any chosen cutoff. -/
def extensionUsingCutoff (S : DistributionSpace 𝕜 Ω) (χ : TestSpace 𝕜 Ω) :
    SmoothFunctions 𝕜 Ω →L[𝕜] 𝕜 :=
  S.comp ((stageInclusion 𝕜 χ.tsupport_subset).comp
    ⟨smoothCutoffStage χ, smoothCutoffStage_continuous χ⟩)

@[simp] theorem extensionUsingCutoff_apply (S : DistributionSpace 𝕜 Ω)
    (χ : TestSpace 𝕜 Ω) (f : SmoothFunctions 𝕜 Ω) :
    extensionUsingCutoff S χ f = S (smoothCutoffProduct χ f) := by
  apply congrArg S
  ext x
  rfl

/-- Finite order for the extension follows from local order on the one cutoff stage. -/
theorem extensionUsingCutoff_bound (S : DistributionSpace 𝕜 Ω) (χ : TestSpace 𝕜 Ω) :
    ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ f,
      ‖extensionUsingCutoff S χ f‖ ≤
        C * smoothSeminorm 𝕜 ⟨tsupport χ, χ.hasCompactSupport⟩ χ.tsupport_subset m f := by
  obtain ⟨C, hC, m, hb⟩ := (localOrder d 𝕜 Ω S.toLinearMap).mp S.continuous
    ⟨tsupport χ, χ.hasCompactSupport⟩ χ.tsupport_subset
  obtain ⟨D, hD, hprod⟩ := smoothCutoffStage_bound χ m
  refine ⟨m, C * D, mul_nonneg hC hD, fun f => ?_⟩
  calc
    _ ≤ C * coordinateSupSeminorm 𝕜 ⟨tsupport χ, χ.hasCompactSupport⟩ m
        (smoothCutoffStage χ f) := hb _
    _ ≤ C * (D * smoothSeminorm 𝕜 ⟨tsupport χ, χ.hasCompactSupport⟩
        χ.tsupport_subset m f) := mul_le_mul_of_nonneg_left (hprod f) hC
    _ = _ := (mul_assoc _ _ _).symm

/-- The compact-support extension theorem, including empty support and S = 0. -/
theorem compactSupportExtension : CompactExtensionExpected.Extension := by
  intro d 𝕜 _ Ω S hS
  obtain ⟨χ, hχ⟩ := exists_supportCutoff S hS
  refine ⟨extensionUsingCutoff S χ, ⟨χ, hχ⟩, ?_, ?_, ?_, ?_⟩
  · intro ψ hψ f
    rw [extensionUsingCutoff_apply]
    exact smoothCutoff_independent S χ ψ hχ hψ f
  · intro φ
    rw [extensionUsingCutoff_apply]
    exact smoothCutoff_agrees S χ hχ φ
  · obtain ⟨m, C, hC, hb⟩ := extensionUsingCutoff_bound S χ
    exact ⟨⟨tsupport χ, χ.hasCompactSupport⟩, χ.tsupport_subset, m, C, hC, hb⟩
  · intro E' hE'
    ext f
    exact (hE' χ hχ f).trans (extensionUsingCutoff_apply S χ f).symm

/-- The ordinary inclusion of Schwartz functions into C∞. -/
def schwartzToSmoothLM (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    SchwartzTests d 𝕜 →ₗ[𝕜] SmoothFunctions 𝕜 (⊤ : Opens (Space d)) where
  toFun f := ⟨f, (f.smooth ⊤).contDiffOn, by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every compact-smooth seminorm is bounded by finitely many unweighted
Schwartz seminorms. -/
theorem schwartzToSmooth_continuous (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    Continuous (schwartzToSmoothLM d 𝕜) := by
  classical
  apply WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms 𝕜 (Space d) 𝕜)
    smoothFunctions_withSeminorms
  intro i
  let s : Finset (ℕ × ℕ) := (Finset.range (i.2 + 1)).image (fun k => (0, k))
  refine ⟨s, 1, ?_⟩
  intro f
  simp only [one_smul, Seminorm.comp_apply]
  apply (smoothSeminorm_le_iff i.1.val i.1.property i.2 _ _ (apply_nonneg _ _)).mpr
  intro k hk a x _
  apply (coordinateEvaluationBound d k 𝕜 _ a).trans
  apply (SchwartzMap.norm_iteratedFDeriv_le_seminorm 𝕜 f k x).trans
  exact Seminorm.le_finset_sup_apply
    (p := fun j : ℕ × ℕ => SchwartzMap.seminorm 𝕜 j.1 j.2) (x := f)
    (show (0, k) ∈ s from
      Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk), rfl⟩)

/-- The inclusion, with its actual compact-smooth continuity. -/
def schwartzToSmooth (d : ℕ) (𝕜 : Type) [RCLike 𝕜] :
    SchwartzTests d 𝕜 →L[𝕜] SmoothFunctions 𝕜 (⊤ : Opens (Space d)) :=
  ⟨schwartzToSmoothLM d 𝕜, schwartzToSmooth_continuous d 𝕜⟩

/-- A compactly supported ordinary distribution has a tempered extension,
obtained by restricting its canonical smooth extension. -/
theorem compactSupportTemperedExtension : CompactExtensionExpected.TemperedExtension := by
  intro d 𝕜 _ S hS
  obtain ⟨E, _, hformula, hagrees, _, _⟩ := compactSupportExtension d 𝕜 ⊤ S hS
  refine ⟨E, hformula, E.comp (schwartzToSmooth d 𝕜), fun f => rfl, ?_⟩
  intro φ
  change E (schwartzToSmooth d 𝕜 (testToSchwartz d 𝕜 φ)) = S φ
  rw [show schwartzToSmooth d 𝕜 (testToSchwartz d 𝕜 φ) = testToSmooth 𝕜 φ from rfl]
  exact hagrees φ

/-- Every smooth function on the open domain has a unique representative in the
zero-extension model. No boundary regularity is required. -/
theorem smoothFunctions_representation : CompactExtensionExpected.SmoothRepresentation := by
  intro d 𝕜 _ Ω f hf
  classical
  let g : SmoothFunctions 𝕜 Ω := ⟨(Ω : Set (Space d)).indicator f,
    hf.congr (by intro x hx; simp [hx]), by intro x hx; simp [hx]⟩
  refine ⟨g, (by intro x hx; simp [g, hx]), ?_⟩
  intro g' hg'
  apply Subtype.ext
  funext x
  by_cases hx : x ∈ Ω
  · exact (hg' hx).trans (by simp [g, hx])
  · exact (g'.property.2 x hx).trans (by simp [g, hx])

/-- A local smooth function has a globally smooth representative near any
interior point, obtained with one of the upstream cutoffs. -/
theorem smoothFunctions_local_representative (f : SmoothFunctions 𝕜 Ω)
    (x : Space d) (hx : x ∈ Ω) :
    ∃ g : Space d → 𝕜, ContDiff ℝ (⊤ : ℕ∞) g ∧ f.val =ᶠ[𝓝 x] g := by
  obtain ⟨χ, _, U, hU, _, hχ⟩ := cutoff d Ω ⟨{x}, isCompact_singleton⟩
    (by simpa using hx)
  let χk : TestSpace 𝕜 Ω := TestFunction.postcompCLM
    (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) χ
  refine ⟨smoothCutoffProduct χk f, (smoothCutoffProduct χk f).contDiff, ?_⟩
  filter_upwards [U.isOpen.mem_nhds (hU (mem_singleton x))] with y hy
  change f.val y = f.val y * (χ y : 𝕜)
  rw [hχ y hy]
  simp

/-- Iterated coordinate derivatives depend only on the germ at the point. -/
theorem partialWord_eventuallyEq {f g : Space d → 𝕜} {x : Space d}
    (h : f =ᶠ[𝓝 x] g) (l : List (Fin d)) :
    partialWord f l =ᶠ[𝓝 x] partialWord g l := by
  induction l with
  | nil => exact h
  | cons i l ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun A : Space d →L[ℝ] 𝕜 => A (coordinateVector d i)) hy

/-- The ordinary local multi-index derivative agrees with evaluation of the
Fréchet derivative on coordinate vectors. -/
theorem smooth_multiPartial_ofFn (f : SmoothFunctions 𝕜 Ω) {k : ℕ}
    (a : Fin k → Fin d) (x : Space d) (hx : x ∈ Ω) :
    multiPartial f.val (List.ofFn a : Multiset (Fin d)) x =
      iteratedFDeriv ℝ k f.val x (fun j => coordinateVector d (a j)) := by
  obtain ⟨g, hg, hfg⟩ := smoothFunctions_local_representative f x hx
  calc
    _ = multiPartial g (List.ofFn a : Multiset (Fin d)) x :=
      (partialWord_eventuallyEq hfg _).eq_of_nhds
    _ = iteratedFDeriv ℝ k g x (fun j => coordinateVector d (a j)) :=
      multiPartial_ofFn hg a x
    _ = _ := congrArg (fun A : Space d [×k]→L[ℝ] 𝕜 =>
      A (fun j => coordinateVector d (a j))) (hfg.iteratedFDeriv ℝ k).eq_of_nhds.symm

/-- Exact identification with the original multi-index derivative suprema. -/
theorem smoothSeminorm_multiIndex : CompactExtensionExpected.MultiIndexFormula := by
  intro d 𝕜 _ Ω K hK m f C hC
  rw [smoothSeminorm_le_iff K hK m f C hC]
  constructor
  · intro h α hα x hx
    let l := α.sort (· ≤ ·)
    have hl : (l : Multiset (Fin d)) = α := Multiset.sort_eq _ _
    have ha := h l.length (by simpa [l] using hα) l.get x hx
    rw [← smooth_multiPartial_ofFn f l.get x (hK hx)] at ha
    simpa [List.ofFn_get, hl] using ha
  · intro h k hk a x hx
    rw [← smooth_multiPartial_ofFn f a x (hK hx)]
    exact h (List.ofFn a) (by simpa using hk) x hx

/-- The support hypothesis includes the zero distribution and the empty support
case, which are characterized here without any compactness assumption. -/
theorem compactExtension_emptySupport : CompactExtensionExpected.EmptySupport := by
  intro d 𝕜 _ Ω S
  constructor
  · intro hS
    ext φ
    exact pairing_zero_of_eqOn_zero S φ isOpen_empty
      (by simp [hS]) (by simp)
  · rintro rfl
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact notMem_relativeSupport_of_vanishes (0 : DistributionSpace 𝕜 Ω)
      Ω.isOpen Subset.rfl (by intro φ _; rfl) hx.1 hx

end P102.U4
