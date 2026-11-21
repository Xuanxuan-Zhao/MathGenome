import MathGenome.Internal.FourierSobolev.Specs.P102.U4.TestSpace
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section
open Set TopologicalSpace Filter
open scoped ContDiff Distributions Topology Manifold

namespace P102.U4

abbrev tests (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) := TestSpace 𝕜 Ω
abbrev fixedTests (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d)) :=
  FixedSupport d 𝕜 K
abbrev distributions (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) :=
  DistributionSpace 𝕜 Ω

theorem stageContinuity : Expected.StageContinuity := by
  intro d 𝕜 _ Ω K hK
  exact (stageInclusion 𝕜 hK).continuous

theorem finalTopology : Expected.FinalTopology := by
  intro d 𝕜 _ Ω F _ _ _ _ _ _ _ _ T
  exact TestFunction.continuous_iff_continuous_comp T

theorem zeroExtensionProperties : Expected.ZeroExtensionProperties := by
  intro d 𝕜 _ V Ω h f
  have heq : (zeroExtension 𝕜 h f : Space d → 𝕜) = f := by
    simp [zeroExtension, TestFunction.monoCLM_apply, h]
  refine ⟨fun x => congrFun heq x, ?_, ?_⟩
  · intro x hx
    rw [congrFun heq x]
    exact f.zero_on_compl hx
  · intro k x
    rw [heq]

theorem smoothZeroExtension : Expected.SmoothZeroExtension := by
  intro d 𝕜 _ V f hf hs
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ V
  · exact hf.contDiffAt (V.isOpen.mem_nhds hx)
  · have hxs : x ∉ tsupport f := fun h => hx (hs h)
    have hzero : f =ᶠ[𝓝 x] 0 := by
      filter_upwards [(isClosed_closure (s := Function.support f)).isOpen_compl.mem_nhds hxs] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact contDiffAt_const.congr_of_eventuallyEq hzero

theorem emptyTests : Expected.EmptyTests := by
  intro d 𝕜 _ f
  ext x
  exact f.zero_on_compl (by simp)

theorem frechetStageTopology : Expected.FrechetStageTopology := by
  intro d 𝕜 _ K
  exact ContDiffMapSupportedIn.withSeminorms' 𝕜 (Space d) 𝕜 ⊤ K

theorem pairingBilinear : Expected.PairingBilinear := by
  intro d 𝕜 _ Ω T S f g a
  exact ⟨map_add T f g, by simp, rfl, rfl⟩

theorem cutoff : Expected.Cutoff := by
  intro d V K hK
  obtain ⟨B, hBo, hKB, hBc⟩ := exists_isOpen_superset_and_isCompact_closure K.isCompact
  obtain ⟨W, hWo, hKW, hWV⟩ := K.isCompact.exists_isOpen_closure_subset
    ((V.isOpen.inter hBo).mem_nhdsSet.mpr (subset_inter hK hKB))
  have hWc : IsCompact (closure W) := hBc.of_isClosed_subset isClosed_closure
    (hWV.trans (inter_subset_right.trans subset_closure))
  have hKi : (K : Set (Space d)) ⊆ interior (closure W) :=
    hKW.trans (hWo.subset_interior_iff.mpr subset_closure)
  obtain ⟨g, hg1, hg0, hg01⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, Space d)) K.isCompact.isClosed hKi
      (n := ⊤)
  have hgs : tsupport (g : Space d → ℝ) ⊆ closure W :=
    closure_minimal (fun x hx => by
      by_contra hn
      exact hx (hg0 x hn)) isClosed_closure
  let χ : TestSpace ℝ V :=
    ⟨g, g.contMDiff.contDiff, hWc.of_isClosed_subset isClosed_closure hgs,
      hgs.trans (hWV.trans inter_subset_left)⟩
  obtain ⟨U, hUo, hKU, hgU⟩ := eventually_nhdsSet_iff_exists.mp hg1
  refine ⟨χ, fun x => hg01 x, ⟨U ∩ V, hUo.inter V.isOpen⟩,
    subset_inter hKU hK, inter_subset_right, ?_⟩
  intro x hx
  exact hgU x hx.1

theorem coordinateEvaluationBound : Expected.CoordinateEvaluationBound := by
  intro d k 𝕜 _ A a
  simpa [coordinateVector] using A.le_opNorm (fun j => coordinateVector d (a j))

theorem coordinateVolume : Expected.CoordinateVolume := by
  intro d
  exact PiLp.volume_preserving_ofLp (Fin d)

theorem coordinateNorm : Expected.CoordinateNorm := by
  intro d x i
  exact PiLp.norm_apply_le x i

theorem emptyStage : Expected.EmptyStage := by
  intro d 𝕜 _ f
  have hf : f = 0 := by
    ext x
    exact f.zero_on_compl (by simp)
  exact ⟨hf, fun k => by simp [hf]⟩

theorem fixedSupportExtension : Expected.FixedSupportExtension := by
  intro d 𝕜 _ V Ω h K hK f
  ext x
  simp [zeroExtension, stageInclusion, TestFunction.monoCLM_apply, h]

theorem operatorNormBound : Expected.OperatorNormBound := by
  intro d k 𝕜 _ A M hM hA
  apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hM)
  intro v
  have hv (j : Fin k) : ∑ i : Fin d, (v j) i • coordinateVector d i = v j :=
    (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (v j)
  calc
    ‖A v‖ = ‖A (fun j => ∑ i : Fin d, (v j) i • coordinateVector d i)‖ := by
      simp only [hv]
    _ = ‖∑ a : Fin k → Fin d,
      (∏ j, (v j) (a j)) • A (fun j => coordinateVector d (a j))‖ := by
      rw [A.map_sum]
      simp only [A.map_smul_univ]
    _ ≤ ∑ a : Fin k → Fin d,
      ‖(∏ j, (v j) (a j)) • A (fun j => coordinateVector d (a j))‖ := norm_sum_le _ _
    _ ≤ ∑ _a : Fin k → Fin d, (∏ j, ‖v j‖) * M := by
      apply Finset.sum_le_sum
      intro a _
      rw [norm_smul, norm_prod]
      exact mul_le_mul (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun j _ => PiLp.norm_apply_le (v j) (a j))) (hA a) (norm_nonneg _) (by positivity)
    _ = (d : ℝ) ^ k * M * ∏ j, ‖v j‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow]
      ring

@[simp] theorem realPart_apply {d : ℕ} {Ω : Opens (Space d)}
    (f : TestSpace ℂ Ω) (x : Space d) : realPart Ω f x = (f x).re := rfl

@[simp] theorem imagPart_apply {d : ℕ} {Ω : Opens (Space d)}
    (f : TestSpace ℂ Ω) (x : Space d) : imagPart Ω f x = (f x).im := rfl

@[simp] theorem complexifyTest_apply {d : ℕ} {Ω : Opens (Space d)}
    (f : TestSpace ℝ Ω) (x : Space d) : complexifyTest Ω f x = (f x : ℂ) := rfl

theorem realPart_smul {d : ℕ} (Ω : Opens (Space d)) (c : ℂ) (f : TestSpace ℂ Ω) :
    realPart Ω (c • f) = c.re • realPart Ω f - c.im • imagPart Ω f := by
  ext x
  simp [Complex.mul_re]

theorem imagPart_smul {d : ℕ} (Ω : Opens (Space d)) (c : ℂ) (f : TestSpace ℂ Ω) :
    imagPart Ω (c • f) = c.re • imagPart Ω f + c.im • realPart Ω f := by
  ext x
  simp [Complex.mul_im]

theorem complexExtension : Expected.ComplexExtension := by
  intro d Ω T
  let S : DistributionSpace ℂ Ω :=
    { toFun := fun f => T (realPart Ω f) + Complex.I * T (imagPart Ω f)
      map_add' := by intros; simp only [map_add, mul_add]; ring
      map_smul' := by
        intro c f
        simp only [realPart_smul, imagPart_smul, map_sub, map_add, map_smul,
          smul_eq_mul, RingHom.id_apply, Complex.real_smul]
        have hc : (c.re : ℂ) + Complex.I * (c.im : ℂ) = c := by
          simpa only [mul_comm Complex.I] using c.re_add_im
        calc
          _ = ((c.re : ℂ) + Complex.I * (c.im : ℂ)) *
              (T (realPart Ω f) + Complex.I * T (imagPart Ω f)) := by
            linear_combination -(c.im : ℂ) * T (imagPart Ω f) * Complex.I_mul_I
          _ = _ := by rw [hc]
      cont := (T.continuous.comp (realPart Ω).continuous).add
        (continuous_const.mul (T.continuous.comp (imagPart Ω).continuous)) }
  refine ⟨S, (fun f => rfl), ?_, ?_, ?_⟩
  · intro φ ψ
    have hr : realPart Ω (complexifyTest Ω φ + Complex.I • complexifyTest Ω ψ) = φ := by
      ext x
      simp
    have hi : imagPart Ω (complexifyTest Ω φ + Complex.I • complexifyTest Ω ψ) = ψ := by
      ext x
      simp
    change T _ + Complex.I * T _ = _
    rw [hr, hi]
  · intro φ
    have hr : realPart Ω (complexifyTest Ω φ) = φ := by ext x; simp
    have hi : imagPart Ω (complexifyTest Ω φ) = 0 := by ext x; simp
    change T _ + Complex.I * T _ = _
    simp [hr, hi]
  · intro S' hS'
    ext f
    have hd : complexifyTest Ω (realPart Ω f) +
        Complex.I • complexifyTest Ω (imagPart Ω f) = f := by
      ext x
      simp only [add_apply, smul_apply, complexifyTest_apply, realPart_apply, imagPart_apply,
        smul_eq_mul]
      simpa only [mul_comm Complex.I] using (f x).re_add_im
    calc
      S' f = S' (complexifyTest Ω (realPart Ω f) +
          Complex.I • complexifyTest Ω (imagPart Ω f)) := congrArg S' hd.symm
      _ = T (realPart Ω f) + Complex.I * T (imagPart Ω f) := by
        rw [map_add, map_smul, hS', hS']
        rfl
      _ = S f := rfl

theorem coordinateWordSeminorm_le_iff {d k : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (a : Fin k → Fin d) (f : FixedSupport d 𝕜 K)
    (C : ℝ) (hC : 0 ≤ C) :
    coordinateWordSeminorm 𝕜 K a f ≤ C ↔
      ∀ x ∈ K, ‖iteratedFDeriv ℝ k f x (fun j => coordinateVector d (a j))‖ ≤ C := by
  change ‖(coordinateEvaluation 𝕜 a).compLeftContinuousBounded (Space d)
    (ContDiffMapSupportedIn.structureMapCLM 𝕜 ⊤ k f)‖ ≤ C ↔ _
  rw [BoundedContinuousFunction.norm_le hC]
  change (∀ x, ‖iteratedFDeriv ℝ k f x (fun j => coordinateVector d (a j))‖ ≤ C) ↔ _
  constructor
  · exact fun h x _ => h x
  · intro h x
    by_cases hx : x ∈ K
    · exact h x hx
    · simp [f.iteratedFDeriv_zero_on_compl hx, hC]

theorem coordinateSeminormFormula : Expected.CoordinateSeminormFormula := by
  intro d 𝕜 _ K m f C hC
  constructor
  · intro h k hk a x hx
    have hword : coordinateWordSeminorm 𝕜 K a f ≤ C :=
      (Seminorm.le_finset_sup_apply (Finset.mem_univ a)).trans
        ((Seminorm.le_finset_sup_apply (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))).trans h)
    exact (coordinateWordSeminorm_le_iff 𝕜 K a f C hC).mp hword x hx
  · intro h
    apply Seminorm.finset_sup_apply_le hC
    intro k hk
    apply Seminorm.finset_sup_apply_le hC
    intro a _
    exact (coordinateWordSeminorm_le_iff 𝕜 K a f C hC).mpr
      (h k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) a)

theorem coordinateSup_le_frechet {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) (f : FixedSupport d 𝕜 K) :
    coordinateSupSeminorm 𝕜 K m f ≤
      ((Finset.range (m + 1)).sup (frechetSeminorm 𝕜 K)) f := by
  apply (coordinateSeminormFormula d 𝕜 K m f _ (apply_nonneg _ _)).mpr
  intro k hk a x _
  exact (coordinateEvaluationBound d k 𝕜 _ a).trans
    ((ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜).trans
      (Seminorm.le_finset_sup_apply (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))))

theorem frechet_le_coordinateSup {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (k : ℕ) (f : FixedSupport d 𝕜 K) :
    frechetSeminorm 𝕜 K k f ≤ (d : ℝ) ^ k * coordinateSupSeminorm 𝕜 K k f := by
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff 𝕜 (by positivity) k f).mpr
  intro x hx
  apply operatorNormBound d k 𝕜 _ _ (apply_nonneg _ _)
  intro a
  exact (coordinateSeminormFormula d 𝕜 K k f _ (apply_nonneg _ _)).mp le_rfl k le_rfl a x hx

theorem coordinateStageTopology : Expected.CoordinateStageTopology := by
  intro d 𝕜 _ K
  apply (ContDiffMapSupportedIn.withSeminorms 𝕜 (Space d) 𝕜 ⊤ K).congr
  · apply Seminorm.IsBounded.of_real
    intro m
    exact ⟨Finset.range (m + 1), 1, fun f => by
      have h := coordinateSup_le_frechet 𝕜 K m f
      unfold frechetSeminorm at h
      simpa only [LinearMap.id_apply, one_mul] using h⟩
  · apply Seminorm.IsBounded.of_real
    intro k
    exact ⟨{k}, (d : ℝ) ^ k, fun f => by
      simpa only [LinearMap.id_apply, Finset.sup_singleton, frechetSeminorm] using frechet_le_coordinateSup 𝕜 K k f⟩

theorem localTestZeroExtension : Expected.LocalTestZeroExtension := by
  classical
  intro d 𝕜 _ V K hK f hf hs
  let g := (V : Set (Space d)).indicator f
  have hgs : Function.support g ⊆ K := by
    intro x hx
    have hxV : x ∈ V := by
      by_contra h
      exact hx (by simp [g, h])
    apply hs
    exact ⟨by simpa [g, hxV] using hx, hxV⟩
  have hgts : tsupport g ⊆ K := closure_minimal hgs K.isCompact.isClosed
  have hgd : ContDiffOn ℝ (⊤ : ℕ∞) g V := hf.congr (fun x hx => by simp [g, hx])
  let φ : TestSpace 𝕜 V :=
    ⟨g, smoothZeroExtension d 𝕜 V g hgd (hgts.trans hK),
      K.isCompact.of_isClosed_subset isClosed_closure hgts, hgts.trans hK⟩
  refine ⟨φ, hgts, ?_, ?_⟩
  · intro x hx
    change (V : Set (Space d)).indicator f x = f x
    simp [hx]
  · intro x hx
    change (V : Set (Space d)).indicator f x = 0
    simp only [Set.mem_compl_iff] at hx
    simp [hx]

theorem partialWord_contDiff {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {f : Space d → 𝕜}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (l : List (Fin d)) : ContDiff ℝ (⊤ : ℕ∞) (partialWord f l) := by
  induction l with
  | nil => exact hf
  | cons i l ih =>
    exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem partialWord_swap {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {f : Space d → 𝕜}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i j : Fin d) (l : List (Fin d)) :
    partialWord f (i :: j :: l) = partialWord f (j :: i :: l) := by
  ext x
  have hg := partialWord_contDiff hf l
  have hd : DifferentiableAt ℝ (fderiv ℝ (partialWord f l)) x :=
    (hg.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero x
  simp only [partialWord]
  rw [fderiv_clm_apply hd (differentiableAt_const (coordinateVector d j)),
    fderiv_clm_apply hd (differentiableAt_const (coordinateVector d i))]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using
    (hg.contDiffAt.isSymmSndFDerivAt (by simp) (coordinateVector d i) (coordinateVector d j))

theorem partialWord_perm {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {f : Space d → 𝕜}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {l l' : List (Fin d)} (h : l.Perm l') :
    partialWord f l = partialWord f l' := by
  induction h with
  | nil => rfl
  | cons i h ih => simp only [partialWord, ih]
  | swap i j l => exact partialWord_swap hf _ _ _
  | trans h h' ih ih' => exact ih.trans ih'

theorem partialWord_ofFn {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {f : Space d → 𝕜}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {k : ℕ} (a : Fin k → Fin d) (x : Space d) :
    partialWord f (List.ofFn a) x =
      iteratedFDeriv ℝ k f x (fun j => coordinateVector d (a j)) := by
  induction k generalizing x with
  | zero => simp [partialWord, iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (partialWord f (List.ofFn (Fin.tail a))) x (coordinateVector d (a 0)) = _
    have hi : partialWord f (List.ofFn (Fin.tail a)) =
        fun y => iteratedFDeriv ℝ k f y (fun j => coordinateVector d (a j.succ)) := by
      ext y
      exact ih (Fin.tail a) y
    rw [hi]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
      (hf.iteratedFDeriv_right (m := 1) (by simp)).differentiable one_ne_zero x
    rw [fderiv_continuousMultilinear_apply_const hd]
    rfl

theorem multiPartial_ofFn {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {f : Space d → 𝕜}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {k : ℕ} (a : Fin k → Fin d) (x : Space d) :
    multiPartial f (List.ofFn a : Multiset (Fin d)) x =
      iteratedFDeriv ℝ k f x (fun j => coordinateVector d (a j)) := by
  have hp : ((List.ofFn a : Multiset (Fin d)).sort (· ≤ ·)).Perm (List.ofFn a) :=
    Multiset.coe_eq_coe.mp (Multiset.sort_eq _ _)
  rw [multiPartial, partialWord_perm hf hp, partialWord_ofFn hf]

theorem multiIndexSeminormFormula : Expected.MultiIndexSeminormFormula := by
  intro d 𝕜 _ K m f C hC
  rw [coordinateSeminormFormula d 𝕜 K m f C hC]
  constructor
  · intro h α hα x hx
    let l := α.sort (· ≤ ·)
    have hl : (l : Multiset (Fin d)) = α := Multiset.sort_eq _ _
    have ha := h l.length (by simpa [l] using hα) l.get x hx
    rw [← multiPartial_ofFn f.contDiff] at ha
    simpa [List.ofFn_get, hl] using ha
  · intro h k hk a x hx
    simpa only [multiPartial_ofFn f.contDiff] using
      h (List.ofFn a) (by simpa using hk) x hx

abbrev coordinateSeminorm (d : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) := coordinateSupSeminorm 𝕜 K m

theorem emptyCoordinateSeminorm : Expected.EmptyCoordinateSeminorm := by
  intro d 𝕜 _ f m
  rw [(emptyStage d 𝕜 f).1]
  exact map_zero _

theorem complexScalarContinuity : Expected.ComplexScalarContinuity := by
  intro d Ω
  have hI : Continuous (fun f : TestSpace ℂ Ω => Complex.I • f) := by
    convert (TestFunction.postcompCLM (Complex.I • ContinuousLinearMap.id ℂ ℂ)
      (Ω := Ω) (n := ⊤)).continuous using 1
    funext f
    ext x
    rfl
  have heq : (fun p : ℂ × TestSpace ℂ Ω => p.1 • p.2) =
      (fun p : ℂ × TestSpace ℂ Ω => p.1.re • p.2 + p.1.im • (Complex.I • p.2)) := by
    funext p
    ext x
    simp only [smul_apply, add_apply, Complex.real_smul, smul_eq_mul]
    conv_lhs => rw [← p.1.re_add_im]
    ring
  rw [heq]
  exact ((Complex.continuous_re.comp continuous_fst).smul continuous_snd).add
    ((Complex.continuous_im.comp continuous_fst).smul (hI.comp continuous_snd))

instance continuousSMulComplexTests {d : ℕ} (Ω : Opens (Space d)) :
    ContinuousSMul ℂ (TestSpace ℂ Ω) where
  continuous_smul := complexScalarContinuity d Ω

theorem multiIndexCoordinates : Expected.MultiIndexCoordinates := by
  intro d α
  refine ⟨fun i => rfl, ?_⟩
  exact (Multiset.sum_count_eq_card (s := Finset.univ) (m := α)
    (fun i _ => Finset.mem_univ i)).symm

theorem extensionSeminorms : Expected.ExtensionSeminorms := by
  intro d 𝕜 _ V Ω h K hK f
  exact ⟨f, (fixedSupportExtension d 𝕜 V Ω h K hK f).symm, fun _ => rfl, fun _ => rfl⟩

theorem orderSeminormComparison : Expected.OrderSeminormComparison := by
  intro d 𝕜 _ K k f
  have hw (a : Fin k → Fin d) : coordinateWordSeminorm 𝕜 K a f ≤ frechetSeminorm 𝕜 K k f := by
    apply (coordinateWordSeminorm_le_iff 𝕜 K a f _ (apply_nonneg _ _)).mpr
    intro x _
    exact (coordinateEvaluationBound d k 𝕜 _ a).trans
      (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜)
  refine ⟨Seminorm.finset_sup_apply_le (apply_nonneg _ _) (fun a _ => hw a), ?_⟩
  apply (ContDiffMapSupportedIn.seminorm_top_le_iff 𝕜 (by positivity) k f).mpr
  intro x hx
  apply operatorNormBound d k 𝕜 _ _ (apply_nonneg _ _)
  intro a
  apply (coordinateWordSeminorm_le_iff 𝕜 K a f _ (apply_nonneg _ _)).mp
    (Seminorm.le_finset_sup_apply (Finset.mem_univ a)) x hx

theorem finestTopology : Expected.FinestTopology := by
  intro d 𝕜 _ Ω t
  let : TopologicalSpace (TestSpace 𝕜 Ω) := t
  intro _ _ _
  rw [TestFunction.topologicalSpace_le_iff]
  simp only [TestFunction.originalTop, iSup_le_iff, ← continuous_iff_coinduced_le]
  rfl

theorem stageCoverage : Expected.StageCoverage := by
  intro d 𝕜 _ Ω f
  let K : Compacts (Space d) := ⟨tsupport f, f.hasCompactSupport⟩
  let g : FixedSupport d 𝕜 K :=
    ContDiffMapSupportedIn.of_support_subset f.contDiff subset_closure
  exact ⟨K, f.tsupport_subset, g, rfl⟩

end P102.U4
