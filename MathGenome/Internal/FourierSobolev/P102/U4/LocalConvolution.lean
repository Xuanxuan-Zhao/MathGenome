import MathGenome.Internal.FourierSobolev.Specs.P102.U4.LocalConvolution
import MathGenome.Internal.FourierSobolev.P102.U4.LocalOrder
import MathGenome.Internal.FourierSobolev.P102.U4.RegularDerivatives
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.LocallyConvex.HahnBanach

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions Topology

namespace P102.U4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CompactParameter

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

variable {E F Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace Y] [CompactSpace Y]

/-- Interchange a continuous compact parameter and a continuous linear argument. -/
def flipCLM : C(Y, E →L[ℝ] F) →L[ℝ] (E →L[ℝ] C(Y, F)) := by
  let L : C(Y, E →L[ℝ] F) →ₗ[ℝ] (E →L[ℝ] C(Y, F)) :=
    { toFun := fun A => by
        let l : E →ₗ[ℝ] C(Y, F) :=
          { toFun := fun v => ⟨fun y => A y v, A.continuous.clm_apply continuous_const⟩
            map_add' := fun _ _ => by ext y; exact map_add (A y) _ _
            map_smul' := fun _ _ => by ext y; exact map_smul (A y) _ _ }
        exact l.mkContinuous ‖A‖ (fun v => (ContinuousMap.norm_le _ (by positivity)).mpr
          fun y => (A y).le_opNorm v |>.trans
            (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm y) (norm_nonneg v)))
      map_add' := fun _ _ => by ext v y; rfl
      map_smul' := fun _ _ => by ext v y; rfl }
  refine LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ)
    (E := C(Y, E →L[ℝ] F)) (F := E →L[ℝ] C(Y, F)) L 1 ?_
  intro A
  change ‖L A‖ ≤ 1 * ‖A‖
  have hbound : ‖L A‖ ≤ ‖A‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
    intro v
    exact (ContinuousMap.norm_le _ (by positivity)).mpr fun y =>
      (A y).le_opNorm v |>.trans
        (mul_le_mul_of_nonneg_right (A.norm_coe_le_norm y) (norm_nonneg v))
  simpa only [one_mul] using hbound

@[simp] theorem flipCLM_apply (A : C(Y, E →L[ℝ] F)) (v : E) (y : Y) :
    flipCLM A v y = A y v := rfl

/-- Jointly continuous pointwise derivatives give a derivative in the uniform norm. -/
theorem hasFDerivAt {f : E → C(Y, F)} {A : E → C(Y, E →L[ℝ] F)}
    (hA : Continuous A) (hf : ∀ x y, HasFDerivAt (fun z => f z y) (A x y) x) (x : E) :
    HasFDerivAt f (flipCLM (A x)) x := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hAδ⟩ := (Metric.continuousAt_iff (f := A) (a := x)).mp hA.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds x hδ] with z hz
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro y
  have hb : ∀ w ∈ Metric.ball x δ, ‖A w y - A x y‖ ≤ ε := by
    intro w hw
    have hdist : dist (A w) (A x) = ‖A w - A x‖ := dist_eq_norm (A w) (A x)
    exact ((A w - A x).norm_coe_le_norm y).trans
      (le_of_lt (hdist ▸ hAδ hw))
  have h := (convex_ball x δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun w => f w y - A x y w)
    (f' := fun w => A w y - A x y)
    (x := x) (y := z)
    (fun w _ => ((hf w y).sub (A x y).hasFDerivAt).hasFDerivWithinAt)
    hb (by simp [hδ]) hz
  simpa only [ContinuousMap.sub_apply, flipCLM_apply, map_sub, sub_sub_sub_comm] using h

section Restriction

variable {Z : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Restrict the second argument of a continuous function to a compact set. -/
def family (K : Compacts Z) (g : E × Z → F) (hg : Continuous g) (x : E) : C(K, F) :=
  ⟨fun y => g (x, y), hg.comp (continuous_const.prodMk continuous_subtype_val)⟩

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ Z] in
theorem continuous_family (K : Compacts Z) {g : E × Z → F} (hg : Continuous g) :
    Continuous (family K g hg) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact hg.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- Smoothness on a product gives smooth dependence in the uniform norm on a compact set. -/
theorem contDiff_family {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Compacts Z) {g : E × Z → F} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (family K g hg.continuous) := by
  have hnat : ∀ (n : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (g : E × Z → F) (hg : ContDiff ℝ (⊤ : ℕ∞) g),
      ContDiff ℝ n (family K g hg.continuous) := by
    intro n
    induction n with
    | zero =>
      intro F _ _ g hg
      exact contDiff_zero.mpr (continuous_family K hg.continuous)
    | succ n ih =>
      intro F _ _ g hg
      let D : E × Z → E →L[ℝ] F :=
        fun p => (fderiv ℝ g p).comp (ContinuousLinearMap.inl ℝ E Z)
      have hD : ContDiff ℝ (⊤ : ℕ∞) D :=
        (hg.fderiv_right (by simp)).clm_comp contDiff_const
      let A : E → C(K, E →L[ℝ] F) := family K D hD.continuous
      apply contDiff_succ_iff_hasFDerivAt.mpr
      refine ⟨fun x => flipCLM (A x), ?_, ?_⟩
      · change ContDiff ℝ n ((flipCLM (E := E) (F := F) (Y := K)) ∘ family K D hD.continuous)
        exact ContinuousLinearMap.contDiff _ |>.comp (ih _ D hD)
      · intro x
        apply hasFDerivAt (continuous_family K hD.continuous)
        intro w y
        exact ((hg.differentiable (by simp)) (w, (y : Z))).hasFDerivAt.comp w
          (hasFDerivAt_prodMk_left w (y : Z))
  exact contDiff_infty.mpr fun n => hnat n F g hg

end Restriction

end CompactParameter

namespace FiniteJets

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev Word (d m : ℕ) := (k : Fin (m + 1)) × (Fin k.val → Fin d)

abbrev Jets {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d)) (m : ℕ) :=
  Word d m → C(K, 𝕜)

/-- Finite coordinate derivatives, restricted to the fixed compact support. -/
def jet {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d)) (m : ℕ) :
    FixedSupport d 𝕜 K →ₗ[𝕜] Jets 𝕜 K m where
  toFun φ a := ⟨fun y => iteratedFDeriv ℝ a.1.val φ y
      (fun j => coordinateVector d (a.2 j)),
    (coordinateEvaluation 𝕜 a.2).continuous.comp
      ((φ.contDiff.continuous_iteratedFDeriv (by simp)).comp continuous_subtype_val)⟩
  map_add' φ ψ := by
    funext a
    ext y
    change iteratedFDeriv ℝ a.1.val (φ + ψ) y _ = _
    simp only [FunLike.coe_add, iteratedFDeriv_add
      (φ.contDiff.of_le (by simp)) (ψ.contDiff.of_le (by simp)),
      Pi.add_apply]
    rfl
  map_smul' c φ := by
    funext a
    ext y
    change iteratedFDeriv ℝ a.1.val (c • φ) y _ = _
    simp only [FunLike.coe_smul, iteratedFDeriv_const_smul_apply
      (φ.contDiff.of_le (by simp)).contDiffAt]
    rfl

@[simp] theorem jet_apply {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (K : Compacts (Space d))
    (m : ℕ) (φ : FixedSupport d 𝕜 K) (a : Word d m) (y : K) :
    jet 𝕜 K m φ a y = iteratedFDeriv ℝ a.1.val φ y
      (fun j => coordinateVector d (a.2 j)) := rfl

theorem jet_injective {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) : Function.Injective (jet 𝕜 K m) := by
  intro φ ψ h
  ext y
  by_cases hy : y ∈ K
  · have hval := congrArg (fun J : Jets 𝕜 K m =>
      J ⟨⟨0, by omega⟩, fun j => Fin.elim0 j⟩ ⟨y, hy⟩) h
    simpa only [jet_apply, iteratedFDeriv_zero_apply] using hval
  · rw [φ.zero_on_compl hy, ψ.zero_on_compl hy]

theorem coordinateSupSeminorm_le_jet_norm {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) (φ : FixedSupport d 𝕜 K) :
    coordinateSupSeminorm 𝕜 K m φ ≤ ‖jet 𝕜 K m φ‖ := by
  apply (coordinateSeminormFormula d 𝕜 K m φ _ (norm_nonneg _)).mpr
  intro k hk a y hy
  let w : Word d m := ⟨⟨k, by omega⟩, a⟩
  exact ((jet 𝕜 K m φ w).norm_coe_le_norm ⟨y, hy⟩).trans
    (norm_le_pi_norm (jet 𝕜 K m φ) w)

/-- A fixed-support distribution is a bounded linear functional of finitely many jets.
The extension to the ambient normed jet space is an application of Hahn–Banach. -/
theorem distribution_factorization {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    {Ω : Opens (Space d)} (T : DistributionSpace 𝕜 Ω) (K : Compacts (Space d))
    (hK : (K : Set (Space d)) ⊆ Ω) :
    ∃ m : ℕ, ∃ L : Jets 𝕜 K m →L[𝕜] 𝕜, ∀ φ : FixedSupport d 𝕜 K,
      L (jet 𝕜 K m φ) = T (stageInclusion 𝕜 hK φ) := by
  obtain ⟨C, hC, m, hbound⟩ := (localOrder d 𝕜 Ω T.toLinearMap).mp T.continuous K hK
  let J := jet 𝕜 K m
  let e := LinearEquiv.ofInjective J (jet_injective 𝕜 K m)
  let t : J.range →ₗ[𝕜] 𝕜 :=
    T.toLinearMap.comp ((stageInclusion 𝕜 hK).toLinearMap.comp e.symm.toLinearMap)
  have ht : ∀ z : J.range, ‖t z‖ ≤ C * ‖z‖ := by
    intro z
    have hz : J (e.symm z) = z.val := congrArg Subtype.val (e.apply_symm_apply z)
    exact (hbound (e.symm z)).trans
      (mul_le_mul_of_nonneg_left
        ((coordinateSupSeminorm_le_jet_norm 𝕜 K m (e.symm z)).trans_eq
          (congrArg norm hz)) hC)
  obtain ⟨L, hL⟩ := StrongDual.exists_extension J.range (t.mkContinuous C ht)
  refine ⟨m, L, fun φ => ?_⟩
  have h := hL (e φ)
  change L (J φ) = T (stageInclusion 𝕜 hK (e.symm (e φ))) at h
  simpa only [LinearEquiv.symm_apply_apply] using h

end FiniteJets

abbrev admissibleDomain : LocalConvolutionExpected.DomainType := @convolutionDomain
abbrev admissibleKernelTest : LocalConvolutionExpected.TestType := @convolutionTest
abbrev convolutionLocal : LocalConvolutionExpected.ConvolutionType := @localConvolution
abbrev partialKernel : LocalConvolutionExpected.KernelPartialType := @kernelPartial

theorem localConvolution_openDomain : LocalConvolutionExpected.OpenDomain := by
  intro d 𝕜 _ Ω ρ
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  exact ρ.hasCompactSupport.eventually_forall_of_forall_eventually fun z hz =>
    (continuous_fst.sub continuous_snd).continuousAt.eventually
      (Ω.isOpen.mem_nhds (hx z hz))

/-- Nearby kernels have their supports in one compact subset of Ω. -/
theorem localConvolution_commonSupport {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (x : Space d) (hx : x ∈ convolutionDomain Ω ρ) :
    ∃ V : Opens (Space d), x ∈ V ∧ (V : Set (Space d)) ⊆ convolutionDomain Ω ρ ∧
      ∃ K : Compacts (Space d), (K : Set (Space d)) ⊆ Ω ∧
        ∀ z ∈ V, tsupport (translatedKernel ρ z) ⊆ K := by
  obtain ⟨A, hAc, hxA, hAU⟩ :=
    exists_compact_subset (localConvolution_openDomain d 𝕜 Ω ρ) hx
  let B : Set (Space d) := (fun p : Space d × Space d => p.1 - p.2) ''
    (A ×ˢ tsupport ρ)
  have hBc : IsCompact B := (hAc.prod ρ.hasCompactSupport).image
    (continuous_fst.sub continuous_snd)
  refine ⟨⟨interior A, isOpen_interior⟩, hxA, interior_subset.trans hAU,
    ⟨B, hBc⟩, ?_, ?_⟩
  · rintro y ⟨⟨a, z⟩, ⟨ha, hz⟩, rfl⟩
    exact hAU ha z hz
  · intro z hz y hy
    have h : z - y ∈ tsupport ρ :=
      tsupport_comp_subset_preimage ρ (continuous_const.sub continuous_id) hy
    exact ⟨(z, z - y), ⟨interior_subset hz, h⟩, sub_sub_cancel z y⟩

/-- Coordinate derivatives of a reflected translate, including the empty word. -/
theorem partialWord_const_sub {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space d)
    (l : List (Fin d)) :
    partialWord (fun y => f (x - y)) l =
      fun y => (-1 : 𝕜) ^ l.length * partialWord f l (x - y) := by
  induction l with
  | nil => simp [partialWord]
  | cons i l ih =>
    ext y
    change fderiv ℝ (partialWord (fun y => f (x - y)) l) y (coordinateVector d i) = _
    rw [ih]
    have hder := (((partialWord_contDiff hf l).differentiable (by simp)) (x - y)).hasFDerivAt
    have hcomp := (hder.comp y ((hasFDerivAt_id y).const_sub x)).const_mul
      ((-1 : 𝕜) ^ l.length)
    have heq : fderiv ℝ (fun y => (-1 : 𝕜) ^ l.length * partialWord f l (x - y)) y =
        (-1 : 𝕜) ^ l.length • (fderiv ℝ (partialWord f l) (x - y)).comp
          (-ContinuousLinearMap.id ℝ (Space d)) := hcomp.fderiv
    rw [heq]
    simp [partialWord, pow_succ]

/-- The finite jet of a reflected translate, defined for every parameter x. -/
def translationJet {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (x : Space d) : FiniteJets.Jets 𝕜 K m :=
  fun a => CompactParameter.family K
    (fun p : Space d × Space d => (-1 : 𝕜) ^ a.1.val *
      partialWord ρ (List.ofFn a.2) (p.1 - p.2))
    ((contDiff_const.mul ((partialWord_contDiff ρ.contDiff (List.ofFn a.2)).comp
      (contDiff_fst.sub contDiff_snd))).continuous) x

theorem contDiff_translationJet {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) :
    ContDiff ℝ (⊤ : ℕ∞) (translationJet K m ρ) := by
  apply contDiff_pi.mpr
  intro a
  exact CompactParameter.contDiff_family K
    (contDiff_const.mul ((partialWord_contDiff ρ.contDiff (List.ofFn a.2)).comp
      (contDiff_fst.sub contDiff_snd)))

theorem translationJet_eq_jet {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (x : Space d) (φ : FixedSupport d 𝕜 K) (hφ : (φ : Space d → 𝕜) = fun y => ρ (x - y)) :
    translationJet K m ρ x = FiniteJets.jet 𝕜 K m φ := by
  funext a
  ext y
  rw [FiniteJets.jet_apply, ← partialWord_ofFn φ.contDiff a.2, hφ, partialWord_const_sub ρ.contDiff]
  simp only [List.length_ofFn]
  rfl

theorem partialWord_append {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Space d → 𝕜) (l l' : List (Fin d)) :
    partialWord f (l ++ l') = partialWord (partialWord f l') l := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.cons_append, partialWord, ih]

theorem partialWord_coordinate {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {f : Space d → 𝕜} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i : Fin d) (l : List (Fin d)) :
    partialWord (fun z => fderiv ℝ f z (coordinateVector d i)) l =
      fun z => fderiv ℝ (partialWord f l) z (coordinateVector d i) := by
  calc
    _ = partialWord f (l ++ [i]) := (partialWord_append f l [i]).symm
    _ = partialWord f ([i] ++ l) := partialWord_perm hf (List.perm_append_comm)
    _ = _ := rfl

theorem translationJet_coordinate_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (x : Space d) (i : Fin d) :
    fderiv ℝ (translationJet K m ρ) x (coordinateVector d i) =
      translationJet K m (testPartialWord ⊤ [i] ρ) x := by
  funext a
  ext y
  let ev : FiniteJets.Jets 𝕜 K m →L[ℝ] 𝕜 :=
    (ContinuousMap.evalCLM ℝ y).comp (ContinuousLinearMap.proj a)
  have h := ev.hasFDerivAt.comp x
    (((contDiff_translationJet K m ρ).differentiable (by simp)) x).hasFDerivAt
  have heq := congrArg (fun D : Space d →L[ℝ] 𝕜 => D (coordinateVector d i)) h.fderiv
  change fderiv ℝ (fun z => (-1 : 𝕜) ^ a.1.val *
      partialWord ρ (List.ofFn a.2) (z - (y : Space d))) x (coordinateVector d i) =
    (fderiv ℝ (translationJet K m ρ) x (coordinateVector d i)) a y at heq
  rw [← heq]
  have hder := (((partialWord_contDiff ρ.contDiff (List.ofFn a.2)).differentiable
    (by simp)) (x - (y : Space d))).hasFDerivAt
  have hpoint := (hder.comp x ((hasFDerivAt_id x).sub_const (y : Space d))).const_mul
    ((-1 : 𝕜) ^ a.1.val)
  have heq' : fderiv ℝ (fun z => (-1 : 𝕜) ^ a.1.val *
      partialWord ρ (List.ofFn a.2) (z - (y : Space d))) x =
      (-1 : 𝕜) ^ a.1.val • (fderiv ℝ (partialWord ρ (List.ofFn a.2))
        (x - (y : Space d))).comp (ContinuousLinearMap.id ℝ (Space d)) := hpoint.fderiv
  rw [heq']
  change (-1 : 𝕜) ^ a.1.val * fderiv ℝ (partialWord ρ (List.ofFn a.2))
    (x - (y : Space d)) (coordinateVector d i) =
    (-1 : 𝕜) ^ a.1.val * partialWord (testPartialWord ⊤ [i] ρ) (List.ofFn a.2)
      (x - (y : Space d))
  rw [testPartialWord_coe, show partialWord (ρ : Space d → 𝕜) [i] =
    (fun z => fderiv ℝ ρ z (coordinateVector d i)) from rfl,
    partialWord_coordinate ρ.contDiff]

theorem localConvolution_admissibleTest : LocalConvolutionExpected.AdmissibleTest := by
  intro d 𝕜 _ Ω ρ x hx y
  rfl

theorem localConvolution_pairing : LocalConvolutionExpected.Pairing := by
  intro d 𝕜 _ Ω T ρ x hx
  exact dite_eq_left hx

theorem localConvolution_eq_jetPairing {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (T : DistributionSpace 𝕜 Ω)
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (K : Compacts (Space d))
    (hK : (K : Set (Space d)) ⊆ Ω) (m : ℕ) (L : FiniteJets.Jets 𝕜 K m →L[𝕜] 𝕜)
    (hL : ∀ φ, L (FiniteJets.jet 𝕜 K m φ) = T (stageInclusion 𝕜 hK φ))
    (x : Space d) (hx : x ∈ convolutionDomain Ω ρ)
    (hs : tsupport (translatedKernel ρ x) ⊆ K) :
    localConvolution T ρ x = L (translationJet K m ρ x) := by
  let φ : FixedSupport d 𝕜 K := ContDiffMapSupportedIn.of_support_subset
    (translatedKernel ρ x).contDiff ((subset_tsupport _).trans hs)
  rw [translationJet_eq_jet K m ρ x φ rfl, hL,
    localConvolution_pairing d 𝕜 Ω T ρ x hx]
  congr 1

theorem localConvolution_smooth : LocalConvolutionExpected.Smooth := by
  intro d 𝕜 _ Ω T ρ x hx
  obtain ⟨V, hxV, hVU, K, hK, hs⟩ := localConvolution_commonSupport Ω ρ x hx
  obtain ⟨m, L, hL⟩ := FiniteJets.distribution_factorization 𝕜 T K hK
  have heq : localConvolution T ρ =ᶠ[𝓝 x] fun z => L (translationJet K m ρ z) := by
    filter_upwards [V.isOpen.mem_nhds hxV] with z hz
    exact localConvolution_eq_jetPairing T ρ K hK m L hL z (hVU hz) (hs z hz)
  have hat : ContDiffAt ℝ (⊤ : ℕ∞) (fun z => L (translationJet K m ρ z)) x :=
    ((L.restrictScalars ℝ).contDiff.comp (contDiff_translationJet K m ρ)).contDiffAt
  exact (hat.congr_of_eventuallyEq heq).contDiffWithinAt

/-- Taking any coordinate word derivative cannot enlarge topological support. -/
theorem testPartialWord_tsupport_subset {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Ω : Opens (Space d)) (l : List (Fin d)) (φ : TestSpace 𝕜 Ω) :
    tsupport (testPartialWord Ω l φ) ⊆ tsupport φ := by
  induction l with
  | nil => exact Subset.rfl
  | cons i l ih =>
    change tsupport (TestFunction.lineDerivCLM 𝕜 (k := ⊤) (coordinateVector d i)
      (testPartialWord Ω l φ)) ⊆ _
    have heq : (TestFunction.lineDerivCLM 𝕜 (k := ⊤) (coordinateVector d i)
        (testPartialWord Ω l φ) : Space d → 𝕜) =
        fun x => fderiv ℝ (testPartialWord Ω l φ) x (coordinateVector d i) := by
      ext x
      rw [TestFunction.lineDerivCLM_eq_fderivCLM,
        TestFunction.fderivCLM_apply_of_le _ (by simp)]
    rw [heq]
    exact (tsupport_comp_subset (map_zero (ContinuousLinearMap.apply ℝ 𝕜
      (coordinateVector d i))) _).trans ((tsupport_fderiv_subset ℝ).trans ih)

theorem localConvolution_kernelDerivative : LocalConvolutionExpected.KernelDerivative := by
  intro d 𝕜 _ α ρ
  exact ⟨fun x => congrFun (testPartialWord_coe ⊤ (α.sort (· ≤ ·)) ρ) x,
    testPartialWord_tsupport_subset ⊤ _ ρ⟩

theorem localConvolution_derivativeDomain : LocalConvolutionExpected.DerivativeDomain := by
  intro d 𝕜 _ Ω α ρ x hx z hz
  exact hx z ((localConvolution_kernelDerivative d 𝕜 α ρ).2 hz)

theorem translatedKernel_tsupport_mono {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {ρ σ : TestSpace 𝕜 (⊤ : Opens (Space d))}
    (hs : tsupport σ ⊆ tsupport ρ) (x : Space d) :
    tsupport (translatedKernel σ x) ⊆ tsupport (translatedKernel ρ x) := by
  change tsupport ((σ : Space d → 𝕜) ∘ Homeomorph.subLeft x) ⊆
    tsupport ((ρ : Space d → 𝕜) ∘ Homeomorph.subLeft x)
  rw [tsupport_comp_eq_preimage, tsupport_comp_eq_preimage]
  exact preimage_mono hs

theorem localConvolution_coordinate_derivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (T : DistributionSpace 𝕜 Ω)
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (i : Fin d)
    (x : Space d) (hx : x ∈ convolutionDomain Ω ρ) :
    fderiv ℝ (localConvolution T ρ) x (coordinateVector d i) =
      localConvolution T (testPartialWord ⊤ [i] ρ) x := by
  obtain ⟨V, hxV, hVU, K, hK, hs⟩ := localConvolution_commonSupport Ω ρ x hx
  obtain ⟨m, L, hL⟩ := FiniteJets.distribution_factorization 𝕜 T K hK
  have heq : localConvolution T ρ =ᶠ[𝓝 x] fun z => L (translationJet K m ρ z) := by
    filter_upwards [V.isOpen.mem_nhds hxV] with z hz
    exact localConvolution_eq_jetPairing T ρ K hK m L hL z (hVU hz) (hs z hz)
  have hder := (L.restrictScalars ℝ).hasFDerivAt.comp x
    (((contDiff_translationJet K m ρ).differentiable (by simp)) x).hasFDerivAt
  have hfx : fderiv ℝ (localConvolution T ρ) x =
      (L.restrictScalars ℝ).comp (fderiv ℝ (translationJet K m ρ) x) :=
    (hder.congr_of_eventuallyEq heq).fderiv
  rw [hfx, ContinuousLinearMap.comp_apply, translationJet_coordinate_derivative]
  symm
  apply localConvolution_eq_jetPairing T _ K hK m L hL x
  · intro z hz
    exact hx z (testPartialWord_tsupport_subset ⊤ [i] ρ hz)
  · exact (translatedKernel_tsupport_mono (testPartialWord_tsupport_subset ⊤ [i] ρ) x).trans
      (hs x hxV)

/-- All ordinary coordinate words can be moved onto the kernel. -/
theorem localConvolution_partialWord {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (T : DistributionSpace 𝕜 Ω)
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (l : List (Fin d)) :
    ∀ x ∈ convolutionDomain Ω ρ,
      partialWord (localConvolution T ρ) l x = localConvolution T (testPartialWord ⊤ l ρ) x := by
  induction l with
  | nil => intro x hx; rfl
  | cons i l ih =>
    intro x hx
    have heq : partialWord (localConvolution T ρ) l =ᶠ[𝓝 x]
        localConvolution T (testPartialWord ⊤ l ρ) := by
      filter_upwards [(localConvolution_openDomain d 𝕜 Ω ρ).mem_nhds hx] with z hz
      exact ih z hz
    change fderiv ℝ (partialWord (localConvolution T ρ) l) x (coordinateVector d i) = _
    rw [heq.fderiv_eq]
    apply localConvolution_coordinate_derivative T (testPartialWord ⊤ l ρ) i x
    intro z hz
    exact hx z (testPartialWord_tsupport_subset ⊤ l ρ hz)

theorem localConvolution_derivative : LocalConvolutionExpected.Derivative := by
  intro d 𝕜 _ Ω α T ρ x hx
  exact localConvolution_partialWord T ρ (α.sort (· ≤ ·)) x hx

/-- The required multi-index identity in order zero, without any smoothness premise. -/
theorem localConvolution_derivative_zero {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} (T : DistributionSpace 𝕜 Ω)
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (x : Space d) :
    multiPartial (localConvolution T ρ) (0 : MultiIndex d) x =
      localConvolution T (kernelPartial 0 ρ) x := by
  simp [multiPartial, kernelPartial, testPartialWord, partialWord]

theorem localConvolution_regularIntegral : LocalConvolutionExpected.RegularIntegral := by
  intro d 𝕜 _ Ω f hf ρ x hx
  rw [localConvolution_pairing d 𝕜 Ω _ ρ x hx, regular_pairing d 𝕜 Ω f hf]
  rfl

end P102.U4
