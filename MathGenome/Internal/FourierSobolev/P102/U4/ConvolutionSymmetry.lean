import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ConvolutionSymmetry
import MathGenome.Internal.FourierSobolev.P102.U4.LocalConvolution
import MathGenome.Internal.FourierSobolev.P102.U4.CompactSupportExtension
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular

import MathGenome.Internal.FourierSobolev.P102.U4.DistributionConvolution
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions Topology Pointwise

namespace P102.U4
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace DistributionInterchange

section DirectionalWords
variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Ordinary repeated derivatives in a list of constant directions. -/
def directionalWord (f : E → F) : List E → E → F
  | [] => f
  | v :: l => fun x => fderiv ℝ (directionalWord f l) x v

theorem directionalWord_contDiff {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (l : List E) :
    ContDiff ℝ (⊤ : ℕ∞) (directionalWord f l) := by
  induction l with
  | nil => exact hf
  | cons v l ih => exact (ih.fderiv_right (by simp)).clm_apply contDiff_const

theorem directionalWord_append (f : E → F) (l l' : List E) :
    directionalWord f (l ++ l') = directionalWord (directionalWord f l') l := by
  induction l with
  | nil => rfl
  | cons v l ih => simp only [List.cons_append, directionalWord, ih]

theorem directionalWord_swap {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v w : E) (l : List E) :
    directionalWord f (v :: w :: l) = directionalWord f (w :: v :: l) := by
  ext x
  have hg := directionalWord_contDiff hf l
  have hd : DifferentiableAt ℝ (fderiv ℝ (directionalWord f l)) x :=
    (hg.fderiv_right (m := 1) (by simp)).differentiable one_ne_zero x
  simp only [directionalWord]
  rw [fderiv_clm_apply hd (differentiableAt_const w),
    fderiv_clm_apply hd (differentiableAt_const v)]
  simpa only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using
    (hg.contDiffAt.isSymmSndFDerivAt (by simp) v w)

theorem directionalWord_perm {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {l l' : List E} (h : l.Perm l') :
    directionalWord f l = directionalWord f l' := by
  induction h with
  | nil => rfl
  | cons v h ih => simp only [directionalWord, ih]
  | swap v w l => exact directionalWord_swap hf w v l
  | trans h h' ih ih' => exact ih.trans ih'

theorem directionalWord_postcomp {f : E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : F →L[ℝ] G) (l : List E) :
    directionalWord (fun x => L (f x)) l = fun x => L (directionalWord f l x) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    ext x
    simp only [directionalWord, ih]
    exact congrArg (fun D : E →L[ℝ] G => D v)
      (L.hasFDerivAt.comp x
        (((directionalWord_contDiff hf l).differentiable (by simp)) x).hasFDerivAt).fderiv

theorem directionalWord_tsupport_subset {f : E → F}
    (l : List E) : tsupport (directionalWord f l) ⊆ tsupport f := by
  induction l with
  | nil => exact Subset.rfl
  | cons v l ih =>
    exact (tsupport_comp_subset (map_zero (ContinuousLinearMap.apply ℝ F v)) _).trans
      ((tsupport_fderiv_subset ℝ).trans ih)

theorem directionalWord_comp_linear {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (A : D →L[ℝ] E) (l : List D) :
    directionalWord (fun x => f (A x)) l = fun x => directionalWord f (l.map A) (A x) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    ext x
    simp only [directionalWord, ih, List.map_cons]
    have h := (((directionalWord_contDiff hf (l.map A)).differentiable
      (by simp)) (A x)).hasFDerivAt.comp x A.hasFDerivAt
    exact congrArg (fun D : D →L[ℝ] F => D v) h.fderiv

end DirectionalWords

section ProductWords
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Differentiate a vertical slice by differentiating in the vertical directions. -/
theorem directionalWord_rightSlice {f : E × E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : E) (l : List E) :
    directionalWord (fun y => f (x, y)) l =
      fun y => directionalWord f (l.map (fun v => (0, v))) (x, y) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    ext y
    simp only [directionalWord, ih, List.map_cons]
    have h := (((directionalWord_contDiff hf (l.map (fun v => (0, v)))).differentiable
      (by simp)) (x, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
    exact congrArg (fun D : E →L[ℝ] F => D v) h.fderiv

/-- The corresponding horizontal-slice identity. -/
theorem directionalWord_leftSlice {f : E × E → F}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (y : E) (l : List E) :
    directionalWord (fun x => f (x, y)) l =
      fun x => directionalWord f (l.map (fun v => (v, 0))) (x, y) := by
  induction l with
  | nil => rfl
  | cons v l ih =>
    ext x
    simp only [directionalWord, ih, List.map_cons]
    have h := (((directionalWord_contDiff hf (l.map (fun v => (v, 0)))).differentiable
      (by simp)) (x, y)).hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y)
    exact congrArg (fun D : E →L[ℝ] F => D v) h.fderiv

end ProductWords

/-- The coordinate-word notation agrees with derivatives in coordinate vectors. -/
theorem partialWord_eq_directionalWord {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Space d → 𝕜) (l : List (Fin d)) :
    partialWord f l = directionalWord f (l.map (coordinateVector d)) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [partialWord, directionalWord, List.map_cons, ih]

/-- The finite jet in the vertical variable, with horizontal variable as parameter. -/
def rightJet {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) (f : Space d × Space d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space d) : FiniteJets.Jets 𝕜 K m :=
  fun a => CompactParameter.family K
    (directionalWord f ((List.ofFn a.2).map (fun i => (0, coordinateVector d i))))
    (directionalWord_contDiff hf _).continuous x

theorem rightJet_contDiff {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) (f : Space d × Space d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (rightJet K m f hf) := by
  exact contDiff_pi.mpr fun a =>
    CompactParameter.contDiff_family K (directionalWord_contDiff hf _)

/-- The jet family is the ordinary jet of every slice supported in K. -/
theorem rightJet_eq {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) (f : Space d × Space d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : Space d) (φ : FixedSupport d 𝕜 K)
    (hφ : (φ : Space d → 𝕜) = fun y => f (x, y)) :
    rightJet K m f hf x = FiniteJets.jet 𝕜 K m φ := by
  funext a
  ext y
  rw [FiniteJets.jet_apply, ← partialWord_ofFn φ.contDiff a.2,
    partialWord_eq_directionalWord, hφ, directionalWord_rightSlice hf]
  simp only [List.map_map]
  rfl

/-- Differentiation of a finite jet in its parameter is pointwise differentiation.
Both groups of directions are retained explicitly for the eventual interchange. -/
theorem rightJet_directionalWord {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (K : Compacts (Space d)) (m : ℕ) (f : Space d × Space d → 𝕜)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (l : List (Space d)) (x : Space d)
    (a : FiniteJets.Word d m) (y : K) :
    directionalWord (rightJet K m f hf) l x a y =
      directionalWord f (l.map (fun v => (v, 0)) ++
        (List.ofFn a.2).map (fun i => (0, coordinateVector d i))) (x, y) := by
  let ev : FiniteJets.Jets 𝕜 K m →L[ℝ] 𝕜 :=
    (ContinuousMap.evalCLM ℝ y).comp (ContinuousLinearMap.proj a)
  have h := congrFun (directionalWord_postcomp (rightJet_contDiff K m f hf) ev l) x
  change directionalWord
    (fun z => directionalWord f ((List.ofFn a.2).map
      (fun i => (0, coordinateVector d i))) (z, y)) l x =
    directionalWord (rightJet K m f hf) l x a y at h
  rw [directionalWord_leftSlice (directionalWord_contDiff hf _),
    ← directionalWord_append] at h
  exact h.symm

/-- The support of every vertical slice lies in the same compact projection. -/
theorem rightSlice_tsupport_subset {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Φ : ProductTests d 𝕜) (x : Space d) :
    tsupport (productRightSlice Φ x) ⊆ Prod.snd '' tsupport Φ := by
  apply closure_minimal
  · intro y hy
    exact ⟨(x, y), subset_tsupport Φ hy, rfl⟩
  · exact (Φ.hasCompactSupport.image continuous_snd).isClosed

/-- Applying any distribution to the slices of a two-variable test gives a test.
There is no compact-support assumption on the distribution. -/
theorem rightPairing_isTest {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (Φ : ProductTests d 𝕜) :
    ∃ ψ : WholeTests d 𝕜, ∀ x, ψ x = S (productRightSlice Φ x) := by
  let K : Compacts (Space d) := ⟨Prod.snd '' tsupport Φ,
    Φ.hasCompactSupport.image continuous_snd⟩
  obtain ⟨m, L, hL⟩ := FiniteJets.distribution_factorization 𝕜 S K (subset_univ _)
  have heq : (fun x => S (productRightSlice Φ x)) = fun x => L (rightJet K m Φ Φ.contDiff x) := by
    funext x
    let φ : FixedSupport d 𝕜 K := ContDiffMapSupportedIn.of_support_subset
      (productRightSlice Φ x).contDiff ((subset_tsupport _).trans (rightSlice_tsupport_subset Φ x))
    rw [rightJet_eq K m Φ Φ.contDiff x φ rfl, hL]
    rfl
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => S (productRightSlice Φ x)) := by
    rw [heq]
    exact (L.restrictScalars ℝ).contDiff.comp (rightJet_contDiff K m Φ Φ.contDiff)
  have hcompact : HasCompactSupport (fun x => S (productRightSlice Φ x)) := by
    apply HasCompactSupport.intro (Φ.hasCompactSupport.image continuous_fst)
    intro x hx
    have hzero : productRightSlice Φ x = 0 := by
      ext y
      by_contra h
      exact hx ⟨(x, y), subset_tsupport Φ h, rfl⟩
    rw [hzero, map_zero]
  exact ⟨⟨_, hsmooth, hcompact, subset_univ _⟩, fun _ => rfl⟩

/-- Interchanging the two coordinates preserves the space of product tests. -/
def swapTest {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Φ : ProductTests d 𝕜) : ProductTests d 𝕜 where
  toFun p := Φ p.swap
  contDiff' := Φ.contDiff.comp (contDiff_snd.prodMk contDiff_fst)
  hasCompactSupport' := Φ.hasCompactSupport.comp_homeomorph (Homeomorph.prodComm _ _)
  tsupport_subset' := subset_univ _

/-- The analogous assertion for horizontal slices. -/
theorem leftPairing_isTest {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (T : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (Φ : ProductTests d 𝕜) :
    ∃ θ : WholeTests d 𝕜, ∀ y, θ y = T (productLeftSlice Φ y) := by
  obtain ⟨θ, hθ⟩ := rightPairing_isTest T (swapTest Φ)
  refine ⟨θ, fun y => ?_⟩
  rw [hθ]
  congr 1

/-- All derivatives of an inner distribution pairing are obtained by applying
its fixed finite-jet functional to the corresponding parameter derivatives. -/
theorem rightPairing_directionalWord {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (Φ : ProductTests d 𝕜)
    (K : Compacts (Space d)) (hK : Prod.snd '' tsupport Φ ⊆ K)
    (m : ℕ) (L : FiniteJets.Jets 𝕜 K m →L[𝕜] 𝕜)
    (hL : ∀ φ, L (FiniteJets.jet 𝕜 K m φ) = S (stageInclusion 𝕜 (subset_univ _) φ))
    (ψ : WholeTests d 𝕜) (hψ : ∀ x, ψ x = S (productRightSlice Φ x))
    (l : List (Space d)) (x : Space d) :
    directionalWord ψ l x = L (fun a =>
      ⟨fun y : K => directionalWord Φ (l.map (fun v => (v, 0)) ++
        (List.ofFn a.2).map (fun i => (0, coordinateVector d i))) (x, y),
       (directionalWord_contDiff Φ.contDiff _).continuous.comp
         (continuous_const.prodMk continuous_subtype_val)⟩) := by
  have heq : (ψ : Space d → 𝕜) = fun x => L (rightJet K m Φ Φ.contDiff x) := by
    funext x
    let φ : FixedSupport d 𝕜 K := ContDiffMapSupportedIn.of_support_subset
      (productRightSlice Φ x).contDiff
        ((subset_tsupport _).trans ((rightSlice_tsupport_subset Φ x).trans hK))
    rw [hψ, rightJet_eq K m Φ Φ.contDiff x φ rfl, hL]
    rfl
  rw [heq]
  have hp := congrFun (directionalWord_postcomp
    (rightJet_contDiff K m Φ Φ.contDiff) (L.restrictScalars ℝ) l) x
  change directionalWord (fun x => L (rightJet K m Φ Φ.contDiff x)) l x =
    L (directionalWord (rightJet K m Φ Φ.contDiff) l x) at hp
  rw [hp]
  congr 1
  funext a
  ext y
  exact rightJet_directionalWord K m Φ Φ.contDiff l x a y

namespace CompactFunctionals
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [CompactSpace Y] {𝕜 : Type} [RCLike 𝕜]

/-- A separated continuous function on a product. -/
def separated (f : C(X, 𝕜)) (g : C(Y, 𝕜)) : C(X × Y, 𝕜) :=
  ⟨fun p => f p.1 * g p.2, (f.continuous.comp continuous_fst).mul
    (g.continuous.comp continuous_snd)⟩

def separatedSpan : Submodule 𝕜 C(X × Y, 𝕜) :=
  Submodule.span 𝕜 {h | ∃ f g, h = separated f g}

omit [CompactSpace X] [CompactSpace Y] in
theorem separated_mem (f : C(X, 𝕜)) (g : C(Y, 𝕜)) :
    separated f g ∈ separatedSpan := Submodule.subset_span ⟨f, g, rfl⟩

theorem separatedSpan_mul {f g : C(X × Y, 𝕜)}
    (hf : f ∈ separatedSpan) (hg : g ∈ separatedSpan) : f * g ∈ separatedSpan := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, b, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨c, d, rfl⟩ := hg
      have he : separated a b * separated c d = separated (a * c) (b * d) := by
        ext p; simp only [separated, ContinuousMap.coe_mk, ContinuousMap.mul_apply]; ring
      rw [he]
      exact separated_mem _ _
    | zero => simp
    | add f g hf hg ihf ihg =>
      simpa only [mul_add] using (separatedSpan (𝕜 := 𝕜)).add_mem ihf ihg
    | smul c f hf ih =>
      simpa only [mul_smul_comm] using (separatedSpan (𝕜 := 𝕜)).smul_mem c ih
  | zero => simp
  | add f g hf hg ihf ihg =>
    simpa only [add_mul] using (separatedSpan (𝕜 := 𝕜)).add_mem ihf ihg
  | smul c f hf ih =>
    simpa only [smul_mul_assoc] using (separatedSpan (𝕜 := 𝕜)).smul_mem c ih

theorem separatedSpan_star {f : C(X × Y, 𝕜)}
    (hf : f ∈ separatedSpan) : star f ∈ separatedSpan := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, b, rfl⟩ := hf
    have he : star (separated a b) = separated (star a) (star b) := by
      ext p
      simp [separated]
    rw [he]
    exact separated_mem _ _
  | zero => simp
  | add f g hf hg ihf ihg =>
    simpa only [star_add] using (separatedSpan (𝕜 := 𝕜)).add_mem ihf ihg
  | smul c f hf ih =>
    simpa only [star_smul] using (separatedSpan (𝕜 := 𝕜)).smul_mem (star c) ih

/-- Finite sums of separated functions form a unital star subalgebra. -/
def separatedAlgebra : StarSubalgebra 𝕜 C(X × Y, 𝕜) where
  carrier := (separatedSpan (X := X) (Y := Y) (𝕜 := 𝕜) : Set C(X × Y, 𝕜))
  zero_mem' := separatedSpan.zero_mem
  add_mem' := separatedSpan.add_mem
  mul_mem' := separatedSpan_mul
  one_mem' := by
    have he : separated (1 : C(X, 𝕜)) (1 : C(Y, 𝕜)) = 1 := by
      ext p; simp [separated]
    exact he ▸ separated_mem (1 : C(X, 𝕜)) (1 : C(Y, 𝕜))
  algebraMap_mem' c := by
    have he : separated (ContinuousMap.const X c) (1 : C(Y, 𝕜)) = algebraMap 𝕜 C(X × Y, 𝕜) c := by
      ext p; simp [separated]
    exact he ▸ separated_mem (ContinuousMap.const X c) (1 : C(Y, 𝕜))
  star_mem' := separatedSpan_star

/-- Apply a bounded functional to the vertical continuous slices. -/
def applyRight (M : C(Y, 𝕜) →L[𝕜] 𝕜) : C(X × Y, 𝕜) →L[𝕜] C(X, 𝕜) := by
  let A : C(X × Y, 𝕜) →ₗ[𝕜] C(X, 𝕜) :=
    { toFun := fun f => ⟨fun x => M (f.curry x), M.continuous.comp f.curry.continuous⟩
      map_add' := by
        intro f g; ext x
        change M ((f + g).curry x) = M (f.curry x) + M (g.curry x)
        rw [show (f + g).curry x = f.curry x + g.curry x by ext y; rfl, map_add]
      map_smul' := by
        intro c f; ext x
        change M ((c • f).curry x) = c • M (f.curry x)
        rw [ContinuousMap.curry_smul_apply, map_smul] }
  refine A.mkContinuous ‖M‖ (fun f => ?_)
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro x
  apply (M.le_opNorm _).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg M)
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro y
  exact f.norm_coe_le_norm (x, y)

/-- Coordinate interchange as a bounded linear map. -/
def flip : C(X × Y, 𝕜) →L[𝕜] C(Y × X, 𝕜) := by
  let A : C(X × Y, 𝕜) →ₗ[𝕜] C(Y × X, 𝕜) :=
    { toFun := fun f => f.comp ⟨Prod.swap, continuous_swap⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine A.mkContinuous 1 (fun f => ?_)
  rw [one_mul]
  exact (ContinuousMap.norm_le _ (norm_nonneg _)).mpr fun p => f.norm_coe_le_norm p.swap

theorem applyRight_separated (M : C(Y, 𝕜) →L[𝕜] 𝕜)
    (f : C(X, 𝕜)) (g : C(Y, 𝕜)) : applyRight M (separated f g) = (M g) • f := by
  ext x
  change M ((separated f g).curry x) = M g • f x
  have he : (separated f g).curry x = f x • g := by ext y; rfl
  rw [he, map_smul]
  exact mul_comm _ _

variable [T35Space X] [T35Space Y]

/-- Stone–Weierstrass applies to the algebra of separated continuous functions. -/
theorem separatedAlgebra_separates :
    (separatedAlgebra (X := X) (Y := Y) (𝕜 := 𝕜)).SeparatesPoints := by
  intro p q hpq
  by_cases hx : p.1 = q.1
  · have hy : p.2 ≠ q.2 := fun h => hpq (Prod.ext hx h)
    obtain ⟨g, hg, hne⟩ := separatesPoints_continuous_of_t35Space hy
    let g' : C(Y, 𝕜) := ⟨fun y => (g y : 𝕜), RCLike.continuous_ofReal.comp hg⟩
    refine ⟨_, ⟨separated 1 g', ⟨separated_mem _ _, rfl⟩⟩, ?_⟩
    simpa [separated, g'] using (RCLike.ofReal_injective.ne hne : (g p.2 : 𝕜) ≠ (g q.2 : 𝕜))
  · obtain ⟨f, hf, hne⟩ := separatesPoints_continuous_of_t35Space hx
    let f' : C(X, 𝕜) := ⟨fun x => (f x : 𝕜), RCLike.continuous_ofReal.comp hf⟩
    refine ⟨_, ⟨separated f' 1, ⟨separated_mem _ _, rfl⟩⟩, ?_⟩
    simpa [separated, f'] using (RCLike.ofReal_injective.ne hne : (f p.1 : 𝕜) ≠ (f q.1 : 𝕜))

/-- Bounded scalar functionals on compact continuous-function spaces commute.
This is proved by density, and is not an assumed Fubini theorem. -/
theorem interchange (L : C(X, 𝕜) →L[𝕜] 𝕜) (M : C(Y, 𝕜) →L[𝕜] 𝕜)
    (f : C(X × Y, 𝕜)) :
    L (applyRight M f) = M (applyRight L (flip f)) := by
  let P := L.comp (applyRight M)
  let Q := M.comp ((applyRight L).comp flip)
  have hseparated (a : C(X, 𝕜)) (b : C(Y, 𝕜)) :
      P (separated a b) = Q (separated a b) := by
    change L (applyRight M (separated a b)) = M (applyRight L (flip (separated a b)))
    have he : flip (separated a b) = separated b a := by
      ext p; exact mul_comm _ _
    rw [he, applyRight_separated, applyRight_separated, map_smul, map_smul]
    exact mul_comm _ _
  have hspan : ∀ g ∈ separatedSpan, P g = Q g := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg => obtain ⟨a, b, rfl⟩ := hg; exact hseparated a b
    | zero => rw [map_zero, map_zero]
    | add a b ha hb iha ihb => rw [map_add, map_add, iha, ihb]
    | smul c a ha ih => rw [map_smul, map_smul, ih]
  have hd := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (separatedAlgebra (X := X) (Y := Y) (𝕜 := 𝕜)) separatedAlgebra_separates
  have hmem : f ∈ closure (separatedSpan (X := X) (Y := Y) (𝕜 := 𝕜) : Set _) := by
    change f ∈ (separatedAlgebra (X := X) (Y := Y) (𝕜 := 𝕜)).topologicalClosure
    rw [hd]; trivial
  exact (closure_minimal hspan (isClosed_eq P.continuous Q.continuous)) hmem

/-- The same commutation for finite tuples of compact-function spaces. -/
theorem piInterchange {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : (ι → C(X, 𝕜)) →L[𝕜] 𝕜) (M : (κ → C(Y, 𝕜)) →L[𝕜] 𝕜)
    (F : ι → κ → C(X × Y, 𝕜)) (A : ι → C(X, 𝕜)) (B : κ → C(Y, 𝕜))
    (hA : ∀ a x, A a x = M (fun b => (F a b).curry x))
    (hB : ∀ b y, B b y = L (fun a => (flip (F a b)).curry y)) :
    L A = M B := by
  classical
  let La (a : ι) := L.comp (ContinuousLinearMap.single 𝕜 (fun _ => C(X, 𝕜)) a)
  let Mb (b : κ) := M.comp (ContinuousLinearMap.single 𝕜 (fun _ => C(Y, 𝕜)) b)
  have hA' (a : ι) : A a = ∑ b, applyRight (Mb b) (F a b) := by
    ext x
    rw [hA]
    rw [ContinuousMap.sum_apply]
    change M (fun b => (F a b).curry x) = ∑ b, Mb b ((F a b).curry x)
    exact (ContinuousLinearMap.sum_comp_single 𝕜 (fun _ => C(Y, 𝕜)) M
      (fun b => (F a b).curry x)).symm
  have hB' (b : κ) : B b = ∑ a, applyRight (La a) (flip (F a b)) := by
    ext y
    rw [hB, ContinuousMap.sum_apply]
    change L (fun a => (flip (F a b)).curry y) = ∑ a, La a ((flip (F a b)).curry y)
    exact (ContinuousLinearMap.sum_comp_single 𝕜 (fun _ => C(X, 𝕜)) L
      (fun a => (flip (F a b)).curry y)).symm
  calc
    L A = ∑ a, La a (A a) := (ContinuousLinearMap.sum_comp_single 𝕜 (fun _ => C(X, 𝕜)) L A).symm
    _ = ∑ a, ∑ b, La a (applyRight (Mb b) (F a b)) := by simp_rw [hA', map_sum]
    _ = ∑ a, ∑ b, Mb b (applyRight (La a) (flip (F a b))) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_congr rfl fun b _ => interchange (La a) (Mb b) (F a b)
    _ = ∑ b, ∑ a, Mb b (applyRight (La a) (flip (F a b))) := Finset.sum_comm
    _ = ∑ b, Mb b (B b) := by simp_rw [hB', map_sum]
    _ = M B := ContinuousLinearMap.sum_comp_single 𝕜 (fun _ => C(Y, 𝕜)) M B

end CompactFunctionals

/-- Horizontal support of the inner pairing is controlled by the test support. -/
theorem rightPairing_tsupport_subset {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (Φ : ProductTests d 𝕜)
    (ψ : WholeTests d 𝕜) (hψ : ∀ x, ψ x = S (productRightSlice Φ x)) :
    tsupport ψ ⊆ Prod.fst '' tsupport Φ := by
  apply closure_minimal
  · intro x hx
    by_contra h
    have hz : productRightSlice Φ x = 0 := by
      ext y
      by_contra hy
      exact h ⟨(x, y), subset_tsupport Φ hy, rfl⟩
    exact hx (by rw [hψ, hz, map_zero])
  · exact (Φ.hasCompactSupport.image continuous_fst).isClosed

theorem swapTest_tsupport_subset {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Φ : ProductTests d 𝕜) : tsupport (swapTest Φ) ⊆ Prod.swap ⁻¹' tsupport Φ :=
  tsupport_comp_subset_preimage Φ continuous_swap

theorem directionalWord_swapTest {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (Φ : ProductTests d 𝕜) (l : List (Space d × Space d)) (p : Space d × Space d) :
    directionalWord (swapTest Φ) l p = directionalWord Φ (l.map Prod.swap) p.swap := by
  exact congrFun (directionalWord_comp_linear Φ.contDiff
    (ContinuousLinearEquiv.prodComm ℝ (Space d) (Space d)).toContinuousLinearMap l) p

/-- Interchange of arbitrary distributions on a smooth compactly supported test.
Finite local orders reduce it to the proved compact-functional commutation. -/
theorem interchange : ConvolutionSymmetryExpected.Interchange := by
  intro d 𝕜 _ T S Φ
  obtain ⟨ψ, hψ⟩ := rightPairing_isTest S Φ
  obtain ⟨θ, hθ⟩ := leftPairing_isTest T Φ
  refine ⟨ψ, θ, hψ, hθ, ?_⟩
  let K : Compacts (Space d) := ⟨Prod.fst '' tsupport Φ, Φ.hasCompactSupport.image continuous_fst⟩
  let J : Compacts (Space d) := ⟨Prod.snd '' tsupport Φ, Φ.hasCompactSupport.image continuous_snd⟩
  have hsK : Prod.snd '' tsupport (swapTest Φ) ⊆ K := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨p.swap, swapTest_tsupport_subset Φ hp, rfl⟩
  have hsJ : Prod.fst '' tsupport (swapTest Φ) ⊆ J := by
    rintro x ⟨p, hp, rfl⟩
    exact ⟨p.swap, swapTest_tsupport_subset Φ hp, rfl⟩
  have hθ' : ∀ y, θ y = T (productRightSlice (swapTest Φ) y) := by
    intro y
    rw [hθ]
    congr 1
  let ψK : FixedSupport d 𝕜 K := ContDiffMapSupportedIn.of_support_subset ψ.contDiff
    ((subset_tsupport _).trans (rightPairing_tsupport_subset S Φ ψ hψ))
  let θJ : FixedSupport d 𝕜 J := ContDiffMapSupportedIn.of_support_subset θ.contDiff
    ((subset_tsupport _).trans ((rightPairing_tsupport_subset T (swapTest Φ) θ hθ').trans hsJ))
  obtain ⟨m, L, hL⟩ := FiniteJets.distribution_factorization 𝕜 T K (subset_univ _)
  obtain ⟨n, M, hM⟩ := FiniteJets.distribution_factorization 𝕜 S J (subset_univ _)
  let F : FiniteJets.Word d m → FiniteJets.Word d n → C(K × J, 𝕜) := fun a b =>
    ⟨fun p => directionalWord Φ
      ((List.ofFn a.2).map (fun i => (coordinateVector d i, 0)) ++
       (List.ofFn b.2).map (fun i => (0, coordinateVector d i))) (p.1, p.2),
      (directionalWord_contDiff Φ.contDiff _).continuous.comp
        ((continuous_subtype_val.comp continuous_fst).prodMk
         (continuous_subtype_val.comp continuous_snd))⟩
  have hA (a : FiniteJets.Word d m) (x : K) :
      FiniteJets.jet 𝕜 K m ψK a x = M (fun b => (F a b).curry x) := by
    rw [FiniteJets.jet_apply]
    change iteratedFDeriv ℝ a.1.val ψ x (fun j => coordinateVector d (a.2 j)) = _
    rw [← partialWord_ofFn ψ.contDiff a.2, partialWord_eq_directionalWord,
      rightPairing_directionalWord S Φ J (Subset.rfl) n M hM ψ hψ]
    congr 1
    funext b
    ext y
    simp only [List.map_map]
    rfl
  have hB (b : FiniteJets.Word d n) (y : J) :
      FiniteJets.jet 𝕜 J n θJ b y = L (fun a => (CompactFunctionals.flip (F a b)).curry y) := by
    rw [FiniteJets.jet_apply]
    change iteratedFDeriv ℝ b.1.val θ y (fun j => coordinateVector d (b.2 j)) = _
    rw [← partialWord_ofFn θ.contDiff b.2, partialWord_eq_directionalWord,
      rightPairing_directionalWord T (swapTest Φ) K hsK m L hL θ hθ']
    congr 1
    funext a
    ext x
    change directionalWord (swapTest Φ)
      (((List.ofFn b.2).map (coordinateVector d)).map (fun v => (v, 0)) ++
       (List.ofFn a.2).map (fun i => (0, coordinateVector d i))) (y, x) =
      directionalWord Φ
        ((List.ofFn a.2).map (fun i => (coordinateVector d i, 0)) ++
         (List.ofFn b.2).map (fun i => (0, coordinateVector d i))) (x, y)
    rw [directionalWord_swapTest]
    simp only [List.map_append, List.map_map, Prod.swap_prod_mk]
    exact congrFun (directionalWord_perm Φ.contDiff (List.perm_append_comm)) (x, y)
  have he := CompactFunctionals.piInterchange L M F
    (FiniteJets.jet 𝕜 K m ψK) (FiniteJets.jet 𝕜 J n θJ) hA hB
  rw [hL, hM] at he
  exact he

end DistributionInterchange
namespace ConvolutionSymmetryProof
variable {d : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- The compact two-variable test used to compare the two orders of pairing. -/
def cutoffAddition (φ χ η : WholeTests d 𝕜) : ProductTests d 𝕜 where
  toFun p := η p.1 * χ p.2 * φ (p.1 + p.2)
  contDiff' := ((η.contDiff.comp contDiff_fst).mul
    (χ.contDiff.comp contDiff_snd)).mul (φ.contDiff.comp (contDiff_fst.add contDiff_snd))
  hasCompactSupport' := HasCompactSupport.intro (η.hasCompactSupport.prod χ.hasCompactSupport) (by
    intro p hp
    by_cases hx : p.1 ∈ tsupport η
    · have hy : p.2 ∉ tsupport χ := fun hy => hp ⟨hx, hy⟩
      simp [image_eq_zero_of_notMem_tsupport hy]
    · simp [image_eq_zero_of_notMem_tsupport hx])
  tsupport_subset' := subset_univ _

theorem cutoffAddition_right (S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (φ χ η : WholeTests d 𝕜) (hχ : IsSupportCutoff S χ) (x : Space d) :
    S (productRightSlice (cutoffAddition φ χ η) x) = η x * convolutionInner S φ x := by
  obtain ⟨U, hU, hχU⟩ := hχ
  have he : S (productRightSlice (cutoffAddition φ χ η) x) = S (η x • additionTest φ x) := by
    apply supportLocality d 𝕜 ⊤ S _ _ U U.isOpen hU
    intro y hy
    change η x * χ y * φ (x + y) = η x * φ (x + y)
    rw [hχU y hy, mul_one]
  rw [he, map_smul]
  rfl

theorem cutoffAddition_left (T : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (φ χ η : WholeTests d 𝕜) (hη : IsSupportCutoff T η) (y : Space d) :
    T (productLeftSlice (cutoffAddition φ χ η) y) = χ y * convolutionInner T φ y := by
  obtain ⟨U, hU, hηU⟩ := hη
  have he : T (productLeftSlice (cutoffAddition φ χ η) y) = T (χ y • additionTest φ y) := by
    apply supportLocality d 𝕜 ⊤ T _ _ U U.isOpen hU
    intro x hx
    change η x * χ y * φ (x + y) = χ y * φ (y + x)
    rw [hηU x hx, one_mul, add_comm x y]
  rw [he, map_smul]
  rfl

/-- The right-compact defining formula uniquely determines the convolution. -/
theorem compact_comm (C : ConvolutionFamily d 𝕜) (hC : ConvolutionLaws C)
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hT : IsCompact (relativeSupport T)) (hS : IsCompact (relativeSupport S)) :
    C T S (Or.inr hS) = C S T (Or.inr hT) := by
  obtain ⟨χ, hχ⟩ := exists_supportCutoff S hS
  obtain ⟨η, hη⟩ := exists_supportCutoff T hT
  ext φ
  obtain ⟨u, hu, hCu⟩ := hC.1 T S hS φ
  obtain ⟨v, hv, hCv⟩ := hC.1 S T hT φ
  obtain ⟨ψ, θ, hψ, hθ, he⟩ :=
    DistributionInterchange.interchange d 𝕜 T S (cutoffAddition φ χ η)
  have hTu : T ψ = T u := by
    obtain ⟨U, hU, hηU⟩ := hη
    apply supportLocality d 𝕜 ⊤ T ψ u U U.isOpen hU
    intro x hx
    rw [hψ, cutoffAddition_right S φ χ η hχ, hηU x hx, one_mul, hu]
  have hSv : S θ = S v := by
    obtain ⟨U, hU, hχU⟩ := hχ
    apply supportLocality d 𝕜 ⊤ S θ v U U.isOpen hU
    intro y hy
    rw [hθ, cutoffAddition_left T φ χ η hη, hχU y hy, one_mul, hv]
  rw [hCu, hCv, ← hTu, ← hSv]
  exact he

/-- Extend the right-compact construction to every pair with one compact factor. -/
def symmetrize (C : ConvolutionFamily d 𝕜) : ConvolutionFamily d 𝕜 := by
  classical
  exact fun T S h => if hS : IsCompact (relativeSupport S) then C T S (Or.inr hS)
    else C S T (Or.inr (h.resolve_right hS))

theorem symmetrize_right (C : ConvolutionFamily d 𝕜)
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S))
    (h : IsCompact (relativeSupport T) ∨ IsCompact (relativeSupport S)) :
    symmetrize C T S h = C T S (Or.inr hS) := by
  simp only [symmetrize, dite_eq_left hS]

theorem symmetrize_left (C : ConvolutionFamily d 𝕜) (hC : ConvolutionLaws C)
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hT : IsCompact (relativeSupport T))
    (h : IsCompact (relativeSupport T) ∨ IsCompact (relativeSupport S)) :
    symmetrize C T S h = C S T (Or.inr hT) := by
  classical
  by_cases hS : IsCompact (relativeSupport S)
  · rw [symmetrize_right C T S hS h]
    exact compact_comm C hC T S hT hS
  · simp only [symmetrize, dite_eq_right hS]

theorem symmetrize_comm (C : ConvolutionFamily d 𝕜) (hC : ConvolutionLaws C)
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (h : IsCompact (relativeSupport T) ∨ IsCompact (relativeSupport S)) :
    symmetrize C T S h = symmetrize C S T h.symm := by
  rcases h with hT | hS
  · rw [symmetrize_left C hC T S hT, symmetrize_right C S T hT]
  · rw [symmetrize_right C T S hS, symmetrize_left C hC S T hS]

theorem functionConvolution_comm (f g : Space d → 𝕜) :
    functionConvolution f g = functionConvolution g f := by
  ext x
  change (∫ y, f (x - y) * g y) = ∫ y, g (x - y) * f y
  rw [← integral_sub_left_eq_self (fun y => f (x - y) * g y) volume x]
  simp_rw [sub_sub_cancel, mul_comm]

/-- Symmetric completion preserves every support, derivative, regularization and
locally integrable compatibility conclusion of the preceding convolution goal. -/
theorem symmetrize_laws (C : ConvolutionFamily d 𝕜) (hC : ConvolutionLaws C) :
    ConvolutionLaws (symmetrize C) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro T S hS φ
    rw [symmetrize_right C T S hS]
    exact hC.1 T S hS φ
  · intro T S h
    by_cases hS : IsCompact (relativeSupport S)
    · rw [symmetrize_right C T S hS h]
      exact hC.2.1 T S _
    · have hT := h.resolve_right hS
      rw [symmetrize_left C hC T S hT h, add_comm]
      exact hC.2.1 S T _
  · intro T S hS α
    obtain ⟨⟨hα, heα⟩, heT⟩ := hC.2.2.1 T S hS α
    refine ⟨⟨hα, ?_⟩, ?_⟩
    · rw [symmetrize_right C T S hS, symmetrize_right C T (distributionPartial α S) hα]
      exact heα
    · rw [symmetrize_right C T S hS, symmetrize_right C (distributionPartial α T) S hS]
      exact heT
  · intro T ρ
    obtain ⟨hρ, hρeq⟩ := hC.2.2.2.1 T ρ
    exact ⟨hρ, (symmetrize_right C T _ hρ _).trans hρeq⟩
  · intro f g hf hg hfg
    obtain ⟨hint, hloc, h, heq⟩ := hC.2.2.2.2 f g hf hg hfg
    refine ⟨hint, hloc, h, ?_⟩
    by_cases hS : IsCompact (relativeSupport (regularDistribution ⊤ g))
    · rw [symmetrize_right C _ _ hS]
      exact heq
    · have hT := h.resolve_right hS
      obtain ⟨_, _, h', heq'⟩ := hC.2.2.2.2 g f hg hf hfg.symm
      rw [symmetrize_left C hC _ _ hT]
      exact heq'.trans (congrArg (regularDistribution ⊤) (functionConvolution_comm g f))

/-- Symmetry transports the derivative identities to the left-compact case. -/
theorem all_derivative_laws (C : ConvolutionFamily d 𝕜) (hC : ConvolutionLaws C)
    (hcomm : ∀ T S h, C T S h = C S T h.symm) : ConvolutionDerivativeLaws C := by
  intro T S h α
  rcases h with hT | hS
  · obtain ⟨⟨hTα, heT⟩, heS⟩ := hC.2.2.1 S T hT α
    refine ⟨⟨Or.inl hTα, ?_⟩, ⟨Or.inl hT, ?_⟩⟩
    · rw [hcomm T S, heT]
      exact hcomm S (distributionPartial α T) _
    · rw [hcomm T S, heS]
      exact hcomm (distributionPartial α S) T _
  · obtain ⟨⟨hSα, heS⟩, heT⟩ := hC.2.2.1 T S hS α
    exact ⟨⟨Or.inr hS, heT⟩, ⟨Or.inr hSα, heS⟩⟩

/-- The cutoffs required in the iterated formula always exist. -/
theorem exists_cutoffs (S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) (φ : WholeTests d 𝕜) :
    ∃ χ η : WholeTests d 𝕜,
      IsSupportCutoff S χ ∧ IsOneNear η (tsupport φ - relativeSupport S) := by
  obtain ⟨χ, hχ⟩ := exists_supportCutoff S hS
  obtain ⟨η, _, U, hU, _, hη⟩ := cutoff d ⊤
    ⟨tsupport φ - relativeSupport S, (by
      have he : tsupport φ - relativeSupport S =
          (fun p : Space d × Space d => p.1 - p.2) '' (tsupport φ ×ˢ relativeSupport S) := by
        ext z
        constructor
        · rintro ⟨a, ha, b, hb, rfl⟩
          exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
        · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
          exact ⟨a, ha, b, hb, rfl⟩
      rw [he]
      exact (φ.hasCompactSupport.prod hS).image (continuous_fst.sub continuous_snd))⟩ (subset_univ _)
  let ηk : WholeTests d 𝕜 := TestFunction.postcompCLM (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜) η
  refine ⟨χ, ηk, hχ, U, hU, ?_⟩
  intro x hx
  change (η x : 𝕜) = 1
  rw [hη x hx]
  simp

/-- The requisite cutoffs give both iterated pairings with the same value.
This also proves independence of the choices of the cutoffs. -/
theorem cutoff_pairing (hInner : DistributionConvolutionExpected.InnerTest)
    (C : ConvolutionFamily d 𝕜) (hC : ConvolutionLaws C)
    (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (hS : IsCompact (relativeSupport S)) (φ χ η : WholeTests d 𝕜)
    (hχ : IsSupportCutoff S χ) (hη : IsOneNear η (tsupport φ - relativeSupport S)) :
    ∃ ψ θ : WholeTests d 𝕜,
      (∀ x, ∃ σ : WholeTests d 𝕜,
        (∀ y, σ y = η x * χ y * φ (x + y)) ∧ ψ x = S σ) ∧
      (∀ y, ∃ τ : WholeTests d 𝕜,
        (∀ x, τ x = η x * χ y * φ (x + y)) ∧ θ y = T τ) ∧
      C T S (Or.inr hS) φ = T ψ ∧ T ψ = S θ := by
  obtain ⟨ψ, θ, hψ, hθ, heq⟩ :=
    DistributionInterchange.interchange d 𝕜 T S (cutoffAddition φ χ η)
  refine ⟨ψ, θ, fun x => ⟨productRightSlice (cutoffAddition φ χ η) x, fun _ => rfl, hψ x⟩,
    fun y => ⟨productLeftSlice (cutoffAddition φ χ η) y, fun _ => rfl, hθ y⟩, ?_, heq⟩
  obtain ⟨u, hu, hCu⟩ := hC.1 T S hS φ
  rw [hCu]
  congr 1
  ext x
  rw [hψ, cutoffAddition_right S φ χ η hχ, hu]
  obtain ⟨U, hU, hηU⟩ := hη
  by_cases hx : convolutionInner S φ x = 0
  · rw [hx, mul_zero]
  · have hxU := hU ((hInner d 𝕜 S hS φ).2.1 (subset_tsupport _ hx))
    rw [hηU x hxU, one_mul]

end ConvolutionSymmetryProof

/-- Conditional draft only: the original closed declaration is reserved to its owner. -/
theorem distributionInterchange_conditional
    (_hConvolution : DistributionConvolutionExpected.Convolution)
    (_hConstruction : DistributionConvolutionExpected.Construction)
    (_hExtension : DistributionConvolutionExpected.ExtensionPairing)
    (_hOperator : DistributionConvolutionExpected.InnerOperator)
    (_hInner : DistributionConvolutionExpected.InnerTest)
    (_hRegular : DistributionConvolutionExpected.RegularInner) :
    ConvolutionSymmetryExpected.Interchange := DistributionInterchange.interchange

/-- Conditional full U4-04: all six frozen premises retain their original types
and order. No unproved upstream implementation is imported. -/
theorem convolutionSymmetry_conditional
    (hConvolution : DistributionConvolutionExpected.Convolution)
    (_hConstruction : DistributionConvolutionExpected.Construction)
    (_hExtension : DistributionConvolutionExpected.ExtensionPairing)
    (_hOperator : DistributionConvolutionExpected.InnerOperator)
    (hInner : DistributionConvolutionExpected.InnerTest)
    (_hRegular : DistributionConvolutionExpected.RegularInner) :
    ConvolutionSymmetryExpected.Convolution := by
  intro d 𝕜 _
  obtain ⟨C, hC⟩ := hConvolution d 𝕜
  change ConvolutionLaws C at hC
  let D := ConvolutionSymmetryProof.symmetrize C
  have hD : ConvolutionLaws D := ConvolutionSymmetryProof.symmetrize_laws C hC
  have hcomm : ∀ T S h, D T S h = D S T h.symm :=
    ConvolutionSymmetryProof.symmetrize_comm C hC
  exact ⟨D, hD, ConvolutionSymmetryProof.all_derivative_laws D hD hcomm, hcomm,
    ConvolutionSymmetryProof.exists_cutoffs, ConvolutionSymmetryProof.cutoff_pairing hInner D hD⟩

end P102.U4

theorem _root_.«P102».«U4».«convolutionSymmetry» : _root_.«P102».«U4».«ConvolutionSymmetryExpected».«Convolution» :=
  @_root_.«P102».«U4».«convolutionSymmetry_conditional» (@_root_.«P102».«U4».«distributionConvolution») (@_root_.«P102».«U4».«distributionConvolution_construction») (@_root_.«P102».«U4».«distributionConvolution_extensionPairing») (@_root_.«P102».«U4».«distributionConvolution_innerOperator») (@_root_.«P102».«U4».«distributionConvolution_innerTest») (@_root_.«P102».«U4».«distributionConvolution_regularInner»)
theorem _root_.«P102».«U4».«distributionInterchange» : _root_.«P102».«U4».«ConvolutionSymmetryExpected».«Interchange» :=
  @_root_.«P102».«U4».«distributionInterchange_conditional» (@_root_.«P102».«U4».«distributionConvolution») (@_root_.«P102».«U4».«distributionConvolution_construction») (@_root_.«P102».«U4».«distributionConvolution_extensionPairing») (@_root_.«P102».«U4».«distributionConvolution_innerOperator») (@_root_.«P102».«U4».«distributionConvolution_innerTest») (@_root_.«P102».«U4».«distributionConvolution_regularInner»)
