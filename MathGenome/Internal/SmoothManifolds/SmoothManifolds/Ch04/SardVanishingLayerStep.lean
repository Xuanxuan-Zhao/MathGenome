import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.SardVanishingLayerStep
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

open Set MeasureTheory
open scoped ContDiff Topology

namespace SmoothManifolds.Ch04.SardVanishingLayer

lemma vanishingJets_mono {m n i j : ℕ} {U : Set (Fin m → ℝ)}
    {f : (Fin m → ℝ) → (Fin n → ℝ)} (hij : i ≤ j) :
    vanishingJets U f j ⊆ vanishingJets U f i := by
  rintro x ⟨hx, hf⟩
  exact ⟨hx, fun k hk hki ↦ hf k hk (hki.trans hij)⟩

lemma fderiv_eq_zero_of_mem_vanishingJets {m n j : ℕ}
    {U : Set (Fin m → ℝ)} {f : (Fin m → ℝ) → (Fin n → ℝ)}
    {x : Fin m → ℝ} (hj : 1 ≤ j) (hx : x ∈ vanishingJets U f j) :
    fderiv ℝ f x = 0 := by
  apply norm_eq_zero.mp
  rw [← norm_iteratedFDeriv_one f, hx.2 1 le_rfl hj, norm_zero]

/-- Nullity of images is local on a second countable source, even for arbitrary sets. -/
lemma image_null_of_locally_image_null {E F : Type*} [TopologicalSpace E]
    [SecondCountableTopology E] [MeasurableSpace F] (μ : Measure F)
    (f : E → F) (s : Set E)
    (h : ∀ x ∈ s, ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ μ (f '' (s ∩ W)) = 0) :
    μ (f '' s) = 0 := by
  classical
  choose W hWo hxW hW using h
  obtain ⟨t, ht, hcover⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover
    (fun x : s ↦ W x x.2) (fun x ↦ hWo x x.2) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxW x hx⟩)
  have hnull : μ (⋃ x ∈ t, f '' (s ∩ W x x.2)) = 0 :=
    (measure_biUnion_null_iff ht).mpr (fun x _ ↦ hW x x.2)
  apply measure_mono_null _ hnull
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hcover hx)
  exact mem_iUnion₂.mpr ⟨y, hy, ⟨x, ⟨hx, hxy⟩, rfl⟩⟩

/-- Application of the smaller-dimensional Sard hypothesis to a smooth
parameterization of points where the ambient first derivative vanishes. -/
lemma image_null_of_parameterization {m n d : ℕ} (hn : 0 < n) (ih : sardIn d)
    {U : Set (Fin m → ℝ)} {f : (Fin m → ℝ) → (Fin n → ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    {V : Set (Fin d → ℝ)} (hV : IsOpen V)
    {φ : (Fin d → ℝ) → (Fin m → ℝ)} (hφ : ContDiffOn ℝ ∞ φ V)
    (hφU : MapsTo φ V U) {s : Set (Fin m → ℝ)}
    (hs : s ⊆ φ '' V) (hzero : ∀ x ∈ s, fderiv ℝ f x = 0) :
    volume (f '' s) = 0 := by
  have hg : ContDiffOn ℝ ∞ (f ∘ φ) V := hf.comp hφ hφU
  apply measure_mono_null (t := (f ∘ φ) ''
    {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ (f ∘ φ) x)}) _ (ih n V (f ∘ φ) hV hg)
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hy, rfl⟩ := hs hx
  refine ⟨y, ⟨hy, ?_⟩, rfl⟩
  rw [fderiv_comp y ((hf.differentiableOn (by simp) (φ y) (hφU hy)).differentiableAt
      (hU.mem_nhds (hφU hy)))
    ((hφ.differentiableOn (by simp) y hy).differentiableAt (hV.mem_nhds hy)),
    hzero _ hx, ContinuousLinearMap.zero_comp]
  intro hsurj
  obtain ⟨z, hz⟩ := hsurj (fun _ ↦ (1 : ℝ))
  have := congrFun hz ⟨0, hn⟩
  norm_num at this

/-- A nonzero next derivative supplies a scalar equation vanishing on the
current jet stratum and having nonzero differential at the chosen point. -/
lemma exists_regular_scalar {m n j : ℕ} {U : Set (Fin m → ℝ)}
    {f : (Fin m → ℝ) → (Fin n → ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ ∞ f U) (hj : 1 ≤ j) {a : Fin m → ℝ}
    (ha : a ∈ vanishingJets U f j \ vanishingJets U f (j + 1)) :
    ∃ h : (Fin m → ℝ) → ℝ, ContDiffOn ℝ ∞ h U ∧
      (∀ x ∈ vanishingJets U f j, h x = 0) ∧ fderiv ℝ h a ≠ 0 := by
  classical
  have hnext : iteratedFDeriv ℝ (j + 1) f a ≠ 0 := by
    intro h
    apply ha.2
    refine ⟨ha.1.1, fun i hi hij ↦ ?_⟩
    by_cases hle : i ≤ j
    · exact ha.1.2 i hi hle
    · have : i = j + 1 := by omega
      subst i
      exact h
  obtain ⟨v, i, hvi⟩ : ∃ (v : Fin (j + 1) → (Fin m → ℝ)) (i : Fin n),
      iteratedFDeriv ℝ (j + 1) f a v i ≠ 0 := by
    by_contra! h
    apply hnext
    ext v i
    exact h v i
  let L : ((Fin m → ℝ) [×j]→L[ℝ] (Fin n → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ Fin m → ℝ)
        (Fin n → ℝ) (Fin.tail v))
  let h := fun x ↦ L (iteratedFDeriv ℝ j f x)
  have hc : ∀ x ∈ U, ContDiffAt ℝ ∞ (iteratedFDeriv ℝ j f) x := by
    intro x hx
    exact (hf.contDiffAt (hU.mem_nhds hx)).iteratedFDeriv_right (by simp)
  refine ⟨h, ?_, ?_, ?_⟩
  · intro x hx
    exact (L.contDiff.contDiffAt.comp x (hc x hx)).contDiffWithinAt
  · intro x hx
    simp [h, hx.2 j hj le_rfl]
  · have hd : fderiv ℝ h a = L.comp (fderiv ℝ (iteratedFDeriv ℝ j f) a) :=
      (L.hasFDerivAt.comp a ((hc a ha.1.1).differentiableAt (by simp)).hasFDerivAt).fderiv
    intro hz
    apply hvi
    rw [iteratedFDeriv_succ_apply_left]
    have := congrArg (fun T : (Fin m → ℝ) →L[ℝ] ℝ ↦ T (v 0)) hz
    simpa [hd, L] using this

/-- A regular scalar level set is locally covered by a smooth map from
`ℝ^(m-1)`. The neighborhood and parameter domain are open, and the image
of the parameterization stays in the original domain. -/
lemma exists_hypersurface_parameterization {m : ℕ} {U : Set (Fin m → ℝ)}
    {h : (Fin m → ℝ) → ℝ} (hU : IsOpen U) (hh : ContDiffOn ℝ ∞ h U)
    {a : Fin m → ℝ} (ha : a ∈ U) (hdh : fderiv ℝ h a ≠ 0) :
    ∃ (W : Set (Fin m → ℝ)) (V : Set (Fin (m - 1) → ℝ))
      (φ : (Fin (m - 1) → ℝ) → (Fin m → ℝ)),
      IsOpen W ∧ a ∈ W ∧ IsOpen V ∧ ContDiffOn ℝ ∞ φ V ∧ MapsTo φ V U ∧
      {x | x ∈ W ∧ h x = 0} ⊆ φ '' V := by
  classical
  let dh := fderiv ℝ h a
  have hr : dh.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    obtain ⟨v, hv⟩ : ∃ v, dh v ≠ 0 := by
      by_contra! hz
      apply hdh
      ext v
      exact hz v
    intro y
    refine ⟨(y / dh v) • v, ?_⟩
    simp [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  have hfin : Module.finrank ℝ dh.ker = m - 1 := by
    have heq := dh.toLinearMap.finrank_range_add_finrank_ker
    change Module.finrank ℝ dh.range + Module.finrank ℝ dh.ker =
      Module.finrank ℝ (Fin m → ℝ) at heq
    rw [hr] at heq
    simp only [finrank_top, Module.finrank_self, Module.finrank_fin_fun] at heq
    omega
  let c : (Fin (m - 1) → ℝ) ≃L[ℝ] dh.ker :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [hfin])
  have hs : HasStrictFDerivAt h dh a :=
    (hh.contDiffAt (hU.mem_nhds ha)).hasStrictFDerivAt (by simp)
  let d := hs.implicitFunctionDataOfComplemented h dh hr
    dh.ker_closedComplemented_of_finiteDimensional_range
  let e := d.toOpenPartialHomeomorph
  have hright : ContDiff ℝ ∞ d.rightFun := by
    dsimp [d, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
    fun_prop
  have hp : ContDiffOn ℝ ∞ d.prodFun U := hh.prodMk hright.contDiffOn
  have hpc : ContinuousAt (fderiv ℝ d.prodFun) a :=
    (hp.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt (hU.mem_nhds ha)
  have hi : ∀ᶠ x in 𝓝 a, (fderiv ℝ d.prodFun x).IsInvertible :=
    hpc.eventually d.isInvertible_fderiv_prodFun.eventually_nhds
  obtain ⟨O, hOsub, hO, haO⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hU.mem_nhds ha) hi)
  let V := (fun z ↦ ((0 : ℝ), c z)) ⁻¹' (e.target ∩ e.symm ⁻¹' O)
  let φ := fun z ↦ e.symm ((0 : ℝ), c z)
  have hV : IsOpen V := (e.isOpen_inter_preimage_symm hO).preimage (by fun_prop)
  have hφ : ContDiffOn ℝ ∞ φ V := by
    intro z hz
    obtain ⟨ci, hci⟩ := (hOsub hz.2).2
    have hpre : e.symm (0, c z) ∈ U := (hOsub hz.2).1
    have hfde : HasFDerivAt e (ci : (Fin m → ℝ) →L[ℝ] ℝ × dh.ker)
        (e.symm (0, c z)) := by
      rw [hci]
      exact (hp.contDiffAt (hU.mem_nhds hpre)).differentiableAt (by simp) |>.hasFDerivAt
    have hcde : ContDiffAt ℝ ∞ e.symm (0, c z) :=
      e.contDiffAt_symm hz.1 hfde (hp.contDiffAt (hU.mem_nhds hpre))
    exact (hcde.comp z (by fun_prop)).contDiffWithinAt
  refine ⟨O ∩ e.source, V, φ, hO.inter e.open_source,
    ⟨haO, d.pt_mem_toOpenPartialHomeomorph_source⟩, hV, hφ, ?_, ?_⟩
  · intro z hz
    exact (hOsub hz.2).1
  · rintro x ⟨hx, hxh⟩
    refine ⟨c.symm (e x).2, ?_, ?_⟩
    · change (0, c (c.symm (e x).2)) ∈ e.target ∩ e.symm ⁻¹' O
      have hxe : (0, c (c.symm (e x).2)) = e x := by
        apply Prod.ext
        · exact hxh.symm
        · simp
      rw [hxe]
      refine ⟨e.map_source hx.2, ?_⟩
      change e.symm (e x) ∈ O
      rw [e.left_inv hx.2]
      exact hx.1
    · change e.symm (0, c (c.symm (e x).2)) = x
      have hxe : (0, c (c.symm (e x).2)) = e x := by
        apply Prod.ext
        · exact hxh.symm
        · simp
      rw [hxe, e.left_inv hx.2]

/-- Hypersurface reduction for every nonterminal vanishing-jet layer. -/
theorem vanishing_layer : Specs.vanishingLayer := by
  intro m n j _hm hn hj U f hU hf ih
  apply image_null_of_locally_image_null volume f
  intro a ha
  obtain ⟨h, hh, hzero, hdh⟩ := exists_regular_scalar hU hf hj ha
  obtain ⟨W, V, φ, hW, haW, hV, hφ, hφU, hcover⟩ :=
    exists_hypersurface_parameterization hU hh ha.1.1 hdh
  refine ⟨W, hW, haW,
    image_null_of_parameterization hn ih hU hf hV hφ hφU ?_ ?_⟩
  · intro x hx
    exact hcover ⟨hx.2, hzero x hx.1.1⟩
  · intro x hx
    exact fderiv_eq_zero_of_mem_vanishingJets hj hx.1.1

end SmoothManifolds.Ch04.SardVanishingLayer
