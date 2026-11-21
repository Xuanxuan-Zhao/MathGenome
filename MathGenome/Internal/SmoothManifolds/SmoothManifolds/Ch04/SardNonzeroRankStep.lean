import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch04.SardNonzeroRankStep
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.Complemented
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open Set MeasureTheory
open scoped ContDiff

namespace SmoothManifolds.Ch04.SardNonzeroRank

section FiniteDimensional

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Surjectivity is an open condition on finite-dimensional-target linear maps. -/
theorem isOpen_surjective : IsOpen {A : E →L[ℝ] F | Function.Surjective A} := by
  convert isOpen_setOfPred_nat_le_rank (𝕜 := ℝ) (E := E) (F := F)
    (Module.finrank ℝ F) using 1
  ext A
  change Function.Surjective A ↔
    (Module.finrank ℝ F : Cardinal) ≤ Module.rank ℝ (LinearMap.range A.toLinearMap)
  rw [← Module.finrank_eq_rank, Nat.cast_le]
  constructor
  · intro h
    rw [LinearMap.range_eq_top.mpr h]
    simp
  · intro h
    exact LinearMap.range_eq_top.mp
      (Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) h))

/-- Critical sets are sigma compact inside an open Euclidean domain. This proves
the compact-exhaustion hypothesis, rather than assuming measurable critical images. -/
theorem criticalSet_isSigmaCompact [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) :
    IsSigmaCompact {x | x ∈ U ∧ ¬Function.Surjective (fderiv ℝ f x)} := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  have hc : IsClosed {x : U | ¬Function.Surjective (fderiv ℝ f x)} :=
    (SardNonzeroRank.isOpen_surjective (E := E) (F := F)).isClosed_compl.preimage
      (hf.continuousOn_fderiv_of_isOpen hU (by simp)).domRestrict
  have hs : IsSigmaCompact {x : U | ¬Function.Surjective (fderiv ℝ f x)} :=
    isSigmaCompact_univ.of_isClosed_subset hc (subset_univ _)
  convert hs.image continuous_subtype_val using 1
  ext x
  simp only [mem_image, mem_ofPred_eq, Subtype.exists, exists_and_left, exists_prop]
  aesop

end FiniteDimensional

/-- A nonzero linear map to a one-dimensional target is surjective. -/
theorem surjective_fin_one_of_ne_zero {m : ℕ}
    (A : (Fin m → ℝ) →L[ℝ] (Fin 1 → ℝ)) (hA : A ≠ 0) :
    Function.Surjective A := by
  apply surjective_of_nonzero_of_finrank_eq_one
    (K := ℝ) (f := A.toLinearMap) (by simp) ?_
  intro h
  apply hA
  ext x i
  exact congrFun (LinearMap.congr_fun h x) i

/-- The off-zero stratum is empty for scalar-valued maps, without a regularity premise. -/
theorem offZeroCriticalSet_target_one {m : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin 1 → ℝ)) : offZeroCriticalSet U f = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hx.2.1 (surjective_fin_one_of_ne_zero _ hx.2.2)

/-- The scalar-target case of the requested conclusion. -/
theorem nonzeroRank_target_one {m : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin 1 → ℝ)) :
    volume (f '' offZeroCriticalSet U f) = 0 := by
  simp [offZeroCriticalSet_target_one]

/-- Fubini applied only to a compact image. The sections themselves need no
measurability assumption: they are contained in lower-dimensional critical images. -/
theorem compact_skew_image_null {d q : ℕ} (ih : SardIn d)
    {V : Set (ℝ × (Fin d → ℝ))} (hV : IsOpen V)
    {g : (ℝ × (Fin d → ℝ)) → (Fin q → ℝ)} (hg : ContDiffOn ℝ ∞ g V)
    {K : Set (ℝ × (Fin d → ℝ))} (hK : IsCompact K) (hKV : K ⊆ V)
    (hcrit : ∀ p ∈ K,
      ¬Function.Surjective (fderiv ℝ (fun z => g (p.1, z)) p.2)) :
    volume ((fun p => (p.1, g p)) '' K) = 0 := by
  rw [Measure.volume_eq_prod]
  apply Measure.measure_prod_null_of_ae_null
    (hK.image_of_continuousOn ((continuousOn_fst.prodMk hg.continuousOn).mono hKV)).measurableSet
  apply Filter.Eventually.of_forall
  intro t
  have hslice : ContDiffOn ℝ ∞ (fun z => g (t, z)) (Prod.mk t ⁻¹' V) :=
    hg.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hz => hz)
  apply measure_mono_null ?_
    (ih q (Prod.mk t ⁻¹' V) (fun z => g (t, z))
      (hV.preimage (continuous_const.prodMk continuous_id)) hslice)
  rintro y ⟨⟨s, z⟩, hp, heq⟩
  have hst : s = t := congrArg Prod.fst heq
  subst s
  exact ⟨z, ⟨hKV hp, hcrit (t, z) hp⟩, congrArg Prod.snd heq⟩

/-- Countable compact exhaustion removes all measurability premises from the
critical subset in a skew-product chart. -/
theorem sigmaCompact_skew_image_null {d q : ℕ} (ih : SardIn d)
    {V : Set (ℝ × (Fin d → ℝ))} (hV : IsOpen V)
    {g : (ℝ × (Fin d → ℝ)) → (Fin q → ℝ)} (hg : ContDiffOn ℝ ∞ g V)
    {C : Set (ℝ × (Fin d → ℝ))} (hC : IsSigmaCompact C) (hCV : C ⊆ V)
    (hcrit : ∀ p ∈ C,
      ¬Function.Surjective (fderiv ℝ (fun z => g (p.1, z)) p.2)) :
    volume ((fun p => (p.1, g p)) '' C) = 0 := by
  obtain ⟨K, hK, hKC⟩ := hC
  have hsub (i : ℕ) : K i ⊆ C := hKC ▸ subset_iUnion K i
  rw [← hKC, image_iUnion]
  exact measure_iUnion_null fun i => compact_skew_image_null ih hV hg (hK i)
    ((hsub i).trans hCV) (fun p hp => hcrit p (hsub i hp))

/-- The block triangular derivative of a skew product is surjective exactly
when its vertical block is surjective. -/
theorem skew_linear_surjective_iff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : (ℝ × E) →L[ℝ] F) :
    Function.Surjective ((ContinuousLinearMap.fst ℝ ℝ E).prod A) ↔
      Function.Surjective (A.comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
  constructor
  · intro h y
    obtain ⟨⟨t, z⟩, hp⟩ := h (0, y)
    have ht : t = 0 := congrArg Prod.fst hp
    subst t
    exact ⟨z, congrArg Prod.snd hp⟩
  · intro h ⟨t, y⟩
    obtain ⟨z, hz⟩ := h (y - A (t, 0))
    refine ⟨(t, z), Prod.ext rfl ?_⟩
    change A (t, z) = y
    have he : (t, z) = (t, (0 : E)) + (0, z) := by simp
    rw [he, map_add]
    change A (t, 0) + A.comp (ContinuousLinearMap.inr ℝ ℝ E) z = y
    rw [hz]
    simp

/-- Criticality in a smooth skew-product chart is precisely criticality on
the open slice, using actual ambient derivatives on both sides. -/
theorem skew_critical_iff {d q : ℕ}
    {V : Set (ℝ × (Fin d → ℝ))} (hV : IsOpen V)
    {g : (ℝ × (Fin d → ℝ)) → (Fin q → ℝ)} (hg : ContDiffOn ℝ ∞ g V)
    {p : ℝ × (Fin d → ℝ)} (hp : p ∈ V) :
    Function.Surjective (fderiv ℝ (fun p => (p.1, g p)) p) ↔
      Function.Surjective (fderiv ℝ (fun z => g (p.1, z)) p.2) := by
  have hd : DifferentiableAt ℝ g p :=
    (hg.differentiableOn (by simp) p hp).differentiableAt (hV.mem_nhds hp)
  have hprod := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk hd.hasFDerivAt
  have hslice := hd.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) p.1 p.2)
  simp only [Function.comp_def] at hslice
  rw [hprod.fderiv, hslice.fderiv]
  exact skew_linear_surjective_iff _

/-- Sard's conclusion for the entire critical image of a smooth skew product.
The induction hypothesis is used solely for its vertical slices. -/
theorem skew_critical_image_null {d q : ℕ} (ih : SardIn d)
    {V : Set (ℝ × (Fin d → ℝ))} (hV : IsOpen V)
    {g : (ℝ × (Fin d → ℝ)) → (Fin q → ℝ)} (hg : ContDiffOn ℝ ∞ g V) :
    volume ((fun p => (p.1, g p)) ''
      {p | p ∈ V ∧ ¬Function.Surjective (fderiv ℝ (fun p => (p.1, g p)) p)}) = 0 := by
  apply sigmaCompact_skew_image_null ih hV hg
    (criticalSet_isSigmaCompact hV (contDiffOn_fst.prodMk hg)) (fun _ hp => hp.1)
  intro p hp hsurj
  exact hp.2 ((skew_critical_iff hV hg hp.1).mpr hsurj)

/-- Split off any chosen coordinate, with the same underlying function as the
standard measure-preserving product decomposition. -/
noncomputable def coordinateSplit {q : ℕ} (i : Fin (q + 1)) :
    (Fin (q + 1) → ℝ) ≃L[ℝ] (ℝ × (Fin q → ℝ)) :=
  LinearEquiv.toContinuousLinearEquiv
    { toEquiv := (Fin.insertNthEquiv (fun _ : Fin (q + 1) => ℝ) i).symm
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem coordinateSplit_apply {q : ℕ} (i : Fin (q + 1))
    (v : Fin (q + 1) → ℝ) : coordinateSplit i v = (v i, fun j => v (i.succAbove j)) := rfl

/-- The coordinate splitting preserves the given product Lebesgue measures. -/
theorem coordinateSplit_measurePreserving {q : ℕ} (i : Fin (q + 1)) :
    MeasurePreserving (coordinateSplit i) :=
  volume_preserving_piFinSuccAbove (fun _ : Fin (q + 1) => ℝ) i

/-- A nonzero scalar linear map can be made the first coordinate of an
isomorphism. The remaining coordinates have exactly source dimension minus one. -/
theorem exists_scalar_split {m : ℕ}
    (B : (Fin m → ℝ) →L[ℝ] ℝ) (hB : B ≠ 0) :
    ∃ L : (Fin m → ℝ) ≃L[ℝ] (ℝ × (Fin (m - 1) → ℝ)),
      ∀ x, (L x).1 = B x := by
  have hsurj : Function.Surjective B :=
    surjective_of_nonzero_of_finrank_eq_one (K := ℝ) (f := B.toLinearMap)
      (by simp) (by intro h; apply hB; ext x; exact LinearMap.congr_fun h x)
  have hrange : B.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hdim : Module.finrank ℝ B.ker = m - 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker B.toLinearMap
    rw [hrange] at h
    simp only [finrank_top, Module.finrank_self,
      Module.finrank_pi, Fintype.card_fin] at h
    omega
  let K : B.ker ≃L[ℝ] (Fin (m - 1) → ℝ) :=
    (LinearEquiv.ofFinrankEq B.ker (Fin (m - 1) → ℝ) (by simpa using hdim)).toContinuousLinearEquiv
  have hc := B.ker_closedComplemented_of_finiteDimensional_range
  let P := Classical.choose hc
  have hP := Classical.choose_spec hc
  let L := B.equivProdOfSurjectiveOfIsCompl P hrange
    (LinearMap.range_eq_of_proj hP) (LinearMap.isCompl_of_proj hP)
  exact ⟨L.trans (ContinuousLinearEquiv.prodCongr (.refl ℝ ℝ) K), fun _ => rfl⟩

/-- A smooth inverse chart, restricted so that all of its source lies in the
original open domain. Invertibility near the base point supplies smoothness at
every point of its target, including for order infinity. -/
theorem exists_smooth_inverse_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {H : E → F} (hH : ContDiffOn ℝ ∞ H U)
    {a : E} (ha : a ∈ U) (L : E ≃L[ℝ] F) (hD : HasFDerivAt H (L : E →L[ℝ] F) a) :
    ∃ e : OpenPartialHomeomorph E F,
      a ∈ e.source ∧ e.source ⊆ U ∧
      (∀ x, e x = H x) ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let e₀ := (hH.contDiffAt (hU.mem_nhds ha)).toOpenPartialHomeomorph H hD (by simp)
  let S : Set E := U ∩ {x | (fderiv ℝ H x).IsInvertible}
  have hS : IsOpen S :=
    (hH.continuousOn_fderiv_of_isOpen hU (by simp)).isOpen_inter_preimage hU
      ContinuousLinearMap.isOpen_setOfPred_isInvertible
  let e := e₀.restrOpen S hS
  have hsource : e.source = e₀.source ∩ S := rfl
  have hsub : e.source ⊆ U := fun _ hx => (hsource ▸ hx).2.1
  have hfun : ∀ x, e x = H x := fun _ => rfl
  refine ⟨e, ?_, hsub, hfun, ?_⟩
  · rw [hsource]
    refine ⟨ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _, ha, ?_⟩
    change (fderiv ℝ H a).IsInvertible
    rw [hD.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  · intro y hy
    have hx := e.map_target hy
    have hxu := hsub hx
    obtain ⟨A, hA⟩ := (hsource ▸ hx).2.2
    have hd : HasFDerivAt e (A : E →L[ℝ] F) (e.symm y) := by
      rw [hA]
      exact (hH.differentiableOn (by simp) _ hxu).differentiableAt
        (hU.mem_nhds hxu) |>.hasFDerivAt
    exact (e.contDiffAt_symm hy hd
      (hH.contDiffAt (hU.mem_nhds hxu))).contDiffWithinAt

/-- A scalar submersion gives a smooth coordinate chart whose first coordinate
is exactly the given scalar function. -/
theorem exists_scalar_chart {m : ℕ}
    {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    {h : (Fin m → ℝ) → ℝ} (hh : ContDiffOn ℝ ∞ h U)
    {a : Fin m → ℝ} (ha : a ∈ U) (hD : fderiv ℝ h a ≠ 0) :
    ∃ e : OpenPartialHomeomorph (Fin m → ℝ) (ℝ × (Fin (m - 1) → ℝ)),
      a ∈ e.source ∧ e.source ⊆ U ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ p ∈ e.target, h (e.symm p) = p.1 := by
  obtain ⟨L, hL⟩ := exists_scalar_split (fderiv ℝ h a) hD
  let P := (ContinuousLinearMap.snd ℝ ℝ (Fin (m - 1) → ℝ)).comp L.toContinuousLinearMap
  let H := fun x => (h x, P x)
  have hH : ContDiffOn ℝ ∞ H U := hh.prodMk P.contDiff.contDiffOn
  have hDH : HasFDerivAt H (L : (Fin m → ℝ) →L[ℝ] (ℝ × (Fin (m - 1) → ℝ))) a := by
    convert ((hh.differentiableOn (by simp) a ha).differentiableAt
      (hU.mem_nhds ha)).hasFDerivAt.prodMk P.hasFDerivAt using 1
    apply ContinuousLinearMap.ext
    intro x
    exact Prod.ext (hL x) rfl
  obtain ⟨e, hae, heU, heH, heinv⟩ := exists_smooth_inverse_chart hU hH ha L hDH
  refine ⟨e, hae, heU, heinv, ?_⟩
  intro p hp
  have heq := e.right_inv hp
  rw [heH] at heq
  exact congrArg Prod.fst heq

/-- A nonzero vector-valued derivative has a component with nonzero derivative. -/
theorem exists_nonzero_component {m n : ℕ}
    {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    {f : (Fin m → ℝ) → (Fin n → ℝ)} (hf : ContDiffOn ℝ ∞ f U)
    {a : Fin m → ℝ} (ha : a ∈ U) (hD : fderiv ℝ f a ≠ 0) :
    ∃ i : Fin n, fderiv ℝ (fun x => f x i) a ≠ 0 := by
  have hd := (hf.differentiableOn (by simp) a ha).differentiableAt (hU.mem_nhds ha)
  have heq (i : Fin n) : fderiv ℝ (fun x => f x i) a =
      (ContinuousLinearMap.proj i).comp (fderiv ℝ f a) := by
    exact ((ContinuousLinearMap.proj i).hasFDerivAt.comp a hd.hasFDerivAt).fderiv
  by_contra! h
  apply hD
  ext x i
  have hi := congrArg (fun A : (Fin m → ℝ) →L[ℝ] ℝ => A x) (h i)
  rw [heq] at hi
  exact hi

/-- A neighborhood of every point with nonzero derivative has null critical
image. Only the smaller-source-dimensional induction hypothesis is used. -/
theorem critical_image_null_near_nonzero {m q : ℕ}
    {U : Set (Fin m → ℝ)} (hU : IsOpen U)
    {f : (Fin m → ℝ) → (Fin (q + 1) → ℝ)} (hf : ContDiffOn ℝ ∞ f U)
    (ih : SardIn (m - 1)) {a : Fin m → ℝ} (ha : a ∈ U)
    (hD : fderiv ℝ f a ≠ 0) :
    ∃ W : Set (Fin m → ℝ), IsOpen W ∧ a ∈ W ∧ W ⊆ U ∧
      volume (f '' {x | x ∈ W ∧ ¬Function.Surjective (fderiv ℝ f x)}) = 0 := by
  obtain ⟨i, hi⟩ := exists_nonzero_component hU hf ha hD
  obtain ⟨e, hae, heU, heinv, hefirst⟩ :=
    exists_scalar_chart hU (contDiffOn_pi.mp hf i) ha hi
  let T := coordinateSplit i
  let F := fun p => T (f (e.symm p))
  have hF : ContDiffOn ℝ ∞ F e.target :=
    T.contDiff.comp_contDiffOn (hf.comp heinv (fun p hp => heU (e.map_target hp)))
  let g := fun p => (F p).2
  have hg : ContDiffOn ℝ ∞ g e.target := hF.snd
  have hskew : EqOn (fun p => (p.1, g p)) F e.target := by
    intro p hp
    exact Prod.ext (hefirst p hp).symm rfl
  let C := {x | x ∈ e.source ∧ ¬Function.Surjective (fderiv ℝ f x)}
  have hnull : volume (T '' (f '' C)) = 0 := by
    apply measure_mono_null ?_ (skew_critical_image_null ih e.open_target hg)
    rintro y ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have hp := e.map_source hx.1
    refine ⟨e x, ⟨hp, ?_⟩, ?_⟩
    · intro hsurj
      have heqD := (hskew.eventuallyEq_of_mem (e.open_target.mem_nhds hp)).fderiv_eq (𝕜 := ℝ)
      rw [heqD] at hsurj
      have hdf : HasFDerivAt f (fderiv ℝ f x) (e.symm (e x)) := by
        rw [e.left_inv hx.1]
        exact ((hf.differentiableOn (by simp) x (heU hx.1)).differentiableAt
          (hU.mem_nhds (heU hx.1))).hasFDerivAt
      have hdi := ((heinv.differentiableOn (by simp) (e x) hp).differentiableAt
        (e.open_target.mem_nhds hp)).hasFDerivAt
      have hcomp : HasFDerivAt F
          ((T.toContinuousLinearMap.comp (fderiv ℝ f x)).comp
            (fderiv ℝ e.symm (e x))) (e x) := by
        simpa only [Function.comp_def, ContinuousLinearMap.comp_assoc] using
          T.hasFDerivAt.comp (e x) (hdf.comp (e x) hdi)
      rw [hcomp.fderiv] at hsurj
      apply hx.2
      intro z
      obtain ⟨v, hv⟩ := hsurj (T z)
      exact ⟨fderiv ℝ e.symm (e x) v, T.injective hv⟩
    · rw [hskew hp]
      dsimp [F]
      rw [e.left_inv hx.1]
  refine ⟨e.source, e.open_source, hae, heU, ?_⟩
  have hpre := (coordinateSplit_measurePreserving i).preimage_null hnull
  rwa [T.injective.preimage_image] at hpre

/-- The off-zero-derivative part of the critical image in the Euclidean Sard
induction. The outer measure pulled back by image permits countable localization
in the source without any measurability assumption on the final image. -/
theorem nonzeroRankStep : Specs.nonzeroRankStep := by
  intro m n _hm hn U f hU hf ih
  cases n with
  | zero => omega
  | succ q =>
    change (OuterMeasure.comap f volume.toOuterMeasure) (offZeroCriticalSet U f) = 0
    apply measure_null_of_locally_null
    intro x hx
    obtain ⟨W, hW, hxW, _hWU, hnull⟩ :=
      critical_image_null_near_nonzero hU hf ih hx.1 hx.2.2
    refine ⟨W ∩ offZeroCriticalSet U f,
      Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hxW)) self_mem_nhdsWithin, ?_⟩
    change volume (f '' (W ∩ offZeroCriticalSet U f)) = 0
    apply measure_mono_null (image_mono ?_) hnull
    intro y hy
    exact ⟨hy.1, hy.2.2.1⟩

end SmoothManifolds.Ch04.SardNonzeroRank
