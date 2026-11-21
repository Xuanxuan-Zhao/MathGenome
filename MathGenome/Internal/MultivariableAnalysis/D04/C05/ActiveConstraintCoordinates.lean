import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ActiveConstraintCoordinates
import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeInterfaces
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.ContDiff.WithLp

noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04.ActiveConstraints
open Specs.D04.C05.ActiveConstraintCoordinates

/-- Independence of scalar rows is exactly surjectivity of their joint map. -/
theorem rows_surjective {ι : Type} [Fintype ι] {n : ℕ}
    (f : E n →ₗ[ℝ] (ι → ℝ))
    (hli : LinearIndependent ℝ (fun i => (LinearMap.proj i).comp f)) :
    Function.Surjective f := by
  have hi : LinearIndependent ℝ (fun i x => f x i) :=
    hli.map' (LinearMap.ltoFun ℝ _ ℝ ℝ) (LinearMap.ker_eq_bot.mpr LinearMap.coe_injective)
  have hs := span_flip_eq_top_iff_linearIndependent.mpr hi
  apply LinearMap.range_eq_top.mp
  change Submodule.span ℝ (Set.range f) = ⊤ at hs
  simpa only [← LinearMap.coe_range, Submodule.span_eq] using hs

/-- A surjection can be completed by linear coordinates on its kernel.
The dimension identity includes the empty and full-rank cases. -/
theorem exists_linear_completion {ι : Type} [Fintype ι] {n : ℕ}
    (f : E n →ₗ[ℝ] (ι → ℝ)) (hf : Function.Surjective f) :
    ∃ (k : ℕ) (w : E n →ₗ[ℝ] E k)
      (e : E n ≃L[ℝ] ((ι → ℝ) × E k)),
      Fintype.card ι + k = n ∧ ∀ x, e x = (f x, w x) := by
  obtain ⟨b, hb⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  have hby (y : ι → ℝ) : f (b y) = y := LinearMap.congr_fun hb y
  let w : E n →ₗ[ℝ] f.ker :=
    (LinearMap.id - b.comp f).codRestrict f.ker (by intro x; simp [hby])
  have hbij : Function.Bijective (f.prod w) := by
    constructor
    · intro x z he
      have h1 := congrArg Prod.fst he
      have h2 := congrArg (fun p => (p.2 : E n)) he
      change f x = f z at h1
      change x - b (f x) = z - b (f z) at h2
      rw [h1] at h2
      exact sub_left_inj.mp h2
    · rintro ⟨y,z⟩
      refine ⟨b y + z, ?_⟩
      apply Prod.ext
      · simp [hby]
      · apply Subtype.ext
        change b y + z - b (f (b y + z)) = z
        simp [hby]
  let k := Module.finrank ℝ f.ker
  let eK : f.ker ≃ₗ[ℝ] E k := LinearEquiv.ofFinrankEq _ _ (by simp [k, E])
  let e := ((LinearEquiv.ofBijective (f.prod w) hbij).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl ℝ (ι → ℝ)) eK)).toContinuousLinearEquiv
  refine ⟨k, eK.toLinearMap.comp w, e, ?_, fun x => rfl⟩
  have he := e.toLinearEquiv.finrank_eq
  simpa [E] using he.symm

end D04.ActiveConstraints

namespace D04
open Specs.D04.C05.ActiveConstraintCoordinates

/-- Local constraint coordinates of every positive finite order. -/
theorem active_constraint_coordinates :
    Specs.D04.C05.ActiveConstraintCoordinates.active_constraint_coordinatesType := by
  classical
  intro n q s r U g h c a hr hU hg hh ha hga hha hli
  let I := Active h a
  let f : E n →ₗ[ℝ] ((Fin q ⊕ I) → ℝ) := LinearMap.pi (constraintRows g h a)
  have hf : Function.Surjective f := by
    apply ActiveConstraints.rows_surjective
    convert hli using 1
    funext i
    apply LinearMap.ext
    intro x
    rfl
  obtain ⟨k, w, e, hdim, he⟩ := ActiveConstraints.exists_linear_completion f hf
  let split : (((Fin q ⊕ I) → ℝ) × E k) ≃ₗ[ℝ]
      ((Fin q → ℝ) × ((I → ℝ) × E k)) :=
    (LinearEquiv.prodCongr (LinearEquiv.sumArrowLequivProdArrow (Fin q) I ℝ ℝ)
      (LinearEquiv.refl ℝ (E k))).trans (LinearEquiv.prodAssoc ℝ _ _ _)
  let e' := e.trans split.toContinuousLinearEquiv
  let φ := coordinateMap g h c a w
  have hg' : ContDiffOn ℝ (r : ℕ∞ω) g U := (crOn_iff_contDiffOn r U g hU).mp hg
  have hh' : ContDiffOn ℝ (r : ℕ∞ω) h U := (crOn_iff_contDiffOn r U h hU).mp hh
  have hgsc (j : Fin q) : ContDiffOn ℝ (r : ℕ∞ω) (fun x => g x j) U :=
    (contDiffOn_piLp 2).mp hg' j
  have hhsc (i : Fin s) : ContDiffOn ℝ (r : ℕ∞ω) (fun x => h x i) U :=
    (contDiffOn_piLp 2).mp hh' i
  have hr0 : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have dgs (j : Fin q) : HasFDerivAt (fun x => g x j)
      (totalDerivative (fun x => g x j) a) a :=
    ((hgsc j).contDiffAt (hU.mem_nhds ha)).differentiableAt hr0 |>.hasFDerivAt
  have dhs (i : Fin s) : HasFDerivAt (fun x => h x i)
      (totalDerivative (fun x => h x i) a) a :=
    ((hhsc i).contDiffAt (hU.mem_nhds ha)).differentiableAt hr0 |>.hasFDerivAt
  have hφ : ContDiffOn ℝ (r : ℕ∞ω) φ U :=
    (contDiffOn_pi.mpr (fun j => (hgsc j).sub contDiffOn_const)).prodMk
      ((contDiffOn_pi.mpr (fun i : I => hhsc i.val)).prodMk w.toContinuousLinearMap.contDiff.contDiffOn)
  have hemap : e'.toContinuousLinearMap =
      (ContinuousLinearMap.pi (fun j : Fin q => totalDerivative (fun x => g x j) a)).prod
      ((ContinuousLinearMap.pi (fun i : I => totalDerivative (fun x => h x i.val) a)).prod
        w.toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro x
    change split (e x) = _
    rw [he]
    rfl
  have hdφ : HasFDerivAt φ e'.toContinuousLinearMap a := by
    rw [hemap]
    exact (hasFDerivAt_pi.mpr (fun j => (dgs j).sub_const (c j))).prodMk
      ((hasFDerivAt_pi.mpr (fun i : I => dhs i.val)).prodMk w.toContinuousLinearMap.hasFDerivAt)
  have hφa : φ a = (0, (0, w a)) := by
    apply Prod.ext
    · funext j
      change g a j - c j = 0
      rw [hga, sub_self]
    · apply Prod.ext
      · funext i
        exact i.property
      · rfl
  -- A common neighborhood keeps every inactive inequality strictly positive.
  have hpos (i : Fin s) : ∀ᶠ x in 𝓝 a, h a i ≠ 0 → 0 < h x i := by
    by_cases hi : h a i = 0
    · exact Filter.Eventually.of_forall (fun _ hne => (hne hi).elim)
    · have hia : 0 < h a i := lt_of_le_of_ne (hha i) (Ne.symm hi)
      have ht := (dhs i).continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds hia)
      filter_upwards [ht] with x hx
      exact fun _ => hx
  have hposAll : {x | ∀ i : Fin s, h a i ≠ 0 → 0 < h x i} ∈ 𝓝 a :=
    Filter.eventually_all.mpr hpos
  obtain ⟨W, hWsub, hW, haW⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds ha) hposAll)
  have hWU : W ⊆ U := fun _ hx => (hWsub hx).1
  have hWpos (x : E n) (hx : x ∈ W) :
      ∀ i : Fin s, h a i ≠ 0 → 0 < h x i := (hWsub hx).2
  -- Apply the inverse theorem to the completed coordinate map.
  have hφAt := hφ.contDiffAt (hU.mem_nhds ha)
  let T := hφAt.toOpenPartialHomeomorph φ hdφ hr0
  have hTa : a ∈ T.source := hφAt.mem_toOpenPartialHomeomorph_source hdφ hr0
  have hTφa : φ a ∈ T.target := T.map_source hTa
  have hTinv : T.symm (φ a) = a := T.left_inv hTa
  have hgAt : ContDiffAt ℝ (r : ℕ∞ω) T.symm (φ a) :=
    hφAt.to_localInverse hdφ hr0
  have hgN : {y | ContDiffAt ℝ (r : ℕ∞ω) T.symm y} ∈ 𝓝 (φ a) :=
    hgAt.eventually (by simp)
  have hZ : IsOpen (T.target ∩ T.symm ⁻¹' W) := T.isOpen_inter_preimage_symm hW
  have hφZ : φ a ∈ T.target ∩ T.symm ⁻¹' W := ⟨hTφa, by simpa only [mem_preimage, hTinv] using haW⟩
  have hN : (T.target ∩ T.symm ⁻¹' W) ∩
      {y | ContDiffAt ℝ (r : ℕ∞ω) T.symm y} ∈ 𝓝 (0, (0, w a)) := by
    rw [← hφa]
    exact inter_mem (hZ.mem_nhds hφZ) hgN
  -- Product topology gives three compatible open coordinate neighborhoods.
  obtain ⟨A₀, hA₀, BC₀, hBC₀, hNsub⟩ := mem_nhds_prod_iff.mp hN
  obtain ⟨B₀, hB₀, C₀, hC₀, hBCsub⟩ := mem_nhds_prod_iff.mp hBC₀
  obtain ⟨A, hAsub, hA, h0A⟩ := mem_nhds_iff.mp hA₀
  obtain ⟨B, hBsub, hB, h0B⟩ := mem_nhds_iff.mp hB₀
  obtain ⟨C, hCsub, hC, hwC⟩ := mem_nhds_iff.mp hC₀
  let Y := A ×ˢ (B ×ˢ C)
  have hY : IsOpen Y := hA.prod (hB.prod hC)
  have hYsub (y) (hy : y ∈ Y) :
      y ∈ (T.target ∩ T.symm ⁻¹' W) ∩
        {y | ContDiffAt ℝ (r : ℕ∞ω) T.symm y} :=
    hNsub ⟨hAsub hy.1, hBCsub ⟨hBsub hy.2.1, hCsub hy.2.2⟩⟩
  have hφY : φ a ∈ Y := by rw [hφa]; exact ⟨h0A, h0B, hwC⟩
  let X := (T.source ∩ φ ⁻¹' Y) ∩ W
  have hX : IsOpen X := (T.isOpen_inter_preimage hY).inter hW
  have haX : a ∈ X := ⟨⟨hTa, hφY⟩, haW⟩
  have hXU : X ⊆ U := fun _ hx => hWU hx.2
  have hYT : Y ⊆ T.target := fun _ hy => (hYsub _ hy).1.1
  have hInvX : MapsTo T.symm Y X := by
    intro y hy
    refine ⟨⟨T.map_target (hYT hy), ?_⟩, (hYsub y hy).1.2⟩
    change φ (T.symm y) ∈ Y
    rw [show φ (T.symm y) = y from T.right_inv (hYT hy)]
    exact hy
  have hBij : BijOn φ X Y := by
    refine ⟨fun _ hx => hx.1.2, T.injOn.mono (fun _ hx => hx.1.1), ?_⟩
    intro y hy
    exact ⟨T.symm y, hInvX hy, T.right_inv (hYT hy)⟩
  have hleft : LeftInvOn T.symm φ X := fun _ hx => T.left_inv hx.1.1
  have hright : RightInvOn T.symm φ Y := fun _ hy => T.right_inv (hYT hy)
  have hInvCr : CrOn r Y T.symm :=
    (crOn_iff_contDiffOn r Y T.symm hY).mpr (fun y hy => (show ContDiffAt ℝ (r : ℕ∞ω) T.symm y from (hYsub y hy).2).contDiffWithinAt)
  have hφCr : CrOn r X φ := (crOn_iff_contDiffOn r X φ hX).mpr (hφ.mono hXU)
  have hfeas (x : E n) (hx : x ∈ X) :
      x ∈ Feasible U g h c ↔ (φ x).1 = 0 ∧ ∀ i : I, 0 ≤ (φ x).2.1 i := by
    constructor
    · rintro ⟨_, hgc, hhc⟩
      constructor
      · funext j
        change g x j - c j = 0
        rw [hgc, sub_self]
      · intro i
        exact hhc i.val
    · rintro ⟨hu, hv⟩
      refine ⟨hXU hx, ?_, ?_⟩
      · ext j
        have hj := congrFun hu j
        change g x j - c j = 0 at hj
        exact sub_eq_zero.mp hj
      · intro i
        by_cases hi : h a i = 0
        · exact hv ⟨i, hi⟩
        · exact (hWpos x hx.2 i hi).le
  refine ⟨k, w, X, A, B, C, T.symm, ?_⟩
  refine ⟨?_, hX, hA, hB, hC, haX, h0A, h0B, hwC, hXU, hφa,
    hBij, hInvX, hleft, hright, hφCr, hInvCr, ?_, hfeas, ?_⟩
  · simpa only [Fintype.card_sum, Fintype.card_fin] using hdim
  · intro x hx i hi
    exact hWpos x hx.2 i hi
  · intro y hy
    rw [hfeas (T.symm y) (hInvX hy)]
    rw [hright hy]

end D04
