import Specs.LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
import LinearAlgebraicGroups.Arithmetic.AbsoluteSimpleLocalLie
import LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart
import LinearAlgebraicGroups.Arithmetic.LocalCocharacterEvaluation
import LinearAlgebraicGroups.Arithmetic.PadicLogarithmChart
import LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Batteries.Tactic.OpenPrivate
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Group.Action
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.NoncommPiCoprod
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup

noncomputable section

open Set Filter MeasureTheory Topology
open scoped LinearAlgebra.Projectivization BigOperators
open scoped LinearAlgebraicGroups.Specs.Arithmetic.ProjectiveRecurrence

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence

open LinearAlgebraicGroups.Specs.Arithmetic.ProjectiveRecurrence

section Coordinates

variable {K V ι : Type*} [NormedField K] [AddCommGroup V] [Module K V]

/-- Ratio of absolute values of two homogeneous coordinates. The denominator must be
nonzero on any of the positive bounded intervals used below. -/
private def ratio (b : V ≃ₗ[K] (ι → K)) (i j : ι) (x : ℙ K V) : ℝ :=
  Projectivization.lift (fun v : {v : V // v ≠ 0} ↦ ‖b v.1 i‖ / ‖b v.1 j‖) (by
    intro a c t h
    have ht : t ≠ 0 := by
      rintro rfl
      exact a.2 (by simpa using h)
    rw [h, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr ht)) x

private theorem ratio_mk (b : V ≃ₗ[K] (ι → K)) (i j : ι) (v : V) (hv : v ≠ 0) :
    ratio b i j (Projectivization.mk K v hv) = ‖b v i‖ / ‖b v j‖ := rfl

private theorem isOpen_ratioBand [TopologicalSpace V] (b : V ≃ₗ[K] (ι → K))
    (hb : Continuous b) (i j : ι) {l u : ℝ} :
    IsOpen {x : ℙ K V | l < ratio b i j x ∧ ratio b i j x < u ∧
      ‖b x.rep j‖ ≠ 0} := by
  change IsOpen ((Projectivization.mk' K (V := V)) ⁻¹' _)
  let f (v : {v : V // v ≠ 0}) := ‖b v.1 i‖
  let g (v : {v : V // v ≠ 0}) := ‖b v.1 j‖
  have hf : Continuous f := ((continuous_apply i).comp (hb.comp continuous_subtype_val)).norm
  have hg : Continuous g := ((continuous_apply j).comp (hb.comp continuous_subtype_val)).norm
  convert (isOpen_lt (continuous_const.mul hg) hf).inter
    ((isOpen_lt hf (continuous_const.mul hg)).inter (isOpen_ne_fun hg continuous_const)) using 1
  ext v
  rcases v with ⟨v, hv⟩
  obtain ⟨t, ht⟩ := Projectivization.exists_smul_eq_mk_rep K v hv
  simp only [mem_preimage, Projectivization.mk'_eq_mk, mem_ofPred_eq, mem_inter_iff, ratio_mk]
  have hn : ‖b (Projectivization.mk K v hv).rep j‖ ≠ 0 ↔ ‖b v j‖ ≠ 0 := by
    rw [← ht, Units.smul_def, map_smul]
    change ‖(t : K) * b v j‖ ≠ 0 ↔ ‖b v j‖ ≠ 0
    simp [norm_mul, Units.ne_zero t]
  rw [hn]
  change (l < ‖b v i‖ / ‖b v j‖ ∧ ‖b v i‖ / ‖b v j‖ < u ∧ ‖b v j‖ ≠ 0) ↔
    l * ‖b v j‖ < ‖b v i‖ ∧ ‖b v i‖ < u * ‖b v j‖ ∧ ‖b v j‖ ≠ 0
  by_cases h : ‖b v j‖ = 0
  · simp [h]
  · rw [lt_div_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)),
        div_lt_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h))]

private theorem ratio_smul (b : V ≃ₗ[K] (ι → K)) (a : V ≃ₗ[K] V) (d : ι → K)
    (ha : ∀ v i, b (a v) i = d i * b v i) (i j : ι) (x : ℙ K V) :
    ratio b i j (a • x) = (‖d i‖ / ‖d j‖) * ratio b i j x := by
  induction x using Projectivization.ind with
  | h v hv =>
    simp only [Projectivization.smul_mk, ratio_mk, LinearEquiv.smul_def, ha, norm_mul]
    exact mul_div_mul_comm _ _ _ _

private theorem ratio_iterate (b : V ≃ₗ[K] (ι → K)) (a : V ≃ₗ[K] V) (d : ι → K)
    (ha : ∀ v i, b (a v) i = d i * b v i) (i j : ι) (x : ℙ K V) (n : ℕ) :
    ratio b i j ((a • ·)^[n] x) = (‖d i‖ / ‖d j‖) ^ n * ratio b i j x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ratio_smul b a d ha, ih, pow_succ', mul_assoc]

theorem projectiveHausdorff : ProjectiveHausdorff := by
  intro K V ι _ _ _ _ b hb hb'
  let U := {v : V // v ≠ 0}
  let : MulAction Kˣ U :=
    { smul := fun c v ↦ ⟨c • v.1, (smul_ne_zero_iff_ne c).2 v.2⟩
      one_smul := fun v ↦ Subtype.ext (one_smul _ v.1)
      mul_smul := fun a c v ↦ Subtype.ext (mul_smul a c v.1) }
  have : ContinuousConstSMul Kˣ U := ⟨fun c ↦ by
    have hc : Continuous (fun v : U ↦ ((c : K) • v.1 : V)) := by
      have hcoord : Continuous (fun v : U ↦ (c : K) • b v.1) := by
        apply continuous_pi
        exact fun i ↦ continuous_const.mul ((continuous_apply i).comp (hb.comp continuous_subtype_val))
      have eq : (fun v : U ↦ (c : K) • v.1) = b.symm ∘ (fun v : U ↦ (c : K) • b v.1) := by
        funext v
        change _ = b.symm ((c : K) • b v.1)
        rw [← map_smul, b.symm_apply_apply]
      rw [eq]
      exact hb'.comp hcoord
    exact hc.subtype_mk _⟩
  let q := Projectivization.mk' K (V := V)
  have hq : IsOpenQuotientMap q := by
    refine ⟨?_, continuous_coinduced_rng, ?_⟩
    · intro x
      exact ⟨⟨x.rep, x.rep_nonzero⟩, x.mk_rep⟩
    · intro S hS
      change IsOpen (q ⁻¹' (q '' S))
      have he : q ⁻¹' (q '' S) = ⋃ c : Kˣ, (c • · : U → U) ⁻¹' S := by
        ext u
        simp only [mem_preimage, mem_iUnion, mem_image]
        constructor
        · rintro ⟨y, hy, he⟩
          obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff K _ _ y.2 u.2).mp he
          have hm : c • u = y := Subtype.ext hc
          exact ⟨c, hm.symm ▸ hy⟩
        · rintro ⟨c, hc⟩
          refine ⟨c • u, hc, ?_⟩
          exact (Projectivization.mk_eq_mk_iff K _ _ (c • u).2 u.2).mpr ⟨c, rfl⟩
      rw [he]
      exact isOpen_iUnion fun c ↦ hS.preimage (continuous_const_smul c)
  apply (t2Space_iff_of_isOpenQuotientMap hq).2
  have hr : {v : U × U | Projectivization.mk' K v.1 = Projectivization.mk' K v.2} =
      ⋂ i : ι, ⋂ j : ι, {v : U × U | b v.1.1 i * b v.2.1 j = b v.2.1 i * b v.1.1 j} := by
    ext v
    simp only [mem_ofPred_eq, mem_iInter, Projectivization.mk'_eq_mk, Projectivization.mk_eq_mk_iff']
    constructor
    · rintro ⟨c, hc⟩ i j
      rw [← hc, map_smul]
      change c * b v.2.1 i * b v.2.1 j = b v.2.1 i * (c * b v.2.1 j)
      ring
    · intro heq
      have hwn : b v.2.1 ≠ 0 := fun h ↦ v.2.2 (b.injective (by rw [h, map_zero]))
      obtain ⟨j, hj⟩ : ∃ j, b v.2.1 j ≠ 0 := by
        by_contra! h
        exact hwn (funext h)
      refine ⟨b v.1.1 j / b v.2.1 j, b.injective (funext fun i ↦ ?_)⟩
      rw [map_smul]
      change (b v.1.1 j / b v.2.1 j) * b v.2.1 i = b v.1.1 i
      rw [div_mul_eq_mul_div]
      exact ((eq_div_iff hj).2 (by
        rw [mul_comm (b v.1.1 j) (b v.2.1 i)]
        exact heq i j)).symm
  rw [hr]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  have hcoord (i : ι) : Continuous (fun v : U ↦ b v.1 i) :=
    (continuous_apply i).comp (hb.comp continuous_subtype_val)
  exact isClosed_eq (((hcoord i).comp continuous_fst).mul ((hcoord j).comp continuous_snd))
    (((hcoord i).comp continuous_snd).mul ((hcoord j).comp continuous_fst))

private theorem ratioBand_null [TopologicalSpace V]
    [MeasurableSpace (ℙ K V)] [BorelSpace (ℙ K V)]
    (b : V ≃ₗ[K] (ι → K)) (hb : Continuous b) (a : V ≃ₗ[K] V) (d : ι → K)
    (ha : ∀ v i, b (a v) i = d i * b v i)
    (μ : Measure (ℙ K V)) [IsFiniteMeasure μ] (hm : MeasurePreserving (a • ·) μ μ)
    (i j : ι) (hij : ‖d i‖ < ‖d j‖) {l u : ℝ} (hl : 0 < l) (_hu : 0 < u) :
    μ {x | l < ratio b i j x ∧ ratio b i j x < u ∧ ‖b x.rep j‖ ≠ 0} = 0 := by
  let s : Set (ℙ K V) := {x | l < ratio b i j x ∧ ratio b i j x < u ∧ ‖b x.rep j‖ ≠ 0}
  let q := ‖d i‖ / ‖d j‖
  have hq₀ : 0 ≤ q := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hq₁ : q < 1 := (div_lt_one (lt_of_le_of_lt (norm_nonneg _) hij)).2 hij
  have ht : Tendsto (fun n : ℕ ↦ q ^ n * u) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq₀ hq₁).mul_const u
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hl))
  have heq : {x ∈ s | ∀ m ≥ N, (a • ·)^[m] x ∉ s} = s := by
    ext x
    refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
    intro m hmN hm'
    have h' : l < ratio b i j ((a • ·)^[m] x) := hm'.1
    rw [ratio_iterate b a d ha] at h'
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_left h.2.1.le (pow_nonneg hq₀ _)).trans
      (hN m hmN).le)) h'
  have ho : IsOpen s := isOpen_ratioBand b hb i j
  change μ s = 0
  rw [← heq]
  exact hm.conservative.measure_mem_forall_ge_image_notMem_eq_zero ho.nullMeasurableSet N

theorem supportInWeightLines : SupportInWeightLines := by
  intro K V ι _ _ _ _ _ _ b hb a d ha hs μ _ hm x hx
  have hnonzero : b x.rep ≠ 0 := fun h ↦ x.rep_nonzero (b.injective (by simpa using h))
  obtain ⟨i, hi⟩ : ∃ i, b x.rep i ≠ 0 := by
    by_contra! h
    exact hnonzero (funext h)
  have sameWeight (j : ι) (hj : b x.rep j ≠ 0) : ‖d i‖ = ‖d j‖ := by
    suffices noStrict : ∀ p q, b x.rep p ≠ 0 → b x.rep q ≠ 0 → ‖d p‖ < ‖d q‖ → False by
      exact le_antisymm (le_of_not_gt (noStrict j i hj hi)) (le_of_not_gt (noStrict i j hi hj))
    intro p q hp hq hpq
    let r := ratio b p q x
    have hr : 0 < r := by
      rw [show r = ratio b p q (Projectivization.mk K x.rep x.rep_nonzero) by rw [Projectivization.mk_rep]]
      rw [ratio_mk]
      exact div_pos (norm_pos_iff.mpr hp) (norm_pos_iff.mpr hq)
    let s : Set (ℙ K V) := {y | r / 2 < ratio b p q y ∧ ratio b p q y < r * 2 ∧ ‖b y.rep q‖ ≠ 0}
    have hxs : x ∈ s := ⟨by change r / 2 < r; linarith, by change r < r * 2; linarith,
      norm_ne_zero_iff.mpr hq⟩
    have hopen : IsOpen s := isOpen_ratioBand b hb p q
    have hnull : μ s = 0 := ratioBand_null b hb a d ha μ hm p q hpq
      (by positivity) (by positivity)
    exact (ne_of_gt ((Measure.mem_support_iff_forall x).mp hx s (hopen.mem_nhds hxs))) hnull
  refine ⟨d i, b.injective (funext fun j ↦ ?_)⟩
  rw [ha, map_smul]
  change d j * b x.rep j = d i * b x.rep j
  by_cases hj : b x.rep j = 0
  · simp [hj]
  · rw [hs i j (sameWeight j hj)]

end Coordinates

private theorem exteriorProduct_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} {v : Fin n → V} (hv : LinearIndependent K v) :
    exteriorPower.ιMulti K n v ≠ 0 := by
  let e : Fin n ↪o Fin n := (OrderIso.refl _).toOrderEmbedding
  simpa [exteriorPower.ιMulti_family, e] using
    (exteriorPower.ιMulti_family_linearIndependent_field n hv).ne_zero
      (Set.powersetCard.ofFinEmbEquiv e)

private theorem wedge_eq_zero_iff {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} {v : Fin n → V} (hv : LinearIndependent K v) (z : V) :
    ExteriorAlgebra.ι K z * ExteriorAlgebra.ιMulti K n v = 0 ↔
      z ∈ Submodule.span K (Set.range v) := by
  have hcons : ExteriorAlgebra.ιMulti K (n + 1) (Fin.cons z v) =
      ExteriorAlgebra.ι K z * ExteriorAlgebra.ιMulti K n v := by
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    rfl
  rw [← hcons, ← exteriorPower.ιMulti_apply_coe, Submodule.coe_eq_zero]
  constructor
  · intro h
    by_contra hz
    exact exteriorProduct_ne_zero (linearIndependent_finCons.mpr ⟨hv, hz⟩) h
  · intro h
    exact (exteriorPower.ιMulti K (n + 1)).map_linearDependent (Fin.cons z v) (by
      simpa only [linearIndependent_finCons, hv, true_and, not_not] using h)

theorem exteriorLinePreservation : ExteriorLinePreservation := by
  intro K V _ _ _ n v hv
  have hn := exteriorProduct_ne_zero hv
  refine ⟨hn, fun a ↦ ?_⟩
  rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  change (∃ c : K, c • exteriorPower.ιMulti K n v =
    exteriorPower.map n a.toLinearMap (exteriorPower.ιMulti K n v)) ↔ _
  rw [exteriorPower.map_apply_ιMulti]
  let W := Submodule.span K (Set.range v)
  change _ ↔ ∀ z ∈ W, a z ∈ W
  constructor
  · rintro ⟨c, hc⟩ z hz
    have hav : LinearIndependent K (a ∘ v) := hv.map' a.toLinearMap (LinearMap.ker_eq_bot.mpr a.injective)
    have hc0 : c ≠ 0 := by
      intro h
      exact exteriorProduct_ne_zero hav (by simpa [h] using hc.symm)
    have hwed : ExteriorAlgebra.ιMulti K n (a ∘ v) = c • ExteriorAlgebra.ιMulti K n v :=
      congrArg Subtype.val hc.symm
    have hm : a z ∈ Submodule.span K (Set.range (a ∘ v)) := by
      rw [Set.range_comp]
      change a z ∈ Submodule.span K (a.toLinearMap '' Set.range v)
      rw [← Submodule.map_span]
      exact Submodule.mem_map_of_mem hz
    rw [← wedge_eq_zero_iff hav, hwed, mul_smul_comm, smul_eq_zero, or_iff_right hc0,
      wedge_eq_zero_iff hv] at hm
    exact hm
  · intro ha
    let b : Fin n → W := fun i ↦ ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
    let ab : Fin n → W := fun i ↦ ⟨a (v i), ha _ (b i).2⟩
    have hb : LinearIndependent K b := by
      refine LinearIndependent.of_comp W.subtype ?_
      exact hv
    have hw : Module.finrank K W = n := by
      simpa [W] using finrank_span_eq_card hv
    have : Module.Finite K W := Module.Finite.of_basis (Module.Basis.span hv)
    have hdim : Module.finrank K (⋀[K]^n W) = 1 := by rw [exteriorPower.finrank_eq, hw, Nat.choose_self]
    obtain ⟨x, hx, hspan⟩ := finrank_eq_one_iff'.mp hdim
    have hne := exteriorProduct_ne_zero hb
    obtain ⟨s, hs⟩ := hspan (exteriorPower.ιMulti K n b)
    obtain ⟨t, ht⟩ := hspan (exteriorPower.ιMulti K n ab)
    have hs0 : s ≠ 0 := by
      intro h
      exact hne (by simpa [h] using hs.symm)
    refine ⟨t / s, ?_⟩
    have he : (t / s) • exteriorPower.ιMulti K n b = exteriorPower.ιMulti K n ab := by
      rw [← hs, smul_smul, div_mul_cancel₀ _ hs0, ht]
    simpa only [map_smul, exteriorPower.map_apply_ιMulti, Function.comp_def,
      Submodule.coe_subtype, b, ab, LinearEquiv.coe_coe] using
      congrArg (exteriorPower.map n W.subtype) he

private theorem continuous_projective_smul {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
    (a : V ≃ₗ[K] V) (ha : Continuous a) : Continuous (a • · : ℙ K V → ℙ K V) := by
  rw [continuous_coinduced_dom]
  have hm : Continuous (Projectivization.mk' K (V := V)) := continuous_coinduced_rng
  let f : {v : V // v ≠ 0} → {v : V // v ≠ 0} :=
    fun v ↦ ⟨a v.1, fun h ↦ v.2 (map_eq_zero_iff a a.injective |>.mp h)⟩
  have hf : Continuous f := (ha.comp continuous_subtype_val).subtype_mk _
  exact hm.comp hf

theorem projectiveOrbitMeasure : ProjectiveOrbitMeasure := by
  intro P J K V _ _ _ _ _ _ _ _ _ _ L q hq ρ x hx hcont hact hμ
  let : MeasurableSpace (P ⧸ L) := borel (P ⧸ L)
  have : BorelSpace (P ⧸ L) := ⟨rfl⟩
  obtain ⟨μ, hfin, hpos, hinv⟩ := hμ
  let F := orbitMap L q ρ x hx
  have hF : Continuous F := (QuotientGroup.isQuotientMap_mk L).continuous_iff.mpr hcont
  let ν := μ.map F
  have hRange : Set.range F = Set.range (fun j : J ↦ ρ j • x) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective z
      exact ⟨q p, rfl⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨p, rfl⟩ := hq j
      exact ⟨QuotientGroup.mk p, rfl⟩
  have hsupport : ν.support = closure (Set.range F) := by
    apply le_antisymm
    · apply Measure.support_subset_of_isClosed isClosed_closure
      apply ae_iff.mpr
      change μ.map F (closure (Set.range F))ᶜ = 0
      rw [Measure.map_apply hF.measurable isClosed_closure.isOpen_compl.measurableSet]
      have hempty : F ⁻¹' (closure (Set.range F))ᶜ = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact hy (subset_closure (Set.mem_range_self y))
      rw [hempty, measure_empty]
    · apply closure_minimal _ ν.isClosed_support
      rintro _ ⟨y, rfl⟩
      rw [Measure.support_eq_forall_isOpen]
      intro U hy hU
      have ho : IsOpen (F ⁻¹' U) := hU.preimage hF
      have hn : (F ⁻¹' U).Nonempty := ⟨y, hy⟩
      rw [Measure.map_apply hF.measurable hU.measurableSet]
      exact ho.measure_pos μ hn
  refine ⟨ν, by infer_instance, ?_, by rw [← hRange]; exact hsupport, ?_⟩
  · intro j
    obtain ⟨p, rfl⟩ := hq j
    have hp := measurePreserving_smul p μ
    have ht : Measurable (ρ (q p) • · : ℙ K V → ℙ K V) :=
      (continuous_projective_smul _ (hact (q p))).measurable
    refine ⟨ht, ?_⟩
    have hcomm : (ρ (q p) • ·) ∘ F = F ∘ (p • ·) := by
      funext y
      obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective y
      change ρ (q p) • (ρ (q r) • x) = ρ (q (p * r)) • x
      rw [map_mul, map_mul, mul_smul]
    change (μ.map F).map (ρ (q p) • ·) = μ.map F
    rw [Measure.map_map ht hF.measurable, hcomm,
      ← Measure.map_map hF.measurable hp.measurable, hp.map_eq]
  · intro hc ht
    rw [← hRange, hsupport]
    exact (isCompact_range hF).isClosed.closure_eq

private theorem fixed_of_mem_weightLines {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (a : V ≃ₗ[K] V) {y : ℙ K V} (hy : y ∈ weightLines a) : a • y = y := by
  obtain ⟨c, hc⟩ := hy
  rw [← y.mk_rep, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨c, hc.symm⟩

theorem conjugatesFixOrbitLine : ConjugatesFixOrbitLine := by
  intro P J K V ι _ _ _ _ _ _ _ _ L q hq ρ x hx hcont hact hμ a b hb d hd hs g
  let : MeasurableSpace (ℙ K V) := borel _
  have : BorelSpace (ℙ K V) := ⟨rfl⟩
  obtain ⟨ν, hfin, hinv, hsupport, _⟩ := projectiveOrbitMeasure L q hq ρ x hx hcont hact hμ
  have hmem : ρ g⁻¹ • x ∈ ν.support := by
    rw [hsupport]
    exact subset_closure ⟨g⁻¹, rfl⟩
  have hfix := fixed_of_mem_weightLines (ρ a)
    (supportInWeightLines b hb (ρ a) d hd hs ν (hinv a) hmem)
  rw [map_mul, map_mul, mul_smul, mul_smul, hfix, ← mul_smul, ← map_mul, mul_inv_cancel,
    map_one, one_smul]

theorem containsContractedElements : ContainsContractedElements := by
  intro G _ _ _ N _ hN a u ha h
  have hm (n : ℕ) : (a ^ n * u * (a ^ n)⁻¹) * u⁻¹ ∈ N := by
    have hn := N.pow_mem ha n
    have hc := (inferInstance : N.Normal).conj_mem (a ^ n)⁻¹ (N.inv_mem hn) u
    simpa only [mul_assoc] using N.mul_mem hn hc
  have hlim : Tendsto (fun n : ℕ ↦ (a ^ n * u * (a ^ n)⁻¹) * u⁻¹) atTop (𝓝 u⁻¹) := by
    simpa only [one_mul] using h.mul tendsto_const_nhds
  exact N.inv_mem_iff.mp (hN.mem_of_tendsto hlim (Eventually.of_forall hm))

theorem normalClosureContainsContracted : NormalClosureContainsContracted := by
  intro G _ _ _ A a u ha hu
  let N := Subgroup.normalClosure A
  letI := Subgroup.is_normal_topologicalClosure N
  exact containsContractedElements N.topologicalClosure N.isClosed_topologicalClosure
    (N.le_topologicalClosure (Subgroup.subset_normalClosure ha)) hu

theorem contractedElementsFixLine : ContractedElementsFixLine := by
  intro G X _ _ _ _ _ _ x hcont A h a u ha hu
  let S := MulAction.stabilizer G x
  have hS : IsClosed (S : Set G) := isClosed_singleton.preimage hcont
  let C := (Subgroup.normalClosure A).topologicalClosure
  have hC : C ≤ S := by
    apply Subgroup.topologicalClosure_minimal _ _ hS
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro z hz
    obtain ⟨b, hb, g, hg⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    have hg' : (g : G) * b = z * (g : G) := hg
    have he : z = (g : G) * b * (g : G)⁻¹ := by
      rw [hg', mul_assoc, mul_inv_cancel, mul_one]
    change z • x = x
    rw [he]
    exact h b hb g
  have : C.Normal := Subgroup.is_normal_topologicalClosure (Subgroup.normalClosure A)
  exact hC (containsContractedElements C (Subgroup.isClosed_topologicalClosure _)
    (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ha)) hu)

private theorem exteriorWeights {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [LinearOrder ι] (n : ℕ) (b : Module.Basis ι K V) (a : V ≃ₗ[K] V)
    (t : K) (ht : t ≠ 0) (w : ι → ℤ) (ha : ∀ i, a (b i) = t ^ (w i) • b i)
    (s : Set.powersetCard ι n) :
    exteriorEquiv n a (b.exteriorPower n s) =
      t ^ (∑ j : Fin n, w (Set.powersetCard.ofFinEmbEquiv.symm s j)) • b.exteriorPower n s := by
  rw [exteriorPower.basis_apply]
  change exteriorPower.map n a.toLinearMap
    (exteriorPower.ιMulti K n (b ∘ Set.powersetCard.ofFinEmbEquiv.symm s)) = _
  rw [exteriorPower.map_apply_ιMulti]
  simp only [Function.comp_def, LinearEquiv.coe_coe, ha]
  rw [AlternatingMap.map_smul_univ]
  congr 1
  symm
  induction (Finset.univ : Finset (Fin n)) using Finset.cons_induction_on with
  | empty => simp
  | cons i u hi ih => rw [Finset.sum_cons, Finset.prod_cons, zpow_add₀ ht, ih]

set_option maxHeartbeats 400000 in
theorem conjugatesPreserveSubspace : ConjugatesPreserveSubspace := by
  classical
  intro P J K V ι _ _ _ _ _ _ _ _ _ _ _ L q hq hqc ρ b hρ W hW hμ a t ht ht1 w hw
  have : Module.Finite K V := Module.Finite.of_basis b
  let B := Module.finBasis K W
  let n := Module.finrank K W
  let v : Fin n → V := fun i ↦ B i
  have hv : LinearIndependent K v :=
    B.linearIndependent.map' W.subtype W.ker_subtype
  have hspan : Submodule.span K (Set.range v) = W := by
    change Submodule.span K (Set.range (W.subtype ∘ B)) = W
    rw [Set.range_comp, ← Submodule.map_span, B.span_eq, Submodule.map_top, W.range_subtype]
  obtain ⟨hn, hline⟩ := exteriorLinePreservation n v hv
  let X := (⋀[K]^n V)
  let β : Module.Basis (Set.powersetCard ι n) K X := b.exteriorPower n
  let e := β.equivFun
  let : TopologicalSpace X := TopologicalSpace.induced e inferInstance
  have he : Continuous e := continuous_induced_dom
  let σ := exteriorRepresentation n ρ
  let x : ℙ K X := Projectivization.mk K (exteriorPower.ιMulti K n v) hn
  have hx : ∀ p ∈ L, σ (q p) • x = x := fun p hp ↦ (hline _).2 (by simpa [hspan] using hW p hp)
  have horbit : Continuous (fun j : J ↦ σ j • x) := by
    have hvectors : Continuous (fun j : J ↦ exteriorPower.ιMulti K n (fun i ↦ ρ j (v i)) : J → X) := by
      apply continuous_induced_rng.mpr
      apply continuous_pi
      intro s
      change Continuous (fun j : J ↦ β.repr (exteriorPower.ιMulti K n (fun i ↦ ρ j (v i))) s)
      have coords (j : J) : β.repr (exteriorPower.ιMulti K n (fun i ↦ ρ j (v i))) s =
          (Matrix.of (fun i l ↦ b.coord (Set.powersetCard.ofFinEmbEquiv.symm s l) (ρ j (v i)))).det := by
        change (b.exteriorPower n).repr _ s = _
        rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
      simp_rw [coords]
      exact (continuous_matrix (fun i j ↦ hρ (v i) (Set.powersetCard.ofFinEmbEquiv.symm s j))).matrix_det
    have hnv (j : J) : exteriorPower.ιMulti K n (fun i ↦ ρ j (v i)) ≠ 0 :=
      exteriorProduct_ne_zero (hv.map' (ρ j).toLinearMap (LinearMap.ker_eq_bot.mpr (ρ j).injective))
    have hm : Continuous (Projectivization.mk' K (V := X)) := continuous_coinduced_rng
    have hfun : (fun j : J ↦ σ j • x) = fun j ↦
        Projectivization.mk K (exteriorPower.ιMulti K n (fun i ↦ ρ j (v i))) (hnv j) := by
      funext j
      dsimp only [x]
      rw [Projectivization.smul_mk]
      have hmap : σ j (exteriorPower.ιMulti K n v) =
          exteriorPower.ιMulti K n (fun i ↦ ρ j (v i)) :=
        exteriorPower.map_apply_ιMulti _ _
      simp only [LinearEquiv.smul_def, Projectivization.mk_eq_mk_iff']
      exact ⟨1, by simpa only [one_smul] using hmap.symm⟩
    rw [hfun]
    exact hm.comp (hvectors.subtype_mk hnv)
  have hlinear (j : J) : Continuous (σ j : X → X) := by
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro i
    have hsum : (fun x : X ↦ e (σ j x) i) = fun x ↦ ∑ s, (e x s) * e (σ j (β s)) i := by
      funext u
      calc
        e (σ j u) i = e (σ j (∑ s, (e u s) • β s)) i :=
          congrArg (fun x ↦ e (σ j x) i) (β.sum_equivFun u).symm
        _ = _ := by simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    change Continuous (fun x : X ↦ e (σ j x) i)
    rw [hsum]
    exact continuous_finsetSum _ (fun s _ ↦ ((continuous_apply s).comp he).mul continuous_const)
  let d (s : Set.powersetCard ι n) : K :=
    t ^ (∑ j : Fin n, w (Set.powersetCard.ofFinEmbEquiv.symm s j))
  have hd (u : X) (i : Set.powersetCard ι n) : e (σ a u) i = d i * e u i := by
    have hmap : (β.coord i).comp (σ a).toLinearMap = d i • β.coord i := by
      apply β.ext
      intro s
      change β.coord i (σ a (β s)) = d i * β.coord i (β s)
      rw [show σ a (β s) = d s • β s from exteriorWeights n b (ρ a) t ht w hw s]
      rw [map_smul, smul_eq_mul]
      by_cases h : s = i
      · subst s
        rfl
      · rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm h)]
        rw [mul_zero, mul_zero]
    exact DFunLike.congr_fun hmap u
  have hsep (i j : Set.powersetCard ι n) (h : ‖d i‖ = ‖d j‖) : d i = d j := by
    simp only [d, norm_zpow] at h
    exact congrArg (t ^ · : ℤ → K) ((zpow_right_injective₀ (norm_pos_iff.mpr ht) ht1) h)
  have hf := conjugatesFixOrbitLine L q hq σ x hx (horbit.comp hqc) hlinear hμ a e he d hd hsep
  have preserves (j : J) (hj : σ j • x = x) : ∀ u ∈ W, ρ j u ∈ W := by
    simpa only [hspan] using (hline _).mp hj
  refine ⟨fun g ↦ preserves _ (hf g), ?_⟩
  intro g u hu
  have he' : Continuous e.symm := by
    apply continuous_induced_rng.mpr
    have hcomp : (⇑e ∘ ⇑e.symm) = (id : (Set.powersetCard ι n → K) → (Set.powersetCard ι n → K)) :=
      funext e.apply_symm_apply
    rw [hcomp]
    exact continuous_id
  have : T2Space (ℙ K X) := projectiveHausdorff e he he'
  let : MulAction J (ℙ K X) := MulAction.compHom _ σ
  apply preserves u
  have hc (k : J) : σ (k * (g * a * g⁻¹) * k⁻¹) • x = x := by
    simpa only [mul_assoc, mul_inv_rev] using hf (k * g)
  exact contractedElementsFixLine x horbit {g * a * g⁻¹} (fun j hj k ↦ by
    rw [Set.mem_singleton_iff.mp hj]
    exact hc k) (Set.mem_singleton _) hu

theorem simpleAfterRestriction : SimpleAfterRestriction := by
  intro F E L _ _ _ _ _ h
  refine ⟨fun I ↦ ?_, h.non_abelian⟩
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  let J : LieIdeal E L := {
    carrier := {x | ∀ e : E, e • x ∈ I}
    zero_mem' := fun e ↦ by rw [smul_zero]; exact I.zero_mem
    add_mem' := fun hx hy e ↦ by rw [smul_add]; exact I.add_mem (hx e) (hy e)
    smul_mem' := fun e _ hx r ↦ by rw [smul_smul]; exact hx (r * e)
    lie_mem := fun {x y} hy r ↦ by rw [← lie_smul]; exact I.lie_mem (hy r) }
  obtain ⟨y, hy, hy0⟩ : ∃ y ∈ I, y ≠ (0 : L) := by
    by_contra! hn
    exact hI (bot_unique fun y hy ↦ (LieSubmodule.mem_bot _).mpr (hn y hy))
  have hj : ∀ x : L, ⁅x, y⁆ ∈ J := fun x e ↦ by
    rw [← smul_lie]
    exact I.lie_mem hy
  rcases h.eq_bot_or_eq_top J with hbot | htop
  · exfalso
    have hyc : y ∈ LieAlgebra.center E L :=
      (LieModule.mem_maxTrivSubmodule E L L y).mpr (fun x ↦
        (LieSubmodule.mem_bot _).mp (hbot ▸ hj x))
    rcases h.eq_bot_or_eq_top (LieAlgebra.center E L) with hc | hc
    · exact hy0 ((LieSubmodule.mem_bot _).mp (hc ▸ hyc))
    · exact h.non_abelian ((LieAlgebra.isLieAbelian_iff_center_eq_top E L).mpr hc)
  · apply top_unique
    intro x _
    have hx : x ∈ J := htop.symm ▸ LieSubmodule.mem_top x
    simpa using hx 1

theorem containsDivisibleSubgroups : ContainsDivisibleSubgroups := by
  intro G _ _ _ H _ hH
  have : DiscreteTopology (G ⧸ H) := QuotientGroup.discreteTopology_iff.mpr hH
  have : Finite (G ⧸ H) := finite_of_compact_of_discrete
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  intro U hU u hu
  let f : U →* Equiv.Perm (G ⧸ H) := (MulAction.toPermHom G (G ⧸ H)).comp U.subtype
  let n := Nat.card (Equiv.Perm (G ⧸ H))
  obtain ⟨v, hv⟩ := hU ⟨u, hu⟩ n Nat.card_pos
  have hpow : f (⟨u, hu⟩ : U) = 1 := by rw [← hv, map_pow, pow_card_eq_one']
  have hfix := DFunLike.congr_fun hpow (QuotientGroup.mk (s := H) (1 : G))
  change (QuotientGroup.mk (s := H) (u * 1)) = QuotientGroup.mk 1 at hfix
  have hm := QuotientGroup.eq.mp hfix.symm
  simpa using hm

theorem cocompactOpenContainsContracted : CocompactOpenContainsContracted := by
  intro G _ _ _ H _ hH a u hu
  have : H.FiniteIndex := (containsDivisibleSubgroups H hH).1
  let U : OpenSubgroup G := ⟨H, hH⟩
  have hclosed : IsClosed (H : Set G) := U.isClosed
  have hopen : IsOpen (H.normalCore : Set G) :=
    H.normalCore.isOpen_of_isClosed_of_finiteIndex (H.normalCore_isClosed hclosed)
  have he := hu.eventually (hopen.mem_nhds H.normalCore.one_mem)
  obtain ⟨n, hn⟩ := he.exists
  exact H.normalCore_le (by
    have hm := (inferInstance : H.normalCore.Normal).conj_mem _ hn (a ^ n)⁻¹
    simpa only [mul_assoc, inv_mul_cancel_left, inv_inv, inv_mul_cancel, mul_one] using hm)

section LocalLie

open CategoryTheory AlgebraicGeometry
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup IdentityLieStructure Lie)
open Specs.CharacterDescent (Cocharacter)
open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (Index closedSubgroupAlgebraicGroup)
open Specs.PadicLogarithmChart (schemeConjugation)
open Specs.GeometricRadicals (IsUnipotentRadical)
open InfinitesimalCommutator (matrixDifferential)
open AdelicGroups LocalCocharacterEvaluation LinearAlgebraicGroups.CocharacterDynamics
open scoped Matrix.Norms.Operator

universe u

private def subgroupRealization {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    (i : MatrixRealization G) (U : ClosedSubgroup G.val) :
    MatrixRealization (closedSubgroupAlgebraicGroup U) :=
  { size := i.size
    ambient := i.ambient
    matrix := i.matrix
    embedding := U.inclusion ≫ i.embedding
    closed := by
      letI := U.isClosedImmersion
      letI := i.closed
      change IsClosedImmersion (U.inclusion.hom.hom.left ≫ i.embedding.hom.hom.left)
      infer_instance }

private abbrev subgroupPoints {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    (i : MatrixRealization G) (U : ClosedSubgroup G.val) :
    PointsIn (subgroupRealization i U) F →* PointsIn i F :=
  (((groupPointsFunctor F).map U.inclusion).app (CommAlgCat.of F F)).hom

private theorem subgroupMatrix {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    (i : MatrixRealization G) (U : ClosedSubgroup G.val)
    (x : PointsIn (subgroupRealization i U) F) :
    asMatrix (subgroupRealization i U) F x = asMatrix i F (subgroupPoints i U x) := by
  simp only [asMatrix, subgroupRealization, Functor.map_comp, NatTrans.comp_app,
    GrpCat.hom_comp, subgroupPoints]
  rfl

private theorem subgroupDifferential {F : Type u} [Field F] {G : AffineAlgebraicGroup F}
    (i : MatrixRealization G) (U : ClosedSubgroup G.val) (x : Lie F U.group) :
    matrixDifferential (subgroupRealization i U).embedding (subgroupRealization i U).matrix x =
      matrixDifferential i.embedding i.matrix (mapPointKernel U.inclusion x) := by
  unfold matrixDifferential
  congr 4

@[instance_reducible]
private def restrictLieAlgebra (E F L : Type*) [Field E] [Field F] [Algebra E F]
    [LieRing L] [LieAlgebra F L] : LieAlgebra E L where
  toModule := Module.compHom L (algebraMap E F)
  lie_smul t x y := by
    change ⁅x, (algebraMap E F t) • y⁆ = (algebraMap E F t) • ⁅x, y⁆
    exact lie_smul _ _ _

private theorem top_of_simple {E L : Type*} [Field E] [LieRing L] [LieAlgebra E L]
    (hs : LieAlgebra.IsSimple E L) (W : Submodule E L) (hW : W ≠ ⊥)
    (h : ∀ x y : L, y ∈ W → ⁅x, y⁆ ∈ W) : W = ⊤ := by
  let I : LieIdeal E L := { W with lie_mem := fun {x y} hy => h x y hy }
  rcases hs.eq_bot_or_eq_top I with he | he
  · exact (hW (congrArg LieSubmodule.toSubmodule he)).elim
  · exact congrArg LieSubmodule.toSubmodule he

private def matrixConjugation {E B : Type*} [Field E] [Ring B] [Algebra E B]
    (a : Bˣ) : B →ₗ[E] B where
  toFun v := a.val * v * a⁻¹.val
  map_add' x y := by simp only [mul_add, add_mul]
  map_smul' t x := by rw [RingHom.id_apply, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]

private theorem matrixConjugation_mul {E B : Type*} [Field E] [Ring B] [Algebra E B]
    (a b : Bˣ) (v : B) :
    matrixConjugation (E := E) (a * b) v =
      matrixConjugation (E := E) a (matrixConjugation (E := E) b v) := by
  simp only [matrixConjugation, LinearMap.coe_mk, AddHom.coe_mk, Units.val_mul, mul_inv_rev,
    mul_assoc]

private theorem matrixConjugation_one {E B : Type*} [Field E] [Ring B] [Algebra E B]
    (v : B) : matrixConjugation (E := E) 1 v = v := by
  simp [matrixConjugation]

private theorem matrixConjugation_commutator {E B : Type*} [Field E] [Ring B] [Algebra E B]
    (a : Bˣ) (x y : B) :
    matrixConjugation (E := E) a (x * y - y * x) =
      matrixConjugation (E := E) a x * matrixConjugation (E := E) a y -
        matrixConjugation (E := E) a y * matrixConjugation (E := E) a x := by
  rw [map_sub]
  congr 1 <;>
    simp [matrixConjugation, mul_assoc, ← mul_assoc a⁻¹.val a.val]

/-- Transfer the projective recurrence conclusion to the actual adjoint action
of a local cocharacter and all of its conjugates. -/
private theorem localContractingPreserves {P : Type*} {E : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [NontriviallyNormedField E] [CompleteSpace E]
    {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T2Space F]
    [Algebra E F] [FiniteDimensional E F]
    (hscalar : Continuous (algebraMap E F))
    (G : AffineAlgebraicGroup F) (i : MatrixRealization G) (s : IdentityLieStructure G.val)
    (L : Subgroup P) (q : P →* PointsIn i F) (hq : Function.Surjective q) (hqc : Continuous q)
    (hμ : ArithmeticLatticeProjection.FiniteInvariantQuotientMeasure L)
    (c : Cocharacter G.val) (t : Eˣ) (ht : ‖(t : E)‖ < 1) :
    letI := s.lieRing
    letI := s.lieAlgebra
    letI : Module E (Lie F G.val) := Module.compHom (Lie F G.val) (algebraMap E F)
    ∀ W : Submodule E (Lie F G.val),
      (∀ p ∈ L, ∀ x ∈ W, schemeConjugation (q p) x ∈ W) →
      ∀ g b : PointsIn i F,
        (let a : PointsIn i F :=
          cocharacterPoint c (CommAlgCat.of F F) (Units.map (algebraMap E F).toMonoidHom t)
         Tendsto (fun n : ℕ ↦ (g * a * g⁻¹) ^ n * b * ((g * a * g⁻¹) ^ n)⁻¹) atTop (𝓝 1)) →
        ∀ x ∈ W, schemeConjugation b x ∈ W := by
  classical
  letI := s.lieRing
  letI := s.lieAlgebra
  let V := Lie F G.val
  letI : SMul F V := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI : Module E V := Module.compHom V (algebraMap E F)
  letI : IsScalarTower E F V :=
    IsScalarTower.of_algebraMap_smul (R := E) (A := F) (M := V) fun _ _ ↦ rfl
  intro W hW g b hb x hx
  obtain ⟨A, ρ, hρ, _, _, hσ⟩ := adjointEvaluation G i c s
  let d := Module.finBasis E F
  obtain ⟨σ, hσρ, hcont, hdiag⟩ := hσ d hscalar
  have hact (a : PointsIn i F) (v : Lie F G.val) : σ a v = schemeConjugation a v :=
    (hσρ a v).trans (Subtype.ext (hρ a v))
  let basis := d.smulTower A.basis
  letI : LinearOrder (Fin (Module.finrank E F) × ULift.{u} (Fin A.dimension)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Equiv.injective _)
  let a : PointsIn i F :=
    cocharacterPoint c (CommAlgCat.of F F) (Units.map (algebraMap E F).toMonoidHom t)
  rw [← hact]
  exact (conjugatesPreserveSubspace L q hq hqc σ basis (fun v j => hcont v j) W
    (fun p hp v hv => hact (q p) v ▸ hW p hp v hv) hμ a t t.ne_zero ht.ne
      (fun j => A.weight j.2) (hdiag t)).2 g b hb x hx

private theorem tendsto_conjugated_powers {J : Type*} [Group J] [TopologicalSpace J]
    [IsTopologicalGroup J] (g a b : J)
    (h : Tendsto (fun n : ℕ => a ^ n * b * (a ^ n)⁻¹) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ =>
      (g * a * g⁻¹) ^ n * (g * b * g⁻¹) * ((g * a * g⁻¹) ^ n)⁻¹) atTop (𝓝 1) := by
  let f := MulAut.conj g
  have hf : Continuous f := (continuous_const.mul continuous_id).mul continuous_const
  convert (hf.continuousAt.tendsto.comp h) using 1
  · funext n
    simp only [Function.comp_apply, map_mul, map_inv, map_pow, f, MulAut.conj_apply]
  · rw [map_one]

open Specs.PadicLogarithmChart (smallLogarithmSpan schemeConjugation)

private def HasSimpleLie {F : Type u} [Field F] (G : AffineAlgebraicGroup F) : Prop :=
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  LieAlgebra.IsSimple F (Lie F G.val)

/-- The Lie algebra generated by all conjugates of a nonzero direction in a
contracting radical acts on the small-logarithm span. -/
private theorem padicOpenOfFiniteCovolume (p : ℕ) [Fact p.Prime]
    {F : Type u} [NormedField F] [CharZero F] [NormedAlgebra ℚ_[p] F]
    [FiniteDimensional ℚ_[p] F] (G : AffineAlgebraicGroup F) (i : MatrixRealization G)
    (hG : Specs.GeometricRadicals.IsSemisimple G) (hsimple : HasSimpleLie G)
    (hrank : 0 < Specs.RelativeRank.relativeRank G)
    (H : Subgroup (PointsIn i F)) (hH : IsClosed (H : Set (PointsIn i F)))
    (hnd : ¬ DiscreteTopology H) (hμ : ArithmeticLatticeProjection.FiniteInvariantQuotientMeasure H) :
    IsOpen (H : Set (PointsIn i F)) := by
  classical
  let ι := Index.{u} i.size
  let B := Matrix ι ι F
  let V := Lie F G.val
  letI : CompleteSpace F := FiniteDimensional.complete ℚ_[p] F
  letI : CompleteSpace B := inferInstanceAs (CompleteSpace (ι → ι → F))
  letI : FiniteDimensional ℚ_[p] B := inferInstanceAs (FiniteDimensional ℚ_[p] (ι → ι → F))
  letI : IsTopologicalGroup (PointsIn i F) :=
    IsInducing.isTopologicalGroup (asMatrix i F) (.induced _)
  let s := identityLieStructure G
  letI := s.lieRing
  letI := s.lieAlgebra
  letI : SMul F V := s.lieAlgebra.toModule.toDistribMulAction.toMulAction.toSMul
  letI : LieAlgebra ℚ_[p] V := restrictLieAlgebra ℚ_[p] F V
  letI : IsScalarTower ℚ_[p] F V :=
    IsScalarTower.of_algebraMap_smul (R := ℚ_[p]) (A := F) (M := V) fun _ _ ↦ rfl
  obtain ⟨d, hd, hdm, hconj, hbr⟩ := PadicLogarithmChart.matrixLieComparison F G i s
  let δ : V →ₗ[ℚ_[p]] B := LinearMap.restrictScalars ℚ_[p] (M := V) (M₂ := B) d
  have hδ : ∀ x : V, δ x = matrixDifferential i.embedding i.matrix x := hdm
  obtain ⟨T, hT, ⟨c⟩⟩ := PadicLogarithmChart.schemeExponentialChart p F G i hG.1
  let T₀ := T.restrictScalars ℚ_[p]
  have htangent (x : B) : x ∈ T₀ ↔ x ∈ δ.range := by
    change x ∈ (T : Set B) ↔ x ∈ Set.range δ
    rw [hT]
    simp only [Set.mem_range, hδ]
    rfl
  let S := smallLogarithmSpan c H
  let M : Submodule ℚ_[p] B := S.map T₀.subtype
  let W : Submodule ℚ_[p] V := M.comap δ
  have hM : M ≤ δ.range := by
    rintro _ ⟨x, _, rfl⟩
    exact (htangent _).mp x.property
  have hM_preimage {Y : B} (hY : Y ∈ M) : ∃ y ∈ W, δ y = Y := by
    obtain ⟨y, hy⟩ := hM hY
    exact ⟨y, show δ y ∈ M by rwa [hy], hy⟩
  have hinj : Function.Injective δ := hd
  obtain ⟨hne, hstable, hopen⟩ := PadicLogarithmChart.schemeLogarithmSpan p F G i T hT c H hH
  have hWne : W ≠ ⊥ := by
    intro h
    apply hne hnd
    refine le_antisymm (fun x hx => ?_) bot_le
    obtain ⟨y, hy, hxy⟩ := hM_preimage (Submodule.mem_map_of_mem (f := T₀.subtype) hx)
    have hy0 := (Submodule.mem_bot ℚ_[p]).mp (h ▸ hy)
    apply (Submodule.mem_bot ℚ_[p]).mpr
    apply Subtype.ext
    simpa [hy0] using hxy.symm
  have hWfix (g : PointsIn i F) (hg : g ∈ H) (x : V) (hx : x ∈ W) :
      schemeConjugation g x ∈ W := by
    obtain ⟨z, hz, hzx⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hx)
    change d (schemeConjugation g x) ∈ M
    rw [hconj]
    exact hzx ▸ hstable ⟨g, hg⟩ z hz
  have hscalar : Continuous (algebraMap ℚ_[p] F) := (Algebra.linearMap ℚ_[p] F).continuous_of_finiteDimensional
  obtain ⟨t, ht⟩ := contractingScalarExists (E := ℚ_[p])
  obtain ⟨A, _, a, D, z, hz, hz0⟩ := isotropicContractingLie G hG hrank
  let cochar : Cocharacter G.val := a ≫ A.inclusion
  let a₀ : PointsIn i F :=
    cocharacterPoint cochar (CommAlgCat.of F F) (Units.map (algebraMap ℚ_[p] F).toMonoidHom t)
  let j := subgroupRealization i D.contracting
  let m := asMatrix i F
  let mU := asMatrix j F
  let incl := subgroupPoints i D.contracting
  let C (u : Bˣ) := matrixConjugation (E := ℚ_[p]) u
  have hC (g : PointsIn i F) (x : V) : δ (schemeConjugation g x) = C (m g) (δ x) :=
    hconj g x
  have hpres (g : PointsIn i F) (b : PointsIn j F) (Y : B) (hY : Y ∈ M) :
      C (m (g * incl b * g⁻¹)) Y ∈ M := by
    obtain ⟨x, hx, rfl⟩ := hM_preimage hY
    rw [← hC]
    refine localContractingPreserves hscalar G i s H (MonoidHom.id _) Function.surjective_id
      continuous_id hμ cochar t ht W hWfix g (g * incl b * g⁻¹) ?_ x hx
    apply tendsto_conjugated_powers g a₀ (incl b)
    apply contractingEvaluation G i cochar D hscalar t ht
    exact ⟨b, rfl⟩
  obtain ⟨zU, hzU⟩ := hz
  obtain ⟨U, hU, ⟨cU⟩⟩ := PadicLogarithmChart.schemeExponentialChart p F
    (closedSubgroupAlgebraicGroup D.contracting) j (characteristicZeroSmoothness F _)
  have hzT : δ z ∈ U := by
    change δ z ∈ (U : Set (Matrix (Index.{u} j.size) (Index.{u} j.size) F))
    rw [hU]
    exact ⟨zU, (subgroupDifferential i D.contracting zU).trans
      (by rw [hzU, hδ])⟩
  have hbrM (g : PointsIn i F) (Y : B) (hY : Y ∈ M) :
      C (m g) (δ z) * Y - Y * C (m g) (δ z) ∈ M := by
    let N := M.comap (C (m g))
    have hinv (b : PointsIn j F) (y : B) (hy : y ∈ N) : C (mU b) y ∈ N := by
      change C (m g) (C (mU b) y) ∈ M
      have he : C (m g) (C (mU b) y) = C (m (g * incl b * g⁻¹)) (C (m g) y) := by
        rw [show mU b = m (incl b) from subgroupMatrix i D.contracting b]
        simp only [C, ← matrixConjugation_mul, map_mul, map_inv,
          mul_assoc, inv_mul_cancel, mul_one]
      rw [he]
      exact hpres g b _ hy
    have hY' : C (m g)⁻¹ Y ∈ N := by
      change C (m g) (C (m g)⁻¹ Y) ∈ M
      simpa only [C, ← matrixConjugation_mul, mul_inv_cancel, matrixConjugation_one] using hY
    have hh := PadicLogarithmChart.differentiatedInvariance p B
      (U.restrictScalars ℚ_[p]) (PointsIn j F) cU N N.closed_of_finiteDimensional hinv
      ⟨δ z, hzT⟩ (C (m g)⁻¹ Y) hY'
    change C (m g) (δ z * C (m g)⁻¹ Y - C (m g)⁻¹ Y * δ z) ∈ M at hh
    rw [matrixConjugation_commutator] at hh
    simpa only [C, ← matrixConjugation_mul, mul_inv_cancel, matrixConjugation_one] using hh
  let I : Submodule ℚ_[p] V :=
    Submodule.span ℚ_[p] (Set.range fun g : PointsIn i F => schemeConjugation g z)
  have hIg : ∀ g : PointsIn i F, C (m g) (δ z) ∈ I.map δ :=
    fun g => hC g z ▸ Submodule.mem_map_of_mem (Submodule.subset_span ⟨g, rfl⟩)
  have hIstable (g : PointsIn i F) (Y : B) (hY : Y ∈ I.map δ) :
      C (m g) Y ∈ I.map δ := by
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hY
    refine Submodule.span_induction (p := fun x _ => C (m g) (δ x) ∈ I.map δ) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨b, rfl⟩
      rw [hC, ← matrixConjugation_mul, ← map_mul]
      exact hIg (g * b)
    · simpa only [map_zero] using (I.map δ).zero_mem
    · intro x y _ _ hx hy
      simpa only [map_add] using (I.map δ).add_mem hx hy
    · intro a x _ hx
      simpa only [map_smul] using (I.map δ).smul_mem a hx
  have hIne : I ≠ ⊥ := by
    intro h
    have hi : schemeConjugation (1 : PointsIn i F) z ∈ I := Submodule.subset_span ⟨1, rfl⟩
    apply hz0
    apply hinj
    have he := congrArg δ ((Submodule.mem_bot ℚ_[p]).mp (h ▸ hi))
    simpa only [hC, map_one, C, matrixConjugation_one] using he
  have hsimple' := simpleAfterRestriction (F := ℚ_[p]) (E := F) (L := V) hsimple
  have hItop : I = ⊤ := by
    apply top_of_simple hsimple' I hIne
    intro x y hy
    letI : FiniteDimensional ℚ_[p] (I.map δ) :=
      FiniteDimensional.finiteDimensional_submodule (I.map δ)
    have hh := PadicLogarithmChart.differentiatedInvariance p B T₀ (PointsIn i F) c (I.map δ)
      (I.map δ).closed_of_finiteDimensional hIstable ⟨δ x, (htangent _).mpr ⟨x, rfl⟩⟩
      (δ y) (Submodule.mem_map_of_mem hy)
    change δ x * δ y - δ y * δ x ∈ I.map δ at hh
    rw [← show δ ⁅x, y⁆ = δ x * δ y - δ y * δ x from hbr x y] at hh
    exact (Submodule.comap_map_eq_of_injective hinj I) ▸ hh
  have hWtop : W = ⊤ := by
    apply top_of_simple hsimple' W hWne
    intro x y hy
    have hY := Submodule.mem_comap.mp hy
    have hx : x ∈ I := hItop ▸ Submodule.mem_top
    refine Submodule.span_induction (p := fun x _ => ⁅x, y⁆ ∈ W) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨g, rfl⟩
      change δ ⁅schemeConjugation g z, y⁆ ∈ M
      rw [show δ ⁅schemeConjugation g z, y⁆ =
        δ (schemeConjugation g z) * δ y - δ y * δ (schemeConjugation g z) from hbr _ _, hC]
      exact hbrM g (δ y) hY
    · simpa only [zero_lie] using W.zero_mem
    · intro x x' _ _ hx hx'
      simpa only [add_lie] using W.add_mem hx hx'
    · intro a x _ hx
      simpa only [smul_lie] using W.smul_mem a hx
  apply hopen
  refine eq_top_iff.mpr (fun x _ => ?_)
  obtain ⟨y, hy⟩ := (htangent (x : B)).mp x.property
  have hmem : y ∈ W := hWtop ▸ Submodule.mem_top
  obtain ⟨z, hz, he⟩ := Submodule.mem_map.mp (Submodule.mem_comap.mp hmem)
  exact (Subtype.ext (he.trans hy) : z = x) ▸ hz

theorem padicProjection : PadicProjection.{u} := by
  intro p _ F _ _ _ _ G i hG hrank H hH hnd hμ
  have hsimp : HasSimpleLie G := absoluteSimpleLocalLie F G hG (identityLieStructure G)
  have ho := padicOpenOfFiniteCovolume p G i hG.1 hsimp hrank H hH hnd hμ
  refine ⟨ho, fun hcompact => ?_⟩
  letI := hcompact
  letI : IsTopologicalGroup (PointsIn i F) :=
    IsInducing.isTopologicalGroup (asMatrix i F) (.induced _)
  have hs : Continuous (algebraMap ℚ_[p] F) :=
    (Algebra.linearMap ℚ_[p] F).continuous_of_finiteDimensional
  obtain ⟨hindex, hrad⟩ := openCocompactContainsRadicals G i hs H ho
  have hle : Subgroup.closure (parabolicRadicalPoints G) ≤ H := by
    apply (Subgroup.closure_le H).mpr
    rintro x ⟨P, hP, U, hU, hx⟩
    exact hrad P hP U hU hx
  have hle' : (↑(Subgroup.closure (G := PointsIn i F) (parabolicRadicalPoints G)) :
      Set (PointsIn i F)) ⊆ H := hle
  exact ⟨hindex, hle, fun hd => eq_top_iff.mpr (fun x _ => closure_minimal hle' hH (hd x))⟩

end LocalLie

section Archimedean

open CategoryTheory AlgebraicGeometry
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup IdentityLieStructure Lie)
open Specs.CharacterDescent (Cocharacter)
open Specs.IntegralModels (MatrixRealization)
open Specs.PadicLogarithmChart (schemeConjugation)
open Specs.ArchimedeanLieChart
open AdelicGroups LinearAlgebraicGroups.CocharacterDynamics
open scoped Matrix.Norms.Operator

private theorem productEvaluationPreserves {P J K : Type*} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [NormedField K] [Fintype J] [DecidableEq J]
    {A V I : J → Type*} [∀ j, Group (A j)] [∀ j, TopologicalSpace (A j)]
    [∀ j, IsTopologicalGroup (A j)] [∀ j, AddCommGroup (V j)] [∀ j, Module K (V j)]
    [∀ j, Fintype (I j)]
    (L : Subgroup P) (q : P →* (∀ j, A j)) (hq : Function.Surjective q) (hqc : Continuous q)
    (hμ : ArithmeticLatticeProjection.FiniteInvariantQuotientMeasure L)
    (r : ∀ j, A j →* (V j ≃ₗ[K] V j)) (b : ∀ j, Module.Basis (I j) K (V j))
    (hcont : ∀ j x k, Continuous (fun g : A j => (b j).coord k (r j g x)))
    (a : ∀ j, A j) (t : Kˣ) (ht : ‖(t : K)‖ < 1)
    (w : ∀ j, I j → ℤ) (hdiag : ∀ j k, r j (a j) (b j k) = (t : K) ^ (w j k) • b j k)
    (W : Submodule K (∀ j, V j))
    (hW : ∀ p ∈ L, ∀ x ∈ W, (fun j => r j (q p j) (x j)) ∈ W)
    (g : ∀ j, A j) (hg : Tendsto (fun n : ℕ => a ^ n * g * (a ^ n)⁻¹) atTop (𝓝 1))
    (x : ∀ j, V j) (hx : x ∈ W) : (fun j => r j (g j) (x j)) ∈ W := by
  let ρ : (∀ j, A j) →* ((∀ j, V j) ≃ₗ[K] (∀ j, V j)) := {
    toFun g := LinearEquiv.piCongrRight fun j => r j (g j)
    map_one' := LinearEquiv.ext fun x => funext fun j => by
      change r j 1 (x j) = x j
      rw [map_one]
      rfl
    map_mul' g h := LinearEquiv.ext fun x => funext fun j => by
      change r j (g j * h j) (x j) = r j (g j) (r j (h j) (x j))
      rw [map_mul]
      rfl }
  let β := Pi.basis b
  letI : LinearOrder ((j : J) × I j) :=
    LinearOrder.lift' (Fintype.equivFin _) (Equiv.injective _)
  have hρcont (x : ∀ j, V j) (k : (j : J) × I j) :
      Continuous (fun g : ∀ j, A j => β.coord k (ρ g x)) := by
    simp only [β, Module.Basis.coord_apply, Pi.basis_repr]
    exact (hcont k.1 (x k.1) k.2).comp (continuous_apply k.1)
  have hρdiag (k : (j : J) × I j) :
      ρ a (β k) = (t : K) ^ (w k.1 k.2) • β k := by
    rw [show β k = Pi.single k.1 (b k.1 k.2) from Pi.basis_apply b k]
    funext j
    change r j (a j) (Pi.single k.1 (b k.1 k.2) j) =
      (t : K) ^ (w k.1 k.2) • Pi.single k.1 (b k.1 k.2) j
    by_cases h : j = k.1
    · subst j
      simpa only [Pi.single_eq_same] using hdiag k.1 k.2
    · simp only [Pi.single_eq_of_ne h, map_zero, smul_zero]
  exact (conjugatesPreserveSubspace L q hq hqc ρ β hρcont W hW hμ a t t.ne_zero ht.ne
    (fun k => w k.1 k.2) hρdiag).2 1 g (by simpa only [one_mul, inv_one, mul_one] using hg) x hx

set_option maxHeartbeats 600000 in
/-- A coordinate-supported evaluation has the given weights in that
coordinate and weight zero in every other factor. -/
private theorem productContractingPreserves {P : Type*} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] {J : Type u} [Fintype J] [DecidableEq J]
    (F : J → Type u) [∀ j, NormedField (F j)] [∀ j, NormedAlgebra ℝ (F j)]
    [∀ j, FiniteDimensional ℝ (F j)] (G : ∀ j, AffineAlgebraicGroup (F j))
    (i : ∀ j, MatrixRealization (G j)) (s : ∀ j, IdentityLieStructure (G j).val)
    (L : Subgroup P) (q : P →* PointProduct F G i)
    (hq : Function.Surjective q) (hqc : Continuous q)
    (hμ : ArithmeticLatticeProjection.FiniteInvariantQuotientMeasure L)
    (j₀ : J) (c : Cocharacter (G j₀).val) (t : ℝˣ) (ht : ‖(t : ℝ)‖ < 1) :
    letI : ∀ j, LieRing (Lie (F j) (G j).val) := fun j => (s j).lieRing
    letI : ∀ j, LieAlgebra (F j) (Lie (F j) (G j).val) := fun j => (s j).lieAlgebra
    letI : ∀ j, Module ℝ (Lie (F j) (G j).val) :=
      fun j => Module.restrictScalars ℝ (F j) (Lie (F j) (G j).val)
    ∀ W : Submodule ℝ (∀ j, Lie (F j) (G j).val),
      (∀ p ∈ L, ∀ x ∈ W, (fun j => schemeConjugation (G := G j) (q p j) (x j)) ∈ W) →
      ∀ b : PointProduct F G i,
        (let a : PointProduct F G i := Pi.mulSingle j₀
          (cocharacterPoint c (CommAlgCat.of (F j₀) (F j₀))
            (Units.map (algebraMap ℝ (F j₀)).toMonoidHom t))
         Tendsto (fun n : ℕ => a ^ n * b * (a ^ n)⁻¹) atTop (𝓝 1)) →
        ∀ x ∈ W, (fun j => schemeConjugation (G := G j) (b j) (x j)) ∈ W := by
  classical
  let V (j : J) := Lie (F j) (G j).val
  letI : ∀ j, LieRing (V j) := fun j => (s j).lieRing
  letI : ∀ j, LieAlgebra (F j) (V j) := fun j => (s j).lieAlgebra
  letI : ∀ j, SMul (F j) (V j) := fun j => (s j).lieAlgebra.toSMul
  letI : ∀ j, Module ℝ (V j) := fun j => Module.restrictScalars ℝ (F j) (V j)
  letI : ∀ j, IsScalarTower ℝ (F j) (V j) :=
    fun j => IsScalarTower.of_algebraMap_smul (R := ℝ) (A := F j) (M := V j) fun _ _ => rfl
  letI : ∀ j, IsTopologicalGroup (PointsIn (i j) (F j)) :=
    fun j => IsInducing.isTopologicalGroup (asMatrix (i j) (F j)) (.induced _)
  let A (j : J) := PointsIn (i j) (F j)
  let cs : ∀ j, Cocharacter (G j).val := Function.update (fun _ => 0) j₀ c
  let a : PointProduct F G i := Pi.mulSingle j₀
    (cocharacterPoint c (CommAlgCat.of (F j₀) (F j₀))
      (Units.map (algebraMap ℝ (F j₀)).toMonoidHom t))
  let B (j : J) (n : ℕ) := Fin (Module.finrank ℝ (F j)) × ULift.{u} (Fin n)
  have hdata (j : J) : ∃ (n : ℕ) (b : Module.Basis (B j n) ℝ (V j))
      (r : A j →* (V j ≃ₗ[ℝ] V j)) (w : B j n → ℤ),
      (∀ g x, r g x = schemeConjugation (G := G j) g x) ∧
      (∀ x k, Continuous (fun g : A j => b.coord k (r g x))) ∧
      ∀ k, r (a j) (b k) = (t : ℝ) ^ (w k) • b k := by
    obtain ⟨D, r, hr, _, _, hσ⟩ := LocalCocharacterEvaluation.adjointEvaluation
      (G j) (i j) (cs j) (s j)
    let d := Module.finBasis ℝ (F j)
    have hs : Continuous (algebraMap ℝ (F j)) :=
      (Algebra.linearMap ℝ (F j)).continuous_of_finiteDimensional
    obtain ⟨σ, hσr, hc, hw⟩ := hσ d hs
    refine ⟨D.dimension, d.smulTower D.basis, σ, (fun k => if j = j₀ then D.weight k.2 else 0),
      (fun g x => (hσr g x).trans (Subtype.ext (hr g x))), (fun x k => hc x k), ?_⟩
    intro k
    by_cases h : j = j₀
    · subst j
      dsimp only
      rw [ite_eq_left (rfl : j₀ = j₀)]
      rw [show a j₀ = cocharacterPoint (cs j₀) (CommAlgCat.of (F j₀) (F j₀))
          (Units.map (algebraMap ℝ (F j₀)).toMonoidHom t) by simp [a, cs]]
      exact hw t k
    · rw [show a j = 1 from Pi.mulSingle_eq_of_ne h _, map_one]
      simp [h]
  choose n b r w hact hcont hdiag using hdata
  have hρact (g : PointProduct F G i) (x : ∀ j, V j) :
      (fun j => r j (g j) (x j)) = fun j => schemeConjugation (G := G j) (g j) (x j) :=
    funext fun j => hact j (g j) (x j)
  intro W hW u hu x hx
  rw [← hρact]
  exact productEvaluationPreserves (A := A) (V := V) (I := fun j => B j (n j))
    L q hq hqc hμ r b hcont a t ht w hdiag W
    (fun p hp v hv => hρact (q p) v ▸ hW p hp v hv) u hu x hx

private theorem mem_subgroup_of_single {J : Type*} [Fintype J] [DecidableEq J]
    {A : J → Type*} [∀ j, Group (A j)] (H : Subgroup (∀ j, A j)) (g : ∀ j, A j)
    (h : ∀ j, Pi.mulSingle j (g j) ∈ H) : g ∈ H := by
  let m := MonoidHom.noncommPiCoprod (MonoidHom.mulSingle A) Pi.mulSingle_commute
  have hm : m = MonoidHom.id _ := MonoidHom.pi_ext (fun j a =>
    MonoidHom.noncommPiCoprod_mulSingle _ j a)
  have hg : m g ∈ H := H.noncommProd_mem
    (fun _ _ _ _ hne => Pi.mulSingle_commute hne _ _) (fun j _ => h j)
  rwa [hm] at hg

private def matrixStabilizer {J B E : Type*} [Group J] [Ring B] [Field E] [Algebra E B]
    (m : J →* Bˣ) (W : Submodule E B) : Subgroup J where
  carrier := {g | ∀ Y ∈ W, matrixConjugation (E := E) (m g) Y ∈ W ∧
    matrixConjugation (E := E) (m g⁻¹) Y ∈ W}
  one_mem' Y hY := by simpa only [inv_one, map_one, matrixConjugation_one] using And.intro hY hY
  mul_mem' {g h} hg hh Y hY := by
    simp only [Set.mem_setOf_eq] at hg hh
    rw [mul_inv_rev, map_mul, map_mul, matrixConjugation_mul, matrixConjugation_mul]
    exact ⟨(hg _ (hh Y hY).1).1, (hh _ (hg Y hY).2).2⟩
  inv_mem' {g} hg Y hY := by simpa only [inv_inv] using (hg Y hY).symm

private theorem matrixStabilizer_closed {J B E : Type*} [Group J] [TopologicalSpace J]
    [IsTopologicalGroup J] [NormedRing B] [NormedField E] [NormedAlgebra E B]
    (m : J →* Bˣ) (hm : Continuous m) (W : Submodule E B) (hW : IsClosed (W : Set B)) :
    IsClosed (matrixStabilizer m W : Set J) := by
  have h (Y : B) : Continuous (fun g => matrixConjugation (E := E) (m g) Y) := by
    exact ((Units.continuous_val.comp hm).mul continuous_const).mul
      (Units.continuous_val.comp hm.inv)
  have he : (matrixStabilizer m W : Set J) =
      ⋂ Y : W, {g | matrixConjugation (E := E) (m g) Y ∈ W ∧
                       matrixConjugation (E := E) (m g⁻¹) Y ∈ W} := by
    ext g
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun hg Y => hg Y Y.property, fun hg Y hY => hg ⟨Y, hY⟩⟩
  rw [he]
  exact isClosed_iInter (fun Y => (hW.preimage (h Y)).inter
    (hW.preimage ((h Y).comp continuous_inv)))

private theorem expUnit_matrixConjugation {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
    [CompleteSpace B] (a : Bˣ) (X : B) :
    expUnit (matrixConjugation (E := ℝ) a X) = a * expUnit X * a⁻¹ := by
  apply Units.ext
  simp only [ArchimedeanLieChart.expUnit_val, Units.val_mul]
  symm
  apply NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ)
    (MulSemiringAction.toRingHom (ConjAct Bˣ) B (ConjAct.toConjAct a))
    (continuous_const_smul (ConjAct.toConjAct a))
  rw [NormedSpace.expSeries_radius_eq_top]
  exact edist_lt_top _ _

private theorem openNormalContainsContracted {A : Type*} [Group A] [TopologicalSpace A]
    (N : Subgroup A) [N.Normal] (hN : IsOpen (N : Set A)) (a b : A)
    (hb : Tendsto (fun n : ℕ => a ^ n * b * (a ^ n)⁻¹) atTop (𝓝 1)) : b ∈ N := by
  obtain ⟨n, hn⟩ := (hb.eventually (hN.mem_nhds N.one_mem)).exists
  have hh := (inferInstance : N.Normal).conj_mem _ hn (a ^ n)⁻¹
  simpa only [mul_assoc, inv_mul_cancel_left, inv_inv, inv_mul_cancel, mul_one] using hh

open private pointMatrices_closedEmbedding from
  LinearAlgebraicGroups.Arithmetic.ArchimedeanLieChart

set_option maxHeartbeats 850000 in
private theorem archimedeanProductFull {J : Type u} [Fintype J]
    (F : J → Type u) [∀ j, NormedField (F j)] [∀ j, NormedAlgebra ℝ (F j)]
    [∀ j, CompleteSpace (F j)] [∀ j, FiniteDimensional ℝ (F j)] [∀ j, CharZero (F j)]
    (G : ∀ j, AffineAlgebraicGroup (F j)) (i : ∀ j, MatrixRealization (G j))
    (hsimple : ∀ j, HasSimpleLie (G j))
    (hgen : ∀ j, Dense
      (↑(Subgroup.closure (G := PointsIn (i j) (F j)) (cocharacterRadicalPoints (G j))) :
        Set (PointsIn (i j) (F j))))
    (H : Subgroup (PointProduct F G i)) (hH : IsClosed (H : Set (PointProduct F G i)))
    (hnd : ∀ Q : Set J, Q.Nonempty → ¬ _root_.IsDiscrete
      ((fun g : PointProduct F G i => fun j : Q => g j.val) '' (H : Set (PointProduct F G i))))
    (hμ : ArithmeticLatticeProjection.FiniteInvariantQuotientMeasure H) :
    H = ⊤ := by
  classical
  let X := PointProduct F G i
  let B := MatrixProduct F G i
  let A (j : J) := PointsIn (i j) (F j)
  let V (j : J) := Lie (F j) (G j).val
  let s (j : J) := identityLieStructure (G j)
  letI : ∀ j, LieRing (V j) := fun j => (s j).lieRing
  letI : ∀ j, LieAlgebra (F j) (V j) := fun j => (s j).lieAlgebra
  letI : ∀ j, LieAlgebra ℝ (V j) := fun j => restrictLieAlgebra ℝ (F j) (V j)
  letI : ∀ j, IsTopologicalGroup (A j) :=
    fun j => IsInducing.isTopologicalGroup (asMatrix (i j) (F j)) (.induced _)
  letI : IsTopologicalGroup X := inferInstanceAs (IsTopologicalGroup (∀ j, A j))
  letI : FiniteDimensional ℝ B :=
    inferInstanceAs (FiniteDimensional ℝ (∀ j, Matrix _ _ (F j)))
  let m := pointMatrices F G i
  have hm := pointMatrices_closedEmbedding i
  obtain ⟨d, hd, hentry, hamb, hchart, ⟨e, he0, he, _⟩, _, hconj, hderiv⟩ :=
    ArchimedeanLieChart.productChart J F G i s
  obtain ⟨M, eH, hM, hline, heH0, heH, hconjH, _, _, hMfull⟩ := hchart H hH
  let W := M.comap d
  let C (g : X) := matrixConjugation (E := ℝ) (m g)
  have hdc (g : X) (x : ∀ j, V j) :
      d (fun j => schemeConjugation (G := G j) (g j) (x j)) = C g (d x) := by
    obtain ⟨y, hyl, hym⟩ := hconj g x
    have h : (fun j => schemeConjugation (G := G j) (g j) (x j)) = y :=
      funext fun j => Subtype.ext (hyl j).symm
    exact (congrArg d h).trans hym
  have hWH (g : X) (hg : g ∈ H) (x : ∀ j, V j) (hx : x ∈ W) :
      (fun j => schemeConjugation (G := G j) (g j) (x j)) ∈ W := by
    change d _ ∈ M
    rw [hdc]
    exact hconjH ⟨g, hg⟩ ⟨d x, hx⟩
  obtain ⟨t, ht⟩ := LocalCocharacterEvaluation.contractingScalarExists (E := ℝ)
  let ins (j : J) := MonoidHom.mulSingle A j
  have hins (j : J) : Continuous (ins j) := continuous_mulSingle j
  have hcontract (j : J) (b : A j) (hb : b ∈ cocharacterRadicalPoints (G j)) :
      ∃ a : A j, Tendsto (fun n : ℕ => a ^ n * b * (a ^ n)⁻¹) atTop (𝓝 1) := by
    obtain ⟨c, D, hc⟩ := hb
    exact ⟨_, LocalCocharacterEvaluation.contractingEvaluation (G j) (i j) c D
      (Algebra.linearMap ℝ (F j)).continuous_of_finiteDimensional t ht b hc⟩
  have hstabRad (j : J) (b : A j) (hb : b ∈ cocharacterRadicalPoints (G j)) :
      ∀ Y ∈ M, C (ins j b) Y ∈ M := by
    obtain ⟨c, D, hc⟩ := hb
    let a : A j := cocharacterPoint c (CommAlgCat.of (F j) (F j))
      (Units.map (algebraMap ℝ (F j)).toMonoidHom t)
    have hlim : Tendsto (fun n : ℕ => a ^ n * b * (a ^ n)⁻¹) atTop (𝓝 1) :=
      LocalCocharacterEvaluation.contractingEvaluation (G j) (i j) c D
        (Algebra.linearMap ℝ (F j)).continuous_of_finiteDimensional t ht b hc
    have hlim' : Tendsto (fun n : ℕ => (ins j a) ^ n * ins j b * ((ins j a) ^ n)⁻¹) atTop (𝓝 1) := by
      have h : Tendsto (fun n : ℕ => ins j (a ^ n * b * (a ^ n)⁻¹)) atTop (𝓝 (ins j 1)) :=
        ((hins j).continuousAt (x := 1)).tendsto.comp hlim
      simpa only [map_mul, map_inv, map_pow, map_one] using h
    intro Y hY
    obtain ⟨x, rfl⟩ := hM hY
    rw [← hdc]
    exact productContractingPreserves F G i s H (MonoidHom.id X) Function.surjective_id
      continuous_id hμ j c t ht W hWH (ins j b) hlim' x hY
  let N := matrixStabilizer m M
  have hN : IsClosed (N : Set X) :=
    matrixStabilizer_closed m hm.continuous M M.closed_of_finiteDimensional
  have hNfull : N = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    apply mem_subgroup_of_single N
    intro j
    have hclosed : IsClosed ((N.comap (ins j) : Subgroup (A j)) : Set (A j)) :=
      hN.preimage (hins j)
    have hle : (↑(Subgroup.closure (G := A j) (cocharacterRadicalPoints (G j))) :
        Set (A j)) ⊆ (N.comap (ins j) : Subgroup (A j)) := by
      apply (Subgroup.closure_le (N.comap (ins j))).mpr
      intro b hb
      have hb' : b⁻¹ ∈ cocharacterRadicalPoints (G j) := by
        obtain ⟨c, D, hD⟩ := hb
        exact ⟨c, D, Subgroup.inv_mem _ hD⟩
      change ∀ Y ∈ M, C (ins j b) Y ∈ M ∧ C (ins j b)⁻¹ Y ∈ M
      intro Y hY
      rw [← map_inv]
      exact ⟨hstabRad j b hb Y hY, hstabRad j b⁻¹ hb' Y hY⟩
    exact closure_minimal hle hclosed (hgen j (x j))
  have hstable (g : X) (Y : B) (hY : Y ∈ M) : C g Y ∈ M :=
    ((hNfull.symm ▸ Subgroup.mem_top g : g ∈ N) Y hY).1
  have hcomm (x y : ∀ j, V j) (hy : y ∈ W) : (fun j => ⁅x j, y j⁆) ∈ W := by
    let f (t : ℝ) := conjugate (expUnit (t • d x)) (d y)
    have hft (t : ℝ) : f t ∈ M := by
      obtain ⟨g, hg⟩ : expUnit (t • d x) ∈ m.range :=
        (hamb (d x)).mpr ⟨x, rfl⟩ t
      rw [show f t = C g (d y) from by simp only [f, ← hg]; rfl]
      exact hstable g _ hy
    exact M.closed_of_finiteDimensional.mem_of_tendsto (hderiv x y).tendsto_slope_zero
      (Eventually.of_forall fun t => M.smul_mem _ (M.sub_mem (hft (0 + t)) (hft 0)))
  let Wj (j : J) := W.comap (LinearMap.single ℝ V j)
  have hsimple' (j : J) : LieAlgebra.IsSimple ℝ (V j) :=
    simpleAfterRestriction (E := F j) (hsimple j)
  have hsbr (j : J) (a : V j) (x : ∀ j, V j) :
      (fun k => ⁅Pi.single j a k, x k⁆) = Pi.single j ⁅a, x j⁆ := by
    funext k
    by_cases h : k = j
    · subst k
      simp only [Pi.single_eq_same]
    · simp only [Pi.single_eq_of_ne h, zero_lie]
  have hfull (j : J) (hj : Wj j ≠ ⊥) : Wj j = ⊤ := by
    apply top_of_simple (hsimple' j) (Wj j) hj
    intro x y hy
    have h := hcomm (Pi.single j x) (Pi.single j y) hy
    rw [hsbr, Pi.single_eq_same] at h
    exact h
  have hzero (j : J) (hj : Wj j = ⊥) (x : ∀ j, V j) (hx : x ∈ W) : x j = 0 := by
    have hcz : x j ∈ LieAlgebra.center ℝ (V j) := by
      apply (LieModule.mem_maxTrivSubmodule ℝ (V j) (V j) _).mpr
      intro y
      have h := hcomm (Pi.single j y) x hx
      rw [hsbr] at h
      exact (Submodule.mem_bot ℝ).mp (hj ▸ (show ⁅y, x j⁆ ∈ Wj j from h))
    rcases (hsimple' j).eq_bot_or_eq_top (LieAlgebra.center ℝ (V j)) with hb | ht
    · exact (LieSubmodule.mem_bot _).mp (hb ▸ hcz)
    · exact ((hsimple' j).non_abelian ((LieAlgebra.isLieAbelian_iff_center_eq_top _ _).mpr ht)).elim
  have he1 : e 0 = (1 : X) := by
    apply hm.injective
    rw [map_one, he 0 he0]
    simp
  have hfactor (j : J) (hj : Wj j ≠ ⊥) (g : A j) : ins j g ∈ H := by
    let Hj := H.comap (ins j)
    let Nj := Hj.normalCore
    have hNj : IsOpen (Nj : Set (A j)) := by
      apply Nj.isOpen_of_mem_nhds (g := (1 : A j))
      have h1 : ins j 1 ∈ e.target := by rw [map_one, ← he1]; exact e.map_source he0
      refine mem_of_superset ((e.open_target.preimage (hins j)).mem_nhds h1) ?_
      intro a ha b
      have ha' : ins j a ∈ e.target := ha
      obtain ⟨x, hx⟩ := (e.symm (ins j a)).property
      have heqa : m (ins j a) = expUnit (d x) := by
        have h := he (e.symm (ins j a)) (e.map_target ha')
        rw [e.right_inv ha', ← hx] at h
        exact h
      let Y := d (Pi.single j (x j))
      have hY : Y ∈ M := (show x j ∈ Wj j from (hfull j hj).symm ▸ Submodule.mem_top)
      have hya : m (ins j a) = expUnit Y := by
        apply Units.ext
        funext k
        rw [ArchimedeanLieChart.expUnit_apply]
        by_cases hk : k = j
        · subst k
          have hYj : Y j = d x j := by simp only [Y, hentry, Pi.single_eq_same]
          rw [hYj]
          have hh := congrArg (fun u : Bˣ => u.val j) heqa
          simpa only [ArchimedeanLieChart.expUnit_apply] using hh
        · have h0 : tangentMatrix (i k) (0 : V k) = 0 := by
            simpa only [map_zero, Pi.zero_apply] using (hentry (0 : ∀ j, V j) k).symm
          simp only [Y, hentry, Pi.single_eq_of_ne hk, h0, ArchimedeanLieChart.expUnit_zero]
          simp [m, pointMatrices, ins, Pi.mulSingle_eq_of_ne hk]
      have hby : C (ins j b) Y ∈ M := hstable _ _ hY
      obtain ⟨z, hz, hez⟩ := (hline _).mp hby 1
      have hz' : m z = m (ins j (b * a * b⁻¹)) := by
        simpa only [one_smul, C, expUnit_matrixConjugation, ← hya, map_mul, map_inv] using hez
      show ins j (b * a * b⁻¹) ∈ H
      rw [← hm.injective hz']
      exact hz
    have hle : (↑(Subgroup.closure (G := A j) (cocharacterRadicalPoints (G j))) :
        Set (A j)) ⊆ Nj := by
      apply (Subgroup.closure_le Nj).mpr
      intro b hb
      obtain ⟨a, ha⟩ := hcontract j b hb
      exact openNormalContainsContracted Nj hNj a b ha
    exact Hj.normalCore_le (closure_minimal hle (OpenSubgroup.isClosed ⟨Nj, hNj⟩) (hgen j g))
  let Q : Set J := {j | Wj j = ⊥}
  by_cases hQ : Q.Nonempty
  · let F' (j : Q) := F j.val
    let G' (j : Q) := G j.val
    let i' (j : Q) := i j.val
    let s' (j : Q) := s j.val
    let X' := PointProduct F' G' i'
    let V' (j : Q) := Lie (F' j) (G' j).val
    letI : ∀ j : Q, LieRing (V' j) := fun j => (s' j).lieRing
    letI : ∀ j : Q, LieAlgebra (F' j) (V' j) := fun j => (s' j).lieAlgebra
    letI : ∀ j : Q, Module ℝ (V' j) := fun j => Module.restrictScalars ℝ (F' j) (V' j)
    let zfun (g : X') (j : J) : A j := if h : j ∈ Q then g ⟨j, h⟩ else 1
    let z : X' →* X :=
      { toFun := zfun
        map_one' := funext (fun j => by
          change zfun 1 j = (1 : A j)
          by_cases h : j ∈ Q <;> simp only [zfun, dite_eq_left, dite_eq_right, h] <;> rfl)
        map_mul' := fun a b => funext (fun j => by
          change zfun (a * b) j = zfun a j * zfun b j
          by_cases h : j ∈ Q
          · simp only [zfun, dite_eq_left h]
            rfl
          · simp only [zfun, dite_eq_right h, mul_one]) }
    have hz : Continuous z := by
      apply continuous_pi
      intro j
      by_cases h : j ∈ Q
      · simpa only [z, zfun, MonoidHom.coe_mk, OneHom.coe_mk, dif_pos h] using
          (continuous_apply (⟨j, h⟩ : Q) : Continuous (fun g : X' => g ⟨j, h⟩))
      · simpa only [z, zfun, MonoidHom.coe_mk, OneHom.coe_mk, dif_neg h] using
          (continuous_const : Continuous (fun _ : X' => (1 : A j)))
    let H' := H.comap z
    have hH' : IsClosed (H' : Set X') := hH.preimage hz
    obtain ⟨d', _, hentry', _, hchart', _, _, _, _⟩ :=
      ArchimedeanLieChart.productChart Q F' G' i' s'
    obtain ⟨M', _, hM', hline', _, _, _, _, hdM', _⟩ := hchart' H' hH'
    have hM'zero : M' = ⊥ := by
      apply bot_unique
      intro y hy
      obtain ⟨v, rfl⟩ := hM' hy
      let v₀ (j : J) : V j := if h : j ∈ Q then v ⟨j, h⟩ else 0
      have hv₀ : v₀ ∈ W := by
        apply (hline _).mpr
        intro t
        obtain ⟨g, hg, hge⟩ := (hline' _).mp hy t
        refine ⟨z g, hg, ?_⟩
        have hh := (ArchimedeanLieChart.productCoordinateCompatibility J F G i
          (fun j => j ∈ Q)).2 _ g hge
        have hx : (fun j => if h : j ∈ Q then (t • d' v) ⟨j, h⟩ else 0) = t • d v₀ := by
          funext j
          by_cases h : j ∈ Q
          · simp only [Pi.smul_apply, dif_pos h, hentry, v₀, hentry']
            rfl
          · have h0 : tangentMatrix (i j) (0 : V j) = 0 := by
              simpa only [map_zero, Pi.zero_apply] using (hentry (0 : ∀ j, V j) j).symm
            simp only [Pi.smul_apply, dif_neg h, hentry, v₀, h0, smul_zero]
        rw [← hx]
        exact hh
      have hv : v = 0 := by
        funext j
        change v j = (0 : V' j)
        simpa only [v₀, dif_pos j.property] using hzero j.val j.property v₀ hv₀
      have hdz : d' (0 : ∀ j : Q, V' j) = 0 := by
        funext j
        rw [hentry']
        simpa only [map_zero, Pi.zero_apply] using (hentry (0 : ∀ j, V j) j.val).symm
      rw [hv, hdz]
      exact (⊥ : Submodule ℝ _).zero_mem
    have hdisc : _root_.IsDiscrete (H' : Set X') :=
      isDiscrete_iff_discreteTopology.mpr (hdM' hM'zero)
    exfalso
    apply hnd Q hQ (hdisc.mono ?_)
    rintro _ ⟨g, hg, rfl⟩
    let g₀ (j : J) : A j := if j ∈ Q then 1 else g j
    have hg₀ : g₀ ∈ H := by
      apply mem_subgroup_of_single H
      intro j
      change ins j (g₀ j) ∈ H
      by_cases hj : j ∈ Q
      · rw [show g₀ j = 1 from if_pos hj, map_one]
        exact H.one_mem
      · exact hfactor j hj _
    have hh : z (fun j : Q => g j.val) = g₀⁻¹ * g := by
      funext j
      by_cases hj : j ∈ Q
      · simp [z, zfun, g₀, hj]
      · simp [z, zfun, g₀, hj]
    change z _ ∈ H
    rw [hh]
    exact H.mul_mem (H.inv_mem hg₀) hg
  · apply eq_top_iff.mpr
    intro g _
    apply mem_subgroup_of_single H
    exact fun j => hfactor j (fun h => hQ ⟨j, h⟩) (g j)

end Archimedean

section BaseChangeSimplicity

open scoped TensorProduct

private theorem adjointEndomorphisms {k L : Type*} [Field k] [IsAlgClosed k] [LieRing L]
    [LieAlgebra k L] [FiniteDimensional k L] (hL : LieAlgebra.IsSimple k L)
    (S : Subalgebra k (Module.End k L)) (hS : ∀ x : L, LieAlgebra.ad k L x ∈ S) :
    S = ⊤ := by
  classical
  letI : Module S L := Module.compHom L S.val.toRingHom
  letI : IsScalarTower k S L := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Nontrivial L := by
    rcases subsingleton_or_nontrivial L with h | h
    · exact (hL.non_abelian ⟨fun x y => Subsingleton.elim _ _⟩).elim
    · exact h
  letI : IsSimpleOrder (Submodule S L) := IsSimpleOrder.of_forall_eq_top (fun P hP => by
    let I : LieIdeal k L :=
      { P.restrictScalars k with
        lie_mem := fun {x y} hy => P.smul_mem ⟨LieAlgebra.ad k L x, hS x⟩ hy }
    rcases hL.eq_bot_or_eq_top I with hb | ht
    · exfalso
      apply hP
      apply bot_unique
      intro x hx
      exact (Submodule.mem_bot S).mpr ((LieSubmodule.mem_bot _ ).mp (hb ▸ (show x ∈ I from hx)))
    · apply eq_top_iff.mpr
      intro x _
      change x ∈ I
      exact ht.symm ▸ (LieSubmodule.mem_top x : x ∈ (⊤ : LieIdeal k L)))
  letI : IsSimpleModule S L := ⟨⟩
  have hscalar := (IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := S) (V := L) k).surjective
  apply eq_top_iff.mpr
  intro f _
  let f' : Module.End (Module.End S L) L :=
    { toFun := f
      map_add' := fun x y => map_add f x y
      map_smul' := by
        intro g x
        obtain ⟨r, rfl⟩ := hscalar g
        change f (r • x) = r • f x
        exact map_smul f r x }
  let b := Module.finBasis k L
  obtain ⟨s, hs⟩ := jacobson_density f' (Finset.univ.image b)
  have he : f = s.val := by
    apply b.ext
    intro j
    exact hs (b j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  exact he.symm ▸ s.property

private theorem simpleTensor {k E L : Type*} [Field k] [IsAlgClosed k] [Field E]
    [Algebra k E] [LieRing L] [LieAlgebra k L] [FiniteDimensional k L]
    (hL : LieAlgebra.IsSimple k L) : LieAlgebra.IsSimple E (E ⊗[k] L) := by
  classical
  refine ⟨fun I => ?_, fun h => hL.non_abelian ?_⟩
  · let e := Module.End.baseChangeHom k E L
    let S : Subalgebra k (Module.End k L) :=
      { carrier := {f | ∀ x ∈ I, e f x ∈ I}
        zero_mem' := by intro x _; simpa only [map_zero, LinearMap.zero_apply] using I.zero_mem
        add_mem' := by
          intro f g hf hg x hx
          rw [map_add, LinearMap.add_apply]
          exact I.add_mem (hf x hx) (hg x hx)
        one_mem' := by intro x hx; simpa only [map_one, Module.End.one_apply] using hx
        mul_mem' := by intro f g hf hg x hx; simpa only [map_mul, Module.End.mul_apply] using hf _ (hg x hx)
        algebraMap_mem' := by
          intro t x hx
          rw [e.commutes]
          rw [IsScalarTower.algebraMap_apply k E (Module.End E (E ⊗[k] L))]
          change (algebraMap k E t) • x ∈ I
          exact I.smul_mem (algebraMap k E t) hx }
    have hS (x : L) : LieAlgebra.ad k L x ∈ S := by
      have he : e (LieAlgebra.ad k L x) = LieAlgebra.ad E (E ⊗[k] L) (1 ⊗ₜ[k] x) := by
        apply TensorProduct.AlgebraTensorModule.ext
        intro t y
        change (LieAlgebra.ad k L x).baseChange E (t ⊗ₜ[k] y) = ⁅(1 : E) ⊗ₜ[k] x, t ⊗ₜ[k] y⁆
        rw [LinearMap.baseChange_tmul, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
        rfl
      intro y hy
      rw [he]
      exact I.lie_mem hy
    have htop := adjointEndomorphisms hL S hS
    by_cases hI : I = ⊥
    · exact Or.inl hI
    right
    obtain ⟨z, hz, hz0⟩ : ∃ z : E ⊗[k] L, z ∈ I ∧ z ≠ 0 := by
      by_contra! hh
      exact hI (bot_unique (fun x hx => (LieSubmodule.mem_bot _ ).mpr (hh x hx)))
    let b := Module.finBasis k L
    let bE := b.baseChange E
    obtain ⟨j, hj⟩ : ∃ j, bE.coord j z ≠ 0 := by
      by_contra! h
      apply hz0
      apply bE.repr.injective
      ext j
      exact (h j).trans (by simp)
    have hb (i : Fin (Module.finrank k L)) : bE i ∈ I := by
      let f := (b.coord j).smulRight (b i)
      have hf : f ∈ S := htop.symm ▸ (show f ∈ (⊤ : Subalgebra k (Module.End k L)) by trivial)
      have he : e f = (bE.coord j).smulRight (bE i) := by
        apply bE.ext
        intro l
        change f.baseChange E ((b.baseChange E) l) = _ 
        rw [Module.Basis.baseChange_apply, LinearMap.baseChange_tmul]
        by_cases h : j = l
        · subst l
          simp [f, bE]
        · simp [f, bE, Module.Basis.coord_apply, h]
      have hh : e f z ∈ I := hf z hz
      rw [he] at hh
      have hh' : (bE.coord j z) • bE i ∈ I := hh
      have hh'' := I.smul_mem (bE.coord j z)⁻¹ hh'
      rw [smul_smul, inv_mul_cancel₀ hj, one_smul] at hh''
      exact hh'' 
    have hs : Submodule.span E (Set.range bE) ≤ I.toSubmodule :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hb i)
    apply eq_top_iff.mpr
    rw [bE.span_eq] at hs
    exact hs 
  · constructor
    intro x y
    have he := h.trivial (1 ⊗ₜ[k] x) (1 ⊗ₜ[k] y)
    rw [LieAlgebra.ExtendScalars.bracket_tmul, mul_one, Module.FaithfullyFlat.one_tmul_eq_zero_iff] at he
    exact he

private theorem simple_of_lieEquiv {k L M : Type*} [Field k] [LieRing L] [LieRing M]
    [LieAlgebra k L] [LieAlgebra k M] (e : L ≃ₗ⁅k⁆ M)
    (h : LieAlgebra.IsSimple k L) : LieAlgebra.IsSimple k M := by
  refine ⟨fun I => ?_, fun ha => h.non_abelian ⟨fun x y => e.injective ?_⟩⟩
  · let J := I.comap e.toLieHom
    rcases h.eq_bot_or_eq_top J with hbot | htop
    · left
      apply bot_unique
      intro y hy
      obtain ⟨x, rfl⟩ := e.surjective y
      have hx : x ∈ J := hy
      rw [hbot] at hx
      rw [(LieSubmodule.mem_bot _).mp hx, map_zero]
      exact (⊥ : LieIdeal k M).zero_mem
    · right
      apply eq_top_iff.mpr
      intro y _
      obtain ⟨x, rfl⟩ := e.surjective y
      exact (htop.symm ▸ LieSubmodule.mem_top x : x ∈ J)
  · change e ⁅x, y⁆ = e 0
    rw [e.map_lie, map_zero, ha.trivial]

private theorem tensorBracket {R S L M : Type*} [Field R] [Field S] [Algebra R S]
    [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra S M]
    (f : S ⊗[R] L →ₗ[S] M)
    (h : ∀ (a b : S) (x y : L), f ⁅a ⊗ₜ[R] x, b ⊗ₜ[R] y⁆ =
      ⁅f (a ⊗ₜ[R] x), f (b ⊗ₜ[R] y)⁆) :
    ∀ x y, f ⁅x, y⁆ = ⁅f x, f y⁆ := by
  intro x y
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y => exact h a b x y
    | add y z hy hz => simp only [lie_add, map_add, hy, hz]
  | add x z hx hz => simp only [add_lie, map_add, hx, hz]

private def cancelLieBaseChange (k A E L : Type*) [Field k] [Field A] [Field E]
    [Algebra k A] [Algebra k E] [Algebra A E] [IsScalarTower k A E]
    [LieRing L] [LieAlgebra k L] : (E ⊗[A] (A ⊗[k] L)) ≃ₗ⁅E⁆ (E ⊗[k] L) where
  __ := TensorProduct.AlgebraTensorModule.cancelBaseChange k A E E L
  map_lie' := by
    let f := TensorProduct.AlgebraTensorModule.cancelBaseChange k A E E L
    change ∀ {x y}, f ⁅x, y⁆ = ⁅f x, f y⁆
    intro x y
    apply tensorBracket f.toLinearMap _ x y
    intro a b x y
    induction x using TensorProduct.inductionOn with
    | tmul u x =>
      induction y using TensorProduct.inductionOn with
      | tmul v y =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul]
        change ((u * v) • (a * b)) ⊗ₜ[k] ⁅x, y⁆ = ⁅(u • a) ⊗ₜ[k] x, (v • b) ⊗ₜ[k] y⁆
        rw [LieAlgebra.ExtendScalars.bracket_tmul]
        congr 1
        simp only [Algebra.smul_def, map_mul]
        ring
      | add y z hy hz => simp only [TensorProduct.tmul_add, lie_add, map_add, hy, hz]
    | add x z hx hz => simp only [TensorProduct.tmul_add, add_lie, map_add, hx, hz]

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private simple_of_geometric_normal_subgroups simple_of_baseChange from
  LinearAlgebraicGroups.Arithmetic.AbsoluteSimpleLocalLie
open private groupLieRadical_eq_bot from
  LinearAlgebraicGroups.Representation.SemisimplyDifferentiated
open private tangent_coordinates from LinearAlgebraicGroups.Affine.AdjointRepresentation

universe u

private theorem simpleAfterFieldExtension {k F L : Type u} [Field k] [Field F]
    [Algebra k F] [LieRing L] [LieAlgebra k L]
    [FiniteDimensional (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] L)]
    (h : LieAlgebra.IsSimple (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] L)) :
    LieAlgebra.IsSimple F (F ⊗[k] L) := by
  let K := AlgebraicClosure k
  let E := AlgebraicClosure F
  let f : K →ₐ[k] E := IsAlgClosed.lift
  letI : Algebra K E := f.toRingHom.toAlgebra
  letI : IsScalarTower k K E :=
    IsScalarTower.of_algebraMap_eq (R := k) (S := K) (A := E) fun x => (f.commutes x).symm
  have he : LieAlgebra.IsSimple E (E ⊗[k] L) :=
    simple_of_lieEquiv (cancelLieBaseChange k K E L) (simpleTensor h)
  exact simple_of_baseChange (cancelLieBaseChange k F E L) he

private theorem geometricLieSimple {k : Type u} [Field k] [CharZero k]
    (G : AffineAlgebraicGroup k) (hG : IsAbsolutelyAlmostSimple G)
    (t : IdentityLieStructure (GeometricGroup G).val) :
    letI := t.lieRing
    letI := t.lieAlgebra
    LieAlgebra.IsSimple (AlgebraicClosure k) (Lie (AlgebraicClosure k) (GeometricGroup G).val) := by
  letI := t.lieRing
  letI := t.lieAlgebra
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  letI := hG.1.2.1
  letI : GeometricallyConnected H.val.X.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.val.X.hom (fieldSpecMap k K)))
  have hR := LinearAlgebraicGroups.GeometricRadicals.geometricSolvableRadicalLargest G
  have hr := groupLieRadical_eq_bot H _ hR hG.1.2.2 t
  exact simple_of_geometric_normal_subgroups H t hG.2.1 hG.2.2 hr

set_option maxHeartbeats 650000 in
private theorem localLieSimpleOfBaseChange {k F : Type u} [Field k] [Field F]
    [CharZero k] [Algebra k F] (G : AffineAlgebraicGroup k) (hG : IsAbsolutelyAlmostSimple G)
    (sF : IdentityLieStructure (baseChangedAlgebraicGroup F G).val) :
    letI := sF.lieRing
    letI := sF.lieAlgebra
    LieAlgebra.IsSimple F (Lie F (baseChangedAlgebraicGroup F G).val) := by
  let s := identityLieStructure G
  let K := AlgebraicClosure k
  let H := GeometricGroup G
  let t := identityLieStructure H
  let L := Lie k G.val
  let V := Lie F (baseChangedAlgebraicGroup F G).val
  let U := Lie K H.val
  letI : LieRing L := s.lieRing
  letI : LieAlgebra k L := s.lieAlgebra
  letI : LieRing U := t.lieRing
  letI : LieAlgebra K U := t.lieAlgebra
  letI : LieRing V := sF.lieRing
  letI : LieAlgebra F V := sF.lieAlgebra
  obtain ⟨eK, _⟩ := (identityLieBracketBaseChange k K G).2 s t
  obtain ⟨eF, _⟩ := (identityLieBracketBaseChange k F G).2 s sF
  let eK' : (K ⊗[k] L) ≃ₗ⁅K⁆ U := eK
  let eF' : (F ⊗[k] L) ≃ₗ⁅F⁆ V := eF
  have hk : LieAlgebra.IsSimple K (K ⊗[k] L) :=
    simple_of_lieEquiv eK'.symm (geometricLieSimple G hG t)
  obtain ⟨_, b, _⟩ := tangent_coordinates G s
  letI : FiniteDimensional K (K ⊗[k] L) := Module.Finite.of_basis (b.baseChange K)
  exact simple_of_lieEquiv eF' (simpleAfterFieldExtension hk)

end BaseChangeSimplicity

section ArithmeticProjections

open CategoryTheory AlgebraicGeometry
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.IntegralModels (MatrixRealization)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open Specs.PadicLogarithmChart (completionNormedField rationalPrime)
open AdelicGroups ArithmeticLatticeProjection
open scoped NumberField

open private cosetMap continuous_cosetMap surjective_cosetMap quotientMeasure_pushforward
  from LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection

private theorem compactQuotientOfProjection {P X : Type*} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
    (L : Subgroup P) (H : Subgroup X) (q : P →* X) (hq : Function.Surjective q)
    (hqc : Continuous q) (hL : L ≤ H.comap q) [CompactSpace (P ⧸ L)] :
    CompactSpace (X ⧸ H) :=
  ⟨(Function.Surjective.range_eq (surjective_cosetMap q hL hq)) ▸
    isCompact_range (continuous_cosetMap q hL hqc)⟩

private theorem dependentProductProjectionSurjective {I J : Type*}
    {A : I → Type*} [∀ i, One (A i)] {f : J → I} (hf : Function.Injective f) :
    Function.Surjective (fun x : ∀ i, A i => fun j => x (f j)) := by
  classical
  intro x
  refine ⟨fun i => if h : ∃ j, f j = i then h.choose_spec ▸ x h.choose else 1, ?_⟩
  funext j
  let h : ∃ l, f l = f j := ⟨j, rfl⟩
  change (if h : ∃ l, f l = f j then h.choose_spec ▸ x h.choose else 1) = x j
  rw [dite_eq_left h]
  have he := hf h.choose_spec
  have transport (a b : J) (e : a = b) : (congrArg f e ▸ x a : A (f b)) = x b := by
    cases e
    rfl
  exact transport _ _ he

private theorem localPointSet_eq_image {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, u} K) (i : MatrixRealization G) (v : D.Place)
    (j : MatrixRealization (baseChangedAlgebraicGroup (D.Completion v) G))
    (e : PointsIn j (D.Completion v) ≃ₜ* LocalPoints D i v)
    (he : ∀ p, (show Points G.val.X (CommAlgCat.of K (D.Completion v)) from e p).left =
      (baseChangePoint K (D.Completion v) G.val.X (CommAlgCat.of (D.Completion v) (D.Completion v))
        p).left)
    (A : Set (PointsIn j (D.Completion v))) :
    localPointSet D i v A = e '' A := by
  ext g
  constructor
  · rintro ⟨p, hp, hpg⟩
    exact ⟨p, hp, Over.OverMorphism.ext ((he p).trans hpg.symm)⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, hp, he p⟩

private theorem evaluatePlaceSurjective {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, u} K) (i : MatrixRealization G) {T : Finset D.Place} {v : D.Place}
    (hv : v ∈ T) : Function.Surjective (evaluatePlace D i hv) := by
  classical
  intro g
  refine ⟨Pi.mulSingle (⟨v, hv⟩ : ↥T) g, Pi.mulSingle_eq_same _ _⟩

private theorem evaluatePlaceContinuous {K : Type u} [Field K] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, u} K) (i : MatrixRealization G) {T : Finset D.Place} {v : D.Place}
    (hv : v ∈ T) : Continuous (evaluatePlace D i hv) :=
  @continuous_apply (↥T) (fun w => LocalPoints D i w.val) _ ⟨v, hv⟩

set_option maxHeartbeats 1300000 in
private theorem placeProjectionData {K X : Type u} [Field K] [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] {G : AffineAlgebraicGroup K}
    (D : GlobalFieldData.{u, u} K) (i : MatrixRealization G) (S T : Finset D.Place)
    (U : Subgroup (Adeles D i T)) (hS : S ⊆ T) (v : D.Place) (hvS : v ∉ S) (hvT : v ∈ T)
    (hA : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hSc : ¬ CompactSpace (FinitePoints D i S))
    (hUc : IsCompact (U : Set (Adeles D i T))) (hUo : IsOpen (U : Set (Adeles D i T)))
    (e : X ≃ₜ* LocalPoints D i v) :
    let H := ((lattice D i T U).map (evaluatePlace D i hvT)).topologicalClosure
    let H₀ := H.comap e.toMonoidHom
    CompactSpace (LocalPoints D i v ⧸ H) ∧ CompactSpace (X ⧸ H₀) ∧
      IsClosed (H₀ : Set X) ∧ ¬ DiscreteTopology H₀ ∧ FiniteInvariantQuotientMeasure H₀ := by
  classical
  let L := lattice D i T U
  let f := evaluatePlace D i hvT
  let H := (L.map f).topologicalClosure
  let H₀ := H.comap e.toMonoidHom
  let q := e.symm.toMonoidHom.comp f
  have hf : Continuous f := evaluatePlaceContinuous D i hvT
  have hfs := evaluatePlaceSurjective D i hvT
  have hqs : Function.Surjective q := e.symm.surjective.comp hfs
  have hqc : Continuous q := e.symm.continuous.comp hf
  have hL : L ≤ H.comap f := fun x hx => subset_closure ⟨x, hx, rfl⟩
  have hL₀ : L ≤ H₀.comap q := by
    intro x hx
    change e (e.symm (f x)) ∈ H
    rw [e.apply_symm_apply]
    exact hL hx
  have hH := (L.map f).isClosed_topologicalClosure
  have hH₀ : IsClosed (H₀ : Set X) := hH.preimage e.continuous
  obtain ⟨_, _, _, hcompact, _, _, hμ⟩ := latticeConstruction D i T U hA ⟨v, hvT⟩ hUc hUo
  letI := hcompact

  have hc := compactQuotientOfProjection L H f hfs hf hL
  have hc₀ := compactQuotientOfProjection L H₀ q hqs hqc hL₀
  have hμ₀ := quotientMeasure_pushforward L H₀ q hL₀ hqc hqs hμ
  let J : Finset D.Place := {v}
  have hvJ : v ∈ J := Finset.mem_singleton_self v
  have hJT : J ⊆ T := Finset.singleton_subset_iff.mpr hvT
  have hJS : Disjoint J S := Finset.disjoint_singleton_left.mpr hvS
  have hnd := (projectionProperties D i S T J U hS hJT hA hSc ⟨v, hvJ⟩ hJS hUc hUo).1
  let qJ := e.symm.toMonoidHom.comp (evaluatePlace D i hvJ)
  have hqJ : Continuous qJ := e.symm.continuous.comp (evaluatePlaceContinuous D i hvJ)
  have hqJi : Function.Injective qJ := by
    intro x y hxy
    have he := e.symm.injective hxy
    funext j
    have hj : j = (⟨v, hvJ⟩ : ↥J) := Subtype.ext (Finset.mem_singleton.mp j.property)
    rw [hj]
    exact he
  have hnd₀ : ¬ DiscreteTopology H₀ := by
    intro hd
    have hdis : _root_.IsDiscrete (H₀ : Set X) := isDiscrete_iff_discreteTopology.mpr hd
    apply hnd ((hdis.preimage hqJ.continuousOn hqJi).mono ?_)
    rintro x ⟨y, hy, rfl⟩
    change q y ∈ H₀
    exact hL₀ hy
  exact ⟨hc, hc₀, hH₀, hnd₀, hμ₀⟩

set_option maxHeartbeats 800000 in
theorem padicLatticeProjection : PadicLatticeProjection.{u} := by
  classical
  intro K _ _ G i D hD
  subst D
  let D : GlobalFieldData.{u, u} K := .number inferInstance
  intro w S T U hS hwS hwT hA hSc hUc hUo hG hrank
  let v : D.Place := .inl w
  let F := w.adicCompletion K
  obtain ⟨p, hp, hwp⟩ := PadicLogarithmChart.numberPlacePrime K w
  letI : Fact p.Prime := ⟨hp⟩
  letI : w.asIdeal.LiesOver (rationalPrime p).asIdeal := hwp
  letI : NormedField F := completionNormedField p w
  letI : Algebra K F := completionAlgebra D v
  obtain ⟨a, ha⟩ := PadicLogarithmChart.numberCompletionPadic p K w
  letI : NormedAlgebra ℚ_[p] F := a
  letI : FiniteDimensional ℚ_[p] F := ha
  letI : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective
  let G₀ := baseChangedAlgebraicGroup F G
  obtain ⟨_, j₀, _, e₀, he₀, _⟩ := ArchimedeanLieChart.baseChangeMatrixComparison K F G i
  let j : MatrixRealization G₀ := j₀
  let X := PointsIn j F
  let Y := PointsIn i F
  let e : X ≃ₜ* Y := e₀
  letI : IsTopologicalGroup X := by
    exact IsInducing.isTopologicalGroup (asMatrix j F) (.induced _)
  letI : IsTopologicalGroup Y := by
    exact IsInducing.isTopologicalGroup (asMatrix i F) (.induced _)
  let L := lattice D i T U
  let f : FinitePoints D i T →* Y := evaluatePlace D i hwT
  let H := (L.map f).topologicalClosure
  let H₀ := H.comap e.toMonoidHom
  obtain ⟨hc, hc₀, hH₀, hnd₀, hμ₀⟩ :=
    placeProjectionData D i S T U hS v hwS hwT hA hSc hUc hUo e
  letI : CompactSpace (Y ⧸ H) := hc
  letI : CompactSpace (X ⧸ H₀) := hc₀
  have hH := (L.map f).isClosed_topologicalClosure
  have hss : Specs.GeometricRadicals.IsSemisimple G₀ :=
    (LinearAlgebraicGroups.Reductive.RadicalBaseChange.semisimpleFieldExtension (K := F) G
      hG.1.1 hG.1.2.1).mpr hG.1
  have hsim : HasSimpleLie G₀ :=
    localLieSimpleOfBaseChange G hG (identityLieStructure G₀)
  have hopen₀ := padicOpenOfFiniteCovolume p G₀ j hss hsim hrank H₀ hH₀ hnd₀ hμ₀
  have hopen : IsOpen (H : Set Y) := by
    have heq : e.symm ⁻¹' (H₀ : Set X) = (H : Set Y) := by
      ext x
      change e (e.symm x) ∈ H ↔ x ∈ H
      rw [e.apply_symm_apply]
    rw [← heq]
    exact hopen₀.preimage e.symm.continuous
  have hscalar : Continuous (algebraMap ℚ_[p] F) :=
    (Algebra.linearMap ℚ_[p] F).continuous_of_finiteDimensional
  obtain ⟨_, hrad⟩ := LocalCocharacterEvaluation.openCocompactContainsRadicals G₀ j hscalar H₀ hopen₀
  let A : Subgroup Y := Subgroup.closure (localPointSet D i v (parabolicRadicalPoints G₀))
  have hAH : A ≤ H := by
    apply (Subgroup.closure_le H).mpr
    rw [localPointSet_eq_image D i v j e he₀]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨P, hP, R, hR, hxR⟩ := hx
    exact hrad P hP R hR hxR
  have hfull (hd : Dense (A : Set Y)) : H = ⊤ :=
    eq_top_iff.mpr (fun x _ => closure_minimal hAH hH (hd x))
  exact ⟨H, rfl, hopen, (containsDivisibleSubgroups H hopen).1, hAH, hfull⟩

set_option maxHeartbeats 900000 in
private theorem archimedeanSubproductsNondiscrete {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, u} K) (i : MatrixRealization G)
    (S T : Finset D.Place) (A : Finset D.InfinitePlace) (U : Subgroup (Adeles D i T))
    (hS : S ⊆ T) (hAS : ∀ w : ↑A, Sum.inr w.val ∉ S)
    (hAT : ∀ w : ↑A, Sum.inr w.val ∈ T)
    (hA : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hSc : ¬ CompactSpace (FinitePoints D i S))
    (hUc : IsCompact (U : Set (Adeles D i T))) (hUo : IsOpen (U : Set (Adeles D i T)))
    {B : ↥A → Type u} [∀ j, Group (B j)] [∀ j, TopologicalSpace (B j)]
    (e : ∀ j, B j ≃ₜ* LocalPoints D i (.inr j.val))
    (q : FinitePoints D i T →* (∀ j, B j))
    (hcoord : ∀ g j, q g j = (e j).symm (g ⟨.inr j.val, hAT j⟩))
    (H : Subgroup (∀ j, B j)) (hL : lattice D i T U ≤ H.comap q)
    (Q : Set (↥A)) (hQ : Q.Nonempty) :
    ¬ _root_.IsDiscrete ((fun g : ∀ j, B j => fun j : Q => g j.val) '' (H : Set _)) := by
  classical
  let place (j : ↥A) : D.Place := Sum.inr j.val
  intro hd
  let R : Finset D.Place := Finset.univ.image (fun j : Q => place j.val)
  have hmem (j : Q) : place j.val ∈ R := Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hRT : R ⊆ T := by
    intro r hr
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
    exact hAT j.val
  have hRne : R.Nonempty := by
    obtain ⟨j, hj⟩ := hQ
    exact ⟨place j, hmem ⟨j, hj⟩⟩
  have hRS : Disjoint R S := by
    rw [Finset.disjoint_left]
    intro r hr hsr
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
    exact hAS j.val hsr
  have hnon := (projectionProperties D i S T R U hS hRT hA hSc hRne hRS hUc hUo).1
  let qR (x : FinitePoints D i R) (j : Q) : B j.val :=
    (e j.val).symm (x ⟨place j.val, hmem j⟩)
  have hqR : Continuous qR := by
    change Continuous (fun x : FinitePoints D i R =>
      fun j : Q => (e j.val).symm (evaluatePlace D i (hmem j) x))
    exact continuous_pi fun j =>
      (e j.val).symm.continuous.comp (evaluatePlaceContinuous D i (hmem j))
  have hqRi : Function.Injective qR := by
    intro x y hx
    funext r
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp r.property
    have hr : (⟨place j.val, hmem j⟩ : ↥R) = r := Subtype.ext hj
    rw [← hr]
    exact (e j.val).symm.injective (congrFun hx j)
  apply hnon ((hd.preimage hqR.continuousOn hqRi).mono ?_)
  rintro x ⟨y, hy, rfl⟩
  refine ⟨q y, hL hy, funext fun j => ?_⟩
  exact hcoord y j.val

set_option maxHeartbeats 950000 in
private theorem archimedeanProjectionWithCharts {K : Type u} [Field K]
    {G : AffineAlgebraicGroup K} (D : GlobalFieldData.{u, u} K) (i : MatrixRealization G)
    (S T : Finset D.Place) (A : Finset D.InfinitePlace) (U : Subgroup (Adeles D i T))
    (hS : S ⊆ T) (hAne : A.Nonempty) (hAS : ∀ w : ↑A, Sum.inr w.val ∉ S)
    (hAT : ∀ w : ↑A, Sum.inr w.val ∈ T)
    (hA : CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i))
    (hSc : ¬ CompactSpace (FinitePoints D i S))
    (hUc : IsCompact (U : Set (Adeles D i T))) (hUo : IsOpen (U : Set (Adeles D i T)))
    (F : ↥A → Type u) [∀ j, NormedField (F j)] [∀ j, NormedAlgebra ℝ (F j)]
    [∀ j, CompleteSpace (F j)] [∀ j, FiniteDimensional ℝ (F j)] [∀ j, CharZero (F j)]
    (G₀ : ∀ j, AffineAlgebraicGroup (F j)) (i₀ : ∀ j, MatrixRealization (G₀ j))
    (e : ∀ j, PointsIn (i₀ j) (F j) ≃ₜ* LocalPoints D i (.inr j.val))
    (hsimple : ∀ j, HasSimpleLie (G₀ j))
    (hgen₀ : ∀ j, Dense
      (↑(Subgroup.closure (G := PointsIn (i₀ j) (F j)) (cocharacterRadicalPoints (G₀ j))) :
        Set (PointsIn (i₀ j) (F j)))) :
    Dense (↑((lattice D i T U).map (evaluateArchimedean D i A hAT)) :
      Set (∀ w : ↑A, LocalPoints D i (.inr w.val))) := by
  classical
  let J := ↥A
  let place (j : J) : D.Place := .inr j.val
  let X := ∀ j, PointsIn (i₀ j) (F j)
  let L := lattice D i T U
  let f := evaluateArchimedean D i A hAT
  let q : FinitePoints D i T →* X := MonoidHom.pi
    (fun j => (e j).symm.toMonoidHom.comp (evaluatePlace D i (hAT j)))
  have hqc : Continuous q := by
    change Continuous (fun g : FinitePoints D i T =>
      fun j : J => (e j).symm (evaluatePlace D i (hAT j) g))
    exact continuous_pi fun j =>
      (e j).symm.continuous.comp (evaluatePlaceContinuous D i (hAT j))
  have hqs : Function.Surjective q := by
    intro x
    let ins (j : J) : ↥T := ⟨place j, hAT j⟩
    have hins : Function.Injective ins := by
      intro a b hab
      exact Subtype.ext (Sum.inr.inj (congrArg Subtype.val hab))
    obtain ⟨g, hg⟩ := dependentProductProjectionSurjective
      (A := fun w : ↥T => LocalPoints D i w.val) hins (fun j => e j (x j))
    refine ⟨g, funext fun j => ?_⟩
    change (e j).symm (g (ins j)) = x j
    have hj : g (ins j) = e j (x j) := congrFun hg j
    rw [hj, ContinuousMulEquiv.symm_apply_apply]
  have hT : T.Nonempty := by
    obtain ⟨j, hj⟩ := hAne
    exact ⟨place ⟨j, hj⟩, hAT ⟨j, hj⟩⟩
  obtain ⟨_, _, _, _, _, _, hμ⟩ := latticeConstruction D i T U hA hT hUc hUo
  let H := (L.map q).topologicalClosure
  have hL : L ≤ H.comap q := fun x hx => subset_closure ⟨x, hx, rfl⟩
  have hμH := quotientMeasure_pushforward L H q hL hqc hqs hμ
  have hnd := archimedeanSubproductsNondiscrete D i S T A U hS hAS hAT hA hSc hUc hUo
    e q (fun _ _ => rfl) H hL
  have hfull : H = ⊤ := archimedeanProductFull F G₀ i₀ hsimple hgen₀ H
    (L.map q).isClosed_topologicalClosure hnd hμH
  let eprod (x : X) (j : J) := e j (x j)
  have hep : Continuous eprod :=
    continuous_pi fun j => (e j).continuous.comp
      (@continuous_apply J (fun j => PointsIn (i₀ j) (F j)) _ j)
  have hs : Function.Surjective eprod := by
    intro x
    exact ⟨fun j => (e j).symm (x j), funext fun j => (e j).apply_symm_apply (x j)⟩
  have heq (g : FinitePoints D i T) : eprod (q g) = f g := by
    funext j
    exact (e j).apply_symm_apply (f g j)
  have hd : Dense ((L.map q : Subgroup X) : Set X) :=
    dense_iff_closure_eq.mpr (congrArg (fun M : Subgroup X => (M : Set X)) hfull)
  have hout := hs.denseRange.dense_image hep hd
  have himage : eprod '' ((L.map q : Subgroup X) : Set X) = ((L.map f : Subgroup _) : Set _) := by
    ext x
    constructor
    · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
      exact ⟨g, hg, (heq g).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨q g, ⟨g, hg, rfl⟩, heq g⟩
  rwa [himage] at hout

set_option maxHeartbeats 1000000 in
theorem archimedeanLatticeProjection : ArchimedeanLatticeProjection.{u} := by
  classical
  intro K _ _ G i D hD
  subst D
  let D : GlobalFieldData.{u, u} K := .number inferInstance
  intro S T A U hS hAne hAS hAT hA hSc hUc hUo hG hgen
  let J := ↥A
  let place (j : J) : D.Place := .inr j.val
  let F (j : J) := j.val.Completion
  letI : ∀ j, NormedField (F j) := fun j =>
    inferInstanceAs (NormedField j.val.Completion)
  letI : ∀ j, Algebra K (F j) := fun j => completionAlgebra D (place j)
  letI : ∀ j, CompleteSpace (F j) := fun j =>
    inferInstanceAs (CompleteSpace j.val.Completion)
  have hnorm (j : J) := ArchimedeanLieChart.completionRealStructures K j.val
  choose scalars hfd _ _ using hnorm
  letI : ∀ j, NormedAlgebra ℝ (F j) := scalars
  letI : ∀ j, FiniteDimensional ℝ (F j) := hfd
  letI : ∀ j, CharZero (F j) := fun j =>
    charZero_of_injective_algebraMap (algebraMap ℝ (F j)).injective
  let G₀ (j : J) := baseChangedAlgebraicGroup (F j) G
  have hbase (j : J) : ∃ (i₀ : MatrixRealization (G₀ j))
      (e : PointsIn i₀ (F j) ≃ₜ* PointsIn i (F j)),
      ∀ p, (show Points G.val.X (CommAlgCat.of K (F j)) from e p).left =
        (baseChangePoint K (F j) G.val.X (CommAlgCat.of (F j) (F j)) p).left := by
    obtain ⟨_, ij, _, ej, hej, _⟩ :=
      ArchimedeanLieChart.baseChangeMatrixComparison K (F j) G i
    exact ⟨ij, ej, hej⟩
  choose i₀ e he using hbase
  have hgen₀ (j : J) :
      Dense (↑(Subgroup.closure (G := PointsIn (i₀ j) (F j)) (cocharacterRadicalPoints (G₀ j))) :
        Set (PointsIn (i₀ j) (F j))) := by
    have hd := hgen j
    change Dense (↑(Subgroup.closure (G := PointsIn i (F j)) (localPointSet D i (place j)
      (cocharacterRadicalPoints (G₀ j)))) : Set (PointsIn i (F j))) at hd
    rw [localPointSet_eq_image D i (place j) (i₀ j) (e j) (he j)] at hd
    have hi : IsDenseInducing (e j) :=
      ⟨(e j).toHomeomorph.isInducing, (e j).surjective.denseRange⟩
    apply hi.dense_image.mp
    let C : Set (PointsIn (i₀ j) (F j)) := cocharacterRadicalPoints (G₀ j)
    have hmap := MonoidHom.map_closure (e j).toMonoidHom C
    have heq := congrArg (fun H : Subgroup (PointsIn i (F j)) => (H : Set (PointsIn i (F j)))) hmap
    rw [Subgroup.coe_map] at heq
    change Dense ((e j).toMonoidHom '' (↑(Subgroup.closure C) : Set (PointsIn (i₀ j) (F j))))
    rw [heq]
    exact hd
  have hsimple (j : J) : HasSimpleLie (G₀ j) :=
    localLieSimpleOfBaseChange G hG (identityLieStructure (G₀ j))
  exact archimedeanProjectionWithCharts D i S T A U hS hAne hAS hAT hA hSc hUc hUo
    F G₀ i₀ e hsimple hgen₀

end ArithmeticProjections

end LinearAlgebraicGroups.Arithmetic.ProjectiveRecurrence
