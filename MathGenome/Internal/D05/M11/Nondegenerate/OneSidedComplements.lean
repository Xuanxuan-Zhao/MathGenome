import MathGenome.Internal.Specs.D05.M11.Nondegenerate.OneSidedComplements
import MathGenome.Internal.D05.M06.Projection
import Mathlib.LinearAlgebra.Projection

noncomputable section
namespace D05.M11.Nondegenerate.OneSidedComplements
open Module Matrix
open scoped BigOperators

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (σ τ : K ≃+* K) (B : V →ₛₗ[σ.toRingHom] V →ₛₗ[τ.toRingHom] K)

/-- Undo the scalar automorphism in the second slot to obtain a linear map.
Its domain is the entire ambient space, which need not be finite dimensional. -/
def rightCoordinateMap (W : Submodule K V) {n : ℕ} (e : Basis (Fin n) K W) :
    V →ₗ[K] (Fin n → K) where
  toFun v i := τ.symm (B (e i) v)
  map_add' x y := by ext i; simp only [map_add, Pi.add_apply]
  map_smul' a x := by
    ext i
    change τ.symm (B (e i) (a • x)) = a * τ.symm (B (e i) x)
    rw [(B (e i)).map_smulₛₗ]
    change τ.symm (τ a * B (e i) x) = _
    rw [map_mul, τ.symm_apply_apply]

lemma matching_of_basis (W : Submodule K V) {n : ℕ} (e : Basis (Fin n) K W)
    {v z : V} (h : ∀ i, B (e i) v = B (e i) z) : ∀ w : W, B w v = B w z := by
  have heq : (B.flip v).domRestrict W = (B.flip z).domRestrict W := e.ext h
  exact fun w => LinearMap.congr_fun heq w

lemma rightCoordinateMap_injective (W : Submodule K V) {n : ℕ}
    (e : Basis (Fin n) K W) (h : (B.domRestrict₁₂ W W).SeparatingRight) :
    Function.Injective ((rightCoordinateMap σ τ B W e).comp W.subtype) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro w hw
  apply h w
  have hb : ∀ i, B (e i) w = B (e i) (0 : V) := by
    intro i
    apply τ.symm.injective
    have := congrFun hw i
    simpa only [rightCoordinateMap, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.comp_apply, Submodule.subtype_apply, Pi.zero_apply, map_zero] using this
  intro x
  exact matching_of_basis σ τ B W e hb x |>.trans (by rw [map_zero])

lemma rightCoordinateMap_surjective (W : Submodule K V) {n : ℕ}
    (e : Basis (Fin n) K W) (h : (B.domRestrict₁₂ W W).SeparatingRight) :
    Function.Surjective ((rightCoordinateMap σ τ B W e).comp W.subtype) := by
  have := Module.Finite.of_basis e
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp
    (rightCoordinateMap_injective σ τ B W e h)
  simp [Module.finrank_eq_card_basis e]

lemma exists_matching (W : Submodule K V) [FiniteDimensional K W]
    (h : (B.domRestrict₁₂ W W).SeparatingRight) (v : V) :
    ∃ w : W, ∀ x : W, B x w = B x v := by
  let e := Module.finBasis K W
  obtain ⟨w, hw⟩ := rightCoordinateMap_surjective σ τ B W e h
    (rightCoordinateMap σ τ B W e v)
  refine ⟨w, matching_of_basis σ τ B W e ?_⟩
  intro i
  exact τ.symm.injective (congrFun hw i)

/-- Right separation on a finite-dimensional restriction implies left separation.
Surjectivity supplies a vector with any prescribed basis-pairing values. -/
lemma left_of_right (W : Submodule K V) [FiniteDimensional K W]
    (h : (B.domRestrict₁₂ W W).SeparatingRight) :
    (B.domRestrict₁₂ W W).SeparatingLeft := by
  let e := Module.finBasis K W
  intro x hx
  apply e.repr.injective
  ext i
  obtain ⟨y, hy⟩ := rightCoordinateMap_surjective σ τ B W e h
    (fun j => τ.symm (if j = i then 1 else 0))
  have hb : ∀ j, B (e j) y = if j = i then 1 else 0 := by
    intro j
    exact τ.symm.injective (congrFun hy j)
  have hsum : B x y = ∑ j, σ (e.repr x j) * B (e j) y := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    rw [B.map_sum₂]
    apply Finset.sum_congr rfl
    intro j _
    rw [B.map_smulₛₗ₂]
    rfl
  have hc : σ (e.repr x i) = 0 := by
    simpa only [hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] using hsum.symm.trans (hx y)
  simpa using σ.injective (hc.trans (map_zero σ).symm)

theorem right_intersection_iff :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.right_intersection_iff := by
  intro K V _ _ _
  intro σ τ B W _
  constructor
  · intro hd
    have hr : (B.domRestrict₁₂ W W).SeparatingRight := by
      intro w hw
      apply Subtype.ext
      have hm : (w : V) ∈ W ⊓ W.orthogonalBilin B :=
        ⟨w.property, fun x hx => hw ⟨x, hx⟩⟩
      rw [hd] at hm
      simpa only [Submodule.mem_bot, Submodule.coe_zero] using hm
    exact ⟨left_of_right σ τ B W hr, hr⟩
  · intro h
    apply le_antisymm _ bot_le
    intro v hv
    have hz : (⟨v, hv.1⟩ : W) = 0 := h.2 ⟨v, hv.1⟩ (fun w => hv.2 w w.property)
    simpa only [Submodule.mem_bot, Submodule.coe_zero] using (congrArg Subtype.val hz)

theorem left_intersection_iff :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.left_intersection_iff := by
  intro K V _ _ _
  intro σ τ B W _
  exact (right_intersection_iff τ σ B.flip W).trans and_comm

theorem right_complement :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.right_complement := by
  intro K V _ _ _
  intro σ τ B W _ h
  apply IsCompl.of_eq ((right_intersection_iff σ τ B W).mpr h)
  apply top_unique
  intro v _
  obtain ⟨w, hw⟩ := exists_matching σ τ B W h.2 v
  have hp : v - w ∈ W.orthogonalBilin B := by
    intro x hx
    change B x (v - w) = 0
    rw [map_sub, hw ⟨x, hx⟩, sub_self]
  exact Submodule.mem_sup.mpr ⟨w, w.property, v - w, hp, by simp⟩

theorem left_complement :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.left_complement := by
  intro K V _ _ _
  intro σ τ B W _ h
  exact right_complement τ σ B.flip W ⟨h.2, h.1⟩

theorem complement_membership :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.complement_membership := by
  intro K V _ _ _
  intro σ τ B W v
  exact ⟨Iff.rfl, Iff.rfl⟩

theorem right_direct_sum :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.right_direct_sum := by
  intro K V _ _ _
  intro σ τ B W _ h
  have hc := right_complement σ τ B W h
  exact (D05.M06.DirectSum.pair_internal_iff_sup_inf W _).mpr ⟨hc.sup_eq_top, hc.inf_eq_bot⟩

theorem left_direct_sum :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.left_direct_sum := by
  intro K V _ _ _
  intro σ τ B W _ h
  exact right_direct_sum τ σ B.flip W ⟨h.2, h.1⟩

theorem right_projection :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.right_projection := by
  intro K V _ _ _
  intro σ τ B W _ h
  have hc := right_complement σ τ B W h
  have hd := (D05.M06.DirectSum.pair_internal_iff_sup_inf W (W.orthogonalBilin B)).mpr
    ⟨hc.sup_eq_top, hc.inf_eq_bot⟩
  obtain ⟨E, ⟨hp, hr, hk⟩, hu⟩ := D05.M06.Projection.projection_exists_unique W _ hd
  have hfix : ∀ w ∈ W, E w = w := fun w hw =>
    (D05.M06.Projection.range_iff_fixed E hp w).mp (hr.symm ▸ hw)
  have hres : ∀ v, v - E v ∈ W.orthogonalBilin B := by
    intro v
    rw [← hk]
    exact (D05.M06.Projection.decomposition_formula E hp v).2.1
  refine ⟨E, ⟨hp, hr, hk, hfix, hres, ?_⟩, ?_⟩
  · intro w hw v
    have heq := hres v w hw
    change B w (v - E v) = 0 at heq
    rw [map_sub, sub_eq_zero] at heq
    exact heq.symm
  · intro F hf
    exact hu F ⟨hf.1, hf.2.1, hf.2.2.1⟩

theorem left_projection :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.left_projection := by
  intro K V _ _ _
  intro σ τ B W _ h
  exact right_projection τ σ B.flip W ⟨h.2, h.1⟩

lemma second_expansion (W : Submodule K V) {n : ℕ} (e : Basis (Fin n) K W)
    (i : Fin n) (y : W) :
    B (e i) y = ((Matrix.of (fun i j => B (e i) (e j))) *ᵥ
      (fun j => τ (e.repr y j))) i := by
  conv_lhs => rw [← e.sum_repr y]
  simp only [Submodule.coe_sum, Submodule.coe_smul]
  rw [map_sum]
  change (∑ j, B (e i) (e.repr y j • (e j : V))) =
    ∑ j, B (e i) (e j) * τ (e.repr y j)
  apply Finset.sum_congr rfl
  intro j _
  rw [(B (e i)).map_smulₛₗ]
  exact mul_comm _ _

theorem matrix_criterion :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.matrix_criterion := by
  intro K V _ _ _
  intro σ τ B W n e
  have := Module.Finite.of_basis e
  let H : Matrix (Fin n) (Fin n) K := Matrix.of (fun i j => B (e i) (e j))
  constructor
  · intro h
    apply Matrix.mulVec_surjective_iff_isUnit.mp
    intro d
    obtain ⟨w, hw⟩ := rightCoordinateMap_surjective σ τ B W e h.2 (fun i => τ.symm (d i))
    refine ⟨fun j => τ (e.repr w j), ?_⟩
    ext i
    rw [← second_expansion σ τ B W e i w]
    exact τ.symm.injective (congrFun hw i)
  · intro h
    have hr : (B.domRestrict₁₂ W W).SeparatingRight := by
      intro w hw
      have heq : H *ᵥ (fun j => τ (e.repr w j)) = H *ᵥ 0 := by
        ext i
        rw [Matrix.mulVec_zero, Pi.zero_apply, ← second_expansion σ τ B W e i w]
        exact hw (e i)
      have hz := Matrix.mulVec_injective_iff_isUnit.mpr h heq
      apply e.repr.injective
      ext j
      have hj := congrFun hz j
      exact τ.injective (by simpa only [Pi.zero_apply, Finsupp.zero_apply, map_zero] using hj)
    exact ⟨left_of_right σ τ B W hr, hr⟩

theorem projection_coordinates :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.projection_coordinates := by
  intro K V _ _ _
  intro σ τ B W n e h E hp hr hk v hv j
  let H : Matrix (Fin n) (Fin n) K := Matrix.of (fun i k => B (e i) (e k))
  have hH : IsUnit H := (matrix_criterion σ τ B W e).mp h
  have hres : v - E v ∈ W.orthogonalBilin B := by
    rw [← hk]
    exact (D05.M06.Projection.decomposition_formula E hp v).2.1
  have heq : H *ᵥ (fun k => τ (e.repr ⟨E v, hv⟩ k)) = fun i => B (e i) v := by
    ext i
    rw [← second_expansion σ τ B W e i ⟨E v, hv⟩]
    have hm := hres (e i) (e i).property
    change B (e i) (v - E v) = 0 at hm
    rw [map_sub, sub_eq_zero] at hm
    exact hm.symm
  have hinv := congrArg (fun d => H⁻¹ *ᵥ d) heq
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul H
    ((Matrix.isUnit_iff_isUnit_det H).mp hH), Matrix.one_mulVec] at hinv
  have hj := congrFun hinv j
  exact (τ.symm_apply_apply (e.repr ⟨E v, hv⟩ j)).symm.trans (congrArg τ.symm hj)

theorem zero_subspace :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.zero_subspace := by
  intro K V _ _ _
  intro σ τ B
  refine ⟨Submodule.orthogonalBilin_bot, Submodule.orthogonalBilin_bot, ?_⟩
  intro E hE
  exact LinearMap.range_eq_bot.mp hE

theorem bilinear_specialization :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.bilinear_specialization := by
  intro K V _ _ _
  intro B W _ h
  exact ⟨right_complement (RingEquiv.refl K) (RingEquiv.refl K) B W h,
    left_complement (RingEquiv.refl K) (RingEquiv.refl K) B W h⟩

theorem sesquilinear_specialization :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.sesquilinear_specialization := by
  intro K V _ _ _ B W _ h
  constructor
  · exact right_complement (RingEquiv.refl K) (starRingAut : K ≃+* K) B W h
  · exact left_complement (RingEquiv.refl K) (starRingAut : K ≃+* K) B W h

private lemma exampleForm_apply (K : Type*) [Field K] (x y : Fin 2 → K) :
    Specs.D05.M11.Radicals.exampleForm K x y = x 0 * y 1 := by
  simp [Specs.D05.M11.Radicals.exampleForm, Specs.D05.M11.Radicals.exampleMatrix,
    Matrix.toBilin'_apply, Fin.sum_univ_two]

theorem complements_can_differ :
    Specs.D05.M11.Nondegenerate.OneSidedComplements.complements_can_differ := by
  intro K _
  let B := Specs.D05.M11.Radicals.exampleForm K
  let w : Fin 2 → K := fun _ => 1
  let W : Submodule K (Fin 2 → K) := K ∙ w
  change (B.restrict W).Nondegenerate ∧ W.orthogonalBilin B ≠ W.orthogonalBilin B.flip
  have hw : w ∈ W := Submodule.mem_span_singleton_self w
  constructor
  · apply (right_intersection_iff (RingEquiv.refl K) (RingEquiv.refl K) B W).mp
    apply le_antisymm _ bot_le
    rintro x ⟨hx, hy⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have hz := hy w hw
    change Specs.D05.M11.Radicals.exampleForm K w (a • w) = 0 at hz
    rw [exampleForm_apply] at hz
    have ha : a = 0 := by simpa [w] using hz
    simp [ha]
  · intro heq
    have hm : Pi.single (0 : Fin 2) (1 : K) ∈ W.orthogonalBilin B := by
      intro x _
      rw [exampleForm_apply]
      simp
    rw [heq] at hm
    have hz := hm w hw
    change B (Pi.single 0 1) w = 0 at hz
    rw [exampleForm_apply] at hz
    simp [w] at hz

end D05.M11.Nondegenerate.OneSidedComplements
