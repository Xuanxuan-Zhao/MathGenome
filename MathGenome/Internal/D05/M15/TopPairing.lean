import MathGenome.Internal.Specs.D05.M15.TopPairing
import MathGenome.Internal.D05.M15.DeterminantLine
import MathGenome.Internal.D05.M15.ExteriorBasis
import MathGenome.Internal.D05.M15.ExteriorPairing

noncomputable section
namespace D05.M15.TopPairing

open Specs.D05.M15.TopPairing
open Specs.D05.M15.DeterminantLine (volume)

abbrev topProduct : topProduct_type := topProduct_value
abbrev volumeCoordinate : volumeCoordinate_type := @volumeCoordinate_value
abbrev scalarPairing : scalarPairing_type := scalarPairing_value

theorem product_coe : Specs.D05.M15.TopPairing.product_coe := by
  intro K V _ _ _ p q n h x y
  subst n
  rfl

theorem volume_normalization : Specs.D05.M15.TopPairing.volume_normalization := by
  intro K V _ _ _ n b
  exact (exteriorPower.alternatingMapLinearEquiv_apply_ιMulti b.det b).trans b.det_self

theorem volume_reconstruction : Specs.D05.M15.TopPairing.volume_reconstruction := by
  intro K V _ _ _ n b z
  obtain ⟨B, hB⟩ := D05.M15.DeterminantLine.top_wedge_basis b
  have hz : B.repr z 0 • volume b = z := by
    simpa only [Fin.sum_univ_one, hB] using B.sum_repr z
  have hL := congrArg (volumeCoordinate b) hz
  simp only [map_smul, volume_normalization b, smul_eq_mul, mul_one] at hL
  rw [← hL]
  exact hz.symm

theorem volume_trivialization : Specs.D05.M15.TopPairing.volume_trivialization := by
  intro K V _ _ _ n b
  refine ⟨{ volumeCoordinate b with
    invFun := fun a => a • volume b
    left_inv := fun z => (volume_reconstruction b z).symm
    right_inv := ?_ }, rfl⟩
  intro a
  change volumeCoordinate b (a • volume b) = a
  simp only [map_smul, volume_normalization b, smul_eq_mul, mul_one]

/-- The paper's ordered top wedge is the all-indices exterior basis vector. -/
theorem basis_univ_eq_volume {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (b : Module.Basis (Fin n) K V) :
    b.ExteriorAlgebra Finset.univ = (volume b : _root_.ExteriorAlgebra K V) := by
  have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
  rw [_root_.ExteriorAlgebra.basis_apply_ofCard b hc]
  have he : (Finset.univ : Finset (Fin n)).orderEmbOfFin hc =
      (OrderIso.refl (Fin n)).toOrderEmbedding :=
    (Finset.orderEmbOfFin_unique' hc (fun _ => Finset.mem_univ _)).symm
  simp only [_root_.ExteriorAlgebra.ιMulti_family,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, Set.powersetCard.ofCard, he,
    Function.comp_def, OrderIso.coe_toOrderEmbedding, OrderIso.refl_apply]
  rfl

theorem basis_product : Specs.D05.M15.TopPairing.basis_product := by
  intro K V _ _ _ n b p q h I J
  classical
  have hc : p + q = Fintype.card (Fin n) := by simpa using h
  have hd : Disjoint I.val J.val ↔ I.val = J.valᶜ := by
    rw [Set.powersetCard.disjoint_iff_eq_compl hc]
    exact Subtype.ext_iff
  simp only [D05.M15.ExteriorBasis.increasingWedge_eq_family,
    ← exteriorPower.basis_apply]
  apply Subtype.ext
  rw [product_coe]
  change (b.exteriorPower p I : _root_.ExteriorAlgebra K V) *
    (b.exteriorPower q J : _root_.ExteriorAlgebra K V) = _
  rw [← _root_.ExteriorAlgebra.basis_eq_coe_basis,
    ← _root_.ExteriorAlgebra.basis_eq_coe_basis]
  by_cases hij : Disjoint I.val J.val
  · rw [ite_eq_left (hd.mp hij)]
    rw [_root_.ExteriorAlgebra.basis_mul_of_disjoint b I J hij]
    have hu : (Set.powersetCard.disjUnion hij).val = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [Set.powersetCard.coe_disjUnion, Finset.disjUnion_eq_union,
        Finset.card_union_of_disjoint hij]
      exact (congrArg₂ (· + ·) I.prop J.prop).trans hc
    rw [Set.powersetCard.sign_eq_permOfDisjoint_sign hc I J hij,
      hu, basis_univ_eq_volume b]
    rfl
  · rw [ite_eq_right (fun h' => hij (hd.mpr h'))]
    exact _root_.ExteriorAlgebra.basis_mul_of_not_disjoint b I J hij

theorem scalar_basis : Specs.D05.M15.TopPairing.scalar_basis := by
  intro K V _ _ _ n b p q h I J
  classical
  change volumeCoordinate b (topProduct K V p q n h
    (Specs.D05.M15.ExteriorBasis.increasingWedge b p I)
    (Specs.D05.M15.ExteriorBasis.increasingWedge b q J)) = _
  rw [basis_product b p q h I J]
  split_ifs
  · simp only [Units.smul_def, map_zsmul, volume_normalization b]
  · exact map_zero _

theorem sign_unit : Specs.D05.M15.TopPairing.sign_unit := by
  intro K _ n p I
  rcases Int.units_eq_one_or (Set.powersetCard.sign I) with h | h
  · left; simp [h]
  · right; simp [h]

theorem sign_nonzero : Specs.D05.M15.TopPairing.sign_nonzero := by
  intro K _ n p I
  rcases sign_unit (K := K) n p I with h | h
  · rw [h]; exact one_ne_zero
  · rw [h]; exact neg_ne_zero.mpr one_ne_zero

theorem coefficient_reconstruction : Specs.D05.M15.TopPairing.coefficient_reconstruction := by
  intro K V _ _ _ n b p q h x y
  exact volume_reconstruction b _

theorem determinant_line_dimension : Specs.D05.M15.TopPairing.determinant_line_dimension := by
  intro K V _ _ _ _
  simpa only [Nat.choose_self] using
    D05.M15.ExteriorBasis.dimension (K := K) (V := V) (Module.finrank K V)

/-- Moving a degree equality between the product and its scalar coordinate. -/
theorem scalarPairing_eq_compr₂ {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] {p q n : ℕ}
    (h : p + q = n) (L : (⋀[K]^n V) →ₗ[K] K) :
    scalarPairing K V p q n h L =
      (exteriorPower.wedge K V p q).compr₂ (h ▸ L) := by
  subst n
  rfl

/-- Trivializing the target of the actual product gives Mathlib's wedge pairing. -/
theorem scalarPairing_eq_wedgePairing {K V : Type*}
    [Field K] [AddCommGroup V] [Module K V] {p q n : ℕ}
    (h : p + q = n) (hn : n = Module.finrank K V)
    (e : (⋀[K]^n V) ≃ₗ[K] K) :
    scalarPairing K V p q n h e.toLinearMap =
      exteriorPower.wedgePairing (hn ▸ e) (h.trans hn) := by
  cases hn
  exact scalarPairing_eq_compr₂ h e.toLinearMap

theorem perfect : Specs.D05.M15.TopPairing.perfect := by
  intro K V _ _ _ n b p q h
  let : FiniteDimensional K V := Module.Finite.of_basis b
  have hn : n = Module.finrank K V := by
    simpa using (Module.finrank_eq_card_basis b).symm
  obtain ⟨e, he⟩ := volume_trivialization b
  rw [← he]
  change (scalarPairing K V p q n h e.toLinearMap).IsPerfPair
  rw [scalarPairing_eq_wedgePairing h hn e]
  infer_instance

theorem dual_identification : Specs.D05.M15.TopPairing.dual_identification := by
  intro K V _ _ _ n b p hp
  let B := scalarPairing K V p (n-p) n (Nat.add_sub_of_le hp) (volumeCoordinate b)
  let : B.IsPerfPair := perfect b p (n-p) (Nat.add_sub_of_le hp)
  exact ⟨B.flip.toPerfPair, fun _ _ => rfl⟩

theorem arbitrary_volume : Specs.D05.M15.TopPairing.arbitrary_volume := by
  intro K V _ _ _ _ ω hω
  obtain ⟨e, he⟩ := volume_trivialization (Module.finBasis K V)
  have hc : e ω ≠ 0 := by
    intro hzero
    exact hω (e.injective (hzero.trans e.map_zero.symm))
  let L := e.trans (LinearEquiv.smulOfNeZero K K ((e ω)⁻¹) (inv_ne_zero hc))
  refine ⟨L, ?_, ?_⟩
  · change (e ω)⁻¹ • e ω = 1
    exact inv_mul_cancel₀ hc
  · intro p hp
    change (scalarPairing K V p _ _ _ L.toLinearMap).IsPerfPair
    rw [scalarPairing_eq_wedgePairing (Nat.add_sub_of_le hp) rfl L]
    infer_instance

theorem rescaled_volume : Specs.D05.M15.TopPairing.rescaled_volume := by
  intro K V _ _ _ p q n h L ω c hc hL
  constructor
  · simp [LinearMap.smul_apply, map_smul, hL, hc]
  · intro x y
    change c⁻¹ * L (topProduct K V p q n h x y) =
      L (topProduct K V p q n h x y) / c
    rw [div_eq_mul_inv, mul_comm]

theorem boundary_degrees : Specs.D05.M15.TopPairing.boundary_degrees := by
  intro K V _ _ _ n L a z
  have hl : topProduct K V 0 n n (Nat.zero_add n)
      ((exteriorPower.zeroEquiv K V).symm a) z = a • z := by
    apply Subtype.ext
    rw [product_coe]
    simp [exteriorPower.zeroEquiv_symm_apply,
      exteriorPower.ιMulti_apply_coe, _root_.ExteriorAlgebra.ιMulti_zero_apply]
  have hr : topProduct K V n 0 n (Nat.add_zero n) z
      ((exteriorPower.zeroEquiv K V).symm a) = a • z := by
    apply Subtype.ext
    rw [product_coe]
    simp [exteriorPower.zeroEquiv_symm_apply,
      exteriorPower.ιMulti_apply_coe, _root_.ExteriorAlgebra.ιMulti_zero_apply]
  change L (topProduct K V 0 n n _ _ z) = _ ∧
    L (topProduct K V n 0 n _ z _) = _
  rw [hl, hr, map_smul, smul_eq_mul]
  exact ⟨rfl, mul_comm _ _⟩

end D05.M15.TopPairing
