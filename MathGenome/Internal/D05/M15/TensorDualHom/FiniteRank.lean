import MathGenome.Internal.Specs.D05.M15.TensorDualHom.FiniteRank
import MathGenome.Internal.D05.M15.TensorDualHom.CompositionTrace
import MathGenome.Internal.D05.M02.BasisExtension.Choice

/-! The canonical tensor–Hom map identifies tensors with finite-rank maps in
arbitrary dimension, and composition has no unit in infinite dimension. -/

namespace D05.M15.TensorDualHom.FiniteRank

open scoped TensorProduct
open D05.M15.TensorDualHom (phi)

abbrev finiteRankMaps := Specs.D05.M15.TensorDualHom.FiniteRank.finiteRankMaps
abbrev compositionProduct := Specs.D05.M15.TensorDualHom.FiniteRank.compositionProduct

/-- Finitely supported coordinate families of functionals are determined by all
their evaluations. No uniform finite support for an arbitrary operator is asserted. -/
theorem phi_finsupp_injective {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] :
    Function.Injective (dualTensorHom K V (I →₀ K)) := by
  classical
  rw [dualTensorHom_finsupp, LinearMap.coe_comp]
  apply (LinearMap.finsuppLinearMap_injective K V K I K).comp
  exact (Finsupp.mapRange_injective _ (map_zero _) (by
    rw [dualTensorHom_self_right]
    exact (TensorProduct.rid K (Module.Dual K V)).injective)).comp
      (TensorProduct.finsuppRight K K (Module.Dual K V) K I).injective

/-- Naturality in the vector factor, with the canonical upstream map. -/
theorem phi_postcompose {K V W Z : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup Z] [Module K Z]
    (L : W →ₗ[K] Z) (t : Module.Dual K V ⊗[K] W) :
    phi K V Z (L.lTensor (Module.Dual K V) t) = L.comp (phi K V W t) :=
  LinearMap.congr_fun (dualTensorHom_comp_lTensor L) t

theorem phi_injective : Specs.D05.M15.TensorDualHom.FiniteRank.phi_injective := by
  intro K V W _ _ _ _ _
  classical
  -- This is the declared unrestricted basis-extension principle, applied to ∅.
  obtain ⟨S, _, b, _⟩ := D05.M02.BasisExtension.Choice.basis_extension
    (K := K) (V := W) ∅ (by simp)
  intro s t h
  apply (b.repr.lTensor (Module.Dual K V)).injective
  apply phi_finsupp_injective
  change phi K V (S →₀ K) (b.repr.toLinearMap.lTensor _ s) =
    phi K V (S →₀ K) (b.repr.toLinearMap.lTensor _ t)
  rw [phi_postcompose, phi_postcompose, h]

theorem mem_range_iff : Specs.D05.M15.TensorDualHom.FiniteRank.mem_range_iff := by
  intro K V W _ _ _ _ _ T
  constructor
  · rintro ⟨t, rfl⟩
    exact D05.M15.TensorDualHom.finite_rank t
  · intro hT
    letI := hT
    -- Factor T through its finite-dimensional image; the right-factor theorem
    -- has no finite-dimensional assumption on V.
    obtain ⟨t, ht⟩ := (dualTensorHom_bijective_of_finite_projective_right
      (R := K) (M := V) (N := T.range)).2 T.rangeRestrict
    refine ⟨T.range.subtype.lTensor (Module.Dual K V) t, ?_⟩
    rw [phi_postcompose, ht]
    rfl

theorem finite_rank_equivalence :
    Specs.D05.M15.TensorDualHom.FiniteRank.finite_rank_equivalence := by
  intro K V W _ _ _ _ _
  let L : (Module.Dual K V ⊗[K] W) →ₗ[K] finiteRankMaps K V W :=
    (phi K V W).codRestrict _ (fun t => D05.M15.TensorDualHom.finite_rank t)
  have hL : Function.Bijective L := by
    constructor
    · intro s t h
      exact phi_injective (congrArg Subtype.val h)
    · intro T
      obtain ⟨t, ht⟩ := (mem_range_iff T.val).mpr T.property
      exact ⟨t, Subtype.ext ht⟩
  exact ⟨LinearEquiv.ofBijective L hL, fun _ => rfl⟩

theorem product_tmul : Specs.D05.M15.TensorDualHom.FiniteRank.product_tmul := by
  intro K V _ _ _ f g v w
  change (phi K V V (f ⊗ₜ[K] v)).lTensor _ (g ⊗ₜ[K] w) = _
  rw [LinearMap.lTensor_tmul, D05.M15.TensorDualHom.phi_tmul,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul']

theorem phi_product : Specs.D05.M15.TensorDualHom.FiniteRank.phi_product := by
  intro K V _ _ _ s t
  exact phi_postcompose (phi K V V s) t

theorem product_assoc : Specs.D05.M15.TensorDualHom.FiniteRank.product_assoc := by
  intro K V _ _ _ r s t
  apply phi_injective
  rw [phi_product, phi_product, phi_product, phi_product]
  rfl

theorem product_agrees_finite :
    Specs.D05.M15.TensorDualHom.FiniteRank.product_agrees_finite := by
  intro K V _ _ _ _
  apply LinearMap.ext
  intro s
  apply LinearMap.ext
  intro t
  apply phi_injective
  rw [phi_product, D05.M15.TensorDualHom.CompositionTrace.phi_product]

theorem unit_iff_identity : Specs.D05.M15.TensorDualHom.FiniteRank.unit_iff_identity := by
  intro K V _ _ _ e
  constructor
  · intro he
    classical
    rcases subsingleton_or_nontrivial V with hV | hV
    · ext x
      exact Subsingleton.elim _ _
    · obtain ⟨S, _, b, _⟩ := D05.M02.BasisExtension.Choice.basis_extension
        (K := K) (V := V) ∅ (by simp)
      obtain ⟨i⟩ := b.index_nonempty
      ext v
      have h := congrArg (fun t => phi K V V t (b i))
        (he (b.coord i ⊗ₜ[K] v)).1
      rw [phi_product] at h
      simpa [LinearMap.comp_apply, dualTensorHom_apply] using h
  · intro he t
    constructor <;> apply phi_injective
    · rw [phi_product, he, LinearMap.id_comp]
    · rw [phi_product, he, LinearMap.comp_id]

theorem identity_infinite_rank :
    Specs.D05.M15.TensorDualHom.FiniteRank.identity_infinite_rank := by
  intro K V _ _ _ hV h
  exact D05.M15.TensorDualHom.identity_not_in_range hV
    ((mem_range_iff LinearMap.id).mpr h)

theorem no_unit : Specs.D05.M15.TensorDualHom.FiniteRank.no_unit := by
  intro K V _ _ _ hV
  rintro ⟨e, he⟩
  exact D05.M15.TensorDualHom.identity_not_in_range hV
    ⟨e, (unit_iff_identity e).mp he⟩

end D05.M15.TensorDualHom.FiniteRank
