import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.IG.SpecializationDecomposition
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.IG.SpecializationCoefficients

open scoped Polynomial

namespace GaloisFormalization.IG.SpecializationDecomposition

open SpecializationData SpecializationCoefficients
open Specs.GaloisFormalization.IG.SpecializationDecomposition

noncomputable section

abbrev constantInValuationRing :=
  @Specs.GaloisFormalization.IG.SpecializationDecomposition.constantInValuationRing

abbrev residueAlgebra := @Specs.GaloisFormalization.IG.SpecializationDecomposition.residueAlgebra

abbrev onValuationRing := @Specs.GaloisFormalization.IG.SpecializationDecomposition.onValuationRing

theorem normalizedValueGroup : NormalizedValueGroup := by
  intro k _ ℓ _ _ a L _ _ i
  let w := inducedOrder i.toRingHom
  let t := algebraMap (RatFunc k) L (RatFunc.X - RatFunc.C a)
  change w t = 1 ∧ _
  have ht : w t = 1 := by
    let := substitutionAlgebra ℓ a
    change (i t).orderTop = 1
    rw [show i t = substitution ℓ a (RatFunc.X - RatFunc.C a) from i.commutes _,
      substitution_sub_C]
    exact HahnSeries.orderTop_single one_ne_zero
  refine ⟨ht, Set.Subset.antisymm ?_ ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact WithTop.ne_top_iff_exists.mp (w.ne_top_iff.mpr x.ne_zero)
  · have htne : t ≠ 0 := w.ne_top_iff.mp (by rw [ht]; exact WithTop.coe_ne_top)
    let u : Lˣ := Units.mk0 t htne
    have hpow (n : ℕ) : w (t ^ n) = ((n : ℤ) : WithTop ℤ) := by
      rw [w.map_pow, ht]
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_one]
    rintro _ ⟨n, rfl⟩
    refine ⟨u ^ n, ?_⟩
    change w ((u ^ n : Lˣ) : L) = (n : WithTop ℤ)
    rw [Units.val_zpow_eq_zpow_val]
    change w (t ^ n) = _
    cases n with
    | ofNat n => simpa only [Int.ofNat_eq_natCast, zpow_natCast] using hpow n
    | negSucc n =>
        rw [zpow_negSucc, w.map_inv, hpow]
        rfl

theorem residueFieldEquivalence : ResidueFieldEquivalence := by
  intro k _ ℓ _ _ a L _ _ f hf _ _ _ _ i hm
  let := residueAlgebra i
  let r : residueField i.toRingHom →ₐ[k] ℓ :=
    { toRingHom := residueEmbedding i.toRingHom
      commutes' := fun c => by
        let := substitutionAlgebra ℓ a
        change residueEmbedding i.toRingHom
          (IsLocalRing.residue _ (constantInValuationRing i c)) = _
        rw [residueEmbedding_residue]
        change (i (algebraMap (RatFunc k) L (RatFunc.C c))).coeff 0 = _
        rw [show i (algebraMap (RatFunc k) L (RatFunc.C c)) =
          substitution ℓ a (RatFunc.C c) from i.commutes _, substitution_C,
          HahnSeries.C_apply, HahnSeries.coeff_single_same] }
  have hr : Function.Surjective r := by
    apply (AlgHom.range_eq_top r).mp
    apply top_unique
    rw [← Polynomial.IsSplittingField.adjoin_rootSet ℓ (specialize a f hf),
      Algebra.adjoin_le_iff]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hm.2.surjOn hy
    obtain ⟨F, hF⟩ := hm.1 x hx
    let x' : valuationRing i.toRingHom :=
      ⟨x, (nonnegative_iff_powerSeries _).2 ⟨F, hF⟩⟩
    exact ⟨IsLocalRing.residue _ x', (residueEmbedding_residue _ _).trans hxy⟩
  exact ⟨AlgEquiv.ofBijective r ⟨r.injective, hr⟩, rfl⟩

section ReductionAction

variable {k : Type*} [Field k] {ℓ : Type*} [Field ℓ] [Algebra k ℓ]
  {a : k} {L : Type*} [Field L] [Algebra (RatFunc k) L]

private theorem order_preserved (i : PointEmbedding (ℓ := ℓ) a L)
    (σ : decompositionGroup i) (x : L) :
    inducedOrder i.toRingHom ((σ : L ≃ₐ[RatFunc k] L) x) =
      inducedOrder i.toRingHom x := by
  by_cases hx : x = 0
  · rw [hx, map_zero]
  · exact σ.property x hx

private theorem positiveIdeal_le_comap (i : PointEmbedding (ℓ := ℓ) a L)
    (σ : decompositionGroup i) :
    positiveIdeal i.toRingHom ≤ (positiveIdeal i.toRingHom).comap (onValuationRing i σ) := by
  intro x hx
  change onValuationRing i σ x ∈ positiveIdeal i.toRingHom
  rw [mem_positiveIdeal] at hx ⊢
  change 0 < inducedOrder i.toRingHom ((σ : L ≃ₐ[RatFunc k] L) (x : L))
  rw [order_preserved]
  exact hx

private def residueEnd (i : PointEmbedding (ℓ := ℓ) a L) (σ : decompositionGroup i) :
    letI := residueAlgebra i
    residueField i.toRingHom →ₐ[k] residueField i.toRingHom :=
  letI := residueAlgebra i
  let A := valuationRing i.toRingHom
  let m := positiveIdeal i.toRingHom
  let q : residueField i.toRingHom →+* residueField i.toRingHom :=
    Ideal.quotientMap m (onValuationRing i σ) (positiveIdeal_le_comap i σ)
  { toRingHom := q
    commutes' := fun c => by
      change q (IsLocalRing.residue A (constantInValuationRing i c)) =
        IsLocalRing.residue A (constantInValuationRing i c)
      have hq (x : A) : q (IsLocalRing.residue A x) =
          IsLocalRing.residue A (onValuationRing i σ x) :=
        Ideal.quotientMap_mk (H := positiveIdeal_le_comap i σ)
      rw [hq]
      congr 1
      exact Subtype.ext ((σ : L ≃ₐ[RatFunc k] L).commutes (RatFunc.C c)) }

private theorem residueEnd_residue (i : PointEmbedding (ℓ := ℓ) a L)
    (σ : decompositionGroup i) (x : valuationRing i.toRingHom) :
    letI := residueAlgebra i
    residueEnd i σ (IsLocalRing.residue _ x) =
      IsLocalRing.residue _ (onValuationRing i σ x) :=
  Ideal.quotientMap_mk (H := positiveIdeal_le_comap i σ)

private def laurentAlgHom (a : k) (τ : ℓ ≃ₐ[k] ℓ) :
    letI := substitutionAlgebra ℓ a
    LaurentSeries ℓ →ₐ[RatFunc k] LaurentSeries ℓ :=
  letI := substitutionAlgebra ℓ a
  { toRingHom := laurentMap τ.toRingHom
    commutes' := fun x => by
      change laurentMap τ.toRingHom (substitution ℓ a x) = substitution ℓ a x
      let alg := τ.toRingHom.toAlgebra
      have ht : @IsScalarTower k ℓ ℓ _ alg.toSMul _ :=
        @IsScalarTower.of_algebraMap_eq k ℓ ℓ _ _ _ _ alg _ fun c => (τ.commutes c).symm
      exact DFunLike.congr_fun (@substitution_naturality k _ ℓ _ _ ℓ _ _ alg ht a) x }

private theorem orderTop_laurentMap (τ : ℓ ≃ₐ[k] ℓ) (s : LaurentSeries ℓ) :
    (laurentMap τ.toRingHom s).orderTop = s.orderTop := by
  apply le_antisymm
  · apply HahnSeries.le_orderTop_iff_forall.mpr
    intro n hn
    have h := HahnSeries.coeff_eq_zero_of_lt_orderTop hn
    rw [laurentMap_coeff] at h
    exact τ.injective (h.trans (map_zero τ).symm)
  · apply HahnSeries.le_orderTop_iff_forall.mpr
    intro n hn
    rw [laurentMap_coeff, HahnSeries.coeff_eq_zero_of_lt_orderTop hn, map_zero]

private theorem liftFibreAutomorphism (f : (RatFunc k)[X])
    [Polynomial.IsSplittingField (RatFunc k) L f] (i : PointEmbedding (ℓ := ℓ) a L)
    (τ : ℓ ≃ₐ[k] ℓ) :
    ∃ σ : decompositionGroup i, ∀ x : L,
      i ((σ : L ≃ₐ[RatFunc k] L) x) = laurentMap τ.toRingHom (i x) := by
  let := substitutionAlgebra ℓ a
  let j := (laurentAlgHom a τ).comp i
  have hrange : j.range = i.range :=
    (Polynomial.IsSplittingField.adjoin_rootSet_eq_range L f j).symm.trans
      (Polynomial.IsSplittingField.adjoin_rootSet_eq_range L f i)
  let σ := ((AlgEquiv.ofInjectiveField j).trans
    (Subalgebra.equivOfEq j.range i.range hrange)).trans (AlgEquiv.ofInjectiveField i).symm
  have hσ (x : L) : i (σ x) = laurentMap τ.toRingHom (i x) := by
    change ((AlgEquiv.ofInjectiveField i) (σ x) : LaurentSeries ℓ) = _
    dsimp only [σ, AlgEquiv.trans_apply]
    rw [AlgEquiv.apply_symm_apply]
    rfl
  refine ⟨⟨σ, ?_⟩, hσ⟩
  intro x _
  change (i (σ x)).orderTop = (i x).orderTop
  rw [hσ]
  exact orderTop_laurentMap τ (i x)

end ReductionAction

theorem decompositionEquivalence : DecompositionEquivalence := by
  intro k _ ℓ _ _ a L _ _ f hf hm hs _ _ i hmatch
  let := substitutionAlgebra ℓ a
  let := residueAlgebra i
  let : FiniteDimensional k ℓ :=
    Polynomial.IsSplittingField.finiteDimensional ℓ (specialize a f hf)
  obtain ⟨e, he⟩ := residueFieldEquivalence f hf hm hs i hmatch
  let A := valuationRing i.toRingHom
  let red := reduction i.toRingHom
  have heval (x : A) : e (IsLocalRing.residue A x) = red x := by
    change e.toRingHom (IsLocalRing.residue A x) = red x
    rw [he]
    rfl
  have hsurj : Function.Surjective red := by
    intro y
    obtain ⟨q, rfl⟩ := e.surjective y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective (R := A) q
    exact ⟨x, (heval x).symm⟩
  let act (σ : decompositionGroup i) : ℓ →ₐ[k] ℓ :=
    e.toAlgHom.comp ((residueEnd i σ).comp e.symm.toAlgHom)
  let ρ (σ : decompositionGroup i) : ℓ ≃ₐ[k] ℓ :=
    AlgEquiv.ofBijective (act σ) (act σ).bijective
  have hρ (σ : decompositionGroup i) (x : A) :
      ρ σ (red x) = red (onValuationRing i σ x) := by
    change e (residueEnd i σ (e.symm (red x))) = _
    rw [← heval x, e.symm_apply_apply, residueEnd_residue, heval]
  let φ : decompositionGroup i →* (ℓ ≃ₐ[k] ℓ) :=
    { toFun := ρ
      map_one' := by
        apply AlgEquiv.ext
        intro y
        obtain ⟨x, rfl⟩ := hsurj y
        change ρ 1 (red x) = red x
        rw [hρ]
        rfl
      map_mul' := fun σ τ => by
        apply AlgEquiv.ext
        intro y
        obtain ⟨x, rfl⟩ := hsurj y
        change ρ (σ * τ) (red x) = ρ σ (ρ τ (red x))
        rw [hρ, hρ, hρ]
        rfl }
  -- An automorphism of the splitting field is determined by its action on the roots.
  have hinj : Function.Injective φ := by
    intro σ τ hστ
    apply Subtype.ext
    apply AlgEquiv.coe_toAlgHom_injective
    apply AlgHom.ext_of_adjoin_eq_top (Polynomial.IsSplittingField.adjoin_rootSet L f)
    intro x hx
    let σ₀ : L ≃ₐ[RatFunc k] L := σ
    let τ₀ : L ≃ₐ[RatFunc k] L := τ
    have hσx := Polynomial.rootSet_mapsTo σ₀.toAlgHom hx
    have hτx := Polynomial.rootSet_mapsTo τ₀.toAlgHom hx
    obtain ⟨F, hF⟩ := hmatch.1 x hx
    let x' : A := ⟨x, (nonnegative_iff_powerSeries _).2 ⟨F, hF⟩⟩
    have h := DFunLike.congr_fun hστ (red x')
    change ρ σ (red x') = ρ τ (red x') at h
    rw [hρ, hρ] at h
    apply hmatch.2.injOn hσx hτx
    exact (reduction_apply _ _).symm.trans (h.trans (reduction_apply _ _))
  have honto : Function.Surjective φ := by
    intro τ
    obtain ⟨σ, hσ⟩ := liftFibreAutomorphism f i τ
    refine ⟨σ, AlgEquiv.ext fun y => ?_⟩
    obtain ⟨x, rfl⟩ := hsurj y
    change ρ σ (red x) = τ (red x)
    rw [hρ]
    change reduction i.toRingHom (onValuationRing i σ x) =
      τ (reduction i.toRingHom x)
    rw [reduction_apply, reduction_apply]
    change (i ((σ : L ≃ₐ[RatFunc k] L) (x : L))).coeff 0 = τ ((i (x : L)).coeff 0)
    rw [hσ, laurentMap_coeff]
    rfl
  exact ⟨MulEquiv.ofBijective φ ⟨hinj, honto⟩, hρ⟩

end

end GaloisFormalization.IG.SpecializationDecomposition
