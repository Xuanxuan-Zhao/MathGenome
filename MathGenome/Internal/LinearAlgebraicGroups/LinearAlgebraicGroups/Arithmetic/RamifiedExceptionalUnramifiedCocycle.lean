import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalUnramifiedCocycle
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalFormsOverUnramifiedFields
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.NonabelianCohomology
import Batteries.Tactic.OpenPrivate
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Tactic.Group

import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
open CategoryTheory
open scoped CategoryTheory.MonObj

namespace LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalUnramifiedCocycle

section UnramifiedDescent

open MaximalUnramifiedBrauer (IsUnramified maximalUnramified mem_maximalUnramified_iff)
open LinearAlgebraicGroups.Descent.NonabelianCohomology
open Polynomial ValuativeRel IsLocalRing
open Specs.RamifiedExceptionalUnramifiedCocycle (integers residueField Reduces)
attribute [local instance] Specs.ExceptionalLocalRootCoordinates.canonicalExtension
open scoped Topology WithZero

open private cyclotomicStage le_cyclotomicStage_of_unramified roots_X_pow_sub_one finrank_le_residue_of_adjoin_roots
  map_maximalIdeal_of_finrank_le_residue surjective_of_map_maximalIdeal from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
open private descend_of_trivial_on_kernel eventually_trivial restriction_ker from
  MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.NonabelianCohomology

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- Surjectivity on values for a finite unramified extension identifies the two
normalized valuations used in the marked affine comparison. -/
private theorem unramifiedLocalExtensionOfSurjectiveValues
    {K : Type u} [Field K] [Algebra F K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    (hs : Function.Surjective (fun z : F => valuation K (algebraMap F K z))) :
    Specs.ExceptionalAffineBruhat.IsUnramifiedLocalExtension F K := by
  let eF := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  let eK := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let m := ValuativeExtension.mapValueGroupWithZero F K
  let f : ℤᵐ⁰ →*₀ ℤᵐ⁰ := eK.toMonoidWithZeroHom.comp (m.comp eF.symm.toMonoidWithZeroHom)
  have hm : StrictMono f :=
    eK.strictMono.comp ((ValuativeExtension.mapValueGroupWithZero_strictMono
      (A := F) (B := K)).comp eF.symm.strictMono)
  have hv (z : F) : f (eF (valuation F z)) = eK (valuation K (algebraMap F K z)) := by
    change eK (m (eF.symm (eF (valuation F z)))) = _
    rw [eF.symm_apply_apply, ValuativeExtension.mapValueGroupWithZero_valuation]
  obtain ⟨z, hz⟩ := hs (eK.symm (WithZero.exp 1))
  change valuation K (algebraMap F K z) = _ at hz
  have hpre : f (eF (valuation F z)) = WithZero.exp 1 := by
    rw [hv, hz, eK.apply_symm_apply]
  have hexp : (1 : ℤᵐ⁰) < WithZero.exp 1 := WithZero.one_lt_exp_iff.mpr Int.zero_lt_one
  have hz₁ : 1 < eF (valuation F z) := by
    apply hm.lt_iff_lt.mp
    rwa [map_one, hpre]
  have hmin {x : ℤᵐ⁰} (hx : 1 < x) : WithZero.exp 1 ≤ x := by
    have h := WithZero.lt_mul_exp_iff_le (x := x) (y := 1) one_ne_zero
    exact le_of_not_gt (fun hx' => hx.not_ge (h.mp (by simpa only [one_mul] using hx')))
  have hf₁ : f (WithZero.exp 1) = WithZero.exp 1 := by
    apply le_antisymm
    · exact (hm.monotone (hmin hz₁)).trans_eq hpre
    · apply hmin
      simpa only [map_one] using hm hexp
  have hid (x : ℤᵐ⁰) : f x = x := by
    obtain rfl | hx := eq_or_ne x 0
    · exact map_zero f
    lift x to ℤ using hx
    have he (a : ℤ) : WithZero.exp a = (WithZero.exp (1 : ℤ)) ^ a := by
      rw [← WithZero.exp_zsmul]
      exact congrArg WithZero.exp (by simp)
    rw [he, map_zpow₀, hf₁]
  intro z
  change eK (valuation K (algebraMap F K z)) = eF (valuation F z)
  rw [← hv, hid]

private noncomputable def closureEquiv (F S : Type u) [Field F] [Field S] [Algebra F S]
    [IsSepClosure F S] : SeparableClosure F ≃ₐ[F] S :=
  IsSepClosure.equiv F (SeparableClosure F) S

variable {S : Type u} [Field S] [Algebra F S] [IsSepClosure F S]

private noncomputable def unramifiedSubfield (F S : Type u) [Field F] [Field S] [Algebra F S]
    [IsSepClosure F S] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IntermediateField F S :=
  (maximalUnramified F).map (closureEquiv F S).toAlgHom

private theorem cyclotomicData {n : ℕ} (hn : (n : residueField F) ≠ 0) :
    ∃ K : FiniteGaloisIntermediateField F S, IsUnramified F K ∧
      ((X ^ n - Polynomial.C (1 : F)).map (algebraMap F K)).Splits ∧
      K.toIntermediateField = (cyclotomicStage F n).map (closureEquiv F S).toAlgHom := by
  let p : F[X] := X ^ n - Polynomial.C 1
  have hnF : (n : F) ≠ 0 := by
    intro hz
    apply hn
    have hzO : (n : integers F) = 0 := by
      apply Subtype.ext
      simpa using hz
    simpa only [map_natCast, map_zero] using congrArg (IsLocalRing.residue (integers F)) hzO
  have hn' : n ≠ 0 := fun h => hn (by simp [h])
  have hsep : p.Separable := separable_X_pow_sub_C 1 hnF one_ne_zero
  have hsplit : (p.map (algebraMap F S)).Splits :=
    (IsSepClosure.sep_closed F (K := S)).splits_codomain p hsep
  let K := IntermediateField.adjoin F (p.rootSet S)
  let : p.IsSplittingField F K := IntermediateField.adjoin_rootSet_isSplittingField hsplit
  let : FiniteDimensional F K := Polynomial.IsSplittingField.finiteDimensional K p
  let : IsGalois F K := IsGalois.of_separable_splitting_field hsep
  obtain ⟨r, T, hext, hlocal, _, _, _⟩ := finiteExtension_localField (K := F) (L := K)
  let : ValuativeRel K := r
  let : TopologicalSpace K := T
  have hgen : IntermediateField.adjoin F {x : K | x ^ n = 1} = ⊤ := by
    rw [← roots_X_pow_sub_one (B := F) hn']
    exact (isSplittingField_iff_intermediateField.mp (inferInstance : p.IsSplittingField F K)).2
  have hle := finrank_le_residue_of_adjoin_roots hn hgen
  refine ⟨{ K with finiteDimensional := inferInstance, isGalois := inferInstance },
    ⟨inferInstance, inferInstance, r, T, hlocal, hext,
      surjective_of_map_maximalIdeal (map_maximalIdeal_of_finrank_le_residue hle)⟩,
    Polynomial.IsSplittingField.splits K p, ?_⟩
  change K = _
  dsimp [K, cyclotomicStage, p]
  rw [IntermediateField.adjoin_map, roots_X_pow_sub_one hn', roots_X_pow_sub_one hn']
  congr 1
  ext x
  constructor
  · intro hx
    refine ⟨(closureEquiv F S).symm x, ?_, (closureEquiv F S).apply_symm_apply x⟩
    change ((closureEquiv F S).symm x) ^ n = 1
    rw [← map_pow, show x ^ n = 1 from hx, map_one]
  · rintro ⟨y, hy, rfl⟩
    change (closureEquiv F S y) ^ n = 1
    rw [← map_pow, show y ^ n = 1 from hy, map_one]

private theorem le_cyclotomicStageIn {B : IntermediateField F S}
    [FiniteDimensional F B] (hB : B ≤ unramifiedSubfield F S) :
    ∃ n : ℕ, (n : residueField F) ≠ 0 ∧
      B ≤ (cyclotomicStage F n).map (closureEquiv F S).toAlgHom := by
  obtain ⟨a, ha⟩ := Field.exists_primitive_element F B
  obtain ⟨x, hx, hxa⟩ := hB a.property
  obtain ⟨U, hU, hxU⟩ := mem_maximalUnramified_iff.mp hx
  obtain ⟨n, hn, hUn⟩ := le_cyclotomicStage_of_unramified hU
  refine ⟨n, hn, ?_⟩
  have he : IntermediateField.adjoin F ({(a : S)} : Set S) = B := by
    change IntermediateField.adjoin F ({B.val a} : Set S) = B
    rw [← Set.image_singleton (f := B.val) (a := a), ← IntermediateField.adjoin_map, ha,
      ← AlgHom.fieldRange_eq_map, B.fieldRange_val]
  rw [← he]
  exact IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ⟨x, hUn hxU, hxa⟩)

private theorem finiteUnramifiedStage {B : IntermediateField F S}
    [FiniteDimensional F B] (hB : B ≤ unramifiedSubfield F S) :
    ∃ E : FiniteGaloisIntermediateField F S, IsUnramified F E ∧ B ≤ E.toIntermediateField := by
  obtain ⟨n, hn, hBn⟩ := le_cyclotomicStageIn hB
  obtain ⟨E, hE, _, he⟩ := cyclotomicData (S := S) hn
  exact ⟨E, hE, he.symm ▸ hBn⟩

/-- A continuous cocycle trivial on the fixing group of the maximal unramified
extension descends to a finite unramified Galois group with the corresponding
kernel-fixed coefficients. -/
private theorem cocycleDescendsAtUnramifiedLevel
    {M : Type v} [Group M] [TopologicalSpace M] [DiscreteTopology M]
    {ρ : Gal(S/F) →* MulAut M} (a : Cocycle ρ)
    (ha : ∀ σ ∈ (unramifiedSubfield F S).fixingSubgroup, a σ = 1) :
    ∃ (E : FiniteGaloisIntermediateField F (S))
      (c : Cocycle (levelAction ρ E)), IsUnramified F E ∧ DescendsAt ρ a E c := by
  let U : Subgroup Gal(S/F) :=
    { carrier := {σ | a σ = 1}
      one_mem' := a.map_one
      mul_mem' := fun {σ τ} hσ hτ => by
        change a σ = 1 at hσ
        change a τ = 1 at hτ
        change a (σ * τ) = 1
        simp [a.property.2, hσ, hτ]
      inv_mem' := fun {σ} hσ => by
        change a σ = 1 at hσ
        change a σ⁻¹ = 1
        have h := a.property.2 σ⁻¹ σ
        simpa [hσ] using h.symm }
  have hclosed : IsClosed (U : Set Gal(S/F)) :=
    (isClosed_discrete ({1} : Set M)).preimage a.property.1
  let B := IntermediateField.fixedField U
  have hBK : B ≤ unramifiedSubfield F S := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (unramifiedSubfield F S)]
    exact IntermediateField.fixedField_le ha
  obtain ⟨L, hL⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois _).mp
    (eventually_trivial a)
  have hBL : B ≤ L.toIntermediateField := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup L.toIntermediateField]
    exact IntermediateField.fixedField_le hL
  let f := IntermediateField.inclusion hBL
  let : FiniteDimensional F B := FiniteDimensional.of_injective f.toLinearMap f.injective
  obtain ⟨E, hE, hBE⟩ := finiteUnramifiedStage hBK
  have hfix : B.fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨U, hclosed⟩
  have hker : ∀ σ ∈ (restriction E).ker, a σ = 1 := by
    rw [restriction_ker]
    intro σ hσ
    have hm := IntermediateField.fixingSubgroup_le hBE hσ
    rwa [hfix] at hm
  obtain ⟨c, hc⟩ := descend_of_trivial_on_kernel
    (AlgEquiv.restrictNormalHom_surjective (S)) a hker
  exact ⟨E, c, hE, hc⟩

set_option maxHeartbeats 600000 in
/-- Inflation from an unramified finite stage can be expressed using actual
rational points and their coefficient action. -/
private theorem pointCocycleDescendsAtUnramifiedLevel
    (G : Specs.GroupScheme F)
    (a : @Cocycle (Gal(S/F))
      (LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F (S) G.X)
      _ (krullTopology F (S)) _ ⊥ (pointAction F (S) G.X))
    (ha : ∀ σ ∈ (unramifiedSubfield F S).fixingSubgroup, a σ = 1) :
    ∃ (E : FiniteGaloisIntermediateField F (S))
      (r : ValuativeRel E) (T : TopologicalSpace E),
      letI := r
      letI := T
      ∃ (hlocal : IsNonarchimedeanLocalField E) (_ : ValuativeExtension F E),
        letI := hlocal
        Specs.ExceptionalAffineBruhat.IsUnramifiedLocalExtension F E ∧
        ∃ c : Gal(E/F) → LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F E G.X,
          (∀ σ τ, c (σ * τ) = c σ * pointAction F E G.X σ (c τ)) ∧
          ∀ σ, pointMap F E G.X E.toIntermediateField.val (c (restriction E σ)) = a σ := by
  let : TopologicalSpace (LinearAlgebraicGroups.Descent.NonabelianCohomology.Points
    F (S) G.X) := ⊥
  let : DiscreteTopology (LinearAlgebraicGroups.Descent.NonabelianCohomology.Points
    F (S) G.X) := ⟨rfl⟩
  obtain ⟨E, c, ⟨_, _, r, T, hlocal, hext, hs⟩, hc⟩ :=
    cocycleDescendsAtUnramifiedLevel a ha
  let := r
  let := T
  obtain ⟨e, hmap, hact⟩ := finitePointsIdentification (H := G.X) E
  refine ⟨E, r, T, hlocal, hext, unramifiedLocalExtensionOfSurjectiveValues hs,
    fun σ => e.symm (c σ), ?_, ?_⟩
  · intro σ τ
    apply e.injective
    simpa only [MulEquiv.apply_symm_apply, map_mul, hact] using c.property.2 σ τ
  · intro σ
    rw [← hmap, MulEquiv.apply_symm_apply, hc]

end UnramifiedDescent

section ResidueComparison

open ValuativeRel IsLocalRing
open Specs.ExceptionalAffineBruhat (IsUnramifiedLocalExtension)
open Specs.RamifiedExceptionalUnramifiedCocycle
  (integers residueField Reduces ResidueGaloisComparison ResidueGaloisRestriction)
attribute [local instance] Specs.ExceptionalLocalRootCoordinates.canonicalExtension

open private restrictToIntegers unramified_adjoin_roots residue_natCast_ne_zero_iff
  root_of_unity_mem_integer root_of_unity_eq_of_residue_eq valuation_isIntegralClosure
  map_maximalIdeal_of_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K]

omit [ValuativeExtension F K] in
private theorem surjectiveValuesOfUnramified (h : IsUnramifiedLocalExtension F K) :
    Function.Surjective (fun z : F => valuation K (algebraMap F K z)) := by
  let eF := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  let eK := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  intro z
  obtain ⟨x, hx⟩ := valuation_surjective (eF.symm (eK z))
  refine ⟨x, eK.injective ?_⟩
  have hn := h x
  change eK (valuation K (algebraMap F K x)) = eF (valuation F x) at hn
  change eK (valuation K (algebraMap F K x)) = eK z
  rw [hn, hx, eF.apply_symm_apply]

private noncomputable def reductionHom [FiniteDimensional F K] :
    Gal(K/F) →* Gal(residueField K / residueField F) where
  toFun σ := ResidueField.mapAlgEquiv' (restrictToIntegers σ)
  map_one' := by
    ext x : 1
    obtain ⟨a, rfl⟩ := residue_surjective x
    rfl
  map_mul' σ τ := by
    ext x : 1
    obtain ⟨a, rfl⟩ := residue_surjective x
    rfl

private theorem residueDegree [FiniteDimensional F K] [Algebra.IsSeparable F K]
    (h : IsUnramifiedLocalExtension F K) :
    Module.finrank (residueField F) (residueField K) = Module.finrank F K := by
  let : IsIntegralClosure (integers K) (integers F) K := valuation_isIntegralClosure
  let : Module.Finite (integers F) (integers K) :=
    IsIntegralClosure.finite (integers F) F K (integers K)
  let : Module.Free (integers F) (integers K) :=
    IsIntegralClosure.module_free (integers F) F K (integers K)
  have hmap := map_maximalIdeal_of_surjective (surjectiveValuesOfUnramified h)
  -- Identify the two quotients by the equality of maximal ideals.
  let p := maximalIdeal (integers F)
  let pK := p.map (algebraMap (integers F) (integers K))
  let : Algebra (residueField F) (integers K ⧸ pK) :=
    Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  have hfin := (IsLocalRing.finrank_quotient_map (R := integers F) (S := integers K)).trans
    (IsIntegralClosure.rank (integers F) F K (integers K))
  have heq : (integers K ⧸ (maximalIdeal (integers F)).map
      (algebraMap (integers F) (integers K))) ≃ₐ[residueField F] residueField K :=
    { Ideal.quotEquivOfEq hmap with
      commutes' := fun a => by
        obtain ⟨a, rfl⟩ := residue_surjective a
        rfl }
  exact heq.toLinearEquiv.finrank_eq.symm.trans hfin

private theorem reductionHom_injective [FiniteDimensional F K] [IsGalois F K]
    (h : IsUnramifiedLocalExtension F K) : Function.Injective (reductionHom (F := F) (K := K)) := by
  obtain ⟨n, hn, hgen⟩ := unramified_adjoin_roots (surjectiveValuesOfUnramified h)
  intro σ τ heq
  have htop : Algebra.adjoin F {x : K | x ^ n = 1} = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic (R := F) x), hgen]
    rfl
  have hστ : σ.toAlgHom = τ.toAlgHom := AlgHom.ext_of_adjoin_eq_top htop <| by
    intro x hx
    change x ^ n = 1 at hx
    have hn' : n ≠ 0 := fun h => hn (by simp [h])
    let a : integers K := ⟨x, root_of_unity_mem_integer hn' hx⟩
    have heq' : residue (integers K) (restrictToIntegers σ a) =
        residue (integers K) (restrictToIntegers τ a) :=
      DFunLike.congr_fun heq (residue (integers K) a)
    have hxσ : (σ x) ^ n = 1 := by rw [← map_pow, hx, map_one]
    have hxτ : (τ x) ^ n = 1 := by rw [← map_pow, hx, map_one]
    exact congrArg Subtype.val (root_of_unity_eq_of_residue_eq
      ((residue_natCast_ne_zero_iff (L := K) n).mp hn) hxσ hxτ heq')
  ext x
  exact DFunLike.congr_fun hστ x

private theorem residueGaloisComparisonProof : ResidueGaloisComparison.{u} := by
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ h
  let : Finite (residueField K) :=
    IsNonarchimedeanLocalField.instFiniteResidueFieldSubtypeMemSubringIntegerValueGroupWithZeroValuation K
  let : IsGalois (residueField F) (residueField K) := inferInstance
  have hcard : Nat.card Gal(K/F) = Nat.card Gal(residueField K / residueField F) := by
    rw [IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank, residueDegree h]
  have hb := (Nat.bijective_iff_injective_and_card (reductionHom (F := F) (K := K))).mpr
    ⟨reductionHom_injective h, hcard⟩
  refine ⟨MulEquiv.ofBijective _ hb, fun σ x => ?_⟩
  exact ⟨restrictToIntegers σ x, rfl, rfl⟩

private theorem residueGaloisRestrictionProof : ResidueGaloisRestriction.{u} := by
  intro F K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ τ υ hτ hυ x
  obtain ⟨x, rfl⟩ := residue_surjective x
  obtain ⟨y, hy, hυy⟩ := hυ x
  obtain ⟨z, hz, hτz⟩ := hτ (algebraMap (integers K) (integers L) x)
  have he : algebraMap (integers K) (integers L) y = z := by
    apply Subtype.ext
    change algebraMap K L (y : K) = (z : L)
    rw [hy, hz]
    exact AlgEquiv.restrictNormal_commutes σ K (x : K)
  rw [ResidueField.algebraMap_residue, hτz, hυy, ResidueField.algebraMap_residue, he]

end ResidueComparison

section ResidueEnlargement

open Polynomial ValuativeRel IsLocalRing
open Specs.ExceptionalAffineBruhat (IsUnramifiedLocalExtension)
open Specs.RamifiedExceptionalUnramifiedCocycle (integers residueField UnramifiedResidueEnlargement)
open private cyclotomicStage cyclotomicStage_le_of_dvd roots_X_pow_sub_one
  root_of_unity_mem_integer residue_natCast_ne_zero_iff unramified_adjoin_roots
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
attribute [local instance] Specs.ExceptionalLocalRootCoordinates.canonicalExtension

private theorem residueSplitsRootsOfUnity {L : Type u} [Field L] [ValuativeRel L]
    {n : ℕ} (hn : n ≠ 0) (hs : (X ^ n - Polynomial.C (1 : L)).Splits) :
    (X ^ n - (1 : (residueField L)[X])).Splits := by
  let f : (integers L)[X] := X ^ n - 1
  let i := algebraMap (integers L) L
  have hmap : f.map i = X ^ n - Polynomial.C (1 : L) := by simp [f]
  have hsplit : f.Splits := by
    apply Polynomial.Splits.of_splits_map_of_injective (i := i)
      (f := f) Subtype.val_injective (hmap.symm ▸ hs)
    intro x hx
    rw [hmap] at hx
    have hroot := (Polynomial.mem_roots
      (Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hn) (1 : L))).mp hx
    have hpow : x ^ n = 1 := by simpa [Polynomial.IsRoot, sub_eq_zero] using hroot
    exact ⟨⟨x, root_of_unity_mem_integer hn hpow⟩, rfl⟩
  simpa only [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
    using hsplit.map (residue (integers L))

/-- Uniqueness of the extension to the top field makes the chosen valuative
relations compatible with the middle field. -/
private theorem valuativeExtensionOfTower {F K L : Type u} [Field F] [Field K] [Field L]
    [Algebra F K] [Algebra F L] [Algebra K L] [IsScalarTower F K L]
    [FiniteDimensional F L] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
    [r : ValuativeRel L] [h : ValuativeExtension F L] :
    ValuativeExtension K L := by
  let : FiniteDimensional K L := FiniteDimensional.right F K L
  obtain ⟨r', _, hext', _, _, _, _⟩ := finiteExtension_localField (K := K) (L := L)
  have hFL : @ValuativeExtension F L _ _ _ r' _ := by
    let : ValuativeRel L := r'
    constructor
    intro a b
    rw [IsScalarTower.algebraMap_apply F K L, IsScalarTower.algebraMap_apply F K L,
      @ValuativeExtension.vle_iff_vle K L _ _ _ r' _ hext',
      ValuativeExtension.vle_iff_vle (A := F) (B := K)]
  obtain ⟨r₀, _, _, _, _, _, huniq⟩ := finiteExtension_localField (K := F) (L := L)
  have hr : r' = r := (huniq r' hFL).trans (huniq r h).symm
  exact Eq.mp (congrArg (fun s => @ValuativeExtension K L _ _ _ s _) hr) hext'

private theorem unramifiedResidueEnlargementProof : UnramifiedResidueEnlargement.{u} := by
  intro F S _ _ _ _ _ _ _ K _ _ _ _ hK R _ _ _
  classical
  let : Fintype R := Fintype.ofFinite R
  let q := Fintype.card R
  let m := q - 1
  have hq : 1 < q := Fintype.one_lt_card
  have hmR : (m : R) ≠ 0 := by
    change ((q - 1 : ℕ) : R) ≠ 0
    rw [Nat.cast_sub hq.le, Nat.cast_card_eq_zero]
    simp
  have hmK : (m : residueField K) ≠ 0 := fun h =>
    hmR (by simpa only [map_natCast, map_zero] using congrArg (algebraMap (residueField K) R) h)
  have hmF : (m : residueField F) ≠ 0 :=
    (residue_natCast_ne_zero_iff (L := K) m).mpr hmK
  obtain ⟨n, hn, hgen⟩ := unramified_adjoin_roots (surjectiveValuesOfUnramified hK)
  have hn₀ : n ≠ 0 := fun h => hn (by simp [h])
  have hmn : (n * m : ℕ) ≠ 0 := Nat.mul_ne_zero hn₀ (fun h => hmF (by simp [h]))
  have hnF : ((n * m : ℕ) : residueField F) ≠ 0 := by
    rw [Nat.cast_mul]
    exact mul_ne_zero hn hmF
  obtain ⟨L, ⟨_, _, r, T, hlocal, hext, hsurj⟩, hsplit, hL⟩ :=
    cyclotomicData (S := S) hnF
  have hle : K.toIntermediateField ≤ L.toIntermediateField := by
    rw [hL]
    have hsub : K.toIntermediateField ≤
        (cyclotomicStage F n).map (closureEquiv F S).toAlgHom := by
      rw [← K.toIntermediateField.fieldRange_val, AlgHom.fieldRange_eq_map, ← hgen,
        IntermediateField.adjoin_map]
      apply IntermediateField.adjoin_le_iff.mpr
      rintro _ ⟨x, hx, rfl⟩
      let y := (closureEquiv F S).symm (x : S)
      have hy : y ^ n = 1 := by
        change ((closureEquiv F S).symm (K.toIntermediateField.val x)) ^ n = 1
        change x ^ n = 1 at hx
        rw [← map_pow, ← map_pow, hx, map_one, map_one]
      refine ⟨y, ?_, (closureEquiv F S).apply_symm_apply _⟩
      apply IntermediateField.subset_adjoin
      rw [roots_X_pow_sub_one (B := F) (C := SeparableClosure F) hn₀]
      exact hy
    exact hsub.trans (IntermediateField.map_mono _
      (cyclotomicStage_le_of_dvd hn₀ hmn (dvd_mul_right n m)))
  let : Algebra K L := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  let : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x =>
    ((IntermediateField.inclusion hle).commutes x).symm
  let : ValuativeRel L := r
  let : TopologicalSpace L := T
  let : IsNonarchimedeanLocalField L := hlocal
  let : ValuativeExtension F L := hext
  let hKL : ValuativeExtension K L := valuativeExtensionOfTower (F := F)
  have hsurjKL : Function.Surjective (fun x : K => valuation L (algebraMap K L x)) := by
    intro v
    obtain ⟨x, hx⟩ := hsurj v
    refine ⟨algebraMap F K x, ?_⟩
    change valuation L (algebraMap K L (algebraMap F K x)) = v
    rw [← IsScalarTower.algebraMap_apply F K L]
    exact hx
  refine ⟨L, hle, r, T, hlocal, hext, hKL, unramifiedLocalExtensionOfSurjectiveValues hsurj,
    unramifiedLocalExtensionOfSurjectiveValues hsurjKL, ?_⟩
  have hsL : (X ^ (n * m) - Polynomial.C (1 : L)).Splits := by
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
      Polynomial.map_one, map_one] using hsplit
  have hsm : (X ^ m - (1 : (residueField L)[X])).Splits :=
    (residueSplitsRootsOfUnity hmn hsL).of_dvd
      (by simpa only [Polynomial.C_1] using
        (Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hmn) (1 : residueField L)))
      (by
        simpa only [← pow_mul, Nat.mul_comm m n] using
          sub_one_dvd_pow_sub_one (X ^ m : (residueField L)[X]) n)
  refine ⟨Polynomial.IsSplittingField.lift R (X ^ q - X) ?_⟩
  simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
  have hq' : q = m + 1 := by omega
  rw [hq', pow_succ]
  simpa only [sub_mul, one_mul] using hsm.mul (Polynomial.Splits.X (R := residueField L))

end ResidueEnlargement

section Inertia

open AlgebraicGeometry Opposite WithConv Coalgebra
open scoped TensorProduct
open _root_.LinearAlgebraicGroups.Specs
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology
open Specs.AutomorphismSequence (AdjointQuotient SplitSequence)
open Specs.CharacterDescent (StandardLattice)
open Specs.ExceptionalFormsOverUnramifiedFields (IsExceptionalReference)
open Specs.ExceptionalTwistedTraceComparison (projectionOnPoints)
open Specs.Pinning (AttachedDatum PinnedGroup)
open Specs.QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction basedAutTopology
  fieldGalTopology)
open Specs.RootGroups (AdditiveLine)
open Specs.RamifiedExceptionalUnramifiedCocycle (FiniteUnramifiedInflation)
open MaximalUnramifiedBrauer (maximalUnramified)
open Specs.DiagonalizableGroups (groupAlgebra)
open _root_.LinearAlgebraicGroups.CharacterDescent
  (extendedHopfFunctor extendedHopfTower groupAlgebraBaseChange)
open ExceptionalFormsOverUnramifiedFields (cocycle_into_subgroup)
open scoped Topology

attribute [local instance] basedAutTopology fieldGalTopology

open private matching_twisted_point adjoint_cocycle_fixes torus_embedding
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalFormsOverUnramifiedFields

variable {F K S : Type u} [Field F] [Field K] [Field S]
  [Algebra F K] [Algebra F S] [Algebra K S] [IsScalarTower F K S] [IsSepClosure F S]

private theorem continuousRestrictionOfScalars [Algebra.IsAlgebraic K S] :
    Continuous (AlgEquiv.restrictScalarsHom F : Gal(S/K) →* Gal(S/F)) := by
  let f : Gal(S/K) →* Gal(S/F) := AlgEquiv.restrictScalarsHom F
  apply continuous_of_continuousAt_one f
  rw [ContinuousAt, map_one, Filter.tendsto_def]
  intro U hU
  obtain ⟨L, _, hLU⟩ := (krullTopology_mem_nhds_one_iff F S U).mp hU
  obtain ⟨a, ha⟩ := Field.exists_primitive_element F L
  have hopen := stabilizer_isOpen_of_isIntegral (K := K) (a : S)
  refine Filter.mem_of_superset (hopen.mem_nhds ((MulAction.stabilizer Gal(S/K) (a : S)).one_mem))
    fun σ hσ => hLU ?_
  have he : IntermediateField.adjoin F ({(a : S)} : Set S) = L := by
    change IntermediateField.adjoin F ({L.val a} : Set S) = L
    rw [← Set.image_singleton (f := L.val) (a := a), ← IntermediateField.adjoin_map, ha,
      ← AlgHom.fieldRange_eq_map, L.fieldRange_val]
  change f σ ∈ L.fixingSubgroup
  rw [← he, IntermediateField.mem_fixingSubgroup_iff]
  change ∀ x ∈ IntermediateField.adjoin F ({(a : S)} : Set S), (f σ) • x = x
  rw [IntermediateField.forall_mem_adjoin_smul_eq_self_iff]
  intro x hx
  have hx' : x = (a : S) := Set.mem_singleton_iff.mp hx
  subst x
  exact MulAction.mem_stabilizer_iff.mp hσ

private theorem torusOverIntermediateField [IsSepClosure K S]
    (B : HopfAlgebraCategory F) (hB : Specs.CharacterDescent.IsTorus B) :
    Specs.CharacterDescent.IsTorus (extendedHopf K B) := by
  obtain ⟨E, _, _, _, r, ⟨i⟩⟩ := hB
  let : IsSepClosed S := IsSepClosure.sep_closed F
  let f : E →ₐ[F] S := IsSepClosed.lift
  let : Algebra E S := f.toRingHom.toAlgebra
  let : IsScalarTower F E S := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  refine ⟨S, ‹Field S›, ‹Algebra K S›, inferInstance, r, ⟨?_⟩⟩
  exact (CommHopfAlgCat.isoMk (groupAlgebraBaseChange E S (StandardLattice.{u} r))).symm ≪≫
    (extendedHopfFunctor S).mapIso i ≪≫ extendedHopfTower (K := E) S B ≪≫
      (extendedHopfTower (K := K) S B).symm

private abbrev extendTorusPoint (B : HopfAlgebraCategory F) (a : B →ₐ[F] S) :
    extendedHopf K B →ₐ[K] S :=
  Algebra.TensorProduct.liftEquivRight F K B S a

omit [IsSepClosure F S] in
private theorem extendTorusPoint_tmul (B : HopfAlgebraCategory F) (a : B →ₐ[F] S)
    (x : K) (y : B) :
    extendTorusPoint B a (x ⊗ₜ[F] y) = algebraMap K S x * a y :=
  Algebra.TensorProduct.lift_tmul (Algebra.ofId K S) a (fun _ _ => Commute.all _ _) x y

private noncomputable def extendConvolution (B : HopfAlgebraCategory F) :
    (convolutionPoints B).obj (CommAlgCat.of F S) ≃*
      (convolutionPoints (extendedHopf K B)).obj (CommAlgCat.of K S) where
  toFun f := toConv (extendTorusPoint B f.ofConv)
  invFun f := toConv ((Algebra.TensorProduct.liftEquivRight F K B S).symm f.ofConv)
  left_inv f := WithConv.ofConv_injective ((Algebra.TensorProduct.liftEquivRight F K B S).left_inv _)
  right_inv f := WithConv.ofConv_injective ((Algebra.TensorProduct.liftEquivRight F K B S).right_inv _)
  map_mul' f g := by
    apply WithConv.ofConv_injective
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro a
    let fK : WithConv (extendedHopf K B →ₐ[K] S) := toConv (extendTorusPoint B f.ofConv)
    let gK : WithConv (extendedHopf K B →ₐ[K] S) := toConv (extendTorusPoint B g.ofConv)
    change extendTorusPoint B (f * g).ofConv (1 ⊗ₜ[F] a) = (fK * gK) (1 ⊗ₜ[F] a)
    rw [extendTorusPoint_tmul, map_one, one_mul]
    let f' : WithConv (B →ₐ[F] S) := f
    let g' : WithConv (B →ₐ[F] S) := g
    change (f' * g') a = _
    rw [AlgHom.convMul_apply, AlgHom.convMul_apply, TensorProduct.comul_tmul]
    generalize comul (R := F) a = t
    induction t using TensorProduct.inductionOn with
    | tmul a b =>
      simp [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, f', g', fK, gK]
    | add a b ha hb =>
      simp only [TensorProduct.tmul_add, map_add, ha, hb]

private noncomputable def torusPointEquiv (B : HopfAlgebraCategory F) :
    _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X ≃*
      _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points K S (specGroup (extendedHopf K B)).X :=
  (((hopfSpecPointIso B).app (CommAlgCat.of F S)).groupIsoToMulEquiv.symm.trans
    (extendConvolution B)).trans
      (((hopfSpecPointIso (extendedHopf K B)).app (CommAlgCat.of K S)).groupIsoToMulEquiv)

omit [IsSepClosure F S] in
private theorem torusPointEquiv_action (B : HopfAlgebraCategory F) (σ : Gal(S/K))
    (a : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X) :
    torusPointEquiv B (pointAction F S (specGroup B).X (σ.restrictScalars F) a) =
      pointAction K S (specGroup (extendedHopf K B)).X σ (torusPointEquiv B a) := by
  let C := extendedHopf K B
  let R := CommAlgCat.of F S
  let T := CommAlgCat.of K S
  let e := hopfSpecPointIso B
  let i := hopfSpecPointIso C
  let f : R ⟶ R := CommAlgCat.ofHom (σ.restrictScalars F).toAlgHom
  let g : T ⟶ T := CommAlgCat.ofHom σ.toAlgHom
  have he := e.inv.naturality_apply f a
  change e.inv.app R (pointAction F S (specGroup B).X (σ.restrictScalars F) a) =
    toConv ((σ.restrictScalars F).toAlgHom.comp (e.inv.app R a).ofConv) at he
  have hi := i.inv.naturality_apply g (torusPointEquiv B a)
  change i.inv.app T (pointAction K S (specGroup C).X σ (torusPointEquiv B a)) =
    toConv (σ.toAlgHom.comp (i.inv.app T (torusPointEquiv B a)).ofConv) at hi
  apply (i.app T).groupIsoToMulEquiv.symm.injective
  change _ = i.inv.app T _
  rw [hi]
  have cancel (x : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X) :
      i.inv.app T (torusPointEquiv B x) = extendConvolution B (e.inv.app R x) :=
    (i.app T).groupIsoToMulEquiv.symm_apply_apply _
  have hc (z : (convolutionPoints B).obj R) :
      extendConvolution (K := K) B (toConv ((σ.restrictScalars F).toAlgHom.comp z.ofConv)) =
        toConv (σ.toAlgHom.comp (extendConvolution (K := K) B z).ofConv) := by
    apply WithConv.ofConv_injective
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro b
    simp [extendConvolution]
  exact (cancel _).trans ((congrArg (extendConvolution (K := K) B) he).trans
    ((hc _).trans (congrArg (fun z => toConv (σ.toAlgHom.comp z.ofConv)) (cancel a).symm)))

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

set_option maxHeartbeats 600000 in
private theorem restrictTorusCocycleIsNeutral (B : HopfAlgebraCategory F)
    (hB : Specs.CharacterDescent.IsTorus B)
    (a : @Cocycle (Gal(S/F)) (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X)
      _ (krullTopology F S) _ ⊥ (pointAction F S (specGroup B).X)) :
    let K := maximalUnramified F
    let f : K →ₐ[F] S := (closureEquiv F S).toAlgHom.comp (maximalUnramified F).val
    letI : Algebra K S := f.toRingHom.toAlgebra
    letI : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
    ∃ b : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X, ∀ σ : Gal(S/K),
      (1 : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X) =
        b⁻¹ * (a.val (σ.restrictScalars F) : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X) *
          pointAction F S (specGroup B).X (σ.restrictScalars F) b := by
  dsimp only
  let K := maximalUnramified F
  let f : K →ₐ[F] S := (closureEquiv F S).toAlgHom.comp (maximalUnramified F).val
  let : Algebra K S := f.toRingHom.toAlgebra
  let : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let : IsSepClosure K S :=
    ⟨IsSepClosure.sep_closed F, Algebra.isSeparable_tower_top_of_isSeparable F K S⟩
  let C := extendedHopf K B
  let p := torusPointEquiv (K := K) (S := S) B
  let : TopologicalSpace (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X) := ⊥
  let : DiscreteTopology (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X) := ⟨rfl⟩
  let : TopologicalSpace (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points K S (specGroup C).X) := ⊥
  let c : Cocycle (pointAction K S (specGroup C).X) :=
    ⟨fun σ => p (a.val (σ.restrictScalars F)),
      continuous_of_discreteTopology.comp
        (a.property.1.comp (continuousRestrictionOfScalars (K := K))),
      fun σ τ => by
        change p (a.val ((AlgEquiv.restrictScalarsHom F) (σ * τ))) = _
        rw [map_mul, a.property.2, map_mul]
        exact congrArg (p (a.val (σ.restrictScalars F)) * ·) (torusPointEquiv_action B σ _)⟩
  have hc := MaximalUnramifiedTorusTorsors.torus_vanishing F S C
    (torusOverIntermediateField (K := K) (S := S) B hB) (classOf c)
  obtain ⟨b, hb⟩ := classOf_eq_iff.mp hc
  refine ⟨p.symm b, fun σ => p.injective ?_⟩
  change p 1 = p ((p.symm b)⁻¹ * a.val (σ.restrictScalars F) *
    pointAction F S (specGroup B).X (σ.restrictScalars F) (p.symm b))
  rw [map_one, map_mul, map_mul, map_inv]
  have he := torusPointEquiv_action B σ (p.symm b)
  change p (pointAction F S (specGroup B).X (σ.restrictScalars F) (p.symm b)) =
    pointAction K S (specGroup C).X σ (p (p.symm b)) at he
  rw [he, MulEquiv.apply_symm_apply]
  exact hb σ

set_option maxHeartbeats 500000 in
private theorem torusCocycleTrivialOnInertia (B : HopfAlgebraCategory F)
    (hB : Specs.CharacterDescent.IsTorus B)
    (a : @Cocycle (Gal(S/F)) (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X)
      _ (krullTopology F S) _ ⊥ (pointAction F S (specGroup B).X)) :
    ∃ b : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X,
      ∀ σ ∈ (unramifiedSubfield F S).fixingSubgroup,
        (1 : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X) =
          b⁻¹ * (a.val σ : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X) *
            pointAction F S (specGroup B).X σ b := by
  let K := maximalUnramified F
  let f : K →ₐ[F] S := (closureEquiv F S).toAlgHom.comp (maximalUnramified F).val
  let : Algebra K S := f.toRingHom.toAlgebra
  let : IsScalarTower F K S := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  obtain ⟨b, hb⟩ := restrictTorusCocycleIsNeutral (S := S) B hB a
  refine ⟨b, fun σ hσ => ?_⟩
  let τ : Gal(S/K) :=
    { σ.toRingEquiv with
      commutes' := fun x => hσ ⟨f x, ⟨x, x.property, rfl⟩⟩ }
  have hτ : τ.restrictScalars F = σ := by ext x; rfl
  simpa only [hτ] using hb τ

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem continuousCoefficientAction (G : AffineAlgebraicGroup F) :
    letI : TopologicalSpace (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S G.val.X) := ⊥
    Continuous (fun q : Gal(S/F) × _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S G.val.X =>
      pointAction F S G.val.X q.1 q.2) := by
  let : TopologicalSpace (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S G.val.X) := ⊥
  let : DiscreteTopology (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S G.val.X) := ⟨rfl⟩
  let : LocallyOfFiniteType G.val.X.hom := G.property.2.1
  apply (continuousAction_iff_finiteLevel (ρ := pointAction F S G.val.X)).mpr
  intro m
  obtain ⟨L, hL⟩ := point_defined_at_finite_level m
  exact ⟨L, (finitePoints_iff_fixed L m).mp hL⟩

set_option maxHeartbeats 600000 in
private theorem adjointCocycleTrivialOnInertia
    {A : AdditiveLine F} {P : PinnedGroup A} {D : AttachedDatum P.pair}
    {l : Aut D.toBased ≃* Aut P} {Q : AdjointQuotient P.pair.G}
    {E : SplitSequence P D l Q}
    {ω : Cocycle (trivialOuterAction (k := F) (S := S) D.toBased)}
    (V : PinnedRepresentative (S := S) E ω) (hV : IsExceptionalReference D)
    (Q₀ : AdjointQuotient V.model.val)
    (a : @Cocycle (Gal(S/F)) (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S Q₀.quotient.val.X)
      _ (krullTopology F S) _ ⊥ (pointAction F S Q₀.quotient.val.X)) :
    ∃ b : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S Q₀.quotient.val.X,
      ∀ σ ∈ (unramifiedSubfield F S).fixingSubgroup,
        (1 : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S Q₀.quotient.val.X) =
          b⁻¹ * (a.val σ : _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S Q₀.quotient.val.X) *
            pointAction F S Q₀.quotient.val.X σ b := by
  let G := V.model.val
  let M := _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S Q₀.quotient.val.X
  let : Infinite F := by
    obtain ⟨v, hv, hv'⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := F)
    obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective v
    exact Infinite.of_injective (fun n : ℕ => x ^ n) (fun n m hnm =>
      (pow_right_strictAnti₀ hv hv').injective (by
        simpa only [map_pow, hx] using congrArg (ValuativeRel.valuation F) hnm))
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  obtain ⟨H⟩ := ExceptionalTwistedTraceComparison.adjointTwisting G V.reductive Q₀ a
  obtain ⟨x, y, b, C, hC, hCx, hb⟩ := matching_twisted_point V hV H
  obtain ⟨U, hU, _, p, _, hp, hσ, hpfix⟩ :=
    StronglyRegularSeparableTransporter.adjointTorusStabilizer
      (S := S) G V.reductive x C hC hCx Q₀ H.inner H.onLift
  obtain ⟨B, hB, q, hq, hqσ, hrange⟩ := torus_embedding Q₀.quotient U hU p hp hσ
  let r := pointAction F S Q₀.quotient.val.X
  let s := pointAction F S (specGroup B).X
  let b₀ : M := projectionOnPoints Q₀ b
  let : TopologicalSpace (_root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S (specGroup B).X) := ⊥
  have hm (σ : Gal(S/F)) : b₀⁻¹ * (a.val σ : M) * r σ b₀ ∈ q.range := by
    rw [hrange, hpfix]
    exact adjoint_cocycle_fixes H x y b hb σ
  obtain ⟨c, hc⟩ := cocycle_into_subgroup (ρ := r) (σ := s)
    (continuousCoefficientAction Q₀.quotient) q hq hqσ a b₀ hm
  obtain ⟨d, hd⟩ := torusCocycleTrivialOnInertia B hB c
  refine ⟨b₀ * q d, fun σ hσ => ?_⟩
  have h := congrArg q (hd σ hσ)
  change q 1 = q (d⁻¹ * c σ * s σ d) at h
  rw [map_one, map_mul, map_mul, map_inv, hqσ, hc] at h
  simpa only [mul_inv_rev, map_mul, mul_assoc] using h

private def correctedCocycle {Γ M : Type u} [Group Γ] [TopologicalSpace Γ]
    [Group M] [TopologicalSpace M] [DiscreteTopology M] {ρ : Γ →* MulAut M}
    (hρ : Continuous (fun q : Γ × M => ρ q.1 q.2))
    (a : Cocycle ρ) (b : M) : Cocycle ρ :=
  ⟨fun σ => b⁻¹ * a σ * ρ σ b,
    (continuous_const.mul a.property.1).mul
      (hρ.comp (continuous_id.prodMk continuous_const)),
    fun σ τ => by
      change b⁻¹ * a (σ * τ) * ρ (σ * τ) b =
        (b⁻¹ * a σ * ρ σ b) * ρ σ (b⁻¹ * a τ * ρ τ b)
      rw [a.property.2, map_mul ρ, MulAut.mul_apply, map_mul, map_mul, map_inv]
      group⟩

set_option maxHeartbeats 600000 in
private theorem finiteUnramifiedInflationProof : FiniteUnramifiedInflation.{u} := by
  intro F S _ _ _ _ _ _ _ A P D l Q E ω V hsem hsc hE Q₀ a
  let G := Q₀.quotient.val
  let M := _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology.Points F S G.X
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  let r := pointAction F S G.X
  obtain ⟨b, hb⟩ := adjointCocycleTrivialOnInertia V ⟨hsem, hsc, Or.inl hE⟩ Q₀ a
  let d : Cocycle r := correctedCocycle (continuousCoefficientAction Q₀.quotient) a b
  obtain ⟨K, v, T, hlocal, hext, hunr, c, hlaw, hpoint⟩ :=
    pointCocycleDescendsAtUnramifiedLevel G d (fun σ hσ => (hb σ hσ).symm)
  exact ⟨K, v, T, hlocal, hext, hunr, b, c, hlaw, hpoint⟩

end Inertia

section Conditional

universe u

open Specs.RamifiedExceptionalUnramifiedCocycle

/-- Finite unramified inflation for the adjoint cocycle of the pinned reference. -/
theorem finiteUnramifiedInflation_conditional
    (_coxeterDoubleCosets : Specs.ExceptionalAffineBruhat.CoxeterDoubleCosets.{u, u, u})
    (_e6CoweightQuotient : Specs.ExceptionalAffineBruhat.E6CoweightClass)
    (_e6ProjectedLattices : Specs.ExceptionalAffineBruhat.E6ProjectedLattices)
    (_leftCosetIndex : Specs.ExceptionalAffineBruhat.LeftCosetIndex.{u})
    (_ramifiedAffineBruhatComparison : Specs.ExceptionalAffineBruhat.RamifiedAffineBruhatComparison.{u})
    (_rankOneDoubleCosetProduct : Specs.ExceptionalAffineBruhat.RankOneDoubleCosetProduct.{u})
    (_rankOneWallConjugation : Specs.ExceptionalAffineBruhat.RankOneWallConjugation.{u})
    (_rankOneWallMultiplication : Specs.ExceptionalAffineBruhat.RankOneWallMultiplication.{u})
    (_residueLayerCounts : Specs.ExceptionalAffineBruhat.ResidueLayerCounts.{u})
    (_residuePowerCounts : Specs.ExceptionalAffineBruhat.ResiduePowerCounts.{u})
    (_splitAffineBruhatComparison : Specs.ExceptionalAffineBruhat.SplitAffineBruhatComparison.{u})
    : FiniteUnramifiedInflation.{u} :=
  finiteUnramifiedInflationProof

theorem residueGaloisComparison_conditional
    (_coxeterDoubleCosets : Specs.ExceptionalAffineBruhat.CoxeterDoubleCosets.{u, u, u})
    (_e6CoweightQuotient : Specs.ExceptionalAffineBruhat.E6CoweightClass)
    (_e6ProjectedLattices : Specs.ExceptionalAffineBruhat.E6ProjectedLattices)
    (_leftCosetIndex : Specs.ExceptionalAffineBruhat.LeftCosetIndex.{u})
    (_ramifiedAffineBruhatComparison : Specs.ExceptionalAffineBruhat.RamifiedAffineBruhatComparison.{u})
    (_rankOneDoubleCosetProduct : Specs.ExceptionalAffineBruhat.RankOneDoubleCosetProduct.{u})
    (_rankOneWallConjugation : Specs.ExceptionalAffineBruhat.RankOneWallConjugation.{u})
    (_rankOneWallMultiplication : Specs.ExceptionalAffineBruhat.RankOneWallMultiplication.{u})
    (_residueLayerCounts : Specs.ExceptionalAffineBruhat.ResidueLayerCounts.{u})
    (_residuePowerCounts : Specs.ExceptionalAffineBruhat.ResiduePowerCounts.{u})
    (_splitAffineBruhatComparison : Specs.ExceptionalAffineBruhat.SplitAffineBruhatComparison.{u})
    : ResidueGaloisComparison.{u} :=
  residueGaloisComparisonProof

theorem residueGaloisRestriction_conditional
    (_coxeterDoubleCosets : Specs.ExceptionalAffineBruhat.CoxeterDoubleCosets.{u, u, u})
    (_e6CoweightQuotient : Specs.ExceptionalAffineBruhat.E6CoweightClass)
    (_e6ProjectedLattices : Specs.ExceptionalAffineBruhat.E6ProjectedLattices)
    (_leftCosetIndex : Specs.ExceptionalAffineBruhat.LeftCosetIndex.{u})
    (_ramifiedAffineBruhatComparison : Specs.ExceptionalAffineBruhat.RamifiedAffineBruhatComparison.{u})
    (_rankOneDoubleCosetProduct : Specs.ExceptionalAffineBruhat.RankOneDoubleCosetProduct.{u})
    (_rankOneWallConjugation : Specs.ExceptionalAffineBruhat.RankOneWallConjugation.{u})
    (_rankOneWallMultiplication : Specs.ExceptionalAffineBruhat.RankOneWallMultiplication.{u})
    (_residueLayerCounts : Specs.ExceptionalAffineBruhat.ResidueLayerCounts.{u})
    (_residuePowerCounts : Specs.ExceptionalAffineBruhat.ResiduePowerCounts.{u})
    (_splitAffineBruhatComparison : Specs.ExceptionalAffineBruhat.SplitAffineBruhatComparison.{u})
    : ResidueGaloisRestriction.{u} :=
  residueGaloisRestrictionProof

theorem unramifiedResidueEnlargement_conditional
    (_coxeterDoubleCosets : Specs.ExceptionalAffineBruhat.CoxeterDoubleCosets.{u, u, u})
    (_e6CoweightQuotient : Specs.ExceptionalAffineBruhat.E6CoweightClass)
    (_e6ProjectedLattices : Specs.ExceptionalAffineBruhat.E6ProjectedLattices)
    (_leftCosetIndex : Specs.ExceptionalAffineBruhat.LeftCosetIndex.{u})
    (_ramifiedAffineBruhatComparison : Specs.ExceptionalAffineBruhat.RamifiedAffineBruhatComparison.{u})
    (_rankOneDoubleCosetProduct : Specs.ExceptionalAffineBruhat.RankOneDoubleCosetProduct.{u})
    (_rankOneWallConjugation : Specs.ExceptionalAffineBruhat.RankOneWallConjugation.{u})
    (_rankOneWallMultiplication : Specs.ExceptionalAffineBruhat.RankOneWallMultiplication.{u})
    (_residueLayerCounts : Specs.ExceptionalAffineBruhat.ResidueLayerCounts.{u})
    (_residuePowerCounts : Specs.ExceptionalAffineBruhat.ResiduePowerCounts.{u})
    (_splitAffineBruhatComparison : Specs.ExceptionalAffineBruhat.SplitAffineBruhatComparison.{u})
    : UnramifiedResidueEnlargement.{u} :=
  unramifiedResidueEnlargementProof

end Conditional

end LinearAlgebraicGroups.Arithmetic.RamifiedExceptionalUnramifiedCocycle

universe v8_closure_cd77e5cca95a6c77_u0
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedExceptionalUnramifiedCocycle».«finiteUnramifiedInflation» : _root_.«LinearAlgebraicGroups».«Specs».«RamifiedExceptionalUnramifiedCocycle».«FiniteUnramifiedInflation».{v8_closure_cd77e5cca95a6c77_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedExceptionalUnramifiedCocycle».«finiteUnramifiedInflation_conditional».{v8_closure_cd77e5cca95a6c77_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_cd77e5cca95a6c77_u0, v8_closure_cd77e5cca95a6c77_u0, v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_cd77e5cca95a6c77_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedExceptionalUnramifiedCocycle».«residueGaloisComparison» : _root_.«LinearAlgebraicGroups».«Specs».«RamifiedExceptionalUnramifiedCocycle».«ResidueGaloisComparison».{v8_closure_cd77e5cca95a6c77_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedExceptionalUnramifiedCocycle».«residueGaloisComparison_conditional».{v8_closure_cd77e5cca95a6c77_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_cd77e5cca95a6c77_u0, v8_closure_cd77e5cca95a6c77_u0, v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_cd77e5cca95a6c77_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedExceptionalUnramifiedCocycle».«residueGaloisRestriction» : _root_.«LinearAlgebraicGroups».«Specs».«RamifiedExceptionalUnramifiedCocycle».«ResidueGaloisRestriction».{v8_closure_cd77e5cca95a6c77_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedExceptionalUnramifiedCocycle».«residueGaloisRestriction_conditional».{v8_closure_cd77e5cca95a6c77_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_cd77e5cca95a6c77_u0, v8_closure_cd77e5cca95a6c77_u0, v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_cd77e5cca95a6c77_u0})
theorem _root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedExceptionalUnramifiedCocycle».«unramifiedResidueEnlargement» : _root_.«LinearAlgebraicGroups».«Specs».«RamifiedExceptionalUnramifiedCocycle».«UnramifiedResidueEnlargement».{v8_closure_cd77e5cca95a6c77_u0} :=
  @_root_.«LinearAlgebraicGroups».«Arithmetic».«RamifiedExceptionalUnramifiedCocycle».«unramifiedResidueEnlargement_conditional».{v8_closure_cd77e5cca95a6c77_u0} (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«coxeterDoubleCosets».{v8_closure_cd77e5cca95a6c77_u0, v8_closure_cd77e5cca95a6c77_u0, v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6CoweightQuotient») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«e6ProjectedLattices») (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«leftCosetIndex».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«ramifiedAffineBruhatComparison».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneDoubleCosetProduct».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallConjugation».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«rankOneWallMultiplication».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residueLayerCounts».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«residuePowerCounts».{v8_closure_cd77e5cca95a6c77_u0}) (@_root_.«LinearAlgebraicGroups».«Arithmetic».«ExceptionalAffineBruhat».«splitAffineBruhatComparison».{v8_closure_cd77e5cca95a6c77_u0})
