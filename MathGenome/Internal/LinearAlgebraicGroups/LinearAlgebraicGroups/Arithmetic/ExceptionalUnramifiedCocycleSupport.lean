import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalUnramifiedCocycleSupport
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.ExceptionalFormsOverUnramifiedFields
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeFormComparison
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.IntegralRealization
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
import Batteries.Tactic.OpenPrivate

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalUnramifiedCocycleSupport

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.SemiCartesianMonoidalCategory Opposite
open scoped CategoryTheory.MonObj Polynomial Topology IntermediateField
open _root_.LinearAlgebraicGroups.Specs (GroupScheme)
open Specs.ExceptionalUnramifiedCocycleSupport
open Descent.NonabelianCohomology
open MaximalUnramifiedBrauer (IsUnramified maximalUnramified)
open private cyclotomicStage cyclotomicStage_data le_cyclotomicStage_of_unramified
  cyclotomicStage_le_of_dvd from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer
open private descend_of_trivial_on_kernel from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.NonabelianCohomology

noncomputable section

local notation "CohPoints" => Descent.NonabelianCohomology.Points

section UnramifiedDescent

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "Fsep" => SeparableClosure F
local notation "κ" => IsLocalRing.ResidueField (Valuation.integer (ValuativeRel.valuation F))

private theorem finite_subfield_in_cyclotomic_stage (J : IntermediateField F Fsep)
    [FiniteDimensional F J] (hJ : J ≤ maximalUnramified F) :
    ∃ n : ℕ, (n : κ) ≠ 0 ∧ J ≤ cyclotomicStage F n := by
  classical
  have stage_for_finite_set (s : Finset Fsep) (hs : ∀ x ∈ s, x ∈ maximalUnramified F) :
      ∃ n : ℕ, (n : κ) ≠ 0 ∧ ∀ x ∈ s, x ∈ cyclotomicStage F n := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp, by simp⟩
    | @insert x s hx ih =>
      obtain ⟨E, hE, hxE⟩ := MaximalUnramifiedBrauer.mem_maximalUnramified_iff.mp
        (hs x (Finset.mem_insert_self _ _))
      obtain ⟨m, hm, hEm⟩ := le_cyclotomicStage_of_unramified hE
      obtain ⟨n, hn, hsn⟩ := ih (fun z hz => hs z (Finset.mem_insert_of_mem hz))
      have hm' : m ≠ 0 := fun h => hm (by simp [h])
      have hn' : n ≠ 0 := fun h => hn (by simp [h])
      refine ⟨m * n, by simpa using mul_ne_zero hm hn, fun z hz => ?_⟩
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact cyclotomicStage_le_of_dvd hm' (mul_ne_zero hm' hn') (dvd_mul_right m n) (hEm hxE)
      · exact cyclotomicStage_le_of_dvd hn' (mul_ne_zero hm' hn') (dvd_mul_left n m) (hsn z hz)
  let b := Module.finBasis F J
  obtain ⟨n, hn, hbn⟩ := stage_for_finite_set (Finset.univ.image (fun i => (b i : Fsep)))
    (by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact hJ (b i).property)
  refine ⟨n, hn, fun x hx => ?_⟩
  have hb (i : Fin (Module.finrank F J)) : (b i : Fsep) ∈ cyclotomicStage F n :=
    hbn _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  let p : J →ₗ[F] Fsep := J.val.toLinearMap
  have hspan : Submodule.span F (Set.range b) ≤
      (cyclotomicStage F n).toSubmodule.comap p := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hb i
  rw [b.span_eq] at hspan
  exact hspan (show (⟨x, hx⟩ : J) ∈ (⊤ : Submodule F J) from trivial)

/-- A continuous point cocycle trivial on the subgroup fixing the maximal
unramified field is inflated from an unramified stage containing the given level. -/
theorem descend_unramified_point_cocycle {H : GroupScheme F}
    (L₀ : FiniteGaloisIntermediateField F Fsep) (hL₀ : IsUnramified F L₀)
    (a : Specs.ExceptionalTwistedTraceComparison.PointCocycle (S := Fsep) H)
    (ha : ∀ σ ∈ (maximalUnramified F).fixingSubgroup, a.val σ = 1) :
    ∃ (L : FiniteGaloisIntermediateField F Fsep) (c : Gal(L/F) → CohPoints F L H.X),
      L₀ ≤ L ∧ IsUnramified F L ∧
      (∀ σ τ, c (σ * τ) = c σ * pointAction F L H.X σ (c τ)) ∧
      ∀ σ, pointMap F L H.X L.toIntermediateField.val (c (restriction L σ)) = a.val σ := by
  classical
  let r := pointAction F Fsep H.X
  let : TopologicalSpace (CohPoints F Fsep H.X) := ⊥
  have : DiscreteTopology (CohPoints F Fsep H.X) := ⟨rfl⟩
  change Cocycle r at a
  let N : Subgroup Gal(Fsep/F) :=
    { carrier := {σ | a σ = 1}
      one_mem' := a.map_one
      mul_mem' := by
        intro σ τ hσ hτ
        change a σ = 1 at hσ
        change a τ = 1 at hτ
        simp [a.property.2, hσ, hτ]
      inv_mem' := by
        intro σ hσ
        change a σ = 1 at hσ
        change a σ⁻¹ = 1
        simpa [hσ] using (a.property.2 σ⁻¹ σ).symm }
  have hopen : IsOpen (N : Set Gal(Fsep/F)) :=
    (isOpen_discrete ({1} : Set (CohPoints F Fsep H.X))).preimage a.property.1
  have hclosed : IsClosed (N : Set Gal(Fsep/F)) :=
    (isClosed_discrete ({1} : Set (CohPoints F Fsep H.X))).preimage a.property.1
  let J := IntermediateField.fixedField N
  have hJN : J.fixingSubgroup = N :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨N, hclosed⟩ : _root_.ClosedSubgroup Gal(Fsep/F))
  let : FiniteDimensional F J :=
    (InfiniteGalois.isOpen_iff_finite J).mp (by
      rw [hJN]
      exact hopen)
  have hJ : J ≤ maximalUnramified F := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup (maximalUnramified F)]
    exact IntermediateField.fixedField_le ha
  obtain ⟨n, hn, hJn⟩ := finite_subfield_in_cyclotomic_stage J hJ
  obtain ⟨m, hm, hL₀m⟩ :=
    le_cyclotomicStage_of_unramified (E := L₀.toIntermediateField) hL₀
  have hn' : n ≠ 0 := fun h => hn (by simp [h])
  have hm' : m ≠ 0 := fun h => hm (by simp [h])
  have hnm : ((n * m : ℕ) : κ) ≠ 0 := by simpa using mul_ne_zero hn hm
  have hL := (cyclotomicStage_data (F := F) hnm).1
  let Lf := cyclotomicStage F (n * m)
  let : FiniteDimensional F Lf := hL.1
  have hnormal : IsGalois F Lf := by
    let p : F[X] := Polynomial.X ^ (n * m) - Polynomial.C 1
    have hnF : ((n * m : ℕ) : F) ≠ 0 := by
      intro h
      apply hnm
      have hz : ((n * m : ℕ) : Valuation.integer (ValuativeRel.valuation F)) = 0 :=
        Subtype.ext (by simpa using h)
      simpa using congrArg (IsLocalRing.residue (Valuation.integer (ValuativeRel.valuation F))) hz
    have hsep : p.Separable := Polynomial.separable_X_pow_sub_C 1 hnF one_ne_zero
    let : p.IsSplittingField F Lf :=
      IntermediateField.adjoin_rootSet_isSplittingField (IsSepClosed.splits_codomain p hsep)
    exact IsGalois.of_separable_splitting_field hsep
  let L : FiniteGaloisIntermediateField F Fsep :=
    { toIntermediateField := Lf, finiteDimensional := hL.1, isGalois := hnormal }
  have hJL : J ≤ L.toIntermediateField :=
    hJn.trans (cyclotomicStage_le_of_dvd hn' (mul_ne_zero hn' hm') (dvd_mul_right n m))
  have hL₀L : L₀ ≤ L := (FiniteGaloisIntermediateField.le_iff _ _).mpr
    (hL₀m.trans (cyclotomicStage_le_of_dvd hm' (mul_ne_zero hn' hm') (dvd_mul_left m n)))
  have hk (σ : Gal(Fsep/F)) (hσ : σ ∈ (restriction L).ker) : a σ = 1 := by
    change σ ∈ N
    rw [← hJN]
    exact IntermediateField.fixingSubgroup_le hJL
      (L.toIntermediateField.restrictNormalHom_ker ▸ hσ)
  let : TopologicalSpace Gal(L/F) := ⊥
  have : DiscreteTopology Gal(L/F) := ⟨rfl⟩
  obtain ⟨c, hc⟩ := descend_of_trivial_on_kernel
    (AlgEquiv.restrictNormalHom_surjective Fsep : Function.Surjective (restriction L)) a hk
  obtain ⟨e, he, hequiv⟩ := finitePointsIdentification (H := H.X) L
  refine ⟨L, fun σ => e.symm (c σ), hL₀L, hL, ?_, ?_⟩
  · intro σ τ
    apply e.injective
    simp only [map_mul, hequiv, MulEquiv.apply_symm_apply]
    exact c.property.2 σ τ
  · intro σ
    rw [← he, MulEquiv.apply_symm_apply]
    exact hc σ

end UnramifiedDescent


theorem descentFromFixingSubgroup : DescentFromFixingSubgroup.{u} := by
  intro F _ _ _ _ G L₀ hL₀ a ha
  exact descend_unramified_point_cocycle L₀ hL₀ a ha

section Residue

open ValuativeRel IsLocalRing
open private valuation_hasExtension restrictToIntegers unramified_adjoin_roots
  residue_natCast_ne_zero_iff root_of_unity_mem_integer root_of_unity_eq_of_residue_eq
  valuation_isIntegralClosure map_maximalIdeal_of_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer

local notation "O" K => Valuation.integer (valuation K)
local notation "κ" K => ResidueField (O K)

variable {F L : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [Field L] [Algebra F L]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L]

private theorem residue_degree [(valuation F).HasExtension (valuation L)]
    (h : Function.Surjective (fun x : F => valuation L (algebraMap F L x))) :
    Module.finrank (κ F) (κ L) = Module.finrank F L := by
  let : IsIntegralClosure (O L) (O F) L := valuation_isIntegralClosure
  let : Module.Finite (O F) (O L) := IsIntegralClosure.finite (O F) F L (O L)
  let : Module.Free (O F) (O L) := IsIntegralClosure.module_free (O F) F L (O L)
  have hmap := map_maximalIdeal_of_surjective h
  have hr := (IsLocalRing.finrank_quotient_map (R := O F) (S := O L)).trans
    (IsIntegralClosure.rank (O F) F L (O L))
  let I := (maximalIdeal (O F)).map (algebraMap (O F) (O L))
  let J := maximalIdeal (O L)
  let R := (O F) ⧸ maximalIdeal (O F)
  let f : ((O L) ⧸ I) →ₐ[R] ((O L) ⧸ J) :=
    { Ideal.Quotient.factor hmap.le with
      commutes' := fun a => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        rfl }
  have hf : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 ?_, Ideal.Quotient.factor_surjective hmap.le⟩
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk J a = 0 at hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    change a ∈ (maximalIdeal (O F)).map (algebraMap (O F) (O L))
    rw [hmap]
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  exact ((AlgEquiv.ofBijective f hf).toLinearEquiv.finrank_eq).symm.trans hr

private def reduceAutomorphism [(valuation F).HasExtension (valuation L)] :
    Gal(L/F) →* ((κ L) ≃ₐ[κ F] (κ L)) where
  toFun σ := ResidueField.mapAlgEquiv' (restrictToIntegers σ)
  map_one' := by
    ext z
    obtain ⟨x, rfl⟩ := residue_surjective z
    rfl
  map_mul' σ τ := by
    ext z
    obtain ⟨x, rfl⟩ := residue_surjective z
    rfl

private theorem reduceAutomorphism_injective [(valuation F).HasExtension (valuation L)]
    (h : Function.Surjective (fun x : F => valuation L (algebraMap F L x))) :
    Function.Injective (reduceAutomorphism (F := F) (L := L)) := by
  obtain ⟨n, hn, hgen⟩ := unramified_adjoin_roots h
  have hn0 : n ≠ 0 := fun e => hn (by simp [e])
  intro σ τ heq
  have htop : Algebra.adjoin F {x : L | x ^ n = 1} = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic (R := F) x), hgen]
    rfl
  have he : σ.toAlgHom = τ.toAlgHom := AlgHom.ext_of_adjoin_eq_top htop <| by
    intro x hx
    change x ^ n = 1 at hx
    let a : O L := ⟨x, root_of_unity_mem_integer hn0 hx⟩
    have hred := DFunLike.congr_fun heq (residue (O L) a)
    have hxσ : (σ x) ^ n = 1 := by rw [← map_pow, hx, map_one]
    have hxτ : (τ x) ^ n = 1 := by rw [← map_pow, hx, map_one]
    exact congrArg Subtype.val <| root_of_unity_eq_of_residue_eq
      ((residue_natCast_ne_zero_iff (L := L) n).mp hn) hxσ hxτ hred
  ext x
  exact DFunLike.congr_fun he x

theorem arithmeticFrobenius : ArithmeticFrobenius.{u} := by
  classical
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ h
  let : (valuation F).HasExtension (valuation L) := valuation_hasExtension
  let : Fintype (κ F) := Fintype.ofFinite _
  let : Fintype (κ L) := Fintype.ofFinite _
  let r := reduceAutomorphism (F := F) (L := L)
  have hinj := reduceAutomorphism_injective h
  have hd := residue_degree h
  have hcard : Nat.card Gal(L/F) = Nat.card ((κ L) ≃ₐ[κ F] (κ L)) := by
    rw [IsGalois.card_aut_eq_finrank F L, IsGalois.card_aut_eq_finrank (κ F) (κ L), hd]
  have hsurj : Function.Surjective r := by
    let : Fintype Gal(L/F) := Fintype.ofFinite _
    let : Fintype ((κ L) ≃ₐ[κ F] (κ L)) := Fintype.ofFinite _
    apply (Finite.injective_iff_surjective_of_equiv (f := r) (Fintype.equivOfCardEq _)).mp hinj
    simpa only [Nat.card_eq_fintype_card] using hcard
  let e := MulEquiv.ofBijective r ⟨hinj, hsurj⟩
  let fr := FiniteField.frobeniusAlgEquivOfAlgebraic (κ F) (κ L)
  let σ := e.symm fr
  have he : e σ = fr := e.apply_symm_apply fr
  have hres (x : O L) :
      residue (O L) (restrictToIntegers σ x) =
        residue (O L) x ^ Nat.card (κ F) := by
    have hx := DFunLike.congr_fun he (residue (O L) x)
    change residue (O L) (restrictToIntegers σ x) =
      residue (O L) x ^ Fintype.card (κ F) at hx
    simpa only [Nat.card_eq_fintype_card] using hx
  refine ⟨σ, fun x => ⟨restrictToIntegers σ x, rfl, hres x⟩, ?_, ?_, ?_⟩
  · intro τ hτ
    apply e.injective
    ext x
    obtain ⟨a, rfl⟩ := residue_surjective x
    obtain ⟨y, hy, hyr⟩ := hτ a
    have : y = restrictToIntegers τ a := Subtype.ext hy
    exact (this ▸ hyr).trans (hres a).symm
  · rw [← e.orderOf_eq, he, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hd]
  · have hh := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (κ F) (κ L)).comp
        (finCongr hd.symm).bijective
    apply (e.bijective.of_comp_iff' _).mp
    convert hh using 1
    funext i
    change e (σ ^ i.val) = fr ^ i.val
    rw [map_pow, he]

end Residue

section Enlargement

open Polynomial ValuativeRel IsLocalRing
open private roots_X_pow_sub_one valuation_hasExtension residue_natCast_ne_zero_iff
  root_of_unity_mem_integer root_of_unity_eq_of_residue_eq
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Arithmetic.MaximalUnramifiedBrauer

local notation "O" K => Valuation.integer (valuation K)
local notation "κ" K => ResidueField (O K)

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

private theorem cyclotomic_separable {m : ℕ} (hm : (m : κ F) ≠ 0) :
    (X ^ m - C (1 : F)).Separable := by
  apply separable_X_pow_sub_C 1 _ one_ne_zero
  intro h
  apply hm
  have hO : (m : O F) = 0 := Subtype.ext (by simpa using h)
  simpa only [map_natCast, map_zero] using congrArg (residue (O F)) hO

private theorem cyclotomic_isGalois {m : ℕ} (hm : (m : κ F) ≠ 0) :
    IsGalois F (cyclotomicStage F m) := by
  have hsep := cyclotomic_separable hm
  let : (X ^ m - C (1 : F)).IsSplittingField F (cyclotomicStage F m) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsSepClosed.splits_codomain _ hsep)
  exact IsGalois.of_separable_splitting_field hsep

private theorem exponent_dvd_of_pow_sub_one_dvd {q d f : ℕ}
    (hq : 1 < q) (hd : 0 < d) (h : q ^ d - 1 ∣ q ^ f - 1) : d ∣ f := by
  let m := q ^ d - 1
  have hpow : 1 ≤ q ^ d := Nat.one_le_pow _ _ (by omega)
  have hqf : 1 ≤ q ^ f := Nat.one_le_pow _ _ (by omega)
  have hbase : q ^ d ≡ 1 [MOD m] := by
    simpa only [m, Nat.sub_add_cancel hpow, Nat.zero_add] using
      (Nat.modEq_zero_iff_dvd.mpr (dvd_refl m)).add_right 1
  have hf : q ^ f ≡ 1 [MOD m] := by
    simpa only [m, Nat.sub_add_cancel hqf, Nat.zero_add] using
      (Nat.modEq_zero_iff_dvd.mpr h).add_right 1
  have hrem : q ^ (f % d) ≡ 1 [MOD m] := by
    conv at hf => lhs; rw [← Nat.mod_add_div f d, pow_add, pow_mul]
    simpa only [one_pow, mul_one] using
      ((Nat.ModEq.refl (q ^ (f % d))).mul (hbase.pow (f / d))).symm.trans hf
  have hlt : q ^ (f % d) < q ^ d := Nat.pow_lt_pow_right hq (Nat.mod_lt f hd)
  have hpos : 0 < q ^ (f % d) := pow_pos (by omega) _
  have hdiv : m ∣ q ^ (f % d) - 1 := by
    apply Nat.modEq_zero_iff_dvd.mp
    simpa only [Nat.sub_self] using Nat.ModEq.sub (by omega) (Nat.le_refl 1) hrem (Nat.ModEq.refl 1)
  have hz := Nat.eq_zero_of_dvd_of_lt hdiv (show q ^ (f % d) - 1 < m by
    dsimp [m]
    omega)
  apply Nat.dvd_of_mod_eq_zero
  apply Nat.pow_right_injective hq
  simpa using (show q ^ (f % d) = 1 by omega)

private theorem roots_divide_residue_units
    {L : Type u} [Field L] [Algebra F L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [ValuativeExtension F L]
    {m : ℕ} (hm : (m : κ F) ≠ 0)
    (hs : ((X ^ m - C (1 : F)).map (algebraMap F L)).Splits) :
    m ∣ Nat.card (κ L) - 1 := by
  classical
  have hm0 : m ≠ 0 := fun e => hm (by simp [e])
  let : NeZero m := ⟨hm0⟩
  have hmc : (m : κ L) ≠ 0 := (residue_natCast_ne_zero_iff (L := L) m).mp hm
  let p : F[X] := X ^ m - C 1
  have hcount : Nat.card (p.rootSet L) = m := by
    rw [Nat.card_eq_fintype_card, card_rootSet_eq_natDegree (cyclotomic_separable hm) hs]
    exact natDegree_X_pow_sub_C
  let e : rootsOfUnity m L ≃ p.rootSet L :=
    (rootsOfUnityEquivNthRoots L m).trans (Equiv.subtypeEquivRight fun x => by
      rw [mem_nthRoots (Nat.pos_of_ne_zero hm0), show p.rootSet L = {x : L | x ^ m = 1}
        from roots_X_pow_sub_one hm0]
      rfl)
  have hroots : Nat.card (rootsOfUnity m L) = m := (Nat.card_congr e).trans hcount
  obtain ⟨ζ, hζ⟩ := card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp hroots
  let z : O L := ⟨ζ, root_of_unity_mem_integer hm0 hζ.pow_eq_one⟩
  have hz : z ^ m = 1 := Subtype.ext hζ.pow_eq_one
  let w := residue (O L) z
  have hw : w ^ m = 1 := by rw [← map_pow, hz, map_one]
  have hprim : IsPrimitiveRoot w m := ⟨hw, fun j hj => by
    apply hζ.dvd_of_pow_eq_one j
    have hpow : ((z ^ j : O L) : L) ^ m = 1 := by
      change (ζ ^ j) ^ m = 1
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hred : residue (O L) (z ^ j) = residue (O L) 1 := by
      simpa only [map_pow, map_one] using hj
    have he := root_of_unity_eq_of_residue_eq hmc hpow (one_pow m) hred
    exact congrArg Subtype.val he⟩
  let : Fintype (κ L) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact hprim.dvd_of_pow_eq_one _
    (FiniteField.pow_card_sub_one_eq_one w (fun h => by simp [h, hm0] at hw))

private theorem split_order_dvd {L : Type u} [Field L] [Algebra F L]
    {m : ℕ} (hm : (m : κ F) ≠ 0) (hu : IsUnramified F L) (hg : IsGalois F L)
    (hs : ((X ^ m - C (1 : F)).map (algebraMap F L)).Splits) :
    m ∣ Nat.card (κ F) ^ Module.finrank F L - 1 := by
  obtain ⟨hfinite, _, r, T, hloc, hext, hsurj⟩ := hu
  let : FiniteDimensional F L := hfinite
  let : IsGalois F L := hg
  let : ValuativeRel L := r
  let : TopologicalSpace L := T
  let : IsNonarchimedeanLocalField L := hloc
  let : ValuativeExtension F L := hext
  let : (valuation F).HasExtension (valuation L) := valuation_hasExtension
  have hdiv := roots_divide_residue_units (L := L) hm hs
  rwa [Module.natCard_eq_pow_finrank (K := κ F), residue_degree (F := F) (L := L) hsurj] at hdiv

set_option maxHeartbeats 600000 in
set_option synthInstance.maxHeartbeats 80000 in
theorem unramifiedEnlargement : UnramifiedEnlargement.{u} := by
  classical
  intro F _ _ _ _ L₀ hL₀ n hn
  let q := Nat.card (κ F)
  let d := Module.finrank F L₀ * n
  have hd : 0 < d := Nat.mul_pos Module.finrank_pos hn
  let m := q ^ d - 1
  let : Fintype (κ F) := Fintype.ofFinite _
  have hq : 1 < q := by simpa only [q, Nat.card_eq_fintype_card] using
    (Fintype.one_lt_card (α := κ F))
  have hm : (m : κ F) ≠ 0 := by
    have hqzero : (q : κ F) = 0 := by
      simpa only [q, Nat.card_eq_fintype_card] using (Nat.cast_card_eq_zero (R := κ F))
    rw [show m = q ^ d - 1 from rfl, Nat.cast_sub (Nat.one_le_pow _ _ (by omega)),
      Nat.cast_pow, hqzero, zero_pow hd.ne', Nat.cast_one]
    simp
  obtain ⟨j, hj, h₀j⟩ := le_cyclotomicStage_of_unramified (E := L₀.toIntermediateField) hL₀
  have hjm : ((j * m : ℕ) : κ F) ≠ 0 := by simpa only [Nat.cast_mul] using mul_ne_zero hj hm
  have hj0 : j ≠ 0 := fun e => hj (by simp [e])
  have hm0 : m ≠ 0 := fun e => hm (by simp [e])
  have hjm0 := mul_ne_zero hj0 hm0
  let E := cyclotomicStage F (j * m)
  have hE := (cyclotomicStage_data hjm).1
  let L : FiniteGaloisIntermediateField F (SeparableClosure F) :=
    { toIntermediateField := E, finiteDimensional := hE.1, isGalois := cyclotomic_isGalois hjm }
  have h : L₀.toIntermediateField ≤ L.toIntermediateField :=
    h₀j.trans (cyclotomicStage_le_of_dvd hj0 hjm0 (dvd_mul_right j m))
  have hi : cyclotomicStage F m ≤ E :=
    cyclotomicStage_le_of_dvd hm0 hjm0 (dvd_mul_left m j)
  have hsplit : ((X ^ m - C (1 : F)).map (algebraMap F E)).Splits := by
    let i := IntermediateField.inclusion hi
    have he : i.toRingHom.comp (algebraMap F (cyclotomicStage F m)) = algebraMap F E :=
      RingHom.ext i.commutes
    simpa only [Polynomial.map_map, he] using (cyclotomicStage_data hm).2.map i.toRingHom
  have hdvd : d ∣ Module.finrank F L := by
    exact exponent_dvd_of_pow_sub_one_dvd hq hd (split_order_dvd hm hE (cyclotomic_isGalois hjm) hsplit)
  let i := IntermediateField.inclusion h
  let : Algebra L₀ L := i.toAlgebra
  let : IsScalarTower F L₀ L := IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  let : Module.Free L₀ L := Module.Free.of_divisionRing _ _
  have hr : n ∣ Module.finrank L₀ L := by
    rw [← Module.finrank_mul_finrank F L₀ L] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left Module.finrank_pos hdvd
  let : IsGalois F L := L.isGalois
  let f : Gal(L/F) →* Gal(L₀/F) := AlgEquiv.restrictNormalHom L₀
  refine ⟨L, h, hE, hr, f, AlgEquiv.restrictNormalHom_surjective L,
    fun σ x => AlgEquiv.restrictNormal_commutes σ L₀ x, ?_⟩
  intro σ
  apply AlgEquiv.ext
  intro x
  apply L₀.toIntermediateField.val.injective
  change (L₀.toIntermediateField.val (f (restriction L σ) x)) =
    L₀.toIntermediateField.val (restriction L₀ σ x)
  change L.toIntermediateField.val (i (f (restriction L σ) x)) =
    L₀.toIntermediateField.val (restriction L₀ σ x)
  rw [show i (f (restriction L σ) x) = restriction L σ (i x) from
    AlgEquiv.restrictNormal_commutes (restriction L σ) L₀ x]
  exact (AlgEquiv.restrictNormalHom_apply L.toIntermediateField σ (i x)).trans
    (AlgEquiv.restrictNormalHom_apply L₀.toIntermediateField σ x).symm

end Enlargement

section Twist

open Specs.AutomorphismSequence
open Specs.RelativeFormComparison
open private modelOfRelativeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

theorem neutralTwist : NeutralTwist.{u} := by
  intro k S _ _ _ _ G Q a T hn
  obtain ⟨b, hb⟩ := hn
  let : TopologicalSpace (CohPoints k S Q.quotient.val.X) := ⊥
  let : TopologicalSpace Gal(S/k) := krullTopology k S
  let : TopologicalSpace (RelativeAut G.val (fieldTest k S)) := ⊥
  obtain ⟨C⟩ := Descent.RelativeFormComparison.relativeFormClassification (S := S) G
  obtain ⟨c, hc, hclass⟩ := C.computes
    (modelOfRelativeIso G T.group T.trivialization) T.trivialization
  let p : CohPoints k S Q.quotient.val.X →* RelativeAut G.val (fieldTest k S) :=
    (T.inner.app (op (fieldTest k S))).hom.comp
      { toFun := ULift.up, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hequiv (σ : Gal(S/k)) (x : CohPoints k S Q.quotient.val.X) :
      p (pointAction k S Q.quotient.val.X σ x) = automorphismAction k S G.val σ (p x) :=
    ConcreteCategory.congr_hom (T.inner.naturality (fieldMap k S σ).op)
      (ULift.up x : (groupSections Q.quotient.val).obj (op (fieldTest k S)))
  have hc' : ChangesBy c (trivial _) (p b) := by
    intro σ
    change 1 = (p b)⁻¹ * c σ * automorphismAction k S G.val σ (p b)
    have hp : p (show CohPoints k S Q.quotient.val.X from a.val σ) = c σ := (T.cocycle_eq σ).symm.trans (hc σ).symm
    have h : (1 : CohPoints k S Q.quotient.val.X) =
        (b⁻¹ * (show CohPoints k S Q.quotient.val.X from a.val σ)) *
          pointAction k S Q.quotient.val.X σ b := hb σ
    rw [← map_inv, ← hp, ← map_mul, ← hequiv, ← map_mul, ← h, map_one]
  have hneutral := classOf_eq_iff.mpr ⟨p b, hc'⟩
  exact Quotient.exact (C.equiv.injective ((hclass.trans hneutral).trans C.pointed.symm)).symm

end Twist

open _root_.LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open Specs.AutomorphismSequence (AdjointQuotient relativePoints restrictIso)
open Specs.RelativeFormComparison (fieldTest fieldMap)
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open private centre_baseChange from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralTorus
open private baseChangeMapPullback baseChangeKernelSquare
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Components

section ScalarExtension

variable {F K S : Type u} [Field F] [Field K] [Field S] [Algebra F K]
  [Algebra K S] [Algebra F S] [IsScalarTower F K S]

/-- The quotient projection and its full scheme-theoretic kernel after base change. -/
def baseChangeAdjointQuotient (K : Type u) [Field K] [Algebra F K]
    {G : AffineAlgebraicGroup F} (Q : AdjointQuotient G) :
    AdjointQuotient (baseChangedAlgebraicGroup K G) := by
  let B := groupBaseChange F K
  let h := centre_baseChange Q.isCentre K
  let hZ := h.choose
  have hc := h.choose_spec
  let P := baseChangeMapPullback (K := K) Q.projection.hom.hom
  exact
    { centre := baseChangedSubgroup K Q.centre hZ
      isCentre := hc
      quotient := baseChangedAlgebraicGroup K Q.quotient
      projection := B.map Q.projection
      fppf := ⟨MorphismProperty.of_isPullback P.flip Q.fppf.1,
        MorphismProperty.of_isPullback P.flip Q.fppf.2.1,
        MorphismProperty.of_isPullback P.flip Q.fppf.2.2⟩
      kernel := baseChangeKernelSquare Q.projection Q.centre.inclusion Q.kernel }

private theorem restrictScalars_continuous [IsSepClosure F S] :
    Continuous (AlgEquiv.restrictScalarsHom F : Gal(S/K) →* Gal(S/F)) := by
  let r : Gal(S/K) →* Gal(S/F) := AlgEquiv.restrictScalarsHom F
  apply continuous_of_continuousAt_one r
  show Filter.Tendsto r (𝓝 1) (𝓝 (r 1))
  rw [map_one]
  intro U hU
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff F S U).mp hU
  let : FiniteDimensional F E := hE
  obtain ⟨x, hx⟩ := Field.exists_primitive_element F E
  let J : IntermediateField K S := K⟮(x : S)⟯
  have hJ : FiniteDimensional K J := IntermediateField.adjoin.finiteDimensional
    (IsIntegral.tower_top (A := K) (Algebra.IsIntegral.isIntegral (R := F) (x : S)))
  apply (krullTopology_mem_nhds_one_iff K S _).mpr
  refine ⟨J, hJ, fun σ hσ => hsub ?_⟩
  have hv : σ (x : S) = (x : S) :=
    (IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ _ (IntermediateField.mem_adjoin_simple_self _ _)
  have hle : F⟮(x : S)⟯ ≤ IntermediateField.fixedField (Subgroup.zpowers (r σ)) := by
    apply IntermediateField.adjoin_le_iff.mpr
    intro y hy
    have hy' : y = (x : S) := Set.mem_singleton_iff.mp hy
    subst y
    change (x : S) ∈ IntermediateField.fixedField (Subgroup.zpowers (r σ))
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    rintro τ ⟨m, rfl⟩
    exact MulAction.mem_fixedBy_zpow (g := r σ) (a := (x : S)) hv m
  have he : F⟮(x : S)⟯ = E := by
    simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using
      congrArg (IntermediateField.lift (F := E)) hx
  rw [he] at hle
  exact (IntermediateField.le_iff_le _ _).mp hle (Subgroup.mem_zpowers _)

open private relativeSectionGroupEquiv from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AutomorphismSequence

private abbrev forgetField (F K : Type u) [Field F] [Field K] [Algebra F K] :
    SchemeOver K ⥤ SchemeOver F :=
  Over.map (fieldSpecMap F K)

private def fieldTestIso :
    (forgetField F K).obj (fieldTest K S) ≅ fieldTest F S :=
  Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ fieldSpecMap F S = fieldSpecMap K S ≫ fieldSpecMap F K
    rw [Category.id_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    ext x
    exact IsScalarTower.algebraMap_apply F K S x)

private def forgetFieldPoints (G : GroupScheme F) (U : SchemeOver K) :
    (U ⟶ ((groupBaseChange F K).obj G).X) ≃*
      ((forgetField F K).obj U ⟶ G.X) :=
  relativeSectionGroupEquiv
    ((Over.iteratedSliceBackward (Over.mk (fieldSpecMap F K))).obj U) G

private def rebasePointEquiv (G : GroupScheme F) :
    CohPoints K S ((groupBaseChange F K).obj G).X ≃* CohPoints F S G.X :=
  (forgetFieldPoints (F := F) (K := K) G (fieldTest K S)).trans
    { toFun := fun x => (fieldTestIso (F := F) (K := K) (S := S)).inv ≫ x
      invFun := fun x => (fieldTestIso (F := F) (K := K) (S := S)).hom ≫ x
      left_inv := by intro x; dsimp only; simp only [Iso.hom_inv_id_assoc]
      right_inv := by intro x; dsimp only; simp only [Iso.inv_hom_id_assoc]
      map_mul' := MonObj.comp_mul _ }

/-- The projection from the scalar-extension fibre product is equivariant
for restriction of scalar automorphisms. -/
theorem baseChangePoints_action (G : GroupScheme F) (σ : Gal(S/K))
    (p : CohPoints K S ((groupBaseChange F K).obj G).X) :
    rebasePointEquiv G (pointAction K S ((groupBaseChange F K).obj G).X σ p) =
      pointAction F S G.X (σ.restrictScalars F) (rebasePointEquiv G p) := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ (((fieldMap K S σ).left ≫ p.left) ≫ pullback.fst G.X.hom (fieldSpecMap F K)) =
    (fieldMap F S (σ.restrictScalars F)).left ≫ (𝟙 _ ≫ (p.left ≫
      pullback.fst G.X.hom (fieldSpecMap F K)))
  simp only [Category.id_comp]
  rfl

end ScalarExtension

section RelativeExtension

open Specs.AutomorphismSequence (RelativeAut)
open Specs.RelativeFormComparison (transportedAut automorphismAction)
open private modelOfRelativeIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

variable {F K S : Type u} [Field F] [Field K] [Field S] [Algebra F K]
  [Algebra K S] [Algebra F S] [IsScalarTower F K S]

private def forgetFieldSlice :
    Over (fieldTest K S) ⥤ Over (fieldTest F S) :=
  Over.post (forgetField F K) ⋙ Over.map (fieldTestIso (F := F) (K := K) (S := S)).hom

private def relativeBaseChange (G : GroupScheme F) :
    relativePoints ((groupBaseChange F K).obj G) (fieldTest K S) ≅
      (forgetFieldSlice (F := F) (K := K) (S := S)).op ⋙ relativePoints G (fieldTest F S) :=
  NatIso.ofComponents (fun U => (forgetFieldPoints G U.unop.left).toGrpIso) (by
    intro U V m
    apply GrpCat.ext
    intro x
    apply Over.OverMorphism.ext
    exact Category.assoc ..)

private def rebaseRelativeIso {G H : GroupScheme F}
    (j : relativePoints G (fieldTest F S) ≅ relativePoints H (fieldTest F S)) :
    relativePoints ((groupBaseChange F K).obj G) (fieldTest K S) ≅
      relativePoints ((groupBaseChange F K).obj H) (fieldTest K S) :=
  relativeBaseChange G ≪≫
    Functor.isoWhiskerLeft (forgetFieldSlice (F := F) (K := K) (S := S)).op j ≪≫
    (relativeBaseChange H).symm

private theorem rebaseRelativeIso_fixed {G H : GroupScheme F}
    (j : relativePoints G (fieldTest F S) ≅ relativePoints H (fieldTest F S))
    (σ : Gal(S/K)) (hj : restrictIso (fieldMap F S (σ.restrictScalars F)) j = j) :
    restrictIso (fieldMap K S σ) (rebaseRelativeIso (K := K) j) = rebaseRelativeIso (K := K) j := by
  apply Iso.ext
  apply NatTrans.ext
  funext U
  apply GrpCat.ext
  intro x
  change U.unop.left ⟶ ((groupBaseChange F K).obj G).X at x
  let J := forgetFieldSlice (F := F) (K := K) (S := S)
  let U' := (Over.map (fieldMap K S σ)).obj U.unop
  let V := (Over.map (fieldMap F S (σ.restrictScalars F))).obj (J.obj U.unop)
  let W := J.obj U'
  let t : V ⟶ W := Over.homMk (𝟙 _) (by
    refine (Category.id_comp W.hom).trans ?_
    apply Over.OverMorphism.ext
    change (U.unop.hom.left ≫ (fieldMap K S σ).left) ≫ 𝟙 _ =
      (U.unop.hom.left ≫ 𝟙 _) ≫ (fieldMap F S (σ.restrictScalars F)).left
    simp only [Category.comp_id]
    rfl)
  let eG := forgetFieldPoints (F := F) (K := K) G U.unop.left
  let eH := forgetFieldPoints (F := F) (K := K) H U.unop.left
  change eH.symm ((j.hom.app (op W)).hom (eG x)) =
    eH.symm ((j.hom.app (op (J.obj U.unop))).hom (eG x))
  apply congrArg eH.symm
  have ht := ConcreteCategory.congr_hom (j.hom.naturality t.op) (eG x)
  change (j.hom.app (op V)).hom (𝟙 _ ≫ eG x) =
    𝟙 _ ≫ (j.hom.app (op W)).hom (eG x) at ht
  have ht' : (j.hom.app (op V)).hom (eG x) = (j.hom.app (op W)).hom (eG x) :=
    (congrArg (j.hom.app (op V)).hom (Category.id_comp (eG x))).symm.trans
      (ht.trans (Category.id_comp ((j.hom.app (op W)).hom (eG x))))
  exact ht'.symm.trans
    (congrArg (fun i => (i.hom.app (op (J.obj U.unop))).hom (eG x)) hj)

private theorem iso_of_fixed_trivialization [IsSepClosure F S]
    (G H : AffineAlgebraicGroup F)
    (j : relativePoints G.val (fieldTest F S) ≅ relativePoints H.val (fieldTest F S))
    (hj : ∀ σ, restrictIso (fieldMap F S σ) j = j) : Nonempty (G.val ≅ H.val) := by
  let : TopologicalSpace (RelativeAut G.val (fieldTest F S)) := ⊥
  obtain ⟨C⟩ := Descent.RelativeFormComparison.relativeFormClassification (S := S) G
  obtain ⟨a, ha, he⟩ := C.computes (modelOfRelativeIso G H j) j
  have ht : a = trivial (automorphismAction F S G.val) := by
    apply Subtype.ext
    funext σ
    rw [ha]
    change Aut.of (restrictIso (fieldMap F S σ) j ≪≫ j.symm) = 1
    rw [hj σ, Iso.self_symm_id]
    rfl
  exact Quotient.exact (C.equiv.injective ((he.trans (congrArg classOf ht)).trans C.pointed.symm)).symm

end RelativeExtension

section Restriction

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "Fur" => maximalUnramified F
local notation "Fsep" => SeparableClosure F

private instance sepClosure_unramified : IsSepClosure Fur Fsep :=
  ⟨IsSepClosure.sep_closed F, Algebra.isSeparable_tower_top_of_isSeparable F Fur Fsep⟩

private def restrictPointCocycle {G : GroupScheme F}
    (a : Specs.ExceptionalTwistedTraceComparison.PointCocycle (S := Fsep) G) :
    Specs.ExceptionalTwistedTraceComparison.PointCocycle (S := Fsep) ((groupBaseChange F Fur).obj G) := by
  let r : Gal(Fsep/Fur) →* Gal(Fsep/F) := AlgEquiv.restrictScalarsHom F
  let e := rebasePointEquiv (F := F) (K := Fur) (S := Fsep) G
  let : TopologicalSpace (CohPoints F Fsep G.X) := ⊥
  let : TopologicalSpace (CohPoints Fur Fsep ((groupBaseChange F Fur).obj G).X) := ⊥
  have : DiscreteTopology (CohPoints F Fsep G.X) := ⟨rfl⟩
  change Cocycle (pointAction F Fsep G.X) at a
  change Cocycle (pointAction Fur Fsep ((groupBaseChange F Fur).obj G).X)
  refine ⟨fun σ => e.symm (a (r σ)), ?_, fun σ τ => e.injective ?_⟩
  · exact continuous_of_discreteTopology.comp (a.property.1.comp
      (restrictScalars_continuous (F := F) (K := Fur) (S := Fsep)))
  · change e (e.symm (a (r (σ * τ)))) =
      e (e.symm (a (r σ)) * pointAction Fur Fsep ((groupBaseChange F Fur).obj G).X σ (e.symm (a (r τ))))
    simp only [map_mul, MulEquiv.apply_symm_apply]
    rw [show e (pointAction Fur Fsep ((groupBaseChange F Fur).obj G).X σ (e.symm (a (r τ)))) =
      pointAction F Fsep G.X (r σ) (e (e.symm (a (r τ)))) from baseChangePoints_action G σ _,
        MulEquiv.apply_symm_apply]
    exact a.property.2 (r σ) (r τ)

end Restriction

section Reference

open _root_.LinearAlgebraicGroups.Specs (ClosedSubgroup)
open Specs.AbstractPairing (Root IsAttachedCoroot)
open Specs.CentralIsogenies (IsCentralIsogeny characterPullback)
open Specs.CharacterDescent (Cocharacter)
open Specs.CharacterPairing (absoluteRoots)
open Specs.ExceptionalFormsOverUnramifiedFields (IsExceptionalReference HasTypeE)
open Specs.GeometricRadicals (IsReductive IsSemisimple)
open Specs.AutomorphismSequence (AdjointQuotient)
open Specs.IntegralSemisimpleModel (Model)
open Specs.Pinning (AttachedDatum BasedIso PinnedGroup SimpleRoot)
open Specs.QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction pinnedSection
  basedAutTopology fieldGalTopology)
open Specs.RootGroups (AdditiveLine)
open Specs.SimplyConnectedLattice (corootLattice)
open _root_.LinearAlgebraicGroups.Specs (IsSchemeKernel)
open private schemeKernel_exists schemeKernel_sections from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private centralizes_iff from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.Stabilizers
open private transportSubgroup from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private latticeCriterion_pair realization_corootSpan of_fullCorootLattice model_simplyConnected
  fibreTowerIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private pinnedRepresentatives from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms

attribute [local instance] basedAutTopology fieldGalTopology

variable {k : Type u} [Field k]

set_option maxHeartbeats 700000 in
private theorem centre_of_iso {G H : GroupScheme k} (e : G ≅ H) (Z : ClosedSubgroup G)
    (hZ : RepresentsSubgroup Z (fun _ g => Centralizes (𝟙 G) g)) :
    RepresentsSubgroup (transportSubgroup e Z) (fun _ g => Centralizes (𝟙 H) g) := by
  intro U g
  let F := Grp.forget (SchemeOver k)
  let i : G.X ⟶ H.X := e.hom.hom.hom
  let j : H.X ⟶ G.X := e.inv.hom.hom
  have hij : i ≫ j = 𝟙 G.X := (F.map_comp _ _).symm.trans
    ((F.congr_map e.hom_inv_id).trans (F.map_id G))
  have hji : j ≫ i = 𝟙 H.X := (F.map_comp _ _).symm.trans
    ((F.congr_map e.inv_hom_id).trans (F.map_id H))
  have he : Centralizes (𝟙 H) g ↔ Centralizes (𝟙 G) (g ≫ j) := by
    rw [centralizes_iff, centralizes_iff]
    change (∀ (V : SchemeOver k) (t : V ⟶ U) (y : V ⟶ H.X),
      Commute (t ≫ g) (y ≫ 𝟙 H.X)) ↔
      (∀ (V : SchemeOver k) (t : V ⟶ U) (y : V ⟶ G.X),
        Commute (t ≫ (g ≫ j)) (y ≫ 𝟙 G.X))
    simp only [Category.comp_id]
    constructor
    · intro h V t y
      let m : (V ⟶ H.X) →* (V ⟶ G.X) := IsMonHom.monoidHom e.inv.hom.hom V
      have hd := (h V t (y ≫ i)).map m
      change Commute ((t ≫ g) ≫ j) ((y ≫ i) ≫ j) at hd
      simpa only [Category.assoc, hij, Category.comp_id] using hd
    · intro h V t y
      let m : (V ⟶ G.X) →* (V ⟶ H.X) := IsMonHom.monoidHom e.hom.hom.hom V
      have hd := (h V t (y ≫ j)).map m
      change Commute ((t ≫ (g ≫ j)) ≫ i) ((y ≫ j) ≫ i) at hd
      simpa only [Category.assoc, hji, Category.comp_id] using hd
  change Centralizes (𝟙 H) g ↔ ∃ z : U ⟶ Z.group.X,
    z ≫ (transportSubgroup e Z).inclusion.hom.hom = g
  have hf : Centralizes (𝟙 G) (g ≫ j) ↔
      ∃ z : U ⟶ Z.group.X, z ≫ Z.inclusion.hom.hom = g ≫ j :=
    hZ U (g ≫ j)
  refine he.trans (hf.trans ?_)
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change z ≫ (Z.inclusion.hom.hom ≫ i) = g
    rw [← Category.assoc, hz, Category.assoc, hji, Category.comp_id]
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change z ≫ (Z.inclusion.hom.hom ≫ i) = g at hz
    have hh := congrArg (fun f => f ≫ j) hz
    simpa only [Category.assoc, hij, Category.comp_id] using hh

private def adjointQuotientOfIso {G H : AffineAlgebraicGroup k}
    (e : G.val ≅ H.val) (Q : AdjointQuotient G) : AdjointQuotient H := by
  let F := Grp.forget (SchemeOver k)
  let B := F ⋙ Over.forget _
  let u := e.inv ≫ Q.projection
  let Z := transportSubgroup e Q.centre
  have hk : IsSchemeKernel u Z := by
    apply Q.kernel.of_iso (Iso.refl _) (F.mapIso e) (Iso.refl _) (Iso.refl _)
    · change F.map Q.centre.inclusion ≫ F.map e.hom = 𝟙 _ ≫ F.map (Q.centre.inclusion ≫ e.hom)
      rw [Category.id_comp, F.map_comp]
    · change toUnit Q.centre.group.X = 𝟙 _ ≫ toUnit Q.centre.group.X
      exact (Category.id_comp _).symm
    · change F.map Q.projection ≫ 𝟙 _ = F.map e.hom ≫ F.map (e.inv ≫ Q.projection)
      rw [Category.comp_id, ← F.map_comp, Iso.hom_inv_id_assoc]
    · simp
  let : IsIso (B.map e.inv) := B.map_isIso e.inv
  have hu : Flat (B.map u) ∧ Surjective (B.map u) ∧ LocallyOfFinitePresentation (B.map u) := by
    have hq : Flat (B.map Q.projection) := Q.fppf.1
    have hsurj : Surjective (B.map Q.projection) := Q.fppf.2.1
    have hlfp : LocallyOfFinitePresentation (B.map Q.projection) := Q.fppf.2.2
    rw [show B.map u = B.map e.inv ≫ B.map Q.projection from B.map_comp _ _]
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨Z, centre_of_iso e Q.centre Q.isCentre, Q.quotient, u, hu, hk⟩

private def simpleRootEquiv {A : AdditiveLine k} {P : PinnedGroup A}
    (D : AttachedDatum P.pair) : SimpleRoot P.pair ≃ D.toBased.base.support :=
  Equiv.subtypeEquivRight fun α => (D.simple_iff α).symm

private theorem typeE_of_basedIso {k' : Type u} [Field k'] {A : AdditiveLine k}
    {A' : AdditiveLine k'} {P : PinnedGroup A} {P' : PinnedGroup A'}
    {D : AttachedDatum P.pair} {D' : AttachedDatum P'.pair}
    (e : BasedIso D.toBased D'.toBased) {n : ℕ} (h : HasTypeE D n) : HasTypeE D' n := by
  obtain ⟨b, hb⟩ := h
  let b₀ := simpleRootEquiv D
  let b₁ := simpleRootEquiv D'
  let s : D.toBased.base.support ≃ D'.toBased.base.support :=
    (e.val.indexEquiv.image _).trans (Set.equivOfEq e.property)
  let c := b.trans (b₀.trans (s.trans b₁.symm))
  refine ⟨c, fun i j => ?_⟩
  have hp : D'.toBased.datum.pairing (e.val.indexEquiv (b i).val) (e.val.indexEquiv (b j).val) =
      D.toBased.datum.pairing (b i).val (b j).val := e.val.toHom.pairing
  exact hp.trans (hb i j)

set_option maxHeartbeats 700000 in
private theorem cartan_pairing_eq {A : AdditiveLine k} (P : PinnedGroup A)
    (D E : AttachedDatum P.pair) (i j : SimpleRoot P.pair) :
    letI := D.comm
    D.datum.rootDatum.pairing i.val j.val =
      (letI := E.comm; E.datum.rootDatum.pairing i.val j.val) := by
  let := D.comm
  let G := P.pair.G
  let T := P.pair.T
  let := G.property.1
  obtain ⟨N, hN⟩ := schemeKernel_exists (𝟙 G.val)
  have hn : N.inclusion.hom.hom = 1 := by
    have hsection : N.inclusion.hom.hom ∈ Specs.SubgroupSections N N.group.X := by
      change ∃ p : N.group.X ⟶ N.group.X, p ≫ N.inclusion.hom.hom = N.inclusion.hom.hom
      exact ⟨𝟙 _, Category.id_comp _⟩
    have h := (schemeKernel_sections hN N.inclusion.hom.hom).mp hsection
    change N.inclusion.hom.hom ≫ 𝟙 G.val.X = 1 at h
    simpa only [Category.comp_id] using h
  have hcen : Centralizes (𝟙 G.val) N.inclusion.hom.hom := by
    apply (centralizes_iff _ _).mpr
    intro Y y t
    rw [hn, MonObj.comp_one]
    exact Commute.one_left _
  have hid : IsCentralIsogeny (𝟙 G.val) :=
    ⟨inferInstanceAs (IsFinite (𝟙 G.val.X.left)),
      inferInstanceAs (Flat (𝟙 G.val.X.left)),
      inferInstanceAs (Surjective (𝟙 G.val.X.left)), N, hN, hcen⟩
  obtain ⟨_, _, _, hpair⟩ := Classification.CentralIsogenies.centralIsogenyComparison
    G G P.pair.reductive P.pair.reductive T T P.pair.split P.pair.maximal P.pair.split P.pair.maximal
    (𝟙 G.val) (𝟙 T.group) hid (by simp) (inferInstanceAs (Surjective (𝟙 T.group.X.left)))
  let β := j.val
  have hχ : characterPullback (𝟙 T.group) β.val = β.val := by
    change 𝟙 T.group ≫ β.val = β.val
    exact Category.id_comp _
  have hα : characterPullback (𝟙 T.group) β.val ∈ absoluteRoots T := hχ.symm ▸ β.property
  have hβ : (⟨characterPullback (𝟙 T.group) β.val, hα⟩ : Root T) = β := Subtype.ext hχ
  have hc : IsAttachedCoroot T ⟨characterPullback (𝟙 T.group) β.val, hα⟩
      (Additive.toMul (D.datum.rootDatum.coroot β)) := hβ.symm ▸ D.datum.attached β
  have hp := (hpair β.val β.property hα).2 _ _ hc (E.datum.attached β)
  have he : D.datum.rootDatum.coroot β = E.datum.rootDatum.coroot β :=
    Additive.toMul.injective (by simpa only [Category.comp_id] using hp)
  change D.datum.rootDatum.toLinearMap (D.datum.rootDatum.root i.val)
      (D.datum.rootDatum.coroot j.val) = E.datum.rootDatum.toLinearMap
      (E.datum.rootDatum.root i.val) (E.datum.rootDatum.coroot j.val)
  rw [D.datum.root_eq, E.datum.root_eq, he]
  exact (D.datum.pairing_eq _ _).trans (E.datum.pairing_eq _ _).symm

private theorem typeE_of_same_pair {A : AdditiveLine k} (P : PinnedGroup A)
    (D E : AttachedDatum P.pair) {n : ℕ} (h : HasTypeE D n) : HasTypeE E n := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, fun i j => (cartan_pairing_eq P D E (b i) (b j)).symm.trans (hb i j)⟩

end Reference

section Exceptional

open Specs.ExceptionalUnramifiedCocycleSupport
open Specs.ExceptionalTwistedTraceComparison (PointCocycle)
open Specs.ExceptionalFormsOverUnramifiedFields (IsExceptionalReference)
open Specs.AutomorphismSequence (AdjointQuotient)
open Specs.IntegralSemisimpleModel (Model)
open Specs.QuasiSplitInnerForms (PinnedRepresentative trivialOuterAction pinnedSection
  basedAutTopology fieldGalTopology)
open Specs.RelativeFormComparison (transportedAut)
open private pinnedRepresentatives from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.QuasiSplitInnerForms
open private latticeCriterion_pair realization_corootSpan of_fullCorootLattice model_simplyConnected
  fibreTowerIso from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
open private changeCocycle from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.BorelInnerAlignment

attribute [local instance] basedAutTopology fieldGalTopology

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 75000 in
theorem exceptionalCocycleSupport : ExceptionalCocycleSupport.{u} := by
  intro F _ _ _ _ A P D l Q E ω V hV Q₀ L₀ hL₀ houter a
  let K := maximalUnramified F
  let S := SeparableClosure F
  let r : Gal(S/K) →* Gal(S/F) := AlgEquiv.restrictScalarsHom F
  let G := V.model.val
  let GK := baseChangedAlgebraicGroup K G
  have h₀K : L₀.toIntermediateField ≤ K :=
    le_iSup (fun J : {J : IntermediateField F S // IsUnramified F J} => J.val)
      ⟨L₀.toIntermediateField, hL₀⟩
  obtain ⟨ω₀, hω₀⟩ := houter
  have houterK (σ : Gal(S/K)) : ω (r σ) = 1 := by
    have hσ : r σ ∈ K.fixingSubgroup :=
      (IntermediateField.mem_fixingSubgroup_iff K _).mpr fun x hx => σ.commutes ⟨x, hx⟩
    have hL : r σ ∈ L₀.toIntermediateField.fixingSubgroup :=
      IntermediateField.fixingSubgroup_le h₀K hσ
    have he : restriction L₀ (r σ) = 1 := by
      change r σ ∈ (AlgEquiv.restrictNormalHom L₀.toIntermediateField).ker
      rwa [L₀.toIntermediateField.restrictNormalHom_ker]
    rw [← hω₀, he, map_one]
  have hfixed (σ : Gal(S/K)) :
      restrictIso (fieldMap F S (r σ)) V.trivialization = V.trivialization := by
    have h := V.transport_eq (r σ)
    rw [houterK, map_one] at h
    change Aut.of (restrictIso (fieldMap F S (r σ)) V.trivialization ≪≫ V.trivialization.symm) = 1 at h
    have he := congrArg Aut.asIso h
    change restrictIso (fieldMap F S (r σ)) V.trivialization ≪≫ V.trivialization.symm = Iso.refl _ at he
    have hh := congrArg (fun i => i ≪≫ V.trivialization) he
    simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans] using hh
  let PK := baseChangedAlgebraicGroup K P.pair.G
  obtain ⟨hPV⟩ := iso_of_fixed_trivialization PK GK
    (rebaseRelativeIso (K := K) V.trivialization)
    (fun σ => rebaseRelativeIso_fixed V.trivialization σ (hfixed σ))
  have hcoroot := (latticeCriterion_pair Classification.IntegralRealization.integralRealization
    P.pair D hV.1).mp hV.2.1
  obtain ⟨M⟩ := Classification.IntegralRealization.integralRealization D.toBased
  obtain ⟨AF, RF, eF, _, _, _, _, _, _⟩ := M.fieldFibre F
  obtain ⟨AK, RK, eK, _, _, _, _, _, _⟩ := M.fieldFibre K
  obtain ⟨iF⟩ := ((Classification.PinnedEquivalence.pinnedEquivalence.2 F).2.1
    P.pair RF.pinned.pair D RF.attached).mpr ⟨RF.datumIso.val⟩
  let iK : PK.val ≅ RK.pinned.pair.G.val :=
    (groupBaseChange F K).mapIso (iF ≪≫ eF.symm) ≪≫ (fibreTowerIso F K).symm.app M.group ≪≫ eK
  have hsem := of_fullCorootLattice RK.pinned.pair RK.attached
    (realization_corootSpan RK hcoroot)
  have hsc := model_simplyConnected M hcoroot eK
  obtain ⟨DK, lK, QK, EK, _, _⟩ := Descent.QuasiSplitInnerForms.automorphismSequences RK.pinned
  have htypeK : IsExceptionalReference DK := by
    refine ⟨hsem, hsc, ?_⟩
    have liftType : ∀ n, Specs.ExceptionalFormsOverUnramifiedFields.HasTypeE D n →
        Specs.ExceptionalFormsOverUnramifiedFields.HasTypeE DK n :=
      fun n h => typeE_of_same_pair RK.pinned RK.attached DK
        (typeE_of_basedIso RK.datumIso h)
    exact hV.2.2.imp (liftType 6) (fun h => h.imp (liftType 7) (liftType 8))
  let ωK := trivial (trivialOuterAction (k := K) (S := S) DK.toBased)
  obtain ⟨VK⟩ := pinnedRepresentatives (S := S) EK ωK
  obtain ⟨iVK⟩ := iso_of_fixed_trivialization RK.pinned.pair.G VK.model.val VK.trivialization
    (fun σ => by
      have h := VK.transport_eq σ
      change transportedAut K S VK.trivialization σ = pinnedSection EK (1 : Aut DK.toBased) at h
      rw [map_one] at h
      have he := congrArg Aut.asIso h
      change restrictIso (fieldMap K S σ) VK.trivialization ≪≫ VK.trivialization.symm = Iso.refl _ at he
      have hh := congrArg (fun i => i ≪≫ VK.trivialization) he
      simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl, Iso.refl_trans] using hh)
  let J : AdjointQuotient VK.model.val :=
    adjointQuotientOfIso (hPV.symm ≪≫ iK ≪≫ iVK) (baseChangeAdjointQuotient K Q₀)
  let H := Q₀.quotient.val
  let HK := (groupBaseChange F K).obj H
  let : TopologicalSpace (CohPoints K S HK.X) := ⊥
  let : TopologicalSpace (CohPoints F S H.X) := ⊥
  let : DiscreteTopology (CohPoints F S H.X) := ⟨rfl⟩
  let aK : Cocycle (pointAction K S HK.X) := restrictPointCocycle a
  let z : groupH1 K HK.X S := classOf aK
  have hn : classOf aK = basepoint (pointAction K S HK.X) := by
    have h := ExceptionalFormsOverUnramifiedFields.adjoint_vanishing F S VK htypeK J
      (show groupH1 K J.quotient.val.X S from z)
    exact h
  obtain ⟨bK, hbK⟩ := classOf_eq_iff.mp hn
  let e := rebasePointEquiv (F := F) (K := K) (S := S) H
  let b := e bK
  change Cocycle (pointAction F S H.X) at a
  let : LocallyOfFiniteType H.X.hom := Q₀.quotient.property.2.1
  have hact : Continuous (fun p : Gal(S/F) × CohPoints F S H.X => pointAction F S H.X p.1 p.2) := by
    apply (continuousAction_iff_finiteLevel (ρ := pointAction F S H.X)).mpr
    intro x
    obtain ⟨L, hx⟩ := point_defined_at_finite_level x
    exact ⟨L, (finitePoints_iff_fixed L x).mp hx⟩
  obtain ⟨c, hc⟩ := changeCocycle (pointAction F S H.X) hact a b
  have htriv : ∀ σ ∈ K.fixingSubgroup, c σ = 1 := by
    intro σ hσ
    let τ := K.fixingSubgroupEquiv ⟨σ, hσ⟩
    have hr : r τ = σ := AlgEquiv.ext fun _ => rfl
    have hadd : e (aK.val τ) = a (r τ) := MulEquiv.apply_symm_apply e _
    have h := hbK τ
    change (1 : CohPoints K S HK.X) = bK⁻¹ * (show CohPoints K S HK.X from aK.val τ) *
      pointAction K S HK.X τ bK at h
    have hin := congrArg e h
    have hequiv : e (pointAction K S HK.X τ bK) = pointAction F S H.X (r τ) b :=
      baseChangePoints_action H τ bK
    rw [map_one, map_mul, map_mul, map_inv, hadd, hequiv, hr] at hin
    exact (hc σ).trans hin.symm
  refine ⟨b, ?_⟩
  obtain ⟨L, d, hlo, hL, hd, hline⟩ := descend_unramified_point_cocycle L₀ hL₀ c htriv
  exact ⟨L, d, hlo, hL, hd, fun σ => (hline σ).trans (hc σ)⟩

end Exceptional

end
end LinearAlgebraicGroups.Arithmetic.ExceptionalUnramifiedCocycleSupport
