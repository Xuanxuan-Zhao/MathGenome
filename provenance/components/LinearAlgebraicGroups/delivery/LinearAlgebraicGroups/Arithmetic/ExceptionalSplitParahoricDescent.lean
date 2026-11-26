import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalSplitParahoricDescent
import LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import LinearAlgebraicGroups.Affine.GroupSchemes
import LinearAlgebraicGroups.Arithmetic.IntegralPinnedAutomorphisms
import LinearAlgebraicGroups.Arithmetic.ExceptionalScaledParahoricAction
import LinearAlgebraicGroups.Descent.ResidueFlagDescent
import Mathlib.FieldTheory.Finite.GaloisField
import Batteries.Tactic.OpenPrivate
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Flat.TorsionFree

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalSplitParahoricDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct Polynomial WithZero Pointwise CategoryTheory.MonObj
open Specs.ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer)
open Specs.ExceptionalAffineBruhat
open Specs.ExceptionalAffineBuilding
open Specs.ExceptionalSplitParahoricDescent

universe u v

noncomputable section

set_option linter.style.haveILetI false

section CoefficientLift

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
    (p : K[X]) (hp : ∀ σ : Gal(K/F), p.map σ.toRingHom = p)

private def liftPolynomialActionHom (σ : Gal(K/F)) : AdjoinRoot p →ₐ[F] AdjoinRoot p :=
  AdjoinRoot.liftAlgHom p ((IsScalarTower.toAlgHom F K _).comp σ.toAlgHom)
    (AdjoinRoot.root p) (by
      change p.eval₂ ((algebraMap K _).comp σ.toRingHom) (AdjoinRoot.root p) = 0
      rw [← Polynomial.eval₂_map, hp σ, ← Polynomial.aeval_def, AdjoinRoot.aeval_eq,
        AdjoinRoot.mk_self])

private theorem liftPolynomialActionHom_root (σ : Gal(K/F)) :
    liftPolynomialActionHom p hp σ (AdjoinRoot.root p) = AdjoinRoot.root p :=
  AdjoinRoot.liftAlgHom_root ..

private theorem liftPolynomialActionHom_scalar (σ : Gal(K/F)) (x : K) :
    liftPolynomialActionHom p hp σ (algebraMap K (AdjoinRoot p) x) =
      algebraMap K (AdjoinRoot p) (σ x) :=
  AdjoinRoot.liftAlgHom_of ..

private theorem liftPolynomialActionHom_one :
    liftPolynomialActionHom p hp 1 = AlgHom.id F _ := by
  apply AlgHom.toRingHom_injective
  apply AdjoinRoot.ringHom_ext
  · ext1 x
    exact liftPolynomialActionHom_scalar p hp 1 x
  · exact liftPolynomialActionHom_root p hp 1

private theorem liftPolynomialActionHom_mul (σ τ : Gal(K/F)) :
    liftPolynomialActionHom p hp (σ * τ) =
      (liftPolynomialActionHom p hp σ).comp (liftPolynomialActionHom p hp τ) := by
  apply AlgHom.toRingHom_injective
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro x
    change liftPolynomialActionHom p hp (σ * τ) (algebraMap K _ x) =
      liftPolynomialActionHom p hp σ (liftPolynomialActionHom p hp τ (algebraMap K _ x))
    rw [liftPolynomialActionHom_scalar, liftPolynomialActionHom_scalar p hp τ,
      liftPolynomialActionHom_scalar p hp σ, AlgEquiv.mul_apply]
  · change liftPolynomialActionHom p hp (σ * τ) (AdjoinRoot.root p) =
      liftPolynomialActionHom p hp σ (liftPolynomialActionHom p hp τ (AdjoinRoot.root p))
    rw [liftPolynomialActionHom_root, liftPolynomialActionHom_root p hp τ,
      liftPolynomialActionHom_root p hp σ]

/-- A coefficient action fixing the polynomial extends to its root algebra,
where it fixes the distinguished root. -/
def liftPolynomialAction : Gal(K/F) →* (AdjoinRoot p ≃ₐ[F] AdjoinRoot p) where
  toFun σ := AlgEquiv.ofAlgHom (liftPolynomialActionHom p hp σ)
    (liftPolynomialActionHom p hp σ⁻¹)
    (by rw [← liftPolynomialActionHom_mul, mul_inv_cancel, liftPolynomialActionHom_one])
    (by rw [← liftPolynomialActionHom_mul, inv_mul_cancel, liftPolynomialActionHom_one])
  map_one' := by
    ext x
    exact DFunLike.congr_fun (liftPolynomialActionHom_one p hp) x
  map_mul' σ τ := by
    ext x
    exact DFunLike.congr_fun (liftPolynomialActionHom_mul p hp σ τ) x

theorem liftPolynomialAction_root (σ : Gal(K/F)) :
    liftPolynomialAction p hp σ (AdjoinRoot.root p) = AdjoinRoot.root p :=
  liftPolynomialActionHom_root p hp σ

theorem liftPolynomialAction_scalar (σ : Gal(K/F)) (x : K) :
    liftPolynomialAction p hp σ (algebraMap K (AdjoinRoot p) x) =
      algebraMap K (AdjoinRoot p) (σ x) :=
  liftPolynomialActionHom_scalar p hp σ x

end CoefficientLift

/-- The extension of scalars fixes the polynomial used for the face scaling. -/
theorem uniformizerPolynomial_map {F K : Type u} [Field F] [Field K] [Algebra F K]
    (d : ℕ) (π : Fˣ) (σ : Gal(K/F)) :
    (uniformizerPolynomial (K := K) d π).map σ.toRingHom =
      uniformizerPolynomial (K := K) d π := by
  simp [uniformizerPolynomial]

section ScalingField

variable {F K L : Type u} [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]

/-- Transport the coefficient action to the specified scaling field. -/
def scalingCoefficientAction (d : ℕ) (π : Fˣ)
    (r : AdjoinRoot (uniformizerPolynomial (K := K) d π) ≃ₐ[K] L) :
    Gal(K/F) →* Gal(L/F) :=
  let q := r.restrictScalars F
  { toFun := fun σ =>
      (q.symm.trans (liftPolynomialAction _ (uniformizerPolynomial_map d π) σ)).trans q
    map_one' := by
      rw [map_one]
      ext z
      exact q.apply_symm_apply z
    map_mul' σ τ := by
      rw [map_mul]
      ext z
      simp only [AlgEquiv.trans_apply, AlgEquiv.mul_apply, AlgEquiv.symm_apply_apply] }

theorem scalingCoefficientAction_scalar (d : ℕ) (π : Fˣ)
    (r : AdjoinRoot (uniformizerPolynomial (K := K) d π) ≃ₐ[K] L)
    (σ : Gal(K/F)) (z : K) :
    scalingCoefficientAction d π r σ (algebraMap K L z) = algebraMap K L (σ z) := by
  change r (liftPolynomialAction _ (uniformizerPolynomial_map d π) σ
    (r.symm (algebraMap K L z))) = algebraMap K L (σ z)
  rw [AlgEquiv.commutes, liftPolynomialAction_scalar, AlgEquiv.commutes]

theorem scalingCoefficientAction_root (d : ℕ) (π : Fˣ)
    (r : AdjoinRoot (uniformizerPolynomial (K := K) d π) ≃ₐ[K] L)
    (σ : Gal(K/F)) :
    scalingCoefficientAction d π r σ (r (AdjoinRoot.root _)) = r (AdjoinRoot.root _) := by
  change r (liftPolynomialAction _ (uniformizerPolynomial_map d π) σ
    (r.symm (r (AdjoinRoot.root _)))) = r (AdjoinRoot.root _)
  rw [AlgEquiv.symm_apply_apply, liftPolynomialAction_root]

end ScalingField

section ResidueCoefficients

open ValuativeRel
open Specs.ExceptionalLocalRootCoordinates (canonicalExtension normalizedValuation residueMap)
open Specs.ExceptionalIwahoriCongruence (localIntegers residueHom)
attribute [local instance] canonicalExtension

variable {F L : Type u} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension F L]

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
private theorem automorphism_preserves_value_order (σ : Gal(L/F)) (x y : L) :
    valuation L (σ x) ≤ valuation L (σ y) ↔ valuation L x ≤ valuation L y := by
  let r₀ : ValuativeRel L := inferInstance
  have h₀ : @ValuativeExtension F L _ _ _ r₀ _ := inferInstance
  let v := valuation L
  have hcompare (a b : L) : @ValuativeRel.vle L _ r₀ a b ↔ v a ≤ v b :=
    (valuation L).vle_iff_le
  let r : ValuativeRel L := .ofValuation (v.comap σ.toRingHom)
  have hr : @ValuativeExtension F L _ _ _ r _ := by
    refine ⟨?_⟩
    intro x y
    change v (σ (algebraMap F L x)) ≤ v (σ (algebraMap F L y)) ↔ _
    rw [AlgEquiv.commutes, AlgEquiv.commutes, ← hcompare]
    exact h₀.vle_iff_vle x y
  obtain ⟨s, T, hs⟩ := finiteExtension_localField (K := F) (L := L)
  have eq : r = r₀ := (hs.2.2.2.2 r hr).trans (hs.2.2.2.2 r₀ h₀).symm
  change @ValuativeRel.vle L _ r x y ↔ _
  rw [eq]
  exact hcompare x y

/-- A coefficient automorphism of a finite local extension preserves the
normalized valuation, including if the extension has an inseparable part. -/
theorem normalizedValuation_automorphism (σ : Gal(L/F)) (x : L) :
    normalizedValuation L (σ x) = normalizedValuation L x := by
  change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L) (valuation L (σ x)) =
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L) (valuation L x)
  apply congrArg (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L)
  have hlt (a b : L) : valuation L (σ a) < valuation L (σ b) ↔
      valuation L a < valuation L b :=
    (not_le).symm.trans ((not_congr (automorphism_preserves_value_order σ b a)).trans not_le)
  let f : ℕ → ValueGroupWithZero L := fun n => valuation L ((σ ^ n) x)
  have hstep (n : ℕ) : f (n + 1) = valuation L (σ ((σ ^ n) x)) := by
    dsimp only [f]
    rw [pow_succ', AlgEquiv.mul_apply]
  have hstart : f 0 = valuation L x := by simp [f]
  have hfinal : f (orderOf σ) = f 0 := by
    dsimp only [f]
    rw [pow_orderOf_eq_one, pow_zero]
  rcases lt_trichotomy (valuation L (σ x)) (valuation L x) with h | h | h
  · have hs : ∀ n, f (n + 1) < f n := by
      intro n
      induction n with
      | zero => simpa only [hstep, pow_zero, AlgEquiv.one_apply, hstart] using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n]
        exact (hlt _ _).2 ih
    exact False.elim ((strictAnti_nat_of_succ_lt hs (orderOf_pos σ)).ne hfinal)
  · exact h
  · have hs : ∀ n, f n < f (n + 1) := by
      intro n
      induction n with
      | zero => simpa only [hstep, pow_zero, AlgEquiv.one_apply, hstart] using h
      | succ n ih =>
        rw [hstep (n + 1), hstep n]
        exact (hlt _ _).2 ih
    exact False.elim ((strictMono_nat_of_lt_succ hs (orderOf_pos σ)).ne hfinal.symm)

set_option quotPrecheck false in
local notation "O(" L ")" => (valuation L).valuationSubring

/-- A local coefficient automorphism restricted to the integer ring. -/
def integerCoefficient (σ : Gal(L/F)) : O(L) ≃ₐ[O(F)] O(L) where
  toFun z := ⟨σ (z : L), by
    have hz : valuation L (z : L) ≤ valuation L 1 := by
      simpa only [map_one] using ((valuation L).mem_valuationSubring_iff _).1 z.property
    apply ((valuation L).mem_valuationSubring_iff _).2
    simpa only [map_one] using (automorphism_preserves_value_order σ (z : L) 1).2 hz⟩
  invFun z := ⟨σ.symm (z : L), by
    have hz : valuation L (z : L) ≤ valuation L 1 := by
      simpa only [map_one] using ((valuation L).mem_valuationSubring_iff _).1 z.property
    apply ((valuation L).mem_valuationSubring_iff _).2
    simpa only [map_one] using (automorphism_preserves_value_order σ.symm (z : L) 1).2 hz⟩
  left_inv z := Subtype.ext (σ.symm_apply_apply z)
  right_inv z := Subtype.ext (σ.apply_symm_apply z)
  map_mul' z w := Subtype.ext (map_mul σ (z : L) (w : L))
  map_add' z w := Subtype.ext (map_add σ (z : L) (w : L))
  commutes' z := Subtype.ext (σ.commutes (z : F))

/-- The action induced by field coefficients on the actual residue field. -/
def residueCoefficientAction :
    letI := (residueMap F L).toAlgebra
    Gal(L/F) →* Gal(residue L / residue F) :=
  letI := (residueMap F L).toAlgebra
  { toFun := fun σ =>
      { __ := IsLocalRing.ResidueField.mapEquiv (integerCoefficient σ).toRingEquiv
        commutes' := by
          intro z
          obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
          exact congrArg (IsLocalRing.residue O(L)) ((integerCoefficient σ).commutes w) }
    map_one' := by
      ext z
      obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
      rfl
    map_mul' σ τ := by
      ext z
      obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
      rfl }

omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
theorem residueCoefficientAction_eq (σ : Gal(L/F)) (z z' : localIntegers L)
    (hz : (z' : L) = σ (z : L)) :
    letI := (residueMap F L).toAlgebra
    residueCoefficientAction σ ((residueHom (localIntegers L)).hom z) =
      (residueHom (localIntegers L)).hom z' := by
  change IsLocalRing.residue O(L) (integerCoefficient σ z) = IsLocalRing.residue O(L) z'
  exact congrArg (IsLocalRing.residue O(L)) (Subtype.ext hz.symm)

end ResidueCoefficients

section ScalingResidue

open ValuativeRel
open Specs.ExceptionalLocalRootCoordinates (canonicalExtension normalizedValuation residueMap)
open Specs.ExceptionalIwahoriCongruence (localIntegers residueHom)
attribute [local instance] canonicalExtension

variable {F K L : Type u} [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  [FiniteDimensional F K] [FiniteDimensional K L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension F K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L] [ValuativeExtension K L]

/-- The residue action of the lifted coefficient automorphisms. -/
def scalingResidueAction (d : ℕ) (π : Fˣ)
    (r : AdjoinRoot (uniformizerPolynomial (K := K) d π) ≃ₐ[K] L) :
    letI := (residueMap F L).toAlgebra
    Gal(K/F) →* Gal(residue L / residue F) :=
  letI := (residueMap F L).toAlgebra
  letI := FiniteDimensional.trans F K L
  residueCoefficientAction.comp (scalingCoefficientAction d π r)

theorem scalingResidueAction_eq (d : ℕ) (π : Fˣ)
    (r : AdjoinRoot (uniformizerPolynomial (K := K) d π) ≃ₐ[K] L)
    (σ : Gal(K/F)) (z z' : localIntegers L)
    (hz : (z' : L) = scalingCoefficientAction d π r σ (z : L)) :
    letI := (residueMap F L).toAlgebra
    scalingResidueAction d π r σ ((residueHom (localIntegers L)).hom z) =
      (residueHom (localIntegers L)).hom z' := by
  letI := FiniteDimensional.trans F K L
  exact residueCoefficientAction_eq _ z z' hz

/-- The canonical residue map for the scaling field intertwines the
unramified-level action with its lift. -/
theorem scalingResidueAction_restrict (d : ℕ) (π : Fˣ)
    (r : AdjoinRoot (uniformizerPolynomial (K := K) d π) ≃ₐ[K] L)
    (σ : Gal(K/F)) (z : residue K) :
    letI := (residueMap F L).toAlgebra
    letI := (residueMap F K).toAlgebra
    scalingResidueAction d π r σ (residueMap K L z) =
      residueMap K L (residueCoefficientAction σ z) := by
  letI := FiniteDimensional.trans F K L
  letI := (residueMap F L).toAlgebra
  letI := (residueMap F K).toAlgebra
  obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
  change IsLocalRing.residue (valuation L).valuationSubring
      (integerCoefficient (scalingCoefficientAction d π r σ)
        (algebraMap (valuation K).valuationSubring (valuation L).valuationSubring w)) =
    IsLocalRing.residue (valuation L).valuationSubring
      (algebraMap (valuation K).valuationSubring (valuation L).valuationSubring
        (integerCoefficient σ w))
  exact congrArg (IsLocalRing.residue (valuation L).valuationSubring)
    (Subtype.ext (scalingCoefficientAction_scalar d π r σ (w : K)))

end ScalingResidue

section UniformizerValues

open ValuativeRel WithZero
open Specs.ExceptionalLocalRootCoordinates
  (canonicalExtension normalizedValuation normalizedValueGroupMap)
attribute [local instance] canonicalExtension

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L]

private theorem normalized_lt_one {R : Type u} [Field R] [ValuativeRel R]
    [TopologicalSpace R] [IsNonarchimedeanLocalField R] (x : R) :
    normalizedValuation R x < 1 ↔ valuation R x < 1 := by
  have h : normalizedValuation R x < normalizedValuation R 1 ↔ valuation R x < valuation R 1 :=
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt R).toOrderIso.lt_iff_lt
  simpa only [map_one] using h

private theorem normalized_value_map (x : K) :
    normalizedValueGroupMap K L (normalizedValuation K x) =
      normalizedValuation L (algebraMap K L x) := by
  let eK := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  let eL := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  change eL (ValuativeExtension.mapValueGroupWithZero K L (eK.symm (eK (valuation K x)))) =
    eL (valuation L (algebraMap K L x))
  rw [eK.symm_apply_apply, ValuativeExtension.mapValueGroupWithZero_valuation]

/-- The value of the uniformizer root and the normalized values of all base scalars. -/
theorem scaled_uniformizer_values {d : ℕ} (hd : 0 < d) {π : K} {ξ : L}
    (hπ : normalizedValuation K π = exp (-1 : ℤ)) (hξ : ξ ^ d = algebraMap K L π) :
    ∃ c : ℤ, 0 < c ∧ normalizedValuation L ξ = exp (-c) ∧
      ∀ x : K, x ≠ 0 → normalizedValuation L (algebraMap K L x) =
        exp ((d : ℤ) * c * log (normalizedValuation K x)) := by
  have hπ₀ : π ≠ 0 := fun hz => exp_ne_zero (a := (-1 : ℤ)) (hπ.symm.trans (by simp [hz]))
  have hξ₀ : ξ ≠ 0 := fun hz => ((_root_.map_ne_zero (algebraMap K L)).mpr hπ₀)
    (by simpa [hz, Nat.ne_of_gt hd] using hξ.symm)
  let c := -(log (normalizedValuation L ξ))
  have hξv : normalizedValuation L ξ = exp (-c) := by
    simpa only [c, neg_neg] using (exp_log ((_root_.map_ne_zero (normalizedValuation L)).mpr hξ₀)).symm
  have hall : normalizedValuation L (algebraMap K L π) = exp (-c) ^ d := by rw [← hξ, map_pow, hξv]
  have hπlt : normalizedValuation L (algebraMap K L π) < 1 := by
    let := canonicalExtension K L
    refine (normalized_lt_one _).mpr
      ((Valuation.HasExtension.val_map_lt_one_iff (valuation K) (valuation L) π).mpr ?_)
    apply (normalized_lt_one π).mp
    rw [hπ, ← exp_zero]
    exact exp_lt_exp.mpr (by decide)
  have hc : 0 < c := by
    have hp : exp (-c) ^ d < 1 := hall ▸ hπlt
    have hv : exp (-c) < 1 := by
      by_contra! h
      exact (not_le_of_gt hp) (one_le_pow₀ h)
    have : -c < 0 := exp_lt_exp.mp (by simpa only [exp_zero] using hv)
    omega
  refine ⟨c, hc, hξv, ?_⟩
  intro x hx
  let n := log (normalizedValuation K x)
  let f := normalizedValueGroupMap K L
  have hexp (z : ℤ) (e : ℤ) : (exp z : ℤᵐ⁰) ^ e = exp (e * z) := by
    change (((↑(Multiplicative.ofAdd z)) : ℤᵐ⁰) ^ e) =
      ↑(Multiplicative.ofAdd (e * z))
    rw [← WithZero.coe_zpow]
    rfl
  have hπ' : f (exp (-1 : ℤ)) = exp (-((d : ℤ) * c)) := by
    rw [← hπ, normalized_value_map, hall, ← zpow_natCast, hexp]
    congr 1
    simp
  have hz (z : ℤ) : exp z = (exp (-1 : ℤ) : ℤᵐ⁰) ^ (-z) := by rw [hexp]; simp
  calc
    normalizedValuation L (algebraMap K L x) = f (exp n) := by
      rw [exp_log ((_root_.map_ne_zero (normalizedValuation K)).mpr hx), normalized_value_map]
    _ = exp ((d : ℤ) * c * n) := by
      rw [hz n, map_zpow₀, hπ', hexp]
      congr 1
      simp [mul_comm]


end UniformizerValues

section UnramifiedResidueCoefficients

open Specs.ExceptionalLocalRootCoordinates (canonicalExtension normalizedValuation residueMap)
open ValuativeRel WithZero
attribute [local instance] canonicalExtension

variable {F K : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]

set_option quotPrecheck false in
local notation "O(" K ")" => (valuation K).valuationSubring

@[instance_reducible]
private def integerGaloisAction : MulSemiringAction Gal(K/F) O(K) :=
  MulSemiringAction.compHom O(K)
  ({ toFun := fun σ => (integerCoefficient σ).toRingEquiv
     map_one' := by ext z; rfl
     map_mul' := by intro σ τ; ext z; rfl } : Gal(K/F) →* RingAut O(K))

attribute [local instance] integerGaloisAction

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem integer_isGaloisGroup : IsGaloisGroup Gal(K/F) O(F) O(K) where
  commutes := ⟨by
    intro σ x y
    change integerCoefficient σ (x • y) = x • integerCoefficient σ y
    exact map_smul (integerCoefficient σ) x y⟩
  isInvariant := ⟨by
    intro x hx
    have h : ∀ g : Gal(K/F), g • (x : K) = (x : K) :=
      fun g => congrArg Subtype.val (hx g)
    obtain ⟨y, hy⟩ := Algebra.IsInvariant.isInvariant (A := F) (G := Gal(K/F)) (x : K) h
    have hy' : y ∈ O(F) := by
      rw [(valuation F).mem_valuationSubring_iff, ← map_one (valuation F),
        ← Valuation.HasExtension.val_map_le_iff (valuation F) (valuation K), hy]
      simpa only [map_one] using ((valuation K).mem_valuationSubring_iff _).mp x.property
    exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩⟩
  faithful := ⟨by
    intro σ τ h
    ext x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective O(K) x
    have hh (z : O(K)) : σ (algebraMap O(K) K z) = τ (algebraMap O(K) K z) :=
      congrArg Subtype.val (h z)
    rw [map_div₀, map_div₀, hh, hh]⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem integer_isIntegralClosure : IsIntegralClosure O(K) O(F) K := by
  letI := integer_isGaloisGroup (F := F) (K := K)
  letI := Algebra.IsInvariant.isIntegral O(F) O(K) Gal(K/F)
  refine ⟨Subtype.val_injective, fun {x} => ⟨?_, ?_⟩⟩
  · intro hx
    exact ⟨⟨x, (Valuation.valuationSubring.integers (valuation K)).mem_of_integral
      (hx.tower_top (A := O(K)))⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact (Algebra.IsIntegral.isIntegral y).algebraMap

private theorem normalized_le {T : Type u} [Field T] [ValuativeRel T]
    [TopologicalSpace T] [IsNonarchimedeanLocalField T] (x y : T) :
    normalizedValuation T x ≤ normalizedValuation T y ↔ valuation T x ≤ valuation T y :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt T).toOrderIso.le_iff_le

private theorem maximalIdeal_eq_span_uniformizer {T : Type u} [Field T] [ValuativeRel T]
    [TopologicalSpace T] [IsNonarchimedeanLocalField T] (π : O(T))
    (hπ : normalizedValuation T (π : T) = exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal O(T) = Ideal.span {π} := by
  have hπlt : normalizedValuation T (π : T) < 1 := by
    rw [hπ, exp_lt_one_iff]
    decide
  refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr
    ((Valuation.mem_maximalIdeal_iff T _).mpr ((normalized_lt_one _).mp hπlt)))
  intro z hz
  have hlt := (normalized_lt_one (z : T)).mpr ((Valuation.mem_maximalIdeal_iff T _).mp hz)
  rw [Ideal.mem_span_singleton]
  apply (Valuation.integer.integers (valuation T)).dvd_iff_le.mpr
  apply (normalized_le _ _).mp
  change normalizedValuation T (z : T) ≤ normalizedValuation T π
  rw [hπ]
  by_cases h0 : normalizedValuation T (z : T) = 0
  · simp [h0]
  · rw [← exp_log h0, exp_le_exp]
    have hlog : log (normalizedValuation T (z : T)) < 0 := by
      apply exp_lt_exp.mp
      simpa only [exp_log h0, exp_zero] using hlt
    omega

omit [FiniteDimensional F K] [IsGalois F K] in
private theorem unramified_map_maximalIdeal (h : IsUnramifiedLocalExtension F K)
    (π : Fˣ) (hπ : normalizedValuation F (π : F) = exp (-1 : ℤ)) :
    (IsLocalRing.maximalIdeal O(F)).map (algebraMap O(F) O(K)) = IsLocalRing.maximalIdeal O(K) := by
  have hπlt : normalizedValuation F (π : F) < 1 := by
    rw [hπ, exp_lt_one_iff]
    decide
  let p : O(F) := ⟨π, ((normalized_lt_one _).mp hπlt).le⟩
  have hq : normalizedValuation K ((algebraMap O(F) O(K) p : O(K)) : K) =
      exp (-1 : ℤ) := (h (π : F)).trans hπ
  rw [maximalIdeal_eq_span_uniformizer p hπ, Ideal.map_span, Set.image_singleton,
    maximalIdeal_eq_span_uniformizer _ hq]

/-- For the unramified extension the canonical map on coefficient groups
is bijective, with its action computed by reduction of integral points. -/
theorem unramified_residueCoefficientAction_bijective
    (h : IsUnramifiedLocalExtension F K)
    (π : Fˣ) (hπ : normalizedValuation F (π : F) = exp (-1 : ℤ)) :
    letI := (residueMap F K).toAlgebra
    Function.Bijective (residueCoefficientAction (F := F) (L := K)) := by
  classical
  let R := O(F)
  let S := O(K)
  let p := IsLocalRing.maximalIdeal R
  let q := IsLocalRing.maximalIdeal S
  let G := Gal(K/F)
  letI : IsGaloisGroup G R S := integer_isGaloisGroup
  letI : Algebra.IsIntegral R S := Algebra.IsInvariant.isIntegral R S G
  letI : IsIntegralClosure S R K := integer_isIntegralClosure
  letI : Module.Finite R S := IsIntegralClosure.finite R F K S
  letI : Module.IsTorsionFree R S := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (fun x y hxy => Subtype.ext ((algebraMap F K).injective (congrArg Subtype.val hxy)))
  letI : Finite (residue F) := (localField_properties F).2.1
  letI : Finite (residue K) := (localField_properties K).2.1
  letI : Finite (R ⧸ p) := inferInstanceAs (Finite (residue F))
  letI : Algebra.FormallyUnramified R S := Algebra.FormallyUnramified.iff_map_maximalIdeal_eq.mpr
    ⟨inferInstance, unramified_map_maximalIdeal h π hπ⟩
  have hi : q.ramificationIdx R = 1 := Ideal.ramificationIdx_eq_one q R
  have hc := Ideal.card_inertia_eq_ramificationIdxIn (G := G) p q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p q G, hi, Subgroup.card_eq_one] at hc
  letI := (residueMap F K).toAlgebra
  let act : Gal(K/F) →* Gal(residue K / residue F) := residueCoefficientAction (F := F) (L := K)
  change Function.Bijective act
  constructor
  · apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_antisymm _ bot_le
    intro σ hs
    rw [← hc, Ideal.mem_inertia]
    intro x
    have hs' : act σ = 1 := hs
    have hdiff : IsLocalRing.residue S (integerCoefficient σ x - x) = 0 := by
      rw [map_sub]
      apply sub_eq_zero.mpr
      exact DFunLike.congr_fun hs' (IsLocalRing.residue S x)
    exact (IsLocalRing.residue_eq_zero_iff _).mp hdiff
  · intro g
    let g' : (S ⧸ q) ≃ₐ[R ⧸ p] (S ⧸ q) :=
      AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun z => g.commutes z)
    obtain ⟨s, hs⟩ := Ideal.Quotient.stabilizerHom_surjective G p q g'
    refine ⟨s, ?_⟩
    apply AlgEquiv.ext
    intro z
    obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
    exact DFunLike.congr_fun hs (IsLocalRing.residue S w)

section TransportToScalingField

variable {L : Type u} [Field L] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  [FiniteDimensional K L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension F L] [ValuativeExtension K L]

omit [FiniteDimensional F K] [IsGalois F K] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
private theorem residueMap_comp_apply (z : residue F) :
    residueMap K L (residueMap F K z) = residueMap F L z := by
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective z
  change IsLocalRing.residue O(L) (algebraMap O(K) O(L) (algebraMap O(F) O(K) z)) =
    IsLocalRing.residue O(L) (algebraMap O(F) O(L) z)
  apply congrArg (IsLocalRing.residue O(L))
  apply Subtype.ext
  exact (IsScalarTower.algebraMap_apply F K L (z : F)).symm

/-- The lifted action gives the full residue Galois group when the scaling
extension has unchanged residue field. -/
theorem scalingResidueAction_bijective
    (h : IsUnramifiedLocalExtension F K) (d : ℕ) (π : Fˣ)
    (hπ : normalizedValuation F (π : F) = exp (-1 : ℤ))
    (r : AdjoinRoot (Specs.ExceptionalSplitParahoricDescent.uniformizerPolynomial (K := K) d π)
      ≃ₐ[K] L)
    (hr : Function.Bijective (residueMap K L)) :
    letI := (residueMap F L).toAlgebra
    Function.Bijective (scalingResidueAction d π r) := by
  letI := (residueMap F K).toAlgebra
  letI := (residueMap F L).toAlgebra
  let e : residue K ≃ₐ[residue F] residue L :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (residueMap K L) hr) residueMap_comp_apply
  let c : Gal(residue K / residue F) ≃ Gal(residue L / residue F) :=
    { toFun := fun σ => e.symm.trans (σ.trans e)
      invFun := fun σ => e.trans (σ.trans e.symm)
      left_inv := by intro σ; apply AlgEquiv.ext; intro z; simp
      right_inv := by intro σ; apply AlgEquiv.ext; intro z; simp }
  have hc : (scalingResidueAction d π r : Gal(K/F) → Gal(residue L / residue F)) =
      c ∘ residueCoefficientAction := by
    funext σ
    apply AlgEquiv.ext
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    change scalingResidueAction d π r σ (residueMap K L w) =
      e (residueCoefficientAction σ (e.symm (e w)))
    rw [e.symm_apply_apply]
    exact scalingResidueAction_restrict d π r σ w
  rw [hc]
  exact c.bijective.comp (unramified_residueCoefficientAction_bijective h π hπ)

end TransportToScalingField


end UnramifiedResidueCoefficients


section FixedFace

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model)
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)

variable {K G W V : Type u} {J : Type v} [Field K] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {D : BasedRootDatum.{u}} {M : Model D} [Group G] [Group W]
  {j : G →* FieldPoints M K} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}
  {C : LocalComparison (j := j) (Wf := W) A p}
  {B : Building C} {Q : C.TypeQuotient}
  {Γ : Type u} [Group Γ] {ρ : Γ →* MulAut G} {h : Γ → V ≃ᵃ[ℚ] V}

private theorem realAffine_rationalPoint (r : RealCoordinates V) (e : V ≃ᵃ[ℚ] V) (x : V) :
    realAffine r r e (rationalPoint r x) = rationalPoint r (e x) := by
  have he : e x = e.linear x + e 0 := by simpa using e.map_vadd (0 : V) x
  simp only [Specs.ExceptionalRealAlcove.realAffine, Specs.ExceptionalRealAlcove.rationalPoint,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]
  rw [he, TensorProduct.tmul_add]
  rfl

private theorem rationalPoint_injective (r : RealCoordinates V) :
    Function.Injective (rationalPoint r) :=
  r.injective.comp (Module.Flat.tensorProduct_mk_injective (R := ℚ) (S := ℝ) (M := V))

private theorem lift_one_iwahori (B : Building C) : (C.lift 1 : G) ∈ C.I := by
  have hk : C.lift 1 ∈ C.affine.ker := by simp [C.lift_label]
  have ht : (C.lift 1 : G) ∈ C.T₀ := by
    exact (congrArg (fun H : Subgroup G => (C.lift 1 : G) ∈ H) C.kernel).mp
      ⟨C.lift 1, hk, rfl⟩
  exact ((congrArg (fun H : Subgroup G => (C.lift 1 : G) ∈ H)
    B.iwahori_inter_normalizer).mpr ht).1

private theorem chart_place_at_chamber (g : C.G₀) (t : Weights (A.SimpleWall p)) :
    B.realization.chart g (simplexPoint B.realization.coordinates B.realization.vertex t) =
      B.realization.place g t := by
  have hchart := B.realization.chart_place g 1 t
  have hr (x) :
      realAffine B.realization.coordinates B.realization.coordinates
        ((1 : A.affineWeylGroup).val) x = x := by
    simp [Specs.ExceptionalRealAlcove.realAffine, AffineEquiv.one_def]
  rw [hr] at hchart
  rw [hchart]
  apply (B.realization.place_eq _ _ _ _).2
  have hi : (C.lift 1 : G) ∈ parahoric C (cotype t) :=
    Subgroup.subset_closure (Or.inl (lift_one_iwahori B))
  exact ⟨rfl, by simpa [mul_inv_rev, mul_assoc] using (parahoric C (cotype t)).inv_mem hi⟩

private theorem adjoint_place (ad : AdjointAction B Q) (g k : C.G₀)
    (t : Weights (A.SimpleWall p)) :
    ad.action (g : G) (B.realization.place k t) = B.realization.place (g * k) t := by
  rw [← chart_place_at_chamber k t, ad.restrict, B.realization.translate_chart, chart_place_at_chamber]

private theorem translate_chamber (ad : AdjointAction B Q) (g k : C.G₀) :
    ad.action (g : G) '' B.realization.closedFace k ∅ = B.realization.closedFace (g * k) ∅ := by
  simp only [Realization.closedFace, Set.image_image]
  exact Set.image_congr (fun t _ => adjoint_place ad g k t)

private def permuteWeights {S : Type*} (e : Equiv.Perm S) (t : Weights S) : Weights S :=
  ⟨t.val ∘ e.symm, fun i => t.property.1 (e.symm i), by
    rw [show (∑ᶠ i, (t.val ∘ e.symm) i) = ∑ᶠ i, t.val i from finsum_comp_equiv e.symm]
    exact t.property.2⟩

private theorem coefficient_chamber (coef : CoefficientAction B ρ h) (σ : Γ)
    (k k' : C.G₀) (hk : (k' : G) = ρ σ (k : G)) :
    coef.action σ '' B.realization.closedFace k ∅ = B.realization.closedFace k' ∅ := by
  simp only [Realization.closedFace, Set.image_image, Set.empty_subset, Set.ofPred_true]
  apply Set.Subset.antisymm
  · rintro _ ⟨t, _, rfl⟩
    refine ⟨permuteWeights (coef.types σ) t, Set.mem_univ _, ?_⟩
    symm
    apply coef.place_action σ k k' hk t (permuteWeights (coef.types σ) t)
    intro i
    exact congrArg t.val ((coef.types σ).symm_apply_apply i)
  · rintro _ ⟨s, _, rfl⟩
    exact ⟨permuteWeights (coef.types σ).symm s, Set.mem_univ _,
      coef.place_action σ k k' hk _ _ (fun _ => rfl)⟩

/-- The twisted action preserves the actual face parahoric. -/
theorem twisted_parahoric_mem (ad : AdjointAction B Q) (coef : CoefficientAction B ρ h)
    (hauto : ∀ σ, AutomorphismComparison C (ρ σ) (h σ))
    (hcoef : ∀ σ g z, coef.action σ (ad.action g z) = ad.action (ρ σ g) (coef.action σ z))
    (a : Γ → G) (t : Weights (A.SimpleWall p))
    (hfix : ∀ σ, ad.action (a σ) (coef.action σ (B.realization.place 1 t)) =
      B.realization.place 1 t) (σ : Γ) (g : parahoric C (cotype t)) :
    a σ * ρ σ (g : G) * (a σ)⁻¹ ∈ parahoric C (cotype t) := by
  let z := B.realization.place 1 t
  have gfix : ad.action (g : G) z = z := by
    let k : C.G₀ := ⟨g, B.realization.face_mem _ g.property⟩
    rw [show (g : G) = (k : G) from rfl, ad.restrict]
    exact (B.stabilizer _ t rfl k).2 g.property
  have hconj : ad.action (a σ * ρ σ (g : G) * (a σ)⁻¹) z = z := by
    rw [map_mul, map_mul, map_inv]
    change ad.action (a σ) (ad.action (ρ σ (g : G)) ((ad.action (a σ)).symm z)) = z
    have he : (ad.action (a σ)).symm z = coef.action σ z :=
      ((ad.action (a σ)).symm_apply_eq).2 (hfix σ).symm
    rw [he, ← hcoef, gfix, hfix]
  letI := Q.normal
  have hmem : ρ σ (g : G) ∈ C.G₀ := by
    rw [← (hauto σ).2.2.2.1]
    exact ⟨g, B.realization.face_mem _ g.property, rfl⟩
  have hnormal : a σ * ρ σ (g : G) * (a σ)⁻¹ ∈ C.G₀ :=
    Subgroup.Normal.conj_mem inferInstance _ hmem _
  let k : C.G₀ := ⟨_, hnormal⟩
  exact (B.stabilizer _ t rfl k).1 (by simpa only [← ad.restrict] using hconj)

private theorem length_zero_lift_mem (Q : C.TypeQuotient)
    (ω : alcoveStabilizer A (A.alcove p)) :
    (Q.lift ω : G) ∈ lengthZeroNormalizer C :=
  ⟨Q.lift ω, ⟨ω, ω.property, (Q.affine_lift ω).symm⟩, rfl⟩

private theorem standard_point_in_chamber (t : Weights (A.SimpleWall p)) :
    B.realization.place 1 t ∈ B.realization.closedFace 1 ∅ :=
  ⟨t, Set.empty_subset _, rfl⟩

/-- Remove the actual length-zero lift of the type change. The remaining element
belongs to the parahoric, and the length-zero and coefficient operators together
fix the marked apartment point. -/
theorem twisted_stabilizer_factorization (ad : AdjointAction B Q)
    (coef : CoefficientAction B ρ h) (a : Γ → G) (t : Weights (A.SimpleWall p))
    (hfix : ∀ σ, ad.action (a σ) (coef.action σ (B.realization.place 1 t)) =
      B.realization.place 1 t) (σ : Γ) :
    ∃ b : parahoric C (cotype t),
      let ω := typeChange Q (a σ)
      a σ = (b : G) * (Q.lift ω : G) ∧
      realAffine B.realization.coordinates B.realization.coordinates ω.val.val
        (realAffine B.realization.coordinates B.realization.coordinates (h σ)
          (simplexPoint B.realization.coordinates B.realization.vertex t)) =
        simplexPoint B.realization.coordinates B.realization.vertex t := by
  let ω := typeChange Q (a σ)
  let n := Q.lift ω
  let z := B.realization.place 1 t
  letI := Q.normal
  have htype : typeChange Q (n : G) = ω := Q.quotient_lift ω
  have hg₀ : a σ * (n : G)⁻¹ ∈ C.G₀ := by
    have htype' : typeChange Q (a σ * (n : G)⁻¹) = 1 := by
      rw [map_mul, map_inv, htype, mul_inv_cancel]
    change Q.quotient (QuotientGroup.mk (a σ * (n : G)⁻¹)) = 1 at htype'
    rw [← map_one Q.quotient, Q.quotient.injective.eq_iff, QuotientGroup.eq_one_iff] at htype'
    exact htype'
  let g : C.G₀ := ⟨a σ * (n : G)⁻¹, hg₀⟩
  have hgn : (g : G) * (n : G) = a σ := by
    dsimp [g]
    group
  have hn : ad.action (n : G) '' B.realization.closedFace 1 ∅ =
      B.realization.closedFace 1 ∅ :=
    (ad.chamber_stabilizer _).2 <|
      (le_sup_right : lengthZeroNormalizer C ≤ C.I ⊔ lengthZeroNormalizer C)
        (length_zero_lift_mem Q ω)
  have hncoef : ad.action (n : G) (coef.action σ z) ∈ B.realization.closedFace 1 ∅ := by
    have hc : coef.action σ z ∈ B.realization.closedFace 1 ∅ := by
      rw [← coefficient_chamber coef σ 1 1 (by simp)]
      exact Set.mem_image_of_mem _ (standard_point_in_chamber t)
    rw [← hn]
    exact Set.mem_image_of_mem _ hc
  obtain ⟨s, _, hs⟩ := hncoef
  have hplace : B.realization.place g s = B.realization.place 1 t := by
    have hp := adjoint_place ad g 1 s
    rw [mul_one, hs] at hp
    rw [← hp]
    have hh := hfix σ
    rw [← hgn, map_mul] at hh
    exact hh
  obtain ⟨hst, hstabilizer⟩ := (B.realization.place_eq g 1 s t).1 hplace
  subst s
  have hg : (g : G) ∈ parahoric C (cotype t) := by
    simpa using (parahoric C (cotype t)).inv_mem hstabilizer
  refine ⟨⟨g, hg⟩, hgn.symm, ?_⟩
  apply (B.realization.chart_isometry 1).injective
  rw [← Q.affine_lift, ← ad.chart_normalizer, ← coef.chart σ 1 1 (by simp),
    chart_place_at_chamber]
  exact hs.symm

/-- The normalizer part and the pinned coefficient action satisfy the
affine fixing equation in the original rational apartment. -/
theorem twisted_stabilizer_affine_equation (ad : AdjointAction B Q)
    (coef : CoefficientAction B ρ h) (a : Γ → G) (t : Weights (A.SimpleWall p))
    (hfix : ∀ σ, ad.action (a σ) (coef.action σ (B.realization.place 1 t)) =
      B.realization.place 1 t)
    (x : V) (hx : rationalPoint B.realization.coordinates x =
      simplexPoint B.realization.coordinates B.realization.vertex t) (σ : Γ) :
    ∃ b : parahoric C (cotype t),
      let ω := typeChange Q (a σ)
      a σ = (b : G) * (Q.lift ω : G) ∧ C.affine (Q.lift ω) (h σ x) = x := by
  obtain ⟨b, hprod, hpoint⟩ := twisted_stabilizer_factorization ad coef a t hfix σ
  refine ⟨b, hprod, rationalPoint_injective B.realization.coordinates ?_⟩
  rw [← hx, realAffine_rationalPoint, realAffine_rationalPoint] at hpoint
  simpa only [Q.affine_lift] using hpoint

/-- Applying the twist to a chamber uses conjugation on the parahoric and
the left factor of the image of the standard chamber. -/
theorem twisted_chamber_image (ad : AdjointAction B Q)
    (coef : CoefficientAction B ρ h) (σ : Γ) (a : G)
    (ω : alcoveStabilizer A (A.alcove p)) (b g g' : C.G₀)
    (hb : a = (b : G) * (Q.lift ω : G))
    (hρg : ρ σ (g : G) ∈ C.G₀)
    (hg' : (g' : G) = (a * ρ σ (g : G) * a⁻¹) * b) :
    ad.action a '' (coef.action σ '' B.realization.closedFace g ∅) =
      B.realization.closedFace g' ∅ := by
  let k : C.G₀ := ⟨ρ σ (g : G), hρg⟩
  have hn : ad.action (Q.lift ω : G) '' B.realization.closedFace 1 ∅ =
      B.realization.closedFace 1 ∅ :=
    (ad.chamber_stabilizer _).2 <|
      (le_sup_right : lengthZeroNormalizer C ≤ C.I ⊔ lengthZeroNormalizer C)
        (length_zero_lift_mem Q ω)
  have hk := translate_chamber ad k 1
  rw [mul_one] at hk
  rw [coefficient_chamber coef σ g k rfl, ← hk, Set.image_image]
  change (⇑(ad.action a * ad.action (k : G))) '' _ = _
  rw [← map_mul]
  have he : a * (k : G) = (g' : G) * (Q.lift ω : G) := by
    rw [hg']
    change a * ρ σ (g : G) = a * ρ σ (g : G) * a⁻¹ * (b : G) * (Q.lift ω : G)
    rw [mul_assoc _ (b : G), ← hb]
    group
  rw [he, map_mul]
  change (⇑(ad.action (g' : G)) ∘ ⇑(ad.action (Q.lift ω : G))) '' _ = _
  calc
    _ = ad.action (g' : G) '' (ad.action (Q.lift ω : G) '' B.realization.closedFace 1 ∅) :=
      (Set.image_image _ _ _).symm
    _ = _ := by rw [hn, translate_chamber, mul_one]

end FixedFace

section TorusScaling

/-- Clearing the common denominator in the combined affine fixing equation
gives the character exponent in the scaled normalizer. -/
theorem scaled_character_exponent {Y : Type u} [AddCommGroup Y]
    (w δ : Y →ₗ[ℤ] Y) (χ : Y →ₗ[ℤ] ℤ)
    (x : ℚ ⊗[ℤ] Y) (d : ℕ) (y z : Y)
    (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hfix : w.baseChange ℚ (δ.baseChange ℚ x) + (1 : ℚ) ⊗ₜ[ℤ] z = x) :
    χ y - χ (w (δ y)) = (d : ℤ) * χ z := by
  have hsmul : (d : ℚ) • ((1 : ℚ) ⊗ₜ[ℤ] z) = (1 : ℚ) ⊗ₜ[ℤ] ((d : ℤ) • z) := by
    rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul]
    simp
  have ht : (1 : ℚ) ⊗ₜ[ℤ] y =
      (1 : ℚ) ⊗ₜ[ℤ] (w (δ y)) + (1 : ℚ) ⊗ₜ[ℤ] ((d : ℤ) • z) := by
    calc
      _ = (d : ℚ) • x := hy.symm
      _ = (d : ℚ) • (w.baseChange ℚ (δ.baseChange ℚ x) + (1 : ℚ) ⊗ₜ[ℤ] z) :=
        congrArg ((d : ℚ) • ·) hfix.symm
      _ = _ := by rw [smul_add, ← map_smul, ← map_smul, hy, hsmul,
        LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
  have he := congrArg (fun v => (TensorProduct.AlgebraTensorModule.rid ℤ ℚ ℚ)
     (χ.baseChange ℚ v)) ht
  simp only [map_add, LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.rid_tmul,
    mul_one, map_zsmul, zsmul_eq_mul] at he
  have hi : χ y = χ (w (δ y)) + (d : ℤ) * χ z := by exact_mod_cast he
  omega

open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open WithZero

/-- The logarithmic valuation of the corrected torus coordinate vanishes. -/
theorem scaled_character_valuation {L : Type u} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (ξ t : Lˣ) (d : ℕ) (c m v : ℤ)
    (hξ : normalizedValuation L (ξ : L) = exp (-c))
    (ht : normalizedValuation L (t : L) = exp ((d : ℤ) * c * v))
    (hm : m = (d : ℤ) * v) :
    normalizedValuation L ((ξ : L) ^ m * (t : L)) = 1 := by
  have hexp : (exp (-c) : ℤᵐ⁰) ^ m = exp (m * -c) := by
    change (((↑(Multiplicative.ofAdd (-c))) : ℤᵐ⁰) ^ m) =
      ↑(Multiplicative.ofAdd (m * -c))
    rw [← WithZero.coe_zpow]
    rfl
  rw [map_mul, map_zpow₀, hξ, ht, hexp, ← exp_add]
  have he : m * -c + (d : ℤ) * c * v = 0 := by rw [hm]; ring
  rw [he, exp_zero]

/-- On every test ring, the integral correction by a multiple of the
denominator disappears on the scheme of roots of unity. -/
theorem scaled_cocharacters_on_mu {D : Specs.Pinning.BasedRootDatum.{u}}
    (w δ : D.Y →ₗ[ℤ] D.Y) (x : ℚ ⊗[ℤ] D.Y) (d : ℕ) (y z : D.Y)
    (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hfix : w.baseChange ℚ (δ.baseChange ℚ x) + (1 : ℚ) ⊗ₜ[ℤ] z = x)
    (R : Specs.IntegralSemisimpleModel.IntegralAlgebra.{u}) (s : Rˣ) (hs : s ^ d = 1) :
    Specs.IntegralSemisimpleModel.cocharacter D y R s =
      Specs.IntegralSemisimpleModel.cocharacter D (w (δ y)) R s := by
  apply MonoidHom.ext
  intro χ
  let f := D.datum.toLinearMap (Multiplicative.toAdd χ)
  change s ^ f y = s ^ f (w (δ y))
  have hm := scaled_character_exponent w δ f x d y z hy hfix
  have he : f y = (d : ℤ) * f z + f (w (δ y)) := by omega
  rw [he, zpow_add, zpow_mul, zpow_natCast, hs, one_zpow, one_mul]

end TorusScaling

section IncidentFlags

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover)
open Specs.ExceptionalLocalRootCoordinates (residueMap)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)

variable {F K L : Type u} [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  [FiniteDimensional F K] [IsGalois F K] [FiniteDimensional K L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [ValuativeExtension F L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {B : SplitBuildingLevel Y}
  {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')}
  {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} {y : E.Y} {π : Kˣ} {ξ : Lˣ}
  {R : FaceReduction B t x d y π L ξ}
  {ρ : Gal(K/F) →* MulAut (FieldPoints M' K)}
  {h : Gal(K/F) → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {coef : CoefficientAction B.ad ρ h} {a : Gal(K/F) → FieldPoints M' K}

omit [FiniteDimensional F K] [IsGalois F K] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [ValuativeExtension F K] in
/-- For the marked normalizer lift, the combined affine fixing equation
identifies the cocharacters on the whole roots-of-unity functor. -/
theorem marked_scaled_cocharacters_on_mu
    (C : MarkedFibre M' F)
    (l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned)
    (ω : Gal(K/F) →* Aut C.realization.attached.toBased)
    (hmarked : MarkedCoefficientAction C l ω ρ h)
    (hfix : ∀ σ, B.adjoint.action (a σ) (coef.action σ (B.ad.realization.place 1 t)) =
      B.ad.realization.place 1 t)
    (hx : rationalPoint B.ad.realization.coordinates x =
      simplexPoint B.ad.realization.coordinates B.ad.realization.vertex t)
    (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    (σ : Gal(K/F)) :
    ∃ b : parahoric Y.ad (cotype t),
      let n := Y.typeQuotient.lift (typeChange Y.typeQuotient (a σ))
      let N := Y.ad.localIwahori.normalizer
      let w := (N.label n).val.coweightEquiv.symm
      let δ := (Specs.ExceptionalValuedTorusNormalizer.markedDiagramEquiv C.realization
        (ω σ)).asIso.hom.val.coweightEquiv.symm
      a σ = (b : FieldPoints M' K) * (n : FieldPoints M' K) ∧
      ∀ (S : Specs.IntegralSemisimpleModel.IntegralAlgebra.{u}) (s : Sˣ), s ^ d = 1 →
        Specs.IntegralSemisimpleModel.cocharacter E y S s =
          Specs.IntegralSemisimpleModel.cocharacter E (w (δ y)) S s := by
  let n := Y.typeQuotient.lift (typeChange Y.typeQuotient (a σ))
  let N := Y.ad.localIwahori.normalizer
  let w := (N.label n).val.coweightEquiv.symm
  let δ := (Specs.ExceptionalValuedTorusNormalizer.markedDiagramEquiv C.realization
    (ω σ)).asIso.hom.val.coweightEquiv.symm
  let z := (N.translation (N.torusPart n)).toAdd
  obtain ⟨b, hb, hpoint⟩ := twisted_stabilizer_affine_equation
    B.adjoint coef a t hfix x hx σ
  have heq : w.toLinearMap.baseChange ℚ (δ.toLinearMap.baseChange ℚ x) +
      (1 : ℚ) ⊗ₜ[ℤ] z = x := by
    change Y.ad.affine n (h σ x) = x at hpoint
    rw [Y.ad_points.2.2.2.2.2.2.1 n, hmarked.2.1 σ] at hpoint
    exact hpoint
  exact ⟨b, hb, scaled_cocharacters_on_mu w.toLinearMap δ.toLinearMap x d y z hy heq⟩

open WithZero
open Specs.ExceptionalLocalRootCoordinates (normalizedValuation)
open Specs.ExceptionalIwahoriCongruence (integralRing)
open Specs.IntegralSemisimpleModel (TorusValues cocharacter torusPoint)

omit [Algebra F L] [IsScalarTower F K L] [FiniteDimensional F K] [IsGalois F K]
  [FiniteDimensional K L] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeExtension F K] [ValuativeExtension F L] in
/-- In the split normalizer coordinates, the torus part after correction by the
two scaling cocharacters has valuation one in every character. -/
theorem marked_scaled_torus_valuation
    (C : MarkedFibre M' F)
    (l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned)
    (ω : Gal(K/F) →* Aut C.realization.attached.toBased)
    (hmarked : MarkedCoefficientAction C l ω ρ h)
    (hfix : ∀ σ, B.adjoint.action (a σ) (coef.action σ (B.ad.realization.place 1 t)) =
      B.ad.realization.place 1 t)
    (hx : rationalPoint B.ad.realization.coordinates x =
      simplexPoint B.ad.realization.coordinates B.ad.realization.vertex t)
    (hd : 0 < d) (hy : (d : ℚ) • x = (1 : ℚ) ⊗ₜ[ℤ] y)
    (hπ : normalizedValuation K (π : K) = exp (-1 : ℤ))
    (hroot : (ξ : L) ^ d = algebraMap K L (π : K))
    (σ : Gal(K/F)) :
    ∃ (b : parahoric Y.ad (cotype t)) (v : TorusValues E (integralRing K)),
      let n := Y.typeQuotient.lift (typeChange Y.typeQuotient (a σ))
      let N := Y.ad.localIwahori.normalizer
      let w := (N.label n).val.coweightEquiv.symm
      let δ := (Specs.ExceptionalValuedTorusNormalizer.markedDiagramEquiv C.realization
        (ω σ)).asIso.hom.val.coweightEquiv.symm
      a σ = (b : FieldPoints M' K) * (n : FieldPoints M' K) ∧
      (N.torusPart n : FieldPoints M' K) =
        torusPoint E (integralRing K) v ≫ M'.torus.hom.hom ∧
      ∀ χ : E.X,
        let f := E.datum.toLinearMap χ
        normalizedValuation L
          ((ξ : L) ^ (f y - f (w (δ y))) *
            algebraMap K L (v (Multiplicative.ofAdd χ) : K)) = 1 := by
  let n := Y.typeQuotient.lift (typeChange Y.typeQuotient (a σ))
  let N := Y.ad.localIwahori.normalizer
  let w := (N.label n).val.coweightEquiv.symm
  let δ := (Specs.ExceptionalValuedTorusNormalizer.markedDiagramEquiv C.realization
    (ω σ)).asIso.hom.val.coweightEquiv.symm
  let z := (N.translation (N.torusPart n)).toAdd
  obtain ⟨b, hb, hpoint⟩ := twisted_stabilizer_affine_equation
    B.adjoint coef a t hfix x hx σ
  have heq : w.toLinearMap.baseChange ℚ (δ.toLinearMap.baseChange ℚ x) +
      (1 : ℚ) ⊗ₜ[ℤ] z = x := by
    change Y.ad.affine n (h σ x) = x at hpoint
    rw [Y.ad_points.2.2.2.2.2.2.1 n, hmarked.2.1 σ] at hpoint
    exact hpoint
  obtain ⟨v, hv⟩ := (N.torusPoints (N.torusPart n)).1 (N.torusPart n).property
  obtain ⟨c, _, hξv, hval⟩ := scaled_uniformizer_values hd hπ hroot
  refine ⟨b, v, hb, hv, fun χ => ?_⟩
  let f := E.datum.toLinearMap χ
  have hlog := N.characterLog (N.torusPart n) v hv χ
  have hpow := scaled_character_exponent w.toLinearMap δ.toLinearMap f x d y z hy heq
  let u := Units.map (algebraMap K L).toMonoidHom (v (Multiplicative.ofAdd χ))
  have hu : normalizedValuation L (u : L) = exp ((d : ℤ) * c * f z) := by
    change normalizedValuation L (algebraMap K L (v (Multiplicative.ofAdd χ) : K)) = _
    rw [hval _ (v (Multiplicative.ofAdd χ)).ne_zero]
    change f z = log (normalizedValuation K (v (Multiplicative.ofAdd χ) : K)) at hlog
    rw [hlog]
  exact scaled_character_valuation ξ u d c (f y - f (w (δ y))) (f z) hξv hu hpow

private theorem rationalFlag_fixed {k k' : Type u} [Field k] [Field k'] [Algebra k k']
    {X : SchemeOver k} (σ : Gal(k'/k)) (f : Points X (CommAlgCat.of k k)) :
    let f' := mapPoints (CommAlgCat.ofHom (Algebra.ofId k k')) f
    mapPoints (CommAlgCat.ofHom σ.toAlgHom) f' = f' := by
  dsimp only []
  have hcomp : CommAlgCat.ofHom (Algebra.ofId k k') ≫ CommAlgCat.ofHom σ.toAlgHom =
      CommAlgCat.ofHom (Algebra.ofId k k') :=
    CommAlgCat.hom_ext (AlgHom.ext (fun z => σ.commutes z))
  change (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op ≫
    (testSpec k).map (CommAlgCat.ofHom (Algebra.ofId k k')).op ≫ f = _
  rw [← Category.assoc, ← Functor.map_comp, ← CategoryTheory.op_comp, hcomp]

private theorem incident_of_face_point (g : Y.ad.G₀)
    (hg : B.ad.realization.place 1 t ∈ B.ad.realization.closedFace g ∅) :
    (QuotientGroup.mk (g : FieldPoints M' K) : FieldPoints M' K ⧸ Y.ad.I) ∈
      IncidentChambers B (B.ad.realization.place 1 t) := by
  obtain ⟨s, _, hs⟩ := hg
  exact ⟨g, s, rfl, hs⟩

private theorem face_point_of_incident (q : IncidentChambers B (B.ad.realization.place 1 t)) :
    ∃ g : Y.ad.G₀, q.val = QuotientGroup.mk (g : FieldPoints M' K) ∧
      B.ad.realization.place 1 t ∈ B.ad.realization.closedFace g ∅ := by
  obtain ⟨g, s, hq, hs⟩ := q.property
  exact ⟨g, hq, s, Set.empty_subset _, hs⟩

/-- Every rational flag for the descended comparison gives an incident chamber
fixed by the twisted action. -/
theorem lift_rationalFlag (S : DescendedFaceResidue R coef a)
    (hauto : ∀ σ, AutomorphismComparison Y.ad (ρ σ) (h σ))
    (hfix : ∀ σ, B.adjoint.action (a σ) (coef.action σ (B.ad.realization.place 1 t)) =
      B.ad.realization.place 1 t)
    (f : Points S.flags.scheme (CommAlgCat.of (residue F) (residue F))) :
    ∃ (q : IncidentChambers B (B.ad.realization.place 1 t)) (g : Y.ad.G₀),
      IsLiftOfFlag S f q ∧ q.val = QuotientGroup.mk (g : FieldPoints M' K) ∧
      ∀ σ, B.adjoint.action (a σ) '' (coef.action σ '' B.ad.realization.closedFace g ∅) =
        B.ad.realization.closedFace g ∅ := by
  letI := (residueMap F L).toAlgebra
  let k := residue F
  let k' := residue L
  let E := baseChangePointsEquiv k' S.flags.scheme (CommAlgCat.of k' k')
  let f' := mapPoints (CommAlgCat.ofHom (Algebra.ofId k k')) f
  let q := R.incident.symm (E.symm f' ≫ S.flagComparison.hom)
  have hq : IsLiftOfFlag S f q := by
    change E (R.incident q ≫ S.flagComparison.inv) = f'
    simp [q]
  obtain ⟨g, hqg, hg⟩ := face_point_of_incident q
  refine ⟨q, g, hq, hqg, fun σ => ?_⟩
  obtain ⟨b, hb, _⟩ := twisted_stabilizer_factorization B.adjoint coef a t hfix σ
  have hpg : (g : FieldPoints M' K) ∈ parahoric Y.ad (cotype t) := by
    obtain ⟨s, _, hs⟩ := hg
    obtain ⟨hst, hm⟩ := (B.ad.realization.place_eq g 1 s t).1 hs
    subst s
    simpa using (parahoric Y.ad (cotype t)).inv_mem hm
  let gₚ : parahoric Y.ad (cotype t) := ⟨g, hpg⟩
  let b₀ : Y.ad.G₀ := ⟨b, B.ad.realization.face_mem _ b.property⟩
  let g' : Y.ad.G₀ := ⟨_, B.ad.realization.face_mem _ (
    (parahoric Y.ad (cotype t)).mul_mem (S.parahoricInvariant σ gₚ) b.property)⟩
  have hρg : ρ σ (g : FieldPoints M' K) ∈ Y.ad.G₀ := by
    exact (congrArg (fun H => ρ σ (g : FieldPoints M' K) ∈ H) (hauto σ).2.2.2.1).mp
      ⟨g, g.property, rfl⟩
  have hi := twisted_chamber_image B.adjoint coef σ (a σ) (typeChange Y.typeQuotient (a σ))
    b₀ g g' hb hρg rfl
  have hg' : B.ad.realization.place 1 t ∈ B.ad.realization.closedFace g' ∅ := by
    rw [← hi, ← hfix σ]
    exact Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hg)
  let q' : IncidentChambers B (B.ad.realization.place 1 t) :=
    ⟨QuotientGroup.mk (g' : FieldPoints M' K), incident_of_face_point g' hg'⟩
  have hq' : E (R.incident q' ≫ S.flagComparison.inv) =
      mapPoints (CommAlgCat.ofHom (S.residueAction σ).toAlgHom)
        (E (R.incident q ≫ S.flagComparison.inv)) :=
    S.semilinear_flags σ q q' g g' hqg rfl hi
  change E (R.incident q ≫ S.flagComparison.inv) = f' at hq
  rw [hq, rationalFlag_fixed] at hq'
  have hqeq : q' = q := by
    apply R.incident.injective
    have he := E.injective (hq'.trans hq.symm)
    have he' := congrArg (· ≫ S.flagComparison.hom) he
    simpa using he'
  have hcoset : (QuotientGroup.mk (g' : FieldPoints M' K) : FieldPoints M' K ⧸ Y.ad.I) =
      QuotientGroup.mk (g : FieldPoints M' K) := congrArg Subtype.val hqeq |>.trans hqg
  have hI : (g' : FieldPoints M' K)⁻¹ * (g : FieldPoints M' K) ∈ Y.ad.I :=
    QuotientGroup.eq.mp hcoset
  refine hi.trans ?_
  simp only [Realization.closedFace]
  apply Set.image_congr
  intro s _
  exact (B.ad.realization.place_eq g' g s s).2
    ⟨rfl, Subgroup.subset_closure (Or.inl hI)⟩

end IncidentFlags

section IntegralPinning

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra fibre forgetFibrePoint)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint integralTestAlgebra)
open Specs.ExceptionalIwahoriCongruence (integralRing integralRingMap changeRingHom)
open Specs.ExceptionalIwahoriImageComparison (integralPointHom)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv)
open Specs.ExceptionalScaledParahoricAction (PinnedOperators coefficientPoint)

attribute [local instance] integerAlgebra

open private pinnedFieldLift_unique from LinearAlgebraicGroups.Arithmetic.IntegralPinnedAutomorphisms
open private forgetFibrePoint_comp from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel
open private fibrePointEquiv from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent

set_option backward.isDefEq.respectTransparency false in
private theorem pinnedOperator_exists
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    {E : BasedRootDatum.{u}} {M : Model E} (C : MarkedFibre M F)
    (l : Aut C.realization.attached.toBased ≃* Aut C.realization.pinned)
    (ω : Gal(K/F) →* Aut C.realization.attached.toBased)
    {ρ : Gal(K/F) →* MulAut (FieldPoints M K)}
    {h : Gal(K/F) → (ℚ ⊗[ℤ] E.Y) ≃ᵃ[ℚ] (ℚ ⊗[ℤ] E.Y)}
    (hmarked : MarkedCoefficientAction C l ω ρ h) :
    ∃ δ : PinnedOperators ρ h,
      ∀ σ, δ.diagram σ = (markedDiagramEquiv C.realization (ω σ)).asIso.hom.val := by
  obtain ⟨lift, hlift, _, hone, hmul⟩ := IntegralPinnedAutomorphisms.integralPinnedAutomorphisms E M
  let τ := (markedDiagramEquiv C.realization).toMonoidHom.comp ω
  let δ : Gal(K/F) →* Aut M.group :=
    { toFun := fun σ => Aut.of (lift (τ σ).asIso.hom)
      map_one' := by
        rw [map_one]
        exact congrArg Aut.of hone
      map_mul' := by
        intro σ τ'
        rw [map_mul]
        exact congrArg Aut.of (hmul (τ τ').asIso.hom (τ σ).asIso.hom) }
  refine ⟨{ diagram := fun σ => (τ σ).asIso.hom.val
            pinned := δ
            h_eq := hmarked.2.1
            torus_formula := fun σ => (hlift (τ σ).asIso.hom).1.1
            root_formula := ?_
            generic_eq := ?_ }, fun _ => rfl⟩
  · intro σ i
    obtain ⟨units, hu⟩ := (hlift (τ σ).asIso.hom).2.1
    exact ⟨units i, hu i⟩
  · intro σ g
    obtain ⟨g₀, h₀, hf⟩ := (hlift (τ σ).asIso.hom).2.2 F (pinnedFibreMarking C)
    have he := pinnedFieldLift_unique (pinnedFibreMarking C) (τ σ).asIso.hom
      g₀ (l (ω σ)).asIso.hom h₀ (hmarked.2.2 σ)
    subst g₀
    obtain ⟨e, he⟩ := ExceptionalMarkedRootDescent.markedFibrePointComparison C
    let T := CommAlgCat.of F K
    let f := CommAlgCat.ofHom σ.toAlgHom
    obtain ⟨v, hv⟩ := (fibrePointEquiv C T).surjective g
    change markedFibrePoint C T v = g at hv
    rw [← hv, hmarked.1]
    have hc : changeRingHom M.group (integralRingMap σ.toRingHom) (markedFibrePoint C T v) =
        markedFibrePoint C T (mapPoints f v) := by
      rw [← he, ← he]
      exact (ConcreteCategory.congr_hom (e.hom.naturality f) v).symm
    change integralPointHom (lift (τ σ).asIso.hom).hom (integralRing K)
        (changeRingHom M.group (integralRingMap σ.toRingHom) (markedFibrePoint C T v)) = _
    rw [hc]
    let P := (l (ω σ)).asIso.hom.group
    let A := (fibre F).map (lift (τ σ).asIso.hom).hom
    change A ≫ C.groupIso.hom = C.groupIso.hom ≫ P.hom at hf
    have hi : C.groupIso.inv ≫ A = P.hom ≫ C.groupIso.inv := by
      calc
        C.groupIso.inv ≫ A = C.groupIso.inv ≫ (A ≫ C.groupIso.hom) ≫ C.groupIso.inv := by simp
        _ = P.hom ≫ C.groupIso.inv := by rw [hf]; simp [Category.assoc]
    have hcomp := congrArg (fun (α : C.realization.pinned.pair.G.val ⟶ (fibre F).obj M.group) =>
      α.hom.hom) hi
    change (forgetFibrePoint M.group T (mapPoints f v ≫ C.groupIso.inv.hom.hom)) ≫
      (lift (τ σ).asIso.hom).hom.hom.hom =
      forgetFibrePoint M.group T ((mapPoints f v ≫ P.hom.hom.hom) ≫ C.groupIso.inv.hom.hom)
    rw [← forgetFibrePoint_comp, Category.assoc, ← Grp.comp_hom_hom, hcomp, Grp.comp_hom_hom,
      ← Category.assoc]

end IntegralPinning

section ResidueScheme

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open Specs.AdjointCocharacters (coordinateHopfIso)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalSplitParahoricDescent (fieldPointIso)
open Specs.ExceptionalScaledParahoricAction (coordinatePoint transportAlgebra transportPoint)
open Specs.ResidueFlagDescent
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open _root_.LinearAlgebraicGroups.Descent (HopfDescentDatum)

set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

open private conjugationIso comp_conjugation
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {H : AffineAlgebraicGroup K} (D : HopfDescentDatum k (Specs.AdjointCocharacters.coordinateHopf H))

private theorem coordinatePoint_surjective (H : AffineAlgebraicGroup K) (T : TestAlgebra K) :
    Function.Surjective (coordinatePoint H T) := by
  intro p
  let e := coordinateHopfIso H
  let f : (testSpec K).obj (op T) ⟶
      (testSpec K).obj (op (CommAlgCat.of K (Specs.AdjointCocharacters.coordinateHopf H))) :=
    p ≫ e.inv.hom.hom
  let F := algSpec.fullyFaithful (R := CommRingCat.of K)
  let g := F.preimage f
  have hg : (testSpec K).map g = f := F.map_preimage f
  refine ⟨g.unop, ?_⟩
  change (testSpec K).map g ≫ e.hom.hom.hom = _
  rw [hg]
  change (p ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = p
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id]

private theorem transportAlgebra_over (σ : Gal(K/k)) (T : TestAlgebra K) :
    ((testSpec K).obj (op (transportAlgebra σ T))).hom =
      ((testSpec K).obj (op T)).hom ≫ scalarMap σ⁻¹ := by
  change Spec.map (CommRingCat.ofHom (σ⁻¹ : Gal(K/k)).toRingHom ≫
      CommRingCat.ofHom (algebraMap K T)) = _
  rw [Spec.map_comp]
  rfl

private theorem coordinatePoint_transport (σ : Gal(K/k)) (T : TestAlgebra K)
    (f : CommAlgCat.of K (Specs.AdjointCocharacters.coordinateHopf H) ⟶ T) :
    (coordinatePoint H (transportAlgebra σ T) (transportPoint D σ f)).left =
      (coordinatePoint H T f).left ≫ schemeOperator H D σ := by
  let e := coordinateHopfIso H
  let m := CommRingCat.ofHom (coordinateOperator D σ)
  let a := CommRingCat.ofHom f.hom.toRingHom
  change Spec.map (CommRingCat.ofHom (transportPoint D σ f).hom.toRingHom) ≫
      e.hom.hom.hom.left =
    (Spec.map a ≫ e.hom.hom.hom.left) ≫ (e.inv.hom.hom.left ≫ Spec.map m ≫ e.hom.hom.hom.left)
  have hh : e.hom.hom.hom.left ≫ e.inv.hom.hom.left = 𝟙 _ :=
    (Over.forget _).congr_map ((Grp.forget _).congr_map e.hom_inv_id)
  calc
    _ = Spec.map (m ≫ a) ≫ e.hom.hom.hom.left := rfl
    _ = _ := by simp only [Spec.map_comp, Category.assoc, reassoc_of% hh]

private theorem schemeOperator_inverse (σ : Gal(K/k)) :
    schemeOperator H D σ ≫ schemeOperator H D σ⁻¹ = 𝟙 _ := by
  let f := (Grp.forget (SchemeOver K) ⋙ Over.forget _).mapIso (coordinateHopfIso H)
  let m := CommRingCat.ofHom (coordinateOperator D σ)
  let n := CommRingCat.ofHom (coordinateOperator D σ⁻¹)
  change (f.inv ≫ Spec.map m ≫ f.hom) ≫ f.inv ≫ Spec.map n ≫ f.hom = _
  have hm : n ≫ m = 𝟙 _ := by
    ext x
    change D.action.act σ⁻¹ (D.action.act (σ⁻¹)⁻¹ x) = x
    rw [inv_inv, ← D.action.mul_act, inv_mul_cancel, D.action.one_act]
  rw [Category.assoc, Category.assoc, f.hom_inv_id_assoc, ← Category.assoc (Spec.map m),
    ← Spec.map_comp, hm, Spec.map_id, Category.id_comp, f.inv_hom_id]
  rfl

private theorem transportedSection (u : GroupPoints H.val (CommAlgCat.of K K))
    (σ : Gal(K/k)) (T : TestAlgebra K) :
    let T' := transportAlgebra σ T
    let m : CommAlgCat.of K K ⟶ T' := ConcreteCategory.ofHom
      { toRingHom := algebraMap K T', commutes' := fun _ => rfl }
    mapPoints m u = toUnit ((testSpec K).obj (op T')) ≫ ((fieldPointIso K).hom ≫ u) := by
  intro T' m
  change (testSpec K).map m.op ≫ u = _ ≫ _ ≫ u
  have h : (testSpec K).map m.op ≫ (fieldPointIso K).inv =
      toUnit ((testSpec K).obj (op T')) :=
    (isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _
  have he : (testSpec K).map m.op =
      toUnit ((testSpec K).obj (op T')) ≫ (fieldPointIso K).hom := by
    rw [← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he, Category.assoc]

private theorem movesBorel_of_points (B : ClosedSubgroup H.val) (σ : Gal(K/k))
    (u : RationalPoint H.val.X)
    (hp : ∀ (T : TestAlgebra K) (p : GroupPoints H.val T),
        (∃ b : GroupPoints B.group T, b ≫ B.inclusion.hom.hom = p) ↔
        ∃ b' : GroupPoints B.group (transportAlgebra σ T),
          (b' ≫ B.inclusion.hom.hom ≫ (conjugationIso u).hom.hom.hom).left =
            p.left ≫ schemeOperator H D σ) :
    MovesBorel D B σ u := by
  let HB : AffineAlgebraicGroup K := closedSubgroupAlgebraicGroup B
  let T := CommAlgCat.of K (Specs.AdjointCocharacters.coordinateHopf HB)
  let E := ((Grp.forget (SchemeOver K)).mapIso (coordinateHopfIso HB))
  let e := (Over.forget _).mapIso E
  let a := schemeOperator H D σ
  let a' := schemeOperator H D σ⁻¹
  have haa' : a ≫ a' = 𝟙 _ := schemeOperator_inverse D σ
  have ha'a : a' ≫ a = 𝟙 _ := by
    simpa only [inv_inv] using schemeOperator_inverse D σ⁻¹
  have ha' : a' ≫ H.val.X.hom = H.val.X.hom ≫ scalarMap σ := by
    simpa only [inv_inv] using schemeOperator_over H D σ⁻¹
  let i := B.inclusion.hom.hom
  let j := i ≫ (conjugationIso u).hom.hom.hom
  let b : GroupPoints B.group T := E.hom
  obtain ⟨p, h₁⟩ := (hp T (b ≫ i)).mp ⟨b, rfl⟩
  have hf : (e.inv ≫ p.left) ≫ j.left = i.left ≫ a := by
    change p.left ≫ j.left = (e.hom ≫ i.left) ≫ a at h₁
    rw [Category.assoc, h₁]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  let T₀ := transportAlgebra σ⁻¹ T
  let T₁ := transportAlgebra σ T₀
  have hT : ((testSpec K).obj (op T₁)).hom = ((testSpec K).obj (op T)).hom := by
    rw [transportAlgebra_over, transportAlgebra_over, inv_inv, Category.assoc,
      scalarMap_comp_inverse, Category.comp_id]
  let b' : GroupPoints B.group T₁ := Over.homMk b.left ((Over.w b).trans hT.symm)
  let p₀ : GroupPoints H.val T₀ := Over.homMk (b.left ≫ j.left ≫ a') (by
    change (b.left ≫ j.left ≫ a') ≫ H.val.X.hom = ((testSpec K).obj (op T₀)).hom
    rw [Category.assoc, Category.assoc, ha', ← Category.assoc j.left, Over.w j,
      ← Category.assoc b.left, Over.w b]
    change ((testSpec K).obj (op T)).hom ≫ scalarMap σ =
      ((testSpec K).obj (op T₀)).hom
    simpa only [inv_inv] using (transportAlgebra_over σ⁻¹ T).symm)
  have hp₀ : (b' ≫ i ≫ (conjugationIso u).hom.hom.hom).left = p₀.left ≫ a := by
    change b.left ≫ j.left = (b.left ≫ j.left ≫ a') ≫ a
    simp only [Category.assoc]
    rw [ha'a]
    simp
  obtain ⟨q, h₂⟩ := (hp T₀ p₀).mpr ⟨b', hp₀⟩
  have hq : (e.inv ≫ q.left) ≫ i.left = j.left ≫ a' := by
    have hh := congrArg Over.Hom.left h₂
    change q.left ≫ i.left = e.hom ≫ j.left ≫ a' at hh
    rw [Category.assoc, hh, e.inv_hom_id_assoc]
  haveI : IsClosedImmersion i.left := B.isClosedImmersion
  haveI : Mono i.left := inferInstance
  haveI : Mono j.left := by
    change Mono (i.left ≫ (conjugationIso u).hom.hom.hom.left)
    haveI : IsIso (conjugationIso u).hom.hom.hom.left :=
      (Grp.forget (SchemeOver K) ⋙ Over.forget _).map_isIso (conjugationIso u).hom
    infer_instance
  let z : B.group.X.left ≅ B.group.X.left :=
    { hom := e.inv ≫ p.left
      inv := e.inv ≫ q.left
      hom_inv_id := by
        apply (cancel_mono i.left).mp
        rw [Category.assoc, hq, ← Category.assoc _ j.left, hf, Category.assoc,
          haa', Category.comp_id, Category.id_comp]
      inv_hom_id := by
        apply (cancel_mono j.left).mp
        rw [Category.assoc, hf, ← Category.assoc _ i.left, hq, Category.assoc,
          ha'a, Category.comp_id, Category.id_comp] }
  refine ⟨z, ?_⟩
  intro c
  have hconj : j = c * i * c⁻¹ := comp_conjugation u i
  change z.hom ≫ (c * i * c⁻¹).left = i.left ≫ a
  rw [← hconj]
  exact hf


private theorem movesBorel_of_transport (B : ClosedSubgroup H.val) (σ : Gal(K/k))
    (u : GroupPoints H.val (CommAlgCat.of K K))
    (hp : ∀ (T : TestAlgebra K) (f : CommAlgCat.of K (Specs.AdjointCocharacters.coordinateHopf H) ⟶ T),
      let T' := transportAlgebra σ T
      let m : CommAlgCat.of K K ⟶ T' := ConcreteCategory.ofHom
        { toRingHom := algebraMap K T', commutes' := fun _ => rfl }
      let q : GroupPoints H.val T' := mapPoints m u
      (∃ b : GroupPoints B.group T, b ≫ B.inclusion.hom.hom = coordinatePoint H T f) ↔
        ∃ b' : GroupPoints B.group T',
          let z : GroupPoints H.val T' := b' ≫ B.inclusion.hom.hom
          q * z * q⁻¹ = coordinatePoint H T' (transportPoint D σ f)) :
    MovesBorel D B σ ((fieldPointIso K).hom ≫ u) := by
  apply movesBorel_of_points D B σ
  intro T p
  obtain ⟨f, rfl⟩ := coordinatePoint_surjective H T p
  rw [← coordinatePoint_transport D σ T f]
  let T' := transportAlgebra σ T
  let m : CommAlgCat.of K K ⟶ T' := ConcreteCategory.ofHom
    { toRingHom := algebraMap K T', commutes' := fun _ => rfl }
  let v := (fieldPointIso K).hom ≫ u
  let q : GroupPoints H.val T' := mapPoints m u
  have hv : q = toUnit ((testSpec K).obj (op T')) ≫ v := transportedSection u σ T
  have hcomp (b : GroupPoints B.group T') :
      b ≫ B.inclusion.hom.hom ≫ (conjugationIso v).hom.hom.hom =
        q * (show GroupPoints H.val T' from b ≫ B.inclusion.hom.hom) * q⁻¹ := by
    rw [← Category.assoc]
    have ht := comp_conjugation v (b ≫ B.inclusion.hom.hom)
    rw [hv]
    exact ht
  have hm := hp T f
  dsimp only [] at hm
  constructor
  · intro h
    obtain ⟨b, hb⟩ := hm.mp h
    exact ⟨b, congrArg Over.Hom.left ((hcomp b).trans hb)⟩
  · rintro ⟨b, hb⟩
    exact hm.mpr ⟨b, (hcomp b).symm.trans (Over.OverMorphism.ext hb)⟩

private theorem rationalPoint_transport (σ : Gal(K/k))
    (f : CommAlgCat.of K (Specs.AdjointCocharacters.coordinateHopf H) ⟶ CommAlgCat.of K K) :
    let T := CommAlgCat.of K K
    let T' := transportAlgebra σ T
    let m : T' ⟶ T := ConcreteCategory.ofHom (C := CommAlgCat K) (X := T') (Y := T)
      { σ.toRingHom with commutes' := fun r => σ.apply_symm_apply r }
    (fieldPointIso K).hom ≫ mapPoints m (coordinatePoint H T' (transportPoint D σ f)) =
      groupPointOperator H D σ ((fieldPointIso K).hom ≫ coordinatePoint H T f) := by
  intro T T' m
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ scalarMap σ ≫ (coordinatePoint H T' (transportPoint D σ f)).left =
    scalarMap σ ≫ (𝟙 _ ≫ (coordinatePoint H T f).left) ≫ schemeOperator H D σ
  rw [Category.id_comp, Category.id_comp, coordinatePoint_transport]

private theorem baseChangePoint_coefficient (σ : Gal(K/k)) (X : SchemeOver k)
    (g : RationalPoint ((baseChange k K).obj X)) :
    baseChangePoint k K X (CommAlgCat.of K K) ((fieldPointIso K).inv ≫ coefficientPoint σ X g) =
      mapPoints (CommAlgCat.ofHom σ.toAlgHom)
        (baseChangePoint k K X (CommAlgCat.of K K) ((fieldPointIso K).inv ≫ g)) := by
  let p := pullback.fst X.hom (fieldSpecMap k K)
  have hp : coefficientMap σ X ≫ p = p := pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  change (𝟙 _ ≫ scalarMap σ ≫ g.left ≫ coefficientMap σ X) ≫ p =
    scalarMap σ ≫ (𝟙 _ ≫ g.left) ≫ p
  simp only [Category.assoc, Category.id_comp, hp]

end ResidueScheme

section DescentComparisons

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open _root_.LinearAlgebraicGroups.Specs (GroupScheme AffineAlgebraicGroup ClosedSubgroup)
open Specs.ResidueFlagDescent
open Specs.GeometricRadicals (IsReductive)
open Specs.GeometricBorelConjugacy (IsKBorel ConjugatesSubgroups)
open Specs.QuotientEmbedding (Presentation)
open _root_.LinearAlgebraicGroups.Descent

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open private twist twistGroupBaseChangeIso twistBaseChangeIso twistedSections
  from LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private group_operator_comparison descendedGroup reductive_descends
  rational_borel_conjugacy borel_after_field_extension projection_comparison
  coefficientPoint_eq_twisted operated_conjugates translation translationIso comp_translation
  from LinearAlgebraicGroups.Descent.ResidueFlagDescent
open private sectionsMap from LinearAlgebraicGroups.Reductive.GeometricRadicals
open private transportSubgroup from LinearAlgebraicGroups.Reductive.RadicalBaseChange
open private extendSubgroup conjugates_inverse from LinearAlgebraicGroups.RootData.BorelNormalizer
open private conjugates_trans normalizes_of_conjugates_self
  from LinearAlgebraicGroups.Reductive.MaximalToriConjugate
open private projection_eq_iff from LinearAlgebraicGroups.Flag.QuotientEmbedding

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

private theorem coefficientMap_naturality (σ : Gal(K/k)) {X Y : SchemeOver k} (f : X ⟶ Y) :
    ((baseChange k K).map f).left ≫ coefficientMap σ Y =
      coefficientMap σ X ≫ ((baseChange k K).map f).left := by
  exact congrArg Over.Hom.left ((twistBaseChangeIso (k := k) (K := K) σ⁻¹).hom.naturality f)

private theorem coefficientMap_translation (σ : Gal(K/k)) (G : GroupScheme k)
    (c : RationalPoint ((groupBaseChange k K).obj G).X) :
    (translationIso c).hom.left ≫ coefficientMap σ G.X =
      coefficientMap σ G.X ≫
        (translationIso (G := (groupBaseChange k K).obj G) (coefficientPoint σ G.X c)).hom.left := by
  rw [coefficientPoint_eq_twisted]
  let X := ((groupBaseChange k K).obj G).X
  let F := twist σ⁻¹
  let e := (twistGroupBaseChangeIso σ⁻¹).app G
  let d : F.obj X ⟶ X := e.hom.hom.hom
  have hc : F.map (toUnit X ≫ c) ≫ d = toUnit (F.obj X) ≫ twistedSections σ⁻¹ G c := by
    change F.map (toUnit X ≫ c) ≫ d =
      toUnit (F.obj X) ≫ (Functor.Monoidal.εIso F).hom ≫ F.map c ≫ d
    rw [F.map_comp, ← Functor.Monoidal.toUnit_ε F X]
    simp only [Category.assoc, Functor.Monoidal.εIso_hom]
  let m : (X ⟶ X) →* (F.obj X ⟶ X) :=
    (sectionsMap e.hom (F.obj X)).comp (F.homMonoidHom (X := X) (M := X))
  have hm (x : X ⟶ X) : m x = F.map x ≫ d := rfl
  have ht : F.map (translation c) ≫ d = d ≫ translation (twistedSections σ⁻¹ G c) := by
    change m (𝟙 X * (toUnit X ≫ c)) = _
    rw [map_mul, hm, hm, F.map_id, Category.id_comp, hc, comp_translation]
    rfl
  exact congrArg Over.Hom.left ht

private theorem translation_commutes {G H : GroupScheme K} (f : G ⟶ H)
    (c : RationalPoint G.X) :
    (translationIso c).hom ≫ f.hom.hom =
      f.hom.hom ≫ (translationIso (c ≫ f.hom.hom)).hom := by
  change translation c ≫ f.hom.hom = f.hom.hom ≫ translation (c ≫ f.hom.hom)
  rw [comp_translation]
  change (𝟙 _ * (toUnit _ ≫ c)) ≫ f.hom.hom = _
  rw [MonObj.mul_comp, Category.id_comp, Category.assoc]
  rfl

private theorem translation_comp {G : GroupScheme K} (c u : RationalPoint G.X) :
    (translationIso c).hom ≫ (translationIso u).hom =
      (translationIso (c * u)).hom := by
  change translation c ≫ translation u = translation (c * u)
  rw [comp_translation]
  simp only [rightTranslate, MonObj.comp_mul, mul_assoc]

private theorem groupPointOperator_comparison {H₀ : AffineAlgebraicGroup k} {H : AffineAlgebraicGroup K}
    (D : HopfDescentDatum k (Specs.AdjointCocharacters.coordinateHopf H))
    (e : (groupBaseChange k K).obj H₀.val ≅ H.val) (σ : Gal(K/k))
    (he : e.hom.hom.hom.left ≫ schemeOperator H D σ =
      coefficientMap σ H₀.val.X ≫ e.hom.hom.hom.left)
    (g : RationalPoint ((groupBaseChange k K).obj H₀.val).X) :
    coefficientPoint σ H₀.val.X g ≫ e.hom.hom.hom =
      groupPointOperator H D σ (g ≫ e.hom.hom.hom) := by
  apply Over.OverMorphism.ext
  change (scalarMap σ ≫ g.left ≫ coefficientMap σ H₀.val.X) ≫ e.hom.hom.hom.left =
    scalarMap σ ≫ (g.left ≫ e.hom.hom.hom.left) ≫ schemeOperator H D σ
  simpa only [Category.assoc] using congrArg (fun f ↦ scalarMap σ ≫ g.left ≫ f) he.symm

private theorem rightTranslate_projection {H : AffineAlgebraicGroup K} {B : ClosedSubgroup H.val}
    (Q : Presentation B) {c z : RationalPoint H.val.X}
    (b : RationalPoint B.group.X) (hb : b ≫ B.inclusion.hom.hom = c⁻¹ * z) :
    (translationIso c).hom ≫ Q.projection = (translationIso z).hom ≫ Q.projection := by
  apply (projection_eq_iff Q _ _).2
  refine ⟨toUnit H.val.X ≫ b, ?_⟩
  change (toUnit H.val.X ≫ b) ≫ B.inclusion.hom.hom = (translation c)⁻¹ * translation z
  rw [Category.assoc, hb, MonObj.comp_mul, GrpObj.comp_inv]
  change (toUnit H.val.X ≫ c)⁻¹ * (toUnit H.val.X ≫ z) =
    (𝟙 H.val.X * (toUnit H.val.X ≫ c))⁻¹ * (𝟙 H.val.X * (toUnit H.val.X ≫ z))
  group

private theorem flagSchemeAction {H₀ : AffineAlgebraicGroup k} {H : AffineAlgebraicGroup K}
    {B₀ : ClosedSubgroup H₀.val} {B : ClosedSubgroup H.val}
    (Q₀ : Presentation B₀) (Q : Presentation B) (hH : IsReductive H) (hB : IsKBorel B)
    (D : HopfDescentDatum k (Specs.AdjointCocharacters.coordinateHopf H))
    (e : (groupBaseChange k K).obj H₀.val ≅ H.val)
    (j : (baseChange k K).obj Q₀.scheme ≅ Q.scheme) (c : RationalPoint H.val.X)
    (hc : ConjugatesSubgroups c B (transportSubgroup e (extendSubgroup K B₀)))
    (hj : ∀ (S : SchemeOver K) (g : S ⟶ ((groupBaseChange k K).obj H₀.val).X),
      g ≫ (baseChange k K).map Q₀.projection ≫ j.hom =
        rightTranslate (g ≫ e.hom.hom.hom) c ≫ Q.projection)
    (σ : Gal(K/k)) (u : RationalPoint H.val.X)
    (he : e.hom.hom.hom.left ≫ schemeOperator H D σ =
      coefficientMap σ H₀.val.X ≫ e.hom.hom.hom.left)
    (hu : MovesBorel D B σ u) :
    Q.projection.left ≫ j.inv.left ≫ coefficientMap σ Q₀.scheme ≫ j.hom.left =
      schemeOperator H D σ ≫ (translationIso u).hom.left ≫ Q.projection.left := by
  let X := ((groupBaseChange k K).obj H₀.val).X
  let E : X ≅ H.val.X := (Grp.forget (SchemeOver K)).mapIso e
  let p : X ⟶ (baseChange k K).obj Q₀.scheme := (baseChange k K).map Q₀.projection
  let Qmap := Q.projection.left
  let a := schemeOperator H D σ
  let b : X.left ⟶ X.left := coefficientMap σ H₀.val.X
  let q := coefficientMap σ Q₀.scheme
  let c₀ : RationalPoint X := c ≫ E.inv
  let tr := fun g : RationalPoint H.val.X => (translationIso g).hom.left
  let r : X.left ≅ H.val.X.left := (Over.forget _).mapIso (E ≪≫ translationIso c)
  have hproj : p.left ≫ j.hom.left = r.hom ≫ Qmap := by
    have h := hj _ (𝟙 ((groupBaseChange k K).obj H₀.val).X)
    rw [Category.id_comp, Category.id_comp, ← comp_translation] at h
    exact congrArg Over.Hom.left h
  have hj' : r.hom ≫ Qmap ≫ j.inv.left = p.left := by
    rw [← Category.assoc, ← hproj, Category.assoc]
    have h := (Over.forget _).congr_map j.hom_inv_id
    change j.hom.left ≫ j.inv.left = 𝟙 _ at h
    rw [h, Category.comp_id]
  have hc₀ : c₀ ≫ E.hom = c := by simp [c₀]
  have ht := translation_commutes e.hom c₀
  change (translationIso c₀).hom ≫ E.hom = E.hom ≫
    (translationIso (c₀ ≫ E.hom)).hom at ht
  rw [hc₀] at ht
  have ht' : (translationIso c₀).hom.left ≫ E.hom.left = r.hom :=
    congrArg Over.Hom.left ht
  let c₁ : RationalPoint X := coefficientPoint σ H₀.val.X c₀
  have hc₁ : c₁ ≫ E.hom = groupPointOperator H D σ c := by
    exact (groupPointOperator_comparison D e σ he c₀).trans (congrArg _ hc₀)
  have ht₁ := translation_commutes e.hom c₁
  change (translationIso c₁).hom ≫ E.hom = E.hom ≫
    (translationIso (c₁ ≫ E.hom)).hom at ht₁
  rw [hc₁] at ht₁
  have ht₁' : (translationIso c₁).hom.left ≫ E.hom.left =
      E.hom.left ≫ tr (groupPointOperator H D σ c) := congrArg Over.Hom.left ht₁
  let z := groupPointOperator H D σ c * u
  have hn := normalizes_of_conjugates_self B (conjugates_trans
    (operated_conjugates e D σ he hc hu) (conjugates_inverse hc))
  obtain ⟨s, hs⟩ := (RootData.BorelNormalizer.groundFieldBorelNormalizer H hH B hB _ _).mp hn
  have hcoset : tr z ≫ Qmap = tr c ≫ Qmap := congrArg Over.Hom.left
    (rightTranslate_projection Q s hs).symm
  have hprod : tr (groupPointOperator H D σ c) ≫ tr u = tr z :=
    congrArg Over.Hom.left (translation_comp _ _)
  apply (cancel_epi r.hom).mp
  change r.hom ≫ Qmap ≫ j.inv.left ≫ q ≫ j.hom.left =
    r.hom ≫ a ≫ tr u ≫ Qmap
  have hn' : p.left ≫ q = b ≫ p.left := coefficientMap_naturality σ Q₀.projection
  have he' : E.hom.left ≫ a = b ≫ E.hom.left := he
  have htrans : (translationIso c₀).hom.left ≫ b = b ≫ (translationIso c₁).hom.left :=
    coefficientMap_translation σ H₀.val c₀
  calc
    _ = p.left ≫ q ≫ j.hom.left := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ q ≫ j.hom.left) hj'
    _ = b ≫ p.left ≫ j.hom.left := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ j.hom.left) hn'
    _ = b ≫ r.hom ≫ Qmap := congrArg (fun f => b ≫ f) hproj
    _ = _ := by
      symm
      rw [← ht']
      simp only [Category.assoc, reassoc_of% he', reassoc_of% htrans, reassoc_of% ht₁',
        reassoc_of% hprod, hcoset, reassoc_of% ht']
      rfl

private theorem residueFlagDescent_exists [Fintype k] [Fintype K] [FiniteDimensional k K] [IsGalois k K]
    (H : AffineAlgebraicGroup K) (B : ClosedSubgroup H.val) (Q : Presentation B)
    (hH : IsReductive H) (hB : IsKBorel B)
    (D : HopfDescentDatum k (Specs.AdjointCocharacters.coordinateHopf H))
    (u : Gal(K/k) → RationalPoint H.val.X)
    (hu : ∀ σ, MovesBorel D B σ (u σ)) :
    ∃ (H₀ : AffineAlgebraicGroup k) (B₀ : ClosedSubgroup H₀.val)
      (Q₀ : Presentation B₀)
      (e : (groupBaseChange k K).obj H₀.val ≅ H.val)
      (j : (baseChange k K).obj Q₀.scheme ≅ Q.scheme)
      (c : RationalPoint H.val.X),
      IsReductive H₀ ∧ IsKBorel B₀ ∧
      (∀ σ, e.hom.hom.hom.left ≫ schemeOperator H D σ =
        coefficientMap σ H₀.val.X ≫ e.hom.hom.hom.left) ∧
      (∀ (S : SchemeOver K) (g : S ⟶ ((groupBaseChange k K).obj H₀.val).X),
        g ≫ (baseChange k K).map Q₀.projection ≫ j.hom =
          rightTranslate (g ≫ e.hom.hom.hom) c ≫ Q.projection) ∧
      ∀ σ, Q.projection.left ≫ j.inv.left ≫ coefficientMap σ Q₀.scheme ≫ j.hom.left =
        schemeOperator H D σ ≫ (translationIso (u σ)).hom.left ≫ Q.projection.left := by
  obtain ⟨J, hJ⟩ := affineHopfDescent D
  let H₀ := descendedGroup J
  let e : (groupBaseChange k K).obj H₀.val ≅ H.val :=
    (groupDescentComparison J).symm ≪≫ Specs.AdjointCocharacters.coordinateHopfIso H
  have hr : IsReductive H₀ := reductive_descends e hH
  have he (σ : Gal(K/k)) : e.hom.hom.hom.left ≫ schemeOperator H D σ =
      coefficientMap σ H₀.val.X ≫ e.hom.hom.hom.left := group_operator_comparison J hJ σ
  obtain ⟨_, B₀, hB₀⟩ := FiniteFieldFlags.reductiveQuasiSplit H₀ hr
  obtain ⟨Q₀⟩ := QuotientEmbedding.quotientEmbedding k H₀ B₀
  obtain ⟨c, hc⟩ := rational_borel_conjugacy H hH B _
    hB (borel_after_field_extension e B₀ hB₀)
  obtain ⟨j, hj⟩ := projection_comparison Q₀ Q e c hc
  exact ⟨H₀, B₀, Q₀, e, j, c, hr, hB₀, he, hj,
    fun σ => flagSchemeAction Q₀ Q hH hB D e j c hc hj σ (u σ) (he σ) (hu σ)⟩


private theorem flagPoint_from_scheme {H : AffineAlgebraicGroup K} {B : ClosedSubgroup H.val}
    (Q : Presentation B) (Q₀ : SchemeOver k) (j : (baseChange k K).obj Q₀ ≅ Q.scheme)
    (D : HopfDescentDatum k (Specs.AdjointCocharacters.coordinateHopf H))
    (σ : Gal(K/k)) (u : RationalPoint H.val.X)
    (hw : Q.projection.left ≫ j.inv.left ≫ coefficientMap σ Q₀ ≫ j.hom.left =
      schemeOperator H D σ ≫ (translationIso u).hom.left ≫ Q.projection.left)
    (g : RationalPoint H.val.X) :
    coefficientPoint σ Q₀ (g ≫ Q.projection ≫ j.inv) ≫ j.hom =
      (groupPointOperator H D σ g * u) ≫ Q.projection := by
  have ht := comp_translation (groupPointOperator H D σ g) u
  have ht₀ : toUnit (𝟙_ (SchemeOver K)) = 𝟙 _ :=
    (isTerminalTensorUnit (C := SchemeOver K)).hom_ext _ _
  have ht' : groupPointOperator H D σ g ≫ (translationIso u).hom =
      groupPointOperator H D σ g * u := by
    change groupPointOperator H D σ g ≫ translation u = groupPointOperator H D σ g * u
    simpa only [rightTranslate, ht₀, Category.id_comp] using ht
  rw [← ht']
  apply Over.OverMorphism.ext
  change (scalarMap σ ≫ (g.left ≫ Q.projection.left ≫ j.inv.left) ≫
        coefficientMap σ Q₀) ≫ j.hom.left =
    ((scalarMap σ ≫ g.left ≫ schemeOperator H D σ) ≫ (translationIso u).hom.left) ≫
      Q.projection.left
  simpa only [Category.assoc] using congrArg (fun f => scalarMap σ ≫ g.left ≫ f) hw

end DescentComparisons

section ScaledDescent

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped ValuativeRel
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

open Specs.Pinning (BasedRootDatum)
open Specs.IntegralSemisimpleModel (Model integerAlgebra IntegralAlgebra torusPoint cocharacter)
open Specs.ExceptionalIwahoriImageComparison (MarkedCentralCover integralPointHom)
open Specs.ExceptionalIwahoriCongruence (integralRing changeRingHom localIntegers localIntegersInclusion residueHom)
open Specs.ExceptionalLocalRootCoordinates (residueMap normalizedValuation)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalScaledParahoricAction
  (Coefficients PinnedOperators ScaledInput ScaledIntegralAction ScaledResidueAction
    typeLift markedCocharacter coordinatePoint)
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ResidueFlagDescent
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology (pointAction)

attribute [local instance] integerAlgebra Specs.ExceptionalLocalRootCoordinates.canonicalExtension

variable {F K L : Type u} [Field F] [Field K] [Field L]
  [Algebra F K] [Algebra K L] [Algebra F L] [IsScalarTower F K L]
  [FiniteDimensional F K] [IsGalois F K] [FiniteDimensional K L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension F K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L] [ValuativeExtension F L]
  {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
  {c : MarkedCentralCover M M'} {p : ℚ ⊗[ℤ] D.Y} {p' : ℚ ⊗[ℤ] E.Y}
  {e : (ℚ ⊗[ℤ] D.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)}
  {Y : SplitLevel K c p p' e} {B : SplitBuildingLevel Y}
  {t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p')}
  {x : ℚ ⊗[ℤ] E.Y} {d : ℕ} {y : E.Y} {πK : Kˣ} {ξ : Lˣ}
  {R : FaceReduction B t x d y πK L ξ}

private def scalingCoefficients (hunram : IsUnramifiedLocalExtension F K) (d : ℕ) (π : Fˣ)
    (hπ : normalizedValuation F (π : F) = WithZero.exp (-1 : ℤ))
    (r : AdjoinRoot (uniformizerPolynomial (K := K) d π) ≃ₐ[K] L)
    (hroot : r (AdjoinRoot.root (uniformizerPolynomial (K := K) d π)) = ξ)
    (hres : Function.Bijective (residueMap K L)) :
    Coefficients F K L ξ := by
  letI := (residueMap F L).toAlgebra
  letI := FiniteDimensional.trans F K L
  let f := scalingCoefficientAction d π r
  let i : Gal(K/F) →* (localIntegers L ≃+* localIntegers L) :=
    { toFun := fun σ => (integerCoefficient (f σ)).toRingEquiv
      map_one' := by
        ext z
        change f 1 (z : L) = (z : L)
        rw [map_one]
        rfl
      map_mul' := by
        intro σ τ
        ext z
        change f (σ * τ) (z : L) = f σ (f τ (z : L))
        rw [map_mul]
        rfl }
  let r₀ := MulEquiv.ofBijective (scalingResidueAction d π r)
    (scalingResidueAction_bijective hunram d π hπ r hres)
  exact
    { fieldAction := f
      restrict := scalingCoefficientAction_scalar d π r
      fixes_root := by
        intro σ
        rw [← hroot]
        exact scalingCoefficientAction_root d π r σ
      integerAction := i
      integer_eq := fun _ _ => rfl
      residueAction := r₀
      residue_eq := fun σ z => (scalingResidueAction_eq d π r σ z (i σ z) rfl).symm }

private theorem parahoric_of_incident (q : IncidentChambers B (B.ad.realization.place 1 t))
    (g : Y.ad.G₀) (hq : q.val = QuotientGroup.mk (g : FieldPoints M' K)) :
    (g : FieldPoints M' K) ∈ parahoric Y.ad (cotype t) := by
  obtain ⟨g₀, s, hq₀, hs⟩ := q.property
  obtain ⟨hs', hg₀⟩ := (B.ad.realization.place_eq g₀ 1 s t).1 hs
  subst s
  have hg₀' : (g₀ : FieldPoints M' K) ∈ parahoric Y.ad (cotype t) := by
    simpa using (parahoric Y.ad (cotype t)).inv_mem hg₀
  have hi := QuotientGroup.eq.mp (hq₀.symm.trans hq)
  have hm : (g₀ : FieldPoints M' K)⁻¹ * (g : FieldPoints M' K) ∈
      parahoric Y.ad (cotype t) := Subgroup.subset_closure (Or.inl hi)
  simpa only [mul_inv_cancel_left] using (parahoric Y.ad (cotype t)).mul_mem hg₀' hm

private theorem chamberCoset_of_closedFace_eq
    (t : Weights ((ApartmentRoots.split E.datum ℚ).SimpleWall p'))
    (g g' : Y.ad.G₀)
    (h : B.ad.realization.closedFace g ∅ = B.ad.realization.closedFace g' ∅) :
    (QuotientGroup.mk (g : FieldPoints M' K) : FieldPoints M' K ⧸ Y.ad.I) =
      QuotientGroup.mk (g' : FieldPoints M' K) := by
  have hne : (∅ : Set ((ApartmentRoots.split E.datum ℚ).SimpleWall p')) ≠ Set.univ := by
    intro he
    have hz (i : (ApartmentRoots.split E.datum ℚ).SimpleWall p') : t.val i = 0 :=
      False.elim (Set.notMem_empty i (he.symm ▸ Set.mem_univ i))
    have hsum := t.property.2
    simp only [hz, finsum_zero] at hsum
    exact zero_ne_one hsum
  have hsub := (B.ad.realization.closed_face_incidence ∅ ∅ hne hne g g').1
    (show B.ad.realization.closedFace g ∅ ⊆ B.ad.realization.closedFace g' ∅ from h.le)
  have hmem : (g' : FieldPoints M' K) ∈
      {b : FieldPoints M' K | (g' : FieldPoints M' K)⁻¹ * b ∈ parahoric Y.ad ∅} := by
    change (g' : FieldPoints M' K)⁻¹ * (g' : FieldPoints M' K) ∈ parahoric Y.ad ∅
    rw [inv_mul_cancel]
    exact Subgroup.one_mem _
  have hpar : parahoric Y.ad ∅ = Y.ad.I := by
    unfold Specs.ExceptionalAffineBuilding.parahoric faceSubgroup
    rw [Set.image_empty, Set.union_empty, Subgroup.closure_eq]
  apply QuotientGroup.eq.mpr
  exact hpar ▸ hsub hmem

private theorem baseChangePoint_eq_of_coefficient {k k' : Type u}
    [Field k] [Field k'] [Algebra k k'] (σ : Gal(k'/k)) (X : SchemeOver k)
    {f g : Points ((baseChange k k').obj X) (CommAlgCat.of k' k')}
    (h : (fieldPointIso k').hom ≫ g = coefficientPoint σ X ((fieldPointIso k').hom ≫ f)) :
    baseChangePoint k k' X (CommAlgCat.of k' k') g =
      mapPoints (CommAlgCat.ofHom σ.toAlgHom) (baseChangePoint k k' X (CommAlgCat.of k' k') f) := by
  simpa only [← h, Iso.inv_hom_id_assoc] using
    baseChangePoint_coefficient σ X ((fieldPointIso k').hom ≫ f)

private theorem descend_scaled_face (S : ScaledInput (F := F) R.toFaceReduction)
    (J : ScaledIntegralAction S) (Haction : ScaledResidueAction J) :
    ∃ U : DescendedFaceResidue R S.onBuilding S.a,
      Nonempty (Points U.flags.scheme (CommAlgCat.of (residue F) (residue F))) := by
  let k := residue F
  let k' := residue L
  letI := (residueMap F L).toAlgebra
  letI := FiniteDimensional.trans F K L
  letI : Fintype k := Fintype.ofFinite (𝓀[F])
  letI : Fintype k' := Fintype.ofFinite (𝓀[L])
  let H := R.toFaceReduction.group
  let T := CommAlgCat.of k' k'
  let γ₀ := S.coefficients.residueAction
  let U : Gal(k'/k) → RationalPoint H.val.X := fun σ =>
    (fieldPointIso k').hom ≫ R.reduction (S.b (γ₀.symm σ))
  have hmove (σ : Gal(K/F)) :
      MovesBorel Haction.hopf R.borel (γ₀ σ) ((fieldPointIso k').hom ≫ R.reduction (S.b σ)) :=
    movesBorel_of_transport Haction.hopf R.borel (γ₀ σ) (R.reduction (S.b σ)) (Haction.borel σ)
  have hu (σ : Gal(k'/k)) : MovesBorel Haction.hopf R.borel σ (U σ) := by
    obtain ⟨τ, rfl⟩ := γ₀.surjective σ
    simpa only [U, MulEquiv.symm_apply_apply] using hmove τ
  let A : MarkedResidueAction R S.ρ S.h S.a γ₀.toMonoidHom :=
    { pinned := S.δ
      parahoricFactor := S.b
      factorization := S.factor
      corrector := fun σ => R.integral (S.b σ) * J.normalizer σ
      corrector_eq := by
        intro σ
        dsimp only []
        rw [map_mul, R.scale, J.normalizer_eq, S.factor σ, map_mul]
        group
      hopf := Haction.hopf
      ambient := Haction.ambient
      moves_borel := hmove }
  obtain ⟨H₀, B₀, Q₀, e, j, c₀, hr, hB₀, he, hj, hjAction⟩ :=
    residueFlagDescent_exists H R.borel R.flags R.reductive R.borel_is_borel Haction.hopf U hu
  have hflag (σ : Gal(K/F)) := hjAction (γ₀ σ)
  simp only [U, MulEquiv.symm_apply_apply] at hflag
  let red (g : parahoric Y.ad (cotype t)) : RationalPoint H.val.X :=
    (fieldPointIso k').hom ≫ R.reduction g
  have hRed (σ : Gal(K/F)) (g : parahoric Y.ad (cotype t)) :
      groupPointOperator H Haction.hopf (γ₀ σ) (red g) =
        red ⟨_, J.invariant σ g⟩ := by
    obtain ⟨f, hf⟩ := coordinatePoint_surjective H T (R.reduction g)
    have h₁ := rationalPoint_transport Haction.hopf (γ₀ σ) f
    have h₂ := Haction.rational σ g f hf
    have h₃ := congrArg (fun q => (fieldPointIso k').hom ≫ q) hf
    exact (congrArg (groupPointOperator H Haction.hopf (γ₀ σ)) h₃).symm.trans
      (h₁.symm.trans (congrArg (fun q => (fieldPointIso k').hom ≫ q) h₂))
  refine ⟨{
    liftCoefficient := S.coefficients.fieldAction
    lift_restrict := S.coefficients.restrict
    lift_uniformizer := S.coefficients.fixes_root
    lift_valuation := fun σ => normalizedValuation_automorphism (S.coefficients.fieldAction σ)
    residueAction := γ₀.toMonoidHom
    residueAction_bijective := γ₀.bijective
    residue_action_eq := ?_
    markedAction := A
    descended := H₀
    reductive := hr
    groupComparison := e
    group_scheme_action := fun σ => he (γ₀ σ)
    borel := B₀
    borel_eq := hB₀
    flags := Q₀
    flagComparison := j
    flagBasepoint := c₀
    flag_projection_eq := hj
    flag_scheme_action := hflag
    parahoricInvariant := J.invariant
    semilinear_group := ?_
    semilinear_flags := ?_ }, ⟨(fieldPointIso k).inv ≫ (1 ≫ Q₀.projection)⟩⟩
  · intro σ z z' hz
    have hzz : S.coefficients.integerAction σ z = z' :=
      Subtype.ext ((S.coefficients.integer_eq σ z).trans hz.symm)
    change S.coefficients.residueAction σ ((residueHom (localIntegers L)).hom z) =
      (residueHom (localIntegers L)).hom z'
    rw [← hzz]
    exact (S.coefficients.residue_eq σ z).symm
  · intro σ g
    dsimp only []
    apply baseChangePoint_eq_of_coefficient (γ₀ σ) H₀.val.X
    let f := red g ≫ e.inv.hom.hom
    let f' := red ⟨_, J.invariant σ g⟩ ≫ e.inv.hom.hom
    change f' = coefficientPoint (γ₀ σ) H₀.val.X f
    apply (cancel_mono e.hom.hom.hom).mp
    rw [groupPointOperator_comparison Haction.hopf e (γ₀ σ) (he _) f]
    have h₁ : f' ≫ e.hom.hom.hom = red ⟨_, J.invariant σ g⟩ := by
      simp [f', ← Grp.comp_hom_hom]
    have h₀ : f ≫ e.hom.hom.hom = red g := by simp [f, ← Grp.comp_hom_hom]
    rw [h₀, h₁, hRed]
  · intro σ q q' g g' hq hq' hImage
    dsimp only []
    let g₀ : parahoric Y.ad (cotype t) := ⟨g, parahoric_of_incident q g hq⟩
    let g₁ : parahoric Y.ad (cotype t) := ⟨_, J.invariant σ g₀⟩
    let b : Y.ad.G₀ := ⟨S.b σ, B.ad.realization.face_mem _ (S.b σ).property⟩
    let v : Y.ad.G₀ := ⟨g₁ * S.b σ, B.ad.realization.face_mem _ (g₁ * S.b σ).property⟩
    have hρg : S.ρ σ (g : FieldPoints M' K) ∈ Y.ad.G₀ := by
      exact (congrArg (fun H => S.ρ σ (g : FieldPoints M' K) ∈ H)
        (S.coefficient_comparison σ).2.2.2.1).mp ⟨g, g.property, rfl⟩
    have hImage' := twisted_chamber_image B.adjoint S.onBuilding σ (S.a σ)
      (typeChange Y.typeQuotient (S.a σ)) b g v (S.factor σ) hρg rfl
    have hcoset := chamberCoset_of_closedFace_eq t g' v (hImage.symm.trans hImage')
    have hq₀ := R.incident_eq g₀ q hq
    have hq₁ := R.incident_eq (g₁ * S.b σ) q' (hq'.trans hcoset)
    apply baseChangePoint_eq_of_coefficient (γ₀ σ) Q₀.scheme
    rw [hq₀, hq₁]
    have hf := flagPoint_from_scheme R.flags Q₀.scheme j Haction.hopf (γ₀ σ)
      (red (S.b σ)) (hflag σ) (red g₀)
    have hstep : groupPointOperator H Haction.hopf (γ₀ σ) (red g₀) = red g₁ := hRed σ g₀
    rw [hstep] at hf
    apply (cancel_mono j.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hh : red g₁ * red (S.b σ) = red (g₁ * S.b σ) := by
      unfold red
      rw [map_mul]
      exact (MonObj.comp_mul (fieldPointIso k').hom (R.reduction g₁) (R.reduction (S.b σ))).symm
    rw [hh] at hf
    simpa only [red, Category.assoc] using hf.symm


/-- The actual marked parahoric and its residue flags descend at a standard
face fixed by the twisted coefficient action. -/
theorem splitParahoricResidueDescent : SplitParahoricResidueDescent.{u} := by
  intro F K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hunram
    D E M M' c p p' e Y B ρ h C l ω hmarked hauto coef equivariant
    a hcocycle t x d y π ξ hbary hd hscale hπ hx hfix r hroot R
  let πK := Units.map (algebraMap F K).toMonoidHom π
  have hπK : normalizedValuation K (πK : K) = WithZero.exp (-1 : ℤ) :=
    (hunram (π : F)).trans hπ
  obtain ⟨δ, hδ⟩ := pinnedOperator_exists C l ω hmarked
  let coeffs := scalingCoefficients hunram d π hπ r hroot R.same_residue
  have htorus (σ : Gal(K/F)) :=
    marked_scaled_torus_valuation (coef := coef) (a := a)
      C l ω hmarked hfix hx hd hscale hπK R.parameter σ
  choose b v hv using htorus
  let S : ScaledInput (F := F) R.toFaceReduction :=
    { coefficients := coeffs
      ρ := ρ
      h := h
      δ := δ
      coefficient_comparison := hauto
      onBuilding := coef
      equivariant := equivariant
      a := a
      cocycle := hcocycle
      barycenter := hbary
      point_eq := hx
      fixed := hfix
      d_pos := hd
      scale_eq := hscale
      b := b
      factor := fun σ => (hv σ).1
      affine_fixed := fun σ => (Classical.choose_spec (twisted_stabilizer_affine_equation
        B.adjoint coef a t hfix x hx σ)).2
      torusValues := v
      torusValues_eq := fun σ => (hv σ).2.1
      valuation_cancel := by
        intro σ χ
        dsimp only []
        rw [hδ σ]
        exact (hv σ).2.2 χ
      cocharacter_eq := by
        intro σ T z hz
        dsimp only []
        rw [hδ σ]
        exact ((Classical.choose_spec (marked_scaled_cocharacters_on_mu (coef := coef)
          (a := a) C l ω hmarked hfix hx hscale σ)).2 T z hz).symm }
  obtain ⟨J, ⟨Haction⟩⟩ := ExceptionalScaledParahoricAction.scaledParahoricDescent
    R.toFaceReduction S
  obtain ⟨U, hU⟩ := descend_scaled_face S J Haction
  exact ⟨U, hU, fun f => lift_rationalFlag U hauto hfix f⟩

end ScaledDescent

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalSplitParahoricDescent
