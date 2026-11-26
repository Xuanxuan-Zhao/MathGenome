import Specs.LinearAlgebraicGroups.Arithmetic.SplitIwahoriUnramifiedTorsor
import LinearAlgebraicGroups.Arithmetic.GlobalPlaces
import LinearAlgebraicGroups.Descent.Lang
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.Algebra.Ring.Aut
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.Valuation.Integral

namespace LinearAlgebraicGroups.Arithmetic.SplitIwahoriUnramifiedTorsor

open Specs.SplitIwahoriUnramifiedTorsor
noncomputable section

section Lifting
open AlgebraicGeometry CategoryTheory Opposite
open scoped ValuativeRel

universe u

/-- Smooth affine schemes over the valuation ring of a nonarchimedean
local field lift residue-field points to sections of the valuation ring. -/
theorem liftSmoothAffinePoint {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {X : Over (Spec (CommRingCat.of (localIntegers K)))} (hX : IsAffine X.left)
    (hs : Smooth X.hom)
    (p : (algSpec (CommRingCat.of (localIntegers K))).obj
      (op (CommAlgCat.of (localIntegers K) (residue K))) ⟶ X) :
    Nonempty ((algSpec (CommRingCat.of (localIntegers K))).obj
      (op (CommAlgCat.of (localIntegers K) (localIntegers K))) ⟶ X) := by
  let O := localIntegers K
  let R := CommRingCat.of O
  let F := algSpec R
  obtain ⟨B, ⟨i⟩⟩ := (essImage_algSpec (G := X)).mpr hX
  have hi : (F.obj B).hom = i.hom.left ≫ X.hom := (Over.w i.hom).symm
  have hS : Smooth (F.obj B).hom := by
    rw [hi]
    have : IsIso i.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i.hom))
    infer_instance
  have hS' : (algebraMap O B.unop).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mp hS
  have : Algebra.Smooth O B.unop := RingHom.smooth_algebraMap.mp hS'
  let ff : F.FullyFaithful := algSpec.fullyFaithful (R := R)
  let p' := (ff.preimage (p ≫ i.inv)).unop
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  have : IsAdicComplete (IsLocalRing.maximalIdeal O) O :=
    inferInstanceAs (IsAdicComplete (IsLocalRing.maximalIdeal 𝒪[K]) 𝒪[K])
  obtain ⟨q, _⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete p'.hom
  exact ⟨F.map (CommAlgCat.ofHom q).op ≫ i.hom⟩

set_option maxHeartbeats 40000 in
/-- An actual rational point of the special fibre lifts to an integral
section of a smooth affine scheme over the valuation ring. -/
theorem liftSmoothAffineSpecialPoint {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {X : Over (Spec (CommRingCat.of (localIntegers K)))} (hX : IsAffine X.left)
    (hs : Smooth X.hom)
    (p : Over.mk (𝟙 (Spec (CommRingCat.of (residue K)))) ⟶
      (Over.pullback (residuePoint K)).obj X) :
    Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of (localIntegers K)))) ⟶ X) := by
  let O := localIntegers K
  let k := residue K
  let i : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of O) := residuePoint K
  let W := Over.mk (𝟙 (Spec (CommRingCat.of k)))
  let pO : (Over.map i).obj W ⟶ X := ((Over.mapPullbackAdj i).homEquiv W X).symm p
  let W' := (algSpec (CommRingCat.of O)).obj (op (CommAlgCat.of O k))
  let iso : W' ≅ (Over.map i).obj W := Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
    change 𝟙 _ ≫ (𝟙 _ ≫ i) = Spec.map (CommRingCat.ofHom (algebraMap O k))
    rw [Category.id_comp, Category.id_comp]
    rfl)
  obtain ⟨q⟩ := liftSmoothAffinePoint (K := K) hX hs (iso.hom ≫ pO)
  let io : Over.mk (𝟙 (Spec (CommRingCat.of O))) ≅
      (algSpec (CommRingCat.of O)).obj (op (CommAlgCat.of O O)) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of O))) (by
      change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap O O)) = 𝟙 _
      rw [Category.id_comp, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id])
  exact ⟨io.hom ≫ q⟩

set_option maxHeartbeats 30000 in
/-- Lang's theorem and integral lifting give a section from a transitive
action on the geometric points of the special fibre. -/
theorem section_of_residueAction {K : Type u} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {X : Over (Spec (CommRingCat.of (localIntegers K)))} (hX : IsAffine X.left)
    (hs : Smooth X.hom) (G : Specs.GroupScheme (residue K))
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (Y : SchemeOver (residue K)) (e : Y ≅ (Over.pullback (residuePoint K)).obj X)
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [Nonempty Y.left]
    (a : SchemeLeftAction G Y)
    (ht : ∀ x y : Points Y (CommAlgCat.of (residue K) (AlgebraicClosure (residue K))),
      ∃ g : Points G.X (CommAlgCat.of (residue K) (AlgebraicClosure (residue K))), a.act g x = y) :
    Nonempty (Over.mk (𝟙 (Spec (CommRingCat.of (localIntegers K)))) ⟶ X) := by
  let k := residue K
  have hfin : Finite k := inferInstanceAs (Finite 𝓀[K])
  let _ : Fintype k := Fintype.ofFinite k
  have hLang : Specs.LangRationalPoint.{u} := langRationalPoint
  obtain ⟨p⟩ := hLang k G Y a ht
  let b := Spec (CommRingCat.of k)
  let i : Over.mk (𝟙 b) ≅ (testSpec k).obj (op (CommAlgCat.of k k)) :=
    Over.isoMk (Iso.refl b) (by
      change 𝟙 b ≫ Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 b
      rw [Category.id_comp, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id])
  exact liftSmoothAffineSpecialPoint (K := K) hX hs (i.hom ≫ p ≫ e.hom)

end Lifting
section GaloisAlgebra

open scoped BigOperators TensorProduct

variable {Γ R S B : Type*} [Group Γ] [Fintype Γ]
  [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

private theorem sum_action_fixed {A : Type*} [CommRing A] (s : Γ →* RingAut A)
    (a : A) (γ : Γ) : s γ (∑ τ, s τ a) = ∑ τ, s τ a := by
  rw [map_sum]
  simp only [← RingAut.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft γ) (fun τ => s τ a)

/-- The fixed algebra for a semilinear action that fixes the base scalars. -/
def galoisFixedAlgebra (s : Γ →* RingAut B)
    (hR : ∀ γ r, s γ (algebraMap R B r) = algebraMap R B r) : Subalgebra R B where
  carrier := {b | ∀ γ, s γ b = b}
  zero_mem' γ := map_zero _
  one_mem' γ := map_one _
  add_mem' ha hb γ := by rw [map_add, ha γ, hb γ]
  mul_mem' ha hb γ := by rw [map_mul, ha γ, hb γ]
  algebraMap_mem' r := fun γ => hR γ r

private def galoisSum (s : Γ →* RingAut B)
    (hR : ∀ γ r, s γ (algebraMap R B r) = algebraMap R B r) :
    B →ₗ[R] galoisFixedAlgebra s hR where
  toFun b := ⟨∑ γ, s γ b, sum_action_fixed s b⟩
  map_add' x y := by
    apply Subtype.ext
    simp only [Subalgebra.coe_add, map_add, Finset.sum_add_distrib]
  map_smul' r x := by
    apply Subtype.ext
    change (∑ γ, s γ (r • x)) = r • (∑ γ, s γ x)
    simp only [Algebra.smul_def, map_mul, hR, Finset.mul_sum]

/-- The canonical base-change map from the algebra of fixed elements.
The split Galois coordinates are the coefficients of a preimage of the
identity-component idempotent under the Galois tensor comparison. -/
theorem galoisFixedAlgebra_baseChange (t : Γ →* RingAut S) (s : Γ →* RingAut B)
    (hR : ∀ γ r, s γ (algebraMap R B r) = algebraMap R B r)
    (hCompat : ∀ γ c, s γ (algebraMap S B c) = algebraMap S B (t γ c))
    (hFixed : ∀ c : S, (∀ γ, t γ c = c) → c ∈ Set.range (algebraMap R S))
    {ι : Type*} [Fintype ι] (u v : ι → S)
    [DecidableEq Γ]
    (hCoord : ∀ γ, ∑ i, u i * t γ (v i) = if γ = 1 then 1 else 0) :
    Function.Bijective
      (AlgHom.liftEquiv R S _ B (galoisFixedAlgebra s hR).val) := by
  let D := galoisFixedAlgebra s hR
  let φ := AlgHom.liftEquiv R S D B D.val
  let ψ : B →ₗ[R] S ⊗[R] D :=
    ∑ i, (TensorProduct.mk R S D (u i)).comp
      ((galoisSum s hR).comp (LinearMap.mulLeft R (algebraMap S B (v i))))
  have hψ (b : B) :
      ψ b = ∑ i, u i ⊗ₜ[R] galoisSum s hR (algebraMap S B (v i) * b) := by
    simp [ψ]
  have hφψ (b : B) : φ (ψ b) = b := by
    rw [hψ]
    simp only [map_sum, φ, AlgHom.liftEquiv_tmul]
    change (∑ i, u i • (∑ γ, s γ (algebraMap S B (v i) * b))) = b
    simp only [Algebra.smul_def, map_mul, hCompat, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [← mul_assoc, ← map_mul, ← Finset.sum_mul, ← map_sum, hCoord]
    simp
  have hψφ (z : S ⊗[R] D) : ψ (φ z) = z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c b =>
      have hd (i : ι) : ∃ r : R, algebraMap R S r = ∑ γ, t γ (v i * c) :=
        hFixed _ (sum_action_fixed t (v i * c))
      choose r hr using hd
      have he (i : ι) :
          galoisSum s hR (algebraMap S B (v i) * φ (c ⊗ₜ[R] b)) = r i • b := by
        apply Subtype.ext
        change ∑ γ, s γ (algebraMap S B (v i) * (φ (c ⊗ₜ[R] b))) = r i • b.val
        simp only [φ, AlgHom.liftEquiv_tmul, Subalgebra.val_apply, Algebra.smul_def]
        have hb : ∀ γ, s γ b.val = b.val := b.property
        calc
          _ = ∑ γ, algebraMap S B (t γ (v i * c)) * b.val := by
            apply Finset.sum_congr rfl
            intro γ _
            rw [← mul_assoc, ← map_mul, map_mul, hCompat, hb]
          _ = _ := by rw [← Finset.sum_mul, ← map_sum, ← hr, ← IsScalarTower.algebraMap_apply]
      have hu : ∑ i, u i * algebraMap R S (r i) = c := by
        simp only [hr, map_mul, Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_mul, hCoord]
        simp
      rw [hψ]
      simp only [he]
      simp only [TensorProduct.tmul_smul]
      have hsum : (∑ i, r i • u i) = c := by
        calc
          _ = ∑ i, u i * algebraMap R S (r i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Algebra.smul_def, mul_comm]
          _ = c := hu
      exact (TensorProduct.sum_tmul Finset.univ (fun i => r i • u i) b).symm.trans
        (congrArg (fun x : S => x ⊗ₜ[R] b) hsum)
  exact ⟨Function.LeftInverse.injective hψφ, Function.RightInverse.surjective hφψ⟩

omit [Fintype Γ] in
/-- A surjective Galois tensor comparison supplies the coefficients of
the idempotent supported at the identity. -/
theorem galoisCoordinates_of_surjective (t : Γ →* RingAut S) [DecidableEq Γ]
    (q : Γ → S ⊗[R] S →ₐ[S] S)
    (hq : ∀ γ x y, q γ (x ⊗ₜ[R] y) = x * t γ y)
    (hs : Function.Surjective (fun x γ => q γ x)) :
    ∃ (n : ℕ) (u v : Fin n → S),
      ∀ γ, ∑ i, u i * t γ (v i) = if γ = 1 then 1 else 0 := by
  obtain ⟨z, hz⟩ := hs (fun γ => if γ = 1 then 1 else 0)
  obtain ⟨n, u, v, rfl⟩ := TensorProduct.exists_sum_tmul_eq z
  refine ⟨n, u, v, fun γ => ?_⟩
  simpa only [map_sum, hq] using congrFun hz γ

end GaloisAlgebra

section GaloisTensor

open scoped BigOperators TensorProduct

variable {Γ R S : Type*} [Group Γ] [CommRing R] [CommRing S] [Algebra R S]

/-- Evaluation on the component of the Galois tensor map indexed by an automorphism. -/
def galoisTensorEvaluation (t : Γ →* RingAut S)
    (hR : ∀ γ r, t γ (algebraMap R S r) = algebraMap R S r) (γ : Γ) :
    S ⊗[R] S →ₐ[S] S :=
  AlgHom.liftEquiv R S S S
    { (t γ).toRingHom with commutes' := hR γ }

theorem galoisTensorEvaluation_tmul (t : Γ →* RingAut S)
    (hR : ∀ γ r, t γ (algebraMap R S r) = algebraMap R S r) (γ : Γ) (x y : S) :
    galoisTensorEvaluation t hR γ (x ⊗ₜ[R] y) = x * t γ y := by
  rw [galoisTensorEvaluation, AlgHom.liftEquiv_tmul]
  rfl

/-- Interpolating at pairwise distinct residue actions gives a
surjective Galois tensor comparison over the coefficient ring. -/
theorem galoisTensor_surjective_of_unit_differences [Fintype Γ] (t : Γ →* RingAut S)
    (hR : ∀ γ r, t γ (algebraMap R S r) = algebraMap R S r)
    (hsep : ∀ γ τ, γ ≠ τ → ∃ z : S, IsUnit (t γ z - t τ z)) :
    Function.Surjective (fun x γ => galoisTensorEvaluation t hR γ x) := by
  classical
  let q := galoisTensorEvaluation t hR
  have hq (γ : Γ) (x y : S) : q γ (x ⊗ₜ[R] y) = x * t γ y :=
    galoisTensorEvaluation_tmul t hR γ x y
  have hide (γ : Γ) : ∃ e : S ⊗[R] S, ∀ τ, q τ e = if τ = γ then 1 else 0 := by
    let A := {τ : Γ // τ ≠ γ}
    have hchoose (τ : A) : ∃ (z : S) (u : Sˣ), (u : S) = t γ z - t τ.val z := by
      exact hsep γ τ.val (Ne.symm τ.property)
    choose z u hu using hchoose
    let w (τ : A) : S ⊗[R] S :=
      (↑(u τ)⁻¹ : S) ⊗ₜ[R] z τ -
        ((↑(u τ)⁻¹ : S) * t τ.val (z τ)) ⊗ₜ[R] (1 : S)
    have hw (σ : Γ) (τ : A) :
        q σ (w τ) = (↑(u τ)⁻¹ : S) * (t σ (z τ) - t τ.val (z τ)) := by
      simp only [w, map_sub, hq, map_one, mul_one, mul_sub]
    refine ⟨∏ τ : A, w τ, fun τ => ?_⟩
    rw [map_prod]
    by_cases h : τ = γ
    · subst τ
      rw [ite_eq_left rfl]
      apply Finset.prod_eq_one
      intro σ _
      rw [hw, ← hu]
      exact (u σ).inv_mul
    · rw [ite_eq_right h]
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨τ, h⟩ : A))
      simp only [hw, sub_self, mul_zero]
  choose e he using hide
  intro f
  refine ⟨∑ γ, (f γ ⊗ₜ[R] (1 : S)) * e γ, ?_⟩
  funext τ
  change q τ (∑ γ, (f γ ⊗ₜ[R] (1 : S)) * e γ) = f τ
  simp only [map_sum, map_mul, hq, map_one, mul_one, he]
  rw [Finset.sum_eq_single τ]
  · simp
  · intro γ _ h
    rw [ite_eq_right (Ne.symm h), mul_zero]
  · simp

end GaloisTensor

section ValuationRings

open ValuativeRel Polynomial
open scoped ValuativeRel WithZero

universe u

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel F] [ValuativeRel K] [ValuativeExtension F K]

private theorem localIntegerMap_injective : Function.Injective (localIntegerMap (F := F) (K := K)) :=
  fun _ _ h => Subtype.ext ((algebraMap F K).injective (congrArg Subtype.val h))

variable [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F K]

private theorem galois_mem_localIntegers (σ : Gal(K/F)) (x : K) :
    valuation K (σ x) ≤ 1 ↔ valuation K x ≤ 1 := by
  let rK : ValuativeRel K := inferInstance
  let hExt : @ValuativeExtension F K _ _ _ rK _ := inferInstance
  let v := valuation K
  have hv : v.Compatible := inferInstanceAs ((valuation K).Compatible)
  obtain ⟨r, T, h, hl, hf, hc, hr⟩ := finiteExtension_localField (K := F) (L := K)
  let w := ValuativeRel.ofValuation (v.comap σ.toRingHom)
  have hw : @ValuativeExtension F K _ _ _ w _ := by
    constructor
    intro a b
    change v (σ (algebraMap F K a)) ≤ v (σ (algebraMap F K b)) ↔ a ≤ᵥ b
    rw [σ.commutes, σ.commutes]
    exact (@Valuation.Compatible.vle_iff_le _ _ _ _ v rK hv _ _).symm.trans
      (@ValuativeExtension.vle_iff_vle F K _ _ _ rK _ hExt _ _)
  have he : w = rK := (hr w hw).trans (hr rK hExt).symm
  have hx : @ValuativeRel.vle K _ w x 1 ↔ @ValuativeRel.vle K _ rK x 1 := by rw [he]
  change v (σ x) ≤ v (σ 1) ↔ @ValuativeRel.vle K _ rK x 1 at hx
  rw [map_one, map_one] at hx
  have hright : @ValuativeRel.vle K _ rK x 1 ↔ v x ≤ 1 := by
    have := @Valuation.Compatible.vle_iff_le _ _ _ _ v rK hv x 1
    simpa only [map_one] using this
  exact hx.trans hright

/-- A Galois automorphism of a finite extension of local fields restricts
to a ring automorphism of its valuation ring. -/
def galoisOnLocalIntegers : Gal(K/F) →* RingAut (localIntegers K) where
  toFun σ :=
    { toFun := fun x => ⟨σ (x : K), (galois_mem_localIntegers σ _).mpr x.2⟩
      invFun := fun x => ⟨σ.symm (x : K), (galois_mem_localIntegers σ.symm _).mpr x.2⟩
      left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : K))
      right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : K))
      map_mul' := fun x y => Subtype.ext (map_mul σ (x : K) (y : K))
      map_add' := fun x y => Subtype.ext (map_add σ (x : K) (y : K)) }
  map_one' := RingEquiv.ext fun _ => rfl
  map_mul' _ _ := RingEquiv.ext fun _ => rfl

theorem galoisOnLocalIntegers_apply (σ : Gal(K/F)) (x : localIntegers K) :
    (galoisOnLocalIntegers σ x : K) = σ (x : K) := rfl

private theorem galoisOnLocalIntegers_commutes (σ : Gal(K/F)) (x : localIntegers F) :
    galoisOnLocalIntegers σ (localIntegerMap x) = localIntegerMap x :=
  Subtype.ext (σ.commutes (x : F))

private theorem fixedLocalIntegers_eq_range [IsGalois F K] (x : localIntegers K) :
    (∀ σ : Gal(K/F), galoisOnLocalIntegers σ x = x) ↔
      x ∈ (localIntegerMap (F := F) (K := K)).range := by
  constructor
  · intro h
    have hx (σ : Gal(K/F)) : σ (x : K) = x := congrArg Subtype.val (h σ)
    obtain ⟨y, hy⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (x : K)).mpr hx
    refine ⟨⟨y, (localIntegerMap_mem_iff y).mp (hy.symm ▸ x.2)⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩ σ
    exact galoisOnLocalIntegers_commutes σ y

local notation "R" => 𝒪[F]
local notation "S" => 𝒪[K]

local instance localIntegerAlgebra : Algebra R S :=
  (localIntegerMap (F := F) (K := K)).toAlgebra

local instance localIntegerScalarTower : IsScalarTower R S K :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext fun _ => rfl)

private theorem localIntegers_isIntegralClosure [IsGalois F K] :
    IsIntegralClosure S R K := by
  refine ⟨Subtype.val_injective, fun {x} => ?_⟩
  constructor
  · intro h
    have h' : IsIntegral S x := h.tower_top
    have hx := (Valuation.integer.integers (valuation K)).isIntegral_iff_v_le_one.mp h'
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    let q := minpoly F (x : K)
    let a := algebraMap F K
    have ha : IsIntegral F (x : K) := Algebra.IsIntegral.isIntegral _
    have hm : q.Monic := minpoly.monic ha
    have hs : (q.map a).Splits := (inferInstance : Normal F K).splits (x : K)
    have hr : ∀ y ∈ (q.map a).roots, y ∈ (algebraMap S K).range := by
      intro y hy
      have h₁ : aeval y q = 0 := by
        rw [aeval_def, ← eval_map]
        exact (mem_roots'.mp hy).2
      obtain ⟨σ, rfl⟩ := minpoly.exists_algEquiv_of_root' (IsIntegral.isAlgebraic ha) h₁
      exact ⟨galoisOnLocalIntegers σ x, rfl⟩
    have hl : q.map a ∈ Polynomial.lifts (algebraMap S K) :=
      hs.mem_lift_of_roots_mem_range (hm.map _) _ hr
    have hq (i : ℕ) : q.coeff i ∈ (algebraMap R F).range := by
      have hc := ((Polynomial.lifts_iff_coeff_lifts (q.map a)).mp hl) i
      rw [Polynomial.coeff_map] at hc
      obtain ⟨y, hy⟩ := hc
      have hy' : valuation K (algebraMap S K y) ≤ 1 := y.2
      rw [hy] at hy'
      exact ⟨⟨q.coeff i, (localIntegerMap_mem_iff (K := K) _).mp hy'⟩, rfl⟩
    obtain ⟨p, hp⟩ := (Polynomial.mem_map_range (algebraMap R F)).mpr hq
    change p.map (algebraMap R F) = q at hp
    refine ⟨p, ?_, ?_⟩
    · apply Polynomial.monic_of_injective (IsFractionRing.injective R F)
      simpa only [hp] using hm
    · change aeval (x : K) p = 0
      rw [Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq R F K).symm, hp]
      exact minpoly.aeval F (x : K)

private theorem normalizedValuation_lt_one_iff {L : Type u} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (x : L) :
    normalizedValuation L x < 1 ↔ valuation L x < 1 := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  change e (valuation L x) < 1 ↔ _
  rw [← map_one e]
  exact e.toOrderIso.lt_iff_lt

private theorem normalizedValuation_le_iff {L : Type u} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] (x y : L) :
    normalizedValuation L x ≤ normalizedValuation L y ↔ valuation L x ≤ valuation L y :=
  (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).toOrderIso.le_iff_le

private theorem intValue_lt_one_iff (z : ℤᵐ⁰) : z < 1 ↔ z ≤ WithZero.exp (-1) := by
  by_cases hz : z = 0
  · simp [hz]
  rw [← WithZero.exp_log hz, WithZero.exp_lt_one_iff, WithZero.exp_le_exp]
  omega

private theorem irreducible_of_normalizedValuation {L : Type u} [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    (π : 𝒪[L]) (hπ : normalizedValuation L (π : L) = WithZero.exp (-1)) :
    Irreducible π := by
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr
  ext x
  symm
  have h := Set.ext_iff.mp (Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe (v := valuation L) π) x
  exact h.trans ((normalizedValuation_le_iff (x : L) (π : L)).symm.trans
    ((show normalizedValuation L (x : L) ≤ normalizedValuation L (π : L) ↔
        normalizedValuation L (x : L) < 1 by rw [hπ, intValue_lt_one_iff]).trans
      ((normalizedValuation_lt_one_iff (x : L)).trans
        ((valuation L).mem_maximalIdeal_iff (a := x)).symm)))

private theorem exists_normalizedUniformizer (L : Type u) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] :
    ∃ π : 𝒪[L], normalizedValuation L (π : L) = WithZero.exp (-1) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  obtain ⟨x, hx⟩ := valuation_surjective (e.symm (WithZero.exp (-1)))
  have hv : normalizedValuation L x = WithZero.exp (-1) := by
    change e (valuation L x) = _
    rw [hx, e.apply_symm_apply]
  refine ⟨⟨x, ((normalizedValuation_lt_one_iff x).mp ?_).le⟩, hv⟩
  rw [hv, WithZero.exp_lt_one_iff]
  decide

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [FiniteDimensional F K] in
private theorem unramified_maximalIdeal_map (h : IsUnramifiedLocalExtension F K) :
    (IsLocalRing.maximalIdeal R).map (algebraMap R S) = IsLocalRing.maximalIdeal S := by
  obtain ⟨π, hπ⟩ := exists_normalizedUniformizer F
  have hπK : normalizedValuation K ((algebraMap R S π : S) : K) = WithZero.exp (-1) := by
    change normalizedValuation K (algebraMap F K (π : F)) = _
    rw [h, hπ]
  rw [(irreducible_of_normalizedValuation π hπ).maximalIdeal_eq,
    Ideal.map_span, Set.image_singleton,
    (irreducible_of_normalizedValuation (algebraMap R S π) hπK).maximalIdeal_eq]

omit [FiniteDimensional F K] in
private theorem maximalIdeal_liesOver :
    (IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R) := by
  constructor
  ext x
  change x ∈ IsLocalRing.maximalIdeal R ↔ algebraMap R S x ∈ IsLocalRing.maximalIdeal S
  have ha : valuation K (algebraMap F K (x : F)) < 1 ↔ valuation F (x : F) < 1 := by
    rw [← not_le, ← not_le]
    rw [← (valuation K).one_vle_iff, ← (valuation F).one_vle_iff,
      ← (algebraMap F K).map_one, ValuativeExtension.vle_iff_vle]
  exact ((valuation F).mem_maximalIdeal_iff (a := x)).trans
    (ha.symm.trans ((valuation K).mem_maximalIdeal_iff (a := algebraMap R S x)).symm)

local instance localIntegerAction : MulSemiringAction Gal(K/F) S :=
  MulSemiringAction.compHom S galoisOnLocalIntegers

local instance localIntegerAction_distrib : SMulDistribClass Gal(K/F) S K where
  smul_distrib_smul g r x := map_mul g (r : K) x

private theorem unramified_inertia_trivial [IsGalois F K]
    (h : IsUnramifiedLocalExtension F K) :
    Nat.card ((IsLocalRing.maximalIdeal S).inertia Gal(K/F)) = 1 := by
  let p := IsLocalRing.maximalIdeal R
  let P := IsLocalRing.maximalIdeal S
  let : IsIntegralClosure S R K := localIntegers_isIntegralClosure
  let : Module.Finite R S := IsIntegralClosure.finite R F K S
  let : Algebra.IsIntegral R S := IsIntegralClosure.isIntegral_algebra R K
  let : IsGaloisGroup Gal(K/F) R S := IsGaloisGroup.of_isFractionRing Gal(K/F) R S F K
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr
    localIntegerMap_injective
  let : Module.Flat R S := inferInstance
  let : P.LiesOver p := maximalIdeal_liesOver
  let : Finite (R ⧸ p) := inferInstanceAs (Finite 𝓀[F])
  let : Finite p.ResidueField := inferInstance
  have hpP : p.map (algebraMap R S) = P := unramified_maximalIdeal_map h
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field R
  have hP : P ≠ ⊥ := IsDiscreteValuationRing.not_a_field S
  have hIdx : p.ramificationIdx' P = 1 := by
    apply Ideal.ramificationIdx'_eq_one_of_map_localization hpP.le hP (Ideal.primeCompl_le_nonZeroDivisors P)
    rw [IsScalarTower.algebraMap_eq R S, ← Ideal.map_map, hpP,
      Localization.AtPrime.map_eq_maximalIdeal]
  rw [Ideal.card_inertia_eq_ramificationIdxIn p P,
    Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(K/F),
    ← Ideal.ramificationIdx'_eq_ramificationIdx p P hp, hIdx]

private theorem unramified_galois_difference_unit [IsGalois F K]
    (h : IsUnramifiedLocalExtension F K) (σ τ : Gal(K/F)) (hne : σ ≠ τ) :
    ∃ x : S, IsUnit (galoisOnLocalIntegers σ x - galoisOnLocalIntegers τ x) := by
  classical
  let P := IsLocalRing.maximalIdeal S
  let H := P.inertia Gal(K/F)
  have hsub : Subsingleton H := (Nat.card_eq_one_iff_unique.mp
    (unramified_inertia_trivial h)).1
  by_contra! hh
  have hin : τ⁻¹ * σ ∈ H := by
    apply Ideal.mem_inertia.mpr
    intro x
    change galoisOnLocalIntegers (τ⁻¹ * σ) x - x ∈ P
    apply (IsLocalRing.mem_maximalIdeal _).mpr
    intro hu
    apply hh x
    have he := IsUnit.map (galoisOnLocalIntegers τ).toMonoidHom hu
    change IsUnit (galoisOnLocalIntegers τ (galoisOnLocalIntegers (τ⁻¹ * σ) x - x)) at he
    rw [map_sub, ← RingAut.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul] at he
    exact he
  have heq : (⟨τ⁻¹ * σ, hin⟩ : H) = 1 := hsub.elim _ _
  have hv : τ⁻¹ * σ = 1 := congrArg Subtype.val heq
  exact hne (inv_mul_eq_one.mp hv).symm

end ValuationRings

section AffineDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct BigOperators

universe u v
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {Γ : Type v} [Group Γ] [Fintype Γ]
local notation "U" => Spec (CommRingCat.of S)
local notation "V" => Spec (CommRingCat.of R)
local notation "f" => schemeMap (algebraMap R S)

private abbrev affineOver (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] :
    Over (Spec (CommRingCat.of R)) :=
  Over.mk (schemeMap (algebraMap R A))

/-- A semilinear action on an object over the extension ring, in terms of
its underlying scheme maps. -/
private structure SchemeAction (t : Γ →* RingAut S) (X : Over U) where
  act : Γ → (X.left ⟶ X.left)
  over (σ : Γ) : act σ ≫ X.hom = X.hom ≫ scalar t σ⁻¹
  one : act 1 = 𝟙 _
  mul (σ τ : Γ) : act (σ * τ) = act τ ≫ act σ

private def SchemeAction.transport {t : Γ →* RingAut S} {X Y : Over U}
    (a : SchemeAction t X) (i : X ≅ Y) : SchemeAction t Y where
  act σ := i.inv.left ≫ a.act σ ≫ i.hom.left
  over σ := by
    simp only [Category.assoc, Over.w i.hom]
    rw [a.over, Over.w_assoc]
  one := by simp [a.one, ← Over.comp_left]
  mul σ τ := by
    have h : i.hom.left ≫ i.inv.left = 𝟙 _ := congrArg Over.Hom.left i.hom_inv_id
    simp [a.mul, Category.assoc, reassoc_of% h]

private structure AffineQuotient {t : Γ →* RingAut S} {X : Over U}
    (a : SchemeAction t X) where
  Y : Over V
  affine : IsAffine Y.left
  p : DescentProjection f X Y
  invariant (σ : Γ) : a.act σ ≫ p.projection.left = p.projection.left
  universal {Z : Over V} (hZ : IsAffine Z.left) (q : (Over.map f).obj X ⟶ Z)
    (hq : ∀ σ, a.act σ ≫ q.left = q.left) :
      ∃! r : Y ⟶ Z, p.projection ≫ r = q

private def SchemeAction.onCoordinateRing {B : Type u} [CommRing B] [Algebra S B]
    {t : Γ →* RingAut S} (a : SchemeAction t (affineOver S B)) : Γ →* RingAut B where
  toFun σ :=
    { (Spec.preimage (a.act σ⁻¹)).hom with
      invFun := (Spec.preimage (a.act σ)).hom
      left_inv := fun b => by
        have h := congrArg Spec.preimage (a.mul σ⁻¹ σ)
        rw [inv_mul_cancel, a.one] at h
        change Spec.preimage (𝟙 (Spec (CommRingCat.of B))) = _ at h
        rw [Spec.preimage_id, Spec.preimage_comp] at h
        exact (congrArg (fun m : CommRingCat.of B ⟶ CommRingCat.of B => m.hom b) h).symm
      right_inv := fun b => by
        have h := congrArg Spec.preimage (a.mul σ σ⁻¹)
        rw [mul_inv_cancel, a.one] at h
        change Spec.preimage (𝟙 (Spec (CommRingCat.of B))) = _ at h
        rw [Spec.preimage_id, Spec.preimage_comp] at h
        exact (congrArg (fun m : CommRingCat.of B ⟶ CommRingCat.of B => m.hom b) h).symm }
  map_one' := by
    ext b
    change (Spec.preimage (a.act (1 : Γ)⁻¹)).hom b = b
    rw [inv_one, a.one]
    change (Spec.preimage (𝟙 (Spec (CommRingCat.of B)))).hom b = b
    rw [Spec.preimage_id]
    rfl
  map_mul' σ τ := by
    ext b
    change (Spec.preimage (a.act (σ * τ)⁻¹)).hom b =
      (Spec.preimage (a.act σ⁻¹)).hom ((Spec.preimage (a.act τ⁻¹)).hom b)
    rw [mul_inv_rev, a.mul, Spec.preimage_comp]
    rfl

omit [Fintype Γ] in
private theorem SchemeAction.onCoordinateRing_algebraMap
    {B : Type u} [CommRing B] [Algebra S B] {t : Γ →* RingAut S}
    (a : SchemeAction t (affineOver S B)) (σ : Γ) (c : S) :
    a.onCoordinateRing σ (algebraMap S B c) = algebraMap S B (t σ c) := by
  have h := a.over σ⁻¹
  change a.act σ⁻¹ ≫ schemeMap (algebraMap S B) =
    schemeMap (algebraMap S B) ≫ scalar t (σ⁻¹)⁻¹ at h
  have h := congrArg Spec.preimage h
  simp only [inv_inv, Spec.preimage_comp] at h
  have h' := congrArg (fun m : CommRingCat.of S ⟶ CommRingCat.of B => m.hom c) h
  simp only [Spec.preimage_map, CommRingCat.hom_comp, CommRingCat.hom_ofHom,
    RingHom.comp_apply] at h'
  exact h'

omit [Fintype Γ] in
private theorem SchemeAction.onCoordinateRing_spec
    {B : Type u} [CommRing B] [Algebra S B] {t : Γ →* RingAut S}
    (a : SchemeAction t (affineOver S B)) (σ : Γ) :
    schemeMap (a.onCoordinateRing σ).toRingHom = a.act σ⁻¹ :=
  Spec.map_preimage _

private theorem affineSpec_effective {B A : Type u} [CommRing B] [CommRing A]
    [Algebra S B] [Algebra R B] [Algebra R A] [IsScalarTower R S B]
    (ι : A →ₐ[R] B) (h : Function.Bijective (AlgHom.liftEquiv R S A B ι))
    (p : (Over.map f).obj (affineOver S B) ⟶ affineOver R A)
    (hp : p.left = schemeMap ι.toRingHom) :
    IsIso (((Over.mapPullbackAdj f).homEquiv (affineOver S B) (affineOver R A)) p) := by
  let e := AlgEquiv.ofBijective (AlgHom.liftEquiv R S A B ι) h
  let i := pullbackSpecIso R S A
  let q : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (S ⊗[R] A)) :=
    schemeMap e.toRingHom
  have : IsIso q := by
    let e' : CommRingCat.of (S ⊗[R] A) ≅ CommRingCat.of B := e.toRingEquiv.toCommRingCatIso
    change IsIso (Spec.map e'.hom)
    infer_instance
  let j := ((Over.mapPullbackAdj f).homEquiv (affineOver S B) (affineOver R A)) p
  have hleft : j.left ≫ pullback.fst (schemeMap (algebraMap R A)) f = p.left := by
    simp only [j, Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
    exact pullback.lift_fst p.left (schemeMap (algebraMap S B)) _
  have hright : j.left ≫ pullback.snd (schemeMap (algebraMap R A)) f =
      schemeMap (algebraMap S B) := Over.w j
  have heq : j.left = q ≫ i.inv ≫ (pullbackSymmetry _ _).hom := by
    apply pullback.hom_ext
    · change j.left ≫ pullback.fst (schemeMap (algebraMap R A)) f = _
      rw [hleft, hp, Category.assoc, Category.assoc]
      erw [pullbackSymmetry_hom_comp_fst]
      have hi := pullbackSpecIso_inv_snd (R := R) (S := S) (T := A)
      change i.inv ≫ pullback.snd f _ = _ at hi
      rw [hi]
      unfold q
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change ι x = (AlgHom.liftEquiv R S A B ι) (1 ⊗ₜ[R] x)
      simp [AlgHom.liftEquiv_tmul]
    · change j.left ≫ pullback.snd (schemeMap (algebraMap R A)) f = _
      rw [hright, Category.assoc, Category.assoc]
      erw [pullbackSymmetry_hom_comp_snd]
      have hi := pullbackSpecIso_inv_fst' (R := R) (S := S) (T := A)
      change i.inv ≫ pullback.fst f _ = _ at hi
      rw [hi]
      unfold q
      rw [← Spec.map_comp]
      apply congrArg Spec.map
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      change algebraMap S B x = (AlgHom.liftEquiv R S A B ι) (x ⊗ₜ[R] 1)
      simp [AlgHom.liftEquiv_tmul, Algebra.smul_def]
  have : IsIso ((Over.forget U).map j) := by
    change IsIso j.left
    rw [heq]
    infer_instance
  exact isIso_of_reflects_iso j (Over.forget U)

set_option backward.isDefEq.respectTransparency false in
private def affineSpecQuotient {B : Type u} [CommRing B] [Algebra S B]
    [Algebra R B] [IsScalarTower R S B]
    {t : Γ →* RingAut S} (a : SchemeAction t (affineOver S B))
    (hR : ∀ σ r, t σ (algebraMap R S r) = algebraMap R S r)
    (hFixed : ∀ c : S, (∀ γ, t γ c = c) → c ∈ Set.range (algebraMap R S))
    {ι : Type*} [Fintype ι] [DecidableEq Γ] (u v : ι → S)
    (hCoord : ∀ γ, ∑ i, u i * t γ (v i) = if γ = 1 then 1 else 0) :
    AffineQuotient (R := R) a := by
  let s := a.onCoordinateRing
  have hb (σ : Γ) (r : R) : s σ (algebraMap R B r) = algebraMap R B r := by
    simp only [IsScalarTower.algebraMap_apply R S B, s, a.onCoordinateRing_algebraMap, hR]
  let A := galoisFixedAlgebra s hb
  let X := affineOver S B
  let Y := affineOver R A
  let p : (Over.map f).obj X ⟶ Y := Over.homMk (schemeMap A.val.toRingHom) (by
    change schemeMap A.val.toRingHom ≫ schemeMap (algebraMap R A) =
      schemeMap (algebraMap S B) ≫ f
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (A.val.commutes r).trans (IsScalarTower.algebraMap_apply R S B r))
  refine ⟨Y, inferInstanceAs (IsAffine (Spec (CommRingCat.of A))),
    ⟨p, affineSpec_effective A.val
      (galoisFixedAlgebra_baseChange t s hb a.onCoordinateRing_algebraMap hFixed u v hCoord) p rfl⟩,
    ?_, ?_⟩
  · intro σ
    change a.act σ ≫ schemeMap A.val.toRingHom = schemeMap A.val.toRingHom
    rw [show a.act σ = schemeMap (s σ⁻¹).toRingHom by
      simpa [s] using (a.onCoordinateRing_spec σ⁻¹).symm, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact x.property σ⁻¹
  · intro Z hZ q hq
    obtain ⟨C, ⟨i⟩⟩ := (essImage_algSpec (G := Z)).mpr hZ
    let g : CommRingCat.of C.unop ⟶ CommRingCat.of B :=
      Spec.preimage (q.left ≫ i.inv.left)
    have hg (σ : Γ) (x : C.unop) : s σ (g.hom x) = g.hom x := by
      have he : a.act σ⁻¹ ≫ (q.left ≫ i.inv.left) = q.left ≫ i.inv.left := by
        rw [← Category.assoc, hq]
      have he' := congrArg Spec.preimage he
      rw [Spec.preimage_comp] at he'
      exact congrArg (fun m : CommRingCat.of C.unop ⟶ CommRingCat.of B => m.hom x) he'
    have hgc (r : R) : g.hom (algebraMap R C.unop r) = algebraMap R B r := by
      have hw := Over.w (q ≫ i.inv)
      change (q.left ≫ i.inv.left) ≫ schemeMap (algebraMap R C.unop) =
        schemeMap (algebraMap S B) ≫ f at hw
      have hh := congrArg Spec.preimage hw
      rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map,
        Spec.preimage_map] at hh
      exact (congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of B => m.hom r) hh).trans
        (IsScalarTower.algebraMap_apply R S B r).symm
    let g' : C.unop →ₐ[R] A :=
      { g.hom.codRestrict A.toSubring (fun x σ => hg σ x) with
        commutes' := fun r => Subtype.ext (hgc r) }
    let w : Y ⟶ (algSpec (CommRingCat.of R)).obj C :=
      (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom g').op
    have hw : p ≫ w = q ≫ i.inv := by
      apply Over.OverMorphism.ext
      change schemeMap A.val.toRingHom ≫ schemeMap g'.toRingHom = q.left ≫ i.inv.left
      rw [← Spec.map_comp]
      exact Spec.map_preimage _
    refine ⟨w ≫ i.hom, ?_, ?_⟩
    · change p ≫ (w ≫ i.hom) = q
      rw [← Category.assoc, hw, Category.assoc, i.inv_hom_id, Category.comp_id]
    · intro z hz
      change p ≫ z = q at hz
      rw [← cancel_mono i.inv, Category.assoc, i.hom_inv_id, Category.comp_id]
      apply Over.OverMorphism.ext
      have hh : schemeMap A.val.toRingHom ≫ (z ≫ i.inv).left =
          schemeMap A.val.toRingHom ≫ w.left := by
        exact congrArg Over.Hom.left ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ i.inv) hz).trans hw.symm))
      apply Spec.preimage_injective
      have he := congrArg Spec.preimage hh
      rw [Spec.preimage_comp, Spec.preimage_comp, Spec.preimage_map] at he
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      exact Subtype.ext (congrArg
        (fun m : CommRingCat.of C.unop ⟶ CommRingCat.of B => m.hom x) he)

open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

private structure GaloisDescentContext (t : Γ →* RingAut S) where
  commutes (σ : Γ) (r : R) : t σ (algebraMap R S r) = algebraMap R S r
  fixed_scalars (c : S) : (∀ γ, t γ c = c) → c ∈ Set.range (algebraMap R S)
  coordinates : ∃ (n : ℕ) (a b : Fin n → S),
    ∀ γ, ∑ i, a i * t γ (b i) = @ite S (γ = 1) (Classical.propDecidable _) 1 0

set_option backward.isDefEq.respectTransparency false in
private theorem affineQuotient_exists {t : Γ →* RingAut S}
    (c : GaloisDescentContext (R := R) t) {X : Over U} (a : SchemeAction t X)
    (hX : IsAffine X.left) : Nonempty (AffineQuotient (R := R) a) := by
  classical
  obtain ⟨B, ⟨i⟩⟩ := (essImage_algSpec (G := X)).mpr hX
  let B' := B.unop
  let j : affineOver S B' ≅ X := i
  letI : Algebra R B' := ((algebraMap S B').comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S B' := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨n, u, v, huv⟩ := c.coordinates
  let Q := affineSpecQuotient (R := R) (a.transport j.symm) c.commutes c.fixed_scalars u v huv
  let L := Over.map f
  let adj := Over.mapPullbackAdj f
  let q : L.obj X ⟶ Q.Y := L.map j.inv ≫ Q.p.projection
  have hq (σ : Γ) : a.act σ ≫ q.left = q.left := by
    have hj : j.inv.left ≫ j.hom.left = 𝟙 X.left := congrArg Over.Hom.left j.inv_hom_id
    have h := Q.invariant σ
    change (j.hom.left ≫ a.act σ ≫ j.inv.left) ≫ Q.p.projection.left =
      Q.p.projection.left at h
    change a.act σ ≫ j.inv.left ≫ Q.p.projection.left = j.inv.left ≫ Q.p.projection.left
    have hh := congrArg (j.inv.left ≫ ·) h
    rw [Category.assoc, ← Category.assoc j.inv.left j.hom.left, hj, Category.id_comp] at hh
    simpa only [Category.assoc] using hh
  refine ⟨⟨Q.Y, Q.affine, ⟨q, ?_⟩, hq, ?_⟩⟩
  · have := Q.p.effective
    change IsIso ((adj.homEquiv X Q.Y) (L.map j.inv ≫ Q.p.projection))
    rw [adj.homEquiv_naturality_left]
    infer_instance
  · intro Z hZ g hg
    have hg' (σ : Γ) : (a.transport j.symm).act σ ≫ (L.map j.hom ≫ g).left =
        (L.map j.hom ≫ g).left := by
      have hj : j.inv.left ≫ j.hom.left = 𝟙 X.left := congrArg Over.Hom.left j.inv_hom_id
      change (j.hom.left ≫ a.act σ ≫ j.inv.left) ≫ j.hom.left ≫ g.left =
        j.hom.left ≫ g.left
      simp only [Category.assoc, reassoc_of% hj, hg]
    obtain ⟨l, hl, hu⟩ := Q.universal hZ (L.map j.hom ≫ g) hg'
    refine ⟨l, ?_, fun m hm => hu m ?_⟩
    · change (L.map j.inv ≫ Q.p.projection) ≫ l = g
      rw [Category.assoc, hl, ← Category.assoc, ← L.map_comp, j.inv_hom_id, L.map_id,
        Category.id_comp]
    · change (L.map j.inv ≫ Q.p.projection) ≫ m = g at hm
      rw [Category.assoc] at hm
      rw [← hm, ← Category.assoc, ← L.map_comp, j.hom_inv_id, L.map_id, Category.id_comp]

private def descentComparison {X : Over U} {Y : Over V}
    (p : DescentProjection f X Y) : X ≅ (Over.pullback f).obj Y :=
  letI := p.effective
  asIso (((Over.mapPullbackAdj f).homEquiv X Y) p.projection)

private theorem descentComparison_fst {X : Over U} {Y : Over V}
    (p : DescentProjection f X Y) :
    (descentComparison p).hom.left ≫ pullback.fst Y.hom f = p.projection.left := by
  simp only [descentComparison, asIso, Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst p.projection.left X.hom _

private theorem isIso_of_fpqc_pullback [Surjective (f : U ⟶ V)] [Flat (f : U ⟶ V)]
    [QuasiCompact (f : U ⟶ V)] {Y Z : Over V} (r : Y ⟶ Z)
    (h : IsIso ((Over.pullback f).map r)) : IsIso r := by
  let g := (Over.pullback f).map r
  have h₁ : g.left ≫ pullback.snd Z.hom f = pullback.snd Y.hom f := Over.w g
  have h₂ : g.left ≫ pullback.fst Z.hom f = pullback.fst Y.hom f ≫ r.left := by
    dsimp only [g, Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  have ho : IsPullback (g.left ≫ pullback.snd Z.hom f) (pullback.fst Y.hom f)
      f (r.left ≫ Z.hom) := by
    rw [h₁, Over.w r]
    exact (IsPullback.of_hasPullback Y.hom f).flip
  have hpb := ho.of_right h₂ (IsPullback.of_hasPullback Z.hom f).flip
  have : IsIso g.left := (Over.forget U).map_isIso g
  have hr : IsIso r.left := MorphismProperty.of_isPullback_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ this
  have : IsIso ((Over.forget V).map r) := hr
  exact isIso_of_reflects_iso r (Over.forget V)

private theorem factorDescent [Surjective (f : U ⟶ V)] [Flat (f : U ⟶ V)]
    [QuasiCompact (f : U ⟶ V)] {t : Γ →* RingAut S} (c : GaloisDescentContext (R := R) t)
    {X : Over U} (a : SchemeAction t X) (hX : IsAffine X.left)
    {Y Z : Over V} (hY : IsAffine Y.left) (hZ : IsAffine Z.left)
    (p : DescentProjection f X Y) (hp : ∀ σ, a.act σ ≫ p.projection.left = p.projection.left)
    (q : (Over.map f).obj X ⟶ Z) (hq : ∀ σ, a.act σ ≫ q.left = q.left) :
    ∃ r : Y ⟶ Z, p.projection ≫ r = q := by
  obtain ⟨Q⟩ := affineQuotient_exists c a hX
  obtain ⟨g, hg, _⟩ := Q.universal hY p.projection hp
  obtain ⟨k, hk, _⟩ := Q.universal hZ q hq
  have he : (descentComparison Q.p).hom ≫ (Over.pullback f).map g = (descentComparison p).hom :=
    ((Over.mapPullbackAdj f).homEquiv_naturality_right Q.p.projection g).symm.trans
      (congrArg ((Over.mapPullbackAdj f).homEquiv X Y) hg)
  have : IsIso ((descentComparison Q.p).hom) := inferInstance
  have : IsIso ((descentComparison p).hom) := inferInstance
  have : IsIso ((Over.pullback f).map g) := IsIso.of_isIso_fac_left he
  have := isIso_of_fpqc_pullback g this
  refine ⟨inv g ≫ k, ?_⟩
  rw [← hg, Category.assoc, IsIso.hom_inv_id_assoc, hk]

private theorem descendMap
    [Surjective (f : U ⟶ V)] [Flat (f : U ⟶ V)] [QuasiCompact (f : U ⟶ V)]
    {t : Γ →* RingAut S} (c : GaloisDescentContext (R := R) t)
    {X W : Over U} (a : SchemeAction t X) (hX : IsAffine X.left)
    {Y Z : Over V} (hY : IsAffine Y.left) (hZ : IsAffine Z.left)
    (p : DescentProjection f X Y) (hp : ∀ σ, a.act σ ≫ p.projection.left = p.projection.left)
    (q : DescentProjection f W Z) {b : SchemeAction t W}
    (hq : ∀ σ, b.act σ ≫ q.projection.left = q.projection.left)
    (m : X ⟶ W) (hm : ∀ σ, a.act σ ≫ m.left = m.left ≫ b.act σ) :
    ∃ r : Y ⟶ Z, (descentComparison p).hom ≫ (Over.pullback f).map r = m ≫ (descentComparison q).hom := by
  let L := Over.map f
  let adj := Over.mapPullbackAdj f
  obtain ⟨r, hr⟩ := factorDescent c a hX hY hZ p hp (L.map m ≫ q.projection) (by
    intro σ
    change a.act σ ≫ m.left ≫ q.projection.left = m.left ≫ q.projection.left
    rw [← Category.assoc, hm, Category.assoc, hq])
  refine ⟨r, ?_⟩
  change (adj.homEquiv X Y) p.projection ≫ _ = m ≫ (adj.homEquiv W Z) q.projection
  rw [← adj.homEquiv_naturality_right, ← adj.homEquiv_naturality_left, hr]

end AffineDescent

section Semilinear

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u v
variable {S : Type u} [CommRing S] {Γ : Type v} [Group Γ]
variable {t : Γ →* RingAut S}
local notation "U" => Spec (CommRingCat.of S)

private abbrev shifted (t : Γ →* RingAut S) (σ : Γ) (T : Over U) : Over U :=
  (Over.map (scalar t σ⁻¹)).obj T

private def movePoint {X T : Over U} (a : SchemeAction t X)
    (σ : Γ) (x : T ⟶ X) : shifted t σ T ⟶ X :=
  Over.homMk (x.left ≫ a.act σ) (by rw [Category.assoc, a.over, Over.w_assoc]; rfl)

private def asSchemeAction {G : Grp (Over U)} (a : SemilinearGroupAction t G) :
    SchemeAction t G.X :=
  ⟨a.onScheme, a.onScheme_over, a.one, a.mul⟩

private theorem scalar_one : scalar t (1 : Γ) = 𝟙 U := by
  rw [scalar, map_one]
  exact Spec.map_id _

private theorem scalar_mul (σ τ : Γ) :
    scalar t (σ * τ) = scalar t σ ≫ scalar t τ := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  simp only [map_mul, CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
  rfl

private theorem pullbackAdj_left {A B : Scheme.{u}} (g : A ⟶ B)
    {X : Over A} {Y : Over B} (h : X ⟶ (Over.pullback g).obj Y) :
    (((Over.mapPullbackAdj g).homEquiv X Y).symm h).left =
      h.left ≫ pullback.fst Y.hom g := by
  simp only [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  rfl

private theorem movePoint_eq_adjoint {G : Grp (Over U)} (a : SemilinearGroupAction t G)
    {T : Over U} (σ : Γ) (x : T ⟶ G.X) :
    movePoint (asSchemeAction a) σ x =
      ((Over.mapPullbackAdj (scalar t σ⁻¹)).homEquiv T G.X).symm
        (x ≫ (a.operator σ).hom.hom.hom) := by
  apply Over.OverMorphism.ext
  rw [pullbackAdj_left]
  exact (Category.assoc _ _ _).symm

private theorem movePoint_mul {G : Grp (Over U)} (a : SemilinearGroupAction t G)
    {T : Over U} (σ : Γ) (x y : T ⟶ G.X) :
    movePoint (asSchemeAction a) σ (x * y) =
      movePoint (asSchemeAction a) σ x * movePoint (asSchemeAction a) σ y := by
  let F := Over.pullback (scalar t σ⁻¹)
  letI : GrpObj ((Over.pullback (scalar t σ⁻¹)).obj G.X) :=
    ((Over.pullback (scalar t σ⁻¹)).mapGrp.obj G).grp
  let adj := Over.mapPullbackAdj (scalar t σ⁻¹)
  let e := adj.homEquiv T G.X
  have hm (x y : shifted t σ T ⟶ G.X) : e (x * y) = e x * e y := by
    change adj.unit.app T ≫ F.map (x * y) = _
    simp only [e, Adjunction.homEquiv_apply, Functor.map_mul, MonObj.comp_mul]
    rfl
  rw [movePoint_eq_adjoint, movePoint_eq_adjoint, movePoint_eq_adjoint]
  apply e.injective
  change e (e.symm _) = e (e.symm _ * e.symm _)
  rw [hm, e.apply_symm_apply, e.apply_symm_apply, e.apply_symm_apply]
  exact MonObj.mul_comp x y (a.operator σ).hom.hom.hom

private theorem movePoint_one {G : Grp (Over U)} (a : SemilinearGroupAction t G)
    {T : Over U} (σ : Γ) :
    movePoint (asSchemeAction a) σ (1 : T ⟶ G.X) = 1 := by
  letI : GrpObj ((Over.pullback (scalar t σ⁻¹)).obj G.X) :=
    ((Over.pullback (scalar t σ⁻¹)).mapGrp.obj G).grp
  let adj := Over.mapPullbackAdj (scalar t σ⁻¹)
  let e := adj.homEquiv T G.X
  have h : e 1 = 1 := by
    simp only [e, Adjunction.homEquiv_apply, Functor.map_one, MonObj.comp_one]
    rfl
  rw [movePoint_eq_adjoint]
  apply e.injective
  change e (e.symm _) = e 1
  rw [e.apply_symm_apply, h]
  exact MonObj.one_comp (a.operator σ).hom.hom.hom

private theorem movePoint_inv {G : Grp (Over U)} (a : SemilinearGroupAction t G)
    {T : Over U} (σ : Γ) (x : T ⟶ G.X) :
    movePoint (asSchemeAction a) σ x⁻¹ = (movePoint (asSchemeAction a) σ x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← movePoint_mul, inv_mul_cancel, movePoint_one]

private theorem movePoint_constant {G : Grp (Over U)} (a : SemilinearGroupAction t G)
    {T : Over U} (σ : Γ) (x : Sections G.X) :
    movePoint (asSchemeAction a) σ (toUnit T ≫ x) =
      toUnit (shifted t σ T) ≫ a.onSection σ x := by
  apply Over.OverMorphism.ext
  change (T.hom ≫ x.left) ≫ a.onScheme σ =
    (T.hom ≫ scalar t σ⁻¹) ≫ (scalar t σ ≫ x.left ≫ a.onScheme σ)
  have h := SemilinearGroupAction.scalar_cancel t σ⁻¹
  rw [inv_inv] at h
  simp only [Category.assoc, reassoc_of% h]

private theorem leftTranslation_apply {G : Grp (Over U)}
    {T : Over U} (d : Sections G.X) (x : T ⟶ G.X) :
    x ≫ SemilinearGroupAction.leftTranslation d = (toUnit T ≫ d) * x := by
  rw [SemilinearGroupAction.leftTranslation, MonObj.comp_mul,
    Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit G.X)]

private def translatingAction {G : Grp (Over U)} (a : SemilinearGroupAction t G)
    (d : Γ → Sections G.X) (hd : ∀ σ τ, d (σ * τ) = d σ * a.onSection σ (d τ)) :
    SchemeAction t G.X where
  act := a.translatingMap d
  over σ := by
    unfold SemilinearGroupAction.translatingMap
    rw [Category.assoc, Over.w, a.onScheme_over]
  one := by
    have hOne : a.onScheme 1 = 𝟙 _ := a.one
    have h := hd 1 1
    have he : a.onSection 1 (d 1) = d 1 := by
      apply Over.OverMorphism.ext
      change scalar t (1 : Γ) ≫ (d 1).left ≫ a.onScheme 1 = (d 1).left
      rw [scalar_one, hOne, Category.id_comp, Category.comp_id]
    rw [mul_one, he] at h
    have hd₁ : d 1 = 1 := by
      have h' := congrArg (fun x => (d 1)⁻¹ * x) h
      simpa [← mul_assoc] using h'.symm
    unfold SemilinearGroupAction.translatingMap
    rw [hOne, Category.id_comp, hd₁]
    have hp := leftTranslation_apply (G := G) (1 : Sections G.X) (𝟙 G.X)
    simp only [Category.id_comp, MonObj.comp_one, one_mul] at hp
    exact congrArg Over.Hom.left hp
  mul σ τ := by
    let x : shifted t τ G.X ⟶ G.X := movePoint (asSchemeAction a) τ (𝟙 G.X)
    let y := x ≫ SemilinearGroupAction.leftTranslation (d τ)
    have hx : x.left = a.onScheme τ := Category.id_comp _
    have hy : y.left = a.translatingMap d τ :=
      congrArg (· ≫ (SemilinearGroupAction.leftTranslation (d τ)).left) hx
    let z := movePoint (asSchemeAction a) σ y
    let w := movePoint (asSchemeAction a) σ x
    have hz : z = (toUnit _ ≫ a.onSection σ (d τ)) * w := by
      dsimp only [z, y, w]
      rw [leftTranslation_apply, movePoint_mul, movePoint_constant]
    have hw : w.left = a.onScheme (σ * τ) :=
      (congrArg (· ≫ a.onScheme σ) hx).trans (a.mul σ τ).symm
    have hf : z.left = a.translatingMap d τ ≫ a.onScheme σ :=
      congrArg (· ≫ a.onScheme σ) hy
    have hp : (z ≫ SemilinearGroupAction.leftTranslation (d σ)).left =
        (w ≫ SemilinearGroupAction.leftTranslation (d (σ * τ))).left := by
      congr 1
      rw [leftTranslation_apply, leftTranslation_apply, hz, hd, MonObj.comp_mul, mul_assoc]
    unfold SemilinearGroupAction.translatingMap
    change a.onScheme (σ * τ) ≫ (SemilinearGroupAction.leftTranslation (d (σ * τ))).left =
      (a.translatingMap d τ) ≫ a.onScheme σ ≫
        (SemilinearGroupAction.leftTranslation (d σ)).left
    rw [← Category.assoc, ← hf, ← hw]
    exact hp.symm

end Semilinear

section DescentProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u v
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {Γ : Type v} [Group Γ] {t : Γ →* RingAut S}
local notation "U" => Spec (CommRingCat.of S)
local notation "V" => Spec (CommRingCat.of R)
local notation "f" => schemeMap (algebraMap R S)
local notation "F" => Over.pullback f

private theorem productLeft_ext {X Y : Over U} {Z : Scheme.{u}}
    {p q : Z ⟶ (X ⊗ Y).left}
    (h₁ : p ≫ (fst X Y).left = q ≫ (fst X Y).left)
    (h₂ : p ≫ (snd X Y).left = q ≫ (snd X Y).left) : p = q :=
  pullback.hom_ext h₁ h₂

private def productAction {X Y : Over U} (a : SchemeAction t X) (b : SchemeAction t Y) :
    SchemeAction t (X ⊗ Y) where
  act σ := (lift (movePoint a σ (fst X Y)) (movePoint b σ (snd X Y))).left
  over σ := Over.w _
  one := by
    have hfst := congrArg Over.Hom.left
      (lift_fst (movePoint a 1 (fst X Y)) (movePoint b 1 (snd X Y)))
    have hsnd := congrArg Over.Hom.left
      (lift_snd (movePoint a 1 (fst X Y)) (movePoint b 1 (snd X Y)))
    apply productLeft_ext
    · exact hfst.trans (by change _ ≫ a.act 1 = _; rw [a.one, Category.comp_id]; exact (Category.id_comp _).symm)
    · exact hsnd.trans (by change _ ≫ b.act 1 = _; rw [b.one, Category.comp_id]; exact (Category.id_comp _).symm)
  mul σ τ := by
    let l (γ : Γ) := lift (movePoint a γ (fst X Y)) (movePoint b γ (snd X Y))
    have hl₁ (γ : Γ) : (l γ).left ≫ (fst X Y).left = (fst X Y).left ≫ a.act γ :=
      congrArg Over.Hom.left (lift_fst _ _)
    have hl₂ (γ : Γ) : (l γ).left ≫ (snd X Y).left = (snd X Y).left ≫ b.act γ :=
      congrArg Over.Hom.left (lift_snd _ _)
    change (l (σ * τ)).left = (l τ).left ≫ (l σ).left
    apply productLeft_ext
    · rw [hl₁, Category.assoc, hl₁, ← Category.assoc, hl₁, a.mul, Category.assoc]
    · rw [hl₂, Category.assoc, hl₂, ← Category.assoc, hl₂, b.mul, Category.assoc]

private theorem productAction_fst {X Y : Over U} (a : SchemeAction t X) (b : SchemeAction t Y)
    (σ : Γ) : (productAction a b).act σ ≫ (fst X Y).left = (fst X Y).left ≫ a.act σ :=
  congrArg Over.Hom.left (lift_fst (movePoint a σ (fst X Y)) (movePoint b σ (snd X Y)))

private theorem productAction_snd {X Y : Over U} (a : SchemeAction t X) (b : SchemeAction t Y)
    (σ : Γ) : (productAction a b).act σ ≫ (snd X Y).left = (snd X Y).left ≫ b.act σ :=
  congrArg Over.Hom.left (lift_snd (movePoint a σ (fst X Y)) (movePoint b σ (snd X Y)))

private def terminalAction : SchemeAction t (𝟙_ (Over U)) where
  act σ := scalar t σ⁻¹
  over σ := by change scalar t σ⁻¹ ≫ 𝟙 U = 𝟙 U ≫ _; simp
  one := by rw [inv_one]; exact scalar_one
  mul σ τ := by rw [mul_inv_rev, scalar_mul]

private def projectionOfIso {X : Over U} {Y : Over V} (i : X ≅ (F).obj Y) :
    DescentProjection f X Y where
  projection := ((Over.mapPullbackAdj f).homEquiv X Y).symm i.hom
  effective := by rw [Equiv.apply_symm_apply]; infer_instance

private theorem comparisonOfIso {X : Over U} {Y : Over V} (i : X ≅ (F).obj Y) :
    descentComparison (projectionOfIso i) = i := by
  apply Iso.ext
  exact Equiv.apply_symm_apply ((Over.mapPullbackAdj f).homEquiv X Y) i.hom

private def terminalDescent : DescentProjection f (𝟙_ (Over U)) (𝟙_ (Over V)) :=
  projectionOfIso (preservesTerminalIso F).symm

private theorem terminalDescent_invariant (c : ∀ σ r, t σ (algebraMap R S r) = algebraMap R S r)
    (σ : Γ) :
    (terminalAction (t := t)).act σ ≫ (terminalDescent (R := R) (S := S)).projection.left =
      (terminalDescent (R := R) (S := S)).projection.left := by
  have h : (terminalDescent (R := R) (S := S)).projection.left = f := by
    have hw := Over.w (terminalDescent (R := R) (S := S)).projection
    change (terminalDescent (R := R) (S := S)).projection.left ≫ 𝟙 V = 𝟙 U ≫ f at hw
    exact (Category.comp_id _).symm.trans (hw.trans (Category.id_comp _))
  change scalar t σ⁻¹ ≫ _ = _
  rw [h, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact c σ⁻¹ r

private def productDescent {X W : Over U} {Y Z : Over V}
    (p : DescentProjection f X Y) (q : DescentProjection f W Z) :
    DescentProjection f (X ⊗ W) (Y ⊗ Z) :=
  projectionOfIso (tensorIso (descentComparison p) (descentComparison q) ≪≫
    (prodComparisonIso F Y Z).symm)

private theorem productDescent_comparison_fst {X W : Over U} {Y Z : Over V}
    (p : DescentProjection f X Y) (q : DescentProjection f W Z) :
    (descentComparison (productDescent p q)).hom ≫ (F).map (fst Y Z) =
      fst X W ≫ (descentComparison p).hom := by
  rw [productDescent, comparisonOfIso]
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Category.assoc]
  rw [← CartesianMonoidalCategory.prodComparison_fst F Y Z, ← Category.assoc (prodComparisonIso F Y Z).inv,
    ← prodComparisonIso_hom, Iso.inv_hom_id, Category.id_comp, tensorHom_fst]

private theorem productDescent_comparison_snd {X W : Over U} {Y Z : Over V}
    (p : DescentProjection f X Y) (q : DescentProjection f W Z) :
    (descentComparison (productDescent p q)).hom ≫ (F).map (snd Y Z) =
      snd X W ≫ (descentComparison q).hom := by
  rw [productDescent, comparisonOfIso]
  simp only [Iso.trans_hom, Iso.symm_hom, tensorIso_hom, Category.assoc]
  rw [← CartesianMonoidalCategory.prodComparison_snd F Y Z, ← Category.assoc (prodComparisonIso F Y Z).inv,
    ← prodComparisonIso_hom, Iso.inv_hom_id, Category.id_comp, tensorHom_snd]

private theorem productDescent_projection_fst {X W : Over U} {Y Z : Over V}
    (p : DescentProjection f X Y) (q : DescentProjection f W Z) :
    (productDescent p q).projection.left ≫ (fst Y Z).left =
      (fst X W).left ≫ p.projection.left := by
  have h := (productDescent_comparison_fst p q)
  apply_fun ((Over.mapPullbackAdj f).homEquiv (X ⊗ W) Y).symm at h
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm] at h
  simp only [descentComparison, asIso, Equiv.symm_apply_apply] at h
  change (productDescent p q).projection ≫ fst Y Z =
    (Over.map f).map (fst X W) ≫ p.projection at h
  exact congrArg Over.Hom.left h

private theorem productDescent_projection_snd {X W : Over U} {Y Z : Over V}
    (p : DescentProjection f X Y) (q : DescentProjection f W Z) :
    (productDescent p q).projection.left ≫ (snd Y Z).left =
      (snd X W).left ≫ q.projection.left := by
  have h := (productDescent_comparison_snd p q)
  apply_fun ((Over.mapPullbackAdj f).homEquiv (X ⊗ W) Z).symm at h
  rw [Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_naturality_left_symm] at h
  simp only [descentComparison, asIso, Equiv.symm_apply_apply] at h
  change (productDescent p q).projection ≫ snd Y Z =
    (Over.map f).map (snd X W) ≫ q.projection at h
  exact congrArg Over.Hom.left h

private theorem productDescent_invariant {X W : Over U} {Y Z : Over V}
    (p : DescentProjection f X Y) (q : DescentProjection f W Z)
    (a : SchemeAction t X) (b : SchemeAction t W)
    (hp : ∀ σ, a.act σ ≫ p.projection.left = p.projection.left)
    (hq : ∀ σ, b.act σ ≫ q.projection.left = q.projection.left) (σ : Γ) :
    (productAction a b).act σ ≫ (productDescent p q).projection.left =
      (productDescent p q).projection.left := by
  apply productLeft_ext
  · rw [Category.assoc, productDescent_projection_fst, ← Category.assoc,
      productAction_fst, Category.assoc, hp]
  · rw [Category.assoc, productDescent_projection_snd, ← Category.assoc,
      productAction_snd, Category.assoc, hq]

private theorem affine_product {B : Scheme.{u}} [IsAffine B] {X Y : Over B}
    [IsAffine X.left] [IsAffine Y.left] : IsAffine (X ⊗ Y).left :=
  inferInstanceAs (IsAffine (pullback X.hom Y.hom))

private theorem descended_product_point {X W : Over U} {Y Z T : Over V}
    (p : DescentProjection f X Y) (q : DescentProjection f W Z)
    (x : T ⟶ Y) (y : T ⟶ Z) :
    (F).map (lift x y) ≫ (descentComparison (productDescent p q)).inv =
      lift ((F).map x ≫ (descentComparison p).inv) ((F).map y ≫ (descentComparison q).inv) := by
  apply CartesianMonoidalCategory.hom_ext
  · have h := productDescent_comparison_fst p q
    have e : (descentComparison (productDescent p q)).inv ≫ fst X W =
        (F).map (fst Y Z) ≫ (descentComparison p).inv := by
      rw [← cancel_mono (descentComparison p).hom, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, ← h, Iso.inv_hom_id_assoc]
    rw [Category.assoc, e, lift_fst, ← Category.assoc, ← Functor.map_comp, lift_fst]
  · have h := productDescent_comparison_snd p q
    have e : (descentComparison (productDescent p q)).inv ≫ snd X W =
        (F).map (snd Y Z) ≫ (descentComparison q).inv := by
      rw [← cancel_mono (descentComparison q).hom, Category.assoc, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, ← h, Iso.inv_hom_id_assoc]
    rw [Category.assoc, e, lift_snd, ← Category.assoc, ← Functor.map_comp, lift_snd]

end DescentProducts

section DescendGroup

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u v
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {Γ : Type v} [Group Γ] [Fintype Γ] {t : Γ →* RingAut S}
local notation "U" => Spec (CommRingCat.of S)
local notation "V" => Spec (CommRingCat.of R)
local notation "f" => schemeMap (algebraMap R S)
local notation "F" => Over.pullback f

omit [Fintype Γ] in
private theorem unit_equivariant {G : Grp (Over U)} (a : SemilinearGroupAction t G)
    (σ : Γ) :
    (terminalAction (t := t)).act σ ≫ (η[G.X]).left =
      (η[G.X]).left ≫ (asSchemeAction a).act σ := by
  have h := congrArg Over.Hom.left (movePoint_one a (T := 𝟙_ (Over U)) σ)
  change (η[G.X]).left ≫ a.onScheme σ =
    (𝟙 U ≫ scalar t σ⁻¹) ≫ (η[G.X]).left at h
  rw [Category.id_comp] at h
  exact h.symm

omit [Fintype Γ] in
private theorem multiplication_equivariant {G : Grp (Over U)} (a : SemilinearGroupAction t G)
    (σ : Γ) :
    (productAction (asSchemeAction a) (asSchemeAction a)).act σ ≫ (μ[G.X]).left =
      (μ[G.X]).left ≫ (asSchemeAction a).act σ := by
  have hm : fst G.X G.X * snd G.X G.X = μ[G.X] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have h := movePoint_mul a σ (fst G.X G.X) (snd G.X G.X)
  rw [hm, Hom.mul_def] at h
  exact congrArg Over.Hom.left h.symm

omit [Fintype Γ] in
private theorem inverse_equivariant {G : Grp (Over U)} (a : SemilinearGroupAction t G)
    (σ : Γ) :
    (asSchemeAction a).act σ ≫ (GrpObj.inv (X := G.X)).left =
      (GrpObj.inv (X := G.X)).left ≫ (asSchemeAction a).act σ := by
  have h := movePoint_inv a σ (𝟙 G.X)
  rw [Hom.inv_def, Category.id_comp, Hom.inv_def] at h
  have hi : (movePoint (asSchemeAction a) σ (𝟙 G.X)).left = a.onScheme σ := Category.id_comp _
  exact (congrArg (· ≫ (GrpObj.inv (X := G.X)).left) hi).symm.trans
    (congrArg Over.Hom.left h.symm)

private theorem descendGroup
    [Surjective (f : U ⟶ V)] [Flat (f : U ⟶ V)] [QuasiCompact (f : U ⟶ V)]
    (c : GaloisDescentContext (R := R) t) {G : Grp (Over U)} [IsAffine G.X.left]
    (a : SemilinearGroupAction t G) (Q : AffineQuotient (R := R) (asSchemeAction a)) :
    ∃ g : GrpObj Q.Y,
      let H : Grp (Over V) := { X := Q.Y, grp := g }
      ∃ e : G ≅ (F).mapGrp.obj H, e.hom.hom.hom = (descentComparison Q.p).hom := by
  let p := Q.p
  let g := asSchemeAction a
  let Y := Q.Y
  have : IsAffine Y.left := Q.affine
  have hu : IsAffine (𝟙_ (Over U)).left := inferInstanceAs (IsAffine U)
  have hv : IsAffine (𝟙_ (Over V)).left := inferInstanceAs (IsAffine V)
  obtain ⟨o, ho⟩ := descendMap c terminalAction hu hv Q.affine terminalDescent
    (terminalDescent_invariant c.commutes) p Q.invariant (η[G.X]) (unit_equivariant a)
  obtain ⟨m, hm⟩ := descendMap c (productAction g g) affine_product affine_product Q.affine
    (productDescent p p) (productDescent_invariant p p g g Q.invariant Q.invariant)
    p Q.invariant (μ[G.X]) (multiplication_equivariant a)
  obtain ⟨j, hj⟩ := descendMap c g (inferInstanceAs (IsAffine G.X.left)) Q.affine Q.affine
    p Q.invariant p Q.invariant (GrpObj.inv (X := G.X)) (inverse_equivariant a)
  let i := descentComparison p
  let e {T : Over V} (x : T ⟶ Y) : (F).obj T ⟶ G.X := (F).map x ≫ i.inv
  have hi {T : Over V} {x y : T ⟶ Y} : e x = e y → x = y := by
    intro h
    apply (F).map_injective
    exact (cancel_mono i.inv).mp h
  have hunit {T : Over V} : e (toUnit T ≫ o) = 1 := by
    have h : (F).map (toUnit T) ≫ (descentComparison terminalDescent).inv =
        toUnit ((F).obj T) := toUnit_unique _ _
    change (F).map (toUnit T ≫ o) ≫ i.inv = _
    have ho' : (F).map o ≫ i.inv =
        (descentComparison terminalDescent).inv ≫ η[G.X] := by
      rw [← cancel_epi (descentComparison terminalDescent).hom, Iso.hom_inv_id_assoc,
        ← Category.assoc, ho, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [Functor.map_comp, Category.assoc, ho', ← Category.assoc, h]
    rfl
  have hmul {T : Over V} (x y : T ⟶ Y) : e (lift x y ≫ m) = e x * e y := by
    have hm' : (F).map m ≫ i.inv =
        (descentComparison (productDescent p p)).inv ≫ μ[G.X] := by
      rw [← cancel_epi (descentComparison (productDescent p p)).hom, Iso.hom_inv_id_assoc,
        ← Category.assoc, hm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change (F).map (lift x y ≫ m) ≫ i.inv = _
    rw [Functor.map_comp, Category.assoc, hm', ← Category.assoc, descended_product_point]
    rfl
  have hinv {T : Over V} (x : T ⟶ Y) : e (x ≫ j) = (e x)⁻¹ := by
    have hj' : (F).map j ≫ i.inv = i.inv ≫ GrpObj.inv (X := G.X) := by
      rw [← cancel_epi i.hom, Iso.hom_inv_id_assoc, ← Category.assoc]
      change (descentComparison p).hom ≫ (F).map j ≫ i.inv = _
      rw [← Category.assoc, hj, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    change (F).map (x ≫ j) ≫ i.inv = _
    rw [Functor.map_comp, Category.assoc, hj', ← Category.assoc]
    rfl
  let mon : MonObj Y :=
    { one := o
      mul := m
      one_mul := by
        apply hi
        rw [show o ▷ Y = lift (toUnit _ ≫ o) (snd _ _) by
          apply CartesianMonoidalCategory.hom_ext
          · rw [whiskerRight_fst, lift_fst]
            exact congrArg (· ≫ o) (toUnit_unique _ _)
          · simp]
        rw [hmul, hunit, one_mul, leftUnitor_hom]
      mul_one := by
        apply hi
        rw [show Y ◁ o = lift (fst _ _) (toUnit _ ≫ o) by
          apply CartesianMonoidalCategory.hom_ext
          · simp
          · rw [whiskerLeft_snd, lift_snd]
            exact congrArg (· ≫ o) (toUnit_unique _ _)]
        rw [hmul, hunit, mul_one, rightUnitor_hom]
      mul_assoc := by
        let x := fst (Y ⊗ Y) Y ≫ fst Y Y
        let y := fst (Y ⊗ Y) Y ≫ snd Y Y
        let z := snd (Y ⊗ Y) Y
        have hl : m ▷ Y = lift (lift x y ≫ m) z := by
          apply CartesianMonoidalCategory.hom_ext <;> simp [x, y, z] <;> rfl
        have hr : (α_ Y Y Y).hom ≫ (Y ◁ m) = lift x (lift y z ≫ m) := by
          apply CartesianMonoidalCategory.hom_ext
          · simp [x]
          · simp only [Category.assoc, whiskerLeft_snd, lift_snd]
            rw [← Category.assoc]
            apply congrArg (· ≫ m)
            apply CartesianMonoidalCategory.hom_ext <;> simp [y, z]
        apply hi
        rw [hl, ← Category.assoc, hr, hmul, hmul, hmul, hmul, mul_assoc] }
  let grp : GrpObj Y :=
    { toMonObj := mon
      inv := j
      left_inv := by
        apply hi
        change e (lift j (𝟙 Y) ≫ m) = e (toUnit Y ≫ o)
        rw [hmul, hunit, ← Category.id_comp j, hinv, inv_mul_cancel]
      right_inv := by
        apply hi
        change e (lift (𝟙 Y) j ≫ m) = e (toUnit Y ≫ o)
        rw [hmul, hunit, ← Category.id_comp j, hinv, mul_inv_cancel] }
  let H : Grp (Over V) := { X := Y, grp := grp }
  refine ⟨grp, ?_⟩
  let eG : G ≅ (F).mapGrp.obj H := Grp.mkIso i (by
    change η[G.X] ≫ i.hom = Functor.LaxMonoidal.ε (F) ≫ (F).map o
    rw [Functor.Monoidal.ε_of_cartesianMonoidalCategory]
    simpa only [terminalDescent, comparisonOfIso, Iso.symm_hom] using ho.symm) (by
    change μ[G.X] ≫ i.hom =
      (i.hom ⊗ₘ i.hom) ≫ Functor.LaxMonoidal.μ (F) Y Y ≫ (F).map m
    rw [Functor.Monoidal.μ_of_cartesianMonoidalCategory]
    simpa only [productDescent, comparisonOfIso, Iso.trans_hom, tensorIso_hom,
      Iso.symm_hom, Category.assoc] using hm.symm)
  exact ⟨eG, rfl⟩

end DescendGroup

section CoefficientDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ValuativeRel TensorProduct

universe u
variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel F] [ValuativeRel K] [ValuativeExtension F K]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F K] [IsGalois F K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

local notation "O₀" => localIntegers F
local notation "O₁" => localIntegers K
local notation "b" => coefficientMap (F := F) (K := K)

attribute [local instance] localIntegerAlgebra localIntegerScalarTower

private theorem valuationRingCover (h : IsUnramifiedLocalExtension F K) :
    IsFinite b ∧ Etale b ∧ Surjective b := by
  let : IsIntegralClosure O₁ O₀ K := localIntegers_isIntegralClosure
  let : Module.Finite O₀ O₁ := IsIntegralClosure.finite O₀ F K O₁
  let : FaithfulSMul O₀ O₁ := (faithfulSMul_iff_algebraMap_injective O₀ O₁).mpr
    localIntegerMap_injective
  let : Module.Flat O₀ O₁ := inferInstance
  have hm := unramified_maximalIdeal_map h
  let : IsLocalHom (algebraMap O₀ O₁) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap O₀ O₁)).out 1 3).mpr hm.le
  let : Finite (IsLocalRing.ResidueField O₀) := inferInstanceAs (Finite (residue F))
  let : Algebra.FormallyUnramified O₀ O₁ := Algebra.FormallyUnramified.of_map_maximalIdeal hm
  let : Algebra.FinitePresentation O₀ O₁ := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Etale O₀ O₁ := Algebra.Etale.of_formallyUnramified_of_flat
  let : Module.FaithfullyFlat O₀ O₁ := Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine ⟨?_, ?_, ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩⟩
  · apply (IsFinite.SpecMap_iff _).mpr
    exact (RingHom.finite_algebraMap).mpr inferInstance
  · apply (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    exact RingHom.etale_algebraMap.mpr inferInstance

theorem unramifiedValuationRingCover : UnramifiedValuationRingCover.{u} := by
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨hfin, he, hs⟩ := valuationRingCover h
  exact ⟨hfin, he, hs, galoisOnLocalIntegers, galoisOnLocalIntegers_apply⟩

private theorem coefficientDescentContext [Fintype Gal(K/F)] (h : IsUnramifiedLocalExtension F K) :
    GaloisDescentContext (R := O₀) (galoisOnLocalIntegers (F := F) (K := K)) := by
  classical
  let t := galoisOnLocalIntegers (F := F) (K := K)
  let hc := galoisOnLocalIntegers_commutes (F := F) (K := K)
  refine ⟨hc, fun c h => (fixedLocalIntegers_eq_range c).mp h, ?_⟩
  apply galoisCoordinates_of_surjective t (galoisTensorEvaluation t hc)
    (galoisTensorEvaluation_tmul t hc)
  exact galoisTensor_surjective_of_unit_differences t hc (unramified_galois_difference_unit h)

end CoefficientDescent

section DescendTorsor

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u v
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {Γ : Type v} [Group Γ] {t : Γ →* RingAut S}
local notation "U" => Spec (CommRingCat.of S)
local notation "V" => Spec (CommRingCat.of R)
local notation "f" => schemeMap (algebraMap R S)
local notation "F" => Over.pullback f

private theorem movePoint_translate {G : Grp (Over U)} (a : SemilinearGroupAction t G)
    (d : Γ → Sections G.X) (hd : ∀ σ τ, d (σ * τ) = d σ * a.onSection σ (d τ))
    {T : Over U} (σ : Γ) (x : T ⟶ G.X) :
    movePoint (translatingAction a d hd) σ x =
      (toUnit (shifted t σ T) ≫ d σ) * movePoint (asSchemeAction a) σ x := by
  rw [← leftTranslation_apply]
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).symm

private theorem rightAction_equivariant {G : Grp (Over U)} (a : SemilinearGroupAction t G)
    (d : Γ → Sections G.X) (hd : ∀ σ τ, d (σ * τ) = d σ * a.onSection σ (d τ))
    (σ : Γ) :
    (productAction (translatingAction a d hd) (asSchemeAction a)).act σ ≫ (μ[G.X]).left =
      (μ[G.X]).left ≫ (translatingAction a d hd).act σ := by
  let X := G.X
  have hm : fst X X * snd X X = μ[G.X] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have he :
      movePoint (translatingAction a d hd) σ (μ[G.X]) =
        movePoint (translatingAction a d hd) σ (fst X X) *
          movePoint (asSchemeAction a) σ (snd X X) := by
    rw [← hm, movePoint_translate, movePoint_mul, movePoint_translate, mul_assoc]
  rw [Hom.mul_def] at he
  exact congrArg Over.Hom.left he.symm

private theorem rightRegularShear_isIso (G : Grp (Over U)) :
    IsIso (lift (fst G.X G.X) (μ[G.X])) := by
  let X := G.X
  have hm : fst X X * snd X X = μ[G.X] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  let e : X ⊗ X ≅ X ⊗ X :=
    { hom := lift (fst X X) (μ[G.X])
      inv := lift (fst X X) ((fst X X)⁻¹ * snd X X)
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext
        · simp
        · simp only [Category.assoc, lift_snd, Category.id_comp, MonObj.comp_mul,
            GrpObj.comp_inv, lift_fst, ← hm, inv_mul_cancel_left]
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext
        · simp
        · simp only [Category.assoc, lift_snd, Category.id_comp, ← hm, MonObj.comp_mul,
            lift_fst, mul_inv_cancel_left] }
  exact e.isIso_hom

variable [Fintype Γ]

private theorem descendRightAction
    [Surjective (f : U ⟶ V)] [Flat (f : U ⟶ V)] [QuasiCompact (f : U ⟶ V)]
    (c : GaloisDescentContext (R := R) t) {G : Grp (Over U)} [IsAffine G.X.left]
    (a : SemilinearGroupAction t G) (d : Γ → Sections G.X)
    (hd : ∀ σ τ, d (σ * τ) = d σ * a.onSection σ (d τ))
    (Q : AffineQuotient (R := R) (asSchemeAction a))
    (P : AffineQuotient (R := R) (translatingAction a d hd)) :
    ∃ r : P.Y ⊗ Q.Y ⟶ P.Y,
      (descentComparison (productDescent P.p Q.p)).hom ≫ (F).map r =
        μ[G.X] ≫ (descentComparison P.p).hom := by
  have := P.affine
  have := Q.affine
  exact descendMap c (productAction (translatingAction a d hd) (asSchemeAction a))
    affine_product affine_product P.affine (productDescent P.p Q.p)
    (productDescent_invariant P.p Q.p _ _ P.invariant Q.invariant)
    P.p P.invariant (μ[G.X]) (rightAction_equivariant a d hd)

private theorem rightAction_comparison {G : Grp (Over U)} {P Y : Over V}
    (p : DescentProjection f G.X P) (q : DescentProjection f G.X Y)
    (r : P ⊗ Y ⟶ P) (hr : (descentComparison (productDescent p q)).hom ≫ (F).map r =
      μ[G.X] ≫ (descentComparison p).hom)
    {T : Over U} (x y : T ⟶ G.X) :
    (x * y) ≫ (descentComparison p).hom =
      lift (x ≫ (descentComparison p).hom) (y ≫ (descentComparison q).hom) ≫
        (prodComparisonIso F P Y).inv ≫ (F).map r := by
  rw [Hom.mul_def, Category.assoc, ← hr]
  rw [productDescent, comparisonOfIso]
  simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom, Category.assoc, lift_map_assoc]

private theorem rightAction_on_descended_points {G : Grp (Over U)} {P Y T : Over V}
    (p : DescentProjection f G.X P) (q : DescentProjection f G.X Y)
    (r : P ⊗ Y ⟶ P) (hr : (descentComparison (productDescent p q)).hom ≫ (F).map r =
      μ[G.X] ≫ (descentComparison p).hom)
    (x : T ⟶ P) (g : T ⟶ Y) :
    (F).map (lift x g ≫ r) ≫ (descentComparison p).inv =
      ((F).map x ≫ (descentComparison p).inv) * ((F).map g ≫ (descentComparison q).inv) := by
  have hr' : (F).map r ≫ (descentComparison p).inv =
      (descentComparison (productDescent p q)).inv ≫ μ[G.X] := by
    rw [← cancel_epi (descentComparison (productDescent p q)).hom, Iso.hom_inv_id_assoc,
      ← Category.assoc, hr, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [Functor.map_comp, Category.assoc, hr', ← Category.assoc, descended_product_point]
  rfl

private theorem descended_shear_isIso
    [Surjective (f : U ⟶ V)] [Flat (f : U ⟶ V)] [QuasiCompact (f : U ⟶ V)]
    {G : Grp (Over U)} {P Y : Over V}
    (p : DescentProjection f G.X P) (q : DescentProjection f G.X Y)
    (r : P ⊗ Y ⟶ P) (hr : (descentComparison (productDescent p q)).hom ≫ (F).map r =
      μ[G.X] ≫ (descentComparison p).hom) :
    IsIso (lift (fst P Y) r) := by
  let s := lift (fst P Y) r
  let s' := lift (fst G.X G.X) (μ[G.X])
  let i := descentComparison (productDescent p q)
  let j := descentComparison (productDescent p p)
  have h : i.hom ≫ (F).map s = s' ≫ j.hom := by
    rw [← cancel_mono (CartesianMonoidalCategory.prodComparison F P P)]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_fst, ← Functor.map_comp]
      simp only [s, lift_fst, i, j, productDescent_comparison_fst, ← Category.assoc, s']
    · simp only [Category.assoc, CartesianMonoidalCategory.prodComparison_snd, ← Functor.map_comp]
      simp only [s, lift_snd, i, j, productDescent_comparison_snd, ← Category.assoc, s', hr]
  have he : (F).map s = i.inv ≫ s' ≫ j.hom := by
    rw [← cancel_epi i.hom, Iso.hom_inv_id_assoc, h]
  apply isIso_of_fpqc_pullback (S := S)
  change IsIso ((F).map s)
  rw [he]
  have : IsIso s' := rightRegularShear_isIso G
  infer_instance

private theorem property_descends [Surjective (f : U ⟶ V)] [Flat (f : U ⟶ V)]
    [QuasiCompact (f : U ⟶ V)]
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    [P.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    {X : Over U} {Y : Over V} (i : X ≅ (F).obj Y) (h : P X.hom) : P Y.hom := by
  have : IsIso i.hom.left := (Over.forget U).map_isIso i.hom
  apply MorphismProperty.of_pullback_snd_of_descendsAlong (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (g := f) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have e : i.hom.left ≫ pullback.snd Y.hom f = X.hom := Over.w i.hom
  exact (P.cancel_left_of_respectsIso i.hom.left (pullback.snd Y.hom f)).mp (e.symm ▸ h)

end DescendTorsor

section ResidueLang

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj ValuativeRel

universe u

private theorem pullback_adj_lift {U V : Scheme.{u}} (f : U ⟶ V)
    {T : Over U} {X Y : Over V}
    (x : (Over.map f).obj T ⟶ X) (y : (Over.map f).obj T ⟶ Y) :
    ((Over.mapPullbackAdj f).homEquiv T (X ⊗ Y)) (lift x y) =
      lift (((Over.mapPullbackAdj f).homEquiv T X) x)
        (((Over.mapPullbackAdj f).homEquiv T Y) y) ≫
          (prodComparisonIso (Over.pullback f) X Y).inv := by
  let F := Over.pullback f
  let adj := Over.mapPullbackAdj f
  rw [← cancel_mono (prodComparisonIso F X Y).hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_fst,
      ← adj.homEquiv_naturality_right, lift_fst, lift_fst]
  · rw [Category.assoc, prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_snd,
      ← adj.homEquiv_naturality_right, lift_snd, lift_snd]

private def pullbackAdjGroupEquiv {U V : Scheme.{u}} (f : U ⟶ V) (T : Over U)
    (G : Grp (Over V)) :
    ((Over.map f).obj T ⟶ G.X) ≃* (T ⟶ ((Over.pullback f).mapGrp.obj G).X) where
  toEquiv := (Over.mapPullbackAdj f).homEquiv T G.X
  map_mul' x y := by
    let A := Over.pullback f
    letI : GrpObj (A.obj G.X) := (A.mapGrp.obj G).grp
    change ((Over.mapPullbackAdj f).homEquiv T G.X) (x * y) = _
    simp only [Adjunction.homEquiv_apply, Functor.map_mul, MonObj.comp_mul]
    rfl

private theorem residue_torsor_section
    {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (G : Grp (Over (integerScheme K))) {P : Over (integerScheme K)}
    [IsAffine G.X.left] [IsAffine P.left] [Smooth G.X.hom] [Smooth P.hom] [Surjective P.hom]
    [ConnectedSpace (((Over.pullback (residuePoint K)).obj G.X).left)]
    (r : P ⊗ G.X ⟶ P)
    (hOne : ∀ {T : Over (integerScheme K)} (x : T ⟶ P), lift x (1 : T ⟶ G.X) ≫ r = x)
    (hMul : ∀ {T : Over (integerScheme K)} (x : T ⟶ P) (g h : T ⟶ G.X),
      lift x (g * h) ≫ r = lift (lift x g ≫ r) h ≫ r)
    (hShear : IsIso (lift (fst P G.X) r)) :
    Nonempty (Sections P) := by
  let A := Over.pullback (residuePoint K)
  let adj := Over.mapPullbackAdj (residuePoint K)
  let H : Specs.GroupScheme (residue K) := A.mapGrp.obj G
  let X := A.obj P
  let r' : X ⊗ H.X ⟶ X := (prodComparisonIso A P G.X).inv ≫ A.map r
  have hAction {T : SchemeOver (residue K)} (x : (Over.map (residuePoint K)).obj T ⟶ P)
      (g : (Over.map (residuePoint K)).obj T ⟶ G.X) :
      (adj.homEquiv T P) (lift x g ≫ r) =
        lift ((adj.homEquiv T P) x) ((pullbackAdjGroupEquiv (residuePoint K) T G) g) ≫ r' := by
    rw [adj.homEquiv_naturality_right, pullback_adj_lift]
    exact Category.assoc _ _ _
  have hOne' {T : SchemeOver (residue K)} (x : T ⟶ X) :
      lift x (1 : T ⟶ H.X) ≫ r' = x := by
    let q := adj.homEquiv T P
    let e := pullbackAdjGroupEquiv (residuePoint K) T G
    obtain ⟨x', rfl⟩ := q.surjective x
    have h := hAction x' (1 : (Over.map (residuePoint K)).obj T ⟶ G.X)
    change q (lift _ 1 ≫ r) = lift (q x') (e 1) ≫ r' at h
    rw [map_one, hOne] at h
    exact h.symm
  have hMul' {T : SchemeOver (residue K)} (x : T ⟶ X) (g h : T ⟶ H.X) :
      lift x (g * h) ≫ r' = lift (lift x g ≫ r') h ≫ r' := by
    let q := adj.homEquiv T P
    let e := pullbackAdjGroupEquiv (residuePoint K) T G
    obtain ⟨x', rfl⟩ := q.surjective x
    obtain ⟨g', rfl⟩ := e.surjective g
    obtain ⟨h', rfl⟩ := e.surjective h
    change lift (q x') (e g' * e h') ≫ r' = lift (lift (q x') (e g') ≫ r') (e h') ≫ r'
    rw [← map_mul, ← hAction, hMul, hAction, hAction]
  let l' := lift (prod.snd : H.X ⨯ X ⟶ X) ((prod.fst : H.X ⨯ X ⟶ H.X)⁻¹) ≫ r'
  have hl' {T : SchemeOver (residue K)} (g : T ⟶ H.X) (x : T ⟶ X) :
      prod.lift g x ≫ l' = lift x g⁻¹ ≫ r' := by
    dsimp only [l']
    rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, prod.lift_snd, GrpObj.comp_inv,
      prod.lift_fst]
  let l : SchemeLeftAction H X :=
    { action := l'
      one x := by rw [hl', inv_one, hOne']
      mul g h x := by rw [hl', hl', hl', mul_inv_rev, hMul'] }
  have hl {T : SchemeOver (residue K)} (g : T ⟶ H.X) (x : T ⟶ X) :
      l.act g x = lift x g⁻¹ ≫ r' := hl' g x
  have htrans {T : SchemeOver (residue K)} (x y : T ⟶ X) : ∃ g : T ⟶ H.X, l.act g x = y := by
    let q := adj.homEquiv T P
    let e := pullbackAdjGroupEquiv (residuePoint K) T G
    obtain ⟨x', rfl⟩ := q.surjective x
    obtain ⟨y', rfl⟩ := q.surjective y
    let s := lift (fst P G.X) r
    have : IsIso s := hShear
    let z := lift x' y' ≫ inv s
    have hz : z ≫ s = lift x' y' := by simp [z]
    have hzx : z ≫ fst P G.X = x' := by
      have hh := congrArg (· ≫ fst P P) hz
      simpa only [s, Category.assoc, lift_fst] using hh
    have hzy : z ≫ r = y' := by
      have hh := congrArg (· ≫ snd P P) hz
      simpa only [s, Category.assoc, lift_snd] using hh
    refine ⟨(e (z ≫ snd P G.X))⁻¹, ?_⟩
    rw [hl, inv_inv]
    change lift (q x') (e (z ≫ snd P G.X)) ≫ r' = q y'
    rw [← hAction, ← hzx, ← CartesianMonoidalCategory.comp_lift, lift_fst_snd, Category.comp_id, hzy]
  have : LocallyOfFiniteType H.X.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd G.X.hom (residuePoint K)))
  have : QuasiCompact H.X.hom := inferInstanceAs
    (QuasiCompact (pullback.snd G.X.hom (residuePoint K)))
  have : LocallyOfFiniteType X.hom := inferInstanceAs
    (LocallyOfFiniteType (pullback.snd P.hom (residuePoint K)))
  have : QuasiCompact X.hom := inferInstanceAs
    (QuasiCompact (pullback.snd P.hom (residuePoint K)))
  have hv : Surjective X.hom := inferInstanceAs (Surjective (pullback.snd P.hom (residuePoint K)))
  have : Nonempty X.left := (X.hom.surjective).nonempty
  have : ConnectedSpace H.X.left :=
    ‹ConnectedSpace (((Over.pullback (residuePoint K)).obj G.X).left)›
  exact section_of_residueAction (K := K) (inferInstanceAs (IsAffine P.left))
    (inferInstanceAs (Smooth P.hom)) H X (Iso.refl X) l htrans

end ResidueLang

section IntegralCorrection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj ValuativeRel

universe u v

private theorem translate_section
    {Γ : Type v} [Group Γ] {S : Type u} [CommRing S]
    {t : Γ →* RingAut S} {G : Grp (Over (Spec (CommRingCat.of S)))}
    (a : SemilinearGroupAction t G) (d : Γ → Sections G.X) (σ : Γ) (x : Sections G.X) :
    (d σ * a.onSection σ x).left = scalar t σ ≫ x.left ≫ a.translatingMap d σ := by
  have h := leftTranslation_apply (d σ) (a.onSection σ x)
  let T := Over.mk (𝟙 (Spec (CommRingCat.of S)))
  have he : toUnit T ≫ d σ = d σ :=
    (congrArg (· ≫ d σ) (toUnit_unique (toUnit T) (show T ⟶ 𝟙_ _ from 𝟙 T))).trans
      (Category.id_comp _)
  rw [he] at h
  rw [← h]
  change (scalar t σ ≫ x.left ≫ a.onScheme σ) ≫
    (SemilinearGroupAction.leftTranslation (d σ)).left = _
  simp only [Category.assoc, SemilinearGroupAction.translatingMap]

private theorem fixed_baseChangedSection
    {R S : Type u} [CommRing R] [CommRing S] {Γ : Type v} [Group Γ]
    (f : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R))
    {t : Γ →* RingAut S} {G : Grp (Over (Spec (CommRingCat.of S)))}
    (a : SemilinearGroupAction t G) (d : Γ → Sections G.X)
    {P : Over (Spec (CommRingCat.of R))} (i : G.X ≅ (Over.pullback f).obj P)
    (hc : ∀ σ, scalar t σ ≫ f = f)
    (hp : ∀ σ,
      a.translatingMap d σ ≫ i.hom.left ≫ pullback.fst P.hom f =
        i.hom.left ≫ pullback.fst P.hom f)
    (q : Sections P) (σ : Γ) :
    let x := extendSection f q ≫ i.inv
    d σ * a.onSection σ x = x := by
  let x := extendSection f q ≫ i.inv
  let y := d σ * a.onSection σ x
  have e : x ≫ i.hom = extendSection f q := by simp [x]
  have hx : x.left ≫ i.hom.left ≫ pullback.fst P.hom f = f ≫ q.left := by
    rw [← Category.assoc]
    have he : x.left ≫ i.hom.left = (extendSection f q).left := congrArg Over.Hom.left e
    rw [he]
    exact pullback.lift_fst (f ≫ q.left) (𝟙 _) _
  change y = x
  rw [← cancel_mono i.hom]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (y.left ≫ i.hom.left) ≫ pullback.fst P.hom f =
      (x.left ≫ i.hom.left) ≫ pullback.fst P.hom f
    rw [Category.assoc, Category.assoc, hx]
    dsimp only [y]
    rw [translate_section, Category.assoc, Category.assoc, hp, hx, ← Category.assoc, hc]
  · exact (Over.w (y ≫ i.hom)).trans (Over.w (x ≫ i.hom)).symm

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
  [ValuativeRel F] [ValuativeRel K] [ValuativeExtension F K]
  [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F K] [IsGalois F K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

local notation "O₀" => localIntegers F
local notation "O₁" => localIntegers K
local notation "b" => coefficientMap (F := F) (K := K)
local notation "B" => Over.pullback b

attribute [local instance] localIntegerAlgebra localIntegerScalarTower

omit [FiniteDimensional F K] [IsGalois F K] in
private theorem specialConnected_of_baseChange {D : Over (integerScheme K)}
    {Y : Over (integerScheme F)} (i : D ≅ (B).obj Y)
    [GeometricallyConnected D.hom] (h : IsUnramifiedLocalExtension F K) :
    ConnectedSpace (((Over.pullback (residuePoint F)).obj Y).left) := by
  let m := localIntegerMap (F := F) (K := K)
  let : IsLocalHom m := ((IsLocalRing.local_hom_TFAE m).out 1 3).mpr
    (unramified_maximalIdeal_map h).le
  let r := schemeMap (IsLocalRing.ResidueField.map m)
  let s := residuePoint K
  let t := residuePoint F
  have hs : s ≫ b = r ≫ t := by
    change schemeMap (IsLocalRing.residue O₁) ≫ schemeMap m =
      schemeMap (IsLocalRing.ResidueField.map m) ≫ schemeMap (IsLocalRing.residue O₀)
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact (IsLocalRing.ResidueField.map_comp_residue m).symm
  let W := (Over.pullback t).obj Y
  have hpb : Over.pullback (s ≫ b) = Over.pullback (r ≫ t) := by rw [hs]
  let e : (Over.pullback s).obj D ≅ (Over.pullback r).obj W :=
    (Over.pullback s).mapIso i ≪≫ ((Over.pullbackComp s b).app Y).symm ≪≫
      (eqToIso hpb).app Y ≪≫ (Over.pullbackComp r t).app Y
  have hconn : ConnectedSpace (((Over.pullback s).obj D).left) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ (.of_hasPullback _ _)
  have : ConnectedSpace ↥(pullback W.hom r) :=
    e.hom.left.homeomorph.connectedSpace_iff.mp hconn
  have : Surjective r := inferInstanceAs (Surjective (schemeMap (IsLocalRing.ResidueField.map m)))
  exact (pullback.fst W.hom r).surjective.connectedSpace (pullback.fst W.hom r).continuous

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F K] [IsGalois F K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem comp_coefficientMap
    {t : Gal(K/F) →* RingAut (localIntegers K)}
    (hc : ∀ σ r, t σ (localIntegerMap (F := F) r) = localIntegerMap r)
    (σ : Gal(K/F)) : scalar t σ ≫ b = b := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact hc σ r

set_option backward.isDefEq.respectTransparency false in
theorem unramifiedTranslatingTorsor : UnramifiedTranslatingTorsor.{u} := by
  classical
  intro F K _ _ _ _ _ _ _ _ _ _ _ _ h t ht D ha hs hc a d hd
  have heq : t = galoisOnLocalIntegers (F := F) (K := K) := by
    apply MonoidHom.ext
    intro σ
    exact RingEquiv.ext fun x =>
      Subtype.ext ((ht σ x).trans (galoisOnLocalIntegers_apply σ x).symm)
  subst t
  let t := galoisOnLocalIntegers (F := F) (K := K)
  let f := coefficientMap (F := F) (K := K)
  let A := Over.pullback f
  letI : Fintype Gal(K/F) := Fintype.ofFinite _
  have c : GaloisDescentContext (R := localIntegers F) t := coefficientDescentContext h
  obtain ⟨hfin, het, hsurj⟩ := valuationRingCover h
  have : Flat f := inferInstance
  have : QuasiCompact f := inferInstance
  have : IsAffine D.X.left := ha
  obtain ⟨Q⟩ := affineQuotient_exists c (asSchemeAction a) ha
  obtain ⟨P⟩ := affineQuotient_exists c (translatingAction a d hd) ha
  obtain ⟨grp, e, he⟩ := descendGroup c a Q
  let H : Grp (Over (integerScheme F)) := { X := Q.Y, grp := grp }
  let X := P.Y
  let i := descentComparison P.p
  let j := descentComparison Q.p
  have hj : (Grp.forget _).mapIso e = j := Iso.ext he
  obtain ⟨r, hr⟩ := descendRightAction c a d hd Q P
  have hrIso : IsIso (lift (fst X H.X) r) := descended_shear_isIso P.p Q.p r hr
  let image {T : Over (integerScheme F)} (x : T ⟶ X) : (A).obj T ⟶ D.X :=
    (A).map x ≫ i.inv
  let groupImage {T : Over (integerScheme F)} (g : T ⟶ H.X) : (A).obj T ⟶ D.X :=
    (A).map g ≫ j.inv
  have image_inj {T : Over (integerScheme F)} {x y : T ⟶ X} :
      image x = image y → x = y :=
    fun h => (A).map_injective ((cancel_mono i.inv).mp h)
  have hgroupOne {T : Over (integerScheme F)} : groupImage (1 : T ⟶ H.X) = 1 := by
    letI : GrpObj ((A).obj H.X) := ((A).mapGrp.obj H).grp
    have hi : e.inv.hom.hom = j.inv := congrArg Iso.inv hj
    have he₁ := Functor.map_one (X := T) (M := H.X) A
    change A.map (1 : T ⟶ H.X) ≫ j.inv = _
    rw [← hi, he₁]
    exact MonObj.one_comp e.inv.hom.hom
  have hgroupMul {T : Over (integerScheme F)} (g g' : T ⟶ H.X) :
      groupImage (g * g') = groupImage g * groupImage g' := by
    letI : GrpObj ((A).obj H.X) := ((A).mapGrp.obj H).grp
    have hi : e.inv.hom.hom = j.inv := congrArg Iso.inv hj
    calc
      (A).map (g * g') ≫ j.inv = ((A).map g * (A).map g') ≫ j.inv :=
        congrArg (· ≫ j.inv) (Functor.map_mul A g g')
      _ = _ := by
        change _ = ((A).map g ≫ j.inv) * ((A).map g' ≫ j.inv)
        rw [← hi]
        exact MonObj.mul_comp _ _ e.inv.hom.hom
  have hAct {T : Over (integerScheme F)} (x : T ⟶ X) (g : T ⟶ H.X) :
      image (lift x g ≫ r) = image x * groupImage g :=
    rightAction_on_descended_points P.p Q.p r hr x g
  have hOne {T : Over (integerScheme F)} (x : T ⟶ X) :
      lift x (1 : T ⟶ H.X) ≫ r = x := by
    apply image_inj
    rw [hAct, hgroupOne, mul_one]
  have hMul {T : Over (integerScheme F)} (x : T ⟶ X) (g g' : T ⟶ H.X) :
      lift x (g * g') ≫ r = lift (lift x g ≫ r) g' ≫ r := by
    apply image_inj
    rw [hAct, hAct, hAct, hgroupMul, mul_assoc]
  have : IsAffine H.X.left := Q.affine
  have : IsAffine X.left := P.affine
  have : Smooth H.X.hom := property_descends (R := localIntegers F) (S := localIntegers K) (@Smooth) j hs
  have : Smooth X.hom := property_descends (R := localIntegers F) (S := localIntegers K) (@Smooth) i hs
  have : GeometricallyConnected D.X.hom := hc
  have : Surjective X.hom := property_descends (R := localIntegers F) (S := localIntegers K) (@Surjective) i
      (inferInstanceAs (Surjective D.X.hom))
  have : ConnectedSpace (((Over.pullback (residuePoint F)).obj H.X).left) :=
    specialConnected_of_baseChange j h
  obtain ⟨q⟩ := residue_torsor_section H r hOne hMul hrIso
  have hpt (σ : Gal(K/F)) :
      a.translatingMap d σ ≫ i.hom.left ≫ pullback.fst X.hom f =
        i.hom.left ≫ pullback.fst X.hom f := by
    have hp : i.hom.left ≫ pullback.fst X.hom f = P.p.projection.left :=
      descentComparison_fst P.p
    rw [hp]
    exact P.invariant σ
  have hfix := fixed_baseChangedSection f a d i (comp_coefficientMap c.commutes) hpt q
  refine ⟨{ group := H
            groupAffine := Q.affine
            groupSmooth := inferInstance
            specialConnected := inferInstance
            torsor := X
            torsorAffine := P.affine
            torsorSmooth := inferInstance
            torsorSurjective := inferInstance
            rightAction := r
            actOne := hOne
            actMul := hMul
            torsorIso := hrIso
            groupComparison := e
            torsorComparison := i
            groupEquivariant := ?_
            torsorEquivariant := hpt
            actionComparison := ?_
            integralSection := q
            fixed := hfix
            neutralization := ?_ }⟩
  · intro σ
    change a.onScheme σ ≫ e.hom.hom.hom.left ≫ pullback.fst H.X.hom f =
      e.hom.hom.hom.left ≫ pullback.fst H.X.hom f
    have hp : e.hom.hom.hom.left ≫ pullback.fst H.X.hom f = Q.p.projection.left :=
      (congrArg (fun g : D.X ⟶ A.obj H.X => g.left ≫ pullback.fst H.X.hom f) he).trans
        (descentComparison_fst Q.p)
    rw [hp]
    exact Q.invariant σ
  · intro T x g
    change (x * g) ≫ i.hom = lift (x ≫ i.hom) (g ≫ e.hom.hom.hom) ≫
      (prodComparisonIso A X H.X).inv ≫ (A).map r
    rw [he]
    exact rightAction_comparison P.p Q.p r hr x g
  · intro σ
    dsimp only
    rw [mul_assoc, hfix, inv_mul_cancel]

end IntegralCorrection

end
end LinearAlgebraicGroups.Arithmetic.SplitIwahoriUnramifiedTorsor
