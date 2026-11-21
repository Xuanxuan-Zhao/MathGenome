import MathGenome.Internal.Specs.D05.M15.TopPairing.VolumeDuality
import MathGenome.Internal.D05.M15.TopPairing
import MathGenome.Internal.D05.M15.InteriorProduct.Higher
import MathGenome.Internal.D05.M15.WedgeSign
import MathGenome.Internal.D05.M07.Biddual

set_option maxHeartbeats 500000
set_option maxRecDepth 2500

noncomputable section
namespace D05.M15.TopPairing.VolumeDuality
universe u v w
open Specs.D05.M15.TopPairing.VolumeDuality
abbrev D : D_type := @D_value
abbrev E : E_type := @E_value

section
variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]

theorem D_degree : D_degree (K := K) (V := V) := by
  intro p q n h ωstar x
  subst n
  simpa only [D_value, LinearMap.comp_apply, LinearMap.flip_apply,
    AlgHom.toLinearMap_apply, exteriorPower.coe_map] using
    D05.M15.InteriorProduct.Higher.degree p q
      (exteriorPower.map p (Module.Dual.eval K V) x) ωstar

theorem E_degree : E_degree (K := K) (V := V) := by
  intro p q n h ω α
  subst n
  exact D05.M15.InteriorProduct.Higher.degree p q α ω

theorem degree_zero_D : degree_zero_D (K := K) (V := V) := by
  intro ωstar
  change Specs.D05.M15.InteriorProduct.Higher.contraction_value K (Module.Dual K V)
    (_root_.ExteriorAlgebra.map (Module.Dual.eval K V) 1) ωstar = _
  rw [map_one, D05.M15.InteriorProduct.Higher.unit]
  rfl

theorem degree_zero_E : degree_zero_E (K := K) (V := V) := by
  intro ω
  change Specs.D05.M15.InteriorProduct.Higher.contraction_value K V 1 ω = _
  rw [D05.M15.InteriorProduct.Higher.unit]
  rfl

/-- The determinant pairing is symmetric after the canonical bidual embedding. -/
theorem pairing_eval (r : ℕ) (x : ⋀[K]^r V)
    (α : ⋀[K]^r (Module.Dual K V)) :
    exteriorPower.pairingDual K (Module.Dual K V) r
      (exteriorPower.map r (Module.Dual.eval K V) x) α =
        exteriorPower.pairingDual K V r α x := by
  have he : ((exteriorPower.pairingDual K (Module.Dual K V) r).comp
      (exteriorPower.map r (Module.Dual.eval K V))) =
        (exteriorPower.pairingDual K V r).flip := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro f
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.flip_apply, exteriorPower.map_apply_ιMulti,
      exteriorPower.pairingDual_ιMulti_ιMulti, Function.comp_apply,
      Module.Dual.eval_apply]
    exact (Matrix.det_transpose _).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) α

theorem wedge_map {W : Type w} [AddCommGroup W] [Module K W]
    (f : V →ₗ[K] W) (p q : ℕ) (x : ⋀[K]^p V) (y : ⋀[K]^q V) :
    exteriorPower.wedge K W p q (exteriorPower.map p f x) (exteriorPower.map q f y) =
      exteriorPower.map (p+q) f (exteriorPower.wedge K V p q x y) := by
  apply Subtype.ext
  simp only [exteriorPower.wedge, DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
    exteriorPower.coe_map]
  exact (map_mul _ _ _).symm

theorem E_pairing : E_pairing (K := K) (V := V) := by
  intro p q ω α β z hz
  obtain ⟨z', hz', he⟩ := D05.M15.InteriorProduct.Higher.pairing p q α β ω
  have hzz : z = z' := Subtype.ext (hz.trans hz'.symm)
  subst z'
  exact he

theorem D_pairing : D_pairing (K := K) (V := V) := by
  intro p q ωstar x y z hz
  obtain ⟨z', hz', he⟩ := D05.M15.InteriorProduct.Higher.pairing p q
    (exteriorPower.map p (Module.Dual.eval K V) x)
    (exteriorPower.map q (Module.Dual.eval K V) y) ωstar
  simp only [exteriorPower.coe_map] at hz'
  have hzz : z = z' := Subtype.ext (hz.trans hz'.symm)
  subst z'
  rw [pairing_eval] at he
  change _ = exteriorPower.pairingDual K (Module.Dual K V) (p+q)
    (exteriorPower.wedge K (Module.Dual K (Module.Dual K V)) p q
      (exteriorPower.map p (Module.Dual.eval K V) x)
      (exteriorPower.map q (Module.Dual.eval K V) y)) ωstar at he
  rw [wedge_map, pairing_eval] at he
  exact he

/-- In the top degree the determinant pairing with the dual basis volume is
exactly the already defined normalized coordinate. -/
theorem pairing_volume {n : ℕ} (b : Module.Basis (Fin n) K V) :
    exteriorPower.pairingDual K V n (Specs.D05.M15.DeterminantLine.volume b.dualBasis) =
      Specs.D05.M15.TopPairing.volumeCoordinate_value b := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change exteriorPower.pairingDual K V n (exteriorPower.ιMulti K n b.dualBasis)
    (exteriorPower.ιMulti K n v) =
      exteriorPower.alternatingMapLinearEquiv b.det (exteriorPower.ιMulti K n v)
  rw [D05.M15.ExteriorPairing.elementary]
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [Module.Basis.det_apply]
  congr 1
  ext i j
  exact b.dualBasis_apply i (v j)

/-- The determinant pairing separates on the right in a finite basis. -/
theorem pairing_ext_right {n : ℕ} (b : Module.Basis (Fin n) K V) (q : ℕ)
    {x y : ⋀[K]^q V}
    (he : ∀ β : ⋀[K]^q (Module.Dual K V),
      exteriorPower.pairingDual K V q β x = exteriorPower.pairingDual K V q β y) : x = y := by
  apply (b.exteriorPower q).ext_elem
  intro J
  have hh := he (b.dualBasis.exteriorPower q J)
  rw [exteriorPower.pairingDual_apply_dualBasis_exteriorPower] at hh
  simpa only [Module.Basis.dualBasis_apply] using hh

theorem map_eval_volume {n : ℕ} (b : Module.Basis (Fin n) K V) :
    exteriorPower.map n (Module.Dual.eval K V) (Specs.D05.M15.DeterminantLine.volume b) =
      Specs.D05.M15.DeterminantLine.volume b.dualBasis.dualBasis := by
  change exteriorPower.map n (Module.Dual.eval K V) (exteriorPower.ιMulti K n b) = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  ext φ
  simp [Function.comp_def, Module.Basis.dualBasis_apply]

theorem basis_D : basis_D (K := K) (V := V) := by
  intro n b p q h I
  classical
  subst n
  let : FiniteDimensional K V := Module.Finite.of_basis b
  let c := Set.powersetCard.compl (show q+p=Fintype.card (Fin (p+q)) by simp [Nat.add_comm])
  let z : ⋀[K]^q (Module.Dual K V) :=
    ⟨D_value (Specs.D05.M15.DeterminantLine.volume b.dualBasis)
      (Specs.D05.M15.ExteriorBasis.increasingWedge b p I),
      D_degree p q (p+q) rfl _ _⟩
  have he : z = Set.powersetCard.sign I •
      Specs.D05.M15.ExteriorBasis.increasingWedge b.dualBasis q (c I) := by
    apply (exteriorPower.bijective_pairingDual K V q).injective
    apply (b.exteriorPower q).ext
    intro J
    simp only [exteriorPower.basis_apply]
    rw [D_pairing p q _ _ _ z rfl]
    rw [pairing_volume]
    change Specs.D05.M15.TopPairing.scalarPairing_value K V p q (p+q) rfl
      (Specs.D05.M15.TopPairing.volumeCoordinate_value b)
      (Specs.D05.M15.ExteriorBasis.increasingWedge b p I)
      (Specs.D05.M15.ExteriorBasis.increasingWedge b q J) = _
    rw [D05.M15.TopPairing.scalar_basis]
    simp only [map_zsmul_unit, LinearMap.smul_apply]
    have hd := D05.M15.ExteriorPairing.dual_basis b q (c I) J
    simp only [D05.M15.ExteriorBasis.increasingWedge_eq_family] at hd ⊢
    change exteriorPower.pairingDual K V q _ _ = _ at hd
    rw [hd]
    have hc : I.val = J.valᶜ ↔ c I = J := by
      change I.val = J.valᶜ ↔ _
      constructor
      · intro hh; apply Subtype.ext; simpa [c, hh]
      · intro hh; have hv := congrArg Subtype.val hh; simpa [c] using congrArg Compl.compl hv
    simp only [hc]
    split_ifs <;> simp [Units.smul_def]
  exact congrArg Subtype.val he

theorem basis_E : basis_E (K := K) (V := V) := by
  intro n b p q h I
  classical
  subst n
  let c := Set.powersetCard.compl (show q+p=Fintype.card (Fin (p+q)) by simp [Nat.add_comm])
  let z : ⋀[K]^q V :=
    ⟨E_value (Specs.D05.M15.DeterminantLine.volume b)
      (Specs.D05.M15.ExteriorBasis.increasingWedge b.dualBasis p I),
      E_degree p q (p+q) rfl _ _⟩
  have he : z = Set.powersetCard.sign I •
      Specs.D05.M15.ExteriorBasis.increasingWedge b q (c I) := by
    apply pairing_ext_right b q
    intro β
    have hh : exteriorPower.pairingDual K V q β z =
        exteriorPower.pairingDual K V q β
          (Set.powersetCard.sign I • Specs.D05.M15.ExteriorBasis.increasingWedge b q (c I)) := by
      have hmap : (exteriorPower.pairingDual K V q).flip z =
          (exteriorPower.pairingDual K V q).flip
            (Set.powersetCard.sign I • Specs.D05.M15.ExteriorBasis.increasingWedge b q (c I)) := by
        apply (b.dualBasis.exteriorPower q).ext
        intro J
        simp only [exteriorPower.basis_apply]
        rw [LinearMap.flip_apply, LinearMap.flip_apply, E_pairing p q _ _ _ z rfl]
        rw [← pairing_eval, map_eval_volume, pairing_volume b.dualBasis]
        change Specs.D05.M15.TopPairing.scalarPairing_value K (Module.Dual K V) p q (p+q) rfl
          (Specs.D05.M15.TopPairing.volumeCoordinate_value b.dualBasis)
          (Specs.D05.M15.ExteriorBasis.increasingWedge b.dualBasis p I)
          (Specs.D05.M15.ExteriorBasis.increasingWedge b.dualBasis q J) = _
        rw [D05.M15.TopPairing.scalar_basis]
        simp only [map_zsmul_unit]
        have hd := D05.M15.ExteriorPairing.dual_basis b q J (c I)
        simp only [D05.M15.ExteriorBasis.increasingWedge_eq_family] at hd ⊢
        change exteriorPower.pairingDual K V q _ _ = _ at hd
        rw [hd]
        have hc : I.val = J.valᶜ ↔ J = c I := by
          constructor
          · intro hh; apply Subtype.ext; simpa [c, hh]
          · intro hh; subst J; simp [c]
        simp only [hc]
        split_ifs <;> simp [Units.smul_def]
      exact LinearMap.congr_fun hmap β
    exact hh
  exact congrArg Subtype.val he

attribute [local irreducible] D_value E_value

/-- The product of the two complement signs is the graded commutation sign.
We extract it from the already proved top wedge products, so this also works
in characteristic two. -/
theorem complement_sign {n : ℕ} (b : Module.Basis (Fin n) K V)
    (p q : ℕ) (h : p+q=n) (I : Set.powersetCard (Fin n) p) :
    let J := Set.powersetCard.compl (show q+p=Fintype.card (Fin n) by simp only [Fintype.card_fin]; omega) I
    (((Set.powersetCard.sign I : ℤ) : K) * ((Set.powersetCard.sign J : ℤ) : K)) =
      (-1 : K)^(p*q) := by
  classical
  intro J
  let x := Specs.D05.M15.ExteriorBasis.increasingWedge b p I
  let y := Specs.D05.M15.ExteriorBasis.increasingWedge b q J
  have hg : Specs.D05.M15.TopPairing.topProduct_value K V p q n h x y =
      (-1 : K)^(p*q) • Specs.D05.M15.TopPairing.topProduct_value K V q p n (by omega) y x := by
    apply Subtype.ext
    rw [D05.M15.TopPairing.product_coe, SetLike.val_smul,
      D05.M15.TopPairing.product_coe]
    exact D05.M15.WedgeSign.graded_comm p q (x : _root_.ExteriorAlgebra K V) (y : _root_.ExteriorAlgebra K V) x.property y.property
  change Specs.D05.M15.TopPairing.topProduct_value K V p q n h
    (Specs.D05.M15.ExteriorBasis.increasingWedge b p I)
    (Specs.D05.M15.ExteriorBasis.increasingWedge b q J) = _ at hg
  rw [D05.M15.TopPairing.basis_product, D05.M15.TopPairing.basis_product] at hg
  have hij : I.val = J.valᶜ := by simp [J]
  have hji : J.val = I.valᶜ := rfl
  rw [if_pos hij, if_pos hji] at hg
  have hc := congrArg (Specs.D05.M15.TopPairing.volumeCoordinate_value b) hg
  simp only [Units.smul_def, map_zsmul, map_smul,
    D05.M15.TopPairing.volume_normalization b, zsmul_eq_mul, smul_eq_mul, mul_one] at hc
  rcases Int.units_eq_one_or (Set.powersetCard.sign J) with hJ | hJ
  · simpa [hJ] using hc
  · simp only [hJ, Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one,
      mul_neg_one] at hc ⊢
    rw [hc, neg_neg]

theorem complement_sign_smul {n : ℕ} (b : Module.Basis (Fin n) K V)
    (p q : ℕ) (h : p+q=n) (I : Set.powersetCard (Fin n) p)
    {A : Type*} [AddCommGroup A] [Module K A] (a : A) :
    let J := Set.powersetCard.compl (show q+p=Fintype.card (Fin n) by simp only [Fintype.card_fin]; omega) I
    Set.powersetCard.sign I • Set.powersetCard.sign J • a = (-1 : K)^(p*q) • a := by
  intro J
  rw [Units.smul_def, Units.smul_def, ← Int.cast_smul_eq_zsmul K,
    ← Int.cast_smul_eq_zsmul K, smul_smul, complement_sign b p q h I]

theorem basis_volume_ED {n : ℕ} (b : Module.Basis (Fin n) K V)
    (p q : ℕ) (h : p+q=n) (x : ⋀[K]^p V) :
    E_value (Specs.D05.M15.DeterminantLine.volume b)
      (D_value (Specs.D05.M15.DeterminantLine.volume b.dualBasis) x) =
        (-1 : K)^(p*q) • (x : _root_.ExteriorAlgebra K V) := by
  let F := ((E_value (Specs.D05.M15.DeterminantLine.volume b)).comp
    (D_value (Specs.D05.M15.DeterminantLine.volume b.dualBasis))).comp
      (Submodule.subtype (⋀[K]^p V))
  have hf : F = (-1 : K)^(p*q) • Submodule.subtype (⋀[K]^p V) := by
    apply (b.exteriorPower p).ext
    intro I
    simp only [exteriorPower.basis_apply]
    change E_value (K := K) (V := V) (Specs.D05.M15.DeterminantLine.volume b)
      (D_value (K := K) (V := V) (Specs.D05.M15.DeterminantLine.volume b.dualBasis)
        (Specs.D05.M15.ExteriorBasis.increasingWedge b p I)) = _
    rw [basis_D b p q h I, map_zsmul_unit, basis_E b q p (by omega)]
    have hh : Set.powersetCard.compl (show p+q=Fintype.card (Fin n) by simp only [Fintype.card_fin]; omega)
        (Set.powersetCard.compl (show q+p=Fintype.card (Fin n) by simp only [Fintype.card_fin]; omega) I) = I := by
      apply Subtype.ext; simp
    rw [hh]
    exact complement_sign_smul b p q h I _
  exact LinearMap.congr_fun hf x

theorem basis_volume_DE {n : ℕ} (b : Module.Basis (Fin n) K V)
    (p q : ℕ) (h : p+q=n) (α : ⋀[K]^p (Module.Dual K V)) :
    D_value (Specs.D05.M15.DeterminantLine.volume b.dualBasis)
      (E_value (Specs.D05.M15.DeterminantLine.volume b) α) =
        (-1 : K)^(p*q) • (α : _root_.ExteriorAlgebra K (Module.Dual K V)) := by
  let F := ((D_value (Specs.D05.M15.DeterminantLine.volume b.dualBasis)).comp
    (E_value (Specs.D05.M15.DeterminantLine.volume b))).comp
      (Submodule.subtype (⋀[K]^p (Module.Dual K V)))
  have hf : F = (-1 : K)^(p*q) • Submodule.subtype (⋀[K]^p (Module.Dual K V)) := by
    apply (b.dualBasis.exteriorPower p).ext
    intro I
    simp only [exteriorPower.basis_apply]
    change D_value (K := K) (V := V) (Specs.D05.M15.DeterminantLine.volume b.dualBasis)
      (E_value (K := K) (V := V) (Specs.D05.M15.DeterminantLine.volume b)
        (Specs.D05.M15.ExteriorBasis.increasingWedge b.dualBasis p I)) = _
    rw [basis_E b p q h I, map_zsmul_unit, basis_D b q p (by omega)]
    have hh : Set.powersetCard.compl (show p+q=Fintype.card (Fin n) by simp only [Fintype.card_fin]; omega)
        (Set.powersetCard.compl (show q+p=Fintype.card (Fin n) by simp only [Fintype.card_fin]; omega) I) = I := by
      apply Subtype.ext; simp
    rw [hh]
    exact complement_sign_smul b p q h I _
  exact LinearMap.congr_fun hf α

theorem D_volume_smul (ωstar : _root_.ExteriorAlgebra K (Module.Dual K V))
    (c : K) (x : _root_.ExteriorAlgebra K V) :
    D_value (c • ωstar) x = c • D_value ωstar x := by
  unfold D_value
  change (Specs.D05.M15.InteriorProduct.Higher.contraction_value K (Module.Dual K V)
    (_root_.ExteriorAlgebra.map (Module.Dual.eval K V) x)) (c • ωstar) = _
  exact map_smul (Specs.D05.M15.InteriorProduct.Higher.contraction_value K (Module.Dual K V)
    (_root_.ExteriorAlgebra.map (Module.Dual.eval K V) x)) c ωstar

theorem E_volume_smul (ω : _root_.ExteriorAlgebra K V)
    (c : K) (α : _root_.ExteriorAlgebra K (Module.Dual K V)) :
    E_value (c • ω) α = c • E_value ω α := by
  unfold E_value
  change (Specs.D05.M15.InteriorProduct.Higher.contraction_value K V α) (c • ω) = _
  exact map_smul (Specs.D05.M15.InteriorProduct.Higher.contraction_value K V α) c ω

theorem normalized_factorization {n : ℕ} (b : Module.Basis (Fin n) K V)
    (ω : ⋀[K]^n V) (ωstar : ⋀[K]^n (Module.Dual K V))
    (hω : exteriorPower.pairingDual K V n ωstar ω = 1) :
    ∃ c d : K, ω = c • Specs.D05.M15.DeterminantLine.volume b ∧
      ωstar = d • Specs.D05.M15.DeterminantLine.volume b.dualBasis ∧ c*d=1 := by
  let c := Specs.D05.M15.TopPairing.volumeCoordinate_value b ω
  let d := Specs.D05.M15.TopPairing.volumeCoordinate_value b.dualBasis ωstar
  have hc : ω = c • Specs.D05.M15.DeterminantLine.volume b := D05.M15.TopPairing.volume_reconstruction b ω
  have hd : ωstar = d • Specs.D05.M15.DeterminantLine.volume b.dualBasis :=
    D05.M15.TopPairing.volume_reconstruction b.dualBasis ωstar
  refine ⟨c, d, hc, hd, ?_⟩
  rw [hc, hd] at hω
  simp only [map_smul, LinearMap.smul_apply, pairing_volume,
    D05.M15.TopPairing.volume_normalization b, smul_eq_mul, mul_one] at hω
  exact hω

theorem signed_ED : signed_ED (K := K) (V := V) := by
  intro n b p q h ω ωstar hω x
  obtain ⟨c, d, hc, hd, hcd⟩ := normalized_factorization b ω ωstar hω
  rw [hc, hd]
  simp only [SetLike.val_smul]
  rw [D_volume_smul, E_volume_smul, map_smul, basis_volume_ED b p q h,
    smul_smul, hcd, one_smul]

theorem signed_DE : signed_DE (K := K) (V := V) := by
  intro n b p q h ω ωstar hω α
  obtain ⟨c, d, hc, hd, hcd⟩ := normalized_factorization b ω ωstar hω
  rw [hc, hd]
  simp only [SetLike.val_smul]
  rw [E_volume_smul, D_volume_smul, map_smul, basis_volume_DE b p q h,
    smul_smul, mul_comm d c, hcd, one_smul]

/-- Restrict the actual contractions to their proved homogeneous codomains. -/
def gradedD (p q n : ℕ) (h : p+q=n) (ωstar : ⋀[K]^n (Module.Dual K V)) :
    (⋀[K]^p V) →ₗ[K] (⋀[K]^q (Module.Dual K V)) :=
  ((D_value ωstar).comp (Submodule.subtype (⋀[K]^p V))).codRestrict _
    (fun x => D_degree p q n h ωstar x)

def gradedE (p q n : ℕ) (h : p+q=n) (ω : ⋀[K]^n V) :
    (⋀[K]^p (Module.Dual K V)) →ₗ[K] (⋀[K]^q V) :=
  ((E_value ω).comp (Submodule.subtype (⋀[K]^p (Module.Dual K V)))).codRestrict _
    (fun α => E_degree p q n h ω α)

@[simp] theorem gradedD_coe (p q n : ℕ) (h : p+q=n)
    (ωstar : ⋀[K]^n (Module.Dual K V)) (x : ⋀[K]^p V) :
    (gradedD p q n h ωstar x : _root_.ExteriorAlgebra K (Module.Dual K V)) =
      D_value ωstar x := rfl

@[simp] theorem gradedE_coe (p q n : ℕ) (h : p+q=n)
    (ω : ⋀[K]^n V) (α : ⋀[K]^p (Module.Dual K V)) :
    (gradedE p q n h ω α : _root_.ExteriorAlgebra K V) = E_value ω α := rfl

theorem bijective_of_signed_inverse {A B : Type*} [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (f : A →ₗ[K] B) (g : B →ₗ[K] A)
    (s : K) (hs : s*s=1) (hgf : ∀ x, g (f x) = s • x)
    (hfg : ∀ y, f (g y) = s • y) : Function.Bijective f := by
  constructor
  · intro x y hxy
    have he := congrArg (fun z => s • g z) hxy
    simpa only [hgf, smul_smul, hs, one_smul] using he
  · intro y
    refine ⟨s • g y, ?_⟩
    rw [map_smul, hfg, smul_smul, hs, one_smul]

theorem identifications : identifications (K := K) (V := V) := by
  intro n b p q h ω ωstar hω
  have hs : (-1 : K)^(p*q) * (-1 : K)^(p*q) = 1 := by
    rcases neg_one_pow_eq_or K (p*q) with hh | hh <;> simp [hh]
  constructor
  · let d := gradedD p q n h ωstar
    let e := gradedE q p n (by omega) ω
    have hd : Function.Bijective d := bijective_of_signed_inverse d e _ hs
      (fun x => Subtype.ext (signed_ED b p q h ω ωstar hω x))
      (fun α => Subtype.ext (by
        simp only [d, e, gradedD_coe, gradedE_coe, SetLike.val_smul]
        simpa only [Nat.mul_comm] using signed_DE b q p (by omega) ω ωstar hω α))
    exact ⟨LinearEquiv.ofBijective d hd, fun _ => rfl⟩
  · let e := gradedE p q n h ω
    let d := gradedD q p n (by omega) ωstar
    have he : Function.Bijective e := bijective_of_signed_inverse e d _ hs
      (fun α => Subtype.ext (signed_DE b p q h ω ωstar hω α))
      (fun x => Subtype.ext (by
        simp only [d, e, gradedD_coe, gradedE_coe, SetLike.val_smul]
        simpa only [Nat.mul_comm] using signed_ED b q p (by omega) ω ωstar hω x))
    exact ⟨LinearEquiv.ofBijective e he, fun _ => rfl⟩

/-- Evaluation on a nonzero top vector determines a top covector. -/
theorem top_dual_ext {n : ℕ} (b : Module.Basis (Fin n) K V)
    (ω : ⋀[K]^n V) (hω : ω ≠ 0)
    {α β : ⋀[K]^n (Module.Dual K V)}
    (he : exteriorPower.pairingDual K V n α ω = exteriorPower.pairingDual K V n β ω) :
    α = β := by
  let : FiniteDimensional K V := Module.Finite.of_basis b
  let c := Specs.D05.M15.TopPairing.volumeCoordinate_value b ω
  have hr : ω = c • Specs.D05.M15.DeterminantLine.volume b :=
    D05.M15.TopPairing.volume_reconstruction b ω
  have hc : c ≠ 0 := by
    intro hzero
    apply hω
    rw [hr, hzero, zero_smul]
  have hv : exteriorPower.pairingDual K V n α (Specs.D05.M15.DeterminantLine.volume b) =
      exteriorPower.pairingDual K V n β (Specs.D05.M15.DeterminantLine.volume b) := by
    rw [hr, map_smul, map_smul] at he
    exact (smul_right_injective _ hc) he
  apply (exteriorPower.bijective_pairingDual K V n).injective
  apply LinearMap.ext
  intro z
  rw [D05.M15.TopPairing.volume_reconstruction b z]
  simp only [map_smul, hv]

theorem dual_volume_exists : dual_volume_exists (K := K) (V := V) := by
  intro n b ω hω
  let c := Specs.D05.M15.TopPairing.volumeCoordinate_value b ω
  have hr : ω = c • Specs.D05.M15.DeterminantLine.volume b :=
    D05.M15.TopPairing.volume_reconstruction b ω
  have hc : c ≠ 0 := by
    intro hzero
    apply hω
    rw [hr, hzero, zero_smul]
  let α : ⋀[K]^n (Module.Dual K V) := c⁻¹ • Specs.D05.M15.DeterminantLine.volume b.dualBasis
  have ha : exteriorPower.pairingDual K V n α ω = 1 := by
    change exteriorPower.pairingDual K V n
      (c⁻¹ • Specs.D05.M15.DeterminantLine.volume b.dualBasis) ω = _
    rw [hr]
    simp only [map_smul, LinearMap.smul_apply, pairing_volume,
      D05.M15.TopPairing.volume_normalization b, smul_eq_mul, mul_one]
    exact mul_inv_cancel₀ hc
  exact ⟨α, ha, fun β hβ => top_dual_ext b ω hω (hβ.trans ha.symm)⟩

end

theorem power_inverse_apply {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (g : V ≃ₗ[K] W) (r : ℕ) (y : ⋀[K]^r W) :
    exteriorPower.map r g.toLinearMap (exteriorPower.map r g.symm.toLinearMap y) = y := by
  have hi : g.toLinearMap.comp g.symm.toLinearMap = LinearMap.id := by
    ext z; exact g.apply_symm_apply z
  have he := congrArg (fun f : (⋀[K]^r W) →ₗ[K] (⋀[K]^r W) => f y)
    (exteriorPower.map_comp (n := r) g.symm.toLinearMap g.toLinearMap).symm
  simpa only [hi, exteriorPower.map_id, LinearMap.id_apply, LinearMap.comp_apply] using he

theorem naturality : Specs.D05.M15.TopPairing.VolumeDuality.naturality := by
  intro K V W _ _ _ _ _ n b g p q h ω ωstar ηstar hω hη x
  subst n
  let : FiniteDimensional K V := Module.Finite.of_basis b
  let : FiniteDimensional K W := Module.Finite.of_basis (b.map g)
  have hωnz : ω ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hω
    exact zero_ne_one hω
  have hdual : exteriorPower.map (p+q) g.toLinearMap.dualMap ηstar = ωstar := by
    apply top_dual_ext b ω hωnz
    rw [D05.M15.ExteriorPairing.naturality (p+q) g.toLinearMap ηstar ω, hη, hω]
  let zL := gradedD p q (p+q) rfl ηstar (exteriorPower.map p g.toLinearMap x)
  let zD := gradedD p q (p+q) rfl ωstar x
  let zR := exteriorPower.map q g.symm.toLinearMap.dualMap zD
  have hz : zL = zR := by
    apply (exteriorPower.bijective_pairingDual K W q).injective
    apply LinearMap.ext
    intro y
    calc
      exteriorPower.pairingDual K W q zL y =
          exteriorPower.pairingDual K W (p+q) ηstar
            (exteriorPower.wedge K W p q (exteriorPower.map p g.toLinearMap x) y) :=
        D_pairing p q ηstar _ y zL rfl
      _ = exteriorPower.pairingDual K W (p+q) ηstar
            (exteriorPower.map (p+q) g.toLinearMap
              (exteriorPower.wedge K V p q x (exteriorPower.map q g.symm.toLinearMap y))) := by
        rw [← wedge_map, power_inverse_apply]
      _ = exteriorPower.pairingDual K V (p+q) ωstar
            (exteriorPower.wedge K V p q x (exteriorPower.map q g.symm.toLinearMap y)) := by
        rw [← D05.M15.ExteriorPairing.naturality (p+q) g.toLinearMap ηstar, hdual]
      _ = exteriorPower.pairingDual K V q zD (exteriorPower.map q g.symm.toLinearMap y) :=
        (D_pairing p q ωstar x _ zD rfl).symm
      _ = exteriorPower.pairingDual K W q zR y :=
        (D05.M15.ExteriorPairing.naturality q g.symm.toLinearMap zD y).symm
  have hh := congrArg Subtype.val hz
  simpa only [zL, zR, zD, gradedD_coe, exteriorPower.coe_map] using hh

end D05.M15.TopPairing.VolumeDuality
