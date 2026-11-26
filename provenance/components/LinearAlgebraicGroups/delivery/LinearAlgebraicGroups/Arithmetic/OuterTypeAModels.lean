import LinearAlgebraicGroups.Arithmetic.TypeAMatrixDescentData
import LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations
import Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import LinearAlgebraicGroups.RootData.SpecialLinearDatum
import LinearAlgebraicGroups.Classification.PinnedEquivalence
import MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification
import Mathlib.LinearAlgebra.Matrix.Transvection
import Batteries.Tactic.OpenPrivate

open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.OuterTypeAModels

open Matrix Specs.OuterTypeAModels

variable {F K : Type u} [Field F] [Field K] [Algebra F K] {n : ℕ}

private theorem matrixLift_ext (hn : 2 ≤ n) {σ : Gal(K/F)}
    {p : Multiplicative (ZMod 2)} (b c : MatrixLift n σ p)
    (h : ∀ x : SpecialLinearGroup (Fin n) K, b.toAddEquiv x.val = c.toAddEquiv x.val)
    (x : Mat K n) : b.toAddEquiv x = c.toAddEquiv x := by
  have hoff (i j : Fin n) (hij : i ≠ j) :
      b.toAddEquiv (single i j 1) = c.toAddEquiv (single i j 1) := by
    let y : SpecialLinearGroup (Fin n) K :=
      ⟨transvection i j 1, det_transvection_of_ne i j hij 1⟩
    have hy := h y
    change b.toAddEquiv (1 + single i j 1) = c.toAddEquiv (1 + single i j 1) at hy
    simpa only [map_add, b.map_one, c.map_one, add_right_inj] using hy
  have hall (i j : Fin n) :
      b.toAddEquiv (single i j 1) = c.toAddEquiv (single i j 1) := by
    by_cases hij : i = j
    · subst j
      have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
      obtain ⟨j, hji⟩ := exists_ne i
      have hd : single i j (1 : K) * single j i 1 = single i i 1 := by simp
      rw [← hd]
      by_cases hp : p = 1
      · rw [b.map_mul_even hp, c.map_mul_even hp, hoff i j hji.symm, hoff j i hji]
      · rw [b.map_mul_odd hp, c.map_mul_odd hp, hoff i j hji.symm, hoff j i hji]
    · exact hoff i j hij
  induction x using Matrix.induction_on' with
  | h_zero => simp
  | h_add x y hx hy => simp only [map_add, hx, hy]
  | h_std_basis i j a =>
    have ha : a • single i j (1 : K) = single i j a := by rw [smul_single, smul_eq_mul, mul_one]
    rw [← ha]
    rw [b.map_smul, c.map_smul, hall]

private theorem parity_square (p : Multiplicative (ZMod 2)) : p * p = 1 := by
  change Multiplicative.toAdd p + Multiplicative.toAdd p = (0 : ZMod 2)
  have h : (2 : ZMod 2) = 0 := by decide
  rw [← two_mul, h, zero_mul]

private theorem parity_mul_eq_one (p q : Multiplicative (ZMod 2)) :
    p * q = 1 ↔ p = q := by
  rw [← parity_square q]
  exact mul_right_cancel_iff

private theorem parity_eq_of_odd {p q : Multiplicative (ZMod 2)}
    (hp : p ≠ 1) (hq : q ≠ 1) : p = q := by
  have h : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  have hp' : Multiplicative.toAdd p = 1 := (h _).resolve_left hp
  have hq' : Multiplicative.toAdd q = 1 := (h _).resolve_left hq
  exact hp'.trans hq'.symm

private def MatrixLift.identity (n : ℕ) {p : Multiplicative (ZMod 2)} (hp : p = 1) :
    MatrixLift (F := F) (K := K) n 1 p where
  toAddEquiv := AddEquiv.refl _
  map_one := rfl
  map_smul := fun _ _ => rfl
  map_mul_even := fun _ _ _ => rfl
  map_mul_odd := fun h => (h hp).elim

private def MatrixLift.comp {σ τ : Gal(K/F)}
    {p q r : Multiplicative (ZMod 2)}
    (b : MatrixLift n σ p) (c : MatrixLift n τ q) (hr : p * q = r) :
    MatrixLift n (σ * τ) r where
  toAddEquiv := c.toAddEquiv.trans b.toAddEquiv
  map_one := by rw [AddEquiv.trans_apply, c.map_one, b.map_one]
  map_smul a x := by
    simp only [AddEquiv.trans_apply, c.map_smul, b.map_smul, AlgEquiv.mul_apply]
  map_mul_even hp x y := by
    simp only [AddEquiv.trans_apply]
    have h := (parity_mul_eq_one p q).mp (hr.trans hp)
    by_cases hb : p = 1
    · rw [c.map_mul_even (h ▸ hb), b.map_mul_even hb]
    · rw [c.map_mul_odd (h ▸ hb), b.map_mul_odd hb]
  map_mul_odd hp' x y := by
    have hp : p * q ≠ 1 := hr ▸ hp'
    simp only [AddEquiv.trans_apply]
    by_cases hb : p = 1
    · have hc : q ≠ 1 := fun h => hp (by simp [hb, h])
      rw [c.map_mul_odd hc, b.map_mul_even hb]
    · have hc : q = 1 := by
        by_contra h
        exact hp ((parity_mul_eq_one p q).mpr (parity_eq_of_odd hb h))
      rw [c.map_mul_even hc, b.map_mul_odd hb]

private theorem eval_lift (χ : DiagramCharacter F K)
    (β : ∀ σ : Gal(K/F), MatrixLift n σ (χ σ))
    (s : Gal(K/F) →* MulAut (SpecialLinearGroup (Fin n) K))
    (h : LiftsAction χ β s) (σ : Gal(K/F)) (x : SpecialLinearGroup (Fin n) K) :
    (β σ).toAddEquiv x.val = (s σ (if χ σ = 1 then x else x⁻¹)).val := by
  by_cases hp : χ σ = 1
  · simpa only [ite_eq_left hp] using (h σ x).symm
  · simpa only [ite_eq_right hp, inv_inv] using (h σ x⁻¹).symm

theorem matrixActionLaw : MatrixActionLaw.{u} := by
  intro F K _ _ _ n hn χ β s h
  have hβ := eval_lift χ β s h
  constructor
  · intro x
    let e : MatrixLift n (1 : Gal(K/F)) (χ 1) := MatrixLift.identity n χ.map_one
    change (β 1).toAddEquiv x = e.toAddEquiv x
    refine matrixLift_ext hn (β 1) e (fun y => ?_) x
    change (β 1).toAddEquiv y.val = y.val
    rw [hβ, map_one χ, ite_eq_left rfl, map_one s]
    rfl
  · intro σ τ x
    let c := MatrixLift.comp (β σ) (β τ) (map_mul χ σ τ).symm
    change (β (σ * τ)).toAddEquiv x = c.toAddEquiv x
    refine matrixLift_ext hn (β (σ * τ)) c (fun y => ?_) x
    change (β (σ * τ)).toAddEquiv y.val = (β σ).toAddEquiv ((β τ).toAddEquiv y.val)
    rw [hβ (σ * τ), hβ τ, hβ σ]
    by_cases hs : χ σ = 1
    · simp only [map_mul χ, hs, one_mul, ite_true, map_mul s, MulAut.mul_apply]
    · by_cases ht : χ τ = 1
      · simp only [map_mul χ, ht, mul_one, ite_eq_right hs, ite_true, map_inv,
          map_mul s, MulAut.mul_apply]
      · have hst : χ σ * χ τ = 1 := (parity_mul_eq_one _ _).mpr (parity_eq_of_odd hs ht)
        simp only [map_mul χ, hst, ite_true, ite_eq_right hs, ite_eq_right ht, map_inv,
          inv_inv, map_mul s, MulAut.mul_apply]

private def conjugation {D : Type*} [Ring D] (g : Dˣ) : D ≃+* D where
  toFun x := (g : D) * x * (↑g⁻¹ : D)
  invFun x := (↑g⁻¹ : D) * x * (g : D)
  left_inv x := by
    calc
      (↑g⁻¹ : D) * ((g : D) * x * ↑g⁻¹) * g =
          ((↑g⁻¹ : D) * ↑g) * x * (↑g⁻¹ * ↑g) := by simp only [mul_assoc]
      _ = x := by simp
  right_inv x := by
    calc
      (g : D) * ((↑g⁻¹ : D) * x * g) * ↑g⁻¹ =
          ((g : D) * ↑g⁻¹) * x * (↑g * ↑g⁻¹) := by simp only [mul_assoc]
      _ = x := by simp
  map_add' x y := by simp only [mul_add, add_mul]
  map_mul' x y := by
    calc
      _ = (g : D) * x * (↑g⁻¹ * ↑g) * y * ↑g⁻¹ := by simp [mul_assoc]
      _ = _ := by simp only [mul_assoc]

private theorem conjugation_smul (g : (Mat K n)ˣ) (a : K) (x : Mat K n) :
    conjugation g (a • x) = a • conjugation g x := by
  change (g.val * (a • x)) * (↑g⁻¹ : Mat K n) =
    a • (g.val * x * (↑g⁻¹ : Mat K n))
  rw [mul_smul_comm, smul_mul_assoc]

private def conjugationLift (σ : Gal(K/F)) (p : Multiplicative (ZMod 2))
    (g : (Mat K n)ˣ) : MatrixLift n σ p := by
  let coeff : Mat K n ≃+* Mat K n := σ.toRingEquiv.mapMatrix
  have hcoeff (a : K) (x : Mat K n) : coeff (a • x) = σ a • coeff x :=
    Matrix.map_smul' σ a x (map_mul σ)
  by_cases hp : p = 1
  · let e := coeff.trans (conjugation g)
    exact
      { toAddEquiv := e.toAddEquiv
        map_one := map_one e
        map_smul := fun a x => by
          change conjugation g (coeff (a • x)) = σ a • conjugation g (coeff x)
          rw [hcoeff, conjugation_smul]
        map_mul_even := fun _ => map_mul e
        map_mul_odd := fun h => (h hp).elim }
  · refine
      { toAddEquiv := (coeff.toAddEquiv.trans (transposeAddEquiv _ _ _)).trans
          (conjugation g).toAddEquiv
        map_one := ?_
        map_smul := ?_
        map_mul_even := fun h => (hp h).elim
        map_mul_odd := ?_ }
    · change conjugation g (coeff 1).transpose = 1
      rw [map_one, transpose_one, map_one]
    · intro a x
      change conjugation g (coeff (a • x)).transpose = σ a • conjugation g (coeff x).transpose
      rw [hcoeff, transpose_smul, conjugation_smul]
    · intro _ x y
      change conjugation g (coeff (x * y)).transpose =
        conjugation g (coeff y).transpose * conjugation g (coeff x).transpose
      rw [map_mul, transpose_mul, map_mul]

private theorem conjugationLift_apply (σ : Gal(K/F)) (p : Multiplicative (ZMod 2))
    (g : (Mat K n)ˣ) (x : Mat K n) :
    (conjugationLift σ p g).toAddEquiv x =
      g.val * (if p = 1 then x.map σ else (x.map σ).transpose) * (↑g⁻¹ : Mat K n) := by
  by_cases hp : p = 1 <;> simp [conjugationLift, hp, conjugation]

theorem matrixLiftsExist : MatrixLiftsExist.{u} := by
  intro F K _ _ _ n χ g s hs
  refine ⟨fun σ => conjugationLift σ (χ σ) (g σ), ?_, fun σ => conjugationLift_apply σ (χ σ) (g σ)⟩
  intro σ x
  rw [conjugationLift_apply, hs]
  by_cases hp : χ σ = 1 <;> simp [hp]

open RM03.Brauer.SemilinearDescent (AlgebraAction)
open private fixed_csa from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification

theorem fixedInnerAlgebra : FixedInnerAlgebra.{u} := by
  intro F K _ _ _ _ _ n hn β s hs
  obtain ⟨h1, hm⟩ := matrixActionLaw hn 1 β s hs
  let ρ : AlgebraAction F K (Mat K n) :=
    { act := fun σ => (β σ).toAddEquiv
      one_act := h1
      mul_act := hm
      map_smul := fun σ => (β σ).map_smul
      map_one := fun σ => (β σ).map_one
      map_mul := fun σ => (β σ).map_mul_even rfl }
  have hn' : 0 < n := by omega
  obtain ⟨rel, hrel⟩ := RM03.Brauer.ProjectiveClassification.action_correspondence (k := F) (K := K) hn'
  let c := rel.symm ρ
  have hc := (hrel c ρ).mpr (rel.apply_symm_apply ρ)
  exact ⟨ρ, c, fun _ _ => rfl, hc, RM03.Brauer.ProjectiveClassification.descended_form hn' c ρ hc⟩

section FiniteDescent

variable [FiniteDimensional F K]
variable (χ : DiagramCharacter F K) (β : ∀ σ : Gal(K/F), MatrixLift n σ (χ σ))

private theorem diagramField_degree [IsGalois F K] (hχ : Function.Surjective χ) :
    Module.finrank F (DiagramField χ) = 2 := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index K,
    IntermediateField.fixingSubgroup_fixedField, Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr hχ, Subgroup.card_top,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2),
    Nat.card_eq_fintype_card, ZMod.card]

private def evenAction
    (h1 : ∀ x, (β 1).toAddEquiv x = x)
    (hm : ∀ σ τ x, (β (σ * τ)).toAddEquiv x = (β σ).toAddEquiv ((β τ).toAddEquiv x)) :
    AlgebraAction (DiagramField χ) K (Mat K n) :=
  let e := (IntermediateField.subgroupEquivAlgEquiv χ.ker).symm
  { act := fun g => (β (e g).val).toAddEquiv
    one_act := fun x => by rw [map_one e]; exact h1 x
    mul_act := fun g h x => by rw [map_mul e]; exact hm (e g).val (e h).val x
    map_smul := fun g a x => by
      rw [(β (e g).val).map_smul]
      rfl
    map_one := fun g => (β (e g).val).map_one
    map_mul := fun g => (β (e g).val).map_mul_even (e g).property }

variable {χ β} in
private theorem evenAction_on_subgroup
    (h1 : ∀ x, (β 1).toAddEquiv x = x)
    (hm : ∀ σ τ x, (β (σ * τ)).toAddEquiv x = (β σ).toAddEquiv ((β τ).toAddEquiv x))
    (g : χ.ker) (x : Mat K n) :
    (evenAction χ β h1 hm).act (IntermediateField.subgroupEquivAlgEquiv χ.ker g) x =
      (β g.val).toAddEquiv x := by
  dsimp only [evenAction]
  rw [MulEquiv.symm_apply_apply]

variable {χ β} in
private theorem evenAction_mem_fixed
    (h1 : ∀ x, (β 1).toAddEquiv x = x)
    (hm : ∀ σ τ x, (β (σ * τ)).toAddEquiv x = (β σ).toAddEquiv ((β τ).toAddEquiv x))
    (x : Mat K n) :
    x ∈ (evenAction χ β h1 hm).fixedSubalgebra ↔
      ∀ g : χ.ker, (β g.val).toAddEquiv x = x := by
  constructor
  · intro hx g
    exact (evenAction_on_subgroup h1 hm g x).symm.trans
      (hx (IntermediateField.subgroupEquivAlgEquiv χ.ker g))
  · intro hx g
    obtain ⟨a, rfl⟩ := (IntermediateField.subgroupEquivAlgEquiv χ.ker).surjective g
    exact (evenAction_on_subgroup h1 hm a x).trans (hx a)

theorem fixedAlgebraWithInvolution : FixedAlgebraWithInvolution.{u} := by
  intro F K _ _ _ _ _ n hn χ hχ β s hs
  obtain ⟨h1, hm⟩ := matrixActionLaw hn χ β s hs
  let E := DiagramField χ
  let ρ := evenAction χ β h1 hm
  let A := ρ.fixedSubalgebra
  have memA (x : Mat K n) : x ∈ A ↔ ∀ g : χ.ker, (β g.val).toAddEquiv x = x :=
    evenAction_mem_fixed h1 hm x
  have hCSA := fixed_csa (by omega : 0 < n) ρ
  refine ⟨diagramField_degree χ hχ, ρ, evenAction_on_subgroup h1 hm, hCSA,
    RM03.CSA.degree_eq_matrix_size hCSA ρ.descentEquiv,
    ⟨ρ.descentEquiv, ρ.descentEquiv_tmul⟩, ?_⟩
  obtain ⟨σ, hσ⟩ := hχ (Multiplicative.ofAdd (1 : ZMod 2))
  have hodd : χ σ ≠ 1 := hσ.trans_ne (by decide)
  have hstable (x : A) : (β σ).toAddEquiv x.val ∈ A := by
    apply (memA _).mpr
    intro g
    let g' : χ.ker := ⟨σ⁻¹ * g.val * σ, by
      have hg : χ g.val = 1 := g.property
      simp [map_mul, hg]⟩
    have heq : σ * g'.val = g.val * σ := by simp [g', ← mul_assoc]
    rw [← hm, ← heq, hm, (memA _).mp x.property g']
  have hsquare (x : A) : (β σ).toAddEquiv ((β σ).toAddEquiv x.val) = x.val := by
    rw [← hm]
    exact (memA _).mp x.property ⟨σ * σ, by simp only [MonoidHom.mem_ker, map_mul, parity_square]⟩
  let flip (x : A) : A := ⟨(β σ).toAddEquiv x.val, hstable x⟩
  have hinv (x : A) : flip (flip x) = x := Subtype.ext (hsquare x)
  let star : A ≃+* Aᵐᵒᵖ :=
    { toFun := fun x => MulOpposite.op (flip x)
      invFun := fun x => flip x.unop
      left_inv := hinv
      right_inv := fun x => MulOpposite.unop_injective (hinv x.unop)
      map_add' := fun x y => congrArg MulOpposite.op (Subtype.ext (map_add (β σ).toAddEquiv x.val y.val))
      map_mul' := fun x y => congrArg MulOpposite.op
        (Subtype.ext ((β σ).map_mul_odd hodd x.val y.val)) }
  let bar := (AlgEquiv.restrictNormalHom E) σ
  have hbar (τ : Gal(K/F)) (ht : χ τ ≠ 1) :
      (AlgEquiv.restrictNormalHom E) τ = bar := by
    have hp := parity_eq_of_odd hodd ht
    have heven : σ⁻¹ * τ ∈ χ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hp, inv_mul_cancel]
    have hfixed : σ⁻¹ * τ ∈ (AlgEquiv.restrictNormalHom E).ker := by
      rwa [IntermediateField.restrictNormalHom_ker,
        IntermediateField.fixingSubgroup_fixedField]
    symm
    simpa only [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] using hfixed
  refine ⟨bar, star, ?_, ?_, hinv, ?_, ?_⟩
  · intro h
    apply hodd
    change σ ∈ χ.ker
    rw [← IntermediateField.fixingSubgroup_fixedField χ.ker, ← IntermediateField.restrictNormalHom_ker]
    exact h
  · intro a
    apply MulOpposite.unop_injective
    apply Subtype.ext
    change (β σ).toAddEquiv (algebraMap E (Mat K n) a) =
      algebraMap E (Mat K n) (bar a)
    have hscalar (b : E) : algebraMap E (Mat K n) b = (b : K) • (1 : Mat K n) :=
      (IsScalarTower.algebraMap_apply E K (Mat K n) b).trans (Algebra.algebraMap_eq_smul_one _)
    rw [hscalar a, hscalar (bar a), (β σ).map_smul, (β σ).map_one,
      AlgEquiv.restrictNormalHom_apply E σ a]
  · intro τ ht x
    change (β σ).toAddEquiv x.val = (β τ).toAddEquiv x.val
    have hp := parity_eq_of_odd hodd ht
    let g : χ.ker := ⟨σ⁻¹ * τ, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hp, inv_mul_cancel]⟩
    have heq : σ * g.val = τ := by simp [g]
    rw [← heq, hm, (memA _).mp x.property g]
  · intro τ ht a
    rw [← hbar τ ht]
    exact AlgEquiv.restrictNormalHom_apply E τ a

end FiniteDescent

section BasedDatum

open Specs.Pinning (BasedRootDatum BasedIso)

private theorem matched_root_pairs
    (P Q : BasedRootDatum.{u})
    (f : P.X ≃ₗ[ℤ] Q.X) (g : P.Y ≃ₗ[ℤ] Q.Y)
    (hpair : ∀ x y, Q.datum.toLinearMap (f x) (g y) = P.datum.toLinearMap x y)
    (e : P.base.support ≃ Q.base.support)
    (hroot : ∀ i : P.base.support, f (P.datum.root i) = Q.datum.root (e i))
    (hcoroot : ∀ i : P.base.support, g (P.datum.coroot i) = Q.datum.coroot (e i))
    (i : P.I) :
    ∃ j : Q.I, f (P.datum.root i) = Q.datum.root j ∧
      g (P.datum.coroot i) = Q.datum.coroot j := by
  have : Finite P.I := P.finiteRoots
  have : P.datum.IsReduced := P.reduced
  have : P.datum.IsCrystallographic := ⟨fun _ _ => ⟨_, rfl⟩⟩
  refine P.base.induction_reflect i (p := fun l =>
    ∃ j : Q.I, f (P.datum.root l) = Q.datum.root j ∧
      g (P.datum.coroot l) = Q.datum.coroot j) ?_ ?_ ?_
  · rintro l ⟨j, hr, hc⟩
    refine ⟨Q.datum.reflectionPerm j j, ?_, ?_⟩
    · simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, map_neg, hr]
    · simp only [RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply_self, map_neg, hc]
  · intro l hl
    exact ⟨e ⟨l, hl⟩, hroot ⟨l, hl⟩, hcoroot ⟨l, hl⟩⟩
  · rintro l k ⟨j, hr, hc⟩ hk
    let a : P.base.support := ⟨k, hk⟩
    refine ⟨Q.datum.reflectionPerm (e a) j, ?_, ?_⟩
    · simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply, map_sub,
        map_smul, hr, show f (P.datum.root k) = Q.datum.root (e a) from hroot a]
      congr 2
      change P.datum.toLinearMap (P.datum.root l) (P.datum.coroot a) =
        Q.datum.toLinearMap (Q.datum.root j) (Q.datum.coroot (e a))
      rw [← hr, ← hcoroot a, hpair]
    · simp only [RootPairing.coroot_reflectionPerm, RootPairing.coreflection_apply, map_sub,
        map_smul, hc, show g (P.datum.coroot k) = Q.datum.coroot (e a) from hcoroot a]
      congr 2
      simpa only [RootPairing.root', hc, hroot a] using (hpair (P.datum.root a) (P.datum.coroot l)).symm

set_option maxHeartbeats 800000 in
theorem basedDatumComparison : BasedDatumComparison.{u} := by
  classical
  intro P Q bP bQ hbP hbQ e h
  let g := bP.equiv bQ e
  let f := P.datum.toPerfPair.trans (g.symm.dualMap.trans Q.datum.toPerfPair.symm)
  have hpair (x : P.X) (y : P.Y) : Q.datum.toLinearMap (f x) (g y) = P.datum.toLinearMap x y := by
    change Q.datum.toPerfPair (f x) (g y) = _
    simp [f]
  have hcoroot (i : P.base.support) : g (P.datum.coroot i) = Q.datum.coroot (e i) := by
    simpa only [g, hbP, hbQ] using bP.equiv_apply i bQ e
  have hroot (i : P.base.support) : f (P.datum.root i) = Q.datum.root (e i) := by
    apply Q.datum.toPerfPair.injective
    refine bQ.ext fun j => ?_
    obtain ⟨l, rfl⟩ := e.surjective j
    rw [hbQ, ← hcoroot l]
    change Q.datum.toLinearMap (f (P.datum.root i)) (g (P.datum.coroot l)) =
      Q.datum.toLinearMap (Q.datum.root (e i)) (g (P.datum.coroot l))
    rw [hpair, hcoroot l]
    exact h i l
  have hforward := matched_root_pairs P Q f g hpair e hroot hcoroot
  have hback := matched_root_pairs Q P f.symm g.symm
    (fun x y => by simpa using (hpair (f.symm x) (g.symm y)).symm) e.symm
    (fun i => f.symm_apply_eq.mpr (by simpa using (hroot (e.symm i)).symm))
    (fun i => g.symm_apply_eq.mpr (by simpa using (hcoroot (e.symm i)).symm))
  let j (i : P.I) : Q.I := (hforward i).choose
  have hj (i : P.I) : f (P.datum.root i) = Q.datum.root (j i) ∧
      g (P.datum.coroot i) = Q.datum.coroot (j i) := (hforward i).choose_spec
  have hequiv : Function.Bijective j := by
    constructor
    · intro a b hab
      apply P.datum.root.injective
      apply f.injective
      rw [(hj a).1, (hj b).1, hab]
    · intro a
      obtain ⟨b, hab, _⟩ := hback a
      exact ⟨b, Q.datum.root.injective ((hj b).1.symm.trans (f.eq_symm_apply.mp hab.symm))⟩
  let jEquiv := Equiv.ofBijective j hequiv
  let m : P.datum.Equiv Q.datum :=
    { weightMap := f
      coweightMap := g.symm
      indexEquiv := jEquiv
      weight_coweight_transpose := by
        ext y x
        simpa using hpair x (g.symm y)
      root_weightMap := funext fun i => (hj i).1
      coroot_coweightMap := by
        funext i
        change g.symm (Q.datum.coroot i) = P.datum.coroot (jEquiv.symm i)
        apply g.injective
        rw [g.apply_symm_apply, (hj (jEquiv.symm i)).2]
        exact congrArg Q.datum.coroot (jEquiv.apply_symm_apply i).symm
      bijective_weightMap := f.bijective
      bijective_coweightMap := g.symm.bijective }
  have hm (i : P.base.support) : m.indexEquiv i = (e i).val :=
    Q.datum.root.injective ((hj i).1.symm.trans (hroot i))
  refine ⟨⟨m, ?_⟩, hm⟩
  ext i
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [hm ⟨j, hj⟩]
    exact (e ⟨j, hj⟩).property
  · intro hi
    let p := e.symm ⟨i, hi⟩
    exact ⟨p, p.property, (hm p).trans (congrArg Subtype.val (e.apply_symm_apply ⟨i, hi⟩))⟩

end BasedDatum

section SplitGroup

open Specs.Pinning (PinnedGroup AttachedDatum)
open Specs.SpecialLinearDatum
open CategoryTheory
open private pinnedLift from LinearAlgebraicGroups.Classification.PinnedEquivalence

private def adjacentRoot {r : ℕ} (i : Fin r) : RootIndices (r + 1) :=
  ⟨(i.castSucc, i.succ), fun h => (Nat.ne_of_lt (Nat.lt_succ_self i.val)) (congrArg Fin.val h)⟩

set_option backward.isDefEq.respectTransparency false in
private theorem matrixDatum_typeA {k : Type u} [Field k] {r : ℕ}
    {S : Specs.AffineAlgebraicGroup k} {s : Specs.GeneralLinearStructure.SpecialMatrixPoints S (r + 1)}
    {T : DiagonalTorus s} {L : LatticeIdentification T} {M : RootIdentification T L}
    {B : UpperTriangularBorel T L M} {D : AttachedDatum B.pair}
    (hD : IsMatrixBasedDatum B D) : HasSimplyConnectedTypeA r D.toBased := by
  classical
  let := D.comm
  let adj (i : Fin r) : D.toBased.base.support :=
    ⟨M.indices (adjacentRoot i), hD.2 (adjacentRoot i) |>.mpr ⟨i, rfl, rfl⟩⟩
  have hinj : Function.Injective adj := by
    intro i j hij
    have heq := M.indices.injective (congrArg Subtype.val hij)
    exact Fin.ext (congrArg (fun p : RootIndices (r + 1) => p.val.1.val) heq)
  have hsurj : Function.Surjective adj := by
    intro j
    obtain ⟨p, hp⟩ := M.indices.surjective j.val
    have hj := j.property
    change j.val ∈ D.base.support at hj
    obtain ⟨i, hi, hi'⟩ := (hD.2 p).mp (hp ▸ hj)
    refine ⟨i, Subtype.ext ?_⟩
    change M.indices (adjacentRoot i) = j.val
    rw [← hp]
    apply congrArg M.indices
    exact Subtype.ext (Prod.ext hi.symm hi'.symm)
  let e := Equiv.ofBijective adj ⟨hinj, hsurj⟩
  obtain ⟨b, hb⟩ := RootData.SpecialLinearDatum.simpleCorootBasis r
  let lc : CocharacterLattice (r + 1) ≃ₗ[ℤ] D.toBased.Y := L.cocharacters.symm
  refine ⟨e, (b.reindex e).map lc, ?_, ?_⟩
  · intro a
    obtain ⟨i, rfl⟩ := e.surjective a
    rw [Module.Basis.map_apply, Module.Basis.reindex_apply, Equiv.symm_apply_apply, hb]
    change L.cocharacters.symm (simpleCoroot r i) =
      D.datum.rootDatum.coroot (M.indices (adjacentRoot i))
    apply L.cocharacters.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (hD.1 (adjacentRoot i)).symm
  · intro i j
    change D.datum.rootDatum.toLinearMap
      (D.datum.rootDatum.root (M.indices (adjacentRoot i)))
      (D.datum.rootDatum.coroot (M.indices (adjacentRoot j))) = _
    rw [D.datum.root_eq]
    change D.datum.rootDatum.toLinearMap (Additive.ofMul (M.indices (adjacentRoot i)).val)
      (Additive.ofMul (Additive.toMul (D.datum.rootDatum.coroot (M.indices (adjacentRoot j))))) = _
    rw [D.datum.pairing_eq, L.pairing_eq, M.character_eq]
    change dotPairing (r + 1) (root (r + 1) i.castSucc i.succ)
      (L.cocharacters (D.datum.rootDatum.coroot (M.indices (adjacentRoot j)))) = _
    rw [hD.1]
    exact RootData.SpecialLinearDatum.simpleCartanPairings r i j

theorem splitMatrixComparison : SplitMatrixComparison.{u} := by
  intro k _ r S s
  obtain ⟨T, L, M, B, D, hD, ⟨A, U, _, _, pin, _⟩, _⟩ :=
    RootData.SpecialLinearDatum.matrixPinnedDatum k r S s
  let Q : PinnedGroup A := ⟨B.pair, U, pin⟩
  refine ⟨A, Q, rfl, ?_⟩
  intro P E hE
  obtain ⟨e, b, hb, hCartan⟩ := hE
  obtain ⟨f, c, hc, hCartan'⟩ := matrixDatum_typeA hD
  let j := e.symm.trans f
  have h (i l : E.toBased.base.support) :
      E.toBased.datum.pairing i l = D.toBased.datum.pairing (j i) (j l) := by
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨l, rfl⟩ := e.surjective l
    simpa [j] using (hCartan i l).trans (hCartan' i l).symm
  obtain ⟨d, _⟩ := basedDatumComparison E.toBased D.toBased b c hb hc j h
  obtain ⟨q, _⟩ := pinnedLift P Q E D d
  exact ⟨q⟩

end SplitGroup

section SchemeDescent

open CategoryTheory AlgebraicGeometry Opposite
open _root_.LinearAlgebraicGroups.Specs Specs.TypeAMatrixDescentData
open _root_.LinearAlgebraicGroups.Descent
open private trivialization_coordinates modelPoint standardPointChange standardPointChange_modelPoint standardPointChange_project
  standardTestChange standardTestChange_eval modelPoint_trivialization coordinatePoint
  from LinearAlgebraicGroups.Arithmetic.TypeAMatrixDescentData
open private act_apply_inv act_inv_apply from LinearAlgebraicGroups.Descent.Forms

private theorem modelPoint_injective {P : HopfAlgebraCategory F} {R : TestAlgebra K}
    {W : GroupScheme K} (a : specGroup (extendedHopf K P) ≅ W) :
    Function.Injective (modelPoint (R := R) a) := by
  intro x y h
  have hh := (((groupPointsFunctor K).mapIso a).app R).groupIsoToMulEquiv.injective h
  change coordinatePoint x = coordinatePoint y at hh
  have he := (algSpec.fullyFaithful (R := CommRingCat.of K)).map_injective hh
  exact congrArg (fun f => f.unop.hom) he

private theorem coordinateAction_eq {P : HopfAlgebraCategory F} (σ : Gal(K/F))
    (x : extendedHopf K P) :
    (Algebra.TensorProduct.congr σ (AlgEquiv.refl : P ≃ₐ[F] P)) x =
      (standardCoordinateAction P).act σ x := by
  induction x using TensorProduct.inductionOn with
  | tmul a p => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- A scheme isomorphism over K commuting with semilinear changes on test
algebras is the scalar extension of an isomorphism over F. -/
private theorem descendSchemeIso [FiniteDimensional F K] [IsGalois F K]
    {G H : AffineAlgebraicGroup F}
    (j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val)
    (h : ∀ σ {R S : TestAlgebra K}
      (b : (restrictTestAlgebra F K).obj R ⟶ (restrictTestAlgebra F K).obj S),
      IsSemilinearTestMap σ b → ∀ x, IsTransportedPoint j b x (standardPointChange G.val b x)) :
    ∃ v : G.val ≅ H.val, (groupBaseChange F K).mapIso v = j := by
  obtain ⟨C, _, _⟩ := trivialization_coordinates j
  have he : ∀ σ x, (transportedCoordinateAction (Iso.refl (extendedHopf K C.split)) σ x) =
      transportedCoordinateAction C.iso σ x := by
    intro σ x
    let R := CommAlgCat.of K (extendedHopf K C.split)
    let T := (restrictTestAlgebra F K).obj R
    let b : T ⟶ T := by
      letI : Algebra F T := T.algebra
      exact ConcreteCategory.ofHom (C := CommAlgCat F) (X := T) (Y := T)
        ({ toRingHom := (Algebra.TensorProduct.congr σ
            (AlgEquiv.refl : C.split ≃ₐ[F] C.split)).toRingHom
           commutes' := fun a => by
             change (Algebra.TensorProduct.congr σ (AlgEquiv.refl : C.split ≃ₐ[F] C.split))
               (algebraMap F K a ⊗ₜ[F] (1 : C.split)) = algebraMap F K a ⊗ₜ[F] (1 : C.split)
             change σ (algebraMap F K a) ⊗ₜ[F] (1 : C.split) = algebraMap F K a ⊗ₜ[F] (1 : C.split)
             rw [σ.commutes] } : T →ₐ[F] T)
    have hb (w : extendedHopf K C.split) : b.hom w = (standardCoordinateAction C.split).act σ w :=
      coordinateAction_eq σ w
    have hsem : IsSemilinearTestMap σ b := by
      intro a
      change b.hom (a ⊗ₜ[F] (1 : C.split)) = σ a ⊗ₜ[F] (1 : C.split)
      rfl
    let p : extendedHopf K C.split →ₐ[K] R := AlgHom.id K _
    have hp : standardTestChange b p = p := by
      apply AlgHom.ext
      intro w
      rw [standardTestChange_eval σ b hsem]
      change b.hom ((standardCoordinateAction C.split).act σ⁻¹ w) = w
      rw [hb]
      exact act_apply_inv (standardCoordinateAction C.split) σ w
    let z := modelPoint C.splitComparison p
    have hz : standardPointChange G.val b z = z := by
      dsimp only [z, TrivializationCoordinates.splitComparison]
      rw [standardPointChange_modelPoint p C.splitModel C.extension C.extensionProjection b, hp]
    have hh := h σ b hsem z
    rw [hz] at hh
    have hj : standardPointChange H.val b (z ≫ j.hom.hom.hom) = z ≫ j.hom.hom.hom := by
      apply (baseChangePointsEquiv K H.val.X R).injective
      change baseChangePoint F K H.val.X R (standardPointChange H.val b _) = _
      rw [standardPointChange_project]
      exact hh.symm
    rw [modelPoint_trivialization C p] at hj
    change standardPointChange H.val b (modelPoint C.formComparison (p.comp C.iso.inv.hom.toAlgHom)) = _ at hj
    dsimp only [TrivializationCoordinates.formComparison] at hj
    rw [standardPointChange_modelPoint _ C.formModel C.extension C.extensionProjection b] at hj
    have ht := modelPoint_injective _ hj
    have hw := DFunLike.congr_fun ht ((standardCoordinateAction C.form).act σ (C.iso.hom.hom x))
    rw [standardTestChange_eval σ b hsem] at hw
    rw [act_inv_apply (standardCoordinateAction C.form) σ (C.iso.hom.hom x)] at hw
    change b.hom (C.iso.inv.hom (C.iso.hom.hom x)) =
      C.iso.inv.hom ((standardCoordinateAction C.form).act σ (C.iso.hom.hom x)) at hw
    rw [show C.iso.inv.hom (C.iso.hom.hom x) = x from ConcreteCategory.congr_hom C.iso.hom_inv_id x,
      hb] at hw
    exact hw
  obtain ⟨v, hv, _⟩ := Arithmetic.TypeAMatrixDescentData.equivariantSchemeComparisonDescends
    C.extension C.extensionProjection (Iso.refl _) C.iso 1 (by
      intro σ x
      exact he σ x)
  refine ⟨C.splitModel.symm ≪≫ v ≪≫ C.formModel, ?_⟩
  refine Eq.trans ?_ C.compatibility.symm
  rw [Functor.mapIso_trans, Functor.mapIso_trans, hv]
  simp [Iso.trans_assoc]

open GeneralLinearStructure StandardGroups
open Specs.Unipotent (Index)
open private affineGroupIso affineGroupIso_hom affine_baseChange baseChangePointIso liftSpecialLinear
  from LinearAlgebraicGroups.Descent.InnerTypeA
open private extendMatrixPoints transportedPoint_unique
  from LinearAlgebraicGroups.Arithmetic.TypeAMatrixDescentData
open private fieldSemilinearMap_semilinear field_formula_parity map_inverse_transpose
  from LinearAlgebraicGroups.Arithmetic.TypeAMatrixDescentData

set_option backward.isDefEq.respectTransparency false in
private theorem matrixTransportCharacter_unique
    {G H : AffineAlgebraicGroup F} {s : SpecialMatrixPoints G n}
    {i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val}
    (hn : 3 ≤ n) {χ χ' : DiagramCharacter F K}
    {g g' : Gal(K/F) → GL (Index.{u} n) K}
    (h : HasMatrixTransport s i χ g) (h' : HasMatrixTransport s i χ' g') : χ = χ' := by
  apply MonoidHom.ext
  intro σ
  apply field_formula_parity hn (g σ) (g' σ)
  intro z
  let R := CommAlgCat.of K K
  let f := fieldSemilinearMap σ
  let e := ((extendMatrixPoints (K := K) s).app R).groupIsoToMulEquiv
  let z' := SpecialLinearGroup.map σ.symm.toRingHom z
  let x : Points ((groupBaseChange F K).obj G.val).X R := e.symm z'
  obtain ⟨y, hy, _⟩ := transportedPoint_unique i f x
  let w := baseChangeMatrix s R x
  have hmap : SpecialLinearGroup.map σ.toRingHom w = z := by
    have hx : baseChangeMatrix s R x = z' := e.apply_symm_apply z'
    change SpecialLinearGroup.map σ.toRingHom (baseChangeMatrix s R x) = z
    rw [hx]
    apply Subtype.ext
    ext a b
    exact σ.apply_symm_apply (z.val a b)
  have hv : w.val.map σ.toRingHom = z.val := congrArg Subtype.val hmap
  have hi : w⁻¹.val.transpose.map σ.toRingHom = z⁻¹.val.transpose :=
    (map_inverse_transpose σ.toRingHom w).symm.trans
      (congrArg (fun M : SpecialLinearGroup (Index.{u} n) K => M⁻¹.val.transpose) hmap)
  have hg (U : GL (Index.{u} n) K) : GeneralLinearGroup.map (algebraMap K R) U = U := Units.ext rfl
  have h₁ := h σ f (fieldSemilinearMap_semilinear σ) x y hy
  have h₂ := h' σ f (fieldSemilinearMap_semilinear σ) x y hy
  dsimp only at h₁ h₂
  rw [hg] at h₁ h₂
  change (baseChangeMatrix s R y).val = (g σ).val *
    (if χ σ = 1 then w.val.map σ.toRingHom else w⁻¹.val.transpose.map σ.toRingHom) * (g σ)⁻¹.val at h₁
  change (baseChangeMatrix s R y).val = (g' σ).val *
    (if χ' σ = 1 then w.val.map σ.toRingHom else w⁻¹.val.transpose.map σ.toRingHom) * (g' σ)⁻¹.val at h₂
  rw [hv, hi] at h₁ h₂
  exact h₁.symm.trans h₂

set_option backward.isDefEq.respectTransparency false in
private theorem descendMatrixComparison [FiniteDimensional F K] [IsGalois F K]
    {G H M : AffineAlgebraicGroup F} (s : SpecialMatrixPoints G n)
    (i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val)
    (c : (restrictTestAlgebra F K) ⋙ (groupPointsFunctor F).obj M.val ≅
      specialLinearPoints K (Index.{u} n))
    (χ : DiagramCharacter F K) (g : Gal(K/F) → GL (Index.{u} n) K)
    (hi : HasMatrixTransport s i χ g)
    (hc : ∀ σ {R S : TestAlgebra K}
      (f : (restrictTestAlgebra F K).obj R ⟶ (restrictTestAlgebra F K).obj S),
      IsSemilinearTestMap σ f → ∀ p : Points M.val.X ((restrictTestAlgebra F K).obj R),
      let B := GeneralLinearGroup.map (algebraMap K S) (g σ)
      let X : SpecialLinearGroup (Index.{u} n) R := c.hom.app R p
      (show SpecialLinearGroup (Index.{u} n) S from c.hom.app S (mapPoints f p)).val = B.val *
        (if χ σ = 1 then X.val.map f.hom.toRingHom else (X⁻¹).val.transpose.map f.hom.toRingHom) *
          (B⁻¹).val) :
    Nonempty (H.val ≅ M.val) := by
  let e := extendMatrixPoints (K := K) s ≪≫ (baseChangePointIso M.val ≪≫ c).symm
  let j : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj M.val := affineGroupIso (affine_baseChange G.val.X G.property.1)
    (affine_baseChange M.val.X M.property.1) e
  have hj (R : TestAlgebra K) (x : Points ((groupBaseChange F K).obj G.val).X R) :
      c.hom.app R (baseChangePoint F K M.val.X R (x ≫ j.hom.hom.hom)) = baseChangeMatrix s R x := by
    change (baseChangePointIso M.val ≪≫ c).hom.app R
      (((groupPointsFunctor K).map j.hom).app R x) = _
    have he : (groupPointsFunctor K).map j.hom = e.hom := affineGroupIso_hom _ _ _
    rw [he]
    exact ((baseChangePointIso M.val ≪≫ c).app R).groupIsoToMulEquiv.apply_symm_apply _
  obtain ⟨v, _⟩ := descendSchemeIso (i.symm ≪≫ j) (by
    intro σ R S f hf p
    let x : Points ((groupBaseChange F K).obj G.val).X R := p ≫ i.inv.hom.hom
    let q := standardPointChange H.val f p
    let y : Points ((groupBaseChange F K).obj G.val).X S := q ≫ i.inv.hom.hom
    have hx : x ≫ i.hom.hom.hom = p := by
      simp [x, Category.assoc, ← CategoryTheory.Grp.comp_hom_hom]
    have hy : y ≫ i.hom.hom.hom = q := by
      simp [y, Category.assoc, ← CategoryTheory.Grp.comp_hom_hom]
    have hxy : IsTransportedPoint i f x y := by
      unfold IsTransportedPoint
      rw [hx, hy]
      exact standardPointChange_project H.val f p
    change baseChangePoint F K M.val.X S (y ≫ j.hom.hom.hom) =
      mapPoints f (baseChangePoint F K M.val.X R (x ≫ j.hom.hom.hom))
    apply ((c.app S).groupIsoToMulEquiv.injective)
    apply Subtype.ext
    change (show SpecialLinearGroup (Index.{u} n) S from
      c.hom.app S (baseChangePoint F K M.val.X S (y ≫ j.hom.hom.hom))).val =
        (show SpecialLinearGroup (Index.{u} n) S from c.hom.app S
          (mapPoints f (baseChangePoint F K M.val.X R (x ≫ j.hom.hom.hom)))).val
    rw [hj, hi σ f hf x y hxy, hc σ f hf, hj])
  exact ⟨v⟩

private def lowerGL {R : Type u} [CommRing R] (A : GL (Index.{u} n) R) : GL (Fin n) R :=
  Units.map (Matrix.reindexRingEquiv R Equiv.ulift).toMonoidHom A

set_option backward.isDefEq.respectTransparency false in
private theorem liftMatrixFormula {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (A : GL (Index.{u} n) S) (p : Multiplicative (ZMod 2))
    (X : SpecialLinearGroup (Fin n) R) (Y : SpecialLinearGroup (Fin n) S)
    (h : Y.val = (lowerGL A).val *
      (if p = 1 then X.val.map f else (X⁻¹).val.transpose.map f) * (lowerGL A)⁻¹.val) :
    (liftSpecialLinear n Y).val = A.val *
      (if p = 1 then (liftSpecialLinear n X).val.map f
       else ((liftSpecialLinear n X)⁻¹).val.transpose.map f) * A⁻¹.val := by
  let D := Matrix.reindexRingEquiv S (Equiv.ulift : Index.{u} n ≃ Fin n)
  apply D.injective
  rw [map_mul, map_mul]
  have hInv : D A⁻¹.val = (lowerGL A)⁻¹.val :=
    congrArg Units.val (map_inv (Units.map D.toMonoidHom) A)
  rw [hInv]
  by_cases hp : p = 1
  · rw [ite_eq_left hp]
    exact h.trans (by rw [ite_eq_left hp]; rfl)
  · rw [ite_eq_right hp, ← map_inv (liftSpecialLinear n)]
    exact h.trans (by rw [ite_eq_right hp]; rfl)

open _root_.RM03.CSA (IsCentralSimple degree)
open _root_.RM03.CSA.NormOneGroup
open _root_.RM03.Brauer.ProjectiveClassification (Cocycle IsTransport Implements)
open _root_.LinearAlgebraicGroups.Descent.InnerTypeA.Specification (NormOneCoordinates)
open private Representation Representation.hopf Representation.convolutionIso spectrumPointsIso
  from LinearAlgebraicGroups.Affine.StandardGroups
open private normOneRepresentation from LinearAlgebraicGroups.Descent.InnerTypeA
open private splitNormOnePoints from LinearAlgebraicGroups.Descent.InnerTypeA
open private conjugation_injective conjugation_mk coefficient coefficient_apply_inv
  from MathGenome.Internal.RingModuleAssociativeAlgebra.RM03.Brauer.ProjectiveClassification

private theorem projectiveClass {ρ : AlgebraAction F K (Mat K n)} {c : Cocycle F K n}
    (hc : Implements ρ c) (σ : Gal(K/F)) (A : GL (Fin n) K)
    (hA : ∀ x : Mat K n, ρ.act σ x = A.val * x.map σ * A⁻¹.val) :
    ProjGenLinGroup.mk A = c.val σ := by
  obtain ⟨B, hB⟩ := ProjGenLinGroup.mk_surjective (c.val σ)
  rw [← hB]
  apply conjugation_injective
  ext x i j
  rw [conjugation_mk, conjugation_mk]
  have hx := (hA (coefficient σ⁻¹ x)).symm.trans (hc σ B hB (coefficient σ⁻¹ x))
  simpa only [show ∀ z : Mat K n, z.map σ = coefficient σ z from fun _ => rfl,
    coefficient_apply_inv] using congrArg (fun M : Mat K n => M i j) hx

private theorem representsNormOneOfPoints {A : Type u} [Ring A] [Algebra F A]
    {ι : Type u} [Fintype ι] (hA : IsCentralSimple F A) (b : Module.Basis ι F A)
    {H : AffineAlgebraicGroup F}
    (z : (groupPointsFunctor F).obj H.val ≅ normOneFunctor hA b) : RepresentsNormOne hA b H := by
  let point (R : TestAlgebra F) : Points H.val.X R ≃ normOne (R := R) hA b :=
    (z.app R).groupIsoToMulEquiv.toEquiv
  refine ⟨point, ?_, ?_⟩
  · intro R x y
    exact congrArg (fun t : normOne (R := R) hA b => t.val)
      (map_mul (z.app R).groupIsoToMulEquiv x y)
  · intro R S f x
    exact congrArg (fun t : normOne (R := S) hA b => t.val)
      (NatTrans.naturality_apply z.hom f x)

private theorem normOneSpectrumExists {A : Type u} [Ring A] [Algebra F A]
    {ι : Type u} [Fintype ι] (hA : IsCentralSimple F A) (b : Module.Basis ι F A) :
    ∃ M : AffineAlgebraicGroup F,
      Nonempty ((groupPointsFunctor F).obj M.val ≅ normOneFunctor hA b) := by
  let P := normOneRepresentation hA b
  let := Representation.hopf P
  exact ⟨spectrum F (NormOneCoordinates hA b),
    ⟨spectrumPointsIso (Representation.convolutionIso P)⟩⟩

set_option backward.isDefEq.respectTransparency false in
private theorem normOneMatrixTransport [FiniteDimensional F K] [IsGalois F K]
    {A : Type u} [Ring A] [Algebra F A] {ι : Type u} [Fintype ι]
    (hA : IsCentralSimple F A) (b : Module.Basis ι F A)
    (e : (K ⊗[F] A) ≃ₐ[K] Mat K (degree F A))
    (ρ : AlgebraAction F K (Mat K (degree F A))) (c : Cocycle F K (degree F A))
    (he : IsTransport ρ e) (hc : Implements ρ c)
    (σ : Gal(K/F)) (G : GL (Index.{u} (degree F A)) K)
    (hG : ProjGenLinGroup.mk (lowerGL G) = c.val σ)
    {R S : TestAlgebra K} (f : (restrictTestAlgebra F K).obj R ⟶ (restrictTestAlgebra F K).obj S)
    (hf : IsSemilinearTestMap σ f) (x : (normOneFunctor hA b).obj ((restrictTestAlgebra F K).obj R)) :
    let B := GeneralLinearGroup.map (algebraMap K S) G
    let C := splitNormOnePoints hA b e
    let X : SpecialLinearGroup (Index.{u} (degree F A)) R := C.hom.app R x
    (show SpecialLinearGroup (Index.{u} (degree F A)) S from C.hom.app S ((normOneFunctor hA b).map f x)).val =
      B.val * X.val.map f.hom.toRingHom * B⁻¹.val := by
  let d (T : TestAlgebra K) := extendSplitting (R := restrictTestAlgebraObj F K T) e
  have ht : _root_.LinearAlgebraicGroups.Descent.InnerTypeA.Specification.IsCocycleComparison e d :=
    _root_.LinearAlgebraicGroups.Descent.InnerTypeA.cocycleOnTestAlgebras e d
      (fun T r a => extendSplitting_tmul (R := restrictTestAlgebraObj F K T) e r a)
  let X := normOneSplit (R := restrictTestAlgebraObj F K R) hA b e x
  let Y := normOneSplit (R := restrictTestAlgebraObj F K S) hA b e ((normOneFunctor hA b).map f x)
  have h := ht ρ c he hc σ (lowerGL G) hG f hf x.val
  exact liftMatrixFormula f.hom.toRingHom (GeneralLinearGroup.map (algebraMap K S) G) 1 X Y h

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
private theorem innerSchemeModel [FiniteDimensional F K] [IsGalois F K]
    {A : Type u} [Ring A] [Algebra F A] (hA : IsCentralSimple F A)
    {G H : AffineAlgebraicGroup F} (s : SpecialMatrixPoints G n)
    (i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val)
    (g : Gal(K/F) → GL (Index.{u} n) K) (hi : HasMatrixTransport s i 1 g)
    (hd : degree F A = n) (e : (K ⊗[F] A) ≃ₐ[K] Mat K n)
    (ρ : AlgebraAction F K (Mat K n)) (c : Cocycle F K n)
    (he : IsTransport ρ e) (hc : Implements ρ c)
    (hg : ∀ σ, ProjGenLinGroup.mk (lowerGL (g σ)) = c.val σ) :
    ∃ (ι : Type u) (_ : Fintype ι) (b : Module.Basis ι F A), RepresentsNormOne hA b H := by
  subst n
  let : Module.Finite F A := hA.2.2
  let b := (Module.finBasis F A).reindex Equiv.ulift.symm
  obtain ⟨M, ⟨η⟩⟩ := normOneSpectrumExists hA b
  let cM := Functor.isoWhiskerLeft (restrictTestAlgebra F K) η ≪≫ splitNormOnePoints hA b e
  obtain ⟨v⟩ := descendMatrixComparison (M := M) s i cM 1 g hi (by
    intro σ R S f hf p
    let pR := η.hom.app ((restrictTestAlgebra F K).obj R) p
    let pS := η.hom.app ((restrictTestAlgebra F K).obj S) (mapPoints f p)
    have hp : pS = (normOneFunctor hA b).map f pR := NatTrans.naturality_apply η.hom f p
    let C := splitNormOnePoints hA b e
    let X : SpecialLinearGroup (Index.{u} (degree F A)) R := C.hom.app R pR
    let B := GeneralLinearGroup.map (algebraMap K S) (g σ)
    change (show SpecialLinearGroup (Index.{u} (degree F A)) S from C.hom.app S pS).val =
      B.val * (if (1 : DiagramCharacter F K) σ = 1 then X.val.map f.hom.toRingHom
        else X⁻¹.val.transpose.map f.hom.toRingHom) * B⁻¹.val
    rw [hp, ite_eq_left (MonoidHom.one_apply σ)]
    exact normOneMatrixTransport hA b e ρ c he hc σ (g σ) (hg σ) f hf pR)
  let z := (groupPointsFunctor F).mapIso v ≪≫ η
  exact ⟨_, inferInstance, b, representsNormOneOfPoints hA b z⟩

section Unitary

open _root_.LinearAlgebraicGroups.UnitaryNormEquations (SecondKind matrixProjection
  matrixComparison matrixNaturality matrixSemilinearTransport specialUnitaryRepresentability
  extendMatrixOperator IsSpecialUnitary)
open MulOpposite

variable {E A : Type u} [Field E] [Ring A] [Algebra E A]

local notation "dA" => _root_.Specs.RM03.CSA.degree E A

private theorem extendOperatorFormula {R S : Type u} [CommRing R] [CommRing S] [Algebra K S]
    (p : Multiplicative (ZMod 2)) (σ : Gal(K/F)) (U : GL (Fin dA) K)
    (B : Mat K dA →+ Mat K dA)
    (hB : ∀ x, B x = U.val * (if p = 1 then x.map σ else (x.map σ).transpose) * U⁻¹.val)
    (f : R →+* S) (x : Mat R dA) :
    extendMatrixOperator (E := E) (A := A) B f x =
      U.val.map (algebraMap K S) * (if p = 1 then x.map f else x.transpose.map f) *
        (U⁻¹.val.map (algebraMap K S)) := by
  let L := U.val.map (algebraMap K S)
  let R' := U⁻¹.val.map (algebraMap K S)
  have hterm (r : S) (Z : Mat S dA) :
      r • (L * Z * R') = L * (r • Z) * R' := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hsum : (∑ i, ∑ j, f (x i j) • Matrix.single i j (1 : S)) = x.map f := by
    have h := Matrix.sum_sum_single (x.map f)
    change (∑ i, ∑ j, Matrix.single i j (f (x i j))) = x.map f at h
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using h
  have hsumT : (∑ i, ∑ j, f (x i j) • Matrix.single j i (1 : S)) = x.transpose.map f := by
    rw [Matrix.transpose_map, ← hsum]
    simp only [Matrix.transpose_sum, Matrix.transpose_smul, Matrix.transpose_single]
  unfold extendMatrixOperator
  have hsingle (i j : Fin dA) :
      (B (Matrix.single i j 1)).map (algebraMap K S) =
        L * (if p = 1 then Matrix.single i j 1 else Matrix.single j i 1) * R' := by
    rw [hB, Matrix.map_mul, Matrix.map_mul]
    by_cases hp : p = 1 <;>
      simp only [hp, ite_true, ite_false, Matrix.map_single, map_one, Matrix.transpose_single, L, R']
  calc
    _ = ∑ i, ∑ j, L * (f (x i j) • (if p = 1 then Matrix.single i j 1 else Matrix.single j i 1)) * R' := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hsingle, hterm]
    _ = L * (∑ i, ∑ j, f (x i j) • (if p = 1 then Matrix.single i j 1 else Matrix.single j i 1)) * R' := by
      simp only [Matrix.sum_mul, Matrix.mul_sum]
    _ = _ := by
      by_cases hp : p = 1
      · simp only [ite_eq_left hp, hsum, L, R']
      · simp only [ite_eq_right hp, hsumT, L, R']

variable [Algebra F E] [Algebra E K] [IsScalarTower F E K] [Algebra F A] [IsScalarTower F E A]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem outerSchemeModel [FiniteDimensional F K] [IsGalois F K]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    (hA : _root_.Specs.RM03.CSA.isCentralSimple E A) (star : SecondKind F E A)
    {G H : AffineAlgebraicGroup F} (s : SpecialMatrixPoints G n)
    (i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val)
    (χ : DiagramCharacter F K) (g : Gal(K/F) → GL (Index.{u} n) K) (hi : HasMatrixTransport s i χ g)
    (hd : dA = n) (e : (K ⊗[E] A) ≃ₐ[K] Mat K n)
    (β : ∀ σ : Gal(K/F), MatrixLift n σ (χ σ))
    (hg : ∀ σ x, (β σ).toAddEquiv x =
      (lowerGL (g σ)).val * (if χ σ = 1 then x.map σ else (x.map σ).transpose) *
        (lowerGL (g σ))⁻¹.val)
    (hE : ∀ σ a, σ (algebraMap E K a) =
      algebraMap E K (if χ σ = 1 then a else star.conjugation a))
    (hβ : ∀ σ a, (β σ).toAddEquiv (e (1 ⊗ₜ[E] a)) =
      e (1 ⊗ₜ[E] (if χ σ = 1 then a else (star.adjoint a).unop))) :
    ∃ (ι : Type u) (_ : Fintype ι) (b : Module.Basis ι E A), RepresentsUnitary hA b star H := by
  subst n
  let : Module.Finite E A := hA.2.2
  let b := (Module.finBasis E A).reindex Equiv.ulift.symm
  obtain ⟨M, P, η, point, _, hmul, hnat⟩ := specialUnitaryRepresentability F E A hA b star
  let (R : TestAlgebra K) : Algebra E (restrictTestAlgebraObj F K R) :=
    ((algebraMap K R).comp (algebraMap E K)).toAlgebra
  let (R : TestAlgebra K) : IsScalarTower F K (restrictTestAlgebraObj F K R) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let (R : TestAlgebra K) : IsScalarTower E K (restrictTestAlgebraObj F K R) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let (R : TestAlgebra K) : IsScalarTower F E (restrictTestAlgebraObj F K R) :=
    IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap K R (algebraMap F K x) = algebraMap K R (algebraMap E K (algebraMap F E x))
      rw [IsScalarTower.algebraMap_apply F E K]
  let d (R : TestAlgebra K) : (restrictTestAlgebraObj F K R ⊗[F] A) →ₐ[F] Mat (restrictTestAlgebraObj F K R) dA :=
    matrixProjection (R := restrictTestAlgebraObj F K R) e
  have hex (R : TestAlgebra K) := matrixComparison (R := restrictTestAlgebraObj F K R) hA b star e
  choose w hw using hex
  let chart (R : TestAlgebra K) : P.obj ((restrictTestAlgebra F K).obj R) ≃*
      SpecialLinearGroup (Fin dA) R :=
    { toEquiv := (point _).trans (w R)
      map_mul' := fun x y => by
        apply Subtype.ext
        change (w R (point _ (x * y))).val = (w R (point _ x)).val * (w R (point _ y)).val
        rw [hw R, hw R, hw R, hmul]
        exact map_mul (d R) _ _ }
  have hchart (R : TestAlgebra K) (x : P.obj ((restrictTestAlgebra F K).obj R)) :
      (chart R x).val = d R (point _ x).val.val := hw R _
  let cP : restrictTestAlgebra F K ⋙ P ≅ specialLinearPoints K (Index dA) :=
    NatIso.ofComponents (fun R => ((chart R).trans (liftSpecialLinear _)).toGrpIso) (by
      intro R S f
      apply GrpCat.ext
      intro x
      apply Subtype.ext
      change (liftSpecialLinear _ (chart S (P.map ((restrictTestAlgebra F K).map f) x))).val =
        (liftSpecialLinear _ (chart R x)).val.map f.hom
      have h : (chart S (P.map ((restrictTestAlgebra F K).map f) x)).val =
          (chart R x).val.map f.hom := by
        rw [hchart, hchart, hnat]
        exact matrixNaturality (F := F) (E := E) (A := A) (K := K)
          (R := restrictTestAlgebraObj F K R) (S := restrictTestAlgebraObj F K S)
          e f.hom (point _ x).val.val
      exact congrArg (fun X : Mat S dA => X.submatrix ULift.down ULift.down) h)
  let cM := Functor.isoWhiskerLeft (restrictTestAlgebra F K) η ≪≫ cP
  have hunit σ {R S : TestAlgebra K}
      (f : (restrictTestAlgebra F K).obj R ⟶ (restrictTestAlgebra F K).obj S)
      (hf : IsSemilinearTestMap σ f) (x : P.obj ((restrictTestAlgebra F K).obj R)) :
      (chart S (P.map f x)).val =
      (lowerGL (GeneralLinearGroup.map (algebraMap K S) (g σ))).val *
        (if χ σ = 1 then (chart R x).val.map f.hom.toRingHom
          else ((chart R x)⁻¹).val.transpose.map f.hom.toRingHom) *
        (lowerGL (GeneralLinearGroup.map (algebraMap K S) (g σ)))⁻¹.val := by
    let p := χ σ
    let odd := decide (p ≠ 1)
    let B : Mat K dA →ₛₗ[σ.toRingHom] Mat K dA :=
      { toAddHom := (β σ).toAddEquiv.toAddHom
        map_smul' := (β σ).map_smul }
    have hcentre a : σ (algebraMap E K a) = algebraMap E K (if odd then star.conjugation a else a) := by
      by_cases hp : p = 1 <;> simpa [odd, ← show χ σ = p from rfl, hp] using hE σ a
    have hrestrict a : B (e (1 ⊗ₜ[E] a)) =
        e (1 ⊗ₜ[E] (if odd then (star.adjoint a).unop else a)) := by
      change (β σ).toAddEquiv (e (1 ⊗ₜ[E] a)) = _
      by_cases hp : p = 1 <;> simpa [odd, ← show χ σ = p from rfl, hp] using hβ σ a
    have h := matrixSemilinearTransport (F := F) (E := E) (A := A) (K := K) hA b star
      e σ odd B hcentre hrestrict (R := restrictTestAlgebraObj F K R) (S := restrictTestAlgebraObj F K S)
      f.hom hf (point _ x).val (point _ x).prop
    rw [hchart, hnat]
    change d S (Algebra.TensorProduct.map f.hom (.id F A) (point _ x).val.val) = _
    change d S _ = _ at h
    rw [h, extendOperatorFormula p σ (lowerGL (g σ)) B.toAddMonoidHom (hg σ)]
    let pp : P.obj ((restrictTestAlgebra F K).obj R) →* (restrictTestAlgebraObj F K R ⊗[F] A)ˣ :=
      MonoidHom.mk' (fun z => (point _ z).val) (hmul _)
    have hpInv : (point _ x⁻¹).val = (point _ x).val⁻¹ := map_inv pp x
    have hinv : (chart R x)⁻¹.val = d R ((point _ x).val⁻¹).val := by
      rw [← map_inv (chart R), hchart, hpInv]
    let L := (lowerGL (g σ)).val.map (algebraMap K S)
    let U := (lowerGL (g σ))⁻¹.val.map (algebraMap K S)
    let y := (point ((restrictTestAlgebra F K).obj R) x).val
    let Y := d R (if odd then y⁻¹.val else y.val)
    change L * (if p = 1 then Y.map f.hom.toRingHom else Y.transpose.map f.hom.toRingHom) * U =
      L * (if p = 1 then (chart R x).val.map f.hom.toRingHom
        else (chart R x)⁻¹.val.transpose.map f.hom.toRingHom) * U
    rw [hchart R x, hinv]
    by_cases hp : p = 1
    · have ho : odd = false := by simp [odd, hp]
      simp only [ite_eq_left hp, Y, ho, Bool.false_eq_true, ite_false, y]
    · have ho : odd = true := by simp [odd, hp]
      simp only [ite_eq_right hp, Y, ho, ite_true, y]
  obtain ⟨v⟩ := descendMatrixComparison s i cM χ g hi (by
    intro σ R S f hf p
    let x := η.hom.app ((restrictTestAlgebra F K).obj R) p
    have hp : η.hom.app ((restrictTestAlgebra F K).obj S) (mapPoints f p) = P.map f x :=
      NatTrans.naturality_apply η.hom f p
    change (liftSpecialLinear _ (chart S (η.hom.app _ (mapPoints f p)))).val = _
    rw [hp]
    exact liftMatrixFormula f.hom.toRingHom _ _ (chart R x) (chart S (P.map f x)) (hunit σ f hf x))
  let z := (groupPointsFunctor F).mapIso v ≪≫ η
  refine ⟨_, inferInstance, b, fun R => (z.app R).groupIsoToMulEquiv.toEquiv.trans (point R), ?_, ?_⟩
  · intro R x y
    change (point R ((z.app R).groupIsoToMulEquiv (x * y))).val = _
    rw [map_mul ((z.app R).groupIsoToMulEquiv), hmul]
    rfl
  · intro R S f x
    exact (congrArg (fun y : P.obj S => (point S y).val)
      (NatTrans.naturality_apply z.hom f x)).trans (hnat f (z.hom.app R x))

end Unitary

section SplitCentre

open _root_.LinearAlgebraicGroups.UnitaryNormEquations
  (SecondKind factorProjection factorProjection_tmul factorReducedNorm factorScalarExtension
    IsSpecialUnitary splitCentreComparison)
open private normOneUnitsEquiv from LinearAlgebraicGroups.Arithmetic.UnitaryNormEquations

set_option backward.isDefEq.respectTransparency false in
private theorem normOneOfUnitaryPoints {E A L : Type u} [Field E] [Algebra F E]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E]
    [Field L] [Algebra F L] [Algebra E L] [IsScalarTower F E L]
    [Ring A] [Algebra F A] [Algebra E A] [IsScalarTower F E A]
    (hA : _root_.Specs.RM03.CSA.isCentralSimple E A) {ι : Type u} [Fintype ι] (b : Module.Basis ι E A)
    (star : SecondKind F E A) {H : AffineAlgebraicGroup F} (hH : RepresentsUnitary hA b star H)
    (hL : _root_.Specs.RM03.CSA.isCentralSimple L (L ⊗[E] A)) {U : AffineAlgebraicGroup L}
    (c : (groupPointsFunctor L).obj U.val ≅ restrictTestAlgebra F L ⋙ (groupPointsFunctor F).obj H.val) :
    RepresentsNormOne hL (b.baseChange L) U := by
  obtain ⟨point, hmul, hnat⟩ := hH
  let T (R : TestAlgebra L) := restrictTestAlgebraObj F L R
  let (R : TestAlgebra L) : Algebra E (T R) :=
    ((algebraMap L R).comp (algebraMap E L)).toAlgebra
  let (R : TestAlgebra L) : IsScalarTower E L (T R) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let (R : TestAlgebra L) : IsScalarTower F E (T R) :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap L R (algebraMap F L a) = algebraMap L R (algebraMap E L (algebraMap F E a))
      rw [IsScalarTower.algebraMap_apply F E L]
  let project (R : TestAlgebra L) : (T R ⊗[F] A) →ₐ[F] (T R ⊗[E] A) := factorProjection
  let factor (R : TestAlgebra L) : (T R ⊗[E] A) ≃ₐ[T R] (T R ⊗[L] (L ⊗[E] A)) :=
    factorScalarExtension
  have hnorm (R : TestAlgebra L) (x : T R ⊗[E] A) :
      _root_.Specs.RM03.CSA.NormOneGroup.normAt hL (b.baseChange L) (factor R x) =
        _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b x := by
    obtain ⟨_, _, h⟩ := factorReducedNorm (L := L) (R := T R) hA b
    exact h x
  have hex (R : TestAlgebra L) :
      ∃ w : {x : (T R ⊗[F] A)ˣ // IsSpecialUnitary hA b star x} ≃
          {y : (T R ⊗[E] A)ˣ // _root_.Specs.RM03.CSA.NormOneGroup.normAt hA b y.val = 1},
        ∀ x, (w x).val = Units.map (project R).toMonoidHom x.val := by
    obtain ⟨_, _, w, hw, _⟩ := splitCentreComparison (R := T R) hA b star
    exact ⟨w, hw⟩
  choose w hw using hex
  let e (R : TestAlgebra L) :
      Points U.val.X R ≃
        {x : R ⊗[L] (L ⊗[E] A) // _root_.Specs.RM03.CSA.NormOneGroup.normAt hL (b.baseChange L) x = 1} :=
    (c.app R).groupIsoToMulEquiv.toEquiv.trans ((point (T R)).trans ((w R).trans
      ((normOneUnitsEquiv (R := T R) hA b).trans
        ((factor R).toEquiv.subtypeEquiv fun x => (hnorm R x).symm ▸ Iff.rfl))))
  have he (R : TestAlgebra L) (x : Points U.val.X R) :
      (e R x).val = factor R (project R (point (T R) (c.hom.app R x)).val.val) := by
    change factor R (w R (point (T R) (c.hom.app R x))).val.val = _
    rw [hw]
    rfl
  refine ⟨e, ?_, ?_⟩
  · intro R x y
    have hxy : c.hom.app R (x * y) = c.hom.app R x * c.hom.app R y := map_mul (c.hom.app R).hom x y
    simp only [he, hxy, hmul, Units.val_mul, map_mul]
  · intro R S f x
    let f₀ := (restrictTestAlgebra F L).map f
    have hx : c.hom.app S (mapPoints f x) = mapPoints f₀ (c.hom.app R x) :=
      NatTrans.naturality_apply c.hom f x
    have hmap (y : T R ⊗[F] A) :
        factor S (project S (Algebra.TensorProduct.map f₀.hom (.id F A) y)) =
          Algebra.TensorProduct.map f.hom (.id L (L ⊗[E] A)) (factor R (project R y)) := by
      induction y using TensorProduct.inductionOn with
      | tmul r a =>
        simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, project, factorProjection_tmul]
        rfl
      | add u v hu hv => simp only [map_add, hu, hv]
    rw [he, he, hx]
    have hy := congrArg Units.val (hnat f₀ (c.hom.app R x))
    exact (congrArg (fun y : T S ⊗[F] A => factor S (project S y)) hy).trans (hmap _)

theorem splitCentreTypeAModel : SplitCentreTypeAModel.{u} := by
  intro F E A L _ _ _ _ _ _ _ _ _ _ _ _ _ hA ι _ b star H hH
  obtain ⟨hL, hd, _⟩ := factorReducedNorm (L := L) (R := L) hA b
  exact ⟨hL, hd, normOneOfUnitaryPoints hA b star hH hL
    (U := Unipotent.baseChangedAlgebraicGroup L H) (baseChangePointIso H.val)⟩

end SplitCentre

private theorem diagramCharacter_cases (χ : DiagramCharacter F K) :
    χ = 1 ∨ Function.Surjective χ := by
  by_cases h : χ = 1
  · exact Or.inl h
  · right
    obtain ⟨σ, hσ⟩ : ∃ σ, χ σ ≠ 1 := by
      by_contra! he
      exact h (MonoidHom.ext he)
    intro p
    by_cases hp : p = 1
    · exact ⟨1, (map_one χ).trans hp.symm⟩
    · exact ⟨σ, parity_eq_of_odd hσ hp⟩

private theorem lowerMatrixAction
    (χ : DiagramCharacter F K) (g : Gal(K/F) → GL (Index.{u} n) K)
    (act : Gal(K/F) →* MulAut (SpecialLinearGroup (Index.{u} n) K))
    (ha : ∀ σ X, (act σ X).val = (g σ).val *
      (if χ σ = 1 then X.val.map σ else ((X⁻¹).val.map σ).transpose) * (g σ)⁻¹.val) :
    ∀ σ (x : SpecialLinearGroup (Fin n) K),
      (_root_.LinearAlgebraicGroups.Descent.Forms.relabelAction
        (liftSpecialLinear (R := K) n).symm act σ x).val =
        (lowerGL (g σ)).val *
          (if χ σ = 1 then x.val.map σ else ((x⁻¹).val.map σ).transpose) * (lowerGL (g σ))⁻¹.val := by
  intro σ x
  let r := Matrix.reindexRingEquiv K (Equiv.ulift : Index.{u} n ≃ Fin n)
  have h := congrArg r (ha σ (liftSpecialLinear n x))
  rw [map_mul, map_mul] at h
  have hinv : r (g σ)⁻¹.val = (lowerGL (g σ))⁻¹.val :=
    congrArg Units.val (map_inv (Units.map r.toMonoidHom) (g σ)).symm
  rw [hinv] at h
  by_cases hp : χ σ = 1
  · rw [ite_eq_left hp] at h ⊢
    exact h
  · rw [ite_eq_right hp, ← map_inv (liftSpecialLinear n)] at h
    rwa [ite_eq_right hp]

set_option maxHeartbeats 700000 in
private theorem modelFromLifts [FiniteDimensional F K] [IsGalois F K]
    {G H : AffineAlgebraicGroup F} (s : SpecialMatrixPoints G n)
    (i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val)
    (hn : 2 ≤ n) (χ : DiagramCharacter F K) (g : Gal(K/F) → GL (Index.{u} n) K)
    (hi : HasMatrixTransport s i χ g)
    (β : ∀ σ : Gal(K/F), MatrixLift n σ (χ σ))
    (hβ : ∀ σ x, (β σ).toAddEquiv x = (lowerGL (g σ)).val *
      (if χ σ = 1 then x.map σ else (x.map σ).transpose) * (lowerGL (g σ))⁻¹.val)
    (act : Gal(K/F) →* MulAut (SpecialLinearGroup (Fin n) K))
    (ha : LiftsAction χ β act) : HasTypeAModel H χ β := by
  constructor
  · intro hχ
    subst χ
    obtain ⟨ρ, c, hρ, hc, hA, hd, e, he, _⟩ := fixedInnerAlgebra hn β act ha
    refine ⟨ρ, hρ, hA, hd, innerSchemeModel hA s i g hi hd e ρ c he hc ?_⟩
    intro σ
    apply projectiveClass hc σ (lowerGL (g σ))
    intro x
    simp only [hρ, hβ, MonoidHom.one_apply, ite_true]
  · intro hχ
    obtain ⟨hdeg, ρ, hρ, hA, hd, ⟨e, he⟩, bar, inv, hne, hc, hsq, hinv, hbar⟩ :=
      fixedAlgebraWithInvolution hn χ hχ β act ha
    let E := DiagramField χ
    let A := ρ.fixedSubalgebra
    let : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := hdeg }
    have : Algebra.IsSeparable F E := inferInstance
    let star : _root_.LinearAlgebraicGroups.UnitaryNormEquations.SecondKind F E A :=
      _root_.LinearAlgebraicGroups.UnitaryNormEquations.SecondKind.ofRingEquiv
        bar hne inv hsq (fun a => congrArg MulOpposite.unop (hc a))
    refine ⟨hdeg, inferInstance, ρ, hρ, hA, hd, star, hinv, hbar, ?_⟩
    have hE (σ : Gal(K/F)) (a : E) :
        σ (algebraMap E K a) = algebraMap E K (if χ σ = 1 then a else star.conjugation a) := by
      by_cases hσ : χ σ = 1
      · rw [ite_eq_left hσ]
        exact (IntermediateField.mem_fixedField_iff χ.ker a.val).mp a.property σ hσ
      · rw [ite_eq_right hσ]
        exact (hbar σ hσ a).symm
    have he₁ (x : A) : e (1 ⊗ₜ[E] x) = x.val :=
      (he 1 x).trans (one_smul K x.val)
    have hrestrict (σ : Gal(K/F)) (x : A) :
        (β σ).toAddEquiv (e (1 ⊗ₜ[E] x)) =
          e (1 ⊗ₜ[E] (if χ σ = 1 then x else (star.adjoint x).unop)) := by
      rw [he₁ x, he₁]
      by_cases hσ : χ σ = 1
      · rw [ite_eq_left hσ]
        let τ : χ.ker := ⟨σ, hσ⟩
        exact (hρ τ x.val).symm.trans
          (x.property (IntermediateField.subgroupEquivAlgEquiv χ.ker τ))
      · rw [ite_eq_right hσ]
        exact (hinv σ hσ x).symm
    exact outerSchemeModel hA star s i χ g hi hd e β hβ hE hrestrict

private theorem modelFromMatrixDescent [FiniteDimensional F K] [IsGalois F K]
    {G H : AffineAlgebraicGroup F} {s : SpecialMatrixPoints G n}
    {i : (groupBaseChange F K).obj G.val ≅ (groupBaseChange F K).obj H.val}
    (hn : 3 ≤ n) (h : MatrixDescentAt s i) : MatrixModelAt s i := by
  obtain ⟨_, _, _, _, _, χ, g, act, _, _, _, _, _, _, _, hi, _, ha⟩ := h
  let t := _root_.LinearAlgebraicGroups.Descent.Forms.relabelAction (liftSpecialLinear (R := K) n).symm act
  obtain ⟨β, hL, hβ⟩ := matrixLiftsExist χ (fun σ => lowerGL (g σ)) t (lowerMatrixAction χ g act ha)
  obtain ⟨h1, hm⟩ := matrixActionLaw (by omega) χ β t hL
  refine ⟨χ, g, β, hi, fun χ' g' h' => matrixTransportCharacter_unique hn h' hi,
    hβ, h1, hm, diagramCharacter_cases χ, ?_⟩
  exact modelFromLifts s i (by omega) χ g hi β hβ t hL

theorem typeAModelForTrivialization : TypeAModelForTrivialization.{u} := by
  intro F K _ _ _ _ _ n hn G H s i
  exact modelFromMatrixDescent hn (Arithmetic.TypeAMatrixDescentData.matrixDescentForTrivialization hn s i)

theorem typeAForms : TypeAForms.{u} := by
  intro F _ n hn G H s h
  obtain ⟨K, _, _, _, _, i, hi⟩ := Arithmetic.TypeAMatrixDescentData.finiteMatrixDescent hn s H h
  exact ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, i, modelFromMatrixDescent hn hi⟩

theorem absoluteTypeAMatrixForm : AbsoluteTypeAMatrixForm.{u} := by
  intro F _ r G H s h
  obtain ⟨L, _, _, _, P, hP, hsemi, hsc, D, e, hCartan⟩ := h
  let := D.comm
  have hspan : Submodule.span ℤ (Set.range D.toBased.datum.coroot) = ⊤ :=
    (Classification.SimplyConnectedLattice.latticeCriterion P.G hsemi P.T P.split P.maximal D.datum).mp hsc
  have hb : Submodule.span ℤ (Set.range (fun j : D.toBased.base.support => D.toBased.datum.coroot j)) = ⊤ := by
    have hr : Set.range (fun j : D.toBased.base.support => D.toBased.datum.coroot j) =
        D.toBased.datum.coroot '' (D.toBased.base.support : Set D.toBased.I) := by
      ext y
      exact ⟨fun ⟨j, hj⟩ => ⟨j.val, j.property, hj⟩, fun ⟨j, hj, hy⟩ => ⟨⟨j, hj⟩, hy⟩⟩
    rw [hr, D.toBased.base.span_int_coroot_support, hspan]
  have hD : HasSimplyConnectedTypeA r D.toBased :=
    ⟨e, Module.Basis.mk D.toBased.base.linearIndepOn_coroot hb.ge, Module.Basis.mk_apply _ _, hCartan⟩
  let m := extendMatrixPoints (K := L) s
  obtain ⟨A, Q, hQ, hcompare⟩ := splitMatrixComparison r (Unipotent.baseChangedAlgebraicGroup L G) m
  obtain ⟨U, ⟨p⟩⟩ := Classification.Pinning.pinningsExist A P
  obtain ⟨q⟩ := hcompare ⟨P, U, p⟩ D hD
  refine ⟨L, inferInstance, inferInstance, inferInstance, ?_⟩
  have f : Q.pair.G.val ≅ P.G.val := q.group.symm
  rw [hQ, hP] at f
  exact ⟨f⟩

set_option backward.isDefEq.respectTransparency false in
private theorem specialMatrixModel (F : Type u) [Field F] (n : ℕ) :
    ∃ G : AffineAlgebraicGroup F, Nonempty (SpecialMatrixPoints G n) := by
  obtain ⟨_, sl, _, _, _, _, _, _, _, hrep⟩ :=
    _root_.LinearAlgebraicGroups.StandardGroups.specialLinearGroupSpecification F (Index.{u} n)
  let := sl.hopf
  obtain ⟨_, _, s, _⟩ := hrep
  exact ⟨spectrum F (SLCoordinates F (Index.{u} n)), ⟨s⟩⟩

theorem absoluteTypeAForms : AbsoluteTypeAForms.{u} := by
  intro F _ r hr H h
  obtain ⟨G, ⟨s⟩⟩ := specialMatrixModel F (r + 1)
  refine ⟨G, s, ?_⟩
  exact typeAForms (by omega) s (absoluteTypeAMatrixForm s h)

end SchemeDescent

end LinearAlgebraicGroups.OuterTypeAModels
