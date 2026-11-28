import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.RestrictedDual
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.FiniteLength
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Reconstruction
import Batteries.Tactic.OpenPrivate
import MathGenome.Internal.FourVolumeAlgebra.Shared.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Restricted weight duality for the finite category O. -/

noncomputable section

open CategoryTheory UniversalEnvelopingAlgebra
open scoped Classical DirectSum ModuleCat.Algebra
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)

namespace RepTheorySurvey.CategoryO.RestrictedDual

abbrev tau := @Specs.RepTheorySurvey.CategoryO.RestrictedDual.tau_value
abbrev dualModule := @Specs.RepTheorySurvey.CategoryO.RestrictedDual.dualModule_value
abbrev dualMap := @Specs.RepTheorySurvey.CategoryO.RestrictedDual.dualMap_value
abbrev costandard := @Specs.RepTheorySurvey.CategoryO.RestrictedDual.costandard_value


open Specs.RepTheorySurvey.CategoryO.RestrictedDual
open _root_.LieAlgebrasAndRepresentations (serre_relations serre_reconstruction)
open _root_.LieAlgebrasAndRepresentations.Reconstruction
open _root_.LieAlgebrasAndRepresentations.RealRootSpace (cartan_isMaximalToral)

open _root_.LieAlgebrasAndRepresentations

attribute [local instance 100] LieRing.ofAssociativeRing

universe u v
variable {g : Type u} [LieRing g] [LieAlgebra ℂ g]

private def oppositeGenerator : g →ₗ[ℂ] (U g)ᵐᵒᵖ :=
  (MulOpposite.opLinearEquiv ℂ).toLinearMap.comp (ι ℂ).toLinearMap

@[simp] private theorem oppositeGenerator_apply (x : g) :
    oppositeGenerator x = MulOpposite.op (ι ℂ x) := rfl

private theorem oppositeGenerator_lie (x y : g) :
    ⁅oppositeGenerator x, oppositeGenerator y⁆ = oppositeGenerator ⁅y, x⁆ := by
  rw [oppositeGenerator_apply, oppositeGenerator_apply, oppositeGenerator_apply,
    LieHom.map_lie]
  rfl

private theorem oppositeGenerator_iterBracket (x y : g) (n : ℕ) :
    Serre.iterBracket (oppositeGenerator x) n (oppositeGenerator y) =
      (-1 : ℂ) ^ n • oppositeGenerator (Serre.iterBracket x n y) := by
  induction n with
  | zero => simp [Serre.iterBracket]
  | succ n ih =>
    simp only [Serre.iterBracket, ih, lie_smul, oppositeGenerator_lie, pow_succ]
    rw [← lie_skew x, map_neg, mul_smul, neg_one_smul]
    simp only [neg_neg]

variable [FiniteDimensional ℂ g] (D : Setup g)

set_option backward.isDefEq.respectTransparency false in
private theorem switched_relations (A : Matrix D.Simple D.Simple ℤ)
    (hA : ∀ i j, ⁅(D.h i : g), (D.h j : g)⁆ = 0 ∧
      ⁅(D.h i : g), D.e j⁆ = (A i j : ℂ) • D.e j ∧
      ⁅(D.h i : g), D.f j⁆ = -(A i j : ℂ) • D.f j ∧
      ⁅D.e i, D.f j⁆ = if i = j then (D.h i : g) else 0)
    (hs : ∀ i j, i ≠ j → A i j ≤ 0 ∧
      ((LieAlgebra.ad ℂ g (D.e i)) ^ (1 - A i j).toNat) (D.e j) = 0 ∧
      ((LieAlgebra.ad ℂ g (D.f i)) ^ (1 - A i j).toNat) (D.f j) = 0) :
    Serre.RelationsHold A (fun i => oppositeGenerator (D.f i))
      (fun i => oppositeGenerator (D.e i)) (fun i => oppositeGenerator (D.h i : g)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [oppositeGenerator_lie, (hA j i).1, map_zero]
  · intro i j
    rw [oppositeGenerator_lie, ← lie_skew (D.f j) (D.h i : g), (hA i j).2.2.1,
      neg_smul, neg_neg, map_smul, Int.cast_smul_eq_zsmul ℂ]
  · intro i j
    rw [oppositeGenerator_lie, ← lie_skew (D.e j) (D.h i : g), (hA i j).2.1,
      map_neg, map_smul, Int.cast_smul_eq_zsmul ℂ]
  · intro i j
    rw [oppositeGenerator_lie, (hA j i).2.2.2]
    by_cases h : i = j
    · subst j
      simp
    · simp [h, Ne.symm h]
  · intro i j hij
    rw [oppositeGenerator_iterBracket, Serre.iterBracket_eq_pow, (hs i j hij).2.2,
      map_zero, smul_zero]
  · intro i j hij
    rw [oppositeGenerator_iterBracket, Serre.iterBracket_eq_pow, (hs i j hij).2.1,
      map_zero, smul_zero]

private theorem enveloping_hom_ext {B : Type*} [Ring B] [Algebra ℂ B]
    (A : Matrix D.Simple D.Simple ℤ) (r : Serre.Algebra A ≃ₗ⁅ℂ⁆ g)
    (hr : ∀ i, r (Serre.e A i) = D.e i ∧ r (Serre.f A i) = D.f i ∧
      r (Serre.h A i) = (D.h i : g))
    (p q : U g →ₐ[ℂ] B)
    (he : ∀ i, p (ι ℂ (D.e i)) = q (ι ℂ (D.e i)))
    (hf : ∀ i, p (ι ℂ (D.f i)) = q (ι ℂ (D.f i)))
    (hh : ∀ i, p (ι ℂ (D.h i : g)) = q (ι ℂ (D.h i : g))) : p = q := by
  apply UniversalEnvelopingAlgebra.hom_ext
  let P := (p : U g →ₗ⁅ℂ⁆ B).comp (ι ℂ)
  let Q := (q : U g →ₗ⁅ℂ⁆ B).comp (ι ℂ)
  change P = Q
  have h : P.comp r.toLieHom = Q.comp r.toLieHom := by
    apply Serre.hom_ext A
    · intro i
      change p (ι ℂ (r (Serre.e A i))) = q (ι ℂ (r (Serre.e A i)))
      rw [(hr i).1, he]
    · intro i
      change p (ι ℂ (r (Serre.f A i))) = q (ι ℂ (r (Serre.f A i)))
      rw [(hr i).2.1, hf]
    · intro i
      change p (ι ℂ (r (Serre.h A i))) = q (ι ℂ (r (Serre.h A i)))
      rw [(hr i).2.2, hh]
  ext x
  obtain ⟨x, rfl⟩ := r.surjective x
  exact LieHom.congr_fun h x

theorem tau_spec : TauSpec.{u} := by
  intro g _ _ _ D
  have htor := cartan_isMaximalToral D.semisimple D.cartan
  have hn : Specs.LieAlgebrasAndRepresentations.Reconstruction.NormalizedSimpleVectors
      D.cartan D.direction D.e D.f := fun i =>
    ⟨(D.triple i).e_mem, (D.triple i).f_mem, (D.triple i).e_ne_zero,
      (D.triple i).f_ne_zero, (D.triple i).lie_e_f⟩
  obtain ⟨A, r, hA, hr, hcart⟩ :=
    serre_reconstruction D.semisimple D.cartan htor D.direction D.regular D.e D.f hn
  obtain ⟨B, hB, hrel, hserre, _⟩ :=
    serre_relations D.semisimple D.cartan htor D.direction D.regular D.e D.f hn
  have hAB : ∀ i j, B i j = A i j := fun i j =>
    Int.cast_injective (α := ℂ) ((hB i j).symm.trans (hA i j))
  have hrelA (i j : D.Simple) := hrel i j
  simp only [hAB] at hrelA hserre
  have hsign : ∀ i j, i ≠ j → A i j ≤ 0 := fun i j hij => (hserre i j hij).1
  let E (i : D.Simple) := oppositeGenerator (D.f i)
  let F (i : D.Simple) := oppositeGenerator (D.e i)
  let H (i : D.Simple) := oppositeGenerator (D.h i : g)
  obtain ⟨p, ⟨hpE, hpF, hpH⟩, _⟩ :=
    Serre.presentation_spec A hsign ((U g)ᵐᵒᵖ) E F H (switched_relations D A hrelA hserre)
  let t := UniversalEnvelopingAlgebra.lift ℂ (p.comp r.symm.toLieHom)
  have ht : ExchangesGenerators D t := by
    intro i
    have he : r.symm (D.e i) = Serre.e A i := by
      rw [← (hr i).1, r.symm_apply_apply]
    have hf : r.symm (D.f i) = Serre.f A i := by
      rw [← (hr i).2.1, r.symm_apply_apply]
    have hh : r.symm (D.h i : g) = Serre.h A i := by
      rw [← (hr i).2.2, r.symm_apply_apply]
    have hl (x : g) : t (ι ℂ x) = p (r.symm x) :=
      UniversalEnvelopingAlgebra.lift_ι_apply ℂ (p.comp r.symm.toLieHom) x
    exact ⟨(hl _).trans (by rw [hh]; exact hpH i),
      (hl _).trans (by rw [he]; exact hpE i),
      (hl _).trans (by rw [hf]; exact hpF i)⟩
  have hτ : ExchangesGenerators D (tau D) := Classical.epsilon_spec ⟨t, ht⟩
  refine ⟨hτ, ?_, ?_, ?_⟩
  · intro s hs
    exact enveloping_hom_ext D A r hr s (tau D)
      (fun i => ((hs i).2.1).trans ((hτ i).2.1).symm)
      (fun i => ((hs i).2.2).trans ((hτ i).2.2).symm)
      (fun i => ((hs i).1).trans ((hτ i).1).symm)
  · intro h
    have hh : (h : g) ∈ (Serre.cartan A).map r.toLinearEquiv.toLinearMap :=
      hcart.symm ▸ h.property
    obtain ⟨x, hx, hxe⟩ := hh
    change r x = (h : g) at hxe
    rw [← hxe]
    change ((tau D).toLinearMap.comp (ι ℂ).toLinearMap) (r x) =
      oppositeGenerator (r x)
    refine Submodule.span_induction (p := fun y _ =>
      ((tau D).toLinearMap.comp (ι ℂ).toLinearMap) (r y) = oppositeGenerator (r y))
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      rw [(hr i).2.2, LinearMap.comp_apply, oppositeGenerator_apply]
      exact (hτ i).1
    · rw [map_zero, map_zero, map_zero]
    · intro x y _ _ hx hy
      rw [map_add, map_add, map_add, hx, hy]
    · intro c x _ hx
      rw [map_smul, map_smul, map_smul, hx]
  · let t₂ := (AlgEquiv.opOp ℂ (U g)).symm.toAlgHom.comp
      ((AlgHom.op (tau D)).comp (tau D))
    have h₂ : ∀ a, t₂ a = ((tau D) ((tau D) a).unop).unop := fun _ => rfl
    have heq : t₂ = AlgHom.id ℂ (U g) := by
      apply enveloping_hom_ext D A r hr
      · intro i
        rw [h₂, (hτ i).2.1, MulOpposite.unop_op, (hτ i).2.2]
        rfl
      · intro i
        rw [h₂, (hτ i).2.2, MulOpposite.unop_op, (hτ i).2.1]
        rfl
      · intro i
        rw [h₂, (hτ i).1, MulOpposite.unop_op, (hτ i).1]
        rfl
    intro a
    exact (h₂ a).symm.trans (DFunLike.congr_fun heq a)


section Support

open private root_smul_weight from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightBounds

variable (X : ModuleCat.{v} (U g))

private abbrev W (μ : D.Weight) := weightSpace D.cartan X μ

private abbrev asFunctional (l : twistedDual D X) : Module.Dual ℂ X := l

private theorem functional_smul (a : U g) (l : twistedDual D X) (x : X) :
    asFunctional D X (a • l) x = asFunctional D X l ((tau D a).unop • x) := rfl

private theorem functional_smul_complex (c : ℂ) (l : twistedDual D X) (x : X) :
    asFunctional D X (c • l) x = c * asFunctional D X l x := by
  change asFunctional D X ((algebraMap ℂ (U g) c) • l) x = _
  rw [functional_smul, (tau D).commutes, MulOpposite.algebraMap_apply,
    MulOpposite.unop_op, algebraMap_smul, map_smul]
  rfl

private def unbundle : twistedDual D X ≃ₗ[ℂ] Module.Dual ℂ X where
  toFun := asFunctional D X
  invFun l := l
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' c l := LinearMap.ext fun x => functional_smul_complex D X c l x

private def finiteSupports : Submodule ℂ (twistedDual D X) where
  carrier := {l | (functionalSupport D X (asFunctional D X l)).Finite}
  zero_mem' := by
    change (functionalSupport D X (0 : Module.Dual ℂ X)).Finite
    simp [functionalSupport]
  add_mem' := by
    intro l m hl hm
    apply (hl.union hm).subset
    rintro μ ⟨x, hx⟩
    change asFunctional D X l x + asFunctional D X m x ≠ 0 at hx
    by_cases he : asFunctional D X l x = 0
    · right
      exact ⟨x, fun hz => hx (by rw [he, hz, add_zero])⟩
    · left
      exact ⟨x, he⟩
  smul_mem' := by
    intro c l hl
    apply hl.subset
    rintro μ ⟨x, hx⟩
    refine ⟨x, fun hz => hx ?_⟩
    rw [functional_smul_complex, hz, mul_zero]

private theorem root_preserves_support (a z : g) (α : D.Weight)
    (ht : tau D (ι ℂ a) = MulOpposite.op (ι ℂ z))
    (hz : z ∈ Specs.LieAlgebrasAndRepresentations.RootDecomposition.rootSpace_value D.cartan α)
    (l : twistedDual D X) (hl : l ∈ finiteSupports D X) :
    (ι ℂ a) • l ∈ finiteSupports D X := by
  change (functionalSupport D X (asFunctional D X l)).Finite at hl
  apply (hl.image (fun μ => μ - α)).subset
  rintro μ ⟨x, hx⟩
  let y : W D X (α + μ) := ⟨(ι ℂ z) • (x : X),
    root_smul_weight D X α μ z x hz x.property⟩
  refine ⟨α + μ, ⟨y, ?_⟩, by change α + μ - α = μ; rw [add_comm α μ, add_sub_cancel_right]⟩
  intro hf
  apply hx
  rw [functional_smul, ht, MulOpposite.unop_op]
  exact hf

private theorem cartan_preserves_support (h : D.cartan)
    (l : twistedDual D X) (hl : l ∈ finiteSupports D X) :
    (ι ℂ (h : g)) • l ∈ finiteSupports D X := by
  change (functionalSupport D X (asFunctional D X l)).Finite at hl
  apply hl.subset
  rintro μ ⟨x, hx⟩
  refine ⟨x, fun hf => hx ?_⟩
  rw [functional_smul, (tau_spec D).2.2.1 h, MulOpposite.unop_op,
    (mem_weightSpace D.cartan X μ x).mp x.property h, map_smul, hf, smul_zero]

private theorem preservesSupport (a : U g) (l : twistedDual D X)
    (hl : l ∈ finiteSupports D X) : a • l ∈ finiteSupports D X := by
  have ht := (tau_spec D).1
  have htor := cartan_isMaximalToral D.semisimple D.cartan
  have hn : Specs.LieAlgebrasAndRepresentations.Reconstruction.NormalizedSimpleVectors
      D.cartan D.direction D.e D.f := fun i =>
    ⟨(D.triple i).e_mem, (D.triple i).f_mem, (D.triple i).e_ne_zero,
      (D.triple i).f_ne_zero, (D.triple i).lie_e_f⟩
  obtain ⟨_, _, _, _, hgen⟩ :=
    serre_relations D.semisimple D.cartan htor D.direction D.regular D.e D.f hn
  let S : LieSubalgebra ℂ g :=
    { carrier := {x | ∀ q ∈ finiteSupports D X, (ι ℂ x) • q ∈ finiteSupports D X}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy q hq
        rw [map_add, add_smul]
        exact (finiteSupports D X).add_mem (hx q hq) (hy q hq)
      smul_mem' := by
        intro c x hx q hq
        rw [map_smul, smul_assoc]
        exact (finiteSupports D X).smul_mem c (hx q hq)
      lie_mem' := by
        intro x y hx hy q hq
        rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, sub_smul, mul_smul, mul_smul]
        exact (finiteSupports D X).sub_mem (hx _ (hy _ hq)) (hy _ (hx _ hq)) }
  have hS : S = ⊤ := by
    apply top_unique
    rw [← hgen, LieSubalgebra.lieSpan_le]
    rintro x ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) l hl
    · exact root_preserves_support D X _ _ (-D.alpha i) (ht i).2.1 (D.triple i).f_mem l hl
    · exact root_preserves_support D X _ _ (D.alpha i) (ht i).2.2 (D.triple i).e_mem l hl
    · exact cartan_preserves_support D X (D.h i) l hl
  revert l
  induction a using _root_.Shared.Lie.enveloping_induction ℂ g with
  | scalar c =>
    intro l hl
    exact (finiteSupports D X).smul_mem c hl
  | generator x =>
    exact show x ∈ S from hS.symm ▸ trivial
  | mul a b ha hb =>
    intro l hl
    rw [mul_smul]
    exact ha _ (hb _ hl)
  | add a b ha hb =>
    intro l hl
    rw [add_smul]
    exact (finiteSupports D X).add_mem (ha _ hl) (hb _ hl)

private theorem restricted_finite_support (l : twistedDual D X) (hl : l ∈ restrictedPart D X) :
    (functionalSupport D X (asFunctional D X l)).Finite := by
  change l ∈ finiteSupports D X
  induction hl using Submodule.span_induction with
  | mem l hl =>
    obtain ⟨μ, hμ⟩ := hl
    exact (Set.finite_singleton μ).subset hμ
  | zero => exact (finiteSupports D X).zero_mem
  | add l m _ _ hl hm => exact (finiteSupports D X).add_mem hl hm
  | smul a l _ hl => exact preservesSupport D X a l hl

end Support


section WeightDecomposition

variable (X : ModuleCat.{v} (U g))
variable (hX : DirectSum.IsInternal (W D X))

private def inclusionDual : dualModule D X →ₗ[ℂ] Module.Dual ℂ X :=
  (unbundle D X).toLinearMap.comp ((restrictedPart D X).subtype.restrictScalars ℂ)

private theorem pair_complex (c : ℂ) (l : dualModule D X) (x : X) :
    pair D X (c • l) x = c * pair D X l x :=
  functional_smul_complex D X c l.val x

include hX in
private theorem functional_ext (l m : Module.Dual ℂ X)
    (he : ∀ (μ : D.Weight) (x : W D X μ), l x = m x) : l = m := by
  have h : (⨆ μ, W D X μ) ≤ (l - m).ker := iSup_le fun μ x hx =>
    sub_eq_zero.mpr (he μ ⟨x, hx⟩)
  rw [hX.submodule_iSup_eq_top] at h
  ext x
  exact sub_eq_zero.mp (h (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ X)))

include hX in
private theorem dual_ext_weights (l m : dualModule D X)
    (he : ∀ (μ : D.Weight) (x : W D X μ), pair D X l x = pair D X m x) : l = m := by
  apply Subtype.ext
  exact functional_ext D X hX (asFunctional D X l.val) (asFunctional D X m.val) he

private def weightProjection (μ : D.Weight) : X →ₗ[ℂ] W D X μ :=
  (DirectSum.component ℂ D.Weight (fun μ => W D X μ) μ).comp
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap (W D X)) hX).symm.toLinearMap

private theorem weightProjection_same (μ : D.Weight) (x : W D X μ) :
    weightProjection D X hX μ x = x :=
  hX.ofBijective_coeLinearMap_same x

private theorem weightProjection_other {μ ν : D.Weight} (h : ν ≠ μ) (x : W D X ν) :
    weightProjection D X hX μ x = 0 :=
  hX.ofBijective_coeLinearMap_of_ne h x

private def extendWeight (μ : D.Weight) : Module.Dual ℂ (W D X μ) →ₗ[ℂ] dualModule D X :=
  ((unbundle D X).symm.toLinearMap.comp (weightProjection D X hX μ).dualMap).codRestrict
    ((restrictedPart D X).restrictScalars ℂ) (fun l => by
      apply Submodule.subset_span
      refine ⟨μ, ?_⟩
      rintro ν ⟨x, hx⟩
      by_contra hn
      change l (weightProjection D X hX μ x) ≠ 0 at hx
      rw [weightProjection_other D X hX hn x, map_zero] at hx
      exact hx rfl)

private theorem pair_extend_same (μ : D.Weight) (l : Module.Dual ℂ (W D X μ)) (x : W D X μ) :
    pair D X (extendWeight D X hX μ l) x = l x := by
  change l (weightProjection D X hX μ x) = l x
  rw [weightProjection_same]

private theorem pair_extend_other {μ ν : D.Weight} (h : ν ≠ μ)
    (l : Module.Dual ℂ (W D X μ)) (x : W D X ν) :
    pair D X (extendWeight D X hX μ l) x = 0 := by
  change l (weightProjection D X hX μ x) = 0
  rw [weightProjection_other D X hX h x, map_zero]

private def sumDual : (⨁ μ : D.Weight, Module.Dual ℂ (W D X μ)) →ₗ[ℂ] dualModule D X :=
  DirectSum.toModule ℂ _ _ (extendWeight D X hX)

private theorem sumDual_of (ν : D.Weight) (q : Module.Dual ℂ (W D X ν)) :
    sumDual D X hX (DirectSum.of (fun μ => Module.Dual ℂ (W D X μ)) ν q) =
      extendWeight D X hX ν q :=
  DirectSum.toModule_lof (R := ℂ) (φ := extendWeight D X hX) ν q

private theorem pair_sumDual (l : ⨁ μ : D.Weight, Module.Dual ℂ (W D X μ))
    (μ : D.Weight) (x : W D X μ) :
    pair D X (sumDual D X hX l) x = l μ x := by
  induction l using DirectSum.induction_on with
  | zero => rw [map_zero]; rfl
  | of ν q =>
    rw [sumDual_of]
    by_cases h : ν = μ
    · subst ν
      rw [DirectSum.of_eq_same, pair_extend_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), pair_extend_other D X hX (Ne.symm h)]
      rfl
  | add l m hl hm =>
    rw [map_add]
    change pair D X (sumDual D X hX l) x + pair D X (sumDual D X hX m) x = l μ x + m μ x
    rw [hl, hm]

private theorem exists_sumDual_of_finite (l : Module.Dual ℂ X)
    (hl : (functionalSupport D X l).Finite) :
    ∃ s, inclusionDual D X (sumDual D X hX s) = l := by
  let s : ⨁ μ : D.Weight, Module.Dual ℂ (W D X μ) :=
    DFinsupp.mk hl.toFinset (fun μ => (W D X μ.val).subtype.dualMap l)
  refine ⟨s, functional_ext D X hX _ _ (fun μ x => ?_)⟩
  change pair D X (sumDual D X hX s) x = l x
  rw [pair_sumDual]
  by_cases h : μ ∈ hl.toFinset
  · rw [show s μ = (W D X μ).subtype.dualMap l from DFinsupp.mk_of_mem h]
    rfl
  · rw [show s μ = 0 from DFinsupp.mk_of_notMem h]
    change 0 = l x
    by_contra hn
    exact h (hl.mem_toFinset.mpr ⟨x, Ne.symm hn⟩)

private theorem sumDual_bijective : Function.Bijective (sumDual D X hX) := by
  constructor
  · intro a b h
    apply DirectSum.ext
    intro μ
    ext x
    rw [← pair_sumDual D X hX a μ x, ← pair_sumDual D X hX b μ x, h]
  · intro l
    have h := restricted_finite_support D X l.val l.property
    obtain ⟨s, hs⟩ := exists_sumDual_of_finite D X hX (asFunctional D X l.val) h
    exact ⟨s, Subtype.ext hs⟩

theorem restrictedDual_spec : RestrictedDualSpec.{u,v} := by
  intro g _ _ _ D X hX
  constructor
  · intro l
    refine ⟨restricted_finite_support D X l, fun hf => ?_⟩
    obtain ⟨a, ha⟩ := exists_sumDual_of_finite D X hX l hf
    change (sumDual D X hX a).val = l at ha
    exact ha ▸ (sumDual D X hX a).property
  · exact ⟨LinearEquiv.ofBijective _ (sumDual_bijective D X hX), pair_sumDual D X hX⟩

end WeightDecomposition


section DualWeights

variable (X : ModuleCat.{v} (U g))
variable (hX : DirectSum.IsInternal (W D X))

private theorem pair_cartan_action (ν : D.Weight) (x : W D X ν) (h : D.cartan)
    (l : dualModule D X) :
    pair D X ((ι ℂ (h : g)) • l) x = ν h * pair D X l x := by
  rw [pair_smul, (tau_spec D).2.2.1 h, MulOpposite.unop_op,
    (mem_weightSpace D.cartan X ν x).mp x.property h]
  exact (inclusionDual D X l).map_smul (ν h) (x : X)

include hX in
private theorem dual_weight_iff (μ : D.Weight) (l : dualModule D X) :
    l ∈ W D (dualModule D X) μ ↔
      ∀ (ν : D.Weight), ν ≠ μ → ∀ x : W D X ν, pair D X l x = 0 := by
  constructor
  · intro hl ν hn x
    by_contra hne
    apply hn
    ext h
    have hh := congrArg (fun q : dualModule D X => pair D X q x)
      ((mem_weightSpace D.cartan (dualModule D X) μ l).mp hl h)
    rw [pair_cartan_action D X ν x, pair_complex] at hh
    exact mul_right_cancel₀ hne hh
  · intro hl
    apply (mem_weightSpace D.cartan (dualModule D X) μ l).mpr
    intro h
    apply dual_ext_weights D X hX
    intro ν x
    rw [pair_cartan_action D X ν x, pair_complex]
    by_cases he : ν = μ
    · subst ν
      rfl
    · rw [hl ν he x, mul_zero, mul_zero]

private def weightRestriction (μ : D.Weight) :
    W D (dualModule D X) μ →ₗ[ℂ] Module.Dual ℂ (W D X μ) :=
  ((W D X μ).subtype.dualMap.comp (inclusionDual D X)).comp
    (W D (dualModule D X) μ).subtype

include hX in
private theorem extendWeight_mem (μ : D.Weight) (l : Module.Dual ℂ (W D X μ)) :
    extendWeight D X hX μ l ∈ W D (dualModule D X) μ :=
  (dual_weight_iff D X hX μ _).mpr fun _ h x => pair_extend_other D X hX h l x

include hX in
private theorem weightRestriction_bijective (μ : D.Weight) :
    Function.Bijective (weightRestriction D X μ) := by
  constructor
  · intro l m he
    apply Subtype.ext
    apply dual_ext_weights D X hX
    intro ν x
    by_cases h : ν = μ
    · subst ν
      exact LinearMap.congr_fun he x
    · rw [(dual_weight_iff D X hX μ l).mp l.property ν h x,
        (dual_weight_iff D X hX μ m).mp m.property ν h x]
  · intro l
    refine ⟨⟨extendWeight D X hX μ l, extendWeight_mem D X hX μ l⟩, ?_⟩
    ext x
    exact pair_extend_same D X hX μ l x

private def dualWeightEquiv (μ : D.Weight) :
    W D (dualModule D X) μ ≃ₗ[ℂ] Module.Dual ℂ (W D X μ) :=
  LinearEquiv.ofBijective _ (weightRestriction_bijective D X hX μ)

include hX in
private theorem dual_internal : DirectSum.IsInternal (W D (dualModule D X)) := by
  let := restrictedLieRingModule (dualModule D X) (g := g)
  let := restrictedLieModule (dualModule D X) (g := g)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · exact WeightExactness.weightSpaces_independent (H := D.cartan) (X := dualModule D X)
  · apply top_unique
    intro l hl
    clear hl
    obtain ⟨q, rfl⟩ := (sumDual_bijective D X hX).2 l
    induction q using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | of ν f =>
      rw [sumDual_of]
      exact Submodule.mem_iSup_of_mem ν (extendWeight_mem D X hX ν f)
    | add a b ha hb => rw [map_add]; exact add_mem ha hb

include hX in
private theorem dual_support :
    Specs.RepTheorySurvey.CategoryO.WeightBounds.support D (dualModule D X) =
      Specs.RepTheorySurvey.CategoryO.WeightBounds.support D X := by
  ext μ
  change W D (dualModule D X) μ ≠ ⊥ ↔ W D X μ ≠ ⊥
  rw [← Submodule.nontrivial_iff_ne_bot, ← Submodule.nontrivial_iff_ne_bot]
  exact (dualWeightEquiv D X hX μ).toEquiv.nontrivial_congr.trans (Module.nontrivial_dual_iff ℂ)

theorem dualWeights_spec : DualWeightsSpec.{u,v} := by
  intro g _ _ _ D X hX
  refine ⟨dual_internal D X hX, dual_support D X hX, fun μ => ?_⟩
  exact ⟨dualWeightEquiv D X hX μ, fun _ _ => rfl⟩

end DualWeights


section Exactness

private def cartanMap {X Y : ModuleCat.{v} (U g)} (f : X ⟶ Y) :
    letI := restrictedLieRingModule X (g := g)
    letI := restrictedLieModule X (g := g)
    letI := restrictedLieRingModule Y (g := g)
    letI := restrictedLieModule Y (g := g)
    X →ₗ⁅ℂ,D.cartan⁆ Y := by
  letI := restrictedLieRingModule X (g := g)
  letI := restrictedLieModule X (g := g)
  letI := restrictedLieRingModule Y (g := g)
  letI := restrictedLieModule Y (g := g)
  exact
    { f.hom.restrictScalars ℂ with
      map_lie' := fun {h x} => f.hom.map_smul (ι ℂ (h : g)) x }

private def onWeight {X Y : ModuleCat.{v} (U g)} (f : X ⟶ Y) (μ : D.Weight) :
    W D X μ →ₗ[ℂ] W D Y μ := by
  letI := restrictedLieRingModule X (g := g)
  letI := restrictedLieModule X (g := g)
  letI := restrictedLieRingModule Y (g := g)
  letI := restrictedLieModule Y (g := g)
  exact WeightExactness.weightMap (cartanMap D f) μ

private theorem dualMap_sumDual {X Y : ModuleCat.{v} (U g)} (f : X ⟶ Y)
    (hX : DirectSum.IsInternal (W D X)) (hY : DirectSum.IsInternal (W D Y)) :
    ((dualMap D f).hom.restrictScalars ℂ).comp (sumDual D Y hY) =
      (sumDual D X hX).comp (DirectSum.lmap (fun μ => (onWeight D f μ).dualMap)) := by
  apply LinearMap.ext
  intro a
  apply dual_ext_weights D X hX
  intro μ x
  change pair D X (dualMap D f (sumDual D Y hY a)) x =
    pair D X (sumDual D X hX (DirectSum.lmap (fun μ => (onWeight D f μ).dualMap) a)) x
  rw [pair_dualMap, pair_sumDual, DirectSum.lmap_apply, LinearMap.dualMap_apply]
  exact pair_sumDual D Y hY a μ (onWeight D f μ x)

private theorem exact_directSum {I : Type*} {A B C : I → Type*}
    [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)] [∀ i, AddCommGroup (C i)]
    [∀ i, Module ℂ (A i)] [∀ i, Module ℂ (B i)] [∀ i, Module ℂ (C i)]
    (f : ∀ i, A i →ₗ[ℂ] B i) (k : ∀ i, B i →ₗ[ℂ] C i)
    (h : ∀ i, Function.Exact (f i) (k i)) :
    Function.Exact (DirectSum.lmap f) (DirectSum.lmap k) := by
  intro y
  constructor
  · intro hy
    have hz (i : I) : k i (y i) = 0 := DFunLike.congr_fun hy i
    let a (i : I) := ((h i (y i)).mp (hz i)).choose
    have ha (i : I) : f i (a i) = y i := ((h i (y i)).mp (hz i)).choose_spec
    let x : ⨁ i, A i := DFinsupp.mk y.support (fun i => a i.val)
    refine ⟨x, DirectSum.ext (fun i => ?_)⟩
    change f i (x i) = y i
    by_cases hi : i ∈ y.support
    · rw [show x i = a i from DFinsupp.mk_of_mem hi, ha]
    · rw [show x i = 0 from DFinsupp.mk_of_notMem hi, map_zero,
        DFinsupp.notMem_support_iff.mp hi]
  · rintro ⟨x, rfl⟩
    apply DirectSum.ext
    intro i
    exact (h i).apply_apply_eq_zero (x i)

private theorem dual_shortExact {X Y Z : ModuleCat.{v} (U g)} (f : X ⟶ Y) (k : Y ⟶ Z)
    (hX : DirectSum.IsInternal (W D X)) (hY : DirectSum.IsInternal (W D Y))
    (hZ : DirectSum.IsInternal (W D Z))
    (hf : Function.Injective f) (he : Function.Exact f k) (hk : Function.Surjective k) :
    Function.Injective (dualMap D k) ∧ Function.Exact (dualMap D k) (dualMap D f) ∧
      Function.Surjective (dualMap D f) := by
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  let := restrictedLieRingModule Y (g := g)
  let := restrictedLieModule Y (g := g)
  let := restrictedLieRingModule Z (g := g)
  let := restrictedLieModule Z (g := g)
  have H (μ : D.Weight) := WeightExactness.shortExact (cartanMap D f) (cartanMap D k) hY hf he hk μ
  let df := DirectSum.lmap (fun μ => (onWeight D f μ).dualMap)
  let dk := DirectSum.lmap (fun μ => (onWeight D k μ).dualMap)
  have hdf : Function.Surjective df :=
    (DirectSum.lmap_surjective _).mpr fun μ => LinearMap.dualMap_surjective_of_injective (H μ).1
  have hdk : Function.Injective dk :=
    (DirectSum.lmap_injective _).mpr fun μ => LinearMap.dualMap_injective_of_surjective (H μ).2.2
  have hExact : Function.Exact dk df := by
    apply exact_directSum
    intro μ
    rw [LinearMap.exact_iff, LinearMap.ker_dualMap_eq_dualAnnihilator_range,
      LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    exact congrArg Submodule.dualAnnihilator (H μ).2.1.linearMap_ker_eq.symm
  have bx := sumDual_bijective D X hX
  have by' := sumDual_bijective D Y hY
  have bz := sumDual_bijective D Z hZ
  have cf := dualMap_sumDual D f hX hY
  have ck := dualMap_sumDual D k hY hZ
  refine ⟨?_, ?_, ?_⟩
  · intro x y h
    obtain ⟨a, rfl⟩ := bz.2 x
    obtain ⟨b, rfl⟩ := bz.2 y
    exact congrArg (sumDual D Z hZ) (hdk (by
      apply by'.1
      exact (LinearMap.congr_fun ck a).symm.trans (h.trans (LinearMap.congr_fun ck b))))
  · exact (LinearMap.exact_iff_of_surjective_of_bijective_of_injective dk df
      ((dualMap D k).hom.restrictScalars ℂ) ((dualMap D f).hom.restrictScalars ℂ)
      (sumDual D Z hZ) (sumDual D Y hY) (sumDual D X hX)
      ck cf bz.2 by' bx.1).mp hExact
  · intro x
    obtain ⟨a, rfl⟩ := bx.2 x
    obtain ⟨b, rfl⟩ := hdf a
    exact ⟨sumDual D Y hY b, LinearMap.congr_fun cf b⟩

end Exactness


section DoubleDual

variable (X : ModuleCat.{v} (U g))
variable (hX : DirectSum.IsInternal (W D X))

private def evaluationFull : X →ₗ[ℂ] twistedDual D (dualModule D X) :=
  (unbundle D (dualModule D X)).symm.toLinearMap.comp (inclusionDual D X).flip

include hX in
private theorem evaluation_mem (x : X) :
    evaluationFull D X x ∈ restrictedPart D (dualModule D X) := by
  let P := ((restrictedPart D (dualModule D X)).restrictScalars ℂ).comap (evaluationFull D X)
  suffices h : (⊤ : Submodule ℂ X) ≤ P from h Submodule.mem_top
  rw [← hX.submodule_iSup_eq_top]
  apply iSup_le
  intro μ x hx
  change evaluationFull D X x ∈ restrictedPart D (dualModule D X)
  apply Submodule.subset_span
  refine ⟨μ, ?_⟩
  rintro ν ⟨l, hl⟩
  by_contra h
  exact hl ((dual_weight_iff D X hX ν l).mp l.property μ (Ne.symm h) ⟨x, hx⟩)

set_option backward.isDefEq.respectTransparency false in
private def evaluation : X →ₗ[U g] dualModule D (dualModule D X) where
  toFun x := ⟨evaluationFull D X x, evaluation_mem D X hX x⟩
  map_add' x y := Subtype.ext ((evaluationFull D X).map_add x y)
  map_smul' a x := by
    apply Subtype.ext
    apply LinearMap.ext
    intro l
    change pair D X l (a • x) = pair D (dualModule D X)
      (a • (⟨evaluationFull D X x, evaluation_mem D X hX x⟩ : dualModule D (dualModule D X))) l
    rw [pair_smul]
    change pair D X l (a • x) = pair D X ((tau D a).unop • l) x
    rw [pair_smul, (tau_spec D).2.2.2]

private theorem pair_evaluation (x : X) (l : dualModule D X) :
    pair D (dualModule D X) (evaluation D X hX x) l = pair D X l x := rfl

private theorem bijective_of_weight_maps {Y Z : ModuleCat.{v} (U g)} (f : Y ⟶ Z)
    (hY : DirectSum.IsInternal (W D Y)) (hZ : DirectSum.IsInternal (W D Z))
    (h : ∀ μ, Function.Bijective (onWeight D f μ)) : Function.Bijective f := by
  have hc : (f.hom.restrictScalars ℂ).comp (DirectSum.coeLinearMap (W D Y)) =
      (DirectSum.coeLinearMap (W D Z)).comp (DirectSum.lmap (onWeight D f)) := by
    apply DirectSum.linearMap_ext
    intro μ
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, DirectSum.lmap_lof]
    rfl
  have hb : Function.Bijective (DirectSum.lmap (onWeight D f)) :=
    ⟨(DirectSum.lmap_injective _).mpr fun μ => (h μ).1,
      (DirectSum.lmap_surjective _).mpr fun μ => (h μ).2⟩
  have hcomp : Function.Bijective ((f.hom.restrictScalars ℂ).comp
      (DirectSum.coeLinearMap (W D Y))) := by
    rw [hc]
    exact hZ.comp hb
  exact (Function.Bijective.of_comp_iff f hY).mp hcomp

include hX in
private theorem evaluation_bijective (hfin : ∀ μ, FiniteDimensional ℂ (W D X μ)) :
    Function.Bijective (evaluation D X hX) := by
  let Y := dualModule D X
  let hY : DirectSum.IsInternal (W D Y) := dual_internal D X hX
  apply bijective_of_weight_maps D (ModuleCat.ofHom (evaluation D X hX)) hX (dual_internal D Y hY)
  intro μ
  let := hfin μ
  let e := dualWeightEquiv D Y hY μ
  let q := (Module.evalEquiv ℂ (W D X μ)).trans (dualWeightEquiv D X hX μ).dualMap
  have hh : onWeight D (ModuleCat.ofHom (evaluation D X hX)) μ = (q.trans e.symm).toLinearMap := by
    ext x : 1
    apply e.injective
    change e (onWeight D (ModuleCat.ofHom (evaluation D X hX)) μ x) = e (e.symm (q x))
    rw [LinearEquiv.apply_symm_apply]
    ext l
    exact pair_evaluation D X hX x l
  rw [hh]
  exact (q.trans e.symm).bijective

end DoubleDual


section FiniteLength

open private cartanSubmodule from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.SimpleObjects
open private finiteLength_of_exact from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.FiniteLength
open private local_finite_of_bounds from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.WeightBounds

private def FiniteWeightModule (D : Setup g) (X : ModuleCat.{v} (U g)) : Prop :=
  DirectSum.IsInternal (W D X) ∧ ∀ μ, FiniteDimensional ℂ (W D X μ)

private theorem dual_finite_weights (X : ModuleCat.{v} (U g)) (hX : FiniteWeightModule D X) :
    FiniteWeightModule D (dualModule D X) := by
  refine ⟨dual_internal D X hX.1, fun μ => ?_⟩
  let := hX.2 μ
  exact FiniteDimensional.of_injective _ (dualWeightEquiv D X hX.1 μ).injective

private abbrev submoduleObject {X : ModuleCat.{v} (U g)} (S : Submodule (U g) X) :=
  ModuleCat.of (U g) S

private abbrev quotientObject {X : ModuleCat.{v} (U g)} (S : Submodule (U g) X) :=
  ModuleCat.of (U g) (X ⧸ S)

private abbrev submoduleInclusion {X : ModuleCat.{v} (U g)} (S : Submodule (U g) X) :
    submoduleObject S ⟶ X :=
  ModuleCat.ofHom S.subtype

private abbrev submoduleQuotient {X : ModuleCat.{v} (U g)} (S : Submodule (U g) X) :
    X ⟶ quotientObject S :=
  ModuleCat.ofHom S.mkQ

private theorem submodule_finite_weights (X : ModuleCat.{v} (U g)) (hX : FiniteWeightModule D X)
    (S : Submodule (U g) X) : FiniteWeightModule D (submoduleObject S) := by
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  refine ⟨(WeightExactness.stableSubspace (cartanSubmodule D X S) hX.1).1, fun μ => ?_⟩
  let := hX.2 μ
  apply FiniteDimensional.of_injective (onWeight D (submoduleInclusion S) μ)
  intro a b hab
  exact Subtype.ext (Subtype.ext (congrArg (fun w : W D X μ => (w : X)) hab))

private theorem quotient_finite_weights (X : ModuleCat.{v} (U g)) (hX : FiniteWeightModule D X)
    (S : Submodule (U g) X) : FiniteWeightModule D (quotientObject S) := by
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  let := restrictedLieRingModule (quotientObject S) (g := g)
  let := restrictedLieModule (quotientObject S) (g := g)
  refine ⟨(WeightExactness.quotient (cartanSubmodule D X S) hX.1).1, fun μ => ?_⟩
  let := hX.2 μ
  exact FiniteDimensional.of_surjective (onWeight D (submoduleQuotient S) μ)
    (WeightExactness.weightMap_surjective (cartanMap D (submoduleQuotient S)) hX.1 S.mkQ_surjective μ)

private theorem submodule_dual_exact (X : ModuleCat.{v} (U g)) (hX : FiniteWeightModule D X)
    (S : Submodule (U g) X) :
    Function.Injective (dualMap D (submoduleQuotient S)) ∧
    Function.Exact (dualMap D (submoduleQuotient S)) (dualMap D (submoduleInclusion S)) ∧
    Function.Surjective (dualMap D (submoduleInclusion S)) :=
  dual_shortExact D (submoduleInclusion S) (submoduleQuotient S)
    (submodule_finite_weights D X hX S).1 hX.1 (quotient_finite_weights D X hX S).1
    S.subtype_injective (LinearMap.exact_iff.mpr (by simp)) S.mkQ_surjective

private theorem subsingleton_dual (X : ModuleCat.{v} (U g)) [Subsingleton X] :
    Subsingleton (dualModule D X) := by
  let := (Module.subsingleton_dual_iff ℂ (V := X)).2 (inferInstanceAs (Subsingleton X))
  exact Function.Injective.subsingleton (f := inclusionDual D X) (fun _ _ h => Subtype.ext h)

private theorem subsingleton_of_dual (X : ModuleCat.{v} (U g)) (hX : FiniteWeightModule D X)
    [Subsingleton (dualModule D X)] : Subsingleton X := by
  let := subsingleton_dual D (dualModule D X)
  exact Function.Injective.subsingleton (evaluation_bijective D X hX.1 hX.2).1

private theorem dual_simple_module (X : ModuleCat.{v} (U g)) (hX : FiniteWeightModule D X)
    [IsSimpleModule (U g) X] : IsSimpleModule (U g) (dualModule D X) := by
  have hY := dual_finite_weights D X hX
  let e := LinearEquiv.ofBijective (evaluation D X hX.1) (evaluation_bijective D X hX.1 hX.2)
  have : IsSimpleModule (U g) (dualModule D (dualModule D X)) := IsSimpleModule.congr e.symm
  rw [isSimpleModule_iff]
  have : Nontrivial (dualModule D X) := by
    by_contra hn
    let := not_nontrivial_iff_subsingleton.mp hn
    let := subsingleton_of_dual D X hX
    exact (not_nontrivial_iff_subsingleton.mpr this) (IsSimpleModule.nontrivial (U g) X)
  constructor
  intro S
  by_cases hs : S = ⊥
  · exact Or.inl hs
  right
  let SX := submoduleObject S
  let QX := quotientObject S
  have hS := submodule_finite_weights D (dualModule D X) hY S
  have hQ := quotient_finite_weights D (dualModule D X) hY S
  have hd := submodule_dual_exact D (dualModule D X) hY S
  let p := (dualMap D (submoduleInclusion S)).hom
  have hp : p ≠ 0 := by
    intro hp
    have hsurj : Function.Surjective p := hd.2.2
    rw [hp] at hsurj
    have : Subsingleton (dualModule D SX) := ⟨fun a b => by
      obtain ⟨x, rfl⟩ := hsurj a
      obtain ⟨y, rfl⟩ := hsurj b
      rfl⟩
    let := subsingleton_of_dual D SX hS
    exact hs (Submodule.eq_bot_of_subsingleton (p := S))
  have hpinj := LinearMap.injective_of_ne_zero hp
  have : Subsingleton (dualModule D QX) := ⟨fun a b =>
    hd.1 (hpinj ((hd.2.1.apply_apply_eq_zero a).trans (hd.2.1.apply_apply_eq_zero b).symm))⟩
  let := subsingleton_of_dual D QX hQ
  exact Submodule.Quotient.subsingleton_iff.mp this

private theorem dual_length_of_finiteLength {V : Type v} [AddCommGroup V] [Module (U g) V]
    (h : IsFiniteLength (U g) V) :
    FiniteWeightModule D (ModuleCat.of (U g) V) →
    IsFiniteLength (U g) (dualModule D (ModuleCat.of (U g) V)) := by
  induction h with
  | @of_subsingleton M _ _ _ =>
    intro _
    let := subsingleton_dual D (ModuleCat.of (U g) M)
    exact .of_subsingleton
  | @of_simple_quotient M _ _ S _ _ ih =>
    intro hX
    let X := ModuleCat.of (U g) M
    have hS := submodule_finite_weights D X hX S
    have hQ := quotient_finite_weights D X hX S
    let N := dualModule D (quotientObject (X := X) S)
    let B : Submodule (U g) N := ⊥
    have hN : IsSimpleModule (U g) N := dual_simple_module D (quotientObject (X := X) S) hQ
    have hB : IsSimpleModule (U g) (N ⧸ B) :=
      IsSimpleModule.congr (Submodule.quotEquivOfEqBot B rfl)
    have hlen : IsFiniteLength (U g) N :=
      IsFiniteLength.of_simple_quotient (N := B) IsFiniteLength.of_subsingleton
    let f := dualMap D (submoduleQuotient (X := X) S)
    let k := dualMap D (submoduleInclusion (X := X) S)
    exact finiteLength_of_exact f.hom k.hom (submodule_dual_exact D X hX S).2.1 hlen (ih hS)

private theorem finite_weights_of_O (X : O.{u,v} D) : FiniteWeightModule D X.obj :=
  ⟨X.property.2.1, (weightBounds D X.obj X.property).1⟩

theorem dual_finiteLength : DualLengthSpec.{u,v} := by
  intro g _ _ _ D X
  exact dual_length_of_finiteLength D (categoryO_finiteLength D X) (finite_weights_of_O D X)

theorem dual_mem_O : ∀ D : Setup g, PreservesO.{u,v} D := by
  intro D X
  let := (isFiniteLength_iff_isNoetherian_isArtinian.mp (dual_finiteLength D X)).1
  have h := dual_finite_weights D X.obj (finite_weights_of_O D X)
  refine ⟨inferInstance, h.1, local_finite_of_bounds D _ h.1 ⟨h.2, ?_⟩⟩
  rw [dual_support D X.obj X.property.2.1]
  exact (weightBounds D X.obj X.property).2

end FiniteLength


/-- The contravariant restricted dual functor on finite category O. -/
def dualFunctor (D : Setup g) : (O.{u,v} D)ᵒᵖ ⥤ O.{u,v} D :=
  categoryDualFunctor D (dual_mem_O D)

set_option backward.isDefEq.respectTransparency false in
theorem category_duality : CategoryDualitySpec.{u,v} := by
  intro g _ _ _ D
  refine ⟨dual_mem_O D, ?_, ?_⟩
  · let F : (O.{u,v} D)ᵒᵖ ⥤ O.{u,v} D := dualFunctor D
    let component (X : O.{u,v} D) : X ≅ (F.rightOp ⋙ F).obj X :=
      (objects D).fullyFaithfulι.preimageIso
        (LinearEquiv.ofBijective (evaluation D X.obj X.property.2.1)
          (evaluation_bijective D X.obj X.property.2.1 (finite_weights_of_O D X).2)).toModuleIso
    let E : 𝟭 (O.{u,v} D) ≅ F.rightOp ⋙ F := NatIso.ofComponents component (by
      intro X Y f
      apply ObjectProperty.hom_ext
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      apply LinearMap.ext
      intro l
      change pair D (dualModule D Y.obj) (evaluation D Y.obj Y.property.2.1 (f.hom x)) l =
        pair D (dualModule D Y.obj)
          (dualMap D (dualMap D f.hom) (evaluation D X.obj X.property.2.1 x)) l
      rw [pair_evaluation, pair_dualMap, pair_evaluation, pair_dualMap])
    exact ⟨E, fun _ _ _ => rfl⟩
  · intro X Y Z f k hf he hk
    exact dual_shortExact D f.hom k.hom X.property.2.1 Y.property.2.1 Z.property.2.1 hf he hk

section SimpleLabels

open Specs.RepTheorySurvey.CategoryO.WeightBounds (support)

private theorem cone_zero_or_positive (a : D.Weight) (ha : a ∈ QPlus D) :
    a = 0 ∨ 0 < D.direction a := by
  change a ∈ Submodule.span ℕ (Set.range D.alpha) at ha
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    exact Or.inr i.property.1.2
  | zero => exact Or.inl rfl
  | add a b _ _ ha hb =>
    rcases ha with rfl | ha
    · simpa using hb
    · rcases hb with rfl | hb
      · exact Or.inr (by simpa using ha)
      · exact Or.inr (by rw [map_add]; exact add_pos ha hb)
  | smul n a _ ha =>
    by_cases h : n = 0
    · exact Or.inl (by simp [h])
    · rcases ha with rfl | ha
      · exact Or.inl (smul_zero n)
      · exact Or.inr (by rw [map_nsmul]; exact nsmul_pos ha h)

private theorem weight_antisymm {a b : D.Weight} (h₁ : weightLE D a b) (h₂ : weightLE D b a) :
    a = b := by
  rcases cone_zero_or_positive D (b - a) h₁ with h | h
  · exact (sub_eq_zero.mp h).symm
  rcases cone_zero_or_positive D (a - b) h₂ with h' | h'
  · exact sub_eq_zero.mp h'
  rw [map_sub] at h h'
  linarith

private theorem support_of_surjection {X Y : ModuleCat.{v} (U g)} (f : X ⟶ Y)
    (hX : DirectSum.IsInternal (W D X)) (hf : Function.Surjective f) :
    support D Y ⊆ support D X := by
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  let := restrictedLieRingModule Y (g := g)
  let := restrictedLieModule Y (g := g)
  intro μ hY hzero
  apply hY
  have hs : Function.Surjective (onWeight D f μ) :=
    WeightExactness.weightMap_surjective (cartanMap D f) hX hf μ
  let := (Submodule.subsingleton_iff_eq_bot (p := W D X μ)).mpr hzero
  exact (Submodule.subsingleton_iff_eq_bot (p := W D Y μ)).mp hs.subsingleton

private theorem simple_support_le (lam μ : D.Weight) (h : μ ∈ support D (L D lam)) :
    weightLE D μ lam :=
  ((verma_mem_O D lam).2.2.2.2.1 μ).mp
    (support_of_surjection D (ModuleCat.ofHom (quotientMap D lam)) (verma_mem_O D lam).1.2.1
      (quotientMap_surjective D lam) h)

private theorem simple_label_mem_support (lam : D.Weight) :
    lam ∈ support D (L D lam) := by
  obtain ⟨_, _, h⟩ := simpleQuotient_in_O D lam
  exact (W D (L D lam) lam).ne_bot_iff.mpr ⟨_, h.2.1, h.1⟩

theorem dual_simple : DualSimpleLabelsSpec.{u} := by
  intro g _ _ _ D lam
  obtain ⟨hL, _, _⟩ := simpleQuotient_in_O D lam
  let Y : O.{u,u} D := ⟨dualModule D (L D lam), dual_mem_O D ⟨L D lam, hL⟩⟩
  have := simpleQuotient_simple D lam
  have hYs : Simple Y :=
    (simple_iff_isSimpleModule D Y).mpr
      (dual_simple_module D (L D lam) (finite_weights_of_O D ⟨L D lam, hL⟩))
  obtain ⟨ν, ⟨e⟩, _⟩ := (simpleClassification D Y).mp hYs
  obtain ⟨hLν, _, _⟩ := simpleQuotient_in_O D ν
  let J := L D ν
  let e' : Y.obj ≃ₗ[U g] J := e
  let f : Y.obj ⟶ J := ModuleCat.ofHom (X := Y.obj) (Y := J) e'.toLinearMap
  let k : J ⟶ Y.obj := ModuleCat.ofHom (X := J) (Y := Y.obj) e'.symm.toLinearMap
  have hEq : support D (L D ν) = support D (L D lam) := by
    rw [← dual_support D (L D lam) hL.2.1]
    exact Set.Subset.antisymm
      (support_of_surjection D f Y.property.2.1 e'.surjective)
      (support_of_surjection D k hLν.2.1 e'.symm.surjective)
  have hν : ν = lam := weight_antisymm D
    (simple_support_le D lam ν (hEq ▸ simple_label_mem_support D ν))
    (simple_support_le D ν lam (hEq.symm ▸ simple_label_mem_support D lam))
  subst ν
  exact ⟨e⟩

theorem costandard_mem_O : CostandardInOSpec.{u} := by
  intro g _ _ _ D lam
  exact dual_mem_O D ⟨M D lam, (verma_mem_O D lam).1⟩

end SimpleLabels

end RepTheorySurvey.CategoryO.RestrictedDual
