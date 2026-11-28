import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Affine.VermaWeightSpaces
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.BorelInduction
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.AffineSimpleTriples
import Mathlib.Data.List.OfFn
import Batteries.Tactic.OpenPrivate

/-! The affine Verma module and its highest-weight structure. -/

noncomputable section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace RepTheorySurvey.Affine

open _root_.Specs.RepTheorySurvey.Affine.VermaWeightSpaces

universe u v

/-- The model used in the independent Specs is furnished by the affine
bracket and the triangular summands already constructed upstream. -/
theorem affineVermaModel : affineVermaModel_type.{u} := by
  intro G _ _ _ _ B H _ φ
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, (sidesClosed B H φ).1, (sidesClosed B H φ).2⟩
  · intro x y z
    simpa only [← affineBracket_eq] using (add_lie x y z)
  · intro x y z
    simpa only [← affineBracket_eq] using (lie_add x y z)
  · intro x
    simpa only [← affineBracket_eq] using (lie_self x)
  · intro x y z
    simpa only [← affineBracket_eq] using (leibniz_lie x y z)
  · intro c x y
    simpa only [← affineBracket_eq] using (lie_smul c x y)
  · intro x y hx hy
    rw [← affineBracket_eq, cartanAbelianBracket B H ⟨x, hx⟩ ⟨y, hy⟩]
    exact Submodule.zero_mem _

abbrev affineBorel := @affineBorel_value
abbrev affineWeightCharacter := @affineWeightCharacter_value
abbrev affineVermaAt := @affineVermaAt_value
abbrev affineVerma := @affineVerma_value
abbrev affineVermaTop := @affineVermaTop_value
abbrev affineVermaWeightSpace := @affineVermaWeightSpace_value

open _root_.Specs.RepTheorySurvey.Affine.LoopAlgebra (affineBracket_value)
open _root_.Specs.RepTheorySurvey.Affine.TriangularRootSpaces
open _root_.RepTheorySurvey.CategoryO.BorelInduction
open _root_.Specs.LieAlgebrasAndRepresentations.VermaModules (Direction Regular positive_value)
open UniversalEnvelopingAlgebra (ι)
open scoped TensorProduct

open private lie_cartan_coordinates from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Affine.TriangularRootSpaces
open private rootSum positive_submodule from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules

/-- The identity on affine coordinates identifies the model with the upstream Lie algebra. -/
def affineVermaModelEquiv {G : Type u} [LieRing G] [LieAlgebra ℂ G]
    {B : InvariantForm G} {H : LieSubalgebra ℂ G} {φ : Direction H} (D : Model B H φ) :
    Carrier D ≃ₗ⁅ℂ⁆ AffineAlgebra B :=
  { (LinearEquiv.refl ℂ (AffineAlgebra B)) with map_lie' := fun {_ _} => rfl }

section Borel

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]
  {B : InvariantForm G} {H : LieSubalgebra ℂ G} {φ : Direction H}

private theorem cartan_bracket_rootSum (s : Set ℝ) (h : H) {x : G}
    (hx : x ∈ rootSum H φ s) : ⁅(h : G), x⁆ ∈ rootSum H φ s := by
  refine Submodule.iSup_induction _ (motive := fun x => ⁅(h : G), x⁆ ∈ rootSum H φ s)
    hx ?_ (by simp) (fun a b ha hb => by simpa only [lie_add] using Submodule.add_mem _ ha hb)
  intro α x hx
  rw [(LieAlgebrasAndRepresentations.mem_rootSpace H α.val x).mp hx h]
  exact Submodule.smul_mem _ _ (Submodule.mem_iSup_of_mem α hx)

private theorem cartan_bracket_side (S : LieSubalgebra ℂ G) (sign : ℤ)
    (hS : ∀ (h : H) (x : G), x ∈ S → ⁅(h : G), x⁆ ∈ S)
    (h : affineCartan B H) {x : AffineAlgebra B}
    (hx : x ∈ components B (sideDegrees S sign) ⊥ ⊥) :
    ⁅(h : AffineAlgebra B), x⁆ ∈ components B (sideDegrees S sign) ⊥ ⊥ := by
  have hc := lie_cartan_coordinates B H h x
  change (∀ m, (coordinates B ⁅(h : AffineAlgebra B), x⁆).1.1 m ∈ sideDegrees S sign m) ∧
    _ ∧ _
  refine ⟨fun m => ?_, by simp [hc.2.1], by simp [hc.2.2]⟩
  rw [hc.1 m]
  apply Submodule.add_mem _ _ (Submodule.smul_mem _ _ (hx.1 m))
  have hm := hx.1 m
  by_cases hz : m = 0
  · subst m
    simp only [sideDegrees, ite_true] at hm ⊢
    exact hS _ _ hm
  · simp only [sideDegrees, ite_eq_right hz] at hm ⊢
    split_ifs with hm'
    · trivial
    · rw [ite_eq_right hm', Submodule.mem_bot] at hm
      rw [Submodule.mem_bot]
      rw [hm, lie_zero]

private theorem cartan_bracket_positive (D : Model B H φ)
    (h : cartan D) {x : Carrier D} (hx : x ∈ positive D) : ⁅(h : Carrier D), x⁆ ∈ positive D := by
  change ⁅(h.1 : AffineAlgebra B), x⁆ ∈ components B (sideDegrees (positive_value H φ) 1) ⊥ ⊥
  refine cartan_bracket_side _ _ (fun a b hb => ?_) ⟨h.1, h.2⟩ hx
  change b ∈ (positive_value H φ).toSubmodule at hb
  change _ ∈ (positive_value H φ).toSubmodule
  rw [positive_submodule H φ] at hb ⊢
  exact cartan_bracket_rootSum (Set.Ioi 0) a hb

variable [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra]

private theorem cartan_bracket_cartan (D : Model B H φ) (h k : cartan D) :
    ⁅(h : Carrier D), (k : Carrier D)⁆ = 0 :=
  cartanAbelianBracket B H ⟨h.1, h.2⟩ ⟨k.1, k.2⟩

private theorem split_borel_bracket (D : Model B H φ)
    (a b : cartan D) (x y : positive D) :
    ⁅(a : Carrier D) + x, (b : Carrier D) + y⁆ ∈ positive D := by
  rw [add_lie, lie_add, lie_add, cartan_bracket_cartan, zero_add]
  have hy : ⁅(a : Carrier D), (y : Carrier D)⁆ ∈ positive D := cartan_bracket_positive D a y.2
  have hx : ⁅(x : Carrier D), (b : Carrier D)⁆ ∈ positive D := by
    rw [← lie_skew]
    exact (positive D).neg_mem (cartan_bracket_positive D b x.2)
  have hxy : ⁅(x : Carrier D), (y : Carrier D)⁆ ∈ positive D := (positive D).lie_mem x.2 y.2
  exact (positive D).add_mem hy ((positive D).add_mem hx hxy)

theorem affineBorelUnderlying : affineBorelUnderlying_type.{u} := by
  intro G _ _ _ _ B H _ φ D _
  let S : LieSubalgebra ℂ (Carrier D) :=
    { (cartan D).toSubmodule ⊔ (positive D).toSubmodule with
      lie_mem' := by
        intro x y hx hy
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
        obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hy
        exact (show (positive D).toSubmodule ≤ _ ⊔ _ from le_sup_right)
          (split_borel_bracket D ⟨a, ha⟩ ⟨c, hc⟩ ⟨b, hb⟩ ⟨d, hd⟩) }
  change (cartan D ⊔ positive D).toSubmodule = S.toSubmodule
  rw [LieSubalgebra.toSubmodule_inj]
  apply le_antisymm
  · apply sup_le
    · exact (show (cartan D).toSubmodule ≤ _ ⊔ _ from le_sup_left)
    · exact (show (positive D).toSubmodule ≤ _ ⊔ _ from le_sup_right)
  · change (cartan D).toSubmodule ⊔ (positive D).toSubmodule ≤ (cartan D ⊔ positive D).toSubmodule
    exact sup_le
      ((LieSubalgebra.toSubmodule_le_toSubmodule _ _).mpr le_sup_left)
      ((LieSubalgebra.toSubmodule_le_toSubmodule _ _).mpr le_sup_right)

private theorem negative_borel_compl (D : Model B H φ) (hφ : Regular H φ) :
    IsCompl (negative D).toSubmodule (affineBorel D).toSubmodule := by
  rw [affineBorelUnderlying B H φ D hφ]
  exact (triangularDecomposition B H φ hφ).1

private abbrev cartanBorel (D : Model B H φ) : cartan D →ₗ⁅ℂ⁆ affineBorel D :=
  LieSubalgebra.inclusion le_sup_left

private abbrev positiveBorel (D : Model B H φ) : positive D →ₗ⁅ℂ⁆ affineBorel D :=
  LieSubalgebra.inclusion le_sup_right

private theorem borel_decompose (D : Model B H φ) (hφ : Regular H φ) (z : affineBorel D) :
    ∃ x : cartan D, ∃ y : positive D, cartanBorel D x + positiveBorel D y = z := by
  have hz := z.property
  change z.val ∈ (affineBorel D).toSubmodule at hz
  rw [affineBorelUnderlying B H φ D hφ] at hz
  change (z.val : AffineAlgebra B) ∈ affineCartan B H ⊔ affinePositive B H φ at hz
  obtain ⟨x, hx, y, hy, he⟩ := (Submodule.mem_sup (R := ℂ) (M := AffineAlgebra B)).mp hz
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext he⟩

private def borelEquiv (D : Model B H φ) (hφ : Regular H φ) :
    (cartan D × positive D) ≃ₗ[ℂ] affineBorel D := by
  let f := (cartanBorel D).toLinearMap.coprod (positiveBorel D).toLinearMap
  refine LinearEquiv.ofBijective f ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨x, y⟩ hxy
    have h : (x.1 : AffineAlgebra B) + y.1 = 0 :=
      congrArg Subtype.val hxy
    have hd := (triangularDecomposition B H φ hφ).2
    have hx : (x.1 : AffineAlgebra B) = 0 := Submodule.disjoint_def.mp hd _ x.2
      ((eq_neg_of_add_eq_zero_left h).symm ▸ Submodule.neg_mem _ y.2)
    refine Prod.ext (Subtype.ext hx) (Subtype.ext ?_)
    change (y.1 : AffineAlgebra B) = 0
    simpa only [hx, zero_add] using h
  · intro z
    obtain ⟨x, y, hxy⟩ := borel_decompose D hφ z
    exact ⟨(x, y), hxy⟩

attribute [local instance 100] LieRing.ofAssociativeRing

set_option maxHeartbeats 400000 in
theorem affineVermaCharacter : affineVermaCharacter_type.{u} := by
  intro G _ _ _ _ B H _ φ D _ hφ Λ
  let F : (cartan D × positive D) ≃ₗ[ℂ] affineBorel D := borelEquiv D hφ
  let L : cartan D →ₗ[ℂ] ℂ := {
    toFun := fun x => Λ ⟨x.1, x.2⟩
    map_add' := fun x y => Λ.map_add ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
    map_smul' := fun c x => Λ.map_smul c ⟨x.1, x.2⟩ }
  let p : affineBorel D →ₗ[ℂ] ℂ :=
    (L.comp (LinearMap.fst ℂ (cartan D) (positive D))).comp F.symm.toLinearMap
  have hleft (x : cartan D) : p (cartanBorel D x) = Λ ⟨x.1, x.2⟩ := by
    have he : F (x, 0) = cartanBorel D x := by change _ + positiveBorel D 0 = _; simp
    rw [← he]
    change L (F.symm (F (x, 0))).1 = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hright (y : positive D) : p (positiveBorel D y) = 0 := by
    have he : F (0, y) = positiveBorel D y := by change cartanBorel D 0 + _ = _; simp
    rw [← he]
    change L (F.symm (F (0, y))).1 = _
    rw [LinearEquiv.symm_apply_apply]
    exact map_zero L
  let f : affineBorel D →ₗ⁅ℂ⁆ ℂ := by
    refine { toLinearMap := p, map_lie' := ?_ }
    intro a b
    obtain ⟨x, y, rfl⟩ := borel_decompose D hφ a
    obtain ⟨z, w, rfl⟩ := borel_decompose D hφ b
    let c : positive D := ⟨_, split_borel_bracket D x z y w⟩
    let ax : affineBorel D := cartanBorel D x + positiveBorel D y
    let bx : affineBorel D := cartanBorel D z + positiveBorel D w
    change p (positiveBorel D c) = p ax * p bx - p bx * p ax
    rw [hright, mul_comm (p bx) (p ax), sub_self]
  refine ⟨UniversalEnvelopingAlgebra.lift ℂ f, ⟨?_, ?_⟩, ?_⟩
  · intro x
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    exact hleft x
  · intro x
    rw [UniversalEnvelopingAlgebra.lift_ι_apply]
    exact hright x
  · intro χ hχ
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro z
    obtain ⟨x, y, rfl⟩ := borel_decompose D hφ z
    change χ (ι ℂ (cartanBorel D x + positiveBorel D y)) =
      UniversalEnvelopingAlgebra.lift ℂ f (ι ℂ (cartanBorel D x + positiveBorel D y))
    rw [UniversalEnvelopingAlgebra.lift_ι_apply, map_add (ι ℂ), map_add χ, map_add f]
    change χ (ι ℂ (cartanBorel D x)) + χ (ι ℂ (positiveBorel D y)) =
      p (cartanBorel D x) + p (positiveBorel D y)
    rw [hleft, hright, hχ.1 x, hχ.2 y]

private theorem characterScalarTower (D : Model B H φ) (χ : U (affineBorel D) →ₐ[ℂ] ℂ) :
    letI := characterModule D χ
    IsScalarTower ℂ (U (affineBorel D)) ℂ :=
  by
    letI := characterModule D χ
    refine ⟨fun z a c => ?_⟩
    change χ (algebraMap ℂ (U (affineBorel D)) z * a) * c = z * (χ a * c)
    rw [map_mul, χ.commutes, Algebra.algebraMap_self_apply, mul_assoc]

theorem affineVermaPBW : affineVermaPBW_type.{u} := by
  intro G _ _ _ _ B H _ φ D _ hφ Λ χ _
  letI := characterModule D χ
  letI := characterScalarTower D χ
  let F := inducedPBWEquiv (negative D) (affineBorel D) (E := ℂ) (negative_borel_compl D hφ)
  refine ⟨(TensorProduct.rid ℂ (U (negative D))).symm.trans F, fun a => ?_⟩
  change F ((TensorProduct.rid ℂ (U (negative D))).symm a) = _
  rw [show (TensorProduct.rid ℂ (U (negative D))).symm a = a ⊗ₜ[ℂ] 1 from rfl,
    inducedPBWEquiv_tensor]
  symm
  change inclusion (negative D) a • induceTensor (inclusion (affineBorel D)) 1 (1 : ℂ) = _
  rw [smul_tensor, mul_one]

private theorem act_top (D : Model B H φ) (χ : U (affineBorel D) →ₐ[ℂ] ℂ)
    (a : U (affineBorel D)) :
    inclusion (affineBorel D) a • affineVermaTop D χ = χ a • affineVermaTop D χ := by
  letI := characterModule D χ
  let i := inclusion (affineBorel D)
  change i a • induceTensor i 1 (1 : ℂ) = _
  rw [smul_tensor, mul_one, ← one_mul (i a), balance_tensor]
  let q := (balance i ℂ).mkQ.restrictScalars ℂ
  change q ((1 : U (Carrier D)) ⊗ₜ[ℂ] (χ a * 1)) =
    χ a • q ((1 : U (Carrier D)) ⊗ₜ[ℂ] (1 : ℂ))
  rw [← map_smul]
  exact congrArg q (TensorProduct.tmul_smul (χ a) _ (1 : ℂ))

private theorem top_is_highest (D : Model B H φ) (Λ : Weight B H)
    (χ : U (affineBorel D) →ₐ[ℂ] ℂ) (hχ : IsWeightCharacter D Λ χ) :
    IsHighestVector D Λ (affineVermaTop D χ) := by
  constructor
  · intro x
    change ι ℂ ((cartanBorel D x : affineBorel D) : Carrier D) • affineVermaTop D χ = _
    simpa only [inclusion_ι, hχ.1 x] using act_top D χ (ι ℂ (cartanBorel D x))
  · intro x
    change ι ℂ ((positiveBorel D x : affineBorel D) : Carrier D) • affineVermaTop D χ = _
    simpa only [inclusion_ι, hχ.2 x, zero_smul] using act_top D χ (ι ℂ (positiveBorel D x))

theorem affineVermaUniversal : affineVermaUniversal_type.{u, v} := by
  intro G _ _ _ _ B H _ φ D _ hφ Λ χ hχ
  refine ⟨top_is_highest D Λ χ hχ, ?_⟩
  intro V _ _
  let A := U (Carrier D)
  let C := U (affineBorel D)
  let i := inclusion (affineBorel D)
  letI : Module ℂ V := scalarModule (B := A) V
  letI : IsScalarTower ℂ A V := IsScalarTower.of_algebraMap_smul (A := A) fun _ _ => rfl
  letI := restrictModule i V
  letI : IsScalarTower ℂ C V := IsScalarTower.of_algebraMap_smul (A := C) fun c v => by
    change i (algebraMap ℂ C c) • v = algebraMap ℂ A c • v
    rw [i.commutes]
  letI := characterModule D χ
  letI := characterScalarTower D χ
  intro w hw
  have hgen (x : affineBorel D) : (ι ℂ x : C) • w = χ (ι ℂ x) • w := by
    obtain ⟨a, b, rfl⟩ := borel_decompose D hφ x
    have ha : (ι ℂ (cartanBorel D a) : C) • w = Λ ⟨a.1, a.2⟩ • w := by
      change i (ι ℂ (cartanBorel D a)) • w = _
      rw [inclusion_ι]
      exact hw.1 a
    have hb : (ι ℂ (positiveBorel D b) : C) • w = 0 := by
      change i (ι ℂ (positiveBorel D b)) • w = 0
      rw [inclusion_ι]
      exact hw.2 b
    simp only [map_add, add_smul, ha, hb, add_zero, hχ.1 a, hχ.2 b]
  have hact (b : C) : b • w = χ b • w := by
    induction b using Shared.Lie.enveloping_induction ℂ (affineBorel D) with
    | scalar c => rw [algebraMap_smul, χ.commutes, Algebra.algebraMap_self_apply]
    | generator x => exact hgen x
    | mul a b ha hb =>
      rw [mul_smul, hb, smul_comm a (χ b), ha, smul_smul, map_mul, mul_comm]
    | add a b ha hb => rw [add_smul, ha, hb, map_add, add_smul]
  let f : ℂ →ₗ[C] V :=
    { toFun := fun c => c • w
      map_add' := fun a b => add_smul a b w
      map_smul' := fun b c => by
        change (χ b * c) • w = b • (c • w)
        rw [smul_comm b c, hact, smul_smul, mul_comm] }
  refine ⟨(homEquiv i).symm f, ?_, ?_⟩
  · change extend i f (induceTensor i 1 (1 : ℂ)) = w
    rw [extend_tensor, one_smul]
    exact one_smul ℂ w
  · intro g hg
    apply (homEquiv i).injective
    rw [Equiv.apply_symm_apply]
    apply LinearMap.ext
    intro c
    change g (induceTensor i 1 c) = c • w
    have ht : induceTensor i 1 c = i (algebraMap ℂ C c) • affineVermaTop D χ := by
      rw [act_top, χ.commutes, Algebra.algebraMap_self_apply]
      let q := (balance i ℂ).mkQ.restrictScalars ℂ
      change q ((1 : A) ⊗ₜ[ℂ] c) = c • q ((1 : A) ⊗ₜ[ℂ] (1 : ℂ))
      rw [← map_smul, ← TensorProduct.tmul_smul, smul_eq_mul, mul_one]
    rw [ht, map_smul, hg]
    change i (algebraMap ℂ C c) • w = c • w
    rw [i.commutes]
    rfl

end Borel

section WeightLinearAlgebra

open scoped Classical DirectSum

variable {I J M : Type*} [AddCommGroup M] [Module ℂ M]

private def fiberSpan (x : I → M) (weight : I → J) (μ : J) : Submodule ℂ M :=
  Submodule.span ℂ (Set.range fun i : {i // weight i = μ} => x i.1)

private theorem weight_eq_fiberSpan (W : J → Submodule ℂ M) (hW : iSupIndep W)
    (x : I → M) (weight : I → J) (hx : ∀ i, x i ∈ W (weight i))
    (hspan : Submodule.span ℂ (Set.range x) = ⊤) (μ : J) :
    W μ = fiberSpan x weight μ := by
  have hsub (ν : J) : fiberSpan x weight ν ≤ W ν := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, hi⟩, rfl⟩
    exact hi ▸ hx i
  apply le_antisymm _ (hsub μ)
  let B := ⨆ ν, ⨆ (_ : ν ≠ μ), W ν
  have htop : fiberSpan x weight μ ⊔ B = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : weight i = μ
    · exact (show fiberSpan x weight μ ≤ _ ⊔ _ from le_sup_left)
        (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    · exact (show B ≤ _ ⊔ _ from le_sup_right)
        ((le_iSup₂ (f := fun ν _ => W ν) (weight i) hi) (hx i))
  intro z hz
  have hz' : z ∈ fiberSpan x weight μ ⊔ B := by simp [htop]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz'
  have hb' : b ∈ W μ := by
    rw [← hab] at hz
    exact (add_sub_cancel_left a b) ▸ (W μ).sub_mem hz (hsub μ ha)
  have hb0 : b = 0 := Submodule.disjoint_def.mp (hW μ) _ hb' hb
  rw [hb0, add_zero] at hab
  exact hab ▸ ha

private theorem finite_lists_of_bounded_length [Finite I] (N : ℕ) :
    Set.Finite {l : List I | l.length ≤ N} := by
  classical
  let I' := Σ n : Fin (N + 1), Fin n.val → I
  let f : I' → List I := fun p => List.ofFn p.2
  apply (Set.finite_range f).subset
  intro l hl
  exact ⟨⟨⟨l.length, Nat.lt_succ_of_le hl⟩, l.get⟩, List.ofFn_get l⟩

end WeightLinearAlgebra

section Weights

open scoped Classical DirectSum
open _root_.Specs.RepTheorySurvey.Affine.AffineSimpleTriples
open _root_.Specs.LieAlgebrasAndRepresentations.HighestWeightData (positiveRootCone_value)
open _root_.LieAlgebrasAndRepresentations.HighestRoot (simpleRoots)

variable {G : Type u} [LieRing G] [LieAlgebra ℂ G]
  {B : InvariantForm G} {H : LieSubalgebra ℂ G} {φ : Direction H}

/-- The Cartan operator on the induced module, using the enveloping action. -/
private abbrev cartanOperator (D : Model B H φ) (χ : U (affineBorel D) →ₐ[ℂ] ℂ)
    (h : affineCartan B H) : Module.End ℂ (affineVerma D χ) :=
  Algebra.lsmul ℂ ℂ (affineVerma D χ) (ι ℂ (show Carrier D from h.1))

theorem mem_affineVermaWeightSpace (D : Model B H φ) (χ : U (affineBorel D) →ₐ[ℂ] ℂ)
    (μ : Weight B H) (z : affineVerma D χ) :
    z ∈ affineVermaWeightSpace D χ μ ↔ ∀ h, cartanOperator D χ h z = μ h • z := by
  simp only [affineVermaWeightSpace, affineVermaWeightSpace_value, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem ι_mul_sub (D : Model B H φ) (a b : Carrier D) :
    ι ℂ a * ι ℂ b - ι ℂ b * ι ℂ a = (ι ℂ ⁅a, b⁆ : U (Carrier D)) :=
  ((ι ℂ).map_lie a b).symm

variable [FiniteDimensional ℂ G] [LieAlgebra.IsSimple ℂ G] [H.IsCartanSubalgebra]

private theorem vermaWeightSpace_independent (D : Model B H φ) (χ : U (affineBorel D) →ₐ[ℂ] ℂ) :
    iSupIndep (affineVermaWeightSpace D χ) := by
  let f := cartanOperator D χ
  have commute (h k : affineCartan B H) : Commute (f h) (f k) := by
    apply Commute.map _ (Algebra.lsmul ℂ ℂ (affineVerma D χ))
    change ι ℂ (show Carrier D from h.1) * ι ℂ (show Carrier D from k.1) =
      ι ℂ (show Carrier D from k.1) * ι ℂ (show Carrier D from h.1)
    apply sub_eq_zero.mp
    rw [ι_mul_sub D, cartan_bracket_cartan D ⟨h.1, h.2⟩ ⟨k.1, k.2⟩, map_zero]
  let c : Weight B H → affineCartan B H → ℂ := fun μ h => μ h
  have hi : Function.Injective c := fun _ _ e => LinearMap.ext (congrFun e)
  have hind := (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f
    (fun h k μ => Module.End.mapsTo_maxGenEigenspace_of_comm (commute k h) μ)).comp hi
  refine hind.mono fun μ => le_iInf fun h => ?_
  intro z hz
  apply Module.End.eigenspace_le_maxGenEigenspace
  exact Module.End.mem_eigenspace_iff.mpr ((mem_affineVermaWeightSpace D χ μ z).mp hz h)

private def simpleWord (D : Model B H φ) (χ : U (affineBorel D) →ₐ[ℂ] ℂ)
    (f : AffineSimpleIndex H φ → Carrier D) (l : List (AffineSimpleIndex H φ)) :
    affineVerma D χ :=
  (l.map fun i => ι ℂ (f i)).prod • affineVermaTop D χ

private def simpleWordWeight (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    {φ : Direction H} (θ : Module.Dual ℂ H) (l : List (AffineSimpleIndex H φ)) : Weight B H :=
  (l.map fun i => affineSimpleRoot B H θ i).sum

private theorem simpleWord_mem_weight (D : Model B H φ) (Λ : Weight B H)
    (χ : U (affineBorel D) →ₐ[ℂ] ℂ) (hχ : IsWeightCharacter D Λ χ)
    (θ : Module.Dual ℂ H) (f : AffineSimpleIndex H φ → Carrier D)
    (hf : ∀ i (h : affineCartan B H), ⁅(show Carrier D from h.1), f i⁆ =
      (-affineSimpleRoot B H θ i h) • f i)
    (l : List (AffineSimpleIndex H φ)) :
    simpleWord D χ f l ∈ affineVermaWeightSpace D χ (Λ - simpleWordWeight B H θ l) := by
  rw [mem_affineVermaWeightSpace]
  intro h
  let a : Carrier D := h.1
  induction l with
  | nil =>
    change ι ℂ a • (1 : U (Carrier D)) • affineVermaTop D χ =
      (Λ h - 0) • ((1 : U (Carrier D)) • affineVermaTop D χ)
    rw [one_smul, sub_zero]
    exact (top_is_highest D Λ χ hχ).1 ⟨h.1, h.2⟩
  | cons i l ih =>
    let z := simpleWord D χ f l
    let p := affineSimpleRoot B H θ i h
    let q := (Λ - simpleWordWeight B H θ l) h
    have he : ι ℂ a * ι ℂ (f i) = (-p) • ι ℂ (f i) + ι ℂ (f i) * ι ℂ a := by
      rw [← sub_eq_iff_eq_add, ι_mul_sub D, hf i h, map_smul]
    have hq : ι ℂ a • z = q • z := ih
    have hsum : (Λ - simpleWordWeight B H θ (i :: l)) h = -p + q := by
      simp only [simpleWordWeight, List.map_cons, List.sum_cons, LinearMap.sub_apply,
        LinearMap.add_apply, p, q]
      ring
    have hz : simpleWord D χ f (i :: l) = ι ℂ (f i) • z := by
      simp only [simpleWord, z, List.map_cons, List.prod_cons, mul_smul]
    rw [hz, hsum]
    change ι ℂ a • (ι ℂ (f i) • z) = (-p + q) • (ι ℂ (f i) • z)
    rw [← mul_smul, he, add_smul, smul_assoc, mul_smul, hq, smul_comm (ι ℂ (f i)) q,
      ← add_smul]

private theorem span_simpleWords (D : Model B H φ) (Λ : Weight B H)
    (χ : U (affineBorel D) →ₐ[ℂ] ℂ) (hχ : IsWeightCharacter D Λ χ)
    (hB : B.IsNormalized H) (hφ : Regular H φ)
    (f : AffineSimpleIndex H φ → Carrier D)
    (hf : affineLieSpan B (Set.range (fun i => (f i : AffineAlgebra B))) = affineNegative B H φ) :
    Submodule.span ℂ (Set.range (simpleWord D χ f)) = ⊤ := by
  let g : AffineSimpleIndex H φ → U (Carrier D) := fun i => ι ℂ (f i)
  let S := Algebra.adjoin ℂ (Set.range g)
  let P : Submodule ℂ (AffineAlgebra B) :=
    Submodule.comap (ι ℂ (L := Carrier D)).toLinearMap S.toSubmodule
  have hPclosed : ClosedUnderBracket B P := by
    intro a b ha hb
    change (ι ℂ a : U (Carrier D)) ∈ S at ha
    change (ι ℂ b : U (Carrier D)) ∈ S at hb
    change (ι ℂ ⁅(show Carrier D from a), (show Carrier D from b)⁆ : U (Carrier D)) ∈ S
    rw [← ι_mul_sub D]
    exact S.sub_mem (S.mul_mem ha hb) (S.mul_mem hb ha)
  have hneg : affineNegative B H φ ≤ P := by
    rw [← hf]
    apply sInf_le
    refine ⟨?_, hPclosed⟩
    rintro _ ⟨i, rfl⟩
    exact Algebra.subset_adjoin (Set.mem_range_self i)
  have hincl (a : U (negative D)) : inclusion (negative D) a ∈ S := by
    induction a using Shared.Lie.enveloping_induction ℂ (negative D) with
    | scalar c => rw [(inclusion (negative D)).commutes]; exact S.algebraMap_mem c
    | generator x =>
      rw [Shared.Lie.inclusion, inclusion_ι]
      exact hneg x.2
    | mul a b ha hb => rw [map_mul]; exact S.mul_mem ha hb
    | add a b ha hb => rw [map_add]; exact S.add_mem ha hb
  obtain ⟨F, hF⟩ := affineVermaPBW B H φ D hB hφ Λ χ hχ
  apply top_unique
  intro z _
  obtain ⟨a, rfl⟩ := F.surjective z
  rw [hF]
  have ha := hincl a
  change inclusion (negative D) a ∈ S.toSubmodule at ha
  change inclusion (negative D) a ∈ (Algebra.adjoin ℂ (Set.range g)).toSubmodule at ha
  rw [Algebra.adjoin_eq_span] at ha
  have hmap (b : U (Carrier D))
      (hb : b ∈ Submodule.span ℂ (Submonoid.closure (Set.range g) : Set (U (Carrier D)))) :
      b • affineVermaTop D χ ∈ Submodule.span ℂ (Set.range (simpleWord D χ f)) := by
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨l, hl, rfl⟩ := Submonoid.exists_list_of_mem_closure hb
      clear hb
      have hh : ∃ l' : List (AffineSimpleIndex H φ), l'.map g = l := by
        induction l with
        | nil => exact ⟨[], rfl⟩
        | cons b l ih =>
          obtain ⟨i, hi⟩ := hl b (by simp)
          obtain ⟨l', hl'⟩ := ih (fun c hc => hl c (List.mem_cons_of_mem _ hc))
          exact ⟨i :: l', by simp only [List.map_cons, hi, hl']⟩
      obtain ⟨l', rfl⟩ := hh
      exact Submodule.subset_span ⟨l', rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [add_smul]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [smul_assoc]; exact Submodule.smul_mem _ c ha
  exact hmap _ ha

private def heightScore (B : InvariantForm G) (H : LieSubalgebra ℂ G)
    (φ : Direction H) (θ : Module.Dual ℂ H) : Weight B H →+ ℝ where
  toFun := fun μ => (φ θ + 1) * (μ (cartanD B H)).re + φ (μ.comp (cartanIncl B H))
  map_zero' := by simp
  map_add' := by
    intro μ ν
    simp only [LinearMap.add_apply, Complex.add_re, mul_add, LinearMap.add_comp, map_add]
    ring

private theorem heightScore_pos (θ : Module.Dual ℂ H) (i : AffineSimpleIndex H φ) :
    0 < heightScore B H φ θ (affineSimpleRoot B H θ i) := by
  cases i with
  | none =>
    have hδ : (delta B H).comp (cartanIncl B H) = 0 := LinearMap.ext (delta_cartanIncl B H)
    have hθ : (extendFiniteRoot B H θ).comp (cartanIncl B H) = θ :=
      LinearMap.ext (extendFiniteRoot_cartanIncl B H θ)
    change 0 < (φ θ + 1) * ((delta B H - extendFiniteRoot B H θ) (cartanD B H)).re +
      φ ((delta B H - extendFiniteRoot B H θ).comp (cartanIncl B H))
    simp [LinearMap.sub_comp, hδ, hθ]
  | some i =>
    have he : (extendFiniteRoot B H i.val).comp (cartanIncl B H) = i.val :=
      LinearMap.ext (extendFiniteRoot_cartanIncl B H i.val)
    change 0 < (φ θ + 1) * (extendFiniteRoot B H i.val (cartanD B H)).re +
      φ ((extendFiniteRoot B H i.val).comp (cartanIncl B H))
    simpa only [extendFiniteRoot_cartanD, Complex.zero_re, mul_zero, zero_add, he] using i.2.1.2

private theorem finite_affineSimpleIndex (H : LieSubalgebra ℂ G) (φ : Direction H)
    [H.IsCartanSubalgebra] : Finite (AffineSimpleIndex H φ) := by
  have hss : LieAlgebrasAndRepresentations.IsSemisimple ℂ G := LieAlgebra.radical_eq_bot
  letI : Finite (simpleRoots H φ) :=
    ((LieAlgebrasAndRepresentations.rootSet_finite H
      (LieAlgebrasAndRepresentations.RealRootSpace.cartan_isMaximalToral hss H).1).subset
        (fun _ hi => hi.1.1)).to_subtype
  infer_instance

private theorem score_length_le (θ : Module.Dual ℂ H) (c : ℝ)
    (hc : ∀ i : AffineSimpleIndex H φ, c ≤ heightScore B H φ θ (affineSimpleRoot B H θ i))
    (l : List (AffineSimpleIndex H φ)) :
    c * l.length ≤ heightScore B H φ θ (simpleWordWeight B H θ l) := by
  induction l with
  | nil => simp [simpleWordWeight]
  | cons i l ih =>
    simp only [simpleWordWeight, List.map_cons, List.sum_cons, map_add,
      List.length_cons, Nat.cast_add, Nat.cast_one, mul_add, mul_one] at ih ⊢
    exact add_le_add ih (hc i) |>.trans_eq (add_comm _ _)

private theorem simpleWord_fiber_finite (Λ μ : Weight B H) (θ : Module.Dual ℂ H) :
    Set.Finite {l : List (AffineSimpleIndex H φ) | Λ - simpleWordWeight B H θ l = μ} := by
  letI := finite_affineSimpleIndex H φ
  obtain ⟨i, hi⟩ := Finite.exists_min (fun i : AffineSimpleIndex H φ =>
    heightScore B H φ θ (affineSimpleRoot B H θ i))
  let c := heightScore B H φ θ (affineSimpleRoot B H θ i)
  have hc : 0 < c := heightScore_pos θ i
  obtain ⟨N, hN⟩ := exists_nat_gt (heightScore B H φ θ (Λ - μ) / c)
  apply (finite_lists_of_bounded_length (I := AffineSimpleIndex H φ) N).subset
  intro l hl
  have he : simpleWordWeight B H θ l = Λ - μ := by
    change Λ - simpleWordWeight B H θ l = μ at hl
    rw [← hl, sub_sub_cancel]
  have hle := score_length_le θ c hi l
  rw [he, mul_comm, ← le_div_iff₀ hc] at hle
  exact le_of_lt (Nat.cast_lt.mp (hle.trans_lt hN))

private theorem simpleWord_top_length (Λ : Weight B H) (θ : Module.Dual ℂ H)
    (l : List (AffineSimpleIndex H φ)) (hl : Λ - simpleWordWeight B H θ l = Λ) : l = [] := by
  letI := finite_affineSimpleIndex H φ
  obtain ⟨i, hi⟩ := Finite.exists_min (fun i : AffineSimpleIndex H φ =>
    heightScore B H φ θ (affineSimpleRoot B H θ i))
  let c := heightScore B H φ θ (affineSimpleRoot B H θ i)
  have hc : 0 < c := heightScore_pos θ i
  have hle := score_length_le θ c hi l
  have he : simpleWordWeight B H θ l = 0 := by
    rw [sub_eq_self] at hl
    exact hl
  rw [he, map_zero] at hle
  exact List.length_eq_zero_iff.mp (by
    have h₀ : (l.length : ℝ) ≤ 0 := nonpos_of_mul_nonpos_right hle hc
    exact Nat.eq_zero_of_le_zero (by exact_mod_cast h₀))

private theorem affineVerma_word_data (D : Model B H φ) (Λ : Weight B H)
    (χ : U (affineBorel D) →ₐ[ℂ] ℂ) (hχ : IsWeightCharacter D Λ χ)
    (hB : B.IsNormalized H) (hφ : Regular H φ) (θ : Module.Dual ℂ H)
    (hθ : IsHighestFiniteRoot H φ θ) :
    ∃ f : AffineSimpleIndex H φ → Carrier D,
      Submodule.span ℂ (Set.range (simpleWord D χ f)) = ⊤ ∧
      ∀ l, simpleWord D χ f l ∈ affineVermaWeightSpace D χ (Λ - simpleWordWeight B H θ l) := by
  obtain ⟨⟨T, S⟩⟩ := finiteSimpleTripleChoices H φ hφ θ hθ
  let f : AffineSimpleIndex H φ → Carrier D := affineSimpleF B T S
  refine ⟨f, span_simpleWords D Λ χ hχ hB hφ f ?_, simpleWord_mem_weight D Λ χ hχ θ f ?_⟩
  · exact (affineSimpleGenerators B H φ hB hφ θ hθ T S).2
  · intro i h
    exact (affineSimpleRootWeights B H φ hB hφ θ hθ T S i).2.2.2 h

theorem affineVermaWeights : affineVermaWeights_type.{u} := by
  classical
  intro G _ _ _ _ B H _ φ D hB hφ Λ χ hχ
  obtain ⟨θ, hθ, _⟩ := highestFiniteRoot H φ hφ
  obtain ⟨f, hspan, hw⟩ := affineVerma_word_data D Λ χ hχ hB hφ θ hθ
  let W := affineVermaWeightSpace D χ
  let wt : List (AffineSimpleIndex H φ) → Weight B H := fun l => Λ - simpleWordWeight B H θ l
  have hi : iSupIndep W := vermaWeightSpace_independent D χ
  have hW (μ : Weight B H) : W μ = fiberSpan (simpleWord D χ f) wt μ :=
    weight_eq_fiberSpan W hi _ wt hw hspan μ
  refine ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi ?_, ?_, ?_, ?_⟩
  · apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨l, rfl⟩
    exact Submodule.mem_iSup_of_mem (wt l) (hw l)
  · intro μ
    change FiniteDimensional ℂ (W μ)
    rw [hW]
    have hf : Finite {l : List (AffineSimpleIndex H φ) // wt l = μ} :=
      (simpleWord_fiber_finite Λ μ θ).to_subtype
    exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  · obtain ⟨F, hF⟩ := affineVermaPBW B H φ D hB hφ Λ χ hχ
    intro h0
    have eq : (1 : U (negative D)) = 0 := F.injective (by rw [hF, map_zero, map_one, one_smul, h0])
    have he := congrArg (Shared.Lie.augmentation ℂ (negative D)) eq
    exact one_ne_zero (by simpa only [map_one, map_zero] using he)
  · change W Λ = ℂ ∙ affineVermaTop D χ
    rw [hW]
    unfold fiberSpan
    congr 1
    ext z
    constructor
    · rintro ⟨⟨l, hl⟩, rfl⟩
      have hl' := simpleWord_top_length Λ θ l hl
      simp [hl', simpleWord]
    · intro hz
      have hzl : z = affineVermaTop D χ := hz
      subst z
      exact ⟨⟨[], by simp [wt, simpleWordWeight]⟩, by simp [simpleWord]⟩

theorem affineVermaWeightSupport : affineVermaWeightSupport_type.{u} := by
  classical
  intro G _ _ _ _ B H _ φ D hB hφ Λ χ hχ θ hθ μ hμ
  obtain ⟨f, hspan, hw⟩ := affineVerma_word_data D Λ χ hχ hB hφ θ hθ
  let wt : List (AffineSimpleIndex H φ) → Weight B H := fun l => Λ - simpleWordWeight B H θ l
  have he := weight_eq_fiberSpan (affineVermaWeightSpace D χ)
    (vermaWeightSpace_independent D χ) (simpleWord D χ f) wt hw hspan μ
  have hl : ∃ l : List (AffineSimpleIndex H φ), wt l = μ := by
    by_contra! hn
    apply hμ
    change affineVermaWeightSpace D χ μ = ⊥
    rw [he]
    apply bot_unique
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨l, hl⟩, rfl⟩
    exact (hn l hl).elim
  obtain ⟨l, hl⟩ := hl
  change Λ - simpleWordWeight B H θ l = μ at hl
  rw [← hl, sub_sub_cancel]
  clear hl
  induction l with
  | nil => exact Submodule.zero_mem _
  | cons i l ih =>
    exact Submodule.add_mem _ (Submodule.subset_span ⟨i, rfl⟩) ih

end Weights

end RepTheorySurvey.Affine
