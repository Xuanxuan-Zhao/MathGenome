import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.HarishChandraIsomorphism
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InvariantRestrictionInjection
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Group.Subgroup.Lattice
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightStringsConvexity
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.LongestElementRho
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Symmetrization
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ChevalleyRestriction
import Batteries.Tactic.OpenPrivate

noncomputable section

open scoped TensorProduct

namespace LieAlgebrasAndRepresentations.HarishChandraIsomorphism

open Specs.LieAlgebrasAndRepresentations.HarishChandraIsomorphism
open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.VermaWeightsUniversal
open Specs.LieAlgebrasAndRepresentations.HighestWeightData
open Specs.LieAlgebrasAndRepresentations.SolvableRadical (IsSemisimple_value)
open UniversalEnvelopingAlgebra (ι)
open private envelopingMap_comp envelopingMap_ι from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules
open private highestVector_mem_weight induced_lie tensorClass_eq_smul
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)

abbrev rho := @rhoValue
abbrev projection := @projectionValue
abbrev shifted := @shiftedProjection

@[simp] theorem evaluation_generator (η : Module.Dual ℂ H) (h : H) :
    evaluation H η (SymmetricAlgebra.ι ℂ H h) = η h := SymmetricAlgebra.lift_ι_apply _ _

@[simp] theorem cartan_generator (habel : ∀ a b : H, ⁅a, b⁆ = 0) (h : H) :
    cartanToSymmetric H habel (ι ℂ h) = SymmetricAlgebra.ι ℂ H h :=
  UniversalEnvelopingAlgebra.lift_ι_apply _ _ _

/-- The canonical identification of the enveloping algebra of the abelian
Cartan with its symmetric algebra. -/
def cartanEquiv (habel : ∀ a b : H, ⁅a, b⁆ = 0) : U H ≃ₐ[ℂ] SymmetricAlgebra ℂ H := by
  let F : TensorAlgebra ℂ H →ₐ[ℂ] U H := UniversalEnvelopingAlgebra.mkAlgHom ℂ H
  have hF : TensorAlgebra.symRingCon ℂ H ≤ RingCon.ker F.toRingHom := by
    apply RingCon.ringConGen_le.mpr
    rintro _ _ ⟨x, y⟩
    apply (RingCon.ker_apply _).mpr
    change F (_ * _) = F (_ * _)
    rw [map_mul, map_mul]
    change ι ℂ x * ι ℂ y = ι ℂ y * ι ℂ x
    apply sub_eq_zero.mp
    rw [← LieRing.of_associative_ring_bracket, ← (ι ℂ).map_lie, habel, map_zero]
  let G : SymmetricAlgebra ℂ H →ₐ[ℂ] U H :=
    RingCon.liftₐ (TensorAlgebra.symRingCon ℂ H) F hF
  have hG (h : H) : G (SymmetricAlgebra.ι ℂ H h) = ι ℂ h :=
    RingCon.liftₐ_mk _ _ _ _
  refine AlgEquiv.ofAlgHom (cartanToSymmetric H habel) G ?_ ?_
  · apply SymmetricAlgebra.algHom_ext
    ext h
    change cartanToSymmetric H habel (G (SymmetricAlgebra.ι ℂ H h)) =
      SymmetricAlgebra.ι ℂ H h
    rw [hG, cartan_generator]
  · apply UniversalEnvelopingAlgebra.hom_ext
    ext h
    change G (cartanToSymmetric H habel (ι ℂ h)) = ι ℂ h
    rw [cartan_generator, hG]

@[simp] theorem cartanEquiv_toAlgHom (habel : ∀ a b : H, ⁅a, b⁆ = 0) :
    (cartanEquiv H habel).toAlgHom = cartanToSymmetric H habel := rfl

theorem cartan_identification : cartan_identification_type.{u} := by
  intro L _ _ H habel
  exact ⟨cartanEquiv H habel, cartanEquiv_toAlgHom H habel⟩

theorem evaluation_translation (δ η : Module.Dual ℂ H) (p : SymmetricAlgebra ℂ H) :
    evaluation H η (translation H δ p) = evaluation H (η - δ) p := by
  have he : (evaluation H η).comp (translation H δ) = evaluation H (η - δ) := by
    apply SymmetricAlgebra.algHom_ext
    ext h
    change evaluation H η (translation H δ (SymmetricAlgebra.ι ℂ H h)) =
      evaluation H (η - δ) (SymmetricAlgebra.ι ℂ H h)
    simp [translation]
  exact DFunLike.congr_fun he p

private abbrev cartanIn : H →ₗ⁅ℂ⁆ borel_value H φ := LieSubalgebra.inclusion le_sup_left
private abbrev positiveIn : positive_value H φ →ₗ⁅ℂ⁆ borel_value H φ :=
  LieSubalgebra.inclusion le_sup_right

theorem projection_triangular (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (ht : Function.Bijective (triangular_value H φ))
    (a : U (negative_value H φ)) (b : U H) (c : U (positive_value H φ)) :
    projectionValue H φ habel ht
      (envelopingMap (negative_value H φ).incl a * envelopingMap H.incl b *
        envelopingMap (positive_value H φ).incl c) =
    (Shared.Lie.augmentation ℂ (negative_value H φ) a *
      Shared.Lie.augmentation ℂ (positive_value H φ) c) • cartanToSymmetric H habel b := by
  rw [← VermaModules.triangular_apply H φ a b c]
  change tensorProjection H φ habel
    ((LinearEquiv.ofBijective (triangular_value H φ) ht).symm
      ((LinearEquiv.ofBijective (triangular_value H φ) ht) (a ⊗ₜ[ℂ] (b ⊗ₜ[ℂ] c)))) = _
  rw [LinearEquiv.symm_apply_apply]
  simp [tensorProjection, mul_smul]
  exact smul_comm _ _ _

section Verma

variable (χ : U (borel_value H φ) →ₐ[ℂ] ℂ)
local notation "M" => induced_value H φ χ
local notation "v₀" => highestVector_value H φ χ
local instance : LieRingModule L M := inducedLieRingModule H φ χ
local instance : LieModule ℂ L M := inducedLieModule H φ χ

private theorem cartan_character (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (lam : Module.Dual ℂ H) (hχ : IsWeightCharacter H φ lam χ) (b : U H) :
    χ (envelopingMap (cartanIn H φ) b) = evaluation H lam (cartanToSymmetric H habel b) := by
  have he : χ.comp (envelopingMap (cartanIn H φ)) =
      (evaluation H lam).comp (cartanToSymmetric H habel) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    ext h
    change χ (envelopingMap (cartanIn H φ) (ι ℂ h)) =
      evaluation H lam (cartanToSymmetric H habel (ι ℂ h))
    rw [envelopingMap_ι, hχ.1 h, cartan_generator, evaluation_generator]
  exact DFunLike.congr_fun he b

private theorem positive_character (lam : Module.Dual ℂ H)
    (hχ : IsWeightCharacter H φ lam χ) (c : U (positive_value H φ)) :
    χ (envelopingMap (positiveIn H φ) c) = Shared.Lie.augmentation ℂ (positive_value H φ) c := by
  have he : χ.comp (envelopingMap (positiveIn H φ)) =
      Shared.Lie.augmentation ℂ (positive_value H φ) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    ext x
    change χ (envelopingMap (positiveIn H φ) (ι ℂ x)) =
      Shared.Lie.augmentation ℂ (positive_value H φ) (ι ℂ x)
    rw [envelopingMap_ι, hχ.2 x]
    exact (UniversalEnvelopingAlgebra.lift_ι_apply ℂ (0 : positive_value H φ →ₗ⁅ℂ⁆ ℂ) x).symm
  exact DFunLike.congr_fun he c

private theorem borel_smul_highest (b : U (borel_value H φ)) :
    envelopingMap (borel_value H φ).incl b • v₀ = χ b • v₀ := by
  rw [← tensorClass_eq_smul]
  have hb := VermaModules.tensor_balanced H φ χ 1 b 1
  rw [one_mul, mul_one] at hb
  rw [hb]
  let q := (balance H φ χ).mkQ.restrictScalars ℂ
  change q ((1 : U L) ⊗ₜ[ℂ] χ b) = χ b • q ((1 : U L) ⊗ₜ[ℂ] (1 : ℂ))
  rw [← map_smul]
  exact congrArg q (by simpa using TensorProduct.tmul_smul (R := ℂ) (χ b) (1 : U L) (1 : ℂ))

private theorem triangular_smul_highest (a : U (negative_value H φ)) (b : U H)
    (c : U (positive_value H φ)) :
    (envelopingMap (negative_value H φ).incl a * envelopingMap H.incl b *
      envelopingMap (positive_value H φ).incl c) • v₀ =
      (χ (envelopingMap (cartanIn H φ) b) * χ (envelopingMap (positiveIn H φ) c)) •
        (envelopingMap (negative_value H φ).incl a • v₀) := by
  let iB := envelopingMap (borel_value H φ).incl
  have hb : iB (envelopingMap (cartanIn H φ) b) = envelopingMap H.incl b :=
    DFunLike.congr_fun (envelopingMap_comp (cartanIn H φ) _) b
  have hc : iB (envelopingMap (positiveIn H φ) c) = envelopingMap (positive_value H φ).incl c :=
    DFunLike.congr_fun (envelopingMap_comp (positiveIn H φ) _) c
  rw [← hb, ← hc, mul_assoc, ← map_mul, mul_smul, borel_smul_highest, map_mul, smul_comm]

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

/-- Applying the negative augmentation to the Verma-module realization
recovers evaluation of the PBW Cartan projection. -/
private theorem highest_coefficient
    (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (ht : Function.Bijective (triangular_value H φ))
    (lam : Module.Dual ℂ H) (hχ : IsWeightCharacter H φ lam χ)
    (E : U (negative_value H φ) ≃ₗ[ℂ] M)
    (hE : ∀ a, E a = envelopingMap (negative_value H φ).incl a • v₀) (x : U L) :
    Shared.Lie.augmentation ℂ (negative_value H φ) (E.symm (x • v₀)) =
      evaluation H lam (projectionValue H φ habel ht x) := by
  obtain ⟨t,rfl⟩ := ht.2 x
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => simp only [map_add, add_smul, ht, ht']
  | tmul a t =>
    induction t using TensorProduct.inductionOn with
    | add t t' ht ht' => simp only [TensorProduct.tmul_add, map_add, add_smul, ht, ht']
    | tmul b c =>
      rw [VermaModules.triangular_apply, triangular_smul_highest, projection_triangular,
        ← hE, map_smul, E.symm_apply_apply, map_smul, map_smul, cartan_character H φ χ habel lam hχ,
        positive_character H φ χ lam hχ]
      simp only [smul_eq_mul]
      ring

/-- Central elements act on the entire Verma module by the PBW evaluation. -/
theorem highest_vector_scalar : highest_vector_scalar_type.{u} := by
  intro L _ _ _ hss H _ φ hφ habel ht lam χ hχ z
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  let vTop := highestVector_value H φ χ
  obtain ⟨E, hE, hvTop⟩ := VermaModules.induced_free hss H φ hφ χ
  have hcentral := (Subalgebra.mem_center_iff.mp z.property)
  have htop := (VermaWeightsUniversal.verma_weights hss H φ hφ lam χ hχ).2.2.2
  change weightSpace_value (induced_value H φ χ) H lam = ℂ ∙ vTop at htop
  have hw := (HighestWeight.mem_weightSpace (induced_value H φ χ) H lam vTop).mp
    (highestVector_mem_weight H φ χ lam hχ)
  have hz : z.val • vTop ∈ weightSpace_value (induced_value H φ χ) H lam := by
    apply (HighestWeight.mem_weightSpace (induced_value H φ χ) H lam _).mpr
    intro h
    rw [induced_lie, ← mul_smul, hcentral, mul_smul, ← induced_lie, hw, smul_comm]
  rw [htop, Submodule.mem_span_singleton] at hz
  obtain ⟨d, hd⟩ := hz
  have h1 : E 1 = vTop := by simp [hE, vTop]
  have hd' := highest_coefficient H φ χ habel ht lam hχ E hE z.val
  rw [← hd, ← h1, map_smul, E.symm_apply_apply, map_smul, map_one, smul_eq_mul, mul_one] at hd'
  intro v
  obtain ⟨a,rfl⟩ := E.surjective v
  rw [hE, ← mul_smul, ← hcentral, mul_smul]
  change envelopingMap (negative_value H φ).incl a • (z.val • vTop) =
    _ • (envelopingMap (negative_value H φ).incl a • vTop)
  rw [← hd, hd', smul_comm]

end Verma

section Singular

open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSpace_value)
open Shared.Lie.PBW
open private highest_killed power_smul_eq pow_shift from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient

private theorem generator_pow_ne_zero {K : Type u} [LieRing K] [LieAlgebra ℂ K]
    {x : K} (hx : x ≠ 0) (n : ℕ) : (ι ℂ x) ^ n ≠ 0 := by
  classical
  have hlin : LinearIndepOn ℂ id ({x} : Set K) := (linearIndepOn_singleton_iff ℂ).mpr hx
  let b := Module.Basis.extend hlin
  let i : hlin.extend (Set.subset_univ _) := ⟨x, hlin.subset_extend _ (Set.mem_singleton _)⟩
  letI : LinearOrder (hlin.extend (Set.subset_univ _)) := WellOrderingRel.isWellOrder.linearOrder
  let l : OrderedWord (hlin.extend (Set.subset_univ _)) :=
    ⟨List.replicate n i, List.pairwise_replicate.mpr (Or.inr le_rfl)⟩
  have hb : b i = x := Module.Basis.extend_apply_self hlin i
  have hl := (orderedBasis b).ne_zero l
  rw [orderedBasis_apply] at hl
  simpa [orderedMonomial, monomial, Shared.Lie.word, l, hb] using hl

theorem singular_vector : singular_vector_type.{u} := by
  classical
  intro L _ _ _ hss H _ φ hφ lam χ hχ e f hef i m hm
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  let M := induced_value H φ χ
  let v₀ := highestVector_value H φ χ
  let v := (ι ℂ (f i)) ^ (m + 1) • v₀
  obtain ⟨E, hE, hv₀⟩ := VermaModules.induced_free hss H φ hφ χ
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  have hfi : f i ∈ negative_value H φ := by
    apply LieSubalgebra.subset_lieSpan
    exact ⟨-i.val, by simpa using neg_lt_zero.mpr i.property.1.2, (hef i).2.1⟩
  let fi : negative_value H φ := ⟨f i, hfi⟩
  have hfi0 : fi ≠ 0 := fun hf => (hef i).2.2.2.1 (congrArg Subtype.val hf)
  have hv : E ((ι ℂ fi) ^ (m + 1)) = v := by
    rw [hE, map_pow, envelopingMap_ι]
    rfl
  change v ≠ 0 ∧ (∀ j, ⁅e j, v⁆ = 0) ∧
    ∀ h : H, ⁅(h : L), v⁆ = (lam - (m + 1) • i.val) h • v
  refine ⟨hv ▸ (E.map_ne_zero_iff.mpr (generator_pow_ne_zero hfi0 _)), ?_, ?_⟩
  · intro j
    change ⁅e j, (ι ℂ (f i)) ^ (m + 1) • v₀⁆ = 0
    rw [power_smul_eq]
    have he₀ := highest_killed H φ χ hχ (fun k => (hef k).1)
    by_cases hij : j = i
    · subst j
      let t := IntegrableHighestWeightQuotient.isSl2Triple H φ hss hef i
      have hh := (HighestWeight.mem_weightSpace M H lam v₀).mp
        (highestVector_mem_weight H φ χ lam hχ) (Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value H i.val)
      have hp : IsSl2Triple.HasPrimitiveVectorWith t v₀ (m : ℂ) :=
        ⟨hv₀, hm ▸ hh, he₀ i⟩
      simpa using hp.lie_e_pow_succ_toEnd_f m
    · obtain ⟨_, _, hrel, _, _⟩ := serre_relations hss H hH φ hφ e f hef
      have hx : ⁅e j, f i⁆ = 0 := by simpa [hij] using (hrel j i).2.2.2
      generalize m + 1 = n
      induction n with
      | zero => simpa using he₀ j
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply, leibniz_lie, hx, ih]
        simp
  · have hw := pow_shift H (hef i).2.1
      (highestVector_mem_weight H φ χ lam hχ) (m + 1)
    have hvw : v ∈ weightSpace_value M H (lam + (m + 1) • (-i.val)) := by
      dsimp only [v]
      rw [power_smul_eq]
      exact hw
    simpa only [smul_neg, sub_eq_add_neg] using
      (HighestWeight.mem_weightSpace M H _ v).mp hvw

end Singular

section Polynomials

variable {A B C : Type u} [AddCommGroup A] [Module ℂ A]
  [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]

/-- The algebra homomorphism on symmetric algebras induced by a linear map. -/
def symmetricMap (f : A →ₗ[ℂ] B) : SymmetricAlgebra ℂ A →ₐ[ℂ] SymmetricAlgebra ℂ B :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι ℂ B).comp f)

@[simp] theorem symmetricMap_generator (f : A →ₗ[ℂ] B) (x : A) :
    symmetricMap f (SymmetricAlgebra.ι ℂ A x) = SymmetricAlgebra.ι ℂ B (f x) :=
  SymmetricAlgebra.lift_ι_apply _ _

theorem symmetricMap_comp (g : B →ₗ[ℂ] C) (f : A →ₗ[ℂ] B) :
    symmetricMap (g.comp f) = (symmetricMap g).comp (symmetricMap f) := by
  apply SymmetricAlgebra.algHom_ext
  ext x
  change symmetricMap (g.comp f) (SymmetricAlgebra.ι ℂ A x) =
    symmetricMap g (symmetricMap f (SymmetricAlgebra.ι ℂ A x))
  simp

/-- The algebra isomorphism induced by a linear isomorphism. -/
def symmetricEquiv (e : A ≃ₗ[ℂ] B) : SymmetricAlgebra ℂ A ≃ₐ[ℂ] SymmetricAlgebra ℂ B :=
  AlgEquiv.ofAlgHom (symmetricMap e.toLinearMap) (symmetricMap e.symm.toLinearMap)
    (by
      apply SymmetricAlgebra.algHom_ext
      ext x
      change symmetricMap e.toLinearMap (symmetricMap e.symm.toLinearMap
        (SymmetricAlgebra.ι ℂ B x)) = _
      simp)
    (by
      apply SymmetricAlgebra.algHom_ext
      ext x
      change symmetricMap e.symm.toLinearMap (symmetricMap e.toLinearMap
        (SymmetricAlgebra.ι ℂ A x)) = _
      simp)

@[simp] theorem symmetricEquiv_generator (e : A ≃ₗ[ℂ] B) (x : A) :
    symmetricEquiv e (SymmetricAlgebra.ι ℂ A x) = SymmetricAlgebra.ι ℂ B (e x) :=
  symmetricMap_generator e.toLinearMap x

end Polynomials

section CenterAlgebra

open Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection (polynomialEvaluation eval)

variable [FiniteDimensional ℂ L]

private theorem complex_eval_eq (η : Module.Dual ℂ H) (p : SymmetricAlgebra ℂ H) :
    evaluation H η p = eval (symmetricEquiv (Module.evalEquiv ℂ H) p) η := by
  have he : evaluation H η =
      ((Pi.evalAlgHom ℂ (fun _ : Module.Dual ℂ H => ℂ) η).comp
        (polynomialEvaluation (Module.Dual ℂ H))).comp
          (symmetricEquiv (Module.evalEquiv ℂ H)).toAlgHom := by
    apply SymmetricAlgebra.algHom_ext
    ext h
    change evaluation H η (SymmetricAlgebra.ι ℂ H h) =
      eval (symmetricEquiv (Module.evalEquiv ℂ H) (SymmetricAlgebra.ι ℂ H h)) η
    rw [evaluation_generator, symmetricEquiv_generator, InvariantRestrictionInjection.eval_ι]
    rfl
  exact DFunLike.congr_fun he p

theorem evaluation_ext {p q : SymmetricAlgebra ℂ H}
    (he : ∀ η, evaluation H η p = evaluation H η q) : p = q := by
  apply (symmetricEquiv (Module.evalEquiv ℂ H)).injective
  apply InvariantRestrictionInjection.evaluation_injective
  funext η
  simpa only [← complex_eval_eq H] using he η

private theorem cartan_abelian (hss : IsSemisimple_value ℂ L) [H.IsCartanSubalgebra]
    (a b : H) : ⁅a, b⁆ = 0 := by
  letI : IsLieAbelian H := (RealRootSpace.cartan_isMaximalToral hss H).1.1
  exact trivial_lie_zero H H a b

variable [H.IsCartanSubalgebra]

/-- The triangular PBW projection is multiplicative on the center. -/
def projectionOnCenter (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (ht : Function.Bijective (triangular_value H φ)) :
    Subalgebra.center ℂ (U L) →ₐ[ℂ] SymmetricAlgebra ℂ H where
  __ := (projectionValue H φ habel ht).comp (Subalgebra.center ℂ (U L)).val.toLinearMap
  map_zero' := map_zero _
  map_one' := by
    have h := projection_triangular H φ habel ht 1 1 1
    simpa using h
  map_mul' := by
    intro z t
    apply evaluation_ext H
    intro lam
    obtain ⟨χ, hχ, _⟩ := VermaModules.character_existsUnique hss H φ hφ lam
    obtain ⟨_, _, hv₀⟩ := VermaModules.induced_free hss H φ hφ χ
    let v := highestVector_value H φ χ
    rw [map_mul]
    change evaluation H lam (projectionValue H φ habel ht (z * t).val) =
      evaluation H lam (projectionValue H φ habel ht z.val) *
        evaluation H lam (projectionValue H φ habel ht t.val)
    apply smul_left_injective ℂ hv₀
    change evaluation H lam (projectionValue H φ habel ht (z * t).val) • v =
      (evaluation H lam (projectionValue H φ habel ht z.val) *
        evaluation H lam (projectionValue H φ habel ht t.val)) • v
    rw [← highest_vector_scalar hss H φ hφ habel ht lam χ hχ (z * t) v]
    change (z.val * t.val) • v = _
    rw [mul_smul]
    rw [highest_vector_scalar hss H φ hφ habel ht lam χ hχ t v, smul_comm,
      highest_vector_scalar hss H φ hφ habel ht lam χ hχ z v]
    simp only [smul_smul]
    rw [mul_comm]
  commutes' := by
    intro c
    change projectionValue H φ habel ht (algebraMap ℂ (U L) c) = _
    have h := projection_triangular H φ habel ht 1 (algebraMap ℂ (U H) c) 1
    simpa using h

end CenterAlgebra

section ShiftedInvariance

open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value)
open Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient (Normalized)
open private weightReflection_apply from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightStringsConvexity
open private lieHom_map_enveloping_smul from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaWeightsUniversal

private def affineLine (a b : Module.Dual ℂ H) : SymmetricAlgebra ℂ H →ₐ[ℂ] Polynomial ℂ :=
  SymmetricAlgebra.lift
    (((Algebra.linearMap ℂ (Polynomial ℂ)).comp a) +
      (Polynomial.X : Polynomial ℂ) • ((Algebra.linearMap ℂ (Polynomial ℂ)).comp b))

private theorem eval_affineLine (a b : Module.Dual ℂ H) (t : ℂ) (q : SymmetricAlgebra ℂ H) :
    Polynomial.eval t (affineLine H a b q) = evaluation H (a + t • b) q := by
  have he : (Polynomial.aeval t).comp (affineLine H a b) = evaluation H (a + t • b) := by
    apply SymmetricAlgebra.algHom_ext
    ext h
    change Polynomial.aeval t (affineLine H a b (SymmetricAlgebra.ι ℂ H h)) =
      evaluation H (a + t • b) (SymmetricAlgebra.ι ℂ H h)
    rw [affineLine, SymmetricAlgebra.lift_ι_apply, evaluation_generator]
    change Polynomial.aeval t (Polynomial.C (a h) + Polynomial.X * Polynomial.C (b h)) =
      a h + t * b h
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    rfl
  exact DFunLike.congr_fun he q

/-- A polynomial on the weights that vanishes on all nonnegative-integral
coroot hyperplanes vanishes identically. -/
private theorem polynomial_eq_of_integral_slices {h : H} {b : Module.Dual ℂ H} (hb : b h = 1)
    (p q : SymmetricAlgebra ℂ H)
    (he : ∀ lam : Module.Dual ℂ H, ∀ n : ℕ, lam h = (n : ℂ) →
      evaluation H lam p = evaluation H lam q)
    (lam : Module.Dual ℂ H) : evaluation H lam p = evaluation H lam q := by
  let a := lam - lam h • b
  have ha : a h = 0 := by simp [a, hb]
  have ha' : a + lam h • b = lam := sub_add_cancel _ _
  have hpol : affineLine H a b p = affineLine H a b q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R := ℂ))).mono
    rintro _ ⟨n,rfl⟩
    change Polynomial.eval (n : ℂ) (affineLine H a b p) =
      Polynomial.eval (n : ℂ) (affineLine H a b q)
    rw [eval_affineLine, eval_affineLine]
    exact he _ n (by simp [ha, hb])
  rw [← ha', ← eval_affineLine, ← eval_affineLine, hpol]

private theorem evaluate_symmetricMap (f : H →ₗ[ℂ] H) (lam : Module.Dual ℂ H)
    (p : SymmetricAlgebra ℂ H) :
    evaluation H lam (symmetricMap f p) = evaluation H (lam.comp f) p := by
  have he : (evaluation H lam).comp (symmetricMap f) = evaluation H (lam.comp f) := by
    apply SymmetricAlgebra.algHom_ext
    ext h
    change evaluation H lam (symmetricMap f (SymmetricAlgebra.ι ℂ H h)) =
      evaluation H (lam.comp f) (SymmetricAlgebra.ι ℂ H h)
    simp
  exact DFunLike.congr_fun he p

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

private theorem normalized_root_vectors (hss : IsSemisimple_value ℂ L) :
    ∃ e f, Normalized H φ e f := by
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  choose e f hef using fun i : simple H φ => exists_root_triple hss H hH i.val i.property.1.1
  exact ⟨e, f, fun i => ⟨(hef i).1, (hef i).2.1, (hef i).2.2.1, (hef i).2.2.2.1,
    (hef i).2.2.2.2.1⟩⟩

private theorem unshifted_eq_on_simple_slice
    (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (ht : Function.Bijective (triangular_value H φ))
    (z : Subalgebra.center ℂ (U L)) (i : simple H φ)
    (lam : Module.Dual ℂ H) (m : ℕ) (hm : lam (coroot_value H i.val) = (m : ℂ)) :
    evaluation H lam (projectionValue H φ habel ht z.val) =
      evaluation H (lam - (m + 1) • i.val) (projectionValue H φ habel ht z.val) := by
  obtain ⟨e,f,hef⟩ := normalized_root_vectors H φ hss
  obtain ⟨χ,hχ,_⟩ := VermaModules.character_existsUnique hss H φ hφ lam
  let mu := lam - (m + 1) • i.val
  obtain ⟨χ',hχ',_⟩ := VermaModules.character_existsUnique hss H φ hφ mu
  letI := inducedLieRingModule H φ χ
  letI := inducedLieModule H φ χ
  letI := inducedLieRingModule H φ χ'
  letI := inducedLieModule H φ χ'
  let M := induced_value H φ χ
  let v := (ι ℂ (f i)) ^ (m + 1) • highestVector_value H φ χ
  obtain ⟨hv,he,hweight⟩ := singular_vector hss H φ hφ lam χ hχ e f hef i m hm
  obtain ⟨⟨F,hF,_⟩,_⟩ := VermaWeightsUniversal.verma_universal hss H φ hφ mu χ' hχ'
    e (fun j => ⟨(hef j).1, (hef j).2.2.1⟩) M v hweight he
  have hmap := lieHom_map_enveloping_smul H φ χ' M (fun x w => rfl)
    F z.val (highestVector_value H φ χ')
  rw [highest_vector_scalar hss H φ hφ habel ht mu χ' hχ' z, map_smul, hF,
    highest_vector_scalar hss H φ hφ habel ht lam χ hχ z] at hmap
  exact (smul_left_injective ℂ hv hmap).symm

/-- The simple-reflection identities follow from the Verma singular vectors
and one-variable polynomial interpolation along transverse affine lines. -/
private theorem shifted_simple_invariant
    (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (ht : Function.Bijective (triangular_value H φ))
    (i : simple H φ) (hρ : rhoValue H φ (coroot_value H i.val) = 1)
    (z : Subalgebra.center ℂ (U L)) (η : Module.Dual ℂ H) :
    evaluation H (weightReflection H i.val η) (shiftedProjection H φ habel ht z.val) =
      evaluation H η (shiftedProjection H φ habel ht z.val) := by
  let h := coroot_value H i.val
  have hi : i.val h = 2 := FiniteModuleWeights.coroot_normalized H i.val hss
    (RealRootSpace.cartan_isMaximalToral hss H) i.property.1.1
  let f : H →ₗ[ℂ] H := LinearMap.id - i.val.smulRight h
  let p := projectionValue H φ habel ht z.val
  let q := symmetricMap f (translation H i.val p)
  have hq (lam : Module.Dual ℂ H) :
      evaluation H lam q = evaluation H (lam - (lam h + 1) • i.val) p := by
    rw [show q = symmetricMap f (translation H i.val p) by rfl,
      evaluate_symmetricMap, evaluation_translation]
    apply congrArg (fun a => evaluation H a p)
    ext x
    simp only [f, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, LinearMap.smul_apply, map_sub, map_smul, smul_eq_mul]
    ring
  have he (lam : Module.Dual ℂ H) :
      evaluation H lam p = evaluation H lam q := by
    apply polynomial_eq_of_integral_slices H (h := h) (b := (2 : ℂ)⁻¹ • i.val)
    · simp [hi, smul_eq_mul]
    · intro mu m hm
      rw [hq, hm]
      have hcast : ((m + 1 : ℕ) • i.val) = ((m : ℂ) + 1) • i.val := by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (Nat.cast_smul_eq_nsmul ℂ (m + 1) i.val).symm
      rw [← hcast]
      exact unshifted_eq_on_simple_slice H φ hss hφ habel ht z i mu m hm
  change evaluation H (weightReflection H i.val η) (translation H (rhoValue H φ) p) =
    evaluation H η (translation H (rhoValue H φ) p)
  rw [evaluation_translation, evaluation_translation, he (η - rhoValue H φ), hq,
    weightReflection_apply hi]
  apply congrArg (fun a => evaluation H a p)
  simp only [LinearMap.sub_apply, hρ, sub_add_cancel, h]
  abel

end ShiftedInvariance

section RootComparison

open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value)
open Specs.LieAlgebrasAndRepresentations.RealRootSpace (E Realization realRoots rootRestriction)
open private direction_vector simple_equiv vector_regular extension_injective
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.FiniteHighestWeightExistence
open private weightReflection_apply from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightStringsConvexity

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

private theorem complexification_ext (d : Realization H)
    (a b : Module.Dual ℂ H →ₗ[ℂ] Module.Dual ℂ H)
    (h : ∀ x, a (d.j x) = b (d.j x)) : a = b := by
  ext lam
  obtain ⟨z,rfl⟩ := d.complexification.surjective lam
  induction z using TensorProduct.inductionOn with
  | tmul c x => simp [h x]
  | add z t hz ht => simp [hz, ht]

variable {H} (d : Realization H) [Fact (Realization H)]

local instance : NormedAddCommGroup (E H) := (Fact.out : Realization H).normedAddCommGroup
local instance : InnerProductSpace ℝ (E H) := (Fact.out : Realization H).innerProductSpace

private theorem rho_extension (hss : IsSemisimple_value ℂ L) (v : E H) (hv : ∀ x, φ (d.j x) = inner ℝ v x) :
    d.j (rootRho (realRoots H) v) = rhoValue H φ := by
  classical
  have hR := d.root_system
  letI : Finite (rootSet_value H) :=
    (rootSet_finite H (RealRootSpace.cartan_isMaximalToral hss H).1).to_subtype
  let t : positiveRoots (realRoots H) v → {a : rootSet_value H // 0 < φ a.val} := fun a =>
    ⟨⟨d.j a.val, by
      obtain ⟨b, hb, h⟩ := a.property.1
      rw [← h, d.extension_root b hb]
      exact hb⟩, by rw [hv]; exact a.property.2⟩
  have hbij : Function.Bijective t := by
    constructor
    · intro a b hab
      exact Subtype.ext (extension_injective d (congrArg (fun x => x.val.val) hab))
    · rintro ⟨⟨a, ha⟩, hp⟩
      have hm : rootRestriction H a ∈ positiveRoots (realRoots H) v :=
        ⟨⟨a, ha, rfl⟩, by rw [← hv, d.extension_root a ha]; exact hp⟩
      exact ⟨⟨_, hm⟩, Subtype.ext (Subtype.ext (d.extension_root a ha))⟩
  letI : Fintype (positiveRoots (realRoots H) v) :=
    ((hR.finite.subset fun _ h => h.1) : (positiveRoots (realRoots H) v).Finite).fintype
  letI : Fintype {a : rootSet_value H // 0 < φ a.val} := Fintype.ofFinite _
  rw [rootRho, ← finsum_set_coe_eq_finsum_mem, rhoValue,
    finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_smul, map_sum]
  have hs (q : Module.Dual ℂ H) : (1 / 2 : ℝ) • q = (1 / 2 : ℂ) • q := by
    ext h
    change ((1 / 2 : ℝ) : ℂ) * q h = (1 / 2 : ℂ) * q h
    norm_num
  rw [hs]
  congr 1
  exact Fintype.sum_equiv (Equiv.ofBijective t hbij) _ _ (fun _ => rfl)

private theorem reflection_on_real (hss : IsSemisimple_value ℂ L)
    (α : Module.Dual ℂ H) (ha : α ∈ rootSet_value H) (x : E H) :
    weightReflection H α (d.j x) = d.j (rootReflectionEquiv (rootRestriction H α) x) := by
  have hnorm := FiniteModuleWeights.coroot_normalized H α hss
    (RealRootSpace.cartan_isMaximalToral hss H) ha
  rw [weightReflection_apply hnorm, rootReflectionEquiv_apply, rootReflection,
    map_sub, map_smul, d.extension_root α ha]
  rw [d.coroot_evaluation x α ha, inner_coroot]
  rfl

private def weightWord {v : E H} (s : simple H φ ≃ simpleRoots (realRoots H) v)
    (l : List (simpleRoots (realRoots H) v)) :
    Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H :=
  (l.map (fun a => weightReflection H (s.symm a).val)).prod

private theorem weightWord_on_real {v : E H} (s : simple H φ ≃ simpleRoots (realRoots H) v)
    (hs : ∀ i, d.j (s i : E H) = i.val)
    (hss : IsSemisimple_value ℂ L) (l : List (simpleRoots (realRoots H) v)) (x : E H) :
    weightWord φ s l (d.j x) = d.j (weylWordProduct l x) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha : (s.symm a).val ∈ rootSet_value H := (s.symm a).property.1.1
    have hres : rootRestriction H (s.symm a).val = a.val := by
      apply extension_injective d
      rw [d.extension_root _ ha, ← hs (s.symm a), s.apply_symm_apply]
    simp only [weightWord, List.map_cons, List.prod_cons, LinearEquiv.mul_apply] at ih ⊢
    rw [weylWordProduct_cons, LinearEquiv.mul_apply, ih, reflection_on_real d hss _ ha, hres]

include d in
private theorem rho_pairing_and_weyl_generation (hss : IsSemisimple_value ℂ L)
    (hφ : Regular H φ) :
    (∀ i : simple H φ, rhoValue H φ (coroot_value H i.val) = 1) ∧
    weightWeylGroup H ≤ Subgroup.closure
      (Set.range fun i : simple H φ => weightReflection H i.val) := by
  obtain ⟨v,hv⟩ := direction_vector d φ
  obtain ⟨s,hs⟩ := simple_equiv d φ hv
  have hv' := vector_regular d φ hv hφ
  have hR := d.root_system
  constructor
  · intro i
    have ha : i.val ∈ rootSet_value H := i.property.1.1
    have he : rootRestriction H i.val = (s i : E H) :=
      extension_injective d ((d.extension_root _ ha).trans (hs i).symm)
    rw [← rho_extension φ d hss v hv, d.coroot_evaluation _ _ ha, he,
      rho_simple_coroot_pairing (realRoots H) hR v hv' _ (s i).property]
    norm_num
  · change Subgroup.closure _ ≤ _
    apply (Subgroup.closure_le _).2
    rintro _ ⟨a,ha,rfl⟩
    have hm : rootReflectionEquiv (rootRestriction H a) ∈ rootWeylGroup (realRoots H) :=
      Subgroup.subset_closure ⟨_, ⟨a,ha,rfl⟩, rfl⟩
    obtain ⟨l,hl⟩ := exists_weylWord hR hv' ⟨_, hm⟩
    have hword : weightWord φ s l = weightReflection H a := by
      apply LinearEquiv.toLinearMap_injective
      apply complexification_ext H d
      intro x
      change weightWord φ s l (d.j x) = weightReflection H a (d.j x)
      rw [weightWord_on_real φ d s hs hss, hl, reflection_on_real d hss a ha]
    rw [← hword]
    clear hl hword
    induction l with
    | nil => exact Subgroup.one_mem _
    | cons a l ih =>
      exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨s.symm a,rfl⟩) ih

end RootComparison

section WeylInvariantMap

open private preserved_under_closure from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InvariantRestrictionInjection

open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
open Specs.LieAlgebrasAndRepresentations.RealRootSpace (Realization)

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]

set_option maxHeartbeats 1200000 in
theorem shiftedProjection_mem_invariants
    (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (ht : Function.Bijective (triangular_value H φ)) (z : Subalgebra.center ℂ (U L)) :
    shiftedProjection H φ habel ht z.val ∈ weylInvariants H := by
  let d := RealRootSpace.realization hss H
  letI : Fact (Realization H) := ⟨d⟩
  obtain ⟨hρ, hW⟩ := rho_pairing_and_weyl_generation φ d hss hφ
  let q := shiftedProjection H φ habel ht z.val
  change ∀ w ∈ weightWeylGroup H, ∀ η, evaluation H (w η) q = evaluation H η q
  intro w hw
  have hS : ∀ s ∈ (Set.range fun i : simple H φ => weightReflection H i.val),
      ∀ η, evaluation H (s η) q = evaluation H η q := by
    rintro _ ⟨i,rfl⟩ η
    exact shifted_simple_invariant H φ hss hφ habel ht i (hρ i) z η
  exact preserved_under_closure (f := fun η => evaluation H η q) hS w (hW hw)

/-- Harish–Chandra's homomorphism with the ordinary Weyl invariants as codomain. -/
def hom (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
    (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (ht : Function.Bijective (triangular_value H φ)) :
    Subalgebra.center ℂ (U L) →ₐ[ℂ] weylInvariants H :=
  ((translation H (rhoValue H φ)).comp
    (projectionOnCenter H φ hss hφ habel ht)).codRestrict _
      (shiftedProjection_mem_invariants H φ hss hφ habel ht)

end WeylInvariantMap

section KillingRestriction

open Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection
  (PolynomialFunctions InfinitesimalInvariant infinitesimalInvariants eval restriction)
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
open Specs.LieAlgebrasAndRepresentations.RootForm
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value rootSpace_value)
open private negative_submodule positive_submodule rootSum
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules
open private weightReflection_apply from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.WeightStringsConvexity
open private preserved_under_closure from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.InvariantRestrictionInjection

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
variable (hss : IsSemisimple_value ℂ L)

private def ambientDual : L ≃ₗ[ℂ] Module.Dual ℂ L :=
  (killingForm ℂ L).toDual ((semisimple_iff_killingForm_nondegenerate ℂ L).mp hss)

private def cartanDual : H ≃ₗ[ℂ] Module.Dual ℂ H :=
  ((killingForm ℂ L).restrict H.toSubmodule).toDual
    (killingForm_restrict_toral_nondegenerate hss H (RealRootSpace.cartan_isMaximalToral hss H))

/-- The linear projection onto the Cartan in the triangular decomposition.
It is the Killing-orthogonal projection since opposite root spaces pair and
every nonzero root space is orthogonal to the Cartan. -/
private def cartanProjection : L →ₗ[ℂ] H :=
  (cartanDual H hss).symm.toLinearMap.comp
    (H.toSubmodule.subtype.dualMap.comp (ambientDual hss).toLinearMap)

private theorem cartanProjection_apply (h : H) :
    cartanProjection H hss h = h := by
  apply (cartanDual H hss).injective
  ext k
  change cartanDual H hss ((cartanDual H hss).symm
    (H.toSubmodule.subtype.dualMap (ambientDual hss (h : L)))) k = cartanDual H hss h k
  rw [LinearEquiv.apply_symm_apply]
  rfl

private theorem cartanProjection_rootSpace {α : Module.Dual ℂ H}
    (hα : α ≠ 0) {x : L} (hx : x ∈ rootSpace_value H α) :
    cartanProjection H hss x = 0 := by
  apply (cartanDual H hss).injective
  ext k
  change cartanDual H hss ((cartanDual H hss).symm
    (H.toSubmodule.subtype.dualMap (ambientDual hss x))) k = cartanDual H hss 0 k
  rw [LinearEquiv.apply_symm_apply, map_zero, LinearMap.zero_apply]
  change killingForm ℂ L x (k : L) = 0
  apply rootSpace_killing_orthogonal H α 0 x k hx
  · rw [rootSpace_zero hss H (RealRootSpace.cartan_isMaximalToral hss H)]
    exact k.property
  · simpa using hα

private theorem cartanProjection_rootSum (T : Set ℝ) (hT : (0 : ℝ) ∉ T) :
    rootSum H φ T ≤ LinearMap.ker (cartanProjection H hss) := by
  refine iSup_le fun a x hx => LinearMap.mem_ker.mpr (cartanProjection_rootSpace H hss ?_ hx)
  intro ha
  apply hT
  have hp := a.property
  rwa [ha, map_zero] at hp

private theorem cartanProjection_negative (x : negative_value H φ) :
    cartanProjection H hss (x : L) = 0 := by
  have hx := x.property
  change (x : L) ∈ (negative_value H φ).toSubmodule at hx
  rw [negative_submodule H φ] at hx
  exact cartanProjection_rootSum H φ hss _ (by simp) hx

private theorem cartanProjection_positive (x : positive_value H φ) :
    cartanProjection H hss (x : L) = 0 := by
  have hx := x.property
  change (x : L) ∈ (positive_value H φ).toSubmodule at hx
  rw [positive_submodule H φ] at hx
  exact cartanProjection_rootSum H φ hss _ (by simp) hx

private theorem restriction_eq_symmetricProjection (p : SymmetricAlgebra ℂ L) :
    restriction L H (symmetricEquiv (ambientDual hss) p) =
      symmetricEquiv (cartanDual H hss) (symmetricMap (cartanProjection H hss) p) := by
  have he : (restriction L H).comp (symmetricEquiv (ambientDual hss)).toAlgHom =
      (symmetricEquiv (cartanDual H hss)).toAlgHom.comp (symmetricMap (cartanProjection H hss)) := by
    apply SymmetricAlgebra.algHom_ext
    ext x
    change restriction L H (symmetricEquiv (ambientDual hss) (SymmetricAlgebra.ι ℂ L x)) =
      symmetricEquiv (cartanDual H hss) (symmetricMap (cartanProjection H hss)
        (SymmetricAlgebra.ι ℂ L x))
    simp only [symmetricEquiv_generator, symmetricMap_generator]
    unfold restriction Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.polynomialPullback
    rw [SymmetricAlgebra.lift_ι_apply]
    apply congrArg (SymmetricAlgebra.ι ℂ (Module.Dual ℂ H))
    exact ((cartanDual H hss).apply_symm_apply _).symm
  exact DFunLike.congr_fun he p

private theorem eval_symmetricEquiv (p : SymmetricAlgebra ℂ H) (x : H) :
    eval (symmetricEquiv (cartanDual H hss) p) x = evaluation H (cartanDual H hss x) p := by
  open Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection in
  have he : ((Pi.evalAlgHom ℂ (fun _ : H => ℂ) x).comp (polynomialEvaluation H)).comp
        (symmetricEquiv (cartanDual H hss)).toAlgHom = evaluation H (cartanDual H hss x) := by
    apply SymmetricAlgebra.algHom_ext
    ext h
    change eval (symmetricEquiv (cartanDual H hss) (SymmetricAlgebra.ι ℂ H h)) x =
      evaluation H (cartanDual H hss x) (SymmetricAlgebra.ι ℂ H h)
    rw [symmetricEquiv_generator, InvariantRestrictionInjection.eval_ι, evaluation_generator]
    exact killingForm_symmetric ℂ L h.val x.val
  exact DFunLike.congr_fun he p

private theorem cartanDual_reflection (α : Module.Dual ℂ H) (hα : α (coroot_value H α) = 2)
    (x : H) :
    cartanDual H hss (Module.reflection (x := coroot_value H α) (f := α) hα x) =
      weightReflection H α (cartanDual H hss x) := by
  rw [Module.reflection_apply _ hα, weightReflection_apply hα, map_sub, map_smul]
  have hcor (y : H) : cartanDual H hss (coroot_value H α) y =
      (2 / rootForm_value H α α) * α y := by
    change killingForm ℂ L (coroot_value H α : L) y.val = _
    rw [coroot_value, Submodule.coe_smul, map_smul, LinearMap.smul_apply, smul_eq_mul,
      tAlpha_pairing hss H (RealRootSpace.cartan_isMaximalToral hss H)]
  ext y
  have hh : cartanDual H hss x (coroot_value H α) =
      cartanDual H hss (coroot_value H α) x := killingForm_symmetric ℂ L _ _
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hh, hcor x, hcor y]
  ring

private theorem symmetric_weyl_iff (p : SymmetricAlgebra ℂ H) :
    p ∈ weylInvariants H ↔
      symmetricEquiv (cartanDual H hss) p ∈
        Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.weylInvariants L H := by
  change (∀ w ∈ weightWeylGroup H, ∀ x, evaluation H (w x) p = evaluation H x p) ↔
    ∀ w ∈ Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.weylGroup L H, ∀ x,
      eval (symmetricEquiv (cartanDual H hss) p) (w x) =
        eval (symmetricEquiv (cartanDual H hss) p) x
  have hnorm (α : Module.Dual ℂ H) (ha : α ∈ rootSet_value H) :
      α (coroot_value H α) = 2 := FiniteModuleWeights.coroot_normalized H α hss
    (RealRootSpace.cartan_isMaximalToral hss H) ha
  constructor
  · intro hp
    apply preserved_under_closure (f := fun x => eval (symmetricEquiv (cartanDual H hss) p) x)
    rintro w ⟨α,ha,hw⟩ x
    have hw' : w x = Module.reflection (x := coroot_value H α) (f := α) (hnorm α ha) x :=
      (hw x).trans (Module.reflection_apply x (hnorm α ha)).symm
    rw [eval_symmetricEquiv H hss, eval_symmetricEquiv H hss, hw', cartanDual_reflection H hss]
    exact hp _ (Subgroup.subset_closure ⟨α,ha,rfl⟩) _
  · intro hp
    apply preserved_under_closure (f := fun η => evaluation H η p)
    rintro _ ⟨α,ha,rfl⟩ η
    obtain ⟨x,rfl⟩ := (cartanDual H hss).surjective η
    rw [← cartanDual_reflection H hss α (hnorm α ha),
      ← eval_symmetricEquiv H hss, ← eval_symmetricEquiv H hss]
    exact hp _ (Subgroup.subset_closure ⟨α,ha,fun y => Module.reflection_apply y (hnorm α ha)⟩) x

end KillingRestriction

section AdjointRestriction

open Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection
  (PolynomialFunctions InfinitesimalInvariant infinitesimalInvariants eval restriction)
open Symmetrization (symmetricAdjoint symmetricAdjoint_generator symmetric_derivation_ext HasFormula)

variable [FiniteDimensional ℂ L]
variable (hss : IsSemisimple_value ℂ L)

private def adjointInvariants : Submodule ℂ (SymmetricAlgebra ℂ L) :=
  ⨅ x : L, (symmetricAdjoint (k := ℂ) (g := L) x).toLinearMap.ker

private theorem mem_adjointInvariants (p : SymmetricAlgebra ℂ L) :
    p ∈ adjointInvariants (L := L) ↔ ∀ x : L, symmetricAdjoint (k := ℂ) x p = 0 := by
  simp only [adjointInvariants, Submodule.mem_iInf, LinearMap.mem_ker]
  rfl

private theorem hasDerivAt_symmetricAdjoint (p : SymmetricAlgebra ℂ L) (x y : L) :
    HasDerivAt (fun t : ℂ => eval (symmetricEquiv (ambientDual hss) p) (y + t • ⁅x, y⁆))
      (-eval (symmetricEquiv (ambientDual hss) (symmetricAdjoint (k := ℂ) x p)) y) 0 := by
  induction p using SymmetricAlgebra.induction with
  | algebraMap c =>
    simpa [Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.eval] using
      hasDerivAt_const (0 : ℂ) c
  | ι z =>
    simp only [symmetricAdjoint_generator, symmetricEquiv_generator, InvariantRestrictionInjection.eval_ι]
    have hk : ambientDual hss z ⁅x, y⁆ = -ambientDual hss ⁅x, z⁆ y := by
      change killingForm ℂ L z ⁅x, y⁆ = -killingForm ℂ L ⁅x, z⁆ y
      rw [← killingForm_invariant ℂ L z x y, ← lie_skew x z, map_neg, LinearMap.neg_apply, neg_neg]
    simp only [map_add, map_smul, smul_eq_mul, ← hk]
    simpa using (((hasDerivAt_id' (0 : ℂ)).mul_const (ambientDual hss z ⁅x,y⁆)).const_add
      (ambientDual hss z y))
  | add p q hp hq =>
    convert hp.add hq using 1
    · funext t
      simp [Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.eval, Pi.add_apply]
    · simp [Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.eval, add_comm]
  | mul p q hp hq =>
    convert hp.mul hq using 1
    · funext t
      simp [Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.eval, Pi.mul_apply]
    · simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul,
        Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.eval,
        Pi.add_apply, Pi.mul_apply, zero_smul, add_zero]
      ring

private theorem symmetric_adjoint_iff (p : SymmetricAlgebra ℂ L) :
    p ∈ adjointInvariants (L := L) ↔ InfinitesimalInvariant L (symmetricEquiv (ambientDual hss) p) := by
  rw [mem_adjointInvariants]
  constructor
  · intro hp x y
    simpa [hp x, Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.eval] using
      hasDerivAt_symmetricAdjoint hss p x y
  · intro hp x
    apply (symmetricEquiv (ambientDual hss)).injective
    apply InvariantRestrictionInjection.evaluation_injective
    funext y
    have he := (hasDerivAt_symmetricAdjoint hss p x y).unique (hp x y)
    simpa [Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.eval] using neg_eq_zero.mp he

variable [H.IsCartanSubalgebra]

private theorem symmetric_restriction_bijective
    (ce : infinitesimalInvariants L ≃ₐ[ℂ]
      Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.weylInvariants L H)
    (hce : ∀ p, (ce p).val = restriction L H p.val) :
    (∀ p : adjointInvariants (L := L), symmetricMap (cartanProjection H hss) p.val ∈ weylInvariants H) ∧
    (∀ p q : adjointInvariants (L := L),
      symmetricMap (cartanProjection H hss) p.val =
        symmetricMap (cartanProjection H hss) q.val → p = q) ∧
    ∀ q : weylInvariants H, ∃ p : adjointInvariants (L := L),
      symmetricMap (cartanProjection H hss) p.val = q.val := by
  let transport (p : adjointInvariants (L := L)) : infinitesimalInvariants L :=
    ⟨symmetricEquiv (ambientDual hss) p.val, (symmetric_adjoint_iff hss p.val).1 p.property⟩
  have ht (p : adjointInvariants (L := L)) :
      (ce (transport p)).val =
        symmetricEquiv (cartanDual H hss) (symmetricMap (cartanProjection H hss) p.val) := by
    rw [hce]
    exact restriction_eq_symmetricProjection H hss p.val
  refine ⟨?_, ?_, ?_⟩
  · intro p
    apply (symmetric_weyl_iff H hss _).2
    rw [← ht]
    exact (ce (transport p)).property
  · intro p q hpq
    apply Subtype.ext
    apply (symmetricEquiv (ambientDual hss)).injective
    have he : ce (transport p) = ce (transport q) := Subtype.ext (by rw [ht, ht, hpq])
    exact congrArg Subtype.val (ce.injective he)
  · intro q
    let q' : Specs.LieAlgebrasAndRepresentations.InvariantRestrictionInjection.weylInvariants L H :=
      ⟨symmetricEquiv (cartanDual H hss) q.val, (symmetric_weyl_iff H hss q.val).1 q.property⟩
    let p' := ce.symm q'
    let p := (symmetricEquiv (ambientDual hss)).symm p'.val
    have hp : symmetricEquiv (ambientDual hss) p = p'.val := AlgEquiv.apply_symm_apply _ _
    have hp' : p ∈ adjointInvariants (L := L) :=
      (symmetric_adjoint_iff hss p).2 (hp ▸ p'.property)
    refine ⟨⟨p,hp'⟩, ?_⟩
    apply (symmetricEquiv (cartanDual H hss)).injective
    rw [← ht]
    have he : transport ⟨p,hp'⟩ = p' := Subtype.ext hp
    rw [he]
    exact congrArg Subtype.val (ce.apply_symm_apply q')

/-- Symmetrization identifies the invariant subspace of (S(L)) with the
center of the enveloping algebra. -/
private theorem symmetrization_mem_center_iff
    (s : SymmetricAlgebra ℂ L ≃ₗ[ℂ] U L) (hs : HasFormula s.toLinearMap)
    (p : SymmetricAlgebra ℂ L) : s p ∈ Subalgebra.center ℂ (U L) ↔
      p ∈ adjointInvariants (L := L) := by
  obtain ⟨D, hD, hsD⟩ := Symmetrization.formula_adjoint s.toLinearMap hs
  have hD' (x : L) : D x = symmetricAdjoint (k := ℂ) x :=
    symmetric_derivation_ext _ _ (fun y => (hD x y).trans (symmetricAdjoint_generator x y).symm)
  rw [mem_adjointInvariants, Subalgebra.mem_center_iff]
  constructor
  · intro hz x
    apply s.injective
    rw [← hD', map_zero]
    change s.toLinearMap (D x p) = 0
    rw [hsD]
    exact sub_eq_zero.mpr (hz _)
  · intro hp z
    change Commute z (s p)
    induction z using Shared.Lie.enveloping_induction ℂ L with
    | scalar c => exact Algebra.commute_algebraMap_left c _
    | generator x =>
      have h := hsD x p
      rw [hD', hp x, map_zero] at h
      exact sub_eq_zero.mp h.symm
    | mul a b ha hb => exact ha.mul_left hb
    | add a b ha hb => exact ha.add_left hb

end AdjointRestriction

section AssociatedGraded

open _root_.Shared.Lie (word filtration filtration_mono)
open _root_.Shared.Lie.PBW
open _root_.Shared.Lie.PBW.Graded (symmetricWord symmetricDegree)
open Symmetrization (HasFormula symmetricFiltration)
open private orderedComparison orderedComparison_symm orderedComparison_symm_filtered formula_lowers lowering_bijective
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Symmetrization
open private joinWords joinWords_bijective leftLetter rightLetter borelEquiv negative_borel_isCompl
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.VermaModules

private theorem symmetricFiltration_mono {K : Type u} [LieRing K] [LieAlgebra ℂ K] :
    Monotone (symmetricFiltration (k := ℂ) (g := K)) := by
  intro a b hab
  refine Submodule.span_mono ?_
  rintro _ ⟨xs,hxs,rfl⟩
  exact ⟨xs,hxs.trans hab,rfl⟩

private theorem symmetricMap_word {A B : Type u} [LieRing A] [LieAlgebra ℂ A]
    [LieRing B] [LieAlgebra ℂ B] (f : A →ₗ[ℂ] B) (xs : List A) :
    symmetricMap f (symmetricWord (k := ℂ) xs) = symmetricWord (xs.map f) := by
  simp [symmetricWord, map_list_prod, List.map_map, Function.comp_def]

private theorem symmetricMap_filtered {A B : Type u} [LieRing A] [LieAlgebra ℂ A]
    [LieRing B] [LieAlgebra ℂ B] (f : A →ₗ[ℂ] B) (m : ℤ) :
    symmetricFiltration m ≤ (symmetricFiltration m).comap (symmetricMap f).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨xs,hxs,rfl⟩
  change symmetricMap f (symmetricWord xs) ∈ symmetricFiltration m
  rw [symmetricMap_word]
  exact Submodule.subset_span ⟨xs.map f, by simpa, rfl⟩

private theorem envelopingMap_word {A B : Type u} [LieRing A] [LieAlgebra ℂ A]
    [LieRing B] [LieAlgebra ℂ B] (f : A →ₗ⁅ℂ⁆ B) (xs : List A) :
    envelopingMap f (word ℂ A xs) = word ℂ B (xs.map f) := by
  induction xs with
  | nil => exact map_one _
  | cons x xs ih =>
    change envelopingMap f (ι ℂ x * word ℂ A xs) =
      ι ℂ (f x) * word ℂ B (xs.map f)
    rw [map_mul, envelopingMap_ι, ih]

private theorem cartanToSymmetric_word (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (xs : List H) :
    cartanToSymmetric H habel (word ℂ H xs) = symmetricWord xs := by
  induction xs with
  | nil => exact map_one _
  | cons h xs ih =>
    change cartanToSymmetric H habel (ι ℂ h * word ℂ H xs) =
      SymmetricAlgebra.ι ℂ H h * symmetricWord xs
    rw [map_mul, cartan_generator, ih]

private theorem augmentation_word_cons {K : Type u} [LieRing K] [LieAlgebra ℂ K]
    (x : K) (s : List K) :
    Shared.Lie.augmentation ℂ K (word ℂ K (x :: s)) = 0 := by
  have hx : Shared.Lie.augmentation ℂ K (ι ℂ x) = 0 :=
    UniversalEnvelopingAlgebra.lift_ι_apply ℂ (0 : K →ₗ⁅ℂ⁆ ℂ) x
  change Shared.Lie.augmentation ℂ K (ι ℂ x * word ℂ K s) = 0
  rw [map_mul, hx, zero_mul]

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
variable (hss : IsSemisimple_value ℂ L)

private theorem projection_ordered_product (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (ht : Function.Bijective (triangular_value H φ))
    (xs : List (negative_value H φ)) (ys : List H) (zs : List (positive_value H φ)) :
    projectionValue H φ habel ht
      (word ℂ L (xs.map Subtype.val ++ ys.map Subtype.val ++ zs.map Subtype.val)) =
      symmetricMap (cartanProjection H hss)
        (symmetricWord (xs.map Subtype.val ++ ys.map Subtype.val ++ zs.map Subtype.val)) := by
  have hn : envelopingMap (negative_value H φ).incl (word ℂ _ xs) =
      word ℂ L (xs.map Subtype.val) := envelopingMap_word _ _
  have hc : envelopingMap H.incl (word ℂ _ ys) =
      word ℂ L (ys.map Subtype.val) := envelopingMap_word _ _
  have hp : envelopingMap (positive_value H φ).incl (word ℂ _ zs) =
      word ℂ L (zs.map Subtype.val) := envelopingMap_word _ _
  rw [Shared.Lie.word_append, Shared.Lie.word_append, ← hn, ← hc, ← hp, projection_triangular,
    cartanToSymmetric_word, symmetricMap_word]
  have hy : ys.map (fun y : H => cartanProjection H hss y.val) = ys := by
    simp [cartanProjection_apply H hss]
  cases xs with
  | nil =>
    cases zs with
    | nil =>
      change (Shared.Lie.augmentation ℂ _ 1 * Shared.Lie.augmentation ℂ _ 1) • symmetricWord ys =
        symmetricWord ((([] ++ ys.map Subtype.val) ++ []).map (cartanProjection H hss))
      rw [List.nil_append, List.append_nil, List.map_map]
      change (Shared.Lie.augmentation ℂ _ 1 * Shared.Lie.augmentation ℂ _ 1) • symmetricWord ys =
        symmetricWord (ys.map (fun y : H => cartanProjection H hss y.val))
      rw [hy, map_one, map_one, one_mul, one_smul]
    | cons z zs =>
      rw [augmentation_word_cons]
      simp [symmetricWord, List.map_map, Function.comp_def, cartanProjection_apply H hss,
        cartanProjection_positive H φ hss, Shared.Lie.word]
  | cons x xs =>
    rw [augmentation_word_cons]
    simp [symmetricWord, List.map_map, Function.comp_def, cartanProjection_negative H φ hss]

private theorem projection_is_filtered_and_symbol
    (hφ : Regular H φ) (habel : ∀ a b : H, ⁅a, b⁆ = 0)
    (ht : Function.Bijective (triangular_value H φ))
    (s : SymmetricAlgebra ℂ L ≃ₗ[ℂ] U L) (hs : HasFormula s.toLinearMap) :
    (∀ m : ℤ, filtration ℂ L m ≤
      (symmetricFiltration m).comap (projectionValue H φ habel ht)) ∧
    (∀ (m : ℤ) (p : SymmetricAlgebra ℂ L), p ∈ symmetricFiltration m →
      projectionValue H φ habel ht (s p) - symmetricMap (cartanProjection H hss) p ∈
        symmetricFiltration (m - 1)) := by
  classical
  let N := negative_value H φ
  let P := positive_value H φ
  let I := Module.Free.ChooseBasisIndex ℂ N
  let J := Module.Free.ChooseBasisIndex ℂ H
  let K := Module.Free.ChooseBasisIndex ℂ P
  let : LinearOrder I := WellOrderingRel.isWellOrder.linearOrder
  let : LinearOrder J := WellOrderingRel.isWellOrder.linearOrder
  let : LinearOrder K := WellOrderingRel.isWellOrder.linearOrder
  let n := Module.Free.chooseBasis ℂ N
  let h := Module.Free.chooseBasis ℂ H
  let p := Module.Free.chooseBasis ℂ P
  let hm := RealRootSpace.cartan_isMaximalToral hss H
  let E := borelEquiv H φ hss hm hφ
  let F := Submodule.prodEquivOfIsCompl _ _ (negative_borel_isCompl H φ hss hm hφ)
  let b₀ : Module.Basis (J ⊕ₗ K) ℂ (borel_value H φ) :=
    ((h.prod p).map E).reindex (toLex : (J ⊕ K) ≃ _)
  let b : Module.Basis (I ⊕ₗ (J ⊕ₗ K)) ℂ L :=
    ((n.prod b₀).map F).reindex (toLex : (I ⊕ (J ⊕ₗ K)) ≃ _)
  have hbN (i : I) : b (leftLetter i) = (n i : L) := by
    simp [b, leftLetter, Module.Basis.prod_apply]
    change (n i : L) + ((0 : borel_value H φ) : L) = _
    simp
  have hbH (j : J) : b (rightLetter (leftLetter j)) = (h j : L) := by
    simp [b, b₀, leftLetter, rightLetter, Module.Basis.prod_apply]
    change (0 : L) + (((cartanIn H φ (h j) + positiveIn H φ 0 : borel_value H φ)) : L) = _
    simp <;> rfl
  have hbP (k : K) : b (rightLetter (rightLetter k)) = (p k : L) := by
    simp [b, b₀, rightLetter, Module.Basis.prod_apply]
    change (0 : L) + (((cartanIn H φ 0 + positiveIn H φ (p k) : borel_value H φ)) : L) = _
    simp <;> rfl
  let R := orderedComparison b
  let pr := projectionValue H φ habel ht
  let res := symmetricMap (cartanProjection H hss)
  have hpr : pr = res.toLinearMap.comp R.symm.toLinearMap := by
    apply (orderedBasis b).ext
    intro l
    change pr ((orderedBasis b) l) = res (R.symm ((orderedBasis b) l))
    rw [orderedBasis_apply, show R.symm (orderedMonomial b l) = symmetricWord (l.val.map b)
      from orderedComparison_symm b l]
    obtain ⟨⟨lN,lB⟩,rfl⟩ := joinWords_bijective.2 l
    obtain ⟨⟨lH,lP⟩,rfl⟩ := joinWords_bijective.2 lB
    have hl : ((joinWords (lN, joinWords (lH,lP))).val.map b) =
        (lN.val.map n).map Subtype.val ++ (lH.val.map h).map Subtype.val ++
          (lP.val.map p).map Subtype.val := by
      simp [joinWords, List.map_map, Function.comp_def, List.append_assoc, hbN, hbH, hbP] <;> rfl
    change pr (word ℂ L _) = res (symmetricWord _)
    rw [hl]
    exact projection_ordered_product H φ hss habel ht _ _ _
  have hfiltered (m : ℤ) :
      filtration ℂ L m ≤ (symmetricFiltration m).comap pr := by
    intro a ha
    rw [hpr]
    exact symmetricMap_filtered (cartanProjection H hss) m
      (orderedComparison_symm_filtered b m ha)
  refine ⟨hfiltered, ?_⟩
  intro m q hq
  have ha : R q ∈ filtration ℂ L m := by
    let T := s.toLinearMap.comp R.symm.toLinearMap
    obtain ⟨_, hT⟩ := lowering_bijective T (fun m a ha => formula_lowers b s.toLinearMap hs m ha)
    obtain ⟨z,hz,he⟩ := hT m (s q) (Symmetrization.formula_filtered s.toLinearMap hs m hq)
    have hh : z = R q := by
      apply R.symm.injective
      rw [R.symm_apply_apply]
      exact s.injective he
    exact hh ▸ hz
  have hd := formula_lowers b s.toLinearMap hs m ha
  rw [show (orderedComparison b).symm (R q) = q from R.symm_apply_apply q] at hd
  have ht' := hfiltered (m - 1) hd
  change pr (s q - R q) ∈ symmetricFiltration (m - 1) at ht'
  have hRq : pr (R q) = res q := by rw [hpr]; simp
  rwa [map_sub, hRq] at ht'

end AssociatedGraded

section HomogeneousParts

open _root_.Shared.Lie.PBW.Graded
open Symmetrization (symmetricFiltration symmetricAdjoint symmetricAdjoint_generator)
open scoped DirectSum

variable {K J : Type u} [LieRing K] [LieAlgebra ℂ K] [LieRing J] [LieAlgebra ℂ J]
variable [Fact (Specs.Shared.Lie.filtrationType ℂ K)] [Fact (Specs.Shared.Lie.filtrationType ℂ J)]

private def symmetricGrading (K : Type u) [LieRing K] [LieAlgebra ℂ K]
    [Fact (Specs.Shared.Lie.filtrationType ℂ K)] :
    SymmetricAlgebra ℂ K ≃ₗ[ℂ] Associated ℂ K :=
  LinearEquiv.ofBijective (canonicalMap (k := ℂ) (g := K)).toLinearMap canonicalMap_bijective

private def homogeneousPart (K : Type u) [LieRing K] [LieAlgebra ℂ K]
    [Fact (Specs.Shared.Lie.filtrationType ℂ K)] (n : ℕ) :
    SymmetricAlgebra ℂ K →ₗ[ℂ] SymmetricAlgebra ℂ K :=
  (symmetricGrading K).symm.toLinearMap.comp
    ((DirectSum.lof ℂ ℕ (Piece ℂ K) n).comp
      ((DirectSum.component ℂ ℕ (Piece ℂ K) n).comp (symmetricGrading K).toLinearMap))

private theorem symmetricGrading_degree (n : ℕ) :
    Submodule.map (symmetricGrading K).toLinearMap (symmetricDegree n) =
      LinearMap.range (DirectSum.lof ℂ ℕ (Piece ℂ K) n) := by
  classical
  let I := Module.Free.ChooseBasisIndex ℂ K
  let : LinearOrder I := WellOrderingRel.isWellOrder.linearOrder
  exact canonicalMap_degree (Module.Free.chooseBasis ℂ K) n

private theorem homogeneousPart_mem (n : ℕ) (a : SymmetricAlgebra ℂ K) :
    homogeneousPart K n a ∈ symmetricDegree n := by
  have h : (symmetricGrading K) (homogeneousPart K n a) ∈
      LinearMap.range (DirectSum.lof ℂ ℕ (Piece ℂ K) n) := by
    refine ⟨(symmetricGrading K a) n, ?_⟩
    simp only [homogeneousPart, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rfl
  rw [← symmetricGrading_degree] at h
  rcases h with ⟨b,hb,he⟩
  exact ((symmetricGrading K).injective he) ▸ hb

private theorem homogeneousPart_of_degree {n : ℕ} {a : SymmetricAlgebra ℂ K}
    (ha : a ∈ symmetricDegree n) (i : ℕ) :
    homogeneousPart K i a = if i = n then a else 0 := by
  have h : (symmetricGrading K) a ∈ (symmetricDegree n).map (symmetricGrading K).toLinearMap :=
    Submodule.mem_map_of_mem ha
  rw [symmetricGrading_degree] at h
  obtain ⟨b,hb⟩ := h
  by_cases he : i = n
  · subst i
    rw [if_pos rfl]
    change (symmetricGrading K).symm (DirectSum.lof ℂ ℕ (Piece ℂ K) n
      (DirectSum.component ℂ ℕ (Piece ℂ K) n (symmetricGrading K a))) = a
    rw [← hb, DirectSum.component.lof_self, hb, LinearEquiv.symm_apply_apply]
  · rw [if_neg he]
    change (symmetricGrading K).symm (DirectSum.lof ℂ ℕ (Piece ℂ K) i
      (DirectSum.component ℂ ℕ (Piece ℂ K) i (symmetricGrading K a))) = 0
    rw [← hb, DirectSum.component.of, dif_neg (Ne.symm he), map_zero, map_zero]

private theorem homogeneousPart_sum (a : SymmetricAlgebra ℂ K) :
    ∃ S : Finset ℕ, (∑ n ∈ S, homogeneousPart K n a) = a := by
  classical
  refine ⟨(symmetricGrading K a).support, ?_⟩
  apply (symmetricGrading K).injective
  simp only [map_sum, homogeneousPart, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, DirectSum.lof_eq_of]
  exact DirectSum.sum_support_of _

private theorem symmetricFiltration_iff (m : ℤ) (a : SymmetricAlgebra ℂ K) :
    a ∈ symmetricFiltration m ↔ ∀ n : ℕ, m < n → homogeneousPart K n a = 0 := by
  classical
  constructor
  · intro ha n hn
    refine (Submodule.span_le.mpr ?_ : symmetricFiltration m ≤ (homogeneousPart K n).ker) ha
    rintro _ ⟨xs,hlen,rfl⟩
    have hd : symmetricWord xs ∈ symmetricDegree (k := ℂ) (g := K) xs.length :=
      Submodule.subset_span ⟨xs,rfl,rfl⟩
    change homogeneousPart K n (symmetricWord xs) = 0
    rw [homogeneousPart_of_degree hd, if_neg (by omega)]
  · intro ha
    obtain ⟨S,hS⟩ := homogeneousPart_sum a
    rw [← hS]
    apply Submodule.sum_mem
    intro n hn
    by_cases hd : m < (n : ℤ)
    · rw [ha n hd]
      exact Submodule.zero_mem _
    · exact (Submodule.span_mono (by
        rintro _ ⟨xs,hxs,rfl⟩
        exact ⟨xs,by omega,rfl⟩) :
        symmetricDegree (k := ℂ) (g := K) n ≤ symmetricFiltration m) (homogeneousPart_mem n a)

private theorem homogeneousPart_natural (f : SymmetricAlgebra ℂ K →ₗ[ℂ] SymmetricAlgebra ℂ J)
    (hf : ∀ n, symmetricDegree n ≤ (symmetricDegree n).comap f)
    (i : ℕ) (a : SymmetricAlgebra ℂ K) :
    homogeneousPart J i (f a) = f (homogeneousPart K i a) := by
  classical
  obtain ⟨S,hS⟩ := homogeneousPart_sum a
  calc
    _ = ∑ n ∈ S, homogeneousPart J i (f (homogeneousPart K n a)) := by
      rw [← map_sum, ← map_sum, hS]
    _ = ∑ n ∈ S, f (homogeneousPart K i (homogeneousPart K n a)) := ?_
    _ = _ := by rw [← map_sum, ← map_sum, hS]
  apply Finset.sum_congr rfl
  intro n hn
  rw [homogeneousPart_of_degree (hf n (homogeneousPart_mem n a)),
    homogeneousPart_of_degree (homogeneousPart_mem n a)]
  split <;> simp

omit [Fact (Specs.Shared.Lie.filtrationType ℂ K)] [Fact (Specs.Shared.Lie.filtrationType ℂ J)] in
private theorem symmetricMap_homogeneous (f : K →ₗ[ℂ] J) (n : ℕ) :
    symmetricDegree n ≤ (symmetricDegree n).comap (symmetricMap f).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨xs,hlen,rfl⟩
  change symmetricMap f (symmetricWord xs) ∈ symmetricDegree n
  rw [symmetricMap_word]
  exact Submodule.subset_span ⟨xs.map f,by simpa,rfl⟩

omit [Fact (Specs.Shared.Lie.filtrationType ℂ K)] in
private theorem generator_mul_homogeneous (x : K) {n : ℕ} {p : SymmetricAlgebra ℂ K}
    (hp : p ∈ symmetricDegree n) :
    SymmetricAlgebra.ι ℂ K x * p ∈ symmetricDegree (n + 1) := by
  refine (Submodule.span_le.mpr ?_ : symmetricDegree n ≤
    (symmetricDegree (n+1)).comap
      (LinearMap.mulLeft ℂ (SymmetricAlgebra.ι ℂ K x))) hp
  rintro _ ⟨xs,hlen,rfl⟩
  exact Submodule.subset_span ⟨x :: xs, by simp [hlen], rfl⟩

omit [Fact (Specs.Shared.Lie.filtrationType ℂ K)] in
private theorem adjoint_homogeneous (x : K) (n : ℕ) :
    symmetricDegree n ≤ (symmetricDegree n).comap (symmetricAdjoint (k := ℂ) x).toLinearMap := by
  apply Submodule.span_le.mpr
  rintro _ ⟨xs,rfl,rfl⟩
  change symmetricAdjoint (k := ℂ) x (symmetricWord xs) ∈ symmetricDegree xs.length
  induction xs with
  | nil =>
    simpa [symmetricWord] using (symmetricDegree (k := ℂ) (g := K) 0).zero_mem
  | cons y xs ih =>
    change symmetricAdjoint (k := ℂ) x (SymmetricAlgebra.ι ℂ K y * symmetricWord xs) ∈
      symmetricDegree (xs.length + 1)
    rw [Derivation.leibniz, symmetricAdjoint_generator, smul_eq_mul, smul_eq_mul, mul_comm (symmetricWord xs)]
    exact Submodule.add_mem _
      (generator_mul_homogeneous y ih)
      (generator_mul_homogeneous ⁅x,y⁆ (Submodule.subset_span ⟨xs,rfl,rfl⟩))

private theorem restriction_inverse_filtered [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
    [Fact (Specs.Shared.Lie.filtrationType ℂ H)] [Fact (Specs.Shared.Lie.filtrationType ℂ L)]
    (hss : IsSemisimple_value ℂ L)
    (hinj : ∀ p q : adjointInvariants (L := L),
      symmetricMap (cartanProjection H hss) p.val =
        symmetricMap (cartanProjection H hss) q.val → p = q)
    (m : ℤ) (p : adjointInvariants (L := L))
    (hp : symmetricMap (cartanProjection H hss) p.val ∈ symmetricFiltration m) :
    p.val ∈ symmetricFiltration m := by
  rw [symmetricFiltration_iff] at hp ⊢
  intro n hn
  have hI : homogeneousPart L n p.val ∈ adjointInvariants (L := L) := by
    rw [mem_adjointInvariants]
    intro x
    have h := (mem_adjointInvariants p.val).1 p.property x
    have he := homogeneousPart_natural (symmetricAdjoint (k := ℂ) x).toLinearMap
      (adjoint_homogeneous x) n p.val
    rw [show (symmetricAdjoint (k := ℂ) x).toLinearMap p.val = 0 from h, map_zero] at he
    exact he.symm
  have hz : (symmetricMap (cartanProjection H hss)) (homogeneousPart L n p.val) = 0 := by
    have he := homogeneousPart_natural (symmetricMap (cartanProjection H hss)).toLinearMap
      (symmetricMap_homogeneous (cartanProjection H hss)) n p.val
    exact he.symm.trans (hp n hn)
  have h := hinj ⟨_,hI⟩ 0 (by simpa using hz)
  exact congrArg Subtype.val h

end HomogeneousParts

section DegreeLowering

open _root_.Shared.Lie (filtration filtration_mono filtration_properties)
open _root_.Shared.Lie.PBW.Graded (symmetricWord)
open Symmetrization (symmetricFiltration HasFormula)

private theorem symmetricFiltration_eq_bot_of_neg {K : Type u} [LieRing K] [LieAlgebra ℂ K]
    (m : ℤ) (hm : m < 0) : symmetricFiltration (k := ℂ) (g := K) m = ⊥ := by
  apply le_antisymm _ bot_le
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨xs,hlen,rfl⟩
  omega

private theorem generator_mul_filtered {K : Type u} [LieRing K] [LieAlgebra ℂ K]
    (x : K) (m : ℤ) {p : SymmetricAlgebra ℂ K} (hp : p ∈ symmetricFiltration m) :
    SymmetricAlgebra.ι ℂ K x * p ∈ symmetricFiltration (m + 1) := by
  refine (Submodule.span_le.mpr ?_ : symmetricFiltration m ≤
    (symmetricFiltration (m + 1)).comap (LinearMap.mulLeft ℂ (SymmetricAlgebra.ι ℂ K x))) hp
  rintro _ ⟨xs,hlen,rfl⟩
  exact Submodule.subset_span ⟨x :: xs, by simp; omega, rfl⟩

private theorem translation_generator (δ : Module.Dual ℂ H) (x : H) :
    translation H δ (SymmetricAlgebra.ι ℂ H x) =
      SymmetricAlgebra.ι ℂ H x - algebraMap ℂ (SymmetricAlgebra ℂ H) (δ x) := by
  rw [translation, SymmetricAlgebra.lift_ι_apply]
  rfl

private theorem translation_word_lowers (δ : Module.Dual ℂ H) (xs : List H) :
    translation H δ (symmetricWord xs) - symmetricWord xs ∈
      symmetricFiltration ((xs.length : ℤ) - 1) := by
  induction xs with
  | nil => simp [symmetricWord]
  | cons x xs ih =>
    let w : SymmetricAlgebra ℂ H := symmetricWord xs
    have hw : w ∈ symmetricFiltration (xs.length : ℤ) :=
      Submodule.subset_span ⟨xs,le_rfl,rfl⟩
    have hd : translation H δ w ∈ symmetricFiltration (xs.length : ℤ) := by
      have hh := (symmetricFiltration (xs.length : ℤ)).add_mem
        (symmetricFiltration_mono (by omega) ih) hw
      simpa only [w, sub_add_cancel] using hh
    have he : translation H δ (symmetricWord (x :: xs)) - symmetricWord (x :: xs) =
        SymmetricAlgebra.ι ℂ H x * (translation H δ w - w) - δ x • translation H δ w := by
      change translation H δ (SymmetricAlgebra.ι ℂ H x * w) -
        SymmetricAlgebra.ι ℂ H x * w = _
      rw [map_mul, translation_generator, Algebra.smul_def]
      ring
    rw [he]
    have hm := generator_mul_filtered x ((xs.length : ℤ) - 1) ih
    have hcast : (↑(x :: xs).length : ℤ) - 1 = xs.length := by simp
    rw [hcast]
    exact (symmetricFiltration _).sub_mem (by simpa using hm)
      ((symmetricFiltration _).smul_mem _ hd)

private theorem translation_lowers (δ : Module.Dual ℂ H) (m : ℤ)
    (p : SymmetricAlgebra ℂ H) (hp : p ∈ symmetricFiltration m) :
    translation H δ p - p ∈ symmetricFiltration (m - 1) := by
  refine (Submodule.span_le.mpr ?_ : symmetricFiltration m ≤
    (symmetricFiltration (m-1)).comap
      ((translation H δ).toLinearMap - LinearMap.id)) hp
  rintro _ ⟨xs,hlen,rfl⟩
  exact symmetricFiltration_mono (by omega) (translation_word_lowers H δ xs)

variable [FiniteDimensional ℂ L] [H.IsCartanSubalgebra]
variable (hss : IsSemisimple_value ℂ L) (hφ : Regular H φ)
variable (habel : ∀ a b : H, ⁅a, b⁆ = 0)
variable (ht : Function.Bijective (triangular_value H φ))

include hφ in
private theorem gamma_symbol (s : SymmetricAlgebra ℂ L ≃ₗ[ℂ] U L)
    (hs : HasFormula s.toLinearMap) (m : ℤ) (p : SymmetricAlgebra ℂ L)
    (hp : p ∈ symmetricFiltration m) :
    shiftedProjection H φ habel ht (s p) - symmetricMap (cartanProjection H hss) p ∈
      symmetricFiltration (m - 1) := by
  obtain ⟨hf, hsym⟩ := projection_is_filtered_and_symbol H φ hss hφ habel ht s hs
  let p₀ := projectionValue H φ habel ht (s p)
  have hp₀ : p₀ ∈ symmetricFiltration m := hf m
    (Symmetrization.formula_filtered s.toLinearMap hs m hp)
  have ha := translation_lowers H (rhoValue H φ) m p₀ hp₀
  have hb := hsym m p hp
  have hab := (symmetricFiltration (m - 1)).add_mem ha hb
  change translation H (rhoValue H φ) p₀ - p₀ +
    (p₀ - symmetricMap (cartanProjection H hss) p) ∈ _ at hab
  rw [sub_add_sub_cancel] at hab
  exact hab

set_option maxHeartbeats 1600000 in
private theorem gamma_bijective : Function.Bijective (hom H φ hss hφ habel ht) := by
  obtain ⟨s, hs, hsf, _, _⟩ := Symmetrization.symmetrization_spec ℂ L
  obtain ⟨e, he⟩ := ChevalleyRestriction.chevalley_restriction L hss H
  obtain ⟨_, hinj, hsurj⟩ := symmetric_restriction_bijective H hss e he
  letI : Fact (Specs.Shared.Lie.filtrationType ℂ H) := ⟨filtration_properties ℂ H⟩
  letI : Fact (Specs.Shared.Lie.filtrationType ℂ L) := ⟨filtration_properties ℂ L⟩
  let Z := Subalgebra.center ℂ (U L)
  let W := weylInvariants H
  let res := symmetricMap (cartanProjection H hss)
  let γ := hom H φ hss hφ habel ht
  let lift (p : adjointInvariants (L := L)) : Z :=
    ⟨s p.val, (symmetrization_mem_center_iff s hs p.val).2 p.property⟩
  have hdiff (m : ℤ) (p : adjointInvariants (L := L)) (hp : p.val ∈ symmetricFiltration m) :
      (γ (lift p)).val - res p.val ∈ symmetricFiltration (m - 1) :=
    gamma_symbol H φ hss hφ habel ht s hs m _ hp
  have hF (q : SymmetricAlgebra ℂ H) : ∃ n : ℕ, q ∈ symmetricFiltration n := by
    obtain ⟨t, _, hts, _, _⟩ := Symmetrization.symmetrization_spec ℂ H
    obtain ⟨m, hm⟩ := (filtration_properties ℂ H).2.2.2.2.2 (t q)
    rw [← hts m] at hm
    obtain ⟨p,hp,he⟩ := hm
    exact ⟨m.toNat, symmetricFiltration_mono (Int.self_le_toNat m) (t.injective he ▸ hp)⟩
  have hzero (p : adjointInvariants (L := L)) (hp : p.val ∈ symmetricFiltration (-1)) : p = 0 := by
    apply Subtype.ext
    have h : symmetricFiltration (k := ℂ) (g := L) (-1) = ⊥ :=
      symmetricFiltration_eq_bot_of_neg _ (by decide)
    rwa [h] at hp
  have hker : ∀ n : ℕ, ∀ p : adjointInvariants (L := L), p.val ∈ symmetricFiltration n →
      γ (lift p) = 0 → p = 0 := by
    intro n
    induction n with
    | zero =>
      intro p hp hg
      apply hzero
      apply restriction_inverse_filtered H hss hinj
      have h := hdiff 0 p hp
      rw [hg] at h
      simpa using h
    | succ n ih =>
      intro p hp hg
      apply ih p _ hg
      apply restriction_inverse_filtered H hss hinj
      have h := hdiff (n+1 : ℕ) p hp
      rw [hg] at h
      simpa using h
  have honto : ∀ n : ℕ, ∀ q : W, q.val ∈ symmetricFiltration n → ∃ z : Z, γ z = q := by
    intro n
    induction n with
    | zero =>
      intro q hq
      obtain ⟨p, hp⟩ := hsurj q
      refine ⟨lift p, Subtype.ext ?_⟩
      apply sub_eq_zero.mp
      have h := hdiff 0 p (restriction_inverse_filtered H hss hinj 0 p (hp ▸ hq))
      rw [hp, symmetricFiltration_eq_bot_of_neg _ (by decide : (0 : ℤ) - 1 < 0)] at h
      exact h
    | succ n ih =>
      intro q hq
      obtain ⟨p, hp⟩ := hsurj q
      have hpF : p.val ∈ symmetricFiltration (n+1 : ℕ) :=
        restriction_inverse_filtered H hss hinj _ p (hp ▸ hq)
      let d := γ (lift p) - q
      have hd : d.val ∈ symmetricFiltration n := by
        have h := hdiff (n+1 : ℕ) p hpF
        rw [hp] at h
        change (γ (lift p)).val - q.val ∈ symmetricFiltration n
        simpa using h
      obtain ⟨z,hz⟩ := ih d hd
      refine ⟨lift p - z, ?_⟩
      rw [map_sub, hz]
      exact sub_sub_cancel _ _
  refine ⟨?_, fun q => ?_⟩
  · apply (injective_iff_map_eq_zero γ.toLinearMap).2
    intro z hz
    change γ z = 0 at hz
    obtain ⟨p,hp⟩ := s.surjective z.val
    have hpI : p ∈ adjointInvariants (L := L) :=
      (symmetrization_mem_center_iff s hs p).1 (hp ▸ z.property)
    let a : adjointInvariants (L := L) := ⟨p,hpI⟩
    have hl : lift a = z := Subtype.ext hp
    obtain ⟨m,hm⟩ := (filtration_properties ℂ L).2.2.2.2.2 z.val
    have hFm : p ∈ symmetricFiltration m := by
      rw [← hsf m] at hm
      obtain ⟨b,hb,heq⟩ := hm
      have hpb : b = p := s.injective (heq.trans hp.symm)
      exact hpb ▸ hb
    have ha := hker m.toNat a (symmetricFiltration_mono (Int.self_le_toNat m) hFm) (hl ▸ hz)
    apply Subtype.ext
    rw [← hp]
    have hp₀ : p = 0 := congrArg Subtype.val ha
    simp [hp₀]
  · obtain ⟨n,hn⟩ := hF q.val
    exact honto n q hn

end DegreeLowering

theorem harish_chandra_isomorphism : harish_chandra_isomorphism_type.{u} := by
  intro L _ _ _ hss H _ φ hφ
  let habel := cartan_abelian H hss
  let ht := VermaModules.triangular_bijective hss H φ hφ
  exact ⟨habel, ht, AlgEquiv.ofBijective (hom H φ hss hφ habel ht)
    (gamma_bijective H φ hss hφ habel ht), fun _ => rfl⟩

end LieAlgebrasAndRepresentations.HarishChandraIsomorphism
