import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ClebschGordan
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RootTriples
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightData
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SimpleRoots
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Tactic.Module

/-! Finite module weights (LA-E08). Restrict the actual representation to the
root triple on the common eigenspace for the kernel of the root. On that
subspace the coroot eigenvalue determines the full Cartan weight. -/

noncomputable section
set_option maxHeartbeats 1000000
universe u v
open scoped TensorProduct
namespace LieAlgebrasAndRepresentations.FiniteModuleWeights
open Module
open Specs.LieAlgebrasAndRepresentations.Sl2Model
open Specs.LieAlgebrasAndRepresentations.Sl2SimpleModules
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
attribute [local instance 100] LieRing.ofAssociativeRing

/-- A coordinate of an eigenvector in a diagonal basis detects its eigenvalue. -/
lemma eigenvalue_of_coordinate {M : Type v} [AddCommGroup M] [Module ℂ M]
    {ι : Type*} (b : Basis ι ℂ M) (A : Module.End ℂ M) (d : ι → ℤ)
    (hd : ∀ i, A (b i) = (d i : ℂ) • b i)
    {a : ℂ} {x : M} (hx : A x = a • x) {i : ι} (hi : b.repr x i ≠ 0) :
    a = (d i : ℂ) := by
  have hc : b.repr (A x) i = (d i : ℂ) * b.repr x i := by
    have heq : (b.coord i).comp A = (d i : ℂ) • b.coord i := by
      apply b.ext
      intro j
      simp only [LinearMap.comp_apply, hd, map_smul, LinearMap.smul_apply,
        Basis.coord_apply, Basis.repr_self]
      by_cases h : i = j <;> simp [h]
    exact congrArg (fun f : M →ₗ[ℂ] ℂ => f x) heq
  rw [hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at hc
  exact mul_right_cancel₀ hi hc

/-- Finite sl₂ modules have an integral diagonal basis, with a basis permutation
negating every eigenvalue and all intermediate weights on each string. -/
lemma sl2_weight_basis (M : Type v) [AddCommGroup M] [Module ℂ M]
    [LieRingModule (Model ℂ) M] [LieModule ℂ (Model ℂ) M]
    [FiniteDimensional ℂ M] :
    ∃ (ι : Type v) (b : Basis ι ℂ M) (d : ι → ℤ) (r : ι ≃ ι),
      (∀ i, ⁅H ℂ, b i⁆ = (d i : ℂ) • b i) ∧
      (∀ i, d (r i) = -d i) ∧
      (∀ i (q : ℤ), 0 ≤ d i → 0 ≤ q → q ≤ d i →
        ∃ k, d k = d i - 2 * q) := by
  classical
  obtain ⟨S, hS, hint, hs⟩ := ClebschGordan.finite_standard_decomposition ℂ M
  choose n b hb using fun W : S => hs W.val W.property
  let B := hint.collectedBasis b
  let d : (Σ W : S, Fin (n W + 1)) → ℤ := fun i => n i.1 - 2 * i.2.val
  let r : (Σ W : S, Fin (n W + 1)) ≃ (Σ W : S, Fin (n W + 1)) :=
    Equiv.sigmaCongrRight (fun W => Fin.revPerm)
  refine ⟨_, B, d, r, ?_, ?_, ?_⟩
  · intro i
    have ht := congrArg Subtype.val ((hb i.1 i.2).1)
    simpa [B, DirectSum.IsInternal.collectedBasis_coe, d] using ht
  · rintro ⟨W, j⟩
    simp only [d, r, Equiv.sigmaCongrRight_apply, Fin.revPerm_apply, Fin.val_rev]
    omega
  · rintro ⟨W, j⟩ q hi hq hqi
    have hjq : 0 ≤ (j.val : ℤ) + q ∧ (j.val : ℤ) + q ≤ n W := by
      dsimp [d] at hi hqi
      omega
    refine ⟨⟨W, ⟨(j.val + q).toNat, by omega⟩⟩, ?_⟩
    dsimp [d]
    rw [Int.toNat_of_nonneg hjq.1]
    ring

/-- Reversing each actual simple string reverses the semisimple operator. -/
lemma sl2_spectral_symmetry (M : Type v) [AddCommGroup M] [Module ℂ M]
    [LieRingModule (Model ℂ) M] [LieModule ℂ (Model ℂ) M]
    [FiniteDimensional ℂ M] :
    ∃ T : M ≃ₗ[ℂ] M,
      (∀ x, ⁅H ℂ, T x⁆ = -T ⁅H ℂ, x⁆) ∧
      (∀ (a : ℂ) (x : M), x ≠ 0 → ⁅H ℂ, x⁆ = a • x → ∃ z : ℤ, a = (z : ℂ)) ∧
      (∀ (n j : ℤ), 0 ≤ n → 0 ≤ j → j ≤ n →
        (∃ x : M, x ≠ 0 ∧ ⁅H ℂ, x⁆ = (n : ℂ) • x) →
        ∃ y : M, y ≠ 0 ∧ ⁅H ℂ, y⁆ = ((n - 2*j : ℤ) : ℂ) • y) := by
  classical
  obtain ⟨ι, b, d, r, hd, hr, hs⟩ := sl2_weight_basis M
  let T := b.equiv b r
  have hT : ∀ x, ⁅H ℂ, T x⁆ = -T ⁅H ℂ, x⁆ := by
    have heq : (LieModule.toEnd ℂ (Model ℂ) M (H ℂ)).comp T.toLinearMap =
        -(T.toLinearMap.comp (LieModule.toEnd ℂ (Model ℂ) M (H ℂ))) := by
      apply b.ext
      intro i
      simp [T, Basis.equiv_apply, hd, hr]
    exact fun x => congrArg (fun f : M →ₗ[ℂ] M => f x) heq
  have hcoord (x : M) (hx : x ≠ 0) : ∃ i, b.repr x i ≠ 0 := by
    by_contra! h
    apply hx
    apply b.repr.injective
    ext i
    simp [h i]
  refine ⟨T, hT, ?_, ?_⟩
  · intro a x hx ha
    obtain ⟨i, hi⟩ := hcoord x hx
    exact ⟨d i, eigenvalue_of_coordinate b (LieModule.toEnd ℂ (Model ℂ) M (H ℂ)) d hd ha hi⟩
  · intro n j hn hj hjn hex
    obtain ⟨x, hx, he⟩ := hex
    obtain ⟨i, hi⟩ := hcoord x hx
    have hn' : n = d i := Int.cast_injective
      (eigenvalue_of_coordinate b (LieModule.toEnd ℂ (Model ℂ) M (H ℂ)) d hd he hi)
    obtain ⟨k, hk⟩ := hs i j (hn' ▸ hn) hj (hn' ▸ hjn)
    refine ⟨b k, b.ne_zero k, ?_⟩
    rw [hd, hk, ← hn']

section RootRestriction
variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (H : LieSubalgebra ℂ L)
variable (α μ : Module.Dual ℂ H)

/-- Common eigenspace of the hyperplane ker α, with its actual action on V. -/
def transverseWeightSpace : Submodule ℂ V where
  carrier := {x | ∀ h : H, α h = 0 → ρ h.val x = μ h • x}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy h hh; simp [map_add, hx h hh, hy h hh, smul_add]
  smul_mem' := by
    intro c x hx h hh
    rw [map_smul, hx h hh]
    exact smul_comm c (μ h) x

lemma mem_transverseWeightSpace {x : V} :
    x ∈ transverseWeightSpace ρ H α μ ↔
      ∀ h : H, α h = 0 → ρ h.val x = μ h • x := Iff.rfl

lemma mem_weightSpace {ν : Module.Dual ℂ H} {x : V} :
    x ∈ RepresentationJordan.weightSpace ρ H ν ↔
      ∀ h : H, ρ h.val x = ν h • x := by
  simp [RepresentationJordan.weightSpace]

lemma weight_mem_transverse {x : V} (hx : x ∈ RepresentationJordan.weightSpace ρ H μ) :
    x ∈ transverseWeightSpace ρ H α μ :=
  fun h _ => (mem_weightSpace ρ H).mp hx h

lemma transverse_stable (y : L)
    (hy : ∀ h : H, α h = 0 → ⁅h.val, y⁆ = 0) :
    ∀ x ∈ transverseWeightSpace ρ H α μ, ρ y x ∈ transverseWeightSpace ρ H α μ := by
  intro x hx h hh
  have hc : Commute (ρ h.val) (ρ y) := by
    rw [commute_iff_lie_eq, ← ρ.map_lie, hy h hh, map_zero]
  change (ρ h.val * ρ y) x = _
  rw [hc.eq, Module.End.mul_apply, hx h hh, map_smul]

/-- On a transverse weight space it suffices to test the coroot eigenvalue. -/
lemma transverse_weight_iff (hα : H) (ha : α hα = 2) (c : ℂ)
    {x : V} (hx : x ∈ transverseWeightSpace ρ H α μ) :
    x ∈ RepresentationJordan.weightSpace ρ H (μ + c • α) ↔
      ρ hα.val x = (μ hα + 2*c) • x := by
  rw [mem_weightSpace]
  constructor
  · intro h
    simpa [ha, mul_comm] using h hα
  · intro he h
    let h₀ : H := h - (α h / 2) • hα
    have h₀a : α h₀ = 0 := by simp [h₀, ha]
    have ht := hx h₀ h₀a
    change ρ ((h : L) - (α h / 2) • (hα : L)) x =
      μ (h - (α h / 2) • hα) • x at ht
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul] at ht
    rw [he] at ht
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [sub_eq_iff_eq_add] at ht
    rw [ht]
    module

variable [FiniteDimensional ℂ L]

lemma coroot_normalized (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hα : α ∈ rootSet H) : α (killingCoroot H α) = 2 := by
  rw [killingCoroot_pairing hss H hH]
  exact mul_div_cancel_right₀ 2 (rootForm_self_ne_zero hss H hH α hα)

private def transverseCorootAction (hH : IsMaximalToral H) :
    Module.End ℂ (transverseWeightSpace ρ H α μ) :=
  (ρ (killingCoroot H α : L)).restrict
    (transverse_stable ρ H α μ _ (fun h _ => by
      have ht : ⁅h, killingCoroot H α⁆ = 0 := hH.1.1.trivial h (killingCoroot H α)
      exact congrArg Subtype.val ht))

variable [FiniteDimensional ℂ V]

/-- The root triple acts on the common eigenspace for the kernel of the root. -/
lemma transverse_sl2_data (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
    (hα : α ∈ rootSet H) :
    let K := transverseWeightSpace ρ H α μ
    let A := transverseCorootAction ρ H α μ hH
    ∃ T : K ≃ₗ[ℂ] K,
      (∀ x, A (T x) = -T (A x)) ∧
      (∀ (a : ℂ) (x : K), x ≠ 0 → A x = a • x → ∃ z : ℤ, a = (z : ℂ)) ∧
      (∀ (n j : ℤ), 0 ≤ n → 0 ≤ j → j ≤ n →
        (∃ x : K, x ≠ 0 ∧ A x = (n : ℂ) • x) →
        ∃ y : K, y ≠ 0 ∧ A y = ((n - 2*j : ℤ) : ℂ) • y) := by
  dsimp only
  let K := transverseWeightSpace ρ H α μ
  obtain ⟨e, f, he, hf, he0, hf0, hef, hhe, hhf⟩ :=
    exists_root_triple hss H hH α hα
  have hes := transverse_stable ρ H α μ e (fun h hh => by
    rw [(mem_rootSpace H α e).mp he h, hh, zero_smul])
  have hfs := transverse_stable ρ H α μ f (fun h hh => by
    rw [(mem_rootSpace H (-α) f).mp hf h]
    simp [hh])
  let E' : Module.End ℂ K := (ρ e).restrict hes
  let F' : Module.End ℂ K := (ρ f).restrict hfs
  let H' := transverseCorootAction ρ H α μ hH
  have relE : ⁅H', E'⁆ = (2 : ℂ) • E' := by
    ext x
    change (ρ (killingCoroot H α : L) * ρ e -
      ρ e * ρ (killingCoroot H α : L)) x.val = _
    change (⁅ρ (killingCoroot H α : L), ρ e⁆) x.val = _
    rw [← ρ.map_lie, hhe, map_smul]
    rfl
  have relF : ⁅H', F'⁆ = (-2 : ℂ) • F' := by
    ext x
    change (⁅ρ (killingCoroot H α : L), ρ f⁆) x.val = _
    rw [← ρ.map_lie, hhf, map_smul]
    rfl
  have relEF : ⁅E', F'⁆ = H' := by
    ext x
    change (⁅ρ e, ρ f⁆) x.val = _
    rw [← ρ.map_lie, hef]
    rfl
  let σ := Sl2SimpleModules.representationOfOperators ℂ K E' F' H' relE relF relEF
  let : LieRingModule (Model ℂ) K := LieRingModule.compLieHom K σ
  let : LieModule ℂ (Model ℂ) K := LieModule.compLieHom K σ
  have haction (x : K) : ⁅sl2_h ℂ, x⁆ = H' x := by
    change Sl2SimpleModules.operatorAction ℂ K E' F' H' (sl2_h ℂ) x = H' x
    rw [Sl2SimpleModules.operatorAction_h]
  simpa only [haction] using sl2_spectral_symmetry K

end RootRestriction

/-- Every occurring weight evaluates integrally on the coroot of every root. -/
theorem integral_weights : integral_weights_type.{u,v} := by
  intro L _ _ _ V _ _ _ hss ρ H hH μ hμ α hα
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  let xK : transverseWeightSpace ρ H α μ := ⟨x, weight_mem_transverse ρ H α μ hx⟩
  have hxK0 : xK ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨_, _, hint, _⟩ := transverse_sl2_data ρ H α μ hss hH hα
  apply hint _ xK hxK0
  apply Subtype.ext
  exact (mem_weightSpace ρ H).mp hx (killingCoroot H α)

/-- Every integer step from a weight to its reflection occurs when the coroot
evaluation is nonnegative. -/
theorem saturated_weights : saturated_weights_type.{u,v} := by
  intro L _ _ _ V _ _ _ hss ρ H hH μ hμ α hα n hμn hn j hj hjn
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hμ
  let xK : transverseWeightSpace ρ H α μ := ⟨x, weight_mem_transverse ρ H α μ hx⟩
  have hxK0 : xK ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨_, _, _, hstring⟩ := transverse_sl2_data ρ H α μ hss hH hα
  obtain ⟨y, hy0, hy⟩ := hstring n j hn hj hjn ⟨xK, hxK0, by
    apply Subtype.ext
    have hxe := (mem_weightSpace ρ H).mp hx (killingCoroot H α)
    rw [show μ (killingCoroot H α) = (n : ℂ) from hμn] at hxe
    exact hxe⟩
  have hye : ρ (killingCoroot H α : L) y.val = ((n - 2*j : ℤ) : ℂ) • y.val :=
    congrArg Subtype.val hy
  have hyw : y.val ∈ RepresentationJordan.weightSpace ρ H (μ - j • α) := by
    rw [← Int.cast_smul_eq_zsmul ℂ, sub_eq_add_neg, ← neg_smul]
    apply (transverse_weight_iff ρ H α μ (killingCoroot H α)
      (coroot_normalized H α hss hH hα) (-(j : ℂ)) y.property).2
    rw [hye, show μ (killingCoroot H α) = (n : ℂ) from hμn]
    push_cast
    rw [sub_eq_add_neg, mul_neg]
  intro hbot
  rw [hbot, Submodule.mem_bot] at hyw
  exact hy0 (Subtype.ext hyw)


section

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable {V : Type v} [AddCommGroup V] [Module ℂ V] [finiteV : FiniteDimensional ℂ V]
variable (ρ : L →ₗ⁅ℂ⁆ Module.End ℂ V) (H : LieSubalgebra ℂ L)
variable (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H)
variable (α : Module.Dual ℂ H) (hα : α ∈ rootSet H)
include hss hH hα finiteV

private lemma finrank_weightSpace_le_reflection (μ : Module.Dual ℂ H) :
    Module.finrank ℂ (RepresentationJordan.weightSpace ρ H μ) ≤
      Module.finrank ℂ (RepresentationJordan.weightSpace ρ H (weightReflection H α μ)) := by
  let K := transverseWeightSpace ρ H α μ
  let A := transverseCorootAction ρ H α μ hH
  obtain ⟨T, hT, _, _⟩ := transverse_sl2_data ρ H α μ hss hH hα
  have hc : α (killingCoroot H α) = 2 := coroot_normalized H α hss hH hα
  have hs : weightReflection H α μ = μ + (-μ (killingCoroot H α)) • α := by
    have hc' : corootEvaluation H α α = 2 := hc
    rw [weightReflection, dite_eq_left hc]
    change Module.reflection hc' μ = _
    rw [Module.reflection_apply, sub_eq_add_neg, neg_smul]
    rfl
  have hK : RepresentationJordan.weightSpace ρ H μ ≤ K :=
    fun _ hx => weight_mem_transverse ρ H α μ hx
  let i := Submodule.inclusion hK
  have hmap (x : RepresentationJordan.weightSpace ρ H μ) :
      ((T (i x) : K) : V) ∈ RepresentationJordan.weightSpace ρ H (weightReflection H α μ) := by
    rw [hs]
    apply (transverse_weight_iff ρ H α μ (killingCoroot H α) hc _ (T (i x)).property).2
    have hx : A (i x) = μ (killingCoroot H α) • i x :=
      Subtype.ext ((mem_weightSpace ρ H).mp x.property (killingCoroot H α))
    have h := hT (i x)
    change A (T (i x)) = -T (A (i x)) at h
    rw [hx, map_smul, ← neg_smul] at h
    have he := congrArg (fun y : K => (y : V)) h
    change ρ (killingCoroot H α : L) _ = (-μ (killingCoroot H α)) • _ at he
    rw [show μ (killingCoroot H α) + 2 * (-μ (killingCoroot H α)) =
      -μ (killingCoroot H α) by ring]
    exact he
  let e := (K.subtype.comp (T.toLinearMap.comp i)).codRestrict
    (RepresentationJordan.weightSpace ρ H (weightReflection H α μ)) hmap
  apply LinearMap.finrank_le_finrank_of_injective (f := e)
  intro x y hxy
  have he : (e x : V) = (e y : V) := congrArg Subtype.val hxy
  exact Submodule.inclusion_injective hK (T.injective (Subtype.ext he))

private lemma finrank_weightSpace_reflection (μ : Module.Dual ℂ H) :
    Module.finrank ℂ (RepresentationJordan.weightSpace ρ H (weightReflection H α μ)) =
      Module.finrank ℂ (RepresentationJordan.weightSpace ρ H μ) := by
  have h := finrank_weightSpace_le_reflection ρ H hss hH α hα (weightReflection H α μ)
  have h_inv : weightReflection H α (weightReflection H α μ) = μ := by
    have hc : α (killingCoroot H α) = 2 := coroot_normalized H α hss hH hα
    have hc' : corootEvaluation H α α = 2 := hc
    simp only [weightReflection, dite_eq_left hc]
    exact Module.involutive_reflection hc' μ
  rw [h_inv] at h
  exact le_antisymm h (finrank_weightSpace_le_reflection ρ H hss hH α hα μ)

end

/-- Weight multiplicities are constant on Weyl group orbits. -/
theorem multiplicities_weyl_invariant : multiplicities_weyl_invariant_type.{u,v} := by
  unfold multiplicities_weyl_invariant_type
  intro L _ _ _ V _ _ _ hss ρ H hH w
  let d (μ : Module.Dual ℂ H) := Module.finrank ℂ (RepresentationJordan.weightSpace ρ H μ)
  change ∀ μ, d (w.val μ) = d μ
  refine Subgroup.closure_induction
    (k := weightReflection H '' rootSet H) (x := w.val)
    (p := fun g _ => ∀ μ, d (g μ) = d μ) ?_ ?_ ?_ ?_ w.property
  · rintro g ⟨α, hα, rfl⟩ μ
    exact finrank_weightSpace_reflection ρ H hss hH α hα μ
  · intro μ
    rfl
  · intro g f _ _ hg hf μ
    exact (hg (f μ)).trans (hf μ)
  · intro g _ hg μ
    simpa only [LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using (hg (g⁻¹ μ)).symm

section WeylComplexification

open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value)
open Specs.LieAlgebrasAndRepresentations.RootForm (coroot_value)

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable {H : LieSubalgebra ℂ L} (d : Realization H)

/-- Extend an automorphism of the real Cartan dual and transport it along the
Killing realization's complexification. -/
private def complexifyAutomorphism :
    (E H ≃ₗ[ℝ] E H) →* (Module.Dual ℂ H ≃ₗ[ℂ] Module.Dual ℂ H) where
  toFun f := d.complexification.symm.trans
    ((f.baseChange ℝ ℂ (E H) (E H)).trans d.complexification)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    simp [LinearEquiv.baseChange_one]
  map_mul' f g := by
    apply LinearEquiv.ext
    intro x
    simp [LinearEquiv.baseChange_mul]

private theorem complexifyAutomorphism_apply (f : E H ≃ₗ[ℝ] E H) (x : E H) :
    complexifyAutomorphism d f (d.j x) = d.j (f x) := by
  have h (y : E H) : d.complexification (1 ⊗ₜ[ℝ] y) = d.j y := by simp
  rw [← h x, ← h (f x)]
  change d.complexification
    (f.baseChange ℝ ℂ (E H) (E H) (d.complexification.symm (d.complexification _))) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.baseChange_tmul]

private theorem extension_injective : Function.Injective d.j := by
  intro x y h
  apply LinearMap.ext
  intro z
  have hx := d.extension_formula x z 0
  have hy := d.extension_formula y z 0
  simp at hx hy
  rw [h, hy] at hx
  exact Complex.ofReal_inj.mp hx.symm

/-- Complexification identifies the reflections on the real root space with
the coroot reflections on the whole complex Cartan dual. -/
theorem weyl_complexification : weyl_complexification_type.{u} := by
  intro L _ _ _ H d
  let _ : NormedAddCommGroup (E H) := d.normedAddCommGroup
  let _ : InnerProductSpace ℝ (E H) := d.innerProductSpace
  have hreflection (α : Module.Dual ℂ H) (hα : α ∈ rootSet_value H) (x : E H) :
      d.j (rootReflectionEquiv (rootRestriction H α) x) =
        weightReflection H α (d.j x) := by
    let a := rootRestriction H α
    have ha : a ≠ 0 := d.root_system.nonzero _ ⟨α, hα, rfl⟩
    have heval (y : E H) : d.j y (coroot_value H α) =
        ((2 / inner ℝ a a * inner ℝ y a : ℝ) : ℂ) := by
      rw [d.coroot_evaluation y α hα, coroot, real_inner_smul_right]
    have hnorm : α (coroot_value H α) = 2 := by
      calc
        _ = d.j a (coroot_value H α) :=
          congrArg (fun β : Module.Dual ℂ H => β (coroot_value H α))
            (d.extension_root α hα).symm
        _ = 2 := by
          rw [heval a, div_mul_cancel₀ 2 (_root_.inner_self_ne_zero.mpr ha)]
          norm_cast
    have hnorm' : corootEvaluation H α α = 2 := hnorm
    have hr : rootReflectionEquiv a x =
        x - (2 / inner ℝ a a * inner ℝ x a) • a := by
      rw [rootReflectionEquiv_apply, rootReflection, div_mul_eq_mul_div]
    rw [hr, map_sub, map_smul, d.extension_root α hα, weightReflection, dite_eq_left hnorm]
    change _ = Module.reflection hnorm' (d.j x)
    rw [Module.reflection_apply]
    change _ = d.j x - d.j x (coroot_value H α) • α
    rw [heval x]
    rfl
  refine ⟨hreflection, ?_⟩
  let f := complexifyAutomorphism d
  have hf : Function.Injective f := by
    intro g h hgh
    apply LinearEquiv.ext
    intro x
    apply extension_injective d
    rw [← complexifyAutomorphism_apply d, ← complexifyAutomorphism_apply d]
    exact DFunLike.congr_fun hgh (d.j x)
  have hgen (α : Module.Dual ℂ H) (hα : α ∈ rootSet_value H) :
      f (rootReflectionEquiv (rootRestriction H α)) = weightReflection H α := by
    apply LinearEquiv.toLinearMap_injective
    apply LinearMap.ext_on d.roots_span
    intro β hβ
    change f (rootReflectionEquiv (rootRestriction H α)) β = weightReflection H α β
    rw [← d.extension_root β hβ, complexifyAutomorphism_apply d]
    exact hreflection α hα _
  have hmap : (rootWeylGroup (realRoots H)).map f = weightWeylGroup H := by
    unfold rootWeylGroup weightWeylGroup
    rw [MonoidHom.map_closure]
    congr 1
    ext g
    constructor
    · rintro ⟨_, ⟨_, ⟨α, hα, rfl⟩, rfl⟩, rfl⟩
      exact ⟨α, hα, (hgen α hα).symm⟩
    · rintro ⟨α, hα, rfl⟩
      exact ⟨_, ⟨_, ⟨α, hα, rfl⟩, rfl⟩, hgen α hα⟩
  refine ⟨(Subgroup.equivMapOfInjective _ f hf).trans (MulEquiv.subgroupCongr hmap), ?_⟩
  intro w x
  rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, Subgroup.coe_equivMapOfInjective_apply]
  exact (complexifyAutomorphism_apply d w.val x).symm

end WeylComplexification

section RealWeights

open Specs.LieAlgebrasAndRepresentations.RealRootSpace
open private cartan_lattice_comparison_of_realization
  from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.HighestWeightData

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L]
variable {H : LieSubalgebra ℂ L}

private theorem integral_weight_in_range (d : Realization H) (μ : Module.Dual ℂ H)
    (hμ : ∀ α ∈ rootSet H, ∃ z : ℤ, μ (killingCoroot H α) = (z : ℂ)) :
    ∃ x, d.j x = μ := by
  let _ : NormedAddCommGroup (E H) := d.normedAddCommGroup
  let _ : InnerProductSpace ℝ (E H) := d.innerProductSpace
  let _ : Finite (realRoots H) := d.root_system.finite.to_subtype
  obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun α : realRoots H => innerₗ (E H) α.val) (fun α => by
      refine ⟨α.val, ?_⟩
      exact _root_.inner_self_ne_zero.mpr (d.root_system.nonzero α.val α.property))
  have hv' : RootRegular (realRoots H) v := by
    intro α hα
    rw [real_inner_comm]
    exact hv ⟨α, hα⟩
  obtain ⟨_, _, _, _, hroots, _, _, _, _, _, _, hreal, _⟩ :=
    cartan_lattice_comparison_of_realization.{u,u} d v hv'
      (Equiv.refl (simpleRoots (realRoots H) v))
  -- The comparison uses actual simple coroots, so integrality on all coroots suffices.
  obtain ⟨x, _, hx, _⟩ := hreal μ (fun i => hμ _ (hroots i).2.2.2.1)
  exact ⟨x, hx⟩

/-- Every occurring weight comes from the real Cartan dual, and the real
Weyl group preserves the dimensions of the associated weight spaces. -/
theorem real_weight_multiplicities : real_weight_multiplicities_type.{u,v} := by
  intro L _ _ _ V _ _ _ hss ρ H hH d
  let _ : NormedAddCommGroup (E H) := d.normedAddCommGroup
  let _ : InnerProductSpace ℝ (E H) := d.innerProductSpace
  obtain ⟨_, e, he⟩ := weyl_complexification H d
  constructor
  · intro μ hμ
    exact integral_weight_in_range d μ (integral_weights hss ρ H hH μ hμ)
  · intro w x
    rw [he w x]
    exact multiplicities_weyl_invariant hss ρ H hH (e w) (d.j x)

end RealWeights

end LieAlgebrasAndRepresentations.FiniteModuleWeights
