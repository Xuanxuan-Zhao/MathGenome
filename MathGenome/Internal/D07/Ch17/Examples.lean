import MathGenome.Internal.D07.Ch17.Definition
import MathGenome.Internal.D07.Ch05.ActionDefinition
import MathGenome.Internal.D07.Ch02.TranspositionsParity
import MathGenome.Internal.Specs.D07.Ch17.Examples

/-! Trivial, permutation, regular and sign representations over an arbitrary field. -/
namespace D07.Ch17.Examples

universe u v w

abbrev trivial (K : Type u) (G : Type v) (V : Type w)
    [Field K] [Group G] [AddCommGroup V] [Module K V] : Representation K G V :=
  Representation.trivial K G V

noncomputable abbrev permutation (K : Type u) (G : Type v) (X : Type w)
    [Field K] [Group G] [MulAction G X] : Representation K G (MonoidAlgebra K X) :=
  Representation.ofMulAction K G X

noncomputable abbrev regular (K : Type u) (G : Type v) [Field K] [Group G] :
    Representation K G (MonoidAlgebra K G) := Representation.leftRegular K G

noncomputable abbrev sign (K : Type u) (X : Type v) [Field K] [Fintype X] :
    Representation K (Equiv.Perm X) K := Specs.D07.Ch17.Examples.signValue K X

theorem trivial_action : Specs.D07.Ch17.Examples.TrivialAction.{u, v, w} := by
  intro K G V _ _ _ _ g
  rfl

theorem formal_sums_model : Specs.D07.Ch17.Examples.FormalSumsModel.{u, w} := by
  intro K X _
  exact ⟨MonoidAlgebra.coeffLinearEquiv K, fun _ => rfl, fun _ => rfl⟩

theorem permutation_basis : Specs.D07.Ch17.Examples.PermutationBasis.{u, w} := by
  intro K X _
  exact ⟨MonoidAlgebra.basis X K, fun _ => rfl⟩

theorem permutation_on_basis : Specs.D07.Ch17.Examples.PermutationOnBasis.{u, v, w} := by
  intro K G X _ _ _ g x a
  exact Representation.ofMulAction_single g x a

theorem permutation_unique_extension :
    Specs.D07.Ch17.Examples.PermutationUniqueExtension.{u, v, w} := by
  intro K G X _ _ _ r hr
  funext g
  apply (MonoidAlgebra.basis X K).ext
  intro x
  simpa using (hr g x).trans (permutation_on_basis K G X g x 1).symm

theorem permutation_laws : Specs.D07.Ch17.Examples.PermutationLaws.{u, v, w} := by
  intro K G X _ _ _
  exact ⟨map_one _, map_mul _⟩

theorem permutation_coefficients :
    Specs.D07.Ch17.Examples.PermutationCoefficients.{u, v, w} := by
  intro K G X _ _ _ g f x
  exact Representation.coeff_ofMulAction g f x

theorem permutation_support : Specs.D07.Ch17.Examples.PermutationSupport.{u, v, w} := by
  classical
  intro K G X _ _ _ g f
  ext x
  simp only [Finsupp.mem_support_iff, Specs.D07.Ch17.Examples.permutationValue,
    Representation.coeff_ofMulAction, Finset.mem_image]
  constructor
  · intro hx
    exact ⟨g⁻¹ • x, hx, smul_inv_smul g x⟩
  · rintro ⟨y, hy, rfl⟩
    simpa using hy

theorem permutation_finite_dimension :
    Specs.D07.Ch17.Examples.PermutationFiniteDimension.{u, v, w} := by
  intro K G X _ _ _ _
  exact ⟨Module.Finite.of_basis (MonoidAlgebra.basis X K),
    Module.finrank_eq_nat_card_basis (MonoidAlgebra.basis X K)⟩

theorem permutation_fixes_basis_iff :
    Specs.D07.Ch17.Examples.PermutationFixesBasisIff.{u, v, w} := by
  intro K G X _ _ _ g
  constructor
  · intro h x
    apply MonoidAlgebra.single_left_injective (one_ne_zero : (1 : K) ≠ 0)
    exact (permutation_on_basis K G X g x 1).symm.trans (h x)
  · intro h x
    rw [permutation_on_basis, h x]

theorem permutation_kernel : Specs.D07.Ch17.Examples.PermutationKernel.{u, v, w} := by
  intro K G X _ _ _ g
  constructor
  · intro hg
    apply (permutation_fixes_basis_iff K G X g).mp
    intro x
    exact congrArg (fun r : Module.End K (MonoidAlgebra K X) =>
      r (MonoidAlgebra.single x 1)) hg
  · intro hg
    change permutation K G X g = 1
    apply (MonoidAlgebra.basis X K).ext
    intro x
    exact (permutation_fixes_basis_iff K G X g).mpr hg x

theorem permutation_faithful_iff :
    Specs.D07.Ch17.Examples.PermutationFaithfulIff.{u, v, w} := by
  intro K G X _ _ _
  constructor
  · intro h g k hg
    apply h
    apply (MonoidAlgebra.basis X K).ext
    intro x
    change permutation K G X g (MonoidAlgebra.single x 1) =
      permutation K G X k (MonoidAlgebra.single x 1)
    rw [permutation_on_basis, permutation_on_basis, congrFun hg x]
  · intro h g k hg
    apply h g k
    funext x
    apply MonoidAlgebra.single_left_injective (one_ne_zero : (1 : K) ≠ 0)
    have heq := congrArg (fun r : Module.End K (MonoidAlgebra K X) =>
      r (MonoidAlgebra.single x 1)) hg
    rw [permutation_on_basis, permutation_on_basis] at heq
    exact heq

theorem regular_on_basis : Specs.D07.Ch17.Examples.RegularOnBasis.{u, v} := by
  intro K G _ _ g h a
  exact Representation.ofMulAction_single g h a

theorem regular_faithful : Specs.D07.Ch17.Examples.RegularFaithful.{u, v} := by
  intro K G _ _ g h heq
  apply MonoidAlgebra.single_left_injective (one_ne_zero : (1 : K) ≠ 0)
  have hv := congrArg (fun r : Module.End K (MonoidAlgebra K G) =>
    r (MonoidAlgebra.single 1 1)) heq
  rw [regular_on_basis, regular_on_basis, mul_one, mul_one] at hv
  exact hv

theorem regular_kernel : Specs.D07.Ch17.Examples.RegularKernel.{u, v} := by
  intro K G _ _
  exact (regular K G).ker_eq_bot (regular_faithful K G)

theorem regular_finite_dimension : Specs.D07.Ch17.Examples.RegularFiniteDimension.{u, v} := by
  intro K G _ _ _
  exact permutation_finite_dimension K G G

theorem sign_action : Specs.D07.Ch17.Examples.SignAction.{u, v} := by
  intro K X _ _ σ a
  rfl

theorem sign_laws : Specs.D07.Ch17.Examples.SignLaws.{u, v} := by
  intro K X _ _
  exact ⟨map_one _, map_mul _⟩

theorem sign_dimension : Specs.D07.Ch17.Examples.SignDimension.{u, v} := by
  intro K X _ _
  exact ⟨inferInstance, Module.finrank_self K⟩

theorem sign_characteristic_two : Specs.D07.Ch17.Examples.SignCharacteristicTwo.{u, v} := by
  intro K X _ _ _
  apply MonoidHom.ext
  intro σ
  apply LinearMap.ext
  intro a
  rw [sign_action]
  obtain h | h := (D07.Ch02.TranspositionsParity.sign_values).2.2 X σ
  · simp [h]
  · simp [h, CharTwo.neg_one_eq_one]

theorem permutation_reducible_example :
    Specs.D07.Ch17.Examples.PermutationReducibleExample.{u} := by
  intro K _
  let U : Submodule K (MonoidAlgebra K (Fin 2)) :=
    LinearMap.ker ((Finsupp.lapply (1 : Fin 2)).comp
      (MonoidAlgebra.coeffLinearEquiv K).toLinearMap)
  have h0 : MonoidAlgebra.single (0 : Fin 2) (1 : K) ∈ U := by
    simp [U]
  have h1 : MonoidAlgebra.single (1 : Fin 2) (1 : K) ∉ U := by
    simp [U]
  refine ⟨U, ?_, ?_, ?_⟩
  · intro h
    rw [h, Submodule.mem_bot] at h0
    exact (MonoidAlgebra.single_ne_zero.mpr one_ne_zero) h0
  · intro h
    exact h1 (h ▸ Submodule.mem_top)
  · intro g f hf
    have hg : g = 1 := Subsingleton.elim _ _
    change permutation K PUnit.{1} (Fin 2) g f ∈ U
    rw [hg, map_one]
    exact hf

end D07.Ch17.Examples
