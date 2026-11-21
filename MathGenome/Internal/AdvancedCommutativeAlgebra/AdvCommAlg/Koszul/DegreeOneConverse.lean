import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Koszul.DegreeOneConverse
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.RegularAcyclicity
import Mathlib.RingTheory.TensorProduct.Finite

/-! The degree-one converse, RK-08. The induction uses the long exact
sequence for an appended element and Nakayama on the preceding H₁. -/

open CategoryTheory
open scoped TensorProduct Pointwise
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace AdvCommAlg.Koszul
variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- Every term of the coefficient complex is finite when M is finite. -/
theorem coefficientTerm_finite [Module.Finite R M] (x : List R) (q : ℕ) :
    Module.Finite R ((coefficientComplex M x).X q) := by
  have : Module.Finite R (⋀[R]^q (Fin x.length → R)) :=
    Module.Finite.of_basis (listBasis x q)
  change Module.Finite R ((⋀[R]^q (Fin x.length → R)) ⊗[R] M)
  infer_instance

/-- Homology is a quotient of the cycles, which embed in a finite term. -/
theorem koszulHomology_finite [IsNoetherianRing R] [Module.Finite R M]
    (x : List R) (q : ℕ) : Module.Finite R (homology M x q) := by
  let C := coefficientComplex M x
  have : Module.Finite R (C.X q) := coefficientTerm_finite M x q
  have : Module.Finite R (C.cycles q) :=
    Module.Finite.of_injective (C.iCycles q).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (C.homologyπ q).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

/-- Nakayama in the form needed for a surjective multiplication map. -/
theorem subsingleton_of_surjective_smul [Module.Finite R M] (y : R)
    (hy : y ∈ (⊥ : Ideal R).jacobson)
    (hs : Function.Surjective (fun m : M => y • m)) : Subsingleton M := by
  have htop : (⊤ : Submodule R M) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {y}) ⊤
      Module.Finite.fg_top (by
        intro z hz
        obtain ⟨a, rfl⟩ := hs z
        exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton y))
          (Submodule.mem_top : a ∈ (⊤ : Submodule R M)))
      (Ideal.span_le.mpr (by simpa using hy))
  apply subsingleton_of_forall_eq 0
  intro z
  have hz : z ∈ (⊤ : Submodule R M) := Submodule.mem_top
  rw [htop] at hz
  exact hz

/-- Vanishing of the appended H₁ makes multiplication surjective on the old H₁. -/
theorem append_homologyOne_surjective (x : List R) (y : R)
    [Subsingleton (homology M (x ++ [y]) 1)] :
    Function.Surjective (homologyScalar (coefficientComplex M x) y 1).hom := by
  obtain ⟨S⟩ := append_long_exact_sequence M x y
  intro a
  exact (S.exact_multiply_inclusion 1 a).mp
    (Subsingleton.elim (α := homology M (x ++ [y]) 1) _ _)

/-- The same vanishing makes multiplication injective on the old H₀. -/
theorem append_homologyZero_injective (x : List R) (y : R)
    [Subsingleton (homology M (x ++ [y]) 1)] :
    Function.Injective (homologyScalar (coefficientComplex M x) y 0).hom := by
  obtain ⟨S⟩ := append_long_exact_sequence M x y
  intro a b hab
  apply sub_eq_zero.mp
  have hz : (homologyScalar (coefficientComplex M x) y 0).hom (a-b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨z, hz⟩ := (S.exact_projection_multiply 0 (a-b)).mp hz
  rw [← hz, Subsingleton.elim z 0, map_zero]

/-- RK-08: H₁-vanishing implies weak regularity for entries in the Jacobson radical. -/
theorem degreeOne_converse [IsNoetherianRing R] [Module.Finite R M]
    (x : List R) (hx : ∀ a ∈ x, a ∈ (⊥ : Ideal R).jacobson)
    (h₁ : Subsingleton (homology M x 1)) : RegularSequence.WeaklyRegular M x := by
  induction x using List.reverseRecOn with
  | nil => exact RegularSequence.weaklyRegular_nil M
  | append_singleton x y ih =>
    have h₁' := h₁
    have hx' : ∀ a ∈ x, a ∈ (⊥ : Ideal R).jacobson :=
      fun a ha => hx a (List.mem_append_left _ ha)
    have hy : y ∈ (⊥ : Ideal R).jacobson := hx y (by simp)
    have : Module.Finite R (homology M x 1) := koszulHomology_finite M x 1
    have hprev : Subsingleton (homology M x 1) :=
      subsingleton_of_surjective_smul (homology M x 1) y hy
        (append_homologyOne_surjective M x y)
    have hreg := ih hx' hprev
    apply (RingTheory.Sequence.isWeaklyRegular_append_iff M x [y]).mpr
    refine ⟨hreg, (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ y).mpr ?_⟩
    change Function.Injective (fun z : M ⧸ listSubmodule M x => y • z)
    intro a b hab
    apply (homologyZeroEquiv M x).symm.injective
    apply append_homologyZero_injective M x y
    change y • (homologyZeroEquiv M x).symm a = y • (homologyZeroEquiv M x).symm b
    simpa only [map_smul] using congrArg (homologyZeroEquiv M x).symm hab

/-- For nonzero M, Nakayama also supplies the required proper final quotient. -/
theorem degreeOne_converse_regular [IsNoetherianRing R] [Module.Finite R M]
    [Nontrivial M] (x : List R) (hx : ∀ a ∈ x, a ∈ (⊥ : Ideal R).jacobson)
    (h₁ : Subsingleton (homology M x 1)) : RegularSequence.Regular M x := by
  apply (RingTheory.Sequence.isRegular_iff_isWeaklyRegular_of_subset_jacobson_annihilator
    (M := M) (fun a ha => Ideal.jacobson_mono bot_le (hx a ha))).mpr
  exact degreeOne_converse M x hx h₁

/-- RK-08: regularity, positive acyclicity, and H₁-vanishing are equivalent locally. -/
theorem local_regularity_equivalences [IsNoetherianRing R] [IsLocalRing R]
    [Module.Finite R M] [Nontrivial M] (x : List R)
    (hx : ∀ a ∈ x, a ∈ IsLocalRing.maximalIdeal R) :
    (RegularSequence.Regular M x ↔
      ∀ q : ℕ, 0 < q → Subsingleton (homology M x q)) ∧
    ((∀ q : ℕ, 0 < q → Subsingleton (homology M x q)) ↔
      Subsingleton (homology M x 1)) := by
  have hj : ∀ a ∈ x, a ∈ (⊥ : Ideal R).jacobson := by
    simpa only [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top] using hx
  constructor
  · constructor
    · intro h
      exact weaklyRegular_acyclic M x h.toIsWeaklyRegular
    · intro h
      exact degreeOne_converse_regular M x hj (h 1 (by decide))
  · constructor
    · intro h
      exact h 1 (by decide)
    · intro h
      exact weaklyRegular_acyclic M x (degreeOne_converse M x hj h)

end AdvCommAlg.Koszul
