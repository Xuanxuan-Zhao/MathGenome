import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.FourierTransform
import MathGenome.Internal.AlgebraCore.P103.Ch08.RegularMultiplicity
import MathGenome.Internal.AlgebraCore.P103.Ch08.RepresentationModules
import Mathlib.LinearAlgebra.StdBasis

noncomputable section
universe u v w
namespace P103.Ch08.FourierTransform
open scoped MonoidAlgebra
open FourierSpecs

/-- Ordinary completeness implies completeness on representation spaces in
any universe, by passing through simple regular ideals. -/
theorem complete_exhaustive {G : Type u} [Group G] [Finite G]
    (C : Family.{u,v} G) (hC : Complete C)
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ G W) (hσ : Irreducible ℂ G W σ) :
    ∃ i, Nonempty ((C.representation i).Equiv σ) := by
  obtain ⟨S, hS, ⟨e⟩⟩ := RegularMultiplicity.exists_simple_ideal σ hσ
  have := hS
  obtain ⟨i, ⟨f⟩⟩ := hC (RegularMultiplicitySpecs.idealRepresentation S)
    (RegularMultiplicity.ideal_irreducible S)
  exact ⟨i, ⟨f.trans (RegularMultiplicity.idealRepresentationEquiv σ e.symm)⟩⟩

/-- Match any complete nonrepeating family with the upstream regular ideals. -/
theorem match_family {G : Type u} [Group G] [Finite G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C)
    (D : RegularMultiplicitySpecs.Family G)
    (hD : RegularMultiplicitySpecs.Valid D)
    (hDex : RegularMultiplicitySpecs.Exhaustive.{u,u} D) :
    ∃ t : Fin D.n ≃ Fin C.n, ∀ j,
      Nonempty ((RegularMultiplicitySpecs.idealRepresentation (D.space j)).Equiv
        (C.representation (t j))) := by
  classical
  have occurs (j : Fin D.n) : ∃ i,
      Nonempty ((RegularMultiplicitySpecs.idealRepresentation (D.space j)).Equiv
        (C.representation i)) := by
    have := hD.1 j
    obtain ⟨i, ⟨e⟩⟩ := hEx (RegularMultiplicitySpecs.idealRepresentation (D.space j))
      (RegularMultiplicity.ideal_irreducible (D.space j))
    exact ⟨i, ⟨e.symm⟩⟩
  choose t ht using occurs
  have inj : Function.Injective t := by
    intro i j hij
    apply hD.2 i j
    exact ⟨(RegularMultiplicity.idealModuleEquiv (D.space i)).symm.trans
      ((RegularMultiplicity.moduleEquivOfEquiv
        ((ht i).some.trans (hij ▸ (ht j).some.symm))).trans
          (RegularMultiplicity.idealModuleEquiv (D.space j)))⟩
  have surj : Function.Surjective t := by
    intro i
    obtain ⟨j, ⟨e⟩⟩ := RegularMultiplicity.exhaustive_from_regular D hDex
      (C.representation i) (hC.1 i)
    exact ⟨j, hC.2 (t j) i ⟨(ht j).some.symm.trans e⟩⟩
  exact ⟨Equiv.ofBijective t ⟨inj, surj⟩, ht⟩

/-- Trace is additive on the diagonal blocks of a finite product. -/
theorem trace_pi {I : Type*} [Fintype I] {V : I → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    [∀ i, FiniteDimensional ℂ (V i)] (f : ∀ i, Module.End ℂ (V i)) :
    LinearMap.trace ℂ (∀ i, V i) (LinearMap.piMap f) =
      ∑ i, LinearMap.trace ℂ (V i) (f i) := by
  classical
  let b i := Module.finBasis ℂ (V i)
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis b)]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sigma,
    LinearMap.toMatrix_apply, Pi.basis_apply, Pi.basis_repr]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.trace_eq_matrix_trace ℂ (b i)]
  apply Finset.sum_congr rfl
  intro j _
  simp [LinearMap.piMap, b, LinearMap.toMatrix_apply]

/-- Left multiplication has constant diagonal coefficient in the group basis. -/
theorem trace_left_mul {G : Type u} [Group G] [Fintype G] (a : ℂ[G]) :
    LinearMap.trace ℂ ℂ[G] (Algebra.lmul ℂ ℂ[G] a) =
      (Fintype.card G : ℂ) * a.coeff 1 := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ)]
  simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply,
    MonoidAlgebra.basis]

/-- Extension of the inherited ideal action really is algebra multiplication. -/
theorem ideal_action {G : Type u} [Group G]
    (S : Submodule ℂ[G] ℂ[G]) (a : ℂ[G]) :
    (RegularMultiplicitySpecs.idealRepresentation S).asAlgebraHom a =
      Algebra.lsmul ℂ ℂ S a := by
  change ((MonoidAlgebra.lift ℂ (Module.End ℂ S) G)
    ((MonoidAlgebra.lift ℂ (Module.End ℂ S) G).symm (Algebra.lsmul ℂ ℂ S))) a = _
  rw [Equiv.apply_symm_apply]

/-- Intertwining also commutes with the finite-support algebra extension. -/
theorem equiv_conj_action {G : Type u} [Group G]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    {W : Type w} [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (a : ℂ[G]) :
    e.conj (ρ.asAlgebraHom a) = σ.asAlgebraHom a := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | single g c => simp [Representation.asAlgebraHom_single, e.conj_apply_self]

/-- Compute the same regular trace on the blocks of its actual module decomposition. -/
theorem regular_trace {G : Type u} [Group G] [Fintype G]
    (D : RegularMultiplicitySpecs.Family G)
    (hD : RegularMultiplicitySpecs.Valid D)
    (hEx : RegularMultiplicitySpecs.Exhaustive.{u,u} D) (a : ℂ[G]) :
    LinearMap.trace ℂ ℂ[G] (Algebra.lmul ℂ ℂ[G] a) =
      ∑ i : Fin D.n, (Module.finrank ℂ (D.space i) : ℂ) *
        LinearMap.trace ℂ (D.space i)
          ((RegularMultiplicitySpecs.idealRepresentation (D.space i)).asAlgebraHom a) := by
  classical
  let e := (RegularMultiplicity.regular_decomposition D hD hEx).1.some
  let f := e.trans (DFinsupp.linearEquivFunOnFintype (R := ℂ[G]))
  have hc : (f.restrictScalars ℂ).conj (Algebra.lmul ℂ ℂ[G] a) =
      LinearMap.piMap (fun i : Fin D.n => LinearMap.piMap
        (fun _ : Fin (Module.finrank ℂ (D.space i)) => Algebra.lsmul ℂ ℂ (D.space i) a)) := by
    apply LinearMap.ext
    intro x
    funext i j
    change f (a • f.symm x) i j = a • x i j
    rw [f.map_smul, f.apply_symm_apply]
    rfl
  rw [← LinearMap.trace_conj' _ (f.restrictScalars ℂ), hc, trace_pi]
  simp_rw [trace_pi]
  simp [ideal_action, nsmul_eq_mul]

/-- The regular trace formula transferred to the user's chosen representatives. -/
theorem family_trace {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C) (a : ℂ[G]) :
    (Fintype.card G : ℂ) * a.coeff 1 =
      ∑ i : Fin C.n, (Module.finrank ℂ (C.space i) : ℂ) *
        LinearMap.trace ℂ (C.space i) ((C.representation i).asAlgebraHom a) := by
  classical
  obtain ⟨D, hD, hDex⟩ := RegularMultiplicity.finite_family.{u,u} (G := G)
  obtain ⟨t, ht⟩ := match_family C hC hEx D hD hDex
  rw [← trace_left_mul, regular_trace D hD hDex]
  rw [← t.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  let e := (ht j).some
  rw [e.toLinearEquiv.finrank_eq, ← equiv_conj_action e a, LinearMap.trace_conj']

/-- The same matching transfers the sum of squares to arbitrary representatives. -/
theorem family_square_sum {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C) :
    Fintype.card G = ∑ i : Fin C.n, (Module.finrank ℂ (C.space i)) ^ 2 := by
  classical
  obtain ⟨D, hD, hDex⟩ := RegularMultiplicity.finite_family.{u,u} (G := G)
  obtain ⟨t, ht⟩ := match_family C hC hEx D hD hDex
  rw [(RegularMultiplicity.regular_decomposition D hD hDex).2, ← t.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [(ht j).some.toLinearEquiv.finrank_eq]

/-- Coefficient recovery follows by taking the trace of multiplication by g⁻¹a. -/
theorem coefficient_recovery {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C)
    (a : ℂ[G]) (g : G) :
    inverseCoefficient C (action C a) g = a.coeff g := by
  have h := family_trace C hC hEx (MonoidAlgebra.single g⁻¹ 1 * a)
  simp only [MonoidAlgebra.coeff_single_mul_apply, inv_inv, mul_one, one_mul,
    map_mul, Representation.asAlgebraHom_single, one_smul] at h
  simp only [inverseCoefficient, action, AlgHom.pi_apply]
  rw [← h, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast Fintype.card_ne_zero

/-- The action is faithful because its traces recover all group coefficients. -/
theorem action_injective {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C) :
    Function.Injective (action C) := by
  intro a b hab
  ext g
  rw [← coefficient_recovery C hC hEx a g, ← coefficient_recovery C hC hEx b g, hab]

/-- Equality of dimensions upgrades the given action map to a bijection. -/
theorem action_bijective {G : Type u} [Group G] [Fintype G]
    (C : Family.{u,v} G) (hC : Valid C) (hEx : Complete C) :
    Function.Bijective (action C) := by
  have : ∀ i, FiniteDimensional ℂ (C.space i) :=
    fun i => RegularMultiplicity.finite_dimensional (C.representation i) (hC.1 i)
  have hdim : Module.finrank ℂ ℂ[G] =
      Module.finrank ℂ (∀ i, Module.End ℂ (C.space i)) := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis G ℂ),
      Module.finrank_pi_fintype]
    simp_rw [Module.finrank_linearMap]
    simpa [pow_two] using family_square_sum C hC hEx
  exact ⟨action_injective C hC hEx,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (action C).toLinearMap) hdim).mp
      (action_injective C hC hEx)⟩

/-- Fourier transformation for the specified actions, with its inverse on every tuple. -/
theorem fourier : fourierType.{u,v} := by
  intro G _ _ C hC hEx
  let E := AlgEquiv.ofBijective (action C) (action_bijective C hC hEx)
  refine ⟨E, ?_, ?_, ?_, coefficient_recovery C hC hEx⟩
  · intro a i
    rfl
  · intro a i x
    exact representationModule_sum (C.representation i) a x
  · intro B g
    have h := coefficient_recovery C hC hEx (E.symm B) g
    change inverseCoefficient C (E (E.symm B)) g = _ at h
    rw [E.apply_symm_apply] at h
    exact h.symm

end P103.Ch08.FourierTransform
