import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.MatrixCoefficientOrthogonality
import MathGenome.Internal.AlgebraCore.P103.Ch08.RegularMultiplicity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

noncomputable section
universe u v w
namespace P103.Ch08.MatrixCoefficientOrthogonality
open MatrixCoefficientSpecs Module

variable {G : Type u} [Group G]

/-- The coordinate functional of an orthonormal basis in the source's convention. -/
theorem form_basis (M : Model.{u,v} G) (a : Fin M.d) (x : M.space) :
    M.form.toFun x (M.basis a) = M.basis.repr x a := by
  let f : M.space →ₗ[ℂ] ℂ :=
    { toFun := fun x => M.form.toFun x (M.basis a)
      map_add' := fun x y => M.form.add_left x y _
      map_smul' := fun c x => M.form.smul_left c x _ }
  have hf : f = M.basis.coord a := by
    apply M.basis.ext
    intro j
    simp [f, M.orthonormal, Finsupp.single_apply, eq_comm]
  exact congrArg (fun f : M.space →ₗ[ℂ] ℂ => f x) hf

theorem coefficient_inverse (M : Model.{u,v} G) (a b : Fin M.d) (g : G) :
    coefficient M a b g⁻¹ = star (coefficient M b a g) := by
  rw [coefficient, ← form_basis, coefficient, ← form_basis, M.form.conj_symm]
  have h := M.invariant g (M.ρ g⁻¹ (M.basis b)) (M.basis a)
  simpa using h.symm

variable [Fintype G]

/-- Reynolds averaging on the space of linear maps. -/
def average {V : Type v} {W : Type w} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (B : V →ₗ[ℂ] W) : ρ.IntertwiningMap σ := by
  letI : Invertible (Fintype.card G : ℂ) := invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  exact Representation.invariantsEquivIntertwiningMap ρ σ
    ⟨(Representation.linHom ρ σ).averageMap B,
      (Representation.linHom ρ σ).averageMap_invariant B⟩

theorem average_formula {V : Type v} {W : Type w} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (B : V →ₗ[ℂ] W) :
    (average ρ σ B).toLinearMap =
      (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (σ g).comp (B.comp (ρ g⁻¹)) := by
  simp [average, Representation.invariantsEquivIntertwiningMap,
    Representation.averageMap, GroupAlgebra.average, Representation.linHom_apply,
    LinearMap.intertwiningMap_of_isIntertwiningMap]

/-- Averaging the matrix unit computes the coefficient pairing. -/
theorem average_entry (M : Model.{u,v} G) (N : Model.{u,w} G)
    (a b : Fin M.d) (c d : Fin N.d) :
    M.basis.repr
      (average N.ρ M.ρ ((N.basis.coord d).smulRight (M.basis b)) (N.basis c)) a =
      UnitaritySpecs.functionPairingValue (coefficient M a b) (coefficient N c d) := by
  rw [← Representation.IntertwiningMap.toLinearMap_apply, average_formula]
  simp [UnitaritySpecs.functionPairingValue, LinearMap.sum_apply,
    coefficient, mul_comm]
  change (∑ g, coefficient M a b g * coefficient N d c g⁻¹) =
    ∑ g, coefficient M a b g * star (coefficient N c d g)
  simp_rw [coefficient_inverse]

theorem average_trace {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (B : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ V (average ρ ρ B).toLinearMap = LinearMap.trace ℂ V B := by
  rw [average_formula, map_smul, map_sum]
  have hh (g : G) :
      LinearMap.trace ℂ V ((ρ g).comp (B.comp (ρ g⁻¹))) = LinearMap.trace ℂ V B := by
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc]
    simp [← Module.End.mul_eq_comp, ← map_mul]
  simp_rw [hh]
  simp [smul_eq_mul]

omit [Fintype G] in
theorem dimension (M : Model.{u,v} G) : Module.finrank ℂ M.space = M.d := by
  simpa using Module.finrank_eq_card_basis M.basis

omit [Fintype G] in
theorem dimension_pos (M : Model.{u,v} G) : 0 < M.d := by
  have : Nontrivial M.space := M.irreducible.1
  have : FiniteDimensional ℂ M.space := Module.Finite.of_basis M.basis
  rw [← dimension M]
  exact Module.finrank_pos

/-- Schur's scalar is determined by the preserved trace. -/
theorem average_scalar (M : Model.{u,v} G) (B : M.space →ₗ[ℂ] M.space) :
    (average M.ρ M.ρ B).toLinearMap =
      ((M.d : ℂ)⁻¹ * LinearMap.trace ℂ M.space B) • LinearMap.id := by
  have : FiniteDimensional ℂ M.space := Module.Finite.of_basis M.basis
  obtain ⟨c, hc, _⟩ := Schur.uniqueScalar M.ρ M.irreducible (average M.ρ M.ρ B)
  have he : (average M.ρ M.ρ B).toLinearMap = c • LinearMap.id :=
    congrArg Representation.IntertwiningMap.toLinearMap hc
  have ht := average_trace M.ρ B
  rw [he] at ht
  simp only [map_smul, LinearMap.trace_id, smul_eq_mul, dimension] at ht
  have hd : (M.d : ℂ) ≠ 0 := by exact_mod_cast (dimension_pos M).ne'
  rw [he]
  congr 1
  field_simp
  linear_combination ht

/-- The self-block formula includes both independent coordinate deltas. -/
theorem self_orthogonality : selfOrthogonalityType.{u,v} := by
  intro G _ _ M a b c d
  have : FiniteDimensional ℂ M.space := Module.Finite.of_basis M.basis
  rw [← average_entry M M a b c d]
  rw [← Representation.IntertwiningMap.toLinearMap_apply, average_scalar]
  classical
  simp [LinearMap.trace_smulRight, Finsupp.single_apply]
  split_ifs <;> simp_all

/-- Schur's lemma annihilates the averaged map between different types. -/
theorem inequivalent_orthogonality : inequivalentOrthogonalityType.{u,v,w} := by
  intro G _ _ M N hne a b c d
  rw [← average_entry M N a b c d]
  have hz : average N.ρ M.ρ ((N.basis.coord d).smulRight (M.basis b)) = 0 := by
    by_contra hh
    obtain ⟨e, _⟩ := Schur.nonzeroIntertwiner N.ρ M.ρ N.irreducible M.irreducible _ hh
    exact hne ⟨e⟩
  simp [hz]

/-- The two coordinate deltas and the type delta in one formula. -/
theorem family_orthogonality : familyOrthogonalityType.{u,v} := by
  intro G _ _ F hF p q
  classical
  rcases p with ⟨i, a, b⟩
  rcases q with ⟨j, c, d⟩
  by_cases hij : i = j
  · subst j
    simpa using self_orthogonality (F.model i) a b c d
  · have hne : ¬ Nonempty ((F.model j).ρ.Equiv (F.model i).ρ) :=
      fun h => hij (hF j i h).symm
    rw [inequivalent_orthogonality (F.model i) (F.model j) hne]
    simp [hij]

theorem pairing_smul (f h : G → ℂ) (c d : ℂ) :
    UnitaritySpecs.functionPairingValue (c • f) (d • h) =
      (c * star d) * UnitaritySpecs.functionPairingValue f h := by
  obtain ⟨H, hH⟩ := functionPairing_positive (G := G)
  rw [← hH, H.smul_left, H.smul_right]
  ring

theorem normalized_pairing (F : UnitaryFamily.{u,v} G) (hF : Distinct F)
    (p q : FamilyIndex F) :
    UnitaritySpecs.functionPairingValue (familyNormalized F p)
      (familyNormalized F q) = if p = q then 1 else 0 := by
  classical
  rw [familyNormalized, familyNormalized, pairing_smul, family_orthogonality F hF]
  by_cases hpq : p = q
  · subst q
    simp only [ite_true, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp [(by exact_mod_cast (dimension_pos (F.model p.1)).ne' :
      ((F.model p.1).d : ℂ) ≠ 0)]
  · simp [hpq]

/-- Comparing any complete list with the upstream regular decomposition
transfers the sum-of-squares identity without prescribing the chosen models. -/
theorem family_square_sum (F : UnitaryFamily.{u,v} G) (hF : Distinct F)
    (hEx : Exhaustive.{u,v,u} F) :
    (∑ i : Fin F.n, (F.model i).d ^ 2) = Fintype.card G := by
  classical
  obtain ⟨C, hC, hCex⟩ := RegularMultiplicity.finite_family (G := G)
  have choices (i : Fin F.n) : ∃ j : Fin C.n,
      Nonempty ((RegularMultiplicitySpecs.idealRepresentation (C.space j)).Equiv (F.model i).ρ) :=
    RegularMultiplicity.exhaustive_from_regular C hCex (F.model i).ρ (F.model i).irreducible
  let t : Fin F.n → Fin C.n := fun i => (choices i).choose
  let e (i : Fin F.n) :
      (RegularMultiplicitySpecs.idealRepresentation (C.space (t i))).Equiv (F.model i).ρ :=
    (choices i).choose_spec.some
  have ht : Function.Injective t := by
    intro i j hij
    have ej : (RegularMultiplicitySpecs.idealRepresentation (C.space (t i))).Equiv
        (F.model j).ρ := hij ▸ e j
    exact hF i j ⟨(e i).symm.trans ej⟩
  have hs : Function.Surjective t := by
    intro j
    have : IsSimpleModule _ (C.space j) := hC.1 j
    obtain ⟨i, ⟨f⟩⟩ := hEx (RegularMultiplicitySpecs.idealRepresentation (C.space j))
      (RegularMultiplicity.ideal_irreducible (C.space j))
    let l := (RegularMultiplicity.idealModuleEquiv (C.space (t i))).symm.trans
      ((RegularMultiplicity.moduleEquivOfEquiv ((e i).trans f)).trans
        (RegularMultiplicity.idealModuleEquiv (C.space j)))
    exact ⟨i, hC.2 (t i) j ⟨l⟩⟩
  calc
    (∑ i : Fin F.n, (F.model i).d ^ 2) =
        ∑ j : Fin C.n, (Module.finrank ℂ (C.space j)) ^ 2 := by
      apply Fintype.sum_equiv (Equiv.ofBijective t ⟨ht, hs⟩)
      intro i
      exact congrArg (fun n : ℕ => n ^ 2)
        ((e i).toLinearEquiv.finrank_eq.trans (dimension (F.model i))).symm
    _ = Fintype.card G := (RegularMultiplicity.regular_decomposition C hC hCex).2.symm

theorem number_entries (F : UnitaryFamily.{u,v} G) (hF : Distinct F)
    (hEx : Exhaustive.{u,v,u} F) : Fintype.card (FamilyIndex F) = Fintype.card G := by
  rw [← family_square_sum F hF hEx]
  simp [FamilyIndex, Fintype.card_sigma, pow_two]

/-- Completeness uses the sum-of-squares identity only after orthogonality has
been established; no character-completeness statement is assumed. -/
theorem coefficient_basis : familyBasisType.{u,v} := by
  intro G _ _ F hF hEx
  classical
  obtain ⟨H, hH⟩ := functionPairing_positive (G := G)
  have hi : LinearIndependent ℂ (familyNormalized F) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    let f : (G → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun x => H.toFun x (familyNormalized F i)
        map_add' := fun x y => H.add_left x y _
        map_smul' := fun c x => H.smul_left c x _ }
    have hf (j : FamilyIndex F) : f (familyNormalized F j) = if j = i then 1 else 0 := by
      change H.toFun _ _ = _
      rw [hH, normalized_pairing F hF]
    have ht := congrArg f hg
    simpa [map_sum, hf, hi] using ht
  have hc : Fintype.card (FamilyIndex F) = Module.finrank ℂ (G → ℂ) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact number_entries F hF hEx
  have hn : Nonempty (FamilyIndex F) := by
    apply Fintype.card_pos_iff.mp
    rw [number_entries F hF hEx]
    exact Fintype.card_pos
  let B := basisOfLinearIndependentOfCardEqFinrank hi hc
  have hB (p : FamilyIndex F) : B p = familyNormalized F p := by
    exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hi hc) p
  exact ⟨B, hB, fun p q => by rw [hB, hB]; exact normalized_pairing F hF p q⟩

end P103.Ch08.MatrixCoefficientOrthogonality
