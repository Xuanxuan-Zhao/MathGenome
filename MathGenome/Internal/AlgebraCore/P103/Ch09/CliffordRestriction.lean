import MathGenome.Internal.AlgebraCore.Specs.P103.Ch09.CliffordRestriction
import MathGenome.Internal.AlgebraCore.P103.Ch08.CentralIdempotents
import Batteries.Tactic.OpenPrivate

noncomputable section
universe u v w
namespace P103.Ch09.CliffordRestriction
open P103.Ch08 CliffordRestrictionSpecs
open private libraryIrreducible from MathGenome.Internal.AlgebraCore.P103.Ch08.Schur
open scoped MonoidAlgebra

variable {G : Type u} [Group G] (A : Subgroup G) [A.Normal]
variable {V : Type v} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V)

@[simp] theorem conjugation_inverse (g : G) (a : A) :
    conjugation A g⁻¹ (conjugation A g a) = a := by
  apply Subtype.ext
  simp [conjugation, mul_assoc]

@[simp] theorem conjugation_inverse' (g : G) (a : A) :
    conjugation A g (conjugation A g⁻¹ a) = a := by
  simpa using conjugation_inverse A g⁻¹ a

/-- Translate an A-invariant subspace by the actual action of g on V. -/
def translate (g : G) (U : Subrepresentation (restriction A ρ)) :
    Subrepresentation (restriction A ρ) where
  toSubmodule := U.toSubmodule.map (ρ g)
  apply_mem_toSubmodule a := by
    rintro _ ⟨v, hv, rfl⟩
    refine ⟨ρ (g⁻¹ * a * g) v, U.apply_mem_toSubmodule (conjugation A g a) hv, ?_⟩
    simp [restriction, ← Module.End.mul_apply, ← map_mul, mul_assoc]

/-- Translation identifies the conjugate representation with the translated subspace. -/
def translateEquiv (g : G) (U : Subrepresentation (restriction A ρ)) :
    (conjugate A g U.toRepresentation).Equiv (translate A ρ g U).toRepresentation :=
  Representation.Equiv.mk
    (Submodule.equivMapOfInjective (ρ g) (ρ.apply_bijective g).injective U.toSubmodule)
    (by
      intro a
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change ρ g (ρ (g⁻¹ * a * g) v.val) = ρ a (ρ g v.val)
      simp [← Module.End.mul_apply, ← map_mul, mul_assoc])

/-- Twisting preserves equivariant equivalences, on the same underlying map. -/
def conjugateEquiv {W : Type w} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ A V} {τ : Representation ℂ A W}
    (g : G) (e : σ.Equiv τ) : (conjugate A g σ).Equiv (conjugate A g τ) :=
  Representation.Equiv.mk e.toLinearEquiv (fun a => e.isIntertwining' (conjugation A g a))

/-- Twisting by g and then g⁻¹ recovers the representation. -/
def conjugateInverseEquiv (g : G) (σ : Representation ℂ A V) :
    (conjugate A g⁻¹ (conjugate A g σ)).Equiv σ :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ V) (by
    intro a
    change σ (conjugation A g (conjugation A g⁻¹ a)) = σ a
    rw [conjugation_inverse'])

/-- The regular-ideal family satisfies the canonical isotypic interface. -/
theorem family_valid (C : RegularMultiplicitySpecs.Family A)
    (hC : RegularMultiplicitySpecs.Valid C) : FourierSpecs.Valid (fourierFamily A C) := by
  refine ⟨fun i => ?_, ?_⟩
  · have := hC.1 i
    exact RegularMultiplicity.ideal_irreducible (C.space i)
  · intro i j he
    apply hC.2 i j
    exact ⟨(RegularMultiplicity.idealModuleEquiv (C.space i)).symm.trans
      ((RegularMultiplicity.moduleEquivOfEquiv he.some).trans
        (RegularMultiplicity.idealModuleEquiv (C.space j)))⟩

theorem family_complete (C : RegularMultiplicitySpecs.Family A)
    (hC : RegularMultiplicitySpecs.Exhaustive.{u,u} C) :
    FourierSpecs.Complete (fourierFamily A C) := hC

/-- Forward inclusion for transport, proved directly from the sum of all copies. -/
theorem map_component_le (C : RegularMultiplicitySpecs.Family A)
    (g : G) (i j : Fin C.n)
    (e : (conjugate A g (RegularMultiplicitySpecs.idealRepresentation (C.space i))).Equiv
      (RegularMultiplicitySpecs.idealRepresentation (C.space j))) :
    (component A C ρ i).map (ρ g) ≤ component A C ρ j := by
  unfold component CentralIdempotentSpecs.isotypic
  simp_rw [Submodule.map_iSup]
  apply iSup_le
  intro U
  apply iSup_le
  rintro ⟨f⟩
  exact le_iSup_of_le (translate A ρ g U) (le_iSup_of_le
    ⟨e.symm.trans ((conjugateEquiv A g f).trans (translateEquiv A ρ g U))⟩ le_rfl)

/-- The action carries the entire intrinsic component onto its conjugate. -/
theorem transport : transportType.{u,v} := by
  intro G _ _ A _ C _ _ V _ _ ρ g i j he
  obtain ⟨e⟩ := he
  apply le_antisymm (map_component_le A ρ C g i j e)
  have einv : (conjugate A g⁻¹
      (RegularMultiplicitySpecs.idealRepresentation (C.space j))).Equiv
      (RegularMultiplicitySpecs.idealRepresentation (C.space i)) :=
    (conjugateEquiv A g⁻¹ e.symm).trans
      (conjugateInverseEquiv A g (RegularMultiplicitySpecs.idealRepresentation (C.space i)))
  intro x hx
  have hm := map_component_le A ρ C g⁻¹ j i einv
  have hin : ρ g⁻¹ x ∈ component A C ρ i := hm ⟨x, hx, rfl⟩
  exact ⟨ρ g⁻¹ x, hin, ρ.self_inv_apply g x⟩

/-- Twisting by a group automorphism preserves nonzero irreducibility. -/
theorem conjugate_irreducible (g : G) (σ : Representation ℂ A V)
    (hσ : Irreducible ℂ A V σ) : Irreducible ℂ A V (conjugate A g σ) := by
  refine ⟨hσ.1, fun W => ?_⟩
  let U : Subrepresentation σ := ⟨W.toSubmodule, fun a v hv => by
    have h := W.apply_mem_toSubmodule (conjugation A g⁻¹ a) hv
    simpa only [conjugate, MonoidHom.comp_apply, conjugation_inverse'] using h⟩
  rcases hσ.2 U with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun X : Subrepresentation σ => X.toSubmodule) h
  · right
    apply Subrepresentation.toSubmodule_injective
    exact congrArg (fun X : Subrepresentation σ => X.toSubmodule) h

/-- Equivariant equivalences preserve the nonzero irreducibility convention. -/
theorem irreducible_equiv {W : Type w} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ A V} {τ : Representation ℂ A W}
    (e : σ.Equiv τ) (hσ : Irreducible ℂ A V σ) : Irreducible ℂ A W τ := by
  have : Nontrivial V := hσ.1
  have := libraryIrreducible σ hσ
  have : IsSimpleModule ℂ[A] τ.asModule :=
    IsSimpleModule.congr (RegularMultiplicity.moduleEquivOfEquiv e).symm
  have : Representation.IsIrreducible τ :=
    (Representation.irreducible_iff_isSimpleModule_asModule τ).mpr inferInstance
  exact ⟨IsSimpleModule.nontrivial ℂ[A] τ.asModule, fun U => eq_bot_or_eq_top U⟩

/-- Irreducibility makes the translates of any nonzero subspace span V. -/
theorem translates_span (hρ : Irreducible ℂ G V ρ)
    (W : Submodule ℂ V) (hW : W ≠ ⊥) :
    (⨆ g : G, W.map (ρ g)) = ⊤ := by
  let S := ⨆ g : G, W.map (ρ g)
  have hstable (g : G) : S.map (ρ g) ≤ S := by
    dsimp [S]
    rw [Submodule.map_iSup]
    apply iSup_le
    intro h
    rw [← Submodule.map_comp]
    have he : (ρ g).comp (ρ h) = ρ (g * h) := (ρ.map_mul g h).symm
    rw [he]
    exact le_iSup (fun h : G => W.map (ρ h)) (g * h)
  let U : Subrepresentation ρ := ⟨S, fun g v hv => hstable g ⟨v, hv, rfl⟩⟩
  rcases hρ.2 U with h | h
  · have hbot : S = ⊥ := congrArg Subrepresentation.toSubmodule h
    exfalso
    apply hW
    apply bot_unique
    have hle : W ≤ S := by
      simpa only [map_one, Module.End.one_eq_id, Submodule.map_id] using
        (le_iSup (fun g : G => W.map (ρ g)) 1)
    exact hle.trans_eq hbot
  · exact congrArg Subrepresentation.toSubmodule h

/-- An absent conjugate type is killed by the central projection on every translate. -/
theorem translate_le_kernel [Fintype A]
    (C : RegularMultiplicitySpecs.Family A) (hC : RegularMultiplicitySpecs.Valid C)
    (hEx : RegularMultiplicitySpecs.Exhaustive.{u,u} C)
    (g : G) (i j : Fin C.n)
    (hne : ¬ Nonempty
      ((conjugate A g (RegularMultiplicitySpecs.idealRepresentation (C.space i))).Equiv
        (RegularMultiplicitySpecs.idealRepresentation (C.space j)))) :
    (component A C ρ i).map (ρ g) ≤ LinearMap.ker
      ((restriction A ρ).asAlgebraHom (CentralIdempotentSpecs.idempotent (fourierFamily A C) j)) := by
  unfold component CentralIdempotentSpecs.isotypic
  simp_rw [Submodule.map_iSup]
  apply iSup_le
  intro U
  apply iSup_le
  rintro ⟨e⟩
  let T := translate A ρ g U
  let f := (conjugateEquiv A g e).trans (translateEquiv A ρ g U)
  have hi := (family_valid A C hC).1 i
  have hT := irreducible_equiv A f (conjugate_irreducible A g _ hi)
  have hj : ¬ Nonempty
      (((fourierFamily A C).representation j).Equiv T.toRepresentation) := by
    rintro ⟨h⟩
    exact hne ⟨f.trans h.symm⟩
  have hz := (CentralIdempotents.simple_action (fourierFamily A C)
    (family_valid A C hC) (family_complete A C hEx) T.toRepresentation hT j).2 hj
  intro x hx
  have hh := CentralIdempotents.restriction_action (restriction A ρ) T
    (CentralIdempotentSpecs.idempotent (fourierFamily A C) j) ⟨x, hx⟩
  rw [hz] at hh
  exact hh.symm

/-- The intrinsic components exhaust the restricted representation. -/
theorem components_span [Finite G]
    (C : RegularMultiplicitySpecs.Family A) (hC : RegularMultiplicitySpecs.Valid C)
    (hEx : RegularMultiplicitySpecs.Exhaustive.{u,u} C) :
    (⨆ i, component A C ρ i) = ⊤ := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  apply top_unique
  rw [← CentralIdempotents.irreducibles_span (restriction A ρ)]
  apply iSup_le
  intro U
  apply iSup_le
  intro hU
  obtain ⟨i, ⟨e⟩⟩ := FourierTransform.complete_exhaustive (fourierFamily A C)
    (family_complete A C hEx) U.toRepresentation hU
  have hle : U.toSubmodule ≤ component A C ρ i :=
    le_iSup_of_le U (le_iSup_of_le ⟨e⟩ le_rfl)
  exact hle.trans (le_iSup (fun i => component A C ρ i) i)

/-- The occurring simple types form one conjugacy orbit. -/
theorem single_orbit : orbitType.{u,v} := by
  intro G _ _ A _ C hC hEx V _ _ ρ hρ
  classical
  letI : Fintype A := Fintype.ofFinite A
  have : Nontrivial V := hρ.1
  refine ⟨?_, ?_⟩
  · by_contra! h
    have hb : (⨆ i, component A C ρ i) = ⊥ := iSup_eq_bot.mpr h
    exact (bot_ne_top : (⊥ : Submodule ℂ V) ≠ ⊤)
      (hb.symm.trans (components_span A ρ C hC hEx))
  · intro i j hi hj
    by_contra! h
    have hker : (⨆ g : G, (component A C ρ i).map (ρ g)) ≤ LinearMap.ker
        ((restriction A ρ).asAlgebraHom
          (CentralIdempotentSpecs.idempotent (fourierFamily A C) j)) :=
      iSup_le fun g => translate_le_kernel A ρ C hC hEx g i j (fun ⟨e⟩ => (h g).false e)
    rw [translates_span ρ hρ (component A C ρ i) hi] at hker
    have hz := LinearMap.ker_eq_top.mp (top_unique hker)
    apply hj
    change CentralIdempotentSpecs.isotypic (fourierFamily A C) (restriction A ρ) j = ⊥
    rw [← CentralIdempotents.range_eq_isotypic (fourierFamily A C)
      (family_valid A C hC) (family_complete A C hEx), hz]
    exact LinearMap.range_zero

/-- Translating an intertwiner gives a linear equivalence of multiplicity spaces. -/
def homConjugationEquiv {W : Type w} [AddCommGroup W] [Module ℂ W]
    (g : G) (σ : Representation ℂ A W) :
    (σ.IntertwiningMap (restriction A ρ)) ≃ₗ[ℂ]
      ((conjugate A g σ).IntertwiningMap (restriction A ρ)) where
  toFun f :=
    { toLinearMap := (ρ g).comp f.toLinearMap
      isIntertwining' a := by
        apply LinearMap.ext
        intro x
        change ρ g (f (σ (conjugation A g a) x)) = ρ a (ρ g (f x))
        rw [f.isIntertwining]
        change ρ g (ρ (g⁻¹ * a * g) (f x)) = ρ a (ρ g (f x))
        simp [← Module.End.mul_apply, ← map_mul, mul_assoc] }
  invFun f :=
    { toLinearMap := (ρ g⁻¹).comp f.toLinearMap
      isIntertwining' a := by
        apply LinearMap.ext
        intro x
        change ρ g⁻¹ (f (σ a x)) = ρ a (ρ g⁻¹ (f x))
        have hf := Representation.IntertwiningMap.isIntertwining
          (conjugate A g σ) (restriction A ρ) f (conjugation A g⁻¹ a) x
        change f (σ (conjugation A g (conjugation A g⁻¹ a)) x) =
          ρ (g⁻¹⁻¹ * a * g⁻¹) (f x) at hf
        rw [conjugation_inverse'] at hf
        rw [hf]
        simp [← Module.End.mul_apply, ← map_mul, mul_assoc] }
  left_inv f := by ext x; exact ρ.inv_self_apply g (f x)
  right_inv f := by ext x; exact ρ.self_inv_apply g (f x)
  map_add' f h := by ext x; exact (ρ g).map_add (f x) (h x)
  map_smul' c f := by ext x; exact (ρ g).map_smul c (f x)

/-- Isomorphic choices of a type give linearly isomorphic multiplicity spaces. -/
def homTypeEquiv {W : Type w} [AddCommGroup W] [Module ℂ W]
    {X : Type*} [AddCommGroup X] [Module ℂ X]
    {σ : Representation ℂ A W} {τ : Representation ℂ A X} (e : σ.Equiv τ) :
    (σ.IntertwiningMap (restriction A ρ)) ≃ₗ[ℂ]
      (τ.IntertwiningMap (restriction A ρ)) :=
  (Representation.IntertwiningMap.equivLinearMapAsModule σ (restriction A ρ)).trans
    ((RegularMultiplicity.homCongr (RegularMultiplicity.moduleEquivOfEquiv e)
      (LinearEquiv.refl ℂ[A] (restriction A ρ).asModule)).trans
        (Representation.IntertwiningMap.equivLinearMapAsModule τ (restriction A ρ)).symm)

/-- Equal multiplicities count actual copies by the upstream decomposition theorem. -/
theorem equal_multiplicity : equalMultiplicityType.{u,v} := by
  intro G _ _ A _ C hC hEx V _ _ ρ hρ i j hi hj
  obtain ⟨g, ⟨e⟩⟩ := (single_orbit A C hC hEx ρ hρ).2 i j hi hj
  exact ((homConjugationEquiv A ρ g
    (RegularMultiplicitySpecs.idealRepresentation (C.space i))).trans
      (homTypeEquiv A ρ e)).finrank_eq

/-- Clifford restriction with a complete list of actual simple types and an
actual decomposition, without any additional hypothesis on the restriction. -/
theorem clifford_restriction : cliffordType.{u,v} := by
  intro G _ _ A _ V _ _ ρ hρ
  classical
  letI : Fintype A := Fintype.ofFinite A
  have := RegularMultiplicity.finite_dimensional ρ hρ
  obtain ⟨C, hC, hEx⟩ := RegularMultiplicity.finite_family.{u,u} (G := A)
  refine ⟨C, hC, hEx, ?_, (single_orbit A C hC hEx ρ hρ).1, ?_, ?_⟩
  · exact (RegularMultiplicity.multiplicity_decomposition C hC
      (RegularMultiplicity.exhaustive_from_regular C hEx) (restriction A ρ)).1
  · intro g i
    have := hC.1 i
    obtain ⟨j, ⟨e⟩⟩ := RegularMultiplicity.exhaustive_from_regular C hEx
      (conjugate A g (RegularMultiplicitySpecs.idealRepresentation (C.space i)))
      (conjugate_irreducible A g _ (RegularMultiplicity.ideal_irreducible (C.space i)))
    exact ⟨j, ⟨e.symm⟩, transport A C hC hEx ρ g i j ⟨e.symm⟩⟩
  · intro i j hi hj
    exact ⟨(single_orbit A C hC hEx ρ hρ).2 i j hi hj,
      equal_multiplicity A C hC hEx ρ hρ i j hi hj⟩

end P103.Ch09.CliffordRestriction
