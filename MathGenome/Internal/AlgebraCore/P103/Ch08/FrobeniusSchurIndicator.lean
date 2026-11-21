import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.FrobeniusSchurIndicator
import MathGenome.Internal.AlgebraCore.P103.Ch08.Schur
import MathGenome.Internal.AlgebraCore.P103.Ch08.SquareCharacters
import MathGenome.Internal.AlgebraCore.P103.Ch08.UnitarityPairing
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.Complex.Polynomial.Basic

noncomputable section
universe u v
namespace P103.Ch08.FrobeniusSchurIndicator
open FrobeniusSchurSpecs
open scoped Classical
open private libraryIrreducible from MathGenome.Internal.AlgebraCore.P103.Ch08.Schur

/-- The source's character-sum normalization. -/
def indicator : indicatorType.{u,v} := fun ρ => indicatorValue ρ

variable {G : Type u} [Group G] {V : Type v} [AddCommGroup V] [Module ℂ V]

/-- Invariance makes the curried form an intertwiner to the contragredient. -/
def formMap (ρ : Representation ℂ G V) (B : LinearMap.BilinForm ℂ V)
    (hB : Invariant ρ B) : ρ.IntertwiningMap ρ.dual where
  toLinearMap := B
  isIntertwining' g := by
    ext x y
    change B (ρ g x) y = B x (ρ g⁻¹ y)
    simpa using hB g x (ρ g⁻¹ y)

/-- An intertwiner to the actual dual gives simultaneous invariance. -/
lemma invariant_of_intertwiner (ρ : Representation ℂ G V) (f : ρ.IntertwiningMap ρ.dual) :
    Invariant ρ f.toLinearMap := by
  intro g x y
  have h := congrArg (fun z : Module.Dual ℂ V => z (ρ g y)) (Representation.IntertwiningMap.isIntertwining ρ ρ.dual f g x)
  change f (ρ g x) (ρ g y) = (f x) (ρ g⁻¹ (ρ g y)) at h
  simpa using h

/-- This linear equivalence preserves the underlying bilinear function. -/
def formsEquivIntertwiners (ρ : Representation ℂ G V) :
    invariantForms ρ ≃ₗ[ℂ] (ρ.IntertwiningMap ρ.dual) where
  toFun B := formMap ρ B B.property
  invFun f := ⟨f.toLinearMap, invariant_of_intertwiner ρ f⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma invariant_flip {ρ : Representation ℂ G V} {B : LinearMap.BilinForm ℂ V}
    (hB : Invariant ρ B) : Invariant ρ B.flip := fun g x y => hB g y x

lemma formMap_ne_zero {ρ : Representation ℂ G V} {B : LinearMap.BilinForm ℂ V}
    (hB : Invariant ρ B) (hne : B ≠ 0) : formMap ρ B hB ≠ 0 := by
  intro h
  apply hne
  exact congrArg Representation.IntertwiningMap.toLinearMap h

lemma form_injective {ρ : Representation ℂ G V} (hρ : Irreducible ℂ G V ρ)
    {B : LinearMap.BilinForm ℂ V} (hB : Invariant ρ B) (hne : B ≠ 0) :
    Function.Injective B := by
  have := libraryIrreducible ρ hρ
  exact (Representation.IsIrreducible.injective_or_eq_zero (formMap ρ B hB)).resolve_right
    (formMap_ne_zero hB hne)

/-- Both radicals are invariant; irreducibility kills each of them. -/
theorem invariant_nondegenerate : nondegeneracyType.{u,v} := by
  intro G _ V _ _ _ ρ hρ B hB hne
  have hflip : B.flip ≠ 0 := by
    intro h
    apply hne
    ext x y
    exact congrArg (fun C : LinearMap.BilinForm ℂ V => C y x) h
  constructor
  · intro x hx
    apply form_injective hρ hB hne
    ext y
    simpa using hx y
  · intro y hy
    apply form_injective hρ (invariant_flip hB) hflip
    ext x
    simpa using hy x

/-- The given form, rather than an unrelated abstract isomorphism, supplies
an equivariant isomorphism to the dual. -/
def formEquiv {ρ : Representation ℂ G V} [FiniteDimensional ℂ V]
    (hρ : Irreducible ℂ G V ρ) {B : LinearMap.BilinForm ℂ V}
    (hB : Invariant ρ B) (hne : B ≠ 0) : ρ.Equiv ρ.dual :=
  (formMap ρ B hB).ofBijective
    (B.toDual (invariant_nondegenerate ρ hρ B hB hne)).bijective

@[simp] lemma formEquiv_apply {ρ : Representation ℂ G V} [FiniteDimensional ℂ V]
    (hρ : Irreducible ℂ G V ρ) {B : LinearMap.BilinForm ℂ V}
    (hB : Invariant ρ B) (hne : B ≠ 0) (x y : V) :
    formEquiv hρ hB hne x y = B x y := rfl

theorem selfDual_iff_existsForm : selfDualityType.{u,v} := by
  intro G _ V _ _ _ ρ hρ
  constructor
  · rintro ⟨e⟩
    refine ⟨e.toLinearMap, ?_, invariant_of_intertwiner ρ e.toIntertwiningMap⟩
    intro he
    have : Nontrivial V := hρ.1
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    apply hx
    apply e.injective
    simpa using congrArg (fun f : V →ₗ[ℂ] Module.Dual ℂ V => f x) he
  · rintro ⟨B, hne, hB⟩
    exact ⟨formEquiv hρ hB hne⟩

/-- Schur's lemma makes any invariant form a scalar multiple of a fixed
nonzero one. No self-duality hypothesis is added: it comes from the form. -/
lemma forms_scalar [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    (hρ : Irreducible ℂ G V ρ) {B : LinearMap.BilinForm ℂ V}
    (hB : Invariant ρ B) (hne : B ≠ 0) (C : LinearMap.BilinForm ℂ V)
    (hC : Invariant ρ C) : ∃ c : ℂ, C = c • B := by
  let e := formEquiv hρ hB hne
  let f := e.symm.toIntertwiningMap.comp (formMap ρ C hC)
  obtain ⟨c, hc, _⟩ := Schur.uniqueScalar ρ hρ f
  have he (x : V) : e.symm (C x) = c • x := by
    have hh := congrArg (fun t : ρ.IntertwiningMap ρ => t x) hc
    exact hh
  refine ⟨c, ?_⟩
  ext x y
  have hh := congrArg (fun z : V => e z y) (he x)
  have heB (a b : V) : e a b = B a b := rfl
  simpa only [e.apply_symm_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, heB] using hh

/-- Transposition has sign +1 or -1 on the line of invariant forms. -/
lemma form_symm_or_alt [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    (hρ : Irreducible ℂ G V ρ) {B : LinearMap.BilinForm ℂ V}
    (hB : Invariant ρ B) (hne : B ≠ 0) : B.IsSymm ∨ B.IsAlt := by
  let F := LinearMap.BilinForm.flipHom (R := ℂ) (M := V)
  obtain ⟨c, hc⟩ := forms_scalar hρ hB hne (F B) (invariant_flip hB)
  have hh : B = (c * c) • B := calc
    B = F (F B) := rfl
    _ = F (c • B) := congrArg F hc
    _ = c • F B := map_smul F c B
    _ = (c * c) • B := by rw [hc, smul_smul]
  have hc2 : c * c = 1 := by
    apply smul_left_injective (R := ℂ) hne
    simpa only [smul_smul, one_smul] using hh.symm
  rcases mul_self_eq_one_iff.mp hc2 with h | h
  · left
    apply LinearMap.BilinForm.isSymm_iff_flip.mpr
    simpa [h] using hc
  · right
    intro x
    have hh := congrArg (fun C : LinearMap.BilinForm ℂ V => C x x) hc
    change B x x = c * B x x at hh
    rw [h] at hh
    have ht : (2 : ℂ) * B x x = 0 := by
      calc
        (2 : ℂ) * B x x = B x x - (-1) * B x x := by ring
        _ = 0 := sub_eq_zero.mpr hh
    exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

/-- The two symmetry types cannot coexist on a nonzero invariant form. -/
lemma not_both_form_types [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    (hρ : Irreducible ℂ G V ρ) : ¬ (HasSymmetricForm ρ ∧ HasAlternatingForm ρ) := by
  rintro ⟨⟨B, hB0, hB, hBs⟩, ⟨C, hC0, hC, hCa⟩⟩
  obtain ⟨c, rfl⟩ := forms_scalar hρ hB hB0 C hC
  have hCs := hBs.smul c
  apply hC0
  ext x y
  have hs := hCs.eq x y
  have ha := hCa.neg_eq x y
  have ht : (2 : ℂ) * (c • B) x y = 0 := by
    calc
      (2 : ℂ) * (c • B) x y = (c • B) x y - (-(c • B) x y) := by ring
      _ = 0 := sub_eq_zero.mpr (hs.trans ha.symm)
  exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

/-! The character-to-form bridge works for arbitrary representations. -/
open SquareSpecs

/-- Pull a functional on an actual tensor quotient back to a bilinear form. -/
def quotientForm (R : Submodule ℂ (TensorSquare ℂ V))
    (f : (TensorSquare ℂ V ⧸ R) →ₗ[ℂ] ℂ) : LinearMap.BilinForm ℂ V :=
  (TensorProduct.mk ℂ V V).compr₂ (f.comp R.mkQ)

lemma quotientForm_kills (R : Submodule ℂ (TensorSquare ℂ V))
    (f : (TensorSquare ℂ V ⧸ R) →ₗ[ℂ] ℂ) :
    R ≤ LinearMap.ker (TensorProduct.lift (quotientForm R f)) := by
  rw [quotientForm, TensorProduct.lift_mk_compr₂]
  intro z hz
  change f (R.mkQ z) = 0
  rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero R).mpr hz, map_zero]

lemma quotientForm_invariant (ρ : Representation ℂ G V)
    (R : Submodule ℂ (TensorSquare ℂ V))
    (τ : Representation ℂ G (TensorSquare ℂ V ⧸ R))
    (hτ : ∀ g z, τ g (R.mkQ z) = R.mkQ (CharacterSpecs.tensorValue ρ ρ g z))
    (f : τ.IntertwiningMap (Representation.trivial ℂ G ℂ)) :
    Invariant ρ (quotientForm R f.toLinearMap) := by
  intro g x y
  have h := Representation.IntertwiningMap.isIntertwining τ
    (Representation.trivial ℂ G ℂ) f g (R.mkQ (TensorProduct.tmul ℂ x y))
  rw [hτ] at h
  exact h

/-- Universal property, retaining both the invariant condition and the exact
relation subspace. In the applications R is the symmetric/exterior relation
space from the shared square models. -/
def quotientFormsEquiv (ρ : Representation ℂ G V)
    (R : Submodule ℂ (TensorSquare ℂ V))
    (τ : Representation ℂ G (TensorSquare ℂ V ⧸ R))
    (hτ : ∀ g z, τ g (R.mkQ z) = R.mkQ (CharacterSpecs.tensorValue ρ ρ g z))
    (F : Submodule ℂ (LinearMap.BilinForm ℂ V))
    (hF : ∀ B, B ∈ F ↔ Invariant ρ B ∧ R ≤ LinearMap.ker (TensorProduct.lift B)) :
    F ≃ₗ[ℂ] (τ.IntertwiningMap (Representation.trivial ℂ G ℂ)) where
  toFun B :=
    { toLinearMap := R.liftQ (TensorProduct.lift B.val) ((hF B).mp B.property).2
      isIntertwining' g := by
        apply LinearMap.ext
        intro q
        refine Quotient.inductionOn' q (fun z => ?_)
        change R.liftQ (TensorProduct.lift B.val) ((hF B).mp B.property).2
          (τ g (R.mkQ z)) = R.liftQ (TensorProduct.lift B.val)
            ((hF B).mp B.property).2 (R.mkQ z)
        rw [hτ]
        change TensorProduct.lift B.val (CharacterSpecs.tensorValue ρ ρ g z) =
          TensorProduct.lift B.val z
        induction z using TensorProduct.inductionOn with
        | tmul x y => exact ((hF B).mp B.property).1 g x y
        | add z w hz hw => simp only [map_add, hz, hw] }
  invFun f := ⟨quotientForm R f.toLinearMap, (hF _).mpr
    ⟨quotientForm_invariant ρ R τ hτ f, quotientForm_kills R f.toLinearMap⟩⟩
  left_inv B := by
    apply Subtype.ext
    ext x y
    rfl
  right_inv f := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    refine Quotient.inductionOn' q (fun z => ?_)
    change TensorProduct.lift (quotientForm R f.toLinearMap) z = f (R.mkQ z)
    rw [quotientForm, TensorProduct.lift_mk_compr₂]
    rfl
  map_add' B C := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    refine Quotient.inductionOn' q (fun z => ?_)
    change TensorProduct.lift (B.val + C.val) z =
      TensorProduct.lift B.val z + TensorProduct.lift C.val z
    exact congrArg (fun f : TensorSquare ℂ V →ₗ[ℂ] ℂ => f z)
      ((TensorProduct.lift.equiv (RingHom.id ℂ) V V ℂ).map_add B.val C.val)
  map_smul' c B := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro q
    refine Quotient.inductionOn' q (fun z => ?_)
    change TensorProduct.lift (c • B.val) z = c • TensorProduct.lift B.val z
    exact congrArg (fun f : TensorSquare ℂ V →ₗ[ℂ] ℂ => f z)
      ((TensorProduct.lift.equiv (RingHom.id ℂ) V V ℂ).map_smul c B.val)

lemma symmetric_mem_iff (ρ : Representation ℂ G V) (B : LinearMap.BilinForm ℂ V) :
    B ∈ symmetricForms ρ ↔ Invariant ρ B ∧
      symmetricRelations ℂ V ≤ LinearMap.ker (TensorProduct.lift B) := by
  constructor
  · intro h
    refine ⟨h.1, Submodule.span_le.mpr ?_⟩
    rintro z ⟨x, y, rfl⟩
    change TensorProduct.lift B
      (TensorProduct.tmul ℂ x y - TensorProduct.tmul ℂ y x) = 0
    simpa only [map_sub, TensorProduct.lift.tmul, sub_eq_zero] using h.2.eq x y
  · intro h
    refine ⟨h.1, ⟨fun x y => ?_⟩⟩
    have hz := h.2 (Submodule.subset_span ⟨x, y, rfl⟩)
    change TensorProduct.lift B
      (TensorProduct.tmul ℂ x y - TensorProduct.tmul ℂ y x) = 0 at hz
    simpa only [map_sub, TensorProduct.lift.tmul, sub_eq_zero] using hz

lemma alternating_mem_iff (ρ : Representation ℂ G V) (B : LinearMap.BilinForm ℂ V) :
    B ∈ alternatingForms ρ ↔ Invariant ρ B ∧
      exteriorRelations ℂ V ≤ LinearMap.ker (TensorProduct.lift B) := by
  constructor
  · intro h
    refine ⟨h.1, Submodule.span_le.mpr ?_⟩
    rintro z ⟨x, rfl⟩
    exact h.2 x
  · intro h
    exact ⟨h.1, fun x => h.2 (Submodule.subset_span ⟨x, rfl⟩)⟩

/-- Invariant symmetric forms are invariant functionals on the usual symmetric
square quotient, not on an assumed alternative model. -/
def symmetricFormsEquiv (ρ : Representation ℂ G V) (S : SquareActions ρ) :
    symmetricForms ρ ≃ₗ[ℂ]
      (S.symmetric.IntertwiningMap (Representation.trivial ℂ G ℂ)) :=
  quotientFormsEquiv ρ (symmetricRelations ℂ V) S.symmetric S.symmetric_action
    (symmetricForms ρ) (symmetric_mem_iff ρ)

/-- The exterior relation is generated by x⊗x, so alternating means zero on
the diagonal without an extra convention about skew symmetry. -/
def alternatingFormsEquiv (ρ : Representation ℂ G V) (S : SquareActions ρ) :
    alternatingForms ρ ≃ₗ[ℂ]
      (S.exterior.IntertwiningMap (Representation.trivial ℂ G ℂ)) :=
  quotientFormsEquiv ρ (exteriorRelations ℂ V) S.exterior S.exterior_action
    (alternatingForms ρ) (alternating_mem_iff ρ)

lemma average_character_eq_forms [Fintype G] {W : Type*} [AddCommGroup W]
    [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ G W) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g : G, CharacterSpecs.characterValue σ g =
      (Module.finrank ℂ (σ.IntertwiningMap (Representation.trivial ℂ G ℂ)) : ℂ) := by
  have ht := character_pairing σ (Representation.trivial ℂ G ℂ)
  have htriv (g : G) :
      CharacterSpecs.characterValue (Representation.trivial ℂ G ℂ) g = 1 := by
    simp [CharacterSpecs.characterValue, Representation.trivial]
  simpa only [UnitaritySpecs.functionPairingValue, htriv, star_one, mul_one] using
    ht.1.trans ht.2

/-- The character difference, averaged and identified with the two invariant
form spaces via the actual quotient universal properties. -/
theorem indicator_dimension : dimensionFormulaType.{u,v} := by
  intro G _ _ V _ _ _ ρ
  obtain ⟨S⟩ := SquareCharacters.quotient_models (by norm_num : (2 : ℂ) ≠ 0) ρ
  have hs := (symmetricFormsEquiv ρ S).finrank_eq
  have ha := (alternatingFormsEquiv ρ S).finrank_eq
  rw [hs, ha, ← average_character_eq_forms, ← average_character_eq_forms,
    ← mul_sub, ← Finset.sum_sub_distrib]
  unfold indicatorValue
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  obtain ⟨h₁, h₂⟩ := SquareCharacters.square_characters
    (by norm_num : (2 : ℂ) ≠ 0) ρ S g
  rw [h₁, h₂]
  ring

/-- Every nonzero subspace of invariant forms is a line. -/
lemma form_subspace_dimension [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    (hρ : Irreducible ℂ G V ρ) (F : Submodule ℂ (LinearMap.BilinForm ℂ V))
    (hF : F ≤ invariantForms ρ) :
    Module.finrank ℂ F = if (∃ B : LinearMap.BilinForm ℂ V, B ∈ F ∧ B ≠ 0)
      then 1 else 0 := by
  classical
  split_ifs with h
  · obtain ⟨B, hBF, hB0⟩ := h
    let b : F := ⟨B, hBF⟩
    have hb : b ≠ 0 := fun he => hB0 (congrArg Subtype.val he)
    apply (finrank_eq_one_iff_of_nonzero' b hb).mpr
    intro c
    obtain ⟨a, ha⟩ := forms_scalar hρ (hF hBF) hB0 c.val (hF c.property)
    exact ⟨a, Subtype.ext ha.symm⟩
  · have hzero (B : F) : B = 0 := by
      apply Subtype.ext
      by_contra hne
      exact h ⟨B.val, B.property, hne⟩
    have : Subsingleton F := ⟨fun B C => (hzero B).trans (hzero C).symm⟩
    exact Module.finrank_eq_zero_of_subsingleton ℂ F

lemma symmetric_dimension [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    (hρ : Irreducible ℂ G V ρ) :
    Module.finrank ℂ (symmetricForms ρ) = if HasSymmetricForm ρ then 1 else 0 := by
  classical
  have ht := form_subspace_dimension hρ (symmetricForms ρ) (fun _ h => h.1)
  have hh : (∃ B : LinearMap.BilinForm ℂ V, B ∈ symmetricForms ρ ∧ B ≠ 0) ↔
      HasSymmetricForm ρ := by
    constructor
    · rintro ⟨B, ⟨hB, hs⟩, hne⟩
      exact ⟨B, hne, hB, hs⟩
    · rintro ⟨B, hne, hB, hs⟩
      exact ⟨B, ⟨hB, hs⟩, hne⟩
  simpa only [hh] using ht

lemma alternating_dimension [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    (hρ : Irreducible ℂ G V ρ) :
    Module.finrank ℂ (alternatingForms ρ) = if HasAlternatingForm ρ then 1 else 0 := by
  classical
  have ht := form_subspace_dimension hρ (alternatingForms ρ) (fun _ h => h.1)
  have hh : (∃ B : LinearMap.BilinForm ℂ V, B ∈ alternatingForms ρ ∧ B ≠ 0) ↔
      HasAlternatingForm ρ := by
    constructor
    · rintro ⟨B, ⟨hB, ha⟩, hne⟩
      exact ⟨B, hne, hB, ha⟩
    · rintro ⟨B, hne, hB, ha⟩
      exact ⟨B, ⟨hB, ha⟩, hne⟩
  simpa only [hh] using ht

lemma selfDual_iff_form_types [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    (hρ : Irreducible ℂ G V ρ) :
    SelfDual ρ ↔ HasSymmetricForm ρ ∨ HasAlternatingForm ρ := by
  rw [selfDual_iff_existsForm ρ hρ]
  constructor
  · rintro ⟨B, hB0, hB⟩
    rcases form_symm_or_alt hρ hB hB0 with hs | ha
    · exact Or.inl ⟨B, hB0, hB, hs⟩
    · exact Or.inr ⟨B, hB0, hB, ha⟩
  · rintro (⟨B, hB0, hB, _⟩ | ⟨B, hB0, hB, _⟩)
    all_goals exact ⟨B, hB0, hB⟩

/-- Frobenius–Schur classification, with no prior self-duality or form assumed. -/
theorem classification : classificationType.{u,v} := by
  intro G _ _ V _ _ _ ρ hρ
  classical
  have hdim := indicator_dimension ρ
  rw [symmetric_dimension hρ, alternating_dimension hρ] at hdim
  have hdual := selfDual_iff_form_types hρ
  have hdisjoint := not_both_form_types hρ
  by_cases hs : HasSymmetricForm ρ <;> by_cases ha : HasAlternatingForm ρ
  · exact False.elim (hdisjoint ⟨hs, ha⟩)
  all_goals simp_all <;> norm_num

end P103.Ch08.FrobeniusSchurIndicator
