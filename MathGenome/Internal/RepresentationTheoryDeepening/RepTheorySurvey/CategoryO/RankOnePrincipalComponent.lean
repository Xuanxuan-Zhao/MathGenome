import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.RankOnePrincipalComponent
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.RankOneVermas
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.ComponentBounds
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.OrderedVermaCovers
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.BGGReciprocity
import Batteries.Tactic.OpenPrivate

/-! The principal rank-one component and its indecomposable projective covers. -/

noncomputable section

open CategoryTheory Function UniversalEnvelopingAlgebra
open scoped Classical ModuleCat.Algebra
open Specs.LieAlgebrasAndRepresentations.VermaModules (U)
open Specs.LieAlgebrasAndRepresentations.RootDecomposition (rootSet_value rootSpace_value)
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights
  (weightWeylGroup weightReflection corootEvaluation)
open Specs.LieAlgebrasAndRepresentations.HarishChandraIsomorphism (rhoValue)
open Specs.LieAlgebrasAndRepresentations.ClassicalRootsA (cartan root)
open LieAlgebrasAndRepresentations.ClassicalRootsA (root_set root_apply)
open LieAlgebrasAndRepresentations (sl2_h_val sl2_e_val sl2_f_val sl2_relations)
open Specs.RepTheorySurvey.CategoryO
open Specs.RepTheorySurvey.CategoryO.RankOneVermas
open Specs.RepTheorySurvey.CategoryO.RankOnePrincipalComponent
open Specs.RepTheorySurvey.CategoryO.ComponentBounds
  (centralCharacter_value inComponent_value simpleLabels_value)
open Specs.RepTheorySurvey.CategoryO.ComponentProjectors (coset)
open Specs.RepTheorySurvey.CategoryO.ProjectiveCovers
  (IsIndecomposable componentObjects projectiveCover_value simpleIndex)
open Specs.RepTheorySurvey.CategoryO.BGGReciprocity
  (vermaMultiplicity compositionMultiplicity)

namespace RepTheorySurvey.CategoryO.RankOnePrincipalComponent

open private cartanH diagonal_expansion from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.RankOneVermas
open private verma_equiv_iff from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.BGGReciprocity

variable (D : Setup G) (std : IsStandard D)

private theorem weight_add (a b : ℂ) : weight D (a + b) = weight D a + weight D b := by
  ext x
  exact add_mul a b _

private theorem weight_sub (a b : ℂ) : weight D (a - b) = weight D a - weight D b := by
  ext x
  exact sub_mul a b _

private theorem weight_neg (a : ℂ) : weight D (-a) = -weight D a := by
  ext x
  exact neg_mul a _

private theorem weight_zero : weight D 0 = 0 := by
  ext x
  exact zero_mul _

private theorem weight_coordinates (μ : D.Weight) : weight D (μ (cartanH D std)) = μ := by
  obtain ⟨a, rfl⟩ := (RankOneVermas.weight_parameter D std).1.surjective μ
  rw [(RankOneVermas.weight_parameter D std).2 _ rfl]

private theorem weight_at_h (a : ℂ) : weight D a (cartanH D std) = a :=
  (RankOneVermas.weight_parameter D std).2 _ rfl a

private theorem root_coordinates (μ : D.Weight) :
    μ ∈ rootSet_value D.cartan ↔ μ (cartanH D std) = 2 ∨ μ (cartanH D std) = -2 := by
  have matrix_roots (H : LieSubalgebra ℂ G) (hH : H = cartan 1)
      (x : H) (hx : (x : G) = h) (η : Module.Dual ℂ H) :
      η ∈ rootSet_value H → η x = 2 ∨ η x = -2 := by
    subst H
    intro hη
    obtain ⟨i, j, hij, rfl⟩ := (root_set 1 η).mp hη
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · left
      rw [root_apply, hx]
      norm_num [sl2_h_val]
    · right
      rw [root_apply, hx]
      norm_num [sl2_h_val]
    · exact (hij rfl).elim
  have matrix_root_exists (H : LieSubalgebra ℂ G) (hH : H = cartan 1)
      (x : H) (hx : (x : G) = h) :
      (∃ η ∈ rootSet_value H, η x = 2) ∧ (∃ η ∈ rootSet_value H, η x = -2) := by
    subst H
    refine ⟨⟨root 1 0 1, (root_set 1 _).mpr ⟨0, 1, by decide, rfl⟩, ?_⟩,
      ⟨root 1 1 0, (root_set 1 _).mpr ⟨1, 0, by decide, rfl⟩, ?_⟩⟩
    all_goals
      rw [root_apply, hx]
      norm_num [sl2_h_val]
  refine ⟨matrix_roots D.cartan std.cartan _ rfl μ, ?_⟩
  rcases matrix_root_exists D.cartan std.cartan (cartanH D std) rfl with
    ⟨⟨α, hα, ha⟩, ⟨β, hβ, hb⟩⟩
  rintro (hμ | hμ)
  · rwa [← weight_coordinates D std μ, hμ, ← ha, weight_coordinates D std α]
  · rwa [← weight_coordinates D std μ, hμ, ← hb, weight_coordinates D std β]

include std

private theorem positive_root (μ : D.Weight) :
    μ ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive D.cartan D.direction ↔
      μ = weight D 2 := by
  have hf : f ∈ rootSpace_value D.cartan (weight D (-2)) := by
    apply (LieAlgebrasAndRepresentations.mem_rootSpace _ _ _).mpr
    intro x
    rw [diagonal_expansion D std x, smul_lie, (sl2_relations ℂ).2.1, smul_smul]
    change _ = ((-2 : ℂ) * x.val.val 0 0) • f
    rw [mul_comm]
  have hf' : f ∉ D.nPlus.toSubmodule := by
    rw [std.positive]
    intro hf'
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hf'
    have hh := congrArg (fun x : G => x.val 1 0) hc
    norm_num [sl2_f_val, sl2_e_val] at hh
  have hn : ¬ 0 < D.direction (weight D (-2)) := by
    intro hp
    apply hf'
    rw [(root_parts D).1]
    exact (le_iSup (fun a : {a : D.Weight // 0 < D.direction a} =>
      rootSpace_value D.cartan a.val) ⟨weight D (-2), hp⟩) hf
  have hr (b : ℂ) (hb : b = 2 ∨ b = -2) : weight D b ∈ rootSet_value D.cartan :=
    (root_coordinates D std _).mpr (by rwa [weight_at_h D std])
  refine ⟨?_, ?_⟩
  · rintro ⟨hμ, hp⟩
    rcases (root_coordinates D std _).mp hμ with hμ | hμ
    · rw [← weight_coordinates D std μ, hμ]
    · exfalso
      exact hn (by rwa [← weight_coordinates D std μ, hμ] at hp)
  · rintro rfl
    refine ⟨hr 2 (Or.inl rfl), ?_⟩
    have hne := D.regular _ (hr (-2) (Or.inr rfl))
    rw [weight_neg, map_neg] at hne hn
    exact lt_of_le_of_ne (by linarith) (neg_ne_zero.mp hne).symm

private theorem simple_root : ∃ i : D.Simple, D.alpha i = weight D 2 := by
  refine ⟨⟨weight D 2, (positive_root D std _).mpr rfl, ?_⟩, rfl⟩
  intro β hβ γ hγ
  rw [(positive_root D std _).mp hβ, (positive_root D std _).mp hγ, ← weight_add]
  intro he
  have hh := (RankOneVermas.weight_parameter D std).1.injective he
  norm_num at hh

omit std in
private theorem zero_sub_neg_two : weight D 0 - weight D (-2) = weight D 2 := by
  rw [← weight_sub]
  norm_num

private theorem negative_two_le_zero : weightLE_value D (weight D (-2)) (weight D 0) := by
  obtain ⟨i, hi⟩ := simple_root D std
  change weight D 0 - weight D (-2) ∈ Submodule.span ℕ (Set.range D.alpha)
  rw [zero_sub_neg_two, ← hi]
  exact Submodule.subset_span ⟨i, rfl⟩

private theorem same_coset : coset D (weight D (-2)) = coset D (weight D 0) := by
  obtain ⟨i, hi⟩ := simple_root D std
  apply (Submodule.Quotient.eq _).mpr
  change weight D (-2) - weight D 0 ∈ Submodule.span ℤ (Set.range D.alpha)
  rw [← neg_sub, zero_sub_neg_two, ← hi]
  exact Submodule.neg_mem _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem rho_eq : rhoValue D.cartan D.direction = weight D 1 := by
  let P := {a : rootSet_value D.cartan // 0 < D.direction a.val}
  let p : P := ⟨⟨weight D 2, ((positive_root D std _).mpr rfl).1⟩,
    ((positive_root D std _).mpr rfl).2⟩
  have hp (a : P) : a = p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (positive_root D std _).mp ⟨a.val.property, a.property⟩
  change (1 / 2 : ℂ) • (∑ᶠ a : P, a.val.val) = _
  rw [finsum_eq_single _ p (fun a ha => (ha (hp a)).elim)]
  ext x
  change (1 / 2 : ℂ) * (2 * x.val.val 0 0) = 1 * x.val.val 0 0
  ring

private theorem weightReflection_eq (α : D.Weight) (hα : α (Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value D.cartan α) = 2)
    (μ : D.Weight) : weightReflection D.cartan α μ = -μ := by
  have ha : α (cartanH D std) ≠ 0 := by
    intro he
    have hh : α = 0 := by rw [← weight_coordinates D std α, he, weight_zero]
    simp [hh] at hα
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • α = μ := by
    refine ⟨μ (cartanH D std) / α (cartanH D std), ?_⟩
    have hInjective : Injective (fun ν : D.Weight => ν (cartanH D std)) := by
      intro ν ξ he
      exact (weight_coordinates D std ν).symm.trans
        ((congrArg (weight D) he).trans (weight_coordinates D std ξ))
    apply hInjective
    dsimp only
    rw [LinearMap.smul_apply, smul_eq_mul, div_mul_cancel₀ _ ha]
  rw [← hc, map_smul, weightReflection, dite_eq_left hα]
  have hn : corootEvaluation D.cartan α α = 2 := hα
  change c • Module.reflection hn α = -(c • α)
  rw [Module.reflection_apply_self, smul_neg]

private theorem weyl_sign (w : weightWeylGroup D.cartan) :
    (∀ μ : D.Weight, w.val μ = μ) ∨ (∀ μ : D.Weight, w.val μ = -μ) := by
  obtain ⟨w, hw⟩ := w
  change (∀ μ : D.Weight, w μ = μ) ∨ (∀ μ : D.Weight, w μ = -μ)
  unfold weightWeylGroup at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, _, rfl⟩ := hx
    by_cases hα : α (Specs.LieAlgebrasAndRepresentations.RootForm.coroot_value D.cartan α) = 2
    · exact Or.inr (weightReflection_eq D std α hα)
    · exact Or.inl (by intro μ; rw [weightReflection, dite_eq_right hα]; rfl)
  | one => exact Or.inl fun _ => rfl
  | mul x y _ _ ihx ihy =>
    rcases ihx with hx | hx <;> rcases ihy with hy | hy
    · exact Or.inl (fun μ => show x (y μ) = μ by rw [hx, hy])
    · exact Or.inr (fun μ => show x (y μ) = -μ by rw [hx, hy])
    · exact Or.inr (fun μ => show x (y μ) = -μ by rw [hx, hy])
    · exact Or.inl (fun μ => show x (y μ) = μ by rw [hx, hy, neg_neg])
  | inv x _ ih =>
    rcases ih with hx | hx
    · exact Or.inl (fun μ => x.injective (by change x (x.symm μ) = x μ; rw [x.apply_symm_apply, hx]))
    · exact Or.inr (fun μ => x.injective (by change x (x.symm μ) = x (-μ); rw [x.apply_symm_apply, hx, neg_neg]))

private theorem central_character (a : ℂ) :
    centralCharacter_value D (weight D a) = centralCharacter_value D (weight D 0) ↔ a = 0 ∨ a = -2 := by
  have hχ := (ComponentBounds.centralCharacter_spec D).2 (weight D 0) (weight D a)
  rw [eq_comm, hχ, rho_eq D std, ← weight_add, ← weight_add, zero_add]
  constructor
  · rintro ⟨w, hw⟩
    rcases weyl_sign D std w with h | h
    · rw [h] at hw
      have hh := (RankOneVermas.weight_parameter D std).1.injective hw
      exact Or.inl (by linear_combination hh)
    · rw [h, ← weight_neg] at hw
      have hh := (RankOneVermas.weight_parameter D std).1.injective hw
      exact Or.inr (by linear_combination hh)
  · rintro (rfl | rfl)
    · exact ⟨1, by simp⟩
    · obtain ⟨i, hi⟩ := simple_root D std
      have hroot := i.property.1.1
      have hnorm : D.alpha i (D.h i) = 2 := by
        rw [hi]
        exact (RankOneVermas.weight_parameter D std).2 _ (std.triple i).2.2 2
      let w : weightWeylGroup D.cartan :=
        ⟨weightReflection D.cartan (D.alpha i), Subgroup.subset_closure ⟨_, hroot, rfl⟩⟩
      refine ⟨w, ?_⟩
      change _ = weightReflection D.cartan (D.alpha i) (weight D 1)
      rw [weightReflection_eq D std _ hnorm, ← weight_neg]
      norm_num

omit std in
theorem principal_central_character : CentralCharacterType :=
  central_character

omit std in
theorem simple_labels : SimpleLabelsType := by
  intro D std
  ext μ
  obtain ⟨a, rfl⟩ := (RankOneVermas.weight_parameter D std).1.surjective μ
  change (centralCharacter_value D (weight D a) = centralCharacter_value D (weight D 0) ∧
    coset D (weight D a) = coset D (weight D 0)) ↔ _
  rw [central_character D std]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
    (RankOneVermas.weight_parameter D std).1.injective.eq_iff]
  exact ⟨And.left, fun ha => ⟨ha, ha.elim (fun e => e ▸ rfl) (fun e => e ▸ same_coset D std)⟩⟩


section Covers

omit std

open ProjectiveFiltrations (Layer VermaFlag)
open private inComponent_of_injective from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.ComponentBounds
open private inComponent_of_surjection from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.ProjectiveCovers
open private subobject_mem_O from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.BGGReciprocity
open private surjective_mem_O from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.SimpleObjects

private theorem cover_exists_in_component (μ : D.Weight) :
    ∃ (X : O.{0, 0} D) (p : X.obj →ₗ[U G] L D μ),
      inComponent_value D X.obj (simpleIndex D μ) ∧ IsIndecomposable X.obj ∧
      projectiveCover_value X p := by
  obtain ⟨Λ, hΛ, hμ, _, p₀, S, _, hS, _, _, _, hind, hp⟩ :=
    ProjectiveCovers.exists_projectiveCover D μ
  obtain ⟨hO, hK, _, _⟩ :=
    ProjectiveCovers.projectedTruncation_projective D (simpleIndex D μ) μ Λ hμ hΛ
  let X : O.{0, 0} D := ⟨ModuleCat.of (U G) S, hS⟩
  let Y : O.{0, 0} D := ⟨_, hO⟩
  exact ⟨X, p₀.domRestrict S,
    inComponent_of_injective D (X := X) (Y := Y) _ S.subtype S.subtype_injective hK, hind, hp⟩

private theorem cover_component (μ : D.Weight) (X : O.{0, 0} D)
    (p : X.obj →ₗ[U G] L D μ) (hp : projectiveCover_value X p) :
    inComponent_value D X.obj (simpleIndex D μ) ∧ IsIndecomposable X.obj := by
  obtain ⟨Y, q, hY, hind, hq⟩ := cover_exists_in_component D μ
  let Lμ : O.{0, 0} D := ⟨L D μ, (simpleQuotient_in_O D μ).1⟩
  obtain ⟨e, _⟩ := ProjectiveCovers.unique_over_target D X Y Lμ p q hp hq
  let j := Submodule.orderIsoMapComapOfBijective e.toLinearMap e.bijective
  refine ⟨inComponent_of_injective D (X := X) (Y := Y) _ e.toLinearMap e.injective hY, ?_⟩
  refine ⟨fun h => hind.1 (by simpa using congrArg j h), ?_⟩
  intro A B hAB
  rcases hind.2 (j A) (j B) (j.isCompl_iff.mp hAB) with h | h
  · exact Or.inl (j.injective (by simpa using h))
  · exact Or.inr (j.injective (by simpa using h))

private theorem flag_labels {X : O.{0, 0} D}
    {k : Specs.RepTheorySurvey.CategoryO.ComponentProjectors.Index D}
    (hX : inComponent_value D X.obj k)
    {weights : List D.Weight} {A B : Submodule (U G) X.obj}
    (F : VermaFlag D weights A B) :
    ∀ ν ∈ weights, ν ∈ simpleLabels_value D k := by
  induction F with
  | nil A => simp
  | @cons ξ l A B C hAB hfactor F ih =>
    intro ν hν
    rcases List.mem_cons.mp hν with rfl | hν
    · obtain ⟨E⟩ := hfactor
      let Y : O.{0, 0} D := ⟨ModuleCat.of (U G) B, subobject_mem_O D X B⟩
      have hY := inComponent_of_injective D (X := Y) (Y := X) k B.subtype
        B.subtype_injective hX
      let f : Y.obj →ₗ[U G] L D ν :=
        (quotientMap D ν).comp (E.toLinearMap.comp ((A.comap B.subtype).mkQ))
      have hf : Surjective f :=
        (quotientMap_surjective D ν).comp (E.surjective.comp (Submodule.mkQ_surjective _))
      exact (ComponentBounds.simpleQuotient_mem_component_iff D k ν).mp
        (inComponent_of_surjection k f hf hY)
    · exact ih ν hν

private def botLayer {X : Type} [AddCommGroup X] [Module (U G) X]
    (B : Submodule (U G) X) : Layer ⊥ B ≃ₗ[U G] B :=
  Submodule.quotEquivOfEqBot _ (by rw [Submodule.comap_bot, Submodule.ker_subtype])

private def topLayer {X : Type} [AddCommGroup X] [Module (U G) X]
    (B : Submodule (U G) X) : Layer B ⊤ ≃ₗ[U G] (X ⧸ B) :=
  Submodule.Quotient.equiv _ _ Submodule.topEquiv
    (Submodule.map_comap_eq_of_surjective Submodule.topEquiv.surjective B)

private theorem simpleFactor {V : Type} [AddCommGroup V] [Module (U G) V]
    {ν μ : D.Weight} (E : V ≃ₗ[U G] L D ν) :
    Nonempty (V ≃ₗ[U G] L D μ) ↔ ν = μ := by
  rw [← simpleQuotient_equiv_iff D ν μ]
  exact ⟨fun ⟨F⟩ => ⟨E.symm.trans F⟩, fun ⟨F⟩ => ⟨E.trans F⟩⟩

private theorem compositionMultiplicity_eq_sum {X : ModuleCat (U G)}
    (s : CompositionSeries (Submodule (U G) X)) (μ : D.Weight) :
    compositionMultiplicity D μ s =
      ∑ i : Fin s.length, if Nonempty (Layer (s i.castSucc) (s i.succ) ≃ₗ[U G] L D μ)
        then 1 else 0 :=
  (Finset.sum_boole (R := ℕ)
    (fun i : Fin s.length => Nonempty (Layer (s i.castSucc) (s i.succ) ≃ₗ[U G] L D μ))
    Finset.univ).symm

private theorem one_step_series {X : ModuleCat (U G)} (a : D.Weight)
    (E : X ≃ₗ[U G] L D a) :
    ∃ s : CompositionSeries (Submodule (U G) X), s.head = ⊥ ∧ s.last = ⊤ ∧
      ∀ μ : D.Weight, compositionMultiplicity D μ s = if a = μ then 1 else 0 := by
  let e := ((botLayer (⊤ : Submodule (U G) X)).trans Submodule.topEquiv).trans E
  let s : CompositionSeries (Submodule (U G) X) :=
    { length := 1
      toFun := ![⊥, ⊤]
      step := fun i => by
        fin_cases i
        change (⊥ : Submodule (U G) X) ⋖ ⊤
        exact (covBy_iff_quot_is_simple bot_le).mpr
          (e.isSimpleModule_iff.mpr (simpleQuotient_simple D a)) }
  refine ⟨s, rfl, rfl, fun μ => ?_⟩
  rw [compositionMultiplicity_eq_sum D s μ]
  change (∑ i : Fin 1, if Nonempty (Layer (s i.castSucc) (s i.succ) ≃ₗ[U G] L D μ)
    then 1 else 0) = _
  rw [Fin.sum_univ_one]
  change (if Nonempty (Layer (⊥ : Submodule (U G) X) ⊤ ≃ₗ[U G] L D μ)
    then 1 else 0) = _
  rw [simpleFactor D e]

private theorem two_step_series {X : ModuleCat (U G)} (B : Submodule (U G) X)
    (a b : D.Weight) (E : B ≃ₗ[U G] L D a) (F : (X ⧸ B) ≃ₗ[U G] L D b) :
    ∃ s : CompositionSeries (Submodule (U G) X), s.head = ⊥ ∧ s.last = ⊤ ∧
      ∀ μ : D.Weight, compositionMultiplicity D μ s =
        (if a = μ then 1 else 0) + (if b = μ then 1 else 0) := by
  let e := (botLayer B).trans E
  let f := (topLayer B).trans F
  let s : CompositionSeries (Submodule (U G) X) :=
    { length := 2
      toFun := ![⊥, B, ⊤]
      step := fun i => by
        fin_cases i
        · change (⊥ : Submodule (U G) X) ⋖ B
          exact (covBy_iff_quot_is_simple bot_le).mpr
            (e.isSimpleModule_iff.mpr (simpleQuotient_simple D a))
        · change B ⋖ (⊤ : Submodule (U G) X)
          exact (covBy_iff_quot_is_simple le_top).mpr
            (f.isSimpleModule_iff.mpr (simpleQuotient_simple D b)) }
  refine ⟨s, rfl, rfl, fun μ => ?_⟩
  rw [compositionMultiplicity_eq_sum D s μ]
  change (∑ i : Fin 2, if Nonempty (Layer (s i.castSucc) (s i.succ) ≃ₗ[U G] L D μ)
    then 1 else 0) = _
  rw [Fin.sum_univ_two]
  change (if Nonempty (Layer ⊥ B ≃ₗ[U G] L D μ) then 1 else 0) +
    (if Nonempty (Layer B ⊤ ≃ₗ[U G] L D μ) then 1 else 0) = _
  simp only [simpleFactor D e, simpleFactor D f]

private theorem neg_two_not_natural (m : ℕ) : (-2 : ℂ) ≠ m := by
  intro he
  have he' := congrArg Complex.re he
  simp at he'
  have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
  linarith

include std

private theorem principal_series :
    (∃ s : CompositionSeries (Submodule (U G) (Verma D 0)),
      s.head = ⊥ ∧ s.last = ⊤ ∧
      ∀ μ : D.Weight, compositionMultiplicity D μ s =
        (if weight D (-2) = μ then 1 else 0) + (if weight D 0 = μ then 1 else 0)) ∧
    (∃ s : CompositionSeries (Submodule (U G) (Verma D (-2))),
      s.head = ⊥ ∧ s.last = ⊤ ∧
      ∀ μ : D.Weight, compositionMultiplicity D μ s = if weight D (-2) = μ then 1 else 0) := by
  obtain ⟨q, hq, hker, hbi⟩ := RankOneVermas.quotient_kernel D std
  have hsurj (a : ℂ) : Surjective (q a) := by
    have he : q a = quotientMap D (weight D a) :=
      LinearMap.ext fun x => (hq a x).trans (quotientMap_apply D (weight D a) x).symm
    rw [he]
    exact quotientMap_surjective D (weight D a)
  let e := LinearEquiv.ofBijective (q (-2)) (hbi (-2) neg_two_not_natural)
  have hker0 := hker 0
  rw [Nat.cast_zero] at hker0
  constructor
  · let B := (q 0).ker
    obtain ⟨_, _, _, hE⟩ := RankOneVermas.integral_submodule D std 0
    obtain ⟨E, _⟩ := hE
    have E' : Verma D (-2) ≃ₗ[U G] B := by
      have he : -((0 : ℕ) : ℂ) - 2 = -2 := by norm_num
      rw [he, Nat.cast_zero] at E
      exact E.trans (LinearEquiv.ofEq _ _ hker0.symm)
    exact two_step_series D B (weight D (-2)) (weight D 0) (E'.symm.trans e)
      ((q 0).quotKerEquivOfSurjective (hsurj 0))
  · exact one_step_series D (weight D (-2)) e

private theorem principal_flag_counts (μ : D.Weight) (X : O.{0, 0} D)
    (p : X.obj →ₗ[U G] L D μ) (hp : projectiveCover_value X p)
    (weights : List D.Weight) (F : VermaFlag D (X := X.obj) weights ⊥ ⊤) :
    (weights.countP (fun ν => decide (ν = weight D 0)) =
      (if weight D (-2) = μ then 1 else 0) + (if weight D 0 = μ then 1 else 0)) ∧
    (weights.countP (fun ν => decide (ν = weight D (-2))) =
      if weight D (-2) = μ then 1 else 0) := by
  obtain ⟨⟨s₀, hs₀, hs₀', hm₀⟩, ⟨s₂, hs₂, hs₂', hm₂⟩⟩ := principal_series D std
  have reciprocity (ν : D.Weight) (s : CompositionSeries (Submodule (U G) (M D ν)))
      (h₀ : s.head = ⊥) (h₁ : s.last = ⊤) :
      weights.countP (fun ξ => decide (ξ = ν)) = compositionMultiplicity D μ s := by
    obtain ⟨_, hV, hS⟩ := BGGReciprocity.bgg_reciprocity D μ ν X p hp
    simpa only [vermaMultiplicity, verma_equiv_iff D] using
      (hV weights F).trans (hS s h₀ h₁).symm
  exact ⟨(reciprocity _ s₀ hs₀ hs₀').trans (hm₀ μ),
    (reciprocity _ s₂ hs₂ hs₂').trans (hm₂ μ)⟩

private theorem principal_index_eq (a : ℂ) (ha : a = 0 ∨ a = -2) :
    simpleIndex D (weight D a) = principalIndex D := by
  rcases ha with rfl | rfl
  · rfl
  · exact Prod.ext ((central_character D std _).mpr (Or.inr rfl)) (same_coset D std)

private theorem weights_ne : weight D (-2) ≠ weight D 0 := by
  intro he
  have hh := (RankOneVermas.weight_parameter D std).1.injective he
  norm_num at hh

private theorem principal_ordered_flag (a : ℂ) (ha : a = 0 ∨ a = -2)
    (X : O.{0, 0} D) (p : X.obj →ₗ[U G] Simple D a) (hp : projectiveCover_value X p) :
    (a = 0 → VermaFlag D (X := X.obj) [weight D 0] ⊥ ⊤) ∧
    (a = -2 → VermaFlag D (X := X.obj) [weight D 0, weight D (-2)] ⊥ ⊤) := by
  obtain ⟨weights, F, horder⟩ := OrderedVermaCovers.ordered_verma_flag_of_cover D (weight D a) X p hp
  have hk := (cover_component D (weight D a) X p hp).1
  rw [principal_index_eq D std a ha] at hk
  have hlabels := flag_labels D hk F
  rw [simple_labels D std] at hlabels
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hlabels
  obtain ⟨hcount₀, hcount₂⟩ := principal_flag_counts D std (weight D a) X p hp weights F
  have hlen : weights.length =
      weights.countP (fun ν => decide (ν = weight D 0)) +
      weights.countP (fun ν => decide (ν = weight D (-2))) := by
    rw [List.length_eq_countP_add_countP (fun ν => decide (ν = weight D 0))]
    congr 1
    apply List.countP_congr
    intro ν hν
    rcases hlabels ν hν with rfl | rfl
    · simp [Ne.symm (weights_ne D std)]
    · simp [weights_ne D std]
  constructor
  · rintro rfl
    simp only [weights_ne D std, ↓reduceIte, zero_add] at hcount₀ hcount₂
    obtain ⟨ν, hν⟩ := List.length_eq_one_iff.mp (by omega : weights.length = 1)
    have hξ : ν = weight D 0 := by
      by_contra hn
      simp [hν, hn] at hcount₀
    rwa [hν, hξ] at F
  · rintro rfl
    simp only [Ne.symm (weights_ne D std), ↓reduceIte, add_zero] at hcount₀ hcount₂
    have hw : ∃ ν ξ, weights = [ν, ξ] := by
      have hn : weights.length = 2 := by omega
      exact ⟨_, _, List.eq_getElem_of_length_eq_two weights hn⟩
    obtain ⟨ν, ξ, hνξ⟩ := hw
    have hv := hlabels ν (by simp [hνξ])
    have hx := hlabels ξ (by simp [hνξ])
    rcases hv with rfl | rfl <;> rcases hx with rfl | rfl
    · simp [hνξ, Ne.symm (weights_ne D std)] at hcount₂
    · rwa [hνξ] at F
    · have hordered : [weight D (-2), weight D 0].Pairwise
          (fun ν ξ => weightLE_value D ν ξ → ν = ξ) := hνξ ▸ horder
      have hbad := (List.pairwise_cons.mp hordered).1
        (weight D 0) (by simp) (negative_two_le_zero D std)
      exact (weights_ne D std hbad).elim
    · simp [hνξ, weights_ne D std] at hcount₀

omit std

private theorem one_layer_cover (X : O.{0, 0} D)
    (F : VermaFlag D (X := X.obj) [weight D 0] ⊥ ⊤) :
    Nonempty (X.obj ≃ₗ[U G] Verma D 0) := by
  cases F with
  | cons _ hE tail =>
    cases tail
    obtain ⟨E⟩ := hE
    exact ⟨Submodule.topEquiv.symm.trans ((botLayer ⊤).symm.trans E)⟩

private theorem two_layer_cover (X : O.{0, 0} D)
    (F : VermaFlag D (X := X.obj) [weight D 0, weight D (-2)] ⊥ ⊤) :
    ∃ (i : Verma D 0 →ₗ[U G] X.obj) (q : X.obj →ₗ[U G] Verma D (-2)),
      Injective i ∧ Exact i q ∧ Surjective q := by
  cases F with
  | @cons _ _ _ B _ _ hE rest =>
    cases rest with
    | cons _ hF tail =>
      cases tail
      obtain ⟨E⟩ := hE
      obtain ⟨F⟩ := hF
      let e := E.symm.trans (botLayer B)
      let f := (topLayer B).symm.trans F
      let i := B.subtype.comp e.toLinearMap
      let q := f.toLinearMap.comp B.mkQ
      refine ⟨i, q, B.subtype_injective.comp e.injective, ?_,
        f.surjective.comp B.mkQ_surjective⟩
      rw [LinearMap.exact_iff, LinearEquiv.ker_comp, Submodule.ker_mkQ]
      symm
      change (B.subtype.comp e.toLinearMap).range = B
      rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr e.surjective),
        Submodule.range_subtype]

include std

private theorem verma_vector_ne_zero (a : ℂ) :
    loweringPower D a 0 ≠ 0 := by
  obtain ⟨b, hb⟩ := (RankOneVermas.pbw_basis D std a).1
  rw [← hb]
  exact b.ne_zero 0

private theorem nonsplit {X : O.{0, 0} D} (hind : IsIndecomposable X.obj)
    (i : Verma D 0 →ₗ[U G] X.obj) (q : X.obj →ₗ[U G] Verma D (-2))
    (hi : Injective i) (hex : Exact i q) :
    ¬ ∃ s : Verma D (-2) →ₗ[U G] X.obj, RightInverse s q := by
  rintro ⟨s, hs⟩
  let proj := s.rangeRestrict.comp q
  have hproj (x : s.range) : proj x = x := by
    obtain ⟨y, hy⟩ := x.property
    apply Subtype.ext
    change s (q (x : X.obj)) = (x : X.obj)
    rw [← hy, hs]
  have hc := LinearMap.isCompl_of_proj hproj
  have hker : proj.ker = q.ker :=
    LinearMap.ker_comp_of_ker_eq_bot q (LinearMap.ker_eq_bot.mpr
      (fun _ _ h => hs.injective (congrArg Subtype.val h)))
  change IsCompl s.range proj.ker at hc
  rw [hker, LinearMap.exact_iff.mp hex] at hc
  rcases hind.2 _ _ hc with h | h
  · have hz := LinearMap.mem_range_self s (loweringPower D (-2) 0)
    rw [h, Submodule.mem_bot] at hz
    exact verma_vector_ne_zero D std (-2) (hs.injective (hz.trans s.map_zero.symm))
  · have hz := LinearMap.mem_range_self i (loweringPower D 0 0)
    rw [h, Submodule.mem_bot] at hz
    exact verma_vector_ne_zero D std 0 (hi (hz.trans i.map_zero.symm))

omit std in
theorem cover_structure : CoverStructureType := by
  intro D std
  constructor
  · intro X p hp
    exact one_layer_cover D X ((principal_ordered_flag D std 0 (Or.inl rfl) X p hp).1 rfl)
  · intro X p hp
    obtain ⟨i, q, hi, hex, hq⟩ :=
      two_layer_cover D X ((principal_ordered_flag D std (-2) (Or.inr rfl) X p hp).2 rfl)
    exact ⟨i, q, hi, hex, hq, nonsplit D std (cover_component D _ X p hp).2 i q hi hex⟩

open Specs.RepTheorySurvey.CategoryO.ComponentProjectors (component component_map_mem)
open private component_in_own_index projectiveLift surjective_of_epi_component
  from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.ProjectiveCovers

omit std in
theorem principal_projectivity : ProjectivityType := by
  intro D X hX
  let k := principalIndex D
  let X₀ : (componentObjects D k).FullSubcategory := ⟨X, hX⟩
  change Projective X₀ ↔ Projective X
  constructor
  · intro hproj
    let := hproj
    constructor
    intro B C a q hq
    let F := ComponentProjectors.projectorFunctor D k
    let : F.PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_preserves_shortExact_right F
        (fun S hS => by
          have hs := ComponentProjectors.projector_shortExact D k S hS
          exact ⟨hs.exact, hs.epi_g⟩)
    let B₀ : (componentObjects D k).FullSubcategory := ⟨F.obj B, component_in_own_index k B⟩
    let C₀ : (componentObjects D k).FullSubcategory := ⟨F.obj C, component_in_own_index k C⟩
    let e : B₀ ⟶ C₀ := ObjectProperty.homMk (F.map q)
    let : Epi e := (componentObjects D k).ι.epi_of_epi_map
      (show Epi (F.map q) by infer_instance)
    have hmem (x : X.obj) : a.hom.hom x ∈ component D C.obj k := by
      apply component_map_mem a.hom.hom k
      rw [show component D X.obj k = ⊤ from hX]
      exact Submodule.mem_top
    let a₀ : X₀ ⟶ C₀ := ObjectProperty.homMk (ObjectProperty.homMk (ModuleCat.ofHom
      (a.hom.hom.codRestrict (component D C.obj k) hmem)))
    obtain ⟨b, hb⟩ := Projective.factors a₀ e
    let lift := (component D B.obj k).subtype.comp b.hom.hom.hom
    refine ⟨ObjectProperty.homMk (ModuleCat.ofHom lift), ?_⟩
    apply ObjectProperty.hom_ext
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun x => congrArg (fun f : X₀ ⟶ C₀ =>
      Subtype.val (show component D C.obj k from f.hom.hom.hom x)) hb)
  · intro hproj
    constructor
    intro B C a e he
    obtain ⟨b, hb⟩ := projectiveLift hproj a.hom.hom.hom e.hom.hom.hom
      (surjective_of_epi_component k e)
    refine ⟨ObjectProperty.homMk (ObjectProperty.homMk (ModuleCat.ofHom b)), ?_⟩
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact ModuleCat.hom_ext hb

omit std in
theorem indecomposable_projectives : IndecomposableProjectivesType := by
  intro D std
  constructor
  · intro a ha
    simpa only [principal_index_eq D std a ha] using cover_exists_in_component D (weight D a)
  · intro X hX hind hproj
    let : IsNoetherian (U G) X.obj :=
      (isFiniteLength_iff_isNoetherian_isArtinian.mp (categoryO_finiteLength D X)).1
    let : IsCoatomic (Submodule (U G) X.obj) := inferInstance
    obtain ⟨J, hJ, _⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule (U G) X.obj)).resolve_left hind.1
    let Y : ModuleCat (U G) := ModuleCat.of (U G) (X.obj ⧸ J)
    let q : X.obj →ₗ[U G] Y := J.mkQ
    let Y₀ : O.{0, 0} D := ⟨Y, surjective_mem_O D X.property q J.mkQ_surjective⟩
    have hYS : CategoryTheory.Simple Y₀ :=
      (simple_iff_isSimpleModule D Y₀).mpr (isSimpleModule_iff_isCoatom.mpr hJ)
    have hY := inComponent_of_surjection (principalIndex D) q J.mkQ_surjective hX
    obtain ⟨μ, ⟨hμ, ⟨E⟩⟩, _⟩ :=
      (ComponentBounds.simpleClassification D (principalIndex D) Y₀).mp ⟨hYS, hY⟩
    rw [simple_labels D std] at hμ
    have isCover (a : ℂ) (ha : μ = weight D a) :
        ∃ p : X.obj →ₗ[U G] Simple D a, projectiveCover_value X p := by
      subst μ
      let Z : O.{0, 0} D := ⟨Simple D a, (simpleQuotient_in_O D (weight D a)).1⟩
      let p : X.obj →ₗ[U G] Z.obj := E.toLinearMap.comp q
      exact ⟨p, ProjectiveCovers.projectiveCover_of_indecomposable D X Z p hproj hind
        ((simple_iff_isSimpleModule D Z).mpr (simpleQuotient_simple D _))
        (E.surjective.comp J.mkQ_surjective)⟩
    exact (Set.mem_insert_iff.mp hμ).imp (isCover 0) (isCover (-2) ∘ Set.mem_singleton_iff.mp)

end Covers

end RepTheorySurvey.CategoryO.RankOnePrincipalComponent
