import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.CategoryO.ComponentBounds
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.ComponentProjectors
import Batteries.Tactic.OpenPrivate

/-! Simple labels and weight bounds in the components of finite category O. -/

noncomputable section

open CategoryTheory UniversalEnvelopingAlgebra
open Specs.LieAlgebrasAndRepresentations.VermaModules (U highestVector_value)
open Specs.LieAlgebrasAndRepresentations.FiniteModuleWeights (weightWeylGroup)
open Specs.LieAlgebrasAndRepresentations.HarishChandraIsomorphism (rhoValue)
open Specs.LieAlgebrasAndRepresentations.SimpleHighestWeightQuotient (quotientHighestVector)
open scoped Classical ModuleCat.Algebra

namespace RepTheorySurvey.CategoryO.ComponentBounds

open Specs.RepTheorySurvey.CategoryO.ComponentBounds
open ComponentProjectors (Center CentralCharacter Index coset component centralPart cosetPart)
open Specs.RepTheorySurvey.CategoryO.ComponentProjectors (difference)
open private submodule_mem_O surjective_mem_O from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.CategoryO.SimpleObjects
open private finite_weightWeylGroup from
  MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.ChevalleyRestriction

universe u v w

abbrev centralCharacter : CentralCharacterType.{u} := @centralCharacter_value

set_option linter.checkUnivs false in
abbrev inComponent : InComponentType.{u, v} := @inComponent_value

abbrev simpleLabels : SimpleLabelsType.{u} := @simpleLabels_value

theorem centralCharacter_spec : CentralCharacterSpecType.{u} := by
  intro g _ _ _ D
  obtain ⟨_, _, _, χ, _, _, _, hscalar, horbit, _⟩ :=
    _root_.LieAlgebrasAndRepresentations.CentralCharacters.central_characters.{u, u}
      D.semisimple D.cartan D.direction D.regular
  have hM (μ : D.Weight) (z : Center g) (x : M D μ) : z.val • x = χ μ z • x :=
    (hscalar μ (character D μ) (character_unique D μ).1 z).1 x
  have hχ (μ : D.Weight) : centralCharacter D μ = χ μ := by
    have hchosen : ∀ (z : Center g) (x : M D μ), z.val • x = centralCharacter D μ z • x := by
      unfold centralCharacter centralCharacter_value
      exact Classical.epsilon_spec (p := fun ψ : CentralCharacter g =>
        ∀ (z : Center g) (x : M D μ), z.val • x = ψ z • x) ⟨χ μ, hM μ⟩
    let x : M D μ := highestVector_value D.cartan D.direction (character D μ)
    have hx : x ≠ 0 := (verma_mem_O D μ).2.1
    exact AlgHom.ext fun z => smul_left_injective ℂ hx ((hchosen z x).symm.trans (hM μ z x))
  refine ⟨fun μ z => ?_, fun μ ν => ?_⟩
  · change (∀ x : M D μ, z.val • x = centralCharacter D μ z • x) ∧
      (∀ x : L D μ, z.val • x = centralCharacter D μ z • x)
    rw [hχ]
    let : IsSimpleModule (U g) (L D μ) := simpleQuotient_simple D μ
    let : Nontrivial (L D μ) := IsSimpleModule.nontrivial (U g) (L D μ)
    exact ⟨hM μ z, (hscalar μ (character D μ) (character_unique D μ).1 z).2
      (quotientMap D μ) (quotientMap_surjective D μ)⟩
  · change centralCharacter D μ = centralCharacter D ν ↔ _
    rw [hχ, hχ]
    exact horbit μ ν

variable {g : Type u} [LieRing g] [LieAlgebra ℂ g] [FiniteDimensional ℂ g]
variable (D : Setup g)

private theorem map_weight {X : ModuleCat.{v} (U g)} {Y : ModuleCat.{w} (U g)}
    (f : X →ₗ[U g] Y) (μ : D.Weight) {x : X}
    (hx : x ∈ weightSpace D.cartan X μ) : f x ∈ weightSpace D.cartan Y μ := by
  refine (mem_weightSpace D.cartan Y μ (f x)).mpr fun h => ?_
  rw [← f.map_smul, (mem_weightSpace D.cartan X μ x).mp hx h, f.map_smul_of_tower]

private theorem inComponent_of_surjective {X : ModuleCat.{v} (U g)}
    {Y : ModuleCat.{w} (U g)} (k : Index D) (f : X →ₗ[U g] Y)
    (hf : Function.Surjective f) (hX : inComponent D X k) : inComponent D Y k := by
  have hcoset : cosetPart D X k.2 ≤ (cosetPart D Y k.2).comap f := by
    apply Submodule.span_le.mpr
    rintro x ⟨μ, hμ, hx⟩
    exact Submodule.subset_span ⟨μ, hμ, map_weight D f μ hx⟩
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ component D X k := by
    change component D X k = ⊤ at hX
    rw [hX]
    exact Submodule.mem_top
  refine ⟨(ComponentProjectors.centralPart_membership Y k.1 _).mpr fun z => ?_, hcoset hx.2⟩
  obtain ⟨n, hn⟩ := (ComponentProjectors.centralPart_membership X k.1 x).mp hx.1 z
  exact ⟨n, by rw [← f.map_smul, hn, map_zero]⟩

theorem simpleQuotient_mem_component_iff : SimpleQuotientMemComponentType.{u} := by
  intro g _ _ _ D k μ
  obtain ⟨hO, _, hv⟩ := simpleQuotient_in_O D μ
  let v : L D μ := quotientHighestVector D.cartan D.direction (character D μ)
  let j : Index D := (centralCharacter D μ, coset D μ)
  have hj : v ∈ component D (L D μ) j := by
    refine ⟨(ComponentProjectors.centralPart_membership (L D μ) j.1 v).mpr ?_,
      Submodule.subset_span ⟨μ, rfl, hv.2.1⟩⟩
    intro z
    refine ⟨1, ?_⟩
    have hz := ((centralCharacter_spec D).1 μ z).2 v
    rw [pow_one]
    change (z.val - algebraMap ℂ (U g) (centralCharacter D μ z)) • v = 0
    rw [sub_smul, algebraMap_smul, hz, sub_self]
  change inComponent D (L D μ) k ↔ μ ∈ simpleLabels D k
  constructor
  · intro hk
    have hkj : j = k := by
      by_contra hne
      have hind := (ComponentProjectors.component_decomposition D ⟨L D μ, hO⟩).1.submodule_iSupIndep
      have hdis := hind.pairwiseDisjoint hne
      have hkv : v ∈ component D (L D μ) k := by
        change component D (L D μ) k = ⊤ at hk
        rw [hk]
        exact Submodule.mem_top
      exact hv.1 ((Submodule.disjoint_def.mp hdis) v hj hkv)
    exact ⟨congrArg Prod.fst hkj, congrArg Prod.snd hkj⟩
  · rintro ⟨hc, hξ⟩
    have hkj : j = k := Prod.ext hc hξ
    change component D (L D μ) k = ⊤
    apply top_unique
    rw [← hkj, ← hv.2.2.2]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hj)

theorem simpleClassification : SimpleClassificationType.{u, v} := by
  intro g _ _ _ D k X
  change (Simple X ∧ inComponent D X.obj k) ↔
    ∃! μ : D.Weight, μ ∈ simpleLabels D k ∧ Nonempty (X.obj ≃ₗ[U g] L D μ)
  constructor
  · rintro ⟨hS, hX⟩
    obtain ⟨μ, ⟨e⟩, hμ⟩ := (CategoryO.simpleClassification D X).mp hS
    refine ⟨μ, ⟨(simpleQuotient_mem_component_iff D k μ).mp ?_, ⟨e⟩⟩,
      fun ν hν => hμ ν hν.2⟩
    exact inComponent_of_surjective D k e.toLinearMap e.surjective hX
  · rintro ⟨μ, ⟨hμ, ⟨e⟩⟩, _⟩
    exact ⟨(simple_iff_isSimpleModule D X).mpr (e.isSimpleModule_iff.mpr (simpleQuotient_simple D μ)),
      inComponent_of_surjective D k e.symm.toLinearMap e.symm.surjective
        ((simpleQuotient_mem_component_iff D k μ).mpr hμ)⟩

theorem finite_simpleLabels : FiniteSimpleLabelsType.{u} := by
  intro g _ _ _ D k
  change (simpleLabels D k).Finite
  by_cases h : (simpleLabels D k).Nonempty
  · obtain ⟨μ, hμ⟩ := h
    let : Finite (weightWeylGroup D.cartan) := finite_weightWeylGroup D.cartan D.semisimple
    let ρ := rhoValue D.cartan D.direction
    let f (s : weightWeylGroup D.cartan) : D.Weight := s.val (μ + ρ) - ρ
    apply (Set.finite_range f).subset
    intro ν hν
    have he : centralCharacter D μ = centralCharacter D ν := hμ.1.trans hν.1.symm
    obtain ⟨s, hs⟩ := ((centralCharacter_spec D).2 μ ν).mp he
    exact ⟨s, by change s.val (μ + ρ) - ρ = ν; rw [← hs, add_sub_cancel_right]⟩
  · rw [Set.not_nonempty_iff_eq_empty.mp h]
    exact Set.finite_empty

private theorem exists_label_bound (k : Index D) :
    ∃ Λ : D.Weight, coset D Λ = k.2 ∧ ∀ μ ∈ simpleLabels D k, weightLE D μ Λ := by
  classical
  obtain ⟨η, hη⟩ := (Submodule.mkQ_surjective (Q D)) k.2
  let : Finite D.Simple := finite_simple_roots D
  let : Fintype D.Simple := Fintype.ofFinite D.Simple
  let : Finite (simpleLabels D k) := (finite_simpleLabels D k).to_subtype
  let : Fintype (simpleLabels D k) := Fintype.ofFinite (simpleLabels D k)
  have hcoords (μ : simpleLabels D k) : ∃ c : D.Simple → ℤ,
      (∑ i, c i • D.alpha i) = μ.val - η := by
    apply (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).mp
    change μ.val - η ∈ Q D
    apply (Submodule.Quotient.eq (Q D)).mp
    exact μ.property.2.trans hη.symm
  choose c hc using hcoords
  -- Include the zero coordinates of the representative even if there are no labels.
  let s : Finset (Option (simpleLabels D k)) := Finset.univ
  have hs : s.Nonempty := ⟨none, Finset.mem_univ _⟩
  let coeff (i : D.Simple) (μ : Option (simpleLabels D k)) : ℤ := μ.elim 0 (fun μ => c μ i)
  let m (i : D.Simple) : ℤ := s.sup' hs (coeff i)
  have hm (μ : simpleLabels D k) (i : D.Simple) : c μ i ≤ m i :=
    Finset.le_sup' (coeff i) (show some μ ∈ s from Finset.mem_univ _)
  let β : D.Weight := ∑ i, m i • D.alpha i
  have hβ : β ∈ Q D := by
    change β ∈ Submodule.span ℤ (Set.range D.alpha)
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℤ)).mpr ⟨m, rfl⟩
  refine ⟨η + β, ?_, fun μ hμ => ?_⟩
  · change (Q D).mkQ (η + β) = k.2
    rw [map_add, hη, show (Q D).mkQ β = 0 from (Submodule.Quotient.mk_eq_zero _).mpr hβ, add_zero]
  · change η + β - μ ∈ Submodule.span ℕ (Set.range D.alpha)
    let ν : simpleLabels D k := ⟨μ, hμ⟩
    refine (Submodule.mem_span_range_iff_exists_fun (R := ℕ)).mpr
      ⟨fun i => (m i - c ν i).toNat, ?_⟩
    calc
      (∑ i, (m i - c ν i).toNat • D.alpha i) = ∑ i, (m i - c ν i) • D.alpha i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← Nat.cast_smul_eq_nsmul ℤ, Int.toNat_of_nonneg (sub_nonneg.mpr (hm ν i))]
      _ = β - (μ - η) := by
        simp only [sub_smul, Finset.sum_sub_distrib, β, show _ = μ - η from hc ν]
      _ = η + β - μ := by abel

private theorem inComponent_of_injective {X Y : O.{u, v} D} (k : Index D)
    (f : X.obj →ₗ[U g] Y.obj) (hf : Function.Injective f)
    (hY : inComponent D Y.obj k) : inComponent D X.obj k := by
  change component D Y.obj k = ⊤ at hY
  change component D X.obj k = ⊤
  have hX := (ComponentProjectors.component_decomposition D X).1
  have hind := (ComponentProjectors.component_decomposition D Y).1.submodule_iSupIndep
  apply top_unique
  rw [← hX.submodule_iSup_eq_top]
  apply iSup_le
  intro j
  by_cases hj : j = k
  · subst j
    exact le_refl _
  · intro x hx
    have hjx := Specs.RepTheorySurvey.CategoryO.ComponentProjectors.component_map_mem f j hx
    have hkx : f x ∈ component D Y.obj k := by rw [hY]; exact Submodule.mem_top
    have hx0 := (Submodule.disjoint_def.mp (hind.pairwiseDisjoint hj)) (f x) hjx hkx
    rw [hf (hx0.trans f.map_zero.symm)]
    exact zero_mem _

private theorem weightLE_of_simpleQuotient_weight (μ ν : D.Weight)
    (hy : weightSpace D.cartan (L D μ) ν ≠ ⊥) : weightLE D ν μ := by
  let X := M D μ
  let Y := L D μ
  let := restrictedLieRingModule X (g := g)
  let := restrictedLieModule X (g := g)
  let := restrictedLieRingModule Y (g := g)
  let := restrictedLieModule Y (g := g)
  let f := quotientMap D μ
  let F : X →ₗ⁅ℂ,D.cartan⁆ Y :=
    { f.restrictScalars ℂ with
      map_lie' := fun {h x} => by
        change f ((ι ℂ (h : g)) • x) = (ι ℂ (h : g)) • f x
        exact f.map_smul _ _ }
  have hX := verma_mem_O D μ
  have hF := WeightExactness.weightMap_surjective F hX.1.2.1 (quotientMap_surjective D μ) ν
  obtain ⟨y, hywt, hy0⟩ := (Submodule.ne_bot_iff _).mp hy
  obtain ⟨x, hx⟩ := hF ⟨y, hywt⟩
  have hx0 : (x : X) ≠ 0 := by
    intro h
    have he : f (x : X) = y := congrArg Subtype.val hx
    exact hy0 (by rw [← he, h, map_zero])
  exact (hX.2.2.2.2.1 ν).mp ((Submodule.ne_bot_iff _).mpr ⟨x, x.property, hx0⟩)

private theorem weight_le_some_simple_label (k : Index D) (X : O.{u, v} D)
    (hX : inComponent D X.obj k) (ν : D.Weight)
    (hν : weightSpace D.cartan X.obj ν ≠ ⊥) :
    ∃ μ ∈ simpleLabels D k, weightLE D ν μ := by
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hν
  -- A simple quotient of the cyclic submodule retains the given weight vector.
  let S := Submodule.span (U g) {x}
  let Y : O.{u, v} D := ⟨ModuleCat.of (U g) S,
    submodule_mem_O D X.obj X.property S (Submodule.fg_span_singleton x)⟩
  let y : Y.obj := ⟨x, Submodule.mem_span_singleton_self x⟩
  have hy0 : y ≠ 0 := fun h => hx0 (congrArg (fun z : S => (z : X.obj)) h)
  have hy : y ∈ weightSpace D.cartan Y.obj ν := by
    refine (mem_weightSpace D.cartan Y.obj ν y).mpr fun h => Subtype.ext ?_
    exact (mem_weightSpace D.cartan X.obj ν x).mp hx h
  have hgen : Submodule.span (U g) {y} = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (show (z : X.obj) ∈ S from z.property)
    exact Submodule.mem_span_singleton.mpr ⟨a, Subtype.ext ha⟩
  let : Module.Finite (U g) Y.obj := Y.property.1
  have hbot : (⊥ : Submodule (U g) Y.obj) ≠ ⊤ := by
    intro he
    apply hy0
    apply (Submodule.mem_bot (U g)).mp
    rw [he]
    exact Submodule.mem_top
  obtain ⟨I, hI, _⟩ := (eq_top_or_exists_le_coatom (⊥ : Submodule (U g) Y.obj)).resolve_left hbot
  let Z : ModuleCat.{v} (U g) := ModuleCat.of (U g) (Y.obj ⧸ I)
  let f : Y.obj →ₗ[U g] Z := I.mkQ
  have hf : Function.Surjective f := Submodule.mkQ_surjective I
  have hfy : f y ≠ 0 := by
    intro he
    have hyI := (Submodule.Quotient.mk_eq_zero I).mp he
    apply hI.ne_top
    apply top_unique
    rw [← hgen]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hyI)
  let ZO : O.{u, v} D := ⟨Z, surjective_mem_O D Y.property f hf⟩
  have hZ : inComponent D ZO.obj k := inComponent_of_surjective D k f hf
    (inComponent_of_injective D k S.subtype S.subtype_injective hX)
  have hZsimple : Simple ZO := (simple_iff_isSimpleModule D ZO).mpr
    (isSimpleModule_iff_isCoatom.mpr hI)
  obtain ⟨μ, ⟨hμ, ⟨e⟩⟩, _⟩ := (simpleClassification D k ZO).mp ⟨hZsimple, hZ⟩
  have hewt := map_weight D e.toLinearMap ν (map_weight D f ν hy)
  have he0 : e (f y) ≠ 0 := fun he => hfy (e.injective (he.trans e.map_zero.symm))
  exact ⟨μ, hμ, weightLE_of_simpleQuotient_weight D μ ν
    ((Submodule.ne_bot_iff _).mpr ⟨e (f y), hewt, he0⟩)⟩

theorem exists_common_upper_bound : CommonUpperBoundType.{u, v} := by
  intro g _ _ _ D k
  obtain ⟨Λ, hΛ, hlabels⟩ := exists_label_bound D k
  refine ⟨Λ, hΛ, hlabels, fun X hX ν hν => ?_⟩
  obtain ⟨μ, hμ, hνμ⟩ := weight_le_some_simple_label D k X hX ν hν
  change Λ - ν ∈ QPlus D
  rw [← sub_add_sub_cancel Λ μ ν]
  exact (QPlus D).add_mem (hlabels μ hμ) hνμ

end RepTheorySurvey.CategoryO.ComponentBounds
