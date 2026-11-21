import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.VermaModules
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.PBWSpecialization
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.RealRootSpace
import Batteries.Tactic.OpenPrivate
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.Order.Sum.Order

noncomputable section

open scoped TensorProduct

namespace LieAlgebrasAndRepresentations.VermaModules

open Specs.LieAlgebrasAndRepresentations.VermaModules
open Specs.LieAlgebrasAndRepresentations.SerreRelations (simple)
open UniversalEnvelopingAlgebra
open Function

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

abbrev negative := @negative_value
abbrev positive := @positive_value
abbrev borel := @borel_value
abbrev triangular := @triangular_value
abbrev induced := @induced_value
abbrev highestVector := @highestVector_value
abbrev definingIdeal := @definingIdeal_value
abbrev weightModule := @weightModule_value

@[simp] private theorem envelopingMap_ι {A G : Type u} [LieRing A] [LieAlgebra ℂ A]
    [LieRing G] [LieAlgebra ℂ G] (f : A →ₗ⁅ℂ⁆ G) (a : A) :
    envelopingMap f (ι ℂ a) = ι ℂ (f a) := lift_ι_apply _ _ _

@[simp] private theorem multiply_tmul {A B G : Type u} [LieRing A] [LieAlgebra ℂ A]
    [LieRing B] [LieAlgebra ℂ B] [LieRing G] [LieAlgebra ℂ G]
    (f : A →ₗ⁅ℂ⁆ G) (g : B →ₗ⁅ℂ⁆ G) (a : U A) (b : U B) :
    multiply f g (a ⊗ₜ b) = envelopingMap f a * envelopingMap g b := by
  simp [multiply]

private theorem envelopingMap_comp {A B G : Type u} [LieRing A] [LieAlgebra ℂ A]
    [LieRing B] [LieAlgebra ℂ B] [LieRing G] [LieAlgebra ℂ G]
    (f : A →ₗ⁅ℂ⁆ B) (g : B →ₗ⁅ℂ⁆ G) :
    (envelopingMap g).comp (envelopingMap f) = envelopingMap (g.comp f) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  ext x
  change envelopingMap g (envelopingMap f (ι ℂ x)) = envelopingMap (g.comp f) (ι ℂ x)
  simp only [envelopingMap_ι, LieHom.coe_comp, Function.comp_apply]

theorem direction_from_real : direction_from_real_type.{u} := by
  intro L _ _ _ H ℓ hℓ
  let ρ : Module.Dual ℂ H →ₗ[ℝ] Specs.LieAlgebrasAndRepresentations.RealRootSpace.E H :=
    { toFun := Specs.LieAlgebrasAndRepresentations.RealRootSpace.rootRestriction H
      map_add' := by
        intro a b
        ext x
        simp [Specs.LieAlgebrasAndRepresentations.RealRootSpace.rootRestriction]
      map_smul' := by
        intro c a
        ext x
        simp [Specs.LieAlgebrasAndRepresentations.RealRootSpace.rootRestriction] }
  exact ⟨ℓ.comp ρ, fun a ha => hℓ _ ⟨a, ha, rfl⟩, fun _ => rfl⟩

theorem weight_action : weight_action_type.{u} := by
  intro L _ _ H φ μ χ hχ
  refine ⟨fun h c => ?_, fun x c => ?_⟩
  · change χ _ * c = μ h * c
    rw [hχ.1 h]
  · change χ _ * c = 0
    rw [hχ.2 x, zero_mul]

theorem tensor_balanced : tensor_balanced_type.{u} := by
  intro L _ _ H φ χ a b c
  change (balance H φ χ).mkQ _ = (balance H φ χ).mkQ _
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨a,b,c,rfl⟩)

section PBW

open Shared.Lie.PBW

private def leftLetter {α β : Type u} (a : α) : α ⊕ₗ β := toLex (Sum.inl a)
private def rightLetter {α β : Type u} (b : β) : α ⊕ₗ β := toLex (Sum.inr b)

private def joinWords {α β : Type u} [LinearOrder α] [LinearOrder β]
    (p : OrderedWord α × OrderedWord β) : OrderedWord (α ⊕ₗ β) :=
  ⟨p.1.val.map leftLetter ++ p.2.val.map rightLetter, by
    refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · exact List.pairwise_map.mpr (p.1.property.imp Sum.Lex.inl_le_inl_iff.mpr)
    · exact List.pairwise_map.mpr (p.2.property.imp Sum.Lex.inr_le_inr_iff.mpr)
    · simp only [List.mem_map, forall_exists_index, and_imp]
      rintro _ _ _ rfl _ _ _ rfl
      exact Sum.Lex.inl_le_inr _ _⟩

private theorem joinWords_bijective {α β : Type u} [LinearOrder α] [LinearOrder β] :
    Bijective (joinWords (α := α) (β := β)) := by
  constructor
  · intro p q hpq
    have h := congrArg Subtype.val hpq
    apply Prod.ext
    · apply Subtype.ext
      have he := congrArg (List.filterMap (fun x : α ⊕ₗ β => (ofLex x).getLeft?)) h
      simpa [joinWords, leftLetter, rightLetter, List.filterMap_map, Function.comp_def] using he
    · apply Subtype.ext
      have he := congrArg (List.filterMap (fun x : α ⊕ₗ β => (ofLex x).getRight?)) h
      simpa [joinWords, leftLetter, rightLetter, List.filterMap_map, Function.comp_def] using he
  · rintro ⟨xs, hs⟩
    have split : ∀ l : List (α ⊕ₗ β), l.Pairwise (· ≤ ·) →
        ∃ p : OrderedWord α × OrderedWord β, (joinWords p).val = l := by
      intro l hl
      induction l with
      | nil => exact ⟨(emptyWord α, emptyWord β), rfl⟩
      | cons x ys ih =>
        obtain ⟨hx, hy⟩ := List.pairwise_cons.mp hl
        obtain ⟨⟨⟨as, ha⟩, ⟨bs, hb⟩⟩, hab⟩ := ih hy
        change as.map leftLetter ++ bs.map rightLetter = ys at hab
        rw [← hab] at hx
        cases h : ofLex x with
        | inl a =>
          have he : x = leftLetter (β := β) a := h
          refine ⟨(⟨a :: as, List.pairwise_cons.mpr ⟨?_, ha⟩⟩, ⟨bs, hb⟩), ?_⟩
          · intro c hc
            exact Sum.Lex.inl_le_inl_iff.mp (he ▸ hx _ (List.mem_append_left _
              (List.mem_map_of_mem hc)))
          · change leftLetter a :: (as.map leftLetter ++ bs.map rightLetter) = x :: ys
            rw [he, hab]
        | inr b =>
          have he : x = rightLetter (α := α) b := h
          have ha0 : as = [] := by
            cases as with
            | nil => rfl
            | cons a as =>
              exact (Sum.Lex.not_inr_le_inl (he ▸ hx _ (List.mem_append_left _
                (List.mem_map_of_mem List.mem_cons_self)))).elim
          subst as
          refine ⟨(emptyWord α, ⟨b :: bs, List.pairwise_cons.mpr ⟨?_, hb⟩⟩), ?_⟩
          · intro c hc
            exact Sum.Lex.inr_le_inr_iff.mp (he ▸ hx _ (List.mem_append_right _
              (List.mem_map_of_mem hc)))
          · change rightLetter b :: bs.map rightLetter = x :: ys
            rw [he, ← hab]
            rfl
    obtain ⟨p, hp⟩ := split xs hs
    exact ⟨p, Subtype.ext hp⟩

private theorem multiply_bijective {A B G : Type u}
    [LieRing A] [LieAlgebra ℂ A] [LieRing B] [LieAlgebra ℂ B] [LieRing G] [LieAlgebra ℂ G]
    (f : A →ₗ⁅ℂ⁆ G) (g : B →ₗ⁅ℂ⁆ G) (s : (A × B) ≃ₗ[ℂ] G)
    (hs : ∀ a b, s (a,b) = f a + g b) : Bijective (multiply f g) := by
  classical
  let a := Module.Free.chooseBasis ℂ A
  let b := Module.Free.chooseBasis ℂ B
  let α := Module.Free.ChooseBasisIndex ℂ A
  let β := Module.Free.ChooseBasisIndex ℂ B
  let : LinearOrder α := WellOrderingRel.isWellOrder.linearOrder
  let : LinearOrder β := WellOrderingRel.isWellOrder.linearOrder
  let c : Module.Basis (α ⊕ₗ β) ℂ G :=
    ((a.prod b).map s).reindex (toLex : (α ⊕ β) ≃ (α ⊕ₗ β))
  have hc₁ (i : α) : c (leftLetter i) = f (a i) := by simp [c, leftLetter, hs, Module.Basis.prod_apply]
  have hc₂ (j : β) : c (rightLetter j) = g (b j) := by simp [c, rightLetter, hs, Module.Basis.prod_apply]
  let e := Equiv.ofBijective joinWords (joinWords_bijective (α := α) (β := β))
  let source := (orderedBasis a).tensorProduct (orderedBasis b)
  let target := (orderedBasis c).reindex e.symm
  let F := source.equiv target (Equiv.refl _)
  have heq : F.toLinearMap = multiply f g := by
    apply source.ext
    rintro ⟨p,q⟩
    change F (source (p,q)) = multiply f g (source (p,q))
    rw [show F (source (p,q)) = target (p,q) from source.equiv_apply (p,q) target (Equiv.refl _)]
    simp only [target, source, Module.Basis.reindex_apply, Equiv.symm_symm,
      Module.Basis.tensorProduct_apply', orderedBasis_apply, multiply_tmul]
    change monomial c ((p.val.map leftLetter) ++ (q.val.map rightLetter)) =
      envelopingMap f (monomial a p.val) * envelopingMap g (monomial b q.val)
    rw [monomial_append]
    congr 1
    · simp only [monomial, Shared.Lie.word, List.map_map, Function.comp_def, hc₁, map_list_prod,
        envelopingMap_ι]
    · simp only [monomial, Shared.Lie.word, List.map_map, Function.comp_def, hc₂, map_list_prod,
        envelopingMap_ι]
  rw [← heq]
  exact F.bijective

end PBW

section Roots

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)

private abbrev rootSum (s : Set ℝ) : Submodule ℂ L :=
  ⨆ α : {α : Module.Dual ℂ H // φ α ∈ s}, rootSpace H α.val

private theorem le_rootSum {s : Set ℝ} {α : Module.Dual ℂ H} (hα : φ α ∈ s) :
    rootSpace H α ≤ rootSum H φ s :=
  le_iSup (fun a : {a : Module.Dual ℂ H // φ a ∈ s} => rootSpace H a.val) ⟨α,hα⟩

private theorem rootSum_lie {s t r : Set ℝ}
    (hadd : ∀ x ∈ s, ∀ y ∈ t, x + y ∈ r) {x y : L}
    (hx : x ∈ rootSum H φ s) (hy : y ∈ rootSum H φ t) :
    ⁅x,y⁆ ∈ rootSum H φ r := by
  refine Submodule.iSup_induction _ (motive := fun x => ⁅x,y⁆ ∈ rootSum H φ r) hx
    ?_ (by simp) (fun a b ha hb => by simpa only [add_lie] using Submodule.add_mem _ ha hb)
  intro a z hz
  refine Submodule.iSup_induction _ (motive := fun y => ⁅z,y⁆ ∈ rootSum H φ r) hy
    ?_ (by simp) (fun b c hb hc => by simpa only [lie_add] using Submodule.add_mem _ hb hc)
  intro b w hw
  have hm : φ (a.val + b.val) ∈ r := by rw [map_add]; exact hadd _ a.property _ b.property
  exact Submodule.mem_iSup_of_mem ⟨a.val + b.val, hm⟩ (rootSpace_bracket H _ _ _ _ hz hw)

private theorem rootPart_submodule {s : Set ℝ}
    (hadd : ∀ x ∈ s, ∀ y ∈ s, x + y ∈ s) :
    (rootPart H φ s).toSubmodule = rootSum H φ s := by
  apply le_antisymm
  · let K : LieSubalgebra ℂ L :=
      { rootSum H φ s with lie_mem' := fun hx hy => rootSum_lie H φ hadd hx hy }
    change rootPart H φ s ≤ K
    exact LieSubalgebra.lieSpan_le.mpr fun _ ⟨a, ha, hx⟩ =>
      Submodule.mem_iSup_of_mem ⟨a, ha⟩ hx
  · exact iSup_le fun a _ hx => LieSubalgebra.subset_lieSpan ⟨a.val, a.property, hx⟩

private theorem negative_submodule :
    (negative H φ).toSubmodule = rootSum H φ (Set.Iio 0) :=
  rootPart_submodule H φ (s := Set.Iio 0) (fun _ hx _ hy =>
    Set.mem_Iio.mpr (add_neg (Set.mem_Iio.mp hx) (Set.mem_Iio.mp hy)))

private theorem positive_submodule :
    (positive H φ).toSubmodule = rootSum H φ (Set.Ioi 0) :=
  rootPart_submodule H φ (s := Set.Ioi 0) (fun _ hx _ hy =>
    Set.mem_Ioi.mpr (add_pos (Set.mem_Ioi.mp hx) (Set.mem_Ioi.mp hy)))

private theorem borel_submodule [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) (hφ : Regular H φ) :
    (borel H φ).toSubmodule = H.toSubmodule ⊔ (positive H φ).toSubmodule ∧
    (borel H φ).toSubmodule = rootSum H φ (Set.Ici 0) := by
  have hs : rootSum H φ (Set.Ici 0) = H.toSubmodule ⊔ (positive H φ).toSubmodule := by
    rw [positive_submodule H φ, ← rootSpace_zero hss H hH]
    apply le_antisymm
    · refine iSup_le fun a => ?_
      by_cases h : a.val = 0
      · rw [h]; exact le_sup_left
      · by_cases ha : a.val ∈ rootSet H
        · have hp : φ a.val ∈ Set.Ioi (0 : ℝ) :=
            lt_of_le_of_ne a.property (Ne.symm (hφ _ ha))
          exact (le_rootSum H φ hp).trans le_sup_right
        · rw [rootSpace_eq_bot_of_not_mem H _ h ha]; exact bot_le
    · apply sup_le
      · exact le_rootSum H φ (s := Set.Ici 0) (α := 0) (by simp)
      · exact iSup_le fun a => le_rootSum H φ (s := Set.Ici 0)
          (show 0 ≤ φ a.val from le_of_lt a.property)
  have he : (borel H φ).toSubmodule = rootSum H φ (Set.Ici 0) := by
    rw [← rootPart_submodule H φ (s := Set.Ici 0) (fun _ hx _ hy =>
      Set.mem_Ici.mpr (add_nonneg (Set.mem_Ici.mp hx) (Set.mem_Ici.mp hy)))]
    apply le_antisymm
    · change H ⊔ positive H φ ≤ rootPart H φ _
      rw [sup_le_iff]
      change H.toSubmodule ≤ (rootPart H φ _).toSubmodule ∧
        (positive H φ).toSubmodule ≤ (rootPart H φ _).toSubmodule
      rw [rootPart_submodule H φ (s := Set.Ici 0) (fun _ hx _ hy =>
      Set.mem_Ici.mpr (add_nonneg (Set.mem_Ici.mp hx) (Set.mem_Ici.mp hy))), hs]
      exact ⟨le_sup_left, le_sup_right⟩
    · rw [rootPart_submodule H φ (s := Set.Ici 0) (fun _ hx _ hy =>
      Set.mem_Ici.mpr (add_nonneg (Set.mem_Ici.mp hx) (Set.mem_Ici.mp hy))), hs]
      exact sup_le (show H ≤ borel H φ from le_sup_left)
        (show positive H φ ≤ borel H φ from le_sup_right)
  exact ⟨he.trans hs, he⟩

private theorem negative_borel_isCompl [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) (hφ : Regular H φ) :
    IsCompl (negative H φ).toSubmodule (borel H φ).toSubmodule := by
  rw [negative_submodule H φ, (borel_submodule H φ hss hH hφ).2]
  constructor
  · simp only [rootSum, iSup_subtype]
    exact (rootSpace_independent H hH.1).disjoint_biSup_biSup
      (Set.disjoint_left.mpr fun a ha hb => (not_lt_of_ge (show 0 ≤ φ a from hb)) (show φ a < 0 from ha))
  · rw [codisjoint_iff, ← iSup_rootSpace_eq_top H hH.1]
    apply le_antisymm (le_trans le_top (iSup_rootSpace_eq_top H hH.1).ge)
    refine iSup_le fun a => ?_
    rcases lt_or_ge (φ a) 0 with ha | ha
    · exact (le_rootSum H φ (s := Set.Iio 0) ha).trans le_sup_left
    · exact (le_rootSum H φ (s := Set.Ici 0) ha).trans le_sup_right

private theorem cartan_positive_disjoint [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) :
    Disjoint H.toSubmodule (positive H φ).toSubmodule := by
  rw [← rootSpace_zero hss H hH, positive_submodule H φ]
  simp only [rootSum, iSup_subtype]
  apply (rootSpace_independent H hH.1).disjoint_biSup
  exact fun h => (lt_irrefl (0 : ℝ)) ((map_zero φ) ▸ h)

private abbrev cartanIn : H →ₗ⁅ℂ⁆ borel H φ := LieSubalgebra.inclusion le_sup_left
private abbrev positiveIn : positive H φ →ₗ⁅ℂ⁆ borel H φ := LieSubalgebra.inclusion le_sup_right

private def borelEquiv [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) (hφ : Regular H φ) :
    (H × positive H φ) ≃ₗ[ℂ] borel H φ := by
  let F := (cartanIn H φ).toLinearMap.coprod (positiveIn H φ).toLinearMap
  refine LinearEquiv.ofBijective F ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a,b⟩ hab
    have hs : (a : L) + (b : L) = 0 := congrArg Subtype.val hab
    have he : (a : L) = -(b : L) := eq_neg_of_add_eq_zero_left hs
    have ha : (a : L) = 0 := Submodule.disjoint_def.mp (cartan_positive_disjoint H φ hss hH)
      a a.property (he ▸ (positive H φ).neg_mem b.property)
    exact Prod.ext (Subtype.ext ha) (Subtype.ext (by simpa [ha] using hs))
  · intro x
    have hx := x.property
    change x.val ∈ (borel H φ).toSubmodule at hx
    rw [(borel_submodule H φ hss hH hφ).1, Submodule.mem_sup] at hx
    obtain ⟨a,ha,b,hb,hs⟩ := hx
    exact ⟨(⟨a,ha⟩, ⟨b,hb⟩), Subtype.ext hs⟩

private theorem outer_multiply_bijective [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) (hφ : Regular H φ) :
    Bijective (multiply (negative H φ).incl (borel H φ).incl) :=
  multiply_bijective _ _
    (Submodule.prodEquivOfIsCompl _ _ (negative_borel_isCompl H φ hss hH hφ))
    (fun _ _ => rfl)

theorem triangular_apply : triangular_apply_type.{u} := by
  intro L _ _ H φ a h b
  change (multiply (negative H φ).incl (borel H φ).incl)
    ((TensorProduct.map LinearMap.id (multiply (cartanIn H φ) (positiveIn H φ)))
      (a ⊗ₜ[ℂ] (h ⊗ₜ[ℂ] b))) = _
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, multiply_tmul, map_mul]
  have hc : envelopingMap (borel H φ).incl (envelopingMap (cartanIn H φ) h) =
      envelopingMap H.incl h := DFunLike.congr_fun (envelopingMap_comp (cartanIn H φ) _) h
  have hp : envelopingMap (borel H φ).incl (envelopingMap (positiveIn H φ) b) =
      envelopingMap (positive H φ).incl b :=
    DFunLike.congr_fun (envelopingMap_comp (positiveIn H φ) _) b
  rw [hc, hp, mul_assoc]

theorem triangular_bijective : triangular_bijective_type.{u} := by
  intro L _ _ _ hss H _ φ hφ
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  let inner := multiply (cartanIn H φ) (positiveIn H φ)
  have hi : Bijective inner := multiply_bijective _ _ (borelEquiv H φ hss hH hφ) (fun _ _ => rfl)
  let e := LinearEquiv.ofBijective inner hi
  have ht : Bijective (TensorProduct.map (LinearMap.id (R := ℂ) (M := U (negative H φ)))
      inner) := (TensorProduct.congr (LinearEquiv.refl _ _) e).bijective
  exact (outer_multiply_bijective H φ hss hH hφ).comp ht

private theorem borel_bracket_mem_positive [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) (hφ : Regular H φ)
    (a b : borel H φ) : (⁅a,b⁆ : L) ∈ positive H φ := by
  let E := borelEquiv H φ hss hH hφ
  obtain ⟨⟨h,x⟩, rfl⟩ := E.surjective a
  obtain ⟨⟨k,y⟩, rfl⟩ := E.surjective b
  have hxy : ⁅(x : L), (y : L)⁆ ∈ positive H φ := (positive H φ).lie_mem x.property y.property
  have cross (h : H) (x : positive H φ) : ⁅(h : L), (x : L)⁆ ∈ positive H φ := by
    change ⁅(h : L), (x : L)⁆ ∈ (positive H φ).toSubmodule
    rw [positive_submodule H φ]
    apply rootSum_lie H φ (s := ({0} : Set ℝ)) (t := Set.Ioi 0)
    · intro p hp q hq
      change p = 0 at hp
      simpa [hp] using hq
    · apply Submodule.mem_iSup_of_mem (⟨0, by simp⟩ :
        {α : Module.Dual ℂ H // φ α ∈ ({0} : Set ℝ)})
      rw [rootSpace_zero hss H hH]
      exact h.property
    · rw [← positive_submodule H φ]; exact x.property
  have hab : ⁅(h : L), (k : L)⁆ = 0 := by
    let : IsLieAbelian H := hH.1.1
    exact congrArg Subtype.val (trivial_lie_zero H H h k)
  change ⁅(h : L) + (x : L), (k : L) + (y : L)⁆ ∈ positive H φ
  rw [add_lie, lie_add, lie_add, hab, zero_add, ← lie_skew (x : L) (k : L)]
  exact (positive H φ).add_mem (cross h y)
    ((positive H φ).add_mem ((positive H φ).neg_mem (cross k x)) hxy)

theorem character_existsUnique : character_existsUnique_type.{u} := by
  intro L _ _ _ hss H _ φ hφ μ
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  let E := borelEquiv H φ hss hH hφ
  let ℓ : borel H φ →ₗ[ℂ] ℂ :=
    μ.comp ((LinearMap.fst ℂ H (positive H φ)).comp E.symm.toLinearMap)
  have hleft (h : H) : E (h,0) = cartanIn H φ h := by
    change (cartanIn H φ).toLinearMap h + (positiveIn H φ).toLinearMap 0 = _
    simp
  have hright (x : positive H φ) : E (0,x) = positiveIn H φ x := by
    change (cartanIn H φ).toLinearMap 0 + (positiveIn H φ).toLinearMap x = _
    simp
  have ℓleft (h : H) : ℓ (cartanIn H φ h) = μ h := by rw [← hleft]; simp [ℓ]
  have ℓright (x : positive H φ) : ℓ (positiveIn H φ x) = 0 := by rw [← hright]; simp [ℓ]
  let f : borel H φ →ₗ⁅ℂ⁆ ℂ :=
    { ℓ with
      map_lie' := by
        intro a b
        have hmem := borel_bracket_mem_positive H φ hss hH hφ a b
        have heq : ⁅a,b⁆ = positiveIn H φ ⟨_, hmem⟩ := Subtype.ext rfl
        simp only [heq, LieRing.of_associative_ring_bracket, mul_comm, sub_self]
        exact ℓright _ }
  refine ⟨lift ℂ f, ⟨fun h => ?_, fun x => ?_⟩, ?_⟩
  · exact (lift_ι_apply ℂ f _).trans (ℓleft h)
  · exact (lift_ι_apply ℂ f _).trans (ℓright x)
  · intro χ hχ
    apply UniversalEnvelopingAlgebra.hom_ext
    ext z
    obtain ⟨⟨h,x⟩, rfl⟩ := E.surjective z
    change χ (ι ℂ (E (h,x))) = lift ℂ f (ι ℂ (E (h,x)))
    have he : E (h,x) = cartanIn H φ h + positiveIn H φ x := rfl
    rw [he, map_add, map_add, map_add, hχ.1 h, hχ.2 x, lift_ι_apply, lift_ι_apply]
    change μ h + 0 = ℓ (cartanIn H φ h) + ℓ (positiveIn H φ x)
    rw [ℓleft, ℓright]

end Roots

section Induction

open private rootSpace_le_of_nonzero from MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.SerreRelations

variable {L : Type u} [LieRing L] [LieAlgebra ℂ L]
variable (H : LieSubalgebra ℂ L) (φ : Direction H)
variable (χ : U (borel H φ) →ₐ[ℂ] ℂ)

private abbrev iB := envelopingMap (borel H φ).incl
private abbrev iN := envelopingMap (negative H φ).incl

private def difference (b : U (borel H φ)) : U L :=
  iB H φ b - algebraMap ℂ (U L) (χ b)

private def characterIdeal : Submodule (U L) (U L) :=
  Submodule.span (U L) (Set.range (difference H φ χ))

private theorem balance_map_rid :
    (balance H φ χ).map (TensorProduct.AlgebraTensorModule.rid ℂ (U L) (U L)).toLinearMap =
      characterIdeal H φ χ := by
  unfold balance characterIdeal
  rw [Submodule.map_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨_, ⟨a,b,c,rfl⟩, rfl⟩
    have hb : difference H φ χ b ∈ characterIdeal H φ χ := Submodule.subset_span ⟨b,rfl⟩
    have hm := (characterIdeal H φ χ).smul_mem ((algebraMap ℂ (U L) c) * a) hb
    change ((algebraMap ℂ (U L) c) * a) * difference H φ χ b ∈ characterIdeal H φ χ at hm
    simp only [LinearEquiv.coe_coe, map_sub, TensorProduct.AlgebraTensorModule.rid_tmul]
    change c • (a * iB H φ b) - (χ b * c) • a ∈ characterIdeal H φ χ
    convert hm using 1
    rw [difference, mul_assoc, mul_sub, (Algebra.commutes (R := ℂ) (χ b) a).symm,
      ← Algebra.smul_def, ← Algebra.smul_def, smul_sub, smul_smul,
      mul_comm c (χ b)]
  · apply Submodule.span_le.mpr
    rintro _ ⟨b,rfl⟩
    apply Submodule.subset_span
    refine ⟨_, ⟨1,b,1,rfl⟩, ?_⟩
    simp only [LinearEquiv.coe_coe, map_sub, TensorProduct.AlgebraTensorModule.rid_tmul]
    change (1 : ℂ) • (1 * iB H φ b) - (χ b * 1) • (1 : U L) = difference H φ χ b
    simp [difference, Algebra.smul_def]

private theorem induced_characterQuotient :
    ∃ E : (U L ⧸ characterIdeal H φ χ) ≃ₗ[U L] induced H φ χ,
      ∀ a : U L, E ((characterIdeal H φ χ).mkQ a) = tensorClass H φ χ a 1 := by
  let R := TensorProduct.AlgebraTensorModule.rid ℂ (U L) (U L)
  let E := Submodule.Quotient.equiv (balance H φ χ) (characterIdeal H φ χ)
    R (balance_map_rid H φ χ)
  refine ⟨E.symm, fun a => E.symm_apply_eq.mpr ?_⟩
  simp [E, R, Submodule.mkQ_apply]

private theorem eval_right_mul [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) (hφ : Regular H φ) :
    ∃ p : U L →ₗ[ℂ] U (negative H φ),
      (∀ a, p (iN H φ a) = a) ∧
      ∀ a b, p (a * iB H φ b) = χ b • p a := by
  let E := LinearEquiv.ofBijective _ (outer_multiply_bijective H φ hss hH hφ)
  let q := (TensorProduct.rid ℂ (U (negative H φ))).toLinearMap.comp
    (TensorProduct.map LinearMap.id χ.toLinearMap)
  let p := q.comp E.symm.toLinearMap
  have hE (a : U (negative H φ)) (b : U (borel H φ)) :
      E (a ⊗ₜ b) = iN H φ a * iB H φ b := multiply_tmul _ _ _ _
  have hq (a : U (negative H φ)) (b : U (borel H φ)) :
      p (iN H φ a * iB H φ b) = χ b • a := by
    rw [← hE]
    simp [p, q]
  refine ⟨p, fun a => ?_, fun a b => ?_⟩
  · simpa using hq a 1
  · obtain ⟨z,rfl⟩ := E.surjective a
    induction z using TensorProduct.inductionOn with
    | tmul a c =>
      rw [hE, mul_assoc, ← map_mul, hq, hq, map_mul, smul_smul, mul_comm (χ b)]
    | add z w hz hw => simp only [map_add, add_mul, smul_add, hz, hw]

theorem induced_free : induced_free_type.{u} := by
  intro L _ _ _ hss H _ φ hφ χ
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  obtain ⟨p, hp, hpR⟩ := eval_right_mul H φ χ hss hH hφ
  obtain ⟨E, hE⟩ := induced_characterQuotient H φ χ
  let J := characterIdeal H φ χ
  have hkill {x : U L} (hx : x ∈ J) : ∀ a : U L, p (a*x) = 0 := by
    refine Submodule.span_induction (p := fun x _ => ∀ a : U L, p (a*x) = 0) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨b,rfl⟩ a
      rw [difference, mul_sub, map_sub, hpR, ← Algebra.commutes, ← Algebra.smul_def, map_smul,
        sub_self]
    · simp
    · intro x y _ _ hx hy a
      simp [mul_add, hx, hy]
    · intro c x _ hx a
      exact mul_assoc a c x ▸ hx (a*c)
  let pp := (J.restrictScalars ℂ).liftQ p fun x hx => by
    simpa using hkill hx 1
  let q : U L →ₗ[ℂ] U L ⧸ J := J.mkQ.restrictScalars ℂ
  let I := q.comp (iN H φ).toLinearMap
  have hpp (x : U L) : pp (q x) = p x := rfl
  have hI : Injective I := by
    intro a b hab
    have hh := congrArg pp hab
    simpa only [I, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hpp, hp] using hh
  have hR (a : U L) (b : U (borel H φ)) :
      q (a * iB H φ b) = χ b • q a := by
    rw [← map_smul]
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply (Submodule.Quotient.mk_eq_zero J).mpr
    rw [Algebra.smul_def, Algebra.commutes, ← mul_sub]
    exact J.smul_mem a (Submodule.subset_span ⟨b,rfl⟩)
  have hS : Surjective I := by
    intro x
    obtain ⟨a,rfl⟩ := J.mkQ_surjective x
    let F := LinearEquiv.ofBijective _ (outer_multiply_bijective H φ hss hH hφ)
    obtain ⟨z,rfl⟩ := F.surjective a
    change ∃ b, I b = q (F z)
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change ∃ c, I c = q (multiply (negative H φ).incl (borel H φ).incl (a ⊗ₜ b))
      refine ⟨χ b • a, ?_⟩
      rw [multiply_tmul, hR, map_smul]
      rfl
    | add z w hz hw =>
      obtain ⟨a,ha⟩ := hz
      obtain ⟨b,hb⟩ := hw
      exact ⟨a+b, by simp [ha,hb]⟩
  let X := (LinearEquiv.ofBijective I ⟨hI,hS⟩).trans (E.restrictScalars ℂ)
  have hX (a : U (negative H φ)) : X a = tensorClass H φ χ (iN H φ a) 1 :=
    hE (iN H φ a)
  have hv (a : U (negative H φ)) :
      tensorClass H φ χ (iN H φ a) 1 = iN H φ a • highestVector H φ χ := by
    change (balance H φ χ).mkQ (_ ⊗ₜ[ℂ] (1 : ℂ)) =
      iN H φ a • (balance H φ χ).mkQ ((1 : U L) ⊗ₜ[ℂ] (1 : ℂ))
    rw [← map_smul]
    change _ = (balance H φ χ).mkQ (((iN H φ a) * 1) ⊗ₜ[ℂ] 1)
    rw [mul_one]
  refine ⟨X, fun a => (hX a).trans (hv a), ?_⟩
  have h1 : X 1 = highestVector H φ χ := by simpa [highestVector_value] using hX 1
  change highestVector H φ χ ≠ 0
  rw [← h1]
  intro hz
  have hh := congrArg (Shared.Lie.augmentation ℂ (negative H φ)) (X.map_eq_zero_iff.mp hz)
  exact one_ne_zero (by simpa only [map_one, map_zero] using hh)

private def differenceLinear : U (borel H φ) →ₗ[ℂ] U L :=
  (iB H φ).toLinearMap - (Algebra.linearMap ℂ (U L)).comp χ.toLinearMap

private theorem difference_mul_mem {J : Submodule (U L) (U L)} {a b : U (borel H φ)}
    (ha : difference H φ χ a ∈ J) (hb : difference H φ χ b ∈ J) :
    difference H φ χ (a*b) ∈ J := by
  have h := J.add_mem (J.smul_mem (iB H φ a) hb)
    (J.smul_mem (algebraMap ℂ (U L) (χ b)) ha)
  change iB H φ a * difference H φ χ b +
    algebraMap ℂ (U L) (χ b) * difference H φ χ a ∈ J at h
  convert h using 1
  simp only [difference, map_mul, mul_sub]
  rw [(Algebra.commutes (R := ℂ) (χ b) (iB H φ a)),
    (Algebra.commutes (R := ℂ) (χ b) (algebraMap ℂ (U L) (χ a)))]
  abel

private theorem all_differences_mem {J : Submodule (U L) (U L)}
    (hι : ∀ x : borel H φ, difference H φ χ (ι ℂ x) ∈ J)
    (a : U (borel H φ)) : difference H φ χ a ∈ J := by
  obtain ⟨z, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (borel H φ)) a
  change difference H φ χ (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ z) ∈ J
  induction z using TensorAlgebra.induction with
  | algebraMap r => simp [difference]
  | ι x => exact hι x
  | mul x y hx hy =>
    rw [map_mul]
    exact difference_mul_mem H φ χ hx hy
  | add x y hx hy =>
    change differenceLinear H φ χ _ ∈ J at hx hy ⊢
    rw [map_add, map_add]
    exact J.add_mem hx hy

private theorem positive_le_of_simple [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) (S : LieSubalgebra ℂ L)
    (hs : ∀ i : simple H φ, rootSpace H i.val ≤ S.toSubmodule) :
    positive H φ ≤ S := by
  change (positive H φ).toSubmodule ≤ S.toSubmodule
  rw [positive_submodule H φ]
  apply iSup_le
  intro a
  by_cases ha : a.val ∈ rootSet H
  · have cover : ∀ β ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive H φ,
          rootSpace H β ≤ S.toSubmodule := by
      intro β hβ
      by_contra hmiss
      let D : Set (Module.Dual ℂ H) :=
        {γ | γ ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive H φ ∧
          ¬ rootSpace H γ ≤ S.toSubmodule}
      have hfin : D.Finite := (rootSet_finite H hH.1).subset (fun _ hd => hd.1.1)
      obtain ⟨γ,hγ⟩ := hfin.exists_minimalFor φ D ⟨β,hβ,hmiss⟩
      have hns : γ ∉ simple H φ := fun h => hγ.prop.2 (hs ⟨γ,h⟩)
      obtain ⟨δ,hδ,ε,hε,heq⟩ :
          ∃ δ ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive H φ,
            ∃ ε ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive H φ,
              γ = δ + ε := by
        by_contra hn
        apply hns
        exact ⟨hγ.prop.1, by simpa using hn⟩
      have he : φ γ = φ δ + φ ε := by rw [heq, map_add]
      have hsmall {α : Module.Dual ℂ H}
          (hα : α ∈ Specs.LieAlgebrasAndRepresentations.SerreRelations.positive H φ)
          (h : φ α < φ γ) : rootSpace H α ≤ S.toSubmodule := by
        by_contra hn
        exact (not_le.mpr h) (hγ.le_of_le (show α ∈ D from ⟨hα,hn⟩) h.le)
      have hd := hsmall hδ (by linarith [hε.2])
      have hf := hsmall hε (by linarith [hδ.2])
      obtain ⟨x,hx,hxn⟩ := (rootSpace H δ).ne_bot_iff.mp hδ.1.2
      obtain ⟨y,hy,hyn⟩ := (rootSpace H ε).ne_bot_iff.mp hε.1.2
      have hn := RootStrings.root_bracket_ne_zero hss H hH δ ε hδ.1 hε.1
        (heq ▸ hγ.prop.1.1) x y hx hy hxn hyn
      have hb : ⁅x,y⁆ ∈ rootSpace H γ := heq ▸ rootSpace_bracket H δ ε x y hx hy
      exact hγ.prop.2 (rootSpace_le_of_nonzero H hss hH
        hγ.prop.1.1 S hb hn (S.lie_mem (hd hx) (hf hy)))
    exact cover a.val ⟨ha,a.property⟩
  · have hn : a.val ≠ 0 := by
      intro h
      have hp : 0 < φ a.val := a.property
      rw [h, map_zero] at hp
      exact (lt_irrefl 0) hp
    rw [rootSpace_eq_bot_of_not_mem H _ hn ha]
    exact bot_le

private theorem ideal_eq_characterIdeal [FiniteDimensional ℂ L]
    (hss : IsSemisimple ℂ L) (hH : IsMaximalToral H) (hφ : Regular H φ)
    (μ : Module.Dual ℂ H) (hχ : IsWeightCharacter H φ μ χ)
    (e : simple H φ → L) (he : ∀ i, e i ∈ rootSpace H i.val ∧ e i ≠ 0) :
    definingIdeal H φ μ e = characterIdeal H φ χ := by
  have hep (i : simple H φ) : e i ∈ positive H φ :=
    LieSubalgebra.subset_lieSpan ⟨i.val, i.property.1.2, (he i).1⟩
  have cartanDiff (h : H) :
      difference H φ χ (ι ℂ (cartanIn H φ h)) = ι ℂ (h : L) - algebraMap ℂ (U L) (μ h) := by
    unfold difference
    rw [envelopingMap_ι, hχ.1 h]
    rfl
  have simpleDiff (i : simple H φ) :
      difference H φ χ (ι ℂ (positiveIn H φ ⟨e i, hep i⟩)) = ι ℂ (e i) := by
    unfold difference
    rw [envelopingMap_ι, hχ.2 ⟨e i, hep i⟩, map_zero, sub_zero]
    rfl
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ (⟨h,rfl⟩ | ⟨i,rfl⟩)
    · dsimp only
      rw [← cartanDiff h]
      exact Submodule.subset_span (Set.mem_range_self _)
    · dsimp only
      rw [← simpleDiff i]
      exact Submodule.subset_span (Set.mem_range_self _)
  · let J := definingIdeal H φ μ e
    let ℓ := (differenceLinear H φ χ).comp (ι ℂ (L := borel H φ)).toLinearMap
    let S : LieSubalgebra ℂ (borel H φ) :=
      { (J.restrictScalars ℂ).comap ℓ with
        lie_mem' := by
          intro x y hx hy
          change difference H φ χ (ι ℂ x) ∈ J at hx
          change difference H φ χ (ι ℂ y) ∈ J at hy
          change differenceLinear H φ χ (ι ℂ ⁅x,y⁆) ∈ J
          rw [LieHom.map_lie, LieRing.of_associative_ring_bracket, map_sub]
          exact J.sub_mem (difference_mul_mem H φ χ hx hy) (difference_mul_mem H φ χ hy hx) }
    have hsC (h : H) : cartanIn H φ h ∈ S := by
      change difference H φ χ (ι ℂ (cartanIn H φ h)) ∈ J
      rw [cartanDiff h]
      exact Submodule.subset_span (Or.inl (Set.mem_range_self h))
    have hsE (i : simple H φ) : positiveIn H φ ⟨e i, hep i⟩ ∈ S := by
      change difference H φ χ (ι ℂ (positiveIn H φ ⟨e i, hep i⟩)) ∈ J
      rw [simpleDiff i]
      exact Submodule.subset_span (Or.inr (Set.mem_range_self i))
    let inc := (borel H φ).incl
    have hsP : positive H φ ≤ S.map inc := by
      apply positive_le_of_simple H φ hss hH
      intro i
      exact rootSpace_le_of_nonzero H hss hH i.property.1.1 _ (he i).1 (he i).2
        ⟨_, hsE i, rfl⟩
    have hx (x : positive H φ) : positiveIn H φ x ∈ S := by
      obtain ⟨y,hy,heq⟩ := hsP x.property
      have : y = positiveIn H φ x := Subtype.ext heq
      exact this ▸ hy
    have hall (z : borel H φ) : z ∈ S := by
      obtain ⟨⟨h,x⟩,rfl⟩ := (borelEquiv H φ hss hH hφ).surjective z
      exact S.add_mem (hsC h) (hx x)
    apply Submodule.span_le.mpr
    rintro _ ⟨a,rfl⟩
    exact all_differences_mem H φ χ hall a

theorem induced_presentation : induced_presentation_type.{u} := by
  intro L _ _ _ hss H _ φ hφ μ χ hχ e he
  have hH := RealRootSpace.cartan_isMaximalToral hss H
  change ∃ E : (U L ⧸ definingIdeal H φ μ e) ≃ₗ[U L] induced H φ χ,
    ∀ a : U L, E ((definingIdeal H φ μ e).mkQ a) = tensorClass H φ χ a 1
  rw [ideal_eq_characterIdeal H φ χ hss hH hφ μ hχ e he]
  exact induced_characterQuotient H φ χ

end Induction

end LieAlgebrasAndRepresentations.VermaModules
