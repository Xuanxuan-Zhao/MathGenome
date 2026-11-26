import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricRationalBruhat
import LinearAlgebraicGroups.Flag.BruhatCells
import Batteries.Tactic.OpenPrivate
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.PullbackCarrier

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricRationalBruhat

open _root_.LinearAlgebraicGroups.Specs

open private normalizerLabel_eq normalizerLabel_ker from
  LinearAlgebraicGroups.Flag.BruhatCells

private theorem factorsThroughImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Z) [IsImmersion f]
    (g : Y ⟶ Z) [IsReduced Y] (hg : Set.range g ⊆ Set.range f) :
    ∃ l : Y ⟶ X, l ≫ f = g := by
  let j := f.coborderRange.ι
  let i := f.liftCoborder
  have hi : i ≫ j = f := f.liftCoborder_ι
  have hj : Set.range g ⊆ Set.range j := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hg (Set.mem_range_self y)
    exact ⟨i x, by rw [← Scheme.Hom.comp_apply, hi, hx]⟩
  let g' := IsOpenImmersion.lift j g hj
  have hg' : g' ≫ j = g := IsOpenImmersion.lift_fac j g hj
  let p := pullback.snd i g'
  have : Surjective p := by
    constructor
    intro y
    change y ∈ Set.range (pullback.snd i g')
    rw [Scheme.Pullback.range_snd]
    obtain ⟨x, hx⟩ := hg (Set.mem_range_self y)
    refine ⟨x, j.isEmbedding.injective ?_⟩
    simp only [← Scheme.Hom.comp_apply, hi, hg', hx]
  have : IsClosedImmersion p := inferInstanceAs (IsClosedImmersion (pullback.snd i g'))
  have : IsIso p := isIso_of_isClosedImmersion_of_surjective p
  refine ⟨inv p ≫ pullback.fst i g', ?_⟩
  calc
    _ = (inv p ≫ pullback.fst i g') ≫ (i ≫ j) :=
      congrArg (fun a : X ⟶ Z ↦ (inv p ≫ pullback.fst i g') ≫ a) hi.symm
    _ = inv p ≫ pullback.snd i g' ≫ (g' ≫ j) := by
      rw [Category.assoc, pullback.condition_assoc]
    _ = inv p ≫ pullback.snd i g' ≫ g :=
      congrArg (fun a : Y ⟶ Z ↦ inv p ≫ pullback.snd i g' ≫ a) hg'
    _ = g := by
      rw [← Category.assoc, show inv p ≫ pullback.snd i g' = 𝟙 Y from IsIso.inv_hom_id p,
        Category.id_comp]

/-- The split Bruhat decomposition on ground-field points, with the given Borel
detected by the identity label of the same Weyl representatives. -/
theorem rationalBruhat : Specs.ExceptionalParahoricRationalBruhat.Statement.{u} := by
  classical
  intro k _ G hG T B hT hmax hB hTB
  obtain ⟨hc, D, J, _roots, _opposite, _positiveRadical, _negativeRadical, _cocharacter, _base,
    _hOpposite, _hTorus, _hRoots, _hPositive, _hNegative, _hRegular, _hChamber, _hBase,
    _representatives, ⟨Q⟩, data⟩ :=
    Flag.BruhatCells.bruhatCells G hG T B hT hmax hB hTB
  let := hc
  refine ⟨hc, D, J, ?_⟩
  intro n hn
  dsimp only
  obtain ⟨a, _, cells⟩ := data Q
  obtain ⟨A, C, _, disjointCells, cover, _⟩ := cells n hn
  let R := CommAlgCat.of k k
  let Y := (testSpec k).obj (Opposite.op R)
  let r : D.rootDatum.weylGroup → (Y ⟶ G.val.X) :=
    fun w ↦ toUnit Y ≫ n w ≫ J.normalizer.inclusion.hom.hom
  change (∀ g : Y ⟶ G.val.X, ∃ (w : D.rootDatum.weylGroup) (b₁ b₂ : Y ⟶ B.group.X),
    g = (b₁ ≫ B.inclusion.hom.hom) * r w * (b₂ ≫ B.inclusion.hom.hom)) ∧
    (∀ w, r w ∈ SubgroupSections B Y ↔ w = 1)
  constructor
  · intro g
    let y₀ : Y.left := IsLocalRing.closedPoint k
    have : Subsingleton Y.left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of k)))
    have : IsReduced Y.left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
    have hm : g.left y₀ ∈ ⋃ w, Set.range (C w).doubleOrbitInclusion.left := by
      rw [cover]
      exact Set.mem_univ _
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hm
    let f := (C w).doubleOrbitInclusion
    have : IsImmersion f.left := (C w).doubleOrbitImmersion
    have hrange : Set.range g.left ⊆ Set.range f.left := by
      rintro _ ⟨y, rfl⟩
      rw [show y = y₀ from Subsingleton.elim _ _]
      exact hw
    obtain ⟨l, hl⟩ := factorsThroughImmersion f.left g.left hrange
    let p : Y ⟶ (C w).doubleOrbit :=
      Over.homMk l (by rw [← Over.w f, ← Category.assoc, hl, Over.w g])
    have hp : p ≫ f = g := Over.OverMorphism.ext hl
    obtain ⟨b₁, b₂, hb⟩ := ((C w).doubleOrbitSections Y g).mp ⟨p, hp⟩
    exact ⟨w, b₁, b₂, hb.symm⟩
  · have h₁ : r 1 ∈ SubgroupSections B Y :=
      normalizerLabel_ker J hTB Y (n 1) (normalizerLabel_eq J (hn 1))
    intro w
    refine ⟨?_, fun hw ↦ hw ▸ h₁⟩
    intro hw
    by_contra hne
    have hfactor : r w * (r 1)⁻¹ ∈ SubgroupSections B Y :=
      (SubgroupSections B Y).mul_mem hw ((SubgroupSections B Y).inv_mem h₁)
    obtain ⟨b, hb⟩ := hfactor
    change b ≫ B.inclusion.hom.hom = r w * (r 1)⁻¹ at hb
    obtain ⟨p, hp⟩ := ((C w).doubleOrbitSections Y (r w)).mpr
      ⟨1, 1, by
        change (1 ≫ B.inclusion.hom.hom) * r w * (1 ≫ B.inclusion.hom.hom) = r w
        rw [MonObj.one_comp, one_mul, mul_one]⟩
    obtain ⟨q, hq⟩ := ((C 1).doubleOrbitSections Y (r w)).mpr
      ⟨b, 1, by
        change (b ≫ B.inclusion.hom.hom) * r 1 * (1 ≫ B.inclusion.hom.hom) = r w
        rw [hb, MonObj.one_comp, mul_one, inv_mul_cancel_right]⟩
    let y₀ : Y.left := IsLocalRing.closedPoint k
    have hp' : (C w).doubleOrbitInclusion.left (p.left y₀) = (r w).left y₀ :=
      congrArg (fun m : Y ⟶ G.val.X ↦ m.left y₀) hp
    have hq' : (C 1).doubleOrbitInclusion.left (q.left y₀) = (r w).left y₀ :=
      congrArg (fun m : Y ⟶ G.val.X ↦ m.left y₀) hq
    exact Set.disjoint_left.mp (disjointCells w 1 hne).2 ⟨_, hp'⟩ ⟨_, hq'⟩

end LinearAlgebraicGroups.Arithmetic.ExceptionalParahoricRationalBruhat
