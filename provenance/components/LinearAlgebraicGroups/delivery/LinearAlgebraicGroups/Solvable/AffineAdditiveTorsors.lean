import Specs.LinearAlgebraicGroups.Solvable.AffineAdditiveTorsors
import LinearAlgebraicGroups.Affine.StandardGroups
import LinearAlgebraicGroups.Flag.FppfTorsors
import Mathlib.AlgebraicGeometry.Sites.BigZariski
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups
namespace AdditiveDescent

open Specs.AdditiveDescent
open Algebra.TensorProduct

noncomputable section

section Cech

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

private abbrev contract₂ :
    B ⊗[A] (B ⊗[A] B) →ₗ[A] B ⊗[A] B :=
  ((lmul' A (S := B)).toLinearMap.rTensor B).comp
    (Algebra.TensorProduct.assoc A A A B B B).symm.toLinearEquiv.toLinearMap

private abbrev contract₃ :
    B ⊗[A] (B ⊗[A] (B ⊗[A] B)) →ₗ[A] B ⊗[A] (B ⊗[A] B) :=
  ((lmul' A (S := B)).toLinearMap.rTensor (B ⊗[A] B)).comp
    (Algebra.TensorProduct.assoc A A A B B (B ⊗[A] B)).symm.toLinearEquiv.toLinearMap

private theorem d₁_d₀ : (d₁ A B).comp (d₀ A B) = 0 := by
  apply LinearMap.ext
  intro b
  simp [d₁, d₀, face₀, face₁, face₂, TensorProduct.tmul_sub]

private theorem contract_identity :
    (contract₃ A B).comp ((d₁ A B).lTensor B) +
      ((d₀ A B).lTensor B).comp (contract₂ A B) = LinearMap.id := by
  apply TensorProduct.ext'
  intro a y
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | tmul b c => simp [d₁, d₀, face₀, face₁, face₂]

/-- In degree one, the faithfully flat Amitsur complex is exact. -/
theorem cechExactAtOne : CechExactAtOne.{u} := by
  intro A B _ _ _ _
  apply (Module.FaithfullyFlat.lTensor_exact_iff_exact A B _ _).1
  intro x
  constructor
  · intro hx
    refine ⟨contract₂ A B x, ?_⟩
    have h := LinearMap.congr_fun (contract_identity A B) x
    simpa [hx] using h
  · rintro ⟨y, rfl⟩
    have h := LinearMap.congr_fun (congrArg (LinearMap.lTensor B) (d₁_d₀ A B)) y
    simpa [LinearMap.lTensor_comp] using h

end Cech

section Cover

open Specs.Fppf

variable {k : Type u} [Field k] {S : SchemeOver k} {H : Specs.GroupScheme k}

private theorem overHom_ext {U V : Over S} {f g : U ⟶ V}
    (h : f.left.left = g.left.left) : f = g :=
  Over.OverMorphism.ext (Over.OverMorphism.ext h)

private abbrev liftTest (U : Over S) {X : Scheme.{u}} (p : X ⟶ U.left.left) : Over S :=
  Over.mk (Over.homMk (U := Over.mk (p ≫ U.left.hom)) p rfl ≫ U.hom)

private def testHom {U V : Over S} (f : U.left.left ⟶ V.left.left)
    (h : f ≫ V.hom.left = U.hom.left) : U ⟶ V :=
  Over.homMk (Over.homMk f (by
    rw [← Over.w V.hom, ← Category.assoc, h, Over.w U.hom]))
    (Over.OverMorphism.ext h)

private theorem sectionSieve_iff (P : SchemeAction S H) (U : Over S)
    {X : Scheme.{u}} (p : X ⟶ U.left.left) :
    Sieve.overEquiv U.left (Sieve.overEquiv U (P.sectionSieve U)) p ↔
      Nonempty (P.Section (liftTest U p)) := by
  rw [Sieve.overEquiv_iff, Sieve.overEquiv_iff]
  rfl

private theorem arrows_cover {U : Over S} {ι : Type*} (V : ι → Over S) (g : ∀ i, V i ⟶ U)
    (h : Sieve.ofArrows (fun i ↦ (V i).left.left) (fun i ↦ (g i).left.left) ∈
      Scheme.fppfTopology U.left.left) :
    Sieve.ofArrows V g ∈ torsorTopology S U := by
  change Sieve.overEquiv U.left (Sieve.overEquiv U (Sieve.ofArrows V g)) ∈ Scheme.fppfTopology U.left.left
  rwa [Sieve.overEquiv_ofArrows, Sieve.overEquiv_ofArrows]

private theorem sections_on_sigma (P : SchemeAction S H) {U : Over S}
    {ι : Type u} {X : ι → Scheme.{u}} (f : ∀ i, X i ⟶ U.left.left)
    (x : ∀ i, P.Section (liftTest U (f i))) :
    Nonempty (P.Section (liftTest U (Sigma.desc f))) := by
  let V := liftTest U (Sigma.desc f)
  let g (i : ι) : liftTest U (f i) ⟶ V :=
    testHom (Sigma.ι X i) (by simp [V, liftTest, ← Category.assoc])
  have hcov : Sieve.ofArrows _ g ∈ torsorTopology S V := by
    apply arrows_cover
    exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _
      (sigmaOpenCover X).mem_grothendieckTopology
  have hP := (isSheaf_iff_isSheaf_of_type _ _).1 P.sheaf.property
  have hsheaf := hP.isSheafFor _ hcov
  have hcompat : Presieve.Arrows.Compatible P.sheaf.obj g x := by
    intro i j Z a b hab
    have heq : a.left.left ≫ Sigma.ι X i = b.left.left ≫ Sigma.ι X j :=
      congrArg (fun m : Z ⟶ V ↦ m.left.left) hab
    by_cases hij : i = j
    · subst j
      have : a = b := overHom_ext ((cancel_mono (Sigma.ι X i)).mp heq)
      rw [this]
    · have : IsEmpty Z.left.left := isEmpty_of_commSq_sigmaι_of_ne ⟨heq⟩ hij
      have hb : (⊥ : Sieve Z) ∈ torsorTopology S Z := by
        change Sieve.overEquiv Z.left (Sieve.overEquiv Z ⊥) ∈ Scheme.fppfTopology _
        simp only [map_bot]
        exact Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage _
          (Scheme.bot_mem_grothendieckTopology (P := @IsOpenImmersion) Z.left.left)
      have hf := hP.isSheafFor (⊥ : Presieve Z) (by simpa only [Sieve.generate_bot] using hb)
      exact hf.isSeparatedFor.ext (by simp)
  obtain ⟨t, _, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hsheaf x hcompat
  exact ⟨t⟩

private theorem exists_affine_cover_section (P : FppfTorsor S H) (U : Over S)
    [IsAffine U.left.left] :
    ∃ (B : CommRingCat.{u}) (p : Spec B ⟶ U.left.left),
      Flat p ∧ Surjective p ∧ LocallyOfFinitePresentation p ∧
      Nonempty (P.1.Section (liftTest U p)) := by
  let R := Sieve.overEquiv U.left (Sieve.overEquiv U (P.1.sectionSieve U))
  have hR : R ∈ Scheme.fppfTopology U.left.left := P.2.2 U
  let : Scheme.fppfPrecoverage.HasIsos := ⟨fun f _ ↦ f.singleton_mem_fppfPrecoverage⟩
  obtain ⟨V, hV, hle⟩ := (Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
    (J := Scheme.fppfPrecoverage)).1 hR
  obtain ⟨𝒰, rfl⟩ := Precoverage.mem_iff_exists_zeroHypercover.mp hV
  let original : U.left.left.Cover (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation)) := 𝒰
  let 𝒰' := original.ulift
  have hle' (i : 𝒰'.I₀) : R (𝒰'.f i) :=
    hle _ _ ⟨original.idx i⟩
  have : QuasiCompactCover 𝒰'.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp
      (Scheme.fppfPrecoverage_le_fpqcPrecoverage _ 𝒰'.mem₀).1
  have : IsZariskiLocalAtSource (@Flat : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  have : IsZariskiLocalAtSource (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FinitePresentation)
  have : IsZariskiLocalAtSource
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsLocalAtSource.inf _ _
  obtain ⟨𝒱, e, hfin, _⟩ := QuasiCompactCover.exists_hom.{u,u} 𝒰'
  let W := ∐ 𝒱.cover.X
  let p : W ⟶ U.left.left := Sigma.desc 𝒱.cover.f
  have : Finite 𝒱.cover.I₀ := hfin
  have : ∀ i, IsAffine (𝒱.cover.X i) := fun i ↦ inferInstanceAs (IsAffine (Spec _))
  have : IsAffine W := inferInstanceAs (IsAffine (∐ 𝒱.cover.X))
  have hp : Flat p ∧ LocallyOfFinitePresentation p := 𝒱.cover.sigma.map_prop default
  have hsurj : Surjective p := by
    constructor
    intro z
    obtain ⟨i, y, rfl⟩ := 𝒱.cover.exists_eq z
    exact ⟨Sigma.ι 𝒱.cover.X i y, by simp [← Scheme.Hom.comp_apply, p]⟩
  have hsections (i : 𝒱.I₀) : Nonempty (P.1.Section (liftTest U (𝒱.cover.f i))) := by
    apply (sectionSieve_iff P.1 U _).mp
    rw [← e.w₀ i]
    apply R.downward_closed (g := e.h₀ i)
    exact hle' (e.s₀ i)
  obtain ⟨x⟩ := sections_on_sigma P.1 𝒱.cover.f (fun i ↦ (hsections i).some)
  let q := W.isoSpec.inv ≫ p
  let g : liftTest U q ⟶ liftTest U p :=
    testHom W.isoSpec.inv (by simp [q, liftTest, ← Category.assoc])
  have : Flat p := hp.1
  have : LocallyOfFinitePresentation p := hp.2
  exact ⟨_, q, inferInstanceAs (Flat (W.isoSpec.inv ≫ p)),
    inferInstanceAs (Surjective (W.isoSpec.inv ≫ p)),
    inferInstanceAs (LocallyOfFinitePresentation (W.isoSpec.inv ≫ p)), ⟨P.1.res g x⟩⟩

end Cover

section AffineTests

open Specs.Fppf

variable {k : Type u} [Field k] {S : SchemeOver k} {H : Specs.GroupScheme k}
variable (A : TestAlgebra k)

/-- A test algebra over the affine base, viewed as an algebra over the ground field. -/
private abbrev testAlgebra (B : Type u) [CommRing B] [Algebra A B] : TestAlgebra k :=
  @CommAlgCat.of k _ B _ ((algebraMap A B).comp (algebraMap k A)).toAlgebra

private def restrictAlg {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) : testAlgebra A B ⟶ testAlgebra A C :=
  letI : Algebra k B := ((algebraMap A B).comp (algebraMap k A)).toAlgebra
  letI : Algebra k C := ((algebraMap A C).comp (algebraMap k A)).toAlgebra
  CommAlgCat.ofHom { f.toRingHom with commutes' := fun x ↦ f.commutes (algebraMap k A x) }

variable {A} (r : (testSpec k).obj (op A) ⟶ S)

private abbrev baseRingMap (B : Type u) [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

private def affineBaseMap (B : Type u) [CommRing B] [Algebra A B] :
    (testSpec k).obj (op (testAlgebra A B)) ⟶ (testSpec k).obj (op A) :=
  Over.homMk (baseRingMap (A := A) B) (by
    change baseRingMap (A := A) B ≫ Spec.map (CommRingCat.ofHom (algebraMap k A)) =
      Spec.map (CommRingCat.ofHom ((algebraMap A B).comp (algebraMap k A)))
    exact (Spec.map_comp _ _).symm)

private abbrev affineTest (B : Type u) [CommRing B] [Algebra A B] : Over S :=
  Over.mk (affineBaseMap B ≫ r)

private theorem baseRingMap_comp {B C : Type u} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (f : B →ₐ[A] C) :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ baseRingMap (A := A) B = baseRingMap C := by
  unfold baseRingMap
  rw [← Spec.map_comp]
  congr 1
  ext x
  exact f.commutes x

private def affineMap {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) : affineTest r C ⟶ affineTest r B :=
  Over.homMk ((testSpec k).map (restrictAlg A f).op) (by
    apply Over.OverMorphism.ext
    let r₀ : Spec (CommRingCat.of A) ⟶ S.left := r.left
    exact (Category.assoc (Spec.map (CommRingCat.ofHom f.toRingHom))
      (baseRingMap (A := A) B) r₀).symm.trans
        (congrArg (· ≫ r₀) (baseRingMap_comp f)))

private theorem res_comp (P : SchemeAction S H) {U V W : Over S}
    (f : U ⟶ V) (g : V ⟶ W) (x : P.Section W) :
    P.res f (P.res g x) = P.res (f ≫ g) x := by
  exact (P.sheaf.obj.map_comp_apply g.op f.op x).symm

private theorem affineMap_comp {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C] [Algebra A D] (f : B →ₐ[A] C) (g : C →ₐ[A] D) :
    affineMap r g ≫ affineMap r f = affineMap r (g.comp f) := by
  apply overHom_ext
  change Spec.map (CommRingCat.ofHom g.toRingHom) ≫ Spec.map (CommRingCat.ofHom f.toRingHom) =
    Spec.map (CommRingCat.ofHom (g.comp f).toRingHom)
  exact (Spec.map_comp (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)).symm

private abbrev G := groupSections S H

/-- The additive coordinate of an element in the group acting on an affine test object. -/
private def coordinate (e : (groupPointsFunctor k).obj H ≅ Specs.StandardGroups.additivePoints k)
    (B : Type u) [CommRing B] [Algebra A B] :
    ((G (S := S) (H := H)).obj (op (affineTest r B))) ≃* Multiplicative B := by
  exact MulEquiv.ulift.trans (Iso.groupIsoToMulEquiv (e.app (testAlgebra A B)))

variable (e : (groupPointsFunctor k).obj H ≅ Specs.StandardGroups.additivePoints k)

private abbrev value {B : Type u} [CommRing B] [Algebra A B]
    (g : (groupSections S H).obj (op (affineTest r B))) : B :=
  Multiplicative.toAdd (coordinate r e B g)

private theorem value_map {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
    (f : B →ₐ[A] C) (g : (groupSections S H).obj (op (affineTest r B))) :
    value r e ((groupSections S H).map (affineMap r f).op g) = f (value r e g) := by
  exact e.hom.naturality_apply (restrictAlg A f) g.down

variable {B : Type u} [CommRing B] [Algebra A B]

local notation "B₂" => B ⊗[A] B
local notation "B₃" => B ⊗[A] (B ⊗[A] B)

private abbrev p₀ : affineTest r B₂ ⟶ affineTest r B :=
  affineMap r (includeLeft : B →ₐ[A] B₂)

private abbrev p₁ : affineTest r B₂ ⟶ affineTest r B :=
  affineMap r (includeRight : B →ₐ[A] B₂)

private theorem transition_is_cocycle (P : FppfTorsor S H) (x : P.1.Section (affineTest r B))
    (g : (groupSections S H).obj (op (affineTest r B₂)))
    (hg : P.1.act (P.1.res (p₀ r) x) g = P.1.res (p₁ r) x) :
    d₁ A B (value r e g) = 0 := by
  let q₀ := affineMap r (face₀ A B)
  let q₁ := affineMap r (face₁ A B)
  let q₂ := affineMap r (face₂ A B)
  have h₀ : q₂ ≫ p₀ r = q₁ ≫ p₀ r := by
    dsimp only [q₂, q₁, p₀]
    rw [affineMap_comp, affineMap_comp]
    congr 1
  have h₁ : q₂ ≫ p₁ r = q₀ ≫ p₀ r := by
    dsimp only [q₂, q₀, p₀, p₁]
    rw [affineMap_comp, affineMap_comp]
    congr 1
  have h₂ : q₀ ≫ p₁ r = q₁ ≫ p₁ r := by
    dsimp only [q₀, q₁, p₁]
    rw [affineMap_comp, affineMap_comp]
    congr 1
  let G := groupSections S H
  have translate (q : affineTest r B₃ ⟶ affineTest r B₂) :
      P.1.act (P.1.res (q ≫ p₀ r) x) (G.map q.op g) = P.1.res (q ≫ p₁ r) x := by
    rw [← res_comp, ← P.1.map_act, hg]
    exact res_comp P.1 q (p₁ r) x
  have hm : G.map q₂.op g * G.map q₀.op g = G.map q₁.op g := by
    apply (P.2.1 _ (P.1.res (q₂ ≫ p₀ r) x)).1
    rw [← P.1.act_mul, translate, h₁, translate, h₂, h₀, translate]
  have hv := congrArg (value r e (B := B₃)) hm
  change value r e (G.map q₂.op g * G.map q₀.op g) =
    value r e (G.map q₁.op g) at hv
  rw [show value r e (G.map q₂.op g * G.map q₀.op g) =
    value r e (G.map q₂.op g) + value r e (G.map q₀.op g)
    from congrArg Multiplicative.toAdd (map_mul (coordinate r e B₃) _ _)] at hv
  dsimp only [G, q₂, q₀, q₁] at hv
  rw [value_map, value_map, value_map] at hv
  change face₀ A B (value r e g) - face₁ A B (value r e g) + face₂ A B (value r e g) = 0
  rw [← hv]
  abel

include e in
private theorem corrected_section_compatible [Module.FaithfullyFlat A B]
    (P : FppfTorsor S H) (x : P.1.Section (affineTest r B)) :
    ∃ y : P.1.Section (affineTest r B), P.1.res (p₀ r) y = P.1.res (p₁ r) y := by
  obtain ⟨g, hg⟩ := (P.2.1 _ (P.1.res (p₀ r) x)).2 (P.1.res (p₁ r) x)
  obtain ⟨b, hb⟩ := (cechExactAtOne A B (value r e g)).mp
    (transition_is_cocycle r e P x g hg)
  let a := (coordinate r e B).symm (Multiplicative.ofAdd (-b))
  have ha : value r e a = -b :=
    congrArg Multiplicative.toAdd ((coordinate r e B).apply_symm_apply _)
  let G := groupSections S H
  have hcorr : G.map (p₀ r).op a = g * G.map (p₁ r).op a := by
    apply (coordinate r e B₂).injective
    apply Multiplicative.toAdd.injective
    rw [map_mul]
    change value r e (G.map (p₀ r).op a) = value r e g + value r e (G.map (p₁ r).op a)
    rw [value_map, value_map, ha, map_neg, map_neg, ← hb]
    let l : B →ₐ[A] B₂ := includeLeft
    let t : B →ₐ[A] B₂ := includeRight
    change -l b = t b - l b + -t b
    abel
  refine ⟨P.1.act x a, ?_⟩
  change P.1.sheaf.obj.map (p₀ r).op (P.1.act x a) =
    P.1.sheaf.obj.map (p₁ r).op (P.1.act x a)
  rw [P.1.map_act, P.1.map_act, hcorr, ← P.1.act_mul, hg]

private def coveringMap : affineTest r B ⟶ Over.mk r :=
  Over.homMk (affineBaseMap B) rfl

private theorem coveringMap_condition [Module.FaithfullyFlat A B]
    (hfp : LocallyOfFinitePresentation (baseRingMap (A := A) B)) :
    Sieve.generate (Presieve.singleton (coveringMap r (B := B))) ∈
      torsorTopology S (Over.mk r) := by
  have hff : (algebraMap A B).FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  have ⟨hf, hs⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap A B))).mpr hff
  have hcov : Sieve.generate (Presieve.singleton (baseRingMap (A := A) B)) ∈
      Scheme.fppfTopology (Spec (CommRingCat.of A)) :=
    Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage _)
  have h := arrows_cover (U := Over.mk r) (fun _ : PUnit.{1} ↦ affineTest r B)
    (fun _ ↦ coveringMap r (B := B))
  unfold Sieve.ofArrows at h
  simp only [Presieve.ofArrows_of_unique] at h
  exact h hcov

private theorem compatible_on_cover (P : SchemeAction S H)
    (y : P.Section (affineTest r B)) (hy : P.res (p₀ r) y = P.res (p₁ r) y)
    {Z : Over S} (a b : Z ⟶ affineTest r B)
    (hab : a ≫ coveringMap r = b ≫ coveringMap r) :
    P.res a y = P.res b y := by
  let f := baseRingMap (A := A) B
  have hh : a.left.left ≫ f = b.left.left ≫ f :=
    congrArg (fun m : Z ⟶ Over.mk r ↦ m.left.left) hab
  let i := pullbackSpecIso A B B
  let m : Z.left.left ⟶ Spec (CommRingCat.of B₂) :=
    pullback.lift a.left.left b.left.left hh ≫ i.hom
  have hm₀ : m ≫ (p₀ r (B := B)).left.left = a.left.left := by
    change m ≫ Spec.map (CommRingCat.ofHom (includeLeft : B →ₐ[A] B₂).toRingHom) = _
    let ι := Spec.map (CommRingCat.ofHom (includeLeft : B →ₐ[A] B₂).toRingHom)
    let l := pullback.lift a.left.left b.left.left hh
    have h : i.hom ≫ ι = pullback.fst f f := pullbackSpecIso_hom_fst A B B
    exact (Category.assoc l i.hom ι).trans
      ((congrArg (l ≫ ·) h).trans (pullback.lift_fst _ _ _))
  have hm₁ : m ≫ (p₁ r (B := B)).left.left = b.left.left := by
    change m ≫ Spec.map (CommRingCat.ofHom (includeRight : B →ₐ[A] B₂).toRingHom) = _
    let ι := Spec.map (CommRingCat.ofHom (includeRight : B →ₐ[A] B₂).toRingHom)
    let l := pullback.lift a.left.left b.left.left hh
    have h : i.hom ≫ ι = pullback.snd f f := pullbackSpecIso_hom_snd A B B
    exact (Category.assoc l i.hom ι).trans
      ((congrArg (l ≫ ·) h).trans (pullback.lift_snd _ _ _))
  let q : Z ⟶ affineTest r B₂ := testHom m (by
    have hp : (p₀ r (B := B)).left.left ≫ (affineTest r B).hom.left =
        (affineTest r B₂).hom.left := congrArg Over.Hom.left (Over.w (p₀ r (B := B)))
    exact (congrArg (m ≫ ·) hp.symm).trans
      ((Category.assoc m (p₀ r (B := B)).left.left (affineTest r B).hom.left).symm.trans
        ((congrArg (· ≫ (affineTest r B).hom.left) hm₀).trans
          (congrArg Over.Hom.left (Over.w a)))))
  have hqa : q ≫ p₀ r = a := overHom_ext hm₀
  have hqb : q ≫ p₁ r = b := overHom_ext hm₁
  rw [← hqa, ← hqb, ← res_comp, ← res_comp, hy]

include e in
private theorem section_on_affine [Module.FaithfullyFlat A B]
    (P : FppfTorsor S H) (x : P.1.Section (affineTest r B))
    (hfp : LocallyOfFinitePresentation (baseRingMap (A := A) B)) :
    Nonempty (P.1.Section (Over.mk r)) := by
  obtain ⟨y, hy⟩ := corrected_section_compatible r e P x
  have hs := (isSheaf_iff_isSheaf_of_type _ _).1 P.1.sheaf.property
  have hsheaf := hs.isSheafFor _ (coveringMap_condition r hfp)
  rw [Presieve.isSheafFor_singleton] at hsheaf
  obtain ⟨z, _, _⟩ := hsheaf y (fun a b h ↦ compatible_on_cover r P.1 y hy a b h)
  exact ⟨z⟩

end AffineTests

open Specs.Fppf

/-- An fppf torsor under the additive group on an affine scheme admits a global section. -/
theorem affineAdditiveTorsorSection : AffineAdditiveTorsorSection.{u} := by
  intro k _ H hGa S hS P
  obtain ⟨A, ⟨i⟩⟩ := essImage_algSpec.mpr hS
  let U : Over S := Over.mk i.hom
  have : IsAffine U.left.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A.unop)))
  obtain ⟨B, f, hf, hs, hp, hx⟩ := exists_affine_cover_section P U
  obtain ⟨φ, hφ⟩ := Spec.map_surjective f
  let _ : Algebra A.unop B := φ.hom.toAlgebra
  change baseRingMap (A := A.unop) B = f at hφ
  have hff : Module.FaithfullyFlat A.unop B := by
    apply RingHom.faithfullyFlat_algebraMap_iff.mp
    apply (flat_and_surjective_SpecMap_iff φ).mp
    change Flat (baseRingMap (A := A.unop) B) ∧ Surjective (baseRingMap (A := A.unop) B)
    exact ⟨hφ.symm ▸ hf, hφ.symm ▸ hs⟩
  have hp' : LocallyOfFinitePresentation (baseRingMap (A := A.unop) B) := hφ ▸ hp
  obtain ⟨x⟩ := hx
  let g : affineTest i.hom B ⟶ liftTest U f := testHom (𝟙 _) (by
    change 𝟙 _ ≫ (f ≫ i.hom.left) = baseRingMap (A := A.unop) B ≫ i.hom.left
    exact (Category.id_comp _).trans (congrArg (· ≫ i.hom.left) hφ.symm))
  obtain ⟨y⟩ := section_on_affine i.hom hGa P (P.1.res g x) hp'
  let back : Over.mk (𝟙 S) ⟶ U := Over.homMk i.inv (by simp [U])
  exact ⟨P.1.res back y⟩

open private additiveRepresentation convolutionIso spectrumPointsIso
  from LinearAlgebraicGroups.Affine.StandardGroups

/-- The affine-base statement for the additive group constructed in A03. -/
theorem additiveTorsorSection {k : Type u} [Field k] (S : SchemeOver k)
    (hS : IsAffine S.left) (P : FppfTorsor S (StandardGroups.additiveGroup k).val) :
    Nonempty (P.1.Section (Over.mk (𝟙 S))) := by
  let _ := StandardGroups.additiveHopf k
  exact affineAdditiveTorsorSection (spectrumPointsIso (convolutionIso (additiveRepresentation k)))
    S hS P

/-- In particular, an additive torsor over the ground field has a rational point. -/
theorem additiveTorsorFieldSection {k : Type u} [Field k]
    (P : FppfTorsor (fieldBase k) (StandardGroups.additiveGroup k).val) :
    Nonempty (P.1.Section (fieldTest k)) :=
  additiveTorsorSection (fieldBase k) (inferInstanceAs (IsAffine (Spec (CommRingCat.of k)))) P

end
end AdditiveDescent
end LinearAlgebraicGroups
