import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.CompactTelescope
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedCoproducts
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.DerivedTriangles
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Telescope
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.IndexedSums
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.CoefficientLiftComparison
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomotopyShift
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Batteries.Tactic.OpenPrivate

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe u v w t v' d e j

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG
open CompactTelescope (Compact HomSequenceColimit homGroup representedMap sequenceCocone
  telescopeStage)
open DerivedKProjective (derivedCategoryInstance)

noncomputable section

set_option linter.style.haveILetI false

private def mapCofanColimit {I : Type j}
    {C : Type*} [Category* C] {D : Type*} [Category* D] (F : C ⥤ D)
    {Y : I → C} {P : C} (inj : ∀ n, Y n ⟶ P)
    [PreservesColimit (Discrete.functor Y) F] (h : IsColimit (Cofan.mk P inj)) :
    IsColimit (Cofan.mk (F.obj P) fun n => F.map (inj n)) :=
  isColimitCofanMkObjOfIsColimit F Y inj h

open private module_one_sub_injective from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.Telescope

/-- The difference of the identity and the successor on an abelian-group sum is monic. -/
private theorem successorDifference_mono {Y : ℕ → AddCommGrpCat.{e}} {P : AddCommGrpCat.{e}}
    (inj : ∀ n, Y n ⟶ P) (hU : IsColimit (Cofan.mk P inj))
    (step : ∀ n, Y n ⟶ Y (n+1)) (s : P ⟶ P)
    (hs : ∀ n, inj n ≫ s = step n ≫ inj (n+1)) : Mono (𝟙 P - s) := by
  let F := (forget₂ (ModuleCat.{e} ℤ) AddCommGrpCat.{e}).asEquivalence.inverse
  letI : F.Additive := F.additive_of_preserves_binary_products
  apply Functor.mono_of_mono_map F
  rw [F.map_sub, F.map_id]
  apply (ModuleCat.mono_iff_injective _).2
  apply module_one_sub_injective (fun n => F.map (step n))
    (mapCofanColimit F inj hU) (F.map s)
  intro n
  exact (F.map_comp _ _).symm.trans ((congrArg F.map (hs n)).trans (F.map_comp _ _))

section Triangle

variable {D : Type d} [Category.{e} D] [Preadditive D] [HasShift D ℤ]
  [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

set_option backward.isDefEq.respectTransparency false in
private theorem homSequenceColimit_of_distinguished (C : D) (hC : Compact.{j} C)
    {Y : ℕ → D} {P Z : D} (step : ∀ n, Y n ⟶ Y (n+1))
    (inj : ∀ n, Y n ⟶ P) (hU : IsColimit (Cofan.mk P inj))
    (s : P ⟶ P) (hs : ∀ n, inj n ≫ s = step n ≫ inj (n+1))
    (b : P ⟶ Z) (δ : Z ⟶ (shiftFunctor D (1 : ℤ)).obj P)
    (hdist : Triangle.mk (𝟙 P - s) b δ ∈ distTriang D) :
    HomSequenceColimit C step (fun n => inj n ≫ b) := by
  let T := Triangle.mk (𝟙 P - s) b δ
  let H := homGroup C
  let J := shiftFunctor D (1 : ℤ)
  letI : PreservesColimitsOfShape (Discrete (ULift.{j} ℕ)) H := hC _
  letI : PreservesColimitsOfShape (Discrete ℕ) H :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence Equiv.ulift) H
  have hshift := mapCofanColimit J inj hU
  have hshiftHom := mapCofanColimit H (fun n => J.map (inj n)) hshift
  have hsm (n : ℕ) :
      H.map (J.map (inj n)) ≫ H.map (J.map s) =
        H.map (J.map (step n)) ≫ H.map (J.map (inj (n+1))) := by
    simp only [← H.map_comp, ← J.map_comp, hs]
  have hmono := successorDifference_mono _ hshiftHom _ _ hsm
  have hinj : Mono (H.map (J.map T.mor₁)) := by
    change Mono (H.map (J.map (𝟙 P - s)))
    simpa only [J.map_sub, J.map_id, H.map_sub, H.map_id] using hmono
  have hsurj : Function.Surjective (H.map b) := by
    intro x
    let f : C ⟶ Z := x
    change ∃ g : C ⟶ P, g ≫ b = f
    have hf : (H.map (J.map T.mor₁)) (f ≫ δ) = 0 := by
      change (f ≫ δ) ≫ J.map T.mor₁ = 0
      rw [Category.assoc]
      have hz : δ ≫ J.map T.mor₁ = 0 := comp_distTriang_mor_zero₃₁ T hdist
      exact (congrArg (fun q : Z ⟶ J.obj P => f ≫ q) hz).trans comp_zero
    have hzero : f ≫ δ = 0 := (AddCommGrpCat.mono_iff_injective _).mp hinj
      (hf.trans (map_zero _).symm)
    obtain ⟨g, hg⟩ := T.coyoneda_exact₃ hdist f hzero
    exact ⟨g, hg.symm⟩
  let S := (shortComplexOfDistTriangle T hdist).map H
  letI : Epi S.g := (AddCommGrpCat.epi_iff_surjective _).mpr hsurj
  have hex : S.Exact := H.map_distinguished_exact T hdist
  have hzero : (𝟙 P - s) ≫ b = 0 := comp_distTriang_mor_zero₁₂ T hdist
  have comm (n : ℕ) : step n ≫ (inj (n+1) ≫ b) = inj n ≫ b := by
    have h := congrArg (fun q => inj n ≫ q) hzero
    rw [← Category.assoc, Preadditive.comp_sub, Category.comp_id, Preadditive.sub_comp,
      hs, Category.assoc, comp_zero] at h
    exact (sub_eq_zero.mp h).symm
  let c := H.mapCocone (sequenceCocone step (fun n => inj n ≫ b) comm)
  have hHom := mapCofanColimit H inj hU
  let l (W : Cocone (Functor.ofSequence step ⋙ H)) :=
    Cofan.IsColimit.desc hHom (fun n => W.ι.app n)
  have l_ι (W : Cocone (Functor.ofSequence step ⋙ H)) (n : ℕ) :
      H.map (inj n) ≫ l W = W.ι.app n :=
    hHom.fac _ ⟨n⟩
  have l_zero (W : Cocone (Functor.ofSequence step ⋙ H)) : S.f ≫ l W = 0 := by
    apply hHom.hom_ext
    rintro ⟨n⟩
    change H.map (inj n) ≫ H.map (𝟙 P - s) ≫ l W = H.map (inj n) ≫ 0
    rw [← Category.assoc, ← H.map_comp, Preadditive.comp_sub, Category.comp_id, hs,
      H.map_sub, H.map_comp, Preadditive.sub_comp, Category.assoc, l_ι, l_ι, comp_zero]
    have hn := W.w (homOfLE (Nat.le_succ n))
    rw [Functor.comp_map, Functor.ofSequence_map_homOfLE_succ] at hn
    exact sub_eq_zero.mpr hn.symm
  have hc : IsColimit c := by
    refine IsColimit.mk (fun W => hex.desc (l W) (l_zero W)) ?_ ?_
    · intro W n
      change H.map (inj n ≫ b) ≫ hex.desc (l W) (l_zero W) = W.ι.app n
      calc
        _ = H.map (inj n) ≫ (S.g ≫ hex.desc (l W) (l_zero W)) := by
          rw [H.map_comp]
          exact Category.assoc _ _ _
        _ = H.map (inj n) ≫ l W :=
          congrArg (fun g : S.X₂ ⟶ W.pt => H.map (inj n) ≫ g) (hex.g_desc _ _)
        _ = W.ι.app n := l_ι W n
    · intro W m hm
      apply (cancel_epi S.g).1
      refine Eq.trans ?_ (hex.g_desc _ _).symm
      apply hHom.hom_ext
      rintro ⟨n⟩
      change H.map (inj n) ≫ H.map b ≫ m = H.map (inj n) ≫ l W
      rw [l_ι, ← Category.assoc, ← H.map_comp]
      exact hm n
  refine ⟨comm, ⟨hc⟩, ?_⟩
  intro f
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{e}) :=
    preservesFilteredColimitsOfSize_shrink _
  exact Concrete.isColimit_exists_rep _ hc f

end Triangle

section DG

variable {k : Type u} [CommRing k]
variable {B : DGCategoryModel.{u,v',w} k}

private theorem representedMap_comp (h : Derived.HomotopyCategoryLaws B)
    {M N P : RightDGModule B} (f : M ⟶ N) (g : N ⟶ P) :
    letI := derivedCategoryInstance B h
    representedMap h (f ≫ g) = representedMap h f ≫ representedMap h g := by
  letI := derivedCategoryInstance B h
  letI := Derived.homotopyCategory B h
  let R := toHomotopyCategory B ⋙ Derived.quotient B h
  exact R.map_comp f g

private theorem homotopyClass_sub {M N : RightDGModule B} (f g : M ⟶ N) :
    HomComplex.homotopyClass (Telescope.subMap f g) =
      HomComplex.homotopyClass f - HomComplex.homotopyClass g := by
  open Specs.DerivedFormalization.DG.Basic in
  change classOf (HomComplex.strictCycle (Telescope.subMap f g)) =
    classOf (HomComplex.strictCycle f) - classOf (HomComplex.strictCycle g)
  rw [← Submodule.Quotient.mk_sub]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact funext fun a => CochainComplex.HomComplex.Cochain.ofHom_sub (f.app a) (g.app a)

private theorem homotopyClass_sub_of_eq (h : Derived.HomotopyCategoryLaws B)
    (AK : letI := Derived.homotopyCategory B h; Preadditive (HomComplex.homotopyCategory B))
    (hAK : AK = homotopyPreadditive (A := B)) {M N : RightDGModule B} (f g : M ⟶ N) :
    letI := Derived.homotopyCategory B h
    letI := AK
    (show @Quiver.Hom (HomComplex.homotopyCategory B) _ M N from
      HomComplex.homotopyClass (Telescope.subMap f g)) =
      (show @Quiver.Hom (HomComplex.homotopyCategory B) _ M N from HomComplex.homotopyClass f) -
      (show @Quiver.Hom (HomComplex.homotopyCategory B) _ M N from HomComplex.homotopyClass g) := by
  subst AK
  exact homotopyClass_sub f g

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem compactTelescopeAt {A : DGCategoryModel.{u,v,w} k}
    (h : Derived.HomotopyCategoryLaws B) (F : RightDGModule A ⥤ RightDGModule B)
    (hTri : DerivedTriangles.TriangulationAt B h)
    (hSum : letI := Derived.homotopyCategory B h
      letI := derivedCategoryInstance B h
      ∀ {X : ℕ → RightDGModule A} {U : Cofan X}, IsColimit U →
        Nonempty (IsColimit (Cofan.mk ((Derived.quotient B h).obj (F.obj U.pt))
          (fun n => representedMap h (F.map (U.inj n))))))
    (hSub : ∀ {P : RightDGModule A} (f g : P ⟶ P),
      F.map (Telescope.subMap f g) = Telescope.subMap (F.map f) (F.map g))
    (hCone : ∀ {P : RightDGModule A} (f : P ⟶ P),
      ∃ E : F.obj (ShiftCone.cone f) ≅ ShiftCone.cone (F.map f),
        F.map (ShiftCone.coneInclusion f) ≫ E.hom = ShiftCone.coneInclusion (F.map f)) :
    CompactTelescope.CompactTelescopeAt h F := by
  let K := HomComplex.homotopyCategory B
  let D := Derived.derivedCategory B h
  letI := Derived.homotopyCategory B h
  letI := derivedCategoryInstance B h
  let Q : K ⥤ D := Derived.quotient B h
  let G : RightDGModule B ⥤ K := toHomotopyCategory B
  let R : RightDGModule B ⥤ D := G ⋙ Q
  obtain ⟨SK, AK, ZK, LK, hS, TK, _, _, _, HP, _, SD, AD, ZD, LD, qS, TD,
    _, qT, _, _, _, hDist, _⟩ := hTri
  letI := SK
  letI := AK
  letI := ZK
  letI := LK
  letI := TK
  letI : HasShift D ℤ := SD
  letI : Preadditive D := AD
  letI : HasZeroObject D := ZD
  letI : ∀ n : ℤ, (shiftFunctor D n).Additive := LD
  letI : Q.CommShift ℤ := qS
  letI : Pretriangulated D := TD
  letI : Q.IsTriangulated := qT
  refine ⟨AD, ?_⟩
  intro C hC X step U hU
  let f := Telescope.oneSubSuccessor step hU
  let p := Telescope.successor step hU
  let P : D := R.obj (F.obj U.pt)
  let Z : D := R.obj (F.obj (ShiftCone.cone f))
  let Y (n : ℕ) : D := R.obj (F.obj (X n))
  let i (n : ℕ) : Y n ⟶ P := R.map (F.map (U.inj n))
  let d (n : ℕ) : Y n ⟶ Y (n+1) := R.map (F.map (step n))
  let s : P ⟶ P := R.map (F.map p)
  let b : P ⟶ Z := R.map (F.map (ShiftCone.coneInclusion f))
  have hs (n : ℕ) : i n ≫ s = d n ≫ i (n+1) := by
    change R.map (F.map (U.inj n)) ≫ R.map (F.map p) =
      R.map (F.map (step n)) ≫ R.map (F.map (U.inj (n+1)))
    rw [← R.map_comp, ← R.map_comp, ← F.map_comp, ← F.map_comp]
    exact congrArg (fun a => R.map (F.map a)) (Telescope.inj_successor step hU n)
  have hAK : AK = homotopyPreadditive (A := B) := Subsingleton.elim _ _
  have ha : R.map (F.map f) = 𝟙 P - s := by
    change R.map (F.map (Telescope.subMap (𝟙 U.pt) p)) = _
    rw [hSub, F.map_id]
    let M := F.obj U.pt
    have he : G.map (Telescope.subMap (𝟙 M) (F.map p)) =
        G.map (𝟙 M) - G.map (F.map p) :=
      homotopyClass_sub_of_eq h AK hAK (𝟙 M) (F.map p)
    calc
      _ = Q.map (G.map (𝟙 M) - G.map (F.map p)) :=
        congrArg (fun g : G.obj M ⟶ G.obj M => Q.map g) he
      _ = R.map (𝟙 M) - s := Q.map_sub
      _ = 𝟙 P - s := congrArg (fun g : P ⟶ P => g - s) (R.map_id M)
  let T : Triangle D :=
    Q.mapTriangle.obj (DerivedTriangles.coneTriangle h SK (hS (F.obj U.pt) 1) (F.map f))
  have hT : T ∈ distTriang D := hDist (F.map f)
  obtain ⟨E, hE⟩ := hCone f
  let e : Z ≅ T.obj₃ := R.mapIso E
  let δ : Z ⟶ (shiftFunctor D (1 : ℤ)).obj P :=
    e.hom ≫ T.mor₃
  let T' : Triangle D := Triangle.mk (𝟙 P - s) b δ
  have eT : T' ≅ T := by
    refine Triangle.isoMk T' T (Iso.refl _) (Iso.refl _) e ?_ ?_ ?_
    · change (𝟙 P - s) ≫ 𝟙 P = 𝟙 P ≫ R.map (F.map f)
      simpa only [Category.comp_id, Category.id_comp] using ha.symm
    · change R.map (F.map (ShiftCone.coneInclusion f)) ≫ R.map E.hom =
        𝟙 _ ≫ R.map (ShiftCone.coneInclusion (F.map f))
      rw [← R.map_comp, Category.id_comp, hE]
    · change δ ≫ (shiftFunctor D (1 : ℤ)).map (𝟙 P) = δ
      simp only [(shiftFunctor D (1 : ℤ)).map_id P, Category.comp_id]
  have hT' : T' ∈ distTriang D := isomorphic_distinguished _ hT _ eT
  obtain ⟨hU'⟩ := hSum hU
  have result := homSequenceColimit_of_distinguished C hC d i hU' s hs b δ hT'
  have hlegs : (fun n => R.map (F.map (telescopeStage step hU n))) = fun n => i n ≫ b := by
    funext n
    simp only [telescopeStage, F.map_comp, R.map_comp, i, b, f]
  change HomSequenceColimit C d (fun n => R.map (F.map (telescopeStage step hU n)))
  rw [hlegs]
  exact result

/-- The strict telescope comparison is a quasi-isomorphism, and its image in
the adequate localization identifies the stage maps with the colimit legs. -/
theorem originalTelescopeComparison : CompactTelescope.OriginalTelescopeComparison.{u,v,w,t} := by
  intro k hk A B F h X step U hU L hL
  letI := Derived.homotopyCategory B h
  letI := derivedCategoryInstance B h
  let p := Telescope.telescopeComparison step hU L
  change Module.quasiIsomorphism p ∧ IsIso (representedMap h (F.map p)) ∧ _
  have hp := telescope_quasiIso step hU hL
  refine ⟨hp, ?_, ?_⟩
  · change IsIso ((Q B h).map (homotopyClass (F.map p)))
    apply Localization.inverts (Q B h) (quasiIsomorphisms B)
    exact (quasiIsomorphisms_homotopyClass (F.map p)).2
      ((DG.CoefficientLift.lift_quasiIso_iff p).2 hp)
  · intro n
    rw [← representedMap_comp, ← F.map_comp]
    congr 2
    unfold telescopeStage Telescope.telescopeComparison
    rw [Category.assoc, coneInclusion_coneComparison, inj_sumToSequence]

end DG

set_option backward.isDefEq.respectTransparency false in
/-- For a compact object of the adequate localization, Hom into the telescope
of an original strict sequence is the sequential colimit via the stage inclusions. -/
theorem originalCompactTelescope :
    CompactTelescope.OriginalCompactTelescope.{u,v,w,t} := by
  intro k hk A h
  let B := AmbientDerived.category.{u,v,w,t} A
  let F := AmbientDerived.strictInput.{u,v,w,t} A
  letI := Derived.homotopyCategory B h
  letI := derivedCategoryInstance B h
  apply compactTelescopeAt h F (ambientDerivedTriangulation.{u,v,w,t} A h)
  · intro X U hU
    let sr := DG.IndexedSums.strictSumOfIsColimit hU
    obtain ⟨r, hr, _, ⟨hR⟩⟩ := originalExistingDerivedCoproduct.{u,v,w,0,t} A h sr
    refine ⟨IsColimit.ofIsoColimit hR
      (Cofan.ext (c₁ := DerivedCoproducts.derivedCofan h r) (Iso.refl _) ?_)⟩
    intro n
    change representedMap h (r.inclusion n) ≫ 𝟙 _ =
      representedMap h (F.map (U.inj n))
    rw [Category.comp_id, hr]
    rfl
  · intro P f g
    apply RightDGModuleModel.hom_ext
    intro a
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl
  · intro P f
    obtain ⟨_, _, E, _, hE, _⟩ :=
      DG.CoefficientLift.coneComparison.{u,v,w,max w t} (A := A)
    exact ⟨E f, (hE f).1⟩

set_option backward.isDefEq.respectTransparency false in
/-- The compact Hom comparison also applies to sequences in the whole adequate
module category, including filtrations of native semi-free resolutions. -/
theorem nativeCompactTelescope :
    CompactTelescope.NativeCompactTelescope.{u,v,w} := by
  intro k hk A h
  letI := Derived.homotopyCategory A h
  letI := derivedCategoryInstance A h
  apply compactTelescopeAt h (𝟭 (RightDGModule A)) (nativeDerivedTriangulation.{u,v,w} A h)
  · intro X U hU
    exact nativeExistingDerivedCoproduct.{u,v,w,0} h
      (DG.IndexedSums.strictSumOfIsColimit hU)
  · intro P f g
    rfl
  · intro P f
    exact ⟨Iso.refl _, Category.comp_id _⟩

end

end DerivedFormalization.RightDGModule
