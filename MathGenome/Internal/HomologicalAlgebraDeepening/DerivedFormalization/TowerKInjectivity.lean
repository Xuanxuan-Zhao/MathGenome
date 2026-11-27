import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainModels
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.TowerCohomology

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex.HomComplex
open Specs.DerivedFormalization.TowerExactSequence (transition)

universe u v

noncomputable section

variable {R : Type u} [CommRing R]

/-- Internal Hom with fixed source, acting on the target by postcomposition. -/
private abbrev internalHomTarget (C : Comp.{v} R) : Comp.{v} R ⥤ Comp.{v} R where
  obj B := internalHom C B
  map f := internalHomMap (𝟙 C) f
  map_id B := internalHomMap_id C B
  map_comp f g := by rw [internalHomMap_comp, Category.id_comp]

private lemma internalHomTarget_map_v {C B D : Comp.{v} R} (f : B ⟶ D)
    {q i j : ℤ} (h : i + q = j) (z : Cochain C B q) :
    (((internalHomTarget C).map f).f q z).v i j h = z.v i j h ≫ f.f j := by
  apply ModuleCat.hom_ext
  ext x : 1
  change ((internalHomMap (𝟙 C) f).f q z).v i j h x = (z.v i j h ≫ f.f j) x
  rw [internalHomMap_apply]
  rfl

private abbrev degreeEval (R : Type u) [CommRing R] (j : ℤ) :
    Comp.{v} R ⥤ ModuleCat.{v} R :=
  HomologicalComplex.eval (ModuleCat.{v} R) (.up ℤ) j

private def towerDegreeIsLimit (A : ℕᵒᵖ ⥤ Comp.{v} R) (j : ℤ) :
    IsLimit ((degreeEval R j).mapCone (limit.cone A)) :=
  isLimitOfPreserves (degreeEval R j) (limit.isLimit A)

variable (C : Comp.{v} R) (A : ℕᵒᵖ ⥤ Comp.{v} R)

/-- Evaluating the internal Hom limit cone in degree `q` gives a limit of modules. -/
private def internalHomTowerDegreeIsLimit (q : ℤ) :
    IsLimit ((degreeEval R q).mapCone ((internalHomTarget C).mapCone (limit.cone A))) := by
  let F := (A ⋙ internalHomTarget C) ⋙ degreeEval R q
  let pointCone (s : Cone F) (x : s.pt) (i j : ℤ) (h : i + q = j) :
      Cone (A ⋙ degreeEval R j) :=
    { pt := C.X i
      π :=
        { app := fun n ↦ (s.π.app n x).v i j h
          naturality := by
            intro n m f
            have hn := congrArg (fun k : s.pt ⟶ F.obj m ↦ k x) (s.w f)
            change ((internalHomTarget C).map (A.map f)).f q (s.π.app n x) =
              s.π.app m x at hn
            change 𝟙 _ ≫ (s.π.app m x).v i j h = (s.π.app n x).v i j h ≫ (A.map f).f j
            rw [Category.id_comp]
            exact (Cochain.congr_v hn i j h).symm.trans
              (internalHomTarget_map_v (A.map f) h (s.π.app n x)) } }
  let liftCochain (s : Cone F) (x : s.pt) : Cochain C (limit A) q :=
    Cochain.mk fun i j h ↦ (towerDegreeIsLimit A j).lift (pointCone s x i j h)
  have lift_v_π (s : Cone F) (x : s.pt) (i j : ℤ) (h : i + q = j) (n : ℕᵒᵖ) :
      (liftCochain s x).v i j h ≫ (limit.π A n).f j = (s.π.app n x).v i j h :=
    (towerDegreeIsLimit A j).fac (pointCone s x i j h) n
  let lift (s : Cone F) : s.pt ⟶ (internalHom C (limit A)).X q :=
    ModuleCat.ofHom
      { toFun := liftCochain s
        map_add' := by
          intro x y
          apply Cochain.ext
          intro i j h
          apply (towerDegreeIsLimit A j).hom_ext
          intro n
          change (liftCochain s (x + y)).v i j h ≫ (limit.π A n).f j =
            ((liftCochain s x).v i j h + (liftCochain s y).v i j h) ≫ (limit.π A n).f j
          rw [Preadditive.add_comp, lift_v_π, lift_v_π, lift_v_π, map_add, Cochain.add_v]
        map_smul' := by
          intro r x
          apply Cochain.ext
          intro i j h
          apply (towerDegreeIsLimit A j).hom_ext
          intro n
          change (liftCochain s (r • x)).v i j h ≫ (limit.π A n).f j =
            (r • (liftCochain s x).v i j h) ≫ (limit.π A n).f j
          rw [Linear.smul_comp, lift_v_π, lift_v_π, map_smul, Cochain.smul_v] }
  refine ⟨lift, ?_, ?_⟩
  · intro s n
    apply ModuleCat.hom_ext
    ext x : 1
    apply Cochain.ext
    intro i j h
    change (((internalHomTarget C).map (limit.π A n)).f q (liftCochain s x)).v i j h = _
    rw [internalHomTarget_map_v, lift_v_π]
  · intro s m hm
    apply ModuleCat.hom_ext
    ext x : 1
    apply Cochain.ext
    intro i j h
    apply (towerDegreeIsLimit A j).hom_ext
    intro n
    change (m x).v i j h ≫ (limit.π A n).f j =
      (liftCochain s x).v i j h ≫ (limit.π A n).f j
    have hn := congrArg (fun f : s.pt ⟶ F.obj n ↦ f x) (hm n)
    change ((internalHomTarget C).map (limit.π A n)).f q (m x) = s.π.app n x at hn
    exact ((internalHomTarget_map_v (limit.π A n) h (m x)).symm.trans
      (Cochain.congr_v hn i j h)).trans (lift_v_π s x i j h n).symm

private def internalHomTowerIsLimit :
    IsLimit ((internalHomTarget C).mapCone (limit.cone A)) :=
  HomologicalComplex.isLimitOfEval _ _ (internalHomTowerDegreeIsLimit C A)

private lemma internalHomTower_surjective
    (hs : ∀ (n : ℕ) (i : ℤ), ∃ s : (A.obj (op n)).X i ⟶ (A.obj (op (n + 1))).X i,
      s ≫ (transition A n).f i = 𝟙 _)
    (n : ℕ) (q : ℤ) :
    Function.Surjective ((transition (A ⋙ internalHomTarget C) n).f q) := by
  choose s h using hs n
  intro z
  let w : Cochain C (A.obj (op (n + 1))) q :=
    Cochain.mk fun i j hij ↦ z.v i j hij ≫ s j
  refine ⟨w, ?_⟩
  change ((internalHomTarget C).map (transition A n)).f q w = z
  apply Cochain.ext
  intro i j hij
  rw [internalHomTarget_map_v]
  change (z.v i j hij ≫ s j) ≫ (transition A n).f j = z.v i j hij
  rw [Category.assoc, h, Category.comp_id]

/-- The inverse limit of a degreewise split tower of K-injective complexes is K-injective. -/
theorem towerLimit_isKInjective (R : Type u) [CommRing R] (A : ℕᵒᵖ ⥤ Comp.{v} R)
    (hs : ∀ (n : ℕ) (i : ℤ), ∃ s : (A.obj (op n)).X i ⟶ (A.obj (op (n + 1))).X i,
      s ≫ (transition A n).f i = 𝟙 _)
    (ha : ∀ n : ℕ, IsKInjective (A.obj (op n))) : IsKInjective (limit A) := by
  apply (isKInjective_iff_internalHom_acyclic _).2
  intro C hC
  let B := A ⋙ internalHomTarget C
  have hB : (limit B).Acyclic :=
    towerLimit_acyclic R B (internalHomTower_surjective C A hs)
      (fun n ↦ (isKInjective_iff_internalHom_acyclic _).1 (ha n) C hC)
  let e : internalHom C (limit A) ≅ limit B :=
    (internalHomTowerIsLimit C A).conePointUniqueUpToIso (limit.isLimit B)
  exact fun q ↦ (hB q).of_iso e.symm

end

end DerivedFormalization
