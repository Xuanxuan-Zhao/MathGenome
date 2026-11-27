import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.EffectiveModuleDescent
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.QuasiIsomorphismDetection
import Mathlib.CategoryTheory.Localization.Predicate

/-! Strict descent for unbounded cochain complexes. -/

open CategoryTheory CategoryTheory.Limits
open scoped DerivedFormalization.Descent

namespace StrictComplexDescentSpec

universe u v w r

noncomputable section

attribute [local instance] StrictModuleDataSpec.category

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

abbrev Complex (R : Type r) [CommRing R] := CochainComplex (ModuleCat.{w} R) ℤ

local notation "cochainShape" => ComplexShape.up ℤ

open StrictModuleDataSpec (Power pair)

instance atPositionPreservesZero {n : ℕ} (i : Fin n) :
    (StrictModuleDataSpec.atPosition.{u,v,w} A B i).PreservesZeroMorphisms :=
  inferInstanceAs (ModuleCat.extendScalars.{v,max u v,max u v w}
    (StrictModuleDataSpec.factor A B i).toRingHom).PreservesZeroMorphisms

instance alongPreservesZero {m n : ℕ} (f : Fin m → Fin n) :
    (StrictModuleDataSpec.along.{u,v,w} A B f).PreservesZeroMorphisms :=
  inferInstanceAs (ModuleCat.extendScalars.{max u v,max u v,max u v w}
    (AmitsurAlgebrasSpec.map (A := A) (B := B) f).toRingHom).PreservesZeroMorphisms

abbrev atPosition {n : ℕ} (i : Fin n) :
    Complex.{max u v w} B ⥤ Complex.{max u v w} (Power A B n) :=
  (StrictModuleDataSpec.atPosition.{u,v,w} A B i).mapHomologicalComplex cochainShape

abbrev Theta (K : Complex.{max u v w} B) :=
  (atPosition.{u,v,w} A B (0 : Fin 2)).obj K ≅ (atPosition.{u,v,w} A B (1 : Fin 2)).obj K

variable {A B}

/-- Pull a comparison of complexes back along multiplication of the two factors. -/
def diagonalTheta {K : Complex.{max u v w} B} (θ : Theta.{u,v,w} A B K) : K ≅ K :=
  let D := ModuleCat.extendScalars.{max u v,v,max u v w} (StrictModuleDataSpec.diagonal A B).toRingHom
  (NatIso.mapHomologicalComplex (StrictModuleDataSpec.diagonalPosition.{u,v,w} A B 0) cochainShape).symm.app K ≪≫
    (D.mapHomologicalComplex cochainShape).mapIso θ ≪≫
    (NatIso.mapHomologicalComplex (StrictModuleDataSpec.diagonalPosition.{u,v,w} A B 1) cochainShape).app K

/-- Pull a comparison of complexes back along the given map of factor positions. -/
def alongTheta {n : ℕ} {K : Complex.{max u v w} B} (f : Fin 2 → Fin n)
    (θ : Theta.{u,v,w} A B K) :
    (atPosition.{u,v,w} A B (f 0)).obj K ≅ (atPosition.{u,v,w} A B (f 1)).obj K :=
  (NatIso.mapHomologicalComplex (StrictModuleDataSpec.alongPosition.{u,v,w} A B f 0) cochainShape).app K ≪≫
    ((StrictModuleDataSpec.along.{u,v,w} A B f).mapHomologicalComplex cochainShape).mapIso θ ≪≫
    (NatIso.mapHomologicalComplex (StrictModuleDataSpec.alongPosition.{u,v,w} A B f 1) cochainShape).symm.app K

variable (A B)

/-- A B-complex with a tensor-position chain isomorphism and its strict identities. -/
structure Datum where
  complex : Complex.{max u v w} B
  theta : Theta.{u,v,w} A B complex
  normalized : (diagonalTheta.{u,v,w} theta).hom = 𝟙 complex
  cocycle : (alongTheta.{u,v,w} (pair 2) theta).hom ≫ (alongTheta.{u,v,w} (pair 0) theta).hom =
    (alongTheta.{u,v,w} (pair 1) theta).hom

variable {A B}

/-- A B-linear chain map intertwining the two tensor-position isomorphisms. -/
@[ext]
structure Hom (K L : Datum.{u,v,w} A B) where
  hom : K.complex ⟶ L.complex
  comm : (atPosition.{u,v,w} A B (0 : Fin 2)).map hom ≫ L.theta.hom =
    K.theta.hom ≫ (atPosition.{u,v,w} A B (1 : Fin 2)).map hom

instance : Category (Datum.{u,v,w} A B) where
  Hom := Hom
  id K := ⟨𝟙 K.complex, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, by
    simp only [Functor.map_comp, Category.assoc]
    rw [g.comm, ← Category.assoc, f.comm, Category.assoc]⟩
  id_comp f := Hom.ext (Category.id_comp f.hom)
  comp_id f := Hom.ext (Category.comp_id f.hom)
  assoc f g h := Hom.ext (Category.assoc f.hom g.hom h.hom)

variable (A B)

/-- Forget the strict comparison and retain the B-complex. -/
def forget : Datum.{u,v,w} A B ⥤ Complex.{max u v w} B where
  obj K := K.complex
  map f := f.hom

/-- Strict module morphisms have the usual zero map of underlying modules. -/
@[instance_reducible]
def moduleDataZero : HasZeroMorphisms (StrictModuleDataSpec.Datum.{u,v,w} A B) where
  zero X Y := ⟨⟨0, by
    rw [(StrictModuleDataSpec.atPosition.{u,v,w} A B (0 : Fin 2)).map_zero,
      (StrictModuleDataSpec.atPosition.{u,v,w} A B (1 : Fin 2)).map_zero,
      zero_comp, comp_zero]⟩⟩
  comp_zero f _ := StrictModuleDataSpec.Hom.ext (comp_zero (f := f.hom))
  zero_comp _ _ _ f := StrictModuleDataSpec.Hom.ext (zero_comp (f := f.hom))

attribute [local instance] moduleDataZero

abbrev Degreewise := CochainComplex (StrictModuleDataSpec.Datum.{u,v,w} A B) ℤ

instance moduleForgetPreservesZero :
    (StrictModuleDataSpec.forget.{u,v,w} (A := A) (B := B)).PreservesZeroMorphisms :=
  ⟨fun _ _ ↦ rfl⟩

instance baseChangePreservesZero (h : EffectiveModuleDescentSpec.Coherence.{u,v,w} A B) :
    (EffectiveModuleDescentSpec.baseChange A B h).PreservesZeroMorphisms :=
  ⟨fun M N ↦ StrictModuleDataSpec.Hom.ext
    (Functor.map_zero (ModuleCat.extendScalars.{u,v,max u v w} (algebraMap A B)) M N)⟩

instance descendPreservesZero :
    (DescentCounitSpec.descend (A := A) (B := B)).PreservesZeroMorphisms :=
  ⟨fun X Y ↦ by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (0 : X.module ⟶ Y.module).hom x.val = 0
    exact LinearMap.zero_apply _⟩

/-- Read the module comparisons as the components of one chain isomorphism. -/
def fromDegreewise : Degreewise.{u,v,w} A B ⥤ Datum.{u,v,w} A B where
  obj X :=
    let K := (StrictModuleDataSpec.forget.{u,v,w} (A := A) (B := B)).mapHomologicalComplex cochainShape
    { complex := K.obj X
      theta := HomologicalComplex.Hom.isoOfComponents
        (C₁ := (atPosition.{u,v,w} A B (0 : Fin 2)).obj (K.obj X))
        (C₂ := (atPosition.{u,v,w} A B (1 : Fin 2)).obj (K.obj X))
        (fun i ↦ (X.X i).theta)
        (fun i j _ ↦ (X.d i j).comm.symm)
      normalized := by
        apply HomologicalComplex.hom_ext
        intro i
        exact (X.X i).normalized
      cocycle := by
        apply HomologicalComplex.hom_ext
        intro i
        exact (X.X i).cocycle }
  map f :=
    ⟨((StrictModuleDataSpec.forget.{u,v,w} (A := A) (B := B)).mapHomologicalComplex cochainShape).map f,
      HomologicalComplex.hom_ext _ _ (fun i ↦ (f.f i).comm)⟩
  map_id _ := Hom.ext rfl
  map_comp _ _ := Hom.ext rfl

private def datumAt (K : Datum.{u,v,w} A B) (i : ℤ) : StrictModuleDataSpec.Datum.{u,v,w} A B where
  module := K.complex.X i
  theta := HomologicalComplex.Hom.isoApp K.theta i
  normalized := by
    have h := congrArg (fun f : K.complex ⟶ K.complex ↦ f.f i) K.normalized
    exact h
  cocycle := by
    let K₀ := (atPosition.{u,v,w} A B (0 : Fin 3)).obj K.complex
    let K₂ := (atPosition.{u,v,w} A B (2 : Fin 3)).obj K.complex
    have h := congrArg (fun f : K₀ ⟶ K₂ ↦ f.f i) K.cocycle
    exact h

/-- Read the chain isomorphism componentwise as strict module data. -/
def toDegreewise : Datum.{u,v,w} A B ⥤ Degreewise.{u,v,w} A B where
  obj K :=
    { X := datumAt A B K
      d i j := ⟨K.complex.d i j, (K.theta.hom.comm i j).symm⟩
      shape i j h := StrictModuleDataSpec.Hom.ext (K.complex.shape i j h)
      d_comp_d' i j k _ _ := StrictModuleDataSpec.Hom.ext (K.complex.d_comp_d i j k) }
  map f :=
    { f i := ⟨f.hom.f i, by
        have h := congrArg (HomologicalComplex.Hom.f · i) f.comm
        exact h⟩
      comm' i j _ := StrictModuleDataSpec.Hom.ext (f.hom.comm i j) }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The degreewise and chain-map presentations give equivalent strict categories. -/
def DegreewisePresentation : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∃ e : Degreewise.{u,v,w} A B ≌ Datum.{u,v,w} A B,
      e.functor = fromDegreewise.{u,v,w} A B ∧ e.inverse = toDegreewise.{u,v,w} A B

/-- Apply the canonical scalar-extension datum in every degree. -/
def baseChange (h : EffectiveModuleDescentSpec.Coherence.{u,v,w} A B) :
    Complex.{max u v w} A ⥤ Datum.{u,v,w} A B :=
  (EffectiveModuleDescentSpec.baseChange A B h).mapHomologicalComplex cochainShape ⋙ fromDegreewise.{u,v,w} A B

/-- Take the module equalizer of strict descent in every degree. -/
def descend : Datum.{u,v,w} A B ⥤ Complex.{max u v w} A :=
  toDegreewise.{u,v,w} A B ⋙ (DescentCounitSpec.descend (A := A) (B := B)).mapHomologicalComplex cochainShape

/-- A quasi-isomorphism of strict data is measured on the underlying B-complex. -/
def quasiIsomorphisms : MorphismProperty (Datum.{u,v,w} A B) :=
  (HomologicalComplex.quasiIso (ModuleCat.{max u v w} B) cochainShape).inverseImage (forget.{u,v,w} A B)

/-- The usual quasi-isomorphisms of unbounded A-complexes. -/
abbrev baseQuasiIsomorphisms (R : Type r) [CommRing R] : MorphismProperty (Complex.{w} R) :=
  HomologicalComplex.quasiIso (ModuleCat.{w} R) cochainShape

/-- Faithfully flat descent of complexes and the equivalence induced on their localizations. -/
def Effective : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B],
    ∃ (h : EffectiveModuleDescentSpec.Coherence.{u,v,w} A B)
      (e : Complex.{max u v w} A ≌ Datum.{u,v,w} A B),
      e.functor = baseChange A B h ∧ e.inverse = descend.{u,v,w} A B ∧
      (quasiIsomorphisms.{u,v,w} A B).inverseImage e.functor = baseQuasiIsomorphisms.{max u v w} A ∧
      ∃ e' : (baseQuasiIsomorphisms.{max u v w} A).Localization ≌
          (quasiIsomorphisms.{u,v,w} A B).Localization,
        Nonempty (e.functor ⋙ (quasiIsomorphisms.{u,v,w} A B).Q ≅
          (baseQuasiIsomorphisms.{max u v w} A).Q ⋙ e'.functor) ∧
        Nonempty (e.inverse ⋙ (baseQuasiIsomorphisms.{max u v w} A).Q ≅
          (quasiIsomorphisms.{u,v,w} A B).Q ⋙ e'.inverse)

end

end StrictComplexDescentSpec
