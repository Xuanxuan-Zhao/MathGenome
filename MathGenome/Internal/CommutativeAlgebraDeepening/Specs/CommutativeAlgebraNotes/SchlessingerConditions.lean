import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalArtinAlgebras
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.RingTheory.AdicCompletion.Basic

/-! Independent models for the definitions in the setup to Schlessinger's criteria. -/

universe u w z

namespace CommutativeAlgebraNotes

open CategoryTheory LocalArtinAlgebra

/-- A covariant set-valued functor on local Artin algebras taking the base field to
a singleton. The set universe can be any universe containing the algebra universe. -/
structure ArtinFunctorModel (k : Type u) [Field k] where
  toFunctor : LocalArtinAlgebra.{u,u} k ⥤ Type (max u w)
  [point : Unique (toFunctor.obj (fieldModel k))]

attribute [instance] ArtinFunctorModel.point

namespace SchlessingerConditionsSpec

variable {k : Type u} [Field k]

/-- The residue, regarded as the morphism to the base object. -/
def residueHomModel (A : LocalArtinAlgebra.{u,u} k) : Hom A (fieldModel k) :=
  ⟨A.residue, A.localResidue⟩

/-- The set of pairs having the same image in the common target. -/
def CompatiblePairsModel {X Y Z : Type z} (f : X → Z) (g : Y → Z) :=
  { p : X × Y // f p.1 = g p.2 }

/-- The projections of the compatible-pair algebra give the comparison for any F. -/
def comparisonModel (F : ArtinFunctorModel.{u,w} k)
    {A₁ A A₂ : LocalArtinAlgebra.{u,u} k} (f : Hom A₁ A) (g : Hom A₂ A) :
    F.toFunctor.obj (pullbackModel f g) →
      CompatiblePairsModel
        ((F.toFunctor.map f) : F.toFunctor.obj A₁ → F.toFunctor.obj A)
        ((F.toFunctor.map g) : F.toFunctor.obj A₂ → F.toFunctor.obj A) := by
  intro x
  refine ⟨⟨F.toFunctor.map (pullbackFstModel f g) x,
    F.toFunctor.map (pullbackSndModel f g) x⟩, ?_⟩
  have h : f.comp (pullbackFstModel f g) = g.comp (pullbackSndModel f g) :=
    Hom.ext (fun p => p.property)
  have hm := congrArg (fun a : Hom (pullbackModel f g) A => F.toFunctor.map a) h
  exact ConcreteCategory.congr_hom
    ((F.toFunctor.map_comp (pullbackFstModel f g) f).symm.trans
      (hm.trans (F.toFunctor.map_comp (pullbackSndModel f g) g))) x

/-- The tangent set of F, before any additive structure is constructed. -/
abbrev TangentModel (F : ArtinFunctorModel.{u,w} k) : Type (max u w) :=
  F.toFunctor.obj (dualModel k)

def H1Model (F : ArtinFunctorModel.{u,w} k) : Prop :=
  ∀ {A₁ A A₂ : LocalArtinAlgebra.{u,u} k} (f : Hom A₁ A) (g : Hom A₂ A),
    SmallExtensionModel g → Function.Surjective (comparisonModel F f g)

def H2Model (F : ArtinFunctorModel.{u,w} k) : Prop :=
  ∀ A₁ : LocalArtinAlgebra.{u,u} k,
    Function.Bijective (comparisonModel F (residueHomModel A₁)
      (residueHomModel (dualModel k)))

def H4Model (F : ArtinFunctorModel.{u,w} k) : Prop :=
  ∀ {A B : LocalArtinAlgebra.{u,u} k} (g : Hom B A),
    SmallExtensionModel g → Function.Bijective (comparisonModel F g g)

end SchlessingerConditionsSpec

/-- A complete Noetherian local algebra with a specified residue field.
The augmentation is local, so it identifies the ordinary residue field with k. -/
structure CompleteLocalAlgebraModel (k : Type u) [Field k] where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra k carrier]
  [localRing : IsLocalRing carrier]
  [noetherianRing : IsNoetherianRing carrier]
  [complete : IsAdicComplete (IsLocalRing.maximalIdeal carrier) carrier]
  residue : carrier →ₐ[k] k
  [localResidue : IsLocalHom residue]

attribute [instance] CompleteLocalAlgebraModel.commRing CompleteLocalAlgebraModel.algebra
  CompleteLocalAlgebraModel.localRing CompleteLocalAlgebraModel.noetherianRing
  CompleteLocalAlgebraModel.complete CompleteLocalAlgebraModel.localResidue

namespace CompleteLocalAlgebra

variable {k : Type u} [Field k]

instance : CoeSort (CompleteLocalAlgebraModel k) (Type u) := ⟨CompleteLocalAlgebraModel.carrier⟩

/-- Local algebra homomorphisms from a complete local base to an Artin algebra. -/
abbrev Hom (R : CompleteLocalAlgebraModel k) (A : LocalArtinAlgebra.{u,u} k) :=
  { f : R →ₐ[k] A // IsLocalHom f }

instance {R : CompleteLocalAlgebraModel k} {A : LocalArtinAlgebra.{u,u} k} :
    CoeFun (Hom R A) (fun _ => R → A) := ⟨fun f => f.val⟩

instance {R : CompleteLocalAlgebraModel k} {A : LocalArtinAlgebra.{u,u} k} (f : Hom R A) :
    IsLocalHom f.val := f.property

@[ext]
theorem Hom.ext {R : CompleteLocalAlgebraModel k} {A : LocalArtinAlgebra.{u,u} k} {f g : Hom R A}
    (h : ∀ r, f r = g r) : f = g :=
  Subtype.ext (AlgHom.ext h)

/-- The specified augmentation has the maximal ideal as its kernel. -/
theorem ker_residue (R : CompleteLocalAlgebraModel k) :
    RingHom.ker R.residue = IsLocalRing.maximalIdeal R := by
  ext a
  rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    ← isUnit_map_iff R.residue a, isUnit_iff_ne_zero, not_not]

/-- Postcomposition by a local map between Artin algebras. -/
def Hom.postcomp {R : CompleteLocalAlgebraModel k} {A B : LocalArtinAlgebra.{u,u} k}
    (f : Hom R A) (g : LocalArtinAlgebra.Hom A B) : Hom R B :=
  ⟨(g : A →ₐ[k] B).comp f.val, ⟨fun r h =>
    IsUnit.of_map f.val r (IsUnit.of_map (g : A →ₐ[k] B) (f r) h)⟩⟩

end CompleteLocalAlgebra

namespace SchlessingerConditionsSpec

variable {k : Type u} [Field k]

/-- h_R on the Artin category, acting by postcomposition. -/
def homFunctorModel (R : CompleteLocalAlgebraModel k) :
    LocalArtinAlgebra.{u,u} k ⥤ Type u where
  obj A := CompleteLocalAlgebra.Hom R A
  map g := TypeCat.ofHom (fun f => f.postcomp g)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro f
    exact CompleteLocalAlgebra.Hom.ext (fun _ => rfl)
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro f
    exact CompleteLocalAlgebra.Hom.ext (fun _ => rfl)

private abbrev homToFieldUnique (R : CompleteLocalAlgebraModel k) :
    Unique (CompleteLocalAlgebra.Hom R (fieldModel k)) where
  default := ⟨R.residue, R.localResidue⟩
  uniq f := by
    apply CompleteLocalAlgebra.Hom.ext
    intro r
    change f.val r = R.residue r
    let : IsLocalHom f.val := f.property
    have hker : RingHom.ker f.val = IsLocalRing.maximalIdeal R := by
      ext a
      rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        ← isUnit_map_iff f.val a]
      simp [isUnit_iff_ne_zero]
    have hr : r - algebraMap k R (R.residue r) ∈ RingHom.ker f.val := by
      rw [hker, ← (CompleteLocalAlgebra.ker_residue R), RingHom.mem_ker, map_sub, AlgHom.commutes,
        Algebra.algebraMap_self_apply, sub_self]
    simpa only [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply,
      sub_eq_zero] using hr

/-- h_R with the singleton at k exhibited and with its values lifted to the set universe. -/
def representableModel (R : CompleteLocalAlgebraModel k) : ArtinFunctorModel.{u,w} k where
  toFunctor := homFunctorModel R ⋙ CategoryTheory.uliftFunctor.{w,u}
  point :=
    { default := ⟨(homToFieldUnique R).default⟩
      uniq := fun x => congrArg ULift.up ((homToFieldUnique R).uniq x.down) }

/-- The map governing lifting over a morphism B → A. -/
def liftingMapModel {R : CompleteLocalAlgebraModel k} {F : ArtinFunctorModel.{u,w} k}
    (τ : (representableModel R).toFunctor ⟶ F.toFunctor)
    {A B : LocalArtinAlgebra.{u,u} k} (g : Hom B A) :
    (representableModel R).toFunctor.obj B →
      CompatiblePairsModel
        ((τ.app A) : (representableModel R).toFunctor.obj A → F.toFunctor.obj A)
        ((F.toFunctor.map g) : F.toFunctor.obj B → F.toFunctor.obj A) :=
  fun b => ⟨⟨(representableModel R).toFunctor.map g b, τ.app B b⟩,
    ConcreteCategory.congr_hom (τ.naturality g) b⟩

/-- Smoothness on small extensions, as used in the definition of a hull. -/
def SmoothModel {R : CompleteLocalAlgebraModel k} {F : ArtinFunctorModel.{u,w} k}
    (τ : (representableModel R).toFunctor ⟶ F.toFunctor) : Prop :=
  ∀ {A B : LocalArtinAlgebra.{u,u} k} (g : Hom B A),
    SmallExtensionModel g → Function.Surjective (liftingMapModel τ g)

/-- A hull consists of a complete local base and a smooth natural transformation
inducing a bijection on tangent sets. -/
structure HullModel (F : ArtinFunctorModel.{u,w} k) where
  ring : CompleteLocalAlgebraModel k
  transformation : (representableModel ring).toFunctor ⟶ F.toFunctor
  tangent_bijective : Function.Bijective
    ((transformation.app (dualModel k)) : TangentModel (representableModel ring) → TangentModel F)
  smooth : SmoothModel transformation

/-- Prorepresentability by a complete Noetherian local algebra. -/
def ProrepresentableModel (F : ArtinFunctorModel.{u,w} k) : Prop :=
  ∃ R : CompleteLocalAlgebraModel k,
    Nonempty ((representableModel R).toFunctor ≅ F.toFunctor)

private abbrev truncationIdeal (R : CompleteLocalAlgebraModel k) (n : ℕ) : Ideal R :=
  IsLocalRing.maximalIdeal R ^ (n + 1)

private theorem truncationIdeal_le (R : CompleteLocalAlgebraModel k) (n : ℕ) :
    truncationIdeal R n ≤ IsLocalRing.maximalIdeal R :=
  Ideal.pow_le_self (Nat.succ_ne_zero n)

/-- The Artin quotient R / m^(n+1), indexed starting at the residue field. -/
def truncationModel (R : CompleteLocalAlgebraModel k) (n : ℕ) : LocalArtinAlgebra.{u,u} k := by
  let I := truncationIdeal R n
  have hn : I ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (truncationIdeal_le R n)
  letI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hn
  let q : R →+* R ⧸ I := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  letI : IsLocalRing (R ⧸ I) := IsLocalRing.of_surjective' q hq
  letI : IsArtinianRing (R ⧸ I) := (isArtinianRing_iff_isNilpotent_maximalIdeal _).mpr <| by
    refine ⟨n + 1, ?_⟩
    rw [← IsLocalRing.map_maximalIdeal_of_surjective q hq, ← Ideal.map_pow,
      Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker]
    exact (Ideal.mk_ker (I := I)).ge
  have hI : I ≤ RingHom.ker R.residue := (CompleteLocalAlgebra.ker_residue R).symm ▸ truncationIdeal_le R n
  let ρ := Ideal.Quotient.liftₐ I R.residue hI
  refine { carrier := R ⧸ I, residue := ρ, localResidue := ⟨?_⟩ }
  intro a ha
  obtain ⟨r, rfl⟩ := hq a
  exact (IsUnit.of_map R.residue r ha).map q

/-- The quotient map from R to its positive-power Artin quotient. -/
def toTruncationModel (R : CompleteLocalAlgebraModel k) (n : ℕ) :
    CompleteLocalAlgebra.Hom R (truncationModel R n) := by
  haveI : Nontrivial (truncationModel R n) := inferInstance
  let f : R →ₐ[k] truncationModel R n := Ideal.Quotient.mkₐ k _
  have hf : Function.Surjective f := Ideal.Quotient.mkₐ_surjective k _
  exact ⟨f, ⟨(IsLocalHom.of_surjective f.toRingHom hf).map_nonunit⟩⟩

/-- The transition R / m^(n+1) → R / m^(m+1) for m ≤ n. -/
def truncationMapModel (R : CompleteLocalAlgebraModel k) {m n : ℕ} (h : m ≤ n) :
    Hom (truncationModel R n) (truncationModel R m) := by
  have hI : truncationIdeal R n ≤ truncationIdeal R m := Ideal.pow_le_pow_right (Nat.succ_le_succ h)
  haveI : Nontrivial (truncationModel R m) := inferInstance
  let f : truncationModel R n →ₐ[k] truncationModel R m := Ideal.Quotient.factorₐ k hI
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hI
  exact ⟨f, ⟨(IsLocalHom.of_surjective f.toRingHom hf).map_nonunit⟩⟩

/-- The compatible formal elements used to describe natural transformations from h_R. -/
def CompatibleFamilyModel (R : CompleteLocalAlgebraModel k) (F : ArtinFunctorModel.{u,w} k) :=
  { x : ∀ n : ℕ, F.toFunctor.obj (truncationModel R n) //
    ∀ (m n : ℕ) (h : m ≤ n), F.toFunctor.map (truncationMapModel R h) (x n) = x m }

/-! The following types are the independent bindings of the public interface. -/

section Signatures

-- These signatures intentionally take the maximum of their input universes.
set_option linter.checkUnivs false

abbrev artinFunctorValue (k : Type u) [Field k] := ArtinFunctorModel.{u,w} k

abbrev completeLocalAlgebraValue (k : Type u) [Field k] := CompleteLocalAlgebraModel k

abbrev hullValue (F : ArtinFunctorModel.{u,w} k) := HullModel F

def ArtinFunctorType :=
  ∀ (k : Type u) [Field k], Type (max (u + 1) (w + 1))

def CompleteLocalAlgebraType :=
  ∀ (k : Type u) [Field k], Type (u + 1)

def ResidueHomType := ∀ {k : Type u} [Field k] (A : LocalArtinAlgebra.{u,u} k),
  Hom A (fieldModel k)

def CompatiblePairsType := ∀ {X Y Z : Type z}, (X → Z) → (Y → Z) → Type z

def ComparisonType := ∀ {k : Type u} [Field k] (F : ArtinFunctorModel.{u,w} k)
    {A₁ A A₂ : LocalArtinAlgebra.{u,u} k} (f : Hom A₁ A) (g : Hom A₂ A),
    F.toFunctor.obj (pullbackModel f g) →
      CompatiblePairsModel
        ((F.toFunctor.map f) : F.toFunctor.obj A₁ → F.toFunctor.obj A)
        ((F.toFunctor.map g) : F.toFunctor.obj A₂ → F.toFunctor.obj A)

def TangentType :=
  ∀ {k : Type u} [Field k], ArtinFunctorModel.{u,w} k → Type (max u w)

def ConditionType :=
  ∀ {k : Type u} [Field k], ArtinFunctorModel.{u,w} k → Prop

def HomFunctorType := ∀ {k : Type u} [Field k],
  CompleteLocalAlgebraModel k → (LocalArtinAlgebra.{u,u} k ⥤ Type u)

def RepresentableType := ∀ {k : Type u} [Field k],
  CompleteLocalAlgebraModel k → ArtinFunctorModel.{u,w} k

def LiftingMapType := ∀ {k : Type u} [Field k] {R : CompleteLocalAlgebraModel k}
    {F : ArtinFunctorModel.{u,w} k}
    (τ : (representableModel.{u,w} R).toFunctor ⟶ F.toFunctor)
    {A B : LocalArtinAlgebra.{u,u} k} (g : Hom B A),
    (representableModel.{u,w} R).toFunctor.obj B →
      CompatiblePairsModel
        ((τ.app A) : (representableModel.{u,w} R).toFunctor.obj A → F.toFunctor.obj A)
        ((F.toFunctor.map g) : F.toFunctor.obj B → F.toFunctor.obj A)

def SmoothType := ∀ {k : Type u} [Field k] {R : CompleteLocalAlgebraModel k}
    {F : ArtinFunctorModel.{u,w} k}, ((representableModel.{u,w} R).toFunctor ⟶ F.toFunctor) → Prop

def HullType :=
  ∀ {k : Type u} [Field k], ArtinFunctorModel.{u,w} k → Type (max (u + 1) w)

def TruncationType :=
  ∀ {k : Type u} [Field k], CompleteLocalAlgebraModel k → ℕ → LocalArtinAlgebra.{u,u} k

def ToTruncationType := ∀ {k : Type u} [Field k] (R : CompleteLocalAlgebraModel k) (n : ℕ),
  CompleteLocalAlgebra.Hom R (truncationModel R n)

def TruncationMapType := ∀ {k : Type u} [Field k] (R : CompleteLocalAlgebraModel k) {m n : ℕ},
  m ≤ n → Hom (truncationModel R n) (truncationModel R m)

def CompatibleFamilyType := ∀ {k : Type u} [Field k],
  CompleteLocalAlgebraModel k → ArtinFunctorModel.{u,w} k → Type (max u w)

def TruncationSurjective : Prop :=
  ∀ {k : Type u} [Field k] (R : CompleteLocalAlgebraModel k) (n : ℕ),
    Function.Surjective (toTruncationModel R n)

def TruncationKernel : Prop :=
  ∀ {k : Type u} [Field k] (R : CompleteLocalAlgebraModel k) (n : ℕ),
    RingHom.ker (toTruncationModel R n).val = IsLocalRing.maximalIdeal R ^ (n + 1)

def ToTruncationComp : Prop :=
  ∀ {k : Type u} [Field k] (R : CompleteLocalAlgebraModel k) {m n : ℕ} (h : m ≤ n),
    (toTruncationModel R n).postcomp (truncationMapModel R h) = toTruncationModel R m

end Signatures

end SchlessingerConditionsSpec
end CommutativeAlgebraNotes
