import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AutomorphismSequence
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.Forms

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace LinearAlgebraicGroups.Specs.RelativeFormComparison

open AutomorphismSequence
open _root_.LinearAlgebraicGroups.Descent
open _root_.LinearAlgebraicGroups.Descent.Forms
open _root_.LinearAlgebraicGroups.Descent.NonabelianCohomology

noncomputable section

variable (k S : Type u) [Field k] [Field S] [Algebra k S]

/-- The chosen extension field as a test scheme over the ground field. -/
abbrev fieldTest : SchemeOver k := (testSpec k).obj (op (CommAlgCat.of k S))

abbrev fieldMap (σ : Gal(S/k)) : fieldTest k S ⟶ fieldTest k S :=
  (testSpec k).map (CommAlgCat.ofHom σ.toAlgHom).op

theorem fieldMap_one : fieldMap k S 1 = 𝟙 _ := by
  change (testSpec k).map (𝟙 _) = _
  exact (testSpec k).map_id _

theorem fieldMap_mul (σ τ : Gal(S/k)) :
    fieldMap k S (σ * τ) = fieldMap k S σ ≫ fieldMap k S τ :=
  (testSpec k).map_comp (CommAlgCat.ofHom σ.toAlgHom).op
    (CommAlgCat.ofHom τ.toAlgHom).op

/-- Galois acts on sections by restriction along the automorphism of the test scheme. -/
def relativeAction (F : (SchemeOver k)ᵒᵖ ⥤ GrpCat.{v}) :
    Gal(S/k) →* MulAut (F.obj (op (fieldTest k S))) where
  toFun σ :=
    { toFun := (F.map (fieldMap k S σ).op).hom
      invFun := (F.map (fieldMap k S σ⁻¹).op).hom
      left_inv := fun x => by
        have h : F.map (fieldMap k S σ).op ≫ F.map (fieldMap k S σ⁻¹).op = 𝟙 _ := by
          rw [← F.map_comp, ← op_comp, ← fieldMap_mul, inv_mul_cancel, fieldMap_one,
            op_id, F.map_id]
        exact ConcreteCategory.congr_hom h x
      right_inv := fun x => by
        have h : F.map (fieldMap k S σ⁻¹).op ≫ F.map (fieldMap k S σ).op = 𝟙 _ := by
          rw [← F.map_comp, ← op_comp, ← fieldMap_mul, mul_inv_cancel, fieldMap_one,
            op_id, F.map_id]
        exact ConcreteCategory.congr_hom h x
      map_mul' := (F.map (fieldMap k S σ).op).hom.map_mul }
  map_one' := by
    apply MulEquiv.ext
    intro x
    change (F.map (fieldMap k S 1).op).hom x = x
    rw [fieldMap_one, op_id, F.map_id]
    rfl
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    change (F.map (fieldMap k S (σ * τ)).op).hom x =
      (F.map (fieldMap k S σ).op).hom ((F.map (fieldMap k S τ).op).hom x)
    rw [fieldMap_mul, op_comp, F.map_comp]
    rfl

abbrev automorphismAction (G : GroupScheme k) :
    Gal(S/k) →* MulAut (RelativeAut G (fieldTest k S)) := relativeAction k S (automorphisms G)

local instance relativeTopology (G : GroupScheme k) :
    TopologicalSpace (RelativeAut G (fieldTest k S)) := ⊥

local instance hopfTopology (A : HopfAlgebraCategory k) :
    TopologicalSpace (Coefficients S A) := ⊥

/-- The cocycle value determined by a chosen relative trivialization. -/
def transportedAut {G H : GroupScheme k}
    (i : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S))
    (σ : Gal(S/k)) : RelativeAut G (fieldTest k S) :=
  Aut.of (restrictIso (fieldMap k S σ) i ≪≫ i.symm)

/-- A relative isomorphism is induced by an isomorphism of scalar extensions
when its effect on every section is given by the pullback formula. -/
def IsInduced {G H : GroupScheme k}
    (f : (groupBaseChange k S).obj G ≅ (groupBaseChange k S).obj H)
    (i : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S)) : Prop :=
  ∀ (U : Over (fieldTest k S)) (x : U.left ⟶ G.X),
    ((i.hom.app (op U)).hom x).left =
      pullback.lift x.left U.hom.left
        ((Over.w x).trans (Over.w U.hom).symm) ≫ f.hom.hom.hom.left ≫
        pullback.fst H.X.hom (fieldSpecMap k S)

variable {k S}

def SchemeIsomorphismComparison : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] (G H : GroupScheme k),
    ∃ e : ((groupBaseChange k S).obj G ≅ (groupBaseChange k S).obj H) ≃
        (relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S)),
      ∀ f i, IsInduced k S f i ↔ e f = i

/-- Semilinear conjugation of an isomorphism on extended coordinate Hopf algebras. -/
def HopfConjugates {A B : HopfAlgebraCategory k} (σ : Gal(S/k))
    (i i' : extendedHopf S A ≅ extendedHopf S B) : Prop :=
  ∀ x, i'.hom.hom ((SemilinearAction.scalarExtension (K := S) A).act σ x) =
    (SemilinearAction.scalarExtension (K := S) B).act σ (i.hom.hom x)

/-- An extended Hopf isomorphism gives a relative isomorphism by inverse pullback. -/
def IsInducedByHopf {A B : HopfAlgebraCategory k} {G H : GroupScheme k}
    (t : ∀ C : HopfAlgebraCategory k,
      specGroup (extendedHopf S C) ≅ (groupBaseChange k S).obj (specGroup C))
    (g : specGroup A ≅ G) (h : specGroup B ≅ H)
    (i : extendedHopf S A ≅ extendedHopf S B)
    (r : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S)) : Prop :=
  IsInduced k S (((t A ≪≫ (groupBaseChange k S).mapIso g).symm) ≪≫
    spectrumIso i ≪≫ t B ≪≫ (groupBaseChange k S).mapIso h) r

def HopfIsomorphismComparison : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    {A B : HopfAlgebraCategory k} {G H : GroupScheme k}
    (t : ∀ C : HopfAlgebraCategory k,
      specGroup (extendedHopf S C) ≅ (groupBaseChange k S).obj (specGroup C)),
    IsScalarExtensionComparison t →
    ∀ (g : specGroup A ≅ G) (h : specGroup B ≅ H),
      ∃ e : (extendedHopf S A ≅ extendedHopf S B) ≃
          (relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S)),
        (∀ i r, IsInducedByHopf t g h i r ↔ e i = r) ∧
        ∀ σ i i', HopfConjugates σ i i' ↔ restrictIso (fieldMap k S σ) (e i) = e i'

def HopfCocycleComparison : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S]
    {A B : HopfAlgebraCategory k} {G H : GroupScheme k}
    (t : ∀ C : HopfAlgebraCategory k,
      specGroup (extendedHopf S C) ≅ (groupBaseChange k S).obj (specGroup C)),
    IsScalarExtensionComparison t →
    ∀ (g : specGroup A ≅ G) (h : specGroup B ≅ H)
      (i : extendedHopf S A ≅ extendedHopf S B)
      (r : relativePoints G (fieldTest k S) ≅ relativePoints H (fieldTest k S)),
      IsInducedByHopf t g h i r →
      ∀ {ρ : Gal(S/k) →* MulAut (Coefficients S A)} (a : Cocycle ρ),
        IsTransportedCocycle i a →
        ∀ σ, IsInducedByHopf t g g (a σ).asIso (transportedAut k S r σ).asIso

/-- F03 with coefficients evaluated on the chosen separable closure in the
actual automorphism sheaf, including the cocycle of each trivialization. -/
structure RelativeClassification (k S : Type u) [Field k] [Field S] [Algebra k S]
    (G : AffineAlgebraicGroup k) where
  equiv : SchemeFormClasses S G ≃ H1 (automorphismAction k S G.val)
  continuousAction : Continuous (fun p : Gal(S/k) × RelativeAut G.val (fieldTest k S) =>
    automorphismAction k S G.val p.1 p.2)
  pointed : equiv (Quotient.mk _ ⟨G, ⟨Iso.refl _⟩⟩) = basepoint (automorphismAction k S G.val)
  computes : ∀ (H : SchemeModels S G)
    (i : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val.val (fieldTest k S)),
    ∃ a : Cocycle (automorphismAction k S G.val),
      (∀ σ, a σ = transportedAut k S i σ) ∧ equiv (Quotient.mk _ H) = classOf a
  realizes : ∀ a : Cocycle (automorphismAction k S G.val),
    ∃ (H : SchemeModels S G)
      (i : relativePoints G.val (fieldTest k S) ≅ relativePoints H.val.val (fieldTest k S)),
      (∀ σ, a σ = transportedAut k S i σ) ∧ equiv (Quotient.mk _ H) = classOf a

def Classification : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : AffineAlgebraicGroup k), Nonempty (RelativeClassification k S G)

end

end LinearAlgebraicGroups.Specs.RelativeFormComparison
