import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.AffineGroups
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.NonabelianCohomology
import Mathlib.CategoryTheory.Endomorphism

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Coalgebra
open scoped TensorProduct

namespace LinearAlgebraicGroups.Descent.Forms

open NonabelianCohomology

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Automorphisms of the extended coordinate Hopf algebra represent group-scheme
automorphisms by inverse pullback, which preserves composition order. -/
abbrev Coefficients (K : Type u) [Field K] [Algebra k K] (A : HopfAlgebraCategory k) :=
  Aut (extendedHopf K A)

local instance coefficientTopology (A : HopfAlgebraCategory k) :
    TopologicalSpace (Coefficients K A) := ⊥

local instance coefficientDiscrete (A : HopfAlgebraCategory k) :
    DiscreteTopology (Coefficients K A) := ⟨rfl⟩

/-- Finite-type coordinate Hopf algebras admitting a trivialization over the extension. -/
def Models (K : Type u) [Field K] [Algebra k K] (A : HopfAlgebraCategory k) :=
  {B : HopfAlgebraCategory k // Algebra.FiniteType k B ∧
    Nonempty (extendedHopf K A ≅ extendedHopf K B)}

def modelSetoid (K : Type u) [Field K] [Algebra k K] (A : HopfAlgebraCategory k) :
    Setoid (Models K A) where
  r B C := Nonempty (B.val ≅ C.val)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- Forms up to base-field isomorphism. -/
abbrev FormClasses (K : Type u) [Field K] [Algebra k K] (A : HopfAlgebraCategory k) :=
  Quotient (modelSetoid K A)

def standardModel (A : HopfAlgebraCategory k) (hA : Algebra.FiniteType k A) : Models K A :=
  ⟨A, hA, ⟨Iso.refl _⟩⟩

/-- The coefficient action is conjugation by the standard semilinear action. -/
def IsStandardAction {A : HopfAlgebraCategory k}
    (ρ : Gal(K/k) →* MulAut (Coefficients K A)) : Prop :=
  ∀ (σ : Gal(K/k)) (b : Coefficients K A) (x : extendedHopf K A),
    (ρ σ b).asIso.hom.hom ((SemilinearAction.scalarExtension (K := K) A).act σ x) =
      (SemilinearAction.scalarExtension (K := K) A).act σ (b.asIso.hom.hom x)

/-- The transported action is the given cocycle times the standard datum. -/
def IsTransportedCocycle {A B : HopfAlgebraCategory k}
    (i : extendedHopf K A ≅ extendedHopf K B)
    {ρ : Gal(K/k) →* MulAut (Coefficients K A)} (a : Cocycle ρ) : Prop :=
  ∀ (σ : Gal(K/k)) (x : extendedHopf K A),
    (a σ).asIso.hom.hom ((SemilinearAction.scalarExtension (K := K) A).act σ x) =
      i.inv.hom ((SemilinearAction.scalarExtension (K := K) B).act σ (i.hom.hom x))

/-- The pointed classification, characterized on each choice of trivialization
and realizing every specified cocycle by a form with a trivialization. -/
def Classifies (K : Type u) [Field K] [Algebra k K] (A : HopfAlgebraCategory k)
    (hA : Algebra.FiniteType k A) : Prop :=
  ∃ (ρ : Gal(K/k) →* MulAut (Coefficients K A)) (e : FormClasses K A ≃ H1 ρ),
    IsStandardAction ρ ∧
    Continuous (fun p : Gal(K/k) × Coefficients K A => ρ p.1 p.2) ∧
    e (Quotient.mk _ (standardModel A hA)) = basepoint ρ ∧
    (∀ (B : Models K A) (i : extendedHopf K A ≅ extendedHopf K B.val),
      ∃ a : Cocycle ρ, IsTransportedCocycle i a ∧ e (Quotient.mk _ B) = classOf a) ∧
    (∀ a : Cocycle ρ, ∃ (B : Models K A) (i : extendedHopf K A ≅ extendedHopf K B.val),
      IsTransportedCocycle i a)

section Tower

variable {L S : Type u} [Field L] [Field S] [Algebra k L] [Algebra k S]
  [Algebra L S] [IsScalarTower k L S]

/-- Successive scalar extensions agree with scalar extension to the top field. -/
noncomputable def scalarTowerIso (P : HopfAlgebraCategory k) :
    extendedHopf S (extendedHopf L P) ≅ extendedHopf S P := by
  let e := (Algebra.TensorProduct.cancelBaseChange k L S S P).symm
  refine (CommHopfAlgCat.isoMk (BialgEquiv.ofAlgEquiv e ?_ ?_)).symm
  · apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    change counit (R := S) ((1 : S) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] x)) =
      counit (R := S) ((1 : S) ⊗ₜ[k] x)
    simp [Algebra.smul_def, IsScalarTower.algebraMap_apply k L S]
  · apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro x
    change Algebra.TensorProduct.map e.toAlgHom e.toAlgHom
      (comul (R := S) ((1 : S) ⊗ₜ[k] x)) =
      comul (R := S) ((1 : S) ⊗ₜ[L] ((1 : L) ⊗ₜ[k] x))
    simp only [TensorProduct.comul_tmul, Bialgebra.comul_one, Algebra.TensorProduct.one_def]
    generalize comul (R := k) x = t
    induction t using TensorProduct.inductionOn with
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | tmul a b => rfl

/-- Scalar extension of a Hopf isomorphism in a tower, under the canonical comparisons. -/
noncomputable def raiseIso {P Q : HopfAlgebraCategory k}
    (i : extendedHopf L P ≅ extendedHopf L Q) :
    extendedHopf S P ≅ extendedHopf S Q := by
  let j : extendedHopf S (extendedHopf L P) ≅ extendedHopf S (extendedHopf L Q) :=
    { hom := extendedHopfMap S i.hom
      inv := extendedHopfMap S i.inv
      hom_inv_id := by
        apply CommHopfAlgCat.hom_ext
        apply BialgHom.ext
        intro x
        change (extendedHopfMap S i.inv).hom ((extendedHopfMap S i.hom).hom x) = x
        induction x using TensorProduct.inductionOn with
        | add a b ha hb => simp only [map_add, ha, hb]
        | tmul r x =>
          exact congrArg (fun y : extendedHopf L P => r ⊗ₜ[L] y)
            (ConcreteCategory.congr_hom i.hom_inv_id x)
      inv_hom_id := by
        apply CommHopfAlgCat.hom_ext
        apply BialgHom.ext
        intro x
        change (extendedHopfMap S i.hom).hom ((extendedHopfMap S i.inv).hom x) = x
        induction x using TensorProduct.inductionOn with
        | add a b ha hb => simp only [map_add, ha, hb]
        | tmul r x =>
          exact congrArg (fun y : extendedHopf L Q => r ⊗ₜ[L] y)
            (ConcreteCategory.congr_hom i.inv_hom_id x) }
  exact (scalarTowerIso P).symm.trans (j.trans (scalarTowerIso Q))

end Tower

section Relabel

variable {Γ M N : Type*} [Group Γ] [Group M] [Group N]

/-- Transport an action through a specified isomorphism of coefficient groups. -/
def relabelAction (c : M ≃* N) (ρ : Γ →* MulAut M) : Γ →* MulAut N where
  toFun σ := c.symm.trans ((ρ σ).trans c)
  map_one' := by
    apply MulEquiv.ext
    intro x
    change c (ρ 1 (c.symm x)) = x
    rw [map_one]
    exact c.apply_symm_apply x
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro x
    change c (ρ (σ * τ) (c.symm x)) = c (ρ σ (c.symm (c (ρ τ (c.symm x)))))
    rw [c.symm_apply_apply, map_mul]
    rfl

variable [TopologicalSpace Γ] [TopologicalSpace M] [TopologicalSpace N] [DiscreteTopology M]

/-- Transport the values of a continuous cocycle along a coefficient isomorphism. -/
def relabelCocycle (c : M ≃* N) {ρ : Γ →* MulAut M} (a : Cocycle ρ) :
    Cocycle (relabelAction c ρ) :=
  ⟨fun σ => c (a σ), continuous_of_discreteTopology.comp a.property.1, fun σ τ => by
    change c (a (σ * τ)) = c (a σ) * c (ρ σ (c.symm (c (a τ))))
    rw [c.symm_apply_apply, a.property.2, map_mul]⟩

end Relabel

section Schemes

/-- The group-scheme isomorphism whose inverse pullback is the given Hopf isomorphism. -/
noncomputable def spectrumIso {P Q : HopfAlgebraCategory k} (i : P ≅ Q) :
    specGroup P ≅ specGroup Q :=
  (hopfSpec (CommRingCat.of k)).mapIso i.symm.op

/-- The affine finite-type group scheme associated with a finite-type Hopf algebra. -/
noncomputable abbrev schemeModel (P : HopfAlgebraCategory k) (hP : Algebra.FiniteType k P) :
    Specs.AffineAlgebraicGroup k :=
  (finiteTypeHopfSpec k).obj (Opposite.op (⟨P, hP⟩ : FiniteTypeHopfAlgebraCategory k))

/-- Group-scheme representatives of forms of the specified affine algebraic group. -/
def SchemeModels (K : Type u) [Field K] [Algebra k K] (G : Specs.AffineAlgebraicGroup k) :=
  {H : Specs.AffineAlgebraicGroup k //
    Nonempty ((groupBaseChange k K).obj G.val ≅ (groupBaseChange k K).obj H.val)}

def schemeModelSetoid (K : Type u) [Field K] [Algebra k K] (G : Specs.AffineAlgebraicGroup k) :
    Setoid (SchemeModels K G) where
  r H J := Nonempty (H.val.val ≅ J.val.val)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩⟩

abbrev SchemeFormClasses (K : Type u) [Field K] [Algebra k K]
    (G : Specs.AffineAlgebraicGroup k) := Quotient (schemeModelSetoid K G)

/-- The comparison over the extension field has the canonical projection
to the original affine spectrum. -/
def IsScalarExtensionComparison
    (t : ∀ B : HopfAlgebraCategory k,
      specGroup (extendedHopf K B) ≅ (groupBaseChange k K).obj (specGroup B)) : Prop :=
  ∀ B, (t B).hom.hom.hom.left ≫ pullback.fst (specGroup B).X.hom (fieldSpecMap k K) =
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).toRingHom)

variable (K) in
/-- A coordinate form gives a scheme form via spectrum and scalar extension. -/
noncomputable def realizeSchemeModel {P : HopfAlgebraCategory k}
    {G : Specs.AffineAlgebraicGroup k} (j : specGroup P ≅ G.val)
    (t : ∀ B : HopfAlgebraCategory k,
      specGroup (extendedHopf K B) ≅ (groupBaseChange k K).obj (specGroup B))
    (B : Models K P) : SchemeModels K G :=
  ⟨schemeModel B.val B.property.1, ⟨((t P).trans ((groupBaseChange k K).mapIso j)).symm.trans
    ((spectrumIso (Classical.choice B.property.2)).trans (t B.val))⟩⟩

end Schemes

/-- The classification on actual scheme classes with the actual automorphism group
as coefficients. The coordinate identifications specify both the action and the
cocycle attached to a given trivialization. -/
def SchemeClassifies (K : Type u) [Field K] [Algebra k K]
    (G : Specs.AffineAlgebraicGroup k) : Prop :=
  letI : TopologicalSpace (Aut ((groupBaseChange k K).obj G.val)) := ⊥
  ∃ (P : HopfAlgebraCategory k) (_hP : Algebra.FiniteType k P) (j : specGroup P ≅ G.val)
    (t : ∀ B : HopfAlgebraCategory k,
      specGroup (extendedHopf K B) ≅ (groupBaseChange k K).obj (specGroup B))
    (c : Coefficients K P ≃* Aut ((groupBaseChange k K).obj G.val))
    (ρ : Gal(K/k) →* MulAut (Coefficients K P))
    (e : SchemeFormClasses K G ≃ H1 (relabelAction c ρ)),
    IsScalarExtensionComparison t ∧ IsStandardAction ρ ∧
    (∀ b : Coefficients K P, (c b).asIso =
      ((t P).trans ((groupBaseChange k K).mapIso j)).symm.trans
        ((spectrumIso b.asIso).trans ((t P).trans ((groupBaseChange k K).mapIso j)))) ∧
    Continuous (fun p : Gal(K/k) × Aut ((groupBaseChange k K).obj G.val) =>
      relabelAction c ρ p.1 p.2) ∧
    e (Quotient.mk _ ⟨G, ⟨Iso.refl _⟩⟩) = basepoint (relabelAction c ρ) ∧
    (∀ (B : Models K P) (i : extendedHopf K P ≅ extendedHopf K B.val),
      ∃ a : Cocycle ρ, IsTransportedCocycle i a ∧
        e (Quotient.mk _ (realizeSchemeModel K j t B)) = classOf (relabelCocycle c a)) ∧
    (∀ a : Cocycle (relabelAction c ρ),
      ∃ (B : Models K P) (i : extendedHopf K P ≅ extendedHopf K B.val) (b : Cocycle ρ),
        IsTransportedCocycle i b ∧ relabelCocycle c b = a)

namespace Specification

def Finite : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (A : HopfAlgebraCategory k)
    (hA : Algebra.FiniteType k A), Classifies K A hA

def SeparableClosure : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (A : HopfAlgebraCategory k) (hA : Algebra.FiniteType k A), Classifies S A hA

/-- Both directions of an isomorphism over an algebraic Galois extension
are the scalar extensions of the two directions of one finite-level isomorphism. -/
def FiniteLevelIsomorphisms : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsGalois k S]
    (P Q : HopfAlgebraCategory k) (_ : Algebra.FiniteType k P)
    (_ : Algebra.FiniteType k Q) (L₀ : FiniteGaloisIntermediateField k S)
    (i : extendedHopf S P ≅ extendedHopf S Q),
    ∃ (L : FiniteGaloisIntermediateField k S) (j : extendedHopf L P ≅ extendedHopf L Q),
      L₀ ≤ L ∧ raiseIso j = i

/-- The classification in coordinates uses precisely the original scheme forms,
trivializations and automorphisms, via inverse pullback. -/
def SchemeComparison : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] (G : Specs.AffineAlgebraicGroup k),
    ∃ (P : HopfAlgebraCategory k) (hP : Algebra.FiniteType k P) (j : specGroup P ≅ G.val)
      (t : ∀ B : HopfAlgebraCategory k,
        specGroup (extendedHopf K B) ≅ (groupBaseChange k K).obj (specGroup B))
      (e : FormClasses K P ≃ SchemeFormClasses K G)
      (c : Coefficients K P ≃* Aut ((groupBaseChange k K).obj G.val)),
      IsScalarExtensionComparison t ∧
      e (Quotient.mk _ (standardModel P hP)) =
        Quotient.mk _ ⟨G, ⟨Iso.refl _⟩⟩ ∧
      (∀ B : Models K P, e (Quotient.mk _ B) = Quotient.mk _ (realizeSchemeModel K j t B)) ∧
      (∀ b : Coefficients K P, (c b).asIso =
        ((t P).trans ((groupBaseChange k K).mapIso j)).symm.trans
          ((spectrumIso b.asIso).trans ((t P).trans ((groupBaseChange k K).mapIso j)))) ∧
      (∀ B : Models K P, Function.Bijective (fun i : extendedHopf K P ≅ extendedHopf K B.val =>
        ((t P).trans ((groupBaseChange k K).mapIso j)).symm.trans
          ((spectrumIso i).trans (t B.val))))

def FiniteSchemes : Prop :=
  ∀ {k K : Type u} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (G : Specs.AffineAlgebraicGroup k), SchemeClassifies K G

def SeparableClosureSchemes : Prop :=
  ∀ {k S : Type u} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (G : Specs.AffineAlgebraicGroup k), SchemeClassifies S G

end Specification

end LinearAlgebraicGroups.Descent.Forms
