import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.SemifreeFiltration
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainTensorTransport

/-! Semifree filtrations in a cochain category containing a representative
of the free rank-one module, and their comparison with the diagonal model. -/

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Specs.DerivedFormalization.SemifreeFiltrationTransport

open Cochains (compValue stalkValue shiftValue)
open CochainRingTransport (complexFunctorValue rankOneComparisonValue)
open CochainTensor (isKFlat)

universe u a w

noncomputable section

variable {R : Type u} {A : Type a} [CommRing R] [CommRing A] (e : R ≃+* A)

/-- The shift of the actual represented rank-one stalk. A shift by `s` has
its generator in degree `-s`. -/
abbrev cell (s : ℤ) : compValue.{a} R :=
  (shiftValue R s).obj (CochainTensorTransport.representedUnit e)

/-- The corresponding cell over the representative ring. -/
abbrev diagonalCell (s : ℤ) : compValue.{a} A :=
  (shiftValue A s).obj ((stalkValue A).obj (ModuleCat.of A A))

abbrev stalkSum {I : Type a} (s : I → ℤ) : compValue.{a} R :=
  ∐ fun i => cell e (s i)

/-- The maps into the ambient complex identify the stages with subcomplexes.
The splittings are degreewise module maps. -/
structure Filtration (F : compValue.{a} R) where
  stages : ℕ ⥤ compValue.{a} R
  inclusions : stages ⟶ (Functor.const ℕ).obj F
  injective (n : ℕ) (i : ℤ) : Function.Injective ((inclusions.app n).f i)
  exhaustive (i : ℤ) (x : F.X i) :
    ∃ (n : ℕ) (y : (stages.obj n).X i), (inclusions.app n).f i y = x
  split (n : ℕ) (i : ℤ) :
    ∃ r : (stages.obj (n + 1)).X i ⟶ (stages.obj n).X i,
      (stages.map (homOfLE (Nat.le_succ n))).f i ≫ r = 𝟙 _
  initial :
    ∃ (I : Type a) (s : I → ℤ),
      Nonempty (cokernel (0 : (0 : compValue.{a} R) ⟶ stages.obj 0) ≅ stalkSum e s)
  successive (n : ℕ) :
    ∃ (I : Type a) (s : I → ℤ),
      Nonempty (cokernel (stages.map (homOfLE (Nat.le_succ n))) ≅ stalkSum e s)

/-- A semifree complex at the represented module level. For `[Small.{a} R]`
one can use `CochainRingTransport.shrinkRingEquivValue R` as the representation. -/
def IsSemifree (F : compValue.{a} R) : Prop := Nonempty (Filtration e F)

variable {e}

/-- The union cocone of the chosen original-ring filtration. -/
def Filtration.cocone {F : compValue.{a} R} (P : Filtration e F) : Cocone P.stages where
  pt := F
  ι := P.inclusions

/-- An existing coproduct of cells in the original category can be indexed
at the module level. In the nonzero case the indices are bijective, and in the
zero case the new family is empty. The isomorphism identifies the injections. -/
def reindexCellsType : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] (e : R ≃+* A)
    {I : Type w} (s : I → ℤ) (c : Cofan (fun i => cell e (s i))), IsColimit c →
    ∃ (J : Type a) (k : J → I) (α : stalkSum e (s ∘ k) ≅ c.pt),
      (Nontrivial R → Function.Bijective k) ∧
      (Subsingleton R → IsEmpty J) ∧
      ∀ j, Sigma.ι (fun j' => cell e (s (k j'))) j ≫ α.hom = c.inj (k j)

variable (e)

/-- The equivalence commutes with the cochain shift and identifies the
represented rank-one stalk with the native rank-one stalk. -/
def cellComparison (s : ℤ) :
    (complexFunctorValue e).obj (cell e s) ≅ diagonalCell (A := A) s :=
  ((complexFunctorValue e).commShiftIso s).app (CochainTensorTransport.representedUnit e) ≪≫
    (shiftValue A s).mapIso (rankOneComparisonValue e)

/-- The coproduct comparison induced by the cell comparisons under the exact
ring equivalence. -/
def sumComparison {I : Type a} (s : I → ℤ) :
    (complexFunctorValue e).obj (stalkSum e s) ≅ SemifreeFiltration.stalkSum (R := A) s :=
  preservesColimitIso (complexFunctorValue e) (Discrete.functor (fun i => cell e (s i))) ≪≫
    HasColimit.isoOfNatIso (Discrete.natIso (fun i => cellComparison e (s i.as)))

/-- The coproduct comparison carries each mapped injection to the corresponding
native injection composed with the cell comparison. -/
def sumComparisonType : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] (e : R ≃+* A)
    {I : Type a} (s : I → ℤ) (i : I),
    (complexFunctorValue e).map (Sigma.ι (fun j => cell e (s j)) i) ≫
        (sumComparison e s).hom =
      (cellComparison e (s i)).hom ≫ Sigma.ι (fun j => diagonalCell (A := A) (s j)) i

/-- Comparison of actual cokernels along a stage square. Each presentation by
a coproduct of cells corresponds to a presentation over the other ring using
the same shifts and the same indices. -/
structure QuotientComparison {X Y : compValue.{a} R} {X' Y' : compValue.{a} A}
    (f : X ⟶ Y) (g : X' ⟶ Y') (y : (complexFunctorValue e).obj Y ≅ Y') where
  iso : (complexFunctorValue e).obj (cokernel f) ≅ cokernel g
  projection :
    (complexFunctorValue e).map (cokernel.π f) ≫ iso.hom = y.hom ≫ cokernel.π g
  presentation (I : Type a) (s : I → ℤ) :
    (∀ α : cokernel f ≅ stalkSum e s,
      ∃ β : cokernel g ≅ SemifreeFiltration.stalkSum (R := A) s,
        iso.hom ≫ β.hom = (complexFunctorValue e).map α.hom ≫ (sumComparison e s).hom) ∧
    (∀ β : cokernel g ≅ SemifreeFiltration.stalkSum (R := A) s,
      ∃ α : cokernel f ≅ stalkSum e s,
        iso.hom ≫ β.hom = (complexFunctorValue e).map α.hom ≫ (sumComparison e s).hom)

/-- Comparison of chosen filtrations. The natural isomorphism compares all
stage maps. The inclusion square compares their union cocones. -/
structure FiltrationComparison {F : compValue.{a} R} {G : compValue.{a} A}
    (φ : (complexFunctorValue e).obj F ≅ G)
    (P : Filtration e F) (T : SemifreeFiltration.Filtration G) where
  stages : P.stages ⋙ complexFunctorValue e ≅ T.stages
  inclusions (n : ℕ) :
    (complexFunctorValue e).map (P.inclusions.app n) ≫ φ.hom =
      stages.hom.app n ≫ T.inclusions.app n
  split (n : ℕ) (i : ℤ) :
    let transport := fun (r : (P.stages.obj (n + 1)).X i ⟶ (P.stages.obj n).X i) =>
        (stages.inv.app (n + 1)).f i ≫
          (CochainRingTransport.moduleEquivalenceValue e).functor.map r ≫
          (stages.hom.app n).f i
    Function.Bijective transport ∧
      ∀ r, (P.stages.map (homOfLE (Nat.le_succ n))).f i ≫ r = 𝟙 _ ↔
        (T.stages.map (homOfLE (Nat.le_succ n))).f i ≫ transport r = 𝟙 _
  initial : QuotientComparison e
    (0 : (0 : compValue.{a} R) ⟶ P.stages.obj 0)
    (0 : (0 : compValue.{a} A) ⟶ T.stages.obj 0) (stages.app 0)
  successive (n : ℕ) : QuotientComparison e
    (P.stages.map (homOfLE (Nat.le_succ n)))
    (T.stages.map (homOfLE (Nat.le_succ n))) (stages.app (n + 1))
  originalColimit : IsColimit P.cocone
  diagonalColimit : IsColimit ({ pt := G, ι := T.inclusions } : Cocone T.stages)
  augmentation {X : compValue.{a} R} {Y : compValue.{a} A}
      (p : F ⟶ X) (ψ : (complexFunctorValue e).obj X ≅ Y) (n : ℕ) :
    (complexFunctorValue e).map (P.inclusions.app n ≫ p) ≫ ψ.hom =
      stages.hom.app n ≫ T.inclusions.app n ≫
        (φ.inv ≫ (complexFunctorValue e).map p ≫ ψ.hom)

/-- A chosen filtration on either side admits a comparison with a chosen
filtration on the other side. Taking `G` to be the transported ambient gives
the semifreeness equivalence at the fixed module level. -/
def transportFiltrationType : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] (e : R ≃+* A)
    {F : compValue.{a} R} {G : compValue.{a} A}
    (φ : (complexFunctorValue e).obj F ≅ G),
    (∀ P : Filtration e F, ∃ T : SemifreeFiltration.Filtration G,
      Nonempty (FiltrationComparison e φ P T)) ∧
    (∀ T : SemifreeFiltration.Filtration G, ∃ P : Filtration e F,
      Nonempty (FiltrationComparison e φ P T))

/-- A given semifree filtration suffices for K-flatness for the original
signed tensor and all original-ring acyclic complexes at this level. -/
def filtrationIsKFlatType : Prop :=
  ∀ {R : Type u} {A : Type a} [CommRing R] [CommRing A] (e : R ≃+* A)
    {F : compValue.{a} R}, Filtration e F → isKFlat F

/-- The represented filtration and the signed K-flat test agree with the
native definitions when the ring and the module universe are diagonal. -/
def diagonalType : Prop :=
  ∀ {R : Type u} [CommRing R] (F : compValue.{u} R),
    (IsSemifree (RingEquiv.refl R) F ↔ SemifreeFiltration.isSemifreeValue F) ∧
    (isKFlat F ↔ CochainModels.isKFlatValue F)

end

end Specs.DerivedFormalization.SemifreeFiltrationTransport
