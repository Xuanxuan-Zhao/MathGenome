import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.ProjectiveSpaces
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ArithmeticProjectiveFiniteness
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Cohomology.ArithmeticCohomologyBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 80000

universe u

namespace LinearAlgebraicGroups.Specs.SpreadProjectiveRightTorsor

noncomputable section

open FlagCohomology (SchemeOverRing)
open ArithmeticProjectiveFiniteness (BaseRing)
open ArithmeticCohomologyBaseChange (changeBase)

abbrev rationalMap {m : ℕ} (hm : m ≠ 0) : BaseRing.{u} m →+* ULift.{u} ℚ :=
  ArithmeticCohomologyBaseChange.rationalMap (m := (m : ℤ)) (by exact_mod_cast hm)

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

abbrev changeBaseGroup (φ : A →+* B) :
    Grp (SchemeOverRing A) ⥤ Grp (SchemeOverRing B) :=
  (changeBase φ).mapGrp

/-- The two projections of the right multiplication overlap are the first
projection and multiplication by the image of the second component. -/
def rightMultiply {G H : Grp (SchemeOverRing A)} (i : H ⟶ G) :
    G.X ⨯ H.X ⟶ G.X :=
  (prod.fst : G.X ⨯ H.X ⟶ G.X) * (prod.snd ≫ i.hom.hom)

/-- A section over a Zariski neighborhood of each point of the quotient. -/
def HasLocalSections {X Y : SchemeOverRing A} (q : X ⟶ Y) : Prop :=
  ∀ y : Y.left, ∃ (U : SchemeOverRing A) (j : U ⟶ Y) (s : U ⟶ X),
    IsOpenImmersion j.left ∧ y ∈ Set.range j.left ∧ s ≫ q = j

private theorem specMap_comp (φ : A →+* B) (ψ : B →+* C) :
    Spec.map (CommRingCat.ofHom (ψ.comp φ)) =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

/-- The canonical comparison for two successive changes of the base. -/
def changeBaseComp (φ : A →+* B) (ψ : B →+* C) :
    changeBase (ψ.comp φ) ≅ changeBase φ ⋙ changeBase ψ := by
  let b := Spec.map (CommRingCat.ofHom φ)
  let c := Spec.map (CommRingCat.ofHom ψ)
  let e (X : SchemeOverRing A) : ((changeBase (ψ.comp φ)).obj X).left ≅
      ((changeBase ψ).obj ((changeBase φ).obj X)).left :=
    pullback.congrHom rfl (specMap_comp φ ψ) ≪≫ (pullbackLeftPullbackSndIso X.hom b c).symm
  refine NatIso.ofComponents (fun X => Over.isoMk (e X) (by
    change (e X).hom ≫ pullback.snd (pullback.snd X.hom b) c = _
    simp [e, b, c])) ?_
  intro X Y f
  apply Over.OverMorphism.ext
  change ((changeBase (ψ.comp φ)).map f).left ≫ (e Y).hom =
    (e X).hom ≫ ((changeBase ψ).map ((changeBase φ).map f)).left
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp [e, b, c, Category.assoc, changeBase]
    · simp [e, b, c, Category.assoc, changeBase]
  · simp [e, b, c, Category.assoc, changeBase]

/-- The canonical iterated base change comparison with a prescribed composite ring map. -/
def changeBaseAlongComp (φ : A →+* B) (ψ : B →+* C) {κ : A →+* C}
    (h : ψ.comp φ = κ) : changeBase κ ≅ changeBase φ ⋙ changeBase ψ :=
  eqToIso (congrArg (fun τ => changeBase τ) h.symm) ≪≫ changeBaseComp φ ψ

/-- The reverse comparison uses the inverse of the pullback comparison and
the given identification of the composite ring map. -/
theorem changeBaseAlongComp_inv_app (φ : A →+* B) (ψ : B →+* C) {κ : A →+* C}
    (h : ψ.comp φ = κ) (X : SchemeOverRing A) :
    (changeBaseAlongComp φ ψ h).inv.app X =
      (changeBaseComp φ ψ).inv.app X ≫
        eqToHom (congrArg (fun τ => (changeBase τ).obj X) h) := by
  subst κ
  simp [changeBaseAlongComp]

/-- A rational-fibre isomorphism identifying the two projections on the prescribed base. -/
def RationalFibreComparison (φ : A →+* B) (ψ : B →+* C) {κ : A →+* C}
    (h : ψ.comp φ = κ) {X : SchemeOverRing A} {Y' : SchemeOverRing B} {Y : SchemeOverRing C}
    (p : (changeBase φ).obj X ⟶ Y') (q : (changeBase κ).obj X ⟶ Y) : Prop :=
  ∃ e : Y ≅ (changeBase ψ).obj Y',
    (changeBaseAlongComp φ ψ h).hom.app X ≫ (changeBase ψ).map p = q ≫ e.hom

/-- A projective generic right quotient with local sections spreads to a
projective right quotient with local sections over a single integer localization. -/
def Statement : Prop :=
  ∀ (m : ℕ) (hm : m ≠ 0)
    (G H : Grp (SchemeOverRing (BaseRing.{u} m))) (i : H ⟶ G),
    IsAffine G.X.left → IsAffine H.X.left → Smooth G.X.hom → Smooth H.X.hom →
    IsClosedImmersion i.hom.hom.left →
    ∀ (Y : SchemeOverRing (ULift.{u} ℚ)),
      Smooth Y.hom →
      ∀ (V : Type u) (_ : AddCommGroup V) (_ : Module (ULift.{u} ℚ) V)
        (_ : Module.Finite (ULift.{u} ℚ) V)
        (j : Y ⟶ ProjectiveSpaces.projectiveSpace (ULift.{u} ℚ) V),
        IsClosedImmersion j.left →
        ∀ (q : ((changeBaseGroup (rationalMap hm)).obj G).X ⟶ Y),
          Smooth q.left → Surjective q.left →
          IsPullback prod.fst (rightMultiply ((changeBaseGroup (rationalMap hm)).map i))
            q q →
          HasLocalSections q →
          ∃ (n : ℕ) (hn : n ≠ 0) (_ : m ∣ n)
            (φ : BaseRing.{u} m →+* BaseRing.{u} n)
            (_ : φ.comp (algebraMap (ULift.{u} ℤ) (BaseRing.{u} m)) =
              algebraMap (ULift.{u} ℤ) (BaseRing.{u} n))
            (hφ : (rationalMap hn).comp φ = rationalMap hm)
            (Y' : SchemeOverRing (BaseRing.{u} n)),
            Smooth Y'.hom ∧ Flat Y'.hom ∧
            (∃ (d : ℕ) (j' : Y' ⟶ ArithmeticProjectiveFiniteness.projectiveSpace
              (BaseRing.{u} n) d), IsClosedImmersion j'.left) ∧
            ∃ (q' : ((changeBaseGroup φ).obj G).X ⟶ Y'),
              Smooth q'.left ∧ Surjective q'.left ∧
              IsPullback prod.fst (rightMultiply ((changeBaseGroup φ).map i)) q' q' ∧
              HasLocalSections q' ∧
              RationalFibreComparison φ (rationalMap hn) hφ q' q

end

end LinearAlgebraicGroups.Specs.SpreadProjectiveRightTorsor
