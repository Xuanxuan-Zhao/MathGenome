import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DG.HomComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DG.Derived

open CategoryTheory CochainComplex.HomComplex

universe u v w

namespace DerivedFormalization.RightDGModule

open Specs.DerivedFormalization.DG.Derived (HomotopyCategoryLaws)

noncomputable section

variable {k : Type u} [CommRing k] {A : DGCategory.{u,v,w} k}
variable {M N : RightDGModule A}

/-- Every morphism in the homotopy category is represented by a strict map. -/
theorem homotopyClass_surjective {M N : K A} (g : M ⟶ N) :
    ∃ f : RightDGModule.Hom M N, homotopyClass f = g := by
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ g
  exact ⟨strictMap z, by
    change Specs.DerivedFormalization.DG.Basic.classOf (strictCycle (strictMap z)) = g
    rw [strictCycle_strictMap]
    exact hz⟩

private def componentHomotopy (f g : M ⟶ N) (h : GradedHom M N (-1))
    (hh : Specs.DerivedFormalization.DG.HomComplex.HomotopyEquation f g h) (a : A.Obj) :
    Homotopy (f.app a) (g.app a) := by
  refine (Cochain.equivHomotopy (f.app a) (g.app a)).symm ⟨h.val a, ?_⟩
  ext i x
  simp only [Cochain.add_v, Cochain.ofHom_v, ModuleCat.hom_add, LinearMap.add_apply]
  change (f.app a).f i x =
    GradedHom.app ((homComplex M N).d (-1) 0 h) a i i (add_zero i) x + (g.app a).f i x
  rw [boundary_component]
  exact sub_eq_iff_eq_add.mp (hh a i x)

/-- Homotopic dg module maps induce equal maps in each objectwise cohomology. -/
theorem homologyMap_eq_of_homotopyClass_eq {f g : M ⟶ N}
    (e : homotopyClass f = homotopyClass g) (a : A.Obj) (i : ℤ) :
    HomologicalComplex.homologyMap (f.app a) i =
      HomologicalComplex.homologyMap (g.app a) i := by
  obtain ⟨h, hh⟩ := (homotopyCriterion f g).mp e
  exact (componentHomotopy f g h hh a).homologyMap_eq i

/-- Objectwise quasi-isomorphism is invariant under dg module homotopy. -/
theorem isQuasiIso_iff_of_homotopyClass_eq {f g : M ⟶ N}
    (e : homotopyClass f = homotopyClass g) : IsQuasiIso f ↔ IsQuasiIso g := by
  change (∀ a, QuasiIso (f.app a)) ↔ (∀ a, QuasiIso (g.app a))
  simp only [quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap,
    homologyMap_eq_of_homotopyClass_eq e]

/-- The homotopy classes represented by objectwise quasi-isomorphisms. -/
def quasiIsomorphisms (A : DGCategory.{u,v,w} k) : MorphismProperty (K A) :=
  Specs.DerivedFormalization.DG.Derived.quasiIsomorphisms A

@[simp] theorem quasiIsomorphisms_homotopyClass (f : M ⟶ N) :
    quasiIsomorphisms A (homotopyClass f) ↔ IsQuasiIso f := by
  change (∃ g : M ⟶ N, homotopyClass g = homotopyClass f ∧ IsQuasiIso g) ↔ IsQuasiIso f
  constructor
  · rintro ⟨g, e, hg⟩
    exact (isQuasiIso_iff_of_homotopyClass_eq e).mp hg
  · intro hf
    exact ⟨f, rfl, hf⟩

/-- The native derived category of right dg `A`-modules at the coefficient
universe of `A`. The upstream category instance supplies the default witness
for the category laws of `K(A)`. -/
def D (A : DGCategory.{u,v,w} k)
    (_h : HomotopyCategoryLaws A := by exact ⟨instCategoryK A, rfl⟩) :=
  (quasiIsomorphisms A).Localization
deriving Category

/-- The canonical localization functor from `K(A)` to the native `D(A)`. -/
def Q (A : DGCategory.{u,v,w} k)
    (h : HomotopyCategoryLaws A := by exact ⟨instCategoryK A, rfl⟩) :
    K A ⥤ D A h :=
  (quasiIsomorphisms A).Q

instance Q_isLocalization (A : DGCategory.{u,v,w} k)
    (h : HomotopyCategoryLaws A := by exact ⟨instCategoryK A, rfl⟩) :
    (Q A h).IsLocalization (quasiIsomorphisms A) :=
  inferInstanceAs ((quasiIsomorphisms A).Q.IsLocalization (quasiIsomorphisms A))

end

end DerivedFormalization.RightDGModule
