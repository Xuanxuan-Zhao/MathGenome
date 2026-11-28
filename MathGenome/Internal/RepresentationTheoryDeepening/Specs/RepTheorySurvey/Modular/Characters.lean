import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Modular.ResidualRoots
import Mathlib.RepresentationTheory.Character

/-! Independent specifications for Definition MR03. -/

namespace RepTheorySurvey.Modular.MR03Spec

universe uG uO uK uM
open scoped BigOperators
open IsLocalRing (ResidueField)

set_option linter.checkUnivs false

/-- The conjugacy classes containing a `p`-regular element. -/
def pRegularConjClassesType := (G : Type uG) → [Group G] → ℕ → Type uG

abbrev pRegularConjClassesValue : pRegularConjClassesType.{uG} :=
  fun G _ p => {c : ConjClasses G //
    ∃ g : MR01Spec.pRegularValue G p, ConjClasses.mk g.val = c}

def pRegularConjClassType :=
  ∀ {G : Type uG} [Group G] {p : ℕ},
    MR01Spec.pRegularValue G p → pRegularConjClassesValue G p

def pRegularConjClassValue : pRegularConjClassType.{uG} :=
  fun g => ⟨ConjClasses.mk g.val, ⟨g, rfl⟩⟩

def isPRegularIffOfIsConj :=
  ∀ {G : Type uG} [Group G] {p : ℕ} {g h : G},
    IsConj g h → ((orderOf g).Coprime p ↔ (orderOf h).Coprime p)

def pRegularConjClassSurjective :=
  ∀ {G : Type uG} [Group G] {p : ℕ},
    Function.Surjective (@pRegularConjClassValue G _ p)

-- The restricted additive group and monoid instances are definitionally compatible.
set_option backward.isDefEq.respectTransparency false

def ordinaryCharacterType :=
  ∀ {G : Type uG} [Group G] {K : Type uK} [Field K]
    (V : Type uM) [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)], G → K

/-- The trace of the action of the given group element on the ordinary module. -/
noncomputable def ordinaryCharacterValue : ordinaryCharacterType.{uG, uK, uM} :=
  fun V => Representation.character (Representation.ofModule V)

def ordinaryClassCharacterType :=
  ∀ {G : Type uG} [Group G] {K : Type uK} [Field K]
    (V : Type uM) [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)], ConjClasses G → K

noncomputable def ordinaryClassCharacterValue : ordinaryClassCharacterType.{uG, uK, uM} :=
  @fun G _ K _ V _ _ _ =>
    Quotient.lift (s := IsConj.setoid G) (ordinaryCharacterValue (K := K) V) fun g h hgh => by
      obtain ⟨a, rfl⟩ := isConj_iff.mp (show IsConj g h from hgh)
      exact ((Representation.ofModule (k := K) V).char_conj g a).symm

def ordinaryClassCharacterApply :=
  ∀ {G : Type uG} [Group G] {K : Type uK} [Field K]
    (V : Type uM) [AddCommGroup V] [Module (MonoidAlgebra K G) V]
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)] (g : G),
    ordinaryClassCharacterValue (K := K) V (ConjClasses.mk g) = ordinaryCharacterValue (K := K) V g

section Brauer

def brauerCharacterType :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K], MR01Spec.SplittingSystemData G p O K →
    ∀ (M : Type uM) [AddCommGroup M] [Module (MonoidAlgebra (ResidueField O) G) M]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) M)],
      MR01Spec.pRegularValue G p → O

/-- Each residual root contributes its lift with its algebraic multiplicity on the module. -/
noncomputable def brauerCharacterValue : brauerCharacterType.{uG, uO, uK, uM} :=
  @fun G _ _ p O _ _ _ _K _ _ S M _ _ _ g =>
    let m := MR01Spec.primeToPartValue G p
    letI : NeZero m := ⟨Nat.ne_of_gt (Nat.ordCompl_pos p (Nat.ne_of_gt Nat.card_pos))⟩
    letI := Fintype.ofFinite (rootsOfUnity m (ResidueField O))
    let f := (Representation.ofModule (k := ResidueField O) M g.val).charpoly
    ∑ ζ : rootsOfUnity m (ResidueField O),
      f.rootMultiplicity ζ.val.val • (MR02RootsSpec.residualRootLiftValue S ζ).val.val

def brauerCharacterEqOfIsConj :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : MR01Spec.SplittingSystemData G p O K),
    ∀ (M : Type uM) [AddCommGroup M] [Module (MonoidAlgebra (ResidueField O) G) M]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) M)]
      {g h : MR01Spec.pRegularValue G p},
      IsConj g.val h.val → brauerCharacterValue S M g = brauerCharacterValue S M h

def brauerClassCharacterType :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K], MR01Spec.SplittingSystemData G p O K →
    ∀ (M : Type uM) [AddCommGroup M] [Module (MonoidAlgebra (ResidueField O) G) M]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) M)],
      pRegularConjClassesValue G p → O

noncomputable def brauerClassCharacterValue : brauerClassCharacterType.{uG, uO, uK, uM} :=
  @fun _ _ _ _ _ _ _ _ _ _ _ S M _ _ _ c =>
    brauerCharacterValue S M (Classical.choose c.property)

def brauerClassCharacterApply :=
  ∀ {G : Type uG} [Group G] [Finite G] {p : ℕ}
    {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {K : Type uK} [Field K] [Algebra O K] (S : MR01Spec.SplittingSystemData G p O K),
    ∀ (M : Type uM) [AddCommGroup M] [Module (MonoidAlgebra (ResidueField O) G) M]
      [Module.Finite (ResidueField O)
        (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) M)]
      (g : MR01Spec.pRegularValue G p),
      brauerClassCharacterValue S M (pRegularConjClassValue g) = brauerCharacterValue S M g

end Brauer

end RepTheorySurvey.Modular.MR03Spec
