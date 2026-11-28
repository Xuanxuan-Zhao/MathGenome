import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Modular.ResidualRoots
import Mathlib.RepresentationTheory.Character

/-! Ordinary and Brauer characters of native left group-algebra modules.
The scalar space of each module is finite dimensional, expressed by `Module.Finite` over its field.
-/

namespace RepTheorySurvey.Modular

universe uG uO uK uM
open scoped BigOperators
open IsLocalRing (ResidueField)

variable {G : Type uG} [Group G]

section RegularClasses

variable {p : ℕ}

/-- The conjugacy classes of `p`-regular elements. -/
abbrev PRegularConjClasses (G : Type uG) [Group G] (p : ℕ) :=
  {c : ConjClasses G // ∃ g : PRegular G p, ConjClasses.mk g.val = c}

/-- The conjugacy class of a `p`-regular element, viewed in the regular subtype. -/
def pRegularConjClass (g : PRegular G p) : PRegularConjClasses G p :=
  ⟨ConjClasses.mk g.val, ⟨g, rfl⟩⟩

theorem isPRegular_iff_of_isConj {g h : G} (hgh : IsConj g h) :
    IsPRegular p g ↔ IsPRegular p h := by
  obtain ⟨a, ha⟩ := hgh
  unfold IsPRegular
  rw [SemiconjBy.orderOf_eq (a : G) ha]

theorem pRegularConjClass_surjective :
    Function.Surjective (pRegularConjClass (G := G) (p := p)) := by
  rintro ⟨c, g, rfl⟩
  exact ⟨g, rfl⟩

end RegularClasses

-- The restricted additive group and monoid instances are definitionally compatible.
set_option backward.isDefEq.respectTransparency false

section Ordinary

variable {K : Type uK} [Field K] (V : Type uM) [AddCommGroup V] [Module (MonoidAlgebra K G) V]

/-- The trace of each group element acting on the restricted scalar space of a left module. -/
noncomputable def ordinaryCharacter
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)] : G → K :=
  (moduleRepresentation K G V).character

/-- The ordinary character descended to conjugacy classes. -/
noncomputable def ordinaryClassCharacter
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)] : ConjClasses G → K :=
  Quotient.lift (s := IsConj.setoid G) (ordinaryCharacter (K := K) V) fun g h hgh => by
    obtain ⟨a, rfl⟩ := isConj_iff.mp (show IsConj g h from hgh)
    exact ((moduleRepresentation K G V).char_conj g a).symm

@[simp]
theorem ordinaryClassCharacter_apply
    [Module.Finite K (RestrictScalars K (MonoidAlgebra K G) V)] (g : G) :
    ordinaryClassCharacter (K := K) V (ConjClasses.mk g) = ordinaryCharacter (K := K) V g :=
  rfl

end Ordinary

private theorem charpoly_representation_conj {F W : Type*} [Field F] [AddCommGroup W]
    [Module F W] [FiniteDimensional F W] (ρ : Representation F G W) (g a : G) :
    (ρ (a * g * a⁻¹)).charpoly = (ρ g).charpoly := by
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)
  have he : e.conj (ρ g) = ρ (a * g * a⁻¹) := by
    simp only [LinearEquiv.conj_apply, map_mul]
    rfl
  rw [← he, LinearEquiv.charpoly_conj]

section Brauer

variable [Finite G] {p : ℕ} {O : Type uO} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type uK} [Field K] [Algebra O K]

local notation "m" => primeToPart G p

variable (S : SplittingSystem G p O K) (M : Type uM)
  [AddCommGroup M] [Module (MonoidAlgebra (ResidueField O) G) M]
  [Module.Finite (ResidueField O)
    (RestrictScalars (ResidueField O) (MonoidAlgebra (ResidueField O) G) M)]

/-- The sum of the integral lifts of the eigenvalues, counted with algebraic multiplicity. -/
noncomputable def brauerCharacter (g : PRegular G p) : O :=
  letI : NeZero m := ⟨(primeToPart_pos G p).ne'⟩
  letI := Fintype.ofFinite (rootsOfUnity m (ResidueField O))
  let f := (moduleRepresentation (ResidueField O) G M g.val).charpoly
  ∑ ζ : rootsOfUnity m (ResidueField O), f.rootMultiplicity ζ.val.val • (residualRootLift S ζ).val.val

theorem brauerCharacter_eq_of_isConj {g h : PRegular G p} (hgh : IsConj g.val h.val) :
    brauerCharacter S M g = brauerCharacter S M h := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hgh
  have hchar : (moduleRepresentation (ResidueField O) G M h.val).charpoly =
      (moduleRepresentation (ResidueField O) G M g.val).charpoly := by
    rw [← ha, charpoly_representation_conj]
  unfold brauerCharacter
  rw [hchar]

/-- The integral Brauer character as a function on `p`-regular conjugacy classes. -/
noncomputable def brauerClassCharacter (c : PRegularConjClasses G p) : O :=
  brauerCharacter S M (Classical.choose c.property)

@[simp]
theorem brauerClassCharacter_apply (g : PRegular G p) :
    brauerClassCharacter S M (pRegularConjClass g) = brauerCharacter S M g :=
  brauerCharacter_eq_of_isConj S M
    (ConjClasses.mk_eq_mk_iff_isConj.mp (Classical.choose_spec (pRegularConjClass g).property))

end Brauer

end RepTheorySurvey.Modular
