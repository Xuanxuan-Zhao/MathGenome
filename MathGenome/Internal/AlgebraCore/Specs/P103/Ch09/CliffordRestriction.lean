import MathGenome.Internal.AlgebraCore.Specs.P103.Ch08.CentralIdempotents

/-! Clifford restriction, paper.tex 2126–2131 and 2142–2151.
Representatives are the upstream simple regular ideals. Their exhaustiveness is
ordinary completeness, and their Hom multiplicities count actual copies by the
upstream multiplicity theorem. No finite-dimensionality assumption on V is added.
-/
noncomputable section
universe u v
namespace P103.Ch09.CliffordRestrictionSpecs
open P103.Ch08
open scoped MonoidAlgebra

variable {G : Type u} [Group G] (A : Subgroup G) [A.Normal]

def conjugation (g : G) : A →* A where
  toFun a := ⟨g⁻¹ * a * g, (inferInstance : A.Normal).conj_mem' a a.property g⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by apply Subtype.ext; simp [mul_assoc]

def conjugate {W : Type*} [AddCommGroup W] [Module ℂ W]
    (g : G) (σ : Representation ℂ A W) : Representation ℂ A W :=
  σ.comp (conjugation A g)

def restriction {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) : Representation ℂ A V := ρ.comp A.subtype

/-- The same complete family, viewed through the upstream intrinsic component interface. -/
abbrev fourierFamily (C : RegularMultiplicitySpecs.Family A) : FourierSpecs.Family.{u,u} A where
  n := C.n
  space i := C.space i
  add _ := inferInstance
  module _ := inferInstance
  representation i := RegularMultiplicitySpecs.idealRepresentation (C.space i)

/-- Sum of all invariant subspaces isomorphic to this simple type, independent
of any decomposition of the restricted representation. -/
def component (C : RegularMultiplicitySpecs.Family A)
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (i : Fin C.n) : Submodule ℂ V :=
  CentralIdempotentSpecs.isotypic (fourierFamily A C) (restriction A ρ) i

def transportType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    (C : RegularMultiplicitySpecs.Family A),
    RegularMultiplicitySpecs.Valid C → RegularMultiplicitySpecs.Exhaustive.{u,u} C →
    ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
      (g : G) (i j : Fin C.n),
      Nonempty ((conjugate A g (RegularMultiplicitySpecs.idealRepresentation (C.space i))).Equiv
        (RegularMultiplicitySpecs.idealRepresentation (C.space j))) →
      (component A C ρ i).map (ρ g) = component A C ρ j

/-- There is an occurring type, and every pair of occurring types is conjugate.
The transport theorem also ensures the orbit contains only occurring types. -/
def orbitType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    (C : RegularMultiplicitySpecs.Family A),
    RegularMultiplicitySpecs.Valid C → RegularMultiplicitySpecs.Exhaustive.{u,u} C →
    ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      Irreducible ℂ G V ρ →
      (∃ i, component A C ρ i ≠ ⊥) ∧
      ∀ i j, component A C ρ i ≠ ⊥ → component A C ρ j ≠ ⊥ →
        ∃ g : G, Nonempty
          ((conjugate A g (RegularMultiplicitySpecs.idealRepresentation (C.space i))).Equiv
            (RegularMultiplicitySpecs.idealRepresentation (C.space j)))

def equalMultiplicityType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    (C : RegularMultiplicitySpecs.Family A),
    RegularMultiplicitySpecs.Valid C → RegularMultiplicitySpecs.Exhaustive.{u,u} C →
    ∀ {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
      Irreducible ℂ G V ρ →
      ∀ i j, component A C ρ i ≠ ⊥ → component A C ρ j ≠ ⊥ →
        RegularMultiplicitySpecs.multiplicity C (restriction A ρ) i =
          RegularMultiplicitySpecs.multiplicity C (restriction A ρ) j

/-- An assumption-free version, supplying the complete family and the actual
semisimple decomposition, as well as the canonical conjugacy orbit. -/
def cliffordType : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (A : Subgroup G) [A.Normal]
    {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V),
    Irreducible ℂ G V ρ →
    ∃ C : RegularMultiplicitySpecs.Family A,
      RegularMultiplicitySpecs.Valid C ∧ RegularMultiplicitySpecs.Exhaustive.{u,u} C ∧
      RegularMultiplicitySpecs.Decomposition C (restriction A ρ)
        (RegularMultiplicitySpecs.multiplicity C (restriction A ρ)) ∧
      (∃ i, component A C ρ i ≠ ⊥) ∧
      (∀ (g : G) (i : Fin C.n), ∃ j : Fin C.n,
        Nonempty ((conjugate A g (RegularMultiplicitySpecs.idealRepresentation (C.space i))).Equiv
          (RegularMultiplicitySpecs.idealRepresentation (C.space j))) ∧
        (component A C ρ i).map (ρ g) = component A C ρ j) ∧
      (∀ i j, component A C ρ i ≠ ⊥ → component A C ρ j ≠ ⊥ →
        (∃ g : G, Nonempty
          ((conjugate A g (RegularMultiplicitySpecs.idealRepresentation (C.space i))).Equiv
            (RegularMultiplicitySpecs.idealRepresentation (C.space j)))) ∧
        RegularMultiplicitySpecs.multiplicity C (restriction A ρ) i =
          RegularMultiplicitySpecs.multiplicity C (restriction A ρ) j)

end P103.Ch09.CliffordRestrictionSpecs
