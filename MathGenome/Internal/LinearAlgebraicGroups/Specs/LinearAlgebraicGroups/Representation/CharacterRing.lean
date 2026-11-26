import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.FormalCharacters
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.SimpleClassification
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Representation.DominantOrder
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Basic

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.CharacterRing

open CharacterDescent (Character)
open FormalCharacters (Equivariant formalCharacter tensorRepresentation)
open RootWeightAction (Representation)
open FlagLineBundle (OppositeBorelPair)
open SimpleClassification (SocleModel)
open InducedNonvanishing (Dominant)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus IsUnipotentRadical)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- A finite-dimensional rational representation, presented in a finite basis. -/
structure Rep (G : AffineAlgebraicGroup k) where
  index : Type u
  [finite : Fintype index]
  [decidable : DecidableEq index]
  action : Representation G.val index

attribute [instance] Rep.finite Rep.decidable

def Rep.tensor (V W : Rep G) : Rep G where
  index := V.index × W.index
  action := tensorRepresentation V.action W.action

/-- The one-dimensional trivial rational representation. -/
def Rep.trivial (G : AffineAlgebraicGroup k) : Rep G where
  index := PUnit.{u+1}
  action :=
    { app := fun _ => GrpCat.ofHom 1
      naturality := by
        intro R S f
        apply GrpCat.ext
        intro x
        change 1 = ((StandardGroups.generalLinearPoints k PUnit.{u+1}).map f).hom 1
        exact (map_one (((StandardGroups.generalLinearPoints k PUnit.{u+1}).map f).hom)).symm }

/-- Any exact sequence of finite-dimensional rational modules gives a relation. -/
structure ShortExact (U V W : Rep G) where
  incl : (U.index → k) →ₗ[k] (V.index → k)
  proj : (V.index → k) →ₗ[k] (W.index → k)
  equivIncl : Equivariant U.action V.action incl
  equivProj : Equivariant V.action W.action proj
  injective : Function.Injective incl
  exactness : Function.Exact incl proj
  surjective : Function.Surjective proj

def exactRelations (G : AffineAlgebraicGroup k) : Submodule ℤ (Rep G →₀ ℤ) :=
  Submodule.span ℤ {r | ∃ (U V W : Rep G), Nonempty (ShortExact U V W) ∧
    r = Finsupp.single V 1 - (Finsupp.single U 1 + Finsupp.single W 1)}

/-- The Grothendieck group uses generators for modules and relations for all
short exact sequences. Isomorphic modules give the same generator class by
taking the cokernel of an isomorphism to be zero. -/
abbrev K₀ (G : AffineAlgebraicGroup k) := (Rep G →₀ ℤ) ⧸ exactRelations G

def ofRep (V : Rep G) : K₀ G :=
  (exactRelations G).mkQ (Finsupp.single V 1)

section Invariants

variable {X W : Type*} [CommGroup X] [Group W] (a : W →* MulAut X)

/-- The fixed subring for the Weyl action by permutations of the monomials. -/
def invariantRing : Subring (MonoidAlgebra ℤ X) where
  carrier := {f | ∀ w, MonoidAlgebra.mapDomainRingEquiv ℤ (a w) f = f}
  zero_mem' w := map_zero _
  one_mem' w := map_one _
  add_mem' hf hg w := by rw [map_add, hf w, hg w]
  neg_mem' hf w := by rw [map_neg, hf w]
  mul_mem' hf hg w := by rw [map_mul, hf w, hg w]

/-- An orbit sum counts each distinct character exactly once. -/
def orbitSum [Finite W] (x : X) : MonoidAlgebra ℤ X := by
  classical
  letI := Fintype.ofFinite W
  exact ∑ y ∈ Finset.univ.image (fun w : W => a w x), MonoidAlgebra.single y 1

end Invariants

variable {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X] {D : AbstractPairing.Datum T}

def weylAction (e : DatumAndWeyl.Identification D) :
    D.rootDatum.weylGroup →* MulAut (Character T.group) :=
  e.image.labels.subtype.comp e.labelEquiv.toMonoidHom

abbrev dominantWeights (P : OppositeBorelPair G) := {χ : Character P.torus.group // Dominant P χ}

def simpleRep {P : OppositeBorelPair G} {U : ClosedSubgroup P.positive.group}
    {χ : Character P.torus.group} (S : SocleModel P U χ) : Rep G :=
  ⟨S.J, S.socleAction⟩

/-- The restriction isomorphism and triangular basis theorem for the chosen
split Borel pair. The comparison of weights uses the actual simple roots. -/
def ResultFor (P : OppositeBorelPair G) : Prop :=
  FormalCharacters.CoefficientFormula P.torus ∧
  FormalCharacters.ExactAdditivity P.torus ∧
  FormalCharacters.TensorMultiplicativity P.torus ∧
  ∃ (comm : IsCommMonObj P.torus.group.X), letI := comm
  ∃ (D : AbstractPairing.Datum P.torus) (e : DatumAndWeyl.Identification D)
    (U : ClosedSubgroup P.positive.group),
    IsUnipotentRadical (Unipotent.closedSubgroupAlgebraicGroup P.positive) U ∧
    FormalCharacters.WeylInvariance e ∧
    letI : Finite e.image.labels := e.image.finite
    letI : Finite D.rootDatum.weylGroup := Finite.of_injective e.labelEquiv e.labelEquiv.injective
    let add₀ : Add (K₀ G) := inferInstance
    ∃ (S : ∀ lam : dominantWeights P, SocleModel P U lam.val)
      (orbitBasis : Module.Basis (dominantWeights P) ℤ (invariantRing (weylAction e)))
      (simpleBasis : Module.Basis (dominantWeights P) ℤ (K₀ G)),
      (∀ lam, (orbitBasis lam : MonoidAlgebra ℤ (Character P.torus.group)) =
        orbitSum (weylAction e) lam.val) ∧
      (∀ lam, simpleBasis lam = ofRep (simpleRep (S lam))) ∧
      (∀ lam,
        ∃ c : dominantWeights P →₀ ℤ,
          (∀ mu ∈ c.support, mu ≠ lam ∧
            RootWeightAction.DominanceLE P.torus P.positive mu.val lam.val) ∧
          formalCharacter P.torus (S lam).socleAction =
            orbitSum (weylAction e) lam.val +
              c.sum (fun mu n => n • orbitSum (weylAction e) mu.val)) ∧
      ∃ (ring : CommRing (K₀ G)), letI := ring
        letI : Add (K₀ G) := ⟨ring.add⟩
        (∀ x y : K₀ G, x + y = add₀.add x y) ∧
        (∀ V W : Rep G, ofRep (V.tensor W) = ofRep V * ofRep W) ∧
        ofRep (Rep.trivial G) = 1 ∧
        ∃ restriction : K₀ G ≃+* invariantRing (weylAction e),
          ∀ V : Rep G, (restriction (ofRep V) : MonoidAlgebra ℤ (Character P.torus.group)) =
            formalCharacter P.torus V.action

/-- E09 for any field and any split Borel pair in a connected reductive group.
The opposite Borel used in the induced model is supplied by the conclusion. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsKBorel B → IsSubgroupOf T B →
      ∃ P : OppositeBorelPair G, P.torus = T ∧ P.positive = B ∧ ResultFor P

end

end LinearAlgebraicGroups.Specs.CharacterRing
