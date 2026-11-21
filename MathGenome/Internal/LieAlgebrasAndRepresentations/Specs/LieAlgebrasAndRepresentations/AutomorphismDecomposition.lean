import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.CartanConjugacy
import MathGenome.Internal.LieAlgebrasAndRepresentations.Specs.LieAlgebrasAndRepresentations.IntegrableHighestWeightQuotient
import Mathlib.GroupTheory.SemidirectProduct

/-! LA-J01, notes/005, lines 4537–4581. The diagram is indexed by the
entire set of simple roots. Its automorphisms preserve the oriented Cartan
entries, so the definition permits exchange of isomorphic components. -/

noncomputable section
universe u

namespace Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition

open SerreRelations RootForm VermaModules IntegrableHighestWeightQuotient
open MaximalTori

variable (L : Type u) [LieRing L] [LieAlgebra ℂ L]

/-- Complex Lie automorphisms, with multiplication given by composition. -/
def lieAutomorphisms : Subgroup (L ≃ₗ[ℂ] L) where
  carrier := {g | ∀ x y : L, g ⁅x, y⁆ = ⁅g x, g y⁆}
  one_mem' := fun _ _ => rfl
  mul_mem' {g k} hg hk := by
    intro x y
    change g (k ⁅x, y⁆) = ⁅g (k x), g (k y)⁆
    rw [hk, hg]
  inv_mem' {g} hg := by
    intro x y
    apply g.injective
    simpa using (hg (g.symm x) (g.symm y)).symm

abbrev Aut := lieAutomorphisms L

def inner [FiniteDimensional ℂ L] : Subgroup (Aut L) :=
  (CartanConjugacy.innerAutomorphisms_value L).comap (lieAutomorphisms L).subtype

variable {L}

/-- The permutations of the full Dynkin diagram, encoded by its Cartan
matrix with the row indexed by the coroot. -/
def diagramAutomorphisms [FiniteDimensional ℂ L] (H : LieSubalgebra ℂ L) (φ : Direction H) :
    Subgroup (Equiv.Perm (simple H φ)) where
  carrier := {p | ∀ i j : simple H φ,
    (p j).val (coroot_value H (p i).val) = j.val (coroot_value H i.val)}
  one_mem' := fun _ _ => rfl
  mul_mem' {p q} hp hq := by
    intro i j
    exact (hp (q i) (q j)).trans (hq i j)
  inv_mem' {p} hp := by
    intro i j
    simpa using (hp (p.symm i) (p.symm j)).symm

/-- A section with the prescribed action on the chosen normalized generators,
whose image is a complement to the subgroup of inner exponentials. -/
def decompositionType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), IsMaximalToral_value H →
    ∀ (φ : Direction H), Regular H φ →
    ∀ (e f : simple H φ → L), Normalized H φ e f →
    (inner L).Normal ∧
    ∃ s : diagramAutomorphisms H φ →* Aut L,
      (∀ p i, (s p).val (e i) = e (p.val i) ∧
        (s p).val (f i) = f (p.val i) ∧
        (s p).val (coroot_value H i.val : L) = (coroot_value H (p.val i).val : L)) ∧
      (∀ p, s p ∈ inner L ↔ p = 1) ∧
      Function.Bijective (fun q : inner L × diagramAutomorphisms H φ => q.1.val * s q.2)

def existsPinningType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∃ (H : LieSubalgebra ℂ L), IsMaximalToral_value H ∧
      ∃ (φ : Direction H), Regular H φ ∧
        ∃ (e f : simple H φ → L), Normalized H φ e f

/-- The inherited inner subgroup is generated inside the Lie automorphism
group by the convergent adjoint exponentials. -/
def innerGeneratedType : Prop :=
  ∀ (L : Type u) [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    inner L = Subgroup.closure
      {g | ∃ x : L, g.val.toLinearMap = CartanConjugacy.exponentialOperator x}

/-- Conjugation by the image of the section acts on the normal subgroup. -/
def diagramAction [FiniteDimensional ℂ L] {H : LieSubalgebra ℂ L} {φ : Direction H}
    (hn : (inner L).Normal) (s : diagramAutomorphisms H φ →* Aut L) :
    diagramAutomorphisms H φ →* MulAut (inner L) := by
  letI := hn
  let lift : Aut L →* Subgroup.normalizer (inner L : Set (Aut L)) :=
    { toFun := fun g => ⟨g, by rw [(inner L).normalizer_eq_top]; trivial⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact (inner L).normalizerMonoidHom.comp (lift.comp s)

/-- The external semidirect product with its actual conjugation action and its
multiplication map onto the Lie automorphism group. -/
def semidirectProductType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), IsMaximalToral_value H →
    ∀ (φ : Direction H), Regular H φ →
    ∀ (e f : simple H φ → L), Normalized H φ e f →
    ∃ (hn : (inner L).Normal) (s : diagramAutomorphisms H φ →* Aut L),
      (∀ p i, (s p).val (e i) = e (p.val i) ∧
        (s p).val (f i) = f (p.val i) ∧
        (s p).val (coroot_value H i.val : L) = (coroot_value H (p.val i).val : L)) ∧
      (∀ p, s p ∈ inner L ↔ p = 1) ∧
      ∃ I : (inner L ⋊[diagramAction hn s] diagramAutomorphisms H φ) ≃* Aut L,
        ∀ x, I x = x.left.val * s x.right

open RealRootSpace in
/-- The Cartan-entry encoding identifies the subgroup with all permutations
preserving edge multiplicities and arrows of the full realized diagram. -/
def diagramEncodingType : Prop :=
  ∀ {L : Type u} [LieRing L] [LieAlgebra ℂ L] [FiniteDimensional ℂ L],
    SolvableRadical.IsSemisimple_value ℂ L →
    ∀ (H : LieSubalgebra ℂ L), IsMaximalToral_value H →
    ∀ (φ : Direction H), Regular H φ →
    ∃ d : Realization H,
      letI := d.normedAddCommGroup
      letI := d.innerProductSpace
      ∃ (v : E H) (_ : LieAlgebrasAndRepresentations.RootRegular (realRoots H) v)
        (b : Module.Basis (simple H φ) ℝ (E H)),
        LieAlgebrasAndRepresentations.IsSimpleBasis (realRoots H) v b ∧
        (∀ i, d.j (b i) = i.val) ∧
        let D := LieAlgebrasAndRepresentations.dynkinDiagram b
        ∀ p : Equiv.Perm (simple H φ),
          p ∈ diagramAutomorphisms H φ ↔
            (∀ i j, D.edges (p i) (p j) = D.edges i j) ∧
            (∀ i j, D.arrow (p i) (p j) ↔ D.arrow i j)

end Specs.LieAlgebrasAndRepresentations.AutomorphismDecomposition
