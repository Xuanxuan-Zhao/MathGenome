import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.Actions
import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.GlobalFunctionsHopf
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

namespace RepTheorySurvey.Invariants.RationalActionComparison

open LinearAlgebraicGroups
open LinearAlgebraicGroups.StandardGroups (generalLinearGroup generalLinearGroupPointsIso)
open GlobalFunctions (Sections evaluate)

noncomputable section

variable {k : Type u} [Field k]

/-- The group of points with values in the base field. -/
abbrev KPoints (G : GroupScheme k) : GrpCat.{u} :=
  ((groupPointsFunctor k).obj G).obj (CommAlgCat.of k k)

/-- Contract a tensor by a linear functional on its coefficient factor. -/
def contract {V C : Type u} [AddCommGroup V] [Module k V] [AddCommGroup C] [Module k C]
    (f : C →ₗ[k] k) : V ⊗[k] C →ₗ[k] V :=
  (TensorProduct.rid k V).toLinearMap.comp (f.lTensor V)

variable {G : GroupScheme k} {V W A : Type u} [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W] [Ring A] [Algebra k A]

/-- Rationality is the finite global-coefficient condition on each orbit map. -/
def HasRegularOrbits (r : Representation k (KPoints G) V) : Prop :=
  ∀ v : V, ∃ (n : ℕ) (f : Fin n → Sections G.X) (w : Fin n → V),
    ∀ g : KPoints G, r g v = ∑ i, evaluate g (f i) • w i

/-- Pull back global functions along a point with values in the base field. -/
abbrev pointEvaluation (H : GlobalFunctions.Specs.GlobalHopf G) (g : KPoints G) :
    H.hopf →ₐ[k] k :=
  evaluate (g : Points G.X (CommAlgCat.of k k))

/-- A point action and a coaction agree by evaluation on vectors. -/
def ActsBy (H : GlobalFunctions.Specs.GlobalHopf G)
    (d : RightComodule k H.hopf V) (r : Representation k (KPoints G) V) : Prop :=
  ∀ (g : KPoints G) (v : V), r g v = contract (pointEvaluation H g).toLinearMap (d.coaction v)

namespace Specs

def SectionsSeparated : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOver k)
    [LocallyOfFiniteType X.hom] [IsReduced X.left],
     Function.Injective (fun f : Sections X => fun g : Points X (CommAlgCat.of k k) => evaluate g f)

def LinearComparison : Prop :=
  ∀ {k V : Type u} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [Smooth G.X.hom]
    (H : GlobalFunctions.Specs.GlobalHopf G) (a : G ⟶ H.spectrum),
    a.hom.hom = GlobalFunctions.unit G.X →
    ∃ e : RightComodule k H.hopf V ≃ {r : Representation k (KPoints G) V // HasRegularOrbits r},
      ∀ d, ActsBy H d (e d).1

def EquivariantMaps : Prop :=
  ∀ {k V W : Type u} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (H : GlobalFunctions.Specs.GlobalHopf G)
    (d : RightComodule k H.hopf V) (e : RightComodule k H.hopf W)
    (r : Representation k (KPoints G) V) (s : Representation k (KPoints G) W)
    (f : V →ₗ[k] W), ActsBy H d r → ActsBy H e s →
    (r.IsIntertwiningMap s f ↔ Invariants.Specs.isComoduleMap d e f)

def StableSubspaces : Prop :=
  ∀ {k V : Type u} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (H : GlobalFunctions.Specs.GlobalHopf G) (d : RightComodule k H.hopf V)
    (r : Representation k (KPoints G) V) (S : Submodule k V), ActsBy H d r →
    ((∀ (g : KPoints G) (x : S), r g x ∈ S) ↔ d.IsSubcomodule S)

def InvariantSubspaces : Prop :=
  ∀ {k V : Type u} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [Smooth G.X.hom]
    (H : GlobalFunctions.Specs.GlobalHopf G) (d : RightComodule k H.hopf V)
    (r : Representation k (KPoints G) V), ActsBy H d r →
    r.invariants = RationalRepresentations.invariants H.hopf d

def OrbitSpan : Prop :=
  ∀ {k V : Type u} [Field k] [AddCommGroup V] [Module k V] (G : GroupScheme k)
    (r : Representation k (KPoints G) V), HasRegularOrbits r →
    ∀ v : V, ∃ S : Subrepresentation r,
      S.toSubmodule = Submodule.span k (Set.range (fun g : KPoints G ↦ r g v)) ∧
      v ∈ S ∧ FiniteDimensional k S.toSubmodule

def AlgebraComparison : Prop :=
  ∀ {k A : Type u} [Field k] [IsAlgClosed k] [Ring A] [Algebra k A]
    (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [Smooth G.X.hom]
    (H : GlobalFunctions.Specs.GlobalHopf G) (a : G ⟶ H.spectrum),
    a.hom.hom = GlobalFunctions.unit G.X →
    ∃ e : Invariants.Specs.RationalAlgebraAction H.hopf A ≃
        {r : Invariants.Specs.GroupAlgebraAction k (KPoints G) A //
          HasRegularOrbits (Invariants.Specs.groupRepresentation r)},
      ∀ d, ActsBy H (Invariants.Specs.rationalToRightComodule d)
        (Invariants.Specs.groupRepresentation (e d).1) ∧
        Invariants.Specs.groupFixedSubalgebra (e d).1 = Invariants.Specs.rationalFixedSubalgebra d

def FiniteDimensionalComparison : Prop :=
  ∀ {k V ι : Type u} [Field k] [IsAlgClosed k] [AddCommGroup V] [Module k V]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι k V)
    (G : GroupScheme k) [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [Smooth G.X.hom]
    (H : GlobalFunctions.Specs.GlobalHopf G) (a : G ⟶ H.spectrum),
    a.hom.hom = GlobalFunctions.unit G.X →
    ∃ e : (G ⟶ (generalLinearGroup k ι).val) ≃
        {r : Representation k (KPoints G) V // HasRegularOrbits r},
      ∀ (f : G ⟶ (generalLinearGroup k ι).val) (g : KPoints G) (j : ι),
        (e f).1 g (b j) =
          ∑ i, ((generalLinearGroupPointsIso k ι).hom.app (CommAlgCat.of k k)
            (((groupPointsFunctor k).map f).app (CommAlgCat.of k k) g)).val i j • b i

end Specs
end
end RepTheorySurvey.Invariants.RationalActionComparison
