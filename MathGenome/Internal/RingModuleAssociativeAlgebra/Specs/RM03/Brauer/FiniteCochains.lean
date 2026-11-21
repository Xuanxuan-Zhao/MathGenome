import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Topology.Algebra.MulAction

namespace Specs.RM03.Brauer

universe w

def restrictionQuotient : Prop :=
  ∀ {k S : Type*} [Field k] [Field S] [Algebra k S] [IsSepClosure k S]
    (E : FiniteGaloisIntermediateField k S),
    Topology.IsQuotientMap (AlgEquiv.restrictNormalHom E.toIntermediateField :
      Gal(S/k) →* Gal(E/k))

def finiteCochainRange : Prop :=
  ∀ {k S : Type*} [Field k] [Field S] [Algebra k S] [IsSepClosure k S],
    letI : TopologicalSpace Sˣ := ⊥
    ∀ (r : ℕ) (f : (Fin r → Gal(S/k)) → Sˣ), Continuous f → (Set.range f).Finite

def finiteCochainFactorization : Prop :=
  ∀ {k S : Type*} [Field k] [Field S] [Algebra k S] [IsSepClosure k S],
    letI : TopologicalSpace Sˣ := ⊥
    ∀ (r : ℕ) (f : (Fin r → Gal(S/k)) → Sˣ), Continuous f →
      ∃ (E : FiniteGaloisIntermediateField k S) (fE : (Fin r → Gal(E/k)) → Eˣ),
        ∀ g, Units.map E.toIntermediateField.val.toMonoidHom
          (fE (fun j => AlgEquiv.restrictNormalHom E.toIntermediateField (g j))) = f g

def commonCochainFactorization : Prop :=
  ∀ {k S : Type*} [Field k] [Field S] [Algebra k S] [IsSepClosure k S],
    letI : TopologicalSpace Sˣ := ⊥
    ∀ (ι : Type w) [Finite ι] (r : ι → ℕ)
      (f : ∀ i, (Fin (r i) → Gal(S/k)) → Sˣ),
      (∀ i, Continuous (f i)) →
      ∀ E₀ : FiniteGaloisIntermediateField k S,
        ∃ E : FiniteGaloisIntermediateField k S, E₀ ≤ E ∧
          ∃ fE : ∀ i, (Fin (r i) → Gal(E/k)) → Eˣ,
            ∀ i g, Units.map E.toIntermediateField.val.toMonoidHom
              (fE i (fun j => AlgEquiv.restrictNormalHom E.toIntermediateField (g j))) = f i g

def openUnitStabilizers : Prop :=
  ∀ {k S : Type*} [Field k] [Field S] [Algebra k S] [IsSepClosure k S] (u : Sˣ),
    (∃ E : FiniteGaloisIntermediateField k S,
      (u : S) ∈ E.toIntermediateField ∧
        E.toIntermediateField.fixingSubgroup ≤ MulAction.stabilizer Gal(S/k) u) ∧
    IsOpen (MulAction.stabilizer Gal(S/k) u : Set Gal(S/k))

def continuousUnitAction : Prop :=
  ∀ {k S : Type*} [Field k] [Field S] [Algebra k S] [IsSepClosure k S],
    letI : TopologicalSpace Sˣ := ⊥
    ContinuousSMul Gal(S/k) Sˣ

end Specs.RM03.Brauer
