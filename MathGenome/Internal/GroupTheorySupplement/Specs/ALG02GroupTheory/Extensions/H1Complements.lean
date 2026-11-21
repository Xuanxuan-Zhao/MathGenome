import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Extensions.SectionFactorSystem
import Mathlib.Algebra.Module.ULift
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! Independent specifications for the complement correspondence in paper.tex:438–457. -/

namespace Specs.ALG02GroupTheory.Extensions

universe u v w

variable {A : Type u} {E : Type v} {Q : Type w} [AddCommGroup A] [Group E] [Group Q]
variable (S : GroupExtension (Multiplicative A) E Q)

open Multiplicative (ofAdd toAdd)
open groupCohomology (cocycles₁ H1 H1π)

/-- The left action on the additive kernel induced by conjugation in the extension. -/
noncomputable def kernelAction (q : Q) (a : A) : A :=
  toAdd (abelianActionValue S q (ofAdd a))

/-- Integral coefficients for the induced action. The lifts put the group, the
coefficients, and `ℤ` in the same universe for Mathlib's cohomology. -/
noncomputable def kernelCohomologyRep :
    Rep.{max u w} (ULift.{max u w} ℤ) (ULift.{u} Q) :=
  Rep.of (X := ULift.{w} A)
    { toFun := fun q =>
        { toFun := fun a => ⟨kernelAction S q.down a.down⟩
          map_add' := fun a b => by
            apply ULift.ext
            exact map_mul (abelianActionValue S q.down) (ofAdd a.down) (ofAdd b.down)
          map_smul' := fun n a => by
            apply ULift.ext
            exact map_zsmul (abelianActionValue S q.down).toMonoidHom.toAdditive n.down a.down }
      map_one' := by
        ext a
        change toAdd (abelianActionValue S 1 (ofAdd a.down)) = a.down
        rw [map_one]
        rfl
      map_mul' := fun q r => by
        ext a
        change toAdd (abelianActionValue S (q.down * r.down) (ofAdd a.down)) =
          toAdd (abelianActionValue S q.down (abelianActionValue S r.down (ofAdd a.down)))
        rw [map_mul]
        rfl }

abbrev actualComplements := {H : Subgroup E // isComplementValue S H}

/-- Conjugation of a subgroup by the image of the specified kernel element. -/
def kernelConjugate (a : A) (H : Subgroup E) : Subgroup E :=
  H.map (MulAut.conj (S.inl (ofAdd a))).toMonoidHom

private theorem kernelConjugate_zero (H : Subgroup E) : kernelConjugate S 0 H = H := by
  unfold kernelConjugate
  change H.map (MulAut.conj (S.inl 1)).toMonoidHom = H
  rw [map_one, map_one]
  exact H.map_id

private theorem kernelConjugate_add (a b : A) (H : Subgroup E) :
    kernelConjugate S (a + b) H = kernelConjugate S a (kernelConjugate S b H) := by
  simp only [kernelConjugate, Subgroup.map_map]
  change H.map (MulAut.conj (S.inl (ofAdd a * ofAdd b))).toMonoidHom = _
  rw [map_mul, map_mul]
  rfl

/-- Equivalence by conjugacy by elements of the embedded kernel, on actual subgroups. -/
def complementConjugacySetoid : Setoid (actualComplements S) where
  r H K := ∃ a : A, K.val = kernelConjugate S a H.val
  iseqv :=
    { refl := fun H => ⟨0, (kernelConjugate_zero S H.val).symm⟩
      symm := fun ⟨a, ha⟩ => ⟨-a, by
        rw [ha, ← kernelConjugate_add, neg_add_cancel, kernelConjugate_zero]⟩
      trans := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨b + a, by
        rw [hb, ha, kernelConjugate_add]⟩ }

set_option linter.checkUnivs false in
def ComplementConjugacyClassesType :=
  ∀ {A : Type u} {E : Type v} {Q : Type w} [AddCommGroup A] [Group E] [Group Q],
    GroupExtension (Multiplicative A) E Q → Type v

abbrev ComplementConjugacyClassesValue := Quotient (complementConjugacySetoid S)

/-- The section in the reference coordinates with kernel coordinate `z`. -/
def complementGraph (s₀ : S.Splitting) (z : Q → A) (q : Q) : E :=
  S.inl (ofAdd (z q)) * s₀ q

/-- Write a Mathlib cocycle as a function on the original group with values in the original kernel. -/
def cocycleCoordinate (z : cocycles₁ (kernelCohomologyRep S)) (q : Q) : A :=
  (z (ULift.up q)).down

/-- The graph is a splitting exactly for crossed homomorphisms. -/
def GraphSplittingIff : Prop :=
  ∀ {A : Type u} {E : Type v} {Q : Type w} [AddCommGroup A] [Group E] [Group Q]
    (S : GroupExtension (Multiplicative A) E Q) (s₀ : S.Splitting) (z : Q → A),
    (∃ s : S.Splitting, ∀ q, s q = complementGraph S s₀ z q) ↔
      ∀ q r, z (q * r) = z q + kernelAction S q (z r)

/-- Conjugating a graph by the given kernel element adds the indicated negative coboundary. -/
def GraphConjugacyIff : Prop :=
  ∀ {A : Type u} {E : Type v} {Q : Type w} [AddCommGroup A] [Group E] [Group Q]
    (S : GroupExtension (Multiplicative A) E Q) (s₀ : S.Splitting) (a : A)
    (H K : actualComplements S) (z z' : Q → A),
    (H.val : Set E) = Set.range (complementGraph S s₀ z) →
    (K.val : Set E) = Set.range (complementGraph S s₀ z') →
    (K.val = kernelConjugate S a H.val ↔ ∀ q, z' q = z q + a - kernelAction S q a)

/-- An equivalence that sends each graph to the class of its cocycle and the reference to zero. -/
def ComplementsCorrespondToH1 : Prop :=
  ∀ {A : Type u} {E : Type v} {Q : Type w} [AddCommGroup A] [Group E] [Group Q]
    (S : GroupExtension (Multiplicative A) E Q) (s₀ : S.Splitting),
    ∃ e : ComplementConjugacyClassesValue S ≃ H1 (kernelCohomologyRep S),
      (∀ H : actualComplements S, ∃ z : cocycles₁ (kernelCohomologyRep S),
        (H.val : Set E) = Set.range (complementGraph S s₀ (cocycleCoordinate S z))) ∧
      (∀ z : cocycles₁ (kernelCohomologyRep S), ∃ H : actualComplements S,
        (H.val : Set E) = Set.range (complementGraph S s₀ (cocycleCoordinate S z))) ∧
      (∀ (H : actualComplements S) (z : cocycles₁ (kernelCohomologyRep S)),
        (H.val : Set E) = Set.range (complementGraph S s₀ (cocycleCoordinate S z)) →
        e (Quotient.mk (complementConjugacySetoid S) H) = H1π (kernelCohomologyRep S) z) ∧
      (∃ H : actualComplements S, H.val = s₀.toMonoidHom.range ∧
        e (Quotient.mk (complementConjugacySetoid S) H) = 0)

end Specs.ALG02GroupTheory.Extensions
