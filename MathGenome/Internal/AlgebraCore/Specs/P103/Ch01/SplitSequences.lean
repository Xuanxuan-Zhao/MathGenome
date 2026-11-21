import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.ModuleExactness

/-! Splitting assertions of paper.tex 113–135. A finite direct sum is represented
by the product `A × C`. The two commuting-square equations below express an
isomorphism of sequences whose maps on A and C are identities. Arbitrary unital
rings and zero modules are allowed; right modules use the opposite ring. -/

namespace P103.Specs.Ch01.SplitSequences

def section_iff_retractionType : Prop := ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [Module R A] [Module R B] [Module R C]
  (i : A →ₗ[R] B) (p : B →ₗ[R] C)
  (hi : Function.Injective i) (hp : Function.Surjective p) (h : Function.Exact i p),
  (∃ s : C →ₗ[R] B, p.comp s = LinearMap.id) ↔
    (∃ r : B →ₗ[R] A, r.comp i = LinearMap.id)

def section_iff_sequenceIsomorphismType : Prop := ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [Module R A] [Module R B] [Module R C]
  (i : A →ₗ[R] B) (p : B →ₗ[R] C)
  (hi : Function.Injective i) (hp : Function.Surjective p) (h : Function.Exact i p),
  (∃ s : C →ₗ[R] B, p.comp s = LinearMap.id) ↔
    (∃ e : B ≃ₗ[R] A × C,
      i = e.symm.toLinearMap.comp (LinearMap.inl R A C) ∧
      p = (LinearMap.snd R A C).comp e.toLinearMap)

def splittingType := ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [Module R A] [Module R B] [Module R C]
  (i : A →ₗ[R] B) (p : B →ₗ[R] C)
  (hi : Function.Injective i) (h : Function.Exact i p)
  (s : C →ₗ[R] B) (hs : p.comp s = LinearMap.id), (A × C) ≃ₗ[R] B

noncomputable def splittingValue (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C]
    (i : A →ₗ[R] B) (p : B →ₗ[R] C)
    (hi : Function.Injective i) (h : Function.Exact i p)
    (s : C →ₗ[R] B) (hs : p.comp s = LinearMap.id) : (A × C) ≃ₗ[R] B :=
  (h.splitSurjectiveEquiv hi ⟨s, hs⟩).1.symm

def splitting_applyType : Prop := ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [Module R A] [Module R B] [Module R C]
  (i : A →ₗ[R] B) (p : B →ₗ[R] C)
  (hi : Function.Injective i) (h : Function.Exact i p)
  (s : C →ₗ[R] B) (hs : p.comp s = LinearMap.id) (a : A) (c : C),
  splittingValue R A B C i p hi h s hs (a,c) = i a + s c

def residual_mem_rangeType : Prop := ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [Module R A] [Module R B] [Module R C]
  (i : A →ₗ[R] B) (p : B →ₗ[R] C)
  (h : Function.Exact i p) (s : C →ₗ[R] B) (hs : p.comp s = LinearMap.id) (b : B),
  b - s (p b) ∈ LinearMap.range i

def inverseOnImageType := ∀ (R A B : Type*) [Ring R] [AddCommGroup A]
  [AddCommGroup B] [Module R A] [Module R B]
  (i : A →ₗ[R] B) (hi : Function.Injective i), LinearMap.range i ≃ₗ[R] A

noncomputable def inverseOnImageValue (R A B : Type*) [Ring R] [AddCommGroup A]
    [AddCommGroup B] [Module R A] [Module R B]
    (i : A →ₗ[R] B) (hi : Function.Injective i) : LinearMap.range i ≃ₗ[R] A :=
  (LinearEquiv.ofInjective i hi).symm

def splitting_inverse_formulaType : Prop := ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [Module R A] [Module R B] [Module R C]
  (i : A →ₗ[R] B) (p : B →ₗ[R] C)
  (hi : Function.Injective i) (h : Function.Exact i p)
  (s : C →ₗ[R] B) (hs : p.comp s = LinearMap.id) (b : B)
  (hb : b - s (p b) ∈ LinearMap.range i),
  (splittingValue R A B C i p hi h s hs).symm b =
    (inverseOnImageValue R A B i hi ⟨b - s (p b), hb⟩, p b)

def splitting_mutualInverseType : Prop := ∀ (R A B C : Type*) [Ring R] [AddCommGroup A] [AddCommGroup B]
  [AddCommGroup C] [Module R A] [Module R B] [Module R C]
  (i : A →ₗ[R] B) (p : B →ₗ[R] C)
  (hi : Function.Injective i) (h : Function.Exact i p)
  (s : C →ₗ[R] B) (hs : p.comp s = LinearMap.id),
  Function.LeftInverse (splittingValue R A B C i p hi h s hs).symm
    (splittingValue R A B C i p hi h s hs) ∧
  Function.RightInverse (splittingValue R A B C i p hi h s hs).symm
    (splittingValue R A B C i p hi h s hs)

end P103.Specs.Ch01.SplitSequences
