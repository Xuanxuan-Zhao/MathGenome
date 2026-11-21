import MathGenome.Internal.Specs.D05.M15.TensorUniversal
import MathGenome.Internal.Specs.D05.Foundations.FreeVectors
import MathGenome.Internal.Specs.D05.M06.QuotientLift

/-! Independent statements for paper.tex:2714–2719.
The spaces below are the literal free-vector quotients by the stated relations,
not a tensor product whose universal property is assumed. All input spaces may
have arbitrary dimension. Slot relations impose no characteristic restriction.
-/
namespace Specs.D05.M15.TensorExistence

universe u
noncomputable section
open TensorUniversal

section Binary
variable (K V W : Type u) [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- The four families of bilinearity relations in the free vector space. -/
inductive BinaryRelation : ((V × W) →₀ K) → Prop
  | add_left (v v' : V) (w : W) : BinaryRelation
      (Finsupp.single (v + v', w) 1 - Finsupp.single (v, w) 1 - Finsupp.single (v', w) 1)
  | smul_left (a : K) (v : V) (w : W) : BinaryRelation
      (Finsupp.single (a • v, w) 1 - a • Finsupp.single (v, w) 1)
  | add_right (v : V) (w w' : W) : BinaryRelation
      (Finsupp.single (v, w + w') 1 - Finsupp.single (v, w) 1 - Finsupp.single (v, w') 1)
  | smul_right (a : K) (v : V) (w : W) : BinaryRelation
      (Finsupp.single (v, a • w) 1 - a • Finsupp.single (v, w) 1)

def binaryRelations : Submodule K ((V × W) →₀ K) :=
  Submodule.span K {r | BinaryRelation K V W r}

abbrev BinaryQuotient := ((V × W) →₀ K) ⧸ binaryRelations K V W

noncomputable def elementary (v : V) (w : W) : BinaryQuotient K V W :=
  (binaryRelations K V W).mkQ (Finsupp.single (v, w) 1)
end Binary

/-- The free extension kills the entire relation subspace, not only its generators. -/
def binary_annihilation : Prop :=
  ∀ {K V W H : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup H] [Module K H]
    (b : V →ₗ[K] W →ₗ[K] H),
    binaryRelations K V W ≤ LinearMap.ker
      (Finsupp.linearCombination K (fun p : V × W => b p.1 p.2))

/-- The descended map is unique and retains the free-extension formula. -/
def binary_descent : Prop :=
  ∀ {K V W H : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup H] [Module K H]
    (b : V →ₗ[K] W →ₗ[K] H),
    ∃! l : BinaryQuotient K V W →ₗ[K] H,
      (∀ v w, l (elementary K V W v w) = b v w) ∧
      l.comp (binaryRelations K V W).mkQ =
        Finsupp.linearCombination K (fun p : V × W => b p.1 p.2)

/-- The class of a free generator is bilinear and has the defining universal property. -/
def binary_existence : Prop :=
  ∀ {K V W : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    ∃ τ : V →ₗ[K] W →ₗ[K] BinaryQuotient K V W,
      (∀ v w, τ v w = elementary K V W v w) ∧ IsTensorProduct τ

/-- Elementary classes span the actual quotient. -/
def binary_span : Prop :=
  ∀ {K V W : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    Submodule.span K (Set.range (fun p : V × W => elementary K V W p.1 p.2)) = ⊤

/-- Canonical uniqueness among all models, without assuming an isomorphism or spanning. -/
def binary_unique_equivalence : Prop :=
  ∀ {K V W U U' : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]
    [AddCommGroup U'] [Module K U']
    (τ : V →ₗ[K] W →ₗ[K] U) (σ : V →ₗ[K] W →ₗ[K] U'),
    IsTensorProduct τ → IsTensorProduct σ →
    ∃! E : U ≃ₗ[K] U', ∀ v w, E (τ v w) = σ v w

/-- A normalized bridge to the canonical library tensor product. -/
def binary_canonical_equivalence : Prop :=
  ∀ {K V W : Type u} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W],
    ∃! E : BinaryQuotient K V W ≃ₗ[K] TensorProduct K V W,
      ∀ v w, E (elementary K V W v w) = TensorProduct.tmul K v w

section Finite
variable (K I : Type u) (V : I → Type u) [Field K]
  [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

/-- One additive and one homogeneous relation in each slot. In arity zero
there are no such relations; the free space on the empty tuple remains. -/
inductive SlotRelation : ((∀ i, V i) →₀ K) → Prop
  | add_slot [DecidableEq I] (m : ∀ i, V i) (i : I) (x y : V i) : SlotRelation
      (Finsupp.single (Function.update m i (x + y)) 1 -
        Finsupp.single (Function.update m i x) 1 - Finsupp.single (Function.update m i y) 1)
  | smul_slot [DecidableEq I] (m : ∀ i, V i) (i : I) (a : K) (x : V i) : SlotRelation
      (Finsupp.single (Function.update m i (a • x)) 1 -
        a • Finsupp.single (Function.update m i x) 1)

def slotRelations : Submodule K ((∀ i, V i) →₀ K) :=
  Submodule.span K {r | SlotRelation K I V r}

abbrev FiniteQuotient := ((∀ i, V i) →₀ K) ⧸ slotRelations K I V

noncomputable def finiteElementary (m : ∀ i, V i) : FiniteQuotient K I V :=
  (slotRelations K I V).mkQ (Finsupp.single m 1)
end Finite

/-- Arbitrary finite heterogeneous families use exactly the slot-relation quotient. -/
def finite_annihilation : Prop :=
  ∀ {K I H : Type u} {V : I → Type u} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup H] [Module K H] (b : MultilinearMap K V H),
    slotRelations K I V ≤ LinearMap.ker (Finsupp.linearCombination K b)

def finite_descent : Prop :=
  ∀ {K I H : Type u} {V : I → Type u} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup H] [Module K H] (b : MultilinearMap K V H),
    ∃! l : FiniteQuotient K I V →ₗ[K] H,
      (∀ m, l (finiteElementary K I V m) = b m) ∧
      l.comp (slotRelations K I V).mkQ = Finsupp.linearCombination K b

def finite_existence : Prop :=
  ∀ {K I : Type u} {V : I → Type u} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)],
    ∃ τ : MultilinearMap K V (FiniteQuotient K I V),
      (∀ m, τ m = finiteElementary K I V m) ∧ IsMultitensorProduct τ

def finite_span : Prop :=
  ∀ {K I : Type u} {V : I → Type u} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)],
    Submodule.span K (Set.range (finiteElementary K I V)) = ⊤

def finite_unique_equivalence : Prop :=
  ∀ {K I U U' : Type u} {V : I → Type u} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup U] [Module K U] [AddCommGroup U'] [Module K U']
    (τ : MultilinearMap K V U) (σ : MultilinearMap K V U'),
    IsMultitensorProduct τ → IsMultitensorProduct σ →
    ∃! E : U ≃ₗ[K] U', ∀ m, E (τ m) = σ m

def finite_canonical_equivalence : Prop :=
  ∀ {K I : Type u} {V : I → Type u} [Field K] [Fintype I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)],
    ∃! E : FiniteQuotient K I V ≃ₗ[K] PiTensorProduct K V,
      ∀ m, E (finiteElementary K I V m) = PiTensorProduct.tprod K m

/-- The nullary quotient is the field with the empty elementary tensor equal to 1. -/
def nullary_equivalence : Prop :=
  ∀ {K I : Type u} {V : I → Type u} [Field K] [Fintype I] [IsEmpty I]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)],
    slotRelations K I V = ⊥ ∧
      ∃! E : FiniteQuotient K I V ≃ₗ[K] K,
        ∀ m, E (finiteElementary K I V m) = 1

end
end Specs.D05.M15.TensorExistence
