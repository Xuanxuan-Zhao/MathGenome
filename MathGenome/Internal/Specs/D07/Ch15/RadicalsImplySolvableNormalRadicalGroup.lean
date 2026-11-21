import MathGenome.Internal.Specs.D07.Ch15.RadicalDefinition
import MathGenome.Internal.Specs.D07.Ch15.RootsUnity
import MathGenome.Internal.Specs.D07.Ch15.SolvableClosure
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Algebra.GCDMonoid.Finset

/-! The finite normal radical extension in paper.tex:4417–4421.
There is no separability or restriction on the characteristic. All embeddings
are the specified algebra structures in one algebraic overfield. -/
universe u v
namespace Specs.D07.Ch15.RadicalsImplySolvableNormalRadicalGroup
open IntermediateField Specs.D07.Ch15.RadicalDefinition

/-- The main assertion, with finiteness a consequence of the finite radical tower. -/
def NormalRadicalGroup : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (N : IntermediateField K Ω),
    radicalExtensionValue K Ω N → Normal K N →
      FiniteDimensional K N ∧ Group.IsSolvable (N ≃ₐ[K] N)

/-- The comparison with Mathlib's root-closed subfield retains the original
finite-tower predicate as the hypothesis. -/
def TowerInSolvableByRad : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] (N : IntermediateField K Ω),
    radicalExtensionValue K Ω N → N ≤ solvableByRad K Ω

/-- A single step after the requisite distinct roots of unity are in the base.
The exponent is positive but may be zero as a scalar in the base field. -/
def NormalCyclicStep : Prop :=
  ∀ (M : Type u) (Ω : Type v) [Field M] [Field Ω] [Algebra M Ω]
    [Normal M Ω] (a : Ω) (n : ℕ), 0 < n → a ^ n ∈ (⊥ : IntermediateField M Ω) →
    (∀ z : Ω, z ^ n = 1 → z ∈ (⊥ : IntermediateField M Ω)) →
    Normal M (adjoin M {a}) ∧ IsCyclic ((adjoin M {a}) ≃ₐ[M] (adjoin M {a}))

/-- Adjoin exactly the primitive root prescribed in the source: the LCM of
the prime-to-characteristic parts of the given positive exponents. -/
def LcmRootAdjunction : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] (r : ℕ) (n : Fin r → ℕ),
    (∀ i, 0 < n i) →
    let m := Finset.univ.lcm (fun i => ordCompl[ringExpChar K] (n i))
    0 < m ∧ (m : K) ≠ 0 ∧ ∃ ζ : Ω, IsPrimitiveRoot ζ m ∧
      let C := adjoin K {ζ}
      FiniteDimensional K C ∧ Normal K C ∧
      (∀ σ τ : C ≃ₐ[K] C, σ * τ = τ * σ) ∧
      ∀ i (z : Ω), z ^ n i = 1 → z ∈ C

/-- Restriction to a normal cyclic intermediate step supplies its actual fixing
kernel and a cyclic quotient, without a separability assumption. -/
def CyclicFixingFactor : Prop :=
  ∀ (M : Type u) (E : Type v) [Field M] [Field E] [Algebra M E]
    (L : IntermediateField M E), Normal M L → IsCyclic (L ≃ₐ[M] L) →
    ∃ h : L.fixingSubgroup.Normal,
      letI := h
      IsCyclic ((E ≃ₐ[M] E) ⧸ L.fixingSubgroup)

/-- Full refinement of any specified radical presentation of a normal field.
`F` is the base-changed tower INSIDE its final compositum. Its fixing subgroups
form a descending finite subnormal series: the initial quotient is abelian,
every successive quotient is cyclic, and the last fixing subgroup is trivial.
`Normal` is deliberately used instead of `IsGalois` for the radical steps. -/
def TowerRefinement : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] (r : ℕ)
    (T : Fin (r + 1) → IntermediateField K Ω) (a : Fin r → Ω) (n : Fin r → ℕ),
    T 0 = ⊥ →
    (∀ i, 0 < n i ∧ a i ^ n i ∈ T i.castSucc ∧
      T i.succ = adjoin K ((T i.castSucc : Set Ω) ∪ {a i})) →
    Normal K (T (Fin.last r)) →
    let m := Finset.univ.lcm (fun i => ordCompl[ringExpChar K] (n i))
    ∃ ζ : Ω, IsPrimitiveRoot ζ m ∧
      let C := adjoin K {ζ}
      let N' := C ⊔ T (Fin.last r)
      let F : Fin (r + 1) → IntermediateField K N' :=
        fun i => (C ⊔ T i).comap N'.val
      FiniteDimensional K N' ∧ Normal K N' ∧ Monotone F ∧
      (F (Fin.last r)).fixingSubgroup = ⊥ ∧
      (∃ h : (F 0).fixingSubgroup.Normal, letI := h
        ∀ σ τ : (N' ≃ₐ[K] N') ⧸ (F 0).fixingSubgroup, σ * τ = τ * σ) ∧
      ∀ i : Fin r, ∃ hi : F i.castSucc ≤ F i.succ,
        Normal (F i.castSucc) (extendScalars hi) ∧
        IsCyclic ((extendScalars hi) ≃ₐ[F i.castSucc] (extendScalars hi)) ∧
        ∃ h : ((F i.succ).fixingSubgroup.subgroupOf (F i.castSucc).fixingSubgroup).Normal,
          letI := h
          IsCyclic ((F i.castSucc).fixingSubgroup ⧸
            (F i.succ).fixingSubgroup.subgroupOf (F i.castSucc).fixingSubgroup)

end Specs.D07.Ch15.RadicalsImplySolvableNormalRadicalGroup
