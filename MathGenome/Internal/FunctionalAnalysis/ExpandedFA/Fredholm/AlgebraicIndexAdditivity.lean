import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.AlgebraicIndexAdditivity
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.Definitions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.RingTheory.Finiteness.Finsupp
import Lean.Elab.Tactic.Omega

/-!
The kernel–cokernel sequence of two composable linear maps, followed by
rank–nullity. All maps below are algebraic and the ambient spaces may have
arbitrary dimension. Finiteness of the middle kernel and cokernel is proved
before using natural-number dimensions.
-/

noncomputable section
namespace ExpandedFA.Fredholm
namespace AlgebraicIndexAdditivity
universe u v w z
variable {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w} {Z : Type z}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module 𝕜 X] [Module 𝕜 Y] [Module 𝕜 Z]
variable (T : X →ₗ[𝕜] Y) (S : Y →ₗ[𝕜] Z)

/-- The `T` arrow from the kernel of the composition to the kernel of `S`. -/
def kernelMap : (S.comp T).ker →ₗ[𝕜] S.ker :=
  (T.comp (S.comp T).ker.subtype).codRestrict S.ker fun x => x.property

/-- The connecting arrow, taking the class of a vector in `ker S` modulo `range T`. -/
def connectingMap : S.ker →ₗ[𝕜] Y ⧸ T.range :=
  T.range.mkQ.comp S.ker.subtype

/-- The arrow induced by `S` on the actual cokernels. -/
def cokernelMap : (Y ⧸ T.range) →ₗ[𝕜] Z ⧸ (S.comp T).range :=
  T.range.mapQ (S.comp T).range S (by
    rintro y ⟨x, rfl⟩
    exact ⟨x, rfl⟩)

/-- The final natural quotient arrow. -/
def cokernelProjection : (Z ⧸ (S.comp T).range) →ₗ[𝕜] Z ⧸ S.range :=
  (S.comp T).range.mapQ S.range LinearMap.id (by
    rintro z ⟨x, rfl⟩
    exact ⟨T x, rfl⟩)

/-- Exactness at the first term: the kernel of the `T` arrow is `ker T`. -/
def kernelMapKerEquiv : T.ker ≃ₗ[𝕜] (kernelMap T S).ker := by
  let f : T.ker →ₗ[𝕜] (kernelMap T S).ker :=
    { toFun := fun x => ⟨⟨x, by
        change S (T x) = 0
        rw [x.property, map_zero]⟩, by
        apply Subtype.ext
        exact x.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact LinearEquiv.ofBijective f
    ⟨fun _ _ h => Subtype.ext (congrArg (fun x => x.val.val) h), by
      rintro ⟨x, hx⟩
      refine ⟨⟨x, congrArg Subtype.val hx⟩, ?_⟩
      rfl⟩

/-- Exactness at `ker S`. -/
theorem range_kernelMap : (kernelMap T S).range = (connectingMap T S).ker := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change T.range.mkQ (T x) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩
  · intro hy
    have hy' : (y : Y) ∈ T.range := (Submodule.Quotient.mk_eq_zero _).mp hy
    obtain ⟨x, hx⟩ := hy'
    refine ⟨⟨x, ?_⟩, ?_⟩
    · change S (T x) = 0
      rw [hx]
      exact y.property
    · exact Subtype.ext hx

/-- Exactness at `coker T`: if `Sy = STx`, then `y - Tx` belongs to `ker S`. -/
theorem range_connectingMap : (connectingMap T S).range = (cokernelMap T S).ker := by
  ext q
  obtain ⟨y, rfl⟩ := T.range.mkQ_surjective q
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]
    change (S.comp T).range.mkQ (S k) = 0
    rw [k.property, map_zero]
  · intro hy
    have hy' : S y ∈ (S.comp T).range := (Submodule.Quotient.mk_eq_zero _).mp hy
    obtain ⟨x, hx⟩ := hy'
    refine ⟨⟨y - T x, ?_⟩, ?_⟩
    · change S (y - T x) = 0
      rw [map_sub, ← hx]
      exact sub_self _
    · change T.range.mkQ (y - T x) = T.range.mkQ y
      have hTx : T.range.mkQ (T x) = 0 :=
        (Submodule.Quotient.mk_eq_zero T.range).mpr ⟨x, rfl⟩
      rw [map_sub, hTx, sub_zero]

/-- Exactness at `coker ST`. -/
theorem range_cokernelMap : (cokernelMap T S).range = (cokernelProjection T S).ker := by
  ext q
  obtain ⟨z, rfl⟩ := (S.comp T).range.mkQ_surjective q
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨y, rfl⟩ := T.range.mkQ_surjective p
    rw [← hp]
    change S.range.mkQ (S y) = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨y, rfl⟩
  · intro hz
    have hz' : z ∈ S.range := (Submodule.Quotient.mk_eq_zero _).mp hz
    obtain ⟨y, hy⟩ := hz'
    exact ⟨T.range.mkQ y, congrArg (S.comp T).range.mkQ hy⟩

/-- Exactness at the last term. -/
theorem cokernelProjection_surjective : Function.Surjective (cokernelProjection T S) := by
  intro q
  obtain ⟨z, rfl⟩ := S.range.mkQ_surjective q
  exact ⟨(S.comp T).range.mkQ z, rfl⟩

/-- A vector space with finite kernel and finite range is finite dimensional. -/
theorem finiteDimensional_of_ker_range {U : Type*} {V : Type*}
    [AddCommGroup U] [AddCommGroup V] [Module 𝕜 U] [Module 𝕜 V]
    (f : U →ₗ[𝕜] V) [FiniteDimensional 𝕜 f.ker] [FiniteDimensional 𝕜 f.range] :
    FiniteDimensional 𝕜 U := by
  have : FiniteDimensional 𝕜 (U ⧸ f.ker) :=
    Module.Finite.equiv f.quotKerEquivRange.symm
  exact Module.Finite.of_submodule_quotient f.ker

end AlgebraicIndexAdditivity

universe u v w z
variable {𝕜 : Type u} [Field 𝕜] {X : Type v} {Y : Type w} {Z : Type z}
  [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
  [Module 𝕜 X] [Module 𝕜 Y] [Module 𝕜 Z]

open AlgebraicIndexAdditivity

/-- Algebraic finite-index maps are closed under composition. -/
theorem isAlgebraicFiniteIndex_comp (T : X →ₗ[𝕜] Y) (S : Y →ₗ[𝕜] Z)
    (hT : IsAlgebraicFiniteIndex T) (hS : IsAlgebraicFiniteIndex S) :
    IsAlgebraicFiniteIndex (S.comp T) := by
  have : FiniteDimensional 𝕜 T.ker := hT.1
  have : FiniteDimensional 𝕜 (Y ⧸ T.range) := hT.2
  have : FiniteDimensional 𝕜 S.ker := hS.1
  have : FiniteDimensional 𝕜 (Z ⧸ S.range) := hS.2
  constructor
  · have : FiniteDimensional 𝕜 (kernelMap T S).ker :=
      Module.Finite.equiv (kernelMapKerEquiv T S)
    have : FiniteDimensional 𝕜 (kernelMap T S).range := inferInstance
    exact finiteDimensional_of_ker_range (kernelMap T S)
  · have : FiniteDimensional 𝕜 (cokernelProjection T S).ker := by
      rw [← range_cokernelMap T S]
      infer_instance
    have : FiniteDimensional 𝕜 (cokernelProjection T S).range := inferInstance
    exact finiteDimensional_of_ker_range (cokernelProjection T S)

/-- Alternating dimensions in the actual kernel–cokernel sequence give
`ind (S ∘ T) = ind S + ind T`. The witness for the composition is arbitrary. -/
theorem algebraicIndex_comp (T : X →ₗ[𝕜] Y) (S : Y →ₗ[𝕜] Z)
    (hT : IsAlgebraicFiniteIndex T) (hS : IsAlgebraicFiniteIndex S)
    (hST : IsAlgebraicFiniteIndex (S.comp T)) :
    algebraicIndex (S.comp T) hST = algebraicIndex S hS + algebraicIndex T hT := by
  have : FiniteDimensional 𝕜 T.ker := hT.1
  have : FiniteDimensional 𝕜 (Y ⧸ T.range) := hT.2
  have : FiniteDimensional 𝕜 S.ker := hS.1
  have : FiniteDimensional 𝕜 (Z ⧸ S.range) := hS.2
  have : FiniteDimensional 𝕜 (S.comp T).ker := hST.1
  have : FiniteDimensional 𝕜 (Z ⧸ (S.comp T).range) := hST.2
  have h₁ := (kernelMap T S).finrank_range_add_finrank_ker
  have h₂ := (connectingMap T S).finrank_range_add_finrank_ker
  have h₃ := (cokernelMap T S).finrank_range_add_finrank_ker
  have h₄ := (cokernelProjection T S).finrank_range_add_finrank_ker
  rw [← (kernelMapKerEquiv T S).finrank_eq, range_kernelMap T S] at h₁
  rw [range_connectingMap T S] at h₂
  rw [range_cokernelMap T S] at h₃
  rw [LinearMap.range_eq_top.mpr (cokernelProjection_surjective T S),
    finrank_top] at h₄
  unfold algebraicIndex
  omega

end ExpandedFA.Fredholm
