import MathGenome.Internal.Specs.D05.M15.Multilinear
import MathGenome.Internal.Specs.D05.M06.QuotientLift
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Pi

/-!
Independent statements for paper.tex:2701–2708. Bilinear maps use Mathlib's
`V →ₗ[K] W →ₗ[K] H`; the last statement explicitly identifies this representation
with the prerequisite's two-slot `MultilinearMap`. All spaces are algebraic and
arbitrary dimensional. Extension uses choice, with no preferred complements.
-/
namespace Specs.D05.M15.Multilinear.RestrictionDescentCurrying

/-- Restriction in every slot, including an empty slot family. -/
def restriction : Prop :=
  ∀ {K I : Type*} {V : I → Type*} {H : Type*} [Field K]
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [AddCommGroup H] [Module K H] (b : MultilinearMap K V H)
    (U : ∀ i, Submodule K (V i)),
    ∃ r : MultilinearMap K (fun i => U i) H,
      ∀ u, r u = b (fun i => (u i : V i))

/-- The same restriction for the curried bilinear representation. -/
def bilinear_restriction : Prop :=
  ∀ {K V W H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup H] [Module K H],
  ∀ (U : Submodule K V) (S : Submodule K W) (b : V →ₗ[K] W →ₗ[K] H),
    ∃ r : U →ₗ[K] S →ₗ[K] H, ∀ (u : U) (s : S), r u s = b (u : V) (s : W)

/-- Vanishing on both subspace slots is necessary and sufficient for descent.
The representative formula also specifies the descended map uniquely. -/
def descent_iff : Prop :=
  ∀ {K V W H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup H] [Module K H],
  ∀ (U : Submodule K V) (S : Submodule K W) (b : V →ₗ[K] W →ₗ[K] H),
    (∃! d : (V ⧸ U) →ₗ[K] (W ⧸ S) →ₗ[K] H,
      ∀ v w, d (U.mkQ v) (S.mkQ w) = b v w) ↔
    (∀ u ∈ U, ∀ w, b u w = 0) ∧ (∀ v, ∀ s ∈ S, b v s = 0)

/-- With quotient-valued output, vanishing means membership in L. No
characteristic or dimension restriction is imposed on the three quotients. -/
def descent_mod_iff : Prop :=
  ∀ {K V W H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup H] [Module K H],
  ∀ (U : Submodule K V) (S : Submodule K W) (L : Submodule K H)
    (b : V →ₗ[K] W →ₗ[K] H),
    (∃! d : (V ⧸ U) →ₗ[K] (W ⧸ S) →ₗ[K] (H ⧸ L),
      ∀ v w, d (U.mkQ v) (S.mkQ w) = L.mkQ (b v w)) ↔
    (∀ u ∈ U, ∀ w, b u w ∈ L) ∧ (∀ v, ∀ s ∈ S, b v s ∈ L)

/-- Once complements are fixed, there is exactly one extension with zero
values whenever either slot is in its chosen complement. -/
def extension_with_complements : Prop :=
  ∀ {K V W H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup H] [Module K H],
  ∀ (U U' : Submodule K V) (S S' : Submodule K W)
    (_hU : IsCompl U U') (_hS : IsCompl S S') (b : U →ₗ[K] S →ₗ[K] H),
    ∃! B : V →ₗ[K] W →ₗ[K] H,
      (∀ (u : U) (s : S), B (u : V) (s : W) = b u s) ∧
      (∀ v ∈ U', ∀ w, B v w = 0) ∧ (∀ v, ∀ w ∈ S', B v w = 0)

/-- Choice supplies complements and hence an extension, in arbitrary dimension.
Neither a complement nor a preferred extension is part of the input. -/
def extension : Prop :=
  ∀ {K V W H : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup H] [Module K H],
  ∀ (U : Submodule K V) (S : Submodule K W) (b : U →ₗ[K] S →ₗ[K] H),
    ∃ (U' : Submodule K V) (S' : Submodule K W), IsCompl U U' ∧ IsCompl S S' ∧
      ∃ B : V →ₗ[K] W →ₗ[K] H,
        (∀ (u : U) (s : S), B (u : V) (s : W) = b u s) ∧
        (∀ v ∈ U', ∀ w, B v w = 0) ∧ (∀ v, ∀ w ∈ S', B v w = 0)

/-- Different complements can give different extensions of the same pairing.
Here the second input is the whole scalar space; the two complementary lines
are the lines through (0,1) and (1,1), as in the earlier complement example. -/
def extension_can_differ : Prop :=
  ∀ (K : Type*) [Field K],
    let U := Submodule.span K ({(1, 0)} : Set (K × K))
    let U₀ := Submodule.span K ({(0, 1)} : Set (K × K))
    let U₁ := Submodule.span K ({(1, 1)} : Set (K × K))
    ∃ (b : U →ₗ[K] K →ₗ[K] K) (B₀ B₁ : (K × K) →ₗ[K] K →ₗ[K] K),
      B₀ ≠ B₁ ∧ IsCompl U U₀ ∧ IsCompl U U₁ ∧
      (∀ (u : U) w, B₀ (u : K × K) w = b u w ∧ B₁ (u : K × K) w = b u w) ∧
      (∀ v ∈ U₀, ∀ w, B₀ v w = 0) ∧ (∀ v ∈ U₁, ∀ w, B₁ v w = 0)

/-- Currying is an actual linear equivalence from two-slot multilinear maps.
The inverse is evaluation, on every tuple. The family M permits distinct inputs. -/
def currying : Prop :=
  ∀ {K : Type*} {M : Fin 2 → Type*} {H : Type*} [Field K]
    [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)]
    [AddCommGroup H] [Module K H],
    ∃ E : MultilinearMap K M H ≃ₗ[K] (M 0 →ₗ[K] M 1 →ₗ[K] H),
      (∀ (b : MultilinearMap K M H) (m : ∀ i, M i), E b (m 0) (m 1) = b m) ∧
      (∀ (f : M 0 →ₗ[K] M 1 →ₗ[K] H) (m : ∀ i, M i), E.symm f m = f (m 0) (m 1))

end Specs.D05.M15.Multilinear.RestrictionDescentCurrying
