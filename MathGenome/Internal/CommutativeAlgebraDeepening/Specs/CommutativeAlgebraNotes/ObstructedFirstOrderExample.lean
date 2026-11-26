import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalArtinAlgebras
import Mathlib.LinearAlgebra.Pi

/-! The marked first-order algebra and its lifting obstruction in Example 6.6. -/

noncomputable section

open Polynomial
open scoped TensorProduct

universe u v

namespace CommutativeAlgebraNotes.ObstructedFirstOrderExample

variable (k : Type u) [Field k]

/-- The truncated polynomial ring with truncation exponent `n + 1`. -/
abbrev Truncated (n : ℕ) := AdjoinRoot (X ^ (n + 1) : k[X])

/-- The class of the polynomial variable. -/
abbrev root (n : ℕ) : Truncated k n := AdjoinRoot.root _

theorem root_pow (n : ℕ) : root k n ^ (n + 1) = 0 := by
  change AdjoinRoot.root (X ^ (n + 1) : k[X]) ^ (n + 1) = 0
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_self]

/-- The constant term map. -/
def augmentation (n : ℕ) : Truncated k n →ₐ[k] k :=
  AdjoinRoot.liftAlgHom _ (AlgHom.id k k) 0 (by simp)

@[simp] theorem augmentation_root (n : ℕ) :
    augmentation k n (root k n) = 0 :=
  AdjoinRoot.liftAlgHom_root ..

theorem ker_augmentation (n : ℕ) :
    RingHom.ker (augmentation k n).toRingHom = Ideal.span {root k n} := by
  apply le_antisymm
  · intro x hx
    induction x using AdjoinRoot.induction_on with
    | ih p =>
      change p.eval₂ (RingHom.id k) (0 : k) = 0 at hx
      rw [eval₂_id] at hx
      have hx' : p.coeff 0 = 0 := by rwa [coeff_zero_eq_eval_zero]
      obtain ⟨q, rfl⟩ := X_dvd_iff.mpr hx'
      exact Ideal.mem_span_singleton.mpr ⟨AdjoinRoot.mk _ q, by rw [map_mul, AdjoinRoot.mk_X]⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    change augmentation k n (root k n) = 0
    exact augmentation_root k n

private theorem augmentation_local (n : ℕ) : IsLocalHom (augmentation k n) := by
  constructor
  intro x hx
  have hc : IsUnit (algebraMap k (Truncated k n) (augmentation k n x)) :=
    hx.map (algebraMap k (Truncated k n))
  let c : Truncated k n := algebraMap k _ (augmentation k n x)
  obtain ⟨u, hu⟩ := hc
  have h₁ : x - c ∈ RingHom.ker (augmentation k n).toRingHom := by
    change augmentation k n (x - c) = 0
    rw [map_sub, show augmentation k n c = augmentation k n x from
      (augmentation k n).commutes _, sub_self]
  rw [ker_augmentation, Ideal.mem_span_singleton] at h₁
  obtain ⟨q, hq⟩ := h₁
  have hn : IsNilpotent ((↑u⁻¹ : Truncated k n) * (x - c)) := by
    refine ⟨n + 1, ?_⟩
    rw [hq, mul_left_comm, mul_pow, root_pow, zero_mul]
  have he : x = (↑u : Truncated k n) * (1 + (↑u⁻¹ : Truncated k n) * (x - c)) := by
    rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, hu]
    change x = c + (x - c)
    abel
  rw [he]
  exact u.isUnit.mul hn.isUnit_one_add

/-- The local Artin base with its specified residue field. -/
def base (n : ℕ) : LocalArtinAlgebra.{u,u} k :=
  letI : IsLocalHom (augmentation k n) := augmentation_local k n
  letI : IsLocalHom (augmentation k n).toRingHom :=
    ⟨fun a h => (augmentation_local k n).map_nonunit a h⟩
  letI : IsLocalRing (Truncated k n) := (augmentation k n).toRingHom.domain_isLocalRing
  letI : Module.Finite k (Truncated k n) :=
    (AdjoinRoot.powerBasis' ((monic_X (R := k)).pow (n + 1))).finite
  letI : IsArtinianRing (Truncated k n) := IsArtinianRing.of_finite k _
  { carrier := Truncated k n, residue := augmentation k n }

/-- The class of the polynomial variable in the bundled base. -/
def parameter (n : ℕ) : base k n := root k n

theorem parameter_pow (n : ℕ) : parameter k n ^ (n + 1) = 0 := root_pow k n

/-- The quotient map from the cubic to the quadratic truncated polynomial ring. -/
def reduction : LocalArtinAlgebra.Hom (base k 2) (base k 1) := by
  let f : Truncated k 2 →ₐ[k] Truncated k 1 :=
    AdjoinRoot.liftAlgHom _ (Algebra.ofId k _) (root k 1) (by
      simp only [eval₂_pow, eval₂_X]
      change root k 1 ^ 3 = 0
      rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, root_pow k 1, zero_mul])
  refine ⟨f, ⟨fun a ha => ?_⟩⟩
  let := augmentation_local k 2
  apply IsUnit.of_map (augmentation k 2)
  have h : (augmentation k 1).comp f = augmentation k 2 := by
    apply AdjoinRoot.algHom_ext
    simp [f]
  exact (congrFun (congrArg DFunLike.coe h) a) ▸ ha.map (augmentation k 1)

@[simp] theorem reduction_parameter :
    (reduction k).val (parameter k 2) = parameter k 1 := by
  change AdjoinRoot.liftAlgHom _ (Algebra.ofId k (Truncated k 1)) (root k 1) _
    (root k 2) = root k 1
  exact AdjoinRoot.liftAlgHom_root ..

/-- The original algebra, with the square-zero ideal spanned by three vectors. -/
def residual : LocalArtinAlgebra.{u,u} k :=
  LocalArtinAlgebra.splitModel k (Fin 3 → k)

/-- The ordered marked vectors `1,x,y,z` of the original algebra. -/
def residualVectors (i : Fin 4) : residual k :=
  let e : Fin 4 → k := Pi.single i 1
  (⟨e 0, fun j => e j.succ⟩ : TrivSqZeroExt k (Fin 3 → k))

end CommutativeAlgebraNotes.ObstructedFirstOrderExample

namespace Specs.CommutativeAlgebraNotes.ObstructedFirstOrderExample

open _root_.CommutativeAlgebraNotes
open _root_.CommutativeAlgebraNotes.ObstructedFirstOrderExample

/-- A flat first-order deformation with the stated ordered basis and marking
exists, and its underlying algebra has no flat lift, even without requiring
the isomorphism on the reduction to preserve the marking. -/
def Obstruction : Prop :=
  ∀ (k : Type u) [Field k],
    ∃ (E : MarkedDeformation.{u,u,u,u} (base k 1) (residual k))
      (b : Module.Basis (Fin 4) (base k 1) E),
      let t : base k 1 := parameter k 1
      b 0 = 1 ∧
      (∀ i, E.marking (1 ⊗ₜ[base k 1] b i) = residualVectors k i) ∧
      b 1 * b 2 = t • b 3 ∧ b 3 * b 3 = t • b 2 ∧
      b 1 * b 1 = 0 ∧ b 1 * b 3 = 0 ∧ b 2 * b 2 = 0 ∧ b 2 * b 3 = 0 ∧
      letI := (reduction k).toAlgebra
      ∀ (D : Type v) [CommRing D] [Algebra (base k 2) D] [Module.Flat (base k 2) D],
        IsEmpty ((base k 1) ⊗[base k 2] D ≃ₐ[base k 1] E)

end Specs.CommutativeAlgebraNotes.ObstructedFirstOrderExample
