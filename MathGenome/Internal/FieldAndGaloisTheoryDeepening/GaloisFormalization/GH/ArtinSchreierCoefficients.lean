import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.ArtinSchreierCoefficients
import MathGenome.Internal.FieldAndGaloisTheoryDeepening.GaloisFormalization.GH.KrullLayers
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.Basic

/-! Artin–Schreier coefficients for the intrinsic absolute Galois group. -/

namespace GaloisFormalization.GH.ArtinSchreierCoefficients

universe u v w

noncomputable section

open KrullLayers (AbsoluteGaloisGroup)
open Polynomial

attribute [local instance] ZMod.algebra

section Field

variable (p : ℕ) (F : Type u) [Field F] [Fact p.Prime] [CharP F p]

/-- The map from the prime field into a field of characteristic `p`. -/
def primeFieldInclusion : ZMod p →ₗ[ZMod p] F :=
  Specs.GaloisFormalization.GH.ArtinSchreierCoefficients.primeFieldInclusion p F

/-- Frobenius minus the identity, as a linear map over the prime field. -/
def wp : F →ₗ[ZMod p] F :=
  Specs.GaloisFormalization.GH.ArtinSchreierCoefficients.wp p F

@[simp]
theorem primeFieldInclusion_apply (c : ZMod p) :
    primeFieldInclusion p F c = algebraMap (ZMod p) F c :=
  rfl

@[simp]
theorem wp_apply (x : F) : wp p F x = x ^ p - x :=
  rfl

/-- The quotient of the additive group by the image of Frobenius minus the identity. -/
abbrev Quotient : Type u :=
  F ⧸ LinearMap.range (wp p F)

/-- The projection onto the Artin–Schreier quotient. -/
def quotientMap : F →ₗ[ZMod p] Quotient p F :=
  (LinearMap.range (wp p F)).mkQ

theorem primeFieldInclusion_injective : Function.Injective (primeFieldInclusion p F) :=
  (algebraMap (ZMod p) F).injective

/-- Over any field of characteristic `p`, the zeroes of `wp` are the prime field. -/
theorem exact_wp : Function.Exact (primeFieldInclusion p F) (wp p F) := by
  intro x
  change x ^ p - x = 0 ↔ x ∈ Set.range (algebraMap (ZMod p) F)
  rw [sub_eq_zero, ← Subfield.mem_bot_iff_pow_eq_self F p, ← ZMod.fieldRange_castHom_eq_bot p]
  rfl

/-- Over a separably closed field, every Artin–Schreier polynomial has a root. -/
theorem wp_surjective [IsSepClosed F] : Function.Surjective (wp p F) := by
  intro a
  let f : F[X] := X ^ p - X - C a
  have hsep : f.Separable := by
    rw [separable_def']
    refine ⟨0, -1, ?_⟩
    simp [f, derivative_sub, derivative_pow]
  have hdegree : f.natDegree = p := by
    change (X ^ p - X - C a : F[X]).natDegree = p
    rw [natDegree_sub_C, FiniteField.X_pow_card_sub_X_natDegree_eq F (Fact.out : p.Prime).one_lt]
  have hnonconstant : f.degree ≠ 0 :=
    degree_ne_of_natDegree_ne (n := 0) (hdegree.trans_ne (Fact.out : p.Prime).ne_zero)
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root f hnonconstant hsep
  exact ⟨x, sub_eq_zero.mp (by simpa [Polynomial.IsRoot, f] using hx)⟩

end Field

section Naturality

variable (p : ℕ) {F : Type u} {E : Type v} [Field F] [Field E]
  [Fact p.Prime] [CharP F p] [CharP E p]

theorem wp_natural (f : F →+* E) (x : F) : f (wp p F x) = wp p E (f x) := by
  simp [wp_apply, map_sub, map_pow]

theorem primeFieldInclusion_natural (f : F →+* E) (c : ZMod p) :
    f (primeFieldInclusion p F c) = primeFieldInclusion p E c :=
  DFunLike.congr_fun (Subsingleton.elim (f.comp (algebraMap (ZMod p) F))
    (algebraMap (ZMod p) E)) c

end Naturality

/-- The prime field with trivial action. Use as a local instance. -/
abbrev primeFieldAction (G : Type v) [Monoid G] (p : ℕ) : DistribMulAction G (ZMod p) :=
  Specs.GaloisFormalization.GH.ArtinSchreierCoefficients.primeFieldAction G p

section SeparableClosure

variable (p : ℕ) (k : Type u) (S : Type v) [Field k] [Field S] [Algebra k S]
  [Fact p.Prime] [CharP k p] [IsSepClosure k S]

/-- The short exact linear sequence on the chosen separable closure. -/
theorem shortExact :
    letI : CharP S p := charP_of_injective_algebraMap' k p
    Function.Injective (primeFieldInclusion p S) ∧
      Function.Exact (primeFieldInclusion p S) (wp p S) ∧
      Function.Surjective (wp p S) := by
  let _ : CharP S p := charP_of_injective_algebraMap' k p
  let _ : IsSepClosed S := IsSepClosure.sep_closed k
  exact ⟨primeFieldInclusion_injective p S, exact_wp p S, wp_surjective p S⟩

/-- The natural Galois action on the closure is linear over the prime field. -/
theorem galois_smul :
    letI : CharP S p := charP_of_injective_algebraMap' k p
    ∀ (g : AbsoluteGaloisGroup k S) (c : ZMod p) (x : S),
      g • (c • x) = c • (g • x) := by
  let _ : CharP S p := charP_of_injective_algebraMap' k p
  intro g c x
  change g (primeFieldInclusion p S c * x) = primeFieldInclusion p S c * g x
  rw [map_mul]
  exact congrArg (· * g x) (primeFieldInclusion_natural p g.toRingEquiv.toRingHom c)

/-- Both maps intertwine the indicated Galois actions. -/
theorem equivariant :
    letI : CharP S p := charP_of_injective_algebraMap' k p
    letI : DistribMulAction (AbsoluteGaloisGroup k S) (ZMod p) :=
      primeFieldAction (AbsoluteGaloisGroup k S) p
    (∀ (g : AbsoluteGaloisGroup k S) (c : ZMod p),
      primeFieldInclusion p S (g • c) = g • primeFieldInclusion p S c) ∧
    (∀ (g : AbsoluteGaloisGroup k S) (x : S), wp p S (g • x) = g • wp p S x) := by
  let _ : CharP S p := charP_of_injective_algebraMap' k p
  exact ⟨fun g c => (primeFieldInclusion_natural p g.toRingEquiv.toRingHom c).symm,
    fun g x => (wp_natural p g.toRingEquiv.toRingHom x).symm⟩

omit [CharP k p] in
/-- The two coefficient actions are continuous for the discrete coefficient topologies. -/
theorem continuous_actions [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]
    [TopologicalSpace S] [DiscreteTopology S] :
    letI : DistribMulAction (AbsoluteGaloisGroup k S) (ZMod p) :=
      primeFieldAction (AbsoluteGaloisGroup k S) p
    ContinuousSMul (AbsoluteGaloisGroup k S) (ZMod p) ∧
      ContinuousSMul (AbsoluteGaloisGroup k S) S := by
  let _ : DistribMulAction (AbsoluteGaloisGroup k S) (ZMod p) :=
    primeFieldAction (AbsoluteGaloisGroup k S) p
  exact ⟨⟨continuous_snd⟩, KrullLayers.continuous_fieldAction k S⟩

omit [IsSepClosure k S] in
/-- The coefficient maps are continuous when their domains have the discrete topology. -/
theorem continuous_maps [TopologicalSpace (ZMod p)] [DiscreteTopology (ZMod p)]
    [TopologicalSpace S] [DiscreteTopology S] :
    letI : CharP S p := charP_of_injective_algebraMap' k p
    Continuous (primeFieldInclusion p S) ∧ Continuous (wp p S) :=
  ⟨continuous_of_discreteTopology, continuous_of_discreteTopology⟩

/-- Tensoring the short exact sequence with any prime-field vector space preserves exactness. -/
theorem shortExact_rTensor (M : Type w) [AddCommGroup M] [Module (ZMod p) M] :
    letI : CharP S p := charP_of_injective_algebraMap' k p
    Function.Injective ((primeFieldInclusion p S).rTensor M) ∧
      Function.Exact ((primeFieldInclusion p S).rTensor M) ((wp p S).rTensor M) ∧
      Function.Surjective ((wp p S).rTensor M) := by
  let _ : CharP S p := charP_of_injective_algebraMap' k p
  obtain ⟨hinj, hexact, hsurj⟩ := shortExact p k S
  exact ⟨Module.Flat.rTensor_preserves_injective_linearMap _ hinj,
    Module.Flat.rTensor_exact M hexact, LinearMap.rTensor_surjective M hsurj⟩

end SeparableClosure

end

end GaloisFormalization.GH.ArtinSchreierCoefficients
