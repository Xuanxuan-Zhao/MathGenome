import MathGenome.Internal.AlgebraCore.Specs.P103.Ch01.Scalars

/-! Proofs of the equivalences and scalar laws in Definition 1.3.
The constructions themselves are shared canonical definitions in the Specs. -/
namespace P103.Ch01.Scalars

open P103.Scalars

universe u v w t

/-- The unital algebra whose scalar action is multiplication by a central image. -/
abbrev algebraFromCentralMap {k : Type u} {A : Type v} [CommRing k] [Ring A]
    (f : k →+* Subring.center A) : Algebra k A :=
  P103.Scalars.algebraOfCenter f

/-- Algebra structures are precisely central unital structure maps. -/
theorem centerIdentification (k : Type u) (A : Type v) [CommRing k] [Ring A] :
    Spec.centerIdentification k A := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    apply Algebra.algebra_ext
    intro r
    rfl
  · intro f
    apply RingHom.ext
    intro r
    apply Subtype.ext
    rfl
  · intro f r x
    rfl
  · intro a r
    let _ := a
    exact Algebra.algebraMap_eq_smul_one r

private theorem compatibleModule_ext {k : Type u} {A : Type v} [CommRing k] [Ring A]
    (b c : CompatibleModule k A) (h : b.module = c.module) : b = c := by
  cases b
  cases c
  cases h
  rfl

/-- Bilinear unital multiplication recovers exactly the original algebra and action. -/
theorem moduleIdentification (k : Type u) (A : Type v) [CommRing k] [Ring A] :
    Spec.moduleIdentification k A := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a
    let _ := a
    apply Algebra.algebra_ext
    intro r
    exact (Algebra.algebraMap_eq_smul_one r).symm
  · intro b
    apply compatibleModule_ext
    exact Module.ext' _ _ (fun _ _ => rfl)
  · intro b r
    rfl
  · intro b r x
    let _ := b.module
    calc
      (r • (1 : A)) * x = r • x := by rw [b.left_linear, one_mul]
      _ = x * (r • (1 : A)) := by rw [b.right_linear, mul_one]

/-- The compatible ring maps are exactly algebra maps, or equivalently linear ring maps. -/
theorem morphismIdentification (k : Type u) (A : Type v) (B : Type w)
    [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B] :
    Spec.morphismIdentification k A B := by
  refine ⟨?_, ?_, ?_⟩
  · intro f
    apply AlgHom.ext
    intro x
    rfl
  · intro f
    apply Subtype.ext
    apply RingHom.ext
    intro x
    rfl
  · intro f
    constructor
    · intro h r x
      simp only [Algebra.smul_def, map_mul, h r]
    · intro h r
      calc
        f (algebraMap k A r) = f (r • (1 : A)) :=
          congrArg f (Algebra.algebraMap_eq_smul_one r)
        _ = r • f (1 : A) := h r 1
        _ = algebraMap k B r := by rw [map_one, ← Algebra.algebraMap_eq_smul_one]

/-- Arbitrary ring maps restrict left modules by the stated formula. -/
theorem restrictionAction (R : Type u) (S : Type v) (M : Type w)
    [Ring R] [Ring S] [AddCommGroup M] [Module S M] :
    Spec.restrictionAction R S M := by
  intro u r x
  rfl

/-- Identity and composition laws give the restriction functor on linear maps. -/
theorem restrictionMaps (R : Type u) (S : Type v)
    (M : Type w) (N : Type t) (P : Type*)
    [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module S M] [Module S N] [Module S P] :
    Spec.restrictionMaps R S M N P := by
  intro u
  let _ := restrictModule u M
  let _ := restrictModule u N
  let _ := restrictModule u P
  refine ⟨?_, ?_, ?_⟩
  · intro f x
    rfl
  · apply LinearMap.ext
    intro x
    rfl
  · intro f g
    apply LinearMap.ext
    intro x
    rfl

/-- Restriction is compatible with identity maps and successive changes of rings. -/
theorem restrictionComposition (R : Type u) (S : Type v) (T : Type t) (M : Type w)
    [Ring R] [Ring S] [Ring T] [AddCommGroup M] [Module T M] :
    Spec.restrictionComposition R S T M := by
  constructor
  · exact Module.ext' _ _ (fun _ _ => rfl)
  · intro u v
    exact Module.ext' _ _ (fun _ _ => rfl)

end P103.Ch01.Scalars
