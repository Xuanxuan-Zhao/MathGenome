import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.PV.OperatorRing

namespace GaloisFormalization.PV

universe u v w

/-- A chosen operator on a commutative unital ring. -/
def Operator (kind : OperatorKind) (R : Type u) [CommRing R] : Type u :=
  match kind with
  | .differential => Derivation ℤ R R
  | .difference => R ≃+* R

/-- A field equipped with a differential or difference operator. -/
abbrev OperatorField (kind : OperatorKind) (K : Type u) [Field K] :=
  Operator kind K

namespace Operator

variable {kind : OperatorKind} {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]

/-- Regard a derivation as an operator. -/
def differential (d : Derivation ℤ R R) : Operator .differential R := d

/-- Regard a ring automorphism as an operator. -/
def difference (σ : R ≃+* R) : Operator .difference R := σ

/-- The derivation of a differential operator. -/
def toDerivation (D : Operator .differential R) : Derivation ℤ R R := D

/-- The automorphism of a difference operator. -/
def toRingEquiv (D : Operator .difference R) : R ≃+* R := D

/-- The action of an operator on the ring. -/
def apply (D : Operator kind R) (x : R) : R :=
  match kind, D with
  | .differential, d => (show Derivation ℤ R R from d) x
  | .difference, σ => (show R ≃+* R from σ) x

instance : CoeFun (Operator kind R) (fun _ => R → R) := ⟨apply⟩

@[simp] theorem apply_of_differential (d : Derivation ℤ R R) (x : R) :
    differential d x = d x := rfl

@[simp] theorem apply_of_difference (σ : R ≃+* R) (x : R) :
    difference σ x = σ x := rfl

/-- The zero derivation or the identity automorphism. -/
def trivial (kind : OperatorKind) (R : Type u) [CommRing R] : Operator kind R :=
  match kind with
  | .differential => differential 0
  | .difference => difference (RingEquiv.refl R)

@[simp] theorem trivial_differential_apply (x : R) : trivial .differential R x = 0 := rfl

@[simp] theorem trivial_difference_apply (x : R) : trivial .difference R x = x := rfl

@[simp] theorem map_zero (D : Operator kind R) : D 0 = 0 := by
  cases kind with
  | differential => exact D.toDerivation.map_zero
  | difference => exact D.toRingEquiv.map_zero

@[simp] theorem map_add (D : Operator kind R) (x y : R) : D (x + y) = D x + D y := by
  cases kind with
  | differential => exact D.toDerivation.map_add x y
  | difference => exact D.toRingEquiv.map_add x y

/-- Compatibility with the two chosen operators. -/
def Commutes (D : Operator kind R) (E : Operator kind S) (f : R → S) : Prop :=
  ∀ x, f (D x) = E (f x)

theorem Commutes.id (D : Operator kind R) : D.Commutes D id := fun _ => rfl

theorem Commutes.comp {D : Operator kind R} {E : Operator kind S} {F : Operator kind T}
    {f : R → S} {g : S → T} (hg : E.Commutes F g) (hf : D.Commutes E f) :
    D.Commutes F (g ∘ f) :=
  fun x => (congrArg g (hf x)).trans (hg (f x))

theorem Commutes.inverse {D : Operator kind R} {E : Operator kind S} {f : R ≃ S}
    (hf : D.Commutes E f) : E.Commutes D f.symm := by
  intro y
  apply f.injective
  simpa only [Equiv.apply_symm_apply] using (hf (f.symm y)).symm

theorem Commutes.difference_symm {D : Operator .difference R} {E : Operator .difference S}
    {f : R → S} (hf : D.Commutes E f) (x : R) :
    f (D.toRingEquiv.symm x) = E.toRingEquiv.symm (f x) := by
  apply E.toRingEquiv.injective
  have h := hf (D.toRingEquiv.symm x)
  change f (D.toRingEquiv (D.toRingEquiv.symm x)) = E.toRingEquiv (f (D.toRingEquiv.symm x)) at h
  simpa only [RingEquiv.apply_symm_apply] using h.symm

/-- Operator-compatible unital ring homomorphisms. -/
def RingHom (D : Operator kind R) (E : Operator kind S) :=
  { f : R →+* S // D.Commutes E f }

/-- Operator-compatible ring equivalences. -/
def RingEquiv (D : Operator kind R) (E : Operator kind S) :=
  { f : R ≃+* S // D.Commutes E f }

/-- Operator-compatible algebra homomorphisms over a common base ring. -/
def AlgHom (A : Type w) [CommRing A] [Algebra A R] [Algebra A S]
    (D : Operator kind R) (E : Operator kind S) :=
  { f : R →ₐ[A] S // D.Commutes E f }

/-- Operator-compatible algebra equivalences over a common base ring. -/
def AlgEquiv (A : Type w) [CommRing A] [Algebra A R] [Algebra A S]
    (D : Operator kind R) (E : Operator kind S) :=
  { f : R ≃ₐ[A] S // D.Commutes E f }

/-- An algebra structure whose structure map respects the operators. -/
def IsAlgebra (D : Operator kind R) (E : Operator kind S) [Algebra R S] : Prop :=
  D.Commutes E (algebraMap R S)

/-- An extension via the given algebra map, which is injective and respects the operators. -/
def IsExtension (D : Operator kind R) (E : Operator kind S) [Algebra R S] : Prop :=
  D.IsAlgebra E ∧ Function.Injective (algebraMap R S)

/-- Stability under the derivation, or under the automorphism and its inverse. -/
def IsStable (D : Operator kind R) (s : Set R) : Prop :=
  match kind, D with
  | .differential, d => ∀ ⦃x⦄, x ∈ s → (show Derivation ℤ R R from d) x ∈ s
  | .difference, σ =>
    (∀ ⦃x⦄, x ∈ s → (show R ≃+* R from σ) x ∈ s) ∧
    (∀ ⦃x⦄, x ∈ s → (show R ≃+* R from σ).symm x ∈ s)

theorem IsStable.apply_mem {D : Operator kind R} {s : Set R} (hs : D.IsStable s)
    {x : R} (hx : x ∈ s) : D x ∈ s := by
  cases kind with
  | differential => exact hs hx
  | difference => exact hs.1 hx

theorem IsStable.symm_apply_mem {D : Operator .difference R} {s : Set R} (hs : D.IsStable s)
    {x : R} (hx : x ∈ s) : D.toRingEquiv.symm x ∈ s :=
  hs.2 hx

/-- Unital subrings stable under the operator. -/
def Subring (D : Operator kind R) :=
  { U : _root_.Subring R // D.IsStable (U : Set R) }

/-- Subalgebras stable under the operator. -/
def Subalgebra (A : Type v) [CommRing A] [Algebra A R] (D : Operator kind R) :=
  { U : _root_.Subalgebra A R // D.IsStable (U : Set R) }

/-- Ideals stable under the operator. -/
def Ideal (D : Operator kind R) :=
  { I : _root_.Ideal R // D.IsStable (I : Set R) }

/-- A nonzero ring is operator simple if its stable ideals are zero and the whole ring. -/
def IsSimple (D : Operator kind R) : Prop :=
  Nontrivial R ∧ ∀ I : _root_.Ideal R, D.IsStable (I : Set R) → I = ⊥ ∨ I = ⊤

/-- An element is constant if its derivative vanishes or the automorphism fixes it. -/
def IsConstant (D : Operator kind R) (x : R) : Prop :=
  match kind with
  | .differential => D x = 0
  | .difference => D x = x

/-- The subring of constants of the chosen operator. -/
def constantSubring (D : Operator kind R) : _root_.Subring R :=
  match kind, D with
  | .differential, D =>
    let d := D.toDerivation
    { carrier := {x | d x = 0}
      zero_mem' := d.map_zero
      one_mem' := d.map_one_eq_zero
      add_mem' := fun hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [d.map_add, hx, hy, add_zero]
      mul_mem' := fun hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [d.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
      neg_mem' := fun hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [d.map_neg, hx, neg_zero] }
  | .difference, D => D.toRingEquiv.toRingHom.eqLocus (_root_.RingHom.id R)

@[simp] theorem mem_constantSubring (D : Operator kind R) (x : R) :
    x ∈ D.constantSubring ↔ D.IsConstant x := by
  cases kind <;> rfl

/-- The inclusion of constants, carrying the trivial operator. -/
def constantSubringEmbedding (D : Operator kind R) :
    RingHom (trivial kind D.constantSubring) D :=
  ⟨D.constantSubring.subtype, fun x => by
    have hx := (mem_constantSubring D (x : R)).mp x.property
    cases kind with
    | differential =>
      change 0 = D (x : R)
      exact hx.symm
    | difference =>
      change (x : R) = D (x : R)
      exact hx.symm⟩

theorem constantSubringEmbedding_injective (D : Operator kind R) :
    Function.Injective D.constantSubringEmbedding.val :=
  Subtype.val_injective

theorem Commutes.isConstant {D : Operator kind R} {E : Operator kind S} {f : R →+* S}
    (hf : D.Commutes E f) {x : R} (hx : D.IsConstant x) : E.IsConstant (f x) := by
  cases kind with
  | differential =>
    change D x = 0 at hx
    change E (f x) = 0
    rw [← hf x, hx, f.map_zero]
  | difference =>
    change D x = x at hx
    change E (f x) = f x
    rw [← hf x, hx]

/-- The restriction of a compatible ring map to the constants. -/
def RingHom.mapConstants {D : Operator kind R} {E : Operator kind S} (f : RingHom D E) :
    D.constantSubring →+* E.constantSubring :=
  (f.val.comp D.constantSubring.subtype).codRestrict E.constantSubring fun x =>
    (mem_constantSubring E _).mpr <| f.property.isConstant <|
      (mem_constantSubring D _).mp x.property

section Field

variable {K : Type u} [Field K]

/-- The subfield of constants in an operator field. -/
def constantSubfield (D : OperatorField kind K) : Subfield K where
  toSubring := D.constantSubring
  inv_mem' := by
    intro x hx
    cases kind with
    | differential =>
      change D.toDerivation x = 0 at hx
      change D.toDerivation x⁻¹ = 0
      simp [Derivation.leibniz_inv, hx]
    | difference =>
      change D.toRingEquiv x = x at hx
      change D.toRingEquiv x⁻¹ = x⁻¹
      rw [map_inv₀, hx]

@[simp] theorem mem_constantSubfield (D : OperatorField kind K) (x : K) :
    x ∈ D.constantSubfield ↔ D.IsConstant x :=
  mem_constantSubring D x

/-- The inclusion of the constant subfield, with its trivial operator. -/
def constantSubfieldEmbedding (D : OperatorField kind K) :
    RingHom (trivial kind D.constantSubfield) D :=
  D.constantSubringEmbedding

theorem constantSubfieldEmbedding_injective (D : OperatorField kind K) :
    Function.Injective D.constantSubfieldEmbedding.val :=
  Subtype.val_injective

/-- The default Picard–Vessiot base field assumptions. -/
def IsBaseField (D : OperatorField kind K) : Prop :=
  CharZero K ∧ IsAlgClosed D.constantSubfield

end Field

end Operator
end GaloisFormalization.PV
