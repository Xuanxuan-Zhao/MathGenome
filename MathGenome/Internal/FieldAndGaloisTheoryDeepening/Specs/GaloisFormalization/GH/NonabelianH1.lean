import Mathlib.Data.Quot
import Mathlib.GroupTheory.GroupAction.OfQuotient
import Mathlib.Topology.Algebra.Group.Quotient

/-! The pointed-set model of degree-one continuous nonabelian cohomology. -/

namespace GaloisFormalization.GH.NonabelianH1.Spec

universe u v w x

section Cocycles

variable {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]

/-- The multiplicative inhomogeneous cocycle equation for a left action. -/
def IsCocycle (c : G → B) : Prop := ∀ g h, c (g * h) = c g * g • c h

variable (G B)

/-- Algebraic degree-one cocycles. -/
def OrdinaryCocycle := {c : G → B // IsCocycle c}

instance : CoeFun (OrdinaryCocycle G B) (fun _ => G → B) := ⟨Subtype.val⟩

variable [TopologicalSpace G] [TopologicalSpace B]

/-- Continuous degree-one cocycles. -/
def Cocycle := {c : G → B // Continuous c ∧ IsCocycle c}

instance : CoeFun (Cocycle G B) (fun _ => G → B) := ⟨Subtype.val⟩

variable {G B}

/-- Change a representative by an element of the coefficient group. -/
def twistFunction (c : G → B) (b : B) (g : G) : B := b⁻¹ * c g * g • b

/-- The exact orbit relation of the paper, written on underlying functions. -/
def Cohomologous (c d : G → B) : Prop := ∃ b : B, ∀ g : G, d g = twistFunction c b g

omit [TopologicalSpace G] [TopologicalSpace B] in
theorem cohomologous_equivalence : Equivalence (Cohomologous (G := G) (B := B)) where
  refl c := ⟨1, fun g => by simp [twistFunction]⟩
  symm := by
    rintro c d ⟨b, hb⟩
    refine ⟨b⁻¹, fun g => ?_⟩
    rw [twistFunction, hb g, twistFunction, smul_inv']
    simp [mul_assoc]
  trans := by
    rintro c d e ⟨b, hb⟩ ⟨a, ha⟩
    refine ⟨b * a, fun g => ?_⟩
    rw [ha g, twistFunction, hb g, twistFunction, twistFunction, mul_inv_rev, smul_mul']
    simp only [mul_assoc]

variable (G B)

/-- The continuous cocycle setoid with precisely the prescribed relation. -/
def cocycleSetoid : Setoid (Cocycle G B) where
  r := fun c d => Cohomologous (⇑c) (⇑d)
  iseqv :=
    ⟨fun _ => cohomologous_equivalence.refl _,
      fun h => cohomologous_equivalence.symm h,
      fun h₁ h₂ => cohomologous_equivalence.trans h₁ h₂⟩

/-- The same cocycle setoid without the continuity condition. -/
def ordinaryCocycleSetoid : Setoid (OrdinaryCocycle G B) where
  r := fun c d => Cohomologous (⇑c) (⇑d)
  iseqv :=
    ⟨fun _ => cohomologous_equivalence.refl _,
      fun h => cohomologous_equivalence.symm h,
      fun h₁ h₂ => cohomologous_equivalence.trans h₁ h₂⟩

/-- The two quotients use the same change of representative formula. -/
def H1 := Quotient (cocycleSetoid G B)

def OrdinaryH1 := Quotient (ordinaryCocycleSetoid G B)

def trivial : Cocycle G B :=
  ⟨fun _ => 1, continuous_const, fun g _ => by rw [smul_one, one_mul]⟩

def ordinaryTrivial : OrdinaryCocycle G B :=
  ⟨fun _ => 1, fun g _ => by rw [smul_one, one_mul]⟩

def basepoint : H1 G B := Quotient.mk (cocycleSetoid G B) (trivial G B)

def ordinaryBasepoint : OrdinaryH1 G B :=
  Quotient.mk (ordinaryCocycleSetoid G B) (ordinaryTrivial G B)

variable {G B}

def classOf : Cocycle G B → H1 G B := Quotient.mk (cocycleSetoid G B)

def ordinaryClassOf : OrdinaryCocycle G B → OrdinaryH1 G B :=
  Quotient.mk (ordinaryCocycleSetoid G B)

/-- The continuous cocycle obtained by changing representative. -/
def twist [DiscreteTopology B] [ContinuousSMul G B] (c : Cocycle G B) (b : B) : Cocycle G B :=
  ⟨twistFunction (⇑c) b,
    by
      let : ContinuousMul B := ⟨continuous_of_discreteTopology⟩
      exact (continuous_const.mul c.2.1).mul (continuous_id.smul continuous_const),
    fun g h => by
      change b⁻¹ * c (g * h) * (g * h) • b =
        b⁻¹ * c g * g • b * g • (b⁻¹ * c h * h • b)
      rw [c.2.2 g h, mul_smul, smul_mul', smul_mul', smul_inv']
      simp [mul_assoc]⟩

/-- Forgetting continuity gives all ordinary cocycles on a discrete group. -/
def discreteCocycleEquiv [DiscreteTopology G] : Cocycle G B ≃ OrdinaryCocycle G B where
  toFun c := ⟨⇑c, c.2.2⟩
  invFun c := ⟨⇑c, continuous_of_discreteTopology, c.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The ordinary pointed set at a discrete layer. -/
def discreteEquiv [DiscreteTopology G] : H1 G B ≃ OrdinaryH1 G B :=
  Quotient.congr discreteCocycleEquiv (fun _ _ => Iff.rfl)

end Cocycles

section Maps

variable {G : Type u} {B : Type v} {H : Type w} {A : Type x}
  [Group G] [Group B] [MulDistribMulAction G B] [TopologicalSpace G] [TopologicalSpace B]
  [Group H] [Group A] [MulDistribMulAction H A] [TopologicalSpace H] [TopologicalSpace A]

/-- Equivariance when the target acting group maps to the source acting group. -/
def Compatible (φ : H →* G) (f : B →* A) : Prop :=
  ∀ h b, f (φ h • b) = h • f b

/-- Pull back the group argument and apply the equivariant map to the coefficient. -/
def mapCocycle [DiscreteTopology B] (φ : H →* G) (hφ : Continuous φ)
    (f : B →* A) (hf : Compatible φ f) (c : Cocycle G B) : Cocycle H A :=
  ⟨fun h => f (c (φ h)), continuous_of_discreteTopology.comp (c.2.1.comp hφ),
    fun h k => by
      change f (c (φ (h * k))) = f (c (φ h)) * h • f (c (φ k))
      rw [map_mul, c.2.2, map_mul, hf]⟩

theorem mapCocycle_cohomologous [DiscreteTopology B] (φ : H →* G) (hφ : Continuous φ)
    (f : B →* A) (hf : Compatible φ f) {c d : Cocycle G B}
    (h : (cocycleSetoid G B).r c d) :
    (cocycleSetoid H A).r (mapCocycle φ hφ f hf c) (mapCocycle φ hφ f hf d) := by
  obtain ⟨b, hb⟩ := h
  refine ⟨f b, fun g => ?_⟩
  change f (d (φ g)) = (f b)⁻¹ * f (c (φ g)) * g • f b
  rw [hb, twistFunction, map_mul, map_mul, map_inv, hf]

/-- The map of classes induced by precomposition and postcomposition. -/
def map [DiscreteTopology B] (φ : H →* G) (hφ : Continuous φ)
    (f : B →* A) (hf : Compatible φ f) : H1 G B → H1 H A :=
  @Quotient.map _ _ (cocycleSetoid G B) (cocycleSetoid H A)
    (mapCocycle φ hφ f hf) (fun _ _ => mapCocycle_cohomologous φ hφ f hf)

end Maps

section Subgroups

/-- The coefficient subgroup fixed by the acting subgroup. -/
abbrev Fixed {G : Type u} [Group G] (U : Subgroup G) (B : Type v) [Group B]
    [MulDistribMulAction G B] : Subgroup B :=
  FixedPoints.subgroup U B

variable {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]

/-- The inclusion of fixed coefficients is equivariant over the quotient homomorphism. -/
theorem inflationCompatible (U : Subgroup G) [U.Normal] :
    Compatible (QuotientGroup.mk' U) (Fixed U B).subtype :=
  fun _ _ => rfl

variable [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B]

def restrict (U : Subgroup G) : H1 G B → H1 U B :=
  map U.subtype continuous_subtype_val (MonoidHom.id B) (fun _ _ => rfl)

def inflate (U : Subgroup G) [U.Normal] : H1 (G ⧸ U) (Fixed U B) → H1 G B :=
  map (QuotientGroup.mk' U) QuotientGroup.continuous_mk (Fixed U B).subtype (inflationCompatible U)

end Subgroups

/-! Expected declaration types and properties. The input universes vary independently. -/

set_option linter.checkUnivs false

def OrdinaryCocycleType := ∀ (G : Type u) (B : Type v) [Group G] [Group B]
  [MulDistribMulAction G B], Type (max u v)

def CocycleType := ∀ (G : Type u) (B : Type v) [Group G] [Group B]
  [MulDistribMulAction G B] [TopologicalSpace G] [TopologicalSpace B], Type (max u v)

def IsCocycleType := ∀ {G : Type u} {B : Type v} [Group G] [Group B]
  [MulDistribMulAction G B], (G → B) → Prop

def CohomologousType := ∀ {G : Type u} {B : Type v} [Group G] [Group B]
  [MulDistribMulAction G B], (G → B) → (G → B) → Prop

def CohomologousEquivalence : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B],
    Equivalence (Cohomologous (G := G) (B := B))

def SetoidType := ∀ (G : Type u) (B : Type v) [Group G] [Group B] [MulDistribMulAction G B]
  [TopologicalSpace G] [TopologicalSpace B], Setoid (Cocycle G B)

def TrivialType := ∀ (G : Type u) (B : Type v) [Group G] [Group B] [MulDistribMulAction G B]
  [TopologicalSpace G] [TopologicalSpace B], Cocycle G B

def BasepointType := ∀ (G : Type u) (B : Type v) [Group G] [Group B] [MulDistribMulAction G B]
  [TopologicalSpace G] [TopologicalSpace B], H1 G B

def OrdinaryBasepointType := ∀ (G : Type u) (B : Type v) [Group G] [Group B]
  [MulDistribMulAction G B], OrdinaryH1 G B

def OrdinaryClassOfType := ∀ {G : Type u} {B : Type v} [Group G] [Group B]
  [MulDistribMulAction G B], OrdinaryCocycle G B → OrdinaryH1 G B

def ClassOfType := ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
  [TopologicalSpace G] [TopologicalSpace B], Cocycle G B → H1 G B

def TwistType := ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
  [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B],
  Cocycle G B → B → Cocycle G B

def TwistFormula : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
    (c : Cocycle G B) (b : B) (g : G), twist c b g = b⁻¹ * c g * g • b

def ClassEquality : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] {c d : Cocycle G B},
    classOf c = classOf d ↔ ∃ b : B, ∀ g : G, d g = b⁻¹ * c g * g • b

def DiscreteCocycleEquivType :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology G],
    Cocycle G B ≃ OrdinaryCocycle G B

def DiscreteEquivType := ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
  [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology G], H1 G B ≃ OrdinaryH1 G B

def DiscreteRepresentative : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology G] (c : Cocycle G B),
    discreteEquiv (classOf c) = ordinaryClassOf ⟨⇑c, c.2.2⟩

def DiscreteBasepoint : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology G],
    discreteEquiv (basepoint G B) = ordinaryBasepoint G B

def MapCocycleType :=
  ∀ {G : Type u} {B : Type v} {H : Type w} {A : Type x}
    [Group G] [Group B] [MulDistribMulAction G B] [TopologicalSpace G] [TopologicalSpace B]
    [Group H] [Group A] [MulDistribMulAction H A] [TopologicalSpace H] [TopologicalSpace A]
    [DiscreteTopology B] (φ : H →* G) (_ : Continuous φ) (f : B →* A) (_ : Compatible φ f),
    Cocycle G B → Cocycle H A

def MapCocycleFormula : Prop :=
  ∀ {G : Type u} {B : Type v} {H : Type w} {A : Type x}
    [Group G] [Group B] [MulDistribMulAction G B] [TopologicalSpace G] [TopologicalSpace B]
    [Group H] [Group A] [MulDistribMulAction H A] [TopologicalSpace H] [TopologicalSpace A]
    [DiscreteTopology B] (φ : H →* G) (hφ : Continuous φ) (f : B →* A) (hf : Compatible φ f)
    (c : Cocycle G B) (h : H), mapCocycle φ hφ f hf c h = f (c (φ h))

def MapType :=
  ∀ {G : Type u} {B : Type v} {H : Type w} {A : Type x}
    [Group G] [Group B] [MulDistribMulAction G B] [TopologicalSpace G] [TopologicalSpace B]
    [Group H] [Group A] [MulDistribMulAction H A] [TopologicalSpace H] [TopologicalSpace A]
    [DiscreteTopology B] (φ : H →* G) (_ : Continuous φ) (f : B →* A) (_ : Compatible φ f),
    H1 G B → H1 H A

def MapRepresentative : Prop :=
  ∀ {G : Type u} {B : Type v} {H : Type w} {A : Type x}
    [Group G] [Group B] [MulDistribMulAction G B] [TopologicalSpace G] [TopologicalSpace B]
    [Group H] [Group A] [MulDistribMulAction H A] [TopologicalSpace H] [TopologicalSpace A]
    [DiscreteTopology B] (φ : H →* G) (hφ : Continuous φ) (f : B →* A) (hf : Compatible φ f)
    (c : Cocycle G B),
    map φ hφ f hf (classOf c) = classOf (mapCocycle φ hφ f hf c)

def MapBasepoint : Prop :=
  ∀ {G : Type u} {B : Type v} {H : Type w} {A : Type x}
    [Group G] [Group B] [MulDistribMulAction G B] [TopologicalSpace G] [TopologicalSpace B]
    [Group H] [Group A] [MulDistribMulAction H A] [TopologicalSpace H] [TopologicalSpace A]
    [DiscreteTopology B] (φ : H →* G) (hφ : Continuous φ) (f : B →* A) (hf : Compatible φ f),
    map φ hφ f hf (basepoint G B) = basepoint H A

def FixedType := ∀ {G : Type u} [Group G] (_ : Subgroup G) (B : Type v) [Group B]
  [MulDistribMulAction G B], Subgroup B

def FixedMembership : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    (U : Subgroup G) (b : B), b ∈ Fixed U B ↔ ∀ g ∈ U, g • b = b

def FixedStable : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    (U : Subgroup G) [U.Normal] (g : G) {b : B}, b ∈ Fixed U B → g • b ∈ Fixed U B

def QuotientActionFormula : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    (U : Subgroup G) [U.Normal] (g : G) (b : Fixed U B),
    (((QuotientGroup.mk' U g) • b : Fixed U B) : B) = g • (b : B)

def ContinuousQuotientAction : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B] [ContinuousSMul G B]
    (U : Subgroup G) [U.Normal], ContinuousSMul (G ⧸ U) (Fixed U B)

def RestrictType :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B] (U : Subgroup G),
    H1 G B → H1 U B

def InflateType :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B] (U : Subgroup G) [U.Normal],
    H1 (G ⧸ U) (Fixed U B) → H1 G B

def RestrictRepresentative : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B] (U : Subgroup G)
    (c : Cocycle G B),
    restrict U (classOf c) =
      classOf (mapCocycle U.subtype continuous_subtype_val (MonoidHom.id B) (fun _ _ => rfl) c)

def InflateRepresentative : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B] (U : Subgroup G) [U.Normal]
    (c : Cocycle (G ⧸ U) (Fixed U B)),
    inflate U (classOf c) =
      classOf (mapCocycle (QuotientGroup.mk' U) QuotientGroup.continuous_mk (Fixed U B).subtype
        (inflationCompatible U) c)

def RestrictBasepoint : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B] (U : Subgroup G),
    restrict U (basepoint G B) = basepoint U B

def InflateBasepoint : Prop :=
  ∀ {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B] (U : Subgroup G) [U.Normal],
    inflate U (basepoint (G ⧸ U) (Fixed U B)) = basepoint G B

end GaloisFormalization.GH.NonabelianH1.Spec
