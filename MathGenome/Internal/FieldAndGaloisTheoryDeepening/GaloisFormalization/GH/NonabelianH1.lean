import MathGenome.Internal.FieldAndGaloisTheoryDeepening.Specs.GaloisFormalization.GH.NonabelianH1

/-! Continuous nonabelian degree-one cohomology and its pointed maps. -/

namespace GaloisFormalization.GH.NonabelianH1

open Topology

universe u v w x

section Cocycles

variable {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]
  [TopologicalSpace G] [TopologicalSpace B]

abbrev OrdinaryCocycle : Spec.OrdinaryCocycleType := @Spec.OrdinaryCocycle

abbrev Cocycle : Spec.CocycleType := @Spec.Cocycle

abbrev IsCocycle (c : G → B) : Prop := Spec.IsCocycle c

abbrev Cohomologous (c d : G → B) : Prop := Spec.Cohomologous c d

omit [TopologicalSpace G] [TopologicalSpace B] in
theorem cohomologous_equivalence : Equivalence (Cohomologous (G := G) (B := B)) :=
  Spec.cohomologous_equivalence

def cocycleSetoid : Spec.SetoidType := @Spec.cocycleSetoid

def H1 (G : Type u) (B : Type v) [Group G] [Group B] [MulDistribMulAction G B]
    [TopologicalSpace G] [TopologicalSpace B] : Type (max u v) :=
  Quotient (cocycleSetoid G B)

def OrdinaryH1 (G : Type u) (B : Type v) [Group G] [Group B]
    [MulDistribMulAction G B] : Type (max u v) :=
  Quotient (Spec.ordinaryCocycleSetoid G B)

def trivial : Spec.TrivialType := @Spec.trivial

def classOf : Spec.ClassOfType := @Spec.classOf

def ordinaryClassOf : Spec.OrdinaryClassOfType := @Spec.ordinaryClassOf

/-- The distinguished class represented by the constant identity cocycle. -/
def basepoint : Spec.BasepointType := fun G B _ _ _ _ _ => classOf (trivial G B)

def ordinaryBasepoint : Spec.OrdinaryBasepointType := @Spec.ordinaryBasepoint

instance : Inhabited (H1 G B) := ⟨basepoint G B⟩

instance : Inhabited (OrdinaryH1 G B) := ⟨ordinaryBasepoint G B⟩

theorem Cocycle.continuous (c : Cocycle G B) : Continuous (⇑c) := c.2.1

theorem Cocycle.cocycle (c : Cocycle G B) (g h : G) : c (g * h) = c g * g • c h := c.2.2 g h

@[ext]
theorem Cocycle.ext {c d : Cocycle G B} (h : ∀ g, c g = d g) : c = d :=
  Subtype.ext (funext h)

@[simp]
theorem Cocycle.apply_one (c : Cocycle G B) : c 1 = 1 := by
  have h : c 1 * 1 = c 1 * c 1 := by simpa using c.cocycle 1 1
  exact (mul_left_cancel h).symm

@[simp]
theorem trivial_apply (g : G) : trivial G B g = 1 := rfl

/-- A change by any coefficient produces another continuous cocycle. -/
def twist [DiscreteTopology B] [ContinuousSMul G B] (c : Cocycle G B) (b : B) : Cocycle G B :=
  ⟨fun g => b⁻¹ * c g * g • b,
    by
      let : ContinuousMul B := ⟨continuous_of_discreteTopology⟩
      exact (continuous_const.mul c.continuous).mul (continuous_id.smul continuous_const),
    fun g h => by
      change b⁻¹ * c (g * h) * (g * h) • b =
        b⁻¹ * c g * g • b * g • (b⁻¹ * c h * h • b)
      rw [c.cocycle, mul_smul]
      simp only [smul_mul', smul_inv', mul_assoc, mul_inv_cancel_left]⟩

@[simp]
theorem twist_apply [DiscreteTopology B] [ContinuousSMul G B] (c : Cocycle G B) (b : B) (g : G) :
    twist c b g = b⁻¹ * c g * g • b := rfl

/-- Two representatives have the same class exactly when a coefficient relates them. -/
theorem classOf_eq_iff {c d : Cocycle G B} :
    classOf c = classOf d ↔ ∃ b : B, ∀ g : G, d g = b⁻¹ * c g * g • b :=
  ⟨fun h => Quotient.exact (s := cocycleSetoid G B) h,
    fun h => Quotient.sound (s := cocycleSetoid G B) h⟩

@[simp]
theorem classOf_twist [DiscreteTopology B] [ContinuousSMul G B] (c : Cocycle G B) (b : B) :
    classOf (twist c b) = classOf c :=
  classOf_eq_iff.mpr ⟨b, fun _ => rfl⟩ |>.symm

/-- On a discrete group, an ordinary cocycle has a continuous representative with the same values. -/
def discreteCocycleEquiv : Spec.DiscreteCocycleEquivType := @Spec.discreteCocycleEquiv

/-- Forgetting continuity identifies the pointed sets at every discrete layer. -/
def discreteEquiv : Spec.DiscreteEquivType := @Spec.discreteEquiv

@[simp]
theorem discreteEquiv_classOf [DiscreteTopology G] (c : Cocycle G B) :
    discreteEquiv (classOf c) = ordinaryClassOf ⟨⇑c, c.2.2⟩ := rfl

@[simp]
theorem discreteEquiv_basepoint [DiscreteTopology G] :
    discreteEquiv (basepoint G B) = ordinaryBasepoint G B := rfl

end Cocycles

section Maps

variable {G : Type u} {B : Type v} {H : Type w} {A : Type x}
  [Group G] [Group B] [MulDistribMulAction G B] [TopologicalSpace G] [TopologicalSpace B]
  [Group H] [Group A] [MulDistribMulAction H A] [TopologicalSpace H] [TopologicalSpace A]
  [DiscreteTopology B]

abbrev Compatible (φ : H →* G) (f : B →* A) : Prop := Spec.Compatible φ f

def mapCocycle : Spec.MapCocycleType := @Spec.mapCocycle

@[simp]
theorem mapCocycle_apply (φ : H →* G) (hφ : Continuous φ) (f : B →* A)
    (hf : Compatible φ f) (c : Cocycle G B) (h : H) :
    mapCocycle φ hφ f hf c h = f (c (φ h)) := rfl

/-- Pull back along the group homomorphism and push forward along the coefficient map. -/
def map (φ : H →* G) (hφ : Continuous φ) (f : B →* A) (hf : Compatible φ f) :
    H1 G B → H1 H A :=
  Quotient.lift (fun c => classOf (mapCocycle φ hφ f hf c))
    (fun _ _ h => classOf_eq_iff.mpr (Spec.mapCocycle_cohomologous φ hφ f hf h))

@[simp]
theorem map_classOf (φ : H →* G) (hφ : Continuous φ) (f : B →* A)
    (hf : Compatible φ f) (c : Cocycle G B) :
    map φ hφ f hf (classOf c) = classOf (mapCocycle φ hφ f hf c) := rfl

@[simp]
theorem map_basepoint (φ : H →* G) (hφ : Continuous φ) (f : B →* A) (hf : Compatible φ f) :
    map φ hφ f hf (basepoint G B) = basepoint H A := by
  change classOf (mapCocycle φ hφ f hf (trivial G B)) = classOf (trivial H A)
  congr 1
  apply Cocycle.ext
  intro h
  exact map_one f

end Maps

section Subgroups

variable {G : Type u} {B : Type v} [Group G] [Group B] [MulDistribMulAction G B]

abbrev Fixed : Spec.FixedType := @Spec.Fixed

theorem mem_fixed_iff (U : Subgroup G) (b : B) :
    b ∈ Fixed U B ↔ ∀ g ∈ U, g • b = b :=
  ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g g.2⟩

/-- Normality makes the fixed subgroup stable under the full action. -/
theorem smul_mem_fixed (U : Subgroup G) [U.Normal] (g : G) {b : B} (hb : b ∈ Fixed U B) :
    g • b ∈ Fixed U B :=
  smul_mem_fixedPoints_of_normal (H := U) g hb

@[simp]
theorem coe_quotient_smul_fixed (U : Subgroup G) [U.Normal] (g : G) (b : Fixed U B) :
    (((QuotientGroup.mk' U g) • b : Fixed U B) : B) = g • (b : B) := rfl

variable [TopologicalSpace G] [TopologicalSpace B] [DiscreteTopology B]

/-- The quotient topology gives a continuous action on the fixed coefficients. -/
instance continuousQuotientAction [ContinuousSMul G B] (U : Subgroup G) [U.Normal] :
    ContinuousSMul (G ⧸ U) (Fixed U B) where
  continuous_smul := by
    rw [continuous_prod_of_discrete_right]
    intro b
    apply (QuotientGroup.isQuotientMap_mk U).continuous_iff.mpr
    apply IsInducing.subtypeVal.continuous_iff.mpr
    change Continuous (fun g : G => g • (b : B))
    exact continuous_id.smul continuous_const

def restrict (U : Subgroup G) : H1 G B → H1 U B :=
  map U.subtype continuous_subtype_val (MonoidHom.id B) (fun _ _ => rfl)

def inflate (U : Subgroup G) [U.Normal] : H1 (G ⧸ U) (Fixed U B) → H1 G B :=
  map (QuotientGroup.mk' U) QuotientGroup.continuous_mk (Fixed U B).subtype (fun _ _ => rfl)

@[simp]
theorem restrict_classOf (U : Subgroup G) (c : Cocycle G B) :
    restrict U (classOf c) =
      classOf (mapCocycle U.subtype continuous_subtype_val (MonoidHom.id B) (fun _ _ => rfl) c) :=
  rfl

@[simp]
theorem inflate_classOf (U : Subgroup G) [U.Normal] (c : Cocycle (G ⧸ U) (Fixed U B)) :
    inflate U (classOf c) =
      classOf (mapCocycle (QuotientGroup.mk' U) QuotientGroup.continuous_mk (Fixed U B).subtype
        (fun _ _ => rfl) c) :=
  rfl

@[simp]
theorem restrict_basepoint (U : Subgroup G) : restrict U (basepoint G B) = basepoint U B :=
  map_basepoint _ _ _ _

@[simp]
theorem inflate_basepoint (U : Subgroup G) [U.Normal] :
    inflate U (basepoint (G ⧸ U) (Fixed U B)) = basepoint G B :=
  map_basepoint _ _ _ _

end Subgroups

end GaloisFormalization.GH.NonabelianH1
