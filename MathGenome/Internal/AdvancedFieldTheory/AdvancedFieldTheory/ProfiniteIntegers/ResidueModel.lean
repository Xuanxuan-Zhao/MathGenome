import MathGenome.Internal.AdvancedFieldTheory.Specs.AdvancedFieldTheory.ProfiniteIntegers.ResidueModel

/-!
# The positive-divisibility residue model of the profinite integers

FT-E06A: the additive group is the literal subtype of compatible families in
∏ n : ℕ+, ZMod n. All topology and group structures are inherited from that
product. The inverse-limit property below holds in topological additive groups.
-/

namespace AdvancedFieldTheory.ProfiniteIntegers

open ResidueSystem

/-- Profinite integers in the residue-family model, including the modulus 1. -/
abbrev Zhat : Type := ResidueFamily

/-- Reduction of residues when the target positive modulus divides the source. -/
def reduce (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)) :
    ZMod (n : ℕ) →+ ZMod (m : ℕ) := reduction m n h

/-- The n-th coordinate additive homomorphism. -/
def π (n : ℕ+) : Zhat →+ ZMod (n : ℕ) := coordinate n

/-- The canonical additive homomorphism from integers to residue families. -/
def ι : ℤ →+ Zhat := integerResidues

@[ext]
theorem ext {a b : Zhat} (h : ∀ n : ℕ+, π n a = π n b) : a = b :=
  Subtype.ext (funext h)

/-- Identity and composition laws for the positive-divisibility residue system. -/
theorem transition_laws : ResidueModelSpec.TransitionLaws := by
  constructor
  · intro n a
    exact congrArg (fun f : ZMod (n : ℕ) →+* ZMod (n : ℕ) => f a)
      ZMod.castHom_self
  · intro l m n hlm hmn a
    exact congrArg (fun f : ZMod (n : ℕ) →+* ZMod (l : ℕ) => f a)
      (ZMod.castHom_comp hlm hmn)

/-- The projections form a compatible cone. -/
theorem coordinate_compatibility : ResidueModelSpec.CoordinateCompatibility :=
  fun a m n h => a.property m n h

@[simp]
theorem π_ι (z : ℤ) (n : ℕ+) : π n (ι z) = (z : ZMod (n : ℕ)) := rfl

theorem integer_coordinates : ResidueModelSpec.IntegerCoordinates := π_ι

/-- The topology is exactly the subspace topology of the product of coordinates. -/
theorem subspace_topology : ResidueModelSpec.SubspaceTopology := rfl

theorem finite_discrete_coordinates : ResidueModelSpec.FiniteDiscreteCoordinates :=
  fun _ => ⟨inferInstance, inferInstance⟩

/-- Each compatibility condition is a closed equalizer of continuous maps. -/
theorem compatibleResidues_closed : ResidueModelSpec.ClosedFamilies := by
  change IsClosed {a : Residues | ∀ (m n : ℕ+) (h : (m : ℕ) ∣ (n : ℕ)),
    reduction m n h (a n) = a m}
  simp only [Set.ofPred_forall]
  refine isClosed_iInter fun m => isClosed_iInter fun n => isClosed_iInter fun h => ?_
  exact isClosed_eq
    ((continuous_of_discreteTopology : Continuous (reduction m n h)).comp
      (continuous_apply n))
    (continuous_apply m)

/-- A closed subtype of the product of finite discrete compact spaces is compact. -/
instance instCompactSpace : CompactSpace Zhat :=
  isCompact_iff_compactSpace.mp compatibleResidues_closed.isCompact

theorem zhat_hausdorff : ResidueModelSpec.Hausdorff :=
  (inferInstance : T2Space Zhat)

theorem zhat_topologicalAddGroup : ResidueModelSpec.TopologicalAddGroup :=
  (inferInstance : IsTopologicalAddGroup Zhat)

theorem continuous_π (n : ℕ+) : Continuous (π n) :=
  (continuous_apply n).comp continuous_subtype_val

theorem continuous_projections : ResidueModelSpec.ContinuousProjections := continuous_π

/-- Continuous form of coordinate projection, for maps of inverse-limit cones. -/
def continuousProjection (n : ℕ+) : ContinuousAddMonoidHom Zhat (ZMod (n : ℕ)) where
  toAddMonoidHom := π n
  continuous_toFun := continuous_π n

universe u

/-- Continuity into this inverse limit is precisely coordinatewise continuity. -/
theorem coordinate_continuity : ResidueModelSpec.CoordinateContinuity.{u} := by
  intro X _ f
  constructor
  · intro hf n
    exact (continuous_π n).comp hf
  · intro hf
    exact (continuous_pi hf).subtype_mk (fun x => (f x).property)

/-- Assemble a compatible cone into its unique continuous additive map. -/
def lift {A : Type u} [AddGroup A] [TopologicalSpace A]
    (f : (n : ℕ+) → ContinuousAddMonoidHom A (ZMod (n : ℕ)))
    (h : ∀ (m n : ℕ+) (hmn : (m : ℕ) ∣ (n : ℕ)) (x : A),
      reduce m n hmn (f n x) = f m x) : ContinuousAddMonoidHom A Zhat where
  toFun x := ⟨fun n => f n x, fun m n hmn => h m n hmn x⟩
  map_zero' := by apply ext; intro n; exact map_zero (f n)
  map_add' x y := by apply ext; intro n; exact map_add (f n) x y
  continuous_toFun :=
    (continuous_pi (fun n => (f n).continuous)).subtype_mk _

@[simp]
theorem π_lift {A : Type u} [AddGroup A] [TopologicalSpace A]
    (f : (n : ℕ+) → ContinuousAddMonoidHom A (ZMod (n : ℕ)))
    (h : ∀ (m n : ℕ+) (hmn : (m : ℕ) ∣ (n : ℕ)) (x : A),
      reduce m n hmn (f n x) = f m x) (n : ℕ+) (x : A) :
    π n (lift f h x) = f n x := rfl

/-- The universal property identifies this exact topological additive group as
    the inverse limit of the positive-divisibility residue system. -/
theorem inverse_limit : ResidueModelSpec.InverseLimit.{u} := by
  intro A _ _ f h
  refine ⟨lift f h, fun _ _ => rfl, ?_⟩
  intro F hF
  apply ContinuousAddMonoidHom.ext
  intro x
  apply ext
  intro n
  exact hF n x

end AdvancedFieldTheory.ProfiniteIntegers
