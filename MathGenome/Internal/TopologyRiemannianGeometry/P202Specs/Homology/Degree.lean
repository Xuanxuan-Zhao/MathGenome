import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Homology.SpheresDisks
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.PrismHomotopy

/-! Degree on the geometric unit sphere, using the shared augmented integral
singular complex. Scalar action on all classes makes the convention independent
of a generator, including the oriented boundary generators. -/
noncomputable section
open CategoryTheory
namespace P202Specs.Degree
open P202Specs.SingularChains P202Specs.SpheresDisks

abbrev sphereGroup (n : ℕ) := reducedHomology ℤ ℤ (sphere n) (n : ℤ)
abbrev induced (n : ℕ) (f : sphere n ⟶ sphere n) : sphereGroup n ⟶ sphereGroup n :=
  (reducedHomologyFunctor ℤ ℤ (n : ℤ)).map f

/-- The integer is specified by its action on every reduced homology class.
The fallback only makes the expression total; `degreeAction` proves it is never
used for a sphere self-map. No homology calculation is assumed here. -/
def degree (n : ℕ) (f : sphere n ⟶ sphere n) : ℤ := by
  classical
  exact if h : ∃ d : ℤ, ∀ x : sphereGroup n, induced n f x = d • x then h.choose else 0

def degree_type := (n : ℕ) → (sphere n ⟶ sphere n) → ℤ
def degree_value : degree_type := degree

def degreeAction_type : Prop :=
  ∀ (n : ℕ) (f : sphere n ⟶ sphere n),
    (∀ x : sphereGroup n, induced n f x = degree n f • x) ∧
    ∀ d : ℤ, (∀ x : sphereGroup n, induced n f x = d • x) → d = degree n f

/-- All choices of integral coordinate, hence both choices of generator,
give the same integer. In particular this applies to the oriented sphere
coordinate obtained from the oriented simplex boundary. -/
def generatorIndependent_type : Prop :=
  ∀ (n : ℕ) (f : sphere n ⟶ sphere n) (e : sphereGroup n ≃ₗ[ℤ] ℤ),
    degree n f = e (induced n f (e.symm 1))

def homotopyInvariant_type : Prop :=
  ∀ (n : ℕ) (f g : sphere n ⟶ sphere n),
    TopCat.Homotopy f g → degree n f = degree n g

def identity_type : Prop := ∀ n : ℕ, degree n (𝟙 (sphere n)) = 1

def composition_type : Prop :=
  ∀ (n : ℕ) (f g : sphere n ⟶ sphere n),
    degree n (f ≫ g) = degree n g * degree n f

def constantMap (n : ℕ) (p : sphere n) : sphere n ⟶ sphere n :=
  TopCat.ofHom (ContinuousMap.const _ p)

def constant_type : Prop :=
  ∀ (n : ℕ) (p : sphere n), degree n (constantMap n p) = 0

/-- Negation exchanges the two points of the geometric zero-sphere. -/
def interchange : sphere 0 ⟶ sphere 0 :=
  TopCat.ofHom {
    toFun := fun x => ⟨-x.val, by
      simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using x.property⟩
    continuous_toFun := (continuous_neg.comp continuous_subtype_val).subtype_mk (fun x => by
      simpa only [Metric.mem_sphere, dist_zero_right, Function.comp_apply, norm_neg] using x.property) }

def interchange_type : Prop := degree 0 interchange = -1

/-- Explicitly includes both possible constant maps in dimension zero. -/
def zeroSphere_type : Prop :=
  degree 0 (𝟙 (sphere 0)) = 1 ∧ degree 0 interchange = -1 ∧
    ∀ p : sphere 0, degree 0 (constantMap 0 p) = 0

end P202Specs.Degree
