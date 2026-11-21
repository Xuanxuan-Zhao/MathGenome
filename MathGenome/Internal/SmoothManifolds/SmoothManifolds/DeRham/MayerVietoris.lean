import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.DeRham.MayerVietoris
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch05.Frames
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Localization.Partitions
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.DeRham.Algebra

/-! The open-cover Mayer–Vietoris sequence on the genuine smooth exterior
sections. Restriction and the overlap difference have sign `q(a,b)=b-a`.
The algebraic connecting construction is proved for arbitrary short exact
sequences; the geometric realization is constructed using local smooth germs
and closed-support subordinate partitions. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace SmoothManifolds.MayerVietorisData
universe u
namespace Cochain
variable (A : Cochain.{u})

@[simp] theorem class_zero_iff (k : ℕ) (x : A.closed k) :
    A.classOf k x = 0 ↔ x.val ∈ A.exact k :=
  Submodule.Quotient.mk_eq_zero _

theorem class_surjective (k : ℕ) : Function.Surjective (A.classOf k) :=
  (A.boundaries k).mkQ_surjective

/-- Every differential is a closed form and represents zero cohomology. -/
def boundary (k : ℕ) (x : A.Obj k) : A.closed (k+1) :=
  ⟨A.d k x, A.square k x⟩

@[simp] theorem class_boundary (k : ℕ) (x : A.Obj k) :
    A.classOf (k+1) (A.boundary k x) = 0 :=
  (A.class_zero_iff _ _).mpr ⟨x, rfl⟩

theorem class_eq_iff (k : ℕ) (x y : A.closed k) :
    A.classOf k x = A.classOf k y ↔ (x-y).val ∈ A.exact k := by
  rw [← sub_eq_zero, ← map_sub, A.class_zero_iff]

end Cochain
namespace ChainMap
variable {A B : Cochain.{u}} (f : ChainMap A B)

theorem maps_exact (k : ℕ) (x : A.Obj k) (hx : x ∈ A.exact k) :
    f.map k x ∈ B.exact k := by
  cases k with
  | zero =>
    have : x = 0 := hx
    simp [this]
  | succ k =>
    obtain ⟨y, rfl⟩ := hx
    exact ⟨f.map k y, f.comm k y⟩

def onH (k : ℕ) : A.H k →ₗ[ℝ] B.H k :=
  (A.boundaries k).liftQ ((B.classOf k).comp (f.onClosed k)) (by
    intro x hx
    change B.classOf k (f.onClosed k x) = 0
    exact (B.class_zero_iff _ _).mpr (f.maps_exact k x.val hx))

@[simp] theorem onH_class (k : ℕ) (x : A.closed k) :
    f.onH k (A.classOf k x) = B.classOf k (f.onClosed k x) := rfl

theorem onH_induced : IsInduced f f.onH := fun _ _ => rfl

theorem induced_unique (F : ∀ k, A.H k →ₗ[ℝ] B.H k) (hF : IsInduced f F) :
    F = f.onH := by
  funext k
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := A.class_surjective k x
  exact hF k x

end ChainMap
namespace ShortExact
variable {A B C : Cochain.{u}} (E : ShortExact A B C)

theorem qr_zero (k : ℕ) (a : A.Obj k) : E.q.map k (E.r.map k a) = 0 :=
  (E.exact k _).mpr ⟨a, rfl⟩

/-- A lift of a closed form has a unique closed descending derivative. -/
theorem lift_exists (k : ℕ) (c : C.closed k) :
    ∃ b : B.Obj k, ∃ a : A.closed (k+1),
      E.q.map k b = c.val ∧ E.r.map (k+1) a.val = B.d k b := by
  obtain ⟨b, hb⟩ := E.surjective k c.val
  obtain ⟨a, ha⟩ := (E.exact (k+1) (B.d k b)).mp (by
    rw [← E.q.comm, hb]
    exact c.property)
  have hclosed : A.d (k+1) a = 0 := by
    apply E.injective (k+2)
    rw [map_zero, ← E.r.comm, ha, B.square]
  exact ⟨b, ⟨a, hclosed⟩, hb, ha⟩

/-- Independence of the choice of lift, before taking the quotient on inputs. -/
theorem lift_class_unique (k : ℕ) (c : C.closed k)
    (b b' : B.Obj k) (a a' : A.closed (k+1))
    (hb : E.q.map k b = c.val) (hb' : E.q.map k b' = c.val)
    (ha : E.r.map (k+1) a.val = B.d k b)
    (ha' : E.r.map (k+1) a'.val = B.d k b') :
    A.classOf (k+1) a = A.classOf (k+1) a' := by
  obtain ⟨v, hv⟩ := (E.exact k (b-b')).mp (by rw [map_sub, hb, hb', sub_self])
  apply (A.class_eq_iff _ _ _).mpr
  refine ⟨v, ?_⟩
  apply E.injective (k+1)
  change E.r.map (k+1) (A.d k v) = E.r.map (k+1) (a.val-a'.val)
  rw [← E.r.comm, hv, map_sub, map_sub, ha, ha']

private def chosenLift (k : ℕ) (c : C.closed k) : B.Obj k :=
  (E.lift_exists k c).choose
private def chosenDescent (k : ℕ) (c : C.closed k) : A.closed (k+1) :=
  (E.lift_exists k c).choose_spec.choose
private theorem chosen_properties (k : ℕ) (c : C.closed k) :
    E.q.map k (E.chosenLift k c) = c.val ∧
      E.r.map (k+1) (E.chosenDescent k c).val = B.d k (E.chosenLift k c) :=
  (E.lift_exists k c).choose_spec.choose_spec

/-- The connecting class on closed forms. -/
def deltaClosed (k : ℕ) : C.closed k →ₗ[ℝ] A.H (k+1) where
  toFun c := A.classOf (k+1) (E.chosenDescent k c)
  map_add' c c' := by
    rw [← map_add]
    exact E.lift_class_unique k (c+c')
      (E.chosenLift k (c+c')) (E.chosenLift k c + E.chosenLift k c')
      (E.chosenDescent k (c+c')) (E.chosenDescent k c + E.chosenDescent k c')
      (E.chosen_properties k (c+c')).1
      (by simp only [map_add, (E.chosen_properties k c).1,
        (E.chosen_properties k c').1, Submodule.coe_add])
      (E.chosen_properties k (c+c')).2
      (by simp only [Submodule.coe_add, map_add, (E.chosen_properties k c).2,
        (E.chosen_properties k c').2])
  map_smul' r c := by
    rw [RingHom.id_apply, ← map_smul]
    exact E.lift_class_unique k (r • c)
      (E.chosenLift k (r • c)) (r • E.chosenLift k c)
      (E.chosenDescent k (r • c)) (r • E.chosenDescent k c)
      (E.chosen_properties k (r • c)).1
      (by simp only [map_smul, (E.chosen_properties k c).1, Submodule.coe_smul])
      (E.chosen_properties k (r • c)).2
      (by simp only [Submodule.coe_smul, map_smul, (E.chosen_properties k c).2])

theorem deltaClosed_eq (k : ℕ) (c : C.closed k) (b : B.Obj k)
    (a : A.closed (k+1)) (hb : E.q.map k b = c.val)
    (ha : E.r.map (k+1) a.val = B.d k b) :
    E.deltaClosed k c = A.classOf (k+1) a :=
  E.lift_class_unique k c _ b _ a (E.chosen_properties k c).1 hb
    (E.chosen_properties k c).2 ha

theorem deltaClosed_boundary (k : ℕ) (c : C.closed k) (hc : c ∈ C.boundaries k) :
    E.deltaClosed k c = 0 := by
  cases k with
  | zero =>
    have hz : c.val = 0 := hc
    have : c = 0 := Subtype.ext hz
    rw [this, map_zero]
  | succ k =>
    obtain ⟨c₀, hc₀⟩ := hc
    obtain ⟨b₀, hb₀⟩ := E.surjective k c₀
    rw [E.deltaClosed_eq (k+1) c (B.d k b₀) 0
      (by rw [← E.q.comm, hb₀, hc₀]; rfl)
      (by simpa using (B.square k b₀).symm), map_zero]

/-- δ descends through exact forms, so it is independent of representatives. -/
def delta (k : ℕ) : C.H k →ₗ[ℝ] A.H (k+1) :=
  (C.boundaries k).liftQ (E.deltaClosed k) (by
    intro c hc
    exact E.deltaClosed_boundary k c hc)

@[simp] theorem delta_class (k : ℕ) (c : C.closed k) :
    E.delta k (C.classOf k c) = E.deltaClosed k c := rfl

theorem delta_connecting : IsConnecting E E.delta := by
  intro k c b a hb ha
  exact E.deltaClosed_eq k c b a hb ha

/-- The representative formula makes the connecting family unique. -/
theorem connecting_unique (δ : ∀ k, C.H k →ₗ[ℝ] A.H (k+1))
    (hδ : IsConnecting E δ) : δ = E.delta := by
  funext k
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := C.class_surjective k x
  obtain ⟨b, a, hb, ha⟩ := E.lift_exists k c
  rw [hδ k c b a hb ha, E.delta_connecting k c b a hb ha]

/-- Exact forms are closed, including the zero degree convention. -/
theorem exact_closed (X : Cochain.{u}) (k : ℕ) (x : X.Obj k)
    (hx : x ∈ X.exact k) : X.d k x = 0 := by
  cases k with
  | zero =>
    have : x = 0 := hx
    rw [this, map_zero]
  | succ k =>
    obtain ⟨v, rfl⟩ := hx
    exact X.square k v

/-- A primitive can be lifted, so boundaries lift to boundaries. -/
theorem lift_exact (k : ℕ) (c : C.Obj k) (hc : c ∈ C.exact k) :
    ∃ b : B.Obj k, b ∈ B.exact k ∧ E.q.map k b = c := by
  cases k with
  | zero =>
    have : c = 0 := hc
    exact ⟨0, (B.exact 0).zero_mem, by simp [this]⟩
  | succ k =>
    obtain ⟨v, rfl⟩ := hc
    obtain ⟨w, hw⟩ := E.surjective k v
    exact ⟨B.d k w, ⟨w, rfl⟩, by rw [← E.q.comm, hw]⟩

/-- Exactness at the middle cohomology group in every degree. -/
theorem exact_at_middle (k : ℕ) (y : B.H k) :
    E.q.onH k y = 0 ↔ ∃ x, E.r.onH k x = y := by
  obtain ⟨b, rfl⟩ := B.class_surjective k y
  constructor
  · intro hy
    have hqb : E.q.map k b.val ∈ C.exact k :=
      (C.class_zero_iff _ _).mp hy
    obtain ⟨t, ht, hqt⟩ := E.lift_exact k _ hqb
    obtain ⟨a, ha⟩ := (E.exact k (b.val-t)).mp (by rw [map_sub, hqt, sub_self])
    have haClosed : A.d k a = 0 := by
      apply E.injective (k+1)
      rw [map_zero, ← E.r.comm, ha, map_sub,
        show B.d k b.val = 0 from b.property, exact_closed B k t ht, sub_self]
    refine ⟨A.classOf k ⟨a, haClosed⟩, ?_⟩
    apply (B.class_eq_iff _ _ _).mpr
    change E.r.map k a - b.val ∈ B.exact k
    rw [ha]
    convert (B.exact k).neg_mem ht using 1; abel
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := A.class_surjective k x
    rw [← hx, ChainMap.onH_class, ChainMap.onH_class]
    apply (C.class_zero_iff _ _).mpr
    change E.q.map k (E.r.map k a.val) ∈ C.exact k
    rw [E.qr_zero]
    exact (C.exact k).zero_mem

/-- Exactness at the overlap cohomology group. -/
theorem exact_at_right (k : ℕ) (z : C.H k) :
    E.delta k z = 0 ↔ ∃ y, E.q.onH k y = z := by
  obtain ⟨c, rfl⟩ := C.class_surjective k z
  constructor
  · intro hz
    obtain ⟨b, a, hb, ha⟩ := E.lift_exists k c
    rw [E.delta_connecting k c b a hb ha] at hz
    obtain ⟨v, hv⟩ := (A.class_zero_iff _ _).mp hz
    have hclosed : B.d k (b-E.r.map k v) = 0 := by
      rw [map_sub, E.r.comm, hv, ← ha, sub_self]
    refine ⟨B.classOf k ⟨b-E.r.map k v, hclosed⟩, ?_⟩
    rw [ChainMap.onH_class]
    congr 1
    apply Subtype.ext
    exact (map_sub _ _ _).trans (by rw [hb, E.qr_zero, sub_zero])
  · rintro ⟨y, hy⟩
    obtain ⟨b, rfl⟩ := B.class_surjective k y
    rw [← hy]
    exact (E.delta_connecting k (E.q.onClosed k b) b.val 0 rfl
      (by simpa using b.property.symm)).trans (map_zero _)

/-- Exactness at the manifold group in every positive degree. -/
theorem exact_at_left (k : ℕ) (x : A.H (k+1)) :
    E.r.onH (k+1) x = 0 ↔ ∃ z, E.delta k z = x := by
  obtain ⟨a, rfl⟩ := A.class_surjective (k+1) x
  constructor
  · intro hx
    obtain ⟨b, hb⟩ := (B.class_zero_iff _ _).mp hx
    have hc : C.d k (E.q.map k b) = 0 := by
      rw [E.q.comm, hb]
      exact E.qr_zero (k+1) a.val
    exact ⟨C.classOf k ⟨E.q.map k b, hc⟩,
      E.delta_connecting k _ b a rfl hb.symm⟩
  · rintro ⟨z, hz⟩
    obtain ⟨c, rfl⟩ := C.class_surjective k z
    obtain ⟨b, a', hb, ha'⟩ := E.lift_exists k c
    rw [← hz, E.delta_connecting k c b a' hb ha', ChainMap.onH_class]
    exact (B.class_zero_iff _ _).mpr ⟨b, ha'.symm⟩

/-- The sequence begins with an injection in degree zero. -/
theorem initial_injective : Function.Injective (E.r.onH 0) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := A.class_surjective 0 x
  obtain ⟨a', rfl⟩ := A.class_surjective 0 y
  have hzero := (B.class_eq_iff 0 _ _).mp hxy
  have hv : E.r.map 0 a.val - E.r.map 0 a'.val = 0 := hzero
  have he : a = a' := Subtype.ext (E.injective 0 (sub_eq_zero.mp hv))
  rw [he]

theorem long_exact : IsLongExact E E.r.onH E.q.onH E.delta :=
  ⟨E.initial_injective, E.exact_at_middle, E.exact_at_right, E.exact_at_left⟩

end ShortExact
namespace SequenceMap
variable {A B C A' B' C' : Cochain.{u}}
  {E : ShortExact A B C} {E' : ShortExact A' B' C'} (F : SequenceMap E E')

/-- Naturality follows by applying a chain map to any lift, with no
compatibility condition on the choices used to construct either δ. -/
theorem delta_natural (k : ℕ) (z : C.H k) :
    F.left.onH (k+1) (E.delta k z) = E'.delta k (F.right.onH k z) := by
  obtain ⟨c, rfl⟩ := C.class_surjective k z
  obtain ⟨b, a, hb, ha⟩ := E.lift_exists k c
  rw [E.delta_connecting k c b a hb ha, ChainMap.onH_class, ChainMap.onH_class]
  symm
  apply E'.delta_connecting k _ (F.middle.map k b) (F.left.onClosed (k+1) a)
  · change E'.q.map k (F.middle.map k b) = F.right.map k c.val
    rw [← F.comm_q, hb]
  · change E'.r.map (k+1) (F.left.map (k+1) a.val) = B'.d k (F.middle.map k b)
    rw [← F.comm_r, ha, F.middle.comm]

theorem r_natural (k : ℕ) (x : A.H k) :
    F.middle.onH k (E.r.onH k x) = E'.r.onH k (F.left.onH k x) := by
  obtain ⟨a, rfl⟩ := A.class_surjective k x
  simp only [ChainMap.onH_class]
  congr 1
  exact Subtype.ext (F.comm_r k a.val)

theorem q_natural (k : ℕ) (x : B.H k) :
    F.right.onH k (E.q.onH k x) = E'.q.onH k (F.middle.onH k x) := by
  obtain ⟨b, rfl⟩ := B.class_surjective k x
  simp only [ChainMap.onH_class]
  congr 1
  exact Subtype.ext (F.comm_q k b.val)

end SequenceMap
namespace Cochain
variable (A B : Cochain.{u})

/-- The canonical map from the cohomology of a product to the product of
cohomologies. -/
def productHMap (k : ℕ) : (A.prod B).H k →ₗ[ℝ] (A.H k × B.H k) :=
  ((ChainMap.fst A B).onH k).prod ((ChainMap.snd A B).onH k)

private theorem product_exact_iff (k : ℕ) (x : A.Obj k × B.Obj k) :
    x ∈ (A.prod B).exact k ↔ x.1 ∈ A.exact k ∧ x.2 ∈ B.exact k := by
  cases k with
  | zero =>
    change x = 0 ↔ x.1 = 0 ∧ x.2 = 0
    exact Prod.ext_iff
  | succ k =>
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨⟨v.1, rfl⟩, ⟨v.2, rfl⟩⟩
    · rintro ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
      exact ⟨(v,w), Prod.ext hv hw⟩

theorem productHMap_injective (k : ℕ) : Function.Injective (A.productHMap B k) := by
  intro x y hxy
  obtain ⟨x, rfl⟩ := (A.prod B).class_surjective k x
  obtain ⟨y, rfl⟩ := (A.prod B).class_surjective k y
  apply ((A.prod B).class_eq_iff k x y).mpr
  apply (A.product_exact_iff B k _).mpr
  exact ⟨(A.class_eq_iff k _ _).mp (congrArg Prod.fst hxy),
    (B.class_eq_iff k _ _).mp (congrArg Prod.snd hxy)⟩

theorem productHMap_surjective (k : ℕ) : Function.Surjective (A.productHMap B k) := by
  rintro ⟨x,y⟩
  obtain ⟨a, rfl⟩ := A.class_surjective k x
  obtain ⟨b, rfl⟩ := B.class_surjective k y
  let c : (A.prod B).closed k := ⟨(a.val,b.val), Prod.ext a.property b.property⟩
  exact ⟨(A.prod B).classOf k c, rfl⟩

/-- The middle cohomology in the long sequence really is H(U) ⊕ H(V). -/
def productHEquiv (k : ℕ) : (A.prod B).H k ≃ₗ[ℝ] (A.H k × B.H k) :=
  LinearEquiv.ofBijective (A.productHMap B k)
    ⟨A.productHMap_injective B k, A.productHMap_surjective B k⟩

end Cochain
namespace OpenForms
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  MapData Set
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {k : ℕ}

/-- Pointwise gluing with no nonemptiness assumption on either open set. -/
def glueField (O : OpenCover M) (α : RestrictedField S O.U k)
    (β : RestrictedField S O.V k) : Field S k := by
  classical
  exact fun p => if hp : p ∈ O.U then α ⟨p,hp⟩ else β ⟨p,(O.cover p).resolve_left hp⟩

@[simp] theorem glueField_U (O : OpenCover M) (α : RestrictedField S O.U k)
    (β : RestrictedField S O.V k) (p : O.U) : glueField O α β p.val = α p := by
  classical
  simp only [glueField, dite_eq_left p.property]

 theorem glueField_V (O : OpenCover M) (α : RestrictedField S O.U k)
    (β : RestrictedField S O.V k)
    (h : ∀ (p : M) (hu : p ∈ O.U) (hv : p ∈ O.V), α ⟨p,hu⟩ = β ⟨p,hv⟩)
    (p : O.V) : glueField O α β p.val = β p := by
  classical
  by_cases hp : p.val ∈ O.U
  · rw [glueField, dite_eq_left hp]
    exact h p.val hp p.property
  · simp only [glueField, dite_eq_right hp]

/-- Smoothness glues for the genuine exterior bundle section test, including
half-space charts and empty cover members. -/
theorem glueField_smooth (D : FormBundle C k) (O : OpenCover M)
    (α : RestrictedField S O.U k) (β : RestrictedField S O.V k)
    (hα : IsRestrictedForm D O.U α) (hβ : IsRestrictedForm D O.V β)
    (h : ∀ (p : M) (hu : p ∈ O.U) (hv : p ∈ O.V), α ⟨p,hu⟩ = β ⟨p,hv⟩) :
    IsForm D (glueField O α β) := by
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  let f : M → Bundle.TotalSpace (Euclidean (n.choose k))
      (fun p => Fiber (TangentSpace S p) k) := fun p => ⟨p,glueField O α β p⟩
  have hu : ManifoldSmoothOn S.smoothStructure.val D.space.bundle.totalManifold.smoothStructure.val
      f O.U := by
    apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ f O.U O.U.isOpen).mpr
    have he : (fun p : O.U => f p.val) = (fun p : O.U =>
        (⟨p.val, α p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
          (fun q => Fiber (TangentSpace S q) k))) := by
      funext p
      simp only [f, glueField_U]
    exact he.symm ▸ hα
  have hv : ManifoldSmoothOn S.smoothStructure.val D.space.bundle.totalManifold.smoothStructure.val
      f O.V := by
    apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ f O.V O.V.isOpen).mpr
    have he : (fun p : O.V => f p.val) = (fun p : O.V =>
        (⟨p.val, β p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
          (fun q => Fiber (TangentSpace S q) k))) := by
      funext p
      simp only [f, glueField_V O α β h]
    exact he.symm ▸ hβ
  intro p
  rcases O.cover p with hp | hp
  · exact hu p hp
  · exact hv p hp

/-- Restriction of a smooth intrinsic form is a genuine smooth restricted
section; it does not require a new tangent-bundle hypothesis. -/
theorem restrict_smooth (D : FormBundle C k) (U : TopologicalSpace.Opens M)
    (ω : Field S k) (hω : IsForm D ω) :
    IsRestrictedForm D U (fun p => ω p.val) := by
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  exact (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _
    (fun p => (⟨p,ω p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
      (fun q => Fiber (TangentSpace S q) k))) U U.isOpen).mp (fun p _ => hω p)

/-- Equality of both restrictions implies equality of the global fields. -/
theorem restrictions_injective (O : OpenCover M) (ω η : Field S k)
    (hu : ∀ p : O.U, ω p.val = η p.val) (hv : ∀ p : O.V, ω p.val = η p.val) :
    ω = η := by
  funext p
  rcases O.cover p with hp | hp
  · exact hu ⟨p,hp⟩
  · exact hv ⟨p,hp⟩

/-- Unique smooth gluing, the kernel-equals-image argument on forms. -/
theorem exists_unique_smooth_gluing (D : FormBundle C k) (O : OpenCover M)
    (α : RestrictedField S O.U k) (β : RestrictedField S O.V k)
    (hα : IsRestrictedForm D O.U α) (hβ : IsRestrictedForm D O.V β)
    (h : ∀ (p : M) (hu : p ∈ O.U) (hv : p ∈ O.V), α ⟨p,hu⟩ = β ⟨p,hv⟩) :
    ∃! ω : Field S k, IsForm D ω ∧
      (∀ p : O.U, ω p.val = α p) ∧ (∀ p : O.V, ω p.val = β p) := by
  refine ⟨glueField O α β, ⟨glueField_smooth D O α β hα hβ h,
    glueField_U O α β, glueField_V O α β h⟩, ?_⟩
  intro ω hω
  apply restrictions_injective O
  · intro p
    rw [hω.2.1 p, glueField_U]
  · intro p
    rw [hω.2.2 p, glueField_V O α β h]

/-- Closed-support subordination gives a whole neighborhood of vanishing,
which is stronger than pointwise vanishing off the chosen open set. -/
theorem factor_eventually_zero (ρ : M → ℝ) (p : M)
    (hp : p ∉ sectionSupport ρ) : ∀ᶠ q in nhds p, ρ q = 0 := by
  have hn := isClosed_closure.isOpen_compl.mem_nhds hp
  filter_upwards [hn] with q hq
  by_contra hne
  exact hq (subset_closure hne)

/-- Smooth zero extension over a specified open set W. At each new point
one must supply a whole neighborhood of zero, not only a zero value there. -/
theorem zeroExtend_smooth (D : FormBundle C k) (U W : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm D U ω)
    (hz : ∀ p ∈ W, p ∉ U → ∀ᶠ q in nhds p, zeroExtend ω q = 0) :
    IsRestrictedForm D W (fun p => zeroExtend ω p.val) := by
  classical
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  let f : M → Bundle.TotalSpace (Euclidean (n.choose k))
      (fun p => Fiber (TangentSpace S p) k) := fun p => ⟨p,zeroExtend ω p⟩
  have hi : ManifoldSmoothOn S.smoothStructure.val D.space.bundle.totalManifold.smoothStructure.val
      f U := by
    apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ f U U.isOpen).mpr
    have he : (fun p : U => f p.val) = (fun p : U =>
        (⟨p.val, ω p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
          (fun q => Fiber (TangentSpace S q) k))) := by
      funext p
      simp only [f, zeroExtend, dite_eq_left p.property]
    exact he.symm ▸ hω
  apply (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ f W W.isOpen).mp
  intro p hp
  by_cases hpu : p ∈ U
  · exact hi p hpu
  · apply manifoldContDiffAt_congr (D.space.bundle.zero_smooth p)
    filter_upwards [hz p hp hpu] with q hq
    exact congrArg (fun v => (⟨q,v⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
      (fun r => Fiber (TangentSpace S r) k))) hq.symm

private theorem vectorSmoothAt_restrict {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (U : TopologicalSpace.Opens M) (f : M → V) (p : U)
    (hf : FrameData.VectorSmoothAt S.smoothStructure.val f p.val) :
    FrameData.VectorSmoothAt (openSubsetAtlas S.smoothStructure.val U U.isOpen)
      (fun q : U => f q.val) p := by
  refine ⟨hf.1.comp continuousAt_subtype_val, ?_⟩
  rintro _ ⟨hne,c,hc,rfl⟩ hp
  obtain ⟨W,hW,hpW,F,hF,he⟩ := hf.2 c hc (by simpa using hp)
  exact ⟨W,hW,hpW,F,hF,he.comp_tendsto continuousAt_subtype_val⟩

/-- Scalar multiplication by a smooth function preserves the actual smooth
restricted sections. This uses the linear bundle trivializations. -/
theorem function_smul_smooth (D : FormBundle C k) (U : TopologicalSpace.Opens M)
    (ρ : M → ℝ) (hρ : PartitionData.ScalarSmooth S.smoothStructure.val ρ)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm D U ω) :
    IsRestrictedForm D U (fun p => ρ p.val • ω p) := by
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  intro p
  obtain ⟨i,hi⟩ := D.space.bundle.covers p.val
  let e := D.space.bundle.trivialization i
  letI := D.space.bundle.linear i
  have hρp := vectorSmoothAt_restrict U ρ p
    ((scalarContDiffAt_iff (⊤ : ℕ∞) S.smoothStructure.val ρ p.val).mp (hρ p.val))
  have hc := Frames.sectionCoordinates_smoothAt D.space.bundle U U.isOpen i ω p hi (hω p)
  apply Frames.smoothAt_of_sectionCoordinates D.space.bundle U U.isOpen i _ p hi
  have hh := (hρp.prod hc).postcomp (contDiff_fst.smul contDiff_snd)
  apply hh.congr
  have hip : p.val ∈ e.baseSet := (D.space.bundle.trivialization_baseSet i).symm ▸ hi
  filter_upwards [continuousAt_subtype_val.preimage_mem_nhds (e.open_baseSet.mem_nhds hip)] with q hq
  exact ((e.linearEquivAt ℝ q.val hq).map_smul (ρ q.val) (ω q)).symm

/-- The support argument for the weighted zero extensions used in the lift.
The hypothesis on the product is its genuine smooth restricted-section test. -/
theorem weighted_zeroExtension_smooth (D : FormBundle C k)
    (U W : TopologicalSpace.Opens M) (ρ : M → ℝ) (ω : RestrictedField S U k)
    (hω : IsRestrictedForm D U (fun p => ρ p.val • ω p))
    (hs : sectionSupport ρ ∩ (W : Set M) ⊆ (U : Set M)) :
    IsRestrictedForm D W (fun p => zeroExtend (fun q : U => ρ q.val • ω q) p.val) := by
  classical
  apply zeroExtend_smooth D U W _ hω
  intro p hp hpu
  have hps : p ∉ sectionSupport ρ := fun h => hpu (hs ⟨h,hp⟩)
  filter_upwards [factor_eventually_zero ρ p hps] with q hq
  by_cases hqu : q ∈ U
  · simp only [zeroExtend, dite_eq_left hqu, hq, zero_smul]
  · simp only [zeroExtend, dite_eq_right hqu]

/-- Complete smooth weighted extension: smoothness of the factor and of the
input section, together with closed-support subordination, suffice. -/
theorem weighted_extension (D : FormBundle C k) (U W : TopologicalSpace.Opens M)
    (ρ : M → ℝ) (hρ : PartitionData.ScalarSmooth S.smoothStructure.val ρ)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm D U ω)
    (hs : sectionSupport ρ ∩ (W : Set M) ⊆ (U : Set M)) :
    IsRestrictedForm D W (fun p => zeroExtend (fun q : U => ρ q.val • ω q) p.val) :=
  weighted_zeroExtension_smooth D U W ρ ω (function_smul_smooth D U ρ hρ ω hω) hs

/-- The actual smooth lift of any overlap form, with the source's sign.
This proves the geometric surjectivity on forms before the complex is assembled. -/
theorem exists_smooth_difference_lift (D : FormBundle C k) (O : OpenCover M)
    (γ : RestrictedField S (O.U ⊓ O.V) k)
    (hγ : IsRestrictedForm D (O.U ⊓ O.V) γ) :
    ∃ α : RestrictedField S O.U k, ∃ β : RestrictedField S O.V k,
      IsRestrictedForm D O.U α ∧ IsRestrictedForm D O.V β ∧
      ∀ p : ↥(O.U ⊓ O.V),
        β ⟨p.val,p.property.2⟩ - α ⟨p.val,p.property.1⟩ = γ p := by
  classical
  let sets : Bool → Set M := fun i => if i then O.U else O.V
  have hopen : ∀ i, IsOpen (sets i) := by
    intro i
    cases i
    · exact O.V.isOpen
    · exact O.U.isOpen
  have hcover : ∀ p, ∃ i, p ∈ sets i := by
    intro p
    rcases O.cover p with hp | hp
    · exact ⟨true,hp⟩
    · exact ⟨false,hp⟩
  obtain ⟨ρ,hρ,hs⟩ := exists_smooth_partition S sets hopen hcover
  have hsum (p : M) : ρ true p + ρ false p = 1 := by
    simpa only [finsum_eq_sum_of_fintype, Fintype.sum_bool] using hρ.2.2.2 p
  have hneg : IsRestrictedForm D (O.U ⊓ O.V) (fun p => -γ p) := by
    have he : (fun p : ↥(O.U ⊓ O.V) => (-1 : ℝ) • γ p) = (fun p => -γ p) := by
      funext p
      exact neg_one_smul ℝ (γ p)
    exact he ▸ function_smul_smooth D (O.U ⊓ O.V)
      (fun _ => (-1 : ℝ)) (scalarContDiff_const ⊤ _ (-1)) γ hγ
  let α : RestrictedField S O.U k := fun p =>
    zeroExtend (fun q : ↥(O.U ⊓ O.V) => ρ false q.val • -γ q) p.val
  let β : RestrictedField S O.V k := fun p =>
    zeroExtend (fun q : ↥(O.U ⊓ O.V) => ρ true q.val • γ q) p.val
  refine ⟨α,β,?_,?_,?_⟩
  · apply weighted_extension D (O.U ⊓ O.V) O.U (ρ false) (hρ.1 false) _ hneg
    intro p hp
    exact ⟨hp.2, hs false hp.1⟩
  · apply weighted_extension D (O.U ⊓ O.V) O.V (ρ true) (hρ.1 true) _ hγ
    intro p hp
    exact ⟨hs true hp.1,hp.2⟩
  · intro p
    simp only [α,β,zeroExtend,dite_eq_left p.property,smul_neg,sub_neg_eq_add]
    rw [← add_smul, hsum, one_smul]

/-- Smooth restricted sections form a real vector space. -/
theorem restricted_zero (D : FormBundle C k) (U : TopologicalSpace.Opens M) :
    IsRestrictedForm D U 0 := by
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  exact restrict_smooth D U 0 D.space.bundle.zero_smooth

theorem restricted_add (D : FormBundle C k) (U : TopologicalSpace.Opens M)
    (ω η : RestrictedField S U k) (hω : IsRestrictedForm D U ω)
    (hη : IsRestrictedForm D U η) : IsRestrictedForm D U (ω+η) := by
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  intro p
  obtain ⟨i, hi⟩ := D.space.bundle.covers p.val
  let e := D.space.bundle.trivialization i
  letI := D.space.bundle.linear i
  have hωc := Frames.sectionCoordinates_smoothAt D.space.bundle U U.isOpen i ω p hi (hω p)
  have hηc := Frames.sectionCoordinates_smoothAt D.space.bundle U U.isOpen i η p hi (hη p)
  apply Frames.smoothAt_of_sectionCoordinates D.space.bundle U U.isOpen i _ p hi
  apply ((hωc.prod hηc).postcomp (contDiff_fst.add contDiff_snd)).congr
  have hip : p.val ∈ e.baseSet := (D.space.bundle.trivialization_baseSet i).symm ▸ hi
  filter_upwards [continuousAt_subtype_val.preimage_mem_nhds (e.open_baseSet.mem_nhds hip)] with q hq
  exact ((e.linearEquivAt ℝ q.val hq).map_add (ω q) (η q)).symm

theorem restricted_smul (D : FormBundle C k) (U : TopologicalSpace.Opens M)
    (r : ℝ) (ω : RestrictedField S U k) (hω : IsRestrictedForm D U ω) :
    IsRestrictedForm D U (r • ω) :=
  function_smul_smooth D U (fun _ => r) (scalarContDiff_const ⊤ _ r) ω hω

theorem restricted_sub (D : FormBundle C k) (U : TopologicalSpace.Opens M)
    (ω η : RestrictedField S U k) (hω : IsRestrictedForm D U ω)
    (hη : IsRestrictedForm D U η) : IsRestrictedForm D U (ω-η) := by
  have he : (-1 : ℝ) • η = -η := by
    funext p
    exact neg_one_smul ℝ (η p)
  simpa only [he, sub_eq_add_neg] using
    restricted_add D U ω ((-1 : ℝ) • η) hω (restricted_smul D U (-1) η hη)

/-- Restriction to a smaller open set preserves the full section test. -/
theorem restricted_restrict (D : FormBundle C k) (U W : TopologicalSpace.Opens M)
    (hWU : W ≤ U) (ω : RestrictedField S U k) (hω : IsRestrictedForm D U ω) :
    IsRestrictedForm D W (fun p => ω ⟨p.val,hWU p.property⟩) := by
  classical
  have hh := zeroExtend_smooth D U W ω hω (fun _ hp hn => (hn (hWU hp)).elim)
  have he : (fun p : W => zeroExtend ω p.val) = (fun p : W => ω ⟨p.val,hWU p.property⟩) := by
    funext p
    simp only [zeroExtend, dite_eq_left (hWU p.property)]
  exact he ▸ hh

theorem restricted_derivative_unique (C : CotangentBundle S) (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (η ζ : RestrictedField S U (k+1))
    (hη : HasRestrictedDerivative C U ω η) (hζ : HasRestrictedDerivative C U ω ζ) :
    η = ζ := by
  funext p
  obtain ⟨c,hc,hp⟩ := S.smoothStructure.property.1.1 p.val
  exact (hη c hc p hp).trans (hζ c hc p hp).symm

/-- Restricting the coordinate derivative does not differentiate across the
artificial edge of an open subset. -/
theorem restricted_derivative_restrict (C : CotangentBundle S)
    (U W : TopologicalSpace.Opens M) (hWU : W ≤ U)
    (ω : RestrictedField S U k) (η : RestrictedField S U (k+1))
    (hη : HasRestrictedDerivative C U ω η) :
    HasRestrictedDerivative C W (fun p => ω ⟨p.val,hWU p.property⟩)
      (fun p => η ⟨p.val,hWU p.property⟩) := by
  classical
  intro c hc p hp
  change η ⟨p.val,hWU p.property⟩ = _
  rw [hη c hc ⟨p.val,hWU p.property⟩ hp]
  apply ExteriorDerivativeResults.coordinate_locality
  filter_upwards [W.isOpen.mem_nhds p.property] with q hq
  simp only [zeroExtend, dite_eq_left (hWU hq)]
  split_ifs with h
  · rfl
  · exact (h hq).elim

theorem global_derivative_restrict {B : ∀ k, FormBundle C k} (K : DeRhamData.Calculus C B)
    (k : ℕ) (ω : K.forms k) (U : TopologicalSpace.Opens M) :
    HasRestrictedDerivative C U (fun p => ω.val p.val)
      (fun p => (K.d k ω).val p.val) := by
  classical
  intro c hc p hp
  change K.D k ω.val p.val = _
  rw [K.coordinates k ω.val ((K.mem_forms _ _).mp ω.property) c hc p.val hp]
  apply ExteriorDerivativeResults.coordinate_locality
  filter_upwards [U.isOpen.mem_nhds p.property] with q hq
  simp only [zeroExtend]
  split_ifs with h
  · rfl
  · exact (h hq).elim

end OpenForms
end SmoothManifolds.MayerVietorisData

namespace SmoothManifolds.MayerVietorisResults
open MayerVietorisData
universe u
/-- Canonical cohomology decomposition on the middle complex. -/
theorem product_cohomology :
    Specs.SmoothManifolds.DeRham.MayerVietoris.product_cohomologyType.{u} := by
  intro A B k
  exact ⟨A.productHEquiv B k, fun _ => rfl⟩

theorem induced_exists :
    Specs.SmoothManifolds.DeRham.MayerVietoris.induced_existsType.{u} := by
  intro A B f
  exact ⟨f.onH, f.onH_induced, fun F hF => f.induced_unique F hF⟩

theorem connecting_exists :
    Specs.SmoothManifolds.DeRham.MayerVietoris.connecting_existsType.{u} := by
  intro A B C E
  exact ⟨E.delta, E.delta_connecting, fun δ hδ => E.connecting_unique δ hδ⟩

theorem long_exact : Specs.SmoothManifolds.DeRham.MayerVietoris.long_exactType.{u} := by
  intro A B C E R Q δ hR hQ hδ
  rw [E.r.induced_unique R hR, E.q.induced_unique Q hQ, E.connecting_unique δ hδ]
  exact E.long_exact

theorem naturality : Specs.SmoothManifolds.DeRham.MayerVietoris.naturalityType.{u} := by
  intro A B C A' B' C' E E' F δ δ' FA FB FC R Q R' Q'
    hδ hδ' hFA hFB hFC hR hQ hR' hQ'
  rw [E.connecting_unique δ hδ, E'.connecting_unique δ' hδ',
    F.left.induced_unique FA hFA, F.middle.induced_unique FB hFB,
    F.right.induced_unique FC hFC, E.r.induced_unique R hR,
    E.q.induced_unique Q hQ, E'.r.induced_unique R' hR', E'.q.induced_unique Q' hQ']
  exact ⟨F.r_natural, F.q_natural, F.delta_natural⟩

end SmoothManifolds.MayerVietorisResults

section RestrictedCalculusConstruction

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SmoothManifolds.MayerVietorisData.OpenForms
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MapData Set Filter
open scoped Topology
universe u
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {k : ℕ}

theorem exists_global_germ (D : FormBundle C k) (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm D U ω) (p : U) :
    ∃ α : Field S k, IsForm D α ∧
      ∀ᶠ q in nhds p.val, α q = zeroExtend ω q := by
  classical
  obtain ⟨ρ,hρ,h01,h1,hs,hcp⟩ := exists_local_bump S p.val U U.isOpen p.property
  let α : Field S k := zeroExtend (fun q : U => ρ q.val • ω q)
  refine ⟨α,?_,?_⟩
  · have hh := weighted_extension D U ⊤ ρ hρ ω hω (fun q hq => hs hq.1)
    letI := (cotangentSpace C).topology
    letI := D.space.topology
    have hi := (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _
      (fun q => (⟨q,α q⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun r => Fiber (TangentSpace S r) k))) Set.univ isOpen_univ).mpr hh
    exact fun q => hi q (Set.mem_univ q)
  · filter_upwards [h1, U.isOpen.mem_nhds p.property] with q hq hqu
    simp [α, zeroExtend, hqu, hq]

theorem restricted_smooth_of_global_germs (D : FormBundle C k)
    (U : TopologicalSpace.Opens M) (ω : RestrictedField S U k)
    (h : ∀ p : U, ∃ α : Field S k, IsForm D α ∧
      ∀ᶠ q in nhds p.val, α q = zeroExtend ω q) : IsRestrictedForm D U ω := by
  classical
  letI := (cotangentSpace C).topology
  letI := D.space.topology
  let f : M → Bundle.TotalSpace (Euclidean (n.choose k))
      (fun q => Fiber (TangentSpace S q) k) := fun q => ⟨q,zeroExtend ω q⟩
  have hi : ManifoldSmoothOn S.smoothStructure.val D.space.bundle.totalManifold.smoothStructure.val f U := by
    intro p hp
    obtain ⟨α,hα,he⟩ := h ⟨p,hp⟩
    exact manifoldContDiffAt_congr (hα p) (he.mono (fun q hq => congrArg
      (fun v => (⟨q,v⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun r => Fiber (TangentSpace S r) k))) hq))
  have hh := (manifoldContDiff_restrict_open (⊤ : ℕ∞) _ _ f U U.isOpen).mp hi
  have he : (fun p : U => f p.val) = (fun p : U =>
      (⟨p.val,ω p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun q => Fiber (TangentSpace S q) k))) := by
    funext p
    simp only [f,zeroExtend,dite_eq_left p.property]
  change ManifoldSmooth (openSubsetAtlas S.smoothStructure.val U U.isOpen)
    D.space.bundle.totalManifold.smoothStructure.val (fun p : U =>
      (⟨p.val,ω p⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
        (fun q => Fiber (TangentSpace S q) k)))
  exact he ▸ hh

variable {B : ∀ k, FormBundle C k}

theorem restricted_derivative_eq_global (K : Calculus C B)
    (U : TopologicalSpace.Opens M) (ω : RestrictedField S U k)
    (η : RestrictedField S U (k+1)) (hder : HasRestrictedDerivative C U ω η)
    (α : Field S k) (hα : IsForm (B k) α) (p : U)
    (hgerm : ∀ᶠ q in nhds p.val, α q = zeroExtend ω q) :
    η p = K.D k α p.val := by
  obtain ⟨c,hc,hp⟩ := S.smoothStructure.property.1.1 p.val
  rw [hder c hc p hp, K.coordinates k α hα c hc p.val hp]
  exact ExteriorDerivativeResults.coordinate_locality C k c hc _ _ p.val hp (hgerm.mono (fun _ h => h.symm))

private def germExtension (D : FormBundle C k) (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm D U ω) (p : U) : Field S k :=
  (exists_global_germ D U ω hω p).choose

private theorem germExtension_smooth (D : FormBundle C k) (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm D U ω) (p : U) :
    IsForm D (germExtension D U ω hω p) :=
  (exists_global_germ D U ω hω p).choose_spec.1

private theorem germExtension_germ (D : FormBundle C k) (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm D U ω) (p : U) :
    ∀ᶠ q in nhds p.val, germExtension D U ω hω p q = zeroExtend ω q :=
  (exists_global_germ D U ω hω p).choose_spec.2

private def localD (K : Calculus C B) (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm (B k) U ω) :
    RestrictedField S U (k+1) :=
  fun p => K.D k (germExtension (B k) U ω hω p) p.val

private theorem localD_coordinates (K : Calculus C B) (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm (B k) U ω) :
    HasRestrictedDerivative C U ω (localD K U ω hω) := by
  intro c hc p hp
  exact (K.coordinates k _ (germExtension_smooth (B k) U ω hω p) c hc p.val hp).trans
    (ExteriorDerivativeResults.coordinate_locality C k c hc _ _ p.val hp
      (germExtension_germ (B k) U ω hω p))

private theorem localD_eq_global (K : Calculus C B) (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm (B k) U ω)
    (α : Field S k) (hα : IsForm (B k) α) (p : U)
    (hgerm : ∀ᶠ q in nhds p.val, α q = zeroExtend ω q) :
    localD K U ω hω p = K.D k α p.val :=
  restricted_derivative_eq_global K U ω _ (localD_coordinates K U ω hω) α hα p hgerm

private theorem localD_global_germ (K : Calculus C B) (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm (B k) U ω)
    (α : Field S k) (hα : IsForm (B k) α) (p : U)
    (hgerm : ∀ᶠ q in nhds p.val, α q = zeroExtend ω q) :
    ∀ᶠ q in nhds p.val, K.D k α q = zeroExtend (localD K U ω hω) q := by
  classical
  filter_upwards [hgerm.eventually_nhds, U.isOpen.mem_nhds p.property] with q hq hqu
  simp only [zeroExtend]
  split_ifs with h
  · exact (localD_eq_global K U ω hω α hα ⟨q,h⟩ hq).symm
  · exact (h hqu).elim

private theorem localD_smooth (K : Calculus C B) (U : TopologicalSpace.Opens M)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm (B k) U ω) :
    IsRestrictedForm (B (k+1)) U (localD K U ω hω) := by
  apply restricted_smooth_of_global_germs
  intro p
  obtain ⟨α,hα,he⟩ := exists_global_germ (B k) U ω hω p
  exact ⟨K.D k α, K.axioms.smooth k α hα, localD_global_germ K U ω hω α hα p he⟩

private def restrictedForms (B : ∀ k, FormBundle C k) (U : TopologicalSpace.Opens M)
    (k : ℕ) : Submodule ℝ (RestrictedField S U k) where
  carrier := {ω | IsRestrictedForm (B k) U ω}
  zero_mem' := restricted_zero (B k) U
  add_mem' := fun hω hη => restricted_add (B k) U _ _ hω hη
  smul_mem' := fun r _ hω => restricted_smul (B k) U r _ hω

private theorem global_add_smooth (K : Calculus C B) (α β : Field S k)
    (hα : IsForm (B k) α) (hβ : IsForm (B k) β) : IsForm (B k) (α+β) :=
  (K.mem_forms _ _).mp ((K.forms k).add_mem ((K.mem_forms _ _).mpr hα)
    ((K.mem_forms _ _).mpr hβ))

private theorem global_smul_smooth (K : Calculus C B) (r : ℝ) (α : Field S k)
    (hα : IsForm (B k) α) : IsForm (B k) (r • α) :=
  (K.mem_forms _ _).mp ((K.forms k).smul_mem r ((K.mem_forms _ _).mpr hα))

private theorem zeroExtend_add_germ (U : TopologicalSpace.Opens M)
    (ω η : RestrictedField S U k) (p : U) :
    ∀ᶠ q in nhds p.val, zeroExtend (ω+η) q = zeroExtend ω q + zeroExtend η q := by
  classical
  apply Filter.Eventually.of_forall
  intro q
  simp only [zeroExtend]
  split_ifs <;> simp

private theorem zeroExtend_smul_germ (U : TopologicalSpace.Opens M)
    (r : ℝ) (ω : RestrictedField S U k) (p : U) :
    ∀ᶠ q in nhds p.val, zeroExtend (r • ω) q = r • zeroExtend ω q := by
  classical
  apply Filter.Eventually.of_forall
  intro q
  simp only [zeroExtend]
  split_ifs <;> simp

private theorem localD_add (K : Calculus C B) (U : TopologicalSpace.Opens M)
    (ω η : RestrictedField S U k) (hω : IsRestrictedForm (B k) U ω)
    (hη : IsRestrictedForm (B k) U η) (hωη : IsRestrictedForm (B k) U (ω+η)) :
    localD K U (ω+η) hωη = localD K U ω hω + localD K U η hη := by
  funext p
  obtain ⟨α,hα,heα⟩ := exists_global_germ (B k) U ω hω p
  obtain ⟨β,hβ,heβ⟩ := exists_global_germ (B k) U η hη p
  have he : ∀ᶠ q in nhds p.val, (α+β) q = zeroExtend (ω+η) q := by
    filter_upwards [heα,heβ,zeroExtend_add_germ U ω η p] with q hqα hqβ hq
    simp only [Pi.add_apply,hqα,hqβ,hq]
  change localD K U (ω+η) _ p = localD K U ω _ p + localD K U η _ p
  rw [localD_eq_global K U _ _ (α+β) (global_add_smooth K α β hα hβ) p he,
    localD_eq_global K U _ _ α hα p heα, localD_eq_global K U _ _ β hβ p heβ]
  exact congrFun (K.axioms.add k α β hα hβ) p.val

private theorem localD_smul (K : Calculus C B) (U : TopologicalSpace.Opens M)
    (r : ℝ) (ω : RestrictedField S U k) (hω : IsRestrictedForm (B k) U ω)
    (hrω : IsRestrictedForm (B k) U (r • ω)) :
    localD K U (r • ω) hrω = r • localD K U ω hω := by
  funext p
  obtain ⟨α,hα,heα⟩ := exists_global_germ (B k) U ω hω p
  have he : ∀ᶠ q in nhds p.val, (r • α) q = zeroExtend (r • ω) q := by
    filter_upwards [heα,zeroExtend_smul_germ U r ω p] with q hqα hq
    simp only [Pi.smul_apply,hqα,hq]
  change localD K U (r • ω) _ p = r • localD K U ω _ p
  rw [localD_eq_global K U _ _ (r • α) (global_smul_smooth K r α hα) p he,
    localD_eq_global K U _ _ α hα p heα]
  exact congrFun (K.axioms.smul k r α hα) p.val

private def openDifferential (K : Calculus C B) (U : TopologicalSpace.Opens M)
    (k : ℕ) : restrictedForms B U k →ₗ[ℝ] restrictedForms B U (k+1) where
  toFun ω := ⟨localD K U ω.val ω.property, localD_smooth K U ω.val ω.property⟩
  map_add' ω η := Subtype.ext (localD_add K U ω.val η.val ω.property η.property
    (restricted_add (B k) U ω.val η.val ω.property η.property))
  map_smul' r ω := Subtype.ext (localD_smul K U r ω.val ω.property
    (restricted_smul (B k) U r ω.val ω.property))

private theorem openDifferential_square (K : Calculus C B)
    (U : TopologicalSpace.Opens M) (k : ℕ) (ω : restrictedForms B U k) :
    openDifferential K U (k+1) (openDifferential K U k ω) = 0 := by
  apply Subtype.ext
  funext p
  obtain ⟨α,hα,heα⟩ := exists_global_germ (B k) U ω.val ω.property p
  change localD K U (localD K U ω.val ω.property) _ p = 0
  rw [localD_eq_global K U _ _ (K.D k α) (K.axioms.smooth k α hα) p
    (localD_global_germ K U ω.val ω.property α hα p heα)]
  exact congrFun (K.axioms.square k α hα) p.val

/-- The full smooth de Rham complex on an arbitrary open set, with the
intrinsic coordinate derivative and no condition at the edge of the open set. -/
theorem openCalculus_exists (K : Calculus C B) (U : TopologicalSpace.Opens M) :
    Nonempty (OpenCalculus C B U) := by
  let A : Cochain.{u} := {
    Obj := fun k => restrictedForms B U k
    d := openDifferential K U
    square := openDifferential_square K U }
  refine ⟨{ complex := A
            field := fun k => (restrictedForms B U k).subtype
            injective := fun _ => Subtype.val_injective
            range_smooth := ?_
            coordinates := ?_ }⟩
  · intro k ω
    exact ⟨fun h => ⟨⟨ω,h⟩,rfl⟩, fun ⟨η,hη⟩ => hη ▸ η.property⟩
  · intro k ω
    exact localD_coordinates K U ω.val ω.property

end SmoothManifolds.MayerVietorisData.OpenForms

end RestrictedCalculusConstruction

namespace SmoothManifolds.MayerVietorisData
universe u

namespace OpenForms
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MapData Set
variable {n : ℕ} {a : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n a M} {C : CotangentBundle S} {B : ∀ k, FormBundle C k}

/-- The full-range axiom realizes every actual smooth restricted section. -/
def realize {U : TopologicalSpace.Opens M} (D : OpenCalculus C B U) (k : ℕ)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm (B k) U ω) : D.complex.Obj k :=
  ((D.range_smooth k ω).mp hω).choose

@[simp] theorem field_realize {U : TopologicalSpace.Opens M} (D : OpenCalculus C B U) (k : ℕ)
    (ω : RestrictedField S U k) (hω : IsRestrictedForm (B k) U ω) :
    D.field k (realize D k ω hω) = ω :=
  ((D.range_smooth k ω).mp hω).choose_spec

 theorem field_smooth {U : TopologicalSpace.Opens M} (D : OpenCalculus C B U) (k : ℕ)
    (ω : D.complex.Obj k) : IsRestrictedForm (B k) U (D.field k ω) :=
  (D.range_smooth k _).mpr ⟨ω,rfl⟩

/-- Restriction from the original global calculus to any full realization. -/
def globalRestriction (K : Calculus C B) (U : TopologicalSpace.Opens M)
    (D : OpenCalculus C B U) : ChainMap (globalComplex K) D.complex where
  map k := {
    toFun ω := realize D k (fun p => ω.val p.val)
      (restrict_smooth (B k) U ω.val ((K.mem_forms k _).mp ω.property))
    map_add' x y := by
      apply D.injective k
      simp only [map_add, field_realize]
      rfl
    map_smul' r x := by
      apply D.injective k
      simp only [map_smul, field_realize]
      rfl }
  comm k ω := by
    apply D.injective (k+1)
    have hd := D.coordinates k
      (realize D k (fun p => ω.val p.val)
        (restrict_smooth (B k) U ω.val ((K.mem_forms k _).mp ω.property)))
    change D.field (k+1) (D.complex.d k _) =
      D.field (k+1) (realize D (k+1) (fun p : U => (K.d k ω).val p.val)
        (restrict_smooth (B (k+1)) U (K.d k ω).val
          ((K.mem_forms (k+1) _).mp (K.d k ω).property)))
    simp only [field_realize] at hd ⊢
    exact restricted_derivative_unique C U _ _ _ hd (global_derivative_restrict K k ω U)

@[simp] theorem globalRestriction_field (K : Calculus C B) (U : TopologicalSpace.Opens M)
    (D : OpenCalculus C B U) (k : ℕ) (ω : K.forms k) :
    D.field k ((globalRestriction K U D).map k ω) = fun p : U => ω.val p.val :=
  field_realize D k _ (restrict_smooth (B k) U ω.val ((K.mem_forms k _).mp ω.property))

/-- Restriction between nested open domains, respecting the actual derivative. -/
def openRestriction (U W : TopologicalSpace.Opens M) (hWU : W ≤ U)
    (D : OpenCalculus C B U) (E : OpenCalculus C B W) : ChainMap D.complex E.complex where
  map k := {
    toFun ω := realize E k (fun p => D.field k ω ⟨p.val,hWU p.property⟩)
      (restricted_restrict (B k) U W hWU (D.field k ω) (field_smooth D k ω))
    map_add' x y := by
      apply E.injective k
      simp only [map_add, field_realize]
      rfl
    map_smul' r x := by
      apply E.injective k
      simp only [map_smul, field_realize]
      rfl }
  comm k ω := by
    apply E.injective (k+1)
    have hd := E.coordinates k
      (realize E k (fun p => D.field k ω ⟨p.val,hWU p.property⟩)
        (restricted_restrict (B k) U W hWU (D.field k ω) (field_smooth D k ω)))
    change E.field (k+1) (E.complex.d k _) = E.field (k+1)
      (realize E (k+1) (fun p : W => D.field (k+1) (D.complex.d k ω) ⟨p.val,hWU p.property⟩)
        (restricted_restrict (B (k+1)) U W hWU (D.field (k+1) (D.complex.d k ω))
          (field_smooth D (k+1) (D.complex.d k ω))))
    simp only [field_realize] at hd ⊢
    exact restricted_derivative_unique C W _ _ _ hd
      (restricted_derivative_restrict C U W hWU _ _ (D.coordinates k ω))

@[simp] theorem openRestriction_field (U W : TopologicalSpace.Opens M) (hWU : W ≤ U)
    (D : OpenCalculus C B U) (E : OpenCalculus C B W) (k : ℕ) (ω : D.complex.Obj k) :
    E.field k ((openRestriction U W hWU D E).map k ω) =
      fun p : W => D.field k ω ⟨p.val,hWU p.property⟩ :=
  field_realize E k _ (restricted_restrict (B k) U W hWU (D.field k ω) (field_smooth D k ω))


/-- The two restrictions from the ambient manifold. -/
def coverRestriction (K : Calculus C B) (O : OpenCover M)
    (DU : OpenCalculus C B O.U) (DV : OpenCalculus C B O.V) :
    ChainMap (globalComplex K) (DU.complex.prod DV.complex) where
  map k := ((globalRestriction K O.U DU).map k).prod ((globalRestriction K O.V DV).map k)
  comm k ω := Prod.ext ((globalRestriction K O.U DU).comm k ω)
    ((globalRestriction K O.V DV).comm k ω)

@[simp] theorem coverRestriction_U (K : Calculus C B) (O : OpenCover M)
    (DU : OpenCalculus C B O.U) (DV : OpenCalculus C B O.V) (k : ℕ) (ω : K.forms k) :
    DU.field k ((coverRestriction K O DU DV).map k ω).1 = fun p : O.U => ω.val p.val :=
  globalRestriction_field _ _ _ _ _

@[simp] theorem coverRestriction_V (K : Calculus C B) (O : OpenCover M)
    (DU : OpenCalculus C B O.U) (DV : OpenCalculus C B O.V) (k : ℕ) (ω : K.forms k) :
    DV.field k ((coverRestriction K O DU DV).map k ω).2 = fun p : O.V => ω.val p.val :=
  globalRestriction_field _ _ _ _ _

/-- The overlap map has exactly the sign `b-a`. -/
def coverDifference (O : OpenCover M)
    (DU : OpenCalculus C B O.U) (DV : OpenCalculus C B O.V)
    (DW : OpenCalculus C B (O.U ⊓ O.V)) :
    ChainMap (DU.complex.prod DV.complex) DW.complex where
  map k := ((openRestriction O.V (O.U ⊓ O.V) inf_le_right DV DW).map k).comp
      (LinearMap.snd ℝ (DU.complex.Obj k) (DV.complex.Obj k)) -
    ((openRestriction O.U (O.U ⊓ O.V) inf_le_left DU DW).map k).comp
      (LinearMap.fst ℝ (DU.complex.Obj k) (DV.complex.Obj k))
  comm k ω := by
    change DW.complex.d k
      (((openRestriction O.V (O.U ⊓ O.V) inf_le_right DV DW).map k) ω.2 -
       ((openRestriction O.U (O.U ⊓ O.V) inf_le_left DU DW).map k) ω.1) =
      ((openRestriction O.V (O.U ⊓ O.V) inf_le_right DV DW).map (k+1)) (DV.complex.d k ω.2) -
       ((openRestriction O.U (O.U ⊓ O.V) inf_le_left DU DW).map (k+1)) (DU.complex.d k ω.1)
    rw [map_sub, (openRestriction O.V (O.U ⊓ O.V) inf_le_right DV DW).comm,
      (openRestriction O.U (O.U ⊓ O.V) inf_le_left DU DW).comm]

@[simp] theorem coverDifference_field (O : OpenCover M)
    (DU : OpenCalculus C B O.U) (DV : OpenCalculus C B O.V)
    (DW : OpenCalculus C B (O.U ⊓ O.V)) (k : ℕ)
    (ω : DU.complex.Obj k × DV.complex.Obj k) (p : ↥(O.U ⊓ O.V)) :
    DW.field k ((coverDifference O DU DV DW).map k ω) p =
      DV.field k ω.2 ⟨p.val,p.property.2⟩ - DU.field k ω.1 ⟨p.val,p.property.1⟩ := by
  change DW.field k
    (((openRestriction O.V (O.U ⊓ O.V) inf_le_right DV DW).map k) ω.2 -
     ((openRestriction O.U (O.U ⊓ O.V) inf_le_left DU DW).map k) ω.1) p = _
  rw [map_sub]
  simp only [Pi.sub_apply, openRestriction_field]

/-- Degreewise short exactness assembled from genuine restriction and gluing. -/
def coverShortExact (K : Calculus C B) (O : OpenCover M)
    (DU : OpenCalculus C B O.U) (DV : OpenCalculus C B O.V)
    (DW : OpenCalculus C B (O.U ⊓ O.V)) :
    ShortExact (globalComplex K) (DU.complex.prod DV.complex) DW.complex where
  r := coverRestriction K O DU DV
  q := coverDifference O DU DV DW
  injective k ω η h := by
    apply Subtype.ext
    apply restrictions_injective O
    · intro p
      have he := congrArg (fun z => DU.field k z.1 p) h
      exact (congrFun (coverRestriction_U K O DU DV k ω) p).symm.trans
        (he.trans (congrFun (coverRestriction_U K O DU DV k η) p))
    · intro p
      have he := congrArg (fun z => DV.field k z.2 p) h
      exact (congrFun (coverRestriction_V K O DU DV k ω) p).symm.trans
        (he.trans (congrFun (coverRestriction_V K O DU DV k η) p))
  surjective k γ := by
    obtain ⟨α,β,hα,hβ,he⟩ := exists_smooth_difference_lift (B k) O
      (DW.field k γ) (field_smooth DW k γ)
    refine ⟨(realize DU k α hα, realize DV k β hβ), ?_⟩
    apply DW.injective k
    funext p
    simpa only [coverDifference_field, field_realize] using he p
  exact k x := by
    change DU.complex.Obj k × DV.complex.Obj k at x
    constructor
    · intro hx
      have hh (p : M) (hu : p ∈ O.U) (hv : p ∈ O.V) :
          DU.field k x.1 ⟨p,hu⟩ = DV.field k x.2 ⟨p,hv⟩ := by
        have he : DV.field k x.2 ⟨p,hv⟩ - DU.field k x.1 ⟨p,hu⟩ = 0 := by
          calc
            _ = DW.field k ((coverDifference O DU DV DW).map k x) ⟨p,hu,hv⟩ :=
              (coverDifference_field O DU DV DW k x ⟨p,hu,hv⟩).symm
            _ = 0 := by simp only [hx,map_zero,Pi.zero_apply]
        exact (sub_eq_zero.mp he).symm
      obtain ⟨ω,hω,_⟩ := exists_unique_smooth_gluing (B k) O
        (DU.field k x.1) (DV.field k x.2) (field_smooth DU k x.1)
        (field_smooth DV k x.2) hh
      refine ⟨⟨ω,(K.mem_forms k ω).mpr hω.1⟩, ?_⟩
      apply Prod.ext
      · apply DU.injective k
        funext p
        exact (congrFun (coverRestriction_U K O DU DV k ⟨ω,(K.mem_forms k ω).mpr hω.1⟩) p).trans (hω.2.1 p)
      · apply DV.injective k
        funext p
        exact (congrFun (coverRestriction_V K O DU DV k ⟨ω,(K.mem_forms k ω).mpr hω.1⟩) p).trans (hω.2.2 p)
    · rintro ⟨ω,rfl⟩
      change K.forms k at ω
      apply DW.injective k
      funext p
      calc
        _ = DV.field k ((coverRestriction K O DU DV).map k ω).2 ⟨p.val,p.property.2⟩ -
            DU.field k ((coverRestriction K O DU DV).map k ω).1 ⟨p.val,p.property.1⟩ :=
          coverDifference_field O DU DV DW k _ p
        _ = ω.val p.val - ω.val p.val := congrArg₂ (fun x y => x-y)
          (congrFun (coverRestriction_V K O DU DV k ω) ⟨p.val,p.property.2⟩)
          (congrFun (coverRestriction_U K O DU DV k ω) ⟨p.val,p.property.1⟩)
        _ = 0 := sub_self _
        _ = DW.field k 0 p := by simp only [map_zero,Pi.zero_apply]

/-- This realization retains each prescribed open calculus. -/
def assembledCover (K : Calculus C B) (O : OpenCover M)
    (DU : OpenCalculus C B O.U) (DV : OpenCalculus C B O.V)
    (DW : OpenCalculus C B (O.U ⊓ O.V)) : CoverComplex K O where
  onU := DU
  onV := DV
  onOverlap := DW
  sequence := coverShortExact K O DU DV DW
  restriction_U k ω p := congrFun (coverRestriction_U K O DU DV k ω) p
  restriction_V k ω p := congrFun (coverRestriction_V K O DU DV k ω) p
  difference := coverDifference_field O DU DV DW


/-- One subordinate partition gives smooth zero-extended lifts in every degree. -/
theorem assembledCover_partition (K : Calculus C B) (O : OpenCover M)
    (DU : OpenCalculus C B O.U) (DV : OpenCalculus C B O.V)
    (DW : OpenCalculus C B (O.U ⊓ O.V)) :
    HasPartitionLift (assembledCover K O DU DV DW) := by
  classical
  let sets : Bool → Set M := fun i => if i then O.U else O.V
  have hopen : ∀ i, IsOpen (sets i) := by
    intro i
    cases i
    · exact O.V.isOpen
    · exact O.U.isOpen
  have hcover : ∀ p, ∃ i, p ∈ sets i := by
    intro p
    rcases O.cover p with hp | hp
    · exact ⟨true,hp⟩
    · exact ⟨false,hp⟩
  obtain ⟨ρ,hρ,hs⟩ := exists_smooth_partition S sets hopen hcover
  have hsum (p : M) : ρ true p + ρ false p = 1 := by
    simpa only [finsum_eq_sum_of_fintype, Fintype.sum_bool] using hρ.2.2.2 p
  refine ⟨ρ true,ρ false,hρ.1 true,hρ.1 false,
    fun p => ⟨hρ.2.1 true p,hρ.2.1 false p,hsum p⟩,hs true,hs false,?_⟩
  intro k γ
  dsimp only [assembledCover] at γ ⊢
  have hγ := field_smooth DW k γ
  have hneg : IsRestrictedForm (B k) (O.U ⊓ O.V) (fun p => -DW.field k γ p) := by
    have he : (fun p : ↥(O.U ⊓ O.V) => (-1 : ℝ) • DW.field k γ p) =
        (fun p => -DW.field k γ p) := by
      funext p
      exact neg_one_smul ℝ (DW.field k γ p)
    exact he ▸ function_smul_smooth (B k) (O.U ⊓ O.V)
      (fun _ => (-1 : ℝ)) (scalarContDiff_const ⊤ _ (-1)) _ hγ
  let α : RestrictedField S O.U k := fun p =>
    zeroExtend (fun q : ↥(O.U ⊓ O.V) => ρ false q.val • -DW.field k γ q) p.val
  let β : RestrictedField S O.V k := fun p =>
    zeroExtend (fun q : ↥(O.U ⊓ O.V) => ρ true q.val • DW.field k γ q) p.val
  have hα : IsRestrictedForm (B k) O.U α := by
    apply weighted_extension (B k) (O.U ⊓ O.V) O.U (ρ false) (hρ.1 false) _ hneg
    intro p hp
    exact ⟨hp.2, hs false hp.1⟩
  have hβ : IsRestrictedForm (B k) O.V β := by
    apply weighted_extension (B k) (O.U ⊓ O.V) O.V (ρ true) (hρ.1 true) _ hγ
    intro p hp
    exact ⟨hs true hp.1,hp.2⟩
  refine ⟨realize DU k α hα,realize DV k β hβ,?_,?_,?_,?_,?_⟩
  · intro p hp
    change DU.field k (realize DU k α hα) p = _
    simp only [field_realize, α,zeroExtend,dite_eq_left (show p.val ∈ O.U ⊓ O.V from ⟨p.property,hp⟩),smul_neg]
    rfl
  · intro p hp
    change DU.field k (realize DU k α hα) p = _
    simp only [field_realize, α,zeroExtend,dite_eq_right (show p.val ∉ O.U ⊓ O.V from fun h => hp h.2)]
  · intro p hp
    change DV.field k (realize DV k β hβ) p = _
    simp only [field_realize, β,zeroExtend,dite_eq_left (show p.val ∈ O.U ⊓ O.V from ⟨hp,p.property⟩)]
    rfl
  · intro p hp
    change DV.field k (realize DV k β hβ) p = _
    simp only [field_realize, β,zeroExtend,dite_eq_right (show p.val ∉ O.U ⊓ O.V from fun h => hp h.1)]
  · apply DW.injective k
    funext p
    change DW.field k ((coverDifference O DU DV DW).map k _) p = _
    simp only [coverDifference_field, field_realize, α,β,zeroExtend,dite_eq_left p.property,
      smul_neg,sub_neg_eq_add]
    rw [← add_smul,hsum,one_smul]

 theorem coverComplex_exists (K : Calculus C B) (O : OpenCover M)
    (DU : OpenCalculus C B O.U) (DV : OpenCalculus C B O.V)
    (DW : OpenCalculus C B (O.U ⊓ O.V)) : ∃ D : CoverComplex K O, HasPartitionLift D :=
  ⟨assembledCover K O DU DV DW,assembledCover_partition K O DU DV DW⟩

end OpenForms

end SmoothManifolds.MayerVietorisData

namespace SmoothManifolds.MayerVietorisResults
universe u

/-- The geometric short exact sequence and its actual partition lifts,
constructed under the original manifold and open-cover hypotheses. -/
theorem cover_sequence_exists :
    Specs.SmoothManifolds.DeRham.MayerVietoris.cover_sequence_existsType.{u} := by
  intro n a M _ S C B O
  obtain ⟨K⟩ := DeRhamResults.complex_exists C B
  obtain ⟨DU⟩ := MayerVietorisData.OpenForms.openCalculus_exists K O.U
  obtain ⟨DV⟩ := MayerVietorisData.OpenForms.openCalculus_exists K O.V
  obtain ⟨DW⟩ := MayerVietorisData.OpenForms.openCalculus_exists K (O.U ⊓ O.V)
  obtain ⟨D,hD⟩ := MayerVietorisData.OpenForms.coverComplex_exists K O DU DV DW
  exact ⟨K,D,hD⟩

end SmoothManifolds.MayerVietorisResults

namespace SmoothManifolds.MayerVietorisData
namespace OpenForms
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MapData Set Filter
open scoped Topology
universe u
section RestrictedPullback
variable {n m : ℕ} {a b : ModelKind} {M N : Type u}
  [TopologicalSpace M] [TopologicalSpace N]
  {S : SmoothManifold n a M} {T : SmoothManifold m b N}
  {C : CotangentBundle S} {A : CotangentBundle T}
  {B : ∀ k, FormBundle C k} {E : ∀ k, FormBundle A k}
  (K : Calculus C B) (J : Calculus A E)
  (f : M → N) (hf : IsSmoothMap S T f)
  (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
  (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))
  (U : TopologicalSpace.Opens M) (V : TopologicalSpace.Opens N)
  (h : Set.MapsTo f U V)

/-- Fiberwise pullback on every section over an open set. -/
def restrictedPullField (k : ℕ) :
    RestrictedField T V k →ₗ[ℝ] RestrictedField S U k where
  toFun ω p := FormPullbackData.fiberPullback (V := TangentSpace S p.val)
    (W := TangentSpace T (f p.val)) k (L p.val) (ω ⟨f p.val,h p.property⟩)
  map_add' ω η := by
    funext p
    exact map_add (FormPullbackData.fiberPullback (V := TangentSpace S p.val)
      (W := TangentSpace T (f p.val)) k (L p.val)) _ _
  map_smul' r ω := by
    funext p
    exact map_smul (FormPullbackData.fiberPullback (V := TangentSpace S p.val)
      (W := TangentSpace T (f p.val)) k (L p.val)) r _

include hf hL in
/-- A smooth germ representing a target section pulls back to a smooth germ. -/
theorem restrictedPull_smooth (k : ℕ) (ω : RestrictedField T V k)
    (hω : IsRestrictedForm (E k) V ω) :
    IsRestrictedForm (B k) U (restrictedPullField f L U V h k ω) := by
  letI := (cotangentSpace C).topology
  letI := (B k).space.topology
  intro p
  obtain ⟨α,hα,he⟩ := exists_global_germ (E k) V ω hω ⟨f p.val,h p.property⟩
  have hg := FormPullbackResults.pullback_smooth S T C A f hf L hL k
    (B k) (E k) α hα
  apply manifoldContDiffAt_congr
    (restrict_smooth (B k) U (FormPullbackData.pullbackField S T f L α) hg p)
  have ht : Tendsto (fun q : U => f q.val) (𝓝 p) (𝓝 (f p.val)) :=
    (hf p.val).1.comp continuousAt_subtype_val
  filter_upwards [ht.eventually he] with q hq
  apply congrArg (fun v => (⟨q.val,v⟩ : Bundle.TotalSpace (Euclidean (n.choose k))
    (fun r => Fiber (TangentSpace S r) k)))
  change FormPullbackData.fiberPullback (V := TangentSpace S q.val)
      (W := TangentSpace T (f q.val)) k (L q.val) (α (f q.val)) =
    FormPullbackData.fiberPullback (V := TangentSpace S q.val)
      (W := TangentSpace T (f q.val)) k (L q.val) (ω ⟨f q.val,h q.property⟩)
  apply congrArg (FormPullbackData.fiberPullback (V := TangentSpace S q.val)
      (W := TangentSpace T (f q.val)) k (L q.val))
  change α (f q.val) = zeroExtend ω (f q.val) at hq
  unfold zeroExtend at hq
  split_ifs at hq with hqV
  · exact hq
  · exact (hqV (h q.property)).elim

/-- Transport the actual pullback to any realization of all restricted forms. -/
def openPullElement (X : OpenCalculus C B U) (Y : OpenCalculus A E V)
    (k : ℕ) (ω : Y.complex.Obj k) : X.complex.Obj k :=
  Classical.choose ((X.range_smooth k _).mp
    (restrictedPull_smooth f hf L hL U V h k (Y.field k ω)
      ((Y.range_smooth k _).mpr ⟨ω,rfl⟩)))

theorem openPullElement_field (X : OpenCalculus C B U) (Y : OpenCalculus A E V)
    (k : ℕ) (ω : Y.complex.Obj k) :
    X.field k (openPullElement f hf L hL U V h X Y k ω) =
      restrictedPullField f L U V h k (Y.field k ω) :=
  Classical.choose_spec ((X.range_smooth k _).mp
    (restrictedPull_smooth f hf L hL U V h k (Y.field k ω)
      ((Y.range_smooth k _).mpr ⟨ω,rfl⟩)))

def openPullLinear (X : OpenCalculus C B U) (Y : OpenCalculus A E V)
    (k : ℕ) : Y.complex.Obj k →ₗ[ℝ] X.complex.Obj k where
  toFun := openPullElement f hf L hL U V h X Y k
  map_add' ω η := by
    apply X.injective k
    rw [map_add, openPullElement_field, openPullElement_field, openPullElement_field,
      map_add, map_add]
  map_smul' r ω := by
    apply X.injective k
    rw [map_smul, openPullElement_field, openPullElement_field, map_smul, map_smul]
    rfl

@[simp] theorem openPullLinear_field (X : OpenCalculus C B U) (Y : OpenCalculus A E V)
    (k : ℕ) (ω : Y.complex.Obj k) :
    X.field k (openPullLinear f hf L hL U V h X Y k ω) =
      restrictedPullField f L U V h k (Y.field k ω) :=
  openPullElement_field f hf L hL U V h X Y k ω

/-- A global form is pulled back by the genuine tangent differential. -/
def globalPullLinear (k : ℕ) : J.forms k →ₗ[ℝ] K.forms k where
  toFun ω := ⟨FormPullbackData.pullbackField S T f L ω.val,
    (K.mem_forms k _).mpr (FormPullbackResults.pullback_smooth S T C A f hf L hL k
      (B k) (E k) ω.val ((J.mem_forms k _).mp ω.property))⟩
  map_add' ω η := by
    apply Subtype.ext
    funext p
    exact map_add (FormPullbackData.fiberPullback (V := TangentSpace S p)
      (W := TangentSpace T (f p)) k (L p)) _ _
  map_smul' r ω := by
    apply Subtype.ext
    funext p
    exact map_smul (FormPullbackData.fiberPullback (V := TangentSpace S p)
      (W := TangentSpace T (f p)) k (L p)) r _

def globalPullChain : ChainMap (globalComplex J) (globalComplex K) where
  map := globalPullLinear K J f hf L hL
  comm k ω := by
    apply Subtype.ext
    exact (ExteriorDerivativeResults.smooth_naturality S T C A B E K.D J.D
      K.axioms J.axioms f hf L hL k ω.val ((J.mem_forms k _).mp ω.property)).symm

include K J in
/-- Pullback commutes with each restricted differential by comparison of germs. -/
theorem openPullLinear_comm (X : OpenCalculus C B U) (Y : OpenCalculus A E V)
    (k : ℕ) (ω : Y.complex.Obj k) :
    X.complex.d k (openPullLinear f hf L hL U V h X Y k ω) =
      openPullLinear f hf L hL U V h X Y (k+1) (Y.complex.d k ω) := by
  apply X.injective (k+1)
  funext p
  obtain ⟨α,hα,he⟩ := exists_global_germ (E k) V (Y.field k ω)
    ((Y.range_smooth k _).mpr ⟨ω,rfl⟩) ⟨f p.val,h p.property⟩
  have hg := FormPullbackResults.pullback_smooth S T C A f hf L hL k
    (B k) (E k) α hα
  have hs : ∀ᶠ q in 𝓝 p.val,
      FormPullbackData.pullbackField S T f L α q =
        zeroExtend (X.field k (openPullLinear f hf L hL U V h X Y k ω)) q := by
    filter_upwards [U.isOpen.mem_nhds p.property, (hf p.val).1.eventually he] with q hqU hq
    rw [openPullLinear_field]
    unfold zeroExtend
    split_ifs with hqu
    · change FormPullbackData.fiberPullback (V := TangentSpace S q)
        (W := TangentSpace T (f q)) k (L q) (α (f q)) =
        FormPullbackData.fiberPullback (V := TangentSpace S q)
          (W := TangentSpace T (f q)) k (L q) (Y.field k ω ⟨f q,h hqu⟩)
      apply congrArg (FormPullbackData.fiberPullback (V := TangentSpace S q)
        (W := TangentSpace T (f q)) k (L q))
      change α (f q) = zeroExtend (Y.field k ω) (f q) at hq
      unfold zeroExtend at hq
      split_ifs at hq with hqV
      · exact hq
      · exact (hqV (h hqu)).elim
    · exact (hqu hqU).elim
  rw [restricted_derivative_eq_global K U
    (X.field k (openPullLinear f hf L hL U V h X Y k ω))
    (X.field (k+1) (X.complex.d k (openPullLinear f hf L hL U V h X Y k ω)))
    (X.coordinates k _) (FormPullbackData.pullbackField S T f L α) hg p hs]
  rw [openPullLinear_field]
  change K.D k (FormPullbackData.pullbackField S T f L α) p.val =
    FormPullbackData.fiberPullback (V := TangentSpace S p.val)
      (W := TangentSpace T (f p.val)) (k+1) (L p.val)
      (Y.field (k+1) (Y.complex.d k ω) ⟨f p.val,h p.property⟩)
  rw [restricted_derivative_eq_global J V (Y.field k ω)
    (Y.field (k+1) (Y.complex.d k ω)) (Y.coordinates k ω) α hα
    ⟨f p.val,h p.property⟩ he]
  exact congrFun (ExteriorDerivativeResults.smooth_naturality S T C A B E K.D J.D
    K.axioms J.axioms f hf L hL k α hα).symm p.val

def openPullChain (X : OpenCalculus C B U) (Y : OpenCalculus A E V) :
    ChainMap Y.complex X.complex where
  map := openPullLinear f hf L hL U V h X Y
  comm := openPullLinear_comm K J f hf L hL U V h X Y

end RestrictedPullback
end OpenForms
end SmoothManifolds.MayerVietorisData

namespace SmoothManifolds.MayerVietorisData
namespace OpenForms
open ModelData AtlasData TangentData BundleOperationsData CovectorData ExteriorData
  ExteriorDerivativeData DeRhamData MapData Set Filter
open scoped Topology
universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The geometric pullbacks form a morphism for any two cover realizations. -/
def coverPullback {n m : ℕ} {a b : ModelKind} {M N : Type u}
    [TopologicalSpace M] [TopologicalSpace N]
    {S : SmoothManifold n a M} {T : SmoothManifold m b N}
    {C : CotangentBundle S} {A : CotangentBundle T}
    {B : ∀ k, FormBundle C k} {E : ∀ k, FormBundle A k}
    {K : Calculus C B} {J : Calculus A E} {O : OpenCover M} {P : OpenCover N}
    (D : CoverComplex K O) (G : CoverComplex J P)
    (f : M → N) (hf : IsSmoothMap S T f)
    (L : (p : M) → TangentSpace S p →ₗ[ℝ] TangentSpace T (f p))
    (hL : ∀ p, DifferentialData.IsDifferential S T f p (L p))
    (hU : Set.MapsTo f O.U P.U) (hV : Set.MapsTo f O.V P.V) :
    CoverPullback D G f L hU hV := by
  let hI : Set.MapsTo f (O.U ⊓ O.V) (P.U ⊓ P.V) :=
    fun _ hp => ⟨hU hp.1,hV hp.2⟩
  let pu := openPullChain K J f hf L hL O.U P.U hU D.onU G.onU
  let pv := openPullChain K J f hf L hL O.V P.V hV D.onV G.onV
  let pi := openPullChain K J f hf L hL (O.U ⊓ O.V) (P.U ⊓ P.V) hI
    D.onOverlap G.onOverlap
  let pg := globalPullChain K J f hf L hL
  let pm : ChainMap (G.onU.complex.prod G.onV.complex)
      (D.onU.complex.prod D.onV.complex) := {
    map k := (pu.map k).prodMap (pv.map k)
    comm k ω := Prod.ext (pu.comm k ω.1) (pv.comm k ω.2) }
  refine {
    morphism := {
      left := pg
      middle := pm
      right := pi
      comm_r := ?_
      comm_q := ?_ }
    global_field := ?_
    U_field := ?_
    V_field := ?_
    overlap_field := ?_ }
  · intro k ω
    apply Prod.ext
    · apply D.onU.injective k
      funext p
      change D.onU.field k (openPullLinear f hf L hL O.U P.U hU D.onU G.onU k
        (G.sequence.r.map k ω).1) p =
        D.onU.field k (D.sequence.r.map k (pg.map k ω)).1 p
      rw [openPullLinear_field,D.restriction_U]
      change FormPullbackData.fiberPullback (V := TangentSpace S p.val)
        (W := TangentSpace T (f p.val)) k (L p.val)
        (G.onU.field k (G.sequence.r.map k ω).1 ⟨f p.val,hU p.property⟩) = _
      rw [G.restriction_U]
      rfl
    · apply D.onV.injective k
      funext p
      change D.onV.field k (openPullLinear f hf L hL O.V P.V hV D.onV G.onV k
        (G.sequence.r.map k ω).2) p =
        D.onV.field k (D.sequence.r.map k (pg.map k ω)).2 p
      rw [openPullLinear_field,D.restriction_V]
      change FormPullbackData.fiberPullback (V := TangentSpace S p.val)
        (W := TangentSpace T (f p.val)) k (L p.val)
        (G.onV.field k (G.sequence.r.map k ω).2 ⟨f p.val,hV p.property⟩) = _
      rw [G.restriction_V]
      rfl
  · intro k ω
    apply D.onOverlap.injective k
    funext p
    change D.onOverlap.field k
      (openPullLinear f hf L hL (O.U ⊓ O.V) (P.U ⊓ P.V) hI
        D.onOverlap G.onOverlap k (G.sequence.q.map k ω)) p =
      D.onOverlap.field k (D.sequence.q.map k (pm.map k ω)) p
    rw [openPullLinear_field,D.difference]
    change FormPullbackData.fiberPullback (V := TangentSpace S p.val)
      (W := TangentSpace T (f p.val)) k (L p.val)
      (G.onOverlap.field k (G.sequence.q.map k ω) ⟨f p.val,hI p.property⟩) =
      D.onV.field k (openPullLinear f hf L hL O.V P.V hV D.onV G.onV k ω.2)
        ⟨p.val,p.property.2⟩ -
      D.onU.field k (openPullLinear f hf L hL O.U P.U hU D.onU G.onU k ω.1)
        ⟨p.val,p.property.1⟩
    rw [G.difference]
    have hsub := map_sub
      (FormPullbackData.fiberPullback (V := TangentSpace S p.val)
        (W := TangentSpace T (f p.val)) k (L p.val))
      (G.onV.field k ω.2 ⟨f p.val,hV p.property.2⟩)
      (G.onU.field k ω.1 ⟨f p.val,hU p.property.1⟩)
    exact hsub.trans (congrArg₂ (fun x y : Fiber (TangentSpace S p.val) k => x-y)
      (congrFun (openPullLinear_field f hf L hL O.V P.V hV D.onV G.onV k ω.2)
        ⟨p.val,p.property.2⟩).symm
      (congrFun (openPullLinear_field f hf L hL O.U P.U hU D.onU G.onU k ω.1)
        ⟨p.val,p.property.1⟩).symm)
  · intro k ω
    rfl
  · intro k ω p
    exact congrFun (openPullLinear_field f hf L hL O.U P.U hU D.onU G.onU k ω.1) p
  · intro k ω p
    exact congrFun (openPullLinear_field f hf L hL O.V P.V hV D.onV G.onV k ω.2) p
  · intro k ω p
    exact congrFun (openPullLinear_field f hf L hL (O.U ⊓ O.V) (P.U ⊓ P.V) hI
      D.onOverlap G.onOverlap k ω) p

end OpenForms
end SmoothManifolds.MayerVietorisData

namespace SmoothManifolds.MayerVietorisResults
universe u

theorem cover_pullback_exists :
    Specs.SmoothManifolds.DeRham.MayerVietoris.cover_pullback_existsType.{u} := by
  intro n m a b M N _ _ S T C A B E K J O P D G f hf L hL hU hV
  exact ⟨MayerVietorisData.OpenForms.coverPullback D G f hf L hL hU hV⟩

end SmoothManifolds.MayerVietorisResults
