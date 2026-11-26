import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat

/-! Algebraic actions on the chamber and face cosets of a marked local group. -/

namespace LinearAlgebraicGroups.Specs.ExceptionalBuildingActions

open Set
open ExceptionalAffineRootSystems (ApartmentRoots alcoveStabilizer)
open ExceptionalAffineBruhat
open Pinning (BasedRootDatum)
open IntegralSemisimpleModel (Model integerAlgebra)
attribute [local instance] integerAlgebra
open scoped CategoryTheory.MonObj Classical Pointwise

universe u v

noncomputable section

section Local
variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
  {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
  {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
  {A : ApartmentRoots ℚ V J} {p : V}

variable (C : LocalComparison (j := j) (Wf := Wf) A p)
local notation "Ω" => alcoveStabilizer A (A.alcove p)
local notation "B" => A.SimpleWall p

def parahoric (T : Set B) : Subgroup G :=
  Subgroup.closure ((C.I : Set G) ∪ (fun w => (C.lift w : G)) ∘ C.coxeter.coxeter.simple '' T)

def lengthZeroNormalizer : Subgroup G :=
  ((((alcoveStabilizer A (A.alcove p)).map A.extendedAffineWeylGroup.subtype).comap
    C.affine).map C.N.subtype)

def typeChange (Q : C.TypeQuotient) : G →* Ω :=
  letI := Q.normal
  Q.quotient.toMonoidHom.comp (QuotientGroup.mk' C.G₀)

/-- Chambers as ambient left cosets with a type-preserving representative. -/
abbrev Chamber :=
  Set.range (fun g : C.G₀ => (QuotientGroup.mk (g : G) : G ⧸ C.I))

abbrev baseChamberStabilizer : Subgroup G := C.I ⊔ lengthZeroNormalizer C

/-- The data of the standard simplex used by the gluing construction. -/
structure Coordinates (Q : C.TypeQuotient) (X : Type v) where
  cotype : X → Set B
  perm : Ω →* Equiv.Perm X
  cotype_perm (ω : Ω) (t : X) :
    cotype (perm ω t) = Q.wallPerm ω '' cotype t

variable {C}

def gluing {X : Type v} (cotype : X → Set B) : Setoid (C.G₀ × X) where
  r g h := g.2 = h.2 ∧ (g.1 : G)⁻¹ * (h.1 : G) ∈ parahoric C (cotype g.2)
  iseqv := {
    refl := fun g => ⟨rfl, by simp⟩
    symm := by
      rintro g h ⟨he, hm⟩
      refine ⟨he.symm, ?_⟩
      rw [← he]
      simpa using (parahoric C (cotype g.2)).inv_mem hm
    trans := by
      rintro g h k ⟨he, hm⟩ ⟨he', hm'⟩
      refine ⟨he.trans he', ?_⟩
      rw [← he] at hm'
      simpa [mul_assoc] using (parahoric C (cotype g.2)).mul_mem hm hm' }

abbrev Point {X : Type v} (cotype : X → Set B) := Quotient (gluing (C := C) cotype)

def place {X : Type v} {cotype : X → Set B} (g : C.G₀) (t : X) :
    Point (C := C) cotype := Quotient.mk _ (g, t)

def openFace {X : Type v} {cotype : X → Set B} (g : C.G₀) (T : Set B) :
    Set (Point (C := C) cotype) := place g '' {t | cotype t = T}

def chamberPoints {X : Type v} {cotype : X → Set B} (g : C.G₀) :
    Set (Point (C := C) cotype) := Set.range (place g)

/-- The actual coset equivalence is induced by the inclusion of representatives. -/
structure NormalizerComparison (Q : C.TypeQuotient) where
  kernel : (typeChange C Q).ker = C.G₀
  label (n : C.N) (ω : Ω) (h : C.affine n = ω.val.val) :
    typeChange C Q n = ω
  normalizes : lengthZeroNormalizer C ≤ Subgroup.normalizer (C.I : Set G)
  intersection : C.G₀ ⊓ lengthZeroNormalizer C = C.T₀
  factorization (g : G) :
    ∃ a : C.G₀, g = (a : G) * (Q.lift (typeChange C Q g) : G)
  ordinary_product : (C.G₀ : Set G) * (lengthZeroNormalizer C : Set G) = Set.univ
  chamber_product : (baseChamberStabilizer C : Set G) =
    (C.I : Set G) * (lengthZeroNormalizer C : Set G)
  cosets : Chamber C ≃ (G ⧸ baseChamberStabilizer C)
  cosets_mk (g : C.G₀) :
    cosets ⟨QuotientGroup.mk (g : G), ⟨g, rfl⟩⟩ = QuotientGroup.mk (g : G)
  conjugates (n : C.N) (ω : Ω) (h : C.affine n = ω.val.val) (T : Set B) :
    (parahoric C T).map (MulAut.conj (n : G)).toMonoidHom =
      parahoric C (Q.wallPerm ω '' T)

structure AdjointAction {Q : C.TypeQuotient} {X : Type v} (S : Coordinates C Q X) where
  action : G →* Equiv.Perm (Point (C := C) S.cotype)
  on_place (g : G) (h : C.G₀) (t : X) :
    ∃ k : C.G₀, (k : G) = g * (h : G) * (Q.lift (typeChange C Q g) : G)⁻¹ ∧
      action g (place h t) = place k (S.perm (typeChange C Q g) t)
  ordinary (g h : C.G₀) (t : X) : action g (place h t) = place (g * h) t
  /-- The formula on representatives of the base apartment. -/
  normalizer (n : C.N) (w : A.affineWeylGroup)
      (h : (C.lift w : G) ∈ C.G₀) (t : X) :
    ∃ (v : A.affineWeylGroup) (hv : (C.lift v : G) ∈ C.G₀),
      v.val = C.affine n * w.val * (typeChange C Q n).val.val⁻¹ ∧
      action n (place (C := C) ⟨(C.lift w : G), h⟩ t) =
        place (C := C) ⟨(C.lift v : G), hv⟩ (S.perm (typeChange C Q n) t)
  chamber_stabilizer (h : ∃ t, S.cotype t = ∅) (g : G) :
    action g '' chamberPoints (cotype := S.cotype) 1 = chamberPoints 1 ↔
      g ∈ baseChamberStabilizer C
  face_stabilizer (T : Set B) (h : ∃ t, S.cotype t = T) (g : G) :
    action g '' openFace (cotype := S.cotype) 1 T = openFace 1 T ↔
      ∃ (a : parahoric C T) (ω : Ω), g = (a : G) * (Q.lift ω : G) ∧ Q.wallPerm ω '' T = T
  point_stabilizer (t : X) (g : G) :
    action g (place 1 t) = place 1 t ↔
      ∃ (a : parahoric C (S.cotype t)) (ω : Ω),
        g = (a : G) * (Q.lift ω : G) ∧ S.perm ω t = t
  stabilizer_types (t : X) (g : G) :
    action g (place 1 t) = place 1 t →
      Q.wallPerm (typeChange C Q g) '' S.cotype t = S.cotype t
  barycenter_stabilizer (t : X) (weight : X → B → ℝ) (hw : Function.Injective weight)
      (hperm : ∀ ω i, weight (S.perm ω t) (Q.wallPerm ω i) = weight t i)
      (r : ℝ) (hb : ∀ i, weight t i = if i ∈ S.cotype t then 0 else r) (g : G) :
    action g (place 1 t) = place 1 t ↔
      ∃ (a : parahoric C (S.cotype t)) (ω : Ω),
        g = (a : G) * (Q.lift ω : G) ∧ Q.wallPerm ω '' S.cotype t = S.cotype t

variable {Γ : Type u} [Group Γ]

/-- Marked affine transport for the coefficient operators on the actual points. -/
structure CoefficientTransport (Q : C.TypeQuotient) (ρ : Γ →* MulAut G) where
  affine : Γ →* (V ≃ᵃ[ℚ] V)
  walls : Γ →* Equiv.Perm B
  types : Γ →* MulAut Ω
  comparison (σ : Γ) : AutomorphismComparison C (ρ σ) (affine σ)
  wall (σ : Γ) (i : B) :
    affine σ '' A.wallHyperplane i.val = A.wallHyperplane (walls σ i).val
  simple_label (σ : Γ) (i : B) :
    (C.coxeter.coxeter.simple (walls σ i)).val =
      affine σ * (C.coxeter.coxeter.simple i).val * (affine σ)⁻¹
  type_transport (σ : Γ) :
    TypeQuotientTransport Q Q (ρ σ).toMonoidHom (types σ).toMonoidHom

/-- The coefficient action and every cocycle twist on the same glued points. -/
structure CoefficientAction {Q : C.TypeQuotient} {X : Type v} {S : Coordinates C Q X}
    (ad : AdjointAction S) {ρ : Γ →* MulAut G} (R : CoefficientTransport Q ρ)
    (perm : Γ →* Equiv.Perm X) where
  type_equivariance (σ : Γ) (g : G) :
    typeChange C Q (ρ σ g) = R.types σ (typeChange C Q g)
  wall_compat (σ : Γ) (ω : Ω) :
    R.walls σ * Q.wallPerm ω = Q.wallPerm (R.types σ ω) * R.walls σ
  parahoric_equivariance (σ : Γ) (T : Set B) :
    (parahoric C T).map (ρ σ).toMonoidHom = parahoric C (R.walls σ '' T)
  action : Γ →* Equiv.Perm (Point (C := C) S.cotype)
  on_place (σ : Γ) (g : C.G₀) (t : X) :
    ∃ h : C.G₀, (h : G) = ρ σ g ∧ action σ (place g t) = place h (perm σ t)
  compatible (σ : Γ) (g : G) (x : Point (C := C) S.cotype) :
    action σ (ad.action g x) = ad.action (ρ σ g) (action σ x)
  twist (a : Γ → G) (ha : ∀ σ τ, a (σ * τ) = a σ * ρ σ (a τ)) :
    ∃ (act : Γ →* Equiv.Perm (Point (C := C) S.cotype))
      (types : Γ →* Equiv.Perm B),
      (∀ σ x, act σ x = ad.action (a σ) (action σ x)) ∧
      (∀ σ, types σ = Q.wallPerm (typeChange C Q (a σ)) * R.walls σ) ∧
      ∀ σ g t, ∃ h : C.G₀,
        act σ (place g t) = place h (S.perm (typeChange C Q (a σ)) (perm σ t)) ∧
        S.cotype (S.perm (typeChange C Q (a σ)) (perm σ t)) = types σ '' S.cotype t

end Local

def NormalizerActions : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
    {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
    {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
    {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (j := j) (Wf := Wf) A p) {q : ℕ},
    C.Bruhat q → ∀ Q : C.TypeQuotient, Nonempty (NormalizerComparison Q)

def AdjointActions : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
    {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
    {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
    {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (j := j) (Wf := Wf) A p) {q : ℕ},
    C.Bruhat q → ∀ (Q : C.TypeQuotient) (X : Type v) (S : Coordinates C Q X),
    Nonempty (AdjointAction S)

def CoefficientActions : Prop :=
  ∀ {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] {D : BasedRootDatum.{u}} {M : Model D}
    {G Wf : Type u} [Group G] [Group Wf] {j : G →* FieldPoints M K}
    {V : Type u} {J : Type v} [AddCommGroup V] [Module ℚ V]
    {A : ApartmentRoots ℚ V J} {p : V}
    (C : LocalComparison (j := j) (Wf := Wf) A p) {q : ℕ},
    C.Bruhat q → ∀ (Q : C.TypeQuotient) (X : Type v) (S : Coordinates C Q X)
      (ad : AdjointAction S) (Γ : Type u) [Group Γ] (ρ : Γ →* MulAut G)
      (R : CoefficientTransport Q ρ) (perm : Γ →* Equiv.Perm X),
    (∀ σ t, S.cotype (perm σ t) = R.walls σ '' S.cotype t) →
    (∀ σ ω, perm σ * S.perm ω = S.perm (R.types σ ω) * perm σ) →
    Nonempty (CoefficientAction ad R perm)


end

end LinearAlgebraicGroups.Specs.ExceptionalBuildingActions
