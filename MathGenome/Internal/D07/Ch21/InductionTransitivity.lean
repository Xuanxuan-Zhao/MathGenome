import MathGenome.Internal.Specs.D07.Ch21.InductionTransitivity
import MathGenome.Internal.D07.Ch21.InducedCharacter

namespace D07.Ch21.InductionTransitivity

universe u v w
noncomputable section
open Representation
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
open Specs.D07.Ch21.InductionTransitivity
open D07.Ch21.InductionCosetModelInductionConventionBridge

section Transitivity

variable {G : Type u} [Group G] {H K : Subgroup G} (hHK : H ≤ K)
  {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)

/-- Descend the inner relation, with the outer group coordinate held fixed. -/
def flattenInner (g : G) :
    NotesInd (H.subgroupOf K) (innerInput hHK ρ) →ₗ[ℂ] NotesInd H ρ :=
  notesLift _ _ (fun k => notesMk H ρ (g * (k : G))) (by
    intro k h v
    simpa [innerInput, Subgroup.subgroupOfEquivOfLe, mul_assoc] using
      notes_balance H ρ (g * (k : G)) (Subgroup.subgroupOfEquivOfLe hHK h) v)

@[simp] lemma flattenInner_mk (g : G) (k : K) (v : V) :
    flattenInner hHK ρ g (notesMk _ (innerInput hHK ρ) k v) =
      notesMk H ρ (g * (k : G)) v := notesLift_mk _ _ _ _ _ _

lemma flattenInner_balance (g : G) (k₀ : K) :
    flattenInner hHK ρ (g * (k₀ : G)) =
      (flattenInner hHK ρ g).comp (notesRep _ (innerInput hHK ρ) k₀) := by
  apply notes_hom_ext
  intro k v
  simp [mul_assoc]

/-- Descend the outer relation: both sides give [g k₀ k,v]. -/
def flatten :
    NotesInd K (notesRep _ (innerInput hHK ρ)) →ₗ[ℂ] NotesInd H ρ :=
  notesLift K _ (flattenInner hHK ρ) (by
    intro g k x
    exact LinearMap.congr_fun (flattenInner_balance hHK ρ g k) x)

@[simp] lemma flatten_mk (g : G) (x : NotesInd _ (innerInput hHK ρ)) :
    flatten hHK ρ (notesMk K _ g x) = flattenInner hHK ρ g x :=
  notesLift_mk _ _ _ _ _ _

/-- Insert [1,v]. The H-relation becomes the outer K-relation followed by
the inner H-relation. -/
def unflatten : NotesInd H ρ →ₗ[ℂ] NotesInd K (notesRep _ (innerInput hHK ρ)) :=
  notesLift H ρ (fun g =>
    (notesMk K _ g).comp (notesMk _ (innerInput hHK ρ) 1)) (by
    intro g h v
    change notesMk K _ (g * (h : G)) (notesMk _ (innerInput hHK ρ) 1 v) =
      notesMk K _ g (notesMk _ (innerInput hHK ρ) 1 (ρ h v))
    refine (notes_balance K (notesRep _ (innerInput hHK ρ)) g
      (Subgroup.inclusion hHK h) (notesMk _ (innerInput hHK ρ) 1 v)).trans ?_
    rw [notesRep_mk, mul_one]
    congr 1
    have he : innerInput hHK ρ ((Subgroup.subgroupOfEquivOfLe hHK).symm h) = ρ h := by
      change ρ ((Subgroup.subgroupOfEquivOfLe hHK)
        ((Subgroup.subgroupOfEquivOfLe hHK).symm h)) = ρ h
      rw [MulEquiv.apply_symm_apply]
    have hi : (((Subgroup.subgroupOfEquivOfLe hHK).symm h : H.subgroupOf K) : K) =
        Subgroup.inclusion hHK h := rfl
    simpa only [one_mul, hi, he] using
      notes_balance (H.subgroupOf K) (innerInput hHK ρ) 1
        ((Subgroup.subgroupOfEquivOfLe hHK).symm h) v)

@[simp] lemma unflatten_mk (g : G) (v : V) :
    unflatten hHK ρ (notesMk H ρ g v) =
      notesMk K _ g (notesMk _ (innerInput hHK ρ) 1 v) :=
  notesLift_mk _ _ _ _ _ _

/-- Generator extensionality for the two successive quotients. -/
lemma nested_hom_ext {W : Type w} [AddCommGroup W] [Module ℂ W]
    {f g : NotesInd K (notesRep _ (innerInput hHK ρ)) →ₗ[ℂ] W}
    (h : ∀ a (k : K) v,
      f (notesMk K _ a (notesMk _ (innerInput hHK ρ) k v)) =
      g (notesMk K _ a (notesMk _ (innerInput hHK ρ) k v))) : f = g := by
  apply notes_hom_ext
  intro a x
  exact LinearMap.congr_fun (notes_hom_ext (H.subgroupOf K) (innerInput hHK ρ)
    (f := f.comp (notesMk K _ a)) (g := g.comp (notesMk K _ a)) (h a)) x

/-- Both composites are identities on the spanning quotient generators. -/
def transitivityLinearEquiv :
    NotesInd K (notesRep _ (innerInput hHK ρ)) ≃ₗ[ℂ] NotesInd H ρ :=
  LinearEquiv.ofLinearMap (flatten hHK ρ) (unflatten hHK ρ)
    (by
      apply notes_hom_ext
      intro g v
      change flatten hHK ρ (unflatten hHK ρ (notesMk H ρ g v)) = _
      simp)
    (by
      apply nested_hom_ext hHK ρ
      intro g k v
      change unflatten hHK ρ (flatten hHK ρ
        (notesMk K _ g (notesMk _ (innerInput hHK ρ) k v))) = _
      rw [flatten_mk, flattenInner_mk, unflatten_mk, notes_balance, notesRep_mk, mul_one]
      rfl)

/-- The generator formula commutes with left G-multiplication. -/
def transitivityEquiv :
    (notesRep K (notesRep _ (innerInput hHK ρ))).Equiv (notesRep H ρ) :=
  Representation.Equiv.mk (transitivityLinearEquiv hHK ρ) (by
    intro a
    apply nested_hom_ext hHK ρ
    intro g k v
    change flatten hHK ρ (notesRep K _ a
      (notesMk K _ g (notesMk _ (innerInput hHK ρ) k v))) =
        notesRep H ρ a (flatten hHK ρ
          (notesMk K _ g (notesMk _ (innerInput hHK ρ) k v)))
    simp [mul_assoc])

theorem transitivity : Transitivity.{u,v} := by
  intro G _ _ H K hHK V _ _ ρ
  refine ⟨notesRep _ (innerInput hHK ρ), notesRep K _, notesRep H ρ,
    transitivityEquiv hHK ρ, notesRep_mk _ _, notesRep_mk _ _, notesRep_mk _ _, ?_, ?_⟩
  · intro g k v
    exact (flatten_mk hHK ρ g _).trans (flattenInner_mk hHK ρ g k v)
  · exact unflatten_mk hHK ρ

end Transitivity

section Additivity

variable {G : Type u} [Group G] (H : Subgroup G)
  {V : Type v} {W : Type w} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H V) (θ : Representation ℂ H W)

/-- A balanced family gives the componentwise map on the induced quotient. -/
def splitSum : NotesInd H (ρ.prod θ) →ₗ[ℂ] NotesInd H ρ × NotesInd H θ :=
  notesLift H (ρ.prod θ) (fun g =>
    ((notesMk H ρ g).comp (LinearMap.fst ℂ V W)).prod
      ((notesMk H θ g).comp (LinearMap.snd ℂ V W))) (by
    intro g h v
    apply Prod.ext <;> exact notes_balance H _ g h _)

@[simp] lemma splitSum_mk (g : G) (v : V) (w : W) :
    splitSum H ρ θ (notesMk H (ρ.prod θ) g (v, w)) =
      (notesMk H ρ g v, notesMk H θ g w) := notesLift_mk _ _ _ _ _ _

/-- Induction of the first summand inclusion. -/
def sumInl : NotesInd H ρ →ₗ[ℂ] NotesInd H (ρ.prod θ) :=
  notesLift H ρ (fun g => (notesMk H (ρ.prod θ) g).comp (LinearMap.inl ℂ V W)) (by
    intro g h v
    simpa using notes_balance H (ρ.prod θ) g h (v, 0))

/-- Induction of the second summand inclusion. -/
def sumInr : NotesInd H θ →ₗ[ℂ] NotesInd H (ρ.prod θ) :=
  notesLift H θ (fun g => (notesMk H (ρ.prod θ) g).comp (LinearMap.inr ℂ V W)) (by
    intro g h w
    simpa using notes_balance H (ρ.prod θ) g h (0, w))

@[simp] lemma sumInl_mk (g : G) (v : V) :
    sumInl H ρ θ (notesMk H ρ g v) = notesMk H (ρ.prod θ) g (v, 0) :=
  notesLift_mk _ _ _ _ _ _

@[simp] lemma sumInr_mk (g : G) (w : W) :
    sumInr H ρ θ (notesMk H θ g w) = notesMk H (ρ.prod θ) g (0, w) :=
  notesLift_mk _ _ _ _ _ _

/-- The inverse is the sum of the induced inclusions. -/
def joinSum : NotesInd H ρ × NotesInd H θ →ₗ[ℂ] NotesInd H (ρ.prod θ) :=
  (sumInl H ρ θ).coprod (sumInr H ρ θ)

/-- The quotient maps are inverse, also when either input space is zero. -/
def additivityLinearEquiv :
    NotesInd H (ρ.prod θ) ≃ₗ[ℂ] NotesInd H ρ × NotesInd H θ :=
  LinearEquiv.ofLinearMap (splitSum H ρ θ) (joinSum H ρ θ)
    (by
      apply LinearMap.prod_ext
      · apply notes_hom_ext
        intro g v
        change splitSum H ρ θ (joinSum H ρ θ (notesMk H ρ g v, 0)) = _
        simp [joinSum]
      · apply notes_hom_ext
        intro g w
        change splitSum H ρ θ (joinSum H ρ θ (0, notesMk H θ g w)) = _
        simp [joinSum])
    (by
      apply notes_hom_ext
      intro g v
      rcases v with ⟨v, w⟩
      change joinSum H ρ θ (splitSum H ρ θ (notesMk H (ρ.prod θ) g (v, w))) = _
      rw [splitSum_mk]
      simp only [joinSum, LinearMap.coprod_apply, sumInl_mk, sumInr_mk, ← map_add]
      simp)

/-- Splitting the two summands commutes with left G-translation. -/
def additivityEquiv :
    (notesRep H (ρ.prod θ)).Equiv ((notesRep H ρ).prod (notesRep H θ)) :=
  Representation.Equiv.mk (additivityLinearEquiv H ρ θ) (by
    intro a
    apply notes_hom_ext
    intro g v
    rcases v with ⟨v, w⟩
    change splitSum H ρ θ (notesRep H (ρ.prod θ) a
      (notesMk H (ρ.prod θ) g (v, w))) =
        ((notesRep H ρ).prod (notesRep H θ)) a
          (splitSum H ρ θ (notesMk H (ρ.prod θ) g (v, w)))
    simp)

theorem additivity : Additivity.{u,v,w} := by
  intro G _ _ H V W _ _ _ _ ρ θ
  refine ⟨notesRep H ρ, notesRep H θ, notesRep H (ρ.prod θ),
    additivityEquiv H ρ θ, notesRep_mk _ _, notesRep_mk _ _, notesRep_mk _ _,
    splitSum_mk H ρ θ, ?_, ?_⟩
  · intro g v
    change joinSum H ρ θ (notesMk H ρ g v, 0) = _
    simp [joinSum]
  · intro g w
    change joinSum H ρ θ (0, notesMk H θ g w) = _
    simp [joinSum]

end Additivity

section Characters

open Specs.D07.Ch21.InducedCharacter
open Specs.D07.Ch17.Characters

/-- The shared induced-character theorem applies to the constructed quotient action. -/
lemma induced_character_eq {G : Type u} [Group G] [Fintype G] (H : Subgroup G)
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ H V) (g : G) :
    LinearMap.trace ℂ (NotesInd H ρ) (notesRep H ρ g) =
      induceClassFunction H (characterValue ℂ H V ρ) g :=
  (D07.Ch21.InducedCharacter.character_formulas G H V ρ (notesRep H ρ)
    (notesRep_mk H ρ) Quotient.out QuotientGroup.out_eq' g).2

theorem character_additivity : CharacterAdditivity.{u,v,w} := by
  intro G _ _ H V W _ _ _ _ _ _ ρ θ
  haveI := (D07.Ch21.InductionCosetModel.dimension G H V ρ).1
  haveI := (D07.Ch21.InductionCosetModel.dimension G H W θ).1
  haveI := (D07.Ch21.InductionCosetModel.dimension G H (V × W) (ρ.prod θ)).1
  have hp : characterValue ℂ H (V × W) (ρ.prod θ) =
      fun h => characterValue ℂ H V ρ h + characterValue ℂ H W θ h := by
    funext h
    exact LinearMap.trace_prodMap' (ρ h) (θ h)
  have he := D07.Ch17.Characters.character_equivalence ℂ G
    (NotesInd H (ρ.prod θ)) (NotesInd H ρ × NotesInd H θ)
    (notesRep H (ρ.prod θ)) ((notesRep H ρ).prod (notesRep H θ))
    ⟨additivityEquiv H ρ θ⟩
  funext g
  calc
    induceClassFunction H
        (fun h => characterValue ℂ H V ρ h + characterValue ℂ H W θ h) g =
        LinearMap.trace ℂ (NotesInd H (ρ.prod θ)) (notesRep H (ρ.prod θ) g) := by
      rw [← hp]
      exact (induced_character_eq H (ρ.prod θ) g).symm
    _ = LinearMap.trace ℂ (NotesInd H ρ) (notesRep H ρ g) +
        LinearMap.trace ℂ (NotesInd H θ) (notesRep H θ g) :=
      (congrFun he g).trans (LinearMap.trace_prodMap' _ _)
    _ = _ := by rw [induced_character_eq, induced_character_eq]

theorem character_transitivity : CharacterTransitivity.{u,v} := by
  intro G _ _ H K hHK V _ _ _ ρ
  letI := Fintype.ofFinite K
  haveI := (D07.Ch21.InductionCosetModel.dimension K (H.subgroupOf K) V
    (innerInput hHK ρ)).1
  haveI := (D07.Ch21.InductionCosetModel.dimension G K
    (NotesInd (H.subgroupOf K) (innerInput hHK ρ))
    (notesRep _ (innerInput hHK ρ))).1
  haveI := (D07.Ch21.InductionCosetModel.dimension G H V ρ).1
  have hi : induceClassFunction (H.subgroupOf K)
      (characterValue ℂ (H.subgroupOf K) V (innerInput hHK ρ)) =
      characterValue ℂ K (NotesInd (H.subgroupOf K) (innerInput hHK ρ))
        (notesRep _ (innerInput hHK ρ)) := by
    funext k
    exact (induced_character_eq _ (innerInput hHK ρ) k).symm
  have he := D07.Ch17.Characters.character_equivalence ℂ G
    (NotesInd K (notesRep _ (innerInput hHK ρ))) (NotesInd H ρ)
    (notesRep K (notesRep _ (innerInput hHK ρ))) (notesRep H ρ)
    ⟨transitivityEquiv hHK ρ⟩
  rw [hi]
  funext g
  calc
    _ = LinearMap.trace ℂ (NotesInd K (notesRep _ (innerInput hHK ρ)))
        (notesRep K (notesRep _ (innerInput hHK ρ)) g) :=
      (induced_character_eq K (notesRep _ (innerInput hHK ρ)) g).symm
    _ = LinearMap.trace ℂ (NotesInd H ρ) (notesRep H ρ g) := congrFun he g
    _ = _ := induced_character_eq H ρ g

end Characters

end
end D07.Ch21.InductionTransitivity
