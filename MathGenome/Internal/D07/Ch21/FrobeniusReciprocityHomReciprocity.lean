import MathGenome.Internal.Specs.D07.Ch21.FrobeniusReciprocityHomReciprocity
import MathGenome.Internal.D07.Ch21.InductionCosetModelInductionConventionBridge

namespace D07.Ch21.FrobeniusReciprocityHomReciprocity

universe u v v' w w'
noncomputable section
open Representation
open Specs.D07.Ch21.InductionCosetModelInductionConventionBridge
open D07.Ch21.InductionCosetModelInductionConventionBridge
open Specs.D07.Ch21.FrobeniusReciprocityHomReciprocity

variable {G : Type u} [Group G] (H : Subgroup G)
  {V : Type v} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
  {W : Type w} [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ G W)
  (σ : Representation ℂ G (NotesInd H ρ)) (hσ : IsInducedAction σ)

/-- Evaluation at `[1,v]` is H-equivariant by the quotient balancing relation. -/
def evaluate (T : IntertwiningMap σ τ) : IntertwiningMap ρ (τ.comp H.subtype) where
  toLinearMap := T.toLinearMap.comp (notesMk H ρ 1)
  isIntertwining' h := by
    ext v
    change T (notesMk H ρ 1 (ρ h v)) = τ (h : G) (T (notesMk H ρ 1 v))
    have hb : notesMk H ρ 1 (ρ h v) = σ (h : G) (notesMk H ρ 1 v) := by
      rw [hσ]
      simpa only [one_mul, mul_one] using (notes_balance H ρ 1 h v).symm
    rw [hb]
    exact congrArg (fun f : NotesInd H ρ →ₗ[ℂ] W => f (notesMk H ρ 1 v))
      (T.isIntertwining' (h : G))

@[simp] lemma evaluate_apply (T : IntertwiningMap σ τ) (v : V) :
    evaluate H ρ τ σ hσ T v = T (notesMk H ρ 1 v) := rfl

/-- The formula g A(v) is balanced before passing to the quotient. -/
lemma extension_balanced (A : IntertwiningMap ρ (τ.comp H.subtype))
    (g : G) (h : H) (v : V) :
    (τ (g * (h : G))).comp A.toLinearMap v = (τ g).comp A.toLinearMap (ρ h v) := by
  change τ (g * (h : G)) (A v) = τ g (A (ρ h v))
  rw [A.isIntertwining]
  exact congrArg (fun f : Module.End ℂ W => f (A v)) (map_mul τ g (h : G))

/-- The tensor universal property and the relation subspace give the reverse map. -/
def extend (A : IntertwiningMap ρ (τ.comp H.subtype)) : IntertwiningMap σ τ where
  toLinearMap := notesLift H ρ (fun g => (τ g).comp A.toLinearMap)
    (extension_balanced H ρ τ A)
  isIntertwining' k := by
    apply notes_hom_ext
    intro g v
    change notesLift H ρ (fun g => (τ g).comp A.toLinearMap)
      (extension_balanced H ρ τ A) (σ k (notesMk H ρ g v)) =
      τ k (notesLift H ρ (fun g => (τ g).comp A.toLinearMap)
        (extension_balanced H ρ τ A) (notesMk H ρ g v))
    rw [hσ, notesLift_mk, notesLift_mk]
    exact congrArg (fun f : Module.End ℂ W => f (A v)) (map_mul τ k g)

@[simp] lemma extend_mk (A : IntertwiningMap ρ (τ.comp H.subtype)) (g : G) (v : V) :
    extend H ρ τ σ hσ A (notesMk H ρ g v) = τ g (A v) :=
  notesLift_mk H ρ (fun g => (τ g).comp A.toLinearMap)
    (extension_balanced H ρ τ A) g v

lemma extend_evaluate (T : IntertwiningMap σ τ) :
    extend H ρ τ σ hσ (evaluate H ρ τ σ hσ T) = T := by
  apply IntertwiningMap.ext
  apply notes_hom_ext
  intro g v
  change extend H ρ τ σ hσ (evaluate H ρ τ σ hσ T) (notesMk H ρ g v) = _
  rw [extend_mk, evaluate_apply]
  have ht : T (σ g (notesMk H ρ 1 v)) = τ g (T (notesMk H ρ 1 v)) :=
    congrArg (fun f : NotesInd H ρ →ₗ[ℂ] W => f (notesMk H ρ 1 v))
      (T.isIntertwining' g)
  rw [hσ, mul_one] at ht
  exact ht.symm

lemma evaluate_extend (A : IntertwiningMap ρ (τ.comp H.subtype)) :
    evaluate H ρ τ σ hσ (extend H ρ τ σ hσ A) = A := by
  apply IntertwiningMap.ext
  ext v
  change extend H ρ τ σ hσ A (notesMk H ρ 1 v) = A v
  simp

/-- The source's Hom isomorphism, linear over C and valid in arbitrary dimension. -/
def homEquiv : IntertwiningMap σ τ ≃ₗ[ℂ] IntertwiningMap ρ (τ.comp H.subtype) where
  toFun := evaluate H ρ τ σ hσ
  invFun := extend H ρ τ σ hσ
  left_inv := extend_evaluate H ρ τ σ hσ
  right_inv := evaluate_extend H ρ τ σ hσ
  map_add' T U := by
    apply IntertwiningMap.ext
    ext v
    rfl
  map_smul' c T := by
    apply IntertwiningMap.ext
    ext v
    rfl

lemma homEquiv_formulas : ReciprocityFormulas (homEquiv H ρ τ σ hσ) :=
  ⟨fun _ _ => rfl, extend_mk H ρ τ σ hσ⟩

/-- Frobenius reciprocity on any action with the prescribed generator values. -/
theorem any_induced_action : AnyInducedAction.{u,v,w} := by
  intro G _ _ H V _ _ ρ σ hσ W _ _ τ
  exact ⟨homEquiv H ρ τ σ hσ, homEquiv_formulas H ρ τ σ hσ⟩

/-- In particular it holds for the upstream action descended from left tensor
multiplication, uniformly in the target W. -/
theorem hom_reciprocity : HomReciprocity.{u,v,w} := by
  intro G _ _ H V _ _ ρ
  refine ⟨notesRep H ρ, notesRep_quotient H ρ, notesRep_mk H ρ, ?_⟩
  intro W _ _ τ
  exact ⟨homEquiv H ρ τ (notesRep H ρ) (notesRep_mk H ρ),
    homEquiv_formulas H ρ τ (notesRep H ρ) (notesRep_mk H ρ)⟩


section Morphisms

variable {V' : Type v'} [AddCommGroup V'] [Module ℂ V']
  (ρ' : Representation ℂ H V')
  (σ' : Representation ℂ G (NotesInd H ρ')) (hσ' : IsInducedAction σ')

/-- An H-intertwiner carries the balancing relation to the same relation
for the target representation. -/
lemma inducedMap_balanced (a : IntertwiningMap ρ ρ') (g : G) (h : H) (v : V) :
    (notesMk H ρ' (g * (h : G))).comp a.toLinearMap v =
      (notesMk H ρ' g).comp a.toLinearMap (ρ h v) := by
  change notesMk H ρ' (g * (h : G)) (a v) = notesMk H ρ' g (a (ρ h v))
  rw [notes_balance, a.isIntertwining]

/-- Induction on morphisms, constructed on the source's quotient itself. -/
def inducedMap (a : IntertwiningMap ρ ρ') : IntertwiningMap σ σ' where
  toLinearMap := notesLift H ρ (fun g => (notesMk H ρ' g).comp a.toLinearMap)
    (inducedMap_balanced H ρ ρ' a)
  isIntertwining' k := by
    apply notes_hom_ext
    intro g v
    change notesLift H ρ (fun g => (notesMk H ρ' g).comp a.toLinearMap)
      (inducedMap_balanced H ρ ρ' a) (σ k (notesMk H ρ g v)) =
      σ' k (notesLift H ρ (fun g => (notesMk H ρ' g).comp a.toLinearMap)
        (inducedMap_balanced H ρ ρ' a) (notesMk H ρ g v))
    rw [hσ, notesLift_mk, notesLift_mk]
    exact (hσ' k g (a v)).symm

@[simp] lemma inducedMap_mk (a : IntertwiningMap ρ ρ') (g : G) (v : V) :
    inducedMap H ρ σ hσ ρ' σ' hσ' a (notesMk H ρ g v) = notesMk H ρ' g (a v) :=
  notesLift_mk H ρ (fun g => (notesMk H ρ' g).comp a.toLinearMap)
    (inducedMap_balanced H ρ ρ' a) g v

end Morphisms

/-- The generator formula uniquely determines the equivariant induced map. -/
theorem induced_morphism : InducedMorphism.{u,v,v'} := by
  intro G _ _ H V V' _ _ _ _ ρ ρ' σ σ' hσ hσ' a
  refine ⟨inducedMap H ρ σ hσ ρ' σ' hσ' a,
    inducedMap_mk H ρ σ hσ ρ' σ' hσ' a, ?_⟩
  intro i hi
  apply IntertwiningMap.ext
  apply notes_hom_ext
  intro g v
  change i (notesMk H ρ g v) = inducedMap H ρ σ hσ ρ' σ' hσ' a (notesMk H ρ g v)
  rw [hi, inducedMap_mk]

/-- The square for precomposition by an induced H-map and postcomposition by
a G-map commutes. It holds for any choices satisfying the specified formulas. -/
theorem naturality : Naturality.{u,v,v',w,w'} := by
  intro G _ _ H V V' W W' _ _ _ _ _ _ _ _ ρ ρ' τ τ' σ σ' a b i hi e e' he he' T v
  rw [he'.1]
  change b (T (i (notesMk H ρ' 1 v))) = b (e T (a v))
  rw [hi, he.1]

end
end D07.Ch21.FrobeniusReciprocityHomReciprocity
