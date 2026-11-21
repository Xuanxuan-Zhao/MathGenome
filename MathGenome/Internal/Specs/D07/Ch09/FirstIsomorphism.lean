import MathGenome.Internal.Specs.D07.Ch08.KernelImage
import MathGenome.Internal.Specs.D07.Ch08.InjectiveKernel
import MathGenome.Internal.Specs.D07.Ch09.QuotientLift

/-!
Independent specifications for K07.09.first_isomorphism,
paper.tex:1569–1583. The source rings are associative and unital;
commutativity and nontriviality are not assumed. The quotient uses the
canonical two-sided kernel ideal, and `f.range` is the actual image subring.
The representative formulas specify the induced isomorphisms themselves.
-/

universe u v

namespace Specs.D07.Ch09.FirstIsomorphism

/-- The quotient by the kernel is isomorphic to the image by `[a] ↦ f(a)`. -/
def FirstIsomorphism : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S),
    ∃ e : R ⧸ RingHom.ker f ≃+* f.range,
      ∀ a : R, (e (Ideal.Quotient.mk (RingHom.ker f) a) : S) = f a

/-- For an onto homomorphism the induced isomorphism has codomain `S`. -/
def FirstIsomorphismOfSurjective : Prop :=
  ∀ (R : Type u) (S : Type v) [Ring R] [Ring S] (f : R →+* S),
    Function.Surjective f →
      ∃ e : R ⧸ RingHom.ker f ≃+* S,
        ∀ a : R, e (Ideal.Quotient.mk (RingHom.ker f) a) = f a

end Specs.D07.Ch09.FirstIsomorphism
