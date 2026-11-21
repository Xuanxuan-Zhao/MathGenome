import MathGenome.Internal.Specs.D07.Ch11.GaussContent
import MathGenome.Internal.D07.Ch11.ContentPrimitive

/-!
Gauss's content theorem, with association invariant under all content choices.
The library proves content multiplicativity up to association over a gcd
domain; every UFD has such a structure. It is chosen locally, so the theorem
does not impose a normalization hypothesis on the original coefficient ring.
-/

universe u

namespace D07.Ch11.GaussContent

open Polynomial Specs.D07.Ch11.ContentPrimitive Specs.D07.Ch11.GaussContent

theorem primitiveProduct : PrimitiveProduct.{u} := by
  intro R _ _ _ f g hf hg
  let := contentStructure R
  exact hf.mul hg

theorem chosenContentProductAssociated : ChosenContentProductAssociated.{u} := by
  intro R _ _ _ f g
  let := contentStructure R
  change Associated (f * g).content (f.content * g.content)
  exact Polynomial.associated_content_mul f g

theorem contentProductAssociated : ContentProductAssociated.{u} := by
  intro R _ _ _ f g a b c ha hb hc
  have hfa := (ContentPrimitive.contentAssociateChoice R f a).mp ha
  have hgb := (ContentPrimitive.contentAssociateChoice R g b).mp hb
  have hfgc := (ContentPrimitive.contentAssociateChoice R (f * g) c).mp hc
  exact hfgc.trans ((chosenContentProductAssociated R f g).trans (hfa.mul_mul hgb).symm)

theorem productIsContent : ProductIsContent.{u} := by
  intro R _ _ _ f g a b ha hb
  apply (ContentPrimitive.contentAssociateChoice R (f * g) (a * b)).mpr
  exact (contentProductAssociated R f g a b (content (f * g)) ha hb
    (ContentPrimitive.contentIsGcd R (f * g))).symm

theorem normalizedContentProduct : NormalizedContentProduct.{u} := by
  intro R _ _ _ _ f g
  exact Polynomial.content_mul

end D07.Ch11.GaussContent
