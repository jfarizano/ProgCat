open import Categories
open import Categories.Products
open import Categories.Coproducts
open import Categories.Initial
open import Categories.Iso


-- Para la demostración asumir que la CCC ya tiene inicial y coproducto
module DemFinal.Distributive {a}{b}{C : Cat {a}{b}}
                                          (hasProducts : Products C)
                                          (hasCoproducts : Coproducts C)
                                          (I : Cat.Obj C)
                                          (hasInitial : Initial C I)
                                          where

open import Library hiding (_×_)

open Cat C
open Products hasProducts
open Coproducts hasCoproducts
open Initial hasInitial renaming (law to lawInit)

undistl : ∀{X Y Z : Obj} → Hom ((X × Z) + (Y × Z)) ((X + Y) × Z)
undistl = [ ⟨ inl ∙ π₁ , π₂ ⟩ , ⟨ inr ∙ π₁ , π₂ ⟩ ]

unnull : ∀{X : Obj} → Hom I (I × X)
unnull = ⟨ iden , i ⟩

record Dist : Set (a ⊔ b) where
  field
    distl : ∀{X Y Z} → Iso C (undistl {X} {Y} {Z})
    null : ∀{X} → Iso C (unnull {X})