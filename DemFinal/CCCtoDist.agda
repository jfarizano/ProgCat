open import Library hiding (_×_ ; curry ; uncurry)
open import Categories
open import Categories.Products
open import Categories.Coproducts
open import Categories.Initial
open import Categories.Terminal
open import Categories.Iso

module DemFinal.CCCtoDist {a}{b}{C : Cat {a}{b}}
                                        (hasProducts : Products C)
                                        (hasCoproducts : Coproducts C)
                                        (I : Cat.Obj C)
                                        (hasInitial : Initial C I)
                                        (T : Cat.Obj C)
                                        (hasTerminal : Terminal C T)
                                        where

open Cat C

open Products hasProducts renaming (law1 to law1Prod ; law2 to law2Prod ; law3 to law3Prod)
open import Categories.Products.Properties hasProducts using (iden-pair ; π₂-pair) renaming (fusion to fusionProd)

open Coproducts hasCoproducts renaming (law1 to law1Coprod ; law2 to law2Coprod ; law3 to law3Coprod)
open import Categories.Coproducts.Properties hasCoproducts using () renaming (fusion to fusionCoprod)

open Initial hasInitial renaming (law to lawInit)
open Terminal hasTerminal renaming (law to lawTerm)

open import DemFinal.CCC hasProducts T hasTerminal
open import DemFinal.Distributive hasProducts hasCoproducts I hasInitial

-- De clase 6
intercambio : ∀{A B C D}
         → (f : Hom A C)(g : Hom B C)
         → (h : Hom A D)(k : Hom B D)
         → ⟨ [ f , g ] , [ h , k ] ⟩ ≅ [ ⟨ f , h ⟩ , ⟨ g , k ⟩ ]
intercambio f g h k = law3Coprod (law3Prod (proof 
                                    π₁ ∙ (⟨ [ f , g ] , [ h , k ] ⟩ ∙ inl)
                                   ≅⟨ sym ass ⟩
                                    (π₁ ∙ ⟨ [ f , g ] , [ h , k ] ⟩) ∙ inl
                                   ≅⟨ congl law1Prod ⟩
                                    [ f , g ] ∙ inl
                                   ≅⟨ law1Coprod ⟩
                                    f
                                   ∎)
                                   
                                  (proof 
                                    π₂ ∙ (⟨ [ f , g ] , [ h , k ] ⟩ ∙ inl)
                                   ≅⟨ sym ass ⟩
                                    (π₂ ∙ ⟨ [ f , g ] , [ h , k ] ⟩) ∙ inl
                                   ≅⟨ congl law2Prod ⟩
                                    [ h , k ] ∙ inl
                                   ≅⟨ law1Coprod ⟩
                                    h
                                   ∎))
                                   
                           (law3Prod (proof 
                                    π₁ ∙ (⟨ [ f , g ] , [ h , k ] ⟩ ∙ inr)
                                   ≅⟨ sym ass ⟩
                                    (π₁ ∙ ⟨ [ f , g ] , [ h , k ] ⟩) ∙ inr
                                   ≅⟨ congl law1Prod ⟩
                                    [ f , g ] ∙ inr
                                   ≅⟨ law2Coprod ⟩
                                    g
                                   ∎)
                                   
                                  (proof 
                                    π₂ ∙ (⟨ [ f , g ] , [ h , k ] ⟩ ∙ inr)
                                   ≅⟨ sym ass ⟩
                                    (π₂ ∙ ⟨ [ f , g ] , [ h , k ] ⟩) ∙ inr
                                   ≅⟨ congl law2Prod ⟩
                                    [ h , k ] ∙ inr
                                   ≅⟨ law2Coprod ⟩
                                    k
                                   ∎) )

CCC⇒Dist : CCC → Dist
CCC⇒Dist ccc = record { distl = iso (uncurry [ curry inl , curry inr ])
                                     (proof 
                                        [ ⟨ inl ∙ π₁ , π₂ ⟩ , ⟨ inr ∙ π₁ , π₂ ⟩ ] ∙ uncurry [ curry inl , curry inr ]
                                      ≅⟨ congl (sym (intercambio (inl ∙ π₁) (inr ∙ π₁) π₂ π₂)) ⟩
                                        ⟨ [ inl ∙ π₁ , inr ∙ π₁ ] , [ π₂ , π₂ ] ⟩ ∙ uncurry [ curry inl , curry inr ]
                                      ≅⟨ fusionProd ⟩
                                        ⟨ [ inl ∙ π₁ , inr ∙ π₁ ] ∙ uncurry [ curry inl , curry inr ] , [ π₂ , π₂ ] ∙ uncurry [ curry inl , curry inr ] ⟩
                                      ≅⟨ {!   !} ⟩
                                        {!   !}
                                      ≅⟨ {!   !} ⟩
                                        {!   !}
                                      ≅⟨ {!   !} ⟩
                                        iden
                                      ∎) 
                                     (proof 
                                        uncurry [ curry inl , curry inr ] ∙ [ ⟨ inl ∙ π₁ , π₂ ⟩ , ⟨ inr ∙ π₁ , π₂ ⟩ ]
                                      ≅⟨ fusionCoprod ⟩
                                        [ uncurry [ curry inl , curry inr ] ∙ ⟨ inl ∙ π₁ , π₂ ⟩ , uncurry [ curry inl , curry inr ] ∙ ⟨ inr ∙ π₁ , π₂ ⟩ ]
                                      ≅⟨ {!   !} ⟩
                                        {!   !}
                                      ≅⟨ {!   !} ⟩
                                        {!   !}
                                      ≅⟨ {!   !} ⟩
                                        {!   !}
                                      ≅⟨ {!   !} ⟩
                                        iden
                                      ∎) ; 
                         null = λ {X} →
                                iso (uncurry i) -- null
                                    -- unnull . null
                                    (proof 
                                      ⟨ iden , i ⟩ ∙ uncurry i
                                     ≅⟨ fusionProd ⟩
                                      ⟨ iden ∙ uncurry i , i ∙ uncurry i ⟩
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      iden
                                     ∎)
                                    -- null . unnull
                                    (proof 
                                      uncurry i ∙ ⟨ iden , i ⟩
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      iden
                                     ∎)
                                    
                       }
                where open CCC ccc                

    