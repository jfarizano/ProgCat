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
open Coproducts hasCoproducts renaming (law1 to law1Coprod ; law2 to law2Coprod ; law3 to law3Coprod)
open Initial hasInitial renaming (law to lawInit)
open Terminal hasTerminal renaming (law to lawTerm)

open import DemFinal.CCC hasProducts T hasTerminal
open import DemFinal.Distributive hasProducts hasCoproducts I hasInitial


CCC⇒Dist : CCC → Dist
CCC⇒Dist ccc = record { distr = iso {!   !}
                                     {!   !} 
                                     {!   !} ; 
                         null = iso π₂ 
                                    (proof 
                                      i ∙ π₂
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      {!   !}
                                     ≅⟨ {!   !} ⟩
                                      iden
                                     ∎)
                                    (proof 
                                      π₂ ∙ i
                                     ≅⟨ congr (law3Prod (sym lawInit) (sym lawInit)) ⟩
                                      π₂ ∙ ⟨ i , i ⟩
                                     ≅⟨ law2Prod ⟩
                                      i
                                     ≅⟨ lawInit ⟩
                                      iden
                                     ∎) }
                where open CCC ccc
                      e : ∀{X Y Z : Obj} → Hom X ((Y + Z) ⇒ (X × Y + X × Z))
                      e = {!   !}