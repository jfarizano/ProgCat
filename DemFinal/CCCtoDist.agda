open import Library hiding (_×_ ; curry ; uncurry)
open import Categories
open import Categories.Products
open import Categories.Coproducts
open import Categories.Initial
open import Categories.Terminal
open import Categories.Iso

-- CCC pide: Producto y terminal.
-- Distributive pide: Producto, coproducto e inicial.
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
open import Categories.Products.Properties hasProducts using (iden-pair ; π₂-pair ; fusion-pair) renaming (fusion to fusionProd)

open Coproducts hasCoproducts renaming (law1 to law1Coprod ; law2 to law2Coprod ; law3 to law3Coprod)
open import Categories.Coproducts.Properties hasCoproducts using () renaming (fusion to fusionCoprod)

open Initial hasInitial renaming (law to lawInit)

open import DemFinal.CCC hasProducts T hasTerminal
open import DemFinal.Distributive hasProducts hasCoproducts I hasInitial

CCC⇒Dist : CCC → Dist
CCC⇒Dist ccc = record { distl = iso (uncurry [ (curry inl) , curry inr ])
                                     -- undistl . distl = iden
                                     (proof 
                                        undistl ∙ uncurry h
                                      ≅⟨ uncurry-prop₂ ⟩
                                        uncurry (map⇒ undistl ∙ h)
                                      ≅⟨ cong uncurry lema ⟩
                                        uncurry (curry iden)
                                      ≅⟨ lawcurry1 ⟩
                                        iden
                                      ∎)
                                     -- distl . undistl = iden
                                     (proof 
                                        uncurry h ∙ [ ⟨ inl ∙ π₁ , π₂ ⟩ , ⟨ inr ∙ π₁ , π₂ ⟩ ]
                                      ≅⟨ fusionCoprod ⟩
                                        [ uncurry h ∙ ⟨ inl ∙ π₁ , π₂ ⟩ , uncurry h ∙ ⟨ inr ∙ π₁ , π₂ ⟩ ]
                                      ≅⟨ cong₂ [_,_] (lema2 law1Coprod) (lema2 law2Coprod) ⟩
                                        [ inl , inr ]
                                      ≅⟨ sym (law3Coprod idl idl) ⟩
                                        iden
                                      ∎) ; 
                         null = iso (uncurry i)
                                    -- unnull . null = iden
                                    (proof 
                                      ⟨ iden , i ⟩ ∙ uncurry i
                                     ≅⟨ uncurry-prop₂ ⟩
                                      uncurry (map⇒ ⟨ iden , i ⟩ ∙ i)
                                     ≅⟨ cong uncurry (sym lawInit) ⟩
                                      uncurry i
                                     ≅⟨ cong uncurry lawInit ⟩
                                      uncurry (curry iden)
                                     ≅⟨ lawcurry1 ⟩
                                      iden
                                     ∎)
                                    -- null . unnull = iden
                                    (proof 
                                      uncurry i ∙ ⟨ iden , i ⟩
                                     ≅⟨ sym lawInit ⟩
                                      i
                                     ≅⟨ lawInit ⟩
                                      iden
                                     ∎)
                                    
                       }
                where open CCC ccc
                      open Properties ccc 

                      h : ∀{X Y Z} → Hom (Y + Z) (X ⇒ (Y × X + Z × X))
                      h = [ curry inl , curry inr ]
                      
                      lema : ∀{X Y Z} → map⇒ undistl ∙ h  ≅ curry {X + Y} {Z} {(X + Y) × Z} iden
                      lema = proof 
                              map⇒ undistl ∙ [ curry inl , curry inr ]
                             ≅⟨ fusionCoprod ⟩
                              [ map⇒ undistl ∙ curry inl , map⇒ undistl ∙ curry inr ]
                             ≅⟨ cong₂ [_,_] curry-prop curry-prop ⟩
                              [ curry (undistl ∙ inl) , curry (undistl ∙ inr) ]
                             -- undistl = [ ⟨ inl ∙ π₁ , π₂ ⟩ , ⟨ inr ∙ π₁ , π₂ ⟩ ]
                             ≅⟨ cong₂ [_,_] (cong curry law1Coprod) (cong curry law2Coprod) ⟩
                              [ curry ⟨ inl ∙ π₁ , π₂ ⟩ , curry ⟨ inr ∙ π₁ , π₂ ⟩ ]
                             ≅⟨ cong₂ (λ x y → [ curry ⟨ inl ∙ π₁ , x ⟩ , curry ⟨ inr ∙ π₁ , y ⟩ ]) (sym idl) (sym idl) ⟩
                              [ curry ⟨ inl ∙ π₁ , iden ∙ π₂ ⟩ , curry ⟨ inr ∙ π₁ , iden ∙ π₂ ⟩ ]
                             ≅⟨ refl ⟩
                              [ curry (pair inl iden) , curry (pair inr iden) ]
                             ≅⟨ cong₂ (λ x y → [ curry x , curry y ]) (sym idl) (sym idl) ⟩
                              [ curry (iden ∙ pair inl iden) , curry (iden ∙ pair inr iden) ]
                             ≅⟨ cong₂ [_,_] (sym curry-prop₁) (sym curry-prop₁) ⟩
                              [ curry iden ∙ inl , curry iden ∙ inr ]
                             ≅⟨ sym fusionCoprod ⟩
                              curry iden ∙ [ inl , inr ]
                             ≅⟨ congr (sym (law3Coprod idl idl)) ⟩
                              curry iden ∙ iden
                             ≅⟨ idr ⟩
                              curry iden
                             ∎  
                      -- -----
                      lema2 : ∀{X X' Y Z}{f : Hom X (Y ⇒ Z)}{g : Hom (X' × Y) Z}{h : Hom X' X}
                              → (f ∙ h ≅ curry g)
                              → (uncurry f) ∙ ⟨ h ∙ π₁ , π₂ ⟩ ≅ g       
                      lema2 {f = f}{g}{h} p = proof 
                                               uncurry f ∙ ⟨ h ∙ π₁ , π₂ ⟩
                                              ≅⟨ congl uncurry-prop₁ ⟩
                                               (apply ∙ pair f iden) ∙ ⟨ h ∙ π₁ , π₂ ⟩
                                              ≅⟨ ass ⟩
                                               apply ∙ (pair f iden ∙ ⟨ h ∙ π₁ , π₂ ⟩)
                                              ≅⟨ congr fusion-pair ⟩
                                               apply ∙ ⟨ f ∙ h ∙ π₁ , iden ∙ π₂ ⟩
                                              ≅⟨ congr (cong (λ x → ⟨ x , iden ∙ π₂ ⟩) (sym ass)) ⟩
                                               apply ∙ ⟨ (f ∙ h) ∙ π₁ , iden ∙ π₂ ⟩
                                              ≅⟨ congr (cong (λ x → ⟨ x ∙ π₁ , iden ∙ π₂ ⟩) p) ⟩
                                               apply ∙ ⟨ curry g ∙ π₁ , iden ∙ π₂ ⟩
                                              ≅⟨ refl ⟩
                                               apply ∙ pair (curry g) iden
                                              ≅⟨ curry-exp ⟩
                                               g
                                              ∎  
    