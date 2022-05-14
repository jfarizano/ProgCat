{-# OPTIONS --cumulativity #-}

open import Library

module clase06.ConstruccionesSet where
 
 open import Categories.Sets
 open import clase06.Construcciones Sets

 {- Ejercicios
   -- Probar que Sets tiene objeto terminal, productos, inicial, y coproductos
  -}
 SetsHasProducts : Products
 SetsHasProducts = prod _×_ 
                        fst 
                        snd 
                        (λ f g x → (f x , g x)) 
                        refl 
                        refl 
                        λ {refl refl → refl}

 OneSet : Terminal ⊤
 OneSet = term (λ _ → tt) refl

 -------------------------------------------------
 data _⊎_{a b : Level}(A : Set a)(B : Set b) : Set (a ⊔ b) where
     Inl : A → A ⊎ B
     Inr : B → A ⊎ B

 SetsHasCoproducts : Coproducts
 SetsHasCoproducts = coproduct _⊎_ 
                               Inl 
                               Inr 
                               elim
                               refl 
                               refl 
                               demLaw3
                               where
                               elim : {A B C : Set} → (A → C) → (B → C) → A ⊎ B → C
                               elim f g (Inl x) = f x
                               elim f g (Inr x) = g x
                               demLaw3 : {A B C : Set} {f : A → C} {g : B → C} {h : A ⊎ B → C} →
                                         (λ x → h (Inl x)) ≅ f → (λ x → h (Inr x)) ≅ g → h ≅ elim f g
                               demLaw3 refl refl = ext (λ {(Inl x) → refl
                                                          ; (Inr x) → refl})


--------------------------------------------------
 ZeroSet : Initial ⊥
 ZeroSet = init (λ ()) (ext (λ ()))
--------------------------------------------------
 