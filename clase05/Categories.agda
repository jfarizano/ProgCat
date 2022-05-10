module Categories where

{- importamos extensionalidad, proof irrelevance -}
open import Library

open import Relation.Binary.PropositionalEquality  


--------------------------------------------------
{- Definición de Categoría -}
{-
 - Una colección de objetos  (denotado con Obj (C))
 - Conjuntos de flechas entre objetos (Sean A, B ∈ Obj(C) , hom (A, B))
 - todo objeto tiene una flecha identidad (id : A → A)
 - todo par de flechas "compatibles" puede componerse ( ∘ )
 - la composición es asociativa, con la flecha identidad como unidad. 
     (f ∘ g) ∘ h = f ∘ (g ∘ h)
     f ∘ id = id ∘ f = f 
-}


record Cat : Set₂ where
  infix 7 _∙_ 
  field Obj : Set₁
        Hom : Obj → Obj → Set
        iden : ∀ {X} → Hom X X
        _∙_ : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
        idl : ∀ {X Y} {f : Hom X Y} → iden ∙ f ≡ f  
        idr : ∀ {X Y} {f : Hom X Y} → f ∙ iden ≡ f
        ass : ∀ {X Y Z W} {f : Hom Y Z} {g : Hom X Y}{h : Hom W X} →
              (f ∙ g) ∙ h ≡ f ∙ (g ∙ h)
        

--------------------------------------------------
{- El típico ejemplo de categoría es la categoría Set de conjuntos y
   funciones entre los mismos.
-}


Sets : Cat
Sets = record
         { Obj = Set
         ; Hom = λ X Y → X → Y  
         ; iden = id
         ; _∙_ = λ f g → f ∘ g  
         ; idl = refl
         ; idr = refl
         ; ass = refl
         } 


--------------------------------------------------
{- Para cada categoría existe la categoría dual, que consiste de los
mismos objetos, pero con las flechas invertidas.
   Cₒₚ :  
   Objetos : Obj (C) 
   Hom (X, Y) : Hom (Y, X) ∈ C   

-}

_Op : Cat → Cat
C Op =  let open Cat C in
        record
         { Obj = Obj
         ; Hom = λ X Y → Hom Y X 
         ; iden = iden
         ; _∙_ = λ f g → g ∙ f 
         ; idl = idr
         ; idr = idl
         ; ass = sym ass
         }  



--------------------------------------------------
{- Categoría Discreta

   Una categoría discreta es una categoría en la que los únicos
morfismos son identidades. La composición y ecuaciones de coherencia
son triviales.
-}


Discrete : Set₁ → Cat
Discrete X = record
               { Obj = X
               ; Hom = λ _ _ → ⊤ 
               ; iden = tt  
               ; _∙_ = λ _ _ → tt
               ; idl = refl
               ; idr = refl
               ; ass = refl
               } 



{- A menudo nos queremos "olvidar" de los morfismos de una
categoría. Es decir, miramos a la categoría como una categoría
discreta. Esto se nota en lenguaje categórico como |C| -}

∣_∣ : Cat → Cat
∣ C ∣ = Discrete (Cat.Obj C)

--------------------------------------------------
{- Categoría Producto -}
{- Dadas dos categorías, podemos formar la categoría producto 
   Los objetos son el producto cartesiano de los objetos
   Los morfismos son pares de flechas.


  Obj (C × D) = Obj (C) × Obj(D)
  
         (X , Y) ∈ Obj (C × D) donde X ∈ Obj (C) ∧ y ∈ Obj (D) 

  Hom ((X, Y), (X', Y')) = Hom (X, X') × Hom (Y , Y')

         f : X → X' ∈ Hom (X, X') ∧ g : Y → Y' ∈ Hom (Y, Y') ⇒ (f, g) ∈ Hom ((X, Y), (X', Y'))   

  (f , g) ∘ (f' , g') = (f ∘ f' ,  g ∘ g')
 
  id = (id , id)

-}

_×C_ : Cat → Cat → Cat
C ×C D = record
           { Obj = Obj₁ × Obj₂
           ; Hom = λ {(X , Y) (X' , Y') → Hom₁ X X' × Hom₂ Y Y' }
           ; iden = (iden₁ , iden₂)
           ; _∙_ = λ {(f , g) (f' , g') → f ∙₁ f' , (g ∙₂ g')} 
           ; idl = cong₂ _,_ idl₁ idl₂
           ; idr = cong₂ _,_ idr₁ idr₂
           ; ass = cong₂ _,_ ass₁ ass₂
           } 
           where open Cat C renaming (Obj to Obj₁ ; Hom to Hom₁ ; iden to iden₁ ; _∙_ to _∙₁_ ; idl to idl₁ ; idr to idr₁ ; ass to ass₁)
                 open Cat D renaming (Obj to Obj₂ ; Hom to Hom₂ ; iden to iden₂ ; _∙_ to _∙₂_ ; idl to idl₂ ; idr to idr₂ ; ass to ass₂)  
          


--------------------------------------------------
{- Familia de Conjuntos -}
{- Los objetos son familias de conjuntos
   (conjuntos indexados por un conjunto de índices)

  Los morfismos son funciones que preservan el índice.
 
  Objetos:  {Aᵢ} i ∈ I
  Flechas : Aᵢ → Bᵢ    
-}

Fam : Set → Cat
Fam I = record
          { Obj = I → Set
          ; Hom = λ A B → ∀ {i} → A i → B i  
          ; iden = id
          ; _∙_ = λ f g → f ∘ g  
          ; idl = refl
          ; idr = refl
          ; ass = refl
          } 


--------------------------------------------------
{- Ejemplo extendido: Categorías Slice -}

{- Dada una categoría C, los objetos de un slice
   sobre un objeto I, son morfismos con codominio I
-}


module Slice (C : Cat) where 

  open Cat C

  record Slice₀ (I : Obj) : Set₁ where
    constructor _,_
    field
     base : Obj
     homBase : Hom base I
     
  open Slice₀

  {- record para representar los morfismos de la categoría -}
  record Slice₁ (I : Obj) (X Y : Slice₀ I) : Set where 
    constructor _,_
    field
       baseHom : Hom (base X) (base Y)  -- h  
       prop : (homBase Y) ∙ baseHom ≡ homBase X   -- g ∙ h = f

  {- la composición es simplemente pegar triángulos -}
  Slice-comp :  {I : Obj} {X Y Z : Slice₀ I} →
                Slice₁ I Y Z → Slice₁ I X Y → Slice₁ I X Z
  Slice-comp {I} {X , f} {Y , g} {Z , i} (h , p) (h' , q) =
    ( h ∙ h') , (proof  i ∙ (h ∙ h')
                         ≡⟨ sym ass ⟩
                         (i ∙ h) ∙ h'
                         ≡⟨ cong (λ j → j ∙ h') p ⟩
                         g ∙ h'
                         ≡⟨ q ⟩
                         f
                         ∎ )
  
  open Slice₁

  {- veamos como funciona proof irrelevance -}
  Slice₁-eq : {I : Obj} {X Y : Slice₀ I} {h h' : Slice₁ I X Y} →
              (baseHom h) ≡ (baseHom h')  →
              h ≡ h'
  Slice₁-eq {I} {X , f} {Y , g} {h , p} {.h , q} refl = cong (λ p → (h , p)) (ir p q)
 

  Slice : (I : Obj) → Cat
  Slice I = record
              { Obj = Slice₀ I
              ; Hom = Slice₁ I 
              ; iden = iden , idr
              ; _∙_ = Slice-comp  
              ; idl = Slice₁-eq idl
              ; idr = Slice₁-eq idr
              ; ass = Slice₁-eq ass
              }
 
 
--------------------------------------------------

{- Ejercicio: Definir la categoría con un sólo objeto ⊤, y que sus
morfismos son los elementos de un monoide M -}

module CatMon where

 open import Records-completo hiding (Iso ; ⊤)

 CatMon : Monoid → Cat
 CatMon M = record
  { Obj = Lift _ ⊤
  ; Hom = λ _ _ → Carrier
  ; iden = ε
  ; _∙_ = _∙_
  ; idl = lid
  ; idr = rid
  ; ass = assoc
  }
  where open Monoid M


--------------------------------------------------
{- Ejercicio: Definir la categoría en que los objetos son monoides,
  y las flechas son homomorfismos de monoides
-}

module MonCat where

 open import Records-completo hiding (Iso)

 MonCat : Cat
 MonCat = record
  { Obj = Monoid
  ; Hom = λ M N → (Carrier M → Carrier N)
  ; iden = id
  ; _∙_ = λ g f x → g (f x)
  ; idl = refl
  ; idr = refl
  ; ass = refl
  }
  where open Monoid
 
--------------------------------------------------
{- Ejercicio: Dada un categoría C, definir la siguiente categoría:
  - Los objetos son morfismos de C
  - Un morfismo entre una flecha f: A → B y f': A'→ B' es un par de morfismos
    de C
      g1 : A → A', y g2 : B → B', tal que
                    f' ∙ g₁ ≡ g₂ ∙ f
-}

module ArrowCat (C : Cat) where

 open Cat C 

 record Arrow₀ : Set₁ where
  field
    from : Obj
    to : Obj
    baseHom : Hom from to

 open Arrow₀

 record Arrow₁ (X Y : Arrow₀) : Set where
  field
    homBase : (Hom (from X) (from Y)) × (Hom (to X) (to Y))
    prop : (baseHom Y) ∙ (fst homBase) ≡ (snd homBase) ∙ (baseHom X)

 open Arrow₁

 idenArrow₁ : {X : Arrow₀} → Arrow₁ X X
 idenArrow₁ {X} = record 
     { homBase = iden , iden ; 
       prop = proof 
               baseHom X ∙ iden
              ≡⟨ idr ⟩
               baseHom X
              ≡⟨ sym idl ⟩
               iden ∙ baseHom X
              ∎ } 
                            
 compArrow₁ : {X Y Z : Arrow₀} → Arrow₁ Y Z → Arrow₁ X Y → Arrow₁ X Z
 compArrow₁ {X} {Y} {Z} G F = record 
    { homBase = (fst (homBase G) ∙ fst (homBase F)) , 
                (snd (homBase G) ∙ snd (homBase F)) ; 
      prop = proof 
              baseHom Z ∙ (fst (homBase G) ∙ fst (homBase F))
             ≡⟨ sym ass ⟩
              (baseHom Z ∙ fst (homBase G)) ∙ fst (homBase F)
             ≡⟨ cong (λ x → x ∙ fst (homBase F)) (prop G) ⟩
              (snd (homBase G) ∙ baseHom Y) ∙ fst (homBase F)
             ≡⟨ ass ⟩
              snd (homBase G) ∙ (baseHom Y ∙ fst (homBase F))
             ≡⟨ cong (λ x → snd (homBase G) ∙ x) (prop F) ⟩
              snd (homBase G) ∙ (snd (homBase F) ∙ baseHom X)
             ≡⟨ sym ass ⟩
              (snd (homBase G) ∙ snd (homBase F)) ∙ baseHom X
             ∎ }

 arrow₁-eq : {X Y : Arrow₀} → {f g : Arrow₁ X Y} → (homBase f ≡ homBase g) → (f ≡ g)
 arrow₁-eq {f = record { homBase = homBase ; prop = prop₁ }}
           {g = record { homBase = .(homBase) ; prop = prop }}
           refl = cong (λ p → (record { homBase = homBase ; prop = p })) (ir prop₁ prop)

 ArrowCat : Cat
 ArrowCat = record
  { Obj = Arrow₀
  ; Hom = Arrow₁
  ; iden = idenArrow₁
  ; _∙_ = compArrow₁
  ; idl = λ {X Y f} → arrow₁-eq (proof 
                                  homBase (compArrow₁ idenArrow₁ f)
                                 ≡⟨ refl ⟩
                                  (fst (homBase idenArrow₁) ∙ fst (homBase f)) , (snd (homBase idenArrow₁) ∙ snd (homBase f))
                                 ≡⟨ refl ⟩
                                  iden ∙ fst (homBase f) , iden ∙ snd (homBase f)
                                 ≡⟨ cong₂ _,_ idl idl ⟩
                                  fst (homBase f) , snd (homBase f)
                                 ≡⟨ refl ⟩
                                  homBase f
                                 ∎)
  ; idr = λ {X Y f} → arrow₁-eq (proof 
                                  homBase (compArrow₁ f idenArrow₁)
                                 ≡⟨ refl ⟩
                                  (fst (homBase f) ∙ fst (homBase idenArrow₁)) , (snd (homBase f)) ∙ (snd (homBase idenArrow₁))
                                 ≡⟨ refl ⟩
                                  (fst (homBase f) ∙ iden) , (snd (homBase f)) ∙ iden
                                 ≡⟨ cong₂ _,_ idr idr ⟩
                                  fst (homBase f) , snd (homBase f)
                                 ≡⟨ refl ⟩
                                  homBase f
                                 ∎)
  ; ass = λ {X Y Z W f g h} →  arrow₁-eq (proof 
                                           homBase (compArrow₁ (compArrow₁ f g) h)
                                          ≡⟨ refl ⟩
                                           ((fst (homBase f) ∙ fst (homBase g)) ∙ fst (homBase h)) , ((snd (homBase f) ∙ snd (homBase g)) ∙ snd (homBase h))
                                          ≡⟨ cong₂ _,_ ass ass ⟩
                                           (fst (homBase f) ∙ (fst (homBase g) ∙ fst (homBase h))) , (snd (homBase f) ∙ (snd (homBase g) ∙ snd (homBase h)))
                                          ≡⟨ refl ⟩
                                           homBase (compArrow₁ f (compArrow₁ g h))
                                          ∎)
  }
 
--------------------------------------------------
{- Generalizamos la noción de isomorfismo de la clase pasada a cualquier categoría -}

{- Isomorfismo en una categoría -}

open Cat

record Iso {C : Cat}(A B : Obj C)(fun : Hom C A B) : Set where
  constructor iso
  field inv : Hom C B A
        law1 : _∙_ C fun inv  ≡ iden C {B}
        law2 : _∙_ C inv fun  ≡ iden C {A}

--------------------------------------------------

{- Ejercicio
 Mostrar que en el caso de la categoría Sets, isomorfismo corresponde a biyección de funciones

Ayuda : puede ser útil usar cong-app
-}

-- → Hecho en clase04 

--------------------------------------------------
{- Ejercicio:
 Probar que un isormofismo en (C : Cat) es un isomorfismo en (C Op).
-}

isoC-isoCOp : {C : Cat}{A B : Obj C}{f : Hom C A B} → (iso : Iso {C} A B f) → Iso {C Op} B A f
isoC-isoCOp (iso inv law1 law2) = iso inv law2 law1

--------------------------------------------------
{- Ejercicio EXTRA:
 Definir la categoría de pointed sets:
  - objetos son conjuntos junto con un elemento designado del conjunto.
     Por ejemplo (Bool , false), (ℕ , 0) , etc.
  - los morfismos son funciones entre los conjuntos que preservan el punto
     (A,a) → (B, b) es una función f : A → B, tal que f(a) = b 
-}

--------------------------------------------------

{- Ejercicio EXTRA:
 Definir la categoría cuyos
  - objetos son conjuntos finitos (y por lo tanto isomorfos a Fin n para algún n)
  - morfismos son isomorfismos.  
-}

--------------------------------------------------


   