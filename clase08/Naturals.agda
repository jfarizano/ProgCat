module clase08.Naturals where

open import Library
open import Categories
open import Functors

open Fun

private 
  variable
    a b c d e f : Level
    C : Cat {a} {b}
    D : Cat {c} {d}
    E : Cat {e} {f}


{- Transformacional Naturales -}

record NatT {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}
            (F G : Fun C D) : Set (a ⊔ b ⊔ d) where
  constructor natural
  open Cat hiding (_∙_)
  open Cat D using (_∙_)
  field cmp : ∀ X → Hom D (OMap F X) (OMap G X)      -- componentes de la transformación
        nat : ∀{X Y}{f : Hom C X Y} →                -- condición de naturalidad
              (HMap G f) ∙ (cmp X) ≅ (cmp Y) ∙ (HMap F f)

{- condición de naturalidad 
       
En C          X -----f---> Y

En D         FX --Ff--> FY
              |          |
            cmp X      cmp Y
              |          |
              V          V
             GX --Gf--> GY
-}

open NatT

-- Dos transformaciones naturales son iguales si sus componentes son iguales.
-- La prueba de naturalidad es irrelevante.

NatTEq : ∀{F G : Fun C D}
         {α β : NatT F G} → 
         (λ X → cmp α X) ≅ (λ X → cmp β X) → 
         α ≅ β
NatTEq {α = natural cmp₁ nat₁} {natural .cmp₁ nat₂} refl 
   = cong (natural cmp₁) 
       (iext (λ _ → iext (λ _ → iext (λ _ → ir nat₁ _))))


-- NatTEq2 se puede usar cuando los funtores intervinientes no son definicionalmente iguales
NatTEq2 : ∀ {F G F' G' : Fun C D}
            {α : NatT F G}{β : NatT F' G'}
          → F ≅ F' → G ≅ G'  
          → (λ X → cmp α X) ≅ (λ X → cmp β X)
          → α ≅ β
NatTEq2 refl refl p = NatTEq p

--------------------------------------------------
-- la transformación natural identidad
idNat : ∀{F : Fun C D} → NatT F F
idNat {D = D}{F = F} = let open Cat D 
     in  natural (λ X → iden {OMap F X}) 
                 (trans idr (sym idl))



-- Composición (vertical) de transformaciones naturales
compVNat : ∀{F G H : Fun C D} → 
          NatT G H → NatT F G → NatT F H
compVNat {D = D}{F}{G}{H} α β = let open Cat D 
   in natural 
        (λ X → cmp α X ∙ cmp β X) 
        (λ {X} {Y} {f} → proof 
         (HMap H f ∙ cmp α X ∙ cmp β X)  ≅⟨ sym ass ⟩
        ((HMap H f ∙ cmp α X) ∙ cmp β X)  ≅⟨ congl (nat α) ⟩
        ((cmp α Y ∙ HMap G f) ∙ cmp β X)  ≅⟨ ass ⟩
        (cmp α Y ∙ HMap G f ∙ cmp β X)  ≅⟨ congr (nat β) ⟩
        (cmp α Y ∙ cmp β Y ∙ HMap F f)  ≅⟨ sym ass ⟩
        ((cmp α Y ∙ cmp β Y) ∙ HMap F f) 
        ∎)
{- Se componen componente a componente 
      FX        FX
      |         |
      βX        |
      ↓         |
      GX     compVNat α β X
      |         |
      αX        |
      ↓         ↓
      HX        HX
-}


--------------------------------------------------
{- Categorías de funtores
 Dadas dos categorías C y D, los objetos son los funtores : C → D,
 y los morfismos son las transformaciones naturales entre ellos.
-}
FunctorCat : Cat {a}{b} → Cat {c}{d} → Cat
FunctorCat C D = let open Cat D 
     in record
   { Obj = Fun C D
   ; Hom = NatT
   ; iden = idNat
   ; _∙_ = compVNat
   ; idl = NatTEq (ext (λ x → idl))
   ; idr = NatTEq (ext (λ x → idr))
   ; ass = NatTEq (ext (λ x → ass))
  }

--------------------------------------------------
-- Algunos ejemplos de transformaciones naturales

module Ejemplos where

 open import Categories.Sets
 open import Functors.List
 open import Functors.Maybe
 open import Functors.Constant
 open import Data.Nat

 {- reverse es una transformación natural -}

 open Cat (Sets {lzero})

 reverse-naturality : ∀{X Y : Set}{f : X → Y}(xs ys : List X) → 
          mapList f (foldl (λ ys y → y ∷ ys) ys xs) ≅ 
          foldl (λ ys y → y ∷ ys) (mapList f ys) (mapList f xs)
 reverse-naturality [] ys = refl
 reverse-naturality (x ∷ xs) ys = reverse-naturality xs (x ∷ ys)
 
 revNat : NatT ListF ListF
 revNat = natural (λ- reverse) 
                  (ext (λ xs → reverse-naturality xs []))

{- Definimos las transformaciones naturales en NatT con la componente explícita.
  Las funciones de librería como reverse están definidas con su componente
  implícita. El operador λ- convierte una función implícita en explícita.
-}

-- Ejercicio: probar que concat es una transformación natural
 lemDistMapList : {X Y : Set} {f : X → Y} → (xs : List X) → (xss : List (List X)) → 
                  mapList f (xs ++ foldr _++_ [] xss) ≅
                  mapList f xs ++ mapList f (concat xss)
 lemDistMapList [] xss = refl
 lemDistMapList {f = f} (x ∷ xs) xss = cong (f x ∷_) (lemDistMapList xs xss)
                   
 concatNat-naturality : {X Y : Set} {f : X → Y} →
                        (xss : List (List X)) →
                        mapList f (concat xss) ≅
                        concat (mapList (mapList f) xss)
 concatNat-naturality [] = refl
 concatNat-naturality {f = f} (xs ∷ xss) = 
  proof 
    mapList f (concat (xs ∷ xss))
  ≅⟨ refl ⟩
    mapList f (foldr _++_ [] (xs ∷ xss))
  ≅⟨ refl ⟩
    mapList f (xs ++ (foldr _++_ [] xss))
  ≅⟨ lemDistMapList xs xss ⟩
    mapList f xs ++ mapList f (concat xss)
  ≅⟨ cong (mapList f xs ++_) (concatNat-naturality xss) ⟩
    mapList f xs ++ concat (mapList (mapList f) xss)
  ≅⟨ refl ⟩
    concat (mapList (mapList f) (xs ∷ xss))
  ∎

 concatNat : NatT (ListF ○ ListF) ListF
 concatNat = natural (λ X xss → concat {A = X} xss) 
                     (ext concatNat-naturality) 

 --
-- Ejercicio: probar que length es una transformación natural
-- ¿Entre qué funtores es una transformación natural?
 length-Naturality : ∀{X Y : Set}{f : X → Y} → (xs : List X) →
                     foldr (λ _ → suc) 0 xs ≅ 
                     foldr (λ _ → suc) 0 (mapList f xs)
 length-Naturality [] = refl
 length-Naturality (x ∷ xs) = cong suc (length-Naturality xs)

 lengthNat : NatT ListF (K ℕ)
 lengthNat = natural (λ- length) 
                     (ext length-Naturality)

-- Ejercicio: probar que safehead es una transformación natural
 safeHead : {A : Set} → List A → Maybe A
 safeHead [] = nothing
 safeHead (x ∷ xs) = just x

 headNat-Naturality : {X Y : Set} {f : X → Y} →
                      (xs : OMap ListF X) →
                      (HMap MaybeF f ∙ safeHead) xs ≅ (safeHead ∙ HMap ListF f) xs
 headNat-Naturality [] = refl
 headNat-Naturality (x ∷ xs) = refl

 headNat : NatT ListF MaybeF
 headNat = natural (λ- safeHead) (ext headNat-Naturality)
 
 --
--------------------------------------------------
-- Natural isomorphism
{- Un isomorfismo natural es una transformación natural tal que
   cada componente es un isomorfismo. -}
open import Categories.Iso

record NatIso {a b c d}{C : Cat {a} {b}}{D : Cat {c} {d}}
             {F G : Fun C D}(η : NatT F G)  : Set (a ⊔ d) where
  constructor natiso
  field cmpIso : ∀ X -> Iso D (NatT.cmp η X)

{- EJERCICIO EXTRA: (Intentar solo si terminaron el resto)
  Equivalentemente, un isomorfismo natural es un isomorfismo en FunctorCat 
-}

--------------------------------------------------
-- composición con funtor (a izquierda y a derecha)

{-
compFNat
========
   Funtores F, G : C → D
               J : D → E
         JF , JG : C → E   
   
   tr.nat.     η : F → G

   compFNat J η : JF → JG
-}
compFNat : ∀{F G : Fun C D}
         → (J : Fun D E)
         → (η : NatT F G) → NatT (J ○ F) (J ○ G)
compFNat {D = D} {E = E} {F} {G} J t =
               let open NatT t renaming (cmp to η)
                   open Cat D renaming (_∙_ to _∙D_)
                   open Cat E renaming (_∙_ to _∙E_)
               in
               natural (λ X → HMap J (η X))
                (λ {X Y f} → proof
                  (HMap J (HMap G f) ∙E HMap J (η X))  
                ≅⟨ sym (fcomp J) ⟩
                  HMap J (HMap G f ∙D η X)  
                ≅⟨ cong (HMap J) (nat t) ⟩
                  HMap J (η Y ∙D HMap F f) 
               ≅⟨ fcomp J ⟩
                 (HMap J (η Y) ∙E HMap J (HMap F f))  ≅⟨ refl ⟩
                  (HMap J (η Y) ∙E HMap (J ○ F) f)
                ∎ )

{-
compNatF
========
   Funtores    F : C → D
            J, K : D → E
         JF , KF : C → E   
   
   tr.nat.     η : J → K

   compFNat J η : JF → KF
-}
compNatF :  ∀{J K : Fun D E}
         → (η : NatT J K)
         → (F : Fun C D)
         → NatT (J ○ F) (K ○ F)
compNatF {D = D} {E = E} {C = C} {J} {K} t F =
               let open NatT t renaming (cmp to η)
                   open Cat D renaming (_∙_ to _∙D_)
                   open Cat E renaming (_∙_ to _∙E_)
               in natural (λ X → η (OMap F X)) 
                          (nat t) 

--------------------------------------------------
-- Composición horizontal
compHNat : ∀{F G : Fun C D}{J K : Fun D E}
            (η : NatT F G)(ε : NatT J K)
            → NatT (J ○ F) (K ○ G)
compHNat {D = D}{E = E}{F = F}{G} {J}{K} η ε = 
   let open Cat E
       open Cat D using () renaming (_∙_ to _∙D_)
   in natural (λ X → cmp ε (OMap G X) ∙ HMap J (cmp η X))
              λ {X Y f} → 
              proof 
                (HMap (K ○ G) f ∙ (cmp ε (OMap G X) ∙ HMap J (cmp η X)))  
              ≅⟨  sym ass ⟩
                ((HMap (K ○ G) f ∙ cmp ε (OMap G X)) ∙ HMap J (cmp η X))  
              ≅⟨  congl (nat ε) ⟩
                ((cmp ε (OMap G Y) ∙ HMap J (HMap G f)) ∙ HMap J (cmp η X))  
              ≅⟨  ass ⟩
                (cmp ε (OMap G Y) ∙ (HMap J (HMap G f) ∙ HMap J (cmp η X))) 
              ≅⟨  congr (sym (fcomp J)) ⟩
                (cmp ε (OMap G Y) ∙ HMap J (HMap G f ∙D cmp η X))  
              ≅⟨  congr (cong (HMap J) (nat η)) ⟩
                (cmp ε (OMap G Y) ∙ HMap J (cmp η Y ∙D HMap F f))  
              ≅⟨ congr (fcomp J) ⟩
                (cmp ε (OMap G Y) ∙ HMap J (cmp η Y) ∙ HMap J (HMap F f))  
              ≅⟨  sym ass ⟩
                ((cmp ε (OMap G Y) ∙ HMap J (cmp η Y)) ∙ HMap (J ○ F) f)
              ∎

{-     --F-->   --J--> 
      C       D        E
       --G -->  --K-->
      

      F        J             JF X
      |        |             |
      η        ε          compHNat η ε X
      ↓        ↓             ↓
      G        K             KG X

-}



-- La composición horizontal es asociativa
compHNat-assoc : ∀{a1 b1 a2 b2 a3 b3 a4 b4}
                    {C1 : Cat {a1} {b1}}{C2 : Cat {a2} {b2}}{C3 : Cat {a3} {b3}}{C4 : Cat {a4} {b4}}
                    {F G : Fun C1 C2}{J K : Fun C2 C3}{L M : Fun C3 C4} 
                 →  (η1 : NatT F G)(η2 : NatT J K)(η3 : NatT L M)
                 →  compHNat (compHNat η1 η2) η3 ≅ compHNat η1 (compHNat η2 η3)
compHNat-assoc {C3 = C3}{C4 = C4}{F}{G}{J}{K}{L}{M} (natural cmp1 _) (natural cmp2 _) (natural cmp3 _) =
                   let open Cat C4 renaming (_∙_ to  _∙4_)
                       open Cat C3 using () renaming (_∙_ to  _∙3_)                         
                   in
                     {!   !}

-- ley de intercambio
interchange : ∀ {F G H : Fun C D}{I J K : Fun D E}
              → (α : NatT F G) → (β : NatT G H)
              → (γ : NatT I J) → (δ : NatT J K)
              → compHNat (compVNat β α) (compVNat δ γ) ≅ compVNat (compHNat β δ) (compHNat α γ)
interchange {D = D}{E = E}{F = F}{G}{H}{I = I}{J} (natural α _) (natural β _) (natural γ natγ) (natural δ _) =
          let open NatT
              open Cat D using () renaming (_∙_ to _∙D_)
              open Cat E
           in
           {!   !}

open import Categories.Coproducts

module FunctorCoproduct (cop : Coproducts C) where

 open Cat C
 open import Functors.Coproduct cop
 open Coproducts cop
 open import Categories.Coproducts.Properties cop
 open Fun
 
 -- Ejercicio: Leer la definición de coproducto de funtores _+F_
 -- y definir copairF 

--  copairF : ∀{F G H K} →
--           (NatT {C = D} F H) → (NatT G K) → NatT (F +F G) (H +F K)
--  copairF = {!   !}   