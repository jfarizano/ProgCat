module clase07.Functors where

open import Library
open import Categories

private
  variable
    a b c d e f : Level
    C : Cat {a} {b}
    D : Cat {c} {d}
    E : Cat {e} {f}
open Cat

{- Los Funtores proveen morfismos entre categorías
 Deben preservar la estructura de las mismas.
-}

record Fun (C : Cat {a} {b})(D : Cat {c} {d}) : Set (a ⊔ b ⊔ c ⊔ d)
  where
  constructor functor
  field OMap  : Obj C → Obj D
        HMap  : ∀{X Y} → Hom C X Y → Hom D (OMap X) (OMap Y)
        fid   : ∀{X} → HMap (iden C {X}) ≅ iden D {OMap X}
        fcomp : ∀{X Y Z}{f : Hom C Y Z}{g : Hom C X Y} → 
                HMap (_∙_ C f g) ≅ _∙_ D (HMap f) (HMap g)
open Fun

{- ¿Cómo se relaciona con la noción de Functor en Haskell? -}

--------------------------------------------------
{- Ejemplos -}
--------------------------------------------------

{- Funtor Identidad -}
IdF : Fun C C
IdF {C} = functor 
    id 
    id 
    refl 
    refl

--------------------------------------------------
{- Functor Constante
  Mapea todo objeto de C en un objeto de D dado, y todo morfismo a la identidad.
-}

K : (X : Obj D) → Fun C D
K {D = D} X = let open Cat D using () renaming (_∙_ to _∙d_)
   in functor 
   (λ _ → X) 
   (λ _ → iden D {X}) 
   refl
   (sym (idl D))

--------------------------------------------------
{- Funtor Diagonal
  Mapea X al objeto de la categoría producto (X , X)
-}

open import Categories.ProductCat


Δ : Fun C (C ×C C)
Δ {C = C} = let open Cat C using () renaming (_∙_ to _∙c_)
                open Cat (C ×C C) using () renaming (_∙_ to _∙×_)
  in functor 
   (λ X → X , X) 
   (λ f → f , f) 
   refl 
   refl
--------------------------------------------------
{- Funtores sobre la categoría Sets -}

import Categories.Sets

private Sets : Cat {lsuc lzero} {lzero}
Sets = Categories.Sets.Sets {lzero} 

{- Funtor cuadrado
  (notar la diferencia con el diagonal para la categoría Sets)
  Mapea X al producto cartesiano X × X
 -}
Cuadrado : Fun Sets Sets
Cuadrado = functor 
    (λ X → X × X) 
    (λ f → λ { (x , x') → f x , f x' }) 
    refl 
    refl

-- Funtor Maybe
open import Data.Maybe.Base using (Maybe ; just ; nothing) renaming (map to mapMaybe) public

MaybeF-id : {A : Set} → (x : Maybe A) → mapMaybe (iden Sets) x ≅ iden Sets x
MaybeF-id (just x) = refl
MaybeF-id nothing = refl

MaybeF-comp : {X Y Z : Set} {f : Y → Z} {g : X → Y} →
            (x : Maybe X) →  
            mapMaybe (f ∘ g) x ≅ mapMaybe f (mapMaybe g x)
MaybeF-comp (just x) = refl
MaybeF-comp nothing = refl

MaybeF : Fun Sets Sets
MaybeF = functor Maybe
                 mapMaybe
                 (ext (MaybeF-id))
                 (ext (λ x → MaybeF-comp x))


-- Ejercicio: Funtor Lista
open import Data.List.Base using (List ; [] ; _∷_) renaming (map to mapList) public

ListF-id : {A : Set} → (x : List A) → mapList (iden Sets) x ≅ iden Sets x
ListF-id [] = refl
ListF-id (x ∷ xs) = 
  proof 
    x ∷ mapList (λ z → z) xs
  ≅⟨ cong (x ∷_) (ListF-id xs) ⟩
    x ∷ xs
  ∎

ListF-comp : {X Y Z : Set} {f : Y → Z} {g : X → Y} →
      (x : List X) →
      mapList (f ∘ g) x ≅ (mapList f (mapList g x))
ListF-comp [] = refl
ListF-comp {f = f} {g = g} (x ∷ xs) = 
  proof 
    f (g x) ∷ mapList (λ z → f (g z)) xs
  ≅⟨ cong (f (g x) ∷_) (ListF-comp xs) ⟩
    f (g x) ∷ mapList f (mapList g xs)
  ∎

ListF : Fun Sets Sets
ListF = functor List
                mapList
                (ext ListF-id)
                (ext ListF-comp)

-- Ejercicio EXTRA: Bifuntor de árboles con diferente información en nodos y hojas
data Tree (A B : Set) : Set where
     leaf : A → Tree A B
     node : (lt : Tree A B) → B → (rt : Tree A B) → Tree A B

mapTree : ∀{A A' B B'} → (A → A') → (B → B') → Tree A B → Tree A' B'
mapTree funcA funcB (leaf x) = leaf (funcA x)
mapTree funcA funcB (node lt x rt) = node (mapTree funcA funcB lt)
                                          (funcB x)
                                          (mapTree funcA funcB rt)

TreeF-id : {X : Set × Set} →
           (x : Tree (fst X) (snd X)) →
           mapTree (iden Sets) (iden Sets) x ≅ iden Sets x
TreeF-id (leaf x) = refl
TreeF-id (node lt x rt) =
  proof 
    node (mapTree (iden Sets) (iden Sets) lt) 
         (iden Sets x) 
         (mapTree (iden Sets) (iden Sets) rt)
  ≅⟨ cong₂ (λ l r → node l x r) (TreeF-id lt) (TreeF-id rt) ⟩
    node lt x rt
  ∎

TreeF-comp : {X Y Z : Set × Set}
             {f : (fst Y → fst Z) × (snd Y → snd Z)}
             {g : (fst X → fst Y) × (snd X → snd Y)} →
             (x : Tree (fst X) (snd X)) →
             mapTree (λ x → fst f (fst g x)) (λ x → snd f (snd g x)) x ≅
             mapTree (fst f) (snd f) (mapTree (fst g) (snd g) x)
TreeF-comp (leaf x) = refl
TreeF-comp {f = f} {g = g} (node lt x rt) =
  proof
    node (mapTree (λ x → fst f (fst g x)) (λ x → snd f (snd g x)) lt)
         (snd f (snd g x))
         (mapTree (λ x → fst f (fst g x)) (λ x → snd f (snd g x)) rt)
  ≅⟨ cong₂ (λ l r → node l (snd f (snd g x)) r) (TreeF-comp lt) (TreeF-comp rt) ⟩
    node (mapTree (fst f) (snd f) (mapTree (fst g) (snd g) lt))
         (snd f (snd g x))
         (mapTree (fst f) (snd f) (mapTree (fst g) (snd g) rt))
  ∎

TreeF : Fun (Sets ×C Sets) Sets
TreeF = functor (λ { (A , B) → Tree A B})
                (λ { (f , g) → mapTree f g})
                (ext TreeF-id)
                (ext TreeF-comp)

--------------------------------------------------
{- Ejercicio: Hom functor : probar que el Hom de una categoría C
  es un bifunctor Hom : (C Op) ×C C → Sets
  -}

HomF : ∀{a}{b}{C : Cat {a} {b}} → Fun ((C Op) ×C C) (Categories.Sets.Sets {b})
HomF {C = C} = 
  functor (λ { (X , Y) → Hom C X Y})
          (λ { (f , g) h → (g ∙c h) ∙c f})
          (ext HomF-id) 
          (ext HomF-comp)
          where 
          open Cat C using () renaming ( _∙_ to _∙c_ )
          HomF-id : {X : Obj C × Obj C} → (f : Hom C (fst X) (snd X)) → (iden C ∙c f) ∙c iden C ≅ f
          HomF-id f = proof 
                        ((iden C ∙c f) ∙c iden C)
                      ≅⟨ idr C ⟩
                        (iden C ∙c f)
                      ≅⟨ idl C ⟩
                        f
                      ∎
          HomF-comp : {X Y Z : Obj C × Obj C} → 
                      {f : Hom C (fst Z) (fst Y) × Hom C (snd Y) (snd Z)} →
                      {g : Hom C (fst Y) (fst X) × Hom C (snd X) (snd Y)} →
                      (h : Hom C (fst X) (snd X)) →
                      ((snd f ∙c snd g) ∙c h) ∙c fst g ∙c fst f ≅
                      (snd f ∙c ((snd g ∙c h) ∙c fst g)) ∙c fst f
          HomF-comp {f = f} {g} h = proof 
                                      (((snd f ∙c snd g) ∙c h) ∙c (fst g ∙c fst f))
                                    ≅⟨ cong (_∙c (fst g ∙c fst f)) (ass C) ⟩
                                      ((snd f ∙c (snd g ∙c h)) ∙c (fst g ∙c fst f))
                                    ≅⟨ sym (ass C) ⟩
                                      (((snd f ∙c (snd g ∙c h)) ∙c fst g) ∙c fst f)
                                    ≅⟨ cong (_∙c fst f) (ass C) ⟩
                                      ((snd f ∙c ((snd g ∙c h) ∙c fst g)) ∙c fst f)
                                    ∎

--------------------------------------------------
{- Composición de funtores -}
_○_ : Fun D E → Fun C D → Fun C E
_○_ {D = D}{E = E}{C = C} F G = 
   let open Cat C using () renaming (_∙_ to _∙c_)
       open Cat D using () renaming (_∙_ to _∙d_)
       open Cat E using () renaming (_∙_ to _∙e_)
   in functor 
      (OMap F ∘ OMap G) 
      (HMap F ∘ HMap G) 
      (proof         
        HMap F (HMap G (iden C))       
       ≅⟨ cong (HMap F) (fid G) ⟩
        HMap F (iden D) 
       ≅⟨ fid F ⟩
        iden E
      ∎) 
      (λ {X Y Z f g} →
        proof 
        HMap F (HMap G (f ∙c g))
       ≅⟨ cong (HMap F) (fcomp G) ⟩
        HMap F (HMap G f ∙d HMap G g)
       ≅⟨ fcomp F ⟩
        (HMap F (HMap G f) ∙e HMap F (HMap G g))
       ∎)
    
infixr 10 _○_

--------------------------------------------------
{- ¿Cuándo dos funtores son iguales ?
  Cuando
  1. el mapeo de objetos es igual
  2. Para cualquier par de objetos X,Y, el mapeo de Hom(X,Y) es el mismo

  Notar que las pruebas de las propiedades no son relevantes.
-}
FunctorEq : (F G : Fun C D)
         →  OMap F ≅ OMap G
         →  (λ {X Y} → HMap F {X}{Y}) ≅ (λ {X}{Y} → HMap G {X}{Y})
         → F ≅ G
FunctorEq (functor OMap₁ HMap₁ fid₁ fcomp₁) (functor .OMap₁ .HMap₁ fid₂ fcomp₂) refl refl = 
     cong₂ (functor OMap₁ HMap₁) (iext (λ a → ir _ _))
        (iext (λ a → iext (λ a₁ → iext (λ a₂ → iext (λ a₃ → iext (λ a₄ → ir _ _))))))

--------------------------------------------------

{- Categoría (grande) de categorías chicas Dado que tenemos un funtor
  identidad, y que la composición de funtores es un funtor, tenemos
  una categoría CAT, cuyos objetos son categorías, y sus flechas son
  funtores.
-}

CAT : {a b : Level} → Cat {lsuc (a ⊔ b)} {a ⊔ b}
CAT {a} {b} = record
           { Obj = Cat {a} {b}
           ; Hom = Fun
           ; iden = IdF
           ; _∙_ = _○_
           ; idl = FunctorEq _ _ refl refl 
           ; idr = FunctorEq _ _ refl refl  
           ; ass = FunctorEq _ _ refl refl  
           }



--------------------------------------------------

{- Ejercicio: Probar que los funtores preservan isomorfismos Es decir,
que si tenemos un funtor F : C → D, y f es un componente de un
isomorfismo en C, entonces (HMap F f) es un isomorfismo en D.

-}

open import Categories.Iso

FunIso : (F : Fun C D) → ∀{X Y}(f : Hom C X Y)
       → Iso C f → Iso D (HMap F f)
FunIso {C = C} {D = D} F f (iso inv rinv linv) 
       = let open Cat C using () renaming (_∙_ to _∙c_)
             open Cat D using () renaming (_∙_ to _∙d_)
         in iso (HMap F inv) 
                (proof 
                  (HMap F f ∙d HMap F inv)
                 ≅⟨ sym (fcomp F) ⟩
                  HMap F (f ∙c inv)
                 ≅⟨ cong (HMap F) rinv ⟩
                  HMap F (iden C)
                 ≅⟨ fid F ⟩
                  iden D
                 ∎)
                (proof 
                  (HMap F inv ∙d HMap F f)
                 ≅⟨ sym (fcomp F) ⟩
                  HMap F (inv ∙c f)
                 ≅⟨ cong (HMap F) linv ⟩
                   HMap F (iden C)
                 ≅⟨ fid F ⟩
                  iden D
                 ∎)

--------------------------------------------------
{- Ejercicio EXTRA: Sea C una categoría con productos. Probar
 que el producto _×_ es un functor C × C → C. -}


{- Ejercicio EXTRA*: En una clase anterior definimos un Monoide M como
   categoría (MonCat M) con un solo objeto.  Probar que dar funtor F :
   (MonCat M) → (MonCat N) es equivalente a dar un homomorfismo de
   monoides entre M y N.
 OJO: Hace falta hacer cambios en las definiciones, 
      ya que usamos otra definición de categoría.
-}


    