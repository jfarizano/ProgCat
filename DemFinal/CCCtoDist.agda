open import Library hiding (_×_)
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

open import DemFinal.CCC hasProducts T hasTerminal
open import DemFinal.Distributive hasProducts hasCoproducts I hasInitial

CCC⇒Dist : CCC → Dist
CCC⇒Dist ccc = record { distr = {!   !} ; 
                         null = {!   !} }