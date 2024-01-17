{-# OPTIONS --cubical #-}
module STLC where

    module Syntax where 
        open import Cubical.Data.Prod
        open import Cubical.Data.Bool using (Bool)
        open import Cubical.Data.Unit using (Unit ;tt)
        open import Cubical.Data.List

        -- phoas
        data type : Set₀ where 
            bool ⊤  : type
            _⇒_ _⊕_ : type → type → type
        
        Value : type → Set 
        Value bool = Bool
        Value ⊤ = Unit
        Value (x ⇒ y) = Value x → Value y
        Value (x ⊕ y) = Value x × Value y


        module bar where 
            -- raw terms

            data raw : Set where 
                ttᵣ truᵣ flsᵣ : raw
                _⇒ᵣ_ _∙ᵣ_ : raw → raw → raw 
            
            Ctx : Set 
            data _⊢_♯_ : Ctx → raw → type → Set

            Ctx = List (raw × type) 
            data _⊢_♯_ where 
                ttₜ : {Γ : Ctx} → Γ ⊢ ttᵣ ♯ ⊤
                truₜ : {Γ : Ctx} → Γ ⊢ truᵣ ♯ bool
                flsₜ : {Γ : Ctx} → Γ ⊢ flsᵣ ♯ bool        

           -- Γ : Set 
           -- term : Γ → type → Set
            



        module foo where
            {-
                all the morphisms of the syntatic category
                General Γ ⊢ M : A   becomes ⟪Γ⟫ -m-> ⟪A⟫ 
                where ⟪Γ⟫ is interpreted as ⟪A₁⟫ × ⟪A₂⟫ × .. ⟪Aₙ⟫

            -}
            Γ : Set 
            Γ = List type

            open import Cubical.Foundations.HLevels using (hProp)
            open import Cubical.Functions.Logic using (⊥)

            In : {A : Set} → A → List A → hProp _ 
            In a [] = ⊥
            In a (x ∷ xs) = {! a ≡ x   !}

            --data _⊢_∶_  :where 
            -- non phoas
            -- structural rules?
            --data term : Γ → type → Set where 
            --    ttₜ : {γ : Γ} → term γ ⊤
            --    tru fls : {γ : Γ} → term γ bool
            --    var : {γ : Γ}
                 

        data term : type -> Set where 
            ttₜ : term ⊤
            tru fls : term bool
            var : ∀ {t : type} → (Value t → term t)
            _∙_ : ∀ {dom ran} → term (dom ⇒ ran) → term dom → term ran
            Λ : ∀ {dom ran} → (Value dom → term ran) → term (dom ⇒ ran)

        id_unit : term (⊤ ⇒ ⊤)
        id_unit = Λ λ {tt → ttₜ}


        Γ : Set₀ 
        Γ = List type

    

    module Semantics{o h} where
        open import CatLib
        open Category
        open Syntax renaming (_⇒_ to _⇒ₜ_) using (type; Γ; Value; _∙_; Λ)
        open import Agda.Primitive using (lzero; lsuc)

        concreteCat : Category lzero lzero
        concreteCat .Ob = type
        concreteCat ._⇒_ X Y = Value (X ⇒ₜ Y)
        concreteCat .id X = X
        concreteCat ._∘_ f g = {! ? !}
        concreteCat .idr = {!   !}
        concreteCat .idl = {!   !}
        concreteCat .assoc = {!   !}

        syntaxCat : Category lzero lzero
        syntaxCat .Ob = Γ
        syntaxCat ._⇒_ Γ₁ Γ₂ = {!   !}
        syntaxCat .id = {!   !}
        syntaxCat ._∘_ = {!   !}
        syntaxCat .idr = {!   !}
        syntaxCat .idl = {!   !}
        syntaxCat .assoc = {!   !}
            


    --module Semantics {o ℓ} (𝒞 : Category o ℓ) where
    --    open CartesianClosed 𝒞


        





            