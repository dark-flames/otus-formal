{-# OPTIONS --without-K --safe --termination-depth=2 #-}
module Otus.Syntax.Typed.Properties.Presuppositions where

open import Otus.Syntax.Universe
open import Otus.Syntax.Untyped
open import Otus.Syntax.Typed.Base

open import Data.Nat hiding (_⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product renaming (_,_ to pair)

private
  variable
    l l₁ l₂ : ULevel
    x y : ℕ
    Γ Δ Ξ  : Context
    γ δ δ₁ δ₂ : Substitution
    f a b c A B C : Term
open _⊢_⇒_
open ⊢_
open _⊢_

{- If Γ ⊢ δ ⇒ Δ then ⊢ Γ and ⊢ Δ -}
substWfCtx : Γ ⊢ δ ⇒ Δ → ⊢ Γ × ⊢ Δ
{- If Γ ⊢ A then ⊢ Γ -}
tyWfCtx : Γ ⊢ A → ⊢ Γ
{- If Γ ⊢ a ∷ A then ⊢ Γ -}
tmWfCtx : Γ ⊢ a ∷ A → ⊢ Γ

postulate 
    substEqWf : Γ ⊢ γ ≡ⱼ δ ⇒ Δ → Γ ⊢ γ ⇒ Δ × Γ ⊢ δ ⇒ Δ
    
tyEqWf : Γ ⊢ A ≡ⱼ B → Γ ⊢ A × Γ ⊢  B
---- Context
ctxWeakening :  ⊢ Γ , A → ⊢ Γ
ctxWeakening (CExt ctx _) = ctx

ctxExpand : ⊢ Γ , A → Γ ⊢ A
ctxExpand (CExt _ ty) = ty

---- Substitution
displayMap : Γ ⊢ A → Γ , A ⊢ drop 1 ⇒ Γ
displayMap ΓA = SbDropˢ (SbDropᶻ (tyWfCtx ΓA)) (ΓA)

liftSubst : Δ , A ⊢ drop 1 ⇒ Δ → Γ ⊢ γ ⇒ Δ 
    → Γ , (A [ γ ]ₑ) ⊢ (γ ∘ (drop 1)) , Var 0 ⇒ Δ , A
liftSubst display gamma = let ΔA = ctxExpand (proj₁ (substWfCtx display))
    in let ΓA = TySubst ΔA gamma 
---- (Γ , (A [ γ ]ₑ)) ⊢ drop 1 ⇒ Γ
    in let dropSb = displayMap ΓA
---- (Γ , (A [ γ ]ₑ)) ⊢ γ ∘ drop 1 ⇒ Δ
    in let baseSb = SbComp gamma dropSb
---- (Γ , (A [ γ ]ₑ)) ⊢ Var 0 ∷ (A [ γ ∘ drop 1 ]ₑ)
    in let var = TmTyConv (TmVar ΓA) (TyEqSubstSubst ΓA dropSb)
    in SbExt baseSb ΔA var

tyEqSubst' : Γ ⊢ A ≡ⱼ B → Γ , B ⊢ idₛ ⇒ Γ , A

tyEqSubst'' : Γ ⊢ A ≡ⱼ B → Γ , A ⊢ idₛ ⇒ Γ , B
tyEqSubst'' eq = let ΓA = proj₁ (tyEqWf eq)
    in let ΓB = proj₂ (tyEqWf eq)
---- (Γ , A) ⊢ drop 1 ⇒ Γ
    in let dropSb = displayMap ΓA

---- Γ , A ⊢ Var 0 ∷ (B [ drop 1 ]ₑ)
------ Γ , A ⊢ Var 0 ∷ (A [ drop 1 ]ₑ)
------  Γ , A ⊢ A [ drop 1 ]ₑ ≡ⱼ B [ drop 1 ]ₑ
    in let var = TmTyConv (TmVar ΓA)  (TyEqSubst eq (SbEqRefl dropSb))
    in let extSb = SbExt dropSb ΓB var
    in let extSbReduce = SbEqExtVar extSb {!   !}
    in {!   !}

tyEqSubst : Γ ⊢ A ≡ⱼ B → Γ , A ⊢ idₛ ⇒ Γ , B
tyEqSubst (TyEqRefl ty) = SbDropᶻ (CExt (tyWfCtx ty) ty)
tyEqSubst (TyEqSym eq) = tyEqSubst' eq
tyEqSubst (TyEqTrans l r) = let l' = tyEqSubst l
    in let r' = tyEqSubst r
    in let eq = SbEqIdₗ r' l'
    in proj₂ (substEqWf eq)
tyEqSubst (TyEqPi domain codomain) = let domainSubst = tyEqSubst domain
    in let codomainSubst = tyEqSubst codomain
---- (Γ , Pi A C) ⊢ Var 0 ：： Pi B D
    in {!   !}

tyEqSubst' (TyEqRefl ty) = SbDropᶻ (CExt (tyWfCtx ty) ty)
tyEqSubst' (TyEqSym eq) = tyEqSubst eq
tyEqSubst' (TyEqTrans l r) = let l' = tyEqSubst' l
    in let r' = tyEqSubst' r
    in let eq = SbEqIdₗ l' r'
    in proj₂ (substEqWf eq)



tyEqLift : Γ ⊢ A ≡ⱼ B → Γ ⊢ C → Γ , C ⊢ (A [ drop 1 ]ₑ) ≡ⱼ (B [ drop 1 ]ₑ)
tyEqLift eq eTy = let sb = SbDropˢ (SbDropᶻ (tyWfCtx eTy)) eTy
    in TyEqSubst eq (SbEqRefl sb)

tmEqLift : Γ ⊢ a ≡ⱼ b ∷ A → Γ ⊢ C → Γ , C ⊢ (a [ drop 1 ]ₑ) ≡ⱼ (b [ drop 1 ]ₑ) ∷ (A [ drop 1 ]ₑ)
tmEqLift eq eTy = let sb = SbDropˢ (SbDropᶻ (tyWfCtx eTy)) eTy
    in TmEqSubst eq (SbEqRefl sb)

tm-coe : Γ ⊢ A ≡ⱼ B → Γ , A ⊢ c ∷ C → Γ , B ⊢ c ∷ C
tm-coe ty (TmVar ctx) = let tyB = proj₂ (tyEqWf ty)
    in TmTyConv (TmVar tyB) (TyEqSym (tyEqLift ty tyB))
tm-coe ty (TmLam body) = TmLam {!   !}
tm-coe ty (TmPi domain codomain) = TmPi {!   !} {!   !}
tm-coe ty (TmApp f g) = TmApp {!   !} {!   !}
tm-coe ty (TmSubst t sb) = {!   !}
tm-coe ty (TmU ctx) = let tyB = proj₂ (tyEqWf ty)
    in TmU (CExt (tyWfCtx tyB) tyB)
tm-coe ty (TmTyConv l eq) = {!   !}


-----------------------


substWfCtx (SbDropᶻ p) = pair p p
substWfCtx (SbDropˢ sb ty) = let sb' = substWfCtx sb 
    in pair (CExt (proj₁ sb') ty) (proj₂ sb')
substWfCtx (SbExt sb ty _) = let sb' = substWfCtx sb 
    in pair (proj₁ sb') (CExt (proj₂ sb') ty)
substWfCtx (SbComp l r) = pair (proj₁ (substWfCtx r)) (proj₂ (substWfCtx l))

tyWfCtx (TyPi d _) = tyWfCtx d
tyWfCtx (TyU ctx) = ctx
tyWfCtx (TySubst _ sb) = (proj₁ (substWfCtx sb))
tyWfCtx (TyRussel tm) = tmWfCtx tm

tmWfCtx (TmVar ty) = CExt (tyWfCtx ty) ty
tmWfCtx (TmLam tm) = ctxWeakening (tmWfCtx tm)
tmWfCtx (TmPi domain _) = tmWfCtx domain
tmWfCtx (TmApp f g) = tmWfCtx f
tmWfCtx (TmSubst _ sb) = proj₁ (substWfCtx sb)
tmWfCtx (TmU ctx) = ctx
tmWfCtx (TmTyConv tm _) = tmWfCtx tm

tyEqWf (TyEqRefl ty) = pair ty ty
tyEqWf (TyEqSym e) = swap (tyEqWf e)
tyEqWf (TyEqTrans l r) = pair (proj₁ (tyEqWf l)) (proj₂ (tyEqWf r))
tyEqWf (TyEqPi domain codomain) = let domain' = tyEqWf domain
    in let codomain' = tyEqWf codomain
    in pair
        (TyPi (proj₁ domain') (proj₁ codomain'))
        (TyPi (proj₂ domain') ( {!!})) 