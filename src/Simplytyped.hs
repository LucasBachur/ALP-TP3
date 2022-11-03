module Simplytyped
  ( conversion
  ,    -- conversion a terminos localmente sin nombre
    eval
  ,          -- evaluador
    infer
  ,         -- inferidor de tipos
    quote          -- valores -> terminos
  )
where

import           Data.List
import           Data.Maybe
import           Prelude                 hiding ( (>>=) )
import           Text.PrettyPrint.HughesPJ      ( render )
import           PrettyPrinter
import           Common

-- conversion a términos localmente sin nombres
conversion :: LamTerm -> Term
conversion = conversion' []

conversion' :: [String] -> LamTerm -> Term
conversion' b (LVar n    )   = maybe (Free (Global n)) Bound (n `elemIndex` b)
conversion' b (LApp t u  )   = conversion' b t :@: conversion' b u
conversion' b (LAbs n t u)   = Lam t (conversion' (n : b) u)
conversion' b (LLet s t1 t2) = Let (conversion' b t1) (conversion' (s : b) t2)
conversion' b (LAs t1 t)     = As (conversion' b t1) t
conversion' b (LUnit)        = Unit
conversion' b LZero          = Zero
conversion' b (LPair t1 t2)  = Pair (conversion' b t1) (conversion' b t2)
conversion' b (LFst t)       = Fst (conversion' b t)
conversion' b (LSnd t)       = Snd (conversion' b t)
conversion' b (LSuc t   )    = Suc (conversion' b t)
conversion' b (LRec t1 t2 t3)= Rec (conversion' b t1) (conversion' b t2) (conversion' b t3)
-----------------------
--- eval
-----------------------

sub :: Int -> Term -> Term -> Term
sub i t (Bound j) | i == j    = t
sub _ _ (Bound j) | otherwise = Bound j
sub _ _ (Free n   )           = Free n
sub i t (u   :@: v)           = sub i t u :@: sub i t v
sub i t (Lam t'  u)           = Lam t' (sub (i + 1) t u)
sub i t (Let t1 t2)           = Let (sub i t t1) (sub (i + 1) t t2)
sub i t (As t' t'')           = As (sub i t t') t''
sub i t (Unit)                = Unit
sub i t (Pair t1 t2)          = Pair (sub i t t1) (sub i t t2)
sub i t (Fst t')              = Fst (sub i t t')
sub i t (Snd t')              = Snd (sub i t t')
sub i t Zero                  = Zero
sub i t (Suc u   )            = Suc (sub i t u)
sub i t (Rec t1 t2 t3)        = Rec (sub i t t1) (sub i t t2) (sub i t t3)

-- evaluador de términos
eval :: NameEnv Value Type -> Term -> Value
eval _ (Bound _             ) = error "variable ligada inesperada en eval"
eval e (Free  n             ) = fst $ fromJust $ lookup n e
eval _ (Lam      t   u      ) = VLam t u
eval e (Lam _ u  :@: Lam s v) = eval e (sub 0 (Lam s v) u)
eval e (Lam t u1 :@: u2)      = let v2 = eval e u2 in eval e (sub 0 (quote v2) u1)
eval e (u        :@: v      ) = case eval e u of
  VLam t u' -> eval e (Lam t u' :@: v)
  _         -> error "Error de tipo en run-time, verificar type checker"
eval e (Let t1 t2)            = let v2 = eval e t1 in eval e (sub 0 (quote v2) t2)
eval e (As t1 t)              = eval e t1
eval e (Unit)                 = VUnit
eval e (Pair t1 t2)           = VPair t1' t2'
                                  where t1' = eval e t1
                                        t2' = eval e t2
eval e (Fst (Pair t1 t2))     = eval e t1 
eval e (Snd (Pair t1 t2))     = eval e t2 
eval e Zero                   = VNum NZero
eval e (Suc t              ) = case eval e t of
  VNum num -> VNum (NSuc num)
  _        -> error "Error de tipo en run-time, verificar type checker"
eval e (Rec t1 t2 t3)         = case eval e t3 of
  VNum NZero        -> eval e t1
  VNum (NSuc nv)    -> let t = quote (VNum nv)
                       in eval e ((t2 :@: Rec t1 t2 t) :@: t)
  _                 -> error "Error de tipo en run-time, verificar type checker"
-----------------------
--- quoting
-----------------------

quote :: Value -> Term
quote (VLam t f)      = Lam t f
quote (VUnit)         = Unit
quote (VPair t1 t2)   = Pair (quote t1) (quote t2)
quote (VNum NZero)    = Zero
quote (VNum (NSuc n)) = Suc (quote (VNum n))

----------------------
--- type checker
-----------------------

-- type checker
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

(>>=)
  :: Either String Type -> (Type -> Either String Type) -> Either String Type
(>>=) v f = either Left f v
-- fcs. de error

matchError :: Type -> Type -> Either String Type
matchError t1 t2 =
  err
    $  "se esperaba "
    ++ render (printType t1)
    ++ ", pero "
    ++ render (printType t2)
    ++ " fue inferido."

notfunError :: Type -> Either String Type
notfunError t1 = err $ render (printType t1) ++ " no puede ser aplicado."

notfoundError :: Name -> Either String Type
notfoundError n = err $ show n ++ " no está definida."

infer' :: Context -> NameEnv Value Type -> Term -> Either String Type
infer' c _ (Bound i)    = ret (c !! i)
infer' _ e (Free  n)    = case lookup n e of
  Nothing     -> notfoundError n
  Just (_, t) -> ret t
infer' c e (t :@: u)    = infer' c e t >>= \tt -> infer' c e u >>= \tu ->
  case tt of
    FunT t1 t2 -> if (tu == t1) then ret t2 else matchError t1 tu
    _          -> notfunError tt
infer' c e (Lam t u)    = infer' (t : c) e u >>= \tu -> ret $ FunT t tu
infer' c e (Let t1 t2)  = infer' c e t1 >>= \tu -> infer' (tu : c) e t2
infer' c e (As t1 t)    = infer' c e t1 >>= \t' ->
                           if t' == t then ret t else matchError t t'
infer' c e (Unit)       = ret UnitT
infer' c e (Pair t1 t2) = infer' c e t1 >>=
                          \tt -> infer' c e t2 >>=
                          \tu -> ret $ PairT tt tu
infer' c e (Fst t) = infer' c e t >>= \tt ->
                     case tt of PairT x y -> ret x
                                _         -> err "No se puede aplicar fst a algo que no es una tupla"
infer' c e (Snd t) = infer' c e t >>= \tt ->
                     case tt of PairT x y -> ret y
                                _         -> err "No se puede aplicar snd a algo que no es una tupla"
infer' c e Zero      = ret NatT
infer' c e (Suc n ) = infer' c e n >>= \tn -> if tn == NatT then ret tn else matchError NatT tn
infer' c e (Rec t1 t2 t3) = infer' c e t1 >>= \tn1 -> infer' c e t2 >>= \tn2 ->
    case tn2 of
        FunT tt1 (FunT NatT tt2) -> if (tt1 == tn1 && tt2 == tn1) then infer' c e t3 >>= \tn3 -> if tn3 == NatT then ret tn1 else matchError NatT tn3
                                                                  else matchError (FunT tn1 (FunT NatT tn1)) (FunT tt1 (FunT NatT tt2))
        tt                       -> matchError (FunT tn1 (FunT NatT tn1)) tt
----------------------------------
