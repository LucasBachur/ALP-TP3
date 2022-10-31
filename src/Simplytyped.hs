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
conversion' b (LAs t1 t)    = As (conversion' b t1) t

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
sub i t (As t1 t)              = As (sub i t t1) t

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

-----------------------
--- quoting
-----------------------

quote :: Value -> Term
quote (VLam t f) = Lam t f

----------------------
--- type checker
-----------------------

{- Ejercicio 1
  La funcion infer retorna Either String Type, y no solo Type, porque puede ocurrir un error
  cuando se intenta determina el tipo de un Term. En el caso de que no se pueda inferir se
  detecta el error y se propaga en la ejecucion del programa.
-}

-- type checker
infer :: NameEnv Value Type -> Term -> Either String Type
infer = infer' []

-- definiciones auxiliares
ret :: Type -> Either String Type
ret = Right

err :: String -> Either String Type
err = Left

{- Ejercicio 1
  La funcion (>>=) realiza una evaluacion de los 2 casos posibles del tipo de Either.
  Toma dos valores: v y f.
  Si v tiene la forma Left String, el argumento v representa un error y la funcion devuelve este mismo.
  Si v tiene la forma Right Type, aplica la funcion f a v.
-}

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
infer' c _ (Bound i)   = ret (c !! i)
infer' _ e (Free  n)   = case lookup n e of
  Nothing     -> notfoundError n
  Just (_, t) -> ret t
infer' c e (t :@: u)   = infer' c e t >>= \tt -> infer' c e u >>= \tu ->
  case tt of
    FunT t1 t2 -> if (tu == t1) then ret t2 else matchError t1 tu
    _          -> notfunError tt
infer' c e (Lam t u)   = infer' (t : c) e u >>= \tu -> ret $ FunT t tu
infer' c e (Let t1 t2) = infer' c e t1 >>= \tu -> infer' (tu : c) e t2
infer' c e (As t1 t) = infer' c e t1 >>= \t' ->
                      if t' == t then ret t else matchError t t'
----------------------------------
