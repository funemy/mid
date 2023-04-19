{-# LANGUAGE FlexibleInstances #-}

module DSL (
    var,
    forall,
    (~>),
    lambda,
    app,
    exists,
    (*),
    pair,
    fst,
    snd,
    zero,
    suc,
    nat,
    (===),
    refl,
    subst,
    unit,
    bot,
    quo,
    as,
    induction,
    sym,
    trans,
    cong,
    Term (..),
) where

import Lang (Name (..), Term (..))
import Prelude hiding (fst, pi, snd, (*))

-- | A set of boring helper function for constructing AST
var :: String -> Term
var s = Var (Name s)

forall :: Term -> Term -> Term -> Term
forall (Var n) = Pi n
forall t = error ("The first argument of `forall` must be a variable, but got: " ++ show t)

-- Name "_" is purely for pretty-printing
-- "_" is NOT treated differently
(~>) :: Term -> Term -> Term
ty1 ~> ty2 = Pi (Name "k") ty1 ty2
infixr 9 ~>

lambda :: Term -> Term -> Term
lambda (Var n) = Lam n
lambda t = error ("The first argument of `Lambda` must be a variable, but got: " ++ show t)

app :: Term -> Term -> Term
app = App

exists :: Term -> Term -> Term -> Term
exists (Var s) = Sigma s
exists t = error ("The first argument of `exists` must be a variable, but got: " ++ show t)

(*) :: Term -> Term -> Term
ty1 * ty2 = Sigma (Name "p") ty1 ty2
infix 9 *

pair :: Term -> Term -> Term
pair = MkPair

fst :: Term -> Term
fst = Fst

snd :: Term -> Term
snd = Snd

zero :: Term
zero = Zero

suc :: Term -> Term
suc = Succ

nat :: Int -> Term
nat n
    | n == 0 = Zero
    | n > 0 = Succ (nat (n - 1))
    | otherwise = error "Cannot convert a negative interger to a natural number."

(===) :: Term -> Term -> Term -> Term
(a === b) ty = Equal ty a b
infixl 9 ===

refl :: Term
refl = Refl

subst :: Term -> Term -> Term -> Term
subst = Subst

unit :: Term
unit = Unit

bot :: Term
bot = Absurd

quo :: String -> Term
quo = Quote

as :: Term -> Term -> Term
as = As

-- | Apply symmetry to an equality proof
-- 1st param: an equality proposition (i.e., a equality type)
-- 2nd param: the proof of the equality proposition
-- return: a proof of the symmetric equality proposition
sym :: Term -> Term -> Term
sym (Equal eqTy ta tb) pf = app (app (app (app (t `as` ty) eqTy) ta) tb) pf
  where
    prop = lambda k ((k === x) tyA)
    t = lambda tyA (lambda x (lambda y (lambda eq (subst prop refl eq))))
    ty = forall tyA Universe (forall x tyA (forall y tyA ((x === y) tyA ~> (y === x) tyA)))
sym t1 t2 = error ("Invalid input to sym: " ++ show t1 ++ ", " ++ show t2)

-- | Apply transitivity to two equality proofs
-- 1st param: an equality proposition (x===y) tyA
-- 2nd param: a proof of 1st param
-- 3rd param: an equality proposition (y===z) tyA
-- 4th param: a proof of 3rd param
-- return: a proof of (x===z) tyA
trans :: Term -> Term -> Term -> Term -> Term
trans (Equal eqabTy ta tb) eqabPf (Equal eqbcTy _ tc) eqbcPf
    | eqabTy == eqbcTy = app (app (app (app (app (app transProp eqabTy) ta) tb) tc) eqabPf) eqbcPf
    | otherwise = error ("Cannot apply transitivity to two equalities of different types: " ++ show (eqabTy, eqbcTy))
  where
    transProp = t `as` ty
    t =
        lambda tyA $
            lambda x $
                lambda y $
                    lambda z $
                        lambda eqxy $
                            lambda eqyz $
                                subst (lambda k ((x === k) tyA)) eqxy eqyz
    ty =
        forall tyA Universe $
            forall x tyA $
                forall y tyA $
                    forall z tyA $
                        (x === y) tyA ~> (y === z) tyA ~> (x === z) tyA
trans t1 t2 t3 t4 = error ("Invalid input to trans: " ++ show t1 ++ ", " ++ show t2 ++ ", " ++ show t3 ++ ", " ++ show t4)

-- | Apply congruence to an equality proof
-- 1st param: a function type A -> B
-- 2nd param: a function that has the type A -> B
-- 3rd param: a equality proposition (x === y) A
-- 4th param: a proof of the 3rd param
-- return: a proof of (f x === f y) B
cong :: Term -> Term -> Term -> Term -> Term
cong (Pi _ aTy bTy) fun (Equal _ ta tb) eqab = app (app (app (app (app (app congProp aTy) bTy) ta) tb) fun) eqab
  where
    congProp = t `as` ty
    t =
        lambda tyA $
            lambda tyB $
                lambda x $
                    lambda y $
                        lambda f $
                            lambda
                                eqxy
                                ( subst
                                    (lambda k ((app f x === app f k) tyB))
                                    refl
                                    eqxy
                                )
    ty =
        forall tyA Universe $
            forall tyB Universe $
                forall x tyA $
                    forall y tyA $
                        forall
                            f
                            (tyA ~> tyB)
                            ((x === y) tyA ~> (app f x === app f y) tyB)
cong t1 t2 t3 t4 = error ("Invalid input to cong: " ++ show t1 ++ ", " ++ show t2 ++ ", " ++ show t3 ++ ", " ++ show t4)

x, y, z, k, f, eq, eqxy, eqyz, tyA, tyB :: Term
x = Var (Name "x")
y = Var (Name "y")
z = Var (Name "z")
k = Var (Name "k")
f = Var (Name "f")
eq = Var (Name "eq")
eqxy = Var (Name "eqxy")
eqyz = Var (Name "eqyz")
tyA = Var (Name "A")
tyB = Var (Name "B")

class Inductable t where
    _induction :: [Term] -> t

instance Inductable Term where
    _induction [Nat, t1, t2, t3, t4] = IndNat t1 t2 t3 t4
    _induction [Absurd, t1, t2] = IndAbsurd t1 t2
    _induction (Nat : _) = error "Wrong number of arguments for induction on Nat"
    _induction (Absurd : _) = error "Wrong number of arguments for induction on Absurd"
    _induction (_ : _) = error "Cannot do induction on non-inductive types."
    _induction [] = error "Doing induction on void..."

instance (Inductable t) => Inductable (Term -> t) where
    _induction acc term = _induction (acc ++ [term])

induction :: Inductable t => t
induction = _induction []