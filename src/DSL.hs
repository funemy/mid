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
    top,
    unit,
    bot,
    atom,
    quo,
    set,
    as,
    induction,
    Term (..),
) where

import Lang (Name (..), Term (..))
import Prelude hiding (fst, pi, snd, (*), (==))

-- | A set of boring helper function for constructing AST
var :: String -> Term
var s = Var (Name s)

forall :: Term -> Term -> Term -> Term
forall (Var n) = Pi n
forall t = error ("The first argument of `forall` must be a variable, but got: " ++ show t)

-- Name "_" is purely for pretty-printing
-- "_" is NOT treated differently
(~>) :: Term -> Term -> Term
ty1 ~> ty2 = Pi (Name "_") ty1 ty2
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
nat 0 = Zero
nat n = Succ (nat (n - 1))

(===) :: Term -> Term -> Term -> Term
(x === y) ty = Equal ty x y
infixl 9 ===

refl :: Term
refl = Refl

subst :: Term -> Term -> Term -> Term
subst = Subst

top :: Term
top = UnitTy

unit :: Term
unit = Unit

bot :: Term
bot = Absurd

atom :: Term
atom = Atom

quo :: String -> Term
quo = Quote

set :: Term
set = Universe

as :: Term -> Term -> Term
as = As

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