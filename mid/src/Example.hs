{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

{-# HLINT ignore "Eta reduce" #-}

module Example () where

import DSL
import Env (Res)
import Lang (Name (..))
import Text.Pretty.Simple (pPrint)
import Toplevel (Output, run)
import Prelude hiding (fst, pi, snd, (*), (==))

plus :: Term -> Term -> Term
plus a b = induction Nat (lambda x Nat) a (lambda x (lambda y (suc y))) b

ex1 :: Term
ex1 = plus (nat 2) (nat 3)

test1 :: IO ()
test1 = runTest ex1

ex2 :: Term
ex2 = refl `as` (ex1 === nat 5) Nat

test2 :: IO ()
test2 = runTest ex2

ex3 :: Term
ex3 = refl `as` (ex1 === nat 42) Nat

test3 :: IO ()
test3 = runTest ex3

ex4 :: Term
ex4 = lambda x (induction Absurd ((ex1 === nat 42) Nat) x) `as` (Absurd ~> (ex1 === nat 42) Nat)

test4 :: IO ()
test4 = runTest ex4

ex5 :: Term
ex5 = lambda x refl `as` forall x Nat ((plus x zero === x) Nat)

test5 :: IO ()
test5 = runTest ex5

ex6 :: Term
ex6 = lambda x refl `as` forall x Nat ((plus zero x === x) Nat)

test6 :: IO ()
test6 = runTest ex6

ex7 :: Term
ex7 = lambda x x `as` ((Nat ~> Nat) ~> (Nat ~> Nat))

test7 :: IO ()
test7 = runTest ex7

ex8 :: Term
ex8 = lambda x x `as` (exists y Nat Nat ~> exists y Nat Nat)

test8 :: IO ()
test8 = runTest ex8

ex9 :: Term
ex9 = lambda x (lambda y (lambda eqxy (sym eqxyTy eqxy))) `as` forall x Nat (forall y Nat (forall eqxy eqxyTy ((y === x) Nat)))
  where
    eqxyTy = (x === y) Nat

test9 :: IO ()
test9 = runTest ex9

-- | Symmetry of equality
-- x and y are of some type A
-- eq is the equality proof of x === y
-- we want to proof symmetry y === x
-- proof sketch:
-- - create such a property, say p = forall k:A. (k == x : A)
-- - then apparently (p x) holds
-- - then because we already assume x === y
-- - by substituion, we also have (p y) holds, i.e.,  (y==x : A)
symPf :: Term
symPf = t `as` ty
  where
    prop = lambda k ((k === x) tyA)
    t = lambda tyA (lambda x (lambda y (lambda eq (subst prop refl eq))))
    ty = forall tyA Universe (forall x tyA (forall y tyA ((x === y) tyA ~> (y === x) tyA)))

runSymPf :: IO ()
runSymPf = runTest symPf

transPf :: Term
transPf = t `as` ty
  where
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

runTransPf :: IO ()
runTransPf = runTest transPf

congPf :: Term
congPf = t `as` ty
  where
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

runCongPf :: IO ()
runCongPf = runTest congPf

----------------------------------------------
-- Helper Functions for Constructing Examples
----------------------------------------------

pp :: Show a => a -> IO ()
pp = pPrint

runTest :: Term -> IO ()
runTest = pp . run

x, y, z, p, q, k, f, eq, eqxy, eqyz, eqxz, tyA, tyB :: Term
x = Var (Name "x")
y = Var (Name "y")
z = Var (Name "z")
p = Var (Name "p")
q = Var (Name "q")
k = Var (Name "k")
f = Var (Name "f")
eq = Var (Name "eq")
eqxy = Var (Name "eqxy")
eqyz = Var (Name "eqyz")
eqxz = Var (Name "eqxz")
tyA = Var (Name "A")
tyB = Var (Name "B")