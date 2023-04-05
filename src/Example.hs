{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}

{-# HLINT ignore "Eta reduce" #-}

module Example () where

import DSL
import Env (Res)
import Text.Pretty.Simple (pPrint)
import Toplevel (Output, run)
import Prelude hiding (fst, pi, snd, (*), (==))

plus :: Term -> Term -> Term
plus a b = induction Nat (lambda x Nat) a (lambda x (lambda y (suc (var y)))) b

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
ex4 = lambda x (induction Absurd ((ex1 === nat 42) Nat) (var x)) `as` (Absurd ~> (ex1 === nat 42) Nat)

test4 :: IO ()
test4 = runTest ex4

---------------------------
-- Helper Functions Below
---------------------------

pp :: Show a => a -> IO ()
pp = pPrint

runTest :: Term -> IO ()
runTest = pp . run

x, y, z, p, q, k, f :: String
x = "x"
y = "y"
z = "z"
p = "p"
q = "q"
k = "k"
f = "f"
