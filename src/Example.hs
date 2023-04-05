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
plus a b = induction Nat (lambda "x" Nat) a (lambda "x" (lambda "y" (suc (var "y")))) b

ex1 :: Term
ex1 = plus (nat 2) (nat 3)

test1 :: IO ()
test1 = runTest ex1

---------------------------
-- Helper Functions Below
---------------------------

pp :: Show a => a -> IO ()
pp = pPrint

runTest :: Term -> IO ()
runTest = pPrint . run

x, y, z, p, q, k, f :: String
x = "x"
y = "y"
z = "z"
p = "p"
q = "q"
k = "k"
f = "f"
