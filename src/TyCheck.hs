module TyCheck (
    Ty,
    Closure (..),
    Neutral (..),
    Val (..),
    Normal (..),
    TyCtxEntry (..),
    TyCtx,
) where

import Env
import Lang (Name, Term (..))
import Prelude hiding (lookup)

-- Types are nothing special but values
type Ty = Val

data Closure = Closure
    { cEnv :: Env Val
    , cName :: Name
    , cBody :: Term
    }
    deriving (Show, Eq)

-- Neutral terms are terms in elimination form, but cannot be reduced.
-- E.g., an application whose first element is a variable.
data Neutral
    = NVar Name
    | NApp Neutral Normal
    | NFst Neutral
    | NSnd Neutral
    | NIndNat Normal Normal Normal Neutral
    | NSubst Normal Normal Neutral
    | NIndAbsurd Normal Neutral
    deriving (Show, Eq)

-- The definition of Value should correspond to each ctor defined in Term
-- (Notice not all elements of Term are ctor, e.g., Fst and Snd are eliminator)
--
-- The special ctors in the value definition in a DT language are VPi and VSigma
-- Both of them are constructing types whose second element dependent the first.
-- In other words, the second element is a function (at type-level, conceptually).
-- Therefore, we represent them as VPi Ty Closure (VSigma has the same def),
-- where Ty represents the first element (a non-dependent type).
--
-- Since in DT-language, types and terms are the same thing, the Ty is simply a type synonym for readability
data Val
    = VPi Ty Closure
    | VLam Closure
    | VSigma Ty Closure
    | VMkPair Val Val
    | VNat
    | VZero
    | VSucc Val
    | VEqual Ty Val Val
    | VRefl
    | VUnitTy
    | VUnit
    | VAbsurd
    | VAtom
    | VQuote String
    | VUniverse
    | VNeutral Ty Neutral
    deriving (Show, Eq)

-- Normal form
-- This is the resulting form we want for normalization.
-- Also the form which we will readback to recover a Term.
--
-- Notice that we do not need to include neutral terms here,
-- because neutral terms are also values (VNeutral)
data Normal = Normal Ty Val
    deriving (Show, Eq)

-- Typing context for dependent type checking
-- In DT system, typing context consists of two kinds of entries
-- 1. Variable declarations (abstractions?),
-- i.e., mappings from variable names to their types, introduced by Lam, Pi, and Sigma.
-- 2. Definitions, i.e., mappings from variable names to their definitions (values)
--
-- The reason for having the definition ctx is that we can have expressions in the types now.
-- Those expressions might refer to existing definitions (e.g., calling a type-level function.)
-- We could in theory having two contexts and manage them separately,
-- but that would complicate things like shadowing and computing used names.
data TyCtxEntry
    = Decl Ty
    | Def Ty Val
    deriving (Show)

type TyCtx = Env TyCtxEntry

type Depth = Int

-- used for alpha-equivalence checking
type NameSpace = Env Depth

-- the auxliary function for alpha equivalence checking
alphaEquiv' :: Int -> NameSpace -> Term -> NameSpace -> Term -> Bool
-- simple cases
alphaEquiv' _ _ Nat _ Nat = True
alphaEquiv' _ _ Zero _ Zero = True
alphaEquiv' _ _ UnitTy _ UnitTy = True
alphaEquiv' _ _ Unit _ Unit = True
alphaEquiv' _ _ Absurd _ Absurd = True
alphaEquiv' _ _ Atom _ Atom = True
alphaEquiv' _ _ Universe _ Universe = True
alphaEquiv' _ _ Refl _ Refl = True
alphaEquiv' _ _ (Quote s1) _ (Quote s2) = s1 == s2
alphaEquiv' _ ns1 (Var n1) ns2 (Var n2) = lookup ns1 n1 == lookup ns2 n2
-- inductive cases
alphaEquiv' d ns1 (App t11 t12) ns2 (App t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
alphaEquiv' d ns1 (MkPair t11 t12) ns2 (MkPair t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
alphaEquiv' d ns1 (Fst t1) ns2 (Fst t2) = alphaEquiv' d ns1 t1 ns2 t2
alphaEquiv' d ns1 (Snd t1) ns2 (Snd t2) = alphaEquiv' d ns1 t1 ns2 t2
alphaEquiv' d ns1 (Succ t1) ns2 (Succ t2) = alphaEquiv' d ns1 t1 ns2 t2
alphaEquiv' d ns1 (IndAbsurd t11 t12) ns2 (IndAbsurd t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
-- Special case:
-- If two terms can be type cheked to be Absurd, then they are alpha equivalent no matter what
-- When encountering an absurd term, we just annotate them with type Absurd
-- so the terms are alpha-equivalent no matter what.
-- Otherwise, we don't have a way of type-checking them, because Absurd
-- has no inhabitant.
alphaEquiv' _ _ (As _ Absurd) _ (As _ Absurd) = True
alphaEquiv' d ns1 (As t11 t12) ns2 (As t21 t22) = alphaEquiv' d ns1 t11 ns2 t21 && alphaEquiv' d ns1 t12 ns2 t22
alphaEquiv' d ns1 (Equal t11 t12 t13) ns2 (Equal t21 t22 t23) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        equiv2 = alphaEquiv' d ns1 t12 ns2 t22
        equiv3 = alphaEquiv' d ns1 t13 ns2 t23
     in equiv1 && equiv2 && equiv3
alphaEquiv' d ns1 (Subst t11 t12 t13) ns2 (Subst t21 t22 t23) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        equiv2 = alphaEquiv' d ns1 t12 ns2 t22
        equiv3 = alphaEquiv' d ns1 t13 ns2 t23
     in equiv1 && equiv2 && equiv3
alphaEquiv' d ns1 (IndNat t11 t12 t13 t14) ns2 (IndNat t21 t22 t23 t24) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        equiv2 = alphaEquiv' d ns1 t12 ns2 t22
        equiv3 = alphaEquiv' d ns1 t13 ns2 t23
        equiv4 = alphaEquiv' d ns1 t14 ns2 t24
     in equiv1 && equiv2 && equiv3 && equiv4
-- interesting cases
alphaEquiv' d ns1 (Pi n1 t11 t12) ns2 (Pi n2 t21 t22) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        ns1' = extend ns1 n1 d
        ns2' = extend ns2 n2 d
        equiv2 = alphaEquiv' (d + 1) ns1' t12 ns2' t22
     in equiv1 && equiv2
alphaEquiv' d ns1 (Lam n1 t1) ns2 (Lam n2 t2) =
    let ns1' = extend ns1 n1 d
        ns2' = extend ns2 n2 d
     in alphaEquiv' (d + 1) ns1' t1 ns2' t2
alphaEquiv' d ns1 (Sigma n1 t11 t12) ns2 (Sigma n2 t21 t22) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        ns1' = extend ns1 n1 d
        ns2' = extend ns2 n2 d
        equiv2 = alphaEquiv' (d + 1) ns1' t12 ns2' t22
     in equiv1 && equiv2
-- fallback case
alphaEquiv' _ _ _ _ _ = False

alphaEquiv :: Term -> Term -> Bool
alphaEquiv t1 t2 = alphaEquiv' 0 emptyEnv t1 emptyEnv t2

-- note that type is also a term, therefore the return type is Term
infer :: TyCtx -> Term -> Res Ty
infer = undefined

check :: TyCtx -> Term -> Ty -> Res ()
check = undefined
