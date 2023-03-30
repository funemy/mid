module Norm (Val (..)) where

import Env
import Lang (Name)

-- Types are nothing special but values
type Ty = Val

data Closure = Closure
    { cEnv :: Env Val
    , cName :: Name
    , cBody :: Val
    }
    deriving (Show)

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
    deriving (Show)

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
    deriving (Show)

-- Normal form
-- This is the resulting form we want for normalization.
-- Also the form which we will readback to recover a Term.
--
-- Notice that we do not need to include neutral terms here,
-- because neutral terms are also values (VNeutral)
data Normal = Normal Ty Val
    deriving (Show)