module Lang (
    Closure (..),
    Env (..),
    Name (..),
    Neutral (..),
    Normal (..),
    Term (..),
    Ty,
    TyCtx,
    TyCtxEntry (..),
    Val (..),
    annotated,
) where

import Data.Bifunctor (Bifunctor (second))
import Text.Printf (printf)

newtype Name = Name String
    deriving (Eq)

instance Show Name where
    show (Name s) = s

-- TODO: add List and Vec
-- TODO: add Either
-- FIXME: missing sym/cong/trans for equality
data Term
    = Var Name
    | Pi Name Term Term
    | Lam Name Term
    | App Term Term
    | Sigma Name Term Term
    | -- | Pair constructor
      MkPair Term Term
    | Fst Term
    | Snd Term
    | Nat
    | Zero
    | Succ Term
    | -- | indNat has the same signature as ATAPL
      -- 1st term: the Property (Nat -> U)
      -- 2nd term: the base case (p 0)
      -- 3rd term: the inductive case
      -- 4th term: the number
      IndNat Term Term Term Term
    | -- | Equality type
      -- The 1st argument is the type of the 2nd and 3rd
      -- TODO: we should be able to infer the 1st argument
      Equal Term Term Term
    | -- Ctor for Equality types (i.e., refl)
      -- I'm curious about this, isn't `refl` in Agda takes implicit arguments?
      Refl
    | -- | Substitution on equal terms
      -- Given a property p of some type A, a proof that p holds on an element x : A,
      -- and a proof of x = y (y, of course, should also be of type A),
      -- returns a proof that p also holds on y
      -- 1st term: property p
      -- 2nd term: proof of the first property on x, i.e., (p x)
      -- 3rd term: equality proof of x=y
      Subst Term Term Term
    | UnitTy
    | Unit
    | Absurd
    | -- | Induction principle for Absurd
      -- Given a proposition we want to prove, and a proof of absurdity,
      -- returns a proof of the target proposition
      -- 1st term: the proposition p we want to prove, p : U
      -- 2nd term: a proof of absurdity
      IndAbsurd Term Term
    | -- | Atom type as in "The Litte Typer"
      Atom
    | -- | Ctor for Atom values
      Quote String
    | Universe
    | -- | Type annotation (ascription)
      -- 1st term: term,
      -- 2nd term: type
      As Term Term
    deriving (Eq)

-- A helper function for pretty printing Nats
toInt :: Term -> Int
toInt Zero = 0
toInt (Succ x) = 1 + toInt x
toInt _ = error "Cannot print ill-formed natural numbers."

annotated :: Term -> Bool
annotated (As _ _) = True
annotated _ = False

instance Show Term where
    show (Var s) = show s
    show (Pi n ty@(Sigma{}) ty') = printf "Π%s:(%s).%s" (show n) (show ty) (show ty')
    show (Pi n ty@(Pi{}) ty') = printf "Π%s:(%s).%s" (show n) (show ty) (show ty')
    show (Pi n ty@(Equal{}) ty') = printf "Π%s:(%s).%s" (show n) (show ty) (show ty')
    show (Pi n ty ty') = printf "Π%s:%s.%s" (show n) (show ty) (show ty')
    show (Lam n b) = printf "λ%s.%s" (show n) (show b)
    show (App f a) = printf "%s %s" (show f) (show a)
    show (Sigma n ty@(Pi{}) ty') = printf "Σ%s:(%s).%s" (show n) (show ty) (show ty')
    show (Sigma n ty@(Sigma{}) ty') = printf "Σ%s:(%s).%s" (show n) (show ty) (show ty')
    show (Sigma n ty ty') = printf "Σ%s:%s.%s" (show n) (show ty) (show ty')
    show (MkPair l r) = printf "(%s, %s)" (show l) (show r)
    show (Fst p) = printf "fst %s" (show p)
    show (Snd p) = printf "snd %s" (show p)
    show Nat = "Nat"
    show Zero = "0"
    show (Succ v@(Var _)) = "succ " ++ show v
    show n@(Succ _) = show $ toInt n
    show (IndNat ty t1 t2 t3) = printf "(ind-nat (%s) %s (%s) %s)" (show ty) (show t1) (show t2) (show t3)
    show (Equal ty t1 t2) = printf "%s≡%s:%s" (show t1) (show t2) (show ty)
    show Refl = "refl"
    show (Subst t1 t2 t3) = printf "(subst %s %s %s)" (show t1) (show t2) (show t3)
    show UnitTy = "Unit"
    show Unit = "()"
    show Absurd = "⊥"
    show (IndAbsurd e ty) = printf "(ind-absurd (%s) (%s))" (show e) (show ty)
    show Atom = "Atom"
    show (Quote s) = printf "'%s" s
    show Universe = "U"
    show (As e ty) = printf "%s : %s" (show e) (show ty)

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

-- Types are nothing special but values
type Ty = Val

-- Normal form
-- This is the resulting form we want for normalization.
-- Also the form which we will readback to recover a Term.
--
-- Notice that we do not need to include neutral terms here,
-- because neutral terms are also values (VNeutral)
data Normal = Normal Ty Val
    deriving (Show, Eq)

-- | Typing context for dependent type checking
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

-- FIXME: Consider change this name, as there isn't a clear distinction between typing ctx vs evaluation ctx.
type TyCtx = Env TyCtxEntry

-- A generic definition of environment
-- All utility functions on Env are deinfed in Env.hs
-- Definition of Env is here to resolve cyclic dependencies
newtype Env v = Env [(Name, v)]
    deriving (Show, Eq)

instance Functor Env where
    fmap f (Env xs) = Env (map (second f) xs)