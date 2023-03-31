module Norm (Val (..)) where

import Env
import Err (errMsgNorm)
import Lang (Name, Term (..))
import Prelude hiding (lookup)

-- Types are nothing special but values
type Ty = Val

data Closure = Closure
    { cEnv :: Env Val
    , cName :: Name
    , cBody :: Term
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

-- Helper function for evaluating closures
evalCls :: Closure -> Val -> Res Val
evalCls (Closure env name body) v =
    let env' = extend env name v
     in eval env' body

-- For each elimination form (except NVar?)
-- There should be a separate helper function, to keep eval simple
doApp :: Val -> Val -> Res Val
doApp = undefined

doFst :: Val -> Res Val
doFst = \case
    VMkPair l _ -> Right l
    VNeutral (VSigma ty _) p -> Right $ VNeutral ty (NFst p)
    t -> Left $ errMsgNorm "projecting a non-pair value" t

doSnd :: Val -> Res Val
doSnd = \case
    VMkPair _ r -> Right r
    VNeutral (VSigma tyA cls) p -> do
        tyB <- evalCls cls tyA
        Right $ VNeutral tyB (NSnd p)
    t -> Left $ errMsgNorm "projecting a non-pair value" t

doIndNat :: Val -> Val -> Val -> Val -> Res Val
doIndNat = undefined

doSubst :: Val -> Val -> Val -> Res Val
doSubst = undefined

doIndAbsurd :: Val -> Val -> Res Val
doIndAbsurd = undefined

-- Eval function
eval :: Env Val -> Term -> Res Val
eval env (Var n) = lookup env n
eval env (Pi n tyA tyB) = do
    tyA' <- eval env tyA
    Right $ VPi tyA' (Closure env n tyB)
eval env (Lam n t) = Right $ VLam (Closure env n t)
eval env (App f a) = do
    f' <- eval env f
    a' <- eval env a
    doApp f' a'
eval env (Sigma n tyA tyB) = do
    tyA' <- eval env tyA
    Right $ VSigma tyA' (Closure env n tyB)
eval env (MkPair l r) = do
    l' <- eval env l
    r' <- eval env r
    Right $ VMkPair l' r'
eval env (Fst p) = do
    p' <- eval env p
    doFst p'
eval env (Snd p) = do
    p' <- eval env p
    doSnd p'
eval _ Nat = Right VNat
eval _ Zero = Right VZero
eval env (Succ n) = do
    n' <- eval env n
    Right (VSucc n')
eval env (IndNat t1 t2 t3 t4) = do
    t1' <- eval env t1
    t2' <- eval env t2
    t3' <- eval env t3
    t4' <- eval env t4
    doIndNat t1' t2' t3' t4'
eval env (Equal ty t1 t2) = do
    ty' <- eval env ty
    t1' <- eval env t1
    t2' <- eval env t2
    Right $ VEqual ty' t1' t2'
eval _ Refl = Right VRefl
eval env (Subst t1 t2 t3) = do
    t1' <- eval env t1
    t2' <- eval env t2
    t3' <- eval env t3
    doSubst t1' t2' t3'
eval _ UnitTy = Right VUnitTy
eval _ Unit = Right VUnit
eval _ Absurd = Right VAbsurd
eval env (IndAbsurd t1 t2) = do
    t1' <- eval env t1
    t2' <- eval env t2
    doIndAbsurd t1' t2'
eval _ Atom = Right VAtom
eval _ (Quote s) = Right (VQuote s)
eval _ Universe = Right VUniverse
eval env (As t _) = eval env t

reify :: Normal -> Term
reify = undefined

-- TODO: I still need to think about the difference between eval and reflect
-- To me, it seems more like eval is do the beta-reduction
-- and reflect is doing eta-expansion
reflect :: Term -> Val
reflect = undefined

type Definition = Normal

type Defs = Env Definition

addDefs :: Defs -> [(Name, Term)] -> Res Defs
addDefs = undefined
