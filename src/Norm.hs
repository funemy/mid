module Norm (Val (..)) where

import Env
import Err (errMsgNorm)
import Lang (Name (..), Term (..))
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

-- Helper function for generating function type vales such as A->B
-- Function types are encoded as Pi-types.
-- Since the return type of VPi is a closure (i.e., its normalzation is delayed),
-- the second arg of this function is a Term (instead of Val).
-- NOTE:
-- This function is for creating function types whose input and output types are simple.
-- E.g., Nat -> Nat, Nat -> U
-- No sanity check is performed, use carefully.
vArrow :: Val -> Term -> Val
vArrow ty1 ty2 = VPi ty1 (Closure emptyEnv (Name "_dummy") ty2)

-- Helper function for evaluating closures
evalCls :: Closure -> Val -> Res Val
evalCls (Closure env name body) v =
    let env' = extend env name v
     in eval env' body

-- For each elimination form (except NVar?)
-- There should be a separate helper function, to keep eval simple
doApp :: Val -> Val -> Res Val
doApp f a = case f of
    VLam cls -> evalCls cls a
    VNeutral (VPi tyA cls) func -> do
        tyB <- evalCls cls a
        let aNorm = Normal tyA a
        Right $ VNeutral tyB (NApp func aNorm)
    t -> Left $ errMsgNorm "applying a non-function" t

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
doIndNat prop base ind = \case
    VZero -> Right base
    VSucc n -> do
        a <- doIndNat prop base ind n
        f <- doApp ind n
        doApp f a
    neu@(VNeutral VNat n) -> do
        ty <- doApp prop neu
        baseTy <- doApp prop VZero
        indTy <- indStepTy prop
        let propTy = vArrow VNat Universe
        let prop' = Normal propTy prop
        let base' = Normal baseTy base
        let ind' = Normal indTy ind
        Right $ VNeutral ty (NIndNat prop' base' ind' n)
    t -> Left $ errMsgNorm "using induction principle for nat on non-nat value" t
  where
    -- The type foa the induction step is quite complicated.
    -- So the way we construct it is to write a closed term, and call `eval` on it.
    -- Be careful, we also need to provide the correct Env when calling eval.
    -- The type for induction step is: \Pi n : Nat . p n -> p (n+1),
    -- where p is the property on natural number introduced by outer scope.
    indStepTy :: Val -> Res Val
    indStepTy pVal =
        let n = Name "n"
            nVar = Var n
            p = Name "p"
            pVar = Var p
            t = Pi n Nat (Pi (Name "_dummy") (App pVar nVar) (App pVar (Succ nVar)))
            env = Env [(Name "p", pVal)]
         in eval env t

doSubst :: Val -> Val -> Val -> Res Val
doSubst prop pfA = \case
    VRefl -> Right pfA
    VNeutral (VEqual _ a _) eq -> do
        -- The proposition (p x) (notice the type of p is A -> U)
        ty' <- doApp prop a
        let propNorm = Normal VUniverse prop
        let pfANorm = Normal ty' pfA
        Right $ VNeutral ty' (NSubst propNorm pfANorm eq)
    t -> Left $ errMsgNorm "substituing on non-equality proof" t

doIndAbsurd :: Val -> Val -> Res Val
doIndAbsurd prop = \case
    VNeutral VAbsurd neu ->
        let propNorm = Normal VUniverse prop
         in Right $ VNeutral prop (NIndAbsurd propNorm neu)
    t -> Left $ errMsgNorm "using induction principle for absuridity on non-absurd value" t

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

-- AKA readback
-- Convert normal forms back into terms, guided by type.
-- The reification in dependent-type system is slightly different from simpler systems.
-- NOTE: In DT-language, reification can happen during type checking, therefore it requires a typing context as its first argument.
reify :: TyCtx -> Normal -> Res Term
reify ctx (Normal ty val) = reify' ctx ty val

-- Notice that when pattern matching the second argument,
-- we only match against those values that represent types.
reify' :: TyCtx -> Ty -> Val -> Res Term
-- terms
reify' ctx (VPi tyA cls@(Closure _ n _)) f = do
    let xName = freshen (names ctx) n
    let xVal = VNeutral tyA (NVar xName)
    retTy <- evalCls cls xVal
    app <- doApp f xVal
    body' <- reify' (extend ctx xName (Decl tyA)) retTy app
    Right $ Lam xName body'
reify' ctx (VSigma tyA cls) p = do
    l <- doFst p
    r <- doSnd p
    tyB <- evalCls cls l
    l' <- reify' ctx tyA l
    r' <- reify' ctx tyB r
    Right $ MkPair l' r'
reify' _ VNat VZero = Right Zero
reify' ctx VNat (VSucc n) = do
    n' <- reify' ctx VNat n
    Right (Succ n')
reify' _ (VEqual{}) VRefl = Right Refl
-- any terms with unit type can only be Unit
reify' _ VUnitTy _ = Right Unit
reify' _ VAtom (VQuote s) = Right (Quote s)
-- types
reify' _ VUniverse VNat = Right Nat
reify' _ VUniverse VUnitTy = Right UnitTy
reify' _ VUniverse VAtom = Right Atom
reify' _ VUniverse VAbsurd = Right Absurd
reify' ctx VUniverse (VPi tyA cls@(Closure _ n _)) = do
    tyA' <- reify' ctx VUniverse tyA
    let xName = freshen (names ctx) n
    let xVal = VNeutral tyA (NVar xName)
    tyB <- evalCls cls xVal
    tyB' <- reify' (extend ctx xName (Decl xVal)) VUniverse tyB
    Right $ Pi xName tyA' tyB'
reify' ctx VUniverse (VSigma tyA cls@(Closure _ n _)) = do
    tyA' <- reify' ctx VUniverse tyA
    let xName = freshen (names ctx) n
    let xVal = VNeutral tyA (NVar xName)
    tyB <- evalCls cls xVal
    tyB' <- reify' (extend ctx xName (Decl xVal)) VUniverse tyB
    Right $ Sigma xName tyA' tyB'
reify' ctx VUniverse (VEqual ty t1 t2) = do
    ty' <- reify' ctx VUniverse ty
    t1' <- reify' ctx ty t1
    t2' <- reify' ctx ty t2
    Right $ Equal ty' t1' t2'
-- universe
-- NOTE: I'm not sure about this
reify' _ VUniverse VUniverse = Right Universe
-- neutral terms
-- NOTE: I'm not sure how absurd should be handled properly
reify' ctx VAbsurd (VNeutral VAbsurd neu) = do
    neu' <- reifyNeu ctx neu
    Right (As neu' Absurd)
reify' ctx ty (VNeutral ty' neu) =
    if ty == ty'
        then reifyNeu ctx neu
        else Left $ errMsgNorm "reifying neutral terms with incompatible types" (ty, ty)
-- invalid patterns
reify' _ ty v = Left $ errMsgNorm "cannot reify values with incompatible types" (v, ty)

reifyNeu :: TyCtx -> Neutral -> Res Term
reifyNeu ctx (NVar n) = Right $ Var n
reifyNeu ctx (NApp f a) = do
    f' <- reifyNeu ctx f
    a' <- reify ctx a
    Right $ App f' a'
reifyNeu ctx (NFst p) = do
    p' <- reifyNeu ctx p
    Right $ Fst p'
reifyNeu ctx (NSnd p) = do
    p' <- reifyNeu ctx p
    Right $ Snd p'
reifyNeu ctx (NIndNat norm1 norm2 norm3 neu) = do
    norm1' <- reify ctx norm1
    norm2' <- reify ctx norm2
    norm3' <- reify ctx norm3
    neu' <- reifyNeu ctx neu
    Right $ IndNat norm1' norm2' norm3' neu'
reifyNeu ctx (NSubst norm1 norm2 neu) = do
    norm1' <- reify ctx norm1
    norm2' <- reify ctx norm2
    neu' <- reifyNeu ctx neu
    Right $ Subst norm1' norm2' neu'
reifyNeu ctx (NIndAbsurd norm neu) = do
    norm' <- reify ctx norm
    neu' <- reifyNeu ctx neu
    Right $ IndAbsurd norm' (As neu' Absurd)
