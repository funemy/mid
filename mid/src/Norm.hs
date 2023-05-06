module Norm (
    eval,
    evalCls,
    reify,
    reify',
    indStepTy,
    doApp,
    doFst,
    doSnd,
    doIndAbsurd,
    doIndNat,
    doSubst,
    runEval,
    runNorm,
    runReify,
    arrowTy,
) where

import Env
import Err (errMsgNorm)
import Lang (
    Closure (..),
    Env (..),
    ErrMsg,
    Name (..),
    Neutral (..),
    Normal (..),
    Term (..),
    Ty,
    Val (..),
    fail',
 )
import Prelude hiding (lookup)

-- | Computation of normalization
-- `runNorm` take a list of used names and an environment
newtype Norm v = Norm {runNorm :: [Name] -> Env Val -> Result v}

instance Functor Norm where
    fmap f (Norm comp) = Norm $ \used env -> fmap f (comp used env)

instance Applicative Norm where
    pure v = Norm $ \_ _ -> pure v
    (Norm f) <*> (Norm comp) = Norm $ \used env ->
        let f' = f used env
            comp' = comp used env
         in f' <*> comp'

instance Monad Norm where
    (Norm comp) >>= f = Norm $ \used env -> do
        r <- comp used env
        runNorm (f r) used env

failure :: ErrMsg -> Norm v
failure err = Norm $ \_ _ -> Left err

lift :: Result v -> Norm v
lift r = Norm $ \_ _ -> r

getUsed :: Norm [Name]
getUsed = Norm $ \used _ -> pure used

getEnv :: Norm (Env Val)
getEnv = Norm $ \_ env -> pure env

-- evaluate with the given environment
withEnv :: Env Val -> Norm v -> Norm v
withEnv env (Norm comp) = Norm $ \used _ -> comp used env

withUsed :: [Name] -> Norm v -> Norm v
withUsed used (Norm comp) = Norm $ \_ env -> comp used env

-- Evaluation does not require used names to run
runEval :: Norm v -> Env Val -> Result v
runEval n = runNorm n []

-- Reification does not require environment to run
runReify :: Norm v -> [Name] -> Result v
runReify n used = runNorm n used emptyEnv

-- Helper function for generating function type vales such as A->B
-- Function types are encoded as Pi-types.
-- Since the return type of VPi is a closure (i.e., its normalzation is delayed),
-- the second arg of this function is a Term (instead of Val).
-- NOTE:
-- This function is for creating function types whose input and output types are simple.
-- E.g., Nat -> Nat, Nat -> U
-- No sanity check is performed, use carefully.
arrowTy :: Val -> Term -> Val
arrowTy ty1 ty2 = VPi ty1 (Closure emptyEnv (Name "k") ty2)

-- Helper function for evaluating closures
evalCls :: Closure -> Val -> Result Val
evalCls (Closure env name body) v =
    let env' = extend name v env
     in runEval (eval body) env'

-- This function is used internally in this modual, so we don't need to lift the result of `evalCls` every time.
evalCls' :: Closure -> Val -> Norm Val
evalCls' (Closure env name body) v = withEnv (extend name v env) (eval body)

-- For each elimination form, there is a `doXXX` helper function
-- The original motivation is to keep the body of `eval` simpler,
-- since all elimination forms are slightly more complex to handle.
-- `doApp` is also used in type checking to reduce function applications.
doApp :: Val -> Val -> Result Val
doApp f a = case f of
    VLam cls -> evalCls cls a
    VNeutral (VPi tyA cls) func -> do
        tyB <- evalCls cls a
        let aNorm = Normal tyA a
        pure $ VNeutral tyB (NApp func aNorm)
    t -> fail' $ errMsgNorm "applying a non-function" t

doFst :: Val -> Result Val
doFst = \case
    VMkPair l _ -> pure l
    VNeutral (VSigma ty _) p -> pure $ VNeutral ty (NFst p)
    t -> fail' $ errMsgNorm "projecting a non-pair value" t

doSnd :: Val -> Result Val
doSnd = \case
    VMkPair _ r -> pure r
    VNeutral (VSigma tyA cls) p -> do
        tyB <- evalCls cls tyA
        pure $ VNeutral tyB (NSnd p)
    t -> fail' $ errMsgNorm "projecting a non-pair value" t

doIndNat :: Val -> Val -> Val -> Val -> Result Val
doIndNat prop base ind = \case
    VZero -> pure base
    VSucc n -> do
        a <- doIndNat prop base ind n
        f <- doApp ind n
        doApp f a
    neu@(VNeutral VNat n) -> do
        ty <- doApp prop neu
        baseTy <- doApp prop VZero
        indTy <- indStepTy prop
        let propTy = arrowTy VNat Universe
        let prop' = Normal propTy prop
        let base' = Normal baseTy base
        let ind' = Normal indTy ind
        pure $ VNeutral ty (NIndNat prop' base' ind' n)
    t -> fail' $ errMsgNorm "using induction principle for nat on non-nat value" t

-- Helper function for constructing the types for the inductive step of natural numbers
-- 1st param: a property of natural numbers (normalzed to value)
--
-- The way this function works is to construct a closed term for the type of inductive step,
-- and call `eval` on it.
--
-- NOTE: Be careful, we need to provide the correct Env when calling `eval`.
-- The type for induction step is: \Pi n : Nat . p n -> p (n+1),
-- where p is the property on natural number introduced by outer scope.
-- NOTE: This function is also helpful in type checking
indStepTy :: Val -> Result Val
indStepTy pVal =
    let n = Name "n"
        nVar = Var n
        p = Name "p"
        pVar = Var p
        t = Pi n Nat (Pi (Name "_dummy") (App pVar nVar) (App pVar (Succ nVar)))
        env = Env [(Name "p", pVal)]
     in runEval (eval t) env

doSubst :: Val -> Val -> Val -> Result Val
doSubst prop pfA = \case
    VRefl -> pure pfA
    VNeutral (VEqual ty a b) eq -> do
        -- The proposition (p x) (notice the type of p is A -> U)
        propATy <- doApp prop a
        propBTy <- doApp prop b
        let propTy = arrowTy ty Universe
            propNorm = Normal propTy prop
            pfANorm = Normal propATy pfA
        pure $ VNeutral propBTy (NSubst propNorm pfANorm eq)
    t -> fail' $ errMsgNorm "substituing on non-equality proof" t

doIndAbsurd :: Val -> Val -> Result Val
doIndAbsurd prop = \case
    VNeutral VAbsurd neu ->
        let propNorm = Normal VUniverse prop
         in pure $ VNeutral prop (NIndAbsurd propNorm neu)
    t -> fail' $ errMsgNorm "using induction principle for absuridity on non-absurd value" t

-- Eval function
eval :: Term -> Norm Val
eval (Var n) = do
    env <- getEnv
    lift $ lookup n env
eval (Pi n tyA tyB) = do
    tyA' <- eval tyA
    env <- getEnv
    pure $ VPi tyA' (Closure env n tyB)
eval (Lam n t) = do
    env <- getEnv
    pure $ VLam (Closure env n t)
eval (App f a) = do
    f' <- eval f
    a' <- eval a
    lift $ doApp f' a'
eval (Sigma n tyA tyB) = do
    tyA' <- eval tyA
    env <- getEnv
    pure $ VSigma tyA' (Closure env n tyB)
eval (MkPair l r) = do
    l' <- eval l
    r' <- eval r
    pure $ VMkPair l' r'
eval (Fst p) = do
    p' <- eval p
    lift $ doFst p'
eval (Snd p) = do
    p' <- eval p
    lift $ doSnd p'
eval Nat = pure VNat
eval Zero = pure VZero
eval (Succ n) = do
    n' <- eval n
    pure (VSucc n')
eval (IndNat t1 t2 t3 t4) = do
    t1' <- eval t1
    t2' <- eval t2
    t3' <- eval t3
    t4' <- eval t4
    lift $ doIndNat t1' t2' t3' t4'
eval (Equal ty t1 t2) = do
    ty' <- eval ty
    t1' <- eval t1
    t2' <- eval t2
    pure $ VEqual ty' t1' t2'
eval Refl = pure VRefl
eval (Subst t1 t2 t3) = do
    t1' <- eval t1
    t2' <- eval t2
    t3' <- eval t3
    lift $ doSubst t1' t2' t3'
eval Top = pure VTop
eval Unit = pure VUnit
eval Absurd = pure VAbsurd
eval (IndAbsurd t1 t2) = do
    t1' <- eval t1
    t2' <- eval t2
    lift $ doIndAbsurd t1' t2'
eval Atom = pure VAtom
eval (Quote s) = pure (VQuote s)
eval Universe = pure VUniverse
eval (As t _) = eval t

-- AKA readback
-- Convert normal forms back into terms, guided by type.
-- The reification in dependent-type system is slightly different from simpler systems.
-- NOTE: In DT-language, reification can happen during type checking, therefore it requires a typing context as its first argument.
reify' :: Normal -> Norm Term
reify' (Normal ty val) = reify ty val

-- Notice that when pattern matching the second argument,
-- we only match against those values that represent types.
reify :: Ty -> Val -> Norm Term
-- terms
reify (VPi tyA cls@(Closure _ n _)) f = do
    used <- getUsed
    let xName = freshen used n
    let xVal = VNeutral tyA (NVar xName)
    retTy <- evalCls' cls xVal
    app <- lift $ doApp f xVal
    body' <- withUsed (xName : used) (reify retTy app)
    pure $ Lam xName body'
reify (VSigma tyA cls) p = do
    l <- lift $ doFst p
    r <- lift $ doSnd p
    tyB <- evalCls' cls l
    l' <- reify tyA l
    r' <- reify tyB r
    pure $ MkPair l' r'
reify VNat VZero = pure Zero
reify VNat (VSucc n) = do
    n' <- reify VNat n
    pure (Succ n')
reify (VEqual{}) VRefl = pure Refl
-- any terms with unit type can only be Unit
reify VTop _ = pure Unit
reify VAtom (VQuote s) = pure (Quote s)
-- types
reify VUniverse VNat = pure Nat
reify VUniverse VTop = pure Top
reify VUniverse VAtom = pure Atom
reify VUniverse VAbsurd = pure Absurd
reify VUniverse (VPi tyA cls@(Closure _ n _)) = do
    tyA' <- reify VUniverse tyA
    used <- getUsed
    let xName = freshen used n
    let xVal = VNeutral tyA (NVar xName)
    tyB <- evalCls' cls xVal
    tyB' <- withUsed (xName : used) (reify VUniverse tyB)
    pure $ Pi xName tyA' tyB'
reify VUniverse (VSigma tyA cls@(Closure _ n _)) = do
    tyA' <- reify VUniverse tyA
    used <- getUsed
    let xName = freshen used n
    let xVal = VNeutral tyA (NVar xName)
    tyB <- evalCls' cls xVal
    tyB' <- withUsed (xName : used) (reify VUniverse tyB)
    pure $ Sigma xName tyA' tyB'
reify VUniverse (VEqual ty t1 t2) = do
    ty' <- reify VUniverse ty
    t1' <- reify ty t1
    t2' <- reify ty t2
    pure $ Equal ty' t1' t2'
-- universe
-- NOTE: I'm not sure about this
reify VUniverse VUniverse = pure Universe
-- neutral terms
-- NOTE: I'm not sure how absurd should be handled properly
reify VAbsurd (VNeutral VAbsurd neu) = do
    neu' <- reifyNeu neu
    pure (As neu' Absurd)
reify ty (VNeutral ty' neu) =
    if ty == ty'
        then reifyNeu neu
        else failure $ errMsgNorm "reifying neutral terms with incompatible types" (ty, ty')
-- invalid patterns
reify ty v = failure $ errMsgNorm "cannot reify values with incompatible types" (v, ty)

reifyNeu :: Neutral -> Norm Term
reifyNeu (NVar n) = pure $ Var n
reifyNeu (NApp f a) = do
    f' <- reifyNeu f
    a' <- reify' a
    pure $ App f' a'
reifyNeu (NFst p) = do
    p' <- reifyNeu p
    pure $ Fst p'
reifyNeu (NSnd p) = do
    p' <- reifyNeu p
    pure $ Snd p'
reifyNeu (NIndNat norm1 norm2 norm3 neu) = do
    norm1' <- reify' norm1
    norm2' <- reify' norm2
    norm3' <- reify' norm3
    neu' <- reifyNeu neu
    pure $ IndNat norm1' norm2' norm3' neu'
reifyNeu (NSubst norm1 norm2 neu) = do
    norm1' <- reify' norm1
    norm2' <- reify' norm2
    neu' <- reifyNeu neu
    pure $ Subst norm1' norm2' neu'
reifyNeu (NIndAbsurd norm neu) = do
    norm' <- reify' norm
    neu' <- reifyNeu neu
    pure $ IndAbsurd norm' (As neu' Absurd)
