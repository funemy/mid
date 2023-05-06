module TyCheck (
    infer,
    toEnv,
    runTyCk,
) where

import Env
import Err (errMsgTyCk)
import Lang (
    Closure (..),
    Env (..),
    ErrMsg,
    Name (..),
    Neutral (..),
    Term (..),
    Ty,
    TyCtx,
    TyCtxEntry (..),
    Val (..),
 )
import Norm (arrowTy, doApp, evalCls)
import qualified Norm as N (eval, indStepTy, reify, runEval, runReify)
import Prelude hiding (lookup)

-- | Computation of type checking
-- which is a computation that requires a typing context
--
-- The definitions below is essentially a reader monad,
-- but defining it ourself can remove some boilerplates.
newtype TyCk v = TyCk {runTyCk :: TyCtx -> Result v}

instance Functor TyCk where
    fmap f (TyCk comp) = TyCk $ \ctx -> fmap f (comp ctx)

instance Applicative TyCk where
    pure v = TyCk $ \_ -> pure v
    (TyCk f) <*> (TyCk comp) = TyCk $ \ctx ->
        let f' = f ctx
            comp' = comp ctx
         in f' <*> comp'

instance Monad TyCk where
    (TyCk comp) >>= f = TyCk $ \ctx -> do
        r <- comp ctx
        runTyCk (f r) ctx

failure :: ErrMsg -> TyCk v
failure err = TyCk $ \_ -> Left err

with :: (TyCtx -> TyCtx) -> TyCk v -> TyCk v
with f (TyCk comp) = TyCk $ \ctx -> comp (f ctx)

getCtx :: TyCk TyCtx
getCtx = TyCk $ \ctx -> pure ctx

-- Lifting a Result value to TyCk computation
-- So that we don't need to write a wrapper for every imported function that returns Result
lift :: Result v -> TyCk v
lift r = TyCk $ const r

-- Helper function that wraps `reify` from Norm module
reify :: Ty -> Val -> TyCk Term
reify ty v = do
    ctx <- getCtx
    lift $ N.runReify (N.reify ty v) (names ctx)

-- Helper function that wraps `eval` from Norm module
eval :: Term -> TyCk Val
eval t = do
    ctx <- getCtx
    lift $ N.runEval (N.eval t) (toEnv ctx)

type Depth = Int

-- used for alpha-equivalence checking
type NameSpace = Env Depth

-- the auxliary function for alpha equivalence checking
alphaEquiv' :: Depth -> NameSpace -> Term -> NameSpace -> Term -> Bool
-- simple cases
alphaEquiv' _ _ Nat _ Nat = True
alphaEquiv' _ _ Zero _ Zero = True
alphaEquiv' _ _ Top _ Top = True
alphaEquiv' _ _ Unit _ Unit = True
alphaEquiv' _ _ Absurd _ Absurd = True
alphaEquiv' _ _ Atom _ Atom = True
alphaEquiv' _ _ Universe _ Universe = True
alphaEquiv' _ _ Refl _ Refl = True
alphaEquiv' _ _ (Quote s1) _ (Quote s2) = s1 == s2
alphaEquiv' _ ns1 (Var n1) ns2 (Var n2) = lookup n1 ns1 == lookup n2 ns2
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
        ns1' = extend n1 d ns1
        ns2' = extend n2 d ns2
        equiv2 = alphaEquiv' (d + 1) ns1' t12 ns2' t22
     in equiv1 && equiv2
alphaEquiv' d ns1 (Lam n1 t1) ns2 (Lam n2 t2) =
    let ns1' = extend n1 d ns1
        ns2' = extend n2 d ns2
     in alphaEquiv' (d + 1) ns1' t1 ns2' t2
alphaEquiv' d ns1 (Sigma n1 t11 t12) ns2 (Sigma n2 t21 t22) =
    let equiv1 = alphaEquiv' d ns1 t11 ns2 t21
        ns1' = extend n1 d ns1
        ns2' = extend n2 d ns2
        equiv2 = alphaEquiv' (d + 1) ns1' t12 ns2' t22
     in equiv1 && equiv2
-- fallback case
alphaEquiv' _ _ _ _ _ = False

alphaEquiv :: Term -> Term -> Bool
alphaEquiv t1 = alphaEquiv' 0 emptyEnv t1 emptyEnv

lookupTy :: Name -> TyCk Ty
lookupTy n = do
    ctx <- getCtx
    entry <- lift $ lookup n ctx
    case entry of
        Decl ty -> pure ty
        Def ty _ -> pure ty

-- Convert a typing context into an Env of Val.
-- Used when calling `eval` in `infer`
toEnv :: TyCtx -> Env Val
toEnv (Env []) = Env []
toEnv (Env ((n, e) : xs)) = extend n v rest
  where
    rest = toEnv (Env xs)
    v = case e of
        Decl ty -> VNeutral ty (NVar n)
        Def _ val -> val

-- isXXXs below are a set of helper functions used in type checking
-- In the tutorial, these functions require TyCtx mostly for debugging.
-- We will keep the functions simple for the moment (instead of requiring TyCtx).
isPi :: Ty -> TyCk (Ty, Closure)
isPi (VPi tyA cls) = pure (tyA, cls)
isPi ty = failure $ errMsgTyCk "expect a Pi type, but got" ty

isSigma :: Ty -> TyCk (Ty, Closure)
isSigma (VSigma tyA cls) = pure (tyA, cls)
isSigma ty = failure $ errMsgTyCk "expect a Sigma type, but got" ty

isNat :: Ty -> TyCk ()
isNat VNat = pure ()
isNat ty = failure $ errMsgTyCk "expect a Nat type, but got" ty

isEq :: Ty -> TyCk (Ty, Val, Val)
isEq (VEqual ty t1 t2) = pure (ty, t1, t2)
isEq ty = failure $ errMsgTyCk "expect an Equal type, but got" ty

isAbsurd :: Ty -> TyCk ()
isAbsurd VAbsurd = pure ()
isAbsurd ty = failure $ errMsgTyCk "expect an Absurd type, but got" ty

infer :: Term -> TyCk Ty
infer (Var n) = do
    lookupTy n
infer (Pi n tyA tyB) = do
    check tyA VUniverse
    tyA' <- eval tyA
    with (extend n (Decl tyA')) (check tyB VUniverse)
    pure VUniverse
infer (App f a) = do
    fTy <- infer f
    (tyA, cls) <- isPi fTy
    check a tyA
    aVal <- eval a
    lift $ evalCls cls aVal
infer (Sigma n tyA tyB) = do
    check tyA VUniverse
    tyA' <- eval tyA
    with (extend n (Decl tyA')) (check tyB VUniverse)
    pure VUniverse
infer (Fst p) = do
    pTy <- infer p
    (tyA, _) <- isSigma pTy
    pure tyA
infer (Snd p) = do
    pTy <- infer p
    (_, cls) <- isSigma pTy
    l <- eval (Fst p)
    lift $ evalCls cls l
infer Nat = do
    pure VUniverse
infer Zero = do
    pure VNat
infer (Succ n) = do
    ty <- infer n
    isNat ty
    pure VNat
infer (IndNat prop base ind nat) = do
    -- nat => Nat
    natTy <- infer nat
    isNat natTy
    -- prop <= Pi x : Nat. U
    propTy <- with (const emptyEnv) (eval (Pi (Name "x") Nat Universe))
    check prop propTy
    -- base <= prop 0
    propZ <- eval (App prop Zero)
    check base propZ
    -- ind <= Pi k : Nat . prop k -> prop (k+1)
    propV <- eval prop
    propK <- lift $ N.indStepTy propV
    check ind propK
    -- conclusion: prop nat
    eval (App prop nat)
infer (Equal ty t1 t2) = do
    check ty VUniverse
    tyV <- eval ty
    check t1 tyV
    check t2 tyV
    pure VUniverse
infer (Subst prop propX eq) = do
    eqTy <- infer eq
    (tyA, x, y) <- isEq eqTy
    -- Construct a Pi-type value: A -> U
    let propTy = arrowTy tyA Universe
    -- check propX is indeed a proof of (prop x)
    -- (x came from the Equal type)
    --
    -- FIXME: calling `doApp` here is unsatisfying, because I want all doXXXs to be hidden
    -- in the Norm module.
    -- In theory we can still make things work by only calling `eval`,
    -- but that also requires creating dummy variables and extending the env.
    -- No satisfying solution for now :(.
    check prop propTy
    propV <- eval prop
    propXTy <- lift $ doApp propV x
    check propX propXTy
    -- constructing the return type, i.e., prop y
    lift $ doApp propV y
infer Top = do
    pure VUniverse
infer Unit = do
    pure VTop
infer Absurd = do
    pure VUniverse
infer (IndAbsurd ty absurd) = do
    absurdTy <- infer absurd
    isAbsurd absurdTy
    check ty VUniverse
    eval ty
infer Atom = do
    pure VUniverse
infer (Quote _) = do
    pure VAtom
infer Universe = do
    pure VUniverse
infer (As t ty) = do
    -- NOTE: this check guarantees that ty is actually a type
    -- otherwise it can be an arbitrary term
    check ty VUniverse
    ty' <- eval ty
    check t ty'
    pure ty'
infer t = failure $ errMsgTyCk "No inference rule for" t

-- Helper function
-- checking two values are alpha-equivalent under the given type
equiv :: Ty -> Val -> Val -> TyCk Bool
equiv ty x y = do
    x' <- reify ty x
    y' <- reify ty y
    pure $ alphaEquiv x' y'

check :: Term -> Ty -> TyCk ()
check (Lam name body) ty = do
    (tyA, cls) <- isPi ty
    tyB <- lift $ evalCls cls (VNeutral tyA (NVar name))
    with (extend name (Decl tyA)) (check body tyB)
check (MkPair l r) ty = do
    (tyA, cls) <- isSigma ty
    check l tyA
    lV <- eval l
    tyB <- lift $ evalCls cls lV
    check r tyB
check Refl eq = do
    (ty, x, y) <- isEq eq
    equal <- equiv ty x y
    if equal
        then return ()
        else failure $ errMsgTyCk "cannot prove equality by refl because x and y are not alpha-equivalent" (ty, x, y)
-- subsumption
check t ty1 = do
    ty2 <- infer t
    equal <- equiv VUniverse ty1 ty2
    if equal
        then pure ()
        else failure $ errMsgTyCk "cannot show equivalence between inferred and checked type on term" (t, ty1, ty2)
