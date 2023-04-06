module TyCheck (
    infer,
    toEnv,
) where

import Debug.Trace
import Env
import Err (errMsgTyCk)
import Lang (
    Closure (..),
    Env (..),
    Name (..),
    Neutral (..),
    Term (..),
    Ty,
    TyCtx,
    TyCtxEntry (..),
    Val (..),
 )
import Norm (doApp, eval, evalCls, indStepTy, reify')
import Prelude hiding (lookup)

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
alphaEquiv t1 = alphaEquiv' 0 emptyEnv t1 emptyEnv

lookupTy :: TyCtx -> Name -> Res Ty
lookupTy ctx n = do
    entry <- lookup ctx n
    case entry of
        Decl ty -> return ty
        Def ty _ -> return ty

-- Convert a typing context into an Env of Val.
-- Used when calling `eval` in `infer`
toEnv :: TyCtx -> Env Val
toEnv (Env []) = Env []
toEnv (Env ((n, e) : xs)) = extend rest n v
  where
    rest = toEnv (Env xs)
    v = case e of
        Decl ty -> VNeutral ty (NVar n)
        Def _ val -> val

-- isXXXs below are a set of helper functions used in type checking
-- In the tutorial, these functions require TyCtx mostly for debugging.
-- We will keep the functions simple for the moment (instead of requiring TyCtx).
isPi :: Ty -> Res (Ty, Closure)
isPi (VPi tyA cls) = Right (tyA, cls)
isPi ty = Left $ errMsgTyCk "expect a Pi type, but got" ty

isSigma :: Ty -> Res (Ty, Closure)
isSigma (VSigma tyA cls) = Right (tyA, cls)
isSigma ty = Left $ errMsgTyCk "expect a Sigma type, but got" ty

isNat :: Ty -> Res ()
isNat VNat = Right ()
isNat ty = Left $ errMsgTyCk "expect a Nat type, but got" ty

isEq :: Ty -> Res (Ty, Val, Val)
isEq (VEqual ty t1 t2) = Right (ty, t1, t2)
isEq ty = Left $ errMsgTyCk "expect an Equal type, but got" ty

isAbsurd :: Ty -> Res ()
isAbsurd VAbsurd = Right ()
isAbsurd ty = Left $ errMsgTyCk "expect an Absurd type, but got" ty

infMsg :: Int -> String
infMsg n = replicate n ' ' ++ "[Infer]: "
ckMsg :: Int -> String
ckMsg n = replicate n ' ' ++ "[Check]: "

infer :: Int -> TyCtx -> Term -> Res Ty
infer i ctx t@(Var n) = do
    traceM (infMsg i ++ "lookup `" ++ show t ++ "` under: " ++ show ctx)
    lookupTy ctx n
infer i ctx t@(Pi n tyA tyB) = do
    traceM (infMsg i ++ show t)
    check (i + 2) ctx tyA VUniverse
    tyA' <- eval (toEnv ctx) tyA
    check (i + 2) (extend ctx n (Decl tyA')) tyB VUniverse
    Right VUniverse
infer i ctx t@(App f a) = do
    traceM (infMsg i ++ show t)
    fTy <- infer (i + 2) ctx f
    (tyA, cls) <- isPi fTy
    check (i + 2) ctx a tyA
    aVal <- eval (toEnv ctx) a
    tyB <- evalCls cls aVal
    Right tyB
infer i ctx t@(Sigma n tyA tyB) = do
    traceM (infMsg i ++ show t)
    check (i + 2) ctx tyA VUniverse
    tyA' <- eval (toEnv ctx) tyA
    check (i + 2) (extend ctx n (Decl tyA')) tyB VUniverse
    Right VUniverse
infer i ctx t@(Fst p) = do
    traceM (infMsg i ++ show t)
    pTy <- infer (i + 2) ctx p
    (tyA, _) <- isSigma pTy
    Right tyA
infer i ctx t@(Snd p) = do
    traceM (infMsg i ++ show t)
    pTy <- infer (i + 2) ctx p
    (_, cls) <- isSigma pTy
    l <- eval (toEnv ctx) (Fst p)
    tyB <- evalCls cls l
    Right tyB
infer i _ Nat = do
    traceM (infMsg i ++ show Nat)
    Right VUniverse
infer i _ Zero = do
    traceM (infMsg i ++ show Zero)
    Right VNat
infer i ctx t@(Succ n) = do
    traceM (infMsg i ++ show t)
    ty <- infer (i + 2) ctx n
    isNat ty
    Right VNat
infer i ctx t@(IndNat prop base ind nat) = do
    traceM (infMsg i ++ show t)
    -- nat => Nat
    natTy <- infer (i + 2) ctx nat
    isNat natTy
    -- prop <= Pi x : Nat. U
    propTy <- eval emptyEnv (Pi (Name "x") Nat Universe)
    check (i + 2) ctx prop propTy
    -- base <= prop 0
    propZ <- eval (toEnv ctx) (App prop Zero)
    check (i + 2) ctx base propZ
    -- ind <= Pi k : Nat . prop k -> prop (k+1)
    propV <- eval (toEnv ctx) prop
    propK <- indStepTy propV
    check (i + 2) ctx ind propK
    -- conclusion: prop nat
    propN <- eval (toEnv ctx) (App prop nat)
    Right propN
infer i ctx t@(Equal ty t1 t2) = do
    traceM (infMsg i ++ show t)
    check (i + 2) ctx ty VUniverse
    tyV <- eval (toEnv ctx) ty
    check (i + 2) ctx t1 tyV
    check (i + 2) ctx t2 tyV
    Right VUniverse
infer i ctx t@(Subst prop propX eq) = do
    traceM (infMsg i ++ show t)
    eqTy <- infer (i + 2) ctx eq
    (tyA, x, y) <- isEq eqTy
    -- A trick for constructing this pi type
    -- since tyA is a value instead of a term, we represent the type as a variable
    -- and provide the actual type value in the env, then let `eval` take over.
    let tyName = Name "ty"
    propTy <- eval (Env [(tyName, tyA)]) (Pi (Name "x") (Var tyName) Universe)
    -- check propX is indeed a proof of (prop x)
    -- (x came from the Equal type)
    --
    -- FIXME: calling `doApp` here is unsatisfying, because I want all doXXXs to be hidden
    -- in the Norm module.
    -- In theory we can still make things work by only calling `eval`,
    -- but that also requires creating dummy variables and extending the env.
    -- No satisfying solution for now :(.
    check (i + 2) ctx prop propTy
    propV <- eval (toEnv ctx) prop
    propXTy <- doApp propV x
    check (i + 2) ctx propX propXTy
    -- constructing the return type, i.e., prop y
    propYTy <- doApp propV y
    Right propYTy
infer i _ UnitTy = do
    traceM (infMsg i ++ show UnitTy)
    Right VUniverse
infer i _ Unit = do
    traceM (infMsg i ++ show Unit)
    Right VUnitTy
infer i _ Absurd = do
    traceM (infMsg i ++ show Absurd)
    Right VUniverse
infer i ctx t@(IndAbsurd ty absurd) = do
    traceM (infMsg i ++ show t)
    absurdTy <- infer (i + 2) ctx absurd
    isAbsurd absurdTy
    check (i + 2) ctx ty VUniverse
    tyV <- eval (toEnv ctx) ty
    Right tyV
infer i _ Atom = do
    traceM (infMsg i ++ show Atom)
    Right VUniverse
infer i _ t@(Quote _) = do
    traceM (infMsg i ++ show t)
    Right VAtom
infer i _ Universe = do
    traceM (infMsg i ++ show Universe)
    Right VUniverse
infer i ctx t'@(As t ty) = do
    traceM (infMsg i ++ show t')
    -- NOTE: this check guarantees that ty is actually a type
    -- otherwise it can be an arbitrary term
    check (i + 2) ctx ty VUniverse
    ty' <- eval (toEnv ctx) ty
    check (i + 2) ctx t ty'
    Right ty'
infer _ _ t = Left $ errMsgTyCk "No inference rule for" t

-- Helper function
-- checking two values are alpha-equivalent under the given type
equiv :: TyCtx -> Ty -> Val -> Val -> Res Bool
equiv ctx ty x y = do
    x' <- reify' ctx ty x
    y' <- reify' ctx ty y
    Right $ alphaEquiv x' y'

check :: Int -> TyCtx -> Term -> Ty -> Res ()
check i ctx t@(Lam name body) ty = do
    traceM (ckMsg i ++ show t ++ " : " ++ show ty)
    (tyA, cls) <- isPi ty
    tyB <- evalCls cls (VNeutral tyA (NVar name))
    check (i + 2) (extend ctx name (Decl tyA)) body tyB
check i ctx t@(MkPair l r) ty = do
    traceM (ckMsg i ++ show t ++ " : " ++ show ty)
    (tyA, cls) <- isSigma ty
    check (i + 2) ctx l tyA
    lV <- eval (toEnv ctx) l
    tyB <- evalCls cls lV
    check (i + 2) ctx r tyB
check i ctx Refl eq = do
    traceM (ckMsg i ++ show Refl ++ " : " ++ show eq)
    (ty, x, y) <- isEq eq
    equal <- equiv ctx ty x y
    if equal
        then Right ()
        else Left $ errMsgTyCk "cannot prove equality by refl because x and y are not alpha-equivalent" (ty, x, y)
-- subsumption
check i ctx t ty1 = do
    traceM (ckMsg i ++ show t ++ " : " ++ show ty1)
    ty2 <- infer (i + 2) ctx t
    equal <- equiv ctx VUniverse ty1 ty2
    if equal
        then Right ()
        else Left $ errMsgTyCk "cannot show equivalence between inferred and checked type on term" (t, ty1, ty2)
