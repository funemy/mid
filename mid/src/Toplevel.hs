module Toplevel (
    Output (..),
    toplevel,
    run,
    runWithDefs,
) where

import Env (Result, emptyEnv, extend, names)
import Err (errMsgTop)
import Lang (
    Ctx,
    CtxEntry (Def),
    Name,
    Term (..),
    Val (VUniverse),
    annotated,
 )
import Norm (eval, reify, runEval, runReify)
import TyCheck (infer, runTyCk, toEnv)

-- | Two kinds of elements at toplevel
-- 1. Definition: a term bound with a name, moreover, the term must be annotated (check using `isDefinition`)
-- 2. Program: a term need evaluating
data Toplevel
    = Definition Name Term
    | Program Term
    deriving (Show)

-- The way we evaluate a term is the same as our normalization process i.e., NbE.
-- Therefore the output should be a Term, and we can reuse our pretty-printting
-- defined for terms.
data Output
    = Output Term
    | Void

instance Show Output where
    show (Output t) = "Output: " ++ show t
    show Void = "<void>"

valid :: Toplevel -> Bool
valid (Definition _ t) = annotated t
valid (Program _) = True

toplevel :: Ctx -> Toplevel -> Result (Ctx, Output)
toplevel ctx top
    | valid top = case top of
        Definition name t -> do
            ty <- runTyCk (infer t) ctx
            v <- runEval (eval t) (toEnv ctx)
            let ctx' = extend name (Def ty v) ctx
            Right (ctx', Void)
        Program t -> do
            ty <- runTyCk (infer t) ctx
            v <- runEval (eval t) (toEnv ctx)
            ty' <- runReify (reify VUniverse ty) (names ctx)
            v' <- runReify (reify ty v) (names ctx)
            Right (ctx, Output (As v' ty'))
    | otherwise = Left $ errMsgTop "toplevel definition must have type annotation" top

run :: Term -> Result Output
run t = do
    (_, out) <- toplevel emptyEnv (Program t)
    return out

runWithDefs :: [(Name, Term)] -> [Term] -> Result [Output]
runWithDefs ds ps = do
    let defs = map (uncurry Definition) ds
        programs = map Program ps
        tops = defs ++ programs
    (_, outs) <- go emptyEnv [] tops
    return outs
  where
    go :: Ctx -> [Output] -> [Toplevel] -> Result (Ctx, [Output])
    go ctx outs [] = return (ctx, outs)
    go ctx outs (x : xs) = do
        (ctx', out) <- toplevel ctx x
        go ctx' (out : outs) xs
