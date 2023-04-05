module Toplevel (
    toplevel,
) where

import Env (Res, extend)
import Err (errMsgTop)
import Lang (Name, Term (..), TyCtx, TyCtxEntry (Def), Val (VUniverse), annotated)
import Norm (eval, reify')
import TyCheck (infer, toEnv)

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

valid :: Toplevel -> Bool
valid (Definition _ t) = annotated t
valid (Program _) = True

toplevel :: TyCtx -> Toplevel -> Res (TyCtx, Output)
toplevel ctx top
    | valid top = case top of
        Definition name t -> do
            ty <- infer ctx t
            v <- eval (toEnv ctx) t
            let ctx' = extend ctx name (Def ty v)
            Right (ctx', Void)
        Program t -> do
            ty <- infer ctx t
            v <- eval (toEnv ctx) t
            ty' <- reify' ctx VUniverse ty
            v' <- reify' ctx ty v
            Right (ctx, Output (As v' ty'))
    | otherwise = Left $ errMsgTop "toplevel definition must have type annotation" top
