{-# LANGUAGE FlexibleContexts, LambdaCase #-}

module Scheme.Eval where

import Scheme.Core

import Prelude hiding (lookup)
import qualified Data.HashMap.Strict as H (HashMap, insert, lookup, empty, fromList, union)
import Control.Monad.State
import Control.Monad.Except

-- ### Evaluation helpers

-- Evaluates a symbol to string
-- Throws an error if value is not a symbol
-- Examples:
--   getSym (Symbol "x")  ==> "x"
--   getSym (Number 1)    ==> Not a symbol: x
getSym :: Val -> EvalState String
getSym (Symbol x) = return x
getSym         v  = throwError $ NotASymbol v

-- `let` and `let*`
getBinding :: Val -> EvalState (String, Val)
getBinding (Pair c (Pair e Nil)) = liftM2 (,) (getSym c) (eval e)
getBinding v = throwError $ NotAListOfTwo v

-- Evaluates a list of two to a tuple
-- Throws an error if value is not a list of two
-- This is useful in special form `cond`, since each clause
-- is expected to be exactly a two-element list
getListOf2 :: Val -> EvalState (Val, Val)
getListOf2 (Pair c (Pair e Nil)) = return (c, e)
getListOf2 v = throwError $ NotAListOfTwo v

-- Evaluates a value representing a list into an actual list
getList :: Val -> EvalState [Val]
getList Nil = return []
getList (Pair v1 v2) =
  do xs <- getList v2
     return (v1 : xs)
getList e = throwError $ InvalidSpecialForm "special" e

--- ### Keywords

-- When evaluating special forms, a list form starting with a keyword
-- is expected to match the special form syntax.
keywords :: [String]
keywords = [ "define"
           , "lambda"
           , "cond"
           , "let"
           , "let*"
           , "define-macro"
           , "quasiquote"
           , "unquote"
           ]

-- ### The monadic evaluator
-- Unlike evaluators in previous MPs, `eval` does not take any environment!
-- This is because the environment is encapsulated in the `EvalState` monad.
-- To access the environment, all you have to do is `get`, `modify` or `put`!
eval :: Val -> EvalState Val

-- Self-evaluating expressions
-- TODO: What's self-evaluating?
eval v@(Number _) = return v --"Evaluating numbers"
eval v@(Boolean _) = return v --"Evaluating booleans"

-- Symbol evaluates to the value bound to it
-- TODO
eval (Symbol sym) = do  env <- get
                        case H.lookup sym env of
                          Just val -> return val
                          Nothing -> throwError $ UndefSymbolError sym --"Evaluating symbols"

-- Function closure is also self-evaluating
eval v@(Func {}) = return v

-- We check to see if the pair is a "proper list". If it is,
-- then we try to evaluate it, as one of the following forms:
-- 1. Special form (`define`, `let`, `let*`, `cond`, `quote`, `quasiquote`,
--    `unquote`, `define-macro`, ...)
-- 2. Macro expansion (Macro)
-- 3. Function application (Func)
-- 4. Primitive function application (PrimFunc)
eval expr@(Pair v1 v2) = case flattenList expr of
  Left _ -> throwError $ InvalidExpression expr
  Right lst -> evalList lst where
    --- Evaluator for forms
    invalidSpecialForm :: String -> EvalState e
    invalidSpecialForm frm = throwError $ InvalidSpecialForm frm expr

    evalList :: [Val] -> EvalState Val

    evalList [] = throwError $ InvalidExpression expr

    -- quote
    -- TODO
    evalList [Symbol "quote", e] = return e --"Special form `quote`"

    -- unquote (illegal at surface evaluation)
    -- TODO: since surface-level `unquote` is illegal, all you need to do is
    -- to throw a diagnostic
    evalList [Symbol "unquote", e] = throwError $ UnquoteNotInQuasiquote e --"Special form `unquote`"

    -- quasiquote
    evalList [Symbol "quasiquote", e] = evalQuasi 1 e where
      evalQuasi :: Int -> Val -> EvalState Val
      evalQuasi 0 (Pair (Symbol "unquote") v) = throwError $ UnquoteNotInQuasiquote v
      evalQuasi 1 (Pair (Symbol "unquote") (Pair v Nil)) = eval v
      evalQuasi n (Pair (Symbol "quasiquote") (Pair v Nil)) =
        do v' <- evalQuasi (n+1) v
           return $ Pair (Symbol "quasiquote") (Pair v' Nil)
      evalQuasi n (Pair (Symbol "unquote") (Pair v Nil)) =
        do v' <- evalQuasi (n-1) v
           return $ Pair (Symbol "unquote") (Pair v' Nil)
      evalQuasi n (Pair x y) = Pair <$> evalQuasi n x <*> evalQuasi n y
      evalQuasi _ v = return v

    -- cond
    -- TODO: Handle `cond` here. Use pattern matching to match the syntax
    {-evalList ((Symbol "cond"):rest0) = evalcond rest0 where
      evalcond [] = invalidSpecialForm "cond"
      evalcond (ce:rest1) = do (c1,e1) <- getListOf2 ce
                               case c1 of 
                                Symbol "else" -> if length rest1 == 0
                                                 then eval e1
                                                 else invalidSpecialForm "cond"
                                _ -> do c1val <- eval c1
                                        case c1val of
                                          Boolean False -> if length rest1 == 0
                                                           then return Void
                                                           else evalcond rest1
                                          _ -> eval e1-}
    {-
    evalList ((Symbol "cond"):xs) = aux xs
                                      where 
                                        aux [] = invalidSpecialForm "cond"
                                        aux (y:ys) = do (c, e) <- getListOf2 y
                                                      case c of 
                                                        Symbol "else" -> if (length ys == 0) then (eval e) else (invalidSpecialForm "cond")
                                                        _ -> do ceval <- eval c
                                                              case ceval of 
                                                                Boolean False -> if (length ys == 0) then (return Void) else aux ys
                                                                _ -> eval e 

    evalList ((Symbol "cond"):xs) = aux xs where
      aux [] = invalidSpecialForm "cond"
      aux (y:ys) = do (c, e) <- getListOf2 y
                      case c of
                        Symbol "else" -> if length ys == 0 then eval e else invalidSpecialForm "cond"
                        _ -> do ceval <- eval c
                                case ceval of
                                  Boolean False -> if length ys == 0 then return Void else aux ys
                                  _ -> eval e
    

    evalList ((Symbol "cond"):pairs) = case pairs of [] -> invalidSpecialForm "cond"
                                                     _ -> mapM getListOf2 pairs >>= evalCond 
                                                                  where evalCond [] = return Void
                                                                        evalCond [(Symbol "else",e)] = eval e
                                                                        evalCond ((Symbol "else",_):_) = invalidSpecialForm "cond"
                                                                        evalCond ((c,e):ces) = eval c >>= \cond-> case cond of Boolean False -> evalCond ces
                                                                                                                               _ -> eval e 
    

    -}
    evalList ((Symbol "cond"):xs) = aux xs where
      aux [] = invalidSpecialForm "cond"
      aux (y:ys) = do (c, e) <- getListOf2 y
                      case c of
                        Symbol "else" -> if length ys == 0 then eval e else invalidSpecialForm "cond"
                        _ -> do ceval <- eval c
                                case ceval of
                                  Boolean False -> if length ys == 0 then return Void else aux ys
                                  _ -> eval e

    -- let
    -- TODO: Handle `let` here. Use pattern matching to match the syntax
    evalList [Symbol "let", args, body] =
      do env <- get
         argsList <- getList args
         x <- mapM getBinding argsList
         mapM_ (\(k,v) -> modify $ H.insert k v) x
         val <- eval body
         put env
         return val


    -- lambda
    -- TODO: Handle `lambda` here. Use pattern matching to match the syntax
    evalList [Symbol "lambda", args, body] =
      do env <- get
         argsList <- getList args
         val <- (\argVal -> Func argVal body env) <$> mapM getSym argsList
         return val

    -- define function
    evalList [Symbol "define", Pair (Symbol fname) args, body] =
      do env <- get
         argList <- getList args
         val <- (\argVal -> Func argVal body env) <$> mapM getSym argList
         modify $ H.insert fname val
         return Void

    -- define variable
    -- TODO: Handle `define` for variables here. Use pattern matching
    -- to match the syntax
    evalList [Symbol "define", Symbol var, body] = 
        do val <- eval body 
           modify $ H.insert var val
           return Void

    -- define-macro
    -- TODO: Handle `define-macro` here. Use pattern matching to match
    -- the syntax
    evalList [Symbol "define-macro", Pair (Symbol fname) args, body] =
      do argList <- getList args
         symb <- mapM getSym argList
         modify $ H.insert fname (Macro symb body) 
         return Void

    -- invalid use of keyword, throw a diagnostic
    evalList (Symbol sym : _) | elem sym keywords = invalidSpecialForm sym

    -- application
    evalList (fexpr:args) =
      do f <- eval fexpr
         apply f args

eval val = throwError $ InvalidExpression val

-- Function application
apply :: Val -> [Val] -> EvalState Val
  -- Function
    -- TODO: implement function application
    -- Use do-notation!
apply (Func fmls body cenv) args | length fmls == length args =
  do env <- get 
     var <- mapM eval args 
     modify (H.union cenv)
     mapM_ (\(k,v) -> modify $ H.insert k v) (zip fmls var)
     val <- eval body
     put env
     return val

  -- Macro
    -- TODO: implement macro evaluation
    -- Use do-notation!
apply (Macro fmls body) args | length fmls == length args =
  do env <- get 
     mapM_ (\(k,v) -> modify $ H.insert k v) (zip fmls args)
     val <- eval body
     put env
     eval val

  -- Primitive
apply (PrimFunc p) args =
  do argVals <- mapM eval args
     p argVals
  -- Other values are not applicable
apply f args = throwError $ CannotApply f args
