
-- |
-- Module      :  GHCi.InteractiveTactic
-- Copyright   :  (c) Reed Mullanix 2019
-- License     :  BSD-style
-- Maintainer  :  reedmullanix@gmail.com
--
{-# LANGUAGE PartialTypeSignatures #-}
module GHCi.InteractiveTactic
( hscTactic
) where

import Data.Data

import Control.Exception
import Control.Monad
import Control.Monad.IO.Class

import Bag
import DynFlags
import Lexer
import FastString
import Outputable
import ErrUtils
import IOEnv
import HscMain
import HsDumpAst
import HscTypes
import GHC
import Parser
import TcRnDriver
import TcHsType
import RnUtils
import StringBuffer
import SrcLoc

import Language.Haskell.Tactic.Patterns
import Language.Haskell.Tactic
-- --------------------------------------------------------------------
-- Error handling, stolen from internals of HscMain
throwErrors :: ErrorMessages -> Hsc a
throwErrors = liftIO . throwIO . mkSrcErr

handleWarnings :: Hsc ()
handleWarnings = do
    dflags <- getDynFlags
    w <- getWarnings
    liftIO $ printOrThrowWarnings dflags w
    clearWarnings

getWarnings :: Hsc WarningMessages
getWarnings = Hsc $ \_ w -> return (w, w)

clearWarnings :: Hsc ()
clearWarnings = Hsc $ \_ _ -> return ((), emptyBag)

logWarnings :: WarningMessages -> Hsc ()
logWarnings w = Hsc $ \_ w0 -> return ((), w0 `unionBags` w)

logWarningsReportErrors :: Messages -> Hsc ()
logWarningsReportErrors (warns,errs) = do
    logWarnings warns
    when (not $ isEmptyBag errs) $ throwErrors errs


-- --------------------------------------------------------------------
hscParseType :: String -> Hsc (LHsType GhcPs)
hscParseType str = do
  dflags <- getDynFlags
  let buf = stringToStringBuffer str
      loc = mkRealSrcLoc (fsLit "<interactive>") 1 1
  case unP parseType (mkPState dflags buf loc) of
    PFailed warnFn span err -> do
      logWarningsReportErrors (warnFn dflags)
      handleWarnings
      let msg = mkPlainErrMsg dflags span err
      throwErrors $ unitBag msg
    POk pst ty -> do
      logWarningsReportErrors (getMessages pst dflags)
      liftIO $ dumpIfSet_dyn dflags Opt_D_dump_parsed "Parsed" (ppr ty)
      liftIO $ dumpIfSet_dyn dflags Opt_D_dump_parsed "Parser AST" $ showAstData NoBlankSrcSpan ty
      return $ ty

hscTactic :: HscEnv -> String -> IO (Maybe Expr)
hscTactic hsc_env0 str = runInteractiveHsc hsc_env0 $ do
  hsc_env <- getHscEnv
  psTy <- hscParseType str
  (ty, _kind) <- ioMsgMaybe $ tcRnType hsc_env True psTy
  (msgs, ext) <- ioMsgMaybe $ runTcInteractive hsc_env $ runTactic ty (auto 5)
  logWarningsReportErrors msgs
  return ext
-- hscParseThingWithLocation :: (Outputable thing, Data thing) => String -> Int
--                           -> Lexer.P thing -> String -> Hsc thing
-- hscParseThingWithLocation source linenumber parser str
--   = withTiming getDynFlags
--                (text "Parser [source]")
--                (const ()) $ {-# SCC "Parser" #-} do
--     dflags <- getDynFlags

--     let buf = stringToStringBuffer str
--         loc = mkRealSrcLoc (fsLit source) linenumber 1

--     case unP parser (mkPState dflags buf loc) of
--         PFailed warnFn span err -> do
--             logWarningsReportErrors (warnFn dflags)
--             handleWarnings
--             let msg = mkPlainErrMsg dflags span err
--             throwErrors $ unitBag msg

--         POk pst thing -> do
--             logWarningsReportErrors (getMessages pst dflags)
--             liftIO $ dumpIfSet_dyn dflags Opt_D_dump_parsed "Parser" (ppr thing)
--             liftIO $ dumpIfSet_dyn dflags Opt_D_dump_parsed_ast "Parser AST" $
--                                    showAstData NoBlankSrcSpan thing
--             return thing

-- tacticInteractive :: (GhcMonad m) => String -> m String
-- tacticInteractive str = withSession $ \hsc_env -> do
--   ty <- hscParseTh str
--   _h