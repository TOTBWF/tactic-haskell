{-# LANGUAGE RecordWildCards, LambdaCase #-}
module GHCi.Leak
  ( LeakIndicators
  , getLeakIndicators
  , checkLeakIndicators
  ) where

import Control.Monad
import GHC
import Outputable
import HscTypes
import UniqDFM
import System.Mem
import System.Mem.Weak

-- Checking for space leaks in GHCi. See #15111, and the
-- -fghci-leak-check flag.

data LeakIndicators = LeakIndicators [LeakModIndicators]

data LeakModIndicators = LeakModIndicators
  { leakMod :: Weak HomeModInfo
  , leakIface :: Weak ModIface
  , leakDetails :: Weak ModDetails
  , leakLinkable :: Maybe (Weak Linkable)
  }

-- | Grab weak references to some of the data structures representing
-- the currently loaded modules.
getLeakIndicators :: HscEnv -> IO LeakIndicators
getLeakIndicators HscEnv{..} =
  fmap LeakIndicators $
    forM (eltsUDFM hsc_HPT) $ \hmi@HomeModInfo{..} -> do
      leakMod <- mkWeakPtr hmi Nothing
      leakIface <- mkWeakPtr hm_iface Nothing
      leakDetails <- mkWeakPtr hm_details Nothing
      leakLinkable <- mapM (`mkWeakPtr` Nothing) hm_linkable
      return $ LeakModIndicators{..}

-- | Look at the LeakIndicators collected by an earlier call to
-- `getLeakIndicators`, and print messasges if any of them are still
-- alive.
checkLeakIndicators :: DynFlags -> LeakIndicators -> IO ()
checkLeakIndicators dflags (LeakIndicators leakmods)  = do
  performGC
  forM_ leakmods $ \LeakModIndicators{..} -> do
    deRefWeak leakMod >>= \case
      Nothing -> return ()
      Just hmi ->
        report ("HomeModInfo for " ++
          showSDoc dflags (ppr (mi_module (hm_iface hmi)))) (Just hmi)
    deRefWeak leakIface >>= report "ModIface"
    deRefWeak leakDetails >>= report "ModDetails"
    forM_ leakLinkable $ \l -> deRefWeak l >>= report "Linkable"
 where
  report :: String -> Maybe a -> IO ()
  report _ Nothing = return ()
  report msg (Just _) =
    putStrLn ("-fghci-leak-check: " ++ msg ++ " is still alive!")
