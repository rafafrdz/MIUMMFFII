{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_lh_tests (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [0,1,0,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/lh-va/.stack-work/install/x86_64-linux/db78b532957de866642e86e46f209ef518467f94780315dec09eae695a4a06b2/8.10.7/bin"
libdir     = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/lh-va/.stack-work/install/x86_64-linux/db78b532957de866642e86e46f209ef518467f94780315dec09eae695a4a06b2/8.10.7/lib/x86_64-linux-ghc-8.10.7/lh-tests-0.1.0.0-Fv6mvBcmAhP1j0JtptvHDe-lh-tests-exe"
dynlibdir  = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/lh-va/.stack-work/install/x86_64-linux/db78b532957de866642e86e46f209ef518467f94780315dec09eae695a4a06b2/8.10.7/lib/x86_64-linux-ghc-8.10.7"
datadir    = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/lh-va/.stack-work/install/x86_64-linux/db78b532957de866642e86e46f209ef518467f94780315dec09eae695a4a06b2/8.10.7/share/x86_64-linux-ghc-8.10.7/lh-tests-0.1.0.0"
libexecdir = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/lh-va/.stack-work/install/x86_64-linux/db78b532957de866642e86e46f209ef518467f94780315dec09eae695a4a06b2/8.10.7/libexec/x86_64-linux-ghc-8.10.7/lh-tests-0.1.0.0"
sysconfdir = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/lh-va/.stack-work/install/x86_64-linux/db78b532957de866642e86e46f209ef518467f94780315dec09eae695a4a06b2/8.10.7/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "lh_tests_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "lh_tests_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "lh_tests_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "lh_tests_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "lh_tests_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "lh_tests_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
