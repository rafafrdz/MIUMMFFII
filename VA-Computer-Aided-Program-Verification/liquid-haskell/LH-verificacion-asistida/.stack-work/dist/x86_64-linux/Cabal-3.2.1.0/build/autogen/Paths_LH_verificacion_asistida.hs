{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_LH_verificacion_asistida (
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

bindir     = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/LH-verificacion-asistida/.stack-work/install/x86_64-linux/e5aae3bc1014f3badf38af96dc381842a9523cab41ccd6eef6a9bea8e37f57fe/8.10.7/bin"
libdir     = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/LH-verificacion-asistida/.stack-work/install/x86_64-linux/e5aae3bc1014f3badf38af96dc381842a9523cab41ccd6eef6a9bea8e37f57fe/8.10.7/lib/x86_64-linux-ghc-8.10.7/LH-verificacion-asistida-0.1.0.0-5NHMYuhgw29Gnkg9iLcbdC"
dynlibdir  = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/LH-verificacion-asistida/.stack-work/install/x86_64-linux/e5aae3bc1014f3badf38af96dc381842a9523cab41ccd6eef6a9bea8e37f57fe/8.10.7/lib/x86_64-linux-ghc-8.10.7"
datadir    = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/LH-verificacion-asistida/.stack-work/install/x86_64-linux/e5aae3bc1014f3badf38af96dc381842a9523cab41ccd6eef6a9bea8e37f57fe/8.10.7/share/x86_64-linux-ghc-8.10.7/LH-verificacion-asistida-0.1.0.0"
libexecdir = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/LH-verificacion-asistida/.stack-work/install/x86_64-linux/e5aae3bc1014f3badf38af96dc381842a9523cab41ccd6eef6a9bea8e37f57fe/8.10.7/libexec/x86_64-linux-ghc-8.10.7/LH-verificacion-asistida-0.1.0.0"
sysconfdir = "/media/rafafrdz/Data1/git/MetodosFormales/VA-Computer-Aided-Program-Verification/liquid-haskell/LH-verificacion-asistida/.stack-work/install/x86_64-linux/e5aae3bc1014f3badf38af96dc381842a9523cab41ccd6eef6a9bea8e37f57fe/8.10.7/etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "LH_verificacion_asistida_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "LH_verificacion_asistida_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "LH_verificacion_asistida_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "LH_verificacion_asistida_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "LH_verificacion_asistida_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "LH_verificacion_asistida_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "/" ++ name)
