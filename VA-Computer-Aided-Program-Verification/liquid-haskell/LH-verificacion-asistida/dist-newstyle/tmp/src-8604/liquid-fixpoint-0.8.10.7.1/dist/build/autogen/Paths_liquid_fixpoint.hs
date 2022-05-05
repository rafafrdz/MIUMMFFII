{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
{-# OPTIONS_GHC -w #-}
module Paths_liquid_fixpoint (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where


import qualified Control.Exception as Exception
import qualified Data.List as List
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
version = Version [0,8,10,7,1] []

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir `joinFileName` name)

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath



bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath
bindir     = "/home/rafafrdz/.cabal/store/ghc-8.10.7/liquid-fixpoint-0.8.10.7.1-6b94d727eb8324c50711633ab17e4b8a18796050f54552db8ac5226b13bb6b0c/bin"
libdir     = "/home/rafafrdz/.cabal/store/ghc-8.10.7/liquid-fixpoint-0.8.10.7.1-6b94d727eb8324c50711633ab17e4b8a18796050f54552db8ac5226b13bb6b0c/lib"
dynlibdir  = "/home/rafafrdz/.cabal/store/ghc-8.10.7/liquid-fixpoint-0.8.10.7.1-6b94d727eb8324c50711633ab17e4b8a18796050f54552db8ac5226b13bb6b0c/lib"
datadir    = "/home/rafafrdz/.cabal/store/ghc-8.10.7/liquid-fixpoint-0.8.10.7.1-6b94d727eb8324c50711633ab17e4b8a18796050f54552db8ac5226b13bb6b0c/share"
libexecdir = "/home/rafafrdz/.cabal/store/ghc-8.10.7/liquid-fixpoint-0.8.10.7.1-6b94d727eb8324c50711633ab17e4b8a18796050f54552db8ac5226b13bb6b0c/libexec"
sysconfdir = "/home/rafafrdz/.cabal/store/ghc-8.10.7/liquid-fixpoint-0.8.10.7.1-6b94d727eb8324c50711633ab17e4b8a18796050f54552db8ac5226b13bb6b0c/etc"

getBinDir     = catchIO (getEnv "liquid_fixpoint_bindir")     (\_ -> return bindir)
getLibDir     = catchIO (getEnv "liquid_fixpoint_libdir")     (\_ -> return libdir)
getDynLibDir  = catchIO (getEnv "liquid_fixpoint_dynlibdir")  (\_ -> return dynlibdir)
getDataDir    = catchIO (getEnv "liquid_fixpoint_datadir")    (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "liquid_fixpoint_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "liquid_fixpoint_sysconfdir") (\_ -> return sysconfdir)




joinFileName :: String -> String -> FilePath
joinFileName ""  fname = fname
joinFileName "." fname = fname
joinFileName dir ""    = dir
joinFileName dir fname
  | isPathSeparator (List.last dir) = dir ++ fname
  | otherwise                       = dir ++ pathSeparator : fname

pathSeparator :: Char
pathSeparator = '/'

isPathSeparator :: Char -> Bool
isPathSeparator c = c == '/'
