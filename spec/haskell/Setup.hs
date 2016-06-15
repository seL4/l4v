module Main where

import Distribution.Simple
import Distribution.Simple.Setup
import Distribution.PackageDescription
import Distribution.PackageDescription.Parse
import Distribution.Verbosity
import Control.Monad
import Data.List
import System.Environment(getArgs)
import Control.Applicative

main :: IO ()
main = do
    args <- getArgs
    let targetPrefix = "--configure-option="
    let targetArg = find (targetPrefix `isPrefixOf`) args
    let targetName = fmap (drop (length targetPrefix)) targetArg
    let hooks = autoconfUserHooks {
        readDesc = readDescHook targetName
    }
    defaultMainWithHooksArgs hooks args


buildLibQEmu :: Args -> BuildFlags -> IO HookedBuildInfo
buildLibQEmu args flags = do
    putStrLn "Building haskell sel4 ..."
    preBuild autoconfUserHooks args flags

printKnownTargets :: IO ()
printKnownTargets = do
    putStrLn "Recognised targets are:"
    mapM_ (putStrLn.('\t':).fst) targets

targets =
    [ ("arm-exynos",    ("ARM", "Exynos4210"))
    , ("arm-kzm",       ("ARM", "KZM"))
    , ("arm-sabre",     ("ARM", "Sabre"))
    , ("x64-pc99",      ("X64", "PC99"))
    , ("arm-tk1",       ("ARM_HYP", "TK1"))
    ]

getPlatform :: Maybe String -> IO (Maybe (String, String))
getPlatform targetName =
      return $ do
        targetName <- targetName
        (_, target) <- find ((==targetName).fst) targets
        return target

readDescHook :: Maybe String -> IO (Maybe GenericPackageDescription)
readDescHook targetName = do
    platform <- getPlatform targetName
    (arch, plat) <- case platform of
       Just p -> return p
       Nothing -> do
         putStrLn "Please specify a target: --configure-option=\"<target>\""
         printKnownTargets
         fail "No target"
    dscp <- readPackageDescription normal "SEL4.cabal"
    let pkg_lib = condLibrary dscp
    pkg_lib_upd <- case pkg_lib of
      Just CondNode {condTreeData = lib,condTreeConstraints = cons,condTreeComponents=comp} -> do
        bi_upd <- do
          let bi = libBuildInfo lib
          let opts = cppOptions bi ++ ["-DPLATFORM=" ++ plat] ++ ["-DTARGET=" ++ arch]
                                           ++ ["-DPLATFORM_" ++ plat] ++ ["-DTARGET_" ++ arch]
          return $ bi { cppOptions = opts }
        return $ Just CondNode {condTreeData = lib { libBuildInfo = bi_upd},
                 condTreeConstraints = cons, condTreeComponents = comp}
      Nothing -> return Nothing
    let dscp_upd = dscp { condLibrary = pkg_lib_upd}
    print dscp_upd
    return $ Just dscp_upd

