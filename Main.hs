module Main where

import Control.Monad.Trans
import Control.Monad.Trans.Reader
import Data.List
import System.Environment
import System.Console.Haskeline

import Exp.Lex
import Exp.Par
import Exp.Skel
import Exp.Print
import Exp.Abs
import Exp.Layout
import Exp.ErrM
import AbsToInternal
import Concrete
import qualified MTT as A
import Eval

type Interpreter = InputT IO

defaultPrompt :: String
defaultPrompt = "> "

lexer :: String -> [Token]
lexer = resolveLayout True . myLexer

showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
  putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

unModule :: Module -> [Def]
unModule (Module defs) = defs

parseFiles :: [FilePath] -> IO [Def]
parseFiles [] = return []
parseFiles (f:fs) = do
  s <- readFile f
  let ts = lexer s
  case pModule ts of
    Bad s  -> do
      putStrLn $ "Parse Failed in file " ++ show f ++ "\n"
      putStrLn $ "Tokens: " ++ show ts
      putStrLn s
      return []
    Ok mod -> do
      putStrLn $ "Parsed file " ++ show f ++ " successfully!"
      showTree mod
      defs <- parseFiles fs
      return $ unModule mod ++ defs

main :: IO ()
main = getArgs >>= runInputT defaultSettings . runInterpreter

getImports :: [Def] -> [String]
getImports defs = [ n ++ ".cub" | DefImport (ImportIdent n) <- defs ]

--  names to import -> files already imported -> all definitions
imports :: [String] -> [FilePath] -> [Def] -> Interpreter [Def]
imports [] _  defs = return defs
imports xs fs defs = do
  newDefs <- lift $ parseFiles xs
  let imps = getImports newDefs
  imports (nub imps \\ fs) (fs ++ xs) (defs ++ newDefs)
  
runInterpreter :: [FilePath] -> Interpreter ()
runInterpreter fs = do
  -- parse and type-check files
  defs <- imports fs [] []
  let cg = callGraph defs
  let ns = defsToNames $ concat $ concat cg
  let res = runResolver (handleMutuals cg)
  case res of
    Left err -> outputStrLn $ "Resolver failed: " ++ err
    Right re -> let term = handleLet A.Top re in
      case A.checkExp term of
        Left err -> outputStrLn $ "Type checking failed: " ++ err
        Right () -> do
          outputStrLn $ "Files loaded."
          loop ns re
  where
    -- TODO: All the concrete to abstract to internal should be more
    -- modular so that we don't have to repeat the translations.
    loop :: [String] -> [[([String],A.Exp,A.Exp)]] -> InputT IO ()
    loop ns re = do
      input <- getInputLine defaultPrompt
      case input of
        Nothing    -> outputStrLn help >> loop ns re
        Just ":q"  -> return ()
        Just ":r"  -> runInterpreter fs
        Just ":h"  -> outputStrLn help >> loop ns re
        Just str   -> let ts = lexer str in
          case pExp ts of
            Bad err -> outputStrLn ("Parse error: " ++ err) >> loop ns re
            Ok exp  ->
              case runResolver (local (insertNames ns) $ resolveExp exp) of
                Left err   -> outputStrLn ("Resolver failed: " ++ err) >> loop ns re
                Right body -> let term = handleLet body re in
                  case A.checkExpInfer term of
                    Left err -> outputStrLn ("Could not type-check: " ++ err) >> loop ns re
                    Right _  -> case translate term of
                      Left err -> outputStrLn ("Could not translate to internal syntax: " ++ err) >>
                                  loop ns re
                      Right t  -> let value = eval [] Empty t in
                        outputStrLn ("EVAL: " ++ show value) >> loop ns re

help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :q              quit\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"
