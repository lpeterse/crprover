module Main where

import System.Exit
import System.Console.Readline
import Codec.Binary.UTF8.String 

import Datatypes
import Parser
import Demo
import License
import Manual
import SequenceCalculus
import Prover

--einige String-Formatierungsfunktionen
putUtf8Ln   = putStrLn . encodeString
underline x = x ++ '\n':( map (const '-') x)

-- Userinterface und Hauptschleife
main = (putUtf8Ln manual) >> readEvalPrintLoop []

readEvalPrintLoop :: [Proof] -> IO ()
readEvalPrintLoop ps = do
  maybeLine <- readline ">> "
  case maybeLine of 
       Nothing     -> exitWith (ExitSuccess) -- EOF / control-d
       Just "exit" -> exitWith (ExitSuccess) 
       Just "clear"-> (addHistory "clear")>> readEvalPrintLoop []
       Just "ls"   -> (addHistory "ls")   >> (putStr $ unlines $ map (encodeString.show) $ map fromProof ps) >> (readEvalPrintLoop ps)
       Just "demo" -> (addHistory "demo") >> (sequence $ map (uncurry prove'n'print) examples) >> (readEvalPrintLoop ps)
       Just "help" -> (addHistory "help") >> (putUtf8Ln manual) >> (readEvalPrintLoop ps)
       Just "license" -> (addHistory "license") >> (putUtf8Ln license) >> (readEvalPrintLoop ps)
       Just line -> do addHistory line
                       case line of
                        'A':' ':line' -> case parse (decodeString line') of
                                           Left err -> do{ putStr "parse error at "; print err}
                                           Right x  -> readEvalPrintLoop (ps `union` [A x])
                        _             -> case parse (decodeString line) of
                                           Left err -> do{ putStr "parse error at "; print err}
                                           Right x  -> catch (prove'n'print x ps) (const $ readEvalPrintLoop ps) 
                       readEvalPrintLoop ps

prove'n'print     :: Proposition -> Assumptions -> IO ()
prove'n'print p as = do putUtf8Ln $ underline ("Beweis von "++(init $ tail $ show (map fromProof as))++" ⊦ "++(show p)++":")
                        case prove p as of
                          Nothing -> putUtf8Ln "Nicht beweisbar."
                          Just q  -> putUtf8Ln $ unlines $ map show $ proofToSequence q

