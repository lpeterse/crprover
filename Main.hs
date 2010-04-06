module Main where

import Data.List
import System.Console.Haskeline

import Datatypes
import Parser
import Demo
import License
import Manual
import SequenceCalculus
import Prover

main :: IO ()
main = runInputT defaultSettings (outputStrLn manual >> loop [])
        
loop   :: Assumptions -> InputT IO ()
loop as = do
            minput <- getInputLine ">> "
            case minput of
              Nothing          -> return ()
              Just "quit"      -> return ()
              Just "exit"      -> return ()
              Just "clear"     -> loop [] 
              Just "ls"        -> mapM_ (outputStrLn.show) as >> loop as
              Just "demo"      -> mapM_ (outputStrLn.(uncurry prove')) examples >> loop as
              Just "help"      -> outputStrLn manual  >> loop as
              Just "license"   -> outputStrLn license >> loop as
              Just ('A':' ':l) -> case parse l of
                                    Left err -> outputStrLn "ParseError"  >> loop as 
                                    Right p  -> loop (as `union` [A p])
              Just l           -> case parse l of
                                    Left err -> outputStrLn "ParseError"  >> loop as 
                                    Right p  -> outputStrLn (prove' p as) >> loop as

prove'     :: Proposition -> Assumptions -> String 
prove' p as = underline ("Beweis von "++(init $ tail $ show (map fromProof as))++" ⊦ "++(show p)++":")
              ++ "\n"
              ++ case prove p as of
                   Nothing -> "Nicht beweisbar."
                   Just q  -> unlines $ map show $ proofToSequence q
              where underline x = x ++ '\n':(map (const '-') x)
