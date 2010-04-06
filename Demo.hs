module Demo (examples) where

import Datatypes

examples :: [(Proposition, Assumptions)]
examples  = [
             (If (Const "p") (Const "p"),    []), 
             --     Teste Reductio Ad Absurdum
             (Neg (Const "p"),               [A (If (Const "p") (Neg (Const "q"))), A (Const "q")]), 
             --     Teste OrElimination
             (Const "p",                     [A (Neg (Const "q")), A (Or (Const "p") (Const "q"))]),
             (Const "p",                     [A (Neg (Const "q")), A (Or (Const "q") (Const "p"))]),
             (Const "q",                     [A (Neg (Neg (Neg (Const "p")))), A (Or (Const "q") (Const "p"))]),
             --     Teste AndIntroduction
             (And (Const "p") (Const "q"),   [A (Const "p"), A (Const "q")]),
             --     Teste AndElimination
             (Const "p",                     [A (And (Const "p") (Const "q"))]),
             (Const "q",                     [A (And (Const "p") (Const "q"))]),
             (Const "q",                     [A (And (And (Const "q") (Const "p")) (Const "r"))]),
             --     Kompliziertere Sätze aus dem Skript von Achim Stephan und Sven Walter
             (If (Or (Const "r") (Neg (Const "q"))) (If (Const "p") (Const "r")), [A (If (Const "p") (Const "q"))]),
--             (And (And (Const "r1") (Const "r")) (Neg (Const "p1")),              [A (If (Neg (Const "p")) (And (Const "q") (Const "r"))), A (If (Or (Neg (Const "p")) (Const "q1")) (Neg (Const "p1"))), A (And (Const "r1") (Neg (Const "p")))]),
             (If (And (Const "p") (Const "q")) (Const "r"),                       [A (If (Const "p") (If (Const "q") (Const "r")))]),
             (If (If (Const "p") (Const "q")) (If (If (Const "p") (Neg (Const "q"))) (Neg (Const "p"))), [])
            ]




