module SequenceCalculus (proofToSequence) where

import Data.List
import Datatypes

-- Datentyp, der eine Beweiszeile in Cr-Darstellung repräsentiert.
-- Es gibt eine Menge von Zahlen (soa), die sich auf andere Zeilen beziehen,
-- von denen die aktuelle abhängig ist. Außerdem gibt es einen Zeilenindex und
-- eine Menge von Zahlen (dfl), die angibt, wovon diese Zeile abgeleitet wurde.
data Line = Line { soa :: [Int], index :: Int, proof :: Proof, dfl :: [Int]}
            deriving (Eq)

type Sequence = [Line]

-- Wir nutzen eine eigene, eingängige Darstellung um unsere Zeilen anzuzeigen.
-- Dabei machen wir uns die automatische Dastellung von Listen zu nutze.
instance Show Line where
  show (Line as n p ls) = (fl as' 9)++(fl (show n) 4)++(fl (delbrace (show (fromProof p))) 40)++(fl (lastStep p) 9)++ls'
                         where
                           fl s n | n > length s = s ++ concat (replicate (n-length s) " ")
                                  | otherwise    = s
                           as' = "{" ++ tail (init (show (unique as))) ++ "}"
                           ls' | null ls = ""
                               | otherwise = "(" ++ tail (init (show ls)) ++ ")"
                           unique []     = []
                           unique (x:xs) = x:(unique (filter (/=x) xs))
                           delbrace xs = if (head xs)=='(' && (last xs)==')' then init (tail xs) else xs

-- dient der Ersetzung eines bestimmten Wertes a durch einen anderen b.
replace       :: Eq a => a -> a -> (a -> a)
replace a b    = \x-> if x==a then b else x

-- Bildet Zeile auf Zeile ab, wobei auf alle Zahlen in der Zeile Funktion f angewendet wurde.
mapIntInLine    :: (Int -> Int) -> Line -> Line
mapIntInLine f l = l { soa = (map f (soa l)), index = f (index l), dfl = (map f (dfl l)) }

-- Legt fest, wie die angewendete Regel im Beweis dargestellt werden soll.
lastStep             :: Proof -> String
--lastStep (Unprovable) = ""
lastStep (A _)        = "A"
lastStep (IfInt  _ _) = "⊃-Int" 
lastStep (IfElim _ _) = "⊃-Elim" 
lastStep (IffInt  _ _)= "≣-Int" 
lastStep (IffElim1 _) = "≣-Elim" 
lastStep (IffElim2 _) = "≣-Elim" 
lastStep (AndInt _ _) = "∧-Int" 
lastStep (AndElim1 _) = "∧-Elim" 
lastStep (AndElim2 _) = "∧-Elim" 
lastStep (OrInt1 _ _) = "∨-Int" 
lastStep (OrInt2 _ _) = "∨-Int" 
lastStep (OrElim1 _ _)= "∨-Elim" 
lastStep (OrElim2 _ _)= "∨-Elim" 
lastStep (RAA _ _ _)  = "RAA"

-- bildet einen baumartigen `Proof` auf eine Liste von `Line` ab.
-- Hierbei werden auch gleich noch, Anpassungen der Zahlen vorgenommen
-- und überflüssige Zeilen entfernt.
proofToSequence  :: Proof -> Sequence
proofToSequence   = zipGaps . consolid . lineifyProof 1

-- bildet den Beweis auf Liste von Line ab.
-- n gibt hierbei an, welchen Index die erste Zeile erhalten soll. Dies ist nicht
-- notwendigerweise 1, da Rekursion im Spiel ist.
-- Bei IfInt und RAA, darf im Assumptionset der Zeilenindex einer Zeile weggelasssen werden.
-- Dies war nicht ganz einfach umzusetzen und verunstaltet außerdem die Mengen (siehe `freed`).
lineifyProof                   :: Int -> Proof -> [Line]
--lineifyProof n p@(Unprovable)   = [Line [] n (A (Const "Kein Beweis gefunden.")) []]
lineifyProof n p@(A _)          = [Line [n] n p []]
lineifyProof n p@(IfInt a b)    = as++bs++[Line set (n+las+lbs) p [(n+las+lbs-1), (n+las-1)]] 
                                  where
                                    as  = lineifyProof n       a
                                    bs  = lineifyProof (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last bs)  \\ freed 
                                    freed = map index (filter ((== proof (head as)).proof) bs)
lineifyProof n p@(IfElim a b)   = as++bs++[Line set (n+las+lbs) p [(n+las-1), (n+las+lbs-1)]]
                                  where
                                    as  = lineifyProof n       a
                                    bs  = lineifyProof (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last as) `union` soa (last bs)
lineifyProof n p@(IffInt a b)   = as++bs++[Line set (n+las+lbs) p [(n+las+lbs-1), (n+las-1)]] 
                                  where
                                    as  = lineifyProof n       a
                                    bs  = lineifyProof (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last as) `union` soa (last bs) 
lineifyProof n p@(IffElim1 a)   = as++[Line set (n+las) p [(n+las-1)]]
                                  where
                                    as  = lineifyProof n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(IffElim2 a)   = as++[Line set (n+las) p [(n+las-1)]]
                                  where
                                    as  = lineifyProof n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(AndInt   a b) = as++bs++[Line set (n+las+lbs) p [(n+las-1), (n+las+lbs-1)]] 
                                  where
                                    as  = lineifyProof n       a
                                    bs  = lineifyProof (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last as) `union` soa (last bs)
lineifyProof n p@(AndElim1 a)   = as++[Line set (n+las) p [(n+las-1)]] 
                                  where
                                    as  = lineifyProof n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(AndElim2 a)   = as++[Line set (n+las) p [(n+las-1)]] 
                                  where
                                    as  = lineifyProof n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(OrInt1 a b)   = as++[Line set (n+las) p [(n+las-1)]]
                                  where
                                    as = lineifyProof  n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(OrInt2 a b)   = as++[Line set (n+las) p [(n+las-1)]]
                                  where
                                    as = lineifyProof  n       a
                                    las = length as
                                    set = soa (last as)
lineifyProof n p@(OrElim1 a b)  = as++bs++[Line set (n+las+lbs) p [(n+las-1), (n+las+lbs-1)]]
                                  where
                                    as = lineifyProof  n       a
                                    bs = lineifyProof  (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last as) `union` soa (last bs)
lineifyProof n p@(OrElim2 a b)  = as++bs++[Line set (n+las+lbs) p [(n+las-1), (n+las+lbs-1)]]
                                  where
                                    as = lineifyProof  n       a
                                    bs = lineifyProof  (n+las) b
                                    las = length as
                                    lbs = length bs
                                    set = soa (last as) `union` soa (last bs)
lineifyProof n p@(RAA a b c)    = as++bs++cs++[Line set (n+las+lbs+lcs) p [(n+las-1), (n+las+lbs-1), (n+las+lbs+lcs-1)]]
                                  where
                                    as = lineifyProof  n           a
                                    bs = lineifyProof  (n+las)     b
                                    cs = lineifyProof  (n+las+lbs) c
                                    las = length as
                                    lbs = length bs
                                    lcs = length cs
                                    set = (soa (last as) `union` soa (last bs)) \\ freed 
                                    freed = map index (filter ((== proof (head cs)).proof) (as++bs))

-- Konsolidierung meint hier: Wir suchen gleiche Zeilen, die Annahmen sind, 
-- löschen alle doppelten und müssen dann natürlich die Referenzen in den 
-- anderen Zeilen anpassen. Dies ist nicht der Schönheit geduldet, sondern notwendig,
-- damit wir "die Annahmen wieder loswerden".
consolid                          :: [Line] -> [Line]
consolid []                        = []
consolid (x@(Line _ _ (A _) _):xs) = x:(consolid xs'')
                                     where
                                       doublets  = filter (\k-> proof x == proof k) xs
                                       replace d = \k-> if k==(index d) then (index x) else k
                                       xs'       = xs \\ doublets
                                       xs''      = foldr (\j-> map (mapIntInLine (replace j))) xs' doublets
consolid (x:xs)                    = x:(consolid xs)

-- Durch die Funktion `consolid` entstehen Lücken, die wir schließen, indem wir alle 
-- Zahlen in den nachfolgenden Zeilen anpassen.
-- Hierzu reicht es nicht die Zahlen nur zu erniedrigen - sie müssen gezielt ersetzt werden.
-- Man darf sich bitte selbst denken, warum ich das hier so explizit schreibe.
zipGaps                           :: [Line] -> [Line]
zipGaps []                         = []
zipGaps (x:xs)                     = x:(zipGaps(map (mapIntInLine (\k->if k==(index (head xs)) then k-offset+1 else k)) xs))
                                     where offset = (index (head xs)) - (index x)


