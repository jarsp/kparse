import qualified Data.Map.Strict as M
import Data.Map.Strict ((!))
import qualified Data.Set as S
import qualified Data.List as L
import qualified Debug.Trace as T

type Line = String
type Pos = Int
type Node = (Line, Pos)
type Desc = (Line, Node, Pos)
type Gss = M.Map Node (S.Set Node)
type Workq = [Desc]
type Queued = S.Set Desc
type Popped = M.Map Node (S.Set Pos)
type State = (Desc, Gss, Workq, Queued, Popped)

-- Parse
parse :: State -> State
parse s = (plines ! "LS") s

success :: String -> State -> Bool
success input (_, _, _, u, _) = S.member ("L0", eNode, length input) u

-- Main Loop
process :: State -> State
process s@(_, _, [], _, _) = T.trace ("[]") s
process ((l, _, _), g, q@((l', n', j):r), u, p) = T.trace (show q) goto l' ((l, n', j), g, r, u, p)

-- Goto a line and execute
goto :: Line -> State -> State
goto l ((_, n, i), g, r, u, p) = (plines ! l) $ ((l, n, i), g, r, u, p)

-- Enqueue a new descriptor for processing
enq :: Desc -> State -> State
enq (l, ("cu", -1), -1) old@((lold, n, i), _, _, _, _) = enq (l, n, i) old
enq d' old@(d, g, r, u, p) = 
    if S.member d' u 
        then old
        else (d, g, d':r, S.insert d' u, p)

-- Create a GSS node with label the line to return to
-- If the node has been created and popped before repop node
create :: Desc -> State -> State
create (l, ("cu", -1), -1) old@((lold, n, i), _, _, _, _) = create (l, n, i) old
create (l, n, j) ((lold, _, i), g, r, u, p) = 
    case M.lookup v p of
        Just poss -> S.foldr (\pos s -> enq (l, n, pos) s) st' poss
        Nothing -> st'    
    where v = (l, j)
          g' = M.insertWith (\_ ns -> S.insert n ns) v (S.singleton n) g
          st' = ((lold, v, i), g', r, u, p)

-- Pop a GSS node, enqueuing the return line
-- Marks the node as popped
pop :: Node -> Pos -> State -> State
pop ("cu", -1) (-1) old@((lold, n, i), _, _, _, _) = pop n i old 
pop n@(l, _) j (d, g, r, u, p) = S.foldr (\v s -> enq (l, v, j) s) st' $ g ! n
    where st' = (d, g, r, u, M.insertWith (\_ poss -> S.insert j poss) n (S.singleton j) p)

-- Match a literal. If match, update pos and take left branch. Else right branch.
match :: String -> String -> (State -> State) -> (State -> State) -> State -> State
match s input f f' st@((l, n, i), g, r, u, p) = 
    if L.isPrefixOf s $ drop i input
        then f ((l, n, i + length s), g, r, u, p)
        else f' st

-- Parser input and consts
cu = ("cu", -1) :: Node
ci = -1 :: Pos
iNode = ("L0", 0) :: Node
iDesc = ("L0", iNode, 0) :: Desc
eNode = ("$", 0) :: Node
iGss = M.singleton iNode $ S.singleton eNode
iWorkq = []
iQueued = S.empty
iPopped = M.empty
iState = (iDesc, iGss, iWorkq, iQueued, iPopped) :: State

inp = "bbb"

plines :: M.Map String (State -> State)
plines = M.fromList grammar2'

{- 
 - S ::= ASd | BS | ε
 - A ::= a | c
 - B ::= a | b
-}
grammar0 = [ ("LS", goto "L0" . enq ("LS3", cu, ci) . enq ("LS2", cu, ci) . enq ("LS1", cu, ci))
           , ("L0", process)
           , ("LS1", goto "LA" . create ("L1", cu, ci))
           , ("L1", goto "LS" . create ("L2", cu, ci))
           , ("L2", goto "L0" . match "d" inp (pop cu ci) (id))
           , ("LS2", goto "LB" . create ("L3", cu, ci))
           , ("L3", goto "LS" . create ("L4", cu, ci))
           , ("L4", goto "L0" . pop cu ci)
           , ("LS3", goto "L0" . pop cu ci)
           , ("LA", goto "L0" . enq ("LA2", cu, ci) . enq ("LA1", cu, ci))
           , ("LA1", goto "L0" . match "a" inp (pop cu ci) (id))
           , ("LA2", goto "L0" . match "c" inp (pop cu ci) (id))
           , ("LB", goto "L0" . enq ("LB2", cu, ci). enq ("LB1", cu, ci))
           , ("LB1", goto "L0" . match "a" inp (pop cu ci) (id))
           , ("LB2", goto "L0" . match "b" inp (pop cu ci) (id))
           ]

{-
 - S ::= SSa | ε
-}
grammar1 = [ ("LS", goto "L0" . enq ("LS1", cu, ci) . enq ("LS2", cu, ci))
           , ("L0", process)
           , ("LS1", goto "LS" . create ("L1", cu, ci))
           , ("L1", goto "LS" . create ("L2", cu, ci))
           , ("L2", goto "L0" . match "a" inp (pop cu ci) (id))
           , ("LS2", goto "L0" . pop cu ci)
           ]

{-
 - S ::= SSS | SS | b
-}
grammar2 = [ ("LS", goto "L0" . enq ("LS1", cu, ci) . enq ("LS2", cu, ci) . enq ("LS3", cu, ci))
           , ("L0", process)
           , ("LS1", goto "LS" . create ("L1", cu, ci))
           , ("L1", goto "LS" . create ("L2", cu, ci))
           , ("L2", goto "LS" . create ("L3", cu, ci))
           , ("L3", goto "L0" . pop cu ci)
           , ("LS2", goto "LS" . create ("L4", cu, ci))
           , ("L4", goto "LS" . create ("L5", cu, ci))
           , ("L5", goto "L0" . pop cu ci)
           , ("LS3", goto "L0" . match "b" inp (pop cu ci) (id)) 
           ]

grammar2' = [ ("LS", goto "L0" . enq ("LS1", cu, ci) . enq ("L1", cu, ci) . enq ("LS3", cu, ci))
            , ("L0", process)
            , ("LS1", goto "LS" . create ("L1", cu, ci))
            , ("L1", goto "LS" . create ("L2", cu, ci))
            , ("L2", goto "LS" . create ("L3", cu, ci))
            , ("L3", goto "L0" . pop cu ci)
            , ("LS3", goto "L0" . match "b" inp (pop cu ci) (id)) 
            ]

{-
 - S ::= Ca | d
 - B ::= ε | a
 - C ::= b | BCb | bb
-}
grammar3 = [ ("LS", goto "L0" . enq ("LS1", cu, ci) . enq ("LS2", cu, ci))
           , ("L0", process)
           , ("LS1", goto "LC" . create ("L1", cu, ci))
           , ("L1", goto "L0" . match "a" inp (pop cu ci) (id)) 
           , ("LS2", goto "L0" . match "d" inp (pop cu ci) (id))
           , ("LB", goto "L0" . enq ("LB1", cu, ci) . enq ("LB2", cu, ci))
           , ("LB1", goto "L0" . pop cu ci)
           , ("LB2", goto "L0" . match "a" inp (pop cu ci) (id))
           , ("LC", goto "L0" . enq ("LC1", cu, ci) . enq ("LC2", cu, ci) . enq ("LC3", cu, ci))
           , ("LC1", goto "L0" . match "b" inp (pop cu ci) (id))
           , ("LC2", goto "LB" . create ("L2", cu, ci))
           , ("L2", goto "LC" . create ("L3", cu, ci))
           , ("L3", goto "L0" . match "b" inp (pop cu ci) (id))
           , ("LC3", goto "L0" . match "bb" inp (pop cu ci) (id))
           ]

-- Pretty
pretty :: State -> IO()
pretty s@(d, g, r, u, p) = do putStr "\nParse Result: "
                              putStr (if success inp s then "Success\n" else "Failure\n")
                              putStr "\nDesc: "
                              print d
                              putStr "\nWork Queue: "
                              print r
                              putStrLn "\nGSS:"
                              mapM_ print (M.toList $ M.map (S.toList) g)
                              putStrLn "\nPopped:"
                              mapM_ print (M.toList $ M.map (S.toList) p)
                              putStrLn "\nQueued:"
                              mapM_ print (S.toList u)
                              putStr "\n"

prettys :: State -> IO()
prettys s@(d, g, r, u, p) = do putStr "\nParse Result: "
                               putStr (if success inp s then "Success\n" else "Failure\n")
                               putStr "\nDesc: "
                               print d
                               putStr "\nWork Queue: "
                               print r
                               putStrLn "\nGSS:"
                               mapM_ print (M.toList $ M.map (S.toList) g)
                               putStrLn "\nPopped:"
                               mapM_ print (M.toList $ M.map (S.toList) p)
                               putStr "\n"

prettym :: State -> IO()
prettym s@(d, g, r, u, p) = do putStr "\nParse Result: "
                               putStr (if success inp s then "Success\n" else "Failure\n")
                               putStr "\nDesc: "
                               print d
                               putStr "\nWork Queue: "
                               print r
                               putStr "\n"
