{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

import qualified Data.HashMap.Strict as H
import Data.HashMap.Strict ((!))
import qualified Data.Hashable as HS
import qualified Data.Set as S
import qualified Data.List as L
import qualified Data.Ord as O
import qualified Debug.Trace as TR

------ Type Declarations, Constants ------
class Display a where
    display :: a -> String

pretty :: State -> IO()
pretty s = putStr $ display s

data Symbol = NT String
            | T String
    deriving (Show, Eq, Ord)

instance Display Symbol where
    display (NT s) = s
    display (T s) = s

instance HS.Hashable Symbol where
    hashWithSalt s n =
        case n of
          NT x -> s `HS.hashWithSalt` x
          T x -> s `HS.hashWithSalt` x

type Item = [Symbol]

instance Display Item where
    display l = concatMap (display) l

type Grammar = H.HashMap Symbol (S.Set Item)

instance Display a => Display (S.Set a) where
    display s = S.foldr (\i a -> a ++ " " ++ display i) "" s

instance (Display a, Display b) => Display (H.HashMap a b) where
    display h = H.foldrWithKey (\k v a -> a ++ "\n" ++ display k ++ ": " ++ display v) "" h

data SPPFNode = Node Symbol Integer Integer
              | Inter Symbol Item Item Integer Integer
              | Pack Symbol Item Item Integer SPPFNode SPPFNode
              | None
    deriving (Show, Eq, Ord)

instance Display SPPFNode where
    display (Node s i j) = "(" ++ display s ++ ", " ++ show i ++ ", " ++ show j ++ ")"
    display (Inter s a b i j) = "{" ++ display s ++ " ::= " ++ display a ++ "." ++ display b ++ ", " ++ show i ++ ", " ++ show j ++ "}"
    display (Pack s a b i l r) = "[(" ++ display s ++ " ::= "  ++ display a ++ "." ++ display b ++ ", " ++ show i ++ ") " ++ display l ++ " " ++ display r ++ "]"
    display None = "($)"

instance HS.Hashable SPPFNode where
    hashWithSalt s n =
        case n of
          Node x i j -> s `HS.hashWithSalt` x `HS.hashWithSalt` 
                        i `HS.hashWithSalt` j
          Inter x a b i j -> s `HS.hashWithSalt` x `HS.hashWithSalt` 
                             a `HS.hashWithSalt` b `HS.hashWithSalt` 
                             i `HS.hashWithSalt` j
          Pack x a b i l r -> if r /= None then 
                                 s `HS.hashWithSalt` x `HS.hashWithSalt` 
                                 a `HS.hashWithSalt` b `HS.hashWithSalt`
                                 i `HS.hashWithSalt` l `HS.hashWithSalt` r
                              else
                                 s `HS.hashWithSalt` x `HS.hashWithSalt` 
                                 a `HS.hashWithSalt` b `HS.hashWithSalt`
                                 i `HS.hashWithSalt` l

type SPPF = H.HashMap SPPFNode (S.Set SPPFNode)

type GSSNode = (String, Integer)

instance Display GSSNode where
    display n = show n

type GSSEdge = (GSSNode, SPPFNode) -- should be a regular node

instance Display GSSEdge where
    display (n, s) = "(" ++ display n ++ ", " ++ display s ++ ")"

type GSS = H.HashMap GSSNode (S.Set GSSEdge)

type LabelMap = H.HashMap String (Symbol, Item, Item)

type Desc = (String, GSSNode, Integer, SPPFNode)

instance Display Desc where
    display (l, t, i, w) = "(" ++ l ++ ", " ++ display t ++ ", " ++ show i ++ ", " ++ display w ++ ")"

type RSet = [Desc]

instance Display RSet where
    display = show

type USet = S.Set Desc

type PSet = H.HashMap GSSNode (S.Set SPPFNode)

type State = (Desc, RSet, USet, PSet, GSS, SPPF)

instance Display State where
    display (d, r, u, p, g, s) = "Descriptor:\n" ++ display d ++ "\n\n"
                              ++ "Queue:\n " ++ display r ++ "\n\n"
                              ++ "Added:\n" ++ display u ++ "\n\n"
                              ++ "Popped:\n" ++ display p ++ "\n\n"
                              ++ "GSS:\n" ++ display g ++ "\n\n"
                              ++ "SPPF:\n" ++ display s ++ "\n\n"

type Aux = (Grammar, LabelMap)

type ParseFunc = String -> Aux -> State -> State

epsilon = [] :: Item
base = ("$", 0) :: GSSNode
initGSS = H.singleton base S.empty
initState = (("L0", base, 0, None), [], S.empty, H.empty, initGSS, H.empty) :: State

------ Auxilliary Functions/Data ------

nullable :: Symbol -> Grammar -> Bool
nullable n@(NT x) g = S.member epsilon $ g ! n
nullable (T x) _ = error $ "not a nonterminal: " ++ x

isTerminal :: Symbol -> Bool
isTerminal (T _) = True
isTerminal _ = False

add :: Desc -> State -> State
add d' (d, r, u, p, g, s) = (d, r', u', p, g, s) 
    where isNew = not $ S.member d' u
          u' = S.insert d' u
          r' = if isNew then (d':r) else r

pop :: GSSNode -> Integer -> SPPFNode -> Aux -> State -> State
pop ("$", 0) _ _ _ st = st
pop t@(l, k) i z ax@(gr, lm) (d, r, u, p, g, s) = st'
    where p' = H.insertWith f t (S.singleton z) p
          f _ old = S.insert z old
          (x, a, b) = lm ! l
          st' = S.foldr f' (d, r, u, p', g, s) $ g ! t
          f' (v, w) sx = add (l, v, i, y) sx'
              where (sx', y) = getNodeP x a b w z ax sx

create :: Desc -> Aux -> State -> (State, GSSNode)
create (l, t, i, w) ax@(gr, lm) st@(d, r, u, p, g, s) = (st', v)
    where v = (l, i)
          edge = (t, w)
          g' = H.insertWith f v (S.singleton edge) g
          f _ old = S.insert edge old
          isNew = case H.lookup v g of
                    Just es -> not $ S.member edge es
                    Nothing -> True
          (x, a, b) = lm ! l
          st' = if isNew then
                    case H.lookup v p of
                      Just popped -> S.foldr f' (d, r, u, p, g', s) popped
                      _ -> (d, r, u, p, g', s)
                else
                    (d, r, u, p, g', s)
          f' z@(Node _ _ h) sx = add (l, t, h, y) sx'
            where (sx', y) = getNodeP x a b w z ax sx

getNodeT :: Symbol -> Integer -> State -> (State, SPPFNode)
getNodeT t@(T x) i (d, r, u, p, g, s) = ((d, r, u, p, g, s'), n)
    where s' = H.insertWith f n S.empty s
          f _ old = old
          n = Node t i h 
          h = if x == "" then i else i + 1

getNodeP :: Symbol -> Item -> Item -> SPPFNode -> SPPFNode -> Aux -> State -> (State, SPPFNode)
-- Right child z is never an intermediate or packed node
-- Left child w is never a packed node
getNodeP x@(NT _) a b w z@(Node _ k i) (gr, lm) st@(d, r, u, p, g, s) =
    if (length a == 1)
       && (isTerminal (a !! 0) || (not $ nullable (a !! 0) gr))
       && (b /= epsilon)
    then 
        (st, z)
    else
        let t = if b == epsilon then (Node x) else (Inter x a b)
            y = if w /= None then 
                  case w of
                    Node _ j k -> t j i
                    Inter _ _ _ j k -> t j i
                    _ -> error $ "could not match y in: getNodeP " ++ show x ++ " "
                                 ++ show a ++ " " ++ show b ++ " " ++ show w ++ " "
                                 ++ show z
                else
                  t k i
            pack = if w /= None then Pack x a b k w z else Pack x a b k z None
            s' = H.insertWith f y (S.singleton pack) s
            f _ old = S.insert pack old
         in ((d, r, u, p, g, s'), y)
getNodeP x a b w z _ _ = error $ show x ++ " " ++ show a ++ " " ++ show b ++ " " ++ show w ++ " " ++ show z ++ "\n"

------ Parsing Helpers  ------
getFunc :: String -> H.HashMap String a -> a
getFunc s h = h ! s

getSym :: Integer -> String -> Char
getSym i s = s !! (fromIntegral i)

isSuccessful :: String -> SPPF -> Bool
isSuccessful inp s =
    if H.member (Node (NT "S") 0 $ toInteger $ length inp - 1) s then
        True
    else 
        False

getDesc :: State -> Desc
getDesc (d, _, _, _, _, _) = d

setLabel :: String -> Desc -> Desc
setLabel l' (_, t, i, w) = (l', t, i, w)

getCU :: State -> GSSNode
getCU ((_, t, _, _), _, _, _, _, _) = t

setCU :: GSSNode -> State -> State
setCU t' ((l, t, i, w), r, u, p, g, s) = ((l, t', i, w), r, u, p, g, s)

getCI :: State -> Integer
getCI ((_, _, i, _), _, _, _, _, _) = i

setCI :: Integer -> State -> State
setCI i' ((l, t, i, w), r, u, p, g, s) = ((l, t, i', w), r, u, p, g, s)

getCN :: State -> SPPFNode
getCN ((_, _, _, w), _, _, _, _, _) = w

setCN :: SPPFNode -> State -> State
setCN w' ((l, t, i, w), r, u, p, g, s) = ((l, t, i, w'), r, u, p, g, s)

----- Test Grammars -----

--- G1 ---
g1 = H.fromList [(NT "S", S.fromList [[T "a", NT "S", T "b"],
                                      [T "d"],
                                      [T "a", T "d", T "b"]])
                ]

g1LMap = H.fromList [("RS1", (NT "S", [T "a", NT "S"], [T "b"]))
                    ]

g1Aux = (g1, g1LMap)

getFuncG1 = flip getFunc g1Func

g1Func = H.fromList [("L0", (g1L0)),
                     ("LS", (g1LS)),
                     ("LS1", (g1LS1)),
                     ("RS1", (g1RS1)),
                     ("LS2", (g1LS2)),
                     ("LS3", (g1LS3))
                    ]

g1L0 :: ParseFunc
g1L0 inp ax (d, (r@(l, t, i, w)):rs, u, p, g, s) =
    (getFuncG1 l) inp ax (r, rs, u, p, g, s)
g1L0 _ _ s = s

g1LS :: ParseFunc
g1LS inp ax st = g1L0 inp ax st1
    where t = getCU st
          i = getCI st
          w = getCN st
          c = getSym i inp
          st1 | c == 'a' = add ("LS3", t, i, None) $ add ("LS1", t, i, None) st
              | c == 'd' = add ("LS2", t, i, None) st
              | otherwise = st

g1LS1 :: ParseFunc
g1LS1 inp ax st = 
    let i = getCI st 
        (st1, w1) = getNodeT (T "a") i st
        st2 = setCN w1 $ setCI (i + 1) st1
        (st3, t1) = create (setLabel "RS1" $ getDesc st2) ax st2
        st4 = setCU t1 st3
        match = [getSym (i + 1) inp] `L.isInfixOf` "ad"
        stfinal = if match then st4 else st2
        next = if match then (g1LS) else (g1L0)
     in next inp ax stfinal

g1RS1 :: ParseFunc
g1RS1 inp ax st =
    let i = getCI st
        (st1, cr) = getNodeT (T "b") i st
        (st2, w1) = getNodeP (NT "S") [T "a", NT "S", T "b"] [] (getCN st1) cr ax st1
        st3 = setCN w1 $ setCI (i + 1) st2
        st4 = pop (getCU st3) (getCI st3) (getCN st3) ax st3
        match = getSym i inp == 'b'
        stfinal = if match then st4 else st
     in g1L0 inp ax stfinal

g1LS2 :: ParseFunc
g1LS2 inp ax st =
    let i = getCI st
        (st1, cr) = getNodeT (T "d") i st
        (st2, w1) = getNodeP (NT "S") [T "d"] [] (getCN st2) cr ax st1
        st3 = setCN w1 $ setCI (i + 1) st2
        stfinal = pop (getCU st3) (getCI st3) (getCN st3) ax st3
     in g1L0 inp ax stfinal

g1LS3 :: ParseFunc
g1LS3 inp ax st =
    let i = getCI st
        (st1, w1) = getNodeT (T "a") i st
        st2 = setCI (i + 1) $ setCN w1 st1
        (st3, cr1) = getNodeT (T "d") (i + 1) st2
        (st4, w2) = getNodeP (NT "S") [T "a", T "d"] [T "b"] w1 cr1 ax st3
        st5 = setCI (i + 2) $ setCN w2 st4
        (st6, cr2) = getNodeT (T "b") (i + 2) st5
        (st7, w3) = getNodeP (NT "S") [T "a", T "d", T "b"] [] w2 cr2 ax st6
        st8 = setCI (i + 3) $ setCN w3 st7
        st9 = pop (getCU st8) (getCI st8) (getCN st8) ax st8
        matchd = getSym (i + 1) inp == 'd'
        matchb = getSym (i + 2) inp == 'b'
        stfinal = if matchd && matchb then st9 else (if matchd then st5 else st2)
     in g1L0 inp ax stfinal

--- G2 --

g2 = H.fromList [(NT "S", S.fromList [[NT "S", T "+", NT "S"],
                                      [NT "S", T "*", NT "S"],
                                      [T "x"]])
                ]

g2LMap = H.fromList [("RS1", (NT "S", [NT "S", T "+", NT "S"], [])),
                     ("RS2", (NT "S", [NT "S", T "*", NT "S"], [])),
                     ("L1", (NT "S", [NT "S"], [T "+", NT "S"])),
                     ("L2", (NT "S", [NT "S"], [T "*", NT "S"]))
                    ]

g2Aux = (g2, g2LMap)

getFuncG2 = flip getFunc g2Func

g2Func = H.fromList [("L0", (g2L0)),
                     ("LS", (g2LS)),
                     ("LS1", (g2LS1)),
                     ("L1", (g2L1)),
                     ("RS1", (g2RS1)),
                     ("LS2", (g2LS2)),
                     ("L2", (g2L2)),
                     ("RS2", (g2RS2)),
                     ("LS3", (g2LS3))
                    ]

g2L0 :: ParseFunc
g2L0 inp ax (d, (r@(l, t, i, w)):rs, u, p, g, s) =
    (getFuncG2 l) inp ax (r, rs, u, p, g, s)
g2L0 _ _ s = s

g2LS :: ParseFunc
g2LS inp ax st = g2L0 inp ax st1
    where t = getCU st
          i = getCI st 
          w = getCN st
          c = getSym i inp
          st1 | c == 'x' = add ("LS3", t, i, None) $ add ("LS2", t, i, None) $ add ("LS1", t, i, None) st
              | otherwise = st

g2LS1 :: ParseFunc
g2LS1 inp ax st =
    let (st1, t1) = create (setLabel "L1" $ getDesc st) ax st
        st2 = setCU t1 st1
     in g2LS inp ax st2

g2L1 :: ParseFunc
g2L1 inp ax st = 
    let i = getCI st
        (st1, cr) = getNodeT (T "+") i st
        (st2, w1) = getNodeP (NT "S") [NT "S", T "+"] [NT "S"] (getCN st1) cr ax st1
        st3 = setCN w1 $ setCI (i + 1) st2
        (st4, t1) = create (setLabel "RS1" $ getDesc st3) ax st3 
        st5 = setCU t1 st4
        matchp = getSym i inp == '+'
        matchx = getSym (i + 1) inp == 'x'
        (stfinal, next) = if matchp && matchx then
                             (st5, (g2LS))
                          else if matchp then
                                  (st3, (g2L0))
                               else 
                                  (st, (g2L0))
     in next inp ax stfinal

g2RS1 :: ParseFunc
g2RS1 inp ax st =
    let st1 = pop (getCU st) (getCI st) (getCN st) ax st
     in g2L0 inp ax st1

g2LS2 :: ParseFunc
g2LS2 inp ax st =
    let (st1, t1) = create (setLabel "L2" $ getDesc st) ax st
        st2 = setCU t1 st1
     in g2LS inp ax st2

g2L2 :: ParseFunc
g2L2 inp ax st = 
    let i = getCI st
        (st1, cr) = getNodeT (T "*") i st
        (st2, w1) = getNodeP (NT "S") [NT "S", T "*"] [NT "S"] (getCN st1) cr ax st1
        st3 = setCN w1 $ setCI (i + 1) st2
        (st4, t1) = create (setLabel "RS2" $ getDesc st3) ax st3 
        st5 = setCU t1 st4
        matchp = getSym i inp == '*'
        matchx = getSym (i + 1) inp == 'x'
        (stfinal, next) = if matchp && matchx then
                             (st5, (g2LS))
                          else if matchp then
                                  (st3, (g2L0))
                               else
                                  (st, (g2L0))
     in next inp ax stfinal

g2RS2 :: ParseFunc
g2RS2 inp ax st =
    let st1 = pop (getCU st) (getCI st) (getCN st) ax st
     in g2L0 inp ax st1

g2LS3 :: ParseFunc
g2LS3 inp ax st =
    let i = getCI st 
        (st1, cr) = getNodeT (T "x") i st
        (st2, w1) = getNodeP (NT "S") [T "x"] [] (getCN st1) cr ax st1
        st3 = setCN w1 $ setCI (i + 1) st2
        stfinal = pop (getCU st3) (getCI st3) (getCN st3) ax st3
     in g2L0 inp ax stfinal

--- G3 --

g3 = H.fromList [(NT "S", S.fromList [[NT "S", T "+", NT "S"],
                                      [T "x"]])
                ]

g3LMap = H.fromList [("RS1", (NT "S", [NT "S", T "+", NT "S"], [])),
                     ("L1", (NT "S", [NT "S"], [T "+", NT "S"]))
                    ]

g3Aux = (g3, g3LMap)

getFuncG3 = flip getFunc g3Func

g3Func = H.fromList [("L0", (g3L0)),
                     ("LS", (g3LS)),
                     ("LS1", (g3LS1)),
                     ("L1", (g3L1)),
                     ("RS1", (g3RS1)),
                     ("LS3", (g3LS3))
                    ]

g3L0 :: ParseFunc
g3L0 inp ax (d, (r@(l, t, i, w)):rs, u, p, g, s) =
    (getFuncG3 l) inp ax (r, rs, u, p, g, s)
g3L0 _ _ s = s

g3LS :: ParseFunc
g3LS inp ax st = g3L0 inp ax st1
    where t = getCU st
          i = getCI st 
          w = getCN st
          c = getSym i inp
          st1 | c == 'x' = add ("LS3", t, i, None) $ add ("LS1", t, i, None) st
              | otherwise = st

g3LS1 :: ParseFunc
g3LS1 inp ax st =
    let (st1, t1) = create (setLabel "L1" $ getDesc st) ax st
        st2 = setCU t1 st1
     in g3LS inp ax st2

g3L1 :: ParseFunc
g3L1 inp ax st = 
    let i = getCI st
        (st1, cr) = getNodeT (T "+") i st
        (st2, w1) = getNodeP (NT "S") [NT "S", T "+"] [NT "S"] (getCN st1) cr ax st1
        st3 = setCN w1 $ setCI (i + 1) st2
        (st4, t1) = create (setLabel "RS1" $ getDesc st3) ax st3 
        st5 = setCU t1 st4
        matchp = getSym i inp == '+'
        matchx = getSym (i + 1) inp == 'x'
        (stfinal, next) = if matchp && matchx then
                             (st5, (g3LS))
                          else if matchp then
                                  (st3, (g3L0))
                               else 
                                  (st, (g3L0))
     in next inp ax stfinal

g3RS1 :: ParseFunc
g3RS1 inp ax st =
    let st1 = pop (getCU st) (getCI st) (getCN st) ax st
     in g3L0 inp ax st1

g3LS3 :: ParseFunc
g3LS3 inp ax st =
    let i = getCI st 
        (st1, cr) = getNodeT (T "x") i st
        (st2, w1) = getNodeP (NT "S") [T "x"] [] (getCN st1) cr ax st1
        st3 = setCN w1 $ setCI (i + 1) st2
        stfinal = pop (getCU st3) (getCI st3) (getCN st3) ax st3
     in g3L0 inp ax stfinal
