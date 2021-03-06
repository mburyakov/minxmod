module BDD where

import Predicates
import ArgTree
import ArgOrd
import qualified Data.Map as Map
import Data.Graph.Inductive.Tree
import qualified Data.Graph.Inductive.Graph as Graph
import Data.GraphViz
import Data.GraphViz.Attributes.Complete
import qualified Data.Text.Lazy as Lazy
import Debug.Trace

type BDDIndex = Int

data BDDNode = 
    NodeTrue
  | NodeFalse
  | NodeIf ArgIndex BDDIndex BDDIndex
  | NodeEq ArgIndex ArgIndex BDDIndex BDDIndex
  | NodeForceOrd ForceOrdUsage ArgOrd BDDIndex
    deriving (Eq, Show)

type BDDBox = Map.Map BDDIndex BDDNode

data BoxedBDD = BoxedBDD { bddRoot :: BDDIndex, bddBox::BDDBox}
  deriving Show

data BDDNodeLabel =
    LNodeTrue
  | LNodeFalse
  | LNodeIf ArgIndex
  | LNodeEq ArgIndex ArgIndex
  | LNodeForceOrd ForceOrdUsage ArgOrd

showEqIndex i =
  a ++ "|" ++ b
    where
      a = reverse . tail . reverse . show . reverse . tail . reverse $ i
      b = tail . show $ [last i]

instance Show BDDNodeLabel where
  show LNodeTrue = "T"
  show LNodeFalse = "F"
  show (LNodeForceOrd usage ord) = "usage = " ++ show usage ++ "\nord = " ++ show ord
  show (LNodeIf i) = show i
  show (LNodeEq i j) = showEqIndex i ++ "=" ++ showEqIndex j

bddNodeLabel NodeTrue =
  LNodeTrue
bddNodeLabel NodeFalse =
  LNodeFalse
bddNodeLabel (NodeForceOrd u ord ia) =
  LNodeForceOrd u ord
bddNodeLabel (NodeIf i ia ib) =
  LNodeIf i
bddNodeLabel (NodeEq i j ia ib) =
  LNodeEq i j



type BDDEdgeLabel = Bool

replaceRoot newRoot (BoxedBDD root box) =
  BoxedBDD newRoot box

emptyBox :: BDDBox
emptyBox = Map.empty

newNodeNum box | maxIndex + 1 > maxIndex =
  maxIndex + 1
    where
      maxIndex = if Map.null box then 0 else fst $ Map.findMax box

putNode node box =
  if
    null oldindexes
  then
    BoxedBDD index newbox
  else
    BoxedBDD (head oldindexes) box
    where
      oldindexes = Map.keys $ Map.filter (==node) box
      newbox = Map.insert index node box
      index = newNodeNum box

getNode (BoxedBDD ind box) =
  Map.lookup ind box

putBDD BDDTrue box =
  putNode NodeTrue box
putBDD BDDFalse box =
  putNode NodeFalse box
putBDD (BDDforceOrd u ord a) box =
  putNode (NodeForceOrd u ord ind1) newbox1
    where
      b1@(BoxedBDD ind1 newbox1) = putBDD a box
putBDD (BDDv i a b) box =
  if
    ind1 == ind2
  then
    b1
  else
    putNode (NodeIf i ind1 ind2) newbox2
     where
       b1@(BoxedBDD ind1 newbox1) = putBDD a box
       b2@(BoxedBDD ind2 newbox2) = putBDD b newbox1
putBDD (BDDeq i j a b) box =
  if
    ind1 == ind2
  then
    b1
  else
    putNode (NodeEq i j ind1 ind2) newbox2
     where
       b1@(BoxedBDD ind1 newbox1) = putBDD a box
       (BoxedBDD ind2 newbox2) = putBDD b newbox1

getBDD boxedbdd = do
  v <- getNode boxedbdd
  case v of
    NodeTrue ->
      return BDDTrue
    NodeFalse ->
      return BDDFalse
    (NodeIf i ia ib) -> do
      a <- getBDD $ replaceRoot ia boxedbdd
      b <- getBDD $ replaceRoot ib boxedbdd
      return $ BDDv i a b
    (NodeEq i j ia ib) -> do
      a <- getBDD $ replaceRoot ia boxedbdd
      b <- getBDD $ replaceRoot ib boxedbdd
      return $ BDDeq i j a b
    (NodeForceOrd u ord ia) -> do
      a <- getBDD $ replaceRoot ia boxedbdd
      return $ BDDforceOrd u ord a

edgeToGraph v1 v2 label g =
  Graph.insEdge (v1, v2, label) g

nodeToGraph k v g =
  case v of
    NodeTrue ->
      g
    NodeFalse ->
      g
    (NodeForceOrd u ord ia) ->
      edgeToGraph k ia True g
    (NodeIf i ia ib) ->
      edgeToGraph k ib False $ edgeToGraph k ia True g
    (NodeEq i j ia ib) ->
      edgeToGraph k ib False $ edgeToGraph k ia True g

toGraph :: BDDBox -> Gr BDDNodeLabel BDDEdgeLabel
toGraph box =
  Map.foldrWithKey nodeToGraph g1 box
    where
      g1 = Map.foldrWithKey (\k v g -> Graph.insNode (k,(bddNodeLabel v)) g) Graph.empty box

dotParams = nonClusteredParams {
  fmtEdge =
    \(node1, node2, b) -> 
      if b then
        [Color [X11Color Red]]
      else
        [Style [SItem Dashed []], Color	[X11Color Blue]],
  fmtNode =
    \(node, t) ->
      [Label $ StrLabel $ Lazy.pack $ show t]
}

defaultVis :: (Graph.Graph gr) => gr BDDNodeLabel BDDEdgeLabel -> DotGraph Graph.Node
defaultVis = graphToDot dotParams
