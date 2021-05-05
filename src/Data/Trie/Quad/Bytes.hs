{-# language BangPatterns #-}
{-# language BinaryLiterals #-}
{-# language DataKinds #-}
{-# language DerivingStrategies #-}
{-# language DuplicateRecordFields #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language KindSignatures #-}
{-# language MagicHash #-}
{-# language MultiWayIf #-}
{-# language NamedFieldPuns #-}
{-# language ScopedTypeVariables #-}
{-# language TypeApplications #-}
{-# language UnboxedSums #-}
{-# language UnboxedTuples #-}

module Data.Trie.Quad.Bytes
  ( Trie(..)
  , Node(..)
  , singleton
  , insert
  , lookup
  , valid
  , foldr
  , foldlM'
  , size
  ) where

import Prelude hiding (lookup,length,foldr)

import Data.Trie.Internal (insertSmallArray,replaceSmallArray)
import Data.Bits (countLeadingZeros,xor,popCount,(.&.),(.|.),unsafeShiftR,unsafeShiftL)
import Data.Primitive (ByteArray)
import Data.Bytes.Types (BytesN(..),Bytes(..),ByteArrayN(..))
import Data.Primitive (SmallArray)
import Data.Word (Word8,Word64)
import Control.Monad.ST.Run (runSmallArrayST)
import GHC.TypeNats (Nat)
import qualified Arithmetic.Types as Arithmetic
import qualified Arithmetic.Unsafe as Arithmetic
import qualified Data.Bytes as Bytes
import qualified Data.Foldable as Foldable
import qualified Data.Primitive as PM

-- | Non-empty qp tries with fixed-length keys.
newtype Trie (n :: Nat) a = Trie (Node a)
  deriving newtype (Eq)

data Node a
  = Branch
      !Int -- position, >=0 and <=(n*8-4), must divide 4 evenly 
      !Word -- bitset
      !(SmallArray (Node a))
      -- invariant: max length of children is 16
      -- invariant: position in any child branches is greater than position of parent
  | Leaf
      !ByteArray -- invariant, length n
      !a
  deriving stock (Eq)

size :: Trie n a -> Int
size (Trie t0) = go 0 t0 where
  go !b Leaf{} = b + 1
  go !b (Branch _ _ children) = Foldable.foldl' go b children
  

-- | Nonstrict right fold over the key-value pairs in the trie.
foldr :: (ByteArrayN n -> a -> b -> b) -> b -> Trie n a -> b
{-# inline foldr #-}
foldr g b0 (Trie t0) = go t0 b0 where
  go (Leaf k a) b = g (ByteArrayN k) a b
  go (Branch _ _ children) b = Foldable.foldr go b children

-- | Strict monadic left fold over the key-value pairs in the trie.
foldlM' :: Monad m => (b -> ByteArrayN n -> a -> m b) -> b -> Trie n a -> m b
{-# inline foldlM' #-}
foldlM' g b0 (Trie t0) = go b0 t0 where
  go b (Leaf k a) = g b (ByteArrayN k) a
  go b (Branch _ _ children) = Foldable.foldlM go b children

singleton :: Arithmetic.Nat n -> BytesN n -> a -> Trie n a
singleton (Arithmetic.Nat n) BytesN{array,offset} !v =
  let k = Bytes.toByteArray Bytes{array,offset,length=n}
   in Trie (Leaf k v)

lookup :: Arithmetic.Nat n -> BytesN n -> Trie n a -> Maybe a
{-# inline lookup #-}
lookup (Arithmetic.Nat n) BytesN{array,offset} (Trie t) = case lookup# array offset n t of
  (# (# #) | #) -> Nothing
  (# | v #) -> Just v

lookup# :: ByteArray -> Int -> Int -> Node a -> (# (# #) | a #)
{-# noinline lookup# #-}
lookup# !k !off0 !length t0 = go t0 where
  go (Leaf x v) = if Bytes{array=x,offset=0,length} == Bytes{array=k,offset=off0,length}
    then (# | v #)
    else (# (# #) | #)
  go (Branch pos bitset children) =
    let i :: Word64 -- a 4-bit number, a key slice interpreted as an index
        i = nybbleAtPos pos k off0
        mask :: Word
        mask = unsafeShiftL (1 :: Word) (fromIntegral @Word64 @Int i)
     in case bitset .&. mask of
          0 -> (# (# #) | #)
          _ ->
            let trueIx = popCount (bitset .&. (mask - 1))
             in case PM.indexSmallArray## children trueIx of
                  (# child #) -> go child

-- This function is a bit of a misnomer. It's not actually the nearest key
-- in the trie. It's any key where the maximum number of leading nybbles
-- match the needle.
nearestKey :: ByteArray -> Int -> Node a -> ByteArray
nearestKey !k !off0 t0 = go t0 where
  go (Leaf x _) = x
  go (Branch pos bitset children) =
    let i :: Word64 -- a 4-bit number, a key slice interpreted as an index
        i = nybbleAtPos pos k off0
        mask :: Word
        mask = unsafeShiftL (1 :: Word) (fromIntegral @Word64 @Int i)
     in case bitset .&. mask of
          0 -> case PM.indexSmallArray## children 0 of
            (# child #) -> leftmostChildKey child
          _ ->
            let trueIx = popCount (bitset .&. (mask - 1))
             in case PM.indexSmallArray## children trueIx of
                  (# child #) -> go child

-- Precondition: branch nodes must not be empty
leftmostChildKey :: Node a -> ByteArray
leftmostChildKey t0 = go t0 where
  go (Leaf k _) = k
  go (Branch _ _ children) = go (PM.indexSmallArray children 0)

compressIndex ::
     Word64 -- ^ 4-bit number (0 to 15 inclusive)
  -> Word -- bitset (only lower 16 bits should ever be set)
  -> (Int,Bool)
{-# inline compressIndex #-}
compressIndex !i !bitset = 
  let mask :: Word
      mask = unsafeShiftL (1 :: Word) (fromIntegral @Word64 @Int i)
   in (popCount (bitset .&. (mask - 1)), (bitset .&. mask) /= 0)

insert :: Arithmetic.Nat n -> BytesN n -> a -> Trie n a -> Trie n a
{-# inline insert #-}
insert (Arithmetic.Nat n) BytesN{array, offset} v (Trie trie) = Trie (insertNode n array offset v trie)

insertNode :: Int -> ByteArray -> Int -> a -> Node a -> Node a
{-# noinline insertNode #-}
insertNode !len !k !off0 v t0 =
  let !j = nearestKey k off0 t0
      !critPos = deltaNybbleStartIx len j 0 k off0
      go lf@(Leaf k' _) = if Bytes{array=k,offset=off0,length=len} /= Bytes{array=k',offset=0,length=len}
        then makeDoubleton len critPos k off0 j v lf
        else Leaf k' v
      go br@(Branch pos bitset children) =
        case compare pos critPos of
          LT -> let !kslice = nybbleAtPos pos k off0 in
            case compressIndex kslice bitset of
              (ix,True) -> case PM.indexSmallArray## children ix of
                (# child #) ->
                  let !child' = go child
                   in Branch pos bitset (replaceSmallArray children ix child')
              (_,False) -> errorWithoutStackTrace "Data.Trie.Quad.insert: mistake b"
          GT -> makeDoubleton len critPos k off0 j v br
          EQ -> let !kslice = nybbleAtPos pos k off0 in
            case compressIndex kslice bitset of
              (_,True) -> errorWithoutStackTrace "Data.Trie.Quad.insert: mistake d"
              (ix,False) -> Branch pos
                (bitset .|. unsafeShiftL (1 :: Word) (fromIntegral @Word64 @Int kslice))
                (insertSmallArray children ix (Leaf (Bytes.toByteArray Bytes{array=k,offset=off0,length=len}) v))
   in go t0

nybbleAtPos :: Int -> ByteArray -> Int -> Word64
{-# inline nybbleAtPos #-}
nybbleAtPos !pos !k !off0 =
  0x0F
  .&.
  unsafeShiftR
    (fromIntegral @Word8 @Word64 (PM.indexByteArray k (off0 + (unsafeShiftR pos 3)) :: Word8))
    (4 - (0b0100 .&. pos))

-- critPos must not be 64
-- the given node contains the j key already
-- Note that j is unsliced but k is sliced
makeDoubleton :: Int -> Int -> ByteArray -> Int -> ByteArray -> a -> Node a -> Node a
makeDoubleton !len !critPos !k0 !koff0 !j v !node =
  let !k = Bytes.toByteArray Bytes{array=k0,offset=koff0,length=len}
      !kslice = nybbleAtPos critPos k 0
      !jslice = nybbleAtPos critPos j 0
      !kleaf = Leaf k v
      !arr = runSmallArrayST $ do 
        dst <- PM.newSmallArray 2 kleaf
        let !ix = if kslice < jslice then 1 else 0
        PM.writeSmallArray dst ix node
        PM.unsafeFreezeSmallArray dst
   in Branch critPos
     (unsafeShiftL 1 (fromIntegral @Word64 @Int kslice)
      .|.
      unsafeShiftL 1 (fromIntegral @Word64 @Int jslice)
     ) arr

-- Returns number between 0 and 128. Number always divides 4 evenly.
deltaNybbleStartIx :: Int -> ByteArray -> Int -> ByteArray -> Int -> Int
deltaNybbleStartIx !len0 !a !aoff0 !b !boff0 = go 0 len0 aoff0 boff0 where
  go !result !len !aoff !boff = case len of
    0 -> result
    _ -> 
      let abyte :: Word8 = PM.indexByteArray a aoff
          bbyte :: Word8 = PM.indexByteArray b boff
          diff = countLeadingZeros (xor abyte bbyte)
       in if | diff == 8 -> go (result + 8) (len - 1) (aoff + 1) (boff + 1)
             | diff < 4 -> result
             | otherwise -> result + 4

valid :: Trie n a -> Bool
{-# noinline valid #-}
valid (Trie n0) = go (-1) n0 where
  go !_ Leaf{} = True
  go !i (Branch pos bitset children) =
    PM.sizeofSmallArray children > 1
    &&
    popCount bitset == PM.sizeofSmallArray children
    &&
    pos > i
    &&
    mod pos 4 == 0
    &&
    all (go pos) children
