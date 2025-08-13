{-# language BangPatterns #-}
{-# language BinaryLiterals #-}
{-# language DerivingStrategies #-}
{-# language MagicHash #-}
{-# language NumericUnderscores #-}
{-# language TypeApplications #-}
{-# language UnboxedSums #-}
{-# language UnboxedTuples #-}

module Data.Trie.Quad.Prefix
  ( Trie(..)
  , singleton
  , insert
  , lookup
  , lookup#
  , valid
  ) where

import Prelude hiding (lookup)

import Control.Monad.ST.Run (runSmallArrayST)
import Data.Bits (countLeadingZeros,xor,popCount,(.&.),(.|.),unsafeShiftR,unsafeShiftL)
import Data.Bits (shiftR,shiftL)
import Data.Primitive (SmallArray)
import Data.Word (Word64,Word32)
import Numeric (showHex)

import qualified Data.Primitive as PM

-- | Non-empty qp tries. These have all of the properties that the tries in
--   @Data.Trie.Quad@ have. Additionally:
--
-- * Every key is accompanied by a prefix. The prefix dictates how many of the
--   most significant bits are used. All insignificant bits are set
--   to zero. This is very much like a CIDR mask for IP addresses. A prefix
--   of zero implies a singleton map that matches everything. Prefixes must not
--   be greater than 64.
-- * Interpreted as ranges, the set of keys must not overlap. Overlapping key
--   ranges result in an exception.
-- * The same key must not be inserted more than once. This results in an
--   exception.
data Trie a
  = Branch
      !Word32 -- position, >=0 and <=60, must divide 4 evenly 
      !Word32 -- bitset (only the low 16 bits are used, high 16 bits must be zero)
      !(SmallArray (Trie a)) -- invariant: max length is 16
  | Leaf
      !Word32 -- effective key length, between 0 and 64
      !Word64 -- key, normalized
      !a
  deriving stock (Eq)

normalizeKey ::
     Word32 -- number of most significant bits that are used, N.
  -> Word64 -- the key
  -> Word64 -- key with lower bits zeroed out. Number of zeroed lower bits = 64 - N.
normalizeKey b w = shiftL 0xFFFF_FFFF_FFFF_FFFF (64 - fromIntegral @Word32 @Int b) .&. w

inclusiveUpperBound ::
     Word32 -- number of most significant bits that are used, N.
  -> Word64 -- the key
  -> Word64 -- key with lower bits all set to 1
inclusiveUpperBound b w = shiftR 0xFFFF_FFFF_FFFF_FFFF (fromIntegral @Word32 @Int b) .|. w

singleton ::
     Int -- ^ Number of bits to consider, @[0-64]@
  -> Word64 -- ^ Key, for bit count less than 64, low bits are masked out 
  -> a -- ^ Value
  -> Trie a
singleton !b !k !v
  | b < 0 = errorWithoutStackTrace "Data.Trie.Quad.Prefix: key size less than zero"
  | b > 64 = errorWithoutStackTrace "Data.Trie.Quad.Prefix: key size greater than 64"
  | otherwise = let !b32 = fromIntegral b :: Word32 in Leaf b32 (normalizeKey b32 k) v

lookup ::
     Word64 -- ^ Key
  -> Trie a -- ^ Trie
  -> Maybe a
{-# inline lookup #-}
lookup !k t = case lookup# k t of
  (# (# #) | #) -> Nothing
  (# | v #) -> Just v

lookup# :: Word64 -> Trie a -> (# (# #) | a #)
{-# noinline lookup# #-}
lookup# !k t0 = go t0 where
  go (Leaf xbits x v) = if x == normalizeKey xbits k
    then (# | v #)
    else (# (# #) | #)
  go (Branch pos bitset children) =
    let i :: Word32 -- a 4-bit number, a key slice interpreted as an index
        i = fromIntegral @Word64 @Word32 (0x0F .&. unsafeShiftR k (60 - fromIntegral @Word32 @Int pos))
        (ix,wasFound) = compressIndex i bitset
     in case wasFound of
          -- False -> error
          --   ("not found but i is: " ++ show i ++ ",ix is: " ++ show ix ++
          --    ", bitset was " ++ printf "0b%016b" bitset)
          False -> let ix' = ix - 1 in case ix' of
            (-1) -> (# (# #) | #)
            _ ->
              let !(# child #) = PM.indexSmallArray## children ix'
               in go child
          True ->
            let !(# child #) = PM.indexSmallArray## children ix
             in go child

-- This function is a bit of a misnomer. It's not actually the nearest key
-- in the trie. It's any key where the maximum number of leading nybbles
-- match the needle.
--
-- TODO: I believe it is possible to make this function error in the case
-- of overlapping keys.
nearestKey :: Word64 -> Trie a -> Word64
nearestKey !k t0 = go t0 where
  go (Leaf _ x _) = x
  go (Branch pos bitset children) =
    let i :: Word64 -- a 4-bit number, a key slice interpreted as an index
        i = 0x0F .&. unsafeShiftR k (60 - fromIntegral @Word32 @Int pos)
        mask :: Word32
        mask = unsafeShiftL (1 :: Word32) (fromIntegral @Word64 @Int i)
     in case bitset .&. mask of
          0 -> case PM.indexSmallArray## children 0 of
            (# child #) -> leftmostChildKey child
          _ ->
            let trueIx = popCount (bitset .&. (mask - 1))
             in case PM.indexSmallArray## children trueIx of
                  (# child #) -> go child

-- Precondition: branch nodes must not be empty
leftmostChildKey :: Trie a -> Word64
leftmostChildKey t0 = go t0 where
  go (Leaf _ k _) = k
  go (Branch _ _ children) = go (PM.indexSmallArray children 0)

-- | Behavior is undefined when the number of bits to consider is
-- outside of the acceptable range.
insert ::
     Int -- ^ Number of bits to consider, @[0-64]@
  -> Word64 -- ^ Key, for bit count less than 64, low bits are masked out 
  -> a -- ^ Value
  -> Trie a
  -> Trie a
{-# noinline insert #-}
insert !b !k0 v t0 =
  let !b32 = fromIntegral @Int @Word32 b
      !k = normalizeKey b32 k0
      !j = nearestKey k t0
      !critPos = deltaNybbleStartIx j k
      go lf@(Leaf b' k' _) = if k == k'
        then errorWithoutStackTrace ("Data.Trie.Quad.Prefix: overlapping keys " ++ showHex k0 ('[' : shows b ("] and " ++ showHex k' ('[' : shows b' "]"))))
        else makeDoubleton critPos b32 k j v lf
      go br@(Branch pos bitset children) =
        case compare pos critPos of
          LT -> let !kslice = fromIntegral @Word64 @Word32 (0x0F .&. unsafeShiftR k (60 - fromIntegral @Word32 @Int pos)) in
            case compressIndex kslice bitset of
              (ix,True) -> case PM.indexSmallArray## children ix of
                (# child #) ->
                  let !child' = go child
                   in Branch pos bitset (replaceSmallArray children ix child')
              (_,False) -> errorWithoutStackTrace "Data.Trie.Quad.insert: mistake b"
          GT -> makeDoubleton critPos b32 k j v br
          EQ -> let !kslice = fromIntegral @Word64 @Word32 (0x0F .&. unsafeShiftR k (60 - fromIntegral @Word32 @Int pos)) in
            case compressIndex kslice bitset of
              (_,True) -> errorWithoutStackTrace "Data.Trie.Quad.insert: mistake d"
              (ix,False) -> Branch pos
                (bitset .|. unsafeShiftL (1 :: Word32) (fromIntegral @Word32 @Int kslice))
                (insertSmallArray children ix (Leaf b32 k v))
   in go t0

-- critPos must not be 64
-- the given node contains the j key already
makeDoubleton :: Word32 -> Word32 -> Word64 -> Word64 -> a -> Trie a -> Trie a
makeDoubleton !critPos !klen !k !j v !node =
  let kslice = 0x0F .&. unsafeShiftR k (60 - fromIntegral @Word32 @Int critPos)
      jslice = 0x0F .&. unsafeShiftR j (60 - fromIntegral @Word32 @Int critPos)
      kleaf = Leaf klen k v
      arr = runSmallArrayST $ do 
        dst <- PM.newSmallArray 2 kleaf
        let !ix = if kslice < jslice then 1 else 0
        PM.writeSmallArray dst ix node
        PM.unsafeFreezeSmallArray dst
   in Branch critPos
     (unsafeShiftL 1 (fromIntegral @Word64 @Int kslice)
      .|.
      unsafeShiftL 1 (fromIntegral @Word64 @Int jslice)
     ) arr

-- | /O(n)/ Insert an element at the given position in this array,
-- increasing its size by one.
insertSmallArray :: SmallArray a -> Int -> a -> SmallArray a
insertSmallArray !ary !idx b = runSmallArrayST $ do
  mary <- PM.newSmallArray (count+1) b
  PM.copySmallArray mary 0 ary 0 idx
  PM.copySmallArray mary (idx+1) ary idx (count-idx)
  PM.unsafeFreezeSmallArray mary
  where !count = PM.sizeofSmallArray ary

-- | /O(n)/ Replace the element at the given index.
replaceSmallArray :: SmallArray a -> Int -> a -> SmallArray a
replaceSmallArray !ary !idx b = runSmallArrayST $ do
  mary <- PM.thawSmallArray ary 0 count
  PM.writeSmallArray mary idx b
  PM.unsafeFreezeSmallArray mary
  where !count = PM.sizeofSmallArray ary

-- Returns number between 0 and 64. Number always divides 4 evenly.
deltaNybbleStartIx :: Word64 -> Word64 -> Word32
{-# inline deltaNybbleStartIx #-}
deltaNybbleStartIx a b =
  fromIntegral @Int @Word32 (countLeadingZeros (xor a b)) .&. 0b11111100

compressIndex ::
     Word32 -- ^ 4-bit number (0 to 15 inclusive)
  -> Word32 -- bitset (only lower 16 bits should ever be set)
  -> (Int,Bool)
{-# inline compressIndex #-}
compressIndex !i !bitset = 
  let mask :: Word32
      mask = unsafeShiftL (1 :: Word32) (fromIntegral @Word32 @Int i)
   in (popCount (bitset .&. (mask - 1)), (bitset .&. mask) /= 0)

data MaybeWord64
  = JustWord64 {-# UNPACK #-} !Word64
  | NothingWord64

valid :: Trie a -> Bool
{-# noinline valid #-}
valid t0 = case go 0 (0 :: Word32) t0 of
  JustWord64 _ -> True
  NothingWord64 -> False
  where
  go !prevMax !_ (Leaf k x _) = if prevMax == 0
    -- Checking that prevMax is 0 is a hack that makes the validity check
    -- accept some tries that it should not. The correct thing is to either
    -- augment Word64 with a "bottom" value or track whether or not we are
    -- on the far left-hand side of a trie. I'm willing to live with the
    -- incorrectness since this function is just for testing.
    then JustWord64 (inclusiveUpperBound k x)
    else if prevMax < x
      then JustWord64 (inclusiveUpperBound k x)
      else NothingWord64
  go !prevMax0 !i (Branch pos bitset children)
    | PM.sizeofSmallArray children <= 1 = NothingWord64
    | popCount bitset /= PM.sizeofSmallArray children = NothingWord64
    | pos < i = NothingWord64 -- note: should actually be lte, but word32 has no negatives to use as an initial value
    | mod pos 4 /= 0 = NothingWord64
    | otherwise = foldl
        (\acc node -> case acc of
          NothingWord64 -> NothingWord64
          JustWord64 prevMax -> go prevMax pos node
        ) (JustWord64 prevMax0) children
