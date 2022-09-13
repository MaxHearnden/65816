{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module W65C816S.Memory.Class where

import Data.Binary
import Data.Binary.Get
import Data.Binary.Put
import Data.Word ( Word8 )
import Optics
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as B.L
import Foreign
import Data.ByteString.Lazy.Optics (bytes)
import Data.Functor (($>))
import Data.Kind (Constraint)
import Data.Functor.Identity (Identity)
import GHC.Generics (Generic)

type StorableBinary value = (Storable value, Binary value)

class (Monad (MemMonad mem)) => Memory mem where
  type family ValueConstraint mem value :: Constraint
  type ValueConstraint mem value = StorableBinary value
  type MemMonad mem :: * -> *
  type MemMonad mem = IO
  readByteOff :: ValueConstraint mem value => mem -> Int {- ^Byte Offset -} -> MemMonad mem value
  writeByteOff :: ValueConstraint mem value => mem -> Int {- ^Byte Offset -} -> value -> MemMonad mem mem
  default readByteOff :: (Ixed mem, Is (IxKind mem) An_AffineFold, IxValue mem ~ Word8, Index mem ~ Int, Binary value, MemMonad mem ~ IO) => mem -> Int -> MemMonad mem value
  readByteOff mem off =
    go off $ runGetIncremental get
    where
      go _ (Fail {}) =
        fail "Read error"
      go off (Partial cont) =
        go (succ off) $ cont $ B.singleton <$> (mem ^? ix off)
      go _ (Done _ _ value) =
        pure value
  default writeByteOff :: (Ixed mem, Is (IxKind mem) A_Setter, IxValue mem ~ Word8, Index mem ~ Int, Binary value, MemMonad mem ~ IO) => mem -> Int -> value -> MemMonad mem mem
  writeByteOff mem off (encode -> value) =
    pure $ ifoldlOf' bytes (\(fromIntegral -> index) mem elem ->
      mem & ix (index + off) .~ elem
    ) mem value

instance Memory (Ptr a) where
  readByteOff = peekByteOff
  writeByteOff mem offset value = pokeByteOff mem offset value $> mem

instance Memory [Word8]


-- Little Endian binary instances
newtype LE value = LE {le :: value} deriving (Generic, Storable)

instance Binary (LE Word8)

instance Binary (LE Word16) where
  put = putWord16le . le
  get = LE <$> getWord16le