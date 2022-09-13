{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module W65C816S.Addressing where

import Data.Bits
import Optics
import Optics.Operators
import Data.Word
import W65C816S.State
import Foreign (Storable (..), castPtr)
import Data.Binary
import W65C816S.Memory.Class
import Data.Binary.Put
import Data.Binary.Get
import Optics.State.Operators
import Control.Monad.Trans.State

data LongAddress = Long {address :: Word16, bank :: Word8}

instance Storable LongAddress where
  sizeOf _ = 3
  alignment _ = 1
  peek ptr =
    Long <$> peek (castPtr ptr) <*> peekByteOff ptr 2
  poke ptr (Long addr bank) =
    poke (castPtr ptr) addr *> pokeByteOff ptr 2 bank

instance Binary (LE LongAddress) where
  put (LE (Long addr bank)) = do
    putWord16le addr
    putWord8 bank
  get = do
    LE <$> (Long <$> getWord16le <*> getWord8)

instance Semigroup LongAddress where
  (Long address bank) <> (Long address' bank') =
    let new = address + address'
        newbank = bank + bank' + if new < address then
            1
          else
            0
    in Long new newbank

absolute :: (Memory mem, ValueConstraint mem (LE Word16)) => StateT (W65C816S mem) (MemMonad mem) Word16
absolute = do
  res <- currInstr
  pure (res :: Word16)

absoluteIndexedIndirect :: (Memory mem, ValueConstraint mem (LE Word16)) => StateT (W65C816S mem) (MemMonad mem) Word16
absoluteIndexedIndirect = do
  offset :: Word16 <- currInstr
  e <- use #e
  p <- use #p
  address <- if e || testBit p 4
    then do
      xreg <- fromIntegral <$> use #xl
      pure $ offset + xreg
    else do
      xreg <- use #x
      pure $ offset + xreg
  readMem 0 address

absoluteIndexedWithX :: (Memory mem, ValueConstraint mem (LE Word16)) => StateT (W65C816S mem) (MemMonad mem) Word16
absoluteIndexedWithX = do
  offset :: Word16 <- currInstr
  e <- use #e
  p <- use #p
  if e || testBit p 4
    then do
      xreg <- fromIntegral <$> use #xl
      pure $ offset + xreg
    else do
      xreg <- use #x
      pure $ offset + xreg

absoluteIndexedWithY :: (Memory mem, ValueConstraint mem (LE Word16)) => StateT (W65C816S mem) (MemMonad mem) Word16
absoluteIndexedWithY = do
  offset :: Word16 <- currInstr
  e <- use #e
  p <- use #p
  if e || testBit p 4
    then do
      yreg <- fromIntegral <$> use #yl
      pure $ offset + yreg
    else do
      yreg <- use #y
      pure $ offset + yreg

absoluteIndirect :: (Memory mem, ValueConstraint mem (LE Word16), ValueConstraint mem (LE value)) => StateT (W65C816S mem) (MemMonad mem) value
absoluteIndirect = do
  address :: Word16 <- currInstr
  readMem 0 address

absoluteLongIndexedWithX :: (Memory mem, ValueConstraint mem (LE LongAddress)) => StateT (W65C816S mem) (MemMonad mem) LongAddress
absoluteLongIndexedWithX = do
  Long address block <- currInstr
  e <- use #e
  p <- use #p
  if e || testBit p 4
    then do
      x <- use #xl
      pure $ Long (address + x) block
    else do
      x <- use #x
      pure $ Long (address + x) block

absoluteLong :: (Memory mem, ValueConstraint mem (LE LongAddress)) => StateT (W65C816S mem) (MemMonad mem) LongAddress
absoluteLong = do
  a :: LongAddress <- currInstr
  pure a

blockMove :: (Memory mem, ValueConstraint mem (LE Word8)) => Bool -> StateT (W65C816S mem) (MemMonad mem) (LongAddress, LongAddress)
blockMove True = do
  dstbnk <- currInstr
  srcbnk <- currInstr
  x <- #x <<%= (1 +)
  y <- #y <<%= (1 +)
  #c %= subtract 1
  pure (Long x srcbnk, Long y dstbnk)

blockMove False = do
  dstbnk <- currInstr
  srcbnk <- currInstr
  x <- #x <<%= subtract 1
  y <- #y <<%= subtract 1
  #c %= subtract 1
  pure (Long x srcbnk, Long y dstbnk)

directIndexedIndirect :: (Memory mem, ValueConstraint mem (LE Word8), ValueConstraint mem (LE Word16)) => StateT (W65C816S mem) (MemMonad mem) Word16
directIndexedIndirect = do
  address <- directIndexedWithX
  readMem 0 address

directIndexedWithX :: (Memory mem, ValueConstraint mem (LE Word8)) => StateT (W65C816S mem) (MemMonad mem) Word16
directIndexedWithX = do
  offset :: Word8 <- currInstr
  e <- use #e
  p <- use #p
  x <- if e || testBit p 4
    then do
      fromIntegral <$> use #xl
    else do
      use #x
  d <- use #d
  pure $ x + d + fromIntegral offset

directIndexedWithY :: (Memory mem, ValueConstraint mem (LE Word8)) => StateT (W65C816S mem) (MemMonad mem) Word16
directIndexedWithY = do
  offset :: Word8 <- currInstr
  e <- use #e
  p <- use #p
  y <- if e || testBit p 4
    then do
      fromIntegral <$> use #yl
    else do
      use #y
  d <- use #d
  pure $ y + d + fromIntegral offset

directIndirectIndexed :: (Memory mem, ValueConstraint mem (LE Word8), ValueConstraint mem (LE Word16)) => StateT (W65C816S mem) (MemMonad mem) Word16
directIndirectIndexed = do
  offset :: Word8 <- currInstr
  d <- use #d
  e <- use #e
  p <- use #p
  y <- if e || testBit p 4
    then do
      fromIntegral <$> use #yl
    else do
      use #y
  base <- readMem 0 $ d + fromIntegral offset
  pure $ y + base

directIndirectLongIndexed :: (Memory mem, ValueConstraint mem (LE Word8), ValueConstraint mem (LE LongAddress)) => StateT (W65C816S mem) (MemMonad mem) LongAddress
directIndirectLongIndexed = do
  address <- directIndirectLong
  e <- use #e
  p <- use #p
  y <- if e || testBit p 4
    then do
      fromIntegral <$> use #yl
    else do
      fromIntegral <$> use #y
  pure $ address <> Long y 0

directIndirectLong :: (Memory mem, ValueConstraint mem (LE Word8), ValueConstraint mem (LE LongAddress)) => StateT (W65C816S mem) (MemMonad mem) LongAddress
directIndirectLong = do
  offset :: Word8 <- currInstr
  d <- use #d
  readMem 0 (d + fromIntegral offset)

directIndirect :: (Memory mem, ValueConstraint mem (LE Word8), ValueConstraint mem (LE Word16)) => StateT (W65C816S mem) (MemMonad mem) Word16
directIndirect = do
  readMem 0 =<< direct

direct :: (Memory mem, ValueConstraint mem (LE Word8)) => StateT (W65C816S mem) (MemMonad mem) Word16
direct = do
  offset :: Word8 <- currInstr
  d <- use #d
  pure $ d + fromIntegral offset

immediate = currInstr

stackRelative = do
  offset :: Word8 <- currInstr
  s <- use #s
  pure $ s + fromIntegral offset

stackRelativeIndirectIndexed = do
  e <- use #e
  p <- use #p
  y <- if e || testBit p 4
    then do
      fromInteger <$> use #yl
    else do
      use #y
  address <- stackRelative
  dbr <- use #dbr
  pure $ Long y dbr <> Long address 0