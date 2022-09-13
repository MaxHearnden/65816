{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module W65C816S.Interpret where

import Optics (use, assign)
import W65C816S.State
import W65C816S.Memory.Class
import Control.Monad.Trans.State
import Data.Word
import Control.Monad (unless)
import Optics.State.Operators
import Data.Bits
import W65C816S.Addressing

step :: (Memory mem, ValueConstraint mem (LE LongAddress), ValueConstraint mem (LE Word8), ValueConstraint mem (LE Word16)) => StateT (W65C816S mem) (MemMonad mem) ()
step = do
  opcode :: Word8 <- currInstr
  e <- use #e
  p <- use #p
  case opcode of
    0x00 -> do
      -- ^ BRK s
      unless e $ do
        pushLens #pbr
      pushLens #pc
      pushLens #p
      #pbr .= 0
      #p %= (0x8 .&.)
      if e
        then do
          #p %= (0x14 .|.)
          assign #pc =<< readMem 0 0xfffe
        else do
          #p %= (0x4 .|.)
          assign #pc =<< readMem 0 0xffe6
    0x01 -> do
      -- ^ ORA (d,x)
      if e || testBit p 5
        then do
          value <- readMem 0 =<< directIndexedIndirect
          #a %= (value .|.)
        else do
          value <- readMem 0 =<< directIndexedIndirect
          #c %= (value .|.)
    0x02 -> do
      -- ^ COP s
      unless e $ do
        pushLens #pbr
      pushLens #pc
      pushLens #p
      #pbr .= 0
      #p %= (complement 0x8 .&.)
      #p %= (0x4 .|.)
      if e
        then do
          assign #pc =<< readMem 0 0xfff4
        else do
          assign #pc =<< readMem 0 0xffe4
    0x03 -> do
      -- ^ ORA d,s
      if e || testBit p 5
        then do
          value <- readMem 0 =<< stackRelative
          #a %= (value .|.)
        else do
          value <- readMem 0 =<< stackRelative
          #c %= (value .|.)
    0x04 -> do
      -- ^ TSB d
      pure ()


step' :: StateT (W65C816S [Word8]) IO ()
step' = step