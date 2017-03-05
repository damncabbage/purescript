-- @shouldWarnWith UnusedVar
module Main where

f :: forall a. a -> String
f x = "Ignoring x"
