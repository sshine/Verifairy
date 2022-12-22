{-# LANGUAGE TemplateHaskell #-}

module VerifPal.Version where

import GitHash

gitBuildInfo :: String
gitBuildInfo =
  concat
    [ giBranch gi,
      "@",
      giHash gi,
      dirty,
      " (",
      giCommitDate gi,
      ")"
    ]
  where
    dirty
      | giDirty gi = "~dirty"
      | otherwise = ""
    gi = $$tGitInfoCwd
