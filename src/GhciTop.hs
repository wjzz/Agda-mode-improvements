{-# LANGUAGE CPP, TypeSynonymInstances #-}
{-# OPTIONS -fno-cse #-}

module Agda.Interaction.GhciTop
  ( module Agda.Interaction.GhciTop
  , module Agda.TypeChecker
  , module Agda.TypeChecking.MetaVars
  , module Agda.TypeChecking.Reduce
  , module Agda.TypeChecking.Errors

  , module Agda.Syntax.Position
  , module Agda.Syntax.Parser
--  , module SC  -- trivial clash removal: remove all!
--  , module SA
--  , module SI
  , module Agda.Syntax.Scope.Base
  , module Agda.Syntax.Scope.Monad
  , module Agda.Syntax.Translation.ConcreteToAbstract
  , module Agda.Syntax.Translation.AbstractToConcrete
  , module Agda.Syntax.Translation.InternalToAbstract
  , module Agda.Syntax.Abstract.Name

  , module Agda.Interaction.Exceptions

  , mkAbsolute
  )
  where

import System.Directory
import qualified System.IO as IO
import System.IO.Unsafe
import Data.Char
import Data.Maybe
import Data.IORef
import Data.Function
import Control.Applicative

import Agda.Utils.Fresh
import Agda.Utils.Monad
import Agda.Utils.Pretty as P
import Agda.Utils.String
import Agda.Utils.FileName
import qualified Agda.Utils.Trie as Trie
import Agda.Utils.Tuple
import qualified Agda.Utils.IO.Locale as LocIO
import qualified Agda.Utils.IO.UTF8 as UTF8

import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.State hiding (State)
import Control.Exception
import Data.List as List
import qualified Data.Map as Map
import System.Exit
import qualified System.Mem as System
import System.Time
import Text.PrettyPrint

import Agda.TypeChecker
import Agda.TypeChecking.Monad as TM
  hiding (initState, setCommandLineOptions)
import qualified Agda.TypeChecking.Monad as TM
import Agda.TypeChecking.MetaVars
import Agda.TypeChecking.Reduce
import Agda.TypeChecking.Errors
import Agda.TypeChecking.Serialise (encodeFile)

import Agda.Syntax.Position
import Agda.Syntax.Parser
import qualified Agda.Syntax.Parser.Tokens as T
import Agda.Syntax.Concrete as SC
import Agda.Syntax.Common as SCo
import Agda.Syntax.Concrete.Name as CN
import Agda.Syntax.Concrete.Pretty ()
import Agda.Syntax.Abstract as SA
import Agda.Syntax.Abstract.Pretty
import Agda.Syntax.Internal as SI
import Agda.Syntax.Scope.Base
import Agda.Syntax.Scope.Monad hiding (bindName, withCurrentModule)
import qualified Agda.Syntax.Info as Info
import Agda.Syntax.Translation.ConcreteToAbstract
import Agda.Syntax.Translation.AbstractToConcrete hiding (withScope)
import Agda.Syntax.Translation.InternalToAbstract
import Agda.Syntax.Abstract.Name

import Agda.Interaction.Exceptions
import Agda.Interaction.FindFile
import Agda.Interaction.Options
import Agda.Interaction.MakeCase
import qualified Agda.Interaction.BasicOps as B
import qualified Agda.Interaction.CommandLine.CommandLine as CL
import Agda.Interaction.Highlighting.Emacs
import Agda.Interaction.Highlighting.Generate
import qualified Agda.Interaction.Imports as Imp

import Agda.Termination.TermCheck

import qualified Agda.Compiler.Epic.Compiler as Epic
import qualified Agda.Compiler.MAlonzo.Compiler as MAlonzo

import qualified Agda.Auto.Auto as Auto

#include "../undefined.h"
import Agda.Utils.Impossible

data State = State
  { theTCState           :: TCState
  , theInteractionPoints :: [InteractionId]
    -- ^ The interaction points of the buffer, in the order in which
    --   they appear in the buffer. The interaction points are
    --   recorded in 'theTCState', but when new interaction points are
    --   added by give or refine Agda does not ensure that the ranges
    --   of later interaction points are updated.
  , theCurrentFile       :: Maybe (AbsolutePath, ClockTime)
    -- ^ The file which the state applies to. Only stored if the
    -- module was successfully type checked (potentially with
    -- warnings). The 'ClockTime' is the modification time stamp of
    -- the file when it was last loaded.
  }

initState :: State
initState = State
  { theTCState           = TM.initState
  , theInteractionPoints = []
  , theCurrentFile       = Nothing
  }

{-# NOINLINE theState #-}
theState :: IORef State
theState = unsafePerformIO $ newIORef initState

-- | Can the command run even if the relevant file has not been loaded
-- into the state?

data Independence
  = Independent (Maybe [FilePath])
    -- ^ Yes. If the argument is @'Just' is@, then @is@ is used as the
    -- command's include directories.
  | Dependent
    -- No.

-- | An interactive computation.

data Interaction = Interaction
  { independence :: Independence
    -- ^ Is the command independent?
  , command :: TCM (Maybe ModuleName)
    -- ^ If a module name is returned, then syntax highlighting
    -- information will be written for the given module (by 'ioTCM').
  }

-- ^ Is the command independent?

isIndependent :: Interaction -> Bool
isIndependent i = case independence i of
  Independent {} -> True
  Dependent   {} -> False

-- | Run a TCM computation in the current state. Should only
--   be used for debugging.
ioTCM_ :: TCM a -> IO a
ioTCM_ m = do
  tcs <- readIORef theState
  result <- runTCM $ do
    put $ theTCState tcs
    x <- withEnv initEnv m
    s <- get
    return (x, s)
  case result of
    Right (x, s) -> do
      writeIORef theState $ tcs { theTCState = s }
      return x
    Left err -> do
      Right doc <- runTCM $ prettyTCM err
      putStrLn $ render doc
      return $ undefined
{-
  Right (x, s) <- runTCM $ do
    put $ theTCState tcs
    x <- withEnv initEnv m
    s <- get
    return (x, s)
  writeIORef theState $ tcs { theTCState = s }
  return x
-}

-- | Runs a 'TCM' computation. All calls from the Emacs mode should be
-- wrapped in this function.

ioTCM :: FilePath
         -- ^ The current file. If this file does not match
         -- 'theCurrentFile', and the 'Interaction' is not
         -- \"independent\", then an error is raised.
      -> Maybe FilePath
         -- ^ Syntax highlighting information will be written to this
         -- file, if any.
      -> Interaction
      -> IO ()
ioTCM current highlightingFile cmd = infoOnException $ do
-- #if MIN_VERSION_base(4,2,0)
  -- Ensure that UTF-8 is used for communication with the Emacs mode.
  IO.hSetEncoding IO.stdout IO.utf8
-- #endif

  current <- absolute current

  -- Read the state.
  State { theTCState     = st
        , theCurrentFile = f
        } <- readIORef theState

  -- Run the computation.
  r <- runTCM $ catchError (do
           put st
           x  <- withEnv initEnv $ do
                   case independence cmd of
                     Dependent             -> ensureFileLoaded current
                     Independent Nothing   ->
                       -- Make sure that the include directories have
                       -- been set.
                       setCommandLineOptions =<< commandLineOptions
                     Independent (Just is) -> do
                       ex <- liftIO $ doesFileExist $ filePath current
                       setIncludeDirs is $
                         if ex then ProjectRoot current else CurrentDir
                   command cmd
           st <- get
           return (Right (x, st))
         ) (\e -> do
           s <- prettyError e
           return (Left (s, e))
         )

  -- Update the state.
  case r of
    Right (Right (m, st')) ->
      modifyIORef theState $ \s ->
        s { theTCState   = st'
          }
    _ | isIndependent cmd ->
      modifyIORef theState $ \s ->
        s { theCurrentFile = Nothing }
    _ -> return ()

  -- Write out syntax highlighting info.
  case highlightingFile of
    Nothing -> return ()
    Just f  -> do
      let errHi e s = errHighlighting e
                        `mplus`
                      ((\h -> (h, Map.empty)) <$>
                           generateErrorInfo (getRange e) s)
      UTF8.writeFile f $
        showHighlightingInfo $
          case r of
            Right (Right (mm, st')) -> do
              m  <- mm
              mi <- Map.lookup (SA.toTopLevelModuleName m)
                               (stVisitedModules st')
              return ( iHighlighting $ miInterface mi
                     , stModuleToSource st'
                     )
            Right (Left (s, e)) -> errHi e (Just s)
            Left e              -> errHi e Nothing

  -- If an error was encountered, display an error message and exit
  -- with an error code; otherwise, inform Emacs about the buffer's
  -- goals (if current matches the new current file).
  let errStatus = Status { sChecked               = False
                         , sShowImplicitArguments =
                             optShowImplicit $ stPragmaOptions st
                         }
  case r of
    Right (Left (s, e)) -> displayErrorAndExit errStatus (getRange e) s
    Left e              -> displayErrorAndExit errStatus (getRange e) $
                             tcErrString e
    Right (Right _)     -> do
      f <- theCurrentFile <$> readIORef theState
      case f of
        Just (f, _) | f === current -> do
          is <- theInteractionPoints <$> liftIO (readIORef theState)
          liftIO $ LocIO.putStrLn $ response $
            L [A "agda2-goals-action", Q $ L $ List.map showNumIId is]
        _ -> return ()

-- | @cmd_load m includes@ loads the module in file @m@, using
-- @includes@ as the include directories.

cmd_load :: FilePath -> [FilePath] -> Interaction
cmd_load m includes =
  cmd_load' m includes True (\_ -> command cmd_metas >> return ())

-- | @cmd_load' m includes cmd cmd2@ loads the module in file @m@,
-- using @includes@ as the include directories.
--
-- If type checking completes without any exceptions having been
-- encountered then the command @cmd r@ is executed, where @r@ is the
-- result of 'Imp.typeCheck'.

cmd_load' :: FilePath -> [FilePath]
          -> Bool -- ^ Allow unsolved meta-variables?
          -> ((Interface, Maybe Imp.Warnings) -> TCM ())
          -> Interaction
cmd_load' file includes unsolvedOK cmd =
  Interaction (Independent (Just includes)) $ do
    -- Forget the previous "current file" and interaction points.
    liftIO $ modifyIORef theState $ \s ->
      s { theInteractionPoints = []
        , theCurrentFile       = Nothing
        }

    f <- liftIO $ absolute file
    t <- liftIO $ getModificationTime file

    -- All options (except for the verbosity setting) are reset when a
    -- file is reloaded, including the choice of whether or not to
    -- display implicit arguments. (At this point the include
    -- directories have already been reset, so they are preserved.)
    opts <- commandLineOptions
    setCommandLineOptions $
      defaultOptions { optIncludeDirs   = optIncludeDirs opts
                     , optPragmaOptions =
                         (optPragmaOptions defaultOptions)
                           { optAllowUnsolved = unsolvedOK
                           , optVerbose       = optVerbose (optPragmaOptions opts)
                           }
                     }

    -- Reset the state, preserving options and decoded modules. Note
    -- that Imp.typeCheck resets the decoded modules if the include
    -- directories have changed.
    preserveDecodedModules resetState

    ok <- Imp.typeCheck f

    -- The module type checked. If the file was not changed while the
    -- type checker was running then the interaction points and the
    -- "current file" are stored.
    t' <- liftIO $ getModificationTime file
    when (t == t') $ do
      is <- sortInteractionPoints =<< getInteractionPoints
      liftIO $ modifyIORef theState $ \s ->
        s { theInteractionPoints = is
          , theCurrentFile       = Just (f, t)
          }

    cmd ok

    liftIO System.performGC

    return $ Just $ iModuleName (fst ok)

-- | Available backends.

data Backend = MAlonzo | Epic

-- | @cmd_compile b m includes@ compiles the module in file @m@ using
-- the backend @b@, using @includes@ as the include directories.

cmd_compile :: Backend -> FilePath -> [FilePath] -> Interaction
cmd_compile b file includes =
  cmd_load' file includes False (\(i, mw) ->
    case mw of
      Nothing -> do
        case b of
          MAlonzo -> MAlonzo.compilerMain i
          Epic    -> Epic.compilerMain i
        display_info "*Compilation result*"
                     "The module was successfully compiled."
      Just w ->
        display_info errorTitle $ unlines
          [ "You can only compile modules without unsolved metavariables"
          , "or termination checking problems."
          ])

cmd_constraints :: Interaction
cmd_constraints = Interaction Dependent $ do
    cs <- map show <$> B.getConstraints
    display_info "*Constraints*" (unlines cs)
    return Nothing

-- Show unsolved metas. If there are no unsolved metas but unsolved constraints
-- show those instead.
cmd_metas :: Interaction
cmd_metas = Interaction Dependent $ do -- CL.showMetas []
  ims <- B.typesOfVisibleMetas B.AsIs
  -- Show unsolved implicit arguments normalised.
  hms <- B.typesOfHiddenMetas B.Normalised
  if not $ null ims && null hms
    then do
      di <- mapM (\i -> B.withInteractionId (B.outputFormId i) (showATop i)) ims
      dh <- mapM showA' hms
      display_info "*All Goals*" $ unlines $ di ++ dh
      return Nothing
    else do
      cs <- B.getConstraints
      if null cs
        then display_info "*All Goals*" "" >> return Nothing
        else command cmd_constraints
  where
    metaId (B.OfType i _) = i
    metaId (B.JustType i) = i
    metaId (B.JustSort i) = i
    metaId (B.Assign i e) = i
    metaId _ = __IMPOSSIBLE__
    showA' m = do
      r <- getMetaRange (metaId m)
      d <- B.withMetaId (B.outputFormId m) (showATop m)
      return $ d ++ "  [ at " ++ show r ++ " ]"

-- | If the range is 'noRange', then the string comes from the
-- minibuffer rather than the goal.

type GoalCommand = InteractionId -> Range -> String -> Interaction

cmd_give :: GoalCommand
cmd_give = give_gen B.give $ \rng s ce ->
  case ce of
    ce | rng == noRange -> quote (show ce)
    SC.Paren _ _ -> "'paren"
    _            -> "'no-paren"

cmd_refine :: GoalCommand
cmd_refine = give_gen B.refine $ \_ s -> quote . show

give_gen give_ref mk_newtxt ii rng s = Interaction Dependent $
  give_gen' give_ref mk_newtxt ii rng s

give_gen' give_ref mk_newtxt ii rng s = do
  scope     <- getInteractionScope ii
  (ae, iis) <- give_ref ii Nothing =<< B.parseExprIn ii rng s
  let newtxt = A . mk_newtxt rng s $ abstractToConcrete (makeEnv scope) ae
  iis       <- sortInteractionPoints iis
  liftIO $ modifyIORef theState $ \s ->
             s { theInteractionPoints =
                   replace ii iis (theInteractionPoints s) }
  liftIO $ LocIO.putStrLn $ response $
             L [A "agda2-give-action", showNumIId ii, newtxt]
  command cmd_metas
  return Nothing
  where
  -- Substitutes xs for x in ys.
  replace x xs ys = concatMap (\y -> if y == x then xs else [y]) ys

cmd_intro :: GoalCommand
cmd_intro ii rng _ = Interaction Dependent $ do
  ss <- B.introTactic ii
  B.withInteractionId ii $ case ss of
    []    -> do
      display_infoD "*Intro*" $ text "No introduction forms found."
      return Nothing
    [s]   -> command $ cmd_refine ii rng s
    _:_:_ -> do
      display_infoD "*Intro*" $
        sep [ text "Don't know which constructor to introduce of"
            , let mkOr []     = []
                  mkOr [x, y] = [text x <+> text "or" <+> text y]
                  mkOr (x:xs) = text x : mkOr xs
              in nest 2 $ fsep $ punctuate comma (mkOr ss)
            ]
      return Nothing

cmd_refine_or_intro :: GoalCommand
cmd_refine_or_intro ii rng s =
  (if null s then cmd_intro else cmd_refine) ii rng s

cmd_auto :: GoalCommand
cmd_auto ii rng s = Interaction Dependent $ do
  (res, msg) <- Auto.auto ii rng s
  case res of
   Left xs -> do
    mapM_ (\(ii, s) -> do
      liftIO $ modifyIORef theState $ \s ->
        s { theInteractionPoints = filter (/= ii) (theInteractionPoints s) }
      liftIO $ LocIO.putStrLn $ response $ L [A "agda2-give-action", showNumIId ii, A $ quote s]
     ) xs
    case msg of
     Nothing -> command cmd_metas >> return ()
     Just msg -> display_info "*Auto*" msg
    return Nothing
   Right (Left cs) -> do
    case msg of
     Nothing -> return ()
     Just msg -> display_info "*Auto*" msg
    liftIO $ LocIO.putStrLn $ response $
     Cons (A "last")
          (L [ A "agda2-make-case-action",
               Q $ L $ List.map (A . quote) cs
             ])
    return Nothing
   Right (Right s) -> give_gen' B.refine (\_ s -> quote . show) ii rng s

-- | Sorts interaction points based on their ranges.

sortInteractionPoints :: [InteractionId] -> TCM [InteractionId]
sortInteractionPoints is =
  map fst . sortBy (compare `on` snd) <$>
    mapM (\i -> (,) i <$> getInteractionRange i) is

-- | Pretty-prints the type of the meta-variable.

prettyTypeOfMeta :: B.Rewrite -> InteractionId -> TCM Doc
prettyTypeOfMeta norm ii = do
  form <- B.typeOfMeta norm ii
  case form of
    B.OfType _ e -> prettyATop e
    _            -> text <$> showATop form

-- | Pretty-prints the context of the given meta-variable.

prettyContext
  :: B.Rewrite      -- ^ Normalise?
  -> Bool           -- ^ Print the elements in reverse order?
  -> InteractionId
  -> TCM Doc
prettyContext norm rev ii = B.withInteractionId ii $ do
  ctx <- B.contextOfMeta ii norm
  es  <- mapM (prettyATop . B.ofExpr) ctx
  ns  <- mapM (showATop   . B.ofName) ctx
  let shuffle = if rev then reverse else id
  return $ align 10 $ shuffle $ zip ns (map (text ":" <+>) es)

cmd_context :: B.Rewrite -> GoalCommand
cmd_context norm ii _ _ = Interaction Dependent $ do
  display_infoD "*Context*" =<< prettyContext norm False ii
  return Nothing

cmd_infer :: B.Rewrite -> GoalCommand
cmd_infer norm ii rng s = Interaction Dependent $ do
  display_infoD "*Inferred Type*"
    =<< B.withInteractionId ii
          (prettyATop =<< B.typeInMeta ii norm =<< B.parseExprIn ii rng s)
  return Nothing

-- <wjzz>
  
getTypeString norm s = B.atTopLevel ((liftIO $ parse exprParser s) >>= concreteToAbstract_  
                       >>= (B.typeInCurrent norm) >>= showA)

buildOutputString :: [String] -> [[String]] -> [[String]] -> String
buildOutputString dbNames lemmaNames lemmaTypes = unlines $ map showData fullData where
  lemmas :: [[(String, String)]]
  lemmas = zipWith zip lemmaNames lemmaTypes
  
  fullData :: [(String, [(String, String)])]
  fullData = zip dbNames lemmas
  
  showData :: (String, [(String, String)]) -> String
  showData (dbName, lemmas) = dbName ++ ":\n" ++ (unlines $ map showLemma lemmas)
  
  showLemma :: (String, String) -> String
  showLemma (lname, ltype) = "  " ++ lname ++ ":\n    " ++ ltype

cmd_infer_db_contents :: B.Rewrite -> String -> Interaction
cmd_infer_db_contents norm s = Interaction Dependent $ do
  let parts  = read s :: [[String]]
  let dbs    = concatMap (\l -> if null l then [] else [head l]) parts
  let lemmas = map (\l -> if null l then [] else tail l) parts
  
  -- parse all lemmas
  typesStr <- mapM (mapM (getTypeString norm)) lemmas :: TCM [[String]]
  
  let types = buildOutputString dbs lemmas typesStr
  
  display_info "*DB contents verbose*" types

  return Nothing

-- </wjzz>

cmd_goal_type :: B.Rewrite -> GoalCommand
cmd_goal_type norm ii _ _ = Interaction Dependent $ do
  s <- B.withInteractionId ii $ prettyTypeOfMeta norm ii
  display_infoD "*Current Goal*" s
  return Nothing

-- | Displays the current goal, the given document, and the current
-- context.

cmd_goal_type_context_and doc norm ii _ _ = do
  goal <- B.withInteractionId ii $ prettyTypeOfMeta norm ii
  ctx  <- prettyContext norm True ii
  display_infoD "*Goal type etc.*"
                (text "Goal:" <+> goal $+$
                 doc $+$
                 text (replicate 60 '\x2014') $+$
                 ctx)
  return Nothing

-- | Displays the current goal and context.

cmd_goal_type_context :: B.Rewrite -> GoalCommand
cmd_goal_type_context norm ii rng s = Interaction Dependent $
  cmd_goal_type_context_and P.empty norm ii rng s

-- | Displays the current goal and context /and/ infers the type of an
-- expression.

cmd_goal_type_context_infer :: B.Rewrite -> GoalCommand
cmd_goal_type_context_infer norm ii rng s =
  Interaction Dependent $ do
    typ <- B.withInteractionId ii $
             prettyATop =<< B.typeInMeta ii norm =<< B.parseExprIn ii rng s
    cmd_goal_type_context_and (text "Have:" <+> typ) norm ii rng s

-- | Shows all the top-level names in the given module, along with
-- their types.

showModuleContents :: Range -> String -> TCM ()
showModuleContents rng s = do
  (modules, types) <- B.moduleContents rng s
  types' <- mapM (\(x, t) -> do
                    t <- prettyTCM t
                    return (show x, text ":" <+> t))
                 types
  display_infoD "*Module contents*" $
    text "Modules" $$
    nest 2 (vcat $ map (text . show) modules) $$
    text "Names" $$
    nest 2 (align 10 types')

-- | Shows all the top-level names in the given module, along with
-- their types. Uses the scope of the given goal.

cmd_show_module_contents :: GoalCommand
cmd_show_module_contents ii rng s = Interaction Dependent $ do
  B.withInteractionId ii $ showModuleContents rng s
  return Nothing

-- | Shows all the top-level names in the given module, along with
-- their types. Uses the top-level scope.

cmd_show_module_contents_toplevel :: String -> Interaction
cmd_show_module_contents_toplevel s = Interaction Dependent $ do
  B.atTopLevel $ showModuleContents noRange s
  return Nothing

-- | Sets the command line options and updates the status information.

setCommandLineOptions :: CommandLineOptions -> TCM ()
setCommandLineOptions opts = do
  TM.setCommandLineOptions opts
  liftIO . displayStatus =<< status

-- | Status information.

data Status = Status
  { sShowImplicitArguments :: Bool
    -- ^ Are implicit arguments displayed?
  , sChecked               :: Bool
    -- ^ Has the module been successfully type checked?
  }

-- | Computes some status information.

status :: TCM Status
status = do
  showImpl <- showImplicitArguments

  -- Check if the file was successfully type checked, and has not
  -- changed since. Note: This code does not check if any dependencies
  -- have changed, and uses a time stamp to check for changes.
  cur      <- theCurrentFile <$> liftIO (readIORef theState)
  checked  <- case cur of
    Nothing     -> return False
    Just (f, t) -> do
      t' <- liftIO $ getModificationTime $ filePath f
      case t == t' of
        False -> return False
        True  ->
          not . miWarnings . maybe __IMPOSSIBLE__ id <$>
            (getVisitedModule =<<
               maybe __IMPOSSIBLE__ id .
                 Map.lookup f <$> sourceToModule)

  return $ Status { sShowImplicitArguments = showImpl
                  , sChecked               = checked
                  }

-- | Shows status information.

showStatus :: Status -> String
showStatus s = intercalate "," $ catMaybes [checked, showImpl]
  where
  boolToMaybe b x = if b then Just x else Nothing

  checked  = boolToMaybe (sChecked               s) "Checked"
  showImpl = boolToMaybe (sShowImplicitArguments s) "ShowImplicit"

-- | Displays\/updates status information.

displayStatus :: Status -> IO ()
displayStatus s =
  LocIO.putStrLn $ response $
    L [A "agda2-status-action", A (quote $ showStatus s)]

-- | @display_info' header content@ displays @content@ (with header
-- @header@) in some suitable way.

display_info' :: String -> String -> IO ()
display_info' bufname content =
  LocIO.putStrLn $ response $
    L [ A "agda2-info-action"
      , A (quote bufname)
      , A (quote content)
      ]

-- | @display_info@ does what 'display_info'' does, but additionally
-- displays some status information (see 'status' and
-- 'displayStatus').

display_info :: String -> String -> TCM ()
display_info bufname content = do
  liftIO . displayStatus =<< status
  liftIO $ display_info' bufname content

-- | Like 'display_info', but takes a 'Doc' instead of a 'String'.

display_infoD :: String -> Doc -> TCM ()
display_infoD bufname content = display_info bufname (render content)

-- | Formats a response command.

response :: Lisp String -> String
response l = show (text "agda2_mode_code" <+> pretty l)

data Lisp a = A a | L [Lisp a] | Q (Lisp a) | Cons (Lisp a) (Lisp a)

instance Pretty a => Pretty (Lisp a) where
  pretty (A a )     = pretty a
  pretty (L xs)     = parens (sep (List.map pretty xs))
  pretty (Q x)      = text "'" <> pretty x
  pretty (Cons a b) = parens (pretty a <+> text "." <+> pretty b)

instance Pretty String where pretty = text

instance Pretty a => Show (Lisp a) where show = show . pretty

showNumIId = A . tail . show

takenNameStr :: TCM [String]
takenNameStr = do
  xss <- sequence [ List.map (fst . unArg) <$> getContext
                  , Map.keys <$> asks envLetBindings
                  , List.map qnameName . Map.keys . sigDefinitions <$> getSignature
		  ]
  return $ concat [ parts $ nameConcrete x | x <- concat xss]
  where
    parts x = [ s | Id s <- nameParts x ]

refreshStr :: [String] -> String -> ([String], String)
refreshStr taken s = go nameModifiers where
  go (m:mods) = let s' = s ++ m in
                if s' `elem` taken then go mods else (s':taken, s')
  go _        = __IMPOSSIBLE__

nameModifiers = "" : "'" : "''" : [show i | i <-[3..]]

cmd_make_case :: GoalCommand
cmd_make_case ii rng s = Interaction Dependent $ do
  cs <- makeCase ii rng s
  B.withInteractionId ii $ do
    pcs <- mapM prettyA cs
    liftIO $ LocIO.putStrLn $ response $
      Cons (A "last")
           (L [ A "agda2-make-case-action"
              , Q $ L $ List.map (A . quote . render) pcs
              ])
  return Nothing
  where render = renderStyle (style { mode = OneLineMode })

cmd_solveAll :: Interaction
cmd_solveAll = Interaction Dependent $ do
  out <- getInsts
  liftIO $ LocIO.putStrLn $ response $
    Cons (A "last")
         (L [ A "agda2-solveAll-action"
            , Q . L $ concatMap prn out
            ])
  return Nothing
  where
  getInsts = mapM lowr =<< B.getSolvedInteractionPoints
    where
      lowr (i, m, e) = do
        mi <- getMetaInfo <$> lookupMeta m
        e <- withMetaInfo mi $ lowerMeta <$> abstractToConcrete_ e
        return (i, e)
  prn (ii,e)= [showNumIId ii, A $ quote $ show e]

class LowerMeta a where lowerMeta :: a -> a
instance LowerMeta SC.Expr where
  lowerMeta = go where
    go e = case e of
      Ident _              -> e
      SC.Lit _             -> e
      SC.QuestionMark _ _  -> preMeta
      SC.Underscore _ _    -> preUscore
      SC.App r e1 ae2      -> case appView e of
        SC.AppView (SC.QuestionMark _ _) _ -> preMeta
        SC.AppView (SC.Underscore   _ _) _ -> preUscore
        _ -> SC.App r (go e1) (lowerMeta ae2)
      SC.WithApp r e es	   -> SC.WithApp r (lowerMeta e) (lowerMeta es)
      SC.Lam r bs e1       -> SC.Lam r (lowerMeta bs) (go e1)
      SC.AbsurdLam r h     -> SC.AbsurdLam r h
      SC.Fun r ae1 e2      -> SC.Fun r (lowerMeta ae1) (go e2)
      SC.Pi tb e1          -> SC.Pi (lowerMeta tb) (go e1)
      SC.Set _             -> e
      SC.Prop _            -> e
      SC.SetN _ _          -> e
      SC.ETel tel          -> SC.ETel (lowerMeta tel)
      SC.Let r ds e1       -> SC.Let r (lowerMeta ds) (go e1)
      Paren r e1           -> case go e1 of
        q@(SC.QuestionMark _ Nothing) -> q
        e2                            -> Paren r e2
      Absurd _          -> e
      As r n e1         -> As r n (go e1)
      SC.Dot r e	-> SC.Dot r (go e)
      SC.RawApp r es	-> SC.RawApp r (lowerMeta es)
      SC.OpApp r x es	-> SC.OpApp r x (lowerMeta es)
      SC.Rec r fs	-> SC.Rec r (List.map (id -*- lowerMeta) fs)
      SC.HiddenArg r e	-> SC.HiddenArg r (lowerMeta e)
      SC.QuoteGoal r x e  -> SC.QuoteGoal r x (lowerMeta e)
      SC.Quote r        -> SC.Quote r

instance LowerMeta SC.LamBinding where
  lowerMeta b@(SC.DomainFree _ _) = b
  lowerMeta (SC.DomainFull tb)    = SC.DomainFull (lowerMeta tb)

instance LowerMeta SC.TypedBindings where
  lowerMeta (SC.TypedBindings r bs) = SC.TypedBindings r (lowerMeta bs)

instance LowerMeta SC.TypedBinding where
  lowerMeta (SC.TBind r ns e) = SC.TBind r ns (lowerMeta e)
  lowerMeta (SC.TNoBind e)    = SC.TNoBind (lowerMeta e)

instance LowerMeta SC.RHS where
    lowerMeta (SC.RHS e)    = SC.RHS (lowerMeta e)
    lowerMeta  SC.AbsurdRHS = SC.AbsurdRHS

instance LowerMeta SC.Declaration where
  lowerMeta = go where
    go d = case d of
      TypeSig rel n e1              -> TypeSig rel n (lowerMeta e1)
      SC.Field n e1                 -> SC.Field n (lowerMeta e1)
      FunClause lhs rhs whcl        -> FunClause lhs (lowerMeta rhs) (lowerMeta whcl)
      Data r ind n tel e1 cs        -> Data r ind n
                                         (lowerMeta tel) (lowerMeta e1) (lowerMeta cs)
      SC.Record r n c tel e1 cs     -> SC.Record r n c
                                         (lowerMeta tel) (lowerMeta e1) (lowerMeta cs)
      Infix _ _                     -> d
      Syntax _ _                     -> d
      Mutual r ds                   -> Mutual r (lowerMeta ds)
      Abstract r ds                 -> Abstract r (lowerMeta ds)
      Private r ds                  -> Private r (lowerMeta ds)
      Postulate r sigs              -> Postulate r (lowerMeta sigs)
      SC.Primitive r sigs           -> SC.Primitive r (lowerMeta sigs)
      SC.Open _ _ _                 -> d
      SC.Import _ _ _ _ _           -> d
      SC.Pragma _                   -> d
      ModuleMacro r n tel e1 op dir -> ModuleMacro r n
                                         (lowerMeta tel) (lowerMeta e1) op dir
      SC.Module r qn tel ds         -> SC.Module r qn (lowerMeta tel) (lowerMeta ds)

instance LowerMeta SC.WhereClause where
  lowerMeta SC.NoWhere		= SC.NoWhere
  lowerMeta (SC.AnyWhere ds)	= SC.AnyWhere $ lowerMeta ds
  lowerMeta (SC.SomeWhere m ds) = SC.SomeWhere m $ lowerMeta ds

instance LowerMeta a => LowerMeta [a] where
  lowerMeta as = List.map lowerMeta as

instance LowerMeta a => LowerMeta (Arg a) where
  lowerMeta aa = fmap lowerMeta aa

instance LowerMeta a => LowerMeta (Named name a) where
  lowerMeta aa = fmap lowerMeta aa


preMeta   = SC.QuestionMark noRange Nothing
preUscore = SC.Underscore   noRange Nothing

cmd_compute :: Bool -- ^ Ignore abstract?
               -> GoalCommand
cmd_compute ignore ii rng s = Interaction Dependent $ do
  e <- B.parseExprIn ii rng s
  d <- B.withInteractionId ii $ do
         let c = B.evalInCurrent e
         v <- if ignore then ignoreAbstractMode c else c
         prettyATop v
  display_info "*Normal Form*" (show d)
  return Nothing

-- | Parses and scope checks an expression (using the \"inside scope\"
-- as the scope), performs the given command with the expression as
-- input, and displays the result.

parseAndDoAtToplevel
  :: (SA.Expr -> TCM SA.Expr)
     -- ^ The command to perform.
  -> String
     -- ^ The name to use for the buffer displaying the output.
  -> String
     -- ^ The expression to parse.
  -> Interaction
parseAndDoAtToplevel cmd title s = Interaction Dependent $ do
  e <- liftIO $ parse exprParser s
  display_info title =<<
    B.atTopLevel (showA =<< cmd =<< concreteToAbstract_ e)
  return Nothing

-- | Parse the given expression (as if it were defined at the
-- top-level of the current module) and infer its type.

cmd_infer_toplevel
  :: B.Rewrite  -- ^ Normalise the type?
  -> String
  -> Interaction
cmd_infer_toplevel norm =
  parseAndDoAtToplevel (B.typeInCurrent norm) "*Inferred Type*"

-- | Parse and type check the given expression (as if it were defined
-- at the top-level of the current module) and normalise it.

cmd_compute_toplevel :: Bool -- ^ Ignore abstract?
                     -> String -> Interaction
cmd_compute_toplevel ignore =
  parseAndDoAtToplevel (if ignore then ignoreAbstractMode . c
                                  else inConcreteMode . c)
                       "*Normal Form*"
  where c = B.evalInCurrent

------------------------------------------------------------------------
-- Syntax highlighting

-- | @cmd_write_highlighting_info source target@ writes syntax
-- highlighting information for the module in @source@ into @target@.
--
-- If the module does not exist, or its module name is malformed or
-- cannot be determined, or the module has not already been visited,
-- or the cached info is out of date, then the representation of \"no
-- highlighting information available\" is instead written to
-- @target@.
--
-- This command is used to load syntax highlighting information when a
-- new file is opened, and it would probably be annoying if jumping to
-- the definition of an identifier reset the proof state, so this
-- command tries not to do that. One result of this is that the
-- command uses the current include directories, whatever they happen
-- to be.

cmd_write_highlighting_info :: FilePath -> FilePath -> Interaction
cmd_write_highlighting_info source target =
  Interaction (Independent Nothing) $ do
    liftIO . UTF8.writeFile target . showHighlightingInfo =<< do
      ex <- liftIO $ doesFileExist source
      case ex of
        False -> return Nothing
        True  -> do
          mmi <- (getVisitedModule =<<
                    moduleName =<< liftIO (absolute source))
                   `catchError`
                 \_ -> return Nothing
          case mmi of
            Nothing -> return Nothing
            Just mi -> do
              sourceT <- liftIO $ getModificationTime source
              if sourceT <= miTimeStamp mi
               then do
                modFile <- stModuleToSource <$> get
                return $ Just (iHighlighting $ miInterface mi, modFile)
               else
                return Nothing
    return Nothing

-- | Tells the Emacs mode to go to the first error position (if any).

tellEmacsToJumpToError :: Range -> IO ()
tellEmacsToJumpToError r = do
  case rStart r of
    Nothing                                    -> return ()
    Just (Pn { srcFile = Nothing })            -> return ()
    Just (Pn { srcFile = Just f, posPos = p }) ->
      LocIO.putStrLn $ response $
        L [ A "annotation-goto"
          , Q $ L [A (quote $ filePath f), A ".", A (show p)]
          ]

------------------------------------------------------------------------
-- Implicit arguments

-- | Tells Agda whether or not to show implicit arguments.

showImplicitArgs :: Bool -- ^ Show them?
                 -> Interaction
showImplicitArgs showImpl = Interaction Dependent $ do
  opts <- commandLineOptions
  setCommandLineOptions $
    opts { optPragmaOptions =
             (optPragmaOptions opts) { optShowImplicit = showImpl } }
  return Nothing

-- | Toggle display of implicit arguments.

toggleImplicitArgs :: Interaction
toggleImplicitArgs = Interaction Dependent $ do
  opts <- commandLineOptions
  let ps = optPragmaOptions opts
  setCommandLineOptions $
    opts { optPragmaOptions =
             ps { optShowImplicit = not $ optShowImplicit ps } }
  return Nothing

------------------------------------------------------------------------
-- Error handling

-- | When an error message is displayed the following title should be
-- used, if appropriate.

errorTitle :: String
errorTitle = "*Error*"

-- | Displays an error, instructs Emacs to jump to the site of the
-- error, and terminates the program. Because this function may switch
-- the focus to another file the status information is also updated.

displayErrorAndExit :: Status
                       -- ^ The new status information.
                    -> Range -> String -> IO a
displayErrorAndExit status r s = do
  display_info' errorTitle s
  tellEmacsToJumpToError r
  displayStatus status
  exitWith (ExitFailure 1)

-- | Outermost error handler.

infoOnException m =
  failOnException (displayErrorAndExit s) m `catchImpossible` \e ->
    displayErrorAndExit s noRange (show e)
  where
  s = Status { sChecked               = False
             , sShowImplicitArguments = False
               -- Educated guess... This field is not important, so it
               -- does not really matter if it is displayed
               -- incorrectly when an unexpected error has occurred.
             }

-- | Raises an error if the given file is not the one currently
-- loaded.

ensureFileLoaded :: AbsolutePath -> TCM ()
ensureFileLoaded current = do
  f <- theCurrentFile <$> liftIO (readIORef theState)
  when (Just current /= (fst <$> f)) $
    typeError $ GenericError "Error: First load the file."

-- Helpers for testing ----------------------------------------------------

getCurrentFile :: IO FilePath
getCurrentFile = do
  mf <- theCurrentFile <$> readIORef theState
  case mf of
    Nothing     -> error "command: No file loaded!"
    Just (f, _) -> return (filePath f)

-- | Changes the 'Interaction' so that its first action is to turn off
-- all debug messages.

makeSilent :: Interaction -> Interaction
makeSilent i = i { command = do
  opts <- commandLineOptions
  TM.setCommandLineOptions $ opts
    { optPragmaOptions =
        (optPragmaOptions opts)
          { optVerbose = Trie.singleton [] 0 }
    }
  command i }

top_command' :: FilePath -> Interaction -> IO ()
top_command' f cmd = ioTCM f Nothing $ makeSilent cmd

goal_command :: InteractionId -> GoalCommand -> String -> IO ()
goal_command i cmd s = do
  f <- getCurrentFile
  -- TODO: Test with other ranges as well.
  ioTCM f Nothing $ makeSilent $ cmd i noRange s
