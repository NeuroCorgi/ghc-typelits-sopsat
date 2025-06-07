{-# LANGUAGE CPP                   #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TupleSections         #-}
module GHC.TypeLits.SoPSat
  (plugin)
where

import Control.Arrow (second)
import Control.Monad (forM)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.Writer.Strict (Writer, runWriter, tell)

import Data.IORef (IORef, newIORef, readIORef, modifyIORef, modifyIORef')
import Data.Set (Set, union, fromList)
import qualified Data.Set as S (empty, notMember)
import Data.List (intersect, partition, find)
import Data.Maybe (mapMaybe, fromMaybe, isJust, catMaybes)
import Data.Functor ((<&>))
import Data.Function (on)

import GHC.Builtin.Names (eqTyConKey, heqTyConKey, hasKey, knownNatClassName)
import GHC.Builtin.Types
  ( promotedTrueDataCon, promotedFalseDataCon, cTupleTyCon, naturalTy
  , cTupleDataCon
  )
import GHC.Builtin.Types.Literals
  ( typeNatAddTyCon, typeNatSubTyCon, typeNatExpTyCon, typeNatCmpTyCon
  , typeNatMulTyCon
  )
import GHC.Core.DataCon (dataConWrapId)
import GHC.Core.Predicate (isEqPrimPred, mkPrimEqPred, getClassPredTys_maybe)
#if MIN_VERSION_ghc(9,6,0)
import GHC.Core.Type (coreView)
import GHC.Core.TyCo.Compare (nonDetCmpTc)
#else
import GHC.Core.Type (typeKind, coreView, mkNumLitTy, nonDetCmpTc)
#endif
import GHC.Core.TyCo.Rep (Type(TyConApp, TyVarTy, LitTy), TyLit (NumTyLit))
import GHC.Driver.Plugins (Plugin(..), defaultPlugin, purePlugin)
import GHC.Plugins (IsOutput(..))
import GHC.Tc.Types.Constraint
  (CtEvidence (..), ctLocSpan, setCtEvLoc, setCtLocSpan, emptyRewriterSet)
import GHC.TcPlugin.API
  ( TcPlugin(..), TcPluginStage(..), TcPluginSolveResult(..), TcEvDest(..)
  , TcPluginM, Pred(..), EqRel(..), Role(..), EvTerm(..), Expr(Coercion)
  , Kind, PredType, TyCon, TyVar, CtLoc, Ct, EvTerm, Outputable
  , mkTcPlugin, mkPluginUnivCo, mkModuleName, mkTcOcc, mkNumLitTy
  , mkTyConApp, mkTyVarTy, mkNonCanonical, tcLookupTyCon, tcPluginTrace
  , ctLoc, ctEvPred, ctEvidence, ctEvExpr, ctEvLoc, evId, evCast, newEvVar
  , newGiven, newWanted, isEqPred, isGiven, classifyPredType, typeKind
  ,  className, eqType, nonDetCmpType, tyConAppTyCon_maybe, fsLit
  , emptyUFM, ppr
  )
import GHC.TcPlugin.API.Internal (liftTcPluginM)
import GHC.TcPluginM.Extra (lookupModule, lookupName)
import GHC.Utils.Outputable (showPprUnsafe, (<+>), ($$), text)

import SoPSat.Satisfier (SolverState, evalStatements,  declare, assert, unify)
import SoPSat.SoP (SoPE(..), OrdRel(..), (|+|), (|-|), (|*|), (|^|))
import qualified SoPSat.SoP as SoP (cons, func, int)
import SoPSat.Internal.SoP (SoP (..), Product (..), Symbol (..), Atom (..))

isEqPredClass :: PredType -> Bool
isEqPredClass ty = case tyConAppTyCon_maybe ty of
  Just tc -> tc `hasKey` eqTyConKey || tc `hasKey` heqTyConKey
  _       -> False

plugin :: Plugin
plugin = defaultPlugin
  { tcPlugin = const $ Just $ mkTcPlugin satisfierPlugin
  , pluginRecompile = purePlugin
  }

satisfierPlugin :: TcPlugin
satisfierPlugin = tracePlugin "ghc-typelits-sopsat"
  TcPlugin { tcPluginInit = lookupDefs
           , tcPluginSolve = satisfierSolve
           , tcPluginRewrite = const emptyUFM
           , tcPluginStop = const (return ())
           }

type Defs = (IORef (Set CType), (TyCon,TyCon,TyCon))

newtype CType = CType { unCType :: Type }

instance Eq CType where
  (==) = eqType `on` unCType

instance Ord CType where
  compare = nonDetCmpType `on` unCType

lookupDefs :: TcPluginM 'Init Defs
lookupDefs =
  do
    ref <- liftIO $ newIORef S.empty
    md <- liftTcPluginM $ lookupModule ordModule basePackage
    ordCond <- look md "OrdCond"
    leqT <- look md "<="
    md1 <- liftTcPluginM $ lookupModule typeErrModule basePackage
    assertT <- look md1 "Assert"
    return (ref, (leqT,assertT,ordCond))
  where
    look md s = tcLookupTyCon =<< liftTcPluginM (lookupName md $ mkTcOcc s)
    ordModule = mkModuleName "Data.Type.Ord"
    typeErrModule = mkModuleName "GHC.TypeError"
    basePackage = fsLit "base"


assertOrUnify :: (Ord f, Ord c)
              => SoPE f c -> SolverState f c (Either [SoPE f c] Bool)
assertOrUnify expr =
  assert expr >>= \case True  -> return (Right True)
                        False -> unify expr <&> \case [] -> Right False
                                                      xs -> Left xs

satisfierSolve :: Defs -> [Ct] -> [Ct] -> TcPluginM 'Solve TcPluginSolveResult
satisfierSolve defs@(gen'd,(leqT,_,_)) givens [] = do
  done <- liftIO $ readIORef gen'd
  let
    unit_givens = map fst $ mapMaybe (toNatEquality defs) givens
    reds = reduceGivens leqT done givens
    newlyDone = map (\(_,(prd,_,_)) -> CType prd) reds
  liftIO $ modifyIORef' gen'd $ union (fromList newlyDone)
  newGivens <- forM reds $ \(origCt,(pred',evTerm,_)) ->
                             mkNonCanonical' (ctLoc origCt) <$> newGiven (ctLoc origCt) pred' evTerm

  let checked = fromMaybe [] $
        evalStatements (forM unit_givens (\(ct, expr) -> (ct,) <$> declare expr))

  case partition snd checked of
    (_,[]) -> return (TcPluginOk [] newGivens)
    (_,contradicts) -> return (TcPluginContradiction (map fst contradicts))

satisfierSolve defs@(gen'd,(leqT,_,_)) givens wanteds = do
  done <- liftIO $ readIORef gen'd
  let unit_givens = map (second (subsToPred leqT)) $ mapMaybe (toNatEquality defs) givens
      redGs = reduceGivens leqT done givens
      newlyDone = map (\(_,(prd,_,_)) -> CType prd) redGs
      unit_wanteds = map (second (subsToPred leqT)) $ mapMaybe (toNatEquality defs) wanteds
      nonEqs = filter (not . (\p -> isEqPred p || isEqPrimPred p) . ctEvPred . ctEvidence) wanteds
  redGivens <- forM redGs $ \(origCt, (pred',evTerm,_)) ->
                              mkNonCanonical' (ctLoc origCt) <$> newGiven (ctLoc origCt) pred' evTerm
  reducible_wanteds <- catMaybes <$> mapM (\ct -> fmap (ct,) <$> reduceNatConstr (givens ++ redGivens) ct) nonEqs
  liftIO $ modifyIORef gen'd $ union (fromList newlyDone)
  if null unit_wanteds && null reducible_wanteds
    then return (TcPluginOk [] [])
    else let state = mapM (declare . snd . fst) unit_givens
         in case evalStatements (and <$> state) of
              Just False -> return (TcPluginContradiction givens)
              Nothing    -> return (TcPluginContradiction [])
              Just True  -> do
                ineqForRedWants <- fmap concat $ forM redGs $ \(ct,(_,_,ws)) -> forM ws $
                  fmap (mkNonCanonical' (ctLoc ct)) . newWanted (ctLoc ct)

                reds <- forM reducible_wanteds $ \(origCt,(term,ws,wDicts)) -> do
                  wants <- evSubstPreds (ctLoc origCt) $ subsToPred leqT ws
                  return ((term,origCt), wDicts ++ wants)
                let simpld = fromMaybe [] $
                      evalStatements (state >> forM unit_wanteds (\(expr, nw) -> (,nw) <$> solve expr))
                case partition (succeeded . snd . fst) simpld of
                  (solved,[]) -> do

                    evSolved <- catMaybes <$> mapM evidence solved
                    let (solved',newWanteds) = second concat (unzip $ evSolved ++ reds)
                    return (TcPluginOk solved' (newWanteds ++ ineqForRedWants))
                  (_,contradicts) -> do
                    return (TcPluginContradiction (map (fst . fst) contradicts))
  where
    solve (ct,expr) = (ct,) <$> (assertOrUnify expr >>= declareUnifiers)

    declareUnifiers u@(Left unifiers) = mapM_ declare unifiers >> return u
    declareUnifiers r@(Right _) = return r

    succeeded (Right res) = res
    succeeded (Left _)    = True

    evidence :: ((Ct,Either [SoPE TyCon SoPVar] Bool),[PredType]) -> TcPluginM 'Solve (Maybe ((EvTerm,Ct),[Ct]))
    evidence ((ct,Right _),nw)       = attachEvidence ct nw
    evidence ((ct,Left unifiers),nw) = attachEvidence ct (nw ++ map unifyItemToPredType unifiers)

instance Outputable (SoPE TyCon SoPVar) where
  ppr sope = text $ show sope

instance Show SoPVar where
  show (Const t) = showPprUnsafe t
  show (Var v)   = showPprUnsafe v

instance Show TyCon where
  show = showPprUnsafe

reduceGivens :: TyCon -> Set CType -> [Ct] -> [(Ct, (Type, EvTerm, [PredType]))]
reduceGivens leqT done givens =
  let nonEqs =
        [ ct
        | ct <- givens
        , let ev = ctEvidence ct
              prd = ctEvPred ev
        , isGiven ev
        , not $ (\p -> isEqPred p || isEqPrimPred p || isEqPredClass p) prd
        ]
  in filter
     (\(_,(prd,_,_)) ->
        S.notMember (CType prd) done)
     $ mapMaybe
     (\ct -> (ct,) <$> tryReduceGiven leqT givens ct)
     nonEqs

tryReduceGiven :: TyCon -> [Ct] -> Ct -> Maybe (PredType, EvTerm, [PredType])
tryReduceGiven leqT simplGivens ct = do
  let (mans,ws) = runWriter $ normaliseNatEverywhere $ ctEvPred $ ctEvidence ct
      ws' = [ p
            | p <- subsToPred leqT ws
            , not $ any ((`eqType` p) . ctEvPred . ctEvidence) simplGivens
            ]
  pred' <- mans
  return (pred', toReducedDict (ctEvidence ct) pred', ws')

reduceNatConstr :: [Ct] -> Ct -> TcPluginM 'Solve (Maybe (EvTerm, [(Type,Type)], [Ct]))
reduceNatConstr givens ct =
  let pred0 = ctEvPred $ ctEvidence ct
      (mans,tests) = runWriter $ normaliseNatEverywhere pred0
  in case mans of
    Nothing -> return Nothing
    Just pred' ->
      case find ((`eqType` pred') . ctEvPred . ctEvidence) givens of
        Nothing -> case getClassPredTys_maybe pred' of
          Just (cls,_) | className cls /= knownNatClassName -> do
                           evVar <- newEvVar pred'
                           let wDict = mkNonCanonical (CtWanted pred' (EvVarDest evVar) (ctLoc ct) emptyRewriterSet)
                               evCo = mkPluginUnivCo "ghc-typelits-sopsat" Representational [] pred' pred0
                               ev = evId evVar `evCast` evCo
                           return (Just (EvExpr ev, tests, [wDict]))
          _ -> return Nothing
        Just c -> return (Just (toReducedDict (ctEvidence c) pred0, tests, []))

toReducedDict :: CtEvidence -> PredType -> EvTerm
toReducedDict ct pred' =
  let
    pred0 = ctEvPred ct
    evCo = mkPluginUnivCo "ghc-typelits-sopsat" Representational [] pred0 pred'
    ev = ctEvExpr ct `evCast` evCo
  in EvExpr ev

data SoPVar
  = Const Type
  | Var TyVar

instance Ord TyCon where
  compare = nonDetCmpTc

instance Eq SoPVar where
  (Const a) == (Const b) = a `eqType` b
  (Var a) == (Var b) = a == b
  _ == _ = False

instance Ord SoPVar where
  compare (Const a) (Const b) = nonDetCmpType a b
  compare (Const _) (Var _) = LT
  compare (Var _) (Const _)  = GT
  compare (Var a) (Var b) = compare a b

toNatEquality :: Defs -> Ct -> Maybe ((Ct,SoPE TyCon SoPVar),[(Type,Type)])
toNatEquality (_,(_,assertT,ordCond)) ct =
  case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2
      -> go t1 t2
    IrredPred p
      -> go2 p
    _ -> Nothing
  where
    go (TyConApp tc xs) (TyConApp tc' ys)
      | tc == tc'
      , null ([tc,tc'] `intersect` [typeNatAddTyCon,typeNatSubTyCon
                                   ,typeNatMulTyCon,typeNatExpTyCon])
      = case filter (not . uncurry eqType) (zip xs ys) of
          [(x,y)]
            | isNatKind (typeKind x)
            , isNatKind (typeKind y)
            , let (x', k1) = runWriter (normaliseNat x)
            , let (y', k2) = runWriter (normaliseNat y)
            -> Just ((ct,SoPE x' y' EqR),k1 ++ k2)
          _ -> Nothing
      | tc == ordCond
      , [_,cmp,lt,eq,gt] <- xs
      , TyConApp tcCmpNat [x,y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt
      , ltTc == promotedTrueDataCon
      , TyConApp eqTc [] <- eq
      , eqTc == promotedTrueDataCon
      , TyConApp gtTc [] <- gt
      , gtTc == promotedFalseDataCon
      , let (x', k1) = runWriter (normaliseNat x)
      , let (y', k2) = runWriter (normaliseNat y)
      , let ks = k1 ++ k2
      = case tc' of
         _ | tc' == promotedTrueDataCon
           -> Just ((ct,SoPE x' y' LeR),ks)
         _ | tc' == promotedFalseDataCon
           -> Just ((ct,SoPE x' y' GeR),ks)
         _ -> Nothing
      | tc == assertT
      , tc' == cTupleTyCon 0
      , [] <- ys
      , [TyConApp ordCondTc zs, _] <- xs
      , ordCondTc == ordCond
      , [_,cmp,lt,eq,gt] <- zs
      , TyConApp tcCmpNat [x,y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt
      , ltTc == promotedTrueDataCon
      , TyConApp eqTc [] <- eq
      , eqTc == promotedTrueDataCon
      , TyConApp gtTc [] <- gt
      , gtTc == promotedFalseDataCon
      , let (x', k1) = runWriter (normaliseNat x)
      , let (y', k2) = runWriter (normaliseNat y)
      = Just ((ct,SoPE x' y' LeR),k1 ++ k2)

    go x y
      | isNatKind (typeKind x)
      , isNatKind (typeKind y)
      , let (x', k1) = runWriter (normaliseNat x)
      , let (y', k2) = runWriter (normaliseNat y)
      = Just ((ct,SoPE x' y' EqR),k1 ++ k2)
      | otherwise
      = Nothing

    go2 (TyConApp tc ys)
      | tc == assertT
      , [TyConApp ordCondTc xs, _] <- ys
      , ordCondTc == ordCond
      , [_,cmp,lt,eq,gt] <- xs
      , TyConApp tcCmpNat [x,y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt
      , ltTc == promotedTrueDataCon
      , TyConApp eqTc [] <- eq
      , eqTc == promotedTrueDataCon
      , TyConApp gtTc [] <- gt
      , gtTc == promotedFalseDataCon
      , let (x', k1) = runWriter (normaliseNat x)
      , let (y', k2) = runWriter (normaliseNat y)
      = Just ((ct,SoPE x' y' LeR), k1 ++ k2)

    go2 _ = Nothing

    isNatKind :: Kind -> Bool
    isNatKind = (`eqType` naturalTy)

normaliseNat :: Type -> Writer [(Type,Type)] (SoP TyCon SoPVar)
normaliseNat ty | Just ty1 <- coreView ty = normaliseNat ty1
normaliseNat (TyVarTy v)          = return $ SoP.cons (Var v)
normaliseNat (LitTy (NumTyLit i)) = return $ SoP.int i
normaliseNat (TyConApp tc [x,y])
  | tc == typeNatAddTyCon = (|+|) <$> normaliseNat x <*> normaliseNat y
  | tc == typeNatSubTyCon = do
      tell [(x,y)]
      (|-|) <$> normaliseNat x <*> normaliseNat y
  | tc == typeNatMulTyCon = (|*|) <$> normaliseNat x <*> normaliseNat y
  | tc == typeNatExpTyCon = (|^|) <$> normaliseNat x <*> normaliseNat y
normaliseNat (TyConApp tc args)
  = SoP.func tc <$> mapM normaliseNat args
normaliseNat t = return $ SoP.cons (Const t)

maybeRunWriter :: Monoid a => Writer a (Maybe b) -> Writer a (Maybe b)
maybeRunWriter w =
  case runWriter w of
    (Nothing,_) -> pure Nothing
    (b,a)       -> tell a >> pure b

normaliseNatEverywhere :: Type -> Writer [(Type,Type)] (Maybe Type)
normaliseNatEverywhere ty0
    | TyConApp tc _fields <- ty0
    , tc `elem` knownTyCons = do
        ty1M <- maybeRunWriter (go ty0)
        let ty1 = fromMaybe ty0 ty1M
        ty2 <- normaliseSimplifyNat ty1
        pure (if ty2 `eqType` ty1 then ty1M else Just ty2)
    | otherwise = go ty0
  where
    knownTyCons = [typeNatAddTyCon, typeNatMulTyCon, typeNatSubTyCon, typeNatExpTyCon]

    go :: Type -> Writer [(Type,Type)] (Maybe Type)
    go (TyConApp tc_ fields0_) = do
        fields1_ <- mapM (maybeRunWriter . cont) fields0_
        if any isJust fields1_ then
           pure (Just (TyConApp tc_ (zipWith fromMaybe fields0_ fields1_)))
         else
           pure Nothing
        where
          cont = if tc_ `elem` knownTyCons then go else normaliseNatEverywhere
    go _ = pure Nothing

normaliseSimplifyNat :: Type -> Writer [(Type,Type)]Type
normaliseSimplifyNat ty
  | typeKind ty `eqType` naturalTy = do
      -- Multiplication by 1 ensures simplification
      ty' <- normaliseNat ty
      return $ fromSoP $ ty' |*| SoP.int 1
  | otherwise = return ty

class FromSoP f c t where
  fromSoP :: SoP f c -> t

instance FromSoP TyCon SoPVar Type where
  fromSoP = combineP . map negateP . unS
    where
      negateP (P ((I i):ps@(_:_))) | i == (-1) = Left (P ps)
      negateP (P ((I i):ps))       | i < 0     = Left (P (I (abs i):ps))
      negateP ps                               = Right ps

      combineP []  = mkNumLitTy 0
      combineP [p] = either (\p' -> mkTyConApp typeNatSubTyCon
                              [mkNumLitTy 0, fromProduct p'])
                     fromProduct p
      combineP [p1,p2] = either
        (\x -> either
          (\y -> let r = mkTyConApp typeNatSubTyCon [fromProduct x, fromProduct y]
                 in mkTyConApp typeNatSubTyCon [mkNumLitTy 0, r])
          (\y -> mkTyConApp typeNatSubTyCon [fromProduct y, fromProduct x])
          p2)
        (\x -> either
          (\y -> mkTyConApp typeNatSubTyCon [fromProduct x, fromProduct y])
          (\y -> mkTyConApp typeNatAddTyCon [fromProduct x, fromProduct y])
          p2)
        p1
      combineP (p:ps) =
        let es = combineP ps
        in either (\x -> mkTyConApp typeNatSubTyCon [es, fromProduct x])
                  (\y -> mkTyConApp typeNatAddTyCon [fromProduct y, es])
                  p

      fromProduct (P ps) =
        let ps' = map fromSymbol (foldr mergeExp [] ps)
        in foldr1 (\t1 t2 -> mkTyConApp typeNatMulTyCon [t1,t2]) ps'
        where
          mergeExp :: (Eq f, Eq c)
                   => Symbol f c -> [Either (Symbol f c) (SoP f c,[Product f c])]
                   -> [Either (Symbol f c) (SoP f c,[Product f c])]
          mergeExp (E s p) [] = [Right (s,[p])]
          mergeExp (E s1 p1) (y:ys)
            | Right (s2,p2) <- y
            , s1 == s2
            = Right (s1,p1:p2) : ys
            | otherwise
            = Right (s1,[p1]) : y : ys
          mergeExp x ys = Left x : ys

      fromSymbol (Left (I i)) = mkNumLitTy i
      fromSymbol (Left (A a)) = fromAtom a
      fromSymbol (Left (E s p)) = mkTyConApp typeNatExpTyCon [fromSoP s, fromProduct p]
      fromSymbol (Right (s1,s2)) = mkTyConApp typeNatExpTyCon [fromSoP s1, fromSoP (S s2)]

      fromAtom (C (Var v)) = mkTyVarTy v
      fromAtom (C (Const c)) = c
      fromAtom (F f args) = mkTyConApp f (map fromSoP args)

subsToPred :: TyCon -> [(Type,Type)] -> [PredType]
subsToPred leqT = map (subToPred leqT)

subToPred :: TyCon -> (Type,Type) -> PredType
subToPred leqT (a,b) =
  let
    lhs = TyConApp leqT [naturalTy, b, a]
    rhs = TyConApp (cTupleTyCon 0) []
  in mkPrimEqPred lhs rhs

unifyItemToPredType :: SoPE TyCon SoPVar  -> PredType
unifyItemToPredType SoPE{..} = mkPrimEqPred ty1 ty2
  where
    ty1 = fromSoP lhs
    ty2 = fromSoP rhs

-- Converts ranges from the satisfier to predicates
-- See @satisfierSolve@
rangeToPred :: TyCon -> SoPE TyCon SoPVar -> PredType
rangeToPred leqT (SoPE a b _) = subToPred leqT (fromSoP b, fromSoP a)

evSubstPreds :: CtLoc -> [PredType] -> TcPluginM 'Solve [Ct]
evSubstPreds loc = mapM (fmap mkNonCanonical . newWanted loc)

mkNonCanonical' :: CtLoc -> CtEvidence -> Ct
mkNonCanonical' origCtl ev =
  let
    ct_ls = ctLocSpan origCtl
    ctl   = ctEvLoc ev
  in mkNonCanonical (setCtEvLoc ev (setCtLocSpan ctl ct_ls))

attachEvidence :: Ct -> [PredType] -> TcPluginM 'Solve (Maybe ((EvTerm,Ct),[Ct]))
attachEvidence ct preds = do
  holeWanteds <- evSubstPreds (ctLoc ct) preds
  case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2 ->
      let ctEv = mkPluginUnivCo "ghc-typelits-sopsat" Nominal [] t1 t2
      in return (Just ((EvExpr (Coercion ctEv), ct), holeWanteds))
    IrredPred p ->
      let t1 = mkTyConApp (cTupleTyCon 0) []
          co = mkPluginUnivCo "ghc-typelits-sopsat" Representational [] t1 p
          dcApp = evId $ dataConWrapId $ cTupleDataCon 0
      in return (Just ((EvExpr $ evCast dcApp co, ct), holeWanteds))
    _ -> return Nothing

-- | Print out extra information about the initialisation, stop, and every run
-- of the plugin when @-ddump-tc-trace@ is enabled.
tracePlugin :: String -> TcPlugin -> TcPlugin
tracePlugin s TcPlugin{..} = TcPlugin
  { tcPluginInit    = traceInit
  , tcPluginSolve   = traceSolve
  , tcPluginRewrite = tcPluginRewrite
  , tcPluginStop    = traceStop
  }
 where
  traceInit = do
    tcPluginTrace ("tcPluginInit " ++ s) empty >> tcPluginInit

  traceStop  z = tcPluginTrace ("tcPluginStop " ++ s) empty >> tcPluginStop z

  traceSolve z given wanted = do
    tcPluginTrace ("tcPluginSolve start " ++ s)
                      (text "given   =" <+> ppr given
                    $$ text "wanted  =" <+> ppr wanted)
    r <- tcPluginSolve z given wanted
    case r of
      TcPluginOk solved new
        -> tcPluginTrace ("tcPluginSolve ok " ++ s)
                         (text "solved =" <+> ppr solved
                       $$ text "new    =" <+> ppr new)
      TcPluginContradiction bad
        -> tcPluginTrace ("tcPluginSolve contradiction " ++ s)
                         (text "bad =" <+> ppr bad)
      TcPluginSolveResult bad solved new
        -> tcPluginTrace ("tcPluginSolveResult " ++ s)
                         (text "solved =" <+> ppr solved
                       $$ text "bad    =" <+> ppr bad
                       $$ text "new    =" <+> ppr new)
    return r
