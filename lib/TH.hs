{-@ LIQUID "--skip-module" @-}
{-# OPTIONS_GHC -Wincomplete-patterns #-}

{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unused-local-binds -Wno-unused-matches #-}
module TH where

import Control.Monad (replicateM)
import Data.Char (toLower)
import Data.List (unfoldr, foldl1')

import Language.Haskell.TH

logg :: (Show a, Ppr a) => a -> Q ()
logg x = do
    reportError . show $ x
    reportError . unwords . lines . pprint $ x

nobang :: BangQ
nobang = bang noSourceUnpackedness noSourceStrictness

mapHead :: (a -> a) -> [a] -> [a]
mapHead _ [] = []
mapHead f (x:xs) = f x:xs

lowerFirst :: String -> String
lowerFirst = mapHead toLower

mapNameCapturable :: (String -> String) -> Name -> Name
mapNameCapturable f = mkName . f . nameBase

tyVarBndrName :: TyVarBndr -> Name
tyVarBndrName (PlainTV n) = n
tyVarBndrName (KindedTV n _k) = n

-- | make a type var binder plain (removing a kind signature)
plainifyTV :: TyVarBndr -> TyVarBndr
plainifyTV = plainTV . tyVarBndrName

-- | convert @[a, b, c, d]@ to expression @((a b) c) d@
exApps :: [ExpQ] -> ExpQ
exApps = foldl1' $ \a b -> [e| $a $b |]

-- | convert @[a, b, c, d]@ to type @((a b) c) d@
tyApps :: [TypeQ] -> TypeQ
tyApps = foldl1' $ \a b -> [t| $a $b |]

-- | convert @[a, b, c, d]@ to @a -> (b -> (c -> d))@
arrows :: [TypeQ] -> TypeQ
arrows = foldr1 $ \a b -> [t| $a -> $b |]

-- | convert @a -> (b -> (c -> d))@ to @[a, b, c, d]@
unArrows :: Type -> [Type]
unArrows t = unfoldr go $ Just t
  where
    go = \case
        Just (AppT (AppT ArrowT x) xs) -> Just (x, Just xs)
        Just x                         -> Just (x, Nothing)
        Nothing                        -> Nothing

-- | indexed type from names
consTy :: Name -> [Name] -> TypeQ
consTy tyConName tyVarBndrs = tyApps $ conT tyConName : fmap varT tyVarBndrs

unConsTy :: Type -> [Name]
unConsTy = reverse . unfoldr go . Just
  where
    go = \case
        Just (AppT xs (VarT x)) -> Just (x, Just xs)
        Just (ConT x)           -> Just (x, Nothing)
        _                       -> Nothing

-- | constructor expression from names
consExp :: Name -> [Name] -> ExpQ
consExp conName argNames = exApps $ conE conName : fmap varE argNames

-- | deconstruction pattern from names
consPat :: Name -> [Name] -> PatQ
consPat conName argNames = conP conName $ fmap varP argNames

constructorType :: Name -> DecsQ
constructorType conName = do
    DataConI _conName conTyFull tyName <- reify conName
    -- ty: the original type
    -- con: the constructor of [the original type]
    -- conArg: arguments to [the constructor of [the original type]]
    -- newTy: the type we name after [the constructor of [the original type]]
    -- newCon: constructor of ... the new type
    (conTyCxt, conTy) <- case conTyFull of
            (ForallT _conTyVarBndr conTyCxt conTy) -> return (conTyCxt, conTy)
            conTy@AppT{} -> return ([], conTy)
            conTy@ConT{} -> return ([], conTy)
            t -> fail . ("constructorType: Not implemented: " ++) . show $ t
    let ty = last $ unArrows conTy -- type in the constr-result has type-vars in correct order
        tyVars = tail $ unConsTy ty
        conArgTys = init $ unArrows conTy
        newTyName = mapNameCapturable (++ "C") conName
        newConName = newTyName
        tyQ = return ty
        newTyQ = consTy newTyName tyVars
    dat <- let
        con = normalC newConName $ bangType nobang . return <$> conArgTys
        in dataD (return conTyCxt) newTyName (plainTV <$> tyVars) Nothing [con] []
    conArgNames <- length conArgTys `replicateM` newName "x"
    intro <- let
        name = mapNameCapturable ("intro" ++) newTyName
        sig = sigD name [t| $tyQ -> Maybe $newTyQ |]
        cls0 = clause
            [consPat conName conArgNames]
            (normalB [e| Just $(consExp newConName conArgNames) |]) []
        cls1 = clause [[p| _ |]] (normalB [e| Nothing |]) []
        fun = funD name [cls0, cls1]
        in sequence [sig, fun]
    elim <- let
        name = mapNameCapturable ("elim" ++) newTyName
        sig = sigD name [t| $newTyQ -> $tyQ |]
        cls = clause
            [consPat newConName conArgNames]
            (normalB $ consExp conName conArgNames) []
        fun = funD name [cls]
        in sequence [sig, fun]
    return $ dat : intro ++ elim
