module Data.Container.Applicative.Definition

import Data.Container.Object.Definition
import Data.Container.Extension.Definition
import Misc

%hide Builtin.infixr.(#)

-- this file and the applicative directory is a relic of the old implementation
-- not all of this is used, and likely can be simplified


||| Applicative Container
||| Consists of a container and a proof that its extension is an applicative functor
||| Defined using Idris' auto as we'd like to avoid directly providing this
public export
record ContA where
  constructor (#)
  GetC : Cont
  ||| Question: can we state this without referencing the extension?
  {auto applPrf : Applicative (Ext GetC)}

public export prefix 0 #

||| Convenience functions so we dont have to keep writing GetC
public export
(.Shp) : ContA -> Type
(.Shp) c = (GetC c) .Shp

public export
(.Pos) : (c : ContA) -> c.Shp -> Type
(.Pos) c sh = (GetC c) .Pos sh

-- alternative method of using applicative instances, not sure yet if this is better
public export
data AllApplicative : List Cont -> Type where
  Nil : AllApplicative []
  Cons : (firstAppl : Applicative (Ext c)) =>
    (restAppl : AllApplicative cs) =>
    AllApplicative (c :: cs)


-- is there a better way?
%hint
public export
oneToTwoAppl : AllApplicative [c] => AllApplicative [c, c]
oneToTwoAppl @{Cons} = Cons



-- ||| This states a list version of 
-- ||| Ext c2 . Ext c1 = Ext (c2 . c1)
-- public export
-- ToContainerComp : {conts : List ContA} ->
--   composeExtensionsA conts a -> Ext (composeContainersA conts) a
-- ToContainerComp {conts = []} ce = ce
-- ToContainerComp {conts = [c]} ce = ce
-- ToContainerComp {conts = (c :: d :: cs)} (Shp <| idx) = 
--   let rst = (ToContainerComp {conts=(d :: cs)}) . idx
--   in (Shp <| shapeExt . rst) <| (\(cp ** fsh) => index (rst cp) fsh)

-- public export
-- FromContainerComp : {conts : List ContA} ->
--   Ext (composeContainersA conts) a -> composeExtensionsA conts a
-- FromContainerComp {conts = []} ce = ce
-- FromContainerComp {conts = [c]} ce = ce
-- FromContainerComp {conts = (c :: d :: cs)} ((csh <| cpos) <| idx)
--   = csh <| \dd => FromContainerComp {conts=(d::cs)} (cpos dd <| curry idx dd)




-- public export
-- mapcomposeExtensionsA : {conts : List ContA} ->
--   (f : a -> b) -> composeExtensionsA conts a -> composeExtensionsA conts b
-- mapcomposeExtensionsA {conts = []} f e = f <$> e
-- mapcomposeExtensionsA {conts = ((# c) :: cs)} f e = mapcomposeExtensionsA f <$> e
-- 
-- public export
-- [FCE] {conts : List ContA} -> Functor (composeExtensionsA conts) where
--   map f ce = ?vnn -- mapcomposeExtensionsA
-- 
-- testTT : {c : ContA} -> (f : String -> Int) -> composeExtensionsA [c] String -> composeExtensionsA [c] Int
-- testTT f = map @{FCE {conts=[c]}} f
-- 
-- public export
-- compExtReplicate : {conts : List ContA} ->
--   a -> composeExtensionsA conts a
-- compExtReplicate {conts = []} a = pure a
-- compExtReplicate {conts = ((#) _ {applPrf} :: _)} a
--   = compExtReplicate <$> pure a
-- 
-- public export
-- compExtLiftA2 : {conts : List ContA} ->
--   composeExtensionsA conts a ->
--   composeExtensionsA conts b ->
--   composeExtensionsA conts (a, b)
-- compExtLiftA2 {conts = []} ca cb = pure (extract ca, extract cb)
-- compExtLiftA2 {conts = ((#) c {applPrf} :: cs)} ca cb
--   = uncurry compExtLiftA2 <$> liftA2 ca cb


-- Tensors should eventually more and more use the container backend
-- public export
-- Applicative (composeExtensionsA conts) using FCE where
--   pure = compExtReplicate
--   fs <*> xs = uncurry ($) <$> compExtLiftA2 fs xs

-- public export
-- compReplicate : {conts : List ContA} ->
--   a -> Ext (composeContainersA conts) a
-- compReplicate {conts = []} x = pure x
-- compReplicate {conts = (c :: cs)} x
--   = ?ff <| ?bb

-- compReplicate {conts = []} a = pure a
-- compReplicate {conts = (c :: cs)} a
--   = let (sh <| ind) = compReplicate {conts=cs} a
--     in (?ff <| ?vmm) <| ?bb
--compReplicate {conts = []} a = pure a
--compReplicate {conts = ((# c) :: cs)} a
--  = pure {f=Ext c} $ compReplicate {conts=cs} a



-- ||| Given a list of natural numbers, when we convert this to composition product of containers, this will have a unit shape
-- ||| We don't do rewrites to prove this (as it's not definitionally equal to unit shape, but only isomorphic)
-- ||| Hence, just like with EmptyExt we provide convenience functions to create this unit shape easily
-- public export
-- emptyShapeCubicalTensor : {shape : List Nat} ->
--   (composeContainersA (Vect <$> shape)) .Shp
-- emptyShapeCubicalTensor {shape = []} = ()
-- emptyShapeCubicalTensor {shape = (_ :: _)}
--   = () <| (\_ => emptyShapeCubicalTensor)

-- shapeOfCubicalTensorIsUnit : {shape : List Nat} ->
--   (composeContainersA (Vect <$> shape)) .Shp = ()
-- shapeOfCubicalTensorIsUnit {shape = []} = Refl
-- shapeOfCubicalTensorIsUnit {shape = (s :: ss)}
--   = rewrite shapeOfCubicalTensorIsUnit {shape = ss} in ?afasdf

-- public export
-- composeContainersA' : {conts : List ContA} ->
--   ContAontList conts -> ContA
-- composeContainersA' [] = # CUnit
-- composeContainersA' (c :: cs) =
--   (#) (c >< prodConts (applContListToContList cs))
--     {applPrf = ?composeContainersA_rhs_1}
