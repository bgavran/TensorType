module Data.Container.Base.Fix.Definition

import Data.Container.Base.Object.Definition
import Data.Container.Base.Extension.Definition
import Data.Container.Base.Morphism.Definition

||| Kleene star, aka. the free monad monad on containers
||| Is the least fixpoint in the category of containers of
||| Kleene c = Scalar >+< (c >@ Kleene c)
||| Since Idris doesn't support codata, we can also use this for greatest fixpoint
||| by using corecursive shapes and marking them as partial

public export
data KleeneShp : Cont -> Type where
  Done : KleeneShp c
  More : (Ext c (KleeneShp c)) -> KleeneShp c

public export
data KleenePos : {c : Cont} -> KleeneShp c -> Type where
  DonePos : KleenePos Done
  MorePos : {cs : c.Shp} -> {f : c.Pos cs -> KleeneShp c} ->
    (cp : c.Pos cs) -> KleenePos (f cp) -> KleenePos (More (cs <| f))

public export
Kleene : Cont -> Cont
Kleene c = (ks : KleeneShp c) !> KleenePos ks

namespace Morphism

  public export
  KleeneShp : (c =%> d) -> KleeneShp c -> KleeneShp d
  KleeneShp (!% f) Done = Done
  KleeneShp (!% f) (More (cs <| g)) = More ((f cs).fst <| \dp => KleeneShp (!% f) (g ((f cs).snd dp)))

  public export
  KleenePos : (f : c =%> d) -> (ks : KleeneShp c) -> KleenePos (KleeneShp f ks) -> KleenePos ks
  KleenePos (!% f) Done DonePos = DonePos
  KleenePos (!% f) (More (cs <| g)) (MorePos dp kp) = let
    cp = (f cs).snd dp
    in MorePos ((f cs).snd dp) (KleenePos (!% f) (g ((f cs).snd dp)) kp)

  ||| Action on morphisms
  public export
  Kleene : (c =%> d) -> (Kleene c =%> Kleene d)
  Kleene f = (!%) \ks => (KleeneShp f ks ** KleenePos f ks)
