module Data.CT.DependentPara.Instances

import Data.DPair
import Data.CT.Category.Definition
import Data.CT.Functor.Definition
import Data.CT.DependentAction.Definition
import Data.CT.DependentPara.Definition
import Data.CT.Category.Instances
import Data.CT.Functor.Instances
import Data.CT.DependentAction.Instances

import Data.Container.Base
import Data.Container.Additive

public export infixr 0 -\->
public export infixr 0 =\\=>

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
Instead going in and defining full-blown definitions of dependent actegories with units and coherences we instead leverage the main definition in the background and only instantiate cases, manually:
one for parametric functions and one for parametric additive dependent lenses.
We instantiate them using same names in different namespaces, and leverage Idris' name resolution mechanisms to allow the user to use the same name and
reduce cognitive load
-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

namespace ParametricFunctions
  ||| Parametric functions
  ||| "Usual" dependent para on sets and functions
  public export
  Para : (a, b : Type) -> Type 
  Para = DepParaMor DepActOnType
  
  ||| Infix notation for parametric functions
  ||| We interpret the crossed line as a parameter coming in from the top
  public export
  (-\->) : (a, b : Type) -> Type
  a -\-> b = Para a b

  public export
  trivialParam : (a -> b) -> a -\-> b
  trivialParam f = MkPara 
    (\_ => Unit)
    (\(a ** ()) => f a)

  public export
  id : a -\-> a
  id = trivialParam id

  public export
  composePara : a -\-> b -> b -\-> c -> a -\-> c
  composePara (MkPara p f) (MkPara q g) = MkPara
    (\x => DPair (p x) (\p' => q (f (x ** p'))) )
    (\(x ** (p' ** q')) => g (f (x ** p') ** q'))
  
  public export infixr 10 \>>
  
  public export
  (\>>) : a -\-> b -> b -\-> c -> a -\-> c
  (\>>) = composePara

  public export
  reparam : (pf : a -\-> b) ->
    {q : a -> Type} ->
    (r : (x : a) -> q x -> pf.Param x) ->
    a -\-> b
  reparam (MkPara p f) r = MkPara q (\(x ** qq) => f (x ** (r x qq)))

  public export
  Param : Para a b -> a -> Type
  Param = DepParaMor.Param
  
  public export
  Run : (pf : Para a b) -> (x : a) -> Param pf x -> b
  Run pf = DPair.curry (DepParaMor.Run pf)

  public export
  data IsNotDependent : Para a b -> Type where
    MkNonDep : (p : Type) -> (f : DPair a (const p) -> b) ->
      IsNotDependent (MkPara (\_ => p) f)
  
  public export
  GetNonDep : (pf : Para a b) ->
    IsNotDependent pf => (p : Type ** DPair a (const p) -> b)
  GetNonDep _ @{MkNonDep p f} = (p ** f)

  ||| Get the parameter of a non-dependent parametric function
  public export
  GetParam : (pf : Para a b) ->
    IsNotDependent pf => Type
  GetParam _ @{MkNonDep p f} = p


  public export
  composeNTimes : Nat -> a -\-> a -> a -\-> a
  composeNTimes 0 f = id
  composeNTimes 1 f = f -- to get rid of the annoying Unit parameter
  composeNTimes (S k) f = composePara f (composeNTimes k f)

  public export
  binaryOpToPara : {p : Type} -> (f : (a, p) -> b) -> a -\-> b
  binaryOpToPara f = MkPara
    (\_ => p)
    (\(x ** p') => f (x, p'))


namespace ParametricDependentLenses
  ||| Parametric dependent lenses
  ||| Not really used in this repo
  public export
  ParaDLens : (a, b : Cont) -> Type
  ParaDLens = DepParaMor DepActOnCont

  ||| Used in this repo, as all neural networks are additive dependent lenses
  public export
  ParaAddDLens : (a, b : AddCont) -> Type
  ParaAddDLens = DepParaMor DepActOnAddCont

  ||| Infix notation for additive parametric dependent lenses
  public export
  (=\\=>) : (a, b : AddCont) -> Type
  a =\\=> b = ParaAddDLens a b
  

  public export
  trivialParam : {0 a, b : AddCont} -> (a =%> b) -> a =\\=> b
  trivialParam f = MkPara
    (\_ => Scalar)
    (!% !% \(x ** ()) => let (y ** ky) = (%!) f x in (y ** \y' => (ky y', ())))

  public export
  id : a =\\=> a
  id = trivialParam id
  

  public export
  composePara : a =\\=> b -> b =\\=> c -> a =\\=> c
  composePara (MkPara p f) (MkPara q g) = MkPara
    (\x => DepHancockProduct (p x) (\ps => q (f.fwd (x ** ps))))
    (!%+ \(x ** (ps ** qs)) =>
      (g.fwd (f.fwd (x ** ps) ** qs) ** \cPos =>
        let (bPos, qPos) = g.bwd (f.fwd (x ** ps) ** qs) cPos
            (aPos, pPos) = f.bwd (x ** ps) bPos
        in (aPos, (pPos, qPos))))

  public export infixr 10 &>>

  public export
  (&>>) : a =\\=> b -> b =\\=> c -> a =\\=> c
  (&>>) = composePara

  ||| A predicate witnessing that a parametric additive dependent lens has
  ||| a non-dependent (constant) parameter.
  public export
  data IsNotDependent : ParaAddDLens a b -> Type where
    MkNonDep : (p : AddCont) -> (f : DepHancockProduct a (const p) =%> b) ->
      IsNotDependent {a=a} {b=b} (MkPara (\_ => p) f)
  
  public export
  GetNonDep : (pf : ParaAddDLens a b) ->
    IsNotDependent pf => (pc : AddCont ** DepHancockProduct a (const pc) =%> b)
  GetNonDep _ @{MkNonDep pc f} = (pc ** f)

  public export
  GetParam : (pf : ParaAddDLens a b) ->
    IsNotDependent pf => AddCont
  GetParam _ @{MkNonDep p f} = p

  public export
  toHomRepresentation : (pf : ParaAddDLens a b) ->
    IsNotDependent pf =>
    GetParam pf =%> (InternalLensAdditive a b)
  toHomRepresentation (MkPara (const pc) f) @{MkNonDep pc f}
    = !%+ \p => (!%+ \x => (f.fwd (x ** p) ** \b' => fst (f.bwd (x ** p) b')) ** \l => foldr (\(x ** b') => pc.Plus p (snd (f.bwd (x ** p) b'))) (pc.Zero p) l)

  public export
  composeNTimes : Nat -> a =\\=> a -> a =\\=> a
  composeNTimes 0 f = id
  composeNTimes 1 f = f -- to get rid of the annoying Unit parameter
  composeNTimes (S k) f = composePara f (composeNTimes k f)

  ||| Convert a morphism from product container to one from DepHancockProduct
  ||| This witnesses the isomorphism (a >< p) ≅ DepHancockProduct a (const p)
  public export
  fromNonDepProduct : {0 a, p, b : AddCont} ->
    (a >< p) =%> b -> DepHancockProduct a (const p) =%> b
  fromNonDepProduct f = !%+ \(x ** p') => (%!) f (x, p')

  public export
  binaryOpToPara : {p : AddCont} ->
    (a >< p) =%> b -> a =\\=> b
  binaryOpToPara f = MkPara (\_ => p) (fromNonDepProduct f)

-- public export
-- dependentMap : {t : a -> Type} -> (f : (x : a) -> t x) ->
--   Vect n a -> Vect n (x : a ** t x)
-- dependentMap f [] = []
-- dependentMap f (x :: xs) = (x ** f x) :: dependentMap f xs
-- 
-- public export infixr 10 <$^>
-- public export
-- (<$^>) : {t : a -> Type} -> (f : (x : a) -> t x) ->
--   Vect n a -> Vect n (x : a ** t x)
-- (<$^>) f xs = dependentMap f xs


-- composePara_rhs_1 : (p : Vect n Type) -> (q : Vect m Type)
--   -> (a -> All Prelude.id p -> b)
--   -> (b -> All Prelude.id q -> c)
--   -> (a -> All Prelude.id (p ++ q) -> c)
-- composePara_rhs_1 [] [] f g a [] = ?composePara_rhs_1_rhs_2
-- composePara_rhs_1 [] (q :: ws) f g a (pq :: pqs) = ?composePara_rhs_1_rhs_3
-- composePara_rhs_1 (p :: ps) q f g a pq = ?composePara_rhs_1_rhs_1
-- 
-- composePara : Para a n b -> Para b m c -> Para a (n + m) c
-- composePara (MkPara p f) (MkPara q g) = MkPara (p ++ q) (composePara_rhs_1 p q f g)

