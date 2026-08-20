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

{-------------------------------------------------------------------------------
{-------------------------------------------------------------------------------
Default Para is dependent Para, and default lenses are dependent additive lenses

Ideally, this code would uphold the notation principle that
`-\->` denotes dependent parametric functions and
`=\\=>` denotes dependent parametric lenses

But since learning where the parameter depends on the input hasn't been
implemented yet, the code will write `=\\=>` for non-dependent additive lenses, and simply not export an infix notation for dependent additive lenses

Likewise, instead going in and defining full-blown definitions of dependent 
actegories with units and coherences we instead leverage the main definition in 
the background and only instantiate cases, manually:
one for parametric functions and one for parametric additive dependent lenses.
We instantiate them using same names in different namespaces, and leverage Idris' name resolution mechanisms to allow the user to use the same name and
reduce cognitive load.
However, to reduce typechecking time, there are also now some concrete records.
-------------------------------------------------------------------------------}
-------------------------------------------------------------------------------}

-- Para(Set)
public export infixr 1 -\-> -- dependent parametric functions
public export infixr 1 -\--> -- non-dependent parametric functions

-- Para(AddCont)
public export infixr 1 =\\=> -- non-dependent parametric lenses
-- public export infixr 1 =\\==> -- not exported, see comment at top of file

  
-- Dependent parametric function composition
public export infixr 10 \>>
-- Dependent parametric lens composition
public export infixr 10 &>>

||| The 2-category `Para(Set)`
namespace ParametricFunctions
  ||| Non-dependent parametric functions
  public export
  Para : (a, b : Type) -> Type
  Para = DepParaMor PairType

  ||| Infix notation for non-dependent parametric functions
  ||| We interpret the extra "-" as a mental symbol for "flat",
  ||| i.e. "non-dependent"
  public export
  (-\-->) : (a, b : Type) -> Type
  a -\--> b = Para a b

  ||| Dependent parametric functions, i.e. where the parameter type varies with
  ||| values of the input `a`
  public export
  DPara : (a, b : Type) -> Type 
  DPara = DepParaMor DPairType
  
  ||| Infix notation for dependent parametric functions
  ||| We interpret the crossed line as a parameter coming in from the top
  public export
  (-\->) : (a, b : Type) -> Type
  a -\-> b = DPara a b

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

  public export
  composeParallel : a -\-> b -> c -\-> d -> (a, c) -\-> (b, d)
  composeParallel (MkPara p f) (MkPara q g) = MkPara
    (\(x, y) => (p x, q y))
    (\((x, y) ** (px, qy)) => (f (x ** px), g (y ** qy)))
  
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
  Param : DPara a b -> a -> Type
  Param = DepParaMor.Param
  
  public export
  Run : (pf : DPara a b) -> (x : a) -> Param pf x -> b
  Run pf = DPair.curry (DepParaMor.Run pf)

  public export
  data IsNotDependent : DPara a b -> Type where
    MkNonDep : (p : Type) -> (f : DPair a (const p) -> b) ->
      IsNotDependent (MkPara (\_ => p) f)
  
  public export
  GetNonDep : (pf : DPara a b) ->
    IsNotDependent pf => (p : Type ** DPair a (const p) -> b)
  GetNonDep _ @{MkNonDep p f} = (p ** f)

  ||| Get the parameter of a non-dependent parametric function
  public export
  GetParam : (pf : DPara a b) ->
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

||| The 2-category Para(AddCont)
||| Para(Cont) is not used in TensorType
namespace ParametricLenses
  ||| Non-dependent parametric lenses.
  ||| As mentioned on top, all of these lenses are additive, and dependent
  |||
  ||| As a record, because otherwise the implicit argument carrying slows down
  ||| typechecking practical neural network architectures. That is, every
  ||| `.Param` and `.Run` carry `AddDLens`, `Const` and `PairAddCont` as 
  ||| implcit arguments, unfolded into the full `MkCat` and `MkFunctor` 
  ||| structure. This happens in bodies of, say `>*<`, at *every occurence*
  public export
  record ParaAddLens (a, b : AddCont) where
    constructor MkPara
    Param : AddCont
    Run : (a >*< Param) =%+> b

  ||| Infix notation for non-dependent parametric additive lenses
  ||| Compared to `-\-->`, every line is doubled, meant to be interpreted as 
  ||| information flowing bidirectionally. 
  ||| See comment for top of file for further explanation
  public export
  (=\\=>) : (a, b : AddCont) -> Type
  a =\\=> b = ParaAddLens a b

  namespace Wrapping
    ||| Simple wrapping and unwrapping because this is a record now
    public export
    toDepPara : ParaAddLens a b -> DepParaMor PairAddCont a b
    toDepPara (MkPara p f) = MkPara p f

    public export
    fromDepPara : DepParaMor PairAddCont a b -> ParaAddLens a b
    fromDepPara (MkPara p f) = MkPara p f


  public export
  trivialParam : a =%+> b -> a =\\=> b
  trivialParam f = MkPara
    UnitCont
    (!%+ \(x, ()) =>
      let (y ** ky) = (%!+) f x
      in (y ** \y' => (ky y', ())))

  public export
  binaryOpToPara : {p : AddCont} ->
    (a >*< p) =%+> b -> a =\\=> b
  binaryOpToPara f = MkPara p f

  public export
  id : a =\\=> a
  id = trivialParam id

  public export
  GetParam : ParaAddLens a b -> AddCont
  GetParam (MkPara p _) = p

  public export
  toHomRepresentation : (f : ParaAddLens a b) ->
    (GetParam f) =%+> InternalLensAdditive a b
  toHomRepresentation (MkPara pType f) = !%+ \p =>
    (!%+ \a => (f.fwd (a, p) ** \b' => fst (f.bwd (a, p) b')) **
      \l => foldr (\(a ** b') => pType.Plus p (snd (f.bwd (a, p) b'))) (pType.Zero p) l)

  public export
  composePara : a =\\=> b -> b =\\=> c -> a =\\=> c
  composePara (MkPara p f) (MkPara q g) = MkPara
    (p >*< q)
    (!%+ \(x, (ps, qs)) =>
      (g.fwd (f.fwd (x, ps), qs) ** \cPos =>
        let (bPos, qPos) = g.bwd (f.fwd (x, ps), qs) cPos
            (aPos, pPos) = f.bwd (x, ps) bPos
        in (aPos, (pPos, qPos))))

  public export
  composeParallel : a =\\=> b -> c =\\=> d -> (a >*< c) =\\=> (b >*< d)
  composeParallel (MkPara p f) (MkPara q g) = MkPara
    (p >*< q)
    (swapMiddle %+>> (f >*< g))


namespace DependentParametricLenses
  ||| Dependent parametric lenses, i.e. where the parameter container can vary
  ||| with the shape of the input container
  ||| Defined as its own record for the same reason as `ParaAddLens`
  public export
  record DParaAddLens (a, b : AddCont) where
    constructor MkPara
    Param : a.Shp -> AddCont
    Run : DPair a Param =%+> b

  namespace Wrap
    public export
    toDepPara : DParaAddLens a b -> DepParaMor DPairAddCont a b
    toDepPara (MkPara p f) = MkPara p f

    public export
    fromDepPara : DepParaMor DPairAddCont a b -> DParaAddLens a b
    fromDepPara (MkPara p f) = MkPara p f

  {- commented out for now, since its not used
  ||| Infix notation for additive parametric dependent lenses
  public export
  (=\\=>) : (a, b : AddCont) -> Type
  a =\\=> b = DParaAddLens a b
  
  public export
  trivialParam : a =%+> b -> a =\\=> b
  trivialParam f = MkPara
    (\_ => UnitCont)
    (!% !% \(x ** ()) => let (y ** ky) = (%!+) f x
                         in (y ** \y' => (ky y', ())))

  public export
  id : a =\\=> a
  id = trivialParam id
  
  public export
  composePara : a =\\=> b -> b =\\=> c -> a =\\=> c
  composePara (MkPara p f) (MkPara q g) = MkPara
    (\x => DPair (p x) (\ps => q (f.fwd (x ** ps))))
    (!%+ \(x ** (ps ** qs)) =>
      (g.fwd (f.fwd (x ** ps) ** qs) ** \cPos =>
        let (bPos, qPos) = g.bwd (f.fwd (x ** ps) ** qs) cPos
            (aPos, pPos) = f.bwd (x ** ps) bPos
        in (aPos, (pPos, qPos))))


  public export
  (&>>) : a =\\=> b -> b =\\=> c -> a =\\=> c
  (&>>) = composePara

  ||| A predicate witnessing that a parametric additive dependent lens has
  ||| a non-dependent (constant) parameter.
  public export
  data IsNotDependent : DParaAddLens a b -> Type where
    MkNonDep : (p : AddCont) -> (f : DPair a (const p) =%+> b) ->
      IsNotDependent {a=a} {b=b} (MkPara (\_ => p) f)
  
  public export
  GetNonDep : (pf : DParaAddLens a b) ->
    IsNotDependent pf => (pc : AddCont ** DPair a (const pc) =%+> b)
  GetNonDep _ @{MkNonDep pc f} = (pc ** f)

  public export
  GetParam : (pf : DParaAddLens a b) ->
    IsNotDependent pf => AddCont
  GetParam (MkPara (const p) f) @{MkNonDep p f} = p

  public export
  toHomRepresentation : (pf : DParaAddLens a b) ->
    IsNotDependent pf =>
    GetParam pf =%+> (InternalLensAdditive a b)
  toHomRepresentation (MkPara (const pc) f) @{MkNonDep pc f}
    = !%+ \p => (!%+ \x => (f.fwd (x ** p) ** \b' => fst (f.bwd (x ** p) b')) ** \l => foldr (\(x ** b') => pc.Plus p (snd (f.bwd (x ** p) b'))) (pc.Zero p) l)

  public export
  composeNTimes : Nat -> a =\\=> a -> a =\\=> a
  composeNTimes 0 f = id
  composeNTimes 1 f = f -- to get rid of the annoying Unit parameter
  composeNTimes (S k) f = composePara f (composeNTimes k f)

  ||| Convert a morphism from product container to one from DPair
  ||| This witnesses the isomorphism (a >< p) ≅ DPair a (const p)
  public export
  fromNonDepProduct : (a >*< p) =%+> b -> DPair a (const p) =%+> b
  fromNonDepProduct f = !%+ \(x ** p') => (%!+) f (x, p')


  %hide Data.Container.Base.Morphism.Definition.DependentLenses.(=%>)
  -}

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