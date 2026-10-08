Things here need to be cleaned up and refactored, but effectively, the idea is to expose the forward parts of objects and morphisms from `Data.Container.Additive` at a type level.

Forward mode AD is implemented using Charts, and reverse mode AD is implemented using lenses. In AD on cubical tensors one can usually go back-and-forth between this by transposing the Jacobian matrix, but here we need to be clear about the distinction.
This is because not all applicative linear algebra is done on cubical tensors, i.e. not all of them Naperian. This means they're not transposable, and a genuine distinction appears.

At the moment the differentiation works on pointfree code only, and the plan is to eventually be able to differentiate code like this:

```
fn : (Double, Double) -> Double
fn (x, y) = t + 3
  where t = x * y
```

Perhaps by using elaborator reflection we can turn a fragment of TTImp code into our pointfree code, and then differentiate that.