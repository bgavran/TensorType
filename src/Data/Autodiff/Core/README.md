In this repo we effectively we expose the forward parts of objects and morphisms from `Data.Container` at a type level.


Forward mode AD is implemented using Charts
Reverse mode AD is implemented using Lenses 

In deep learning frameworks this distinction is not usually made because we can always transpose the Jacobian, but here it might be necesssary since some applicative stuff is not Naperian, therefore not transposable

This gives us only pointfree code. We still can't differentiate code like this:

```
fn : (Double, Double) -> Double
fn (x, y) = t + 3
  where t = x * y
```

We'd want a module to turn pointful code into pointfree.

Perhaps by using elaborator reflection we can turn a fragment of TTImp code into our pointfree code, and then differentiate that.




