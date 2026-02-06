TODO update this, we now have `Base` and `Additive`

The boundary of this sublibrary to the outside world is via `Data.Container.idr`
which rexports all the relevant submodules.

These are mostly organised in
`Data/Container/<X>/Definition.idr` and 
`Data/Container/<X>/Instances.idr` files, where 

`Data/Definitions.idr` and `Data/Instances.idr` are the 'vertical slices' of the library, i.e they're the modules in which the former reexports all the
`.../<X>/Definition.idr` for all `X` and the latter reexports all the 
`.../<X>/Instances.idr` for all `X`.

In `src/Data/Container`:

1) In every subfolder, `Definition.idr` never depends on any `Instances.idr` from any subfolder.
2) In every subfolder:
  2.1) `Instance.idr` always depends on `Definition.idr`
  2.2) `Instance.idr` can depend on other `Definition.idr`'s and `Instance.idr`'s from other subfolders

Notably, `Object.Definition.idr` is a root of this dependency graph.

Notably, this sublibrary defines its own `Tensor` and `Tensor'` datatype that are made coherent with respect to constructions inside this library, and not with respect to the outside code.

Therefore, `src/Data.Tensor` reframes its own tensor constructions in a slighly different way (via `Tensor` and `CTensor`), more convenient to the practical programmer.